(* ProofAllocproc.v -- the whole-function WP for allocproc().

   Fifty-five instructions @ 0x80001b28; see CodeAllocproc.v for the
   listing and SpecAllocproc.v for the contract.  Three parts:

   * the SCAN (+0x1c .. +0x30), a bounded fuel induction over proc[] that
     acquires each lock, reads [p->state] out of the invariant's
     always-resident row, and releases again -- the wakeup loop's shape,
     minus the myproc test;
   * the INLINED allocpid (+0x38 .. +0x94; upstream ded23f2 made it [static]
     and gcc folded it in): acquire(&pid_lock), the retry scan for a pid no
     slot holds, [p->pid = pid], release -- one block lemma, [wp_ap_pidsec];
   * the ALLOCATION BODY (+0x98 .. +0xd0), which is where
     [ProcInv.proc_dormant] becomes [ProcInv.proc_priv]: the dormant block
     supplies the scalar cells, the null descriptor array and the second
     [p->pid] half; kalloc supplies the trapframe page
     ([ProcInv.tf_page_of_page_own]); proc_pagetable supplies the table
     ([ProcPtOwn.proc_pt_intro_ppt]);
   * the SHARED EPILOGUE (+0xd2 .. +0xde), reached from ALL FOUR exits, which
     is why [SpecAllocproc.allocproc_post] is stated as a function of the
     RETURNED POINTER rather than inside the continuation;
   * the TWO FAILURE TAILS (+0xe0 and +0xf0), reached when the trapframe
     kalloc or proc_pagetable runs dry.  Each hands the half-built slot to
     freeproc, releases the lock and rejoins the epilogue with a0 = 0.

   THE TAILS ARE WRITTEN TWICE, and there is no way around it: they are the
   same six instructions but at different addresses, so their [instr] facts,
   their two [jal] displacements and their [c.j] displacement all differ, and
   an [iAssert]ed block -- the trick that shares proc_pagetable's four exits
   and freeproc's zeroing run -- can only be stated at ONE pc.  What they do
   NOT differ in is what freeproc is handed: tail 1 passes [None]/[None] (the
   kalloc that failed left p->trapframe zero), tail 2 passes [None]/[Some]
   (the trapframe is a live page and gets kfreed).  That asymmetry is exactly
   why [SpecFreeproc.fp_pt] and [SpecFreeproc.fp_tf] are independently
   optional rather than a single [proc_dormant].

   EXPLICIT-CPUID NOTE.  allocproc is [b]-GENERIC on the outside and pinned
   on the inside: from acquire's return (+0x22) to release's call (+0x28) --
   which includes the WHOLE allocation body -- a held lock forces the index to
   the literal [false], so those thirty leaves collapse with [wp_next_off] and
   read exactly as they did before the refactor, all at acquire's exit hart
   [CIDf].  Only the prologue, the loop head, the post-release tail and the
   epilogue are hart-generic.

   The exits leave at DIFFERENT indices -- the found arm RETURNS HOLDING
   p->lock, so acquire's unbalanced [false] propagates out to the caller,
   while the null arm and both failure tails release and exit at [b].  That is why
   [SpecAllocproc.allocproc_post] carries [sie_cap_gpr] inside its ARMS, and
   why the shared epilogue ([ap_tail] below) is parametric in an exit index
   [xb] and an entry hart [CIDt] and hands back only the final register file.

   The scan is the [ProofWakeup] shape: the loop invariant is ITSELF a
   [wp_next b], so the IH re-enters at a migrated hart and [wp_next_shift] is
   never needed; both the epilogue (hart-free by construction) and the
   function's own continuation (anchored at the section's [CID0]) ride through
   the induction as premises, which makes forwarding them the identity.

   [Set Printing Depth 40] is not cosmetic: this proof's context carries
   [tf_page]'s 4096-conjunct big-op, and without it a one-line mistake
   spends tens of minutes formatting the goal instead of reporting an error
   (claude-notes/durable-notes.md). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn CalleeSaved KernelText.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import WpLock.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import ArrCursor.
Require Import PageGeom KallocInv.
Require Import PtTree PtBuild.
Require Import UserPtTree ProcPtOwn.
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KvmSpec.
Require Import SpecAcquire SpecRelease PidLock SpecKalloc SpecProcPagetable SpecMemset.
Require Import SpecFreeproc.
Require Import SpecProcinit.
Require Import SpecAllocproc.
Require Import CodeAllocproc.
From Kernel Require KernelInstrs KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import KernelRvcDecode.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.
Require Import ChildTok.  (* [gen_alloc] -- the incarnation allocproc mints *)
Local Open Scope Z_scope.
Set Printing Depth 40.


(* ===================================================================== *)
(* Pure address / value arithmetic.  All of it lives OUTSIDE the Iris      *)
(* section, per the zify-hook rule: no [mword] in context when [lia] runs. *)
(* ===================================================================== *)



(* the [struct proc] displacements, in the [sign_extend' 64 (mword 12)] shape
   a load/store leaf produces them.  [p_pid] / [p_pagetable] / [p_trapframe]
   are already SPELLED that way in ProcGeom, so those three are [reflexivity]. *)
Lemma ap_off_24 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state X.
Proof. rewrite /p_state /state_off. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma ap_off_48 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 48 : mword 12)) = p_pid X.
Proof. reflexivity. Qed.

Lemma ap_off_64 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 64 : mword 12)) = p_kstack X.
Proof. rewrite /p_kstack. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma ap_off_80 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 80 : mword 12)) = p_pagetable X.
Proof. reflexivity. Qed.

Lemma ap_off_88 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 88 : mword 12)) = p_trapframe X.
Proof. reflexivity. Qed.

Lemma ap_off_96 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 96 : mword 12)) = p_context X.
Proof. rewrite /p_context /context_off. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma ap_off_104 (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 104 : mword 12)) = pa_add (p_context X) 8.
Proof. rewrite p_ctx_slot1. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.li a5,1] then [c.sw a5,24(s1)] writes exactly the USED code. *)
Lemma ap_used_val :
  trunc32 (add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
  = USED.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.li rd,0] writes the zero word. *)
Lemma ap_li_zero :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))
  = (zero_reg : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.lui a4,0x1] is PGSIZE *)
Lemma ap_lui_pgsize :
  luival (sign_extend' 20 (mword_of_int 1 : mword 6)) = (mword_of_int 4096 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* [li a2,112] out of x0 *)
Lemma ap_li_112 :
  add_vec (zero_reg : mword 64) (sign_extend' 64 (mword_of_int 112 : mword 12))
  = (mword_of_int (Z.of_nat 112) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* a 32-bit word sign-extends to zero only if it IS zero -- the [c.beqz a5]
   after [c.lw a5,24(s1)] is exactly the [state == UNUSED] test. *)
Lemma ap_sext_zero (v : mword 32) :
  eq_vec (sign_extend' 64 v) (zero_reg : mword 64) = true -> v = UNUSED.
Proof.
  intro He. apply eq_vec_true_iff in He.
  apply (f_equal trunc32) in He.
  rewrite trunc32_sext64 in He. rewrite He.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* the FALSE side of the same test: the scan passed this slot, so its state
   is not UNUSED and its lock carries [ProcAvail]'s allocation marker. *)
Lemma ap_is_unused_false (v : mword 32) :
  eq_vec (sign_extend' 64 v) (zero_reg : mword 64) = false -> is_unused v = false.
Proof.
  intro He. rewrite /is_unused. apply bool_decide_eq_false_2. intro Hv. subst v.
  rewrite (_ : eq_vec (sign_extend' 64 UNUSED) (zero_reg : mword 64) = true)
    in He; [discriminate |].
  apply eq_vec_true_iff. apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma ap_zero_nullp : (zero_reg : mword 64) = nullp.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* a page kalloc handed back is not the null pointer, in the shape the
   [c.beqz] fall-through leaf asks for. *)
Lemma ap_valid_nz (r : mword 64) : page_valid r -> eq_vec r (zero_reg : mword 64) = false.
Proof.
  intro Hv. apply eq_vec_false_iff. rewrite ap_zero_nullp.
  exact (page_valid_ne_null r Hv).
Qed.

(* proc_pagetable's two numeric premises about the trapframe page. *)
Lemma ap_tf_align (r : mword 64) :
  page_valid r -> subrange_vec_dec r 11 0 = (zeros' 12 : mword 12).
Proof.
  intros [Hal _]. apply aligned_low12.
  unfold page_aligned, PGSIZE in Hal. rewrite uint_unsigned in Hal. exact Hal.
Qed.

Lemma ap_tf_bound (r : mword 64) : page_valid r -> (uint r + 4096 < 2 ^ 56)%Z.
Proof.
  intros [_ [_ Hhi]]. unfold kmem_hi in Hhi.
  assert (H56 : (2 ^ 56 = 72057594037927936)%Z) by (vm_compute; reflexivity).
  rewrite H56. lia.
Qed.

(* the scan's exit test, [bne s1,s2], as the index comparison. *)
Lemma ap_neq_end (i : nat) :
  (i <= NPROC)%nat ->
  neq_vec (proc_addr i) (proc_addr NPROC) = negb (Nat.eqb i NPROC).
Proof.
  intro Hi. rewrite !proc_addr_acur. unfold pacur.
  apply (acur_neq KernelSyms.proc proc_size i NPROC
           proc_base_nonneg proc_size_pos proc_end_fits Hi).
Qed.

(* The numeric side conditions, as mword-FREE top-level lemmas.  Every one
   of these is discharged inside an Iris goal whose context is full of
   [bv_unsigned]s, where [bitvector.tactics]' zify hook makes [lia] answer
   "Cannot find witness" (claude-notes/durable-notes.md).  Stated here, they
   are closed facts the call sites pass by name. *)
Lemma ap_K4 (K : nat) : (48 <= K)%nat -> (4 <= K)%nat.
Proof. lia. Qed.
Lemma ap_K2 (K : nat) : (48 <= K)%nat -> (2 <= K - 4)%nat.
Proof. lia. Qed.
Lemma ap_K10 (K : nat) : (48 <= K)%nat -> (10 <= K - 4)%nat.
Proof. lia. Qed.
Lemma ap_K14 (K : nat) : (48 <= K)%nat -> (14 <= K - 4)%nat.
Proof. lia. Qed.
Lemma ap_K36 (K : nat) : (48 <= K)%nat -> (40 <= K - 4)%nat.
Proof. lia. Qed.
(* freeproc's, in the two error tails -- the deepest callee now *)
Lemma ap_K44 (K : nat) : (48 <= K)%nat -> (44 <= K - 4)%nat.
Proof. lia. Qed.
Lemma ap_Kback (K : nat) : (48 <= K)%nat -> ((K - 4) + 4)%nat = K.
Proof. lia. Qed.
Lemma ap_lvl1 (lvl : nat) : (Z.of_nat lvl + 2 < 2 ^ 31)%Z -> (Z.of_nat lvl + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.
Lemma ap_lvlS (lvl : nat) : (Z.of_nat lvl + 2 < 2 ^ 31)%Z -> (Z.of_nat (S lvl) + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.
Lemma ap_nb_pt (n : nat) : (K_allocproc < S n)%nat -> (K_proc_pagetable < n)%nat.
Proof. lia. Qed.
Lemma ap_nb_pos (n : nat) : (K_allocproc < n)%nat -> n <> 0%nat.
Proof. lia. Qed.
(* The two facts the FAILURE TAILS need about the budget.

   [ap_sub_dec] re-associates: proc_pagetable is called with the trapframe
   page already spent ([avail_dec on]), so its own exhaustion witness --
   "dry after [n] more" -- is allocproc's "dry after [S n]".

   [ap_refute_dry] is the whole point of the counted seal: a caller that
   brought [K_allocproc < nb] pages can never see the third arm, because
   running dry after at most [K_allocproc] of them contradicts the premise.
   [K_allocproc] stays an opaque atom here -- [lia] never needs its value. *)
Lemma ap_sub_dec (on : option nat) (n : nat) :
  avail_sub (avail_dec on) n = avail_sub on (S n).
Proof.
  replace (S n) with (1 + n)%nat by lia.
  rewrite avail_sub_add avail_sub_S avail_sub_0. reflexivity.
Qed.

Lemma ap_refute_dry (nb n : nat) :
  (K_allocproc < nb)%nat -> (n <= K_allocproc)%nat ->
  avail_zero (avail_sub (Some nb) n) -> False.
Proof. rewrite avail_sub_Some. cbn. lia. Qed.

(* the two null comparisons the tails take.  kalloc reports failure as
   [nullp], proc_pagetable as [mword_of_int 0]; [c.beqz] tests against
   [zero_reg], and all three are the same word. *)
Lemma ap_null_eqz : eq_vec (nullp : mword 64) (zero_reg : mword 64) = true.
Proof. rewrite -ap_zero_nullp. vm_compute. reflexivity. Qed.

Lemma ap_zero_eqz : eq_vec (mword_of_int 0 : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ap_zero_of_int : (mword_of_int 0 : mword 64) = (zero_reg : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ap_nodes_le (n : nat) : (n <= K_proc_pagetable)%nat -> (S n <= K_allocproc)%nat.
Proof. lia. Qed.

(* THE LOCK-ORDER DERIVATIONS.  allocproc's own premise ([Hbelow], added to
   [SpecAllocproc.wp_allocproc_core_body]/[wp_allocproc_sconf_body]) is
   stated at "proc" (rank 11), the only lock allocproc itself acquires.
   While p->lock is held, the held set at any nested call is
   [{["proc"]} ∪ lks], and TWO calls made from inside that
   critical section carry their own order premise: the inlined allocpid's
   "nextpid" (10) and kalloc's "kmem" (11).  Both outrank "proc", so
   [locks_below_union_singleton] pushes [Hbelow] (lifted by
   [locks_below_mono]) across the held "proc" singleton. *)
Lemma ap_below_nextpid (lks : gset string) :
  locks_below lks "proc" ->
  locks_below ({["proc"]} ∪ lks) "nextpid".
Proof.
  intros Hbelow. apply locks_below_union_singleton; [vm_compute; lia |].
  lkbelow.
Qed.

Lemma ap_below_kmem (lks : gset string) :
  locks_below lks "proc" ->
  locks_below ({["proc"]} ∪ lks) "kmem".
Proof.
  intros Hbelow. apply locks_below_union_singleton; [vm_compute; lia |].
  lkbelow.
Qed.

(* the two instances of the exit test, as closed facts *)
Lemma ap_neq_end_eq : neq_vec (proc_addr NPROC) (proc_addr NPROC) = false.
Proof. rewrite (ap_neq_end NPROC (Nat.le_refl NPROC)) Nat.eqb_refl. reflexivity. Qed.

Lemma ap_neq_end_lt (i : nat) : (i < NPROC)%nat -> neq_vec (proc_addr i) (proc_addr NPROC) = true.
Proof.
  intro Hi. rewrite (ap_neq_end i (Nat.lt_le_incl _ _ Hi)).
  destruct (Nat.eqb_spec i NPROC) as [He | _]; [ exfalso; lia | reflexivity ].
Qed.

(* the scan's index arithmetic, likewise mword-free *)
Lemma ap_fuel0 (k : nat) : (NPROC - k <= 0)%nat -> (k < NPROC)%nat -> False.
Proof. unfold NPROC. lia. Qed.
Lemma ap_fuelS (k fuel : nat) : (NPROC - k <= S fuel)%nat -> (NPROC - S k <= fuel)%nat.
Proof. unfold NPROC. lia. Qed.
Lemma ap_kS_lt (k : nat) : (k < NPROC)%nat -> Nat.eqb (S k) NPROC = false -> (S k < NPROC)%nat.
Proof. intros Hk He. apply Nat.eqb_neq in He. lia. Qed.
Lemma ap_zero_lt : (0 < NPROC)%nat.
Proof. unfold NPROC. lia. Qed.
Lemma ap_fuel_init : (NPROC - 0 <= NPROC)%nat.
Proof. unfold NPROC. lia. Qed.


(* The register names, hoisted above the module so that [ap_tail] below can
   use them. *)
Notation ap_ra := (mword_of_int 1 : mword 5).
Notation ap_s0 := (mword_of_int 8 : mword 5).
Notation ap_s1 := (mword_of_int 9 : mword 5).
Notation ap_a0 := (mword_of_int 10 : mword 5).
Notation ap_a1 := (mword_of_int 11 : mword 5).
Notation ap_a2 := (mword_of_int 12 : mword 5).
Notation ap_a4 := (mword_of_int 14 : mword 5).
Notation ap_a5 := (mword_of_int 15 : mword 5).
Notation ap_s2 := (mword_of_int 18 : mword 5).
Notation ap_x0 := (mword_of_int 0 : mword 5).

(* [rget] is the plain map lookup at every register this function reads --
   none of them is tp.  Stated once per register, with the hart IMPLICIT, so a
   [rewrite] fires at whatever hart the leaf's [let]-bound value carries. *)
Lemma ap_rg_ra `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (MM : regfile) : rget MM ap_ra = MM !!! Regidx ap_ra.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_s0 `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (MM : regfile) : rget MM ap_s0 = MM !!! Regidx ap_s0.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_s1 `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (MM : regfile) : rget MM ap_s1 = MM !!! Regidx ap_s1.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_s2 `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (MM : regfile) : rget MM ap_s2 = MM !!! Regidx ap_s2.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_a0 `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (MM : regfile) : rget MM ap_a0 = MM !!! Regidx ap_a0.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_a4 `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (MM : regfile) : rget MM ap_a4 = MM !!! Regidx ap_a4.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_a5 `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (MM : regfile) : rget MM ap_a5 = MM !!! Regidx ap_a5.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_x0 `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (MM : regfile) : rget MM ap_x0 = MM !!! Regidx ap_x0.
Proof. rgne. reflexivity. Qed.

(* ===================================================================== *)
(* THE SHARED EPILOGUE'S CONTRACT (+0xd2 .. +0xde), as a HART-FREE        *)
(* proposition.                                                           *)
(*                                                                        *)
(* Both exits join at +0xd2, but they arrive at DIFFERENT SIE indices --  *)
(* the found arm still holds p->lock, so it runs the epilogue at the      *)
(* literal [false], while the null arm has released everything and runs   *)
(* it at [b].  So the epilogue is parametric in an exit index [xb] AND in *)
(* the hart [CIDt] it is entered on; its own continuation is a            *)
(* [wp_next (CID0 := CIDt) xb], which is what lets the seven leaves       *)
(* migrate at [xb = b] and collapse at [xb = false].                      *)
(*                                                                        *)
(* Quantifying [CIDt] here (rather than anchoring at the lemma's own      *)
(* hart) is what makes this proposition mention no hart at all: forwarding*)
(* it across an iteration of the scan is then the IDENTITY, and it can be *)
(* written verbatim inside the loop invariant's [wp_next] lambda without  *)
(* the anchor being captured by the lambda's binder.                      *)
(*                                                                        *)
(* It hands the caller only the final register file plus [callee_saved];  *)
(* building [SpecAllocproc.allocproc_post] out of the arm's own payload   *)
(* is the ARM's job, which is exactly why the post's SIE index can be     *)
(* per-arm.                                                               *)
(* ===================================================================== *)
(* THE TRAP RESERVE IS A ∀-BOUND PARAMETER [rsv], ALONGSIDE [xb].
   The epilogue is entered at TWO different carves, and the arm alone does not
   determine which.  The found arm still holds p->lock, so it runs at arm
   [false] with the caller's reserve sitting IN the index
   ([trap_res b + (K - 4)]); the null arm has released everything and runs at
   arm [b], where the same physical carve is spelled [(K - 4)] with the reserve
   implicit in [sie_cap]'s own [trap_res b] summand.  So the epilogue cannot
   compute the reserve from [xb] -- at [xb = false] it would get 0, which is
   the found arm's WRONG answer -- and it must not try: it is index-generic,
   pops 4 slots, and conserves whatever it was handed.  Hence [rsv], opaque,
   quantified here so that ONE [ap_tail] resource serves both arms
   ([rsv := trap_res b] found, [rsv := 0] null).

   This is the arm-generic-helper convention: a helper that is generic in the
   arm but applied at a pinned arm from a reserved window takes the reserve as
   a parameter rather than deriving it (see claude-notes). *)
Definition ap_tail `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{XI : CurCtx}
     (m : regfile) (spd pme ret_tgt : mword 64) (K : nat) : iProp Σ :=
  (∀ (rsv : nat) (xb : bool) (CIDt : CpuId) (Mt : regfile) (rv : mword 64),
     ⌜ Mt !!! Regidx csp_rs1 = spd /\
       Mt !!! Regidx ap_s1 = rv /\
       (forall r : mword 5, is_cs_idx r = true ->
          r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
          Mt !!! Regidx r = m !!! Regidx r) ⌝ -∗
     sie_cap_gpr KT1 (CID := CIDt) Mt (rsv + (K - 4))%nat xb pme -∗
     pc_is (CID := CIDt) (mword_of_int (KernelSyms.allocproc + 0xd2)) -∗
     wp_next (CID0 := CIDt) xb pme (fun (CID : CpuId) =>
       ∀ (Mf : regfile),
         ⌜ callee_saved m Mf /\ Mf !!! Regidx ap_a0 = rv ⌝ -∗
         sie_cap_gpr KT1 Mf (rsv + K)%nat xb pme -∗
         pc_is ret_tgt -∗
         WP (Loop : expr riscv_lang)) -∗
     WP (LoopE gen_id CIDt : expr riscv_lang))%I.

(* THE GENERAL PROOF.  Everything allocproc does, at an ARBITRARY page
   budget -- so both failure tails are live code and both are proved.  The
   counted contract is derived from this in [AllocprocSeal] below; nothing
   about the instruction stream differs between the two. *)
Module AllocprocCore (Acquire : ACQUIRE) (Release : RELEASE)
                     (AK : KALLOC) (PPT : PROC_PAGETABLE_GEN) (MS : MEMSET)
                     (FP : FREEPROC) : ALLOCPROC_GEN.

(* ===================================================================== *)
(* THE INLINED allocpid, +0x38 .. +0x94 (upstream ded23f2).               *)
(*                                                                        *)
(*   acquire(&pid_lock);                                                  *)
(*   for (;;) {                                                           *)
(*     pid = nextpid;                                                     *)
(*     nextpid = (pid == PIDMAX) ? 1 : pid + 1;                           *)
(*     for (q = proc; q < &proc[NPROC]; q++) if (q->pid == pid) break;    *)
(*     if (q == &proc[NPROC]) break;                                      *)
(*   }                                                                    *)
(*   p->pid = pid;                                                        *)
(*   release(&pid_lock);                                                  *)
(*                                                                        *)
(* allocpid() used to be a function with a contract (SpecAllocpid.v); gcc  *)
(* now inlines it, so its body is proved HERE as one block lemma stated   *)
(* in the shape that contract had: enter at +0x38 holding the two pieces  *)
(* of [p->pid] the caller owns, leave at +0x98 with the same two pieces   *)
(* at the new pid, callee-saved registers intact, the lock net zero.      *)
(* The scan's registers: a3 = pid, a1 = the next counter value, a5 = q,   *)
(* a2 = &proc[NPROC], a0 = 1 and a6 = PIDMAX (the two constants).          *)
(*                                                                        *)
(* WHAT THE SCAN READS.  [q->pid] for all 64 slots, under <pid_lock> and  *)
(* nothing else -- which is exactly the quarter of every pid cell the     *)
(* lock's payload carries ([PidLock.nextpid_res_at]).  Slot k's quarter   *)
(* is also what completes the cell for the store at +0x8a: the caller     *)
(* holds [proc_pub]'s quarter and the dormant block's half.               *)
(*                                                                        *)
(* THE OUTER LOOP IS AN iLöb, NOT A FUEL INDUCTION.  It terminates (64    *)
(* slots cannot hold all of 65 consecutive candidates), but proving that  *)
(* is a pigeonhole argument nothing needs: partial correctness is the     *)
(* whole story, and what the contract says about the pid -- that it lies  *)
(* in [1, PIDMAX] -- is a loop INVARIANT, not a termination fact.  The    *)
(* inner scan is bounded by the table and is the usual fuel induction.    *)
(* ===================================================================== *)
Notation ap_a3 := (mword_of_int 13 : mword 5).
Notation ap_a6 := (mword_of_int 16 : mword 5).

(* the two constants the scan keeps in a0 (the wrap-around value) and a6
   (PIDMAX), in the shape the [li] leaves produce them *)
Definition ap_c1 : mword 64 :=
  add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))).
Definition ap_c1000 : mword 64 :=
  add_vec zero_reg (sign_extend' 64 (mword_of_int 1000 : mword 12)).

(* ---------------------------------------------------------------------- *)
(* THE PID'S INTERVAL, in the arithmetic the block moves it through.        *)
(*                                                                          *)
(* The bound is carried on the WHOLE 64-bit register and not on [trunc32]   *)
(* of it, because the [beq a3,a6] at +0x64 compares the whole register      *)
(* against PIDMAX: a bound on the low half alone leaves the fall-through    *)
(* arm unable to say the candidate is below PIDMAX.  Four moves need a      *)
(* value law -- the [lw] that loads the counter, the [c.mv]s (covered by    *)
(* [add_vec_zero_l]), the [addiw] that advances it, and the two stores'     *)
(* [trunc32] -- and they are these.                                         *)
(* ---------------------------------------------------------------------- *)
Lemma ap_c1_val : bv_unsigned ap_c1 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma ap_c1000_val : bv_unsigned ap_c1000 = PIDMAX.
Proof. unfold PIDMAX. vm_compute. reflexivity. Qed.

(* the counter's value, as the [lw] at +0x48 sign-extends it *)
Lemma ap_sext_val (w : mword 32) :
  (bv_unsigned w < 2 ^ 31)%Z ->
  bv_unsigned (sign_extend' 64 w : mword 64) = bv_unsigned w.
Proof.
  intro Hw.
  pose proof (bv_unsigned_in_range _ w) as [Hr0 _].
  assert (H31 : (2 ^ 31)%Z = 2147483648) by (vm_compute; reflexivity).
  assert (H64 : (2 ^ 64)%Z = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite H31 in Hw.
  rewrite sext32_64_moi moi64_unsigned. unfold bv_signed.
  assert (Hsw : bv_swrap 32 (bv_unsigned w) = bv_unsigned w).
  { apply bv_swrap_small.
    assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
    rewrite Hhm. lia. }
  rewrite Hsw. apply bvw64_small. rewrite H64. lia.
Qed.

(* +0x68 [addiw a1,a3,1]: below PIDMAX the 32-bit add does not wrap, so the
   next candidate is the current one's successor. *)
Lemma ap_addiw_val (v : mword 64) :
  (1 <= bv_unsigned v < PIDMAX)%Z ->
  bv_unsigned (sign_extend' 64
     (subrange_vec_dec
        (add_vec v (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0 : mword 32)
     : mword 64)
  = (bv_unsigned v + 1)%Z.
Proof.
  intros Hv. unfold PIDMAX in Hv.
  assert (H31 : (2 ^ 31)%Z = 2147483648) by (vm_compute; reflexivity).
  assert (H64 : (2 ^ 64)%Z = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Hd : bv_unsigned (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64) = 1)
    by (vm_compute; reflexivity).
  assert (Hsum : bv_unsigned (add_vec v (sign_extend' 64 (mword_of_int 1 : mword 12)))
                 = (bv_unsigned v + 1)%Z).
  { rewrite add_vec64_unsigned Hd. apply bvw64_small. rewrite H64. lia. }
  assert (Hlow : bv_unsigned (subrange_vec_dec
                   (add_vec v (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0 : mword 32)
                 = (bv_unsigned v + 1)%Z).
  { rewrite subrange_31_0_unsigned Hsum. apply Z.mod_small. lia. }
  rewrite ap_sext_val; [ exact Hlow | rewrite Hlow H31; lia ].
Qed.

(* the two stores' [sw]/[c.sw]: a value inside the interval survives the
   truncation to the cell's 32 bits *)
Lemma ap_trunc_val (v : mword 64) :
  (bv_unsigned v <= PIDMAX)%Z -> bv_unsigned (trunc32 v) = bv_unsigned v.
Proof.
  intro Hv. unfold PIDMAX in Hv.
  pose proof (bv_unsigned_in_range _ v) as [Hr0 _].
  rewrite trunc32_unsigned. apply bv_wrap_small.
  assert (Hm : bv_modulus 32 = 4294967296) by (vm_compute; reflexivity).
  rewrite Hm. lia.
Qed.

(* ...and the two together: a candidate inside the interval survives the
   round trip through the cell's 32 bits, which is what turns the scan's
   [beq a4,a3] fall-through into a fact about the LIST of cell values that
   <pid_lock>'s payload carries. *)
Lemma ap_sext_trunc (v : mword 64) :
  (bv_unsigned v <= PIDMAX)%Z -> sign_extend' 64 (trunc32 v) = v.
Proof.
  intro Hv.
  assert (H31 : (2 ^ 31)%Z = 2147483648) by (vm_compute; reflexivity).
  assert (Ht : bv_unsigned (trunc32 v) = bv_unsigned v) by exact (ap_trunc_val v Hv).
  apply bv_eq. rewrite ap_sext_val; [exact Ht |].
  rewrite Ht H31. unfold PIDMAX in Hv. lia.
Qed.

(* what every point of the retry loop knows about the register map: the
   slot pointer in s1, the two constants, the end-of-table cursor in a2,
   and that nothing callee-saved has moved since the block's entry map [m]. *)
Definition ap_pid_regs (m : regfile) (k : nat) (R : regfile) : Prop :=
  R !!! Regidx ap_s1 = proc_addr k /\
  R !!! Regidx ap_a0 = ap_c1 /\
  R !!! Regidx ap_a6 = ap_c1000 /\
  R !!! Regidx ap_a2 = proc_addr NPROC /\
  callee_saved m R.

Lemma ap_pid_regs_ins (m : regfile) (k : nat) (R : regfile) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> r <> ap_s1 -> r <> ap_a0 -> r <> ap_a6 -> r <> ap_a2 ->
  ap_pid_regs m k R -> ap_pid_regs m k (<[Regidx r := v]> R).
Proof.
  intros Hcs N9 N10 N16 N12 (Hs1 & Ha0 & Ha6 & Ha2 & Hcsv).
  assert (Hne : forall q : mword 5, r <> q -> Regidx q <> Regidx r).
  { intros q Hq He. apply Hq. injection He as He. exact (eq_sym He). }
  split; [| split; [| split; [| split]]].
  - rewrite upd_ne; [exact Hs1 | exact (Hne _ N9)].
  - rewrite upd_ne; [exact Ha0 | exact (Hne _ N10)].
  - rewrite upd_ne; [exact Ha6 | exact (Hne _ N16)].
  - rewrite upd_ne; [exact Ha2 | exact (Hne _ N12)].
  - apply callee_saved_insert_r; [exact Hcs | exact Hcsv].
Qed.

(* the scan's two comparisons against &proc[NPROC], as index facts *)
Lemma ap_end_lt (i : nat) : (i < NPROC)%nat -> eq_vec (proc_addr i) (proc_addr NPROC) = false.
Proof.
  intro Hi. pose proof (ap_neq_end_lt i Hi) as Hn.
  unfold neq_vec in Hn. by apply negb_true_iff in Hn.
Qed.
Lemma ap_fuel_init : (NPROC - 0 <= NPROC)%nat.
Proof. lia. Qed.
Lemma ap_nproc_pos : (0 < NPROC)%nat.
Proof. unfold NPROC. lia. Qed.

(* the relocations: two &pid_lock (auipc a0,0x11 + addi), two &nextpid
   (auipc 0x8 + a 12-bit displacement), proc[] and &proc[NPROC] *)
Lemma ap_pidlk_reloc1 :
  add_vec (add_vec (mword_of_int (KernelSyms.allocproc + 0x38) : mword 64) (auipc_off (mword_of_int 17 : mword 20)))
          (sign_extend' 64 (mword_of_int 2174 : mword 12)) = alp_pid_lock.
Proof. rewrite /alp_pid_lock. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ap_pidlk_reloc2 :
  add_vec (add_vec (mword_of_int (KernelSyms.allocproc + 0x8c) : mword 64) (auipc_off (mword_of_int 17 : mword 20)))
          (sign_extend' 64 (mword_of_int 2090 : mword 12)) = alp_pid_lock.
Proof. rewrite /alp_pid_lock. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ap_nextpid_reloc1 :
  add_vec (add_vec (mword_of_int (KernelSyms.allocproc + 0x44) : mword 64) (auipc_off (mword_of_int 8 : mword 20)))
          (sign_extend' 64 (mword_of_int 1838 : mword 12)) = alp_nextpid.
Proof. rewrite /alp_nextpid. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ap_nextpid_reloc2 :
  add_vec (add_vec (mword_of_int (KernelSyms.allocproc + 0x82) : mword 64) (auipc_off (mword_of_int 8 : mword 20)))
          (sign_extend' 64 (mword_of_int 1776 : mword 12)) = alp_nextpid.
Proof. rewrite /alp_nextpid. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ap_proc_reloc :
  add_vec (add_vec (mword_of_int (KernelSyms.allocproc + 0x6c) : mword 64) (auipc_off (mword_of_int 17 : mword 20)))
          (sign_extend' 64 (mword_of_int 3194 : mword 12)) = proc_addr 0.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ap_procend_reloc :
  add_vec (add_vec (mword_of_int (KernelSyms.allocproc + 0x52) : mword 64) (auipc_off (mword_of_int 22 : mword 20)))
          (sign_extend' 64 (mword_of_int 1684 : mword 12)) = proc_addr NPROC.
Proof. rewrite proc_addr_acur proc_end_is_tickslock. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ap_lka (B : regfile) :
  B !!! Regidx ap_a0 = alp_pid_lock ->
  add_vec (B !!! Regidx ap_a0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = alp_pid_lock.
Proof. intros ->. rewrite /alp_pid_lock. apply bv_eq; vm_compute; reflexivity. Qed.

(* the block's postcondition, named so the loop invariants can carry the
   caller's continuation without restating it *)
(* THE INCARNATION IS MINTED IN HERE, and it has to be: the mint needs the
   pid ([ChildTok.gen_alloc] pins it) and the REGISTRATION needs the name,
   and the only place both exist is inside <pid_lock>'s critical section,
   at the [p->pid = pid] store.  So the block hands its caller a whole
   generation, the slot re-keyed to it ([SlotGen.slot_gen_update], out of
   the whole the dormant block carried) and the pid registered to it. *)
Definition ap_pid_post `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (m : regfile) (k : nat) (av n : nat) (eb : bool) (p : mword 64) (lks : gset string) : iProp Σ :=
  (∀ (mf : regfile) (pidn : mword 32) (γg : gname),
     ⌜ callee_saved m mf ⌝ -∗
     (* THE PID THE BLOCK CHOSE IS IN [1, PIDMAX].  It comes off the
        counter <pid_lock> protects, whose payload carries the same bound
        ([PidLock.nextpid_res_at]), and the retry loop re-establishes it at
        every candidate: the [beq a3,a6] against PIDMAX at +0x64 sends the
        wrap arm to 1 and the fall-through to [pid + 1] with [pid < PIDMAX].
        [SpecAllocproc.allocproc_post] relays it. *)
     ⌜ (1 <= bv_unsigned pidn <= PIDMAX)%Z ⌝ -∗
     sie_cap_gpr KT1 mf av false p -∗
     cpu_own n eb p false lks -∗
     pc_is (mword_of_int (KernelSyms.allocproc + 0x98) : mword 64) -∗
     p_pid (proc_addr k) ↦₄{DfracOwn (1/4)} pidn -∗
     p_pid (proc_addr k) ↦₄{DfracOwn (1/2)} pidn -∗
     (* the fresh incarnation, whole and at the trivial payload -- a process
        nobody forked owes its parent nothing, and a fork REPLACES the
        payload before splitting ([ChildTok.gen_set]) *)
     gen_own γg (DfracOwn 1) (proc_addr k) pidn (fun _ => True)%I -∗
     (* ...the slot, re-keyed to it: the whole this block was handed came
        out of the dormant block at the LAST incarnation's name *)
     slot_gen (proc_addr k) (DfracOwn 1) γg -∗
     (* ...and the pid, registered to it in the authority this lock's
        payload carries ([PidLock.nextpid_res_at]) *)
     pid_reg pidn (DfracOwn 1) γg -∗
     WP (Loop : expr riscv_lang))%I.

Section ProofAllocprocPid.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.

  Local Ltac peel_ne := repeat (rewrite upd_ne; [| vm_compute; discriminate]).
  Local Ltac cs_ins := repeat (apply callee_saved_insert_r; [vm_compute; reflexivity |]).
  Local Ltac regs_ins H :=
    apply ap_pid_regs_ins;
    [ vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate
    | vm_compute; discriminate | vm_compute; discriminate | exact H ].
  Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.

  Lemma wp_ap_pidsec `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γp : gname) (m : regfile) (k : nat) (av n : nat) (eb : bool) (p : mword 64)
      (lks : gset string) (pidi pidh : mword 32) (g0 : gname) :
    (Z.of_nat n + 1 < 2 ^ 31)%Z ->
    (10 <= av)%nat ->
    (k < NPROC)%nat ->
    m !!! Regidx ap_s1 = proc_addr k ->
    locks_below lks "nextpid" ->
    (* THE SLOT'S PID CELL IS STILL 0, which is what the dormant block this
       slot came out of says ([SlotGen.gen_halves_dorm]'s UNUSED arm).  The
       store below overwrites it, and the pid register's domain fact
       ([SlotGen.pid_reg_dom]) survives that only because 0 is registered
       to nothing. *)
    bv_unsigned pidh = 0 ->
    sie_cap_gpr KT1 m av false p -∗
    cpu_own n eb p false lks -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.allocproc + 0x38) : mword 64) -∗
    is_lock γp alp_pid_lock "nextpid"%string nextpid_res_at -∗
    p_pid (proc_addr k) ↦₄{DfracOwn (1/4)} pidi -∗
    p_pid (proc_addr k) ↦₄{DfracOwn (1/2)} pidh -∗
    (* THE SLOT'S GENERATION, WHOLE, out of the dormant block: this block
       re-keys it to the incarnation it mints. *)
    slot_gen (proc_addr k) (DfracOwn 1) g0 -∗
    wp_next false p (fun (CIDc : CpuId) => ap_pid_post (CID := CIDc) m k av n eb p lks) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hav Hk Hs1 Hbelow Hpid0.
    iIntros "Hcg Hcpu #Htext Hpc #Hislock Hpidi Hpidh Hsg Hcont".
    (* release below spells the window index at its own exit arm; the two
       bools agree by [cpu_own_eb_agree], recorded once here *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbeq.
    (* +0x38 auipc a0,0x11 ; +0x3c addi a0,a0,-1936 : a0 := &pid_lock *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.allocproc + 0x38)) ap_a0 (mword_of_int 17 : mword 20) m av false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
    { iApply (api_38 with "Htext"). }
    iIntros (CID1 Hs1c) "Hcg Hpc".
    set (A1 := <[Regidx ap_a0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.allocproc + 0x38) : mword 64) (auipc_off (mword_of_int 17 : mword 20)))]> m).
    change (<[Regidx ap_a0 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.allocproc + 0x38) : mword 64) (auipc_off (mword_of_int 17 : mword 20)))]> m) with A1.
    assert (Hp3c : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x38) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x3c)) by pcstep.
    iEval (rewrite Hp3c) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.allocproc + 0x3c)) ap_a0 ap_a0 (mword_of_int 2174 : mword 12) A1 av false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
    { iApply (api_3c with "Htext"). }
    iIntros (CID2 Hs2c) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 := <[Regidx ap_a0 := regval_into_reg
        (add_vec (A1 !!! Regidx ap_a0) (sign_extend' 64 (mword_of_int 2174 : mword 12)))]> A1).
    change (<[Regidx ap_a0 := regval_into_reg
        (add_vec (A1 !!! Regidx ap_a0) (sign_extend' 64 (mword_of_int 2174 : mword 12)))]> A1) with A2.
    assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x40)) by pcstep.
    iEval (rewrite Hp40) in "Hpc".
    assert (HA2a0 : A2 !!! Regidx ap_a0 = alp_pid_lock).
    { rewrite /A2 upd_eq /A1 upd_eq. exact ap_pidlk_reloc1. }
    (* +0x40 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.allocproc + 0x40)) ap_ra (mword_of_int 2093210 : mword 21) A2 av false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (api_40 with "Htext"). }
    iIntros (CID3 Hs3c) "Hcg Hpc".
    set (A3 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0x40) : mword 64) 4)]> A2).
    change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0x40) : mword 64) 4)]> A2) with A3.
    assert (Hjacq : add_vec (mword_of_int (KernelSyms.allocproc + 0x40) : mword 64) (sign_extend' 64 (mword_of_int 2093210 : mword 21)) = mword_of_int KernelSyms.acquire)
      by pcstep.
    iEval (rewrite Hjacq) in "Hpc".
    assert (HA3ra : A3 !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0x40) : mword 64) 4) by (rewrite /A3 upd_eq; reflexivity).
    assert (HA3a0 : A3 !!! Regidx ap_a0 = alp_pid_lock) by (rewrite /A3 upd_ne; [exact HA2a0 | vm_compute; discriminate]).
    assert (HA3s1 : A3 !!! Regidx ap_s1 = proc_addr k).
    { unfold A3, A2, A1. peel_ne. exact Hs1. }
    assert (HA3cs : callee_saved m A3).
    { unfold A3, A2, A1. cs_ins. apply callee_saved_refl. }
    iDestruct (cpu_own_transport CID CID3 n eb p false ltac:(wp_next_chain) with "Hcpu") as "Hcpu".
    iApply (Acquire.wp_acquire_sconf KT1 γp "nextpid"%string nextpid_res_at A3 n eb p av false lks
              Hn Hav Hbelow with "Hcg Hcpu Htext Hpc [Hislock]").
    all: try lkbelow.
    { iEval (rewrite HA3a0). iExact "Hislock". }
    iIntros (CIDacq Hsacq ms macq) "%Hmsf Hcg Hpc %Hcsacq Hlocked HR _ Hcpu Hpay".
    (* ============ THE CRITICAL SECTION: index [false], hart [CIDacq] ============ *)
    assert (Hp44 : ret_pc (A3 !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0x44))
      by (rewrite HA3ra; pcstep).
    iEval (rewrite Hp44) in "Hpc".
    assert (Hacq_s1 : macq !!! Regidx ap_s1 = proc_addr k).
    { rewrite (callee_saved_lookup Hcsacq ap_s1 ltac:(vm_compute; reflexivity)). exact HA3s1. }
    assert (Hacq_cs : callee_saved m macq) by exact (callee_saved_trans _ _ _ HA3cs Hcsacq).
    iDestruct "HR" as "[Hnp (%pids & %PR & [%Hplen %Hpdom] & Hshares & Hauth)]".
    iDestruct "Hnp" as (nv0) "[Hnp %Hnv0]".
    (* THE FIRST CANDIDATE IS THE COUNTER, and the payload's bound is what
       founds the retry loop's invariant: [1 <= nextpid <= PIDMAX]. *)
    (* +0x44 auipc a3,0x8 ; +0x48 lw a3,1824(a3) : pid := nextpid *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.allocproc + 0x44)) ap_a3 (mword_of_int 8 : mword 20) macq (trap_res false + av)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
    { iApply (api_44 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (B1 := <[Regidx ap_a3 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.allocproc + 0x44) : mword 64) (auipc_off (mword_of_int 8 : mword 20)))]> macq).
    change (<[Regidx ap_a3 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.allocproc + 0x44) : mword 64) (auipc_off (mword_of_int 8 : mword 20)))]> macq) with B1.
    assert (Hp48 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x44) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x48)) by pcstep.
    iEval (rewrite Hp48) in "Hpc".
    assert (Hnaddr1 : add_vec (B1 !!! Regidx ap_a3) (sign_extend' 64 (mword_of_int 1838 : mword 12)) = alp_nextpid).
    { rewrite /B1 upd_eq. exact ap_nextpid_reloc1. }
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.allocproc + 0x48)) ap_a3 ap_a3
              (mword_of_int 1838 : mword 12) B1 (trap_res false + av)%nat nv0 false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc [] [Hnp]").
    { iApply (api_48 with "Htext"). }
    { iEval (rgne; rewrite Hnaddr1). iExact "Hnp". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hnp".
    iEval (rgne; rewrite Hnaddr1) in "Hnp".
    set (B2 := <[Regidx ap_a3 := regval_into_reg (sign_extend' 64 (nv0 : mword 32))]> B1).
    change (<[Regidx ap_a3 := regval_into_reg (sign_extend' 64 (nv0 : mword 32))]> B1) with B2.
    assert (Hp4c : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x48) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x4c)) by pcstep.
    iEval (rewrite Hp4c) in "Hpc".
    (* +0x4c li a6,1000 ; +0x50 c.li a0,1 : PIDMAX and the wrap-around value *)
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.allocproc + 0x4c)) ap_a6 (mword_of_int 1000 : mword 12) ap_c1000 B2 (trap_res false + av)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl with "Hcg Hpc []").
    { iApply (api_4c with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (B3 := <[Regidx ap_a6 := regval_into_reg ap_c1000]> B2).
    change (<[Regidx ap_a6 := regval_into_reg ap_c1000]> B2) with B3.
    assert (Hp50 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x4c) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x50)) by pcstep.
    iEval (rewrite Hp50) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.allocproc + 0x50)) ap_a0 (mword_of_int 1 : mword 6) ap_c1 B3 (trap_res false + av)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl with "Hcg Hpc []").
    { iApply (api_50 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (B4 := <[Regidx ap_a0 := regval_into_reg ap_c1]> B3).
    change (<[Regidx ap_a0 := regval_into_reg ap_c1]> B3) with B4.
    assert (Hp52 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x52)) by pcstep.
    iEval (rewrite Hp52) in "Hpc".
    (* +0x52 auipc a2,0x16 ; +0x56 addi a2,a2,1670 : a2 := &proc[NPROC] *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.allocproc + 0x52)) ap_a2 (mword_of_int 22 : mword 20) B4 (trap_res false + av)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
    { iApply (api_52 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (B5 := <[Regidx ap_a2 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.allocproc + 0x52) : mword 64) (auipc_off (mword_of_int 22 : mword 20)))]> B4).
    change (<[Regidx ap_a2 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.allocproc + 0x52) : mword 64) (auipc_off (mword_of_int 22 : mword 20)))]> B4) with B5.
    assert (Hp56 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x52) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x56)) by pcstep.
    iEval (rewrite Hp56) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.allocproc + 0x56)) ap_a2 ap_a2 (mword_of_int 1684 : mword 12) B5 (trap_res false + av)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
    { iApply (api_56 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B6 := <[Regidx ap_a2 := regval_into_reg
        (add_vec (B5 !!! Regidx ap_a2) (sign_extend' 64 (mword_of_int 1684 : mword 12)))]> B5).
    change (<[Regidx ap_a2 := regval_into_reg
        (add_vec (B5 !!! Regidx ap_a2) (sign_extend' 64 (mword_of_int 1684 : mword 12)))]> B5) with B6.
    assert (Hp5a : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x56) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x5a)) by pcstep.
    iEval (rewrite Hp5a) in "Hpc".
    assert (HB6regs : ap_pid_regs m k B6).
    { split; [| split; [| split; [| split]]].
      - unfold B6, B5, B4, B3, B2, B1. peel_ne. exact Hacq_s1.
      - unfold B6, B5, B4. peel_ne. rewrite upd_eq. reflexivity.
      - unfold B6, B5, B4, B3. peel_ne. rewrite upd_eq. reflexivity.
      - rewrite /B6 upd_eq /B5 upd_eq. exact ap_procend_reloc.
      - unfold B6, B5, B4, B3, B2, B1. cs_ins. exact Hacq_cs. }
    (* +0x5a c.j +0x62 : into the loop *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.allocproc + 0x5a))
              (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0"))) B6 (trap_res false + av)%nat false
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (api_5a with "Htext"). }
    iApply wp_next_off_intro. iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt62 : add_vec (mword_of_int (KernelSyms.allocproc + 0x5a) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.allocproc + 0x62)) by pcstep.
    iEval (rewrite Htgt62) in "Hpc".
    (* ===================== THE RETRY LOOP, +0x62 (iLöb) ===================== *)
    (* The invariant is stated as a [wp_next] over a FRESH hart, the tree's
       idiom for every loop: it is what makes the hart-indexed resources
       inside it resolve to that binder rather than to whichever [CpuId]
       happens to be newest in the context.  The section runs at a fixed
       hart, so every instantiation below is by [reflexivity] through
       [wp_next_chain]. *)
    iAssert (wp_next (CID0 := CIDacq) false p (fun (CIDl : CpuId) =>
        ∀ (R : regfile) (nv : mword 32),
        ⌜ ap_pid_regs m k R ⌝ -∗
        (* THE CANDIDATE IS IN [1, PIDMAX].  The loop's one new invariant:
           the first candidate is the counter, which the payload bounds, and
           every retry copies a1, which the PIDMAX test bounds. *)
        ⌜ (1 <= bv_unsigned (R !!! Regidx ap_a3 : mword 64) <= PIDMAX)%Z ⌝ -∗
        sie_cap_gpr KT1 R (trap_res false + av)%nat false p -∗
        pc_is (mword_of_int (KernelSyms.allocproc + 0x62) : mword 64) -∗
        alp_nextpid ↦₄ nv -∗
        ([∗ list] i ↦ pv ∈ pids, pid_lock_share_at cur_ctx (proc_addr i) pv) -∗
        pid_reg_auth PR -∗
        slot_gen (proc_addr k) (DfracOwn 1) g0 -∗
        locked γp cpu_id -∗
        cpu_own (S n) eb p false ({["nextpid"]} ∪ lks) -∗
        arm_pay KT1 n eb p -∗
        p_pid (proc_addr k) ↦₄{DfracOwn (1/4)} pidi -∗
        p_pid (proc_addr k) ↦₄{DfracOwn (1/2)} pidh -∗
        wp_next (CID0 := CID) false p (fun (CIDc : CpuId) => ap_pid_post (CID := CIDc) m k av n eb p lks) -∗
        WP (Loop : expr riscv_lang)))%I with "[]" as "Hloop".
    { iLöb as "IH".
      iIntros (CIDl Hsl R nv) "%HR %HRa3 Hcg Hpc Hnp Hshares Hauth Hsg Hlocked Hcpu Hpay Hpidi Hpidh Hcont".
      (* +0x62 c.mv a1,a0 : the next counter value defaults to 1 (the wrap) *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.allocproc + 0x62)) ap_a1 ap_a0 R (trap_res false + av)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
      { iApply (api_62 with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
      set (R1 := <[Regidx ap_a1 := regval_into_reg (add_vec zero_reg (R !!! Regidx ap_a0))]> R).
      change (<[Regidx ap_a1 := regval_into_reg (add_vec zero_reg (R !!! Regidx ap_a0))]> R) with R1.
      assert (Hp64 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x64)) by pcstep.
      iEval (rewrite Hp64) in "Hpc".
      assert (HR1 : ap_pid_regs m k R1) by (unfold R1; regs_ins HR).
      assert (HR1a3 : R1 !!! Regidx ap_a3 = R !!! Regidx ap_a3)
        by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
      (* THE MERGE POINT +0x6c.  The two arms of the PIDMAX test differ only
         in a1 (1, or pid + 1), and the only thing downstream reads about it
         is its INTERVAL -- the exit stores it into <nextpid>, whose payload
         carries [1, PIDMAX], and a retry copies it into a3, where the loop
         invariant carries the same.  So the rest of the iteration is one
         block over an a1-generic map that knows only the bound. *)
      iAssert (wp_next (CID0 := CIDl) false p (fun (CIDm : CpuId) =>
          ∀ (Rm : regfile),
          ⌜ ap_pid_regs m k Rm /\ Rm !!! Regidx ap_a3 = R1 !!! Regidx ap_a3 /\
            (1 <= bv_unsigned (Rm !!! Regidx ap_a1 : mword 64) <= PIDMAX)%Z ⌝ -∗
          sie_cap_gpr KT1 Rm (trap_res false + av)%nat false p -∗
          pc_is (mword_of_int (KernelSyms.allocproc + 0x6c) : mword 64) -∗
          alp_nextpid ↦₄ nv -∗
          ([∗ list] i ↦ pv ∈ pids, pid_lock_share_at cur_ctx (proc_addr i) pv) -∗
          pid_reg_auth PR -∗
          slot_gen (proc_addr k) (DfracOwn 1) g0 -∗
          locked γp cpu_id -∗
          cpu_own (S n) eb p false ({["nextpid"]} ∪ lks) -∗
          arm_pay KT1 n eb p -∗
          p_pid (proc_addr k) ↦₄{DfracOwn (1/4)} pidi -∗
          p_pid (proc_addr k) ↦₄{DfracOwn (1/2)} pidh -∗
          wp_next (CID0 := CID) false p (fun (CIDc : CpuId) => ap_pid_post (CID := CIDc) m k av n eb p lks) -∗
          WP (Loop : expr riscv_lang)))%I with "[]" as "Hbody".
      { iIntros (CIDm Hsm Rm) "(%HRm & %HRma3 & %HRma1) Hcg Hpc Hnp Hshares Hauth Hsg Hlocked Hcpu Hpay Hpidi Hpidh Hcont".
        (* +0x6c auipc a5,0x11 ; +0x70 addi a5,a5,-916 : q := proc *)
        iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.allocproc + 0x6c)) ap_a5 (mword_of_int 17 : mword 20) Rm (trap_res false + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
        { iApply (api_6c with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (Rb := <[Regidx ap_a5 := regval_into_reg
            (add_vec (mword_of_int (KernelSyms.allocproc + 0x6c) : mword 64) (auipc_off (mword_of_int 17 : mword 20)))]> Rm).
        change (<[Regidx ap_a5 := regval_into_reg
            (add_vec (mword_of_int (KernelSyms.allocproc + 0x6c) : mword 64) (auipc_off (mword_of_int 17 : mword 20)))]> Rm) with Rb.
        assert (Hp70 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x6c) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x70)) by pcstep.
        iEval (rewrite Hp70) in "Hpc".
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.allocproc + 0x70)) ap_a5 ap_a5 (mword_of_int 3194 : mword 12) Rb (trap_res false + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
        { iApply (api_70 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
        set (Rc := <[Regidx ap_a5 := regval_into_reg
            (add_vec (Rb !!! Regidx ap_a5) (sign_extend' 64 (mword_of_int 3194 : mword 12)))]> Rb).
        change (<[Regidx ap_a5 := regval_into_reg
            (add_vec (Rb !!! Regidx ap_a5) (sign_extend' 64 (mword_of_int 3194 : mword 12)))]> Rb) with Rc.
        assert (Hp74 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x70) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x74)) by pcstep.
        iEval (rewrite Hp74) in "Hpc".
        assert (HRc_a5 : Rc !!! Regidx ap_a5 = proc_addr 0).
        { rewrite /Rc upd_eq /Rb upd_eq. exact ap_proc_reloc. }
        assert (HRb : ap_pid_regs m k Rb) by (unfold Rb; regs_ins HRm).
        assert (HRc : ap_pid_regs m k Rc) by (unfold Rc; regs_ins HRb).
        assert (HRca3 : Rc !!! Regidx ap_a3 = R1 !!! Regidx ap_a3).
        { unfold Rc, Rb. peel_ne. exact HRma3. }
        assert (HRca1 : Rc !!! Regidx ap_a1 = Rm !!! Regidx ap_a1).
        { unfold Rc, Rb. peel_ne. reflexivity. }
        (* ---- THE SCAN, +0x74 .. +0x7e: a fuel induction over proc[] ---- *)
        iAssert (wp_next (CID0 := CIDm) false p (fun (CIDs : CpuId) =>
            ∀ (fuel j : nat) (Rj : regfile),
            ⌜(NPROC - j <= fuel)%nat⌝ -∗ ⌜(j < NPROC)%nat⌝ -∗
            ⌜ ap_pid_regs m k Rj /\ Rj !!! Regidx ap_a3 = R1 !!! Regidx ap_a3 /\
              Rj !!! Regidx ap_a1 = Rm !!! Regidx ap_a1 /\ Rj !!! Regidx ap_a5 = proc_addr j ⌝ -∗
            (* WHAT THE SCAN HAS PROVED SO FAR: no slot it has already read
               holds the candidate.  This is the whole point of the loop and
               the only thing the exit needs -- a pid no slot holds is a key
               <pid_lock>'s register does not have
               ([SlotGen.pid_reg_dom_fresh]), so the registration at the
               store below is an insert. *)
            ⌜ forall i : nat, (i < j)%nat ->
                pids !! i <> Some (trunc32 (R !!! Regidx ap_a3)) ⌝ -∗
            sie_cap_gpr KT1 Rj (trap_res false + av)%nat false p -∗
            pc_is (mword_of_int (KernelSyms.allocproc + 0x74) : mword 64) -∗
            alp_nextpid ↦₄ nv -∗
            ([∗ list] i ↦ pv ∈ pids, pid_lock_share_at cur_ctx (proc_addr i) pv) -∗
            pid_reg_auth PR -∗
            slot_gen (proc_addr k) (DfracOwn 1) g0 -∗
            locked γp cpu_id -∗
            cpu_own (S n) eb p false ({["nextpid"]} ∪ lks) -∗
            arm_pay KT1 n eb p -∗
            p_pid (proc_addr k) ↦₄{DfracOwn (1/4)} pidi -∗
            p_pid (proc_addr k) ↦₄{DfracOwn (1/2)} pidh -∗
            wp_next (CID0 := CID) false p (fun (CIDc : CpuId) => ap_pid_post (CID := CIDc) m k av n eb p lks) -∗
            WP (Loop : expr riscv_lang)))%I with "[]" as "Hscan".
        { iIntros (CIDs Hss fuel). iInduction fuel as [|fuel] "IHf".
          { iIntros (j Rj) "%Hfuel %Hj _ _ _ _ _ _ _ _ _ _ _ _ _". exfalso. exact (ap_fuel0 j Hfuel Hj). }
          iIntros (j Rj) "%Hfuel %Hj (%HRj & %HRja3 & %HRja1 & %HRja5) %Hfresh Hcg Hpc Hnp Hshares Hauth Hsg Hlocked Hcpu Hpay Hpidi Hpidh Hcont".
          pose proof HRj as (HRjs1 & _ & _ & HRja2 & _).
          (* +0x74 c.lw a4,48(a5) : q->pid, read out of the lock's quarter *)
          assert (Hsj : is_Some (pids !! j))
            by (apply lookup_lt_is_Some_2; rewrite Hplen; exact Hj).
          destruct Hsj as [pv Hpvj].
          iDestruct (big_sepL_lookup_acc _ pids j pv Hpvj with "Hshares") as "[Hshj Hshback]".
          rewrite /pid_lock_share_at.
          assert (Hqaddr : add_vec (Rj !!! Regidx ap_a5) (sign_extend' 64 (mword_of_int 48 : mword 12)) = p_pid (proc_addr j))
            by (rewrite HRja5; apply ap_off_48).
          iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.allocproc + 0x74)) ap_a4 ap_a5
                    (mword_of_int 48 : mword 12) Rj (trap_res false + av)%nat pv false (dqm := DfracOwn (1/4))
                    ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc [] [Hshj]").
          { iApply (api_74 with "Htext"). }
          { iEval (rgne; rewrite Hqaddr). iExact "Hshj". }
          iApply wp_next_off_intro. iIntros "Hcg Hpc Hshj".
          iEval (rgne; rewrite Hqaddr) in "Hshj".
          iDestruct ("Hshback" with "[Hshj]") as "Hshares".
          { rewrite /pid_lock_share_at. iExact "Hshj". }
          set (Rd := <[Regidx ap_a4 := regval_into_reg (sign_extend' 64 (pv : mword 32))]> Rj).
          change (<[Regidx ap_a4 := regval_into_reg (sign_extend' 64 (pv : mword 32))]> Rj) with Rd.
          assert (Hp76 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x74) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x76)) by pcstep.
          iEval (rewrite Hp76) in "Hpc".
          assert (HRd : ap_pid_regs m k Rd) by (unfold Rd; regs_ins HRj).
          assert (HRda3 : Rd !!! Regidx ap_a3 = R1 !!! Regidx ap_a3) by (rewrite /Rd upd_ne; [exact HRja3 | vm_compute; discriminate]).
          assert (HRda1 : Rd !!! Regidx ap_a1 = Rm !!! Regidx ap_a1) by (rewrite /Rd upd_ne; [exact HRja1 | vm_compute; discriminate]).
          assert (HRda5 : Rd !!! Regidx ap_a5 = proc_addr j) by (rewrite /Rd upd_ne; [exact HRja5 | vm_compute; discriminate]).
          assert (HRda2 : Rd !!! Regidx ap_a2 = proc_addr NPROC) by (rewrite /Rd upd_ne; [exact HRja2 | vm_compute; discriminate]).
          (* +0x76 beq a4,a3 -> +0x5c : does this slot hold the candidate? *)
          destruct (eq_vec (rget (CID := CIDs) Rd ap_a4) (rget (CID := CIDs) Rd ap_a3)) eqn:Hcmp.
          - (* IN USE: retry with pid := the next counter value *)
            iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.allocproc + 0x76)) (mword_of_int 8166 : mword 13) ap_a3 ap_a4 Rd (trap_res false + av)%nat false
                      ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp ltac:(vm_compute; reflexivity)
                      with "Hcg Hpc []").
            { iApply (api_76 with "Htext"). }
            iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
            assert (Htgt5c : add_vec (mword_of_int (KernelSyms.allocproc + 0x76) : mword 64) (sign_extend' 64 (mword_of_int 8166 : mword 13))
                             = mword_of_int (KernelSyms.allocproc + 0x5c)) by pcstep.
            iEval (rewrite Htgt5c) in "Hpc".
            (* +0x5c beq a5,a2 -> +0x82 : NOT taken -- q is a real slot *)
            assert (Hfall5c : eq_vec (rget (CID := CIDs) Rd ap_a5) (rget (CID := CIDs) Rd ap_a2) = false).
            { rgne; rgne. rewrite HRda5 HRda2. exact (ap_end_lt j Hj). }
            iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.allocproc + 0x5c)) (mword_of_int 38 : mword 13) ap_a2 ap_a5 Rd (trap_res false + av)%nat false
                      ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hfall5c with "Hcg Hpc []").
            { iApply (api_5c with "Htext"). }
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            assert (Hp60 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x5c) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x60)) by pcstep.
            iEval (rewrite Hp60) in "Hpc".
            (* +0x60 c.mv a3,a1 : pid := next *)
            iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.allocproc + 0x60)) ap_a3 ap_a1 Rd (trap_res false + av)%nat false
                      ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
            { iApply (api_60 with "Htext"). }
            iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
            set (Re := <[Regidx ap_a3 := regval_into_reg (add_vec zero_reg (Rd !!! Regidx ap_a1))]> Rd).
            change (<[Regidx ap_a3 := regval_into_reg (add_vec zero_reg (Rd !!! Regidx ap_a1))]> Rd) with Re.
            assert (Hp62 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x60) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x62)) by pcstep.
            iEval (rewrite Hp62) in "Hpc".
            assert (HRe : ap_pid_regs m k Re) by (unfold Re; regs_ins HRd).
            (* the retry re-establishes the loop's invariant from a1's *)
            assert (HRea3 : (1 <= bv_unsigned (Re !!! Regidx ap_a3 : mword 64) <= PIDMAX)%Z).
            { rewrite /Re upd_eq add_vec_zero_l HRda1. exact HRma1. }
            iSpecialize ("IH" $! CIDs with "[%]"); [wp_next_chain |].
            iApply ("IH" $! Re nv with "[%] [%] Hcg Hpc Hnp Hshares Hauth Hsg Hlocked Hcpu Hpay Hpidi Hpidh Hcont").
            + exact HRe.
            + exact HRea3.
          - (* not this slot: q++ *)
            (* ...AND THE SCAN LEARNS IT.  The fall-through is [q->pid <> pid]
               on the whole 64-bit registers; the cell holds 32 bits and the
               candidate is inside [1, PIDMAX], so the two are the same
               statement ([ap_sext_trunc]). *)
            assert (Hnej : pv <> trunc32 (R !!! Regidx ap_a3)).
            { intro Hpv. apply eq_vec_false_iff in Hcmp. apply Hcmp.
              rgne; rgne. rewrite HRda3 HR1a3 /Rd upd_eq Hpv.
              exact (ap_sext_trunc (R !!! Regidx ap_a3) (proj2 HRa3)). }
            assert (Hfresh' : forall i : nat, (i < S j)%nat ->
                      pids !! i <> Some (trunc32 (R !!! Regidx ap_a3))).
            { intros i Hi. destruct (decide (i = j)) as [-> | Hij].
              - rewrite Hpvj. intro Hc. injection Hc as Hc. exact (Hnej Hc).
              - apply Hfresh. lia. }
            iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.allocproc + 0x76)) (mword_of_int 8166 : mword 13) ap_a3 ap_a4 Rd (trap_res false + av)%nat false
                      ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp with "Hcg Hpc []").
            { iApply (api_76 with "Htext"). }
            iApply wp_next_off_intro. iIntros "Hcg Hpc".
            assert (Hp7a : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x76) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x7a)) by pcstep.
            iEval (rewrite Hp7a) in "Hpc".
            (* +0x7a addi a5,a5,360 *)
            iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.allocproc + 0x7a)) ap_a5 ap_a5 (mword_of_int 360 : mword 12) Rd (trap_res false + av)%nat false
                      ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
            { iApply (api_7a with "Htext"). }
            iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
            set (Rf := <[Regidx ap_a5 := regval_into_reg
                (add_vec (Rd !!! Regidx ap_a5) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> Rd).
            change (<[Regidx ap_a5 := regval_into_reg
                (add_vec (Rd !!! Regidx ap_a5) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> Rd) with Rf.
            assert (Hp7e : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x7a) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x7e)) by pcstep.
            iEval (rewrite Hp7e) in "Hpc".
            assert (HRf_a5 : Rf !!! Regidx ap_a5 = proc_addr (S j)).
            { rewrite /Rf upd_eq HRda5. exact (proc_addr_succ j). }
            assert (HRf : ap_pid_regs m k Rf) by (unfold Rf; regs_ins HRd).
            assert (HRfa3 : Rf !!! Regidx ap_a3 = R1 !!! Regidx ap_a3) by (rewrite /Rf upd_ne; [exact HRda3 | vm_compute; discriminate]).
            assert (HRfa1 : Rf !!! Regidx ap_a1 = Rm !!! Regidx ap_a1) by (rewrite /Rf upd_ne; [exact HRda1 | vm_compute; discriminate]).
            assert (HRfa2 : Rf !!! Regidx ap_a2 = proc_addr NPROC) by (rewrite /Rf upd_ne; [exact HRda2 | vm_compute; discriminate]).
            (* +0x7e bne a5,a2 -> +0x74 *)
            destruct (Nat.eqb (S j) NPROC) eqn:Hend.
            + (* THE TABLE IS EXHAUSTED WITHOUT A MATCH: [pid] is free.  Fall to +0x82. *)
              apply Nat.eqb_eq in Hend.
              assert (Hfall : neq_vec (rget (CID := CIDs) Rf ap_a5) (rget (CID := CIDs) Rf ap_a2) = false).
              { rgne; rgne. rewrite HRf_a5 HRfa2 Hend. exact ap_neq_end_eq. }
              iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.allocproc + 0x7e)) (mword_of_int 8182 : mword 13) ap_a2 ap_a5 Rf (trap_res false + av)%nat false
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hfall with "Hcg Hpc []").
              { iApply (api_7e with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc".
              assert (Hp82 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x7e) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x82)) by pcstep.
              iEval (rewrite Hp82) in "Hpc".
              (* ========== THE EXIT: nextpid := next, p->pid := pid, release ========== *)
              (* +0x82 auipc a5,0x8 ; +0x86 sw a1,1762(a5) *)
              iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.allocproc + 0x82)) ap_a5 (mword_of_int 8 : mword 20) Rf (trap_res false + av)%nat false
                        ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
              { iApply (api_82 with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc".
              set (Rg := <[Regidx ap_a5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.allocproc + 0x82) : mword 64) (auipc_off (mword_of_int 8 : mword 20)))]> Rf).
              change (<[Regidx ap_a5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.allocproc + 0x82) : mword 64) (auipc_off (mword_of_int 8 : mword 20)))]> Rf) with Rg.
              assert (Hp86 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x82) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x86)) by pcstep.
              iEval (rewrite Hp86) in "Hpc".
              assert (Hnaddr2 : add_vec (Rg !!! Regidx ap_a5) (sign_extend' 64 (mword_of_int 1776 : mword 12)) = alp_nextpid).
              { rewrite /Rg upd_eq. exact ap_nextpid_reloc2. }
              iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.allocproc + 0x86)) ap_a1 ap_a5
                        (mword_of_int 1776 : mword 12) Rg (trap_res false + av)%nat nv false with "Hcg Hpc [] [Hnp]").
              { iApply (api_86 with "Htext"). }
              { iEval (rgne; rewrite Hnaddr2). iExact "Hnp". }
              iApply wp_next_off_intro. iIntros "Hcg Hpc Hnp".
              iEval (rgne; rewrite Hnaddr2) in "Hnp".
              assert (Hp8a : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x86) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x8a)) by pcstep.
              iEval (rewrite Hp8a) in "Hpc".
              (* +0x8a c.sw a3,48(s1) : p->pid = pid.  All three pieces of the cell:
                 the caller's quarter and half, and the lock's quarter for slot k. *)
              assert (Hskk : is_Some (pids !! k))
                by (apply lookup_lt_is_Some_2; rewrite Hplen; exact Hk).
              destruct Hskk as [pk Hsk].
              iDestruct (big_sepL_insert_acc _ pids k pk Hsk with "Hshares") as "[Hshk Hshback]".
              rewrite /pid_lock_share_at. iRename "Hshk" into "Hpidk".
              iDestruct (p_pid_join3 (proc_addr k) pidi pidh pk with "Hpidi Hpidh Hpidk") as "[%Hpeq Hpidf]".
              assert (HRg_s1 : Rg !!! Regidx ap_s1 = proc_addr k).
              { destruct HRf as (HRfs1 & _). rewrite /Rg upd_ne; [exact HRfs1 | vm_compute; discriminate]. }
              assert (Hpaddr : add_vec (Rg !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 48 : mword 12)) = p_pid (proc_addr k))
                by (rewrite HRg_s1; apply ap_off_48).
              iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.allocproc + 0x8a)) ap_a3 ap_s1
                        (mword_of_int 48 : mword 12) Rg (trap_res false + av)%nat pidi false with "Hcg Hpc [] [Hpidf]").
              { iApply (api_8a with "Htext"). }
              { iEval (rgne; rewrite Hpaddr). iExact "Hpidf". }
              iApply wp_next_off_intro. iIntros "Hcg Hpc Hpidf".
              iEval (rgne; rewrite Hpaddr) in "Hpidf".
              set (pidn := trunc32 (Rg !!! Regidx ap_a3)).
              (* ...and the pid the block chose, at the same interval: a3 has
                 not moved since the loop head, where the invariant bounds it *)
              assert (HRga3 : Rg !!! Regidx ap_a3 = R !!! Regidx ap_a3).
              { rewrite /Rg upd_ne; [| vm_compute; discriminate].
                rewrite HRfa3. exact HR1a3. }
              assert (Hpidnb : (1 <= bv_unsigned pidn <= PIDMAX)%Z).
              { rewrite /pidn HRga3 (ap_trunc_val (R !!! Regidx ap_a3) (proj2 HRa3)).
                exact HRa3. }
              iDestruct (p_pid_split3 with "Hpidf") as "(Hpidi & Hpidh & Hpidk)".
              iDestruct ("Hshback" $! pidn with "[Hpidk]") as "Hshares".
              { rewrite /pid_lock_share_at. iExact "Hpidk". }
              (* the payload's bound, re-established at the value the [sw]
                 stored: a1 is inside the interval and the truncation to the
                 cell's 32 bits does not move it *)
              assert (HRga1 : Rg !!! Regidx ap_a1 = Rm !!! Regidx ap_a1)
                by (rewrite /Rg upd_ne; [exact HRfa1 | vm_compute; discriminate]).
              assert (Hnvb : (1 <= bv_unsigned (trunc32 (Rg !!! Regidx ap_a1)) <= PIDMAX)%Z).
              { rewrite HRga1 (ap_trunc_val (Rm !!! Regidx ap_a1) (proj2 HRma1)).
                exact HRma1. }
              (* ================= THE INCARNATION IS MINTED HERE =================
                 The scan proved the candidate is in no slot, so it is a key
                 the register does not have ([SlotGen.pid_reg_dom_fresh]) and
                 the registration is an INSERT.  The generation is minted at
                 the same point because it is the only one where both halves
                 of what it pins exist: the pid is in hand and the name is
                 what the registration is keyed to. *)
              assert (Hnotin : (pidn : mword 32) ∉ pids).
              { rewrite /pidn HRga3. intro Hin.
                apply elem_of_list_lookup in Hin as [i Hi].
                assert (Hilt : (i < NPROC)%nat)
                  by (apply lookup_lt_Some in Hi; rewrite Hplen in Hi; exact Hi).
                exact (Hfresh' i ltac:(lia) Hi). }
              assert (Hfree : PR !! bv_unsigned pidn = None)
                by exact (pid_reg_dom_fresh PR pids pidn Hpdom Hnotin).
              (* the slot's cell held 0 before the store -- the dormant block
                 this slot came out of says so -- which is what keeps the
                 register's domain fact true across it *)
              assert (Hpk0 : bv_unsigned pk = 0)
                by (rewrite -(proj2 Hpeq); exact Hpid0).
              iApply fupd_wp.
              iMod (gen_alloc (proc_addr k) pidn) as (γg) "Hgen".
              iMod (slot_gen_update (proc_addr k) g0 γg with "Hsg") as "Hsg".
              iMod (pid_reg_insert PR pidn γg Hfree with "Hauth") as "[Hauth Hpr]".
              iModIntro.
              iAssert nextpid_res with "[Hnp Hshares Hauth]" as "HR".
              { rewrite /nextpid_res /nextpid_res_at. iSplitL "Hnp".
                { iExists _. iSplitL "Hnp"; [iExact "Hnp" | iPureIntro; exact Hnvb]. }
                iExists (<[k := pidn]> pids), (<[bv_unsigned pidn := γg]> PR).
                iFrame "Hshares Hauth". iPureIntro. split.
                - rewrite length_insert. exact Hplen.
                - apply (pid_reg_dom_insert PR pids k pk pidn γg Hpdom Hsk Hpk0).
                  lia. }
              assert (Hp8c : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x8a) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x8c)) by pcstep.
              iEval (rewrite Hp8c) in "Hpc".
              (* +0x8c auipc a0,0x11 ; +0x90 addi a0,a0,-2020 : a0 := &pid_lock *)
              iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.allocproc + 0x8c)) ap_a0 (mword_of_int 17 : mword 20) Rg (trap_res false + av)%nat false
                        ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
              { iApply (api_8c with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc".
              set (Rh := <[Regidx ap_a0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.allocproc + 0x8c) : mword 64) (auipc_off (mword_of_int 17 : mword 20)))]> Rg).
              change (<[Regidx ap_a0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.allocproc + 0x8c) : mword 64) (auipc_off (mword_of_int 17 : mword 20)))]> Rg) with Rh.
              assert (Hp90 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x8c) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x90)) by pcstep.
              iEval (rewrite Hp90) in "Hpc".
              iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.allocproc + 0x90)) ap_a0 ap_a0 (mword_of_int 2090 : mword 12) Rh (trap_res false + av)%nat false
                        ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
              { iApply (api_90 with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
              set (Ri := <[Regidx ap_a0 := regval_into_reg
                  (add_vec (Rh !!! Regidx ap_a0) (sign_extend' 64 (mword_of_int 2090 : mword 12)))]> Rh).
              change (<[Regidx ap_a0 := regval_into_reg
                  (add_vec (Rh !!! Regidx ap_a0) (sign_extend' 64 (mword_of_int 2090 : mword 12)))]> Rh) with Ri.
              assert (Hp94 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x90) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x94)) by pcstep.
              iEval (rewrite Hp94) in "Hpc".
              assert (HRia0 : Ri !!! Regidx ap_a0 = alp_pid_lock).
              { rewrite /Ri upd_eq /Rh upd_eq. exact ap_pidlk_reloc2. }
              (* +0x94 jal ra,release *)
              iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.allocproc + 0x94)) ap_ra (mword_of_int 2093262 : mword 21) Ri (trap_res false + av)%nat false
                        ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
              { iApply (api_94 with "Htext"). }
              iApply wp_next_off_intro. iIntros "Hcg Hpc".
              set (Rr := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0x94) : mword 64) 4)]> Ri).
              change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0x94) : mword 64) 4)]> Ri) with Rr.
              assert (Hjrel : add_vec (mword_of_int (KernelSyms.allocproc + 0x94) : mword 64) (sign_extend' 64 (mword_of_int 2093262 : mword 21))
                              = mword_of_int KernelSyms.release) by pcstep.
              iEval (rewrite Hjrel) in "Hpc".
              assert (HRrra : Rr !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0x94) : mword 64) 4)
                by (rewrite /Rr upd_eq; reflexivity).
              assert (HRra0 : Rr !!! Regidx ap_a0 = alp_pid_lock)
                by (rewrite /Rr upd_ne; [exact HRia0 | vm_compute; discriminate]).
              assert (HRrcs : callee_saved m Rr).
              { unfold Rr, Ri, Rh, Rg. cs_ins. destruct HRf as (_ & _ & _ & _ & HRfcs). exact HRfcs. }
              (* release spells the window index at its own exit arm ([outb]); the
                 entry index is [false] and [Hbeq] says they are the same bool *)
              assert (Htr : (trap_res false + av)%nat
                            = (trap_res (match n with O => eb | S _ => false end) + av)%nat)
                by (rewrite Hbeq; reflexivity).
              iEval (rewrite Htr) in "Hcg".
              iApply (Release.wp_release_sconf KT1 γp alp_pid_lock "nextpid"%string nextpid_res_at Rr n eb p av
                        ({["nextpid"]} ∪ lks) (ap_lka Rr HRra0) Hav
                        with "Hcg Htext Hpc Hislock Hlocked HR Hcpu Hpay").
              iIntros (CIDrel Hsrel mrel) "Hcg Hpc %Hcsrel Hcpu".
              rewrite Hbeq in Hsrel.
              iEval (rewrite Hbeq) in "Hcg".
              assert (Hsetback : ({["nextpid"]} ∪ lks) ∖ {["nextpid"]} = lks)
                by (apply locks_add_del_below; lkbelow).
              iEval (rewrite Hbeq Hsetback) in "Hcpu".
              assert (Hp98 : ret_pc (Rr !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0x98))
                by (rewrite HRrra; pcstep).
              iEval (rewrite Hp98) in "Hpc".
              (* ---- hand back: the block's whole hart chain is entry -> acquire -> release ---- *)
              iSpecialize ("Hcont" $! CIDrel with "[%]"); [wp_next_chain |].
              iEval (rewrite /ap_pid_post) in "Hcont".
              iApply ("Hcont" $! mrel pidn γg with "[%] [%] Hcg Hcpu Hpc Hpidi Hpidh Hgen Hsg Hpr").
              * exact (callee_saved_trans _ _ _ HRrcs Hcsrel).
              * exact Hpidnb.
            + (* more slots to look at: back to +0x74 *)
              assert (HjS : (S j < NPROC)%nat) by exact (ap_kS_lt j Hj Hend).
              assert (Htk : neq_vec (rget (CID := CIDs) Rf ap_a5) (rget (CID := CIDs) Rf ap_a2) = true).
              { rgne; rgne. rewrite HRf_a5 HRfa2. exact (ap_neq_end_lt (S j) HjS). }
              iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.allocproc + 0x7e)) (mword_of_int 8182 : mword 13) ap_a2 ap_a5 Rf (trap_res false + av)%nat false
                        ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Htk ltac:(vm_compute; reflexivity)
                        with "Hcg Hpc []").
              { iApply (api_7e with "Htext"). }
              iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
              assert (Htgt74 : add_vec (mword_of_int (KernelSyms.allocproc + 0x7e) : mword 64) (sign_extend' 64 (mword_of_int 8182 : mword 13))
                               = mword_of_int (KernelSyms.allocproc + 0x74)) by pcstep.
              iEval (rewrite Htgt74) in "Hpc".
              iApply ("IHf" $! (S j) Rf with "[%] [%] [%] [%] Hcg Hpc Hnp Hshares Hauth Hsg Hlocked Hcpu Hpay Hpidi Hpidh Hcont").
              * exact (ap_fuelS j fuel Hfuel).
              * exact HjS.
              * split; [exact HRf | split; [exact HRfa3 | split; [exact HRfa1 | exact HRf_a5]]].
              * exact Hfresh'. }
        (* enter the scan at q = &proc[0] *)
        iSpecialize ("Hscan" $! CIDm with "[%]"); [wp_next_chain |].
        iApply ("Hscan" $! NPROC 0%nat Rc with "[%] [%] [%] [%] Hcg Hpc Hnp Hshares Hauth Hsg Hlocked Hcpu Hpay Hpidi Hpidh Hcont").
        - exact ap_fuel_init.
        - exact ap_nproc_pos.
        - split; [exact HRc | split; [exact HRca3 | split; [exact HRca1 | exact HRc_a5]]].
        (* the scan has read nothing yet *)
        - intros i Hi. lia. }
      iSpecialize ("Hbody" $! CIDl with "[%]"); [wp_next_chain |].
      (* +0x64 beq a3,a6 -> +0x6c : pid == PIDMAX ? *)
      destruct (eq_vec (rget (CID := CIDl) R1 ap_a3) (rget (CID := CIDl) R1 ap_a6)) eqn:Hmax.
      - (* the counter wraps: next stays 1 *)
        iApply (wp_beq_taken_s_sconf (mword_of_int (KernelSyms.allocproc + 0x64)) (mword_of_int 8 : mword 13) ap_a6 ap_a3 R1 (trap_res false + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hmax ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (api_64 with "Htext"). }
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt6c : add_vec (mword_of_int (KernelSyms.allocproc + 0x64) : mword 64) (sign_extend' 64 (mword_of_int 8 : mword 13))
                         = mword_of_int (KernelSyms.allocproc + 0x6c)) by pcstep.
        iEval (rewrite Htgt6c) in "Hpc".
        (* THE WRAP ARM: a1 is still a0, i.e. 1, so the next candidate is
           inside the interval with nothing read off a3 at all. *)
        assert (HR1a1 : R1 !!! Regidx ap_a1 = add_vec zero_reg ap_c1).
        { rewrite /R1 upd_eq. destruct HR as (_ & Ha0 & _). by rewrite Ha0. }
        iApply ("Hbody" $! R1 with "[%] Hcg Hpc Hnp Hshares Hauth Hsg Hlocked Hcpu Hpay Hpidi Hpidh Hcont").
        (* [split_and!] would split the interval too, so the last conjunct is
           handed over whole (durable-notes' off-by-one). *)
        split; [exact HR1 | split; [reflexivity | ]].
        rewrite HR1a1 add_vec_zero_l ap_c1_val. unfold PIDMAX. lia.
      - (* +0x68 addiw a1,a3,1 : next := pid + 1 *)
        iApply (wp_beq_fall_s_sconf (mword_of_int (KernelSyms.allocproc + 0x64)) (mword_of_int 8 : mword 13) ap_a6 ap_a3 R1 (trap_res false + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hmax with "Hcg Hpc []").
        { iApply (api_64 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp68 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x64) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x68)) by pcstep.
        iEval (rewrite Hp68) in "Hpc".
        iApply (wp_addiw_s_sconf (mword_of_int (KernelSyms.allocproc + 0x68)) ap_a1 ap_a3 (mword_of_int 1 : mword 12) R1 (trap_res false + av)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc []").
        { iApply (api_68 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rgne) in "Hcg".
        set (R2 := <[Regidx ap_a1 := regval_into_reg
            (sign_extend' 64 (subrange_vec_dec (add_vec (R1 !!! Regidx ap_a3) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> R1).
        change (<[Regidx ap_a1 := regval_into_reg
            (sign_extend' 64 (subrange_vec_dec (add_vec (R1 !!! Regidx ap_a3) (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0))]> R1) with R2.
        assert (Hp6c : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x68) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x6c)) by pcstep.
        iEval (rewrite Hp6c) in "Hpc".
        assert (HR2 : ap_pid_regs m k R2) by (unfold R2; regs_ins HR1).
        (* THE FALL-THROUGH ARM: the candidate is not PIDMAX, so with the
           loop's invariant it is at most PIDMAX - 1 and the [addiw] lands
           inside the interval. *)
        assert (HR1a3b : (1 <= bv_unsigned (R1 !!! Regidx ap_a3 : mword 64) <= PIDMAX)%Z)
          by (rewrite HR1a3; exact HRa3).
        assert (HR1lt : (bv_unsigned (R1 !!! Regidx ap_a3 : mword 64) < PIDMAX)%Z).
        { destruct HR1 as (_ & _ & Ha6 & _).
          assert (Hne : (R1 !!! Regidx ap_a3 : mword 64) <> ap_c1000).
          { intro He. rewrite <- Ha6 in He.
            assert (Hc : eq_vec (rget (CID := CIDl) R1 ap_a3) (rget (CID := CIDl) R1 ap_a6) = true).
            { rgne; rgne. rewrite He. apply eq_vec_refl. }
            rewrite Hc in Hmax. discriminate Hmax. }
          assert (Hnev : bv_unsigned (R1 !!! Regidx ap_a3 : mword 64) <> PIDMAX).
          { intro Hv. apply Hne. apply bv_eq. rewrite Hv. by rewrite ap_c1000_val. }
          lia. }
        assert (Hpre : (1 <= bv_unsigned (R1 !!! Regidx ap_a3 : mword 64) < PIDMAX)%Z)
          by (split; [exact (proj1 HR1a3b) | exact HR1lt]).
        iApply ("Hbody" $! R2 with "[%] Hcg Hpc Hnp Hshares Hauth Hsg Hlocked Hcpu Hpay Hpidi Hpidh Hcont").
        split;
          [ exact HR2
          | split; [ rewrite /R2 upd_ne; [reflexivity | vm_compute; discriminate] | ]].
        rewrite /R2 upd_eq (ap_addiw_val (R1 !!! Regidx ap_a3) Hpre).
        unfold PIDMAX in Hpre |- *. lia. }
    iSpecialize ("Hloop" $! CIDacq with "[%]"); [wp_next_chain |].
    (* the first candidate IS the counter, at the payload's bound *)
    assert (Hnv31 : (bv_unsigned nv0 < 2 ^ 31)%Z).
    { unfold PIDMAX in Hnv0.
      assert (H31 : (2 ^ 31)%Z = 2147483648) by (vm_compute; reflexivity).
      rewrite H31. lia. }
    assert (HB6a3e : B6 !!! Regidx ap_a3 = sign_extend' 64 (nv0 : mword 32)).
    { unfold B6, B5, B4, B3, B2. peel_ne. rewrite upd_eq. reflexivity. }
    assert (HB6a3 : (1 <= bv_unsigned (B6 !!! Regidx ap_a3 : mword 64) <= PIDMAX)%Z).
    { rewrite HB6a3e (ap_sext_val nv0 Hnv31). exact Hnv0. }
    iApply ("Hloop" $! B6 nv0 with "[%] [%] Hcg Hpc Hnp Hshares Hauth Hsg Hlocked Hcpu Hpay Hpidi Hpidh Hcont").
    - exact HB6regs.
    - exact HB6a3.
  Qed.

End ProofAllocprocPid.

Section ProofAllocproc.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  (* The section's hart is called [CID0], NOT [CID]: the loop invariant, the
     epilogue and every leaf continuation bind a fresh [CID], and a section
     variable of that name would be shadowed by them -- while the lemma's own
     anchor has to stay nameable from INSIDE those lambdas (that is what
     [wp_next (CID0 := CID0)] and [wp_next_chain] compose against). *)
  Context `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}.

  Lemma wp_allocproc_core
      (γa : gname) (γk : gname * gname) (γp : gname) (γf : gname)
      (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
      (pme : mword 64) (on : option nat) (op : option nat)
      (b : bool) (lks : gset string)
    : wp_allocproc_core_body γa γk γp γf γs m lvl K eb pme on op b lks.
  Proof.
    cbv beta delta [wp_allocproc_core_body].
    intros pcE ret_tgt HK Hlvl Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs #Hpidlk Henv Hpav Hcont".
    iDestruct (procs_inv_len γs with "Hprocs") as %Hlen.
    iAssert (procs_inv γs) as "#Hpinv". { iExact "Hprocs". }
    (* ================= PROLOGUE (32-byte frame, 4 slots) ================= *)
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (HcspM1 : M1 !!! Regidx csp_rs1 = spd) by (rewrite /M1 upd_eq; reflexivity).
    assert (Hspd4 : pa_stk sp0 4 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (HraM1 : M1 !!! Regidx ap_ra = m !!! Regidx ap_ra) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0M1 : M1 !!! Regidx ap_s0 = m !!! Regidx ap_s0) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1M1 : M1 !!! Regidx ap_s1 = m !!! Regidx ap_s1) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs2M1 : M1 !!! Regidx ap_s2 = m !!! Regidx ap_s2) by (rewrite /M1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b ltac:(pose proof (ap_K4 K HK); lia) Hpush
              with "Hcg Hpc []").
    { iApply (api_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with M1.
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1c & S2c & S3c & S4c & _)".
    iDestruct "S1c" as (v1) "Hb1". iDestruct "S2c" as (v2) "Hb2".
    iDestruct "S3c" as (v3) "Hb3". iDestruct "S4c" as (v4) "Hb4".
    assert (Hslot : forall (k u : nat), (k + u = 4)%nat -> (u < 4)%nat ->
              pa_stk sp0 k = add_vec spd (zero_extend' 64 (concat_vec (mword_of_int (Z.of_nat u) : mword 6) ('b"000")))).
    { intros k u Hku Hu. rewrite -Hspd4.
      destruct u as [|[|[|[|]]]]; try lia; destruct k as [|[|[|[|[|]]]]]; try lia;
        unfold pa_stk, add_vec_int; rewrite add_vec_off2;
        f_equal; apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1a := Hslot 1%nat 3%nat ltac:(lia) ltac:(lia)).
    assert (Hb2a := Hslot 2%nat 2%nat ltac:(lia) ltac:(lia)).
    assert (Hb3a := Hslot 3%nat 1%nat ltac:(lia) ltac:(lia)).
    assert (Hb4a := Hslot 4%nat 0%nat ltac:(lia) ltac:(lia)).
    (* +0x02..+0x08: save ra/s0/s1/s2 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.allocproc + 0x02)) (mword_of_int 3 : mword 6) ap_ra M1 (K - 4)%nat v1 b
              with "Hcg Hpc [] [Hb1]").
    { iApply (api_02 with "Htext"). }
    { iEval (rewrite HcspM1 -Hb1a). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.allocproc + 0x04)) (mword_of_int 2 : mword 6) ap_s0 M1 (K - 4)%nat v2 b
              with "Hcg Hpc [] [Hb2]").
    { iApply (api_04 with "Htext"). }
    { iEval (rewrite HcspM1 -Hb2a). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.allocproc + 0x06)) (mword_of_int 1 : mword 6) ap_s1 M1 (K - 4)%nat v3 b
              with "Hcg Hpc [] [Hb3]").
    { iApply (api_06 with "Htext"). }
    { iEval (rewrite HcspM1 -Hb3a). iExact "Hb3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hb3".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.allocproc + 0x08)) (mword_of_int 0 : mword 6) ap_s2 M1 (K - 4)%nat v4 b
              with "Hcg Hpc [] [Hb4]").
    { iApply (api_08 with "Htext"). }
    { iEval (rewrite HcspM1 -Hb4a). iExact "Hb4". }
    iIntros (CID5 Hs5) "Hcg Hpc Hb4".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    iEval (rewrite HcspM1 ap_rg_ra HraM1) in "Hb1".
    iEval (rewrite HcspM1 ap_rg_s0 Hs0M1) in "Hb2".
    iEval (rewrite HcspM1 ap_rg_s1 Hs1M1) in "Hb3".
    iEval (rewrite HcspM1 ap_rg_s2 Hs2M1) in "Hb4".
    (* ================= THE SHARED EPILOGUE, +0xd2 .. +0xde ==============
       Both exits join here, but at DIFFERENT SIE indices: the found arm
       still holds p->lock (literal [false]), the null arm has released
       everything ([b]).  Hence the [xb] and [CIDt] parameters of [ap_tail].
       The epilogue hands back only the final register file; assembling
       [SpecAllocproc.allocproc_post] out of it is the ARM's job, which is
       exactly what lets the post's SIE index be per-arm. *)
    iAssert (ap_tail m spd pme ret_tgt K) with "[Hb1 Hb2 Hb3 Hb4]" as "Htail".
    { rewrite /ap_tail.
      iIntros (rsv xb CIDt Mt rv) "%Hmt Hcg Hpc Hk".
      destruct Hmt as (Htsp & Hts1 & Htrest).
      (* +0xd2 c.mv a0,s1 *)
      iApply (wp_cmv_s_sconf (CID := CIDt) (mword_of_int (KernelSyms.allocproc + 0xd2)) ap_a0 ap_s1 Mt (rsv + (K - 4))%nat xb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (api_d2 with "Htext"). }
      iIntros (CIDe1 Hse1) "Hcg Hpc".
      iEval (rewrite ap_rg_s1 Hts1) in "Hcg".
      set (E0 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg rv)]> Mt).
      change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg rv)]> Mt) with E0.
      assert (Hp7a : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xd2) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xd4)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp7a) in "Hpc".
      assert (HE0csp : E0 !!! Regidx csp_rs1 = spd)
        by (rewrite /E0 upd_ne; [exact Htsp | vm_compute; discriminate]).
      (* +0xd4 .. +0xda: restore ra/s0/s1/s2 *)
      iApply (wp_cldsp_s_sconf (CID := CIDe1) (mword_of_int (KernelSyms.allocproc + 0xd4)) (mword_of_int 3 : mword 6) ap_ra
                E0 (rsv + (K - 4))%nat (m !!! Regidx ap_ra) xb (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hb1]").
      { iApply (api_d4 with "Htext"). }
      { iEval (rewrite HE0csp). iExact "Hb1". }
      iIntros (CIDe2 Hse2) "Hcg Hpc Hb1".
      set (E1 := <[Regidx ap_ra := regval_into_reg (m !!! Regidx ap_ra)]> E0).
      change (<[Regidx ap_ra := regval_into_reg (m !!! Regidx ap_ra)]> E0) with E1.
      assert (Hp7c : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xd4) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xd6)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp7c) in "Hpc".
      assert (HE1csp : E1 !!! Regidx csp_rs1 = spd) by (rewrite /E1 upd_ne; [exact HE0csp | vm_compute; discriminate]).
      iApply (wp_cldsp_s_sconf (CID := CIDe2) (mword_of_int (KernelSyms.allocproc + 0xd6)) (mword_of_int 2 : mword 6) ap_s0
                E1 (rsv + (K - 4))%nat (m !!! Regidx ap_s0) xb (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hb2]").
      { iApply (api_d6 with "Htext"). }
      { iEval (rewrite HE1csp). iExact "Hb2". }
      iIntros (CIDe3 Hse3) "Hcg Hpc Hb2".
      set (E2 := <[Regidx ap_s0 := regval_into_reg (m !!! Regidx ap_s0)]> E1).
      change (<[Regidx ap_s0 := regval_into_reg (m !!! Regidx ap_s0)]> E1) with E2.
      assert (Hp7e : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xd6) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xd8)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp7e) in "Hpc".
      assert (HE2csp : E2 !!! Regidx csp_rs1 = spd) by (rewrite /E2 upd_ne; [exact HE1csp | vm_compute; discriminate]).
      iApply (wp_cldsp_s_sconf (CID := CIDe3) (mword_of_int (KernelSyms.allocproc + 0xd8)) (mword_of_int 1 : mword 6) ap_s1
                E2 (rsv + (K - 4))%nat (m !!! Regidx ap_s1) xb (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hb3]").
      { iApply (api_d8 with "Htext"). }
      { iEval (rewrite HE2csp). iExact "Hb3". }
      iIntros (CIDe4 Hse4) "Hcg Hpc Hb3".
      set (E3 := <[Regidx ap_s1 := regval_into_reg (m !!! Regidx ap_s1)]> E2).
      change (<[Regidx ap_s1 := regval_into_reg (m !!! Regidx ap_s1)]> E2) with E3.
      assert (Hp80 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xd8) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xda)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp80) in "Hpc".
      assert (HE3csp : E3 !!! Regidx csp_rs1 = spd) by (rewrite /E3 upd_ne; [exact HE2csp | vm_compute; discriminate]).
      iApply (wp_cldsp_s_sconf (CID := CIDe4) (mword_of_int (KernelSyms.allocproc + 0xda)) (mword_of_int 0 : mword 6) ap_s2
                E3 (rsv + (K - 4))%nat (m !!! Regidx ap_s2) xb (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hb4]").
      { iApply (api_da with "Htext"). }
      { iEval (rewrite HE3csp). iExact "Hb4". }
      iIntros (CIDe5 Hse5) "Hcg Hpc Hb4".
      set (E4 := <[Regidx ap_s2 := regval_into_reg (m !!! Regidx ap_s2)]> E3).
      change (<[Regidx ap_s2 := regval_into_reg (m !!! Regidx ap_s2)]> E3) with E4.
      assert (Hp82 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xda) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xdc)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp82) in "Hpc".
      (* +0xdc c.addi16sp sp,32 *)
      assert (HE4csp : E4 !!! Regidx csp_rs1 = spd) by (rewrite /E4 upd_ne; [exact HE3csp | vm_compute; discriminate]).
      assert (Hup : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
        by (rewrite /spd /sp0; apply frame_cancel_32).
      assert (Hwv : add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
        by (rewrite HE4csp; exact Hup).
      assert (Hpop : E4 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
        by (rewrite Hwv HE4csp; symmetry; exact Hspd4).
      iAssert (stack_own (KTR := KT1) sp0 4) with "[Hb1 Hb2 Hb3 Hb4]" as "Hframe4".
      { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
        iSplitL "Hb1". { iExists _. iEval (rewrite Hb1a -HE0csp). iExact "Hb1". }
        iSplitL "Hb2". { iExists _. iEval (rewrite Hb2a -HE1csp). iExact "Hb2". }
        iSplitL "Hb3". { iExists _. iEval (rewrite Hb3a -HE2csp). iExact "Hb3". }
        iSplitL "Hb4". { iExists _. iEval (rewrite Hb4a -HE3csp). iExact "Hb4". }
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf (CID := CIDe5) (mword_of_int (KernelSyms.allocproc + 0xdc)) (mword_of_int 2 : mword 6) E4 (rsv + (K - 4))%nat 4 xb Hpop
                with "Hcg Hpc [] Hframe4").
      { iApply (api_dc with "Htext"). }
      iIntros (CIDe6 Hse6) "Hcg Hpc".
      (* the pop conserves the reserve: [rsv + (K - 4)] + 4 = [rsv + K]. *)
      assert (Hnk : ((rsv + (K - 4)) + 4)%nat = (rsv + K)%nat)
        by (pose proof (ap_Kback K HK); lia).
      iEval (rewrite Hnk) in "Hcg".
      set (E5 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4).
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4) with E5.
      assert (Hp84 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xdc) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xde)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp84) in "Hpc".
      (* +0xde c.ret *)
      assert (HE5ra : E5 !!! Regidx ap_ra = m !!! Regidx ap_ra).
      { rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_ne; [| vm_compute; discriminate].
        rewrite /E3 upd_ne; [| vm_compute; discriminate].
        rewrite /E2 upd_ne; [| vm_compute; discriminate].
        rewrite /E1. apply upd_eq. }
      iApply (wp_cret_s_sconf (CID := CIDe6) (mword_of_int (KernelSyms.allocproc + 0xde)) ap_ra E5 (rsv + K)%nat xb
                ltac:(vm_compute; discriminate) with "Hcg Hpc []").
      { iApply (api_de with "Htext"). }
      iIntros (CIDe7 Hse7) "Hcg Hpc".
      assert (Hretfin : ret_pc (rget (CID := CIDe6) E5 ap_ra) = ret_tgt)
        by (rewrite ap_rg_ra HE5ra; reflexivity).
      iEval (rewrite Hretfin) in "Hpc".
      (* the register-preservation obligations *)
      assert (HE5a0 : E5 !!! Regidx ap_a0 = rv).
      { rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_ne; [| vm_compute; discriminate].
        rewrite /E3 upd_ne; [| vm_compute; discriminate].
        rewrite /E2 upd_ne; [| vm_compute; discriminate].
        rewrite /E1 upd_ne; [| vm_compute; discriminate].
        rewrite /E0 upd_eq. apply add_vec_zero_l. }
      assert (HE5csp : E5 !!! Regidx csp_rs1 = m !!! Regidx csp_rs1)
        by (rewrite /E5 upd_eq; exact Hwv).
      assert (HE5s0 : E5 !!! Regidx ap_s0 = m !!! Regidx ap_s0).
      { rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_ne; [| vm_compute; discriminate].
        rewrite /E3 upd_ne; [| vm_compute; discriminate].
        rewrite /E2. apply upd_eq. }
      assert (HE5s1 : E5 !!! Regidx ap_s1 = m !!! Regidx ap_s1).
      { rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_ne; [| vm_compute; discriminate].
        rewrite /E3. apply upd_eq. }
      assert (HE5s2 : E5 !!! Regidx ap_s2 = m !!! Regidx ap_s2).
      { rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4. apply upd_eq. }
      assert (Hthr : forall r : mword 5, is_cs_idx r = true ->
                       r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                       E5 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /E5 upd_ne; [| congruence].
        rewrite /E4 upd_ne; [| congruence].
        rewrite /E3 upd_ne; [| congruence].
        rewrite /E2 upd_ne; [| congruence].
        rewrite /E1 upd_ne; [| congruence].
        rewrite /E0 upd_ne; [| congruence].
        exact (Htrest r Hr Ncsp N8 N9 N18). }
      iSpecialize ("Hk" $! CIDe7 with "[%]"); [wp_next_chain|].
      iApply ("Hk" $! E5 with "[%] Hcg Hpc").
      split; [| exact HE5a0].
      unfold callee_saved.
      split; [exact HE5csp|].
      split; [exact HE5s0|]. split; [exact HE5s1|].
      split; [exact HE5s2|].
      repeat (split; [apply Hthr; vm_compute; first [reflexivity | discriminate]|]).
      apply Hthr; vm_compute; first [reflexivity | discriminate]. }
    (* ============ the two auipc/addi pairs: s1 := proc, s2 := &proc[NPROC] ==== *)
    iApply (wp_caddi4spn_s_sconf (CID := CID5) (mword_of_int (KernelSyms.allocproc + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) ap_s0
              M1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (api_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A1 := <[Regidx ap_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx ap_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with A1.
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    iApply (wp_auipc_s_sconf (CID := CID6) (mword_of_int (KernelSyms.allocproc + 0x0c)) ap_s1 (mword_of_int 0x11 : mword 20) A1 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (api_0c with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A2 := <[Regidx ap_s1 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.allocproc + 0x0c) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> A1).
    change (<[Regidx ap_s1 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.allocproc + 0x0c) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> A1) with A2.
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    iApply (wp_addi4_s_sconf (CID := CID7) (mword_of_int (KernelSyms.allocproc + 0x10)) ap_s1 ap_s1 (mword_of_int 3290 : mword 12) A2 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (api_10 with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rewrite ap_rg_s1) in "Hcg".
    set (A3 := <[Regidx ap_s1 := regval_into_reg
        (add_vec (A2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 3290 : mword 12)))]> A2).
    change (<[Regidx ap_s1 := regval_into_reg
        (add_vec (A2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 3290 : mword 12)))]> A2) with A3.
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    assert (HA3s1 : A3 !!! Regidx ap_s1 = proc_addr 0).
    { rewrite /A3 upd_eq /A2 upd_eq /proc_addr /proc_base.
      apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_auipc_s_sconf (CID := CID8) (mword_of_int (KernelSyms.allocproc + 0x14)) ap_s2 (mword_of_int 0x16 : mword 20) A3 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (api_14 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (A4 := <[Regidx ap_s2 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.allocproc + 0x14) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> A3).
    change (<[Regidx ap_s2 := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.allocproc + 0x14) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> A3) with A4.
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x14) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    iApply (wp_addi4_s_sconf (CID := CID9) (mword_of_int (KernelSyms.allocproc + 0x18)) ap_s2 ap_s2 (mword_of_int 1746 : mword 12) A4 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (api_18 with "Htext"). }
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rewrite ap_rg_s2) in "Hcg".
    set (A5 := <[Regidx ap_s2 := regval_into_reg
        (add_vec (A4 !!! Regidx ap_s2) (sign_extend' 64 (mword_of_int 1746 : mword 12)))]> A4).
    change (<[Regidx ap_s2 := regval_into_reg
        (add_vec (A4 !!! Regidx ap_s2) (sign_extend' 64 (mword_of_int 1746 : mword 12)))]> A4) with A5.
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    assert (HA5s2 : A5 !!! Regidx ap_s2 = proc_addr NPROC).
    { rewrite /A5 upd_eq /A4 upd_eq proc_addr_acur proc_end_is_tickslock.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HA5s1 : A5 !!! Regidx ap_s1 = proc_addr 0).
    { rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate]. exact HA3s1. }
    assert (HA5csp : A5 !!! Regidx csp_rs1 = spd).
    { rewrite /A5 upd_ne; [| vm_compute; discriminate].
      rewrite /A4 upd_ne; [| vm_compute; discriminate].
      rewrite /A3 upd_ne; [| vm_compute; discriminate].
      rewrite /A2 upd_ne; [| vm_compute; discriminate].
      rewrite /A1 upd_ne; [| vm_compute; discriminate]. exact HcspM1. }
    assert (HA5rest : forall r : mword 5, is_cs_idx r = true ->
                        r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                        A5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Ncsp N8 N9 N18.
      rewrite /A5 upd_ne; [| congruence].
      rewrite /A4 upd_ne; [| congruence].
      rewrite /A3 upd_ne; [| congruence].
      rewrite /A2 upd_ne; [| congruence].
      rewrite /A1 upd_ne; [| congruence].
      rewrite /M1 upd_ne; [| congruence]. reflexivity. }
    (* ===================== THE SCAN =====================
       A bounded fuel induction: no Löb, the fuel bounds [NPROC - k].  The
       loop invariant is ITSELF a [wp_next b], so the induction hypothesis is
       re-enterable at a migrated hart and no [wp_next_shift] is ever needed.
       Both the epilogue [ap_tail] (hart-free by construction) and the
       function's own continuation (anchored at [CID0]) are PREMISES of the
       statement, so forwarding either across an iteration is the IDENTITY. *)
    iAssert (∀ (fuel : nat),
               wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
                 ∀ (k : nat) (Mk : regfile),
                   ⌜(NPROC - k <= fuel)%nat⌝ -∗ ⌜(k < NPROC)%nat⌝ -∗
                   ⌜ Mk !!! Regidx csp_rs1 = spd /\
                     Mk !!! Regidx ap_s1 = proc_addr k /\
                     Mk !!! Regidx ap_s2 = proc_addr NPROC /\
                     (forall r : mword 5, is_cs_idx r = true ->
                        r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                        Mk !!! Regidx r = m !!! Regidx r) ⌝ -∗
                   ap_tail m spd pme ret_tgt K -∗
                   wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
                     ∀ (mr : regfile),
                       ⌜ callee_saved m mr ⌝ -∗
                       pc_is ret_tgt -∗
                       allocproc_post γa γk γf γs lvl eb pme on op b lks mr K
                         (mr !!! Regidx ap_a0) -∗
                       WP (Loop : expr riscv_lang)) -∗
                   sie_cap_gpr KT1 Mk (K - 4)%nat b pme -∗
                   cpu_own lvl eb pme b lks -∗
                   kalloc_env_at γa γk on -∗
                   (* the proc table's regime, and the record of every slot
                      the scan has already passed.  The record is PERSISTENT
                      ([ProcAvail.pslot_used]), which is the only reason it
                      can be carried at all: each slot's own copy went back
                      into its lock at the release. *)
                   procs_avail op -∗
                   ([∗ list] i ∈ seq 0 k, pslot_used i) -∗
                   pc_is (mword_of_int (KernelSyms.allocproc + 0x1c)) -∗
                   WP (Loop : expr riscv_lang)))%I with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (CIDk Hsk k Mk) "%Hfuel %Hk _ _ _ _ _ _ _ _ _". exfalso. exact (ap_fuel0 k Hfuel Hk). }
      iIntros (CIDk Hsk k Mk) "%Hfuel %Hk %Hregs Htl Hcont Hcg Hcpu Henv Hpav #Hacc Hpc".
      destruct Hregs as (Hksp & Hks1 & Hks2 & Hkrest).
      iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbmatch. symmetry in Hbmatch.
      destruct (lookup_lt_is_Some_2 γs k ltac:(rewrite Hlen; exact Hk)) as [γl Hγl].
      iDestruct (procs_inv_lookup γs k γl Hγl with "Hpinv") as "#Hislock".
      (* +0x1c c.mv a0,s1 *)
      iApply (wp_cmv_s_sconf (CID := CIDk) (mword_of_int (KernelSyms.allocproc + 0x1c)) ap_a0 ap_s1 Mk (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (api_1c with "Htext"). }
      iIntros (CIDl1 Hsl1) "Hcg Hpc".
      iEval (rewrite ap_rg_s1) in "Hcg".
      set (L1 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (Mk !!! Regidx ap_s1))]> Mk).
      change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (Mk !!! Regidx ap_s1))]> Mk) with L1.
      assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x1c) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp1e) in "Hpc".
      (* +0x1e jal ra,acquire *)
      iApply (wp_jal_s_sconf (CID := CIDl1) (mword_of_int (KernelSyms.allocproc + 0x1e)) ap_ra (mword_of_int 2093244 : mword 21)
                L1 (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (api_1e with "Htext"). }
      iIntros (CIDl2 Hsl2) "Hcg Hpc".
      set (L2 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0x1e) : mword 64) 4)]> L1).
      change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0x1e) : mword 64) 4)]> L1) with L2.
      assert (Hjacq : add_vec (mword_of_int (KernelSyms.allocproc + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 2093244 : mword 21)) = mword_of_int KernelSyms.acquire)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjacq) in "Hpc".
      assert (HL2ra : L2 !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0x1e) : mword 64) 4) by (rewrite /L2 upd_eq; reflexivity).
      assert (HL2a0 : L2 !!! Regidx ap_a0 = proc_addr k).
      { rewrite /L2 upd_ne; [| vm_compute; discriminate].
        rewrite /L1 upd_eq add_vec_zero_l. exact Hks1. }
      assert (HL2s1 : L2 !!! Regidx ap_s1 = proc_addr k).
      { rewrite /L2 upd_ne; [| vm_compute; discriminate].
        rewrite /L1 upd_ne; [| vm_compute; discriminate]. exact Hks1. }
      assert (HL2s2 : L2 !!! Regidx ap_s2 = proc_addr NPROC).
      { rewrite /L2 upd_ne; [| vm_compute; discriminate].
        rewrite /L1 upd_ne; [| vm_compute; discriminate]. exact Hks2. }
      assert (HL2csp : L2 !!! Regidx csp_rs1 = spd).
      { rewrite /L2 upd_ne; [| vm_compute; discriminate].
        rewrite /L1 upd_ne; [| vm_compute; discriminate]. exact Hksp. }
      assert (HL2rest : forall r : mword 5, is_cs_idx r = true ->
                          r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                          L2 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /L2 upd_ne; [| congruence].
        rewrite /L1 upd_ne; [| congruence].
        exact (Hkrest r Hr Ncsp N8 N9 N18). }
      iDestruct (cpu_own_transport CIDk CIDl2 lvl eb pme b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iApply (Acquire.wp_acquire_sconf KT1 (CID := CIDl2) γl "proc"%string (proc_lock_pay γs γl (proc_addr k)) L2 lvl eb pme (K - 4)%nat b lks
                (ap_lvl1 lvl Hlvl) ltac:(pose proof (ap_K10 K HK); lia) Hbelow
                with "Hcg Hcpu Htext Hpc [Hislock]").
      all: try lkbelow.
      { iEval (rewrite HL2a0). iExact "Hislock". }
      iIntros (CIDf Hsf ms macq) "%Hmsf Hcg Hpc %Hcsacq Hlocked HR _ Hcpu Hpay".
      assert (Hp22 : ret_pc (L2 !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0x22))
        by (rewrite HL2ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp22) in "Hpc".
      iDestruct (proc_lock_res_elim γs γl (proc_addr k) with "HR") as (st ch) "(Hstate & Hpg & Hchan & Hpub & Hslots)".
      assert (Hacq_s1 : macq !!! Regidx ap_s1 = proc_addr k).
      { rewrite (callee_saved_lookup Hcsacq ap_s1 ltac:(vm_compute; reflexivity)). exact HL2s1. }
      assert (Hacq_s2 : macq !!! Regidx ap_s2 = proc_addr NPROC).
      { rewrite (callee_saved_lookup Hcsacq ap_s2 ltac:(vm_compute; reflexivity)). exact HL2s2. }
      assert (Hacq_csp : macq !!! Regidx csp_rs1 = spd).
      { rewrite (callee_saved_lookup Hcsacq csp_rs1 ltac:(vm_compute; reflexivity)). exact HL2csp. }
      assert (Hacq_rest : forall r : mword 5, is_cs_idx r = true ->
                            r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                            macq !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        rewrite (callee_saved_lookup Hcsacq r Hr).
        exact (HL2rest r Hr Ncsp N8 N9 N18). }
      (* +0x22 c.lw a5,24(s1) : p->state *)
      assert (Hstaddr : add_vec (macq !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 24 : mword 12))
                        = p_state (proc_addr k))
        by (rewrite Hacq_s1; apply ap_off_24).
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0x22)) ap_a5 ap_s1
                (mword_of_int 24 : mword 12) macq (trap_res b + (K - 4))%nat st false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hstate]").
      { iApply (api_22 with "Htext"). }
      { iEval (rewrite ap_rg_s1 Hstaddr). iExact "Hstate". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hstate". iEval (rewrite ap_rg_s1 Hstaddr) in "Hstate".
      set (L3 := <[Regidx ap_a5 := regval_into_reg (sign_extend' 64 st)]> macq).
      change (<[Regidx ap_a5 := regval_into_reg (sign_extend' 64 st)]> macq) with L3.
      assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp24) in "Hpc".
      assert (HL3a5 : L3 !!! Regidx ap_a5 = sign_extend' 64 st) by (rewrite /L3 upd_eq; reflexivity).
      assert (HL3s1 : L3 !!! Regidx ap_s1 = proc_addr k)
        by (rewrite /L3 upd_ne; [exact Hacq_s1 | vm_compute; discriminate]).
      assert (HL3s2 : L3 !!! Regidx ap_s2 = proc_addr NPROC)
        by (rewrite /L3 upd_ne; [exact Hacq_s2 | vm_compute; discriminate]).
      assert (HL3csp : L3 !!! Regidx csp_rs1 = spd)
        by (rewrite /L3 upd_ne; [exact Hacq_csp | vm_compute; discriminate]).
      assert (HL3rest : forall r : mword 5, is_cs_idx r = true ->
                          r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                          L3 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Ncsp N8 N9 N18.
        assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
        rewrite /L3 upd_ne; [| congruence].
        exact (Hacq_rest r Hr Ncsp N8 N9 N18). }
      (* +0x24 c.beqz a5 *)
      destruct (eq_vec (L3 !!! Regidx ap_a5) (zero_reg : mword 64)) eqn:Hcmp.
      - (* ============ FOUND: p->state == UNUSED ============ *)
        assert (Hstu : st = UNUSED) by (apply ap_sext_zero; rewrite -HL3a5; exact Hcmp).
        subst st.
        assert (Hcmpr : eq_vec (rget (CID := CIDf) L3 ap_a5) (zero_reg : mword 64) = true)
          by (rewrite ap_rg_a5; exact Hcmp).
        iApply (wp_cbeqz_taken_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0x24)) (mword_of_int 10 : mword 8)
                  (Cregidx (mword_of_int 7)) ap_a5 L3 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  Hcmpr ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (api_24 with "Htext"). }
        iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt38 : add_vec (mword_of_int (KernelSyms.allocproc + 0x24) : mword 64)
                           (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0"))))
                         = mword_of_int (KernelSyms.allocproc + 0x38))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt38) in "Hpc".
        (* the dormant block comes out of the invariant *)
        iDestruct (proc_slots_unused γs (proc_addr k) with "Hslots") as "[Hdorm Hpark]".
        (* UNUSED is unclaimed, so the lock's share IS the whole mirror; the
           store of USED below claims the slot, and the whole variable rides
           out on [proc_held]. *)
        iDestruct (pstate_whole_split (proc_addr k) UNUSED) as "[_ Hwa]".
        iDestruct ("Hwa" with "[Hpg]") as "Hpg"; [rewrite unclaimed_UNUSED; iFrame "Hpg"|].
        iApply fupd_wp.
        iMod (pstate_whole_update (proc_addr k) UNUSED USED with "Hpg") as "Hpg".
        (* THE fd-STATE GHOST IS MINTED HERE: [proc_dormant_unused] is an
           update because a fresh process gets a fresh per-descriptor ghost
           (FdSlots.v).  It is the one place a [pv_fdg] is chosen. *)
        iMod (proc_dormant_unused γf (proc_addr k) with "Hdorm")
          as "(Hctx & Hpgcell & Htfcell & Hspare & Hirsp & Hbsp & Hkst & Hxb & Hrest)".
        iModIntro.
        iDestruct "Hrest" as (V pid0)
          "([%Hof [%Hcwd [%Hszb [%Hpid00 %Hlzv]]]] & Hpidhalf & Hfields & Hofiles & Hrow & Hsg & Hfrag)".
        iDestruct "Hpub" as (kl xs pid1) "(Hkilled & Hxstate & Hpidinv)".
        (* +0x38 .. +0xee: THE INLINED allocpid -- acquire(&pid_lock), the
           retry scan for a pid no slot holds, [p->pid = pid], release.  One
           block lemma ([wp_ap_pidsec] above), stated in the shape the
           standalone allocpid()'s contract used to have; it takes the two
           pieces of the cell this function owns (the invariant's quarter out
           of [proc_pub], the dormant block's half) and hands them back at
           the new pid.  p->lock (rank 9) is still held here, so the block's
           held set is [{["proc"]} ∪ lks], not bare [lks]. *)
        iApply (wp_ap_pidsec (CID := CIDf) γp L3 k (trap_res b + (K - 4))%nat (S lvl) eb pme
                  ({["proc"]} ∪ lks) pid1 pid0 (pv_gen V)
                  (ap_lvlS lvl Hlvl) ltac:(pose proof (ap_K14 K HK); lia) Hk HL3s1 (ap_below_nextpid lks Hbelow) Hpid00
                  with "Hcg Hcpu Htext Hpc Hpidlk Hpidinv Hpidhalf Hsg").
        iApply wp_next_off_intro. rewrite /ap_pid_post.
        iIntros (mfa pidn γg) "%Hcsfa %Hpidnb Hcg Hcpu Hpc Hpidinv Hpidown Hgen Hsg Hpr".
        assert (Hfa_s1 : mfa !!! Regidx ap_s1 = proc_addr k).
        { rewrite (callee_saved_lookup Hcsfa ap_s1 ltac:(vm_compute; reflexivity)). exact HL3s1. }
        assert (Hfa_csp : mfa !!! Regidx csp_rs1 = spd).
        { rewrite (callee_saved_lookup Hcsfa csp_rs1 ltac:(vm_compute; reflexivity)). exact HL3csp. }
        assert (Hfa_rest : forall r : mword 5, is_cs_idx r = true ->
                             r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                             mfa !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          rewrite (callee_saved_lookup Hcsfa r Hr).
          exact (HL3rest r Hr Ncsp N8 N9 N18). }
        (* +0x98 c.li a5,1 *)
        iApply (wp_cli_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0x98)) ap_a5 (mword_of_int 1 : mword 6)
                  (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
                  mfa (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
                  with "Hcg Hpc []").
        { iApply (api_98 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (F2 := <[Regidx ap_a5 := regval_into_reg
            (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mfa).
        change (<[Regidx ap_a5 := regval_into_reg
            (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mfa) with F2.
        assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x98) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp40) in "Hpc".
        assert (HF2s1 : F2 !!! Regidx ap_s1 = proc_addr k)
          by (rewrite /F2 upd_ne; [exact Hfa_s1 | vm_compute; discriminate]).
        (* +0x9a c.sw a5,24(s1) : p->state = USED *)
        assert (Hstaddr2 : add_vec (F2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 24 : mword 12))
                           = p_state (proc_addr k))
          by (rewrite HF2s1; apply ap_off_24).
        iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0x9a)) ap_a5 ap_s1
                  (mword_of_int 24 : mword 12) F2 (trap_res b + (K - 4))%nat UNUSED false
                  with "Hcg Hpc [] [Hstate]").
        { iApply (api_9a with "Htext"). }
        { iEval (rewrite ap_rg_s1 Hstaddr2). iExact "Hstate". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hstate". iEval (rewrite ap_rg_s1 Hstaddr2) in "Hstate".
        assert (Hused : trunc32 (F2 !!! Regidx ap_a5) = USED)
          by (rewrite /F2 upd_eq; apply ap_used_val).
        iEval (rewrite ap_rg_a5 Hused) in "Hstate".
        assert (Hp42 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x9a) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp42) in "Hpc".
        (* +0x9c jal ra,kalloc *)
        iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0x9c)) ap_ra (mword_of_int 2092900 : mword 21)
                  F2 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (api_9c with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (F3 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0x9c) : mword 64) 4)]> F2).
        change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0x9c) : mword 64) 4)]> F2) with F3.
        assert (Hjkal : add_vec (mword_of_int (KernelSyms.allocproc + 0x9c) : mword 64) (sign_extend' 64 (mword_of_int 2092900 : mword 21)) = mword_of_int KernelSyms.kalloc)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjkal) in "Hpc".
        assert (HF3ra : F3 !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0x9c) : mword 64) 4) by (rewrite /F3 upd_eq; reflexivity).
        assert (HF3s1 : F3 !!! Regidx ap_s1 = proc_addr k)
          by (rewrite /F3 upd_ne; [exact HF2s1 | vm_compute; discriminate]).
        assert (HF3csp : F3 !!! Regidx csp_rs1 = spd).
        { rewrite /F3 upd_ne; [| vm_compute; discriminate].
          rewrite /F2 upd_ne; [| vm_compute; discriminate]. exact Hfa_csp. }
        assert (HF3rest : forall r : mword 5, is_cs_idx r = true ->
                            r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                            F3 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /F3 upd_ne; [| congruence].
          rewrite /F2 upd_ne; [| congruence].
          exact (Hfa_rest r Hr Ncsp N8 N9 N18). }
        (* the pair is NAMED in the contract now ([KvmSpec.kalloc_env_at]),
           so this is a plain split rather than an [∃]-elimination -- and the
           name survives the callees below, which is the whole point. *)
        iEval (rewrite /kalloc_env_at) in "Henv".
        iDestruct "Henv" as "(#Hkmem & Havail)".
        (* p->lock is still held: kalloc's own held set is
           [{["proc"]} ∪ lks], and its "kmem" freshness premise
           needs [ap_below_kmem]. *)
        iApply (AK.wp_kalloc_sconf KT1 (CID := CIDf) γa γk (mword_of_int (KernelSyms.kmem + 24))
                  F3 on (S lvl) eb pme (trap_res b + (K - 4))%nat false
                  ({["proc"]} ∪ lks)
                  ltac:(pose proof (ap_K14 K HK); lia) ltac:(reflexivity) (ap_lvlS lvl Hlvl)
                  (ap_below_kmem lks Hbelow)
                  with "Hcg Hcpu Htext Hpc Hkmem Havail").
        all: try lkbelow.
        iApply wp_next_off_intro. iIntros (mka) "Hcg Hcpu Hpc %Hcska Hkpost".
        assert (Hp46 : ret_pc (F3 !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0xa0))
          by (rewrite HF3ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp46) in "Hpc".
        (* [Hkpost] is NOT destructed yet: +0xa0 and +0xa2 move the returned
           word without looking at it, and only the [c.beqz] at +0xa4 cares
           whether kalloc succeeded.  Splitting there rather than here is what
           keeps those two instructions off the duplicated tail. *)
        set (tfr := (mka !!! Regidx ap_a0 : mword 64)).
        assert (Hka_s1 : mka !!! Regidx ap_s1 = proc_addr k).
        { rewrite (callee_saved_lookup Hcska ap_s1 ltac:(vm_compute; reflexivity)). exact HF3s1. }
        assert (Hka_csp : mka !!! Regidx csp_rs1 = spd).
        { rewrite (callee_saved_lookup Hcska csp_rs1 ltac:(vm_compute; reflexivity)). exact HF3csp. }
        assert (Hka_rest : forall r : mword 5, is_cs_idx r = true ->
                             r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                             mka !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          rewrite (callee_saved_lookup Hcska r Hr).
          exact (HF3rest r Hr Ncsp N8 N9 N18). }
        (* +0xa0 c.mv s2,a0 *)
        iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xa0)) ap_s2 ap_a0 mka (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (api_a0 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_a0) in "Hcg".
        set (F4 := <[Regidx ap_s2 := regval_into_reg (add_vec zero_reg (mka !!! Regidx ap_a0))]> mka).
        change (<[Regidx ap_s2 := regval_into_reg (add_vec zero_reg (mka !!! Regidx ap_a0))]> mka) with F4.
        assert (Hp48 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xa0) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xa2)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp48) in "Hpc".
        assert (HF4s1 : F4 !!! Regidx ap_s1 = proc_addr k)
          by (rewrite /F4 upd_ne; [exact Hka_s1 | vm_compute; discriminate]).
        assert (HF4a0 : F4 !!! Regidx ap_a0 = tfr)
          by (rewrite /F4 upd_ne; [reflexivity | vm_compute; discriminate]).
        (* +0xa2 c.sd a0,88(s1) : p->trapframe = the page *)
        assert (Htfaddr : add_vec (F4 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 88 : mword 12))
                          = p_trapframe (proc_addr k))
          by (rewrite HF4s1; apply ap_off_88).
        iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xa2)) ap_a0 ap_s1
                  (mword_of_int 88 : mword 12) F4 (trap_res b + (K - 4))%nat (zero_reg : mword 64) false
                  with "Hcg Hpc [] [Htfcell]").
        { iApply (api_a2 with "Htext"). }
        { iEval (rewrite ap_rg_s1 Htfaddr). iExact "Htfcell". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Htfcell".
        iEval (rewrite ap_rg_s1 Htfaddr ap_rg_a0 HF4a0) in "Htfcell".
        assert (Hp4a : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xa2) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp4a) in "Hpc".
        (* +0xa4 c.beqz a0 : the trapframe allocation's verdict *)
        iDestruct "Hkpost" as "[(%Hnull & %Hdry & Havail) | (%Hpvtf & Hpgown & Havail)]".
        { (* ================== TAIL 1: kalloc failed, +0xe0 ==================
             p->trapframe and p->pagetable are BOTH the zero this arm just
             stored, so freeproc runs at [None]/[None] and the whole slot
             goes back to the lock as a plain UNUSED dormant block. *)
          assert (Hz4a : eq_vec (rget (CID := CIDf) F4 ap_a0) (zero_reg : mword 64) = true)
            by (rewrite ap_rg_a0 HF4a0 Hnull; exact ap_null_eqz).
          iApply (wp_cbeqz_taken_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xa4)) (mword_of_int 30 : mword 8)
                    (Cregidx (mword_of_int 2)) ap_a0 F4 (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                    Hz4a ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (api_a4 with "Htext"). }
          iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Htgt86 : add_vec (mword_of_int (KernelSyms.allocproc + 0xa4) : mword 64)
                             (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0"))))
                           = mword_of_int (KernelSyms.allocproc + 0xe0))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt86) in "Hpc".
          (* the stored trapframe word is the null kalloc returned *)
          assert (Htfz : tfr = (zero_reg : mword 64))
            by (rewrite Hnull; symmetry; exact ap_zero_nullp).
          assert (HF4csp : F4 !!! Regidx csp_rs1 = spd)
            by (rewrite /F4 upd_ne; [exact Hka_csp | vm_compute; discriminate]).
          assert (HF4s2 : F4 !!! Regidx ap_s2 = (zero_reg : mword 64)).
          { rewrite /F4 upd_eq add_vec_zero_l. exact Htfz. }
          assert (HF4rest : forall r : mword 5, is_cs_idx r = true ->
                              r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                              F4 !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9 N18.
            rewrite /F4 upd_ne; [| congruence].
            exact (Hka_rest r Hr Ncsp N8 N9 N18). }
          (* +0xe0 c.mv a0,s1 *)
          iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xe0)) ap_a0 ap_s1 F4 (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (api_e0 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
          set (T1 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (F4 !!! Regidx ap_s1))]> F4).
          change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (F4 !!! Regidx ap_s1))]> F4) with T1.
          assert (Hp88 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xe0) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xe2)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp88) in "Hpc".
          (* +0xe2 jal ra,freeproc *)
          iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xe2)) ap_ra (mword_of_int 2096826 : mword 21)
                    T1 (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (api_e2 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          set (T2 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xe2) : mword 64) 4)]> T1).
          change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xe2) : mword 64) 4)]> T1) with T2.
          assert (Hjfp : add_vec (mword_of_int (KernelSyms.allocproc + 0xe2) : mword 64) (sign_extend' 64 (mword_of_int 2096826 : mword 21)) = mword_of_int KernelSyms.freeproc)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjfp) in "Hpc".
          assert (HT2ra : T2 !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0xe2) : mword 64) 4)
            by (rewrite /T2 upd_eq; reflexivity).
          assert (HT2a0 : T2 !!! Regidx ap_a0 = proc_addr k).
          { rewrite /T2 upd_ne; [| vm_compute; discriminate].
            rewrite /T1 upd_eq add_vec_zero_l. exact HF4s1. }
          assert (HT2s1 : T2 !!! Regidx ap_s1 = proc_addr k).
          { rewrite /T2 upd_ne; [| vm_compute; discriminate].
            rewrite /T1 upd_ne; [| vm_compute; discriminate]. exact HF4s1. }
          assert (HT2s2 : T2 !!! Regidx ap_s2 = (zero_reg : mword 64)).
          { rewrite /T2 upd_ne; [| vm_compute; discriminate].
            rewrite /T1 upd_ne; [| vm_compute; discriminate]. exact HF4s2. }
          assert (HT2csp : T2 !!! Regidx csp_rs1 = spd).
          { rewrite /T2 upd_ne; [| vm_compute; discriminate].
            rewrite /T1 upd_ne; [| vm_compute; discriminate]. exact HF4csp. }
          assert (HT2rest : forall r : mword 5, is_cs_idx r = true ->
                              r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                              T2 !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9 N18.
            assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            rewrite /T2 upd_ne; [| congruence].
            rewrite /T1 upd_ne; [| congruence].
            exact (HF4rest r Hr Ncsp N8 N9 N18). }
          (* LEAVE THE COUNTED REGIME.  freeproc's callees exist only at
             [None]; the seal is irreversible and that is exactly what the
             third arm of [allocproc_post] records.  The sealed bundle is
             persistent, so the post still gets one. *)
          iAssert (kalloc_env_at γa γk on) with "[Havail]" as "Henv".
          { iApply (kalloc_env_at_intro with "Hkmem Havail"). }
          iMod (kalloc_env_at_seal with "Henv") as "#Henv".
          (* freeproc is stated only at the BUNDLE (it never needs the name),
             so it takes the one-way projection; the named copy stays, which
             is what the post's third arm reports. *)
          iDestruct (kalloc_env_at_env with "Henv") as "#Henvb".
          iDestruct (proc_ofiles_null_split γf (pv_fdg V) (proc_addr k) (pv_ofile V) Hof with "Hofiles")
            as "[Hofc Hofs]".
          (* p->lock is still held: freeproc's own held set (opaque -- it
             acquires nothing, so no order premise) is
             [{["proc"]} ∪ lks]. *)
          iApply (FP.wp_freeproc_sconf (CID := CIDf) γp γa T2 k γl V γg pidn USED ch None None
                    (trap_res b + (K - 4))%nat eb pme (S lvl) ({["proc"]} ∪ lks)
                    ltac:(pose proof (ap_K44 K HK); lia) Hk (ap_lvlS lvl Hlvl) HT2a0
                    with "Hcg Hcpu Htext Hpc Hpidlk [Hlocked Hstate Hpg Hchan Hkilled Hxstate Hpidinv] [Hpidown Hfields Hofc Hofs Hspare Hirsp Hbsp Hkst Hctx] Hrow Hsg Hpr Hxb [Hpgcell] [Htfcell] Henvb").
          all: try lkbelow.
          { rewrite /proc_held. iFrame "Hlocked Hstate Hpg Hchan".
            iExists kl, xs, pidn. iFrame "Hkilled Hxstate Hpidinv". }
          { rewrite /fp_rest. iSplitR.
            { iPureIntro. split; [exact Hof|]. split; [exact Hcwd|]. exact Hszb. }
            iFrame "Hpidown Hfields Hofc Hofs Hspare Hirsp Hbsp Hkst Hctx". }
          { rewrite /fp_pt. iExact "Hpgcell". }
          { rewrite /fp_tf. iEval (rewrite -Htfz). iExact "Htfcell". }
          iApply wp_next_off_intro.
          iIntros (mfp) "Hcg Hcpu Hpc %Hcsfp Hheld Hdorm".
          assert (Hp8c : ret_pc (T2 !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0xe6))
            by (rewrite HT2ra; apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp8c) in "Hpc".
          assert (Hfp_s1 : mfp !!! Regidx ap_s1 = proc_addr k).
          { rewrite (callee_saved_lookup Hcsfp ap_s1 ltac:(vm_compute; reflexivity)). exact HT2s1. }
          assert (Hfp_s2 : mfp !!! Regidx ap_s2 = (zero_reg : mword 64)).
          { rewrite (callee_saved_lookup Hcsfp ap_s2 ltac:(vm_compute; reflexivity)). exact HT2s2. }
          assert (Hfp_csp : mfp !!! Regidx csp_rs1 = spd).
          { rewrite (callee_saved_lookup Hcsfp csp_rs1 ltac:(vm_compute; reflexivity)). exact HT2csp. }
          assert (Hfp_rest : forall r : mword 5, is_cs_idx r = true ->
                               r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                               mfp !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9 N18.
            rewrite (callee_saved_lookup Hcsfp r Hr).
            exact (HT2rest r Hr Ncsp N8 N9 N18). }
          (* +0xe6 c.mv a0,s1 *)
          iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xe6)) ap_a0 ap_s1 mfp (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (api_e6 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
          set (T3 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (mfp !!! Regidx ap_s1))]> mfp).
          change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (mfp !!! Regidx ap_s1))]> mfp) with T3.
          assert (Hp8e : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xe6) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xe8)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp8e) in "Hpc".
          (* +0xe8 jal ra,release *)
          iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xe8)) ap_ra (mword_of_int 2093178 : mword 21)
                    T3 (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (api_e8 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          set (T4 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xe8) : mword 64) 4)]> T3).
          change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xe8) : mword 64) 4)]> T3) with T4.
          assert (Hjrel1 : add_vec (mword_of_int (KernelSyms.allocproc + 0xe8) : mword 64) (sign_extend' 64 (mword_of_int 2093178 : mword 21)) = mword_of_int KernelSyms.release)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjrel1) in "Hpc".
          assert (HT4ra : T4 !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0xe8) : mword 64) 4)
            by (rewrite /T4 upd_eq; reflexivity).
          assert (HT4a0 : T4 !!! Regidx ap_a0 = proc_addr k).
          { rewrite /T4 upd_ne; [| vm_compute; discriminate].
            rewrite /T3 upd_eq add_vec_zero_l. exact Hfp_s1. }
          assert (HT4s2 : T4 !!! Regidx ap_s2 = (zero_reg : mword 64)).
          { rewrite /T4 upd_ne; [| vm_compute; discriminate].
            rewrite /T3 upd_ne; [| vm_compute; discriminate]. exact Hfp_s2. }
          assert (HT4csp : T4 !!! Regidx csp_rs1 = spd).
          { rewrite /T4 upd_ne; [| vm_compute; discriminate].
            rewrite /T3 upd_ne; [| vm_compute; discriminate]. exact Hfp_csp. }
          assert (HT4rest : forall r : mword 5, is_cs_idx r = true ->
                              r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                              T4 !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9 N18.
            assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            rewrite /T4 upd_ne; [| congruence].
            rewrite /T3 upd_ne; [| congruence].
            exact (Hfp_rest r Hr Ncsp N8 N9 N18). }
          (* the emptied slot goes back into the lock at UNUSED, hart tag and
             all: the tag never entered [proc_held], since a not-RUNNING proc
             keeps both halves in its lock. *)
          iDestruct "Hheld" as "(Hlocked & Hstate & Hpg & Hchan & Hpub)".
          iApply fupd_wp.
          iMod (pstate_whole_update (proc_addr k) _ UNUSED with "Hpg") as "Hpg".
          iDestruct (pstate_whole_split (proc_addr k) UNUSED) as "[Hwb _]".
          iDestruct ("Hwb" with "Hpg") as "[Hpg _]".
          iModIntro.
          iAssert (proc_lock_res γs γl (proc_addr k)) with "[Hstate Hpg Hchan Hpub Hdorm Hpark]" as "HR".
          { iApply (proc_lock_res_intro γs γl (proc_addr k) UNUSED (zero_reg : mword 64)
                      with "Hstate Hpg Hchan Hpub [Hdorm Hpark]").
            iApply (proc_slots_unused_intro γs (proc_addr k) with "Hdorm Hpark"). }
          assert (Hlka1 : add_vec (T4 !!! Regidx ap_a0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr k).
          { rewrite HT4a0.
            replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64)
              by (apply bv_eq; vm_compute; reflexivity).
            apply kv_addv_zero. }
          (* [b] IS [outb] ([cpu_own] forces it); pure re-spelling for release. *)
          iEval (rewrite Hbmatch) in "Hcg".
          iApply (Release.wp_release_sconf KT1 (CID := CIDf) γl (proc_addr k) "proc"%string (proc_lock_pay γs γl (proc_addr k)) T4 lvl eb pme (K - 4)%nat
                    ({["proc"]} ∪ lks)
                    Hlka1 ltac:(pose proof (ap_K10 K HK); lia)
                    with "Hcg Htext Hpc Hislock Hlocked HR Hcpu Hpay").
          rewrite -Hbmatch.
          iIntros (CIDg Hsg mrl) "Hcg Hpc %Hcsrl Hcpu".
          assert (Hsetback : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks)
      by (apply locks_add_del_below; lkbelow).
          iEval (rewrite Hsetback) in "Hcpu".
          assert (Hp92 : ret_pc (T4 !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0xec))
            by (rewrite HT4ra; apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp92) in "Hpc".
          assert (Hrl_s2 : mrl !!! Regidx ap_s2 = (zero_reg : mword 64)).
          { rewrite (callee_saved_lookup Hcsrl ap_s2 ltac:(vm_compute; reflexivity)). exact HT4s2. }
          assert (Hrl_csp : mrl !!! Regidx csp_rs1 = spd).
          { rewrite (callee_saved_lookup Hcsrl csp_rs1 ltac:(vm_compute; reflexivity)). exact HT4csp. }
          assert (Hrl_rest : forall r : mword 5, is_cs_idx r = true ->
                               r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                               mrl !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9 N18.
            rewrite (callee_saved_lookup Hcsrl r Hr).
            exact (HT4rest r Hr Ncsp N8 N9 N18). }
          (* +0xec c.mv s1,s2 : the returned value is the failed kalloc's 0 *)
          iApply (wp_cmv_s_sconf (CID := CIDg) (mword_of_int (KernelSyms.allocproc + 0xec)) ap_s1 ap_s2 mrl (K - 4)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (api_ec with "Htext"). }
          iIntros (CIDh Hsh) "Hcg Hpc". iEval (rewrite ap_rg_s2) in "Hcg".
          set (T5 := <[Regidx ap_s1 := regval_into_reg (add_vec zero_reg (mrl !!! Regidx ap_s2))]> mrl).
          change (<[Regidx ap_s1 := regval_into_reg (add_vec zero_reg (mrl !!! Regidx ap_s2))]> mrl) with T5.
          assert (Hp94 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xec) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xee)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp94) in "Hpc".
          (* +0xee c.j +0xd2 : join the shared epilogue *)
          iApply (wp_cj_s_sconf (CID := CIDh) (mword_of_int (KernelSyms.allocproc + 0xee))
                    (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))) T5 (K - 4)%nat b
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (api_ee with "Htext"). }
          iIntros (CIDn Hsn). iApply bi.later_intro. iIntros "Hcg Hpc".
          assert (Htgt78a : add_vec (mword_of_int (KernelSyms.allocproc + 0xee) : mword 64)
                              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
                            = mword_of_int (KernelSyms.allocproc + 0xd2))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt78a) in "Hpc".
          iEval (rewrite /ap_tail) in "Htl".
          iApply ("Htl" $! 0%nat b CIDn T5 (zero_reg : mword 64) with "[%] Hcg Hpc").
          { split; [rewrite /T5 upd_ne; [exact Hrl_csp | vm_compute; discriminate]|].
            split; [rewrite /T5 upd_eq add_vec_zero_l; exact Hrl_s2|].
            intros r Hr Ncsp N8 N9 N18.
            rewrite /T5 upd_ne; [| congruence].
            exact (Hrl_rest r Hr Ncsp N8 N9 N18). }
          iIntros (CIDp Hsp Mf) "[%Hcsf %Ha0f] Hcgf Hpcf".
          iDestruct (cpu_own_transport CIDg CIDp lvl eb pme b ltac:(wp_next_chain)
                       with "Hcpu") as "Hcpu".
          iSpecialize ("Hcont" $! CIDp with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! Mf with "[%] Hpcf").
          { exact Hcsf. }
          iEval (rewrite Ha0f).
          rewrite /allocproc_post. iRight. iRight.
          iSplitR; [done|].
          iSplitR.
          { iPureIntro. exists 0%nat. split; [apply Nat.le_0_l|].
            rewrite avail_sub_0. exact Hdry. }
          iFrame "Hcgf Hcpu Henv Hpav". }
        iApply (wp_cbeqz_fall_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xa4)) (mword_of_int 30 : mword 8)
                  (Cregidx (mword_of_int 2)) ap_a0 F4 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite ap_rg_a0 HF4a0; exact (ap_valid_nz tfr Hpvtf))
                  with "Hcg Hpc []").
        { iApply (api_a4 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp4c : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xa4) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp4c) in "Hpc".
        (* +0xa6 c.mv a0,s1 *)
        iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xa6)) ap_a0 ap_s1 F4 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (api_a6 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
        set (F5 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (F4 !!! Regidx ap_s1))]> F4).
        change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (F4 !!! Regidx ap_s1))]> F4) with F5.
        assert (Hp4e : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xa6) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp4e) in "Hpc".
        (* +0xa8 jal ra,proc_pagetable *)
        iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xa8)) ap_ra (mword_of_int 2096682 : mword 21)
                  F5 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (api_a8 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (F6 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xa8) : mword 64) 4)]> F5).
        change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xa8) : mword 64) 4)]> F5) with F6.
        assert (Hjppt : add_vec (mword_of_int (KernelSyms.allocproc + 0xa8) : mword 64) (sign_extend' 64 (mword_of_int 2096682 : mword 21)) = mword_of_int KernelSyms.proc_pagetable)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjppt) in "Hpc".
        assert (HF6ra : F6 !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0xa8) : mword 64) 4) by (rewrite /F6 upd_eq; reflexivity).
        assert (HF6a0 : F6 !!! Regidx ap_a0 = proc_addr k).
        { rewrite /F6 upd_ne; [| vm_compute; discriminate].
          rewrite /F5 upd_eq add_vec_zero_l. exact HF4s1. }
        assert (HF6s1 : F6 !!! Regidx ap_s1 = proc_addr k).
        { rewrite /F6 upd_ne; [| vm_compute; discriminate].
          rewrite /F5 upd_ne; [| vm_compute; discriminate]. exact HF4s1. }
        assert (HF6csp : F6 !!! Regidx csp_rs1 = spd).
        { rewrite /F6 upd_ne; [| vm_compute; discriminate].
          rewrite /F5 upd_ne; [| vm_compute; discriminate].
          rewrite /F4 upd_ne; [| vm_compute; discriminate]. exact Hka_csp. }
        assert (HF6rest : forall r : mword 5, is_cs_idx r = true ->
                            r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                            F6 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /F6 upd_ne; [| congruence].
          rewrite /F5 upd_ne; [| congruence].
          rewrite /F4 upd_ne; [| congruence].
          exact (Hka_rest r Hr Ncsp N8 N9 N18). }
        iAssert (kalloc_env_at γa γk (avail_dec on)) with "[Havail]" as "Henv".
        { iApply (kalloc_env_at_intro with "Hkmem Havail"). }
        (* the GENERAL contract: at an arbitrary budget proc_pagetable can
           fail, and its failure is allocproc's second tail.  p->lock is
           still held here, so the actual held set is
           [{["proc"]} ∪ lks], not bare [lks].
           NOTE: [wp_proc_pagetable_core_body] (SpecProcPagetable.v) carries
           NO [locks_below] premise at all, even though proc_pagetable
           allocates pages internally.  That contract is not in this file's
           scope, so this call supplies no order proof for it -- left as-is
           rather than guessed at; flagging for whoever owns
           SpecProcPagetable.v. *)
        iApply (PPT.wp_proc_pagetable_core (CID := CIDf) γa γk F6 tfr (DfracOwn 1) (S lvl) (trap_res b + (K - 4))%nat eb pme (avail_dec on) false
                  ({["proc"]} ∪ lks)
                  (ap_lvlS lvl Hlvl) ltac:(pose proof (ap_K36 K HK); lia)
                  (ap_tf_align tfr Hpvtf) (ap_tf_bound tfr Hpvtf)
                  with "Hcg Hcpu Htext Hpc [Htfcell] Henv").
        all: try lkbelow.
        { iEval (rewrite HF6a0). iExact "Htfcell". }
        iApply wp_next_off_intro.
        iIntros (mpt) "Hcg Hcpu Hpc Htfcell Hppt %Hcspt".
        iEval (rewrite HF6a0) in "Htfcell".
        assert (Hp52 : ret_pc (F6 !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0xac))
          by (rewrite HF6ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp52) in "Hpc".
        set (tfp := (autocast (T := mword) (subrange_vec_dec tfr 55 12) : mword 44)).
        assert (Hbasetf : page_base tfp = tfr) by (apply page_base_of_valid; exact Hpvtf).
        assert (Hpt_s1 : mpt !!! Regidx ap_s1 = proc_addr k).
        { rewrite (callee_saved_lookup Hcspt ap_s1 ltac:(vm_compute; reflexivity)). exact HF6s1. }
        assert (Hpt_csp : mpt !!! Regidx csp_rs1 = spd).
        { rewrite (callee_saved_lookup Hcspt csp_rs1 ltac:(vm_compute; reflexivity)). exact HF6csp. }
        assert (Hpt_rest : forall r : mword 5, is_cs_idx r = true ->
                             r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                             mpt !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          rewrite (callee_saved_lookup Hcspt r Hr).
          exact (HF6rest r Hr Ncsp N8 N9 N18). }
        (* +0xac c.mv s2,a0 *)
        iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xac)) ap_s2 ap_a0 mpt (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (api_ac with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_a0) in "Hcg".
        set (F7 := <[Regidx ap_s2 := regval_into_reg (add_vec zero_reg (mpt !!! Regidx ap_a0))]> mpt).
        change (<[Regidx ap_s2 := regval_into_reg (add_vec zero_reg (mpt !!! Regidx ap_a0))]> mpt) with F7.
        assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xac) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xae)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp54) in "Hpc".
        assert (HF7s1 : F7 !!! Regidx ap_s1 = proc_addr k)
          by (rewrite /F7 upd_ne; [exact Hpt_s1 | vm_compute; discriminate]).
        (* the returned word, still UNINSPECTED: +0xac and +0xae move it
           without branching on it, so [Hppt] stays whole until +0xb0. *)
        assert (HF7a0 : F7 !!! Regidx ap_a0 = mpt !!! Regidx ap_a0)
          by (rewrite /F7 upd_ne; [reflexivity | vm_compute; discriminate]).
        (* +0xae c.sd a0,80(s1) : p->pagetable = the table *)
        assert (Hpgaddr : add_vec (F7 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 80 : mword 12))
                          = p_pagetable (proc_addr k))
          by (rewrite HF7s1; apply ap_off_80).
        iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xae)) ap_a0 ap_s1
                  (mword_of_int 80 : mword 12) F7 (trap_res b + (K - 4))%nat (zero_reg : mword 64) false
                  with "Hcg Hpc [] [Hpgcell]").
        { iApply (api_ae with "Htext"). }
        { iEval (rewrite ap_rg_s1 Hpgaddr). iExact "Hpgcell". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hpgcell".
        iEval (rewrite ap_rg_s1 Hpgaddr ap_rg_a0 HF7a0) in "Hpgcell".
        assert (Hp56 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xae) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xb0)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp56) in "Hpc".
        (* +0xb0 c.beqz a0 : the page table's verdict *)
        iDestruct "Hppt" as "[(%t & %Hroot & Htree & %Hrep & %Hnodes & Henv)
                            | (%Hptz & %Hdry & #Henv)]".
        2: { (* ============ TAIL 2: proc_pagetable failed, +0xf0 ============
               p->pagetable is the zero this arm just stored, but p->trapframe
               is a LIVE kalloc page: freeproc runs at [None]/[Some] and kfrees
               it.  That asymmetry is the whole reason [fp_pt] / [fp_tf] are
               INDEPENDENTLY optional. *)
          assert (Hptz0 : mpt !!! Regidx ap_a0 = (zero_reg : mword 64))
            by (rewrite Hptz; exact ap_zero_of_int).
          iEval (rewrite Hptz0) in "Hpgcell".
          assert (Hz56 : eq_vec (rget (CID := CIDf) F7 ap_a0) (zero_reg : mword 64) = true)
            by (rewrite ap_rg_a0 HF7a0 Hptz; exact ap_zero_eqz).
          iApply (wp_cbeqz_taken_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xb0)) (mword_of_int 32 : mword 8)
                    (Cregidx (mword_of_int 2)) ap_a0 F7 (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                    Hz56 ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (api_b0 with "Htext"). }
          iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Htgt96 : add_vec (mword_of_int (KernelSyms.allocproc + 0xb0) : mword 64)
                             (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 32 : mword 8) ('b"0"))))
                           = mword_of_int (KernelSyms.allocproc + 0xf0))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt96) in "Hpc".
          assert (HF7csp : F7 !!! Regidx csp_rs1 = spd)
            by (rewrite /F7 upd_ne; [exact Hpt_csp | vm_compute; discriminate]).
          assert (HF7s2 : F7 !!! Regidx ap_s2 = (zero_reg : mword 64)).
          { rewrite /F7 upd_eq add_vec_zero_l. exact Hptz0. }
          assert (HF7rest : forall r : mword 5, is_cs_idx r = true ->
                              r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                              F7 !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9 N18.
            rewrite /F7 upd_ne; [| congruence].
            exact (Hpt_rest r Hr Ncsp N8 N9 N18). }
          (* +0xf0 c.mv a0,s1 *)
          iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xf0)) ap_a0 ap_s1 F7 (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (api_f0 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
          set (U1 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (F7 !!! Regidx ap_s1))]> F7).
          change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (F7 !!! Regidx ap_s1))]> F7) with U1.
          assert (Hp98 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xf0) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xf2)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp98) in "Hpc".
          (* +0xf2 jal ra,freeproc *)
          iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xf2)) ap_ra (mword_of_int 2096810 : mword 21)
                    U1 (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (api_f2 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          set (U2 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xf2) : mword 64) 4)]> U1).
          change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xf2) : mword 64) 4)]> U1) with U2.
          assert (Hjfp2 : add_vec (mword_of_int (KernelSyms.allocproc + 0xf2) : mword 64) (sign_extend' 64 (mword_of_int 2096810 : mword 21)) = mword_of_int KernelSyms.freeproc)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjfp2) in "Hpc".
          assert (HU2ra : U2 !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0xf2) : mword 64) 4)
            by (rewrite /U2 upd_eq; reflexivity).
          assert (HU2a0 : U2 !!! Regidx ap_a0 = proc_addr k).
          { rewrite /U2 upd_ne; [| vm_compute; discriminate].
            rewrite /U1 upd_eq add_vec_zero_l. exact HF7s1. }
          assert (HU2s1 : U2 !!! Regidx ap_s1 = proc_addr k).
          { rewrite /U2 upd_ne; [| vm_compute; discriminate].
            rewrite /U1 upd_ne; [| vm_compute; discriminate]. exact HF7s1. }
          assert (HU2s2 : U2 !!! Regidx ap_s2 = (zero_reg : mword 64)).
          { rewrite /U2 upd_ne; [| vm_compute; discriminate].
            rewrite /U1 upd_ne; [| vm_compute; discriminate]. exact HF7s2. }
          assert (HU2csp : U2 !!! Regidx csp_rs1 = spd).
          { rewrite /U2 upd_ne; [| vm_compute; discriminate].
            rewrite /U1 upd_ne; [| vm_compute; discriminate]. exact HF7csp. }
          assert (HU2rest : forall r : mword 5, is_cs_idx r = true ->
                              r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                              U2 !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9 N18.
            assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            rewrite /U2 upd_ne; [| congruence].
            rewrite /U1 upd_ne; [| congruence].
            exact (HF7rest r Hr Ncsp N8 N9 N18). }
          (* proc_pagetable already resealed the budget on its way out, so
             there is nothing left to seal here -- [Henv] arrives at [None]. *)
          (* ...and freeproc, stated only at the BUNDLE, takes the one-way
             projection; the named copy is what this arm reports. *)
          iDestruct (kalloc_env_at_env with "Henv") as "#Henvb".
          iDestruct (proc_ofiles_null_split γf (pv_fdg V) (proc_addr k) (pv_ofile V) Hof with "Hofiles")
            as "[Hofc Hofs]".
          iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
          iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
            "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
              %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
              %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb & _)".
          iDestruct (tf_page_of_page_own tfp _ ltac:(rewrite Hbasetf; exact Hpvtf)
                       with "Hkmapb [Hpgown]")
            as (tfws) "Htfpage".
          { rewrite Hbasetf. iExact "Hpgown". }
          (* p->lock is still held: freeproc's own held set is
             [{["proc"]} ∪ lks]. *)
          iApply (FP.wp_freeproc_sconf (CID := CIDf) γp γa U2 k γl V γg pidn USED ch None (Some (tfp, tfws))
                    (trap_res b + (K - 4))%nat eb pme (S lvl) ({["proc"]} ∪ lks)
                    ltac:(pose proof (ap_K44 K HK); lia) Hk (ap_lvlS lvl Hlvl) HU2a0
                    with "Hcg Hcpu Htext Hpc Hpidlk [Hlocked Hstate Hpg Hchan Hkilled Hxstate Hpidinv] [Hpidown Hfields Hofc Hofs Hspare Hirsp Hbsp Hkst Hctx] Hrow Hsg Hpr Hxb [Hpgcell] [Htfcell Htfpage] Henvb").
          all: try lkbelow.
          { rewrite /proc_held. iFrame "Hlocked Hstate Hpg Hchan".
            iExists kl, xs, pidn. iFrame "Hkilled Hxstate Hpidinv". }
          { rewrite /fp_rest. iSplitR.
            { iPureIntro. split; [exact Hof|]. split; [exact Hcwd|]. exact Hszb. }
            iFrame "Hpidown Hfields Hofc Hofs Hspare Hirsp Hbsp Hkst Hctx". }
          { rewrite /fp_pt. iExact "Hpgcell". }
          { rewrite /fp_tf. cbn [fst snd].
            iEval (rewrite -Hbasetf) in "Htfcell". iFrame "Htfcell Htfpage".
            iPureIntro. rewrite Hbasetf. exact Hpvtf. }
          iApply wp_next_off_intro.
          iIntros (mfp) "Hcg Hcpu Hpc %Hcsfp Hheld Hdorm".
          assert (Hp9c : ret_pc (U2 !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0xf6))
            by (rewrite HU2ra; apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp9c) in "Hpc".
          assert (Hfp_s1 : mfp !!! Regidx ap_s1 = proc_addr k).
          { rewrite (callee_saved_lookup Hcsfp ap_s1 ltac:(vm_compute; reflexivity)). exact HU2s1. }
          assert (Hfp_s2 : mfp !!! Regidx ap_s2 = (zero_reg : mword 64)).
          { rewrite (callee_saved_lookup Hcsfp ap_s2 ltac:(vm_compute; reflexivity)). exact HU2s2. }
          assert (Hfp_csp : mfp !!! Regidx csp_rs1 = spd).
          { rewrite (callee_saved_lookup Hcsfp csp_rs1 ltac:(vm_compute; reflexivity)). exact HU2csp. }
          assert (Hfp_rest : forall r : mword 5, is_cs_idx r = true ->
                               r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                               mfp !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9 N18.
            rewrite (callee_saved_lookup Hcsfp r Hr).
            exact (HU2rest r Hr Ncsp N8 N9 N18). }
          (* +0xf6 c.mv a0,s1 *)
          iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xf6)) ap_a0 ap_s1 mfp (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (api_f6 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
          set (U3 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (mfp !!! Regidx ap_s1))]> mfp).
          change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (mfp !!! Regidx ap_s1))]> mfp) with U3.
          assert (Hp9e : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xf6) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xf8)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp9e) in "Hpc".
          (* +0xf8 jal ra,release *)
          iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xf8)) ap_ra (mword_of_int 2093162 : mword 21)
                    U3 (trap_res b + (K - 4))%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (api_f8 with "Htext"). }
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          set (U4 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xf8) : mword 64) 4)]> U3).
          change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xf8) : mword 64) 4)]> U3) with U4.
          assert (Hjrel2 : add_vec (mword_of_int (KernelSyms.allocproc + 0xf8) : mword 64) (sign_extend' 64 (mword_of_int 2093162 : mword 21)) = mword_of_int KernelSyms.release)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjrel2) in "Hpc".
          assert (HU4ra : U4 !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0xf8) : mword 64) 4)
            by (rewrite /U4 upd_eq; reflexivity).
          assert (HU4a0 : U4 !!! Regidx ap_a0 = proc_addr k).
          { rewrite /U4 upd_ne; [| vm_compute; discriminate].
            rewrite /U3 upd_eq add_vec_zero_l. exact Hfp_s1. }
          assert (HU4s2 : U4 !!! Regidx ap_s2 = (zero_reg : mword 64)).
          { rewrite /U4 upd_ne; [| vm_compute; discriminate].
            rewrite /U3 upd_ne; [| vm_compute; discriminate]. exact Hfp_s2. }
          assert (HU4csp : U4 !!! Regidx csp_rs1 = spd).
          { rewrite /U4 upd_ne; [| vm_compute; discriminate].
            rewrite /U3 upd_ne; [| vm_compute; discriminate]. exact Hfp_csp. }
          assert (HU4rest : forall r : mword 5, is_cs_idx r = true ->
                              r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                              U4 !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9 N18.
            assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            rewrite /U4 upd_ne; [| congruence].
            rewrite /U3 upd_ne; [| congruence].
            exact (Hfp_rest r Hr Ncsp N8 N9 N18). }
          iDestruct "Hheld" as "(Hlocked & Hstate & Hpg & Hchan & Hpub)".
          iApply fupd_wp.
          iMod (pstate_whole_update (proc_addr k) _ UNUSED with "Hpg") as "Hpg".
          iDestruct (pstate_whole_split (proc_addr k) UNUSED) as "[Hwb _]".
          iDestruct ("Hwb" with "Hpg") as "[Hpg _]".
          iModIntro.
          iAssert (proc_lock_res γs γl (proc_addr k)) with "[Hstate Hpg Hchan Hpub Hdorm Hpark]" as "HR".
          { iApply (proc_lock_res_intro γs γl (proc_addr k) UNUSED (zero_reg : mword 64)
                      with "Hstate Hpg Hchan Hpub [Hdorm Hpark]").
            iApply (proc_slots_unused_intro γs (proc_addr k) with "Hdorm Hpark"). }
          assert (Hlka2 : add_vec (U4 !!! Regidx ap_a0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr k).
          { rewrite HU4a0.
            replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64)
              by (apply bv_eq; vm_compute; reflexivity).
            apply kv_addv_zero. }
          (* [b] IS [outb] ([cpu_own] forces it); pure re-spelling for release. *)
          iEval (rewrite Hbmatch) in "Hcg".
          iApply (Release.wp_release_sconf KT1 (CID := CIDf) γl (proc_addr k) "proc"%string (proc_lock_pay γs γl (proc_addr k)) U4 lvl eb pme (K - 4)%nat
                    ({["proc"]} ∪ lks)
                    Hlka2 ltac:(pose proof (ap_K10 K HK); lia)
                    with "Hcg Htext Hpc Hislock Hlocked HR Hcpu Hpay").
          rewrite -Hbmatch.
          iIntros (CIDg Hsg mrl) "Hcg Hpc %Hcsrl Hcpu".
          assert (Hsetback : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks)
      by (apply locks_add_del_below; lkbelow).
          iEval (rewrite Hsetback) in "Hcpu".
          assert (Hpa2 : ret_pc (U4 !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0xfc))
            by (rewrite HU4ra; apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpa2) in "Hpc".
          assert (Hrl_s2 : mrl !!! Regidx ap_s2 = (zero_reg : mword 64)).
          { rewrite (callee_saved_lookup Hcsrl ap_s2 ltac:(vm_compute; reflexivity)). exact HU4s2. }
          assert (Hrl_csp : mrl !!! Regidx csp_rs1 = spd).
          { rewrite (callee_saved_lookup Hcsrl csp_rs1 ltac:(vm_compute; reflexivity)). exact HU4csp. }
          assert (Hrl_rest : forall r : mword 5, is_cs_idx r = true ->
                               r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                               mrl !!! Regidx r = m !!! Regidx r).
          { intros r Hr Ncsp N8 N9 N18.
            rewrite (callee_saved_lookup Hcsrl r Hr).
            exact (HU4rest r Hr Ncsp N8 N9 N18). }
          (* +0xfc c.mv s1,s2 *)
          iApply (wp_cmv_s_sconf (CID := CIDg) (mword_of_int (KernelSyms.allocproc + 0xfc)) ap_s1 ap_s2 mrl (K - 4)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc []").
          { iApply (api_fc with "Htext"). }
          iIntros (CIDh Hsh) "Hcg Hpc". iEval (rewrite ap_rg_s2) in "Hcg".
          set (U5 := <[Regidx ap_s1 := regval_into_reg (add_vec zero_reg (mrl !!! Regidx ap_s2))]> mrl).
          change (<[Regidx ap_s1 := regval_into_reg (add_vec zero_reg (mrl !!! Regidx ap_s2))]> mrl) with U5.
          assert (Hpa4 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xfc) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xfe)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpa4) in "Hpc".
          (* +0xfe c.j +0xd2 *)
          iApply (wp_cj_s_sconf (CID := CIDh) (mword_of_int (KernelSyms.allocproc + 0xfe))
                    (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0"))) U5 (K - 4)%nat b
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (api_fe with "Htext"). }
          iIntros (CIDn Hsn). iApply bi.later_intro. iIntros "Hcg Hpc".
          assert (Htgt78b : add_vec (mword_of_int (KernelSyms.allocproc + 0xfe) : mword 64)
                              (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0"))))
                            = mword_of_int (KernelSyms.allocproc + 0xd2))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt78b) in "Hpc".
          iEval (rewrite /ap_tail) in "Htl".
          iApply ("Htl" $! 0%nat b CIDn U5 (zero_reg : mword 64) with "[%] Hcg Hpc").
          { split; [rewrite /U5 upd_ne; [exact Hrl_csp | vm_compute; discriminate]|].
            split; [rewrite /U5 upd_eq add_vec_zero_l; exact Hrl_s2|].
            intros r Hr Ncsp N8 N9 N18.
            rewrite /U5 upd_ne; [| congruence].
            exact (Hrl_rest r Hr Ncsp N8 N9 N18). }
          iIntros (CIDp Hsp Mf) "[%Hcsf %Ha0f] Hcgf Hpcf".
          iDestruct (cpu_own_transport CIDg CIDp lvl eb pme b ltac:(wp_next_chain)
                       with "Hcpu") as "Hcpu".
          iSpecialize ("Hcont" $! CIDp with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! Mf with "[%] Hpcf").
          { exact Hcsf. }
          iEval (rewrite Ha0f).
          rewrite /allocproc_post. iRight. iRight.
          iSplitR; [done|].
          iSplitR.
          { iPureIntro. destruct Hdry as (n & Hn & Hz).
            exists (S n). split; [exact (ap_nodes_le n Hn)|].
            rewrite -ap_sub_dec. exact Hz. }
          iFrame "Hcgf Hcpu Henv Hpav". }
        (* the table was built: p->pagetable holds its root page *)
        assert (Hroot' : mpt !!! Regidx ap_a0 = page_base (pt_base t)) by exact Hroot.
        iEval (rewrite Hroot') in "Hpgcell".
        iDestruct (ptree_own_page_valid 2 (DfracOwn 1) t with "Htree") as %Hpvroot.
        iApply (wp_cbeqz_fall_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xb0)) (mword_of_int 32 : mword 8)
                  (Cregidx (mword_of_int 2)) ap_a0 F7 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite ap_rg_a0 HF7a0 Hroot'; exact (ap_valid_nz _ Hpvroot))
                  with "Hcg Hpc []").
        { iApply (api_b0 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xb0) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xb2)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp58) in "Hpc".
        (* +0xb2 li a2,112 *)
        iDestruct (sie_cap_gpr_x0 (CID := CIDf) F7 (trap_res b + (K - 4))%nat false pme ap_x0 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
        iApply (wp_addi4_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xb2)) ap_a2 ap_x0 (mword_of_int 112 : mword 12) F7 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (api_b2 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_x0) in "Hcg".
        set (G1 := <[Regidx ap_a2 := regval_into_reg
            (add_vec (F7 !!! Regidx ap_x0) (sign_extend' 64 (mword_of_int 112 : mword 12)))]> F7).
        change (<[Regidx ap_a2 := regval_into_reg
            (add_vec (F7 !!! Regidx ap_x0) (sign_extend' 64 (mword_of_int 112 : mword 12)))]> F7) with G1.
        assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xb2) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0xb6)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp5c) in "Hpc".
        (* +0xb6 c.li a1,0 *)
        iApply (wp_cli_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xb6)) ap_a1 (mword_of_int 0 : mword 6)
                  (zero_reg : mword 64) G1 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ap_li_zero
                  with "Hcg Hpc []").
        { iApply (api_b6 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (G2 := <[Regidx ap_a1 := regval_into_reg (zero_reg : mword 64)]> G1).
        change (<[Regidx ap_a1 := regval_into_reg (zero_reg : mword 64)]> G1) with G2.
        assert (Hp5e : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xb6) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xb8)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp5e) in "Hpc".
        assert (HG2s1 : G2 !!! Regidx ap_s1 = proc_addr k).
        { rewrite /G2 upd_ne; [| vm_compute; discriminate].
          rewrite /G1 upd_ne; [| vm_compute; discriminate]. exact HF7s1. }
        (* +0xb8 addi a0,s1,96 : &p->context *)
        iApply (wp_addi4_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xb8)) ap_a0 ap_s1 (mword_of_int 96 : mword 12) G2 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (api_b8 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
        set (G3 := <[Regidx ap_a0 := regval_into_reg
            (add_vec (G2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 96 : mword 12)))]> G2).
        change (<[Regidx ap_a0 := regval_into_reg
            (add_vec (G2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 96 : mword 12)))]> G2) with G3.
        assert (Hp62 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xb8) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0xbc)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp62) in "Hpc".
        assert (HG3a0 : G3 !!! Regidx ap_a0 = p_context (proc_addr k)).
        { rewrite /G3 upd_eq HG2s1. apply ap_off_96. }
        assert (HG3a1 : G3 !!! Regidx ap_a1 = (zero_reg : mword 64)).
        { rewrite /G3 upd_ne; [| vm_compute; discriminate].
          rewrite /G2 upd_eq. reflexivity. }
        assert (HG3a2 : G3 !!! Regidx ap_a2 = (mword_of_int (Z.of_nat 112) : mword 64)).
        { rewrite /G3 upd_ne; [| vm_compute; discriminate].
          rewrite /G2 upd_ne; [| vm_compute; discriminate].
          rewrite /G1 upd_eq Hx0. apply ap_li_112. }
        assert (HG3s1 : G3 !!! Regidx ap_s1 = proc_addr k).
        { rewrite /G3 upd_ne; [| vm_compute; discriminate]. exact HG2s1. }
        assert (HG3csp : G3 !!! Regidx csp_rs1 = spd).
        { rewrite /G3 upd_ne; [| vm_compute; discriminate].
          rewrite /G2 upd_ne; [| vm_compute; discriminate].
          rewrite /G1 upd_ne; [| vm_compute; discriminate].
          rewrite /F7 upd_ne; [| vm_compute; discriminate]. exact Hpt_csp. }
        assert (HG3rest : forall r : mword 5, is_cs_idx r = true ->
                            r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                            G3 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N11 : r <> mword_of_int 11) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N12 : r <> mword_of_int 12) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /G3 upd_ne; [| congruence].
          rewrite /G2 upd_ne; [| congruence].
          rewrite /G1 upd_ne; [| congruence].
          rewrite /F7 upd_ne; [| congruence].
          exact (Hpt_rest r Hr Ncsp N8 N9 N18). }
        (* +0xbc jal ra,memset : zero the 112-byte save area *)
        iDestruct (own_ctx_bytes (p_context (proc_addr k)) with "Hctx") as "[Hbw Hctxback]".
        (* A6.87: [byte_any] IS the visibility-free byte, so the window goes
           straight into the free memset engine -- there is nothing to name. *)
        iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xbc)) ap_ra (mword_of_int 2093278 : mword 21)
                  G3 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (api_bc with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (G4 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xbc) : mword 64) 4)]> G3).
        change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0xbc) : mword 64) 4)]> G3) with G4.
        assert (Hjms : add_vec (mword_of_int (KernelSyms.allocproc + 0xbc) : mword 64) (sign_extend' 64 (mword_of_int 2093278 : mword 21)) = mword_of_int KernelSyms.memset)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjms) in "Hpc".
        assert (HG4ra : G4 !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0xbc) : mword 64) 4) by (rewrite /G4 upd_eq; reflexivity).
        assert (HG4a0 : G4 !!! Regidx ap_a0 = p_context (proc_addr k))
          by (rewrite /G4 upd_ne; [exact HG3a0 | vm_compute; discriminate]).
        assert (HG4a1 : G4 !!! Regidx ap_a1 = (zero_reg : mword 64))
          by (rewrite /G4 upd_ne; [exact HG3a1 | vm_compute; discriminate]).
        assert (HG4a2 : G4 !!! Regidx ap_a2 = (mword_of_int (Z.of_nat 112) : mword 64))
          by (rewrite /G4 upd_ne; [exact HG3a2 | vm_compute; discriminate]).
        assert (HG4s1 : G4 !!! Regidx ap_s1 = proc_addr k)
          by (rewrite /G4 upd_ne; [exact HG3s1 | vm_compute; discriminate]).
        assert (HG4csp : G4 !!! Regidx csp_rs1 = spd)
          by (rewrite /G4 upd_ne; [exact HG3csp | vm_compute; discriminate]).
        assert (HG4rest : forall r : mword 5, is_cs_idx r = true ->
                            r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                            G4 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /G4 upd_ne; [| congruence].
          exact (HG3rest r Hr Ncsp N8 N9 N18). }
        (* memset's contract is context-indexed; this caller is not yet
           converted, so it mints a context for the call (SC-only move,
           becomes a compile error at cutover -- the leftover-work marker). *)
        iApply (MS.wp_memset_free_sconf KT1 KT0 (CID := CIDf) G4 (trap_res b + (K - 4))%nat 112 (zero_reg : mword 64) false pme
                  ltac:(pose proof (ap_K2 K HK); lia) ltac:(vm_compute; reflexivity) HG4a1 HG4a2
                  with "Hcg Htext Hpc [Hbw]").
        (* the byte window is ALREADY a ctx fact (ByteBuf is flipped) and so is
           memset's contract: the flip-era shim crossing here was a no-op under
           the permeable seal and is simply wrong now. *)
        { iEval (rewrite HG4a0). iExact "Hbw". }
        iApply wp_next_off_intro. iIntros (mms) "Hcg Hpc Hbw %Hcsms".
        (* ...and [ProcInv.own_ctx_bytes]'s closer wants the ctx window back,
           so no conversion here either. *)
        iEval (rewrite HG4a0) in "Hbw".
        assert (Hp66 : ret_pc (G4 !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0xc0))
          by (rewrite HG4ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp66) in "Hpc".
        iDestruct ("Hctxback" $! (fun _ => nth_byte (autocast (T := mword)
                     (subrange_vec_dec (zero_reg : mword 64) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0)
                    with "Hbw") as (ws) "[%Hwslen Hws]".
        assert (Hms_s1 : mms !!! Regidx ap_s1 = proc_addr k).
        { rewrite (callee_saved_lookup Hcsms ap_s1 ltac:(vm_compute; reflexivity)). exact HG4s1. }
        assert (Hms_csp : mms !!! Regidx csp_rs1 = spd).
        { rewrite (callee_saved_lookup Hcsms csp_rs1 ltac:(vm_compute; reflexivity)). exact HG4csp. }
        assert (Hms_rest : forall r : mword 5, is_cs_idx r = true ->
                             r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                             mms !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          rewrite (callee_saved_lookup Hcsms r Hr).
          exact (HG4rest r Hr Ncsp N8 N9 N18). }
        (* the fourteen context cells, with slots 0 and 1 peeled off *)
        destruct ws as [| w0 ws1]; [ cbn in Hwslen; lia |].
        destruct ws1 as [| w1 rest]; [ cbn in Hwslen; lia |].
        assert (Hrestlen : length rest = 12%nat) by (cbn in Hwslen; lia).
        rewrite !big_sepL_cons.
        iDestruct "Hws" as "(Hc0 & Hc1 & Hcrest)".
        rewrite Nat.mul_0_r RiscvExtras.pa_add_0.
        (* +0xc0 auipc a5,0x0 ; +0xc4 addi a5,a5,-600 : a5 := forkret *)
        iApply (wp_auipc_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xc0)) ap_a5 (mword_of_int 0 : mword 20) mms (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (api_c0 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (H1 := <[Regidx ap_a5 := regval_into_reg
            (add_vec (mword_of_int (KernelSyms.allocproc + 0xc0) : mword 64) (auipc_off (mword_of_int 0 : mword 20)))]> mms).
        change (<[Regidx ap_a5 := regval_into_reg
            (add_vec (mword_of_int (KernelSyms.allocproc + 0xc0) : mword 64) (auipc_off (mword_of_int 0 : mword 20)))]> mms) with H1.
        assert (Hp6a : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xc0) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0xc4)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp6a) in "Hpc".
        iApply (wp_addi4_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xc4)) ap_a5 ap_a5 (mword_of_int 3436 : mword 12) H1 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (api_c4 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_a5) in "Hcg".
        set (H2 := <[Regidx ap_a5 := regval_into_reg
            (add_vec (H1 !!! Regidx ap_a5) (sign_extend' 64 (mword_of_int 3436 : mword 12)))]> H1).
        change (<[Regidx ap_a5 := regval_into_reg
            (add_vec (H1 !!! Regidx ap_a5) (sign_extend' 64 (mword_of_int 3436 : mword 12)))]> H1) with H2.
        assert (Hp6e : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xc4) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0xc8)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp6e) in "Hpc".
        assert (HH2a5 : H2 !!! Regidx ap_a5 = forkret_pc).
        { rewrite /H2 upd_eq /H1 upd_eq /forkret_pc.
          apply bv_eq; vm_compute; reflexivity. }
        assert (HH2s1 : H2 !!! Regidx ap_s1 = proc_addr k).
        { rewrite /H2 upd_ne; [| vm_compute; discriminate].
          rewrite /H1 upd_ne; [| vm_compute; discriminate]. exact Hms_s1. }
        (* +0xc8 c.sd a5,96(s1) : p->context.ra = forkret *)
        assert (Hctx0 : add_vec (H2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 96 : mword 12))
                        = p_context (proc_addr k))
          by (rewrite HH2s1; apply ap_off_96).
        iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xc8)) ap_a5 ap_s1
                  (mword_of_int 96 : mword 12) H2 (trap_res b + (K - 4))%nat w0 false
                  with "Hcg Hpc [] [Hc0]").
        { iApply (api_c8 with "Htext"). }
        { iEval (rewrite ap_rg_s1 Hctx0). iExact "Hc0". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hc0". iEval (rewrite ap_rg_s1 Hctx0 ap_rg_a5 HH2a5) in "Hc0".
        assert (Hp70 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xc8) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xca)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp70) in "Hpc".
        (* +0xca c.ld a5,64(s1) : a5 := p->kstack *)
        iDestruct (procs_inv_kstack γs k γl Hγl with "Hpinv") as (ks) "#Hks".
        assert (Hksaddr : add_vec (H2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                          = p_kstack (proc_addr k))
          by (rewrite HH2s1; apply ap_off_64).
        iApply (wp_cld_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xca)) ap_a5 ap_s1
                  (mword_of_int 64 : mword 12) H2 (trap_res b + (K - 4))%nat ks false (dqm := DfracDiscarded)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc [] []").
        { iApply (api_ca with "Htext"). }
        { iEval (rewrite ap_rg_s1 Hksaddr). rewrite /is_kstack. iExact "Hks". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc _".
        set (H3 := <[Regidx ap_a5 := regval_into_reg ks]> H2).
        change (<[Regidx ap_a5 := regval_into_reg ks]> H2) with H3.
        assert (Hp72 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xca) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xcc)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp72) in "Hpc".
        (* +0xcc c.lui a4,0x1 *)
        iApply (wp_clui_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xcc)) ap_a4
                  (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64) H3 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ap_lui_pgsize
                  with "Hcg Hpc []").
        { iApply (api_cc with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (H4 := <[Regidx ap_a4 := regval_into_reg (mword_of_int 4096 : mword 64)]> H3).
        change (<[Regidx ap_a4 := regval_into_reg (mword_of_int 4096 : mword 64)]> H3) with H4.
        assert (Hp74 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xcc) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xce)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp74) in "Hpc".
        (* +0xce c.add a5,a5,a4 *)
        iApply (wp_cadd_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xce)) ap_a5 ap_a4 H4 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (api_ce with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_a5 ap_rg_a4) in "Hcg".
        set (H5 := <[Regidx ap_a5 := regval_into_reg
            (add_vec (H4 !!! Regidx ap_a5) (H4 !!! Regidx ap_a4))]> H4).
        change (<[Regidx ap_a5 := regval_into_reg
            (add_vec (H4 !!! Regidx ap_a5) (H4 !!! Regidx ap_a4))]> H4) with H5.
        assert (Hp76 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xce) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xd0)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp76) in "Hpc".
        assert (HH4a5 : H4 !!! Regidx ap_a5 = ks).
        { rewrite /H4 upd_ne; [| vm_compute; discriminate].
          rewrite /H3 upd_eq. reflexivity. }
        assert (HH5a5 : H5 !!! Regidx ap_a5 = add_vec ks (mword_of_int 4096)).
        { rewrite /H5 upd_eq HH4a5 /H4 upd_eq. reflexivity. }
        assert (HH5s1 : H5 !!! Regidx ap_s1 = proc_addr k).
        { rewrite /H5 upd_ne; [| vm_compute; discriminate].
          rewrite /H4 upd_ne; [| vm_compute; discriminate].
          rewrite /H3 upd_ne; [| vm_compute; discriminate]. exact HH2s1. }
        (* +0xd0 c.sd a5,104(s1) : p->context.sp = p->kstack + PGSIZE *)
        assert (Hctx1 : add_vec (H5 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 104 : mword 12))
                        = pa_add (p_context (proc_addr k)) 8)
          by (rewrite HH5s1; apply ap_off_104).
        iApply (wp_csd_s_sconf (kt := KT1) (ktd := KT0) (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0xd0)) ap_a5 ap_s1
                  (mword_of_int 104 : mword 12) H5 (trap_res b + (K - 4))%nat w1 false
                  with "Hcg Hpc [] [Hc1]").
        { iApply (api_d0 with "Htext"). }
        { iEval (rewrite ap_rg_s1 Hctx1). iExact "Hc1". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hc1". iEval (rewrite ap_rg_s1 Hctx1 ap_rg_a5 HH5a5) in "Hc1".
        assert (Hp78 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0xd0) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0xd2)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp78) in "Hpc".
        (* ---------- assemble the private block and hand it to the tail ------- *)
        iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhw Hcg]".
        iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
          "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
            %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
            %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb & _)".
        iDestruct (tf_page_of_page_own tfp _ ltac:(rewrite Hbasetf; exact Hpvtf)
                     with "Hkmapb [Hpgown]")
          as (tfws) "Htfpage".
        { rewrite Hbasetf. iExact "Hpgown". }
        iDestruct (proc_pt_intro_ppt t tfp Hrep ltac:(rewrite Hbasetf; exact Hpvtf) with "Htree") as "Hpt".
        iAssert (proc_pt_at (proc_addr k) (upt_desc (pt_base t) tfp) ∅)
          with "[Hpgcell Htfcell Hpt]" as "Hptat".
        { rewrite /proc_pt_at. cbn [ud_root ud_tfp].
          iFrame "Hpt". iSplitL "Hpgcell"; [iExact "Hpgcell"|].
          iEval (rewrite -Hbasetf) in "Htfcell". iExact "Htfcell". }
        (* THE BLOCK'S MEMORY CONJUNCT IS THE LAZY sz-REGION VIEW
           ([ProcDefs.proc_priv_bare]), so the address space just built is
           re-viewed at [p->sz] before it goes in.  The image is anonymous
           here and that is right: a fresh table maps nothing, so every va
           below the size reads as the 0 the lazy view records, and
           [ProcPtOwn.proc_ptm_at_of_pt_at] is exactly that re-viewing. *)
        iDestruct (proc_ptm_at_of_pt_at (proc_addr k) (upt_desc (pt_base t) tfp)
                     (uint (pv_sz V)) ∅ with "Hptat") as "[_ Hptat]".
        iDestruct "Hptat" as (M0) "[_ Hptat]".
        (* THE SLOT'S NEW INCARNATION WAS MINTED IN THE PID SECTION, which is
           where both halves of what it pins exist at once: the pid
           <allocpid> just chose and the name the registration is keyed to
           ([wp_ap_pidsec]'s post).  The block RECORDS the name and nothing
           in the block reads it, which is why every resource below is at
           [V]'s projections unchanged. *)
        iDestruct (proc_priv_nocwd_intro γf (proc_addr k) pidn
                     (MkUstate (upd_gen V γg) M0) (upt_desc (pt_base t) tfp) tfws
                     Hszb (um_below_empty (pv_sz V))
                     (* WHAT THE LAZY BIT CLAIMS OF THE FRESH TABLE, and it
                        claims nothing: the dormant block this one is built
                        from is at [ProcDefs.pv_lazy = true] (lane
                        LAZY-FLAG, K2), so the invariant's implication is
                        vacuous -- which is what lets allocproc install an
                        empty user map. *)
                     ltac:(cbn [us_V upd_gen pv_lazy]; rewrite Hlzv;
                           intro Hc; discriminate Hc)
                     with "Hpidown Hfields Hptat [Htfpage] Hofiles") as "Hpriv".
        { cbn [ud_tfp]. iExact "Htfpage". }
        iEval (rewrite /ap_tail) in "Htl".
        iApply ("Htl" $! (trap_res b) false CIDf H5 (proc_addr k) with "[%] Hcg Hpc").
        { split; [| split].
          - rewrite /H5 upd_ne; [| vm_compute; discriminate].
            rewrite /H4 upd_ne; [| vm_compute; discriminate].
            rewrite /H3 upd_ne; [| vm_compute; discriminate].
            rewrite /H2 upd_ne; [| vm_compute; discriminate].
            rewrite /H1 upd_ne; [| vm_compute; discriminate]. exact Hms_csp.
          - exact HH5s1.
          - intros r Hr Ncsp N8 N9 N18.
            assert (N14 : r <> mword_of_int 14) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            assert (N15 : r <> mword_of_int 15) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
            rewrite /H5 upd_ne; [| congruence].
            rewrite /H4 upd_ne; [| congruence].
            rewrite /H3 upd_ne; [| congruence].
            rewrite /H2 upd_ne; [| congruence].
            rewrite /H1 upd_ne; [| congruence].
            exact (Hms_rest r Hr Ncsp N8 N9 N18). }
        (* the epilogue runs at the literal [false] here -- the lock is still
           held, so the hart cannot move and [wp_next] collapses. *)
        iApply wp_next_off_intro.
        iIntros (Mf) "[%Hcsf %Ha0f] Hcgf Hpcf".
        (* MINT THE MARKER, here and not earlier: the two freeproc tails put
           the slot back at UNUSED and must not spend a slot of the count,
           so the only path that pays is the one that keeps the slot. *)
        iApply fupd_wp.
        iMod (pslot_mint ⊤ op k ltac:(solve_ndisj) with "Hpav") as "[Hpav #Hmkk]".
        iDestruct (pslot_used_at_intro k Hk with "Hmkk") as "#Hmk".
        iModIntro.
        iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! Mf with "[%] Hpcf").
        { exact Hcsf. }
        iEval (rewrite Ha0f).
        (* the post is now THREE-way; the found arm is the middle one *)
        rewrite /allocproc_post. iRight. iLeft.
        iExists k, γl, ch, pidn,
                (us_pt (MkUstate (upd_gen V γg) M0) (upt_desc (pt_base t) tfp) tfws),
                (pt_base t), tfp, ks, rest, (S (pt_nodes t)).
        iSplitR.
        { iPureIntro. split; [reflexivity|]. split; [exact Hk|]. split; [exact Hγl|].
          split; [exact Hpidnb|]. split; [reflexivity|].
          cbn [us_pt upd_usV us_V us_M upd_pt upd_gen pv_ofile pv_cwd pv_fdg pv_gen].
          split; [exact Hof|]. split; [exact Hcwd|].
          split; [exact Hrestlen|]. exact (ap_nodes_le (pt_nodes t) Hnodes). }
        iSplitL "Hlocked Hstate Hpg Hchan Hkilled Hxstate Hpidinv".
        { rewrite /proc_held. iFrame "Hlocked Hstate Hpg Hchan".
          iExists kl, xs, pidn. iFrame "Hkilled Hxstate Hpidinv". }
        iFrame "Hkst".
        iFrame "Hpark Hpriv Hgen Hsg Hpr Hfrag Hrow Hxb Hmk Hspare Hirsp Hbsp Hks".
        iSplitL "Hc0 Hc1 Hcrest".
        { rewrite ctx_cells_run !big_sepL_cons Nat.mul_0_r RiscvExtras.pa_add_0.
          iFrame "Hc0 Hc1 Hcrest". }
        iFrame "Hcgf Hcpu Hpay".
        (* proc_pagetable was called with the trapframe page already spent, so
           its [pt_nodes t] more is allocproc's [S (pt_nodes t)] total *)
        iSplitL "Henv"; [rewrite -(ap_sub_dec on (pt_nodes t)); iExact "Henv" |].
        iExact "Hpav".
      - (* ============ NOT FREE: release and step ============ *)
        assert (Hcmpr : eq_vec (rget (CID := CIDf) L3 ap_a5) (zero_reg : mword 64) = false)
          by (rewrite ap_rg_a5; exact Hcmp).
        iApply (wp_cbeqz_fall_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0x24)) (mword_of_int 10 : mword 8)
                  (Cregidx (mword_of_int 7)) ap_a5 L3 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hcmpr
                  with "Hcg Hpc []").
        { iApply (api_24 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp26) in "Hpc".
        (* THE SLOT'S MARKER, kept.  [st <> UNUSED] here, so the slot is
           allocated and its [proc_slots] carries [pslot_used_at]; it is
           persistent, so taking a copy costs the lock resource nothing and
           the scan leaves this iteration one entry richer. *)
        assert (Hstnu : is_unused st = false) by (apply ap_is_unused_false; exact Hcmp).
        iDestruct (proc_slots_marker γs (proc_addr k) st Hstnu with "Hslots")
          as "[#Hmk Hslots]".
        iDestruct (pslot_used_at_elim k Hk with "Hmk") as "#Hmkk".
        iAssert ([∗ list] i ∈ seq 0 (S k), pslot_used i)%I as "#Hacc'".
        { rewrite seq_S big_sepL_app. iSplitR; [iExact "Hacc"|].
          rewrite big_sepL_singleton. iExact "Hmkk". }
        (* rebuild the lock resource: nothing moved *)
        iAssert (proc_lock_res γs γl (proc_addr k)) with "[Hstate Hpg Hchan Hpub Hslots]" as "HR".
        { iApply (proc_lock_res_intro γs γl (proc_addr k) st ch with "Hstate Hpg Hchan Hpub Hslots"). }
        (* +0x26 c.mv a0,s1 *)
        iApply (wp_cmv_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0x26)) ap_a0 ap_s1 L3 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (api_26 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
        set (R1 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (L3 !!! Regidx ap_s1))]> L3).
        change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (L3 !!! Regidx ap_s1))]> L3) with R1.
        assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp28) in "Hpc".
        (* +0x28 jal ra,release *)
        iApply (wp_jal_s_sconf (CID := CIDf) (mword_of_int (KernelSyms.allocproc + 0x28)) ap_ra (mword_of_int 2093370 : mword 21)
                  R1 (trap_res b + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (api_28 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (R2 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0x28) : mword 64) 4)]> R1).
        change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.allocproc + 0x28) : mword 64) 4)]> R1) with R2.
        assert (Hjrel : add_vec (mword_of_int (KernelSyms.allocproc + 0x28) : mword 64) (sign_extend' 64 (mword_of_int 2093370 : mword 21)) = mword_of_int KernelSyms.release)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjrel) in "Hpc".
        assert (HR2ra : R2 !!! Regidx ap_ra = add_vec_int (mword_of_int (KernelSyms.allocproc + 0x28) : mword 64) 4) by (rewrite /R2 upd_eq; reflexivity).
        assert (HR2a0 : R2 !!! Regidx ap_a0 = proc_addr k).
        { rewrite /R2 upd_ne; [| vm_compute; discriminate].
          rewrite /R1 upd_eq add_vec_zero_l. exact HL3s1. }
        assert (HR2s1 : R2 !!! Regidx ap_s1 = proc_addr k).
        { rewrite /R2 upd_ne; [| vm_compute; discriminate].
          rewrite /R1 upd_ne; [| vm_compute; discriminate]. exact HL3s1. }
        assert (HR2s2 : R2 !!! Regidx ap_s2 = proc_addr NPROC).
        { rewrite /R2 upd_ne; [| vm_compute; discriminate].
          rewrite /R1 upd_ne; [| vm_compute; discriminate]. exact HL3s2. }
        assert (HR2csp : R2 !!! Regidx csp_rs1 = spd).
        { rewrite /R2 upd_ne; [| vm_compute; discriminate].
          rewrite /R1 upd_ne; [| vm_compute; discriminate]. exact HL3csp. }
        assert (HR2rest : forall r : mword 5, is_cs_idx r = true ->
                            r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                            R2 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          assert (N10 : r <> mword_of_int 10) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /R2 upd_ne; [| congruence].
          rewrite /R1 upd_ne; [| congruence].
          exact (HL3rest r Hr Ncsp N8 N9 N18). }
        assert (Hlka : add_vec (R2 !!! Regidx ap_a0) (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr k).
        { rewrite HR2a0.
          replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64) with (mword_of_int 0 : mword 64)
            by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero. }
        (* [b] IS [outb] ([cpu_own] forces it); pure re-spelling for release. *)
        iEval (rewrite Hbmatch) in "Hcg".
        iApply (Release.wp_release_sconf KT1 (CID := CIDf) γl (proc_addr k) "proc"%string (proc_lock_pay γs γl (proc_addr k)) R2 lvl eb pme (K - 4)%nat
                  ({["proc"]} ∪ lks)
                  Hlka ltac:(pose proof (ap_K10 K HK); lia)
                  with "Hcg Htext Hpc Hislock Hlocked HR Hcpu Hpay").
        (* release's exit index is the very [match] [b] is equal to, so the
           back edge lands on the loop invariant unchanged. *)
        rewrite -Hbmatch.
        iIntros (CIDg Hsg mrel) "Hcg Hpc %Hcsrel Hcpu".
        assert (Hsetback : ({["proc"]} ∪ lks) ∖ {["proc"]} = lks)
      by (apply locks_add_del_below; lkbelow).
        iEval (rewrite Hsetback) in "Hcpu".
        assert (Hp2c : ret_pc (R2 !!! Regidx ap_ra) = mword_of_int (KernelSyms.allocproc + 0x2c))
          by (rewrite HR2ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp2c) in "Hpc".
        assert (Hrel_s1 : mrel !!! Regidx ap_s1 = proc_addr k).
        { rewrite (callee_saved_lookup Hcsrel ap_s1 ltac:(vm_compute; reflexivity)). exact HR2s1. }
        assert (Hrel_s2 : mrel !!! Regidx ap_s2 = proc_addr NPROC).
        { rewrite (callee_saved_lookup Hcsrel ap_s2 ltac:(vm_compute; reflexivity)). exact HR2s2. }
        assert (Hrel_csp : mrel !!! Regidx csp_rs1 = spd).
        { rewrite (callee_saved_lookup Hcsrel csp_rs1 ltac:(vm_compute; reflexivity)). exact HR2csp. }
        assert (Hrel_rest : forall r : mword 5, is_cs_idx r = true ->
                              r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                              mrel !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          rewrite (callee_saved_lookup Hcsrel r Hr).
          exact (HR2rest r Hr Ncsp N8 N9 N18). }
        (* +0x2c addi s1,s1,360 : p++ *)
        iApply (wp_addi4_s_sconf (CID := CIDg) (mword_of_int (KernelSyms.allocproc + 0x2c)) ap_s1 ap_s1 (mword_of_int 360 : mword 12) mrel (K - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (api_2c with "Htext"). }
        iIntros (CIDh Hsh) "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
        set (R3 := <[Regidx ap_s1 := regval_into_reg
            (add_vec (mrel !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> mrel).
        change (<[Regidx ap_s1 := regval_into_reg
            (add_vec (mrel !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> mrel) with R3.
        assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp30) in "Hpc".
        assert (HR3s1 : R3 !!! Regidx ap_s1 = proc_addr (S k)).
        { rewrite /R3 upd_eq Hrel_s1. exact (proc_addr_succ k). }
        assert (HR3s2 : R3 !!! Regidx ap_s2 = proc_addr NPROC)
          by (rewrite /R3 upd_ne; [exact Hrel_s2 | vm_compute; discriminate]).
        assert (HR3csp : R3 !!! Regidx csp_rs1 = spd)
          by (rewrite /R3 upd_ne; [exact Hrel_csp | vm_compute; discriminate]).
        assert (HR3rest : forall r : mword 5, is_cs_idx r = true ->
                            r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                            R3 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          rewrite /R3 upd_ne; [| congruence].
          exact (Hrel_rest r Hr Ncsp N8 N9 N18). }
        (* +0x30 bne s1,s2 *)
        destruct (Nat.eqb (S k) NPROC) eqn:Hend.
        + (* the array is exhausted: fall to +0x34 *)
          apply Nat.eqb_eq in Hend.
          assert (Hfall : neq_vec (rget (CID := CIDh) R3 ap_s1) (rget (CID := CIDh) R3 ap_s2) = false)
            by (rewrite ap_rg_s1 ap_rg_s2 HR3s1 HR3s2 Hend; exact ap_neq_end_eq).
          iApply (wp_bne_fall_s_sconf (CID := CIDh) (mword_of_int (KernelSyms.allocproc + 0x30)) (mword_of_int 8172 : mword 13)
                    ap_s2 ap_s1 R3 (K - 4)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hfall
                    with "Hcg Hpc []").
          { iApply (api_30 with "Htext"). }
          iIntros (CIDi Hsi) "Hcg Hpc".
          assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.allocproc + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp34) in "Hpc".
          (* +0x34 c.li s1,0 *)
          iApply (wp_cli_s_sconf (CID := CIDi) (mword_of_int (KernelSyms.allocproc + 0x34)) ap_s1 (mword_of_int 0 : mword 6)
                    (zero_reg : mword 64) R3 (K - 4)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) ap_li_zero
                    with "Hcg Hpc []").
          { iApply (api_34 with "Htext"). }
          iIntros (CIDj Hsj) "Hcg Hpc".
          set (R4 := <[Regidx ap_s1 := regval_into_reg (zero_reg : mword 64)]> R3).
          change (<[Regidx ap_s1 := regval_into_reg (zero_reg : mword 64)]> R3) with R4.
          assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.allocproc + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.allocproc + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp36) in "Hpc".
          (* +0x36 c.j +0x9c *)
          iApply (wp_cj_s_sconf (CID := CIDj) (mword_of_int (KernelSyms.allocproc + 0x36))
                    (sign_extend' 21 (concat_vec (mword_of_int 78 : mword 11) ('b"0"))) R4 (K - 4)%nat b
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (api_36 with "Htext"). }
          iIntros (CIDn Hsn). iApply bi.later_intro. iIntros "Hcg Hpc".
          assert (Htgt78 : add_vec (mword_of_int (KernelSyms.allocproc + 0x36) : mword 64)
                             (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 78 : mword 11) ('b"0"))))
                           = mword_of_int (KernelSyms.allocproc + 0xd2))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt78) in "Hpc".
          iEval (rewrite /ap_tail) in "Htl".
          (* THE SCAN PASSED EVERY SLOT.  [S k = NPROC], so the record the
             loop has been accumulating covers the whole table, and that is
             what forces a counted caller's free count to 0
             ([ProcAvail.procs_avail_zero]) -- the fact the arm reports. *)
          iDestruct (procs_avail_zero op with "[Hacc'] Hpav") as "[%Hz Hpav]";
            [rewrite -Hend; iExact "Hacc'" |].
          iApply ("Htl" $! 0%nat b CIDn R4 (zero_reg : mword 64) with "[%] Hcg Hpc [Hcpu Henv Hpav Hcont]").
          { split; [rewrite /R4 upd_ne; [exact HR3csp | vm_compute; discriminate]|].
            split; [rewrite /R4; apply upd_eq|].
            intros r Hr Ncsp N8 N9 N18.
            rewrite /R4 upd_ne; [| congruence].
            exact (HR3rest r Hr Ncsp N8 N9 N18). }
          iIntros (CIDp Hsp Mf) "[%Hcsf %Ha0f] Hcgf Hpcf".
          iDestruct (cpu_own_transport CIDg CIDp lvl eb pme b ltac:(wp_next_chain)
                       with "Hcpu") as "Hcpu".
          iSpecialize ("Hcont" $! CIDp with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! Mf with "[%] Hpcf").
          { exact Hcsf. }
          iEval (rewrite Ha0f).
          rewrite /allocproc_post. iLeft. iFrame "Hcgf Hcpu Henv Hpav".
          iSplitR; [done | iPureIntro; exact Hz].
        + (* keep scanning: branch back to +0x1c *)
          assert (HkS : (S k < NPROC)%nat) by exact (ap_kS_lt k Hk Hend).
          assert (Htk : neq_vec (rget (CID := CIDh) R3 ap_s1) (rget (CID := CIDh) R3 ap_s2) = true)
            by (rewrite ap_rg_s1 ap_rg_s2 HR3s1 HR3s2; exact (ap_neq_end_lt (S k) HkS)).
          iApply (wp_bne_taken_s_sconf (CID := CIDh) (mword_of_int (KernelSyms.allocproc + 0x30)) (mword_of_int 8172 : mword 13)
                    ap_s2 ap_s1 R3 (K - 4)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Htk
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc []").
          { iApply (api_30 with "Htext"). }
          iApply bi.later_intro. iIntros (CIDi Hsi) "Hcg Hpc".
          assert (Htgt1c : add_vec (mword_of_int (KernelSyms.allocproc + 0x30) : mword 64)
                             (sign_extend' 64 (mword_of_int 8172 : mword 13)) = mword_of_int (KernelSyms.allocproc + 0x1c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt1c) in "Hpc".
          iDestruct (cpu_own_transport CIDg CIDi lvl eb pme b ltac:(wp_next_chain)
                       with "Hcpu") as "Hcpu".
          iSpecialize ("IHf" $! CIDi with "[%]"); [wp_next_chain|].
          iApply ("IHf" $! (S k) R3 with "[%] [%] [%] Htl Hcont Hcg Hcpu Henv Hpav Hacc' Hpc").
          * exact (ap_fuelS k fuel Hfuel).
          * exact HkS.
          * split; [exact HR3csp|]. split; [exact HR3s1|]. split; [exact HR3s2|].
            exact HR3rest. }
    (* ---- enter the scan at k = 0 ---- *)
    iDestruct (cpu_own_transport CID0 CID10 lvl eb pme b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hloop" $! NPROC).
    iSpecialize ("Hloop" $! CID10 with "[%]"); [wp_next_chain|].
    iApply ("Hloop" $! 0%nat A5 with "[%] [%] [%] Htail Hcont Hcg Hcpu [Henv] Hpav [] Hpc").
    - exact ap_fuel_init.
    - exact ap_zero_lt.
    - split; [exact HA5csp|]. split; [exact HA5s1|]. split; [exact HA5s2|].
      exact HA5rest.
    - iExact "Henv".
    - (* the scan has passed no slot yet *) done.
  Qed.

End ProofAllocproc.

End AllocprocCore.


(* ===================================================================== *)
(* THE COUNTED SEAL.                                                      *)
(*                                                                        *)
(* Thirty lines, and every one of them is the same observation: with more *)
(* than [K_allocproc] free pages in hand, neither the trapframe kalloc nor *)
(* proc_pagetable can run dry, so [allocproc_post]'s THIRD arm -- the one  *)
(* the freeproc tails produce -- is refutable and the caller never sees a  *)
(* resealed budget.  The instruction-level proof above knows nothing about *)
(* this; it is a property of the caller's premise, which is exactly why it *)
(* belongs here and not there.                                            *)
(* ===================================================================== *)
Module AllocprocSeal (Core : ALLOCPROC_GEN) : ALLOCPROC.

Section SealAllocproc.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId} `{XI : CurCtx}.

  Lemma wp_allocproc_sconf
      (γa : gname) (γk : gname * gname) (γp : gname) (γf : gname)
      (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
      (pme : mword 64) (on : option nat) (op : option nat)
      (b : bool) (lks : gset string)
    : wp_allocproc_sconf_body γa γk γp γf γs m lvl K eb pme on op b lks.
  Proof.
    cbv beta delta [wp_allocproc_sconf_body].
    intros pcE ret_tgt HK Hlvl Hex Hbelow.
    destruct Hex as (nb & Hon & Hnb). subst on.
    iIntros "Hcg Hcpu #Htext Hpc #Hprocs #Hpidlk Henv Hpav Hcont".
    iApply (Core.wp_allocproc_core γa γk γp γf γs m lvl K eb pme (Some nb) op b lks HK Hlvl Hbelow
              with "Hcg Hcpu Htext Hpc Hprocs Hpidlk Henv Hpav").
    all: try lkbelow.
    iIntros (CIDx Hsx mr) "%Hcs Hpc Hpost".
    iSpecialize ("Hcont" $! CIDx with "[%]"); [exact Hsx|].
    iApply ("Hcont" $! mr with "[%] Hpc [Hpost]"); [exact Hcs|].
    iDestruct "Hpost" as "[Hnull | [Hfound | Hdead]]".
    - iLeft. iExact "Hnull".
    - iRight. iLeft. iExact "Hfound".
    - iDestruct "Hdead" as "(_ & %Hdry & _ & _ & _ & _)".
      destruct Hdry as (n & Hn & Hz).
      destruct (ap_refute_dry nb n Hnb Hn Hz).
  Qed.

End SealAllocproc.

End AllocprocSeal.
