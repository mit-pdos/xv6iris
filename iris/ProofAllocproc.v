(* ProofAllocproc.v -- the whole-function WP for allocproc().

   Fifty-five instructions @ 0x80001b28; see CodeAllocproc.v for the
   listing and SpecAllocproc.v for the contract.  Three parts:

   * the SCAN (+0x1c .. +0x30), a bounded fuel induction over proc[] that
     acquires each lock, reads [p->state] out of the invariant's
     always-resident row, and releases again -- the wakeup loop's shape,
     minus the myproc test;
   * the ALLOCATION BODY (+0x38 .. +0x76), which is where
     [ProcInv.proc_dormant] becomes [ProcInv.proc_priv]: the dormant block
     supplies the scalar cells, the null descriptor array and the second
     [p->pid] half; kalloc supplies the trapframe page
     ([ProcInv.tf_page_of_page_own]); proc_pagetable supplies the table
     ([ProcPtOwn.proc_pt_intro_ppt]);
   * the SHARED EPILOGUE (+0x78 .. +0x84), reached from both exits, which is
     why [SpecAllocproc.allocproc_post] is stated as a function of the
     RETURNED POINTER rather than inside the continuation.

   EXPLICIT-CPUID NOTE.  allocproc is [b]-GENERIC on the outside and pinned
   on the inside: from acquire's return (+0x22) to release's call (+0x28) --
   which includes the WHOLE allocation body -- a held lock forces the index to
   the literal [false], so those thirty leaves collapse with [wp_next_off] and
   read exactly as they did before the refactor, all at acquire's exit hart
   [CIDf].  Only the prologue, the loop head, the post-release tail and the
   epilogue are hart-generic.

   The two exits leave at DIFFERENT indices -- the found arm RETURNS HOLDING
   p->lock, so acquire's unbalanced [false] propagates out to the caller,
   while the null arm releases and exits at [b].  That is why
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
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile InstrBytes WpMmodeLeafBase WpAuipc.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import WpLock.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import ArrCursor.
Require Import PageGeom KallocInv ByteBuf.
Require Import PtTree PtBuild.
Require Import UserPtTree ProcPtOwn.
Require Import ProcGeom CpuOwn.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import KvmSpec.
Require Import SpecAcquire SpecRelease SpecAllocpid SpecKalloc SpecProcPagetable SpecMemset.
Require Import SpecProcinit.
Require Import SpecAllocproc.
Require Import CodeAllocproc.
From Kernel Require KernelInstrs KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import KernelRvcDecode.
Import Defs.
Local Open Scope Z_scope.
Set Printing Depth 40.

Notation AP := KernelSyms.allocproc.

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
Lemma ap_K4 (K : nat) : (40 <= K)%nat -> (4 <= K)%nat.
Proof. lia. Qed.
Lemma ap_K2 (K : nat) : (40 <= K)%nat -> (2 <= K - 4)%nat.
Proof. lia. Qed.
Lemma ap_K10 (K : nat) : (40 <= K)%nat -> (10 <= K - 4)%nat.
Proof. lia. Qed.
Lemma ap_K14 (K : nat) : (40 <= K)%nat -> (14 <= K - 4)%nat.
Proof. lia. Qed.
Lemma ap_K36 (K : nat) : (40 <= K)%nat -> (36 <= K - 4)%nat.
Proof. lia. Qed.
Lemma ap_Kback (K : nat) : (40 <= K)%nat -> ((K - 4) + 4)%nat = K.
Proof. lia. Qed.
Lemma ap_lvl1 (lvl : nat) : (Z.of_nat lvl + 2 < 2 ^ 31)%Z -> (Z.of_nat lvl + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.
Lemma ap_lvlS (lvl : nat) : (Z.of_nat lvl + 2 < 2 ^ 31)%Z -> (Z.of_nat (S lvl) + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.
Lemma ap_nb_pt (n : nat) : (K_allocproc < S n)%nat -> (K_proc_pagetable < n)%nat.
Proof. unfold K_allocproc, K_proc_pagetable. lia. Qed.
Lemma ap_nb_pos (n : nat) : (K_allocproc < n)%nat -> n <> 0%nat.
Proof. unfold K_allocproc. lia. Qed.
Lemma ap_nodes_le (n : nat) : (n <= K_proc_pagetable)%nat -> (S n <= K_allocproc)%nat.
Proof. unfold K_allocproc, K_proc_pagetable. lia. Qed.

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
Lemma ap_rg_ra `{CID : CpuId} (MM : regfile) : rget MM ap_ra = MM !!! Regidx ap_ra.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_s0 `{CID : CpuId} (MM : regfile) : rget MM ap_s0 = MM !!! Regidx ap_s0.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_s1 `{CID : CpuId} (MM : regfile) : rget MM ap_s1 = MM !!! Regidx ap_s1.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_s2 `{CID : CpuId} (MM : regfile) : rget MM ap_s2 = MM !!! Regidx ap_s2.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_a0 `{CID : CpuId} (MM : regfile) : rget MM ap_a0 = MM !!! Regidx ap_a0.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_a4 `{CID : CpuId} (MM : regfile) : rget MM ap_a4 = MM !!! Regidx ap_a4.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_a5 `{CID : CpuId} (MM : regfile) : rget MM ap_a5 = MM !!! Regidx ap_a5.
Proof. rgne. reflexivity. Qed.
Lemma ap_rg_x0 `{CID : CpuId} (MM : regfile) : rget MM ap_x0 = MM !!! Regidx ap_x0.
Proof. rgne. reflexivity. Qed.

(* ===================================================================== *)
(* THE SHARED EPILOGUE'S CONTRACT (+0x78 .. +0x84), as a HART-FREE        *)
(* proposition.                                                           *)
(*                                                                        *)
(* Both exits join at +0x78, but they arrive at DIFFERENT SIE indices --  *)
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
Definition ap_tail `{!riscvGS Σ, !sieG Σ}
    (Φ : mval -> iProp Σ) (m : regfile) (spd pme ret_tgt : mword 64) (K : nat) : iProp Σ :=
  (∀ (xb : bool) (CIDt : CpuId) (Mt : regfile) (rv : mword 64),
     ⌜ Mt !!! Regidx csp_rs1 = spd /\
       Mt !!! Regidx ap_s1 = rv /\
       (forall r : mword 5, is_cs_idx r = true ->
          r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
          Mt !!! Regidx r = m !!! Regidx r) ⌝ -∗
     sie_cap_gpr (CID := CIDt) Mt (K - 4)%nat xb pme -∗
     pc_is (CID := CIDt) (mword_of_int (AP + 0x78)) -∗
     wp_next (CID0 := CIDt) xb pme (fun (CID : CpuId) =>
       ∀ (Mf : regfile),
         ⌜ callee_saved m Mf /\ Mf !!! Regidx ap_a0 = rv ⌝ -∗
         sie_cap_gpr Mf K xb pme -∗
         pc_is ret_tgt -∗
         WP (Loop : expr riscv_lang) {{ Φ }}) -∗
     WP (LoopE CIDt : expr riscv_lang) {{ Φ }})%I.

Module AllocprocProof (Acquire : ACQUIRE) (Release : RELEASE) (Allocpid : ALLOCPID)
                      (AK : KALLOC) (PPT : PROC_PAGETABLE) (MS : MEMSET) : ALLOCPROC.

Section ProofAllocproc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ, !fileG Σ, !fdslotG Σ}.
  (* The section's hart is called [CID0], NOT [CID]: the loop invariant, the
     epilogue and every leaf continuation bind a fresh [CID], and a section
     variable of that name would be shadowed by them -- while the lemma's own
     anchor has to stay nameable from INSIDE those lambdas (that is what
     [wp_next (CID0 := CID0)] and [wp_next_chain] compose against). *)
  Context `{CID0 : CpuId}.

  Lemma wp_allocproc_sconf
      (γa : gname) (γp : gname) (γf : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (m : regfile) (lvl K : nat) (eb : bool)
      (pme : mword 64) (C : iProp Σ) (on : option nat) (b : bool)
    : wp_allocproc_sconf_body γa γp γf Φ γs m lvl K eb pme C on b.
  Proof.
    cbv beta delta [wp_allocproc_sconf_body].
    intros pcE ret_tgt HK Hlvl Hex.
    destruct Hex as (nb & Hon & Hnb). subst on.
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcpu #Htext Hpc #Hpanic #Hprocs #Hpidlk Henv Hcont".
    iDestruct (procs_inv_len Φ γs with "Hprocs") as %Hlen.
    iAssert (procs_inv Φ γs) as "#Hpinv". { iExact "Hprocs". }
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
    iPoseProof (api_00 with "Htext") as "Hi00".
    iApply (wp_caddi_sp_push_s_sconf Φ pcE (mword_of_int 32 : mword 6) m K 4 b (ap_K4 K HK) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with M1.
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (AP + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
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
    iPoseProof (api_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (AP + 0x02)) (mword_of_int 3 : mword 6) ap_ra M1 (K - 4)%nat v1 b
              with "Hcg Hpc Hi02 [Hb1] [-]").
    { iEval (rewrite HcspM1 -Hb1a). iExact "Hb1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hb1".
    assert (Hp04 : add_vec_int (mword_of_int (AP + 0x02) : mword 64) 2 = mword_of_int (AP + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iPoseProof (api_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (AP + 0x04)) (mword_of_int 2 : mword 6) ap_s0 M1 (K - 4)%nat v2 b
              with "Hcg Hpc Hi04 [Hb2] [-]").
    { iEval (rewrite HcspM1 -Hb2a). iExact "Hb2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hb2".
    assert (Hp06 : add_vec_int (mword_of_int (AP + 0x04) : mword 64) 2 = mword_of_int (AP + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iPoseProof (api_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (AP + 0x06)) (mword_of_int 1 : mword 6) ap_s1 M1 (K - 4)%nat v3 b
              with "Hcg Hpc Hi06 [Hb3] [-]").
    { iEval (rewrite HcspM1 -Hb3a). iExact "Hb3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hb3".
    assert (Hp08 : add_vec_int (mword_of_int (AP + 0x06) : mword 64) 2 = mword_of_int (AP + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    iPoseProof (api_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (AP + 0x08)) (mword_of_int 0 : mword 6) ap_s2 M1 (K - 4)%nat v4 b
              with "Hcg Hpc Hi08 [Hb4] [-]").
    { iEval (rewrite HcspM1 -Hb4a). iExact "Hb4". }
    iIntros (CID5 Hs5) "Hcg Hpc Hb4".
    assert (Hp0a : add_vec_int (mword_of_int (AP + 0x08) : mword 64) 2 = mword_of_int (AP + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    iEval (rewrite HcspM1 ap_rg_ra HraM1) in "Hb1".
    iEval (rewrite HcspM1 ap_rg_s0 Hs0M1) in "Hb2".
    iEval (rewrite HcspM1 ap_rg_s1 Hs1M1) in "Hb3".
    iEval (rewrite HcspM1 ap_rg_s2 Hs2M1) in "Hb4".
    (* ================= THE SHARED EPILOGUE, +0x78 .. +0x84 ==============
       Both exits join here, but at DIFFERENT SIE indices: the found arm
       still holds p->lock (literal [false]), the null arm has released
       everything ([b]).  Hence the [xb] and [CIDt] parameters of [ap_tail].
       The epilogue hands back only the final register file; assembling
       [SpecAllocproc.allocproc_post] out of it is the ARM's job, which is
       exactly what lets the post's SIE index be per-arm. *)
    iAssert (ap_tail Φ m spd pme ret_tgt K) with "[Hb1 Hb2 Hb3 Hb4]" as "Htail".
    { rewrite /ap_tail.
      iIntros (xb CIDt Mt rv) "%Hmt Hcg Hpc Hk".
      destruct Hmt as (Htsp & Hts1 & Htrest).
      (* +0x78 c.mv a0,s1 *)
      iPoseProof (api_78 with "Htext") as "Hi78".
      iApply (wp_cmv_s_sconf (CID := CIDt) Φ (mword_of_int (AP + 0x78)) ap_a0 ap_s1 Mt (K - 4)%nat xb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi78 [-]").
      iIntros (CIDe1 Hse1) "Hcg Hpc".
      iEval (rewrite ap_rg_s1 Hts1) in "Hcg".
      set (E0 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg rv)]> Mt).
      change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg rv)]> Mt) with E0.
      assert (Hp7a : add_vec_int (mword_of_int (AP + 0x78) : mword 64) 2 = mword_of_int (AP + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp7a) in "Hpc".
      assert (HE0csp : E0 !!! Regidx csp_rs1 = spd)
        by (rewrite /E0 upd_ne; [exact Htsp | vm_compute; discriminate]).
      (* +0x7a .. +0x80: restore ra/s0/s1/s2 *)
      iPoseProof (api_7a with "Htext") as "Hi7a".
      iApply (wp_cldsp_s_sconf (CID := CIDe1) Φ (mword_of_int (AP + 0x7a)) (mword_of_int 3 : mword 6) ap_ra
                E0 (K - 4)%nat (m !!! Regidx ap_ra) xb (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi7a [Hb1] [-]").
      { iEval (rewrite HE0csp). iExact "Hb1". }
      iIntros (CIDe2 Hse2) "Hcg Hpc Hb1".
      set (E1 := <[Regidx ap_ra := regval_into_reg (m !!! Regidx ap_ra)]> E0).
      change (<[Regidx ap_ra := regval_into_reg (m !!! Regidx ap_ra)]> E0) with E1.
      assert (Hp7c : add_vec_int (mword_of_int (AP + 0x7a) : mword 64) 2 = mword_of_int (AP + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp7c) in "Hpc".
      assert (HE1csp : E1 !!! Regidx csp_rs1 = spd) by (rewrite /E1 upd_ne; [exact HE0csp | vm_compute; discriminate]).
      iPoseProof (api_7c with "Htext") as "Hi7c".
      iApply (wp_cldsp_s_sconf (CID := CIDe2) Φ (mword_of_int (AP + 0x7c)) (mword_of_int 2 : mword 6) ap_s0
                E1 (K - 4)%nat (m !!! Regidx ap_s0) xb (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi7c [Hb2] [-]").
      { iEval (rewrite HE1csp). iExact "Hb2". }
      iIntros (CIDe3 Hse3) "Hcg Hpc Hb2".
      set (E2 := <[Regidx ap_s0 := regval_into_reg (m !!! Regidx ap_s0)]> E1).
      change (<[Regidx ap_s0 := regval_into_reg (m !!! Regidx ap_s0)]> E1) with E2.
      assert (Hp7e : add_vec_int (mword_of_int (AP + 0x7c) : mword 64) 2 = mword_of_int (AP + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp7e) in "Hpc".
      assert (HE2csp : E2 !!! Regidx csp_rs1 = spd) by (rewrite /E2 upd_ne; [exact HE1csp | vm_compute; discriminate]).
      iPoseProof (api_7e with "Htext") as "Hi7e".
      iApply (wp_cldsp_s_sconf (CID := CIDe3) Φ (mword_of_int (AP + 0x7e)) (mword_of_int 1 : mword 6) ap_s1
                E2 (K - 4)%nat (m !!! Regidx ap_s1) xb (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi7e [Hb3] [-]").
      { iEval (rewrite HE2csp). iExact "Hb3". }
      iIntros (CIDe4 Hse4) "Hcg Hpc Hb3".
      set (E3 := <[Regidx ap_s1 := regval_into_reg (m !!! Regidx ap_s1)]> E2).
      change (<[Regidx ap_s1 := regval_into_reg (m !!! Regidx ap_s1)]> E2) with E3.
      assert (Hp80 : add_vec_int (mword_of_int (AP + 0x7e) : mword 64) 2 = mword_of_int (AP + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp80) in "Hpc".
      assert (HE3csp : E3 !!! Regidx csp_rs1 = spd) by (rewrite /E3 upd_ne; [exact HE2csp | vm_compute; discriminate]).
      iPoseProof (api_80 with "Htext") as "Hi80".
      iApply (wp_cldsp_s_sconf (CID := CIDe4) Φ (mword_of_int (AP + 0x80)) (mword_of_int 0 : mword 6) ap_s2
                E3 (K - 4)%nat (m !!! Regidx ap_s2) xb (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi80 [Hb4] [-]").
      { iEval (rewrite HE3csp). iExact "Hb4". }
      iIntros (CIDe5 Hse5) "Hcg Hpc Hb4".
      set (E4 := <[Regidx ap_s2 := regval_into_reg (m !!! Regidx ap_s2)]> E3).
      change (<[Regidx ap_s2 := regval_into_reg (m !!! Regidx ap_s2)]> E3) with E4.
      assert (Hp82 : add_vec_int (mword_of_int (AP + 0x80) : mword 64) 2 = mword_of_int (AP + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp82) in "Hpc".
      (* +0x82 c.addi16sp sp,32 *)
      assert (HE4csp : E4 !!! Regidx csp_rs1 = spd) by (rewrite /E4 upd_ne; [exact HE3csp | vm_compute; discriminate]).
      assert (Hup : add_vec spd (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
        by (rewrite /spd /sp0; apply frame_cancel_32).
      assert (Hwv : add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0)
        by (rewrite HE4csp; exact Hup).
      assert (Hpop : E4 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4)
        by (rewrite Hwv HE4csp; symmetry; exact Hspd4).
      iPoseProof (api_82 with "Htext") as "Hi82".
      iAssert (stack_own sp0 4) with "[Hb1 Hb2 Hb3 Hb4]" as "Hframe4".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hb1". { iExists _. iEval (rewrite Hb1a -HE0csp). iExact "Hb1". }
        iSplitL "Hb2". { iExists _. iEval (rewrite Hb2a -HE1csp). iExact "Hb2". }
        iSplitL "Hb3". { iExists _. iEval (rewrite Hb3a -HE2csp). iExact "Hb3". }
        iSplitL "Hb4". { iExists _. iEval (rewrite Hb4a -HE3csp). iExact "Hb4". }
        done. }
      iEval (rewrite -Hwv) in "Hframe4".
      iApply (wp_caddi16sp_pop_s_sconf (CID := CIDe5) Φ (mword_of_int (AP + 0x82)) (mword_of_int 2 : mword 6) E4 (K - 4)%nat 4 xb Hpop
                with "Hcg Hpc Hi82 Hframe4 [-]").
      iIntros (CIDe6 Hse6) "Hcg Hpc".
      assert (Hnk : ((K - 4) + 4)%nat = K) by (apply ap_Kback; exact HK).
      iEval (rewrite Hnk) in "Hcg".
      set (E5 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4).
      change (<[Regidx csp_rs1 := regval_into_reg
          (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4) with E5.
      assert (Hp84 : add_vec_int (mword_of_int (AP + 0x82) : mword 64) 2 = mword_of_int (AP + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp84) in "Hpc".
      (* +0x84 c.ret *)
      assert (HE5ra : E5 !!! Regidx ap_ra = m !!! Regidx ap_ra).
      { rewrite /E5 upd_ne; [| vm_compute; discriminate].
        rewrite /E4 upd_ne; [| vm_compute; discriminate].
        rewrite /E3 upd_ne; [| vm_compute; discriminate].
        rewrite /E2 upd_ne; [| vm_compute; discriminate].
        rewrite /E1. apply upd_eq. }
      iPoseProof (api_84 with "Htext") as "Hi84".
      iApply (wp_cret_s_sconf (CID := CIDe6) Φ (mword_of_int (AP + 0x84)) ap_ra E5 K xb
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi84 [-]").
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
    iPoseProof (api_0a with "Htext") as "Hi0a".
    iApply (wp_caddi4spn_s_sconf (CID := CID5) Φ (mword_of_int (AP + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) ap_s0
              M1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (A1 := <[Regidx ap_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1).
    change (<[Regidx ap_s0 := regval_into_reg
        (add_vec (M1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> M1) with A1.
    assert (Hp0c : add_vec_int (mword_of_int (AP + 0x0a) : mword 64) 2 = mword_of_int (AP + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    iPoseProof (api_0c with "Htext") as "Hi0c".
    iApply (wp_auipc_s_sconf (CID := CID6) Φ (mword_of_int (AP + 0x0c)) ap_s1 (mword_of_int 0x11 : mword 20) A1 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (A2 := <[Regidx ap_s1 := regval_into_reg
        (add_vec (mword_of_int (AP + 0x0c) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> A1).
    change (<[Regidx ap_s1 := regval_into_reg
        (add_vec (mword_of_int (AP + 0x0c) : mword 64) (auipc_off (mword_of_int 0x11 : mword 20)))]> A1) with A2.
    assert (Hp10 : add_vec_int (mword_of_int (AP + 0x0c) : mword 64) 4 = mword_of_int (AP + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    iPoseProof (api_10 with "Htext") as "Hi10".
    iApply (wp_addi4_s_sconf (CID := CID7) Φ (mword_of_int (AP + 0x10)) ap_s1 ap_s1 (mword_of_int 3140 : mword 12) A2 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rewrite ap_rg_s1) in "Hcg".
    set (A3 := <[Regidx ap_s1 := regval_into_reg
        (add_vec (A2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 3140 : mword 12)))]> A2).
    change (<[Regidx ap_s1 := regval_into_reg
        (add_vec (A2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 3140 : mword 12)))]> A2) with A3.
    assert (Hp14 : add_vec_int (mword_of_int (AP + 0x10) : mword 64) 4 = mword_of_int (AP + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    assert (HA3s1 : A3 !!! Regidx ap_s1 = proc_addr 0).
    { rewrite /A3 upd_eq /A2 upd_eq /proc_addr /proc_base.
      apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (api_14 with "Htext") as "Hi14".
    iApply (wp_auipc_s_sconf (CID := CID8) Φ (mword_of_int (AP + 0x14)) ap_s2 (mword_of_int 0x16 : mword 20) A3 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (A4 := <[Regidx ap_s2 := regval_into_reg
        (add_vec (mword_of_int (AP + 0x14) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> A3).
    change (<[Regidx ap_s2 := regval_into_reg
        (add_vec (mword_of_int (AP + 0x14) : mword 64) (auipc_off (mword_of_int 0x16 : mword 20)))]> A3) with A4.
    assert (Hp18 : add_vec_int (mword_of_int (AP + 0x14) : mword 64) 4 = mword_of_int (AP + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    iPoseProof (api_18 with "Htext") as "Hi18".
    iApply (wp_addi4_s_sconf (CID := CID9) Φ (mword_of_int (AP + 0x18)) ap_s2 ap_s2 (mword_of_int 1596 : mword 12) A4 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rewrite ap_rg_s2) in "Hcg".
    set (A5 := <[Regidx ap_s2 := regval_into_reg
        (add_vec (A4 !!! Regidx ap_s2) (sign_extend' 64 (mword_of_int 1596 : mword 12)))]> A4).
    change (<[Regidx ap_s2 := regval_into_reg
        (add_vec (A4 !!! Regidx ap_s2) (sign_extend' 64 (mword_of_int 1596 : mword 12)))]> A4) with A5.
    assert (Hp1c : add_vec_int (mword_of_int (AP + 0x18) : mword 64) 4 = mword_of_int (AP + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
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
                   ap_tail Φ m spd pme ret_tgt K -∗
                   wp_next (CID0 := CID0) b pme (fun (CID : CpuId) =>
                     ∀ (mr : regfile),
                       ⌜ callee_saved m mr ⌝ -∗
                       pc_is ret_tgt -∗
                       allocproc_post γa γf γs lvl eb pme C (Some nb) b mr K
                         (mr !!! Regidx ap_a0) -∗
                       WP (Loop : expr riscv_lang) {{ Φ }}) -∗
                   sie_cap_gpr Mk (K - 4)%nat b pme -∗
                   cpu_own lvl eb pme C b -∗
                   kalloc_env γa (Some nb) -∗
                   pc_is (mword_of_int (AP + 0x1c)) -∗
                   WP (Loop : expr riscv_lang) {{ Φ }}))%I with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (CIDk Hsk k Mk) "%Hfuel %Hk _ _ _ _ _ _ _". exfalso. exact (ap_fuel0 k Hfuel Hk). }
      iIntros (CIDk Hsk k Mk) "%Hfuel %Hk %Hregs Htl Hcont Hcg Hcpu Henv Hpc".
      destruct Hregs as (Hksp & Hks1 & Hks2 & Hkrest).
      iDestruct (cpu_own_eb_agree with "Hcg Hcpu") as %Hbmatch. symmetry in Hbmatch.
      destruct (lookup_lt_is_Some_2 γs k ltac:(rewrite Hlen; exact Hk)) as [γl Hγl].
      iDestruct (procs_inv_lookup Φ γs k γl Hγl with "Hpinv") as "#Hislock".
      (* +0x1c c.mv a0,s1 *)
      iPoseProof (api_1c with "Htext") as "Hi1c".
      iApply (wp_cmv_s_sconf (CID := CIDk) Φ (mword_of_int (AP + 0x1c)) ap_a0 ap_s1 Mk (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi1c [-]").
      iIntros (CIDl1 Hsl1) "Hcg Hpc".
      iEval (rewrite ap_rg_s1) in "Hcg".
      set (L1 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (Mk !!! Regidx ap_s1))]> Mk).
      change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (Mk !!! Regidx ap_s1))]> Mk) with L1.
      assert (Hp1e : add_vec_int (mword_of_int (AP + 0x1c) : mword 64) 2 = mword_of_int (AP + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp1e) in "Hpc".
      (* +0x1e jal ra,acquire *)
      iPoseProof (api_1e with "Htext") as "Hi1e".
      iApply (wp_jal_s_sconf (CID := CIDl1) Φ (mword_of_int (AP + 0x1e)) ap_ra (mword_of_int 2093250 : mword 21)
                L1 (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi1e [-]").
      iIntros (CIDl2 Hsl2) "Hcg Hpc".
      set (L2 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x1e) : mword 64) 4)]> L1).
      change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x1e) : mword 64) 4)]> L1) with L2.
      assert (Hjacq : add_vec (mword_of_int (AP + 0x1e) : mword 64) (sign_extend' 64 (mword_of_int 2093250 : mword 21)) = mword_of_int KernelSyms.acquire)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjacq) in "Hpc".
      assert (HL2ra : L2 !!! Regidx ap_ra = add_vec_int (mword_of_int (AP + 0x1e) : mword 64) 4) by (rewrite /L2 upd_eq; reflexivity).
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
      iDestruct (cpu_own_transport CIDk CIDl2 lvl eb pme C b ltac:(wp_next_chain)
                   with "Hcpu") as "Hcpu".
      iApply (Acquire.wp_acquire_sconf (CID := CIDl2) Φ γl "proc"%string
                (proc_lock_res Φ γs γl (proc_addr k)) L2 lvl eb pme C (K - 4)%nat b
                (ap_lvl1 lvl Hlvl) (ap_K10 K HK)
                with "Hcg Hcpu Htext Hpc [Hislock] Hpanic [-]").
      { iEval (rewrite HL2a0). iExact "Hislock". }
      iIntros (CIDf Hsf ms macq) "%Hmsf Hcg Hpc %Hcsacq Hlocked HR Hcpu Hpay".
      assert (Hp22 : ret_pc (L2 !!! Regidx ap_ra) = mword_of_int (AP + 0x22))
        by (rewrite HL2ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp22) in "Hpc".
      iDestruct (proc_lock_res_elim Φ γs γl (proc_addr k) with "HR") as (st ch) "(Hstate & Hchan & Hpub & Hslots)".
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
      iPoseProof (api_22 with "Htext") as "Hi22".
      assert (Hstaddr : add_vec (macq !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 24 : mword 12))
                        = p_state (proc_addr k))
        by (rewrite Hacq_s1; apply ap_off_24).
      iApply (wp_clw_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x22)) ap_a5 ap_s1
                (mword_of_int 24 : mword 12) macq (K - 4)%nat st false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi22 [Hstate] [-]").
      { iEval (rewrite ap_rg_s1 Hstaddr). iExact "Hstate". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hstate". iEval (rewrite ap_rg_s1 Hstaddr) in "Hstate".
      set (L3 := <[Regidx ap_a5 := regval_into_reg (sign_extend' 64 st)]> macq).
      change (<[Regidx ap_a5 := regval_into_reg (sign_extend' 64 st)]> macq) with L3.
      assert (Hp24 : add_vec_int (mword_of_int (AP + 0x22) : mword 64) 2 = mword_of_int (AP + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
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
      iPoseProof (api_24 with "Htext") as "Hi24".
      destruct (eq_vec (L3 !!! Regidx ap_a5) (zero_reg : mword 64)) eqn:Hcmp.
      - (* ============ FOUND: p->state == UNUSED ============ *)
        assert (Hstu : st = UNUSED) by (apply ap_sext_zero; rewrite -HL3a5; exact Hcmp).
        subst st.
        assert (Hcmpr : eq_vec (rget (CID := CIDf) L3 ap_a5) (zero_reg : mword 64) = true)
          by (rewrite ap_rg_a5; exact Hcmp).
        iApply (wp_cbeqz_taken_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x24)) (mword_of_int 10 : mword 8)
                  (Cregidx (mword_of_int 7)) ap_a5 L3 (K - 4)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  Hcmpr ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi24 [-]").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt38 : add_vec (mword_of_int (AP + 0x24) : mword 64)
                           (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0"))))
                         = mword_of_int (AP + 0x38))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt38) in "Hpc".
        (* the dormant block comes out of the invariant *)
        iDestruct (proc_slots_unused Φ γs (proc_addr k) with "Hslots") as "[Hdorm Hpark]".
        iDestruct (park_at_full_elim k false Hk with "Hpark") as "Hpark".
        rewrite park_split. iDestruct "Hpark" as "[Hparka Hparkb]".
        iDestruct (proc_dormant_unused γf (proc_addr k) with "Hdorm")
          as "(Hctx & Hpgcell & Htfcell & Hspare & Hrest)".
        iDestruct "Hrest" as (V pid0) "([%Hof [%Hcwd %Hszb]] & Hpidhalf & Hfields & Hofiles)".
        iDestruct "Hpub" as (kl xs pid1) "(Hkilled & Hxstate & Hpidinv)".
        iDestruct (p_pid_join (proc_addr k) pid1 pid0 with "Hpidinv Hpidhalf") as "[%Hpideq Hpidfull]".
        (* +0x38 jal ra,allocpid *)
        iPoseProof (api_38 with "Htext") as "Hi38".
        iApply (wp_jal_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x38)) ap_ra (mword_of_int 2096752 : mword 21)
                  L3 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi38 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (F1 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x38) : mword 64) 4)]> L3).
        change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x38) : mword 64) 4)]> L3) with F1.
        assert (Hjapid : add_vec (mword_of_int (AP + 0x38) : mword 64) (sign_extend' 64 (mword_of_int 2096752 : mword 21)) = mword_of_int KernelSyms.allocpid)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjapid) in "Hpc".
        assert (HF1ra : F1 !!! Regidx ap_ra = add_vec_int (mword_of_int (AP + 0x38) : mword 64) 4) by (rewrite /F1 upd_eq; reflexivity).
        assert (HF1s1 : F1 !!! Regidx ap_s1 = proc_addr k)
          by (rewrite /F1 upd_ne; [exact HL3s1 | vm_compute; discriminate]).
        assert (HF1csp : F1 !!! Regidx csp_rs1 = spd)
          by (rewrite /F1 upd_ne; [exact HL3csp | vm_compute; discriminate]).
        assert (HF1rest : forall r : mword 5, is_cs_idx r = true ->
                            r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                            F1 !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          assert (N1 : r <> mword_of_int 1) by (intro He; rewrite He in Hr; vm_compute in Hr; discriminate).
          rewrite /F1 upd_ne; [| congruence].
          exact (HL3rest r Hr Ncsp N8 N9 N18). }
        iApply (Allocpid.wp_allocpid_sconf (CID := CIDf) Φ γp F1 (K - 4)%nat (S lvl) eb pme C false
                  (ap_lvlS lvl Hlvl) (ap_K14 K HK)
                  with "Hcg Hcpu Htext Hpc Hpidlk Hpanic [-]").
        iApply wp_next_off_intro. iIntros (mfa) "%Hcsfa Hcg Hcpu Hpc".
        assert (Hp3c : ret_pc (F1 !!! Regidx ap_ra) = mword_of_int (AP + 0x3c))
          by (rewrite HF1ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp3c) in "Hpc".
        assert (Hfa_s1 : mfa !!! Regidx ap_s1 = proc_addr k).
        { rewrite (callee_saved_lookup Hcsfa ap_s1 ltac:(vm_compute; reflexivity)). exact HF1s1. }
        assert (Hfa_csp : mfa !!! Regidx csp_rs1 = spd).
        { rewrite (callee_saved_lookup Hcsfa csp_rs1 ltac:(vm_compute; reflexivity)). exact HF1csp. }
        assert (Hfa_rest : forall r : mword 5, is_cs_idx r = true ->
                             r <> csp_rs1 -> r <> ap_s0 -> r <> ap_s1 -> r <> ap_s2 ->
                             mfa !!! Regidx r = m !!! Regidx r).
        { intros r Hr Ncsp N8 N9 N18.
          rewrite (callee_saved_lookup Hcsfa r Hr).
          exact (HF1rest r Hr Ncsp N8 N9 N18). }
        (* +0x3c c.sw a0,48(s1) : p->pid = allocpid() *)
        iPoseProof (api_3c with "Htext") as "Hi3c".
        assert (Hpidaddr : add_vec (mfa !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 48 : mword 12))
                           = p_pid (proc_addr k))
          by (rewrite Hfa_s1; apply ap_off_48).
        iApply (wp_csw_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x3c)) ap_a0 ap_s1
                  (mword_of_int 48 : mword 12) mfa (K - 4)%nat pid1 false
                  with "Hcg Hpc Hi3c [Hpidfull] [-]").
        { iEval (rewrite ap_rg_s1 Hpidaddr). iExact "Hpidfull". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hpidfull". iEval (rewrite ap_rg_s1 Hpidaddr ap_rg_a0) in "Hpidfull".
        assert (Hp3e : add_vec_int (mword_of_int (AP + 0x3c) : mword 64) 2 = mword_of_int (AP + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp3e) in "Hpc".
        set (pidn := trunc32 (mfa !!! Regidx ap_a0)).
        (* +0x3e c.li a5,1 *)
        iPoseProof (api_3e with "Htext") as "Hi3e".
        iApply (wp_cli_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x3e)) ap_a5 (mword_of_int 1 : mword 6)
                  (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
                  mfa (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity)
                  with "Hcg Hpc Hi3e [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (F2 := <[Regidx ap_a5 := regval_into_reg
            (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mfa).
        change (<[Regidx ap_a5 := regval_into_reg
            (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mfa) with F2.
        assert (Hp40 : add_vec_int (mword_of_int (AP + 0x3e) : mword 64) 2 = mword_of_int (AP + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp40) in "Hpc".
        assert (HF2s1 : F2 !!! Regidx ap_s1 = proc_addr k)
          by (rewrite /F2 upd_ne; [exact Hfa_s1 | vm_compute; discriminate]).
        (* +0x40 c.sw a5,24(s1) : p->state = USED *)
        iPoseProof (api_40 with "Htext") as "Hi40".
        assert (Hstaddr2 : add_vec (F2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 24 : mword 12))
                           = p_state (proc_addr k))
          by (rewrite HF2s1; apply ap_off_24).
        iApply (wp_csw_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x40)) ap_a5 ap_s1
                  (mword_of_int 24 : mword 12) F2 (K - 4)%nat UNUSED false
                  with "Hcg Hpc Hi40 [Hstate] [-]").
        { iEval (rewrite ap_rg_s1 Hstaddr2). iExact "Hstate". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hstate". iEval (rewrite ap_rg_s1 Hstaddr2) in "Hstate".
        assert (Hused : trunc32 (F2 !!! Regidx ap_a5) = USED)
          by (rewrite /F2 upd_eq; apply ap_used_val).
        iEval (rewrite ap_rg_a5 Hused) in "Hstate".
        assert (Hp42 : add_vec_int (mword_of_int (AP + 0x40) : mword 64) 2 = mword_of_int (AP + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp42) in "Hpc".
        (* +0x42 jal ra,kalloc *)
        iPoseProof (api_42 with "Htext") as "Hi42".
        iApply (wp_jal_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x42)) ap_ra (mword_of_int 2092996 : mword 21)
                  F2 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi42 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (F3 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x42) : mword 64) 4)]> F2).
        change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x42) : mword 64) 4)]> F2) with F3.
        assert (Hjkal : add_vec (mword_of_int (AP + 0x42) : mword 64) (sign_extend' 64 (mword_of_int 2092996 : mword 21)) = mword_of_int KernelSyms.kalloc)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjkal) in "Hpc".
        assert (HF3ra : F3 !!! Regidx ap_ra = add_vec_int (mword_of_int (AP + 0x42) : mword 64) 4) by (rewrite /F3 upd_eq; reflexivity).
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
        iDestruct "Henv" as (γk) "(#Hkmem & Havail & _)".
        destruct nb as [| nb']; [ exfalso; exact (ap_nb_pos 0%nat Hnb eq_refl) |].
        iApply (AK.wp_kalloc_sconf (CID := CIDf) Φ γa γk (mword_of_int (KernelSyms.kmem + 24))
                  F3 (Some (S nb')) (S lvl) eb pme C (K - 4)%nat false
                  (ap_K14 K HK) ltac:(reflexivity) (ap_lvlS lvl Hlvl)
                  with "Hcg Hcpu Htext Hpc Hkmem Havail Hpanic [-]").
        iApply wp_next_off_intro. iIntros (mka) "Hcg Hcpu Hpc %Hcska Hkpost".
        assert (Hp46 : ret_pc (F3 !!! Regidx ap_ra) = mword_of_int (AP + 0x46))
          by (rewrite HF3ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp46) in "Hpc".
        iDestruct (kalloc_post_success γk nb' (mka !!! Regidx ap_a0) with "Hkpost")
          as "(%Hpvtf & Hpgown & Havail)".
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
        (* +0x46 c.mv s2,a0 *)
        iPoseProof (api_46 with "Htext") as "Hi46".
        iApply (wp_cmv_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x46)) ap_s2 ap_a0 mka (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi46 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_a0) in "Hcg".
        set (F4 := <[Regidx ap_s2 := regval_into_reg (add_vec zero_reg (mka !!! Regidx ap_a0))]> mka).
        change (<[Regidx ap_s2 := regval_into_reg (add_vec zero_reg (mka !!! Regidx ap_a0))]> mka) with F4.
        assert (Hp48 : add_vec_int (mword_of_int (AP + 0x46) : mword 64) 2 = mword_of_int (AP + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp48) in "Hpc".
        assert (HF4s1 : F4 !!! Regidx ap_s1 = proc_addr k)
          by (rewrite /F4 upd_ne; [exact Hka_s1 | vm_compute; discriminate]).
        assert (HF4a0 : F4 !!! Regidx ap_a0 = tfr)
          by (rewrite /F4 upd_ne; [reflexivity | vm_compute; discriminate]).
        (* +0x48 c.sd a0,88(s1) : p->trapframe = the page *)
        iPoseProof (api_48 with "Htext") as "Hi48".
        assert (Htfaddr : add_vec (F4 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 88 : mword 12))
                          = p_trapframe (proc_addr k))
          by (rewrite HF4s1; apply ap_off_88).
        iApply (wp_csd_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x48)) ap_a0 ap_s1
                  (mword_of_int 88 : mword 12) F4 (K - 4)%nat (zero_reg : mword 64) false
                  with "Hcg Hpc Hi48 [Htfcell] [-]").
        { iEval (rewrite ap_rg_s1 Htfaddr). iExact "Htfcell". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Htfcell".
        iEval (rewrite ap_rg_s1 Htfaddr ap_rg_a0 HF4a0) in "Htfcell".
        assert (Hp4a : add_vec_int (mword_of_int (AP + 0x48) : mword 64) 2 = mword_of_int (AP + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp4a) in "Hpc".
        (* +0x4a c.beqz a0 : DEAD (kalloc's page is not null) *)
        iPoseProof (api_4a with "Htext") as "Hi4a".
        iApply (wp_cbeqz_fall_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x4a)) (mword_of_int 30 : mword 8)
                  (Cregidx (mword_of_int 2)) ap_a0 F4 (K - 4)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite ap_rg_a0 HF4a0; exact (ap_valid_nz tfr Hpvtf))
                  with "Hcg Hpc Hi4a [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp4c : add_vec_int (mword_of_int (AP + 0x4a) : mword 64) 2 = mword_of_int (AP + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp4c) in "Hpc".
        (* +0x4c c.mv a0,s1 *)
        iPoseProof (api_4c with "Htext") as "Hi4c".
        iApply (wp_cmv_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x4c)) ap_a0 ap_s1 F4 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi4c [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
        set (F5 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (F4 !!! Regidx ap_s1))]> F4).
        change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (F4 !!! Regidx ap_s1))]> F4) with F5.
        assert (Hp4e : add_vec_int (mword_of_int (AP + 0x4c) : mword 64) 2 = mword_of_int (AP + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp4e) in "Hpc".
        (* +0x4e jal ra,proc_pagetable *)
        iPoseProof (api_4e with "Htext") as "Hi4e".
        iApply (wp_jal_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x4e)) ap_ra (mword_of_int 2096792 : mword 21)
                  F5 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi4e [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (F6 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x4e) : mword 64) 4)]> F5).
        change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x4e) : mword 64) 4)]> F5) with F6.
        assert (Hjppt : add_vec (mword_of_int (AP + 0x4e) : mword 64) (sign_extend' 64 (mword_of_int 2096792 : mword 21)) = mword_of_int KernelSyms.proc_pagetable)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjppt) in "Hpc".
        assert (HF6ra : F6 !!! Regidx ap_ra = add_vec_int (mword_of_int (AP + 0x4e) : mword 64) 4) by (rewrite /F6 upd_eq; reflexivity).
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
        iAssert (kalloc_env γa (Some nb')) with "[Havail]" as "Henv".
        { iExists γk. iFrame "Hkmem Havail Hpanic". }
        iApply (PPT.wp_proc_pagetable_sconf (CID := CIDf) γa Φ F6 tfr (DfracOwn 1) (S lvl) (K - 4)%nat eb pme C (Some nb') false
                  (ap_lvlS lvl Hlvl) (ap_K36 K HK)
                  (ex_intro _ nb' (conj eq_refl (ap_nb_pt nb' Hnb)))
                  (ap_tf_align tfr Hpvtf) (ap_tf_bound tfr Hpvtf)
                  with "Hcg Hcpu Htext Hpc [Htfcell] Henv [-]").
        { iEval (rewrite HF6a0). iExact "Htfcell". }
        iApply wp_next_off_intro.
        iIntros (mpt t) "Hcg Hcpu Hpc Htfcell Htree %Hroot %Hrep %Hnodes Henv %Hcspt".
        iEval (rewrite HF6a0) in "Htfcell".
        assert (Hp52 : ret_pc (F6 !!! Regidx ap_ra) = mword_of_int (AP + 0x52))
          by (rewrite HF6ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp52) in "Hpc".
        iDestruct (ptree_own_page_valid 2 (DfracOwn 1) t with "Htree") as %Hpvroot.
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
        (* +0x52 c.mv s2,a0 *)
        iPoseProof (api_52 with "Htext") as "Hi52".
        iApply (wp_cmv_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x52)) ap_s2 ap_a0 mpt (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi52 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_a0) in "Hcg".
        set (F7 := <[Regidx ap_s2 := regval_into_reg (add_vec zero_reg (mpt !!! Regidx ap_a0))]> mpt).
        change (<[Regidx ap_s2 := regval_into_reg (add_vec zero_reg (mpt !!! Regidx ap_a0))]> mpt) with F7.
        assert (Hp54 : add_vec_int (mword_of_int (AP + 0x52) : mword 64) 2 = mword_of_int (AP + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp54) in "Hpc".
        assert (HF7s1 : F7 !!! Regidx ap_s1 = proc_addr k)
          by (rewrite /F7 upd_ne; [exact Hpt_s1 | vm_compute; discriminate]).
        assert (HF7a0 : F7 !!! Regidx ap_a0 = page_base (pt_base t)).
        { rewrite /F7 upd_ne; [| vm_compute; discriminate]. exact Hroot. }
        (* +0x54 c.sd a0,80(s1) : p->pagetable = the table *)
        iPoseProof (api_54 with "Htext") as "Hi54".
        assert (Hpgaddr : add_vec (F7 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 80 : mword 12))
                          = p_pagetable (proc_addr k))
          by (rewrite HF7s1; apply ap_off_80).
        iApply (wp_csd_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x54)) ap_a0 ap_s1
                  (mword_of_int 80 : mword 12) F7 (K - 4)%nat (zero_reg : mword 64) false
                  with "Hcg Hpc Hi54 [Hpgcell] [-]").
        { iEval (rewrite ap_rg_s1 Hpgaddr). iExact "Hpgcell". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hpgcell".
        iEval (rewrite ap_rg_s1 Hpgaddr ap_rg_a0 HF7a0) in "Hpgcell".
        assert (Hp56 : add_vec_int (mword_of_int (AP + 0x54) : mword 64) 2 = mword_of_int (AP + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp56) in "Hpc".
        (* +0x56 c.beqz a0 : DEAD (a page-table node's page is a kalloc page) *)
        iPoseProof (api_56 with "Htext") as "Hi56".
        iApply (wp_cbeqz_fall_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x56)) (mword_of_int 32 : mword 8)
                  (Cregidx (mword_of_int 2)) ap_a0 F7 (K - 4)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  ltac:(rewrite ap_rg_a0 HF7a0; exact (ap_valid_nz _ Hpvroot))
                  with "Hcg Hpc Hi56 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp58 : add_vec_int (mword_of_int (AP + 0x56) : mword 64) 2 = mword_of_int (AP + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp58) in "Hpc".
        (* +0x58 li a2,112 *)
        iDestruct (sie_cap_gpr_x0 (CID := CIDf) F7 (K - 4)%nat false pme ap_x0 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
        iPoseProof (api_58 with "Htext") as "Hi58".
        iApply (wp_addi4_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x58)) ap_a2 ap_x0 (mword_of_int 112 : mword 12) F7 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi58 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_x0) in "Hcg".
        set (G1 := <[Regidx ap_a2 := regval_into_reg
            (add_vec (F7 !!! Regidx ap_x0) (sign_extend' 64 (mword_of_int 112 : mword 12)))]> F7).
        change (<[Regidx ap_a2 := regval_into_reg
            (add_vec (F7 !!! Regidx ap_x0) (sign_extend' 64 (mword_of_int 112 : mword 12)))]> F7) with G1.
        assert (Hp5c : add_vec_int (mword_of_int (AP + 0x58) : mword 64) 4 = mword_of_int (AP + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp5c) in "Hpc".
        (* +0x5c c.li a1,0 *)
        iPoseProof (api_5c with "Htext") as "Hi5c".
        iApply (wp_cli_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x5c)) ap_a1 (mword_of_int 0 : mword 6)
                  (zero_reg : mword 64) G1 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ap_li_zero
                  with "Hcg Hpc Hi5c [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (G2 := <[Regidx ap_a1 := regval_into_reg (zero_reg : mword 64)]> G1).
        change (<[Regidx ap_a1 := regval_into_reg (zero_reg : mword 64)]> G1) with G2.
        assert (Hp5e : add_vec_int (mword_of_int (AP + 0x5c) : mword 64) 2 = mword_of_int (AP + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp5e) in "Hpc".
        assert (HG2s1 : G2 !!! Regidx ap_s1 = proc_addr k).
        { rewrite /G2 upd_ne; [| vm_compute; discriminate].
          rewrite /G1 upd_ne; [| vm_compute; discriminate]. exact HF7s1. }
        (* +0x5e addi a0,s1,96 : &p->context *)
        iPoseProof (api_5e with "Htext") as "Hi5e".
        iApply (wp_addi4_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x5e)) ap_a0 ap_s1 (mword_of_int 96 : mword 12) G2 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi5e [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
        set (G3 := <[Regidx ap_a0 := regval_into_reg
            (add_vec (G2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 96 : mword 12)))]> G2).
        change (<[Regidx ap_a0 := regval_into_reg
            (add_vec (G2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 96 : mword 12)))]> G2) with G3.
        assert (Hp62 : add_vec_int (mword_of_int (AP + 0x5e) : mword 64) 4 = mword_of_int (AP + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
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
        (* +0x62 jal ra,memset : zero the 112-byte save area *)
        iDestruct (own_ctx_bytes (p_context (proc_addr k)) with "Hctx") as "[Hbw Hctxback]".
        iDestruct (bb_any_named (p_context (proc_addr k)) 112 with "Hbw") as (fb) "Hbw".
        iPoseProof (api_62 with "Htext") as "Hi62".
        iApply (wp_jal_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x62)) ap_ra (mword_of_int 2093374 : mword 21)
                  G3 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi62 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (G4 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x62) : mword 64) 4)]> G3).
        change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x62) : mword 64) 4)]> G3) with G4.
        assert (Hjms : add_vec (mword_of_int (AP + 0x62) : mword 64) (sign_extend' 64 (mword_of_int 2093374 : mword 21)) = mword_of_int KernelSyms.memset)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjms) in "Hpc".
        assert (HG4ra : G4 !!! Regidx ap_ra = add_vec_int (mword_of_int (AP + 0x62) : mword 64) 4) by (rewrite /G4 upd_eq; reflexivity).
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
        iApply (MS.wp_memset_sconf (CID := CIDf) Φ G4 (K - 4)%nat 112 (zero_reg : mword 64) fb false pme
                  (ap_K2 K HK) ltac:(vm_compute; reflexivity) HG4a1 HG4a2
                  with "Hcg Htext Hpc [Hbw] [-]").
        { iEval (rewrite HG4a0). iExact "Hbw". }
        iApply wp_next_off_intro. iIntros (mms) "Hcg Hpc Hbw %Hcsms".
        iEval (rewrite HG4a0) in "Hbw".
        assert (Hp66 : ret_pc (G4 !!! Regidx ap_ra) = mword_of_int (AP + 0x66))
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
        (* +0x66 auipc a5,0x0 ; +0x6a addi a5,a5,-600 : a5 := forkret *)
        iPoseProof (api_66 with "Htext") as "Hi66".
        iApply (wp_auipc_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x66)) ap_a5 (mword_of_int 0 : mword 20) mms (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi66 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (H1 := <[Regidx ap_a5 := regval_into_reg
            (add_vec (mword_of_int (AP + 0x66) : mword 64) (auipc_off (mword_of_int 0 : mword 20)))]> mms).
        change (<[Regidx ap_a5 := regval_into_reg
            (add_vec (mword_of_int (AP + 0x66) : mword 64) (auipc_off (mword_of_int 0 : mword 20)))]> mms) with H1.
        assert (Hp6a : add_vec_int (mword_of_int (AP + 0x66) : mword 64) 4 = mword_of_int (AP + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp6a) in "Hpc".
        iPoseProof (api_6a with "Htext") as "Hi6a".
        iApply (wp_addi4_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x6a)) ap_a5 ap_a5 (mword_of_int 3496 : mword 12) H1 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi6a [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_a5) in "Hcg".
        set (H2 := <[Regidx ap_a5 := regval_into_reg
            (add_vec (H1 !!! Regidx ap_a5) (sign_extend' 64 (mword_of_int 3496 : mword 12)))]> H1).
        change (<[Regidx ap_a5 := regval_into_reg
            (add_vec (H1 !!! Regidx ap_a5) (sign_extend' 64 (mword_of_int 3496 : mword 12)))]> H1) with H2.
        assert (Hp6e : add_vec_int (mword_of_int (AP + 0x6a) : mword 64) 4 = mword_of_int (AP + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp6e) in "Hpc".
        assert (HH2a5 : H2 !!! Regidx ap_a5 = forkret_pc).
        { rewrite /H2 upd_eq /H1 upd_eq /forkret_pc.
          apply bv_eq; vm_compute; reflexivity. }
        assert (HH2s1 : H2 !!! Regidx ap_s1 = proc_addr k).
        { rewrite /H2 upd_ne; [| vm_compute; discriminate].
          rewrite /H1 upd_ne; [| vm_compute; discriminate]. exact Hms_s1. }
        (* +0x6e c.sd a5,96(s1) : p->context.ra = forkret *)
        iPoseProof (api_6e with "Htext") as "Hi6e".
        assert (Hctx0 : add_vec (H2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 96 : mword 12))
                        = p_context (proc_addr k))
          by (rewrite HH2s1; apply ap_off_96).
        iApply (wp_csd_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x6e)) ap_a5 ap_s1
                  (mword_of_int 96 : mword 12) H2 (K - 4)%nat w0 false
                  with "Hcg Hpc Hi6e [Hc0] [-]").
        { iEval (rewrite ap_rg_s1 Hctx0). iExact "Hc0". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hc0". iEval (rewrite ap_rg_s1 Hctx0 ap_rg_a5 HH2a5) in "Hc0".
        assert (Hp70 : add_vec_int (mword_of_int (AP + 0x6e) : mword 64) 2 = mword_of_int (AP + 0x70)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp70) in "Hpc".
        (* +0x70 c.ld a5,64(s1) : a5 := p->kstack *)
        iDestruct (procs_inv_kstack Φ γs k γl Hγl with "Hpinv") as (ks) "#Hks".
        iPoseProof (api_70 with "Htext") as "Hi70".
        assert (Hksaddr : add_vec (H2 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 64 : mword 12))
                          = p_kstack (proc_addr k))
          by (rewrite HH2s1; apply ap_off_64).
        iApply (wp_cld_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x70)) ap_a5 ap_s1
                  (mword_of_int 64 : mword 12) H2 (K - 4)%nat ks false (dqm := DfracDiscarded)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi70 [] [-]").
        { iEval (rewrite ap_rg_s1 Hksaddr). rewrite /is_kstack. iExact "Hks". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc _".
        set (H3 := <[Regidx ap_a5 := regval_into_reg ks]> H2).
        change (<[Regidx ap_a5 := regval_into_reg ks]> H2) with H3.
        assert (Hp72 : add_vec_int (mword_of_int (AP + 0x70) : mword 64) 2 = mword_of_int (AP + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp72) in "Hpc".
        (* +0x72 c.lui a4,0x1 *)
        iPoseProof (api_72 with "Htext") as "Hi72".
        iApply (wp_clui_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x72)) ap_a4
                  (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64) H3 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ap_lui_pgsize
                  with "Hcg Hpc Hi72 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (H4 := <[Regidx ap_a4 := regval_into_reg (mword_of_int 4096 : mword 64)]> H3).
        change (<[Regidx ap_a4 := regval_into_reg (mword_of_int 4096 : mword 64)]> H3) with H4.
        assert (Hp74 : add_vec_int (mword_of_int (AP + 0x72) : mword 64) 2 = mword_of_int (AP + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp74) in "Hpc".
        (* +0x74 c.add a5,a5,a4 *)
        iPoseProof (api_74 with "Htext") as "Hi74".
        iApply (wp_cadd_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x74)) ap_a5 ap_a4 H4 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi74 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_a5 ap_rg_a4) in "Hcg".
        set (H5 := <[Regidx ap_a5 := regval_into_reg
            (add_vec (H4 !!! Regidx ap_a5) (H4 !!! Regidx ap_a4))]> H4).
        change (<[Regidx ap_a5 := regval_into_reg
            (add_vec (H4 !!! Regidx ap_a5) (H4 !!! Regidx ap_a4))]> H4) with H5.
        assert (Hp76 : add_vec_int (mword_of_int (AP + 0x74) : mword 64) 2 = mword_of_int (AP + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
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
        (* +0x76 c.sd a5,104(s1) : p->context.sp = p->kstack + PGSIZE *)
        iPoseProof (api_76 with "Htext") as "Hi76".
        assert (Hctx1 : add_vec (H5 !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 104 : mword 12))
                        = pa_add (p_context (proc_addr k)) 8)
          by (rewrite HH5s1; apply ap_off_104).
        iApply (wp_csd_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x76)) ap_a5 ap_s1
                  (mword_of_int 104 : mword 12) H5 (K - 4)%nat w1 false
                  with "Hcg Hpc Hi76 [Hc1] [-]").
        { iEval (rewrite ap_rg_s1 Hctx1). iExact "Hc1". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hc1". iEval (rewrite ap_rg_s1 Hctx1 ap_rg_a5 HH5a5) in "Hc1".
        assert (Hp78 : add_vec_int (mword_of_int (AP + 0x76) : mword 64) 2 = mword_of_int (AP + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp78) in "Hpc".
        (* ---------- assemble the private block and hand it to the tail ------- *)
        iDestruct (tf_page_of_page_own tfp ltac:(rewrite Hbasetf; exact Hpvtf) with "[Hpgown]")
          as (tfws) "Htfpage".
        { rewrite Hbasetf. iExact "Hpgown". }
        iDestruct (proc_pt_intro_ppt t tfp Hrep ltac:(rewrite Hbasetf; exact Hpvtf) with "Htree") as "Hpt".
        iDestruct (p_pid_split (proc_addr k) pidn with "Hpidfull") as "[Hpidinv Hpidown]".
        iAssert (proc_pt_at (proc_addr k) (upt_desc (pt_base t) tfp))
          with "[Hpgcell Htfcell Hpt]" as "Hptat".
        { rewrite /proc_pt_at. cbn [ud_root ud_tfp].
          iFrame "Hpt". iSplitL "Hpgcell"; [iExact "Hpgcell"|].
          iEval (rewrite -Hbasetf) in "Htfcell". iExact "Htfcell". }
        iDestruct (proc_priv_intro γf (proc_addr k) pidn V (upt_desc (pt_base t) tfp) tfws
                     Hszb (um_below_empty (pv_sz V))
                     with "Hpidown Hfields Hptat [Htfpage] Hofiles") as "Hpriv".
        { cbn [ud_tfp]. iExact "Htfpage". }
        iEval (rewrite /ap_tail) in "Htl".
        iApply ("Htl" $! false CIDf H5 (proc_addr k) with "[%] Hcg Hpc [-]").
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
        iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain|].
        iApply ("Hcont" $! Mf with "[%] Hpcf [-]").
        { exact Hcsf. }
        iEval (rewrite Ha0f).
        rewrite /allocproc_post. iRight.
        iExists k, γl, ch, pidn, (upd_pt V (upt_desc (pt_base t) tfp) tfws),
                (pt_base t), tfp, ks, rest, (S (pt_nodes t)).
        iSplitR.
        { iPureIntro. split; [reflexivity|]. split; [exact Hk|]. split; [exact Hγl|].
          split; [reflexivity|].
          cbn [upd_pt pv_ofile pv_cwd].
          split; [exact Hof|]. split; [exact Hcwd|].
          split; [exact Hrestlen|]. exact (ap_nodes_le (pt_nodes t) Hnodes). }
        iSplitL "Hlocked Hstate Hchan Hkilled Hxstate Hpidinv Hparka".
        { rewrite /proc_held. iFrame "Hlocked Hstate Hchan Hparka".
          iExists kl, xs, pidn. iFrame "Hkilled Hxstate Hpidinv". }
        iFrame "Hparkb Hpriv Hspare Hks".
        iSplitL "Hc0 Hc1 Hcrest".
        { rewrite ctx_cells_run !big_sepL_cons Nat.mul_0_r RiscvExtras.pa_add_0.
          iFrame "Hc0 Hc1 Hcrest". }
        iFrame "Hcgf Hcpu Hpay".
        assert (Havs : avail_sub (Some (S nb')) (S (pt_nodes t)) = avail_sub (Some nb') (pt_nodes t))
          by (rewrite !avail_sub_Some; f_equal; lia).
        rewrite Havs. iExact "Henv".
      - (* ============ NOT FREE: release and step ============ *)
        assert (Hcmpr : eq_vec (rget (CID := CIDf) L3 ap_a5) (zero_reg : mword 64) = false)
          by (rewrite ap_rg_a5; exact Hcmp).
        iApply (wp_cbeqz_fall_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x24)) (mword_of_int 10 : mword 8)
                  (Cregidx (mword_of_int 7)) ap_a5 L3 (K - 4)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hcmpr
                  with "Hcg Hpc Hi24 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp26 : add_vec_int (mword_of_int (AP + 0x24) : mword 64) 2 = mword_of_int (AP + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp26) in "Hpc".
        (* rebuild the lock resource: nothing moved *)
        iAssert (proc_lock_res Φ γs γl (proc_addr k)) with "[Hstate Hchan Hpub Hslots]" as "HR".
        { iApply (proc_lock_res_intro Φ γs γl (proc_addr k) st ch with "Hstate Hchan Hpub Hslots"). }
        (* +0x26 c.mv a0,s1 *)
        iPoseProof (api_26 with "Htext") as "Hi26".
        iApply (wp_cmv_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x26)) ap_a0 ap_s1 L3 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi26 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
        set (R1 := <[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (L3 !!! Regidx ap_s1))]> L3).
        change (<[Regidx ap_a0 := regval_into_reg (add_vec zero_reg (L3 !!! Regidx ap_s1))]> L3) with R1.
        assert (Hp28 : add_vec_int (mword_of_int (AP + 0x26) : mword 64) 2 = mword_of_int (AP + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp28) in "Hpc".
        (* +0x28 jal ra,release *)
        iPoseProof (api_28 with "Htext") as "Hi28".
        iApply (wp_jal_s_sconf (CID := CIDf) Φ (mword_of_int (AP + 0x28)) ap_ra (mword_of_int 2093376 : mword 21)
                  R1 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi28 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (R2 := <[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x28) : mword 64) 4)]> R1).
        change (<[Regidx ap_ra := regval_into_reg (add_vec_int (mword_of_int (AP + 0x28) : mword 64) 4)]> R1) with R2.
        assert (Hjrel : add_vec (mword_of_int (AP + 0x28) : mword 64) (sign_extend' 64 (mword_of_int 2093376 : mword 21)) = mword_of_int KernelSyms.release)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjrel) in "Hpc".
        assert (HR2ra : R2 !!! Regidx ap_ra = add_vec_int (mword_of_int (AP + 0x28) : mword 64) 4) by (rewrite /R2 upd_eq; reflexivity).
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
        iApply (Release.wp_release_sconf (CID := CIDf) Φ γl (proc_addr k) "proc"%string
                  (proc_lock_res Φ γs γl (proc_addr k)) R2 lvl eb pme C (K - 4)%nat
                  Hlka (ap_K10 K HK)
                  with "Hcg Htext Hpc Hislock Hlocked HR Hcpu Hpay [-]").
        (* release's exit index is the very [match] [b] is equal to, so the
           back edge lands on the loop invariant unchanged. *)
        rewrite -Hbmatch.
        iIntros (CIDg Hsg mrel) "Hcg Hpc %Hcsrel Hcpu".
        assert (Hp2c : ret_pc (R2 !!! Regidx ap_ra) = mword_of_int (AP + 0x2c))
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
        iPoseProof (api_2c with "Htext") as "Hi2c".
        iApply (wp_addi4_s_sconf (CID := CIDg) Φ (mword_of_int (AP + 0x2c)) ap_s1 ap_s1 (mword_of_int 360 : mword 12) mrel (K - 4)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi2c [-]").
        iIntros (CIDh Hsh) "Hcg Hpc". iEval (rewrite ap_rg_s1) in "Hcg".
        set (R3 := <[Regidx ap_s1 := regval_into_reg
            (add_vec (mrel !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> mrel).
        change (<[Regidx ap_s1 := regval_into_reg
            (add_vec (mrel !!! Regidx ap_s1) (sign_extend' 64 (mword_of_int 360 : mword 12)))]> mrel) with R3.
        assert (Hp30 : add_vec_int (mword_of_int (AP + 0x2c) : mword 64) 4 = mword_of_int (AP + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
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
        iPoseProof (api_30 with "Htext") as "Hi30".
        destruct (Nat.eqb (S k) NPROC) eqn:Hend.
        + (* the array is exhausted: fall to +0x34 *)
          apply Nat.eqb_eq in Hend.
          assert (Hfall : neq_vec (rget (CID := CIDh) R3 ap_s1) (rget (CID := CIDh) R3 ap_s2) = false)
            by (rewrite ap_rg_s1 ap_rg_s2 HR3s1 HR3s2 Hend; exact ap_neq_end_eq).
          iApply (wp_bne_fall_s_sconf (CID := CIDh) Φ (mword_of_int (AP + 0x30)) (mword_of_int 8172 : mword 13)
                    ap_s2 ap_s1 R3 (K - 4)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hfall
                    with "Hcg Hpc Hi30 [-]").
          iIntros (CIDi Hsi) "Hcg Hpc".
          assert (Hp34 : add_vec_int (mword_of_int (AP + 0x30) : mword 64) 4 = mword_of_int (AP + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp34) in "Hpc".
          (* +0x34 c.li s1,0 *)
          iPoseProof (api_34 with "Htext") as "Hi34".
          iApply (wp_cli_s_sconf (CID := CIDi) Φ (mword_of_int (AP + 0x34)) ap_s1 (mword_of_int 0 : mword 6)
                    (zero_reg : mword 64) R3 (K - 4)%nat b
                    ltac:(vm_compute; discriminate) ltac:(rdok) ap_li_zero
                    with "Hcg Hpc Hi34 [-]").
          iIntros (CIDj Hsj) "Hcg Hpc".
          set (R4 := <[Regidx ap_s1 := regval_into_reg (zero_reg : mword 64)]> R3).
          change (<[Regidx ap_s1 := regval_into_reg (zero_reg : mword 64)]> R3) with R4.
          assert (Hp36 : add_vec_int (mword_of_int (AP + 0x34) : mword 64) 2 = mword_of_int (AP + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hp36) in "Hpc".
          (* +0x36 c.j +0x42 *)
          iPoseProof (api_36 with "Htext") as "Hi36".
          iApply (wp_cj_s_sconf (CID := CIDj) Φ (mword_of_int (AP + 0x36))
                    (sign_extend' 21 (concat_vec (mword_of_int 33 : mword 11) ('b"0"))) R4 (K - 4)%nat b
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi36 [-]").
          iIntros (CIDn Hsn). iNext. iIntros "Hcg Hpc".
          assert (Htgt78 : add_vec (mword_of_int (AP + 0x36) : mword 64)
                             (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 33 : mword 11) ('b"0"))))
                           = mword_of_int (AP + 0x78))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt78) in "Hpc".
          iEval (rewrite /ap_tail) in "Htl".
          iApply ("Htl" $! b CIDn R4 (zero_reg : mword 64) with "[%] Hcg Hpc [Hcpu Henv Hcont]").
          { split; [rewrite /R4 upd_ne; [exact HR3csp | vm_compute; discriminate]|].
            split; [rewrite /R4; apply upd_eq|].
            intros r Hr Ncsp N8 N9 N18.
            rewrite /R4 upd_ne; [| congruence].
            exact (HR3rest r Hr Ncsp N8 N9 N18). }
          iIntros (CIDp Hsp Mf) "[%Hcsf %Ha0f] Hcgf Hpcf".
          iDestruct (cpu_own_transport CIDg CIDp lvl eb pme C b ltac:(wp_next_chain)
                       with "Hcpu") as "Hcpu".
          iSpecialize ("Hcont" $! CIDp with "[%]"); [wp_next_chain|].
          iApply ("Hcont" $! Mf with "[%] Hpcf [-]").
          { exact Hcsf. }
          iEval (rewrite Ha0f).
          rewrite /allocproc_post. iLeft. iFrame "Hcgf Hcpu Henv". done.
        + (* keep scanning: branch back to +0x1c *)
          assert (HkS : (S k < NPROC)%nat) by exact (ap_kS_lt k Hk Hend).
          assert (Htk : neq_vec (rget (CID := CIDh) R3 ap_s1) (rget (CID := CIDh) R3 ap_s2) = true)
            by (rewrite ap_rg_s1 ap_rg_s2 HR3s1 HR3s2; exact (ap_neq_end_lt (S k) HkS)).
          iApply (wp_bne_taken_s_sconf (CID := CIDh) Φ (mword_of_int (AP + 0x30)) (mword_of_int 8172 : mword 13)
                    ap_s2 ap_s1 R3 (K - 4)%nat b
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Htk
                    ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hi30 [-]").
          iNext. iIntros (CIDi Hsi) "Hcg Hpc".
          assert (Htgt1c : add_vec (mword_of_int (AP + 0x30) : mword 64)
                             (sign_extend' 64 (mword_of_int 8172 : mword 13)) = mword_of_int (AP + 0x1c))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt1c) in "Hpc".
          iDestruct (cpu_own_transport CIDg CIDi lvl eb pme C b ltac:(wp_next_chain)
                       with "Hcpu") as "Hcpu".
          iSpecialize ("IHf" $! CIDi with "[%]"); [wp_next_chain|].
          iApply ("IHf" $! (S k) R3 with "[%] [%] [%] Htl Hcont Hcg Hcpu Henv Hpc").
          * exact (ap_fuelS k fuel Hfuel).
          * exact HkS.
          * split; [exact HR3csp|]. split; [exact HR3s1|]. split; [exact HR3s2|].
            exact HR3rest. }
    (* ---- enter the scan at k = 0 ---- *)
    iDestruct (cpu_own_transport CID0 CID10 lvl eb pme C b ltac:(wp_next_chain)
                 with "Hcpu") as "Hcpu".
    iSpecialize ("Hloop" $! NPROC).
    iSpecialize ("Hloop" $! CID10 with "[%]"); [wp_next_chain|].
    iApply ("Hloop" $! 0%nat A5 with "[%] [%] [%] Htail Hcont Hcg Hcpu [Henv] Hpc").
    - exact ap_fuel_init.
    - exact ap_zero_lt.
    - split; [exact HA5csp|]. split; [exact HA5s1|]. split; [exact HA5s2|].
      exact HA5rest.
    - iExact "Henv".
  Qed.

End ProofAllocproc.

End AllocprocProof.
