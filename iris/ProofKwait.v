(* ProofKwait.v -- whole-function WP for kwait() (xv6's wait()).

   The C, the instruction map and the contract are in SpecKwait.v; this file
   is the proof.  Its structure follows the control-flow graph, bottom up,
   one [Local Lemma] per block so that each [Qed] releases its own proof term
   (the argraw lesson in claude-notes/projects/proc-struct-resources.md):

     kw_epilogue    +0x78 .. +0x8e   a0 = s3, restore ra/s0..s7, ret
     kw_exit_wait   +0xe8 .. +0xf6   release(&wait_lock); s3 = -1; -> +0x78
     kw_exit_both   +0x90 .. +0xa4   release(&pp->lock); the above
     kw_found       +0x40 .. +0x74   pid, the optional copyout, the
                                     [pp->parent = 0] store, freeproc, the
                                     two releases -> +0x78
     kw_scan        +0xae/+0xa6/+0xaa the INNER fuel loop over proc[]
     kw_round       +0xdc .. +0xe6 and +0xca .. +0xd8, under an iLöb: one
                                     turn of the OUTER loop, including sleep
     wp_kwait_sconf +0x00 .. +0x3e   the prologue, then [kw_round]

   THE THREE THINGS THIS PROOF HAD TO GET RIGHT.

   * TWO NESTED LOOPS, TWO DIFFERENT INDUCTIONS.  The inner scan is bounded
     (64 slots) and is an ordinary fuel induction, exactly wakeup's and
     kkill's.  The outer loop is UNBOUNDED -- it re-scans after every wakeup
     -- so it is an [iLöb], and the step that pays for the later is sleep's
     own park.  The two are separate lemmas and the inner one takes its exit
     continuation (+0xca) as a PREMISE, so its IH keeps its leading [∀ k M]
     (fdalloc's rule).

   * [havekids] LIVES IN a4, A CALLER-SAVED TEMP.  That is legal only
     because gcc re-materialises it at +0xc6 after every call that could
     clobber it, so it is never live across one -- but it does mean the
     scan's register invariant has to carry a4 as well as the nine
     callee-saved values, and that the found arm (which does not read it)
     must not be made to.

   * THE CHILD IS REACHED THROUGH TWO LOCKS AT ONCE.  wait_lock hands over
     [WaitInv.parents_own] (which licenses the [ld a5,56(s1)] on EVERY slot
     and the [sd x0,56(s1)] on the chosen one), while the child's own
     p->lock hands over [SchedCtx.proc_lock_res] and, through its
     [inv_dormant] guard, the ZOMBIE's [ProcInv.proc_dormant].  Nothing ties
     the two together and nothing needs to: the scan is generic in the slot
     index, so the case [pp = p] (a process recorded as its own parent) is
     not refuted anywhere -- it simply proceeds, and the caller's own
     [proc_priv] rides through untouched. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import IntrDefs WpNext.
Require Import CpuOwn.
Require Import WpLock.
Require Import ArrCursor.
Require Import ProcGeom.
Require Import PageGeom.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FdSlots FileInv.
Require Import ProcInv.
Require Import SchedCtx.
Require Import WaitInv.
Require Import SpecAcquire SpecRelease SpecMyproc SpecKilled SpecSleep.
Require Import SpecCopyout SpecFreeproc.
Require Import SpecPanic.
Require Import SpecProcinit.
Require Import SpecKwait.
From Kernel Require KernelInstrs KernelSyms.
Require Import CodeKwait.
Import Defs.
Local Open Scope Z_scope.
(* a failing tactic in a whole-function WP over [proc_priv] otherwise spends
   tens of minutes FORMATTING the goal -- see durable-notes. *)
Set Printing Depth 40.

Notation KW := KernelSyms.kwait.

Ltac reg_neq_top :=
  lazymatch goal with
  | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
  end.

(* ------------------------------------------------------------------ *)
(* Pure helpers.  Stated with only [mword]/[Z]/[nat] in scope, per the  *)
(* zify rule in durable-notes.                                          *)
(* ------------------------------------------------------------------ *)

(* the five field displacements the scan and the found arm use *)
Lemma kw_state_off (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state X.
Proof. rewrite /p_state /state_off. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kw_xstate_off (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 44 : mword 12)) = p_xstate X.
Proof. rewrite /p_xstate. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kw_pid_off (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 48 : mword 12)) = p_pid X.
Proof. reflexivity. Qed.

Lemma kw_parent_off (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 56 : mword 12)) = p_parent X.
Proof. exact (p_parent_sext X). Qed.

Lemma kw_pagetable_off (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 80 : mword 12)) = p_pagetable X.
Proof. rewrite /p_pagetable. f_equal; apply bv_eq; vm_compute; reflexivity. Qed.

(* a state cell whose 64-bit sign extension is 5 is ZOMBIE *)
Lemma kw_sext_zombie (st : mword 32) :
  (mword_of_int 5 : mword 64) = sign_extend' 64 st -> st = ZOMBIE.
Proof.
  intro H.
  assert (Ht : trunc32 (mword_of_int 5 : mword 64) = trunc32 (sign_extend' 64 st))
    by (rewrite H; reflexivity).
  rewrite trunc32_sext64 in Ht. rewrite -Ht.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* writing back the descriptor that is already there is a no-op -- what the
   arms that never call copyout need to close the block's [upd_upt]. *)
Lemma upd_upt_id (V : pprivate) : upd_upt V (pv_upt V) = V.
Proof. by destruct V. Qed.

(* The stack-budget and nesting side conditions, as NAMED lemmas with only
   [nat]/[Z] in scope.  Inside these blocks the context is full of
   [bv_unsigned]s, so an inline [ltac:(lia)] answers "Cannot find witness" --
   the zify-hook rule in durable-notes, hit at every call site. *)
Lemma kw_K10 (K : nat) : (K_kwait <= K)%nat -> (10 <= K - 10)%nat.
Proof. unfold K_kwait. lia. Qed.
Lemma kw_K10K (K : nat) : (K_kwait <= K)%nat -> (10 <= K)%nat.
Proof. unfold K_kwait. lia. Qed.
Lemma kw_K14 (K : nat) : (K_kwait <= K)%nat -> (14 <= K - 10)%nat.
Proof. unfold K_kwait. lia. Qed.
Lemma kw_K22 (K : nat) : (K_kwait <= K)%nat -> (22 <= K - 10)%nat.
Proof. unfold K_kwait. lia. Qed.
Lemma kw_K44 (K : nat) : (K_kwait <= K)%nat -> (44 <= K - 10)%nat.
Proof. unfold K_kwait. lia. Qed.
Lemma kw_K50 (K : nat) : (K_kwait <= K)%nat -> (50 <= K - 10)%nat.
Proof. unfold K_kwait. lia. Qed.
Lemma kw_ilvl0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma kw_ilvl1 : (Z.of_nat 1 + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma kw_ilvl2 : (Z.of_nat 2 + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma kw_len4 : (Z.of_nat 4 < 2 ^ 64)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma kw_eq_vec_refl {n} (x : mword n) : eq_vec x x = true.
Proof. apply eq_vec_true_iff. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The register invariants.                                            *)
(* ------------------------------------------------------------------ *)
(* [kw_cs_rest] is the callee-saved registers kwait neither saves nor uses
   -- s8..s11 -- as ONE predicate rather than four equalities: the blocks
   thread it through every call with [callee_saved_lookup] and the epilogue
   cashes it in for the four matching conjuncts of the final
   [callee_saved].  Spelled with [csp_rs1] (not [mword_of_int 2]) per
   durable-notes: [congruence] cannot bridge the two. *)
Definition kw_cs_rest (M mb : regfile) : Prop :=
  forall r : mword 5, is_cs_idx r = true ->
    r <> csp_rs1 ->
    r <> (mword_of_int 8 : mword 5) -> r <> (mword_of_int 9 : mword 5) ->
    r <> (mword_of_int 18 : mword 5) -> r <> (mword_of_int 19 : mword 5) ->
    r <> (mword_of_int 20 : mword 5) -> r <> (mword_of_int 21 : mword 5) ->
    r <> (mword_of_int 22 : mword 5) -> r <> (mword_of_int 23 : mword 5) ->
    M !!! Regidx r = mb !!! Regidx r.

Lemma kw_cs_rest_cs (M M' mb : regfile) :
  callee_saved M M' -> kw_cs_rest M mb -> kw_cs_rest M' mb.
Proof.
  intros Hcs H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23.
  rewrite (callee_saved_lookup Hcs r Hr). by apply H.
Qed.

(* an insert at a NON-callee-saved register (a0..a5, ra) *)
Lemma kw_cs_rest_ncs (M mb : regfile) (rr : mword 5) (v : mword 64) :
  is_cs_idx rr = false -> kw_cs_rest M mb -> kw_cs_rest (<[Regidx rr := v]> M) mb.
Proof.
  intros Hn H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23.
  rewrite upd_ne; [by apply H |].
  intro He. apply (is_cs_idx_true_neq rr r Hn Hr). by symmetry.
Qed.

(* ... and at each of the nine registers that ARE callee-saved but are
   excluded by the predicate's own premises.  One lemma apiece: the generic
   [kw_cs_rest_ncs] does NOT apply to them (durable-notes / kkill). *)
Lemma kw_cs_rest_sp (M mb : regfile) (v : mword 64) :
  kw_cs_rest M mb -> kw_cs_rest (<[Regidx csp_rs1 := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kw_cs_rest_s0 (M mb : regfile) (v : mword 64) :
  kw_cs_rest M mb -> kw_cs_rest (<[Regidx (mword_of_int 8 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kw_cs_rest_s1 (M mb : regfile) (v : mword 64) :
  kw_cs_rest M mb -> kw_cs_rest (<[Regidx (mword_of_int 9 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kw_cs_rest_s2 (M mb : regfile) (v : mword 64) :
  kw_cs_rest M mb -> kw_cs_rest (<[Regidx (mword_of_int 18 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kw_cs_rest_s3 (M mb : regfile) (v : mword 64) :
  kw_cs_rest M mb -> kw_cs_rest (<[Regidx (mword_of_int 19 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kw_cs_rest_s4 (M mb : regfile) (v : mword 64) :
  kw_cs_rest M mb -> kw_cs_rest (<[Regidx (mword_of_int 20 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kw_cs_rest_s5 (M mb : regfile) (v : mword 64) :
  kw_cs_rest M mb -> kw_cs_rest (<[Regidx (mword_of_int 21 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kw_cs_rest_s6 (M mb : regfile) (v : mword 64) :
  kw_cs_rest M mb -> kw_cs_rest (<[Regidx (mword_of_int 22 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite upd_ne; [by apply H | congruence]. Qed.
Lemma kw_cs_rest_s7 (M mb : regfile) (v : mword 64) :
  kw_cs_rest M mb -> kw_cs_rest (<[Regidx (mword_of_int 23 : mword 5) := v]> M) mb.
Proof. intros H r Hr N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite upd_ne; [by apply H | congruence]. Qed.

Lemma kw_cs_rest_refl (M : regfile) : kw_cs_rest M M.
Proof. intros r _ _ _ _ _ _ _ _ _ _. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The SCAN's register invariant.                                       *)
(* ------------------------------------------------------------------ *)
(* Note what is NOT here: [a4].  [havekids] lives in a caller-saved temp,
   so acquire and release clobber it, and the scan re-materialises it at
   +0xc6 after every call -- which is exactly why gcc may keep it there at
   all.  It rides beside this predicate as a separate equation, asserted
   only at the points where it is genuinely live (the loop head, the
   pp++/test tail, and the scan's exit). *)
Definition kw_scan_regs (M mm : regfile) (pme addr : mword 64) (kk : nat) : Prop :=
  M !!! Regidx csp_rs1
    = add_vec (mm !!! Regidx csp_rs1)
        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) /\
  M !!! Regidx (mword_of_int 9 : mword 5) = proc_addr kk /\
  M !!! Regidx (mword_of_int 18 : mword 5) = pme /\
  M !!! Regidx (mword_of_int 19 : mword 5) = proc_addr NPROC /\
  M !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 5 : mword 64) /\
  M !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 1 : mword 64) /\
  M !!! Regidx (mword_of_int 22 : mword 5) = wait_lock_addr /\
  M !!! Regidx (mword_of_int 23 : mword 5) = addr /\
  kw_cs_rest M mm.

(* the scan's exit test, [beq s1,s3], as the index comparison *)
Lemma kw_neq_end (i : nat) :
  (i <= NPROC)%nat ->
  neq_vec (proc_addr i) (proc_addr NPROC) = negb (Nat.eqb i NPROC).
Proof.
  intro Hi. rewrite !proc_addr_acur. unfold pacur.
  apply (acur_neq KernelSyms.proc proc_size i NPROC
           proc_base_nonneg proc_size_pos proc_end_fits Hi).
Qed.

Lemma kw_end_lt (i : nat) : (i < NPROC)%nat -> eq_vec (proc_addr i) (proc_addr NPROC) = false.
Proof.
  intro Hi.
  assert (Hn : neq_vec (proc_addr i) (proc_addr NPROC) = true).
  { rewrite (kw_neq_end i (Nat.lt_le_incl _ _ Hi)).
    destruct (Nat.eqb_spec i NPROC) as [He | _]; [ exfalso; lia | reflexivity ]. }
  unfold neq_vec in Hn. by apply negb_true_iff in Hn.
Qed.

Lemma kw_fuel0 (kk : nat) : (NPROC - kk <= 0)%nat -> (kk < NPROC)%nat -> False.
Proof. unfold NPROC. lia. Qed.

(* The three MOVES of the scan's register invariant, as named lemmas with
   the registers spelled out.  Do NOT inline these as
   [split_and!; first [rewrite (callee_saved_lookup H _ ltac:(...)) | ...]]:
   the [_] leaves the lemma's register argument an evar when the [ltac:]
   runs, which is durable-notes' "a tactic in an argument position whose
   expected type is still an evar can DIVERGE" -- it looks exactly like a
   slow file (measured here: no return in two minutes). *)
Lemma kw_scan_regs_cs (M M' mm : regfile) (pme addr : mword 64) (kk : nat) :
  callee_saved M M' -> kw_scan_regs M mm pme addr kk -> kw_scan_regs M' mm pme addr kk.
Proof.
  intros Hcs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite /kw_scan_regs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact A1.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact A2.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact A3.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). exact A4.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)). exact A5.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)). exact A6.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). exact A7.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). exact A8.
  - eapply kw_cs_rest_cs; [exact Hcs | exact A9].
Qed.

Lemma kw_scan_regs_ncs (M mm : regfile) (pme addr : mword 64) (kk : nat)
    (rr : mword 5) (v : mword 64) :
  is_cs_idx rr = false ->
  kw_scan_regs M mm pme addr kk ->
  kw_scan_regs (<[Regidx rr := v]> M) mm pme addr kk.
Proof.
  intros Hn (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  assert (Hne : forall c : mword 5, is_cs_idx c = true -> Regidx c <> Regidx rr)
    by (intros c Hc He; exact (is_cs_idx_true_neq rr c Hn Hc (eq_sym He))).
  rewrite /kw_scan_regs. split_and!.
  - rewrite upd_ne; [exact A1 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A2 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A3 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A4 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A5 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A6 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A7 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A8 | apply Hne; vm_compute; reflexivity].
  - by apply kw_cs_rest_ncs.
Qed.

(* ------------------------------------------------------------------ *)
(* THE OUTER LOOP's register invariant: the scan's, MINUS the cursor.   *)
(* ------------------------------------------------------------------ *)
(* At +0xdc [s1] is dead -- the round is about to rebuild it from the
   [auipc]/[addi] pair -- so the round head cannot carry the [s1] conjunct
   and the scan's predicate cannot serve.  Everything else is the same,
   which is what the two bridges below say. *)
Definition kw_round_regs (M mm : regfile) (pme addr : mword 64) : Prop :=
  M !!! Regidx csp_rs1
    = add_vec (mm !!! Regidx csp_rs1)
        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) /\
  M !!! Regidx (mword_of_int 18 : mword 5) = pme /\
  M !!! Regidx (mword_of_int 19 : mword 5) = proc_addr NPROC /\
  M !!! Regidx (mword_of_int 20 : mword 5) = (mword_of_int 5 : mword 64) /\
  M !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 1 : mword 64) /\
  M !!! Regidx (mword_of_int 22 : mword 5) = wait_lock_addr /\
  M !!! Regidx (mword_of_int 23 : mword 5) = addr /\
  kw_cs_rest M mm.

Lemma kw_round_regs_of_scan (M mm : regfile) (pme addr : mword 64) (kk : nat) :
  kw_scan_regs M mm pme addr kk -> kw_round_regs M mm pme addr.
Proof.
  intros (A1 & _ & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite /kw_round_regs. split_and!; assumption.
Qed.

Lemma kw_scan_regs_of_round (M mm : regfile) (pme addr : mword 64) :
  kw_round_regs M mm pme addr ->
  M !!! Regidx (mword_of_int 9 : mword 5) = proc_addr 0 ->
  kw_scan_regs M mm pme addr 0.
Proof.
  intros (A1 & A3 & A4 & A5 & A6 & A7 & A8 & A9) Hs1.
  rewrite /kw_scan_regs. split_and!; assumption.
Qed.

Lemma kw_round_regs_cs (M M' mm : regfile) (pme addr : mword 64) :
  callee_saved M M' -> kw_round_regs M mm pme addr -> kw_round_regs M' mm pme addr.
Proof.
  intros Hcs (A1 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite /kw_round_regs. split_and!.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact A1.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact A3.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). exact A4.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)). exact A5.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)). exact A6.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). exact A7.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). exact A8.
  - eapply kw_cs_rest_cs; [exact Hcs | exact A9].
Qed.

Lemma kw_round_regs_ncs (M mm : regfile) (pme addr : mword 64)
    (rr : mword 5) (v : mword 64) :
  is_cs_idx rr = false ->
  kw_round_regs M mm pme addr ->
  kw_round_regs (<[Regidx rr := v]> M) mm pme addr.
Proof.
  intros Hn (A1 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  assert (Hne : forall c : mword 5, is_cs_idx c = true -> Regidx c <> Regidx rr)
    by (intros c Hc He; exact (is_cs_idx_true_neq rr c Hn Hc (eq_sym He))).
  rewrite /kw_round_regs. split_and!.
  - rewrite upd_ne; [exact A1 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A3 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A4 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A5 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A6 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A7 | apply Hne; vm_compute; reflexivity].
  - rewrite upd_ne; [exact A8 | apply Hne; vm_compute; reflexivity].
  - by apply kw_cs_rest_ncs.
Qed.

(* [s1] is not a conjunct of the round's predicate, so the cursor's
   reconstruction is invisible to it -- but [s1] IS excluded by
   [kw_cs_rest], so the write still needs its own lemma. *)
Lemma kw_round_regs_s1w (M mm : regfile) (pme addr : mword 64) (v : mword 64) :
  kw_round_regs M mm pme addr ->
  kw_round_regs (<[Regidx (mword_of_int 9 : mword 5) := v]> M) mm pme addr.
Proof.
  intros (A1 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite /kw_round_regs. split_and!.
  - rewrite upd_ne; [exact A1 | reg_neq_top].
  - rewrite upd_ne; [exact A3 | reg_neq_top].
  - rewrite upd_ne; [exact A4 | reg_neq_top].
  - rewrite upd_ne; [exact A5 | reg_neq_top].
  - rewrite upd_ne; [exact A6 | reg_neq_top].
  - rewrite upd_ne; [exact A7 | reg_neq_top].
  - rewrite upd_ne; [exact A8 | reg_neq_top].
  - by apply kw_cs_rest_s1.
Qed.

(* The two directions of "[eb = true], so a chain hypothesis stated at the
   literal [true] and one stated at [eb] are the same fact".  Named lemmas
   because [wp_next_chain]'s [specialize] cannot bridge the two spellings,
   and because [eb] must NOT be substituted inside a body that runs [iNext]
   over [cpu_own] (durable-notes / sp_post_sleep_body). *)
Lemma kw_chain_eb (eb : bool) (pv : mword 64) (A B : CPU) :
  eb = true ->
  (true = false \/ pv = zero_reg -> A = B) ->
  (eb = false \/ pv = zero_reg -> A = B).
Proof. intros He H. by rewrite He. Qed.

Lemma kw_chain_true (eb : bool) (pv : mword 64) (A B : CPU) :
  eb = true ->
  (eb = false \/ pv = zero_reg -> A = B) ->
  (true = false \/ pv = zero_reg -> A = B).
Proof. intros He H. by rewrite He in H. Qed.

(* the cursor bump: the ONLY write to a callee-saved register the scan makes *)
Lemma kw_scan_regs_s1 (M mm : regfile) (pme addr : mword 64) (kk : nat) :
  kw_scan_regs M mm pme addr kk ->
  kw_scan_regs (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (proc_addr (S kk))]> M)
    mm pme addr (S kk).
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite /kw_scan_regs. split_and!.
  - rewrite upd_ne; [exact A1 | reg_neq_top].
  - rewrite upd_eq. reflexivity.
  - rewrite upd_ne; [exact A3 | reg_neq_top].
  - rewrite upd_ne; [exact A4 | reg_neq_top].
  - rewrite upd_ne; [exact A5 | reg_neq_top].
  - rewrite upd_ne; [exact A6 | reg_neq_top].
  - rewrite upd_ne; [exact A7 | reg_neq_top].
  - rewrite upd_ne; [exact A8 | reg_neq_top].
  - by apply kw_cs_rest_s1.
Qed.



Module KwaitProof (Acquire : ACQUIRE) (Release : RELEASE) (Myproc : MYPROC)
                  (Killed : KILLED) (Sleep : SLEEP)
                  (Copyout : COPYOUT) (Freeproc : FREEPROC) : KWAIT.

Section ProofKwait.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !fileG Σ}.
  (* NO section [CpuId]: every block lemma is applied at the hart the block
     before it handed back, which a section variable could not express. *)

  (* peel ONE update layer at a time (unfold-then-peel on the whole set-chain
     is O(depth^2): claude-notes/optimization.md). *)
  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.
  Ltac peel_reg_step :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].
  Ltac peel_reg := peel_reg_step; reflexivity.
  Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.

  (* RE-ANCHORING a [wp_next].  A block lemma receives its continuation
     anchored at ITS entry hart and must hand it to the NEXT block, whose
     entry hart is wherever the intervening instructions landed.  [wp_next]
     is just a guarded [forall CID], so the move is one composition of the
     two conditional equalities -- the resource-side [cpu_own_transport] of
     the continuation side. *)
  Lemma kw_next_reanchor `{GEN : GenId} (CID0 CID1 : CpuId)
      (b : bool) (pv : mword 64) (K : forall (CID : CpuId), iProp Σ) :
    (b = false \/ pv = zero_reg -> (CID1 : CPU) = (CID0 : CPU)) ->
    wp_next (CID0 := CID0) b pv K -∗ wp_next (CID0 := CID1) b pv K.
  Proof.
    intros Hch. iIntros "H" (CID Hs). iApply ("H" $! CID). iPureIntro.
    intro Hb. rewrite (Hs Hb). exact (Hch Hb).
  Qed.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).

  (* The nine callee-saved cells kwait's prologue pushes, plus the padding
     slot 10 the code never touches.  Bundled so that every block lemma
     carries the frame as ONE hypothesis instead of ten. *)
  Definition kw_frame (sp0 : mword 64) (mm : regfile) : iProp Σ :=
    (pa_stk sp0 1  ↦₈ (mm !!! Regidx Rra) ∗
     pa_stk sp0 2  ↦₈ (mm !!! Regidx Rs0) ∗
     pa_stk sp0 3  ↦₈ (mm !!! Regidx Rs1) ∗
     pa_stk sp0 4  ↦₈ (mm !!! Regidx Rs2) ∗
     pa_stk sp0 5  ↦₈ (mm !!! Regidx Rs3) ∗
     pa_stk sp0 6  ↦₈ (mm !!! Regidx Rs4) ∗
     pa_stk sp0 7  ↦₈ (mm !!! Regidx Rs5) ∗
     pa_stk sp0 8  ↦₈ (mm !!! Regidx Rs6) ∗
     pa_stk sp0 9  ↦₈ (mm !!! Regidx Rs7) ∗
     (∃ w : mword 64, pa_stk sp0 10 ↦₈ w))%I.

  (* ------------------------------------------------------------------ *)
  (* THE FUNCTION EXIT, as ONE named proposition.                        *)
  (* ------------------------------------------------------------------ *)
  (* Every block below +0xca hands the caller's continuation on unchanged,
     so it is worth naming: [R] is the frame the continuation still wants
     back (the running-thread bundle -- the [park_hlf] receipt -- which
     nothing between the prologue and the exit touches, and which therefore
     rides through the scan rather than being packaged into the closure).
     Packaging it in would be unsound in the other direction: the +0xca
     exit needs those very resources for sleep, and a closure cannot give
     them back. *)
  Definition kw_exit_fn `{GEN : GenId} (CID0 : CPU) (Φ : mval -> iProp Σ)
      (γf : gname) (mm : regfile) (pme : mword 64) (K : nat) (eb : bool)
      (C : iProp Σ) (pid : mword 32) (V : pprivate) (R : iProp Σ) : iProp Σ :=
    (wp_next (CID0 := CID0) eb pme (fun (CID : CpuId) =>
      ∀ (mf : regfile) (P' : uptd) (rv : mword 32),
        ⌜ callee_saved mm mf ⌝ -∗
        ⌜ mf !!! Regidx Ra0 = sign_extend' 64 rv ⌝ -∗
        ⌜ uptd_ext_sz (pv_sz V) (pv_upt V) P' ⌝ -∗
        sie_cap_gpr mf K eb pme -∗
        cpu_own 0 eb pme C eb -∗
        pc_is (ret_pc (mm !!! Regidx Rra)) -∗
        proc_priv γf pme pid (upd_upt V P') -∗
        R -∗
        WP (Loop : expr riscv_lang) {{ Φ }}))%I.

  (* The running-thread bundle kwait carries from the prologue to the exit
     and touches nowhere in between: it is [R] for every block below, and
     the two resources sleep wants back at the outer loop's foot. *)
  Definition kw_rt (pme : mword 64) (jj : nat) : iProp Σ :=
    (running_claim jj)%I.

  (* ------------------------------------------------------------------ *)
  (* THE OUTER LOOP, +0xdc.  Unbounded (every wakeup re-scans), so this   *)
  (* is what the [iLöb] is about.                                        *)
  (* ------------------------------------------------------------------ *)
  (* The function exit rides IN as a premise (fdalloc's rule -- a resource
     in the context would cost the statement its leading binders), and it
     is anchored at the TURN's own hart rather than at [CID0]: sleep hands
     the thread back on an arbitrary hart, and a [wp_next] can only ever be
     re-anchored FORWARD. *)
  Definition kw_round `{GEN : GenId} (CID0 : CPU) (Φ : mval -> iProp Σ)
      (γf γw : gname) (jj : nat) (mm : regfile) (pme addr : mword 64)
      (K : nat) (eb : bool) (C : iProp Σ) (pid : mword 32) (V : pprivate) : iProp Σ :=
    (wp_next (CID0 := CID0) true pme (fun (CID : CpuId) =>
      ∀ (M : regfile),
        ⌜ kw_round_regs M mm pme addr ⌝ -∗
        sie_cap_gpr M (K - 10)%nat false pme -∗
        cpu_own 1 eb pme C false -∗
        arm_pay 0 eb pme -∗
        pc_is (mword_of_int (KW + 0xdc)) -∗
        locked γw CID -∗ wait_res -∗
        proc_priv γf pme pid V -∗
        kw_frame (mm !!! Regidx csp_rs1) mm -∗
        kw_rt pme jj -∗
        kw_exit_fn CID Φ γf mm pme K eb C pid V (kw_rt pme jj) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}))%I.

  (* [SchedCtx.proc_slots_unused]'s ZOMBIE twin: a ZOMBIE is not RUNNING and
     needs no context, so its slot holds exactly the dormant block and the
     whole park receipt.  Stated here rather than in SchedCtx.v because
     kwait is its first (and so far only) consumer; it belongs beside
     [proc_slots_unused] the moment kexit wants it too. *)
  Lemma kw_slots_zombie `{GEN : GenId} `{CIDz : CpuId} (Ph : mval -> iProp Σ) (gs : list gname) (pa : mword 64) :
    proc_slots Ph gs pa ZOMBIE -∗ proc_dormant pa ZOMBIE ∗ park_at_full pa false.
  Proof.
    rewrite /proc_slots inv_dormant_ZOMBIE not_running_ZOMBIE is_running_ZOMBIE.
    rewrite (_ : needs_ctx ZOMBIE = false); [| vm_compute; reflexivity].
    iIntros "[_ [_ [$ $]]]".
  Qed.

  (* ================================================================== *)
  (* THE EPILOGUE, +0x78 .. +0x8e.  THREE entries -- the found arm falls *)
  (* through into it, and the two [li s3,-1] tails jump here -- so it is *)
  (* one lemma parameterised by the value s3 carries, exactly the        *)
  (* factoring sys_close's [sc_tail] and allocproc's epilogue use.       *)
  (* ================================================================== *)
  Local Lemma kw_epilogue `{GEN : GenId} `{CIDe : CpuId}
      (Φ : mval -> iProp Σ) (mm Mx : regfile) (pme rv : mword 64)
      (K lvl : nat) (eb bx : bool) (C : iProp Σ) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    (10 <= K)%nat ->
    Mx !!! Regidx csp_rs1 = spr ->
    Mx !!! Regidx Rs3 = rv ->
    kw_cs_rest Mx mm ->
    sie_cap_gpr Mx (K - 10)%nat bx pme -∗
    cpu_own lvl eb pme C bx -∗
    kernel_text -∗
    pc_is (mword_of_int (KW + 0x78)) -∗
    kw_frame sp0 mm -∗
    wp_next bx pme (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜ callee_saved mm mf ⌝ -∗
        ⌜ mf !!! Regidx Ra0 = rv ⌝ -∗
        sie_cap_gpr mf K bx pme -∗
        cpu_own lvl eb pme C bx -∗
        pc_is (ret_pc (mm !!! Regidx Rra)) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spr HK Hsp Hs3 Hcs.
    iIntros "Hcg Hown #Htext Hpc Hframe0 Hcont".
    iDestruct "Hframe0" as "(Hc72 & Hc64 & Hc56 & Hc48 & Hc40 & Hc32 & Hc24 & Hc16 & Hc08 & Hc00)".
    iDestruct "Hc00" as (v0) "Hc00".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 7).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 8).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 9).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb10 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 10).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 10 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (kwi_78 with "Htext") as "Hi78".
    iPoseProof (kwi_7a with "Htext") as "Hi7a".
    iPoseProof (kwi_7c with "Htext") as "Hi7c".
    iPoseProof (kwi_7e with "Htext") as "Hi7e".
    iPoseProof (kwi_80 with "Htext") as "Hi80".
    iPoseProof (kwi_82 with "Htext") as "Hi82".
    iPoseProof (kwi_84 with "Htext") as "Hi84".
    iPoseProof (kwi_86 with "Htext") as "Hi86".
    iPoseProof (kwi_88 with "Htext") as "Hi88".
    iPoseProof (kwi_8a with "Htext") as "Hi8a".
    iPoseProof (kwi_8c with "Htext") as "Hi8c".
    iPoseProof (kwi_8e with "Htext") as "Hi8e".
    (* +0x78 c.mv a0,s3 -- the return value *)
    assert (Hrg78 : rget (CID := CIDe) Mx Rs3 = Mx !!! Regidx Rs3) by (rgne; reflexivity).
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0x78)) Ra0 Rs3
              Mx (K - 10)%nat bx ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78 [-]").
    iIntros (CIDe0 Hse0) "Hcg Hpc".
    iEval (rewrite Hrg78 Hs3) in "Hcg".
    set (E0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg rv)]> Mx).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg rv)]> Mx) with E0.
    assert (HspE0 : E0 !!! Regidx csp_rs1 = spr)
      by (rewrite /E0 upd_ne; [exact Hsp | reg_neq]).
    assert (Hp7a : add_vec_int (mword_of_int (KW + 0x78) : mword 64) 2 = mword_of_int (KW + 0x7a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7a) in "Hpc".
    (* +0x7a ld ra,72(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KW + 0x7a)) (mword_of_int 9 : mword 6) Rra
              E0 (K - 10)%nat (mm !!! Regidx Rra) bx
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a [Hc72] [-]").
    { iEval (rewrite HspE0 Hb1). iExact "Hc72". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hc72". iEval (rewrite HspE0 Hb1) in "Hc72".
    set (E1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> E0).
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1 upd_ne; [exact HspE0 | reg_neq]).
    assert (Hp7c : add_vec_int (mword_of_int (KW + 0x7a) : mword 64) 2 = mword_of_int (KW + 0x7c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7c) in "Hpc".
    (* +0x7c ld s0,64(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KW + 0x7c)) (mword_of_int 8 : mword 6) Rs0
              E1 (K - 10)%nat (mm !!! Regidx Rs0) bx
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7c [Hc64] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc64". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hc64". iEval (rewrite HspE1 Hb2) in "Hc64".
    set (E2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1).
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2 upd_ne; [exact HspE1 | reg_neq]).
    assert (Hp7e : add_vec_int (mword_of_int (KW + 0x7c) : mword 64) 2 = mword_of_int (KW + 0x7e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7e) in "Hpc".
    (* +0x7e ld s1,56(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KW + 0x7e)) (mword_of_int 7 : mword 6) Rs1
              E2 (K - 10)%nat (mm !!! Regidx Rs1) bx
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7e [Hc56] [-]").
    { iEval (rewrite HspE2 Hb3). iExact "Hc56". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hc56". iEval (rewrite HspE2 Hb3) in "Hc56".
    set (E3 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E2).
    assert (HspE3 : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3 upd_ne; [exact HspE2 | reg_neq]).
    assert (Hp80 : add_vec_int (mword_of_int (KW + 0x7e) : mword 64) 2 = mword_of_int (KW + 0x80))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp80) in "Hpc".
    (* +0x80 ld s2,48(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KW + 0x80)) (mword_of_int 6 : mword 6) Rs2
              E3 (K - 10)%nat (mm !!! Regidx Rs2) bx
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi80 [Hc48] [-]").
    { iEval (rewrite HspE3 Hb4). iExact "Hc48". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hc48". iEval (rewrite HspE3 Hb4) in "Hc48".
    set (E4 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> E3).
    assert (HspE4 : E4 !!! Regidx csp_rs1 = spr) by (rewrite /E4 upd_ne; [exact HspE3 | reg_neq]).
    assert (Hp82 : add_vec_int (mword_of_int (KW + 0x80) : mword 64) 2 = mword_of_int (KW + 0x82))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp82) in "Hpc".
    (* +0x82 ld s3,40(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KW + 0x82)) (mword_of_int 5 : mword 6) Rs3
              E4 (K - 10)%nat (mm !!! Regidx Rs3) bx
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi82 [Hc40] [-]").
    { iEval (rewrite HspE4 Hb5). iExact "Hc40". }
    iIntros (CIDe5 Hse5) "Hcg Hpc Hc40". iEval (rewrite HspE4 Hb5) in "Hc40".
    set (E5 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> E4).
    assert (HspE5 : E5 !!! Regidx csp_rs1 = spr) by (rewrite /E5 upd_ne; [exact HspE4 | reg_neq]).
    assert (Hp84 : add_vec_int (mword_of_int (KW + 0x82) : mword 64) 2 = mword_of_int (KW + 0x84))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp84) in "Hpc".
    (* +0x84 ld s4,32(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KW + 0x84)) (mword_of_int 4 : mword 6) Rs4
              E5 (K - 10)%nat (mm !!! Regidx Rs4) bx
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi84 [Hc32] [-]").
    { iEval (rewrite HspE5 Hb6). iExact "Hc32". }
    iIntros (CIDe6 Hse6) "Hcg Hpc Hc32". iEval (rewrite HspE5 Hb6) in "Hc32".
    set (E6 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> E5).
    assert (HspE6 : E6 !!! Regidx csp_rs1 = spr) by (rewrite /E6 upd_ne; [exact HspE5 | reg_neq]).
    assert (Hp86 : add_vec_int (mword_of_int (KW + 0x84) : mword 64) 2 = mword_of_int (KW + 0x86))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp86) in "Hpc".
    (* +0x86 ld s5,24(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KW + 0x86)) (mword_of_int 3 : mword 6) Rs5
              E6 (K - 10)%nat (mm !!! Regidx Rs5) bx
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi86 [Hc24] [-]").
    { iEval (rewrite HspE6 Hb7). iExact "Hc24". }
    iIntros (CIDe7 Hse7) "Hcg Hpc Hc24". iEval (rewrite HspE6 Hb7) in "Hc24".
    set (E7 := <[Regidx Rs5 := regval_into_reg (mm !!! Regidx Rs5)]> E6).
    assert (HspE7 : E7 !!! Regidx csp_rs1 = spr) by (rewrite /E7 upd_ne; [exact HspE6 | reg_neq]).
    assert (Hp88 : add_vec_int (mword_of_int (KW + 0x86) : mword 64) 2 = mword_of_int (KW + 0x88))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp88) in "Hpc".
    (* +0x88 ld s6,16(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KW + 0x88)) (mword_of_int 2 : mword 6) Rs6
              E7 (K - 10)%nat (mm !!! Regidx Rs6) bx
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi88 [Hc16] [-]").
    { iEval (rewrite HspE7 Hb8). iExact "Hc16". }
    iIntros (CIDe8 Hse8) "Hcg Hpc Hc16". iEval (rewrite HspE7 Hb8) in "Hc16".
    set (E8 := <[Regidx Rs6 := regval_into_reg (mm !!! Regidx Rs6)]> E7).
    assert (HspE8 : E8 !!! Regidx csp_rs1 = spr) by (rewrite /E8 upd_ne; [exact HspE7 | reg_neq]).
    assert (Hp8a : add_vec_int (mword_of_int (KW + 0x88) : mword 64) 2 = mword_of_int (KW + 0x8a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8a) in "Hpc".
    (* +0x8a ld s7,8(sp) *)
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (KW + 0x8a)) (mword_of_int 1 : mword 6) Rs7
              E8 (K - 10)%nat (mm !!! Regidx Rs7) bx
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi8a [Hc08] [-]").
    { iEval (rewrite HspE8 Hb9). iExact "Hc08". }
    iIntros (CIDe9 Hse9) "Hcg Hpc Hc08". iEval (rewrite HspE8 Hb9) in "Hc08".
    set (E9 := <[Regidx Rs7 := regval_into_reg (mm !!! Regidx Rs7)]> E8).
    assert (HspE9 : E9 !!! Regidx csp_rs1 = spr) by (rewrite /E9 upd_ne; [exact HspE8 | reg_neq]).
    assert (Hp8c : add_vec_int (mword_of_int (KW + 0x8a) : mword 64) 2 = mword_of_int (KW + 0x8c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8c) in "Hpc".
    (* +0x8c c.addi16sp sp,+80 -- the frame pop *)
    set (E10 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E9 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E9).
    assert (Hwv : add_vec (E9 !!! Regidx csp_rs1)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = sp0).
    { rewrite HspE9. unfold spr. apply frame_cancel_80. }
    assert (Hpop : E9 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E9 !!! Regidx csp_rs1)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10).
    { rewrite Hwv HspE9. symmetry. exact Hsprstk. }
    iAssert (stack_own sp0 10) with "[Hc72 Hc64 Hc56 Hc48 Hc40 Hc32 Hc24 Hc16 Hc08 Hc00]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc72". { iExists (mm !!! Regidx Rra). iExact "Hc72". }
      iSplitL "Hc64". { iExists (mm !!! Regidx Rs0). iExact "Hc64". }
      iSplitL "Hc56". { iExists (mm !!! Regidx Rs1). iExact "Hc56". }
      iSplitL "Hc48". { iExists (mm !!! Regidx Rs2). iExact "Hc48". }
      iSplitL "Hc40". { iExists (mm !!! Regidx Rs3). iExact "Hc40". }
      iSplitL "Hc32". { iExists (mm !!! Regidx Rs4). iExact "Hc32". }
      iSplitL "Hc24". { iExists (mm !!! Regidx Rs5). iExact "Hc24". }
      iSplitL "Hc16". { iExists (mm !!! Regidx Rs6). iExact "Hc16". }
      iSplitL "Hc08". { iExists (mm !!! Regidx Rs7). iExact "Hc08". }
      iSplitL "Hc00". { iExists v0. iExact "Hc00". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf Φ (mword_of_int (KW + 0x8c)) (mword_of_int 5 : mword 6)
              E9 (K - 10)%nat 10 bx Hpop
              with "Hcg Hpc Hi8c Hframe [-]").
    iIntros (CIDe10 Hse10) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E9 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E9) with E10.
    assert (Hnk : ((K - 10) + 10)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hp8e : add_vec_int (mword_of_int (KW + 0x8c) : mword 64) 2 = mword_of_int (KW + 0x8e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8e) in "Hpc".
    (* +0x8e c.ret *)
    assert (HE10ra : E10 !!! Regidx Rra = mm !!! Regidx Rra) by peel_reg.
    assert (Hrt : ret_pc (E10 !!! Regidx Rra) = ret_pc (mm !!! Regidx Rra))
      by (rewrite HE10ra; reflexivity).
    iApply (wp_cret_s_sconf Φ (mword_of_int (KW + 0x8e)) Rra E10 K bx
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi8e [-]").
    iIntros (CIDe11 Hse11) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite Hrt) in "Hpc".
    iSpecialize ("Hcont" $! CIDe11 with "[%]"); [wp_next_chain|].
    assert (HownC : bx = false \/ pme = zero_reg -> (CIDe11 : CPU) = (CIDe : CPU))
      by wp_next_chain.
    iDestruct (cpu_own_transport CIDe CIDe11 lvl eb pme C bx HownC with "Hown") as "Hown".
    iApply ("Hcont" $! E10 with "[%] [%] Hcg Hown Hpc").
    { (* callee_saved mm E10 *)
      unfold callee_saved. split_and!;
        first [ rewrite /E10 upd_eq; exact Hwv
              | peel_reg
              | (rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1 /E0;
                 repeat (rewrite upd_ne; [| reg_neq]);
                 apply Hcs; vm_compute; first [reflexivity | discriminate]) ]. }
    { (* a0 = rv *)
      rewrite /E10 upd_ne; [| reg_neq]. rewrite /E9 upd_ne; [| reg_neq].
      rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
      rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
      rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
      rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_ne; [| reg_neq].
      rewrite /E0 upd_eq. apply add_vec_zero_l. }
  Qed.

  (* ================================================================== *)
  (* +0xe8 .. +0xf6 -- the "no kids, or killed" exit.  Releases           *)
  (* wait_lock, puts -1 in s3 and jumps to the epilogue.                 *)
  (* ================================================================== *)
  Local Lemma kw_exit_wait `{GEN : GenId} `{CIDt : CpuId}
      (Φ : mval -> iProp Σ) (γw : gname) (mm Mt : regfile)
      (pme : mword 64) (K : nat) (eb : bool) (C : iProp Σ) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    (K_kwait <= K)%nat ->
    Mt !!! Regidx csp_rs1 = spr ->
    kw_cs_rest Mt mm ->
    sie_cap_gpr Mt (K - 10)%nat false pme -∗
    cpu_own 1 eb pme C false -∗
    arm_pay 0 eb pme -∗
    kernel_text -∗
    pc_is (mword_of_int (KW + 0xe8)) -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    locked γw CIDt -∗
    wait_res -∗
    kw_frame sp0 mm -∗
    wp_next eb pme (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜ callee_saved mm mf ⌝ -∗
        ⌜ mf !!! Regidx Ra0 = (mword_of_int (-1) : mword 64) ⌝ -∗
        sie_cap_gpr mf K eb pme -∗
        cpu_own 0 eb pme C eb -∗
        pc_is (ret_pc (mm !!! Regidx Rra)) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spr HK Hsp Hcs.
    iIntros "Hcg Hown Hpay #Htext Hpc #Hlk Htok Hres Hframe Hcont".
    iPoseProof (kwi_e8 with "Htext") as "Hie8".
    iPoseProof (kwi_ec with "Htext") as "Hiec".
    iPoseProof (kwi_f0 with "Htext") as "Hif0".
    iPoseProof (kwi_f4 with "Htext") as "Hif4".
    iPoseProof (kwi_f6 with "Htext") as "Hif6".
    (* +0xe8 auipc a0,0x10 *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KW + 0xe8)) Ra0 (mword_of_int 16 : mword 20)
              Mt (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hie8 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T0 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0xe8) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> Mt).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0xe8) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> Mt) with T0.
    assert (Hpec : add_vec_int (mword_of_int (KW + 0xe8) : mword 64) 4 = mword_of_int (KW + 0xec))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpec) in "Hpc".
    (* +0xec addi a0,a0,258 : a0 := &wait_lock *)
    assert (HrgT0 : rget (CID := CIDt) T0 Ra0 = T0 !!! Regidx Ra0) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KW + 0xec)) Ra0 Ra0 (mword_of_int 258 : mword 12)
              T0 (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiec [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HrgT0) in "Hcg".
    set (T1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (T0 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 258 : mword 12)))]> T0).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (T0 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 258 : mword 12)))]> T0) with T1.
    assert (HT1a0 : T1 !!! Regidx Ra0 = wait_lock_addr).
    { rewrite /T1 upd_eq /T0 upd_eq /wait_lock_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HT1sp : T1 !!! Regidx csp_rs1 = spr).
    { rewrite /T1 upd_ne; [| reg_neq]. rewrite /T0 upd_ne; [| reg_neq]. exact Hsp. }
    assert (HT1cs : kw_cs_rest T1 mm).
    { rewrite /T1. apply kw_cs_rest_ncs; [vm_compute; reflexivity |].
      rewrite /T0. apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact Hcs]. }
    assert (Hpf0 : add_vec_int (mword_of_int (KW + 0xec) : mword 64) 4 = mword_of_int (KW + 0xf0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpf0) in "Hpc".
    (* +0xf0 jal ra,release *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0xf0)) Rra
              (mword_of_int 2091562 : mword 21) T1 (K - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hif0 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (T2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0xf0) : mword 64) 4)]> T1).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0xf0) : mword 64) 4)]> T1) with T2.
    assert (Hjrel : add_vec (mword_of_int (KW + 0xf0) : mword 64)
                      (sign_extend' 64 (mword_of_int 2091562 : mword 21))
                    = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HT2ra : T2 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0xf0) : mword 64) 4)
      by (rewrite /T2 upd_eq; reflexivity).
    assert (HT2a0 : T2 !!! Regidx Ra0 = wait_lock_addr)
      by (rewrite /T2 upd_ne; [exact HT1a0 | reg_neq]).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = spr)
      by (rewrite /T2 upd_ne; [exact HT1sp | reg_neq]).
    assert (HT2cs : kw_cs_rest T2 mm)
      by (rewrite /T2; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HT1cs]).
    assert (Hlka : add_vec (T2 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = wait_lock_addr)
      by (rewrite HT2a0; apply addv_sext0).
    (* ---- release(&wait_lock): level 1 -> 0, so the exit index is [eb] ---- *)
    iApply (Release.wp_release_sconf Φ γw wait_lock_addr "wait_lock"%string
              wait_res T2 0%nat eb pme C (K - 10)%nat Hlka (kw_K10 K HK)
              with "Hcg Htext Hpc Hlk Htok Hres Hown Hpay [-]").
    iIntros (CIDr Hsr mr) "Hcg Hpc %Hcsr Hown".
    assert (Hpf4 : ret_pc (T2 !!! Regidx Rra) = mword_of_int (KW + 0xf4))
      by (rewrite HT2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpf4) in "Hpc".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HT2sp).
    assert (Hmrcs : kw_cs_rest mr mm) by (eapply kw_cs_rest_cs; [exact Hcsr | exact HT2cs]).
    (* +0xf4 c.li s3,-1 *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (KW + 0xf4)) Rs3 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) mr (K - 10)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hif4 [-]").
    iIntros (CIDs Hss) "Hcg Hpc".
    set (T3 := <[Regidx Rs3 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr).
    change (<[Regidx Rs3 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr) with T3.
    assert (HT3sp : T3 !!! Regidx csp_rs1 = spr)
      by (rewrite /T3 upd_ne; [exact Hmrsp | reg_neq]).
    assert (HT3s3 : T3 !!! Regidx Rs3 = (mword_of_int (-1) : mword 64))
      by (rewrite /T3 upd_eq; reflexivity).
    assert (HT3cs : kw_cs_rest T3 mm)
      by (rewrite /T3; apply kw_cs_rest_s3; exact Hmrcs).
    assert (Hpf6 : add_vec_int (mword_of_int (KW + 0xf4) : mword 64) 2 = mword_of_int (KW + 0xf6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpf6) in "Hpc".
    (* +0xf6 c.j +0x78 *)
    iApply (wp_cj_s_sconf Φ (mword_of_int (KW + 0xf6))
              (sign_extend' 21 (concat_vec (mword_of_int 1985 : mword 11) ('b"0")))
              T3 (K - 10)%nat eb ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hif6 [-]").
    iIntros (CIDj Hsj). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KW + 0xf6) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 1985 : mword 11) ('b"0"))))
                     = mword_of_int (KW + 0x78))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    (* ---- the epilogue ---- *)
    iDestruct (cpu_own_transport CIDr CIDj 0%nat eb pme C eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (kw_epilogue Φ mm T3 pme (mword_of_int (-1) : mword 64) K 0%nat eb eb C
              (kw_K10K K HK) HT3sp HT3s3 HT3cs with "Hcg Hown Htext Hpc Hframe [-]").
    iApply (kw_next_reanchor CIDt CIDj eb pme with "[Hcont]"); [wp_next_chain |].
    iExact "Hcont".
  Qed.

  (* ================================================================== *)
  (* +0x90 .. +0xa4 -- copyout FAILED: release the child's lock, then    *)
  (* wait_lock, return -1.  The only exit that unwinds two levels.       *)
  (* ================================================================== *)
  Local Lemma kw_exit_both `{GEN : GenId} `{CIDt : CpuId}
      (Φ : mval -> iProp Σ) (γs : list gname) (γw γk : gname)
      (mm Mt : regfile) (pme : mword 64) (k K : nat) (eb : bool) (C : iProp Σ) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    (K_kwait <= K)%nat ->
    Mt !!! Regidx csp_rs1 = spr ->
    Mt !!! Regidx Rs1 = proc_addr k ->
    kw_cs_rest Mt mm ->
    sie_cap_gpr Mt (K - 10)%nat false pme -∗
    cpu_own 2 eb pme C false -∗
    arm_pay 1 eb pme -∗
    arm_pay 0 eb pme -∗
    kernel_text -∗
    pc_is (mword_of_int (KW + 0x90)) -∗
    is_lock γk (proc_addr k) "proc"%string (proc_lock_res Φ γs γk (proc_addr k)) -∗
    locked γk CIDt -∗
    proc_lock_res Φ γs γk (proc_addr k) -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    locked γw CIDt -∗
    wait_res -∗
    kw_frame sp0 mm -∗
    wp_next eb pme (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜ callee_saved mm mf ⌝ -∗
        ⌜ mf !!! Regidx Ra0 = (mword_of_int (-1) : mword 64) ⌝ -∗
        sie_cap_gpr mf K eb pme -∗
        cpu_own 0 eb pme C eb -∗
        pc_is (ret_pc (mm !!! Regidx Rra)) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spr HK Hsp Hs1 Hcs.
    iIntros "Hcg Hown Hpay1 Hpay0 #Htext Hpc #Hlkk Htokk HRk #Hlk Htok Hres Hframe Hcont".
    iPoseProof (kwi_90 with "Htext") as "Hi90".
    iPoseProof (kwi_92 with "Htext") as "Hi92".
    iPoseProof (kwi_96 with "Htext") as "Hi96".
    iPoseProof (kwi_9a with "Htext") as "Hi9a".
    iPoseProof (kwi_9e with "Htext") as "Hi9e".
    iPoseProof (kwi_a2 with "Htext") as "Hia2".
    iPoseProof (kwi_a4 with "Htext") as "Hia4".
    (* +0x90 c.mv a0,s1 *)
    assert (Hrg90 : rget (CID := CIDt) Mt Rs1 = Mt !!! Regidx Rs1) by (rgne; reflexivity).
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0x90)) Ra0 Rs1
              Mt (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi90 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hrg90 Hs1) in "Hcg".
    set (U0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr k))]> Mt).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr k))]> Mt) with U0.
    assert (HU0a0 : U0 !!! Regidx Ra0 = proc_addr k)
      by (rewrite /U0 upd_eq; apply add_vec_zero_l).
    assert (HU0sp : U0 !!! Regidx csp_rs1 = spr)
      by (rewrite /U0 upd_ne; [exact Hsp | reg_neq]).
    assert (HU0cs : kw_cs_rest U0 mm)
      by (rewrite /U0; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact Hcs]).
    assert (Hp92 : add_vec_int (mword_of_int (KW + 0x90) : mword 64) 2 = mword_of_int (KW + 0x92))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp92) in "Hpc".
    (* +0x92 jal ra,release *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0x92)) Rra
              (mword_of_int 2091656 : mword 21) U0 (K - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi92 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (U1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x92) : mword 64) 4)]> U0).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x92) : mword 64) 4)]> U0) with U1.
    assert (Hjr1 : add_vec (mword_of_int (KW + 0x92) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091656 : mword 21))
                   = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjr1) in "Hpc".
    assert (HU1ra : U1 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0x92) : mword 64) 4)
      by (rewrite /U1 upd_eq; reflexivity).
    assert (HU1a0 : U1 !!! Regidx Ra0 = proc_addr k)
      by (rewrite /U1 upd_ne; [exact HU0a0 | reg_neq]).
    assert (HU1sp : U1 !!! Regidx csp_rs1 = spr)
      by (rewrite /U1 upd_ne; [exact HU0sp | reg_neq]).
    assert (HU1cs : kw_cs_rest U1 mm)
      by (rewrite /U1; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HU0cs]).
    assert (Hlkk : add_vec (U1 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr k)
      by (rewrite HU1a0; apply addv_sext0).
    (* ---- release(&pp->lock): level 2 -> 1, exit index still [false] ---- *)
    iApply (Release.wp_release_sconf Φ γk (proc_addr k) "proc"%string
              (proc_lock_res Φ γs γk (proc_addr k)) U1 1%nat eb pme C (K - 10)%nat
              Hlkk (kw_K10 K HK)
              with "Hcg Htext Hpc Hlkk Htokk HRk Hown Hpay1 [-]").
    (* the exit index of a release at level 1 is [false], so the hart is
       pinned: collapse the [wp_next] rather than introducing a new CID,
       which is what keeps [locked gw CIDt] usable at the SECOND release. *)
    iApply wp_next_off_intro. iIntros (mq) "Hcg Hpc %Hcsq Hown".
    assert (Hp96 : ret_pc (U1 !!! Regidx Rra) = mword_of_int (KW + 0x96))
      by (rewrite HU1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp96) in "Hpc".
    assert (Hmqsp : mq !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcsq csp_rs1 ltac:(vm_compute; reflexivity)); exact HU1sp).
    assert (Hmqcs : kw_cs_rest mq mm) by (eapply kw_cs_rest_cs; [exact Hcsq | exact HU1cs]).
    (* +0x96 auipc a0,0x10 *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KW + 0x96)) Ra0 (mword_of_int 16 : mword 20)
              mq (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi96 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (U2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0x96) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> mq).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0x96) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> mq) with U2.
    assert (Hp9a : add_vec_int (mword_of_int (KW + 0x96) : mword 64) 4 = mword_of_int (KW + 0x9a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp9a) in "Hpc".
    (* +0x9a addi a0,a0,340 : a0 := &wait_lock *)
    assert (HrgU2 : rget (CID := CIDt) U2 Ra0 = U2 !!! Regidx Ra0) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KW + 0x9a)) Ra0 Ra0 (mword_of_int 340 : mword 12)
              U2 (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi9a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HrgU2) in "Hcg".
    set (U3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (U2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 340 : mword 12)))]> U2).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (U2 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 340 : mword 12)))]> U2) with U3.
    assert (HU3a0 : U3 !!! Regidx Ra0 = wait_lock_addr).
    { rewrite /U3 upd_eq /U2 upd_eq /wait_lock_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HU3sp : U3 !!! Regidx csp_rs1 = spr).
    { rewrite /U3 upd_ne; [| reg_neq]. rewrite /U2 upd_ne; [| reg_neq]. exact Hmqsp. }
    assert (HU3cs : kw_cs_rest U3 mm).
    { rewrite /U3. apply kw_cs_rest_ncs; [vm_compute; reflexivity |].
      rewrite /U2. apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact Hmqcs]. }
    assert (Hp9e : add_vec_int (mword_of_int (KW + 0x9a) : mword 64) 4 = mword_of_int (KW + 0x9e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp9e) in "Hpc".
    (* +0x9e jal ra,release *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0x9e)) Rra
              (mword_of_int 2091644 : mword 21) U3 (K - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi9e [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (U4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x9e) : mword 64) 4)]> U3).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x9e) : mword 64) 4)]> U3) with U4.
    assert (Hjr2 : add_vec (mword_of_int (KW + 0x9e) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091644 : mword 21))
                   = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjr2) in "Hpc".
    assert (HU4ra : U4 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0x9e) : mword 64) 4)
      by (rewrite /U4 upd_eq; reflexivity).
    assert (HU4a0 : U4 !!! Regidx Ra0 = wait_lock_addr)
      by (rewrite /U4 upd_ne; [exact HU3a0 | reg_neq]).
    assert (HU4sp : U4 !!! Regidx csp_rs1 = spr)
      by (rewrite /U4 upd_ne; [exact HU3sp | reg_neq]).
    assert (HU4cs : kw_cs_rest U4 mm)
      by (rewrite /U4; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HU3cs]).
    assert (Hlkw : add_vec (U4 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = wait_lock_addr)
      by (rewrite HU4a0; apply addv_sext0).
    iApply (Release.wp_release_sconf Φ γw wait_lock_addr "wait_lock"%string
              wait_res U4 0%nat eb pme C (K - 10)%nat Hlkw (kw_K10 K HK)
              with "Hcg Htext Hpc Hlk Htok Hres Hown Hpay0 [-]").
    iIntros (CIDr2 Hsr2 mr) "Hcg Hpc %Hcsr Hown".
    assert (Hpa2 : ret_pc (U4 !!! Regidx Rra) = mword_of_int (KW + 0xa2))
      by (rewrite HU4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa2) in "Hpc".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HU4sp).
    assert (Hmrcs : kw_cs_rest mr mm) by (eapply kw_cs_rest_cs; [exact Hcsr | exact HU4cs]).
    (* +0xa2 c.li s3,-1 *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (KW + 0xa2)) Rs3 (mword_of_int 63 : mword 6)
              (mword_of_int (-1) : mword 64) mr (K - 10)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hia2 [-]").
    iIntros (CIDs Hss) "Hcg Hpc".
    set (U5 := <[Regidx Rs3 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr).
    change (<[Regidx Rs3 := regval_into_reg (mword_of_int (-1) : mword 64)]> mr) with U5.
    assert (HU5sp : U5 !!! Regidx csp_rs1 = spr)
      by (rewrite /U5 upd_ne; [exact Hmrsp | reg_neq]).
    assert (HU5s3 : U5 !!! Regidx Rs3 = (mword_of_int (-1) : mword 64))
      by (rewrite /U5 upd_eq; reflexivity).
    assert (HU5cs : kw_cs_rest U5 mm) by (rewrite /U5; apply kw_cs_rest_s3; exact Hmrcs).
    assert (Hpa4 : add_vec_int (mword_of_int (KW + 0xa2) : mword 64) 2 = mword_of_int (KW + 0xa4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa4) in "Hpc".
    (* +0xa4 c.j +0x78 *)
    iApply (wp_cj_s_sconf Φ (mword_of_int (KW + 0xa4))
              (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")))
              U5 (K - 10)%nat eb ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hia4 [-]").
    iIntros (CIDj Hsj). iNext. iIntros "Hcg Hpc".
    assert (Htgt78 : add_vec (mword_of_int (KW + 0xa4) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 2026 : mword 11) ('b"0"))))
                     = mword_of_int (KW + 0x78))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt78) in "Hpc".
    iDestruct (cpu_own_transport CIDr2 CIDj 0%nat eb pme C eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (kw_epilogue Φ mm U5 pme (mword_of_int (-1) : mword 64) K 0%nat eb eb C
              (kw_K10K K HK) HU5sp HU5s3 HU5cs with "Hcg Hown Htext Hpc Hframe [-]").
    iApply (kw_next_reanchor CIDt CIDj eb pme with "[Hcont]"); [wp_next_chain |].
    iExact "Hcont".
  Qed.

  (* ================================================================== *)
  (* +0x5c .. +0x74 -- REAPING THE CHILD, the join of the two arms of    *)
  (* the [addr != 0] test.  Disowns it ([pp->parent = 0], out of         *)
  (* wait_lock's table), frees it, and unwinds both locks.               *)
  (* ================================================================== *)
  Local Lemma kw_reap `{GEN : GenId} `{CIDp : CpuId}
      (Φ : mval -> iProp Σ) (γs : list gname) (γa γw γk : gname)
      (mm Mr : regfile) (pme : mword 64) (k K : nat) (eb : bool) (C : iProp Σ)
      (pidc : mword 32) (ch : mword 64) (ps : list (mword 64)) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    (K_kwait <= K)%nat ->
    (k < NPROC)%nat ->
    Mr !!! Regidx csp_rs1 = spr ->
    Mr !!! Regidx Rs1 = proc_addr k ->
    Mr !!! Regidx Rs3 = sign_extend' 64 pidc ->
    kw_cs_rest Mr mm ->
    sie_cap_gpr Mr (K - 10)%nat false pme -∗
    cpu_own 2 eb pme C false -∗
    arm_pay 1 eb pme -∗
    arm_pay 0 eb pme -∗
    kernel_text -∗
    pc_is (mword_of_int (KW + 0x5c)) -∗
    kalloc_env γa None -∗
    (* the child's lock, contents out, at ZOMBIE *)
    is_lock γk (proc_addr k) "proc"%string (proc_lock_res Φ γs γk (proc_addr k)) -∗
    locked γk CIDp -∗
    p_state (proc_addr k) ↦₄ ZOMBIE -∗
    (* ZOMBIE is unclaimed, so the caller's lock share is the whole mirror --
       which is what the [proc_held] freeproc wants needs. *)
    pstate_whole (proc_addr k) ZOMBIE -∗
    p_chan (proc_addr k) ↦₈ ch -∗
    proc_pub (proc_addr k) -∗
    proc_dormant (proc_addr k) ZOMBIE -∗
    park_at_full (proc_addr k) false -∗
    (* wait_lock, contents out *)
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    locked γw CIDp -∗
    parents_own ps -∗
    kw_frame sp0 mm -∗
    wp_next eb pme (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜ callee_saved mm mf ⌝ -∗
        ⌜ mf !!! Regidx Ra0 = sign_extend' 64 pidc ⌝ -∗
        sie_cap_gpr mf K eb pme -∗
        cpu_own 0 eb pme C eb -∗
        pc_is (ret_pc (mm !!! Regidx Rra)) -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spr HK Hk Hsp Hs1 Hs3 Hcs.
    iIntros "Hcg Hown Hpay1 Hpay0 #Htext Hpc #Henv #Hlkk Htokk Hstate Hpsg Hchan Hpub
             Hdorm Hpark #Hlk Htok Hps Hframe Hcont".
    iPoseProof (kwi_5c with "Htext") as "Hi5c".
    iPoseProof (kwi_60 with "Htext") as "Hi60".
    iPoseProof (kwi_62 with "Htext") as "Hi62".
    iPoseProof (kwi_66 with "Htext") as "Hi66".
    iPoseProof (kwi_68 with "Htext") as "Hi68".
    iPoseProof (kwi_6c with "Htext") as "Hi6c".
    iPoseProof (kwi_70 with "Htext") as "Hi70".
    iPoseProof (kwi_74 with "Htext") as "Hi74".
    (* ---- +0x5c sd x0,56(s1) : pp->parent = 0, out of wait_lock's table ---- *)
    iDestruct (parents_own_length ps with "Hps") as %Hlen.
    destruct (lookup_lt_is_Some_2 ps k ltac:(rewrite Hlen; exact Hk)) as [pv Hpv].
    iDestruct (parents_own_acc ps k pv Hpv with "Hps") as "[Hcell Hback]".
    iDestruct (sie_cap_gpr_x0 Mr (K - 10)%nat false pme (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; reflexivity) with "Hcg") as "[%Hx0 Hcg]".
    assert (Hea5c : add_vec (rget (CID := CIDp) Mr Rs1)
                      (sign_extend' 64 (mword_of_int 56 : mword 12)) = p_parent (proc_addr k)).
    { rewrite (rget_ne (CID := CIDp) Mr Rs1 ltac:(vm_compute; discriminate)) Hs1.
      apply kw_parent_off. }
    assert (Hsv5c : rget (CID := CIDp) Mr (mword_of_int 0 : mword 5) = (zero_reg : mword 64)).
    { rewrite (rget_ne (CID := CIDp) Mr (mword_of_int 0 : mword 5)
                 ltac:(vm_compute; discriminate)). exact Hx0. }
    iApply (wp_sd_s_sconf Φ (mword_of_int (KW + 0x5c)) (mword_of_int 0 : mword 5) Rs1
              (mword_of_int 56 : mword 12) Mr (K - 10)%nat pv false
              with "Hcg Hpc Hi5c [Hcell] [-]").
    { iEval (rewrite Hea5c). iExact "Hcell". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
    iEval (rewrite Hea5c Hsv5c) in "Hcell".
    iDestruct ("Hback" $! (zero_reg : mword 64) with "Hcell") as "Hps".
    assert (Hp60 : add_vec_int (mword_of_int (KW + 0x5c) : mword 64) 4 = mword_of_int (KW + 0x60))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    (* ---- +0x60 c.mv a0,s1 ---- *)
    assert (Hrg60 : rget (CID := CIDp) Mr Rs1 = Mr !!! Regidx Rs1) by (rgne; reflexivity).
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0x60)) Ra0 Rs1
              Mr (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hrg60 Hs1) in "Hcg".
    set (R0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr k))]> Mr).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr k))]> Mr) with R0.
    assert (HR0a0 : R0 !!! Regidx Ra0 = proc_addr k)
      by (rewrite /R0 upd_eq; apply add_vec_zero_l).
    assert (HR0sp : R0 !!! Regidx csp_rs1 = spr) by (rewrite /R0 upd_ne; [exact Hsp | reg_neq]).
    assert (HR0s1 : R0 !!! Regidx Rs1 = proc_addr k) by (rewrite /R0 upd_ne; [exact Hs1 | reg_neq]).
    assert (HR0s3 : R0 !!! Regidx Rs3 = sign_extend' 64 pidc)
      by (rewrite /R0 upd_ne; [exact Hs3 | reg_neq]).
    assert (HR0cs : kw_cs_rest R0 mm)
      by (rewrite /R0; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact Hcs]).
    assert (Hp62 : add_vec_int (mword_of_int (KW + 0x60) : mword 64) 2 = mword_of_int (KW + 0x62))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp62) in "Hpc".
    (* ---- +0x62 jal ra,freeproc ---- *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0x62)) Rra
              (mword_of_int 2095374 : mword 21) R0 (K - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi62 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x62) : mword 64) 4)]> R0).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x62) : mword 64) 4)]> R0) with R1.
    assert (Hjfp : add_vec (mword_of_int (KW + 0x62) : mword 64)
                     (sign_extend' 64 (mword_of_int 2095374 : mword 21))
                   = mword_of_int KernelSyms.freeproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjfp) in "Hpc".
    assert (HR1ra : R1 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0x62) : mword 64) 4)
      by (rewrite /R1 upd_eq; reflexivity).
    assert (HR1a0 : R1 !!! Regidx Ra0 = proc_addr k)
      by (rewrite /R1 upd_ne; [exact HR0a0 | reg_neq]).
    assert (HR1sp : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_ne; [exact HR0sp | reg_neq]).
    assert (HR1s1 : R1 !!! Regidx Rs1 = proc_addr k) by (rewrite /R1 upd_ne; [exact HR0s1 | reg_neq]).
    assert (HR1s3 : R1 !!! Regidx Rs3 = sign_extend' 64 pidc)
      by (rewrite /R1 upd_ne; [exact HR0s3 | reg_neq]).
    assert (HR1cs : kw_cs_rest R1 mm)
      by (rewrite /R1; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HR0cs]).
    (* the ZOMBIE block, in freeproc's own vocabulary *)
    iDestruct (fp_of_dormant_zombie (proc_addr k) with "Hdorm")
      as (Vc pidz) "(Hrest & Hpt & Htf)".
    iDestruct (park_at_full_elim k false Hk with "Hpark") as "Hpark".
    rewrite park_split. iDestruct "Hpark" as "[Hparka Hparkb]".
    iApply (Freeproc.wp_freeproc_sconf γa Φ R1 k γk Vc pidz ZOMBIE ch
              (Some (pv_upt Vc)) (Some (ud_tfp (pv_upt Vc), pv_tf Vc))
              (K - 10)%nat eb pme C 2%nat
              (kw_K44 K HK) kw_ilvl2 HR1a0
              with "Hcg Hown Htext Hpc [Htokk Hstate Hpsg Hchan Hpub Hparka] Hrest Hpt Htf Henv [-]").
    { rewrite /proc_held. iFrame "Htokk Hstate Hpsg Hchan Hpub Hparka". }
    iApply wp_next_off_intro.
    iIntros (mfp) "Hcg Hown Hpc %Hcsfp Hheld Hdorm".
    assert (Hp66 : ret_pc (R1 !!! Regidx Rra) = mword_of_int (KW + 0x66))
      by (rewrite HR1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    assert (Hfpsp : mfp !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcsfp csp_rs1 ltac:(vm_compute; reflexivity)); exact HR1sp).
    assert (Hfps1 : mfp !!! Regidx Rs1 = proc_addr k)
      by (rewrite (callee_saved_lookup Hcsfp Rs1 ltac:(vm_compute; reflexivity)); exact HR1s1).
    assert (Hfps3 : mfp !!! Regidx Rs3 = sign_extend' 64 pidc)
      by (rewrite (callee_saved_lookup Hcsfp Rs3 ltac:(vm_compute; reflexivity)); exact HR1s3).
    assert (Hfpcs : kw_cs_rest mfp mm) by (eapply kw_cs_rest_cs; [exact Hcsfp | exact HR1cs]).
    (* ---- +0x66 c.mv a0,s1 ---- *)
    assert (Hrg66 : rget (CID := CIDp) mfp Rs1 = mfp !!! Regidx Rs1) by (rgne; reflexivity).
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0x66)) Ra0 Rs1
              mfp (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi66 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hrg66 Hfps1) in "Hcg".
    set (R2 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr k))]> mfp).
    change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr k))]> mfp) with R2.
    assert (HR2a0 : R2 !!! Regidx Ra0 = proc_addr k)
      by (rewrite /R2 upd_eq; apply add_vec_zero_l).
    assert (HR2sp : R2 !!! Regidx csp_rs1 = spr) by (rewrite /R2 upd_ne; [exact Hfpsp | reg_neq]).
    assert (HR2s3 : R2 !!! Regidx Rs3 = sign_extend' 64 pidc)
      by (rewrite /R2 upd_ne; [exact Hfps3 | reg_neq]).
    assert (HR2cs : kw_cs_rest R2 mm)
      by (rewrite /R2; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact Hfpcs]).
    assert (Hp68 : add_vec_int (mword_of_int (KW + 0x66) : mword 64) 2 = mword_of_int (KW + 0x68))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp68) in "Hpc".
    (* ---- +0x68 jal ra,release : the child's lock ---- *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0x68)) Rra
              (mword_of_int 2091698 : mword 21) R2 (K - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi68 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x68) : mword 64) 4)]> R2).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x68) : mword 64) 4)]> R2) with R3.
    assert (Hjr1 : add_vec (mword_of_int (KW + 0x68) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091698 : mword 21))
                   = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjr1) in "Hpc".
    assert (HR3ra : R3 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0x68) : mword 64) 4)
      by (rewrite /R3 upd_eq; reflexivity).
    assert (HR3a0 : R3 !!! Regidx Ra0 = proc_addr k)
      by (rewrite /R3 upd_ne; [exact HR2a0 | reg_neq]).
    assert (HR3sp : R3 !!! Regidx csp_rs1 = spr) by (rewrite /R3 upd_ne; [exact HR2sp | reg_neq]).
    assert (HR3s3 : R3 !!! Regidx Rs3 = sign_extend' 64 pidc)
      by (rewrite /R3 upd_ne; [exact HR2s3 | reg_neq]).
    assert (HR3cs : kw_cs_rest R3 mm)
      by (rewrite /R3; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HR2cs]).
    assert (Hlkk2 : add_vec (R3 !!! Regidx Ra0)
                      (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr k)
      by (rewrite HR3a0; apply addv_sext0).
    (* the emptied slot goes back into the lock at UNUSED; the park receipt
       rejoins from the half freeproc handed back inside [proc_held]. *)
    iDestruct "Hheld" as "(Htokk & Hstate & Hpsg & Hchan & Hpub & Hparkc)".
    iAssert (park_at_full (proc_addr k) false) with "[Hparkb Hparkc]" as "Hpark".
    { iApply (park_at_full_intro k false Hk). rewrite park_split. iFrame "Hparkb Hparkc". }
    (* UNUSED is unclaimed, so the whole mirror freeproc handed back becomes
       the lock's share again. *)
    iDestruct (pstate_whole_split (proc_addr k) UNUSED) as "[Hwu _]".
    iDestruct ("Hwu" with "Hpsg") as "[Hpsg _]".
    iAssert (proc_lock_res Φ γs γk (proc_addr k)) with "[Hstate Hpsg Hchan Hpub Hdorm Hpark]" as "HRk".
    { iApply (proc_lock_res_intro Φ γs γk (proc_addr k) UNUSED (zero_reg : mword 64)
                with "Hstate Hpsg Hchan Hpub [Hdorm Hpark]").
      iApply (proc_slots_unused_intro Φ γs (proc_addr k) with "Hdorm Hpark"). }
    iApply (Release.wp_release_sconf Φ γk (proc_addr k) "proc"%string
              (proc_lock_res Φ γs γk (proc_addr k)) R3 1%nat eb pme C (K - 10)%nat
              Hlkk2 (kw_K10 K HK)
              with "Hcg Htext Hpc Hlkk Htokk HRk Hown Hpay1 [-]").
    (* level 1 -> 1: pinned hart, so collapse rather than re-anchor *)
    iApply wp_next_off_intro. iIntros (mq) "Hcg Hpc %Hcsq Hown".
    assert (Hp6c : ret_pc (R3 !!! Regidx Rra) = mword_of_int (KW + 0x6c))
      by (rewrite HR3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6c) in "Hpc".
    assert (Hmqsp : mq !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcsq csp_rs1 ltac:(vm_compute; reflexivity)); exact HR3sp).
    assert (Hmqs3 : mq !!! Regidx Rs3 = sign_extend' 64 pidc)
      by (rewrite (callee_saved_lookup Hcsq Rs3 ltac:(vm_compute; reflexivity)); exact HR3s3).
    assert (Hmqcs : kw_cs_rest mq mm) by (eapply kw_cs_rest_cs; [exact Hcsq | exact HR3cs]).
    (* ---- +0x6c auipc a0,0x10 ---- *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KW + 0x6c)) Ra0 (mword_of_int 16 : mword 20)
              mq (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6c [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0x6c) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> mq).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0x6c) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> mq) with R4.
    assert (Hp70 : add_vec_int (mword_of_int (KW + 0x6c) : mword 64) 4 = mword_of_int (KW + 0x70))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp70) in "Hpc".
    (* ---- +0x70 addi a0,a0,382 : a0 := &wait_lock ---- *)
    assert (HrgR4 : rget (CID := CIDp) R4 Ra0 = R4 !!! Regidx Ra0) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KW + 0x70)) Ra0 Ra0 (mword_of_int 382 : mword 12)
              R4 (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi70 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite HrgR4) in "Hcg".
    set (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (R4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 382 : mword 12)))]> R4).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (R4 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 382 : mword 12)))]> R4) with R5.
    assert (HR5a0 : R5 !!! Regidx Ra0 = wait_lock_addr).
    { rewrite /R5 upd_eq /R4 upd_eq /wait_lock_addr. apply bv_eq; vm_compute; reflexivity. }
    assert (HR5sp : R5 !!! Regidx csp_rs1 = spr).
    { rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq]. exact Hmqsp. }
    assert (HR5s3 : R5 !!! Regidx Rs3 = sign_extend' 64 pidc).
    { rewrite /R5 upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq]. exact Hmqs3. }
    assert (HR5cs : kw_cs_rest R5 mm).
    { rewrite /R5. apply kw_cs_rest_ncs; [vm_compute; reflexivity |].
      rewrite /R4. apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact Hmqcs]. }
    assert (Hp74 : add_vec_int (mword_of_int (KW + 0x70) : mword 64) 4 = mword_of_int (KW + 0x74))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp74) in "Hpc".
    (* ---- +0x74 jal ra,release : wait_lock, level 1 -> 0 ---- *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0x74)) Rra
              (mword_of_int 2091686 : mword 21) R5 (K - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi74 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (R6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x74) : mword 64) 4)]> R5).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x74) : mword 64) 4)]> R5) with R6.
    assert (Hjr2 : add_vec (mword_of_int (KW + 0x74) : mword 64)
                     (sign_extend' 64 (mword_of_int 2091686 : mword 21))
                   = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjr2) in "Hpc".
    assert (HR6ra : R6 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0x74) : mword 64) 4)
      by (rewrite /R6 upd_eq; reflexivity).
    assert (HR6a0 : R6 !!! Regidx Ra0 = wait_lock_addr)
      by (rewrite /R6 upd_ne; [exact HR5a0 | reg_neq]).
    assert (HR6sp : R6 !!! Regidx csp_rs1 = spr) by (rewrite /R6 upd_ne; [exact HR5sp | reg_neq]).
    assert (HR6s3 : R6 !!! Regidx Rs3 = sign_extend' 64 pidc)
      by (rewrite /R6 upd_ne; [exact HR5s3 | reg_neq]).
    assert (HR6cs : kw_cs_rest R6 mm)
      by (rewrite /R6; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HR5cs]).
    assert (Hlkw : add_vec (R6 !!! Regidx Ra0)
                     (sign_extend' 64 (mword_of_int 0 : mword 12)) = wait_lock_addr)
      by (rewrite HR6a0; apply addv_sext0).
    iApply (Release.wp_release_sconf Φ γw wait_lock_addr "wait_lock"%string
              wait_res R6 0%nat eb pme C (K - 10)%nat Hlkw (kw_K10 K HK)
              with "Hcg Htext Hpc Hlk Htok [Hps] Hown Hpay0 [-]").
    { iExists (<[k := (zero_reg : mword 64)]> ps). iExact "Hps". }
    iIntros (CIDr2 Hsr2 mr) "Hcg Hpc %Hcsr Hown".
    assert (Hp78 : ret_pc (R6 !!! Regidx Rra) = mword_of_int (KW + 0x78))
      by (rewrite HR6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp78) in "Hpc".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcsr csp_rs1 ltac:(vm_compute; reflexivity)); exact HR6sp).
    assert (Hmrs3 : mr !!! Regidx Rs3 = sign_extend' 64 pidc)
      by (rewrite (callee_saved_lookup Hcsr Rs3 ltac:(vm_compute; reflexivity)); exact HR6s3).
    assert (Hmrcs : kw_cs_rest mr mm) by (eapply kw_cs_rest_cs; [exact Hcsr | exact HR6cs]).
    (* ---- fall through into the epilogue ---- *)
    iApply (kw_epilogue Φ mm mr pme (sign_extend' 64 pidc) K 0%nat eb eb C
              (kw_K10K K HK) Hmrsp Hmrs3 Hmrcs with "Hcg Hown Htext Hpc Hframe [-]").
    iApply (kw_next_reanchor CIDp CIDr2 eb pme with "[Hcont]"); [wp_next_chain |].
    iExact "Hcont".
  Qed.

  (* ================================================================== *)
  (* +0x40 .. +0x58 -- THE FOUND ARM: read the child's pid, optionally   *)
  (* copy its exit status out, then reap it.                             *)
  (*                                                                     *)
  (* The [addr != 0] test's two arms JOIN at +0x5c, which is why the     *)
  (* reaping tail is its own lemma ([kw_reap]) rather than duplicated:   *)
  (* the arms differ only in whether the user page table grew.           *)
  (* ================================================================== *)
  Local Lemma kw_found `{GEN : GenId} `{CIDf : CpuId}
      (Φ : mval -> iProp Σ) (γs : list gname) (γa γf γw γk : gname)
      (mm Mf : regfile) (pme : mword 64) (k K : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (ch : mword 64) (ps : list (mword 64)) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    (K_kwait <= K)%nat ->
    (k < NPROC)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx Rs1 = proc_addr k ->
    Mf !!! Regidx Rs2 = pme ->
    kw_cs_rest Mf mm ->
    sie_cap_gpr Mf (K - 10)%nat false pme -∗
    cpu_own 2 eb pme C false -∗
    arm_pay 1 eb pme -∗
    arm_pay 0 eb pme -∗
    kernel_text -∗
    pc_is (mword_of_int (KW + 0x40)) -∗
    kalloc_env γa None -∗
    is_lock γk (proc_addr k) "proc"%string (proc_lock_res Φ γs γk (proc_addr k)) -∗
    locked γk CIDf -∗
    p_state (proc_addr k) ↦₄ ZOMBIE -∗
    (* the whole mirror: ZOMBIE is unclaimed, so the lock's share is both
       halves, and [kw_reap] hands it on to freeproc's [proc_held]. *)
    pstate_whole (proc_addr k) ZOMBIE -∗
    p_chan (proc_addr k) ↦₈ ch -∗
    proc_pub (proc_addr k) -∗
    proc_dormant (proc_addr k) ZOMBIE -∗
    park_at_full (proc_addr k) false -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    locked γw CIDf -∗
    parents_own ps -∗
    proc_priv γf pme pid V -∗
    kw_frame sp0 mm -∗
    wp_next eb pme (fun (CID : CpuId) =>
      ∀ (mf : regfile) (P' : uptd) (rv : mword 32),
        ⌜ callee_saved mm mf ⌝ -∗
        ⌜ mf !!! Regidx Ra0 = sign_extend' 64 rv ⌝ -∗
        ⌜ uptd_ext_sz (pv_sz V) (pv_upt V) P' ⌝ -∗
        sie_cap_gpr mf K eb pme -∗
        cpu_own 0 eb pme C eb -∗
        pc_is (ret_pc (mm !!! Regidx Rra)) -∗
        proc_priv γf pme pid (upd_upt V P') -∗
        WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spr HK Hk Hsp Hs1 Hs2 Hcs.
    iIntros "Hcg Hown Hpay1 Hpay0 #Htext Hpc #Henv #Hlkk Htokk Hstate Hpsg Hchan Hpub
             Hdorm Hpark #Hlk Htok Hps Hpriv Hframe Hcont".
    iPoseProof (kwi_40 with "Htext") as "Hi40".
    iPoseProof (kwi_44 with "Htext") as "Hi44".
    iPoseProof (kwi_48 with "Htext") as "Hi48".
    iPoseProof (kwi_4a with "Htext") as "Hi4a".
    iPoseProof (kwi_4e with "Htext") as "Hi4e".
    iPoseProof (kwi_50 with "Htext") as "Hi50".
    iPoseProof (kwi_54 with "Htext") as "Hi54".
    iPoseProof (kwi_58 with "Htext") as "Hi58".
    iDestruct "Hpub" as (kl xs pidc) "(Hkilled & Hxstate & Hpidhalf)".
    (* ---- +0x40 lw s3,48(s1) : pid = pp->pid ---- *)
    assert (Hea40 : add_vec (rget (CID := CIDf) Mf Rs1)
                      (sign_extend' 64 (mword_of_int 48 : mword 12)) = p_pid (proc_addr k)).
    { rewrite (rget_ne (CID := CIDf) Mf Rs1 ltac:(vm_compute; discriminate)) Hs1.
      apply kw_pid_off. }
    iApply (wp_lw_s_sconf Φ (mword_of_int (KW + 0x40)) Rs3 Rs1
              (mword_of_int 48 : mword 12) Mf (K - 10)%nat pidc false
              (dqm := DfracOwn (1/2))
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 [Hpidhalf] [-]").
    { iEval (rewrite Hea40). iExact "Hpidhalf". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hpidhalf".
    iEval (rewrite Hea40) in "Hpidhalf".
    set (F0 := <[Regidx Rs3 := regval_into_reg (sign_extend' 64 pidc)]> Mf).
    change (<[Regidx Rs3 := regval_into_reg (sign_extend' 64 pidc)]> Mf) with F0.
    assert (HF0s3 : F0 !!! Regidx Rs3 = sign_extend' 64 pidc) by (rewrite /F0 upd_eq; reflexivity).
    assert (HF0sp : F0 !!! Regidx csp_rs1 = spr) by (rewrite /F0 upd_ne; [exact Hsp | reg_neq]).
    assert (HF0s1 : F0 !!! Regidx Rs1 = proc_addr k) by (rewrite /F0 upd_ne; [exact Hs1 | reg_neq]).
    assert (HF0s2 : F0 !!! Regidx Rs2 = pme) by (rewrite /F0 upd_ne; [exact Hs2 | reg_neq]).
    assert (HF0cs : kw_cs_rest F0 mm) by (rewrite /F0; apply kw_cs_rest_s3; exact Hcs).
    assert (Hp44 : add_vec_int (mword_of_int (KW + 0x40) : mword 64) 4 = mword_of_int (KW + 0x44))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp44) in "Hpc".
    (* [proc_pub] is re-bundled per ARM: the null-[addr] arm never opens it
       again, while the copyout arm has to keep [p_xstate] out as the source
       buffer until copyout hands it back. *)
    (* ---- +0x44 beq s7,x0 -> +0x5c : is [addr] null? ---- *)
    destruct (eq_vec (rget (CID := CIDf) F0 Rs7) (zero_reg : mword 64)) eqn:Hz.
    - (* ===== addr == 0: no copyout, straight to the reaping tail ===== *)
      iApply (wp_beqz_x0_taken_s_sconf Φ (mword_of_int (KW + 0x44))
                (mword_of_int 24 : mword 13) Rs7 F0 (K - 10)%nat false
                ltac:(vm_compute; discriminate) Hz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi44 [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt5c : add_vec (mword_of_int (KW + 0x44) : mword 64)
                         (sign_extend' 64 (mword_of_int 24 : mword 13))
                       = mword_of_int (KW + 0x5c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt5c) in "Hpc".
      iAssert (proc_pub (proc_addr k)) with "[Hkilled Hxstate Hpidhalf]" as "Hpub".
      { iExists kl, xs, pidc. iFrame "Hkilled Hxstate Hpidhalf". }
      iApply (kw_reap Φ γs γa γw γk mm F0 pme k K eb C pidc ch ps
                HK Hk HF0sp HF0s1 HF0s3 HF0cs
                with "Hcg Hown Hpay1 Hpay0 Htext Hpc Henv Hlkk Htokk Hstate Hpsg Hchan
                      Hpub Hdorm Hpark Hlk Htok Hps Hframe [Hcont Hpriv]").
      iIntros (CIDz) "%Hsz". iIntros (mf) "%Hcsf %Ha0 Hcg Hown Hpc".
      iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf (pv_upt V) pidc with "[%] [%] [%] Hcg Hown Hpc [Hpriv]").
      { exact Hcsf. }
      { exact Ha0. }
      { apply uptd_ext_sz_refl. }
      { rewrite upd_upt_id. iExact "Hpriv". }
    - (* ===== addr != 0: copyout(p->pagetable, addr, &pp->xstate, 4) ===== *)
      iApply (wp_beqz_x0_fall_s_sconf Φ (mword_of_int (KW + 0x44))
                (mword_of_int 24 : mword 13) Rs7 F0 (K - 10)%nat false
                ltac:(vm_compute; discriminate) Hz
                with "Hcg Hpc Hi44 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hp48 : add_vec_int (mword_of_int (KW + 0x44) : mword 64) 4 = mword_of_int (KW + 0x48))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp48) in "Hpc".
      (* +0x48 c.li a3,4 *)
      iApply (wp_cli_s_sconf Φ (mword_of_int (KW + 0x48)) Ra3 (mword_of_int 4 : mword 6)
                (mword_of_int 4 : mword 64) F0 (K - 10)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi48 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (F1 := <[Regidx Ra3 := regval_into_reg (mword_of_int 4 : mword 64)]> F0).
      change (<[Regidx Ra3 := regval_into_reg (mword_of_int 4 : mword 64)]> F0) with F1.
      assert (HF1a3 : F1 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
        by (rewrite /F1 upd_eq; reflexivity).
      assert (HF1sp : F1 !!! Regidx csp_rs1 = spr) by (rewrite /F1 upd_ne; [exact HF0sp | reg_neq]).
      assert (HF1s1 : F1 !!! Regidx Rs1 = proc_addr k) by (rewrite /F1 upd_ne; [exact HF0s1 | reg_neq]).
      assert (HF1s2 : F1 !!! Regidx Rs2 = pme) by (rewrite /F1 upd_ne; [exact HF0s2 | reg_neq]).
      assert (HF1s3 : F1 !!! Regidx Rs3 = sign_extend' 64 pidc)
        by (rewrite /F1 upd_ne; [exact HF0s3 | reg_neq]).
      assert (HF1cs : kw_cs_rest F1 mm)
        by (rewrite /F1; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HF0cs]).
      assert (Hp4a : add_vec_int (mword_of_int (KW + 0x48) : mword 64) 2 = mword_of_int (KW + 0x4a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4a) in "Hpc".
      (* +0x4a addi a2,s1,44 : a2 := &pp->xstate *)
      assert (Hea4a : add_vec (rget (CID := CIDf) F1 Rs1)
                        (sign_extend' 64 (mword_of_int 44 : mword 12)) = p_xstate (proc_addr k)).
      { rewrite (rget_ne (CID := CIDf) F1 Rs1 ltac:(vm_compute; discriminate)) HF1s1.
        apply kw_xstate_off. }
      iApply (wp_addi4_s_sconf Φ (mword_of_int (KW + 0x4a)) Ra2 Rs1 (mword_of_int 44 : mword 12)
                F1 (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi4a [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rewrite Hea4a) in "Hcg".
      set (F2 := <[Regidx Ra2 := regval_into_reg (p_xstate (proc_addr k))]> F1).
      change (<[Regidx Ra2 := regval_into_reg (p_xstate (proc_addr k))]> F1) with F2.
      assert (HF2a2 : F2 !!! Regidx Ra2 = p_xstate (proc_addr k))
        by (rewrite /F2 upd_eq; reflexivity).
      assert (HF2a3 : F2 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
        by (rewrite /F2 upd_ne; [exact HF1a3 | reg_neq]).
      assert (HF2sp : F2 !!! Regidx csp_rs1 = spr) by (rewrite /F2 upd_ne; [exact HF1sp | reg_neq]).
      assert (HF2s1 : F2 !!! Regidx Rs1 = proc_addr k) by (rewrite /F2 upd_ne; [exact HF1s1 | reg_neq]).
      assert (HF2s2 : F2 !!! Regidx Rs2 = pme) by (rewrite /F2 upd_ne; [exact HF1s2 | reg_neq]).
      assert (HF2s3 : F2 !!! Regidx Rs3 = sign_extend' 64 pidc)
        by (rewrite /F2 upd_ne; [exact HF1s3 | reg_neq]).
      assert (HF2cs : kw_cs_rest F2 mm)
        by (rewrite /F2; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HF1cs]).
      assert (Hp4e : add_vec_int (mword_of_int (KW + 0x4a) : mword 64) 4 = mword_of_int (KW + 0x4e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4e) in "Hpc".
      (* +0x4e c.mv a1,s7 : a1 := addr *)
      assert (Hrg4e : rget (CID := CIDf) F2 Rs7 = F2 !!! Regidx Rs7) by (rgne; reflexivity).
      iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0x4e)) Ra1 Rs7
                F2 (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi4e [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rewrite Hrg4e) in "Hcg".
      set (F3 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (F2 !!! Regidx Rs7))]> F2).
      change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg (F2 !!! Regidx Rs7))]> F2) with F3.
      assert (HF3a2 : F3 !!! Regidx Ra2 = p_xstate (proc_addr k))
        by (rewrite /F3 upd_ne; [exact HF2a2 | reg_neq]).
      assert (HF3a3 : F3 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
        by (rewrite /F3 upd_ne; [exact HF2a3 | reg_neq]).
      assert (HF3sp : F3 !!! Regidx csp_rs1 = spr) by (rewrite /F3 upd_ne; [exact HF2sp | reg_neq]).
      assert (HF3s1 : F3 !!! Regidx Rs1 = proc_addr k) by (rewrite /F3 upd_ne; [exact HF2s1 | reg_neq]).
      assert (HF3s2 : F3 !!! Regidx Rs2 = pme) by (rewrite /F3 upd_ne; [exact HF2s2 | reg_neq]).
      assert (HF3s3 : F3 !!! Regidx Rs3 = sign_extend' 64 pidc)
        by (rewrite /F3 upd_ne; [exact HF2s3 | reg_neq]).
      assert (HF3cs : kw_cs_rest F3 mm)
        by (rewrite /F3; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HF2cs]).
      assert (Hp50 : add_vec_int (mword_of_int (KW + 0x4e) : mword 64) 2 = mword_of_int (KW + 0x50))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp50) in "Hpc".
      (* the caller's own address space, opened for copyout *)
      iDestruct (proc_priv_sz_bound γf pme pid V with "Hpriv") as %Hszb.
      iDestruct (proc_priv_copy γf pme pid V with "Hpriv") as "(Hsz & Hpg & Hpt & Hback)".
      (* +0x50 ld a0,80(s2) : a0 := p->pagetable *)
      assert (Hea50 : add_vec (rget (CID := CIDf) F3 Rs2)
                        (sign_extend' 64 (mword_of_int 80 : mword 12)) = p_pagetable pme).
      { rewrite (rget_ne (CID := CIDf) F3 Rs2 ltac:(vm_compute; discriminate)) HF3s2.
        apply kw_pagetable_off. }
      iApply (wp_ld_s_sconf Φ (mword_of_int (KW + 0x50)) Ra0 Rs2 (mword_of_int 80 : mword 12)
                F3 (K - 10)%nat (page_base (ud_root (pv_upt V))) false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi50 [Hpg] [-]").
      { iEval (rewrite Hea50). iExact "Hpg". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hpg".
      iEval (rewrite Hea50) in "Hpg".
      set (F4 := <[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> F3).
      change (<[Regidx Ra0 := regval_into_reg (page_base (ud_root (pv_upt V)))]> F3) with F4.
      assert (HF4a0 : F4 !!! Regidx Ra0 = page_base (ud_root (pv_upt V)))
        by (rewrite /F4 upd_eq; reflexivity).
      assert (HF4a2 : F4 !!! Regidx Ra2 = p_xstate (proc_addr k))
        by (rewrite /F4 upd_ne; [exact HF3a2 | reg_neq]).
      assert (HF4a3 : F4 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
        by (rewrite /F4 upd_ne; [exact HF3a3 | reg_neq]).
      assert (HF4sp : F4 !!! Regidx csp_rs1 = spr) by (rewrite /F4 upd_ne; [exact HF3sp | reg_neq]).
      assert (HF4s1 : F4 !!! Regidx Rs1 = proc_addr k) by (rewrite /F4 upd_ne; [exact HF3s1 | reg_neq]).
      assert (HF4s2 : F4 !!! Regidx Rs2 = pme) by (rewrite /F4 upd_ne; [exact HF3s2 | reg_neq]).
      assert (HF4s3 : F4 !!! Regidx Rs3 = sign_extend' 64 pidc)
        by (rewrite /F4 upd_ne; [exact HF3s3 | reg_neq]).
      assert (HF4cs : kw_cs_rest F4 mm)
        by (rewrite /F4; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HF3cs]).
      assert (Hp54 : add_vec_int (mword_of_int (KW + 0x50) : mword 64) 4 = mword_of_int (KW + 0x54))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp54) in "Hpc".
      (* +0x54 jal ra,copyout *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0x54)) Rra
                (mword_of_int 2094172 : mword 21) F4 (K - 10)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi54 [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (F5 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KW + 0x54) : mword 64) 4)]> F4).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KW + 0x54) : mword 64) 4)]> F4) with F5.
      assert (Hjco : add_vec (mword_of_int (KW + 0x54) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094172 : mword 21))
                     = mword_of_int KernelSyms.copyout)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjco) in "Hpc".
      assert (HF5ra : F5 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0x54) : mword 64) 4)
        by (rewrite /F5 upd_eq; reflexivity).
      assert (HF5a0 : F5 !!! Regidx Ra0 = page_base (ud_root (pv_upt V)))
        by (rewrite /F5 upd_ne; [exact HF4a0 | reg_neq]).
      assert (HF5a2 : F5 !!! Regidx Ra2 = p_xstate (proc_addr k))
        by (rewrite /F5 upd_ne; [exact HF4a2 | reg_neq]).
      assert (HF5a3 : F5 !!! Regidx Ra3 = (mword_of_int 4 : mword 64))
        by (rewrite /F5 upd_ne; [exact HF4a3 | reg_neq]).
      assert (HF5sp : F5 !!! Regidx csp_rs1 = spr) by (rewrite /F5 upd_ne; [exact HF4sp | reg_neq]).
      assert (HF5s1 : F5 !!! Regidx Rs1 = proc_addr k) by (rewrite /F5 upd_ne; [exact HF4s1 | reg_neq]).
      assert (HF5s3 : F5 !!! Regidx Rs3 = sign_extend' 64 pidc)
        by (rewrite /F5 upd_ne; [exact HF4s3 | reg_neq]).
      assert (HF5cs : kw_cs_rest F5 mm)
        by (rewrite /F5; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HF4cs]).
      (* the four source bytes: the child's [xstate] cell, as a byte buffer *)
      (* the alignment fact has to come out BEFORE the split: the four bytes
         no longer carry it, and the rebuild needs it (durable-notes). *)
      iDestruct (word4_pointsto_aligned_p (p_xstate (proc_addr k)) (DfracOwn 1) xs
                   with "Hxstate") as %Halx.
      iDestruct (word4_pointsto_bytes (p_xstate (proc_addr k)) (DfracOwn 1) xs
                   with "Hxstate") as "Hbytes".
      iApply (Copyout.wp_copyout_sconf γa Φ F5 (pv_upt V) (pv_sz V) 4%nat
                (fun i => nth_byte xs i) (K - 10)%nat 2%nat eb pme C
                (DfracOwn 1) (DfracOwn 1) false
                (kw_K50 K HK) HF5a0 ltac:(rewrite HF5a3; apply bv_eq; vm_compute; reflexivity)
                kw_len4 Hszb kw_ilvl2
                with "Hcg Hown Htext Hpc Hsz Hpg Hpt Henv [Hbytes] [-]").
      { iEval (rewrite HF5a2). iExact "Hbytes". }
      iApply wp_next_off_intro.
      iIntros (mco P') "Hcg Hown Hpc Hsz Hpg Hpt Hbytes %Hcsco %Hext %Hrv".
      assert (Hp58 : ret_pc (F5 !!! Regidx Rra) = mword_of_int (KW + 0x58))
        by (rewrite HF5ra; apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp58) in "Hpc".
      iEval (rewrite HF5a2) in "Hbytes".
      iDestruct (word4_pointsto_intro (p_xstate (proc_addr k)) (DfracOwn 1) xs Halx
                   with "Hbytes") as "Hxstate".
      iDestruct ("Hback" $! P' with "[%] Hsz Hpg Hpt") as "Hpriv"; [exact Hext |].
      iAssert (proc_pub (proc_addr k)) with "[Hkilled Hxstate Hpidhalf]" as "Hpub".
      { iExists kl, xs, pidc. iFrame "Hkilled Hxstate Hpidhalf". }
      assert (Hcosp : mco !!! Regidx csp_rs1 = spr)
        by (rewrite (callee_saved_lookup Hcsco csp_rs1 ltac:(vm_compute; reflexivity)); exact HF5sp).
      assert (Hcos1 : mco !!! Regidx Rs1 = proc_addr k)
        by (rewrite (callee_saved_lookup Hcsco Rs1 ltac:(vm_compute; reflexivity)); exact HF5s1).
      assert (Hcos3 : mco !!! Regidx Rs3 = sign_extend' 64 pidc)
        by (rewrite (callee_saved_lookup Hcsco Rs3 ltac:(vm_compute; reflexivity)); exact HF5s3).
      assert (Hcocs : kw_cs_rest mco mm) by (eapply kw_cs_rest_cs; [exact Hcsco | exact HF5cs]).
      (* ---- +0x58 blt a0,x0 -> +0x90 : did copyout fail? ---- *)
      destruct (zopz0zI_s (rget (CID := CIDf) mco Ra0) (zero_reg : mword 64)) eqn:Hblt.
      + (* ===== copyout failed: unwind both locks, return -1 ===== *)
        iApply (wp_blt_x0_taken_s_sconf Φ (mword_of_int (KW + 0x58))
                  (mword_of_int 56 : mword 13) Ra0 mco (K - 10)%nat false
                  ltac:(vm_compute; discriminate) Hblt ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi58 [-]").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt90 : add_vec (mword_of_int (KW + 0x58) : mword 64)
                           (sign_extend' 64 (mword_of_int 56 : mword 13))
                         = mword_of_int (KW + 0x90))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt90) in "Hpc".
        iDestruct (pstate_whole_split (proc_addr k) ZOMBIE) as "[Hwz2 _]".
        iDestruct ("Hwz2" with "Hpsg") as "[Hpsg _]".
        iAssert (proc_lock_res Φ γs γk (proc_addr k)) with "[Hstate Hpsg Hchan Hpub Hdorm Hpark]" as "HRk".
        { iApply (proc_lock_res_intro Φ γs γk (proc_addr k) ZOMBIE ch
                    with "Hstate Hpsg Hchan Hpub [Hdorm Hpark]").
          rewrite /proc_slots inv_dormant_ZOMBIE not_running_ZOMBIE is_running_ZOMBIE.
          rewrite (_ : needs_ctx ZOMBIE = false); [| vm_compute; reflexivity].
          iSplitR; [done |]. iSplitR; [done |]. iFrame "Hdorm Hpark". }
        iApply (kw_exit_both Φ γs γw γk mm mco pme k K eb C
                  HK Hcosp Hcos1 Hcocs
                  with "Hcg Hown Hpay1 Hpay0 Htext Hpc Hlkk Htokk HRk Hlk Htok
                        [Hps] Hframe [Hcont Hpriv]").
        { iExists ps. iExact "Hps". }
        iIntros (CIDz) "%Hsz". iIntros (mf) "%Hcsf %Ha0 Hcg Hown Hpc".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf P' (mword_of_int (-1) : mword 32)
                  with "[%] [%] [%] Hcg Hown Hpc Hpriv").
        { exact Hcsf. }
        { rewrite Ha0. apply bv_eq; vm_compute; reflexivity. }
        { exact Hext. }
      + (* ===== copyout succeeded: fall through to the reaping tail ===== *)
        iApply (wp_blt_x0_fall_s_sconf Φ (mword_of_int (KW + 0x58))
                  (mword_of_int 56 : mword 13) Ra0 mco (K - 10)%nat false
                  ltac:(vm_compute; discriminate) Hblt
                  with "Hcg Hpc Hi58 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp5c : add_vec_int (mword_of_int (KW + 0x58) : mword 64) 4
                       = mword_of_int (KW + 0x5c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp5c) in "Hpc".
        iApply (kw_reap Φ γs γa γw γk mm mco pme k K eb C pidc ch ps
                  HK Hk Hcosp Hcos1 Hcos3 Hcocs
                  with "Hcg Hown Hpay1 Hpay0 Htext Hpc Henv Hlkk Htokk Hstate Hpsg Hchan
                        Hpub Hdorm Hpark Hlk Htok Hps Hframe [Hcont Hpriv]").
        iIntros (CIDz) "%Hsz". iIntros (mf) "%Hcsf %Ha0 Hcg Hown Hpc".
        iSpecialize ("Hcont" $! CIDz with "[%]"); [wp_next_chain |].
        iApply ("Hcont" $! mf P' pidc with "[%] [%] [%] Hcg Hown Hpc Hpriv").
        { exact Hcsf. }
        { exact Ha0. }
        { exact Hext. }
  Qed.

  (* ================================================================== *)
  (* THE INNER SCAN, +0xae / +0xa6 / +0xaa.                              *)
  (*                                                                     *)
  (* A bounded fuel induction over proc[], exactly wakeup's and kkill's.  *)
  (* THE WHOLE SCAN RUNS AT INDEX [false] -- wait_lock is held from       *)
  (* before it to after it, and the acquire/release pair inside a body    *)
  (* never unwinds past level 1 -- so the hart is pinned end to end and   *)
  (* nothing here needs a [wp_next] anchor.  The one continuation that    *)
  (* does is the FUNCTION exit, which the found arm reaches after its     *)
  (* last release re-enables interrupts; that one rides through as a      *)
  (* [wp_next] and is handed to [kw_found] untouched.                     *)
  (*                                                                     *)
  (* Both continuations are PREMISES of the loop statement rather than    *)
  (* resources in its context, so the IH keeps its leading binders        *)
  (* (fdalloc's rule).                                                    *)
  (* ================================================================== *)
  Local Lemma kw_scan `{GEN : GenId} `{CID0 : CpuId}
      (Φ : mval -> iProp Σ) (γs : list gname) (γa γf γw : gname)
      (mm : regfile) (pme addr : mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (R : iProp Σ) :
    let sp0 := mm !!! Regidx csp_rs1 in
    (K_kwait <= K)%nat ->
    length γs = NPROC ->
    procs_inv Φ γs -∗
    panic_wp_any -∗
    kernel_text -∗
    kalloc_env γa None -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    ∀ (kk : nat) (M : regfile) (hv : mword 64) (ps : list (mword 64)),
      ⌜(kk < NPROC)%nat⌝ -∗ ⌜kw_scan_regs M mm pme addr kk⌝ -∗
      ⌜M !!! Regidx Ra4 = hv⌝ -∗
      (* the FUNCTION exit, for the found path *)
      kw_exit_fn CID0 Φ γf mm pme K eb C pid V R -∗
      (* the SCAN exit, at +0xca, at the same (pinned) hart.  It takes the
         FUNCTION exit back as its own argument: the two are ONE linear
         resource and only the branch that actually runs may have it. *)
      (∀ (Mx : regfile) (hx : mword 64) (px : list (mword 64)),
          ⌜ kw_scan_regs Mx mm pme addr NPROC ⌝ -∗
          ⌜ Mx !!! Regidx Ra4 = hx ⌝ -∗
          sie_cap_gpr Mx (K - 10)%nat false pme -∗
          cpu_own 1 eb pme C false -∗
          arm_pay 0 eb pme -∗
          pc_is (mword_of_int (KW + 0xca)) -∗
          locked γw CID0 -∗ parents_own px -∗
          proc_priv γf pme pid V -∗ kw_frame sp0 mm -∗ R -∗
          kw_exit_fn CID0 Φ γf mm pme K eb C pid V R -∗
          WP (Loop : expr riscv_lang) {{ Φ }}) -∗
      sie_cap_gpr M (K - 10)%nat false pme -∗
      cpu_own 1 eb pme C false -∗
      arm_pay 0 eb pme -∗
      pc_is (mword_of_int (KW + 0xae)) -∗
      locked γw CID0 -∗ parents_own ps -∗
      proc_priv γf pme pid V -∗ kw_frame sp0 mm -∗ R -∗
      WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 HK Hlen.
    iIntros "#Hpinv #Hpanic #Htext #Henv #Hlk".
    iAssert (∀ (fuel kk : nat) (M : regfile) (hv : mword 64) (ps : list (mword 64)),
               ⌜(NPROC - kk <= fuel)%nat⌝ -∗ ⌜(kk < NPROC)%nat⌝ -∗
               ⌜kw_scan_regs M mm pme addr kk⌝ -∗ ⌜M !!! Regidx Ra4 = hv⌝ -∗
               kw_exit_fn CID0 Φ γf mm pme K eb C pid V R -∗
               (∀ (Mx : regfile) (hx : mword 64) (px : list (mword 64)),
                   ⌜ kw_scan_regs Mx mm pme addr NPROC ⌝ -∗
                   ⌜ Mx !!! Regidx Ra4 = hx ⌝ -∗
                   sie_cap_gpr Mx (K - 10)%nat false pme -∗
                   cpu_own 1 eb pme C false -∗
                   arm_pay 0 eb pme -∗
                   pc_is (mword_of_int (KW + 0xca)) -∗
                   locked γw CID0 -∗ parents_own px -∗
                   proc_priv γf pme pid V -∗ kw_frame sp0 mm -∗ R -∗
                   kw_exit_fn CID0 Φ γf mm pme K eb C pid V R -∗
                   WP (Loop : expr riscv_lang) {{ Φ }}) -∗
               sie_cap_gpr M (K - 10)%nat false pme -∗
               cpu_own 1 eb pme C false -∗
               arm_pay 0 eb pme -∗
               pc_is (mword_of_int (KW + 0xae)) -∗
               locked γw CID0 -∗ parents_own ps -∗
               proc_priv γf pme pid V -∗ kw_frame sp0 mm -∗ R -∗
               WP (Loop : expr riscv_lang) {{ Φ }})%I with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { iIntros (kk M hv ps) "%Hf %Hk %Hregs %Ha4 Hqfn Hqca Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe HR".
        exfalso. exact (kw_fuel0 kk Hf Hk). }
      iIntros (kk M hv ps) "%Hf %Hk %Hregs %Ha4 Hqfn Hqca Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe HR".
      pose proof Hregs as Hregs'.
      destruct Hregs' as (Hsp & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hcs).
      destruct (lookup_lt_is_Some_2 γs kk ltac:(rewrite Hlen; exact Hk)) as [γk Hγk].
      iDestruct (procs_inv_lookup Φ γs kk γk Hγk with "Hpinv") as "#Hlkk".
      iPoseProof (kwi_ae with "Htext") as "Hiae".
      iPoseProof (kwi_b0 with "Htext") as "Hib0".
      iPoseProof (kwi_b4 with "Htext") as "Hib4".
      iPoseProof (kwi_b6 with "Htext") as "Hib6".
      iPoseProof (kwi_ba with "Htext") as "Hiba".
      iPoseProof (kwi_bc with "Htext") as "Hibc".
      iPoseProof (kwi_c0 with "Htext") as "Hic0".
      iPoseProof (kwi_c2 with "Htext") as "Hic2".
      iPoseProof (kwi_c6 with "Htext") as "Hic6".
      iPoseProof (kwi_c8 with "Htext") as "Hic8".
      iPoseProof (kwi_a6 with "Htext") as "Hia6".
      iPoseProof (kwi_aa with "Htext") as "Hiaa".
      (* ---------------------------------------------------------------- *)
      (* The SHARED tail +0xa6/+0xaa: pp++ and the end-of-table test.      *)
      (* Reached from the no-match arm and from the released arm, at       *)
      (* different [a4]s -- hence a block over an arbitrary [M'] and [hv'] *)
      (* rather than two copies.  It takes the function-exit continuation  *)
      (* as a PREMISE because the next iteration may need it.              *)
      (* ---------------------------------------------------------------- *)
      iAssert (∀ (M' : regfile) (hv' : mword 64) (ps' : list (mword 64)),
                 ⌜kw_scan_regs M' mm pme addr kk⌝ -∗ ⌜M' !!! Regidx Ra4 = hv'⌝ -∗
                 kw_exit_fn CID0 Φ γf mm pme K eb C pid V R -∗
                 sie_cap_gpr M' (K - 10)%nat false pme -∗
                 cpu_own 1 eb pme C false -∗
                 arm_pay 0 eb pme -∗
                 pc_is (mword_of_int (KW + 0xa6)) -∗
                 locked γw CID0 -∗ parents_own ps' -∗
                 proc_priv γf pme pid V -∗ kw_frame sp0 mm -∗ R -∗
                 WP (Loop : expr riscv_lang) {{ Φ }})%I
        with "[IHf Hqca]" as "Hnext".
      { iIntros (M' hv' ps') "%Hregs' %Ha4' Hqfn' Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe HR".
        pose proof Hregs' as Hregs''.
        destruct Hregs'' as (Hsp' & Hs1' & Hs2' & Hs3' & Hs4' & Hs5' & Hs6' & Hs7' & Hcs').
        (* +0xa6 addi s1,s1,360 : pp++ *)
        assert (Hbump : add_vec (rget (CID := CID0) M' Rs1)
                          (sign_extend' 64 (mword_of_int 360 : mword 12)) = proc_addr (S kk)).
        { rewrite (rget_ne (CID := CID0) M' Rs1 ltac:(vm_compute; discriminate)) Hs1'.
          exact (proc_addr_succ kk). }
        iApply (wp_addi4_s_sconf Φ (mword_of_int (KW + 0xa6)) Rs1 Rs1
                  (mword_of_int 360 : mword 12) M' (K - 10)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hia6 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rewrite Hbump) in "Hcg".
        set (N0 := <[Regidx Rs1 := regval_into_reg (proc_addr (S kk))]> M').
        change (<[Regidx Rs1 := regval_into_reg (proc_addr (S kk))]> M') with N0.
        assert (HN0 : kw_scan_regs N0 mm pme addr (S kk))
          by (rewrite /N0; apply kw_scan_regs_s1; exact Hregs').
        assert (HN0a4 : N0 !!! Regidx Ra4 = hv')
          by (rewrite /N0 upd_ne; [exact Ha4' | reg_neq]).
        pose proof HN0 as HN0'.
        destruct HN0' as (HN0sp & HN0s1 & HN0s2 & HN0s3 & HN0s4 & HN0s5 & HN0s6 & HN0s7 & HN0cs).
        assert (Hpaa : add_vec_int (mword_of_int (KW + 0xa6) : mword 64) 4 = mword_of_int (KW + 0xaa))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpaa) in "Hpc".
        (* +0xaa beq s1,s3 -> +0xca : end of the table? *)
        assert (Hrgs1 : rget (CID := CID0) N0 Rs1 = N0 !!! Regidx Rs1) by (rgne; reflexivity).
        assert (Hrgs3 : rget (CID := CID0) N0 Rs3 = N0 !!! Regidx Rs3) by (rgne; reflexivity).
        destruct (Nat.eq_dec (S kk) NPROC) as [Hend | Hne].
        - (* the table is exhausted: leave the scan *)
          assert (Hcmp : eq_vec (rget (CID := CID0) N0 Rs1) (rget (CID := CID0) N0 Rs3) = true).
          { rewrite Hrgs1 Hrgs3 HN0s1 HN0s3 Hend. apply kw_eq_vec_refl. }
          iApply (wp_beq_taken_s_sconf Φ (mword_of_int (KW + 0xaa))
                    (mword_of_int 32 : mword 13) Rs3 Rs1 N0 (K - 10)%nat false
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hiaa [-]").
          iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Htgtca : add_vec (mword_of_int (KW + 0xaa) : mword 64)
                             (sign_extend' 64 (mword_of_int 32 : mword 13))
                           = mword_of_int (KW + 0xca))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgtca) in "Hpc".
          iApply ("Hqca" $! N0 hv' ps' with "[%] [%] Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe HR Hqfn'").
          { rewrite -Hend. exact HN0. }
          { exact HN0a4. }
        - (* more slots: back to +0xae at the bumped cursor *)
          assert (HkS : (S kk < NPROC)%nat) by (unfold NPROC in *; lia).
          assert (Hcmp : eq_vec (rget (CID := CID0) N0 Rs1) (rget (CID := CID0) N0 Rs3) = false).
          { rewrite Hrgs1 Hrgs3 HN0s1 HN0s3. exact (kw_end_lt (S kk) HkS). }
          iApply (wp_beq_fall_s_sconf Φ (mword_of_int (KW + 0xaa))
                    (mword_of_int 32 : mword 13) Rs3 Rs1 N0 (K - 10)%nat false
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp with "Hcg Hpc Hiaa [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Hpae : add_vec_int (mword_of_int (KW + 0xaa) : mword 64) 4
                         = mword_of_int (KW + 0xae))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpae) in "Hpc".
          iApply ("IHf" $! (S kk) N0 hv' ps' with "[%] [%] [%] [%] Hqfn' Hqca Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe HR").
          { unfold NPROC in *; lia. }
          { exact HkS. }
          { exact HN0. }
          { exact HN0a4. } }
      (* ---------------------------------------------------------------- *)
      (* +0xae ld a5,56(s1) : pp->parent, out of wait_lock's table         *)
      (* ---------------------------------------------------------------- *)
      iDestruct (parents_own_length ps with "Hps") as %Hlps.
      destruct (lookup_lt_is_Some_2 ps kk ltac:(rewrite Hlps; exact Hk)) as [pv Hpv].
      iDestruct (parents_own_read ps kk pv Hpv with "Hps") as "[Hcell Hback]".
      assert (Heaae : add_vec (rget (CID := CID0) M Rs1)
                        (sign_extend' 64 (mword_of_int 56 : mword 12)) = p_parent (proc_addr kk)).
      { rewrite (rget_ne (CID := CID0) M Rs1 ltac:(vm_compute; discriminate)) Hs1.
        apply kw_parent_off. }
      iApply (wp_cld_s_sconf Φ (mword_of_int (KW + 0xae)) Ra5 Rs1
                (mword_of_int 56 : mword 12) M (K - 10)%nat pv false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hiae [Hcell] [-]").
      { iEval (rewrite Heaae). iExact "Hcell". }
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcell".
      iEval (rewrite Heaae) in "Hcell".
      iDestruct ("Hback" with "Hcell") as "Hps".
      set (S0 := <[Regidx Ra5 := regval_into_reg pv]> M).
      change (<[Regidx Ra5 := regval_into_reg pv]> M) with S0.
      assert (HS0a5 : S0 !!! Regidx Ra5 = pv) by (rewrite /S0 upd_eq; reflexivity).
      assert (HS0 : kw_scan_regs S0 mm pme addr kk)
        by (rewrite /S0; apply kw_scan_regs_ncs;
            [vm_compute; reflexivity | exact Hregs]).
      assert (HS0a4 : S0 !!! Regidx Ra4 = hv)
        by (rewrite /S0 upd_ne; [exact Ha4 | reg_neq]).
      pose proof HS0 as HS0'.
      destruct HS0' as (HS0sp & HS0s1 & HS0s2 & HS0s3 & HS0s4 & HS0s5 & HS0s6 & HS0s7 & HS0cs).
      assert (Hpb0 : add_vec_int (mword_of_int (KW + 0xae) : mword 64) 2 = mword_of_int (KW + 0xb0))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpb0) in "Hpc".
      (* ---- +0xb0 bne s2,a5 -> +0xa6 : is this slot our child? ---- *)
      assert (Hrga5 : rget (CID := CID0) S0 Ra5 = S0 !!! Regidx Ra5) by (rgne; reflexivity).
      assert (Hrgs2 : rget (CID := CID0) S0 Rs2 = S0 !!! Regidx Rs2) by (rgne; reflexivity).
      destruct (neq_vec (rget (CID := CID0) S0 Ra5) (rget (CID := CID0) S0 Rs2)) eqn:Hne.
      + (* ===== not our child: straight to the increment ===== *)
        iApply (wp_bne_taken_s_sconf Φ (mword_of_int (KW + 0xb0))
                  (mword_of_int 8182 : mword 13) Rs2 Ra5 S0 (K - 10)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hne ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hib0 [-]").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgta6 : add_vec (mword_of_int (KW + 0xb0) : mword 64)
                           (sign_extend' 64 (mword_of_int 8182 : mword 13))
                         = mword_of_int (KW + 0xa6))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgta6) in "Hpc".
        iApply ("Hnext" $! S0 hv ps with "[%] [%] Hqfn Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe HR").
        { exact HS0. }
        { exact HS0a4. }
      + (* ===== our child: take its lock and look at its state ===== *)
        iApply (wp_bne_fall_s_sconf Φ (mword_of_int (KW + 0xb0))
                  (mword_of_int 8182 : mword 13) Rs2 Ra5 S0 (K - 10)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hne with "Hcg Hpc Hib0 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpb4 : add_vec_int (mword_of_int (KW + 0xb0) : mword 64) 4
                       = mword_of_int (KW + 0xb4))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpb4) in "Hpc".
        (* +0xb4 c.mv a0,s1 *)
        assert (Hrgb4 : rget (CID := CID0) S0 Rs1 = S0 !!! Regidx Rs1) by (rgne; reflexivity).
        iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0xb4)) Ra0 Rs1
                  S0 (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hib4 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rewrite Hrgb4 HS0s1) in "Hcg".
        set (S1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr kk))]> S0).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr kk))]> S0) with S1.
        assert (HS1a0 : S1 !!! Regidx Ra0 = proc_addr kk)
          by (rewrite /S1 upd_eq; apply add_vec_zero_l).
        assert (HS1 : kw_scan_regs S1 mm pme addr kk)
          by (rewrite /S1; apply kw_scan_regs_ncs;
              [vm_compute; reflexivity | exact HS0]).
        assert (Hpb6 : add_vec_int (mword_of_int (KW + 0xb4) : mword 64) 2
                       = mword_of_int (KW + 0xb6))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpb6) in "Hpc".
        (* +0xb6 jal ra,acquire *)
        iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0xb6)) Rra
                  (mword_of_int 2091484 : mword 21) S1 (K - 10)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hib6 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (S2 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KW + 0xb6) : mword 64) 4)]> S1).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KW + 0xb6) : mword 64) 4)]> S1) with S2.
        assert (Hjacq : add_vec (mword_of_int (KW + 0xb6) : mword 64)
                          (sign_extend' 64 (mword_of_int 2091484 : mword 21))
                        = mword_of_int KernelSyms.acquire)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjacq) in "Hpc".
        assert (HS2ra : S2 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0xb6) : mword 64) 4)
          by (rewrite /S2 upd_eq; reflexivity).
        assert (HS2a0 : S2 !!! Regidx Ra0 = proc_addr kk)
          by (rewrite /S2 upd_ne; [exact HS1a0 | reg_neq]).
        assert (HS2 : kw_scan_regs S2 mm pme addr kk)
          by (rewrite /S2; apply kw_scan_regs_ncs;
              [vm_compute; reflexivity | exact HS1]).
        iApply (Acquire.wp_acquire_sconf Φ γk "proc"%string
                  (proc_lock_res Φ γs γk (proc_addr kk)) S2 1%nat eb pme C (K - 10)%nat false
                  kw_ilvl1 (kw_K10 K HK)
                  with "Hcg Hown Htext Hpc [Hlkk] Hpanic [-]").
        { iEval (rewrite HS2a0). iExact "Hlkk". }
        iApply wp_next_off_intro.
        iIntros (ms Macq) "%Hms Hcg Hpc %Hpins Htokk HRk Hown Hpay1".
        assert (Hpba : ret_pc (S2 !!! Regidx Rra) = mword_of_int (KW + 0xba))
          by (rewrite HS2ra; apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpba) in "Hpc".
        assert (HAcq : kw_scan_regs Macq mm pme addr kk)
          by (eapply kw_scan_regs_cs; [exact Hpins | exact HS2]).
        iDestruct (proc_lock_res_elim Φ γs γk (proc_addr kk) with "HRk")
          as (st ch) "(Hstate & Hpsg & Hchan & Hpub & Hslots)".
        (* +0xba lw a5,24(s1) : pp->state *)
        assert (Heaba : add_vec (rget (CID := CID0) Macq Rs1)
                          (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state (proc_addr kk)).
        { destruct HAcq as (_ & B2 & _).
          rewrite (rget_ne (CID := CID0) Macq Rs1 ltac:(vm_compute; discriminate)) B2.
          apply kw_state_off. }
        iApply (wp_clw_s_sconf Φ (mword_of_int (KW + 0xba)) Ra5 Rs1
                  (mword_of_int 24 : mword 12) Macq (K - 10)%nat st false (dqm := DfracOwn 1)
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hiba [Hstate] [-]").
        { iEval (rewrite Heaba). iExact "Hstate". }
        iApply wp_next_off_intro. iIntros "Hcg Hpc Hstate".
        iEval (rewrite Heaba) in "Hstate".
        set (S3 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 st)]> Macq).
        change (<[Regidx Ra5 := regval_into_reg (sign_extend' 64 st)]> Macq) with S3.
        assert (HS3a5 : S3 !!! Regidx Ra5 = sign_extend' 64 st)
          by (rewrite /S3 upd_eq; reflexivity).
        assert (HS3 : kw_scan_regs S3 mm pme addr kk)
          by (rewrite /S3; apply kw_scan_regs_ncs;
              [vm_compute; reflexivity | exact HAcq]).
        pose proof HS3 as HS3'.
        destruct HS3' as (HS3sp & HS3s1 & HS3s2 & HS3s3 & HS3s4 & HS3s5 & HS3s6 & HS3s7 & HS3cs).
        assert (Hpbc : add_vec_int (mword_of_int (KW + 0xba) : mword 64) 2
                       = mword_of_int (KW + 0xbc))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpbc) in "Hpc".
        (* ---- +0xbc beq s4,a5 -> +0x40 : is it a ZOMBIE? ---- *)
        assert (Hrgba5 : rget (CID := CID0) S3 Ra5 = S3 !!! Regidx Ra5) by (rgne; reflexivity).
        assert (Hrgbs4 : rget (CID := CID0) S3 Rs4 = S3 !!! Regidx Rs4) by (rgne; reflexivity).
        destruct (eq_vec (rget (CID := CID0) S3 Ra5) (rget (CID := CID0) S3 Rs4)) eqn:Hzomb.
        * (* ===== ZOMBIE: reap it (the function EXITS here) ===== *)
          assert (Hstz : st = ZOMBIE).
          { apply kw_sext_zombie.
            rewrite -HS3a5 -Hrgba5. rewrite -HS3s4 -Hrgbs4.
            symmetry. by apply eq_vec_true_iff in Hzomb. }
          iApply (wp_beq_taken_s_sconf Φ (mword_of_int (KW + 0xbc))
                    (mword_of_int 8068 : mword 13) Rs4 Ra5 S3 (K - 10)%nat false
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hzomb ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hibc [-]").
          iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Htgt40 : add_vec (mword_of_int (KW + 0xbc) : mword 64)
                             (sign_extend' 64 (mword_of_int 8068 : mword 13))
                           = mword_of_int (KW + 0x40))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgt40) in "Hpc".
          rewrite Hstz.
          iDestruct (kw_slots_zombie Φ γs (proc_addr kk) with "Hslots") as "[Hdorm Hpark]".
          (* ZOMBIE is unclaimed, so the lock's share is the whole mirror --
             which is what [proc_held] wants for the freeproc call below. *)
          iDestruct (pstate_whole_split (proc_addr kk) ZOMBIE) as "[_ Hwz]".
          iDestruct ("Hwz" with "[Hpsg]") as "Hpsg";
            [rewrite unclaimed_ZOMBIE; iFrame "Hpsg"|].
          (* the found arm is the one that RETURNS, so this is where [R] is
             cashed into the caller's continuation -- which turns the
             frame-carrying [kw_exit_fn] back into [kw_found]'s plain one. *)
          iAssert (wp_next (CID0 := CID0) eb pme (fun (CID : CpuId) =>
                     ∀ (mf : regfile) (P' : uptd) (rv : mword 32),
                       ⌜ callee_saved mm mf ⌝ -∗
                       ⌜ mf !!! Regidx Ra0 = sign_extend' 64 rv ⌝ -∗
                       ⌜ uptd_ext_sz (pv_sz V) (pv_upt V) P' ⌝ -∗
                       sie_cap_gpr mf K eb pme -∗
                       cpu_own 0 eb pme C eb -∗
                       pc_is (ret_pc (mm !!! Regidx Rra)) -∗
                       proc_priv γf pme pid (upd_upt V P') -∗
                       WP (Loop : expr riscv_lang) {{ Φ }}))%I
            with "[Hqfn HR]" as "Hqfn2".
          { rewrite /kw_exit_fn.
            iIntros (CIDq Hsq mf P' rv) "%Hcsq %Ha0q %Hextq Hcgq Hownq Hpcq Hprivq".
            iApply ("Hqfn" $! CIDq Hsq mf P' rv with
                     "[%] [%] [%] Hcgq Hownq Hpcq Hprivq HR");
              [exact Hcsq | exact Ha0q | exact Hextq]. }
          iApply (kw_found Φ γs γa γf γw γk mm S3 pme kk K eb C pid V ch ps
                    HK Hk HS3sp HS3s1 HS3s2 HS3cs
                    with "Hcg Hown Hpay1 Hpay Htext Hpc Henv Hlkk Htokk Hstate Hpsg Hchan
                          Hpub Hdorm Hpark Hlk Htok Hps Hpriv Hframe Hqfn2").
        * (* ===== not a ZOMBIE: release, set havekids, continue ===== *)
          iApply (wp_beq_fall_s_sconf Φ (mword_of_int (KW + 0xbc))
                    (mword_of_int 8068 : mword 13) Rs4 Ra5 S3 (K - 10)%nat false
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hzomb with "Hcg Hpc Hibc [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          assert (Hpc0 : add_vec_int (mword_of_int (KW + 0xbc) : mword 64) 4
                         = mword_of_int (KW + 0xc0))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc0) in "Hpc".
          (* +0xc0 c.mv a0,s1 *)
          assert (Hrgc0 : rget (CID := CID0) S3 Rs1 = S3 !!! Regidx Rs1) by (rgne; reflexivity).
          iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0xc0)) Ra0 Rs1
                    S3 (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hic0 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          iEval (rewrite Hrgc0 HS3s1) in "Hcg".
          set (S4 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr kk))]> S3).
          change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr kk))]> S3) with S4.
          assert (HS4a0 : S4 !!! Regidx Ra0 = proc_addr kk)
            by (rewrite /S4 upd_eq; apply add_vec_zero_l).
          assert (HS4 : kw_scan_regs S4 mm pme addr kk)
            by (rewrite /S4; apply kw_scan_regs_ncs;
                [vm_compute; reflexivity | exact HS3]).
          assert (Hpc2 : add_vec_int (mword_of_int (KW + 0xc0) : mword 64) 2
                         = mword_of_int (KW + 0xc2))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc2) in "Hpc".
          (* +0xc2 jal ra,release *)
          iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0xc2)) Rra
                    (mword_of_int 2091608 : mword 21) S4 (K - 10)%nat false
                    ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hic2 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          set (S5 := <[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (KW + 0xc2) : mword 64) 4)]> S4).
          change (<[Regidx Rra := regval_into_reg
                        (add_vec_int (mword_of_int (KW + 0xc2) : mword 64) 4)]> S4) with S5.
          assert (Hjrel : add_vec (mword_of_int (KW + 0xc2) : mword 64)
                            (sign_extend' 64 (mword_of_int 2091608 : mword 21))
                          = mword_of_int KernelSyms.release)
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hjrel) in "Hpc".
          assert (HS5ra : S5 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0xc2) : mword 64) 4)
            by (rewrite /S5 upd_eq; reflexivity).
          assert (HS5a0 : S5 !!! Regidx Ra0 = proc_addr kk)
            by (rewrite /S5 upd_ne; [exact HS4a0 | reg_neq]).
          assert (HS5 : kw_scan_regs S5 mm pme addr kk)
            by (rewrite /S5; apply kw_scan_regs_ncs;
                [vm_compute; reflexivity | exact HS4]).
          assert (Hlkc : add_vec (S5 !!! Regidx Ra0)
                           (sign_extend' 64 (mword_of_int 0 : mword 12)) = proc_addr kk)
            by (rewrite HS5a0; apply addv_sext0).
          iAssert (proc_lock_res Φ γs γk (proc_addr kk)) with "[Hstate Hpsg Hchan Hpub Hslots]" as "HRk".
          { iApply (proc_lock_res_intro Φ γs γk (proc_addr kk) st ch
                      with "Hstate Hpsg Hchan Hpub Hslots"). }
          iApply (Release.wp_release_sconf Φ γk (proc_addr kk) "proc"%string
                    (proc_lock_res Φ γs γk (proc_addr kk)) S5 1%nat eb pme C (K - 10)%nat
                    Hlkc (kw_K10 K HK)
                    with "Hcg Htext Hpc Hlkk Htokk HRk Hown Hpay1 [-]").
          iApply wp_next_off_intro. iIntros (mrel) "Hcg Hpc %Hcsrel Hown".
          assert (Hpc6 : ret_pc (S5 !!! Regidx Rra) = mword_of_int (KW + 0xc6))
            by (rewrite HS5ra; apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc6) in "Hpc".
          assert (HRel : kw_scan_regs mrel mm pme addr kk)
            by (eapply kw_scan_regs_cs; [exact Hcsrel | exact HS5]).
          pose proof HRel as HRel'.
          destruct HRel' as (HRsp & HRs1 & HRs2 & HRs3 & HRs4 & HRs5 & HRs6 & HRs7 & HRcs).
          (* +0xc6 c.mv a4,s5 : havekids = 1 *)
          assert (Hrgc6 : rget (CID := CID0) mrel Rs5 = mrel !!! Regidx Rs5) by (rgne; reflexivity).
          iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0xc6)) Ra4 Rs5
                    mrel (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                    with "Hcg Hpc Hic6 [-]").
          iApply wp_next_off_intro. iIntros "Hcg Hpc".
          iEval (rewrite Hrgc6) in "Hcg".
          set (S6 := <[Regidx Ra4 := regval_into_reg (add_vec zero_reg (mrel !!! Regidx Rs5))]> mrel).
          change (<[Regidx Ra4 := regval_into_reg (add_vec zero_reg (mrel !!! Regidx Rs5))]> mrel) with S6.
          assert (HS6 : kw_scan_regs S6 mm pme addr kk)
            by (rewrite /S6; apply kw_scan_regs_ncs;
                [vm_compute; reflexivity | exact HRel]).
          assert (HS6a4 : S6 !!! Regidx Ra4
                          = add_vec zero_reg (mrel !!! Regidx Rs5))
            by (rewrite /S6 upd_eq; reflexivity).
          assert (Hpc8 : add_vec_int (mword_of_int (KW + 0xc6) : mword 64) 2
                         = mword_of_int (KW + 0xc8))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc8) in "Hpc".
          (* +0xc8 c.j +0xa6 *)
          iApply (wp_cj_s_sconf Φ (mword_of_int (KW + 0xc8))
                    (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")))
                    S6 (K - 10)%nat false ltac:(vm_compute; reflexivity)
                    with "Hcg Hpc Hic8 [-]").
          iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
          assert (Htgta6' : add_vec (mword_of_int (KW + 0xc8) : mword 64)
                              (sign_extend' 64 (sign_extend' 21
                                 (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))))
                            = mword_of_int (KW + 0xa6))
            by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Htgta6') in "Hpc".
          iApply ("Hnext" $! S6 (add_vec zero_reg (mrel !!! Regidx Rs5)) ps
                    with "[%] [%] Hqfn Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe HR").
          { exact HS6. }
          { exact HS6a4. } }
    iIntros (kk M hv ps) "%Hk %Hregs %Ha4 Hqfn Hqca Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe HR".
    iApply ("Hloop" $! (NPROC - kk)%nat kk M hv ps
              with "[%] [%] [%] [%] Hqfn Hqca Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe HR");
      [ lia | exact Hk | exact Hregs | exact Ha4 ].
  Qed.

  (* ================================================================== *)
  (* +0xe8 REACHED FROM THE OUTER LOOP.  Both the "no kids" test and the *)
  (* "killed" test jump here, at different register files, so the block  *)
  (* is one lemma: it is [kw_exit_wait] with the caller's continuation   *)
  (* assembled out of [kw_exit_fn] plus the two resources the -1 exits   *)
  (* still hold (the private block, unchanged, and the running-thread    *)
  (* frame).                                                            *)
  (* ================================================================== *)
  Local Lemma kw_exit_neg `{GEN : GenId} `{CIDt : CpuId}
      (Φ : mval -> iProp Σ) (γf γw : gname) (jj : nat) (mm Mt : regfile)
      (pme : mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (px : list (mword 64)) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))) in
    (K_kwait <= K)%nat ->
    Mt !!! Regidx csp_rs1 = spr ->
    kw_cs_rest Mt mm ->
    kernel_text -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    kw_exit_fn CIDt Φ γf mm pme K eb C pid V (kw_rt pme jj) -∗
    sie_cap_gpr Mt (K - 10)%nat false pme -∗
    cpu_own 1 eb pme C false -∗
    arm_pay 0 eb pme -∗
    pc_is (mword_of_int (KW + 0xe8)) -∗
    locked γw CIDt -∗ parents_own px -∗
    proc_priv γf pme pid V -∗ kw_frame sp0 mm -∗ kw_rt pme jj -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spr HK Hsp Hcs.
    iIntros "#Htext #Hlk Hqfn Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe Hrt".
    iApply (kw_exit_wait Φ γw mm Mt pme K eb C HK Hsp Hcs
              with "Hcg Hown Hpay Htext Hpc Hlk Htok [Hps] Hframe [Hqfn Hpriv Hrt]").
    { rewrite /wait_res. iExists px. iExact "Hps". }
    rewrite /kw_exit_fn.
    iIntros (CIDx Hsx mf) "%Hcsx %Ha0x Hcgx Hownx Hpcx".
    iSpecialize ("Hqfn" $! CIDx with "[%]"); [exact Hsx |].
    iApply ("Hqfn" $! mf (pv_upt V) (mword_of_int (-1) : mword 32)
              with "[%] [%] [%] Hcgx Hownx Hpcx [Hpriv] Hrt").
    { exact Hcsx. }
    { rewrite Ha0x. apply bv_eq; vm_compute; reflexivity. }
    { apply uptd_ext_sz_refl. }
    { rewrite upd_upt_id. iExact "Hpriv". }
  Qed.

  (* ================================================================== *)
  (* +0xca .. +0xd8 -- THE ROUND's FOOT: the two -1 tests and sleep.     *)
  (*                                                                     *)
  (* Everything here runs at level 1 with interrupts off, so the hart is *)
  (* pinned right up to sleep -- which is the ONE crossing, and the      *)
  (* reason the loop's own statement is [wp_next]-wrapped.  The back     *)
  (* edge into +0xdc is a plain fall-through with no branch to strip a   *)
  (* later at, which is why the IH arrives here ALREADY stripped (the    *)
  (* [c.j] at +0xe6 paid for it).                                        *)
  (* ================================================================== *)
  Local Lemma kw_round_tail `{GEN : GenId} `{CIDt : CpuId} (CID0 : CPU)
      (Φ : mval -> iProp Σ) (γs : list gname) (γf γw γl : gname) (jj : nat)
      (mm Mx : regfile) (pme addr : mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) (hx : mword 64) (px : list (mword 64)) :
    let sp0 := mm !!! Regidx csp_rs1 in
    (K_kwait <= K)%nat ->
    eb = true ->
    (jj < NPROC)%nat ->
    γs !! jj = Some γl ->
    pme = proc_addr jj ->
    (true = false \/ pme = zero_reg -> (CIDt : CPU) = CID0) ->
    kw_scan_regs Mx mm pme addr NPROC ->
    Mx !!! Regidx Ra4 = hx ->
    kernel_text -∗ procs_inv Φ γs -∗ scheds_inv Φ γs -∗ panic_wp_any -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    kw_round CID0 Φ γf γw jj mm pme addr K eb C pid V -∗
    kw_exit_fn CIDt Φ γf mm pme K eb C pid V (kw_rt pme jj) -∗
    sie_cap_gpr Mx (K - 10)%nat false pme -∗
    cpu_own 1 eb pme C false -∗
    arm_pay 0 eb pme -∗
    pc_is (mword_of_int (KW + 0xca)) -∗
    locked γw CIDt -∗ parents_own px -∗
    proc_priv γf pme pid V -∗ kw_frame sp0 mm -∗ kw_rt pme jj -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 HK Heb Hjj Hgl Hpme Hanch Hregs Ha4.
    subst pme.
    iIntros "#Htext #Hpinv #Hscheds #Hpanic #Hlk IH Hqfn Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe Hrt".
    pose proof Hregs as Hregs2.
    destruct Hregs2 as (Hsp & Hcs1 & Hcs2 & Hcs3 & Hcs4 & Hcs5 & Hcs6 & Hcs7 & Hcs).
    iPoseProof (kwi_ca with "Htext") as "Hica".
    iPoseProof (kwi_cc with "Htext") as "Hicc".
    iPoseProof (kwi_ce with "Htext") as "Hice".
    iPoseProof (kwi_d2 with "Htext") as "Hid2".
    iPoseProof (kwi_d4 with "Htext") as "Hid4".
    iPoseProof (kwi_d6 with "Htext") as "Hid6".
    iPoseProof (kwi_d8 with "Htext") as "Hid8".
    (* ---- +0xca c.beqz a4 -> +0xe8 : havekids == 0? ---- *)
    destruct (eq_vec (rget (CID := CIDt) Mx Ra4) (zero_reg : mword 64)) eqn:Hhk.
    - (* ===== no kids at all: return -1 ===== *)
      iApply (wp_cbeqz_taken_s_sconf Φ (mword_of_int (KW + 0xca)) (mword_of_int 15 : mword 8)
                (Cregidx (mword_of_int 6)) Ra4 Mx (K - 10)%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                Hhk ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hica [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htge8 : add_vec (mword_of_int (KW + 0xca) : mword 64)
                        (sign_extend' 64 (sign_extend' 13
                           (concat_vec (mword_of_int 15 : mword 8) ('b"0"))))
                      = mword_of_int (KW + 0xe8)) by pcstep.
      iEval (rewrite Htge8) in "Hpc".
      iApply (kw_exit_neg Φ γf γw jj mm Mx (proc_addr jj) K eb C pid V px HK Hsp Hcs
                with "Htext Hlk Hqfn Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe Hrt").
    - (* ===== there are kids: ask whether we were killed ===== *)
      iApply (wp_cbeqz_fall_s_sconf Φ (mword_of_int (KW + 0xca)) (mword_of_int 15 : mword 8)
                (Cregidx (mword_of_int 6)) Ra4 Mx (K - 10)%nat false
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hhk
                with "Hcg Hpc Hica [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpcc : add_vec_int (mword_of_int (KW + 0xca) : mword 64) 2
                     = mword_of_int (KW + 0xcc)) by pcstep.
      iEval (rewrite Hpcc) in "Hpc".
      (* +0xcc c.mv a0,s2 *)
      assert (Hrgcc : rget (CID := CIDt) Mx Rs2 = Mx !!! Regidx Rs2) by (rgne; reflexivity).
      iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0xcc)) Ra0 Rs2
                Mx (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hicc [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      iEval (rewrite Hrgcc Hcs2) in "Hcg".
      set (T0 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr jj))]> Mx).
      change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr jj))]> Mx) with T0.
      assert (HT0a0 : T0 !!! Regidx Ra0 = proc_addr jj)
        by (rewrite /T0 upd_eq; apply add_vec_zero_l).
      assert (HT0 : kw_scan_regs T0 mm (proc_addr jj) addr NPROC)
        by (rewrite /T0; apply kw_scan_regs_ncs;
            [vm_compute; reflexivity | exact Hregs]).
      assert (Hpce : add_vec_int (mword_of_int (KW + 0xcc) : mword 64) 2
                     = mword_of_int (KW + 0xce)) by pcstep.
      iEval (rewrite Hpce) in "Hpc".
      (* +0xce jal ra,killed *)
      iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0xce)) Rra
                (mword_of_int 2096904 : mword 21) T0 (K - 10)%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hice [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      set (T1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KW + 0xce) : mword 64) 4)]> T0).
      change (<[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KW + 0xce) : mword 64) 4)]> T0) with T1.
      assert (Hjkl : add_vec (mword_of_int (KW + 0xce) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096904 : mword 21))
                     = mword_of_int KernelSyms.killed) by pcstep.
      iEval (rewrite Hjkl) in "Hpc".
      assert (HT1ra : T1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KW + 0xce) : mword 64) 4)
        by (rewrite /T1 upd_eq; reflexivity).
      assert (HT1a0 : T1 !!! Regidx Ra0 = proc_addr jj)
        by (rewrite /T1 upd_ne; [exact HT0a0 | reg_neq]).
      assert (HT1 : kw_scan_regs T1 mm (proc_addr jj) addr NPROC)
        by (rewrite /T1; apply kw_scan_regs_ncs;
            [vm_compute; reflexivity | exact HT0]).
      iApply (Killed.wp_killed_sconf Φ γs jj γl T1 (K - 10)%nat 1%nat eb
                (proc_addr jj) C false HT1a0 Hjj Hgl kw_ilvl1 (kw_K14 K HK)
                with "Hcg Hown Htext Hpc Hpinv Hpanic [-]").
      iApply wp_next_off_intro. iIntros (mfk kl) "%Hkf Hcg Hown Hpc".
      destruct Hkf as (Hkcs & Hka0).
      assert (Hpd2 : ret_pc (T1 !!! Regidx Rra) = mword_of_int (KW + 0xd2))
        by (rewrite HT1ra; pcstep).
      iEval (rewrite Hpd2) in "Hpc".
      assert (HKl : kw_scan_regs mfk mm (proc_addr jj) addr NPROC)
        by (eapply kw_scan_regs_cs; [exact Hkcs | exact HT1]).
      pose proof HKl as HKl'.
      destruct HKl' as (Hksp & Hks1 & Hks2 & Hks3 & Hks4 & Hks5 & Hks6 & Hks7 & Hkcsr).
      (* ---- +0xd2 c.bnez a0 -> +0xe8 : killed(p) ? ---- *)
      destruct (neq_vec (rget (CID := CIDt) mfk Ra0) (zero_reg : mword 64)) eqn:Hkil.
      + (* ===== killed: return -1 ===== *)
        iApply (wp_cbnez_taken_s_sconf Φ (mword_of_int (KW + 0xd2)) (mword_of_int 11 : mword 8)
                  (Cregidx (mword_of_int 2)) Ra0 mfk (K - 10)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                  Hkil ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hid2 [-]").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htge8' : add_vec (mword_of_int (KW + 0xd2) : mword 64)
                           (sign_extend' 64 (sign_extend' 13
                              (concat_vec (mword_of_int 11 : mword 8) ('b"0"))))
                         = mword_of_int (KW + 0xe8)) by pcstep.
        iEval (rewrite Htge8') in "Hpc".
        iApply (kw_exit_neg Φ γf γw jj mm mfk (proc_addr jj) K eb C pid V px HK Hksp Hkcsr
                  with "Htext Hlk Hqfn Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe Hrt").
      + (* ===== still alive: sleep on p, then scan again ===== *)
        iApply (wp_cbnez_fall_s_sconf Φ (mword_of_int (KW + 0xd2)) (mword_of_int 11 : mword 8)
                  (Cregidx (mword_of_int 2)) Ra0 mfk (K - 10)%nat false
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hkil
                  with "Hcg Hpc Hid2 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hpd4 : add_vec_int (mword_of_int (KW + 0xd2) : mword 64) 2
                       = mword_of_int (KW + 0xd4)) by pcstep.
        iEval (rewrite Hpd4) in "Hpc".
        (* +0xd4 c.mv a1,s6 : the condition lock *)
        assert (Hrgd4 : rget (CID := CIDt) mfk Rs6 = mfk !!! Regidx Rs6) by (rgne; reflexivity).
        iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0xd4)) Ra1 Rs6
                  mfk (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hid4 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rewrite Hrgd4 Hks6) in "Hcg".
        set (T2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg wait_lock_addr)]> mfk).
        change (<[Regidx Ra1 := regval_into_reg (add_vec zero_reg wait_lock_addr)]> mfk) with T2.
        assert (HT2a1 : T2 !!! Regidx Ra1 = wait_lock_addr)
          by (rewrite /T2 upd_eq; apply add_vec_zero_l).
        assert (HT2 : kw_scan_regs T2 mm (proc_addr jj) addr NPROC)
          by (rewrite /T2; apply kw_scan_regs_ncs;
              [vm_compute; reflexivity | exact HKl]).
        assert (Hpd6 : add_vec_int (mword_of_int (KW + 0xd4) : mword 64) 2
                       = mword_of_int (KW + 0xd6)) by pcstep.
        iEval (rewrite Hpd6) in "Hpc".
        (* +0xd6 c.mv a0,s2 : the channel *)
        assert (Hrgd6 : rget (CID := CIDt) T2 Rs2 = T2 !!! Regidx Rs2) by (rgne; reflexivity).
        assert (HT2s2 : T2 !!! Regidx Rs2 = proc_addr jj)
          by (destruct HT2 as (_ & _ & X & _); exact X).
        iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0xd6)) Ra0 Rs2
                  T2 (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hid6 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        iEval (rewrite Hrgd6 HT2s2) in "Hcg".
        set (T3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr jj))]> T2).
        change (<[Regidx Ra0 := regval_into_reg (add_vec zero_reg (proc_addr jj))]> T2) with T3.
        assert (HT3a1 : T3 !!! Regidx Ra1 = wait_lock_addr)
          by (rewrite /T3 upd_ne; [exact HT2a1 | reg_neq]).
        assert (HT3 : kw_scan_regs T3 mm (proc_addr jj) addr NPROC)
          by (rewrite /T3; apply kw_scan_regs_ncs;
              [vm_compute; reflexivity | exact HT2]).
        assert (Hpd8 : add_vec_int (mword_of_int (KW + 0xd6) : mword 64) 2
                       = mword_of_int (KW + 0xd8)) by pcstep.
        iEval (rewrite Hpd8) in "Hpc".
        (* +0xd8 jal ra,sleep *)
        iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0xd8)) Rra
                  (mword_of_int 2096322 : mword 21) T3 (K - 10)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hid8 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        set (T4 := <[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KW + 0xd8) : mword 64) 4)]> T3).
        change (<[Regidx Rra := regval_into_reg
                      (add_vec_int (mword_of_int (KW + 0xd8) : mword 64) 4)]> T3) with T4.
        assert (Hjsl : add_vec (mword_of_int (KW + 0xd8) : mword 64)
                         (sign_extend' 64 (mword_of_int 2096322 : mword 21))
                       = mword_of_int KernelSyms.sleep) by pcstep.
        iEval (rewrite Hjsl) in "Hpc".
        assert (HT4ra : T4 !!! Regidx Rra
                        = add_vec_int (mword_of_int (KW + 0xd8) : mword 64) 4)
          by (rewrite /T4 upd_eq; reflexivity).
        assert (HT4a1 : T4 !!! Regidx Ra1 = wait_lock_addr)
          by (rewrite /T4 upd_ne; [exact HT3a1 | reg_neq]).
        assert (HT4 : kw_scan_regs T4 mm (proc_addr jj) addr NPROC)
          by (rewrite /T4; apply kw_scan_regs_ncs;
              [vm_compute; reflexivity | exact HT3]).
        assert (Hlka : add_vec (T4 !!! Regidx Ra1)
                         (sign_extend' 64 (mword_of_int 0 : mword 12)) = wait_lock_addr)
          by (rewrite HT4a1; apply addv_sext0).
        iEval (rewrite /kw_rt) in "Hrt". iRename "Hrt" into "Hpark".
        iApply (Sleep.wp_sleep_sconf Φ γs jj γl γw wait_lock_addr "wait_lock"%string
                  wait_res T4 (K - 10)%nat eb C Hjj Hgl Hlka Heb (kw_K22 K HK)
                  with "Hcg Hown Hpay Htext Hpc Hpinv Hscheds Hlk Htok [Hps] Hpanic Hpark [-]").
        { rewrite /wait_res. iExists px. iExact "Hps". }
        (* SLEEP RETURNS ON HART [CIDs]: the outer loop's one crossing. *)
        iIntros (CIDs Hss mfs) "%Hscs Hcg Hown Hpay Hpc Htok Hres Hpark".
        assert (Hpdc : ret_pc (T4 !!! Regidx Rra) = mword_of_int (KW + 0xdc))
          by (rewrite HT4ra; pcstep).
        iEval (rewrite Hpdc) in "Hpc".
        assert (HrT4 : kw_round_regs T4 mm (proc_addr jj) addr)
          by (eapply kw_round_regs_of_scan; exact HT4).
        assert (Hrfs : kw_round_regs mfs mm (proc_addr jj) addr)
          by (eapply kw_round_regs_cs; [exact Hscs | exact HrT4]).
        rewrite /kw_round.
        iSpecialize ("IH" $! CIDs with "[%]"); [wp_next_chain |].
        iApply ("IH" $! mfs with "[%] Hcg Hown Hpay Hpc Htok Hres Hpriv Hframe
                                   [Hpark] [Hqfn]").
        { exact Hrfs. }
        { rewrite /kw_rt. iFrame "Hpark". }
        { rewrite /kw_exit_fn.
          iApply (kw_next_reanchor CIDt CIDs eb (proc_addr jj) with "[Hqfn]");
            [ exact (kw_chain_eb eb (proc_addr jj) CIDs CIDt Heb Hss) |].
          iExact "Hqfn". }
  Qed.

  (* ================================================================== *)
  (* +0xdc .. +0xe6 -- ONE TURN of the outer loop, and the [iNext] that  *)
  (* pays for the IH's later.                                            *)
  (* ================================================================== *)
  Local Lemma kw_round_body `{GEN : GenId} `{CIDy : CpuId} (CID0 : CPU)
      (Φ : mval -> iProp Σ) (γs : list gname) (γa γf γw γl : gname) (jj : nat)
      (mm M : regfile) (pme addr : mword 64) (K : nat) (eb : bool) (C : iProp Σ)
      (pid : mword 32) (V : pprivate) :
    let sp0 := mm !!! Regidx csp_rs1 in
    (K_kwait <= K)%nat ->
    eb = true ->
    (jj < NPROC)%nat ->
    γs !! jj = Some γl ->
    length γs = NPROC ->
    pme = proc_addr jj ->
    (true = false \/ pme = zero_reg -> (CIDy : CPU) = CID0) ->
    kw_round_regs M mm pme addr ->
    kernel_text -∗ procs_inv Φ γs -∗ scheds_inv Φ γs -∗ panic_wp_any -∗
    kalloc_env γa None -∗
    is_lock γw wait_lock_addr "wait_lock"%string wait_res -∗
    ▷ kw_round CID0 Φ γf γw jj mm pme addr K eb C pid V -∗
    kw_exit_fn CIDy Φ γf mm pme K eb C pid V (kw_rt pme jj) -∗
    sie_cap_gpr M (K - 10)%nat false pme -∗
    cpu_own 1 eb pme C false -∗
    arm_pay 0 eb pme -∗
    pc_is (mword_of_int (KW + 0xdc)) -∗
    locked γw CIDy -∗ wait_res -∗
    proc_priv γf pme pid V -∗ kw_frame sp0 mm -∗ kw_rt pme jj -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 HK Heb Hjj Hgl Hlen Hpme Hanch Hregs.
    iIntros "#Htext #Hpinv #Hscheds #Hpanic #Henv #Hlk IH Hqfn Hcg Hown Hpay Hpc
             Htok Hres Hpriv Hframe Hrt".
    iDestruct "Hres" as (ps) "Hps".
    iPoseProof (kwi_dc with "Htext") as "Hidc".
    iPoseProof (kwi_de with "Htext") as "Hide".
    iPoseProof (kwi_e2 with "Htext") as "Hie2".
    iPoseProof (kwi_e6 with "Htext") as "Hie6".
    (* +0xdc c.li a4,0 : havekids = 0 *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (KW + 0xdc)) Ra4 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) M (K - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hidc [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D0 := <[Regidx Ra4 := regval_into_reg (mword_of_int 0 : mword 64)]> M).
    change (<[Regidx Ra4 := regval_into_reg (mword_of_int 0 : mword 64)]> M) with D0.
    assert (HD0a4 : D0 !!! Regidx Ra4 = (mword_of_int 0 : mword 64))
      by (rewrite /D0 upd_eq; reflexivity).
    assert (HD0 : kw_round_regs D0 mm pme addr)
      by (rewrite /D0; apply kw_round_regs_ncs;
          [vm_compute; reflexivity | exact Hregs]).
    assert (Hpde : add_vec_int (mword_of_int (KW + 0xdc) : mword 64) 2
                   = mword_of_int (KW + 0xde)) by pcstep.
    iEval (rewrite Hpde) in "Hpc".
    (* +0xde auipc s1,0x10 *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KW + 0xde)) Rs1 (mword_of_int 16 : mword 20)
              D0 (K - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hide [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (D1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0xde) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> D0).
    change (<[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0xde) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> D0) with D1.
    assert (HD1a4 : D1 !!! Regidx Ra4 = (mword_of_int 0 : mword 64))
      by (rewrite /D1 upd_ne; [exact HD0a4 | reg_neq]).
    assert (HD1 : kw_round_regs D1 mm pme addr)
      by (rewrite /D1; apply kw_round_regs_s1w; exact HD0).
    assert (Hpe2 : add_vec_int (mword_of_int (KW + 0xde) : mword 64) 4
                   = mword_of_int (KW + 0xe2)) by pcstep.
    iEval (rewrite Hpe2) in "Hpc".
    (* +0xe2 addi s1,s1,1316 : pp = &proc[0] *)
    assert (Hrge2 : rget (CID := CIDy) D1 Rs1 = D1 !!! Regidx Rs1) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KW + 0xe2)) Rs1 Rs1
              (mword_of_int 1316 : mword 12) D1 (K - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hie2 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hrge2) in "Hcg".
    set (D2 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (D1 !!! Regidx Rs1)
                     (sign_extend' 64 (mword_of_int 1316 : mword 12)))]> D1).
    change (<[Regidx Rs1 := regval_into_reg
                  (add_vec (D1 !!! Regidx Rs1)
                     (sign_extend' 64 (mword_of_int 1316 : mword 12)))]> D1) with D2.
    assert (HD2s1 : D2 !!! Regidx Rs1 = proc_addr 0).
    { rewrite /D2 upd_eq /D1 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HD2a4 : D2 !!! Regidx Ra4 = (mword_of_int 0 : mword 64))
      by (rewrite /D2 upd_ne; [exact HD1a4 | reg_neq]).
    assert (HD2 : kw_round_regs D2 mm pme addr)
      by (rewrite /D2; apply kw_round_regs_s1w; exact HD1).
    assert (HD2scan : kw_scan_regs D2 mm pme addr 0)
      by (apply kw_scan_regs_of_round; [exact HD2 | exact HD2s1]).
    assert (Hpe6 : add_vec_int (mword_of_int (KW + 0xe2) : mword 64) 4
                   = mword_of_int (KW + 0xe6)) by pcstep.
    iEval (rewrite Hpe6) in "Hpc".
    (* +0xe6 c.j +0xae -- ITS [iNext] IS WHAT STRIPS THE IH's LATER, and the
       back edge after sleep (a fall-through) has no branch of its own. *)
    iApply (wp_cj_s_sconf Φ (mword_of_int (KW + 0xe6))
              (sign_extend' 21 (concat_vec (mword_of_int 2020 : mword 11) ('b"0")))
              D2 (K - 10)%nat false ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hie6 [-]").
    iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
    assert (Htgae : add_vec (mword_of_int (KW + 0xe6) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 2020 : mword 11) ('b"0"))))
                    = mword_of_int (KW + 0xae)) by pcstep.
    iEval (rewrite Htgae) in "Hpc".
    (* the scan's exit at +0xca, closed over the (now bare) IH *)
    iAssert (∀ (Mx : regfile) (hx : mword 64) (px : list (mword 64)),
               ⌜ kw_scan_regs Mx mm pme addr NPROC ⌝ -∗
               ⌜ Mx !!! Regidx Ra4 = hx ⌝ -∗
               sie_cap_gpr Mx (K - 10)%nat false pme -∗
               cpu_own 1 eb pme C false -∗
               arm_pay 0 eb pme -∗
               pc_is (mword_of_int (KW + 0xca)) -∗
               locked γw CIDy -∗ parents_own px -∗
               proc_priv γf pme pid V -∗ kw_frame sp0 mm -∗ kw_rt pme jj -∗
               kw_exit_fn CIDy Φ γf mm pme K eb C pid V (kw_rt pme jj) -∗
               WP (Loop : expr riscv_lang) {{ Φ }})%I
      with "[IH]" as "Hqca".
    { iIntros (Mx hx px) "%Hrx %Hax Hcgx Hownx Hpayx Hpcx Htokx Hpsx Hprivx Hframex Hrtx Hqfnx".
      iApply (kw_round_tail (CIDt := CIDy) CID0 Φ γs γf γw γl jj mm Mx pme addr K eb C
                pid V hx px HK Heb Hjj Hgl Hpme Hanch Hrx Hax
                with "Htext Hpinv Hscheds Hpanic Hlk IH Hqfnx Hcgx Hownx Hpayx Hpcx
                      Htokx Hpsx Hprivx Hframex Hrtx"). }
    iDestruct (kw_scan (CID0 := CIDy) Φ γs γa γf γw mm pme addr K eb C pid V
                 (kw_rt pme jj) HK Hlen with "Hpinv Hpanic Htext Henv Hlk") as "Hscan".
    iApply ("Hscan" $! 0%nat D2 (mword_of_int 0 : mword 64) ps
              with "[%] [%] [%] Hqfn Hqca Hcg Hown Hpay Hpc Htok Hps Hpriv Hframe Hrt").
    { unfold NPROC; lia. }
    { exact HD2scan. }
    { exact HD2a4. }
  Qed.

End ProofKwait.

(* ===================================================================== *)
(*  THE WHOLE FUNCTION: the prologue, then the outer loop's Löb.          *)
(* ===================================================================== *)
Section ProofKwaitMain.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ, !fileG Σ}.

  Local Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.
  Local Ltac pcstep := apply bv_eq; vm_compute; reflexivity.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).

  Lemma wp_kwait_sconf `{GEN : GenId} `{CID : CpuId}
      (γa γf γw : gname) (Φ : mval -> iProp Σ) (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (pid : mword 32) (V : pprivate) :
    wp_kwait_sconf_body γa γf γw Φ γs j γl m av eb C b pid V.
  Proof.
    cbv beta delta [wp_kwait_sconf_body].
    intros pcE pj ret_tgt Hj Hgl Hav Heb.
    iIntros "Hcg Hown #Htext Hpc #Hpinv #Hscheds #Hpanic Hpark #Hlk #Henv Hpriv Hcont".
    (* LEVEL 0 WITH AN ENABLED BASE FORCES THE ENABLED INDEX (sys_pause's
       rule): the [b <> eb] instances of this contract are vacuous. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbm.
    assert (Hb : b = eb) by (symmetry; exact Hbm).
    clear Hbm. subst b.
    iDestruct (procs_inv_len with "Hpinv") as %Hlen.
    assert (Hpjv : pj = proc_addr j) by reflexivity.
    (* ============================ PROLOGUE ============================ *)
    iPoseProof (kwi_00 with "Htext") as "Hi00".
    iPoseProof (kwi_02 with "Htext") as "Hi02".
    iPoseProof (kwi_04 with "Htext") as "Hi04".
    iPoseProof (kwi_06 with "Htext") as "Hi06".
    iPoseProof (kwi_08 with "Htext") as "Hi08".
    iPoseProof (kwi_0a with "Htext") as "Hi0a".
    iPoseProof (kwi_0c with "Htext") as "Hi0c".
    iPoseProof (kwi_0e with "Htext") as "Hi0e".
    iPoseProof (kwi_10 with "Htext") as "Hi10".
    iPoseProof (kwi_12 with "Htext") as "Hi12".
    iPoseProof (kwi_14 with "Htext") as "Hi14".
    iPoseProof (kwi_16 with "Htext") as "Hi16".
    iPoseProof (kwi_18 with "Htext") as "Hi18".
    iPoseProof (kwi_1c with "Htext") as "Hi1c".
    iPoseProof (kwi_1e with "Htext") as "Hi1e".
    iPoseProof (kwi_22 with "Htext") as "Hi22".
    iPoseProof (kwi_26 with "Htext") as "Hi26".
    iPoseProof (kwi_2a with "Htext") as "Hi2a".
    iPoseProof (kwi_2c with "Htext") as "Hi2c".
    iPoseProof (kwi_2e with "Htext") as "Hi2e".
    iPoseProof (kwi_32 with "Htext") as "Hi32".
    iPoseProof (kwi_36 with "Htext") as "Hi36".
    iPoseProof (kwi_3a with "Htext") as "Hi3a".
    iPoseProof (kwi_3e with "Htext") as "Hi3e".
    (* +0x00 c.addi16sp sp,-80 *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 10%nat).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi16sp_push_s_sconf Φ pcE (mword_of_int 59 : mword 6) m av 10%nat eb
              (kw_K10K av Hav) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (P0 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> m) with P0.
    assert (HP0sp : P0 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
      by (rewrite /P0 upd_eq; reflexivity).
    assert (HP0cs : kw_cs_rest P0 m) by (rewrite /P0; apply kw_cs_rest_sp; apply kw_cs_rest_refl).
    (* the nine save slots, at the frame pointer the stores use *)
    assert (Hb1 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 1).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 2).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 3).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 4).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 5).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 6).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 7).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 8).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec (P0 !!! Regidx csp_rs1)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1) 9).
    { rewrite HP0sp. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _)".
    iDestruct "F1" as (v1) "H1". iDestruct "F2" as (v2) "H2".
    iDestruct "F3" as (v3) "H3". iDestruct "F4" as (v4) "H4".
    iDestruct "F5" as (v5) "H5". iDestruct "F6" as (v6) "H6".
    iDestruct "F7" as (v7) "H7". iDestruct "F8" as (v8) "H8".
    iDestruct "F9" as (v9) "H9".
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KW + 0x2)) by pcstep.
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 .. +0x12: the nine c.sdsp *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KW + 0x2)) (mword_of_int 9 : mword 6) Rra
              P0 (av - 10)%nat v1 eb with "Hcg Hpc Hi02 [H1] [-]").
    { iEval (rewrite Hb1). iExact "H1". }
    iIntros (CID2 Hs2) "Hcg Hpc H1". iEval (rewrite Hb1) in "H1". iEval (rgne) in "H1".
    assert (Hp04 : add_vec_int (mword_of_int (KW + 0x2) : mword 64) 2 = mword_of_int (KW + 0x4)) by pcstep.
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KW + 0x4)) (mword_of_int 8 : mword 6) Rs0
              P0 (av - 10)%nat v2 eb with "Hcg Hpc Hi04 [H2] [-]").
    { iEval (rewrite Hb2). iExact "H2". }
    iIntros (CID3 Hs3) "Hcg Hpc H2". iEval (rewrite Hb2) in "H2". iEval (rgne) in "H2".
    assert (Hp06 : add_vec_int (mword_of_int (KW + 0x4) : mword 64) 2 = mword_of_int (KW + 0x6)) by pcstep.
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KW + 0x6)) (mword_of_int 7 : mword 6) Rs1
              P0 (av - 10)%nat v3 eb with "Hcg Hpc Hi06 [H3] [-]").
    { iEval (rewrite Hb3). iExact "H3". }
    iIntros (CID4 Hs4) "Hcg Hpc H3". iEval (rewrite Hb3) in "H3". iEval (rgne) in "H3".
    assert (Hp08 : add_vec_int (mword_of_int (KW + 0x6) : mword 64) 2 = mword_of_int (KW + 0x8)) by pcstep.
    iEval (rewrite Hp08) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KW + 0x8)) (mword_of_int 6 : mword 6) Rs2
              P0 (av - 10)%nat v4 eb with "Hcg Hpc Hi08 [H4] [-]").
    { iEval (rewrite Hb4). iExact "H4". }
    iIntros (CID5 Hs5) "Hcg Hpc H4". iEval (rewrite Hb4) in "H4". iEval (rgne) in "H4".
    assert (Hp0a : add_vec_int (mword_of_int (KW + 0x8) : mword 64) 2 = mword_of_int (KW + 0xa)) by pcstep.
    iEval (rewrite Hp0a) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KW + 0xa)) (mword_of_int 5 : mword 6) Rs3
              P0 (av - 10)%nat v5 eb with "Hcg Hpc Hi0a [H5] [-]").
    { iEval (rewrite Hb5). iExact "H5". }
    iIntros (CID6 Hs6) "Hcg Hpc H5". iEval (rewrite Hb5) in "H5". iEval (rgne) in "H5".
    assert (Hp0c : add_vec_int (mword_of_int (KW + 0xa) : mword 64) 2 = mword_of_int (KW + 0xc)) by pcstep.
    iEval (rewrite Hp0c) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KW + 0xc)) (mword_of_int 4 : mword 6) Rs4
              P0 (av - 10)%nat v6 eb with "Hcg Hpc Hi0c [H6] [-]").
    { iEval (rewrite Hb6). iExact "H6". }
    iIntros (CID7 Hs7) "Hcg Hpc H6". iEval (rewrite Hb6) in "H6". iEval (rgne) in "H6".
    assert (Hp0e : add_vec_int (mword_of_int (KW + 0xc) : mword 64) 2 = mword_of_int (KW + 0xe)) by pcstep.
    iEval (rewrite Hp0e) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KW + 0xe)) (mword_of_int 3 : mword 6) Rs5
              P0 (av - 10)%nat v7 eb with "Hcg Hpc Hi0e [H7] [-]").
    { iEval (rewrite Hb7). iExact "H7". }
    iIntros (CID8 Hs8) "Hcg Hpc H7". iEval (rewrite Hb7) in "H7". iEval (rgne) in "H7".
    assert (Hp10 : add_vec_int (mword_of_int (KW + 0xe) : mword 64) 2 = mword_of_int (KW + 0x10)) by pcstep.
    iEval (rewrite Hp10) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KW + 0x10)) (mword_of_int 2 : mword 6) Rs6
              P0 (av - 10)%nat v8 eb with "Hcg Hpc Hi10 [H8] [-]").
    { iEval (rewrite Hb8). iExact "H8". }
    iIntros (CID9 Hs9) "Hcg Hpc H8". iEval (rewrite Hb8) in "H8". iEval (rgne) in "H8".
    assert (Hp12 : add_vec_int (mword_of_int (KW + 0x10) : mword 64) 2 = mword_of_int (KW + 0x12)) by pcstep.
    iEval (rewrite Hp12) in "Hpc".
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (KW + 0x12)) (mword_of_int 1 : mword 6) Rs7
              P0 (av - 10)%nat v9 eb with "Hcg Hpc Hi12 [H9] [-]").
    { iEval (rewrite Hb9). iExact "H9". }
    iIntros (CID10 Hs10) "Hcg Hpc H9". iEval (rewrite Hb9) in "H9". iEval (rgne) in "H9".
    (* the nine cells now hold [m]'s values: re-anchor them off [P0] *)
    assert (HP0ra : P0 !!! Regidx Rra = m !!! Regidx Rra) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s0 : P0 !!! Regidx Rs0 = m !!! Regidx Rs0) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s1 : P0 !!! Regidx Rs1 = m !!! Regidx Rs1) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s2 : P0 !!! Regidx Rs2 = m !!! Regidx Rs2) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s3 : P0 !!! Regidx Rs3 = m !!! Regidx Rs3) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s4 : P0 !!! Regidx Rs4 = m !!! Regidx Rs4) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s5 : P0 !!! Regidx Rs5 = m !!! Regidx Rs5) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s6 : P0 !!! Regidx Rs6 = m !!! Regidx Rs6) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    assert (HP0s7 : P0 !!! Regidx Rs7 = m !!! Regidx Rs7) by (rewrite /P0 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HP0ra) in "H1". iEval (rewrite HP0s0) in "H2".
    iEval (rewrite HP0s1) in "H3". iEval (rewrite HP0s2) in "H4".
    iEval (rewrite HP0s3) in "H5". iEval (rewrite HP0s4) in "H6".
    iEval (rewrite HP0s5) in "H7". iEval (rewrite HP0s6) in "H8".
    iEval (rewrite HP0s7) in "H9".
    iAssert (kw_frame (m !!! Regidx csp_rs1) m)
      with "[H1 H2 H3 H4 H5 H6 H7 H8 H9 F10]" as "Hkframe".
    { rewrite /kw_frame. iFrame "H1 H2 H3 H4 H5 H6 H7 H8 H9". iExact "F10". }
    assert (Hp14 : add_vec_int (mword_of_int (KW + 0x12) : mword 64) 2 = mword_of_int (KW + 0x14)) by pcstep.
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 c.addi4spn s0,sp,80 *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (KW + 0x14)) (Cregidx (mword_of_int 0))
              (mword_of_int 20 : mword 8) Rs0 P0 (av - 10)%nat eb
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (P1 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (P0 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> P0).
    change (<[Regidx Rs0 := regval_into_reg
                  (add_vec (P0 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> P0) with P1.
    assert (HP1sp : P1 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
      by (rewrite /P1 upd_ne; [exact HP0sp | reg_neq]).
    assert (HP1cs : kw_cs_rest P1 m) by (rewrite /P1; apply kw_cs_rest_s0; exact HP0cs).
    assert (Hp16 : add_vec_int (mword_of_int (KW + 0x14) : mword 64) 2 = mword_of_int (KW + 0x16)) by pcstep.
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 c.mv s7,a0 : s7 = addr *)
    assert (Hrg16 : rget (CID := CID11) P1 Ra0 = P1 !!! Regidx Ra0) by (rgne; reflexivity).
    assert (HP1a0 : P1 !!! Regidx Ra0 = m !!! Regidx Ra0).
    { rewrite /P1 upd_ne; [| reg_neq]. rewrite /P0 upd_ne; [reflexivity | reg_neq]. }
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0x16)) Rs7 Ra0
              P1 (av - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    iEval (rewrite Hrg16 HP1a0) in "Hcg".
    set (adr := add_vec (zero_reg : mword 64) (m !!! Regidx Ra0)).
    set (P2 := <[Regidx Rs7 := regval_into_reg adr]> P1).
    change (<[Regidx Rs7 := regval_into_reg (add_vec zero_reg (m !!! Regidx Ra0))]> P1) with P2.
    assert (HP2sp : P2 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
      by (rewrite /P2 upd_ne; [exact HP1sp | reg_neq]).
    assert (HP2s7 : P2 !!! Regidx Rs7 = adr) by (rewrite /P2 upd_eq; reflexivity).
    assert (HP2cs : kw_cs_rest P2 m) by (rewrite /P2; apply kw_cs_rest_s7; exact HP1cs).
    assert (Hp18 : add_vec_int (mword_of_int (KW + 0x16) : mword 64) 2 = mword_of_int (KW + 0x18)) by pcstep.
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18 jal ra,myproc *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0x18)) Rra
              (mword_of_int 2094968 : mword 21) P2 (av - 10)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (P3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x18) : mword 64) 4)]> P2).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x18) : mword 64) 4)]> P2) with P3.
    assert (Hjmy : add_vec (mword_of_int (KW + 0x18) : mword 64)
                     (sign_extend' 64 (mword_of_int 2094968 : mword 21))
                   = mword_of_int KernelSyms.myproc) by pcstep.
    iEval (rewrite Hjmy) in "Hpc".
    assert (HP3ra : P3 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0x18) : mword 64) 4)
      by (rewrite /P3 upd_eq; reflexivity).
    assert (HP3sp : P3 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
      by (rewrite /P3 upd_ne; [exact HP2sp | reg_neq]).
    assert (HP3s7 : P3 !!! Regidx Rs7 = adr) by (rewrite /P3 upd_ne; [exact HP2s7 | reg_neq]).
    assert (HP3cs : kw_cs_rest P3 m)
      by (rewrite /P3; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HP2cs]).
    (* [cpu_own] is the one bundle no leaf re-anchors: it rides the whole
       prologue at the hart it was handed in at, so it is transported once,
       at each call that consumes it. *)
    iDestruct (cpu_own_transport CID CID13 0%nat eb pj C eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Myproc.wp_myproc_sconf Φ P3 (av - 10)%nat 0%nat eb pj C eb
              kw_ilvl0 (kw_K10 av Hav) with "Hcg Hown Htext Hpc [-]").
    iIntros (CID14 Hs14 msm mfm) "%Hms Hcg Hown Hpc %Hmy".
    destruct Hmy as (Hmycs & Hmya0).
    assert (Hp1c : ret_pc (P3 !!! Regidx Rra) = mword_of_int (KW + 0x1c))
      by (rewrite HP3ra; pcstep).
    iEval (rewrite Hp1c) in "Hpc".
    assert (Hmsp : mfm !!! Regidx csp_rs1
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
      by (rewrite (callee_saved_lookup Hmycs csp_rs1 ltac:(vm_compute; reflexivity)); exact HP3sp).
    assert (Hms7 : mfm !!! Regidx Rs7 = adr)
      by (rewrite (callee_saved_lookup Hmycs Rs7 ltac:(vm_compute; reflexivity)); exact HP3s7).
    assert (Hmcs : kw_cs_rest mfm m) by (eapply kw_cs_rest_cs; [exact Hmycs | exact HP3cs]).
    (* +0x1c c.mv s2,a0 : s2 = p *)
    assert (Hrg1c : rget (CID := CID14) mfm Ra0 = mfm !!! Regidx Ra0) by (rgne; reflexivity).
    iApply (wp_cmv_s_sconf Φ (mword_of_int (KW + 0x1c)) Rs2 Ra0
              mfm (av - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    iIntros (CID15 Hs15) "Hcg Hpc".
    iEval (rewrite Hrg1c Hmya0) in "Hcg".
    set (P4 := <[Regidx Rs2 := regval_into_reg (add_vec (zero_reg : mword 64) pj)]> mfm).
    change (<[Regidx Rs2 := regval_into_reg (add_vec zero_reg pj)]> mfm) with P4.
    assert (HP4s2 : P4 !!! Regidx Rs2 = pj) by (rewrite /P4 upd_eq; apply add_vec_zero_l).
    assert (HP4sp : P4 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
      by (rewrite /P4 upd_ne; [exact Hmsp | reg_neq]).
    assert (HP4s7 : P4 !!! Regidx Rs7 = adr) by (rewrite /P4 upd_ne; [exact Hms7 | reg_neq]).
    assert (HP4cs : kw_cs_rest P4 m) by (rewrite /P4; apply kw_cs_rest_s2; exact Hmcs).
    assert (Hp1e : add_vec_int (mword_of_int (KW + 0x1c) : mword 64) 2 = mword_of_int (KW + 0x1e)) by pcstep.
    iEval (rewrite Hp1e) in "Hpc".
    (* +0x1e/+0x22 a0 = &wait_lock *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KW + 0x1e)) Ra0 (mword_of_int 16 : mword 20)
              P4 (av - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e [-]").
    iIntros (CID16 Hs16) "Hcg Hpc".
    set (P5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0x1e) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> P4).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0x1e) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> P4) with P5.
    assert (Hp22 : add_vec_int (mword_of_int (KW + 0x1e) : mword 64) 4 = mword_of_int (KW + 0x22)) by pcstep.
    iEval (rewrite Hp22) in "Hpc".
    assert (Hrg22 : rget (CID := CID16) P5 Ra0 = P5 !!! Regidx Ra0) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KW + 0x22)) Ra0 Ra0 (mword_of_int 460 : mword 12)
              P5 (av - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 [-]").
    iIntros (CID17 Hs17) "Hcg Hpc".
    iEval (rewrite Hrg22) in "Hcg".
    set (P6 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (P5 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 460 : mword 12)))]> P5).
    change (<[Regidx Ra0 := regval_into_reg
                  (add_vec (P5 !!! Regidx Ra0) (sign_extend' 64 (mword_of_int 460 : mword 12)))]> P5) with P6.
    assert (HP6a0 : P6 !!! Regidx Ra0 = wait_lock_addr).
    { rewrite /P6 upd_eq /P5 upd_eq /wait_lock_addr. apply bv_eq; vm_compute; reflexivity. }
    assert (HP6s2 : P6 !!! Regidx Rs2 = pj).
    { rewrite /P6 upd_ne; [| reg_neq]. rewrite /P5 upd_ne; [exact HP4s2 | reg_neq]. }
    assert (HP6sp : P6 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))).
    { rewrite /P6 upd_ne; [| reg_neq]. rewrite /P5 upd_ne; [exact HP4sp | reg_neq]. }
    assert (HP6s7 : P6 !!! Regidx Rs7 = adr).
    { rewrite /P6 upd_ne; [| reg_neq]. rewrite /P5 upd_ne; [exact HP4s7 | reg_neq]. }
    assert (HP6cs : kw_cs_rest P6 m).
    { rewrite /P6. apply kw_cs_rest_ncs; [vm_compute; reflexivity |].
      rewrite /P5. apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HP4cs]. }
    assert (Hp26 : add_vec_int (mword_of_int (KW + 0x22) : mword 64) 4 = mword_of_int (KW + 0x26)) by pcstep.
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26 jal ra,acquire : take wait_lock *)
    iApply (wp_jal_s_sconf Φ (mword_of_int (KW + 0x26)) Rra
              (mword_of_int 2091628 : mword 21) P6 (av - 10)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi26 [-]").
    iIntros (CID18 Hs18) "Hcg Hpc".
    set (P7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x26) : mword 64) 4)]> P6).
    change (<[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KW + 0x26) : mword 64) 4)]> P6) with P7.
    assert (Hjacq : add_vec (mword_of_int (KW + 0x26) : mword 64)
                      (sign_extend' 64 (mword_of_int 2091628 : mword 21))
                    = mword_of_int KernelSyms.acquire) by pcstep.
    iEval (rewrite Hjacq) in "Hpc".
    assert (HP7ra : P7 !!! Regidx Rra = add_vec_int (mword_of_int (KW + 0x26) : mword 64) 4)
      by (rewrite /P7 upd_eq; reflexivity).
    assert (HP7a0 : P7 !!! Regidx Ra0 = wait_lock_addr)
      by (rewrite /P7 upd_ne; [exact HP6a0 | reg_neq]).
    assert (HP7s2 : P7 !!! Regidx Rs2 = pj) by (rewrite /P7 upd_ne; [exact HP6s2 | reg_neq]).
    assert (HP7sp : P7 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
      by (rewrite /P7 upd_ne; [exact HP6sp | reg_neq]).
    assert (HP7s7 : P7 !!! Regidx Rs7 = adr) by (rewrite /P7 upd_ne; [exact HP6s7 | reg_neq]).
    assert (HP7cs : kw_cs_rest P7 m)
      by (rewrite /P7; apply kw_cs_rest_ncs; [vm_compute; reflexivity | exact HP6cs]).
    iDestruct (cpu_own_transport CID14 CID18 0%nat eb pj C eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf Φ γw "wait_lock"%string wait_res P7 0%nat eb pj C
              (av - 10)%nat eb kw_ilvl0 (kw_K10 av Hav)
              with "Hcg Hown Htext Hpc [Hlk] Hpanic [-]").
    { iEval (rewrite HP7a0). iExact "Hlk". }
    iIntros (CID19 Hs19 msa Macq) "%Hmsa Hcg Hpc %Hacs Htok Hres Hown Hpay".
    assert (Hp2a : ret_pc (P7 !!! Regidx Rra) = mword_of_int (KW + 0x2a))
      by (rewrite HP7ra; pcstep).
    iEval (rewrite Hp2a) in "Hpc".
    assert (Hasp : Macq !!! Regidx csp_rs1
                   = add_vec (m !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))
      by (rewrite (callee_saved_lookup Hacs csp_rs1 ltac:(vm_compute; reflexivity)); exact HP7sp).
    assert (Has2 : Macq !!! Regidx Rs2 = pj)
      by (rewrite (callee_saved_lookup Hacs Rs2 ltac:(vm_compute; reflexivity)); exact HP7s2).
    assert (Has7 : Macq !!! Regidx Rs7 = adr)
      by (rewrite (callee_saved_lookup Hacs Rs7 ltac:(vm_compute; reflexivity)); exact HP7s7).
    assert (Hacsr : kw_cs_rest Macq m) by (eapply kw_cs_rest_cs; [exact Hacs | exact HP7cs]).
    (* +0x2a c.li s4,5 ; +0x2c c.li s5,1 *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (KW + 0x2a)) Rs4 (mword_of_int 5 : mword 6)
              (mword_of_int 5 : mword 64) Macq (av - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi2a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (Q0 := <[Regidx Rs4 := regval_into_reg (mword_of_int 5 : mword 64)]> Macq).
    change (<[Regidx Rs4 := regval_into_reg (mword_of_int 5 : mword 64)]> Macq) with Q0.
    assert (Hp2c : add_vec_int (mword_of_int (KW + 0x2a) : mword 64) 2 = mword_of_int (KW + 0x2c)) by pcstep.
    iEval (rewrite Hp2c) in "Hpc".
    iApply (wp_cli_s_sconf Φ (mword_of_int (KW + 0x2c)) Rs5 (mword_of_int 1 : mword 6)
              (mword_of_int 1 : mword 64) Q0 (av - 10)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi2c [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (Q1 := <[Regidx Rs5 := regval_into_reg (mword_of_int 1 : mword 64)]> Q0).
    change (<[Regidx Rs5 := regval_into_reg (mword_of_int 1 : mword 64)]> Q0) with Q1.
    assert (Hp2e : add_vec_int (mword_of_int (KW + 0x2c) : mword 64) 2 = mword_of_int (KW + 0x2e)) by pcstep.
    iEval (rewrite Hp2e) in "Hpc".
    (* +0x2e/+0x32 s3 = &proc[NPROC] *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KW + 0x2e)) Rs3 (mword_of_int 22 : mword 20)
              Q1 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (Q2 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0x2e) : mword 64)
                     (auipc_off (mword_of_int 22 : mword 20)))]> Q1).
    change (<[Regidx Rs3 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0x2e) : mword 64)
                     (auipc_off (mword_of_int 22 : mword 20)))]> Q1) with Q2.
    assert (Hp32 : add_vec_int (mword_of_int (KW + 0x2e) : mword 64) 4 = mword_of_int (KW + 0x32)) by pcstep.
    iEval (rewrite Hp32) in "Hpc".
    assert (Hrg32 : rget (CID := CID19) Q2 Rs3 = Q2 !!! Regidx Rs3) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KW + 0x32)) Rs3 Rs3 (mword_of_int 4052 : mword 12)
              Q2 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi32 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hrg32) in "Hcg".
    set (Q3 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (Q2 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 4052 : mword 12)))]> Q2).
    change (<[Regidx Rs3 := regval_into_reg
                  (add_vec (Q2 !!! Regidx Rs3) (sign_extend' 64 (mword_of_int 4052 : mword 12)))]> Q2) with Q3.
    assert (HQ3s3 : Q3 !!! Regidx Rs3 = proc_addr NPROC).
    { rewrite /Q3 upd_eq /Q2 upd_eq. rewrite proc_addr_acur /pacur.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hp36 : add_vec_int (mword_of_int (KW + 0x32) : mword 64) 4 = mword_of_int (KW + 0x36)) by pcstep.
    iEval (rewrite Hp36) in "Hpc".
    (* +0x36/+0x3a s6 = &wait_lock *)
    iApply (wp_auipc_s_sconf Φ (mword_of_int (KW + 0x36)) Rs6 (mword_of_int 16 : mword 20)
              Q3 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (Q4 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0x36) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> Q3).
    change (<[Regidx Rs6 := regval_into_reg
                  (add_vec (mword_of_int (KW + 0x36) : mword 64)
                     (auipc_off (mword_of_int 16 : mword 20)))]> Q3) with Q4.
    assert (Hp3a : add_vec_int (mword_of_int (KW + 0x36) : mword 64) 4 = mword_of_int (KW + 0x3a)) by pcstep.
    iEval (rewrite Hp3a) in "Hpc".
    assert (Hrg3a : rget (CID := CID19) Q4 Rs6 = Q4 !!! Regidx Rs6) by (rgne; reflexivity).
    iApply (wp_addi4_s_sconf Φ (mword_of_int (KW + 0x3a)) Rs6 Rs6 (mword_of_int 436 : mword 12)
              Q4 (av - 10)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hrg3a) in "Hcg".
    set (Q5 := <[Regidx Rs6 := regval_into_reg
                  (add_vec (Q4 !!! Regidx Rs6) (sign_extend' 64 (mword_of_int 436 : mword 12)))]> Q4).
    change (<[Regidx Rs6 := regval_into_reg
                  (add_vec (Q4 !!! Regidx Rs6) (sign_extend' 64 (mword_of_int 436 : mword 12)))]> Q4) with Q5.
    assert (HQ5s6 : Q5 !!! Regidx Rs6 = wait_lock_addr).
    { rewrite /Q5 upd_eq /Q4 upd_eq /wait_lock_addr. apply bv_eq; vm_compute; reflexivity. }
    (* the round's register invariant, at the loop head *)
    assert (HQ5 : kw_round_regs Q5 m pj adr).
    { rewrite /kw_round_regs. split_and!.
      - rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
        rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
        rewrite /Q1 upd_ne; [| reg_neq]. rewrite /Q0 upd_ne; [| reg_neq]. exact Hasp.
      - rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
        rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
        rewrite /Q1 upd_ne; [| reg_neq]. rewrite /Q0 upd_ne; [| reg_neq]. exact Has2.
      - rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq]. exact HQ3s3.
      - rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
        rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
        rewrite /Q1 upd_ne; [| reg_neq]. rewrite /Q0 upd_eq. reflexivity.
      - rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
        rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
        rewrite /Q1 upd_eq. reflexivity.
      - exact HQ5s6.
      - rewrite /Q5 upd_ne; [| reg_neq]. rewrite /Q4 upd_ne; [| reg_neq].
        rewrite /Q3 upd_ne; [| reg_neq]. rewrite /Q2 upd_ne; [| reg_neq].
        rewrite /Q1 upd_ne; [| reg_neq]. rewrite /Q0 upd_ne; [| reg_neq]. exact Has7.
      - rewrite /Q5. apply kw_cs_rest_s6. rewrite /Q4. apply kw_cs_rest_s6.
        rewrite /Q3. apply kw_cs_rest_s3. rewrite /Q2. apply kw_cs_rest_s3.
        rewrite /Q1. apply kw_cs_rest_s5. rewrite /Q0. apply kw_cs_rest_s4.
        exact Hacsr. }
    assert (Hp3e : add_vec_int (mword_of_int (KW + 0x3a) : mword 64) 4 = mword_of_int (KW + 0x3e)) by pcstep.
    iEval (rewrite Hp3e) in "Hpc".
    (* +0x3e c.j +0xdc : into the outer loop *)
    iApply (wp_cj_s_sconf Φ (mword_of_int (KW + 0x3e))
              (sign_extend' 21 (concat_vec (mword_of_int 79 : mword 11) ('b"0")))
              Q5 (av - 10)%nat false ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi3e [-]").
    iApply wp_next_off_intro. iNext. iIntros "Hcg Hpc".
    assert (Htgdc : add_vec (mword_of_int (KW + 0x3e) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 79 : mword 11) ('b"0"))))
                    = mword_of_int (KW + 0xdc)) by pcstep.
    iEval (rewrite Htgdc) in "Hpc".
    (* ---- the caller's continuation, as [kw_exit_fn] at the CURRENT hart ---- *)
    iAssert (kw_exit_fn CID19 Φ γf m pj av eb C pid V (kw_rt pj j))
      with "[Hcont]" as "Hqfn".
    { rewrite /kw_exit_fn.
      iIntros (CIDx Hsx mf P' rv) "%Hcsx %Ha0x %Hextx Hcgx Hownx Hpcx Hprivx Hparkx".
      iSpecialize ("Hcont" $! CIDx with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf P' rv with "[%] [%] Hcgx Hownx Hpcx Hparkx Hprivx").
      { split; [exact Hcsx | exact Ha0x]. }
      { exact Hextx. } }
    (* ==================== THE OUTER LOOP (iLöb) ==================== *)
    iAssert (kw_round CID Φ γf γw j m pj adr av eb C pid V) with "[]" as "Hround".
    { iLöb as "IH". rewrite /kw_round.
      iIntros (CIDz Hsz N) "%Hrz Hcgz Hownz Hpayz Hpcz Htokz Hresz Hprivz Hframez Hrtz Hqfnz".
      iApply (kw_round_body (CIDy := CIDz) CID Φ γs γa γf γw γl j m N pj adr av eb C pid V
                Hav Heb Hj Hgl Hlen Hpjv Hsz Hrz
                with "Htext Hpinv Hscheds Hpanic Henv Hlk IH Hqfnz Hcgz Hownz Hpayz Hpcz
                      Htokz Hresz Hprivz Hframez Hrtz"). }
    rewrite /kw_round.
    (* the loop's own index is the literal [true] (sleep's crossing), while
       the prologue's chain is stated at [eb] -- [kw_chain_true] is the one
       step [wp_next_chain]'s [specialize] cannot take. *)
    iSpecialize ("Hround" $! CID19 with "[%]");
      [ apply (kw_chain_true eb pj CID19 CID Heb); wp_next_chain |].
    iApply ("Hround" $! Q5 with "[%] Hcg Hown Hpay Hpc Htok Hres Hpriv Hkframe
                                 [Hpark] Hqfn").
    { exact HQ5. }
    { rewrite /kw_rt. iFrame "Hpark". }
  Qed.

End ProofKwaitMain.

End KwaitProof.
