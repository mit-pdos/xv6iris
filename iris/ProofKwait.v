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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import StackOwn CalleeSaved.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode KernelBaseDecode.
Require Import VcGen WpAuipc.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSmodeIntr.
Require Import IntrDefs WpNext.
Require Import CpuOwn.
Require Import WpLock.
Require Import ArrCursor.
Require Import ProcGeom.
Require Import PageGeom.
Require Import KallocInv.
Require Import UptTree UserPtTree.
Require Import ProcPtOwn.
Require Import SwtchCtx.
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

Module KwaitProof (Acquire : ACQUIRE) (Release : RELEASE) (Myproc : MYPROC)
                  (Killed : KILLED) (Sleep : SLEEP)
                  (Copyout : COPYOUT) (Freeproc : FREEPROC).

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

End ProofKwait.
End KwaitProof.
