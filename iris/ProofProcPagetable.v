(* ProofProcPagetable.v -- whole-function proof of proc_pagetable
   (kernel/proc.c): a 4-slot frame, uvmcreate() for the empty root, then the
   TRAMPOLINE and TRAPFRAME mappages runs, then the epilogue.

   Straight-line under the counted page budget (4 free pages for a 3-page
   consumption): uvmcreate's null return and both mappages -1 returns are
   dead, so neither error tail -- which would call uvmfree / uvmunmap -- is
   ever reached.  The two failure arms are refuted arithmetically: the first
   run allocates at most an l1 + an l0 table ([pt_missing_1_le_2]) and the
   second allocates NOTHING, because TRAPFRAME sits one page below TRAMPOLINE
   and shares both of its groups ([ppt_missing_tf_zero]).

   EXPLICIT-CPUID: this function calls no acquire/release, so it never runs
   at a fixed SIE index -- it is [b]-GENERIC start to finish and EVERY plain
   instruction threads a fresh hart ([wp_next b], never the [wp_next_off]
   shortcut).  [Hcnt] (cpu_own) is refreshed for free at each of the three
   callees (uvmcreate, mappages x2, each hands back a fresh copy at its own
   exit hart) and needs [cpu_own_transport] across the four straight-line
   stretches in between (prologue, between uvmcreate and mappages#1, between
   the two mappages runs, and the epilogue).

   THE UVMCREATE TP PREMISE: [wp_uvmcreate_sconf_body] still asks for the RAW
   entry map's tp slot ([mm !!! Regidx 4 = cid_word]), the same shape SpecRelease
   keeps and SpecAcquire dropped -- an inconsistency across Spec files this
   sweep leaves in place, not something a consumer can paper over except by
   proving it.  [callee_saved] no longer says anything about tp, so nothing
   downstream can produce this fact about a raw map by chaining through a
   callee's postcondition.  The fix costs nothing physically: [tp_pin]
   overwrites a map's tp slot unconditionally, so calling uvmcreate at
   [Jp := tp_pin J] instead of [J] makes the premise true BY CONSTRUCTION
   ([upd_eq]) while every other register lookup on [Jp] still equals the one
   on [J] ([tp_pin] only touches slot 4) -- see [CpuOwn.cpu_own_eb_agree]-style
   reasoning in ProofAllocpid.v for the sibling situation with release.

   [kalloc_env] used to be tp-indexed too (KvmSpec.v's comment: "unused in
   the body, kept only because the whole chain's specs were stated
   tp-indexed... the parameter was pure noise") and is not any more, so the
   [Henv] rewrites that used to reconcile that vestigial index across the
   [mm]/[J] seam are gone outright, along with the tp-preservation chain
   ([Hmr0tp]/[HM9tp]/[Hmr1tp]/[HN8tp]) that fed them and the mappages calls'
   own (now nonexistent) tp premise. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore RegFile WpMmodeLeafBase.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import CpuOwn.
Require Import WpSmodeIntr WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import WpLock.
Require Import CalleeSaved StackOwn.
Require Import ProcGeom.
Require Import KallocInv.
Require Import PtBuild KptExecMap TrampPt.
Require Import PtreeType.
(* the epilogue block STATES [pc_is] / [ptree_own] / [kalloc_env] (through
   [ppt_post]) rather than only receiving them, so these come in directly. *)
Require Import InstrBytes.
Require Import KvmSpec.
Require Import PtreeType.
Require Import ProcPt.
Require Import CodeProcPagetable.
Require Import BarePt.
Require Import ProcPtOwn.
Require Import SpecUvmcreate SpecMappages SpecUvmfree SpecUvmunmap SpecProcPagetable.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

(* clean-context (mword-free) budget arithmetic: with an mword anywhere in
   the context the zify hook makes [lia] fail, so the whole-function proof
   applies these as closed facts. *)
Lemma ppt_cap_bounds (K : nat) : (40 <= K)%nat ->
  (4 <= K)%nat /\ (18 <= K - 4)%nat /\ (32 <= K - 4)%nat /\ (36 <= K - 4)%nat
  /\ (22 <= K - 4)%nat.
Proof. lia. Qed.

(* the consumption ledger, per-step [avail_sub]s recombined into one:
   uvmcreate's root, then each walk's nodes. *)
Lemma ppt_env_recomb (on : option nat) (g1 g2 : nat) :
  avail_sub (avail_sub (avail_sub on 1) g1) g2 = avail_sub on (1 + g1 + g2)%nat.
Proof. rewrite !avail_sub_add. reflexivity. Qed.

Lemma ppt_nodes_sum (n1 n2 g1 g2 : nat) :
  n1 = (1 + g1)%nat -> n2 = (n1 + g2)%nat -> n2 = (1 + g1 + g2)%nat.
Proof. lia. Qed.

Lemma ppt_nodes_le (g1 g2 : nat) :
  (g1 <= 2)%nat -> (g2 <= 0)%nat -> (1 + g1 + g2 <= K_proc_pagetable)%nat.
Proof. lia. Qed.


Lemma ppt_lt1 (i : nat) : (i < 1)%nat -> i = 0%nat.
Proof. lia. Qed.

(* the counted premise kills [ppt_post]'s failure arm, whatever the arm's
   witness [n] happens to be: the tail was reached because the allocator ran
   dry after [n <= 3] pages, and the caller promised more than 3 were free. *)
(* the exhaustion witness [ppt_post]'s failure arm wants, out of the one
   mappages hands back: the run consumed [1 + g] pages (uvmcreate's root plus
   the walk's [g]), and [g <= 2] because one TRAMPOLINE page needs at most an
   l1 and an l0. *)
Lemma ppt_fail_n1 (on : option nat) (g : nat) : (g <= 2)%nat ->
  avail_zero (avail_sub (avail_sub on 1) g) ->
  exists n : nat, (n <= K_proc_pagetable)%nat /\ avail_zero (avail_sub on n).
Proof.
  intros Hg Hz. exists (1 + g)%nat.
  split; [lia |]. rewrite avail_sub_add. exact Hz.
Qed.

Lemma ppt_fail_n2 (on : option nat) (g1 g2 : nat) : (g1 <= 2)%nat -> (g2 <= 0)%nat ->
  avail_zero (avail_sub (avail_sub (avail_sub on 1) g1) g2) ->
  exists n : nat, (n <= K_proc_pagetable)%nat /\ avail_zero (avail_sub on n).
Proof.
  intros H1 H2 Hz. exists (1 + g1 + g2)%nat.
  split; [lia |]. rewrite -ppt_env_recomb. exact Hz.
Qed.

Lemma ppt_fail_refute (nb n : nat) :
  (K_proc_pagetable < nb)%nat -> (n <= K_proc_pagetable)%nat ->
  avail_zero (avail_sub (Some nb) n) -> False.
Proof. rewrite avail_sub_Some. unfold avail_zero. lia. Qed.

Module ProcPagetableCore (UV : UVMCREATE) (MP : MAPPAGES)
                         (UF : UVMFREE) (UUF : UVMUNMAP_FIXED) : PROC_PAGETABLE_GEN.

Section ProofProcPagetable.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


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

  (* Discharge an [upd_ne] side goal inside a callee-saved TRANSPORT peel,
     where the register [c] is a VARIABLE constrained only by [is_cs_idx c =
     true] and by the four disequalities [ppt_thr] carries.  Either the
     written register is not callee-saved at all (then [Hc] refutes the
     equation) or it is one of the four this function writes (then the
     corresponding [c <> k] hypothesis does).  [vm_compute in
     Hc] on a variable [c] does nothing (claude-notes/durable-notes.md), and a
     bare [subst] is not an option either -- it would try to expand the
     [set]-bound register maps and fail with "N8 is used in hypothesis ...".
     So the index equation is pushed into [Hc] by [rewrite] instead.
     [congruence] would also close the second case, but it costs seconds
     apiece in this function's context; the four disequalities are passed in
     by name instead, so each is one [exact].

     ORDER MATTERS, AND NOT A LITTLE.  The four [exact]s must come FIRST.
     With the [rewrite]/[vm_compute]/[discriminate] branch leading, each of
     the four frame-register writes pays for that branch's FAILURE, and the
     cost of the failure grows with the proof term: ~1.3s per write at the
     prologue, ~10s per write in the epilogue -- 42s of the 46s this
     threading added to the file.  Leading with the [exact]s (which fail on a
     type mismatch, instantly) takes every peel in the function to
     milliseconds. *)
  Ltac thr_side Hc H2 H8 H9 H18 :=
    let Hx := fresh "Hx" in
    let Hx2 := fresh "Hx2" in
    intros Hx; injection Hx as Hx2;
    first [ exact (H2 Hx2) | exact (H8 Hx2) | exact (H9 Hx2) | exact (H18 Hx2)
          | rewrite Hx2 in Hc; vm_compute in Hc; discriminate ].

  (* [callee_saved mm m] minus the four frame registers proc_pagetable saves
     and restores itself (sp, s0, s1, s2), stated uniformly in the index so
     it can be THREADED: one [ppt_thr mm <map>] fact per callee boundary,
     each proved from the previous by a single [callee_saved_lookup] plus
     that stage's own short peel.  The alternative -- peeling [mr2] all the
     way back to [mm] in one tactic, once per concrete callee-saved index --
     does not survive factoring the epilogue out, because that peel walks
     through the [set]-bound tower and only terminates where the concrete
     index says it should. *)
  Definition ppt_thr (mm m : regfile) : Prop :=
    forall c : mword 5, is_cs_idx c = true ->
      c <> csp_rs1 ->
      c <> (mword_of_int 8 : mword 5) ->
      c <> (mword_of_int 9 : mword 5) ->
      c <> (mword_of_int 18 : mword 5) ->
      m !!! Regidx c = mm !!! Regidx c.

  (* One own-register write at a time.  Peeling the whole [set]-bound tower
     with [rewrite /M9 … /M1; repeat (rewrite upd_ne; [| thr_side Hc])] does
     NOT work: once every layer is unfolded, the WRITTEN VALUES contain
     lookups of their own (e.g. [N5]'s value is [add_vec (N4 !!! Regidx 11)
     …]), and [rewrite] picks the first match, which may be one of those --
     leaving a side goal about two concrete indices that [thr_side] cannot
     close.  Going one insert at a time keeps the redex unambiguous. *)
  Lemma ppt_thr_ins (mm m : regfile) (k : mword 5) (v : mword 64) :
    (forall c : mword 5, is_cs_idx c = true ->
       c <> csp_rs1 ->
       c <> (mword_of_int 8 : mword 5) ->
       c <> (mword_of_int 9 : mword 5) ->
       c <> (mword_of_int 18 : mword 5) -> Regidx c <> Regidx k) ->
    ppt_thr mm m -> ppt_thr mm (<[Regidx k := v]> m).
  Proof.
    intros Hk H c Hc H2 H8 H9 H18.
    rewrite upd_ne; [| exact (Hk c Hc H2 H8 H9 H18)]. apply H; assumption.
  Qed.

  Lemma ppt_thr_refl (mm : regfile) : ppt_thr mm mm.
  Proof. intros c _ _ _ _ _. reflexivity. Qed.

  (* unfold the head [set] variable, or peel one write; repeat *)
  Ltac thr_peel :=
    repeat first
      [ lazymatch goal with
        | |- ppt_thr _ ?M => is_var M; progress unfold M
        end
      | apply ppt_thr_ins;
        [ intros c Hc H2 H8 H9 H18; thr_side Hc H2 H8 H9 H18 |] ].

  Lemma wp_proc_pagetable_core (γa : gname)
      (mm : regfile) (tf : mword 64) (dqtf : dfrac) (lvl K : nat) (eb : bool)
      (p : mword 64) (on : option nat) (b : bool) (lks : gset string)
    : wp_proc_pagetable_core_body γa mm tf dqtf lvl K eb p on b lks.
  Proof.
    cbv beta delta [wp_proc_pagetable_core_body].
    intros pp tfp ret_tgt Hlvl HK Htfal Htfb Hlkbelow.
    pose proof (ppt_cap_bounds K HK) as (Hc4 & Hc18 & Hc32 & Hc36 & Hc22).
    set (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hcnt #Htext Hpc Htfcell Henv Hcont".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 4 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (ppti_00 with "Htext") as "Hi00".
    iPoseProof (ppti_02 with "Htext") as "Hi02".
    iPoseProof (ppti_04 with "Htext") as "Hi04".
    iPoseProof (ppti_06 with "Htext") as "Hi06".
    iPoseProof (ppti_08 with "Htext") as "Hi08".
    iPoseProof (ppti_0a with "Htext") as "Hi0a".
    iPoseProof (ppti_0c with "Htext") as "Hi0c".
    iPoseProof (ppti_0e with "Htext") as "Hi0e".
    iPoseProof (ppti_12 with "Htext") as "Hi12".
    iPoseProof (ppti_14 with "Htext") as "Hi14".
    iPoseProof (ppti_16 with "Htext") as "Hi16".
    iPoseProof (ppti_18 with "Htext") as "Hi18".
    iPoseProof (ppti_1c with "Htext") as "Hi1c".
    iPoseProof (ppti_20 with "Htext") as "Hi20".
    iPoseProof (ppti_22 with "Htext") as "Hi22".
    iPoseProof (ppti_26 with "Htext") as "Hi26".
    iPoseProof (ppti_28 with "Htext") as "Hi28".
    iPoseProof (ppti_2a with "Htext") as "Hi2a".
    iPoseProof (ppti_2e with "Htext") as "Hi2e".
    iPoseProof (ppti_32 with "Htext") as "Hi32".
    iPoseProof (ppti_34 with "Htext") as "Hi34".
    iPoseProof (ppti_38 with "Htext") as "Hi38".
    iPoseProof (ppti_3a with "Htext") as "Hi3a".
    iPoseProof (ppti_3e with "Htext") as "Hi3e".
    iPoseProof (ppti_40 with "Htext") as "Hi40".
    iPoseProof (ppti_42 with "Htext") as "Hi42".
    iPoseProof (ppti_44 with "Htext") as "Hi44".
    iPoseProof (ppti_48 with "Htext") as "Hi48".
    iPoseProof (ppti_4c with "Htext") as "Hi4c".
    iPoseProof (ppti_4e with "Htext") as "Hi4e".
    iPoseProof (ppti_50 with "Htext") as "Hi50".
    iPoseProof (ppti_52 with "Htext") as "Hi52".
    iPoseProof (ppti_54 with "Htext") as "Hi54".
    iPoseProof (ppti_56 with "Htext") as "Hi56".
    iPoseProof (ppti_58 with "Htext") as "Hi58".
    (* ---------------- prologue (generic b) ---------------- *)
    (* +0x00 addi sp,sp,-32 *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.proc_pagetable) (mword_of_int 32 : mword 6) mm K 4 b Hc4 Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    iDestruct "S3" as (v3) "Hc3". iDestruct "S4" as (v4) "Hc4".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr) by (rewrite /W1; rewrite upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.proc_pagetable : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 4)%nat v1 b with "Hcg Hpc Hi02 [Hc1]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1". iEval (rewrite HspW1 Hb1) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 4)%nat v2 b with "Hcg Hpc Hi04 [Hc2]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2". iEval (rewrite HspW1 Hb2) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 sd s1,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              W1 (K - 4)%nat v3 b with "Hcg Hpc Hi06 [Hc3]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc3". iEval (rewrite HspW1 Hb3) in "Hc3".
    assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HW1r9) in "Hc3".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 sd s2,0(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              W1 (K - 4)%nat v4 b with "Hcg Hpc Hi08 [Hc4]").
    { iEval (rewrite HspW1 Hb4). iExact "Hc4". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc4". iEval (rewrite HspW1 Hb4) in "Hc4".
    assert (HW1r18 : W1 !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HW1r18) in "Hc4".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* ================================================================= *)
    (*  THE SHARED EPILOGUE, +0x4c .. +0x58.                              *)
    (*                                                                    *)
    (*  FOUR exits converge on +0x4c.  uvmcreate's null return reaches it  *)
    (*  straight from the [beqz] at +0x14 (a0 had already been copied into *)
    (*  s1 at +0x12); the two mappages failure tails both end [li s1,0; j  *)
    (*  +0x4c]; the success path falls through the [bltz] at +0x48.  s1 IS *)
    (*  THE RETURN VALUE at that join -- +0x4c is [mv a0,s1] -- so the     *)
    (*  block is indexed by [rv] and carries [ppt_post] at that [rv].      *)
    (*  Everything the four exits disagree about lives in there and        *)
    (*  nowhere else; the eight instructions below are shared verbatim.    *)
    (*                                                                    *)
    (*  It is stated HERE, right after the frame stores, because that is   *)
    (*  where [Hc1..Hc4] (the saved registers the block reloads) first     *)
    (*  exist and the earliest exit is still four instructions away.       *)
    (* ================================================================= *)
    iAssert (wp_next b p (fun (CIDe : CpuId) =>
        ∀ (me : regfile) (rv : mword 64),
        ⌜ me !!! Regidx csp_rs1 = spr
          /\ me !!! Regidx (mword_of_int 9 : mword 5) = rv
          /\ ppt_thr mm me ⌝ -∗
        sie_cap_gpr me (K - 4)%nat b p -∗
        cpu_own lvl eb p b lks -∗
        pc_is (mword_of_int (KernelSyms.proc_pagetable + 0x4c) : mword 64) -∗
        p_trapframe pp ↦₈{dqtf} tf -∗
        ppt_post γa on tfp rv -∗
        WP (Loop : expr riscv_lang)))%I
      with "[Hcont Hc1 Hc2 Hc3 Hc4]" as "EPI".
    { iIntros (CIDe Hse me rv).
      iIntros "(%Hmesp & %Hmes1 & %Hmethr) Hcg Hcnt Hpc Htfcell Hpost".
      (* the instruction facts must be re-posed INSIDE with FRESH NAMES: the
         outer [iPoseProof]s are spatial and the [with "[...]"] selection
         does not carry them in (claude-notes/durable-notes.md). *)
      iPoseProof (ppti_4c with "Htext") as "Hj4c".
      iPoseProof (ppti_4e with "Htext") as "Hj4e".
      iPoseProof (ppti_50 with "Htext") as "Hj50".
      iPoseProof (ppti_52 with "Htext") as "Hj52".
      iPoseProof (ppti_54 with "Htext") as "Hj54".
      iPoseProof (ppti_56 with "Htext") as "Hj56".
      iPoseProof (ppti_58 with "Htext") as "Hj58".
      (* +0x4c mv a0,s1 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x4c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                me (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hj4c").
      iIntros (CID29 Hs29) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (E0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (me !!! Regidx (mword_of_int 9 : mword 5)))]> me).
      assert (Hp4e : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp4e) in "Hpc".
      assert (HE0sp : E0 !!! Regidx csp_rs1 = spr) by (rewrite /E0; rewrite upd_ne; [| reg_neq]; exact Hmesp).
      (* +0x4e ld ra,24(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x4e)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
                E0 (K - 4)%nat (mm !!! Regidx (mword_of_int 1 : mword 5)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hj4e [Hc1]").
      { iEval (rewrite HE0sp Hb1). iExact "Hc1". }
      iIntros (CID30 Hs30) "Hcg Hpc Hc1". iEval (rewrite HE0sp Hb1) in "Hc1".
      set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> E0).
      assert (Hp50 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp50) in "Hpc".
      assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1; rewrite upd_ne; [| reg_neq]; exact HE0sp).
      (* +0x50 ld s0,16(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x50)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
                E1 (K - 4)%nat (mm !!! Regidx (mword_of_int 8 : mword 5)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hj50 [Hc2]").
      { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
      iIntros (CID31 Hs31) "Hcg Hpc Hc2". iEval (rewrite HE1sp Hb2) in "Hc2".
      set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
      assert (Hp52 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x50) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp52) in "Hpc".
      assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2; rewrite upd_ne; [| reg_neq]; exact HE1sp).
      (* +0x52 ld s1,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x52)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
                E2 (K - 4)%nat (mm !!! Regidx (mword_of_int 9 : mword 5)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hj52 [Hc3]").
      { iEval (rewrite HE2sp Hb3). iExact "Hc3". }
      iIntros (CID32 Hs32) "Hcg Hpc Hc3". iEval (rewrite HE2sp Hb3) in "Hc3".
      set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
      assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x52) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp54) in "Hpc".
      assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3; rewrite upd_ne; [| reg_neq]; exact HE2sp).
      (* +0x54 ld s2,0(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x54)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
                E3 (K - 4)%nat (mm !!! Regidx (mword_of_int 18 : mword 5)) b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hj54 [Hc4]").
      { iEval (rewrite HE3sp Hb4). iExact "Hc4". }
      iIntros (CID33 Hs33) "Hcg Hpc Hc4". iEval (rewrite HE3sp Hb4) in "Hc4".
      set (E4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 18 : mword 5))]> E3).
      assert (Hp56 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp56) in "Hpc".
      assert (HE4sp : E4 !!! Regidx csp_rs1 = spr) by (rewrite /E4; rewrite upd_ne; [| reg_neq]; exact HE3sp).
      (* +0x56 addi sp,sp,32 -- the frame pop *)
      set (E5 := <[Regidx csp_rs1 := regval_into_reg
          (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4).
      assert (Hwv : add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
      { rewrite HE4sp. unfold spr. apply frame_cancel_32. }
      assert (Hpop : E4 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
      { rewrite Hwv HE4sp. symmetry. exact Hsprstk. }
      iAssert (stack_own sp0 4) with "[Hc1 Hc2 Hc3 Hc4]" as "Hframe".
      { rewrite stack_own_slots. cbn [seq].
        iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
        iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
        iSplitL "Hc3". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc3". }
        iSplitL "Hc4". { iExists (mm !!! Regidx (mword_of_int 18)). iExact "Hc4". }
        done. }
      iEval (rewrite -Hwv) in "Hframe".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x56)) (mword_of_int 2 : mword 6)
                E4 (K - 4)%nat 4 b Hpop with "Hcg Hpc Hj56 Hframe").
      iIntros (CID34 Hs34) "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E4 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E4) with E5.
      assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
      iEval (rewrite Hnk) in "Hcg".
      assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp58) in "Hpc".
      (* +0x58 ret *)
      assert (HE5ra : E5 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by peel_reg.
      assert (Hrt : ret_pc (E5 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt) by (rewrite HE5ra; reflexivity).
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x58)) (mword_of_int 1 : mword 5) E5 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hj58").
      iIntros (CID35 Hs35) "Hcg Hpc".
      iEval (rgne) in "Hpc".
      iEval (rewrite Hrt) in "Hpc".
      (* a0 = s1 = rv, so [ppt_post] rides through unexamined -- which is
         what makes ONE epilogue serve all four exits. *)
      assert (HE5a0 : E5 !!! Regidx (mword_of_int 10 : mword 5) = rv).
      { rewrite /E5. rewrite upd_ne; [| reg_neq]. rewrite /E4. rewrite upd_ne; [| reg_neq].
        rewrite /E3. rewrite upd_ne; [| reg_neq]. rewrite /E2. rewrite upd_ne; [| reg_neq].
        rewrite /E1. rewrite upd_ne; [| reg_neq]. rewrite /E0 upd_eq. rewrite add_vec_zero_l.
        exact Hmes1. }
      iEval (rewrite -HE5a0) in "Hpost".
      iDestruct (cpu_own_transport CIDe CID35 lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CID35 with "[]"); [ iPureIntro; wp_next_chain | ].
      iApply ("Hcont" $! E5 with "Hcg Hcnt Hpc Htfcell Hpost [%]").
      { (* callee_saved mm E5 *)
        (* the four frame registers are restored explicitly from the stack;
           everything else callee-saved rides the threaded [ppt_thr]. *)
        assert (HE5thr : ppt_thr mm E5).
        { thr_peel. exact Hmethr. }
        unfold callee_saved.
        split. { rewrite /E5 upd_eq. rewrite HE4sp. unfold spr. apply frame_cancel_32. }
        split. { rewrite /E5 /E4 /E3. repeat (rewrite upd_ne; [| reg_neq]). rewrite /E2 upd_eq. reflexivity. }
        split. { rewrite /E5 /E4. repeat (rewrite upd_ne; [| reg_neq]). rewrite /E3 upd_eq. reflexivity. }
        split. { rewrite /E5. rewrite upd_ne; [| reg_neq]. rewrite /E4 upd_eq. reflexivity. }
        repeat split;
          apply HE5thr; first [ vm_compute; reflexivity | vm_compute; discriminate ]. } }
    (* +0x0a addi s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> W1).
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c mv s2,a0 : s2 := p *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x0c)) (mword_of_int 18 : mword 5) (mword_of_int 10 : mword 5)
              W2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (W3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (add_vec zero_reg (W2 !!! Regidx (mword_of_int 10 : mword 5)))]> W2).
    assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    (* +0x0e jal uvmcreate *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x0e)) (mword_of_int 1 : mword 5) (mword_of_int 2094990 : mword 21)
              W3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x0e) : mword 64) 4)]> W3).
    assert (Htgtu : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x0e) : mword 64) (sign_extend' 64 (mword_of_int 2094990 : mword 21)) = mword_of_int KernelSyms.uvmcreate) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtu) in "Hpc".
    assert (HJsp : J !!! Regidx csp_rs1 = spr).
    { rewrite /J /W3 /W2. repeat (rewrite upd_ne; [| reg_neq]). exact HspW1. }
    assert (HJ18 : J !!! Regidx (mword_of_int 18 : mword 5) = pp).
    { rewrite /J. rewrite upd_ne; [| reg_neq]. rewrite /W3 upd_eq.
      rewrite add_vec_zero_l. rewrite /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HJthr : ppt_thr mm J).
    { thr_peel. apply ppt_thr_refl. }
    (* [J]'s own tp slot is whatever [mm]'s was -- uvmcreate's contract still
       wants the raw fact ⌜tp = cid_word⌝ (SpecRelease's shape, not
       SpecAcquire's), which nothing hands us any more.  Calling at
       [Jp := tp_pin J] instead settles it BY CONSTRUCTION and costs nothing:
       [Jp] agrees with [J] on sp ([tp_pin_sp]) and on any other concrete
       register ([rget_ne]), so [sie_cap_gpr]/[callee_saved] survive the
       swap. *)
    set (Jp := tp_pin J).
    assert (Hpinidem : tp_pin Jp = tp_pin J).
    { rewrite /Jp. apply (tp_pin_id (tp_pin J) (rget_tp J)). }
    assert (Hjpsp : Jp !!! Regidx csp_rs1 = J !!! Regidx csp_rs1).
    { rewrite /Jp. exact (tp_pin_sp J). }
    assert (Hgpreq : sie_cap_gpr J (K - 4)%nat b p = sie_cap_gpr Jp (K - 4)%nat b p).
    { unfold sie_cap_gpr, sie_cap. rewrite Hjpsp Hpinidem. reflexivity. }
    iEval (rewrite Hgpreq) in "Hcg".
    assert (HcidJp : Jp !!! Regidx (mword_of_int 4 : mword 5) = cid_word)
      by (rewrite /Jp upd_eq; reflexivity).
    assert (HJpsp : Jp !!! Regidx csp_rs1 = spr) by (rewrite Hjpsp; exact HJsp).
    assert (Hjp18 : Jp !!! Regidx (mword_of_int 18 : mword 5) = J !!! Regidx (mword_of_int 18 : mword 5)).
    { rewrite /Jp. apply (rget_ne J (mword_of_int 18) ltac:(vm_compute; discriminate)). }
    assert (HJp18 : Jp !!! Regidx (mword_of_int 18 : mword 5) = pp) by (rewrite Hjp18; exact HJ18).
    (* generic non-tp bridge Jp -> J, restated with a plain [Jp !!! Regidx r]
       LHS (rather than through [rget]) so it is usable by ordinary
       [rewrite] at an arbitrary literal register, not just [apply]/[exact]. *)
    assert (HJp_ne : forall r : mword 5, Regidx r <> Regidx Rtp -> Jp !!! Regidx r = J !!! Regidx r).
    { intros r Hr. rewrite /Jp. apply (rget_ne J r Hr). }
    (* [tp_pin] touches slot 4 only, and tp is NOT callee-saved, so the
       transport crosses the pin for free. *)
    assert (HJpthr : ppt_thr mm Jp).
    { intros c Hc H2 H8 H9 H18.
      rewrite (HJp_ne c (not_eq_sym (is_cs_idx_true_neq Rtp c
                 ltac:(vm_compute; reflexivity) Hc))).
      apply HJthr; assumption. }
    (* the eight plain instructions above have each moved to a fresh hart,
       so uvmcreate wants [Hcnt] at CID8. *)
    iDestruct (cpu_own_transport CID CID8 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (UV.wp_uvmcreate_sconf γa Jp lvl (K - 4)%nat eb p on b
              _ Hlvl Hc18 HcidJp
              with "Hcg Hcnt Htext Hpc Henv").
    all: try lkbelow.
    iIntros (CIDuv Hsuv mr0) "Hcg Hcnt Hpc %Hucs Hpost".
    assert (Hjpra : Jp !!! Regidx (mword_of_int 1 : mword 5) = J !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Jp. apply (rget_ne J (mword_of_int 1) ltac:(vm_compute; discriminate)). }
    assert (Hret12 : ret_pc (Jp !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.proc_pagetable + 0x12)).
    { rewrite Hjpra /J upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret12) in "Hpc".
    set (root0 := mr0 !!! Regidx (mword_of_int 10 : mword 5)).
    assert (Hmr0sp : mr0 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hucs csp_rs1 ltac:(vm_compute; reflexivity)). exact HJpsp. }
    assert (Hmr018 : mr0 !!! Regidx (mword_of_int 18 : mword 5) = pp).
    { rewrite (callee_saved_lookup Hucs (mword_of_int 18) ltac:(vm_compute; reflexivity)). exact HJp18. }
    assert (Hmr0thr : ppt_thr mm mr0).
    { intros c Hc H2 H8 H9 H18.
      rewrite (callee_saved_lookup Hucs c Hc). apply HJpthr; assumption. }
    (* +0x12 mv s1,a0 -- BOTH arms run it; the null return is what makes
       [s1 = 0] the return value the shared epilogue then moves into a0. *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x12)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mr0 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12").
    iIntros (CID9 Hs9) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (mr0 !!! Regidx (mword_of_int 10 : mword 5)))]> mr0).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    assert (HM1a0 : M1 !!! Regidx (mword_of_int 10 : mword 5) = root0)
      by (rewrite /M1; rewrite upd_ne; [reflexivity | reg_neq]).
    assert (HM1sp : M1 !!! Regidx csp_rs1 = spr)
      by (rewrite /M1; rewrite upd_ne; [exact Hmr0sp | reg_neq]).
    assert (HM1thr : ppt_thr mm M1) by (thr_peel; exact Hmr0thr).
    assert (Hnz : (zero_reg : mword 64) = nullp) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hz0 : (zero_reg : mword 64) = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
    iDestruct "Hpost" as "[(%Hrv0 & %Hav0 & Henv) | (%b0 & %Hroot0 & %Hpv0 & Hptree & Henv)]".
    { (* ============================================================== *)
      (*  EXIT #1: uvmcreate's kalloc came back null.                    *)
      (*  There is no tail code at all -- the [beqz] at +0x14 lands       *)
      (*  straight on +0x4c, and s1 already holds the 0 that +0x4c moves  *)
      (*  into a0.  Nothing was allocated, so nothing is owed; the        *)
      (*  environment is resealed only to match [ppt_post]'s failure arm  *)
      (*  (which the tails, that DO call uvmfree, force to be at [None]). *)
      (* ============================================================== *)
      (* [Hrv0] came out of the destruct with [root0] FOLDED (the [set] had
         already run), but unfolding [M1] exposes the raw lookup -- so keep
         both forms. *)
      assert (Hrv0' : mr0 !!! Regidx (mword_of_int 10 : mword 5) = (zero_reg : mword 64))
        by exact Hrv0.
      assert (HM1s1 : M1 !!! Regidx (mword_of_int 9 : mword 5) = (mword_of_int 0 : mword 64)).
      { rewrite /M1 upd_eq. rewrite add_vec_zero_l. rewrite Hrv0'. exact Hz0. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x14)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                M1 (K - 4)%nat b
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HM1a0; rewrite Hrv0; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi14").
      iApply bi.later_intro. iIntros (CIDd1 Hsd1) "Hcg Hpc".
      assert (Htg4c0 : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x14) : mword 64)
                         (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.proc_pagetable + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htg4c0) in "Hpc".
      iMod (kalloc_env_seal with "Henv") as "#Henv0".
      iDestruct (cpu_own_transport CIDuv CIDd1 lvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("EPI" $! CIDd1 with "[%]"); [wp_next_chain|].
      iApply ("EPI" $! M1 (mword_of_int 0 : mword 64) with "[%] Hcg Hcnt Hpc Htfcell []").
      { split_and!; [exact HM1sp | exact HM1s1 | exact HM1thr]. }
      { iRight. iFrame "Henv0". iPureIntro; split_and!; [reflexivity |].
        exists 0%nat. split; [lia |].
        rewrite avail_sub_0. exact Hav0. } }
    assert (Hroot0r : root0 = zero_extend' 64 (concat_vec b0 (zeros' 12 : mword 12)))
      by exact Hroot0.
    (* +0x14 beqz a0 -- FALLS: uvmcreate returned a valid page *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x14)) (mword_of_int 28 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              M1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite HM1a0; apply eq_vec_false_iff; rewrite Hnz;
                    exact (page_valid_ne_null _ Hpv0))
              with "Hcg Hpc Hi14").
    iIntros (CID10 Hs10) "Hcg Hpc".
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* ------- TRAMPOLINE group (+0x16 .. +0x2a) ------- *)
    (* +0x16 li a4,10 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x16)) (mword_of_int 14 : mword 5) (mword_of_int 10 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 10 : mword 6))))
              M1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi16").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (M2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 10 : mword 6))))]> M1).
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18 auipc a3,0x4 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x18)) (mword_of_int 13 : mword 5) (mword_of_int 4 : mword 20)
              M2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi18").
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (M3 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x18)) (auipc_off (mword_of_int 4 : mword 20)))]> M2).
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.proc_pagetable + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    (* +0x1c addi a3,a3,1498 -> trampoline *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x1c)) (mword_of_int 13 : mword 5) (mword_of_int 13 : mword 5) (mword_of_int 1528 : mword 12)
              M3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi1c").
    iIntros (CID13 Hs13) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M4 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec (M3 !!! Regidx (mword_of_int 13 : mword 5)) (sign_extend' 64 (mword_of_int 1528 : mword 12)))]> M3).
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.proc_pagetable + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    (* +0x20 lui a2,0x1 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x20)) (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              M4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi20").
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (M5 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> M4).
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    (* +0x22 lui a1,0x4000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x22)) (mword_of_int 11 : mword 5) (mword_of_int 16384 : mword 20) (luival (mword_of_int 16384 : mword 20))
              M5 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi22").
    iIntros (CID15 Hs15) "Hcg Hpc".
    set (M6 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (luival (mword_of_int 16384 : mword 20))]> M5).
    assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x22) : mword 64) 4 = mword_of_int (KernelSyms.proc_pagetable + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26 addi a1,a1,-1 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x26)) (mword_of_int 11 : mword 5) (mword_of_int 63 : mword 6)
              M6 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi26").
    iIntros (CID16 Hs16) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M7 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (M6 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> M6).
    assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    (* +0x28 slli a1,a1,12 -> TRAMPOLINE *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x28)) (Regidx (mword_of_int 11 : mword 5)) (mword_of_int 11 : mword 5) (mword_of_int 12 : mword 6)
              M7 (K - 4)%nat b eq_refl ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi28").
    iIntros (CID17 Hs17) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M8 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (shift_bits_left (M7 !!! Regidx (mword_of_int 11 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> M7).
    assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    (* +0x2a jal mappages *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x2a)) (mword_of_int 1 : mword 5) (mword_of_int 2094538 : mword 21)
              M8 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi2a").
    iIntros (CID18 Hs18) "Hcg Hpc".
    set (M9 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x2a) : mword 64) 4)]> M8).
    assert (Htgtm1 : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x2a) : mword 64) (sign_extend' 64 (mword_of_int 2094538 : mword 21)) = mword_of_int KernelSyms.mappages) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtm1) in "Hpc".
    (* the argument column for mappages #1 *)
    assert (HM9a0 : M9 !!! Regidx (mword_of_int 10 : mword 5) = root0).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2. repeat (rewrite upd_ne; [| reg_neq]). exact HM1a0. }
    assert (HM9a1 : M9 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int 0x3FFFFFF000).
    { rewrite /M9 /M8. repeat (rewrite upd_ne; [| reg_neq]). rewrite upd_eq.
      rewrite /M7 upd_eq. rewrite /M6 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HM9a2 : M9 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int (Z.of_nat 1 * 4096)).
    { rewrite /M9 /M8 /M7 /M6. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M5 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HM9a3 : M9 !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int 0x80006000).
    { rewrite /M9 /M8 /M7 /M6 /M5. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M4 upd_eq.
      rewrite /M3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HM9a4 : M9 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 10).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4 /M3. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M2 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HM918 : M9 !!! Regidx (mword_of_int 18 : mword 5) = pp).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr018. }
    assert (HM9s1 : M9 !!! Regidx (mword_of_int 9 : mword 5) = root0).
    { rewrite /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2. repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /M1 upd_eq. rewrite add_vec_zero_l. reflexivity. }
    assert (HM9thr : ppt_thr mm M9).
    { thr_peel. exact Hmr0thr. }
    assert (Hsvpn1 : svpn_of (M9 !!! Regidx (mword_of_int 11 : mword 5)) = tramp_vpn)
      by (rewrite HM9a1; apply bv_eq; vm_compute; reflexivity).
    assert (Hppn1 : (autocast (T := mword) (subrange_vec_dec (M9 !!! Regidx (mword_of_int 13 : mword 5)) 55 12) : mword 44) = tramp_ppn)
      by (rewrite HM9a3; apply bv_eq; vm_compute; reflexivity).
    (* the seven plain instructions since uvmcreate's return have each moved
       to a fresh hart, so mappages wants [Hcnt] at CID18. *)
    iDestruct (cpu_own_transport CIDuv CID18 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (MP.wp_mappages_sconf γa M9 (pt_empty_node b0) ∅ 1 10 lvl (K - 4)%nat eb p (avail_sub on 1) b
              _ Hlvl Hc32
              ltac:(rewrite HM9a0; exact Hroot0r)
              ltac:(rewrite HM9a1; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HM9a3; apply bv_eq; vm_compute; reflexivity)
              HM9a2 (Nat.le_refl 1) HM9a4 ppt_perm_ok10
              ltac:(rewrite HM9a1; rewrite uint_unsigned; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
              ltac:(rewrite HM9a3; rewrite uint_unsigned; apply (proj1 (Z.ltb_lt _ _)); vm_compute; reflexivity)
              (pt_rep0_empty b0)
              ltac:(intros i Hi; apply lookup_empty)
              with "Hcg Hcnt Htext Hpc Hptree Henv").
    all: try lkbelow.
    iIntros (CIDmp1 Hsmp1 mr1 t1 k1 g1) "Hcg Hcnt Hpc Hptree %Hnodes1 Henv %Hcs1 %Hbase1 %Hrep1 %Hmono1 %Hg1miss %Hret1".
    assert (Hretm1 : ret_pc (M9 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.proc_pagetable + 0x2e)).
    { rewrite /M9 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretm1) in "Hpc".
    (* the budget refutes the -1 arm *)
    assert (Hg1 : (g1 <= 2)%nat).
    { apply (Nat.le_trans _ _ _ Hg1miss). rewrite Hsvpn1. apply pt_missing_1_le_2. }
    (* the register column at mappages#1's return -- needed by BOTH arms, so
       it is established before the split. *)
    assert (Hmr1sp : mr1 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /M9 /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr0sp. }
    assert (Hmr118 : mr1 !!! Regidx (mword_of_int 18 : mword 5) = pp).
    { rewrite (callee_saved_lookup Hcs1 (mword_of_int 18) ltac:(vm_compute; reflexivity)). exact HM918. }
    assert (Hmr1s1 : mr1 !!! Regidx (mword_of_int 9 : mword 5) = root0).
    { rewrite (callee_saved_lookup Hcs1 (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact HM9s1. }
    assert (Hmr1thr : ppt_thr mm mr1).
    { intros c Hc H2 H8 H9 H18.
      rewrite (callee_saved_lookup Hcs1 c Hc). apply HM9thr; assumption. }
    destruct Hret1 as [(Hk1e & Hmr1a0) | (Hlt1 & Hmr1a0 & Havz1)].
    2:{ (* ============================================================== *)
        (*  TAIL #1, +0x5a: the TRAMPOLINE run failed.                     *)
        (*  npages is 1 and [k1 < 1], so NOTHING was mapped -- the map is  *)
        (*  still empty.  The walk may nevertheless have allocated an l1   *)
        (*  before running dry, which is why the tree cannot simply be     *)
        (*  dropped: [t1] is a bare table with no leaves, and              *)
        (*  uvmfree(pagetable, 0) is exactly the call that frees one.      *)
        (* ============================================================== *)
        assert (Hk10 : k1 = 0%nat) by (apply ppt_lt1; exact Hlt1). subst k1.
        iPoseProof (ppti_5a with "Htext") as "Hj5a".
        iPoseProof (ppti_5c with "Htext") as "Hj5c".
        iPoseProof (ppti_5e with "Htext") as "Hj5e".
        iPoseProof (ppti_62 with "Htext") as "Hj62".
        iPoseProof (ppti_64 with "Htext") as "Hj64".
        (* +0x2e bltz a0 -- TAKEN *)
        iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x2e)) (mword_of_int 44 : mword 13) (mword_of_int 10 : mword 5)
                  mr1 (K - 4)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite Hmr1a0; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi2e").
        iApply bi.later_intro. iIntros (CIDa1 Hsa1) "Hcg Hpc".
        assert (Htg5a : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x2e) : mword 64) (sign_extend' 64 (mword_of_int 44 : mword 13))
                        = mword_of_int (KernelSyms.proc_pagetable + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htg5a) in "Hpc".
        (* +0x5a li a1,0 : uvmfree(pagetable, 0) *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x5a)) (mword_of_int 11 : mword 5)
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  mr1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hj5a").
        iIntros (CIDa2 Hsa2) "Hcg Hpc".
        set (T1 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> mr1).
        assert (Hq5c : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x5c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq5c) in "Hpc".
        (* +0x5c mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x5c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                  T1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hj5c").
        iIntros (CIDa3 Hsa3) "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (T2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (T1 !!! Regidx (mword_of_int 9 : mword 5)))]> T1).
        assert (Hq5e : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x5c) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x5e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq5e) in "Hpc".
        (* +0x5e jal uvmfree *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x5e)) (mword_of_int 1 : mword 5) (mword_of_int 2095416 : mword 21)
                  T2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hj5e").
        iIntros (CIDa4 Hsa4) "Hcg Hpc".
        set (T3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x5e) : mword 64) 4)]> T2).
        assert (Htgtuf : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x5e) : mword 64) (sign_extend' 64 (mword_of_int 2095416 : mword 21))
                         = mword_of_int KernelSyms.uvmfree) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtuf) in "Hpc".
        assert (HT3a0 : T3 !!! Regidx (mword_of_int 10 : mword 5) = page_base b0).
        { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_eq. rewrite add_vec_zero_l.
          rewrite /T1 upd_ne; [| reg_neq]. rewrite Hmr1s1. exact Hroot0r. }
        assert (HT3a1 : T3 !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 0 : mword 64)).
        { rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq]. rewrite /T1 upd_eq. reflexivity. }
        assert (HT3sp : T3 !!! Regidx csp_rs1 = spr).
        { rewrite /T3 /T2 /T1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr1sp. }
        assert (HT3s1 : T3 !!! Regidx (mword_of_int 9 : mword 5) = root0).
        { rewrite /T3 /T2 /T1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr1s1. }
        assert (HT3thr : ppt_thr mm T3) by (thr_peel; exact Hmr1thr).
        assert (HT3ra : T3 !!! Regidx (mword_of_int 1 : mword 5)
                        = add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x5e) : mword 64) 4)
          by (rewrite /T3 upd_eq; reflexivity).
        (* the tree, at uvmfree's altitude: no leaves at all *)
        iDestruct (uptg_of_rep0_empty b0 t1 Hrep1 Hbase1 with "Hptree") as "Hbare".
        (* uvmfree is a [None]-only callee, so the count goes here for good *)
        iMod (kalloc_env_seal with "Henv") as "#Henv0".
        iDestruct (cpu_own_transport CIDmp1 CIDa4 lvl eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iApply (UF.wp_uvmfree_sconf γa T3 b0 ∅ (K - 4)%nat eb p lvl b
                  _ Hc36 Hlvl HT3a0
                  ltac:(rewrite HT3a1; unfold uvm_maxsz;
                        rewrite uint_unsigned; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
                  ltac:(rewrite dom_empty_L; apply empty_subseteq)
                  with "Hcg Hcnt Htext Hpc Hbare Henv0").
        all: try lkbelow.
        iIntros (CIDa5 Hsa5 mr3) "Hcg Hcnt Hpc %Hcsuf".
        assert (Hret62 : ret_pc (T3 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.proc_pagetable + 0x62)).
        { rewrite HT3ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hret62) in "Hpc".
        (* +0x62 li s1,0 : the return value *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x62)) (mword_of_int 9 : mword 5)
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  mr3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hj62").
        iIntros (CIDa6 Hsa6) "Hcg Hpc".
        set (U1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> mr3).
        assert (Hq64 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x62) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x64))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq64) in "Hpc".
        (* +0x64 j +0x4c -- into the shared epilogue *)
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x64))
                  (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0")))
                  U1 (K - 4)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hj64").
        iIntros (CIDa7 Hsa7). iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Htg4c : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x64) : mword 64)
                          (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2036 : mword 11) ('b"0"))))
                        = mword_of_int (KernelSyms.proc_pagetable + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htg4c) in "Hpc".
        assert (HU1sp : U1 !!! Regidx csp_rs1 = spr).
        { rewrite /U1 upd_ne; [| reg_neq].
          rewrite (callee_saved_lookup Hcsuf csp_rs1 ltac:(vm_compute; reflexivity)). exact HT3sp. }
        assert (HU1s1 : U1 !!! Regidx (mword_of_int 9 : mword 5) = (mword_of_int 0 : mword 64))
          by (rewrite /U1 upd_eq; reflexivity).
        assert (HU1thr : ppt_thr mm U1).
        { thr_peel. intros c Hc H2 H8 H9 H18.
          rewrite (callee_saved_lookup Hcsuf c Hc). apply HT3thr; assumption. }
        iDestruct (cpu_own_transport CIDa5 CIDa7 lvl eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("EPI" $! CIDa7 with "[%]"); [wp_next_chain|].
        iApply ("EPI" $! U1 (mword_of_int 0 : mword 64) with "[%] Hcg Hcnt Hpc Htfcell []").
        { split_and!; [exact HU1sp | exact HU1s1 | exact HU1thr]. }
        { iRight. iFrame "Henv0". iPureIntro; split_and!;
            [ reflexivity | exact (ppt_fail_n1 on g1 Hg1 Havz1) ]. } }
    subst k1.
    rewrite Hsvpn1 Hppn1 in Hrep1.
    (* +0x2e bltz a0 -- FALLS: mappages returned 0 *)
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x2e)) (mword_of_int 44 : mword 13) (mword_of_int 10 : mword 5)
              mr1 (K - 4)%nat b ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Hmr1a0; vm_compute; reflexivity)
              with "Hcg Hpc Hi2e").
    iIntros (CID19 Hs19) "Hcg Hpc".
    assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x2e) : mword 64) 4 = mword_of_int (KernelSyms.proc_pagetable + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    (* ------- TRAPFRAME group (+0x32 .. +0x44) ------- *)
    (* +0x32 li a4,6 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x32)) (mword_of_int 14 : mword 5) (mword_of_int 6 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))
              mr1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi32").
    iIntros (CID20 Hs20) "Hcg Hpc".
    set (N1 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))]> mr1).
    assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    (* +0x34 ld a3,88(s2) : a3 := p->trapframe *)
    assert (HN118 : N1 !!! Regidx (mword_of_int 18 : mword 5) = pp)
      by (rewrite /N1; rewrite upd_ne; [exact Hmr118 | reg_neq]).
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x34)) (mword_of_int 13 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 88 : mword 12)
              N1 (K - 4)%nat tf b (dqm := dqtf)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi34 [Htfcell]").
    { iEval (rgne; rewrite HN118). unfold p_trapframe in *. iExact "Htfcell". }
    iIntros (CID21 Hs21) "Hcg Hpc Htfcell". iEval (rgne; rewrite HN118) in "Htfcell".
    set (N2 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg tf]> N1).
    assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.proc_pagetable + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp38) in "Hpc".
    (* +0x38 lui a2,0x1 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x38)) (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              N2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi38").
    iIntros (CID22 Hs22) "Hcg Hpc".
    set (N3 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> N2).
    assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    (* +0x3a lui a1,0x2000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x3a)) (mword_of_int 11 : mword 5) (mword_of_int 8192 : mword 20) (luival (mword_of_int 8192 : mword 20))
              N3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi3a").
    iIntros (CID23 Hs23) "Hcg Hpc".
    set (N4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (luival (mword_of_int 8192 : mword 20))]> N3).
    assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.proc_pagetable + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3e) in "Hpc".
    (* +0x3e addi a1,a1,-1 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x3e)) (mword_of_int 11 : mword 5) (mword_of_int 63 : mword 6)
              N4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi3e").
    iIntros (CID24 Hs24) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (N5 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (N4 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> N4).
    assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp40) in "Hpc".
    (* +0x40 slli a1,a1,13 -> TRAPFRAME *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x40)) (Regidx (mword_of_int 11 : mword 5)) (mword_of_int 11 : mword 5) (mword_of_int 13 : mword 6)
              N5 (K - 4)%nat b eq_refl ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi40").
    iIntros (CID25 Hs25) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (N6 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (shift_bits_left (N5 !!! Regidx (mword_of_int 11 : mword 5)) (subrange_vec_dec (mword_of_int 13 : mword 6) (Z.sub log2_xlen 1) 0))]> N5).
    assert (Hp42 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp42) in "Hpc".
    (* +0x42 mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x42)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              N6 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42").
    iIntros (CID26 Hs26) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (N7 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (N6 !!! Regidx (mword_of_int 9 : mword 5)))]> N6).
    assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp44) in "Hpc".
    (* +0x44 jal mappages *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x44)) (mword_of_int 1 : mword 5) (mword_of_int 2094512 : mword 21)
              N7 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi44").
    iIntros (CID27 Hs27) "Hcg Hpc".
    set (N8 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x44) : mword 64) 4)]> N7).
    assert (Htgtm2 : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x44) : mword 64) (sign_extend' 64 (mword_of_int 2094512 : mword 21)) = mword_of_int KernelSyms.mappages) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtm2) in "Hpc".
    (* the argument column for mappages #2 *)
    assert (HN8a0 : N8 !!! Regidx (mword_of_int 10 : mword 5) = root0).
    { rewrite /N8. rewrite upd_ne; [| reg_neq]. rewrite /N7 upd_eq. rewrite add_vec_zero_l.
      rewrite /N6 /N5 /N4 /N3 /N2 /N1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr1s1. }
    assert (HN8a1 : N8 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int 0x3FFFFFE000).
    { rewrite /N8 /N7. repeat (rewrite upd_ne; [| reg_neq]). rewrite /N6 upd_eq.
      rewrite /N5 upd_eq. rewrite /N4 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HN8a2 : N8 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int (Z.of_nat 1 * 4096)).
    { rewrite /N8 /N7 /N6 /N5 /N4. repeat (rewrite upd_ne; [| reg_neq]). rewrite /N3 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HN8a3 : N8 !!! Regidx (mword_of_int 13 : mword 5) = tf).
    { rewrite /N8 /N7 /N6 /N5 /N4 /N3. repeat (rewrite upd_ne; [| reg_neq]). rewrite /N2 upd_eq. reflexivity. }
    assert (HN8a4 : N8 !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 6).
    { rewrite /N8 /N7 /N6 /N5 /N4 /N3 /N2. repeat (rewrite upd_ne; [| reg_neq]). rewrite /N1 upd_eq.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HN8s1 : N8 !!! Regidx (mword_of_int 9 : mword 5) = root0).
    { rewrite /N8 /N7 /N6 /N5 /N4 /N3 /N2 /N1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr1s1. }
    assert (HN8thr : ppt_thr mm N8).
    { thr_peel. exact Hmr1thr. }
    assert (Hsvpn2 : svpn_of (N8 !!! Regidx (mword_of_int 11 : mword 5)) = tf_vpn)
      by (rewrite HN8a1; apply bv_eq; vm_compute; reflexivity).
    assert (Hppn2 : (autocast (T := mword) (subrange_vec_dec (N8 !!! Regidx (mword_of_int 13 : mword 5)) 55 12) : mword 44) = tfp)
      by (rewrite HN8a3; reflexivity).
    assert (Hrepm1 : pt_rep0 t1 ppt_m1) by (unfold ppt_m1; exact Hrep1).
    (* the nine plain instructions since mappages#1's return have each moved
       to a fresh hart, so mappages#2 wants [Hcnt] at CID27. *)
    iDestruct (cpu_own_transport CIDmp1 CID27 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (MP.wp_mappages_sconf γa N8 t1 ppt_m1 1 6 lvl (K - 4)%nat eb p (avail_sub (avail_sub on 1) g1) b
              _ Hlvl Hc32
              ltac:(rewrite HN8a0; rewrite Hbase1; exact Hroot0r)
              ltac:(rewrite HN8a1; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HN8a3; exact Htfal)
              HN8a2 (Nat.le_refl 1) HN8a4 ppt_perm_ok6
              ltac:(rewrite HN8a1; rewrite uint_unsigned; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
              ltac:(rewrite HN8a3; exact Htfb)
              Hrepm1
              ltac:(intros i Hi; rewrite Hsvpn2; rewrite (ppt_lt1 i Hi);
                    rewrite vpn_at_0; exact ppt_m1_tf)
              with "Hcg Hcnt Htext Hpc Hptree Henv").
    all: try lkbelow.
    iIntros (CIDmp2 Hsmp2 mr2 t2 k2 g2) "Hcg Hcnt Hpc Hptree %Hnodes2 Henv %Hcs2 %Hbase2 %Hrep2 %Hmono2 %Hg2miss %Hret2".
    assert (Hretm2 : ret_pc (N8 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.proc_pagetable + 0x48)).
    { rewrite /N8 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hretm2) in "Hpc".
    assert (Hg2 : (g2 <= 0)%nat).
    { rewrite Hsvpn2 in Hg2miss. rewrite (ppt_missing_tf_zero t1 Hrepm1) in Hg2miss. exact Hg2miss. }
    (* the register column at mappages#2's return -- both arms need it *)
    assert (Hmr2sp : mr2 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hcs2 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N8 /N7 /N6 /N5 /N4 /N3 /N2 /N1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr1sp. }
    assert (Hmr2s1 : mr2 !!! Regidx (mword_of_int 9 : mword 5) = root0).
    { rewrite (callee_saved_lookup Hcs2 (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact HN8s1. }
    assert (Hmr2thr : ppt_thr mm mr2).
    { intros c Hc H2 H8 H9 H18.
      rewrite (callee_saved_lookup Hcs2 c Hc). apply HN8thr; assumption. }
    assert (Hbase2b : pt_base t2 = b0) by (rewrite Hbase2; exact Hbase1).
    destruct Hret2 as [(Hk2e & Hmr2a0) | (Hlt2 & Hmr2a0 & Havz2)].
    2:{ (* ============================================================== *)
        (*  TAIL #2, +0x66: the TRAPFRAME run failed.                      *)
        (*  Unlike tail #1 the table is NOT leafless -- the TRAMPOLINE was  *)
        (*  mapped one call ago and uvmfree would try to free the kernel's  *)
        (*  own trampoline page.  So the tail drops that leaf first, with   *)
        (*  do_free = 0, and THAT is the call [UVMUNMAP] cannot state: it   *)
        (*  clears a fixed leaf and leaves behind a table that is no longer *)
        (*  a well-formed user page table.  [UVMUNMAP_FIXED] is the         *)
        (*  instance built for exactly this pair of call sites (the other   *)
        (*  is proc_freepagetable).                                         *)
        (* ============================================================== *)
        assert (Hk20 : k2 = 0%nat) by (apply ppt_lt1; exact Hlt2). subst k2.
        (* [k2 = 0]: nothing was inserted, so the map is still [ppt_m1] *)
        assert (Hrept1 : pt_rep0 t2 (<[tramp_vpn := mappages_pte tramp_ppn 10 0]> ∅))
          by (rewrite -ppt_m1_eq; exact Hrep2).
        iPoseProof (ppti_66 with "Htext") as "Hj66".
        iPoseProof (ppti_68 with "Htext") as "Hj68".
        iPoseProof (ppti_6a with "Htext") as "Hj6a".
        iPoseProof (ppti_6e with "Htext") as "Hj6e".
        iPoseProof (ppti_70 with "Htext") as "Hj70".
        iPoseProof (ppti_72 with "Htext") as "Hj72".
        iPoseProof (ppti_74 with "Htext") as "Hj74".
        iPoseProof (ppti_78 with "Htext") as "Hj78".
        iPoseProof (ppti_7a with "Htext") as "Hj7a".
        iPoseProof (ppti_7c with "Htext") as "Hj7c".
        iPoseProof (ppti_80 with "Htext") as "Hj80".
        iPoseProof (ppti_82 with "Htext") as "Hj82".
        (* +0x48 bltz a0 -- TAKEN *)
        iApply (wp_blt_x0_taken_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x48)) (mword_of_int 30 : mword 13) (mword_of_int 10 : mword 5)
                  mr2 (K - 4)%nat b ltac:(vm_compute; discriminate)
                  ltac:(rgne; rewrite Hmr2a0; vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi48").
        iApply bi.later_intro. iIntros (CIDb1 Hsb1) "Hcg Hpc".
        assert (Htg66 : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x48) : mword 64) (sign_extend' 64 (mword_of_int 30 : mword 13))
                        = mword_of_int (KernelSyms.proc_pagetable + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htg66) in "Hpc".
        (* +0x66 li a3,0 : do_free = 0 *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x66)) (mword_of_int 13 : mword 5)
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  mr2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hj66").
        iIntros (CIDb2 Hsb2) "Hcg Hpc".
        set (V1 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> mr2).
        assert (Hq68 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x66) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x68))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq68) in "Hpc".
        (* +0x68 li a2,1 : npages = 1 *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x68)) (mword_of_int 12 : mword 5)
                  (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
                  V1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hj68").
        iIntros (CIDb3 Hsb3) "Hcg Hpc".
        set (V2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 1 : mword 64)]> V1).
        assert (Hq6a : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x68) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x6a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq6a) in "Hpc".
        (* +0x6a lui a1,0x4000 ; +0x6e addi a1,a1,-1 ; +0x70 slli a1,a1,12
           -- the same three-instruction TRAMPOLINE constant as +0x22..+0x28 *)
        iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x6a)) (mword_of_int 11 : mword 5) (mword_of_int 16384 : mword 20) (luival (mword_of_int 16384 : mword 20))
                  V2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hj6a").
        iIntros (CIDb4 Hsb4) "Hcg Hpc".
        set (V3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (luival (mword_of_int 16384 : mword 20))]> V2).
        assert (Hq6e : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x6a) : mword 64) 4 = mword_of_int (KernelSyms.proc_pagetable + 0x6e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq6e) in "Hpc".
        iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x6e)) (mword_of_int 11 : mword 5) (mword_of_int 63 : mword 6)
                  V3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hj6e").
        iIntros (CIDb5 Hsb5) "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (V4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (V3 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> V3).
        assert (Hq70 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x6e) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x70))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq70) in "Hpc".
        iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x70)) (Regidx (mword_of_int 11 : mword 5)) (mword_of_int 11 : mword 5) (mword_of_int 12 : mword 6)
                  V4 (K - 4)%nat b eq_refl ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hj70").
        iIntros (CIDb6 Hsb6) "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (V5 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (shift_bits_left (V4 !!! Regidx (mword_of_int 11 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> V4).
        assert (Hq72 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x70) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x72))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq72) in "Hpc".
        (* +0x72 mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x72)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                  V5 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hj72").
        iIntros (CIDb7 Hsb7) "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (V6 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (V5 !!! Regidx (mword_of_int 9 : mword 5)))]> V5).
        assert (Hq74 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x72) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x74))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq74) in "Hpc".
        (* +0x74 jal uvmunmap *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x74)) (mword_of_int 1 : mword 5) (mword_of_int 2094926 : mword 21)
                  V6 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hj74").
        iIntros (CIDb8 Hsb8) "Hcg Hpc".
        set (V7 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x74) : mword 64) 4)]> V6).
        assert (Htgtuu : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x74) : mword 64) (sign_extend' 64 (mword_of_int 2094926 : mword 21))
                         = mword_of_int KernelSyms.uvmunmap) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtuu) in "Hpc".
        assert (HV7a0 : V7 !!! Regidx (mword_of_int 10 : mword 5) = page_base b0).
        { rewrite /V7 upd_ne; [| reg_neq]. rewrite /V6 upd_eq. rewrite add_vec_zero_l.
          rewrite /V5 /V4 /V3 /V2 /V1. repeat (rewrite upd_ne; [| reg_neq]).
          rewrite Hmr2s1. exact Hroot0r. }
        assert (HV7a1 : V7 !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int 0x3FFFFFF000).
        { rewrite /V7 /V6. repeat (rewrite upd_ne; [| reg_neq]). rewrite /V5 upd_eq.
          rewrite /V4 upd_eq. rewrite /V3 upd_eq. apply bv_eq; vm_compute; reflexivity. }
        assert (HV7a2 : V7 !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int 1 : mword 64)).
        { rewrite /V7 /V6 /V5 /V4 /V3. repeat (rewrite upd_ne; [| reg_neq]). rewrite /V2 upd_eq. reflexivity. }
        assert (HV7a3 : V7 !!! Regidx (mword_of_int 13 : mword 5) = (mword_of_int 0 : mword 64)).
        { rewrite /V7 /V6 /V5 /V4 /V3 /V2. repeat (rewrite upd_ne; [| reg_neq]). rewrite /V1 upd_eq. reflexivity. }
        assert (HV7sp : V7 !!! Regidx csp_rs1 = spr).
        { rewrite /V7 /V6 /V5 /V4 /V3 /V2 /V1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr2sp. }
        assert (HV7s1 : V7 !!! Regidx (mword_of_int 9 : mword 5) = root0).
        { rewrite /V7 /V6 /V5 /V4 /V3 /V2 /V1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr2s1. }
        assert (HV7thr : ppt_thr mm V7) by (thr_peel; exact Hmr2thr).
        assert (HV7ra : V7 !!! Regidx (mword_of_int 1 : mword 5)
                        = add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x74) : mword 64) 4)
          by (rewrite /V7 upd_eq; reflexivity).
        (* the tree at the fixed-leaf altitude: one leaf, the trampoline *)
        iDestruct (uptg_of_rep0_tramp b0 t2 Hrept1 Hbase2b with "Hptree") as "Hupt".
        iMod (kalloc_env_seal with "Henv") as "#Henv0".
        iDestruct (cpu_own_transport CIDmp2 CIDb8 lvl eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iApply (UUF.wp_uvmunmap_fixed_sconf γa V7 upt_fixed_tramp b0 ∅ tramp_vpn
                  (K - 4)%nat eb p lvl b
                  _ Hc22 Hlvl HV7a0
                  ltac:(rewrite HV7a1; apply bv_eq; vm_compute; reflexivity)
                  HV7a2 HV7a3
                  ltac:(rewrite HV7a1; apply bv_eq; vm_compute; reflexivity)
                  (or_introl eq_refl)
                  ltac:(rewrite HV7a1; rewrite uint_unsigned;
                        apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
                  with "Hcg Hcnt Htext Hpc Hupt Henv0").
        iIntros (CIDb9 Hsb9 mr3) "Hcg Hcnt Hpc %Hcsuu Hupt".
        (* dropping the only fixed leaf leaves a BARE table -- uvmfree's *)
        iEval (rewrite upt_fixed_tramp_del_tramp) in "Hupt".
        assert (Hret78 : ret_pc (V7 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.proc_pagetable + 0x78)).
        { rewrite HV7ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hret78) in "Hpc".
        (* +0x78 li a1,0 : uvmfree(pagetable, 0) *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x78)) (mword_of_int 11 : mword 5)
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  mr3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hj78").
        iIntros (CIDc1 Hsc1) "Hcg Hpc".
        set (W4 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> mr3).
        assert (Hq7a : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x78) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x7a))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq7a) in "Hpc".
        (* +0x7a mv a0,s1 *)
        iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x7a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                  W4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hj7a").
        iIntros (CIDc2 Hsc2') "Hcg Hpc".
        iEval (rgne) in "Hcg".
        set (W5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (W4 !!! Regidx (mword_of_int 9 : mword 5)))]> W4).
        assert (Hq7c : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x7c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq7c) in "Hpc".
        (* +0x7c jal uvmfree *)
        iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x7c)) (mword_of_int 1 : mword 5) (mword_of_int 2095386 : mword 21)
                  W5 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hj7c").
        iIntros (CIDc3 Hsc3) "Hcg Hpc".
        set (W6 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x7c) : mword 64) 4)]> W5).
        assert (Htgtuf2 : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x7c) : mword 64) (sign_extend' 64 (mword_of_int 2095386 : mword 21))
                          = mword_of_int KernelSyms.uvmfree) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgtuf2) in "Hpc".
        assert (HW6s1 : W6 !!! Regidx (mword_of_int 9 : mword 5) = root0).
        { rewrite /W6 /W5 /W4. repeat (rewrite upd_ne; [| reg_neq]).
          rewrite (callee_saved_lookup Hcsuu (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact HV7s1. }
        assert (HW6a0 : W6 !!! Regidx (mword_of_int 10 : mword 5) = page_base b0).
        { rewrite /W6 upd_ne; [| reg_neq]. rewrite /W5 upd_eq. rewrite add_vec_zero_l.
          rewrite /W4 upd_ne; [| reg_neq].
          rewrite (callee_saved_lookup Hcsuu (mword_of_int 9) ltac:(vm_compute; reflexivity)).
          rewrite HV7s1. exact Hroot0r. }
        assert (HW6a1 : W6 !!! Regidx (mword_of_int 11 : mword 5) = (mword_of_int 0 : mword 64)).
        { rewrite /W6 upd_ne; [| reg_neq]. rewrite /W5 upd_ne; [| reg_neq]. rewrite /W4 upd_eq. reflexivity. }
        assert (HW6sp : W6 !!! Regidx csp_rs1 = spr).
        { rewrite /W6 /W5 /W4. repeat (rewrite upd_ne; [| reg_neq]).
          rewrite (callee_saved_lookup Hcsuu csp_rs1 ltac:(vm_compute; reflexivity)). exact HV7sp. }
        assert (HW6thr : ppt_thr mm W6).
        { thr_peel. intros c Hc H2 H8 H9 H18.
          rewrite (callee_saved_lookup Hcsuu c Hc). apply HV7thr; assumption. }
        assert (HW6ra : W6 !!! Regidx (mword_of_int 1 : mword 5)
                        = add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x7c) : mword 64) 4)
          by (rewrite /W6 upd_eq; reflexivity).
        iDestruct (cpu_own_transport CIDb9 CIDc3 lvl eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iApply (UF.wp_uvmfree_sconf γa W6 b0 ∅ (K - 4)%nat eb p lvl b
                  _ Hc36 Hlvl HW6a0
                  ltac:(rewrite HW6a1; unfold uvm_maxsz;
                        rewrite uint_unsigned; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
                  ltac:(rewrite dom_empty_L; apply empty_subseteq)
                  with "Hcg Hcnt Htext Hpc Hupt Henv0").
        all: try lkbelow.
        iIntros (CIDc4 Hsc4 mr4) "Hcg Hcnt Hpc %Hcsuf2".
        assert (Hret80 : ret_pc (W6 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.proc_pagetable + 0x80)).
        { rewrite HW6ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hret80) in "Hpc".
        (* +0x80 li s1,0 : the return value *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x80)) (mword_of_int 9 : mword 5)
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
                  mr4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hj80").
        iIntros (CIDc5 Hsc5) "Hcg Hpc".
        set (W7 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> mr4).
        assert (Hq82 : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x80) : mword 64) 2 = mword_of_int (KernelSyms.proc_pagetable + 0x82))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq82) in "Hpc".
        (* +0x82 j +0x4c -- into the shared epilogue *)
        iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x82))
                  (sign_extend' 21 (concat_vec (mword_of_int 2021 : mword 11) ('b"0")))
                  W7 (K - 4)%nat b ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hj82").
        iIntros (CIDc6 Hsc6). iApply bi.later_intro. iIntros "Hcg Hpc".
        assert (Htg4c2 : add_vec (mword_of_int (KernelSyms.proc_pagetable + 0x82) : mword 64)
                           (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2021 : mword 11) ('b"0"))))
                         = mword_of_int (KernelSyms.proc_pagetable + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htg4c2) in "Hpc".
        assert (HW7sp : W7 !!! Regidx csp_rs1 = spr).
        { rewrite /W7 upd_ne; [| reg_neq].
          rewrite (callee_saved_lookup Hcsuf2 csp_rs1 ltac:(vm_compute; reflexivity)). exact HW6sp. }
        assert (HW7s1 : W7 !!! Regidx (mword_of_int 9 : mword 5) = (mword_of_int 0 : mword 64))
          by (rewrite /W7 upd_eq; reflexivity).
        assert (HW7thr : ppt_thr mm W7).
        { thr_peel. intros c Hc H2 H8 H9 H18.
          rewrite (callee_saved_lookup Hcsuf2 c Hc). apply HW6thr; assumption. }
        iDestruct (cpu_own_transport CIDc4 CIDc6 lvl eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iSpecialize ("EPI" $! CIDc6 with "[%]"); [wp_next_chain|].
        iApply ("EPI" $! W7 (mword_of_int 0 : mword 64) with "[%] Hcg Hcnt Hpc Htfcell []").
        { split_and!; [exact HW7sp | exact HW7s1 | exact HW7thr]. }
        { iRight. iFrame "Henv0". iPureIntro; split_and!;
            [ reflexivity | exact (ppt_fail_n2 on g1 g2 Hg1 Hg2 Havz2) ]. } }
    subst k2.
    rewrite Hsvpn2 Hppn2 in Hrep2.
    assert (Hrepfin : pt_rep0 t2 (ppt_map tfp)) by (unfold ppt_map; exact Hrep2).
    (* the consumption ledger: exactly the tree that was built *)
    assert (Hnt : pt_nodes t2 = (1 + g1 + g2)%nat).
    { apply (ppt_nodes_sum (pt_nodes t1) (pt_nodes t2) g1 g2).
      - rewrite Hnodes1. rewrite pt_nodes_empty. reflexivity.
      - exact Hnodes2. }
    (* +0x48 bltz a0 -- FALLS *)
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (KernelSyms.proc_pagetable + 0x48)) (mword_of_int 30 : mword 13) (mword_of_int 10 : mword 5)
              mr2 (K - 4)%nat b ltac:(vm_compute; discriminate)
              ltac:(rgne; rewrite Hmr2a0; vm_compute; reflexivity)
              with "Hcg Hpc Hi48").
    iIntros (CID28 Hs28) "Hcg Hpc".
    assert (Hp4c : add_vec_int (mword_of_int (KernelSyms.proc_pagetable + 0x48) : mword 64) 4 = mword_of_int (KernelSyms.proc_pagetable + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4c) in "Hpc".
    (* ---------------- the shared epilogue ---------------- *)
    (* the success exit: s1 still holds uvmcreate's root, which is what
       +0x4c moves into a0. *)
    assert (Havf : avail_sub (avail_sub (avail_sub on 1) g1) g2
                   = avail_sub on (pt_nodes t2))
      by (rewrite Hnt; apply ppt_env_recomb).
    iEval (rewrite Havf) in "Henv".
    assert (Hs1fin : mr2 !!! Regidx (mword_of_int 9 : mword 5)
                     = zero_extend' 64 (concat_vec (pt_base t2) (zeros' 12 : mword 12))).
    { rewrite Hmr2s1. rewrite Hbase2 Hbase1. exact Hroot0r. }
    iDestruct (cpu_own_transport CIDmp2 CID28 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("EPI" $! CID28 with "[%]"); [wp_next_chain|].
    iApply ("EPI" $! mr2 (zero_extend' 64 (concat_vec (pt_base t2) (zeros' 12 : mword 12)))
              with "[%] Hcg Hcnt Hpc Htfcell [Hptree Henv]").
    { split_and!; [exact Hmr2sp | exact Hs1fin | exact Hmr2thr]. }
    { iLeft. iExists t2. iFrame "Hptree Henv".
      iPureIntro; split_and!;
        [ reflexivity | exact Hrepfin | rewrite Hnt; exact (ppt_nodes_le g1 g2 Hg1 Hg2) ]. }
  Qed.

End ProofProcPagetable.

End ProcPagetableCore.

(* ===================================================================== *)
(* THE COUNTED SEAL.  Statement unchanged from before the tails existed:  *)
(* a caller who promises more than [K_proc_pagetable] free pages gets the *)
(* success arm, full stop.  All this module does is destruct [ppt_post]   *)
(* and kill the failure arm with [ppt_fail_refute] -- the arm carries the *)
(* [avail_zero (avail_sub on n)] witness precisely so that it can.        *)
(* ===================================================================== *)
Module ProcPagetableProof (UV : UVMCREATE) (MP : MAPPAGES)
                          (UF : UVMFREE) (UUF : UVMUNMAP_FIXED) : PROC_PAGETABLE.

Module Core := ProcPagetableCore UV MP UF UUF.

Section SealProcPagetable.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_proc_pagetable_sconf (γa : gname)
      (mm : regfile) (tf : mword 64) (dqtf : dfrac) (lvl K : nat) (eb : bool)
      (p : mword 64) (on : option nat) (b : bool) (lks : gset string)
    : wp_proc_pagetable_sconf_body γa mm tf dqtf lvl K eb p on b lks.
  Proof.
    cbv beta delta [wp_proc_pagetable_sconf_body].
    intros pp tfp ret_tgt Hlvl HK Hex Htfal Htfb Hlkbelow.
    destruct Hex as (nb & Hon & Hnb). subst on.
    iIntros "Hcg Hcnt #Htext Hpc Htfcell Henv Hcont".
    iApply (Core.wp_proc_pagetable_core γa mm tf dqtf lvl K eb p (Some nb) b lks
              Hlvl HK Htfal Htfb with "Hcg Hcnt Htext Hpc Htfcell Henv [Hcont]").
    all: try lkbelow.
    iIntros (CIDr Hsr mr) "Hcg Hcnt Hpc Htfcell Hpost %Hcs".
    iDestruct "Hpost" as "[(%t & %Hrv & Hptree & %Hrep & %Hnt & Henv)
                           | (_ & %Hfail & _)]";
      [| destruct Hfail as (n & Hn & Hz);
         exfalso; exact (ppt_fail_refute nb n Hnb Hn Hz)].
    iSpecialize ("Hcont" $! CIDr with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! mr t with "Hcg Hcnt Hpc Htfcell Hptree [%] [%] [%] Henv [%]").
    { exact Hrv. }
    { exact Hrep. }
    { exact Hnt. }
    { exact Hcs. }
  Qed.

End SealProcPagetable.

End ProcPagetableProof.
