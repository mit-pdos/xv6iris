(* ProofIsmapped.v -- ismapped() over the SIE-agnostic sconf world.

     int ismapped(pagetable_t pagetable, uint64 va) {
       pte_t *pte = walk(pagetable, va, 0);
       if (pte == 0) return 0;
       return ( *pte & PTE_V) ? 1 : 0;
     }

   A 2-slot-frame wrapper around the NO-ALLOC walk (SpecWalk's
   [WALK_NOALLOC]): thirteen instructions, one call, one branch, a two-way
   join at the epilogue (+0x14).  The tree rides through READ-ONLY at the
   caller's generic dfrac.  Spec of record: SpecIsmapped.v.

   The pure and separation-logic pieces this proof rests on live in PtBuild.v:
   [andi1_unsigned] / [pte_valid_bit0] / [candi1_imm] (V is bit 0, so
   [andi w,1] on a valid PTE is exactly 1 -- next to [walk_vbit_eq], which
   proves only the zero/nonzero verdict the walk's [beqz] needs) and
   [ptree_own_level0_ro] (the read-only twin of [ptree_own_level0_upd]).

   EXPLICIT-CPUID: ismapped is b-GENERIC (SpecIsmapped's body wraps its
   continuation in [wp_next b (fun CID => ...)], with no SIE-arm flip), so
   every leaf application below lands at a freshly-quantified hart via
   [iIntros (CIDk Hsk) "..."] -- never [rewrite wp_next_off].  The epilogue
   at +0x14 is reached from TWO branches with a DIFFERENT NUMBER of leaves
   run beforehand (the null branch reaches it directly off the taken beqz;
   the found branch runs the [cld]/[candi] pair first), so the two branches
   land on the epilogue at hart values Rocq cannot identify syntactically.
   The epilogue is therefore its OWN lemma ([ismapped_epi]) with [CID] as an
   explicit BINDER (durable-notes: "a whole-function proof's post-resume
   half must be its own lemma with CID as a binder... a Context {CID:CpuId}
   section variable cannot be instantiated from inside its own section"),
   proved once and applied at whichever hart each branch actually reaches;
   its own trailing continuation is [wp_next]-wrapped exactly like a leaf's,
   so the two call sites discharge the WHOLE function's own [Hcont] the same
   way a straight-line stretch discharges its own continuation ([iIntros
   (CIDf Hsf) ...] then [wp_next_chain] against every [Hsk] accumulated
   since entry, including the ones from the epilogue itself). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import HartTp WpNext.
Require Import KernelText.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import CommonWalk PtTree.
Require Import KptTree.   (* pt_slot_phys_to_mem / pt_slot_mem_to_phys *)
Require Import PtBuild.
Require Import CodeIsmapped.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecWalk.
Require Import SpecIsmapped.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* THE WHOLE FUNCTION.                                                    *)
(* ===================================================================== *)

Module IsmappedProof (WalkNoalloc : WALK_NOALLOC) : ISMAPPED.

(* ---- the epilogue (+0x14..+0x1a): pop the frame and return, whatever
   a0 holds -- its own lemma, CID a BINDER (see the file header). ---- *)
Section IsmappedEpi.
  Context `{!riscvGS Σ, !sieG Σ}.

  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  Lemma ismapped_epi `{GEN : GenId} `{CID : CpuId} (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64))
      (vpn : mword 27) (K : nat) (HK2 : (2 <= K)%nat) (dq : dfrac) (b : bool) (p : mword 64) (ret_tgt : mword 64)
      (Hrt_def : ret_tgt = ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)))
      (spr sp0 : mword 64)
      (Hsp0_def : sp0 = mm !!! Regidx csp_rs1)
      (Hsprdef : spr = add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
      (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1)
      (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2)
      (mw : regfile)
      (Hmwsp : mw !!! Regidx csp_rs1 = spr)
      (Hmwagree : forall c : mword 5, is_cs_idx c = true ->
            c <> mword_of_int 8 -> c <> csp_rs1 -> mw !!! Regidx c = mm !!! Regidx c)
      (M : regfile)
    : ⌜callee_saved mw M⌝ -∗
      kernel_text -∗
      sie_cap_gpr M (K - 2)%nat b p -∗
      pc_is (mword_of_int (KernelSyms.ismapped + 0x14) : mword 64) -∗
      ptree_own 2 dq t -∗
      pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
      pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
      ⌜ (M !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0 /\ m !! vpn = None)
        \/ (exists w, m !! vpn = Some w /\
             M !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 1) ⌝ -∗
      wp_next b p (fun (CID' : CpuId) =>
        ∀ (mr : regfile),
        sie_cap_gpr mr K b p -∗
        pc_is ret_tgt -∗
        ptree_own 2 dq t -∗
        ⌜callee_saved mm mr⌝ -∗
        ⌜ (mr !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 0 /\ m !! vpn = None)
          \/ (exists w, m !! vpn = Some w /\
               mr !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int 1) ⌝ -∗
        WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    iIntros "%HcsM #Htext Hcg Hpc Hptree Hc1 Hc2 %Hpay' Hcont".
    assert (HspM : M !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup HcsM csp_rs1 ltac:(vm_compute; reflexivity)).
      exact Hmwsp. }
    assert (HMagree : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 ->
              M !!! Regidx c = mm !!! Regidx c).
    { intros c Hc Hc8 Hcsp.
      rewrite (callee_saved_lookup HcsM c Hc). apply Hmwagree; assumption. }
    iPoseProof (imi_14 with "Htext") as "Hi14".
    iPoseProof (imi_16 with "Htext") as "Hi16".
    iPoseProof (imi_18 with "Htext") as "Hi18".
    iPoseProof (imi_1a with "Htext") as "Hi1a".
    (* +0x14 c.ldsp ra,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ismapped + 0x14)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              M (K - 2)%nat (mm !!! Regidx (mword_of_int 1)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 [Hc1] [-]").
    { iEval (rewrite HspM Hb1). iExact "Hc1". }
    iIntros (CIDa Hsa) "Hcg Hpc Hc1".
    iEval (rewrite HspM Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1))]> M).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.ismapped + 0x14) : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 c.ldsp s0,0(sp) *)
    assert (HspE1 : E1 !!! Regidx csp_rs1 = spr).
    { rewrite /E1. rewrite upd_ne; [| vm_compute; discriminate]. exact HspM. }
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.ismapped + 0x16)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 2)%nat (mm !!! Regidx (mword_of_int 8)) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi16 [Hc2] [-]").
    { iEval (rewrite HspE1 Hb2). iExact "Hc2". }
    iIntros (CIDb Hsb) "Hcg Hpc Hc2".
    iEval (rewrite HspE1 Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8))]> E1).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.ismapped + 0x16) : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 c.addi sp,+16 : the frame pop *)
    assert (HspE2 : E2 !!! Regidx csp_rs1 = spr).
    { rewrite /E2. rewrite upd_ne; [| vm_compute; discriminate]. exact HspE1. }
    set (E3 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> E2).
    assert (HspE3 : E3 !!! Regidx csp_rs1 = sp0).
    { rewrite /E3 upd_eq. rewrite HspE2.
      unfold regval_into_reg. rewrite Hsprdef. apply frame_cancel_16. }
    assert (Hwv : add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = sp0).
    { rewrite -HspE3. rewrite /E3 upd_eq. reflexivity. }
    assert (Hsprstk : pa_stk sp0 2 = spr).
    { rewrite /pa_stk /add_vec_int. rewrite Hsprdef. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpop : E2 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))) 2).
    { rewrite Hwv HspE2. symmetry. exact Hsprstk. }
    iAssert (stack_own sp0 2) with "[Hc1 Hc2]" as "Hfr".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      done. }
    iEval (rewrite -Hwv) in "Hfr".
    iApply (wp_caddi_sp_pop_s_sconf (mword_of_int (KernelSyms.ismapped + 0x18)) (mword_of_int 16 : mword 6)
              E2 (K - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi18 Hfr [-]").
    iIntros (CIDc Hsc) "Hcg Hpc".
    assert (Hnk : ((K - 2) + 2)%nat = K) by (clear -HK2; lia).
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.ismapped + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.ret *)
    assert (HE3ra : E3 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /E3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /E2. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_eq. reflexivity. }
    assert (HE3a0 : E3 !!! Regidx (mword_of_int 10 : mword 5) = M !!! Regidx (mword_of_int 10 : mword 5)).
    { rewrite /E3. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /E2. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /E1. rewrite upd_ne; [| vm_compute; discriminate]. reflexivity. }
    assert (HE3peel : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 ->
              E3 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc Hc8 Hcsp.
      rewrite /E3. rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; apply Hcsp; reflexivity].
      rewrite /E2. rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; apply Hc8; reflexivity].
      rewrite /E1. rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c; vm_compute in Hc; discriminate].
      apply HMagree; assumption. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.ismapped + 0x1a)) (mword_of_int 1 : mword 5) E3 K b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1a [-]").
    iIntros (CIDd Hsd) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hrt : ret_pc (E3 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt)
      by (rewrite HE3ra Hrt_def; reflexivity).
    iEval (rewrite Hrt) in "Hpc".
    iSpecialize ("Hcont" $! CIDd with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! E3 with "Hcg Hpc Hptree [%] [%]").
    { (* callee_saved mm E3 *)
      unfold callee_saved. split_and!.
      - rewrite HspE3 Hsp0_def. reflexivity.
      - rewrite /E3. rewrite upd_ne; [| vm_compute; discriminate].
        rewrite /E2 upd_eq. reflexivity.
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate].
      - apply HE3peel; [vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. }
    { rewrite HE3a0. exact Hpay'. }
  Qed.

End IsmappedEpi.

Section ProofIsmapped.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Ltac rgne :=
    rewrite rget_ne;
    [ | let H1 := fresh in let H2 := fresh in
        intro H1; injection H1 as H2; vm_compute in H2; congruence ].

  Lemma wp_ismapped_sconf (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac) (b : bool) (p : mword 64)
    : wp_ismapped_sconf_body mm t m K dq b p.
  Proof.
    cbv beta delta [wp_ismapped_sconf_body].
    intros pcE va vpn ret_tgt HK Hroot Hvab Hrep.
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> mm).
    iIntros "Hcg #Htext Hpc Hptree Hcont".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (imi_00 with "Htext") as "Hi00".
    iPoseProof (imi_02 with "Htext") as "Hi02".
    iPoseProof (imi_04 with "Htext") as "Hi04".
    iPoseProof (imi_06 with "Htext") as "Hi06".
    iPoseProof (imi_08 with "Htext") as "Hi08".
    iPoseProof (imi_0a with "Htext") as "Hi0a".
    (* ---- +0x00 c.addi sp,-16 : the 2-slot frame push ---- *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 2).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.ismapped) (mword_of_int 48 : mword 6) mm K 2 b ltac:(lia) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & _)".
    iDestruct "S1" as (v8) "Hc1". iDestruct "S2" as (v0) "Hc2".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr)
      by (rewrite /W1 upd_eq; reflexivity).
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.ismapped : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* ---- +0x02 c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ismapped + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 2)%nat v8 b with "Hcg Hpc Hi02 [Hc1] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1".
    iEval (rewrite HspW1 Hb1) in "Hc1".
    iEval (rgne) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.ismapped + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- +0x04 c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.ismapped + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat v0 b with "Hcg Hpc Hi04 [Hc2] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2".
    iEval (rewrite HspW1 Hb2) in "Hc2".
    iEval (rgne) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)).
    { rewrite /W1. rewrite upd_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.ismapped + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- +0x06 c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.ismapped + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> W1).
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.ismapped + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- +0x08 c.li a2,0 (walk's alloc argument) ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.ismapped + 0x08)) (mword_of_int 12 : mword 5) (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) W2 (K - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (W3 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (mword_of_int 0 : mword 64)]> W2).
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.ismapped + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* ---- +0x0a jal walk ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.ismapped + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095566 : mword 21)
              W3 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (W4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.ismapped + 0x0a) : mword 64) 4)]> W3).
    assert (Hpcwk : add_vec (mword_of_int (KernelSyms.ismapped + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095566 : mword 21)) = mword_of_int KernelSyms.walk) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpcwk) in "Hpc".
    (* ---- the register facts at walk's entry ---- *)
    assert (HW4sp : W4 !!! Regidx csp_rs1 = spr).
    { rewrite /W4 /W3 /W2.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact HspW1. }
    assert (HW4a0 : W4 !!! Regidx (mword_of_int 10 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact Hroot. }
    assert (HW4a1 : W4 !!! Regidx (mword_of_int 11 : mword 5) = va).
    { rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      reflexivity. }
    assert (HW4a2 : W4 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 0).
    { rewrite /W4. rewrite upd_ne; [| vm_compute; discriminate].
      rewrite /W3 upd_eq. reflexivity. }
    assert (HW4ra : W4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.ismapped + 0x0a) : mword 64) 4)
      by (rewrite /W4 upd_eq; reflexivity).
    assert (Hret0e : ret_pc (W4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.ismapped + 0x0e)).
    { rewrite HW4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    (* ---- the call ---- *)
    iApply (WalkNoalloc.wp_walk_noalloc_sconf W4 t m (K - 2)%nat dq b p
              ltac:(lia) HW4a0 HW4a2
              ltac:(rewrite HW4a1; exact Hvab)
              Hrep
              with "Hcg Htext Hpc Hptree [-]").
    iIntros (CID7 Hs7 mw) "Hcg Hpc Hptree %Hkcs %Hpay".
    iEval (rewrite Hret0e) in "Hpc".
    assert (HW4vpn : svpn_of (W4 !!! Regidx (mword_of_int 11 : mword 5)) = vpn)
      by (rewrite HW4a1; reflexivity).
    rewrite HW4vpn in Hpay.
    (* ---- the recovered register facts ---- *)
    assert (Hmwsp : mw !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HW4sp. }
    assert (Hmwagree : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 8 -> c <> csp_rs1 ->
              mw !!! Regidx c = mm !!! Regidx c).
    { intros c Hc Hc8 Hcsp.
      rewrite (callee_saved_lookup Hkcs c Hc).
      rewrite /W4 /W3 /W2 /W1.
      repeat (rewrite upd_ne;
        [| intros Habs; injection Habs as Habs2; subst c;
           first [ apply Hc8; reflexivity | apply Hcsp; reflexivity | vm_compute in Hc; discriminate ] ]).
      reflexivity. }
    iPoseProof (imi_0e with "Htext") as "Hi0e".
    iPoseProof (imi_10 with "Htext") as "Hi10".
    iPoseProof (imi_12 with "Htext") as "Hi12".
    (* ================================================================= *)
    (* +0x0e c.beqz a0 : the walk verdict.                                *)
    (* ================================================================= *)
    destruct Hpay as [(Ha0z & Hnone) | (p2 & p1 & w0 & Hl0 & Ha0v & Hverd)].
    { (* ---- walk returned NULL: branch TAKEN, a0 = 0 already ---- *)
      unshelve iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.ismapped + 0x0e)) (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
                mw (K - 2)%nat b
                ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate)
                _
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi0e [-]").
      1: { rgne. rewrite Ha0z. vm_compute; reflexivity. }
      iNext. iIntros (CID8 Hs8) "Hcg Hpc".
      assert (Htgt14 : add_vec (mword_of_int (KernelSyms.ismapped + 0x0e) : mword 64)
                (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.ismapped + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt14) in "Hpc".
      iApply (ismapped_epi (CID:=CID8) mm t m vpn K ltac:(lia) dq b p ret_tgt eq_refl spr sp0 eq_refl eq_refl Hb1 Hb2 mw Hmwsp Hmwagree mw
                with "[%] Htext Hcg Hpc Hptree Hc1 Hc2 [%] [-]").
      { apply callee_saved_refl. }
      { left. split; [exact Ha0z | exact Hnone]. }
      iIntros (CID9 Hs9 mr) "Hcg Hpc Hptree %Hcs %Hpay2".
      iSpecialize ("Hcont" $! CID9 with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! mr with "Hcg Hpc Hptree [%] [%]").
      { exact Hcs. } { exact Hpay2. } }
    (* ---- walk returned the L0 slot address: read it ---- *)
    iDestruct (ptree_own_level0_ro dq t vpn p2 p1 w0 Hl0 with "Hptree") as "(#Hcl0 & Hcell & Hclose)".
    iDestruct (phys_word_pointsto_ram with "Hcell") as %Hslotram.
    (* the slot is owned PHYSICALLY ([↦ₚ₈]); the load goes THROUGH
       translation, so convert to the VA tier via the node's own claim. *)
    iDestruct (pt_slot_phys_to_mem (u_next_base p1) (vpn_idx 0 vpn) dq w0
                 with "Hcl0 Hcell") as "Hcell".
    assert (Ha0nz : mw !!! Regidx (mword_of_int 10 : mword 5) <> mword_of_int 0).
    { rewrite Ha0v. intro Heq. rewrite Heq in Hslotram.
      unfold addr_is_ram in Hslotram. destruct Hslotram as [Hlo _].
      apply (proj2 (Z.leb_le _ _)) in Hlo. vm_compute in Hlo. discriminate. }
    (* +0x0e c.beqz a0 FALLS *)
    unshelve iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.ismapped + 0x0e)) (mword_of_int 3 : mword 8) (Cregidx (mword_of_int 2)) (mword_of_int 10 : mword 5)
              mw (K - 2)%nat b
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              _
              with "Hcg Hpc Hi0e [-]").
    1: { rgne. apply eq_vec_false_iff. intro He. apply Ha0nz.
         rewrite He. apply bv_eq; vm_compute; reflexivity. }
    iIntros (CID10 Hs10) "Hcg Hpc".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.ismapped + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.ld a0,0(a0) *)
    assert (Hea0 : forall X : mword 64,
        add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iApply (wp_cld_s_sconf (mword_of_int (KernelSyms.ismapped + 0x10)) (mword_of_int 10 : mword 5) (mword_of_int 10 : mword 5)
              (mword_of_int 0 : mword 12)
              mw (K - 2)%nat w0 b (dqm:=dq)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [Hcell] [-]").
    { iEval (rgne). iEval (rewrite Hea0 Ha0v). iExact "Hcell". }
    iIntros (CID11 Hs11) "Hcg Hpc Hcell".
    iEval (rgne) in "Hcell". iEval (rewrite Hea0 Ha0v) in "Hcell".
    set (B1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg w0]> mw).
    assert (HB1a0 : B1 !!! Regidx (mword_of_int 10 : mword 5) = w0)
      by (rewrite /B1 upd_eq; reflexivity).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.ismapped + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* give the tree back: the slot is untouched *)
    iDestruct (pt_slot_mem_to_phys (u_next_base p1) (vpn_idx 0 vpn) dq w0
                 with "Hcl0 Hcell") as "Hcell".
    iDestruct ("Hclose" with "Hcell") as "Hptree".
    (* +0x12 c.andi a0,a0,1 *)
    iApply (wp_candi_s_sconf (mword_of_int (KernelSyms.ismapped + 0x12)) (mword_of_int 10 : mword 5) (mword_of_int 1 : mword 6)
              B1 (K - 2)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (and_vec (B1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> B1).
    assert (HB2a0 : B2 !!! Regidx (mword_of_int 10 : mword 5)
                    = and_vec w0 (sign_extend' 64 (mword_of_int 1 : mword 12))).
    { rewrite /B2 upd_eq. rewrite HB1a0. rewrite candi1_imm. reflexivity. }
    assert (HcsB2 : callee_saved mw B2).
    { rewrite /B2. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      rewrite /B1. apply callee_saved_insert_r; [vm_compute; reflexivity |].
      apply callee_saved_refl. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.ismapped + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.ismapped + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* the two sub-verdicts of the reached slot *)
    destruct Hverd as [Hsome | (Hw0z & Hnone)].
    { (* mapped: the leaf word is model-valid, so the V bit is set *)
      assert (Hpv : pte_valid w0).
      { destruct Hrep as (Hmaps & _).
        destruct (Hmaps vpn w0 Hsome) as (q2 & q1 & Hmp).
        destruct Hmp as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv0 & _).
        exact Hv0. }
      iApply (ismapped_epi (CID:=CID12) mm t m vpn K ltac:(lia) dq b p ret_tgt eq_refl spr sp0 eq_refl eq_refl Hb1 Hb2 mw Hmwsp Hmwagree B2
                with "[%] Htext Hcg Hpc Hptree Hc1 Hc2 [%] [-]").
      { exact HcsB2. }
      { right. exists w0. split; [exact Hsome |].
        rewrite HB2a0. exact (pte_valid_bit0 w0 Hpv). }
      iIntros (CID13 Hs13 mr) "Hcg Hpc Hptree %Hcs %Hpay2".
      iSpecialize ("Hcont" $! CID13 with "[]"); [iPureIntro; wp_next_chain|].
      iApply ("Hcont" $! mr with "Hcg Hpc Hptree [%] [%]").
      { exact Hcs. } { exact Hpay2. } }
    (* unmapped-with-path: the slot holds the literal zero *)
    iApply (ismapped_epi (CID:=CID12) mm t m vpn K ltac:(lia) dq b p ret_tgt eq_refl spr sp0 eq_refl eq_refl Hb1 Hb2 mw Hmwsp Hmwagree B2
              with "[%] Htext Hcg Hpc Hptree Hc1 Hc2 [%] [-]").
    { exact HcsB2. }
    { left. split; [| exact Hnone].
      rewrite HB2a0 Hw0z. apply bv_eq; vm_compute; reflexivity. }
    iIntros (CID14 Hs14 mr) "Hcg Hpc Hptree %Hcs %Hpay2".
    iSpecialize ("Hcont" $! CID14 with "[]"); [iPureIntro; wp_next_chain|].
    iApply ("Hcont" $! mr with "Hcg Hpc Hptree [%] [%]").
    { exact Hcs. } { exact Hpay2. }
  Qed.

End ProofIsmapped.

End IsmappedProof.
