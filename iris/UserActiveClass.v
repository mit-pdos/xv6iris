(* UserActiveClass.v -- worklist item (A): the [active_class] assembly.

   Builds [active_class] (the no-pending-interrupt fetch/decode/execute
   classification) as a [va] CASE TREE routing every geometry to one of the
   six producers/adapters in UserClassifyAsm.v, then [active_step_branch].
   The two execute totalities are taken as Coq-level hypotheses [Hbase]/[Hrvc]
   (the sibling UserTotalU.v supplies [base_exec_total_u_holds] /
   [rvc_exec_total_u_holds] of exactly this shape).

   Closes the capstone: [active_class_intro] -> [wp_user_step_active]
   (UserStepFull) -> [wp_user_exec_active] (UserStep). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras.
Require Import MinstretInv WireInv RegFile UserBits AlignBits.
Require Import TrampPt KptTree UptTree.
Require Import UserPtTree UserExec UserStep UserStepFull.
Require Import UserFetchPt UserClassify UserClassifyAsm.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1  Pure alignment bridges (bit0 <-> 2-alignment; +2 preserves it).    *)
(* ===================================================================== *)

(* bit 0 of [va] is 0  =>  [va] is even *)
Lemma access0_even (va : mword 64) :
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  bv_unsigned va mod 2 = 0.
Proof.
  intro H0.
  unfold neq_vec in H0. rewrite negb_false_iff in H0.
  unfold eq_vec, access_vec_dec, access_mword_dec, slice, get_word in H0.
  rewrite MachineWord.MachineWord.eqb_true_iff in H0.
  apply bv_eq in H0.
  unfold MachineWord.slice in H0.
  rewrite bv_extract_unsigned in H0.
  replace (bv_unsigned ('b"0")) with 0%Z in H0 by (vm_compute; reflexivity).
  revert H0.
  match goal with
  | |- bv_wrap ?n (Z.shiftr (bv_unsigned va) ?s) = 0%Z -> _ =>
      replace s with 0%Z by (vm_compute; reflexivity);
      rewrite Z.shiftr_0_r;
      replace (bv_wrap n (bv_unsigned va)) with (bv_unsigned va mod 2)
        by (unfold bv_wrap; replace (bv_modulus n) with 2%Z by (vm_compute; reflexivity);
            reflexivity)
  end.
  intro H; exact H.
Qed.

(* CONVERSE of [align2_low_bit]: bit0 = 0  =>  2-aligned. *)
Lemma align2_of_bit0 (va : mword 64) :
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  is_aligned_vaddr (Virtaddr va) 2 = true.
Proof.
  intro H0. pose proof (access0_even va H0) as He.
  unfold is_aligned_vaddr. apply Z.eqb_eq.
  rewrite uint_unsigned.
  pose proof (bv_unsigned_in_range _ va) as Hr.
  rewrite Z.rem_mod_nonneg; [ | lia | lia ].
  exact He.
Qed.

(* 2-alignment is preserved by adding 2. *)
Lemma align2_add2 (va : mword 64) :
  is_aligned_vaddr (Virtaddr va) 2 = true ->
  is_aligned_vaddr (Virtaddr (add_vec_int va 2)) 2 = true.
Proof.
  unfold is_aligned_vaddr. intro H. apply Z.eqb_eq in H. apply Z.eqb_eq.
  rewrite uint_unsigned in H. rewrite uint_unsigned.
  pose proof (bv_unsigned_in_range _ va) as Hv.
  pose proof (bv_unsigned_in_range _ (add_vec_int va 2)) as Hs.
  rewrite Z.rem_mod_nonneg in H; [ | lia | lia ].
  rewrite Z.rem_mod_nonneg; [ | lia | lia ].
  unfold add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hjv : bv_unsigned (mword_of_int 2 : mword 64) = 2) by (vm_compute; reflexivity).
  rewrite Hjv.
  rewrite mod2_wrap.
  2:{ apply Z.leb_le; vm_compute; reflexivity. }
  rewrite Zplus_mod. rewrite H. reflexivity.
Qed.

(* ===================================================================== *)
(* §2  The fetch classification of a va: fetchable OR fault-flavor.       *)
(* ===================================================================== *)

(* a va whose instruction fetch will succeed: canonical, mapped, and the
   leaf passes the U-mode fetch check on every A/D variant. *)
Definition u_fetchable (um : gmap (mword 27) (mword 64)) (va : mword 64) : Prop :=
  exists w, um !! svpn_of va = Some w
            /\ uleaf_ok (InstructionFetch tt) w
            /\ neq_vec (bits_of_virtaddr (Virtaddr va))
                 (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                    (Z.sub 39 1) 0)) = false.

Section UserActiveClass.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).
  Context (Rut : uptd -> iProp Σ).

  (* every canonical/non-canonical va either fetches or faults; the
     tramp/tf pages are denied leaves (U=0), a genuinely unmapped canonical
     va is a page fault, non-canonical faults outright. *)
  Lemma fetch_classify (va : mword 64) :
    upt_acc_wf pt.(ud_um) ->
    u_fetchable pt.(ud_um) va \/ u_fetch_fault_flavor pt.(ud_tfp) pt.(ud_um) va.
  Proof.
    intro Hwf.
    unfold u_fetch_fault_flavor, u_fault_flavor.
    destruct (neq_vec (bits_of_virtaddr (Virtaddr va))
                (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                   (Z.sub 39 1) 0))) eqn:Hcn.
    - (* non-canonical *)
      right. left. reflexivity.
    - (* canonical *)
      destruct (decide (svpn_of va = tramp_vpn)) as [Het | Hnt].
      + (* trampoline page: denied leaf *)
        right. right. right. split; [reflexivity|].
        exists pte_tramp. split.
        * unfold upt_leaf_at. left. split; [exact Het | reflexivity].
        * exact (uleaf_denied_tramp (InstructionFetch tt)).
      + destruct (decide (svpn_of va = tf_vpn)) as [Hetf | Hntf].
        * (* trapframe page: denied leaf *)
          right. right. right. split; [reflexivity|].
          exists (pte_tf pt.(ud_tfp)). split.
          -- unfold upt_leaf_at. right. left. split; [exact Hetf | reflexivity].
          -- exact (uleaf_denied_tf pt.(ud_tfp) (InstructionFetch tt)).
        * destruct (pt.(ud_um) !! svpn_of va) as [w|] eqn:Hm.
          -- (* mapped user leaf: classified by upt_acc_wf *)
             destruct (Hwf (svpn_of va) w Hm (InstructionFetch tt) (or_introl eq_refl))
               as [Hok | Hden].
             ++ left. exists w. split; [exact Hm | split; [exact Hok | exact Hcn]].
             ++ right. right. right. split; [reflexivity|].
                exists w. split.
                ** unfold upt_leaf_at. right. right. exact Hm.
                ** exact Hden.
          -- (* unmapped, and not tramp/tf: page fault *)
             right. right. left. split; [reflexivity|]. split; [reflexivity|].
             split; [exact Hnt | exact Hntf].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §3  The obligation bundle: for a fixed [va] (canonical/aligned data   *)
  (*     of [va] decided purely) each post-minstret-increment state yields *)
  (*     [active_step_obligation] by routing to the right producer.        *)
  (* ------------------------------------------------------------------- *)
  Lemma active_obligations (Ei : coPset) (σ : mstate) (va : mword 64)
      (g : regfile) (ms_v : mword 64) :
    (forall E s v h, ⊢ base_exec_total_u C pt E s v h) ->
    (forall E s v h, ⊢ rvc_exec_total_u C pt E s v h) ->
    upt_acc_wf pt.(ud_um) ->
    user_mstatus_ok ms_v ->
    register_lookup mstatus σ.(sregs) = ms_v ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    eq_vec (register_lookup elp σ.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    register_lookup hart_state σ.(sregs) = HART_ACTIVE tt ->
    hw_config -∗
    (∀ b : bool, active_step_obligation C pt Ei (set_reg σ (R_bool minstret_increment) b) va g).
  Proof.
    intros Hbase Hrvc Hwf Hmsok Lms Hmisa_s Hmenv_s Hhtif_s Hpma_s Help_s Hhart_s.
    iIntros "#Hhw". iIntros (b).
    set (σb := set_reg σ (R_bool minstret_increment) b).
    (* transport every config fact to the post-increment state *)
    assert (HmisaB : register_lookup misa σb.(sregs) = MISA_C)
      by (apply lookup_set_mi; [exact Hmisa_s | vm_compute; reflexivity]).
    assert (HmenvB : register_lookup menvcfg σb.(sregs) = MENVCFG_S)
      by (apply lookup_set_mi; [exact Hmenv_s | vm_compute; reflexivity]).
    assert (HhtifB : register_lookup htif_tohost_base σb.(sregs) = None)
      by (apply lookup_set_mi; [exact Hhtif_s | vm_compute; reflexivity]).
    assert (HpmaB : pma_allows_all (register_lookup pma_regions σb.(sregs))).
    { rewrite (lookup_set_mi σ b pma_regions _ eq_refl ltac:(vm_compute; reflexivity)).
      exact Hpma_s. }
    assert (HelpB : eq_vec (register_lookup elp σb.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false).
    { rewrite (lookup_set_mi σ b elp _ eq_refl ltac:(vm_compute; reflexivity)).
      exact Help_s. }
    assert (HmsokB : user_mstatus_ok (register_lookup mstatus σb.(sregs))).
    { rewrite (lookup_set_mi σ b mstatus _ Lms ltac:(vm_compute; reflexivity)).
      exact Hmsok. }
    assert (HhartB : register_lookup hart_state σb.(sregs) = HART_ACTIVE tt)
      by (apply lookup_set_mi; [exact Hhart_s | vm_compute; reflexivity]).
    (* the pure va case tree *)
    destruct (neq_vec (access_vec_dec va 0) ('b"0")) eqn:Hb0.
    - (* odd pc -> address-align fault *)
      iApply (user_fetch_fault_active_align C pt Ei σb va g Hb0 HhartB).
    - (* even pc *)
      assert (Hal2 : is_aligned_vaddr (Virtaddr va) 2 = true) by (apply align2_of_bit0; exact Hb0).
      destruct (is_aligned_vaddr (Virtaddr va) 4) eqn:Hal4.
      + (* 4-aligned *)
        destruct (fetch_classify va Hwf) as [(w & Hum & Hok & Hcanon) | Hfault].
        * (* mapped & ok -> success *)
          iPoseProof (Hbase Ei σb va g) as "Htb".
          iPoseProof (Hrvc Ei σb va g) as "Htr".
          iApply (user_exec_step_producer_u C pt Ei σb va g w
                    Hum Hok Hal4 Hcanon HmisaB HmenvB HhtifB HmsokB HpmaB HelpB
                    with "Hhw Htb Htr").
        * (* faults -> page fault *)
          iApply (user_fetch_fault_active C pt Ei σb va g Hfault Hal4 HhartB HhtifB HpmaB).
      + (* 2-aligned not 4-aligned: bit1 = 1 *)
        assert (Hb1 : neq_vec (access_vec_dec va 1) ('b"0") = true).
        { destruct (neq_vec (access_vec_dec va 1) ('b"0")) eqn:Hb1'; [reflexivity|].
          exfalso. rewrite (align4_of_low_bits va Hb0 Hb1') in Hal4. discriminate. }
        destruct (fetch_classify va Hwf) as [(w & Hum & Hok & Hcanon) | Hfault_va].
        * (* low half ok: classify va+2 *)
          assert (Hal2h : is_aligned_vaddr (Virtaddr (add_vec_int va 2)) 2 = true)
            by (apply align2_add2; exact Hal2).
          destruct (fetch_classify (add_vec_int va 2) Hwf)
            as [(wh & Humh & Hokh & Hcanonh) | Hfault_vah].
          -- (* both halves ok *)
             iPoseProof (Hbase Ei σb va g) as "Htb".
             iPoseProof (Hrvc Ei σb va g) as "Htr".
             iApply (user_exec_step_producer_2_u C pt Ei σb va g w wh
                       Hum Hok Humh Hokh Hal2 Hal2h Hb0 Hb1 Hal4 Hcanon Hcanonh
                       HmisaB HmenvB HhtifB HmsokB HpmaB HelpB with "Hhw Htb Htr").
          -- (* low ok, straddle faults at va+2 *)
             iPoseProof (Hbase Ei σb va g) as "Htb".
             iPoseProof (Hrvc Ei σb va g) as "Htr".
             iApply (user_exec_or_fault_active_2_second C pt Ei σb va g w
                       Hum Hok Hfault_vah Hal2 Hb0 Hb1 Hal4 Hcanon
                       HhartB HmisaB HmenvB HhtifB HmsokB HpmaB HelpB with "Hhw Htb Htr").
        * (* low half faults *)
          iApply (user_fetch_fault_active_2_first C pt Ei σb va g
                    Hfault_va Hb0 Hb1 Hal4 HhartB HmisaB HhtifB HpmaB).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §4  active_class, from hw_config + the two totalities.                *)
  (* ------------------------------------------------------------------- *)
  Lemma active_class_intro (Ei : coPset) :
    (forall E s v h, ⊢ base_exec_total_u C pt E s v h) ->
    (forall E s v h, ⊢ rvc_exec_total_u C pt E s v h) ->
    hw_config -∗ active_class C pt Rut Ei.
  Proof.
    intros Hbase Hrvc.
    iIntros "#Hhw". iModIntro.
    iIntros (σ ms_v sc_v stval_v sepc_v va g).
    iIntros "%Hmsok %Lpriv %Lms %Lpc %Hdisp Hregs Hupt Hcfg Hrut Hint Hbody Hcont".
    iDestruct "Hint" as "(Hreg & Hgh & Hdev)".
    iDestruct "Hregs" as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc & Hpc & Hnpc & Hgpr)".
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmenv & Hsenv & Hmsten & Hssten)".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & #Hpma & #Hhtif & #Help & _ & _ & _ & _ & _ & %Hpmaall & _ & _ & %Help_ne & _ & %Hmisa_eq & _)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Hhtif_s.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Hmenv_s.
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_s.
    assert (Hmisa_s : register_lookup misa σ.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_eq).
    assert (Hpma_s : pma_allows_all (register_lookup pma_regions σ.(sregs)))
      by (rewrite Lpma; exact Hpmaall).
    assert (Help_s : eq_vec (register_lookup elp σ.(sregs))
                       (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_ne).
    iDestruct (active_obligations Ei σ va g ms_v Hbase Hrvc Hwf Hmsok Lms
                 Hmisa_s Hmenv_s Hhtif_s Hpma_s Help_s Hhart_s with "Hhw") as "Hob".
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iAssert (mstate_interp σ) with "[Hreg Hgh Hdev]" as "Hint". { iFrame. }
    iAssert (user_pt_inv pt) with "[Hutlb Hudata]" as "Hupt".
    { iFrame "Hutlb Hudata". iPureIntro; split; assumption. }
    iAssert (user_cfg C) with "[Hstvec Hmie Hmdl Hmedl Hmenv Hsenv Hmsten Hssten]"
      as "Hcfg". { iFrame. }
    iApply (active_step_branch C pt Rut Ei σ ms_v sc_v stval_v sepc_v va g mst mi
              Hmsok Lpriv Lms Lpc Hdisp
              with "Hhw Hint Hmst Hmi Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr
                    Hupt Hcfg Hrut Hob Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* §5  Wire toward the capstone.                                         *)
  (* ------------------------------------------------------------------- *)

  (* the ACTIVE-residue step obligation, from the two totalities. *)
  Lemma user_step_obligation_active_holds :
    (forall E s v h, ⊢ base_exec_total_u C pt E s v h) ->
    (forall E s v h, ⊢ rvc_exec_total_u C pt E s v h) ->
    hw_config -∗ minstret_inv -∗ wire_inv -∗ user_step_obligation_active C pt Rut.
  Proof.
    intros Hbase Hrvc. iIntros "#Hhw #Hmin #Hwinv".
    iApply (wp_user_step_active C pt Rut with "Hhw Hmin Hwinv").
    iApply (active_class_intro (⊤ ∖ ↑minstretN ∖ ↑wireN ∖ ↑clockN) Hbase Hrvc with "Hhw").
  Qed.

  (* THE CAPSTONE: safety of arbitrary user-mode execution, parametrized on
     the two execute totalities. *)
  Theorem wp_user_exec_full :
    (forall E s v h, ⊢ base_exec_total_u C pt E s v h) ->
    (forall E s v h, ⊢ rvc_exec_total_u C pt E s v h) ->
    hw_config -∗ minstret_inv -∗ wire_inv -∗
    user_inv C pt Rut -∗ stvec_handler_wp C pt Rut -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hbase Hrvc. iIntros "#Hhw #Hmin #Hwinv Hinv Htrap".
    iApply (wp_user_exec_active C pt Rut with "Hmin [] Hinv Htrap").
    iApply (user_step_obligation_active_holds Hbase Hrvc with "Hhw Hmin Hwinv").
  Qed.

End UserActiveClass.
