From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr.
Local Open Scope Z_scope.

(* register-generic JAL execute: writes rd := link (nextPC), sets nextPC := target. *)
Lemma exec_execute_JAL_gpr (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 1) = false ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hbit1.
  apply (exec_execute_JAL imm (Regidx rd) s _ Halign Hbit1).
  rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs))
             (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  reflexivity.
Qed.

Section ForwardJALg.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (imm : mword 21) (rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (JAL (imm, Regidx rd), s0).

  Definition sAjg : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcjg : mstate := set_reg sAjg nextPC (add_vec_int pc 4).
  Definition jtgtg : mword 64 :=
    add_vec (register_lookup PC s_pcjg.(sregs)) (sign_extend' 64 imm).
  Definition jlinkg : mword 64 := register_lookup nextPC s_pcjg.(sregs).
  Definition sXjg : mstate :=
    set_reg (set_reg s_pcjg nextPC jtgtg)
            (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg jlinkg).
  Definition sTjg : mstate := set_reg sXjg PC (register_lookup nextPC sXjg.(sregs)).
  Definition sFjg : mstate :=
    if b then set_reg sTjg minstret (add_vec_int (register_lookup minstret sTjg.(sregs)) 1)
         else sTjg.

  Lemma forward_exec_jal_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (access_vec_dec jtgtg 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec jtgtg 1) = false ->
    exec riscv_step s = Some (tt, sFjg).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp Halign Hbit1.
    assert (LpcA  : register_lookup PC sAjg.(sregs) = pc).
    { unfold sAjg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAjg.(sregs) = Machine).
    { unfold sAjg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAjg.(sregs) = HART_ACTIVE tt).
    { unfold sAjg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAjg.(sregs))) ('b"1") = true).
    { unfold sAjg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAjg.(sregs))) ('b"1") = false).
    { unfold sAjg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAjg.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAjg, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAjg = Some (None, sAjg)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAjg _ (exec_currentlyEnabled_S sAjg) (or_introl LSA) LmIEA). }
    assert (HfetchA : exec (fetch tt) sAjg = Some (F_Base w, sAjg)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAjg = Some (JAL (imm, Regidx rd), sAjg))
      by (apply Hdec; exact LprivA).
    assert (HexecJ : exec (execute (JAL (imm, Regidx rd))) s_pcjg
              = Some (RETIRE_SUCCESS, sXjg)).
    { change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      rewrite (exec_execute_JAL_gpr imm rd s_pcjg Hrd0 Halign Hbit1).
      unfold sXjg, jtgtg, jlinkg. reflexivity. }
    assert (Hha : exec (run_hart_active 0) sAjg
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXjg)).
    { exact (exec_hart_active_progress sAjg sAjg sXjg sAjg w
               (JAL (imm, Regidx rd)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecJ I). }
    apply (exec_riscv_step_ADD s sXjg w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXjg, s_pcjg, sAjg; cbn zeta. trans_mi. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXjg, s_pcjg, sAjg; cbn zeta. trans_mi. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardJALg.

Section CleanJALg.
  Context (s : mstate) (pc : mword 64) (b : bool) (imm : mword 21) (rd : mword 5) (mst0 : mword 64).
  Definition base_upd_jg : mstate :=
    set_reg
      (set_reg
         (set_reg
            (set_reg (set_reg s (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
            nextPC (jtgtg s pc b imm))
         (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (add_vec_int pc 4)))
      PC (jtgtg s pc b imm).
  Definition sFcjg : mstate :=
    if b then set_reg base_upd_jg minstret (add_vec_int mst0 1) else base_upd_jg.

  Lemma sFj_eq_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFjg s pc b imm rd = sFcjg.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXjg s pc b imm rd).(sregs) = jtgtg s pc b imm).
    { unfold sXjg; cbv zeta. unfold set_reg; cbn [sregs]. tmig.
      rewrite register_lookup_set. reflexivity. }
    assert (Ejlink : jlinkg s pc b = add_vec_int pc 4).
    { unfold jlinkg, s_pcjg; cbv zeta. unfold set_reg; cbn [sregs].
      rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTjg s pc b imm rd = base_upd_jg).
    { unfold sTjg. rewrite Enpc. unfold sXjg, s_pcjg, sAjg; cbv zeta.
      rewrite Ejlink. unfold base_upd_jg, s_pcjg, sAjg. reflexivity. }
    unfold sFjg, sFcjg. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_jg.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_jg, set_reg; cbn [sregs]. tmig. tmig. tmig. tmig. tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanJALg.

Lemma jtgt_eq_gpr (s : mstate) (pc : mword 64) (b : bool) (imm : mword 21) :
  register_lookup PC s.(sregs) = pc ->
  jtgtg s pc b imm = add_vec pc (sign_extend' 64 imm).
Proof.
  intro Lpc. unfold jtgtg, s_pcjg, sAjg. unfold set_reg; cbn [sregs].
  rewrite irrelevant_register_set; [|vm_compute; reflexivity].
  rewrite irrelevant_register_set; [|vm_compute; reflexivity].
  rewrite Lpc. reflexivity.
Qed.

(* ====================================================================== *)
(* The register-GENERIC JAL WP: ONE lemma for 32-bit `jal rd, off`, ANY    *)
(* link register rd; the GPRs live in the single [gpr_file] resource.      *)
(* ====================================================================== *)
Section WpJalGpr.
  Context `{!riscvGS Σ}.

  Lemma wp_jal_gpr (pc : mword 64) (w : mword 32) (imm : mword 21) (rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (JAL (imm, Regidx rd), s0)) ->
    eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 0) ('b"0") = true ->
    bit_to_bool (access_vec_dec (add_vec pc (sign_extend' 64 imm)) 1) = false ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec pc (sign_extend' 64 imm) -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (add_vec_int pc 4)]> m) -∗
        misa ↦ᵣ misa0 -∗
        nextPC ↦ᵣ add_vec pc (sign_extend' 64 imm) -∗
        (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrd Hmd HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hal0 Hal1 Hb1 HmIE Help)
      "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply wp_exec_step. iIntros (s ns κs nt) "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hmst")   as %Lmst.
    iDestruct (reg_valid with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa")  as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hjt : jtgtg s pc b1 imm = add_vec pc (sign_extend' 64 imm))
      by (apply jtgt_eq_gpr; exact Lpc).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcjg s pc b1 imm rd mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFj_eq_gpr s pc b1 imm rd mst0 Lpc Lmst).
      apply (forward_exec_jal_gpr s pc b1 w imm rd Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help.
      - rewrite Hjt. exact Hal0.
      - rewrite Hjt. exact Hal1. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ nextPC _ (jtgtg s pc b1 imm) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc 4)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (jtgtg s pc b1 imm) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hjt) in "Hpc". iEval (rewrite Hjt) in "Hnpc".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int pc 4)) with "Hrdc") as "Hfile".
    unfold sFcjg, base_upd_jg. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpJalGpr.

(* Demonstration: ONE lemma [wp_jal_gpr] serves many link registers. *)
Section WpJalGprDemo.
  Context `{!riscvGS Σ}.
  Definition wp_jal_x1 (pc : mword 64) (w : mword 32) (imm : mword 21) :=
    wp_jal_gpr pc w imm (mword_of_int 1).
  Definition wp_jal_x5 (pc : mword 64) (w : mword 32) (imm : mword 21) :=
    wp_jal_gpr pc w imm (mword_of_int 5).
  Goal gpr_of_Z (uint (mword_of_int 1 : mword 5)) = x1
    /\ gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ uint (mword_of_int 1 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpJalGprDemo.
