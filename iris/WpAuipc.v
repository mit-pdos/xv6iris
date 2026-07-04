(* WpAuipc.v -- the AUIPC opcode: execute reduction, forward_exec_auipc, wp_step_auipc. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

(* --- get_arch_pc reads PC (state-pure). --- *)
Lemma run_get_arch_pc s :
  run (get_arch_pc tt) s (register_lookup PC s.(sregs)) s.
Proof. unfold get_arch_pc. exact (run_read_reg_fwd PC s). Qed.

Lemma exec_get_arch_pc s :
  exec (get_arch_pc tt) s = Some (register_lookup PC s.(sregs), s).
Proof. unfold get_arch_pc. exact (exec_read_reg PC s). Qed.

(* --- execute (UTYPE imm rd AUIPC): read PC, add imm<<12, write rd, retire. --- *)
Definition auipc_off (imm : mword 20) : mword 64 :=
  sign_extend' 64 (concat_vec imm (Ox"000")).

Lemma exec_execute_UTYPE_AUIPC (i : mword 5) (imm : mword 20) s :
  uint i = 2 ->
  exec (execute_UTYPE imm (Regidx i) AUIPC) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 x2)
            (regval_into_reg
               (add_vec (register_lookup PC s.(sregs)) (auipc_off imm)))).
Proof.
  intro Hi.
  unfold execute_UTYPE, auipc_off. cbn match.
  rewrite (exec_bind_Some _ _ _
             (add_vec (register_lookup PC s.(sregs))
                      (sign_extend' 64 (concat_vec imm (Ox"000")))) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_get_arch_pc s)). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_x2 i s _ Hi)). apply exec_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* forward_exec_auipc: thread the generic try_step wrapper + the generic    *)
(* run_hart_active progress engine around the AUIPC execute leaf.           *)
(* Hypotheses mirror forward_exec_final's: universally-quantified fetch /    *)
(* decode / should_inc facts + booting-Machine register conditions.         *)
(* ---------------------------------------------------------------------- *)

Section ForwardAUIPC.
  Context (s : mstate) (w : mword 32) (pc : mword 64) (imm : mword 20)
          (i : mword 5) (b : bool).

  Hypothesis Hi : uint i = 2.
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hdec_gen : forall s0 : mstate,
    register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx i, AUIPC), s0).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).

  Definition sAa : mstate := set_reg s (R_bool minstret_increment) b.
  Definition sXa : mstate :=
    let s1 := set_reg sAa nextPC (add_vec_int pc 4) in
    set_reg s1 (R_bitvector_64 x2)
      (regval_into_reg (add_vec (register_lookup PC s1.(sregs)) (auipc_off imm))).
  Definition sTa : mstate := set_reg sXa PC (register_lookup nextPC sXa.(sregs)).
  Definition sFa : mstate :=
    if b then set_reg sTa minstret
                  (add_vec_int (register_lookup minstret sTa.(sregs)) 1)
         else sTa.

  Lemma forward_exec_auipc :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFa).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    (* booting-config reads transfer through the minstret_increment write. *)
    assert (LpcA  : register_lookup PC sAa.(sregs) = pc).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAa.(sregs) = Machine).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAa.(sregs) = HART_ACTIVE tt).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAa.(sregs))) ('b"1") = true).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAa.(sregs))) ('b"1") = false).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAa.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAa, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    (* dispatchInterrupt = None at sAa via the getPendingSet keystone;
       currentlyEnabled Ext_S reduces for any state (exec_currentlyEnabled_S). *)
    assert (HdispA : exec (dispatchInterrupt Machine) sAa = Some (None, sAa)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAa _ (exec_currentlyEnabled_S sAa) LSA LmIEA). }
    (* fetch / decode at sAa (state-preserving). *)
    assert (HfetchA : exec (fetch tt) sAa = Some (F_Base w, sAa))
      by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAa = Some (UTYPE (imm, Regidx i, AUIPC), sAa))
      by (apply Hdec_gen; exact LprivA).
    (* execute leaf at s_pc = set_reg sAa nextPC (pc+4). *)
    pose (s_pc := set_reg sAa nextPC (add_vec_int pc 4)).
    assert (HpcPCpc : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LpcA | vm_compute; reflexivity ]. }
    assert (HexecA : exec (execute (UTYPE (imm, Regidx i, AUIPC))) s_pc
              = Some (RETIRE_SUCCESS, sXa)).
    { change (execute (UTYPE (imm, Regidx i, AUIPC)))
        with (execute_UTYPE imm (Regidx i) AUIPC).
      unfold sXa. fold s_pc.
      exact (exec_execute_UTYPE_AUIPC i imm s_pc Hi). }
    (* the run_hart_active reduction (exact value) via the generic engine. *)
    assert (Hha : exec (run_hart_active 0) sAa
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXa)).
    { exact (exec_hart_active_progress sAa sAa sXa sAa w
               (UTYPE (imm, Regidx i, AUIPC)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecA I). }
    (* the generic try_step wrapper. *)
    apply (exec_riscv_step_ADD s sXa w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - (* hart_state at sXa = HART_ACTIVE tt *)
      unfold sXa, sAa; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - (* minstret_increment at sXa = b *)
      unfold sXa, sAa; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity. (* Hrvfi : get_config_rvfi tt = false -- definitional *)
  Qed.

  (* clean-form post-state (concrete values), mirror of base_upd/sFc/sF_eq. *)
  Variable mst0 : mword 64.
  Hypothesis Lmst_a : register_lookup minstret s.(sregs) = mst0.

  Definition base_upd_a : mstate :=
    set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b)
                              nextPC (add_vec_int pc 4))
                     (R_bitvector_64 x2) (regval_into_reg (add_vec pc (auipc_off imm))))
            PC (add_vec_int pc 4).
  Definition sFca : mstate :=
    if b then set_reg base_upd_a minstret (add_vec_int mst0 1)
         else base_upd_a.

  Ltac tmiss := rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].

  Lemma sFa_eq : register_lookup PC s.(sregs) = pc -> sFa = sFca.
  Proof.
    intro LpcS.
    assert (Enpc : register_lookup nextPC sXa.(sregs) = add_vec_int pc 4).
    { unfold sXa; cbv zeta. unfold set_reg; cbn [sregs]. tmiss.
      rewrite register_lookup_set. reflexivity. }
    assert (Epc1 : register_lookup PC (set_reg sAa nextPC (add_vec_int pc 4)).(sregs) = pc).
    { unfold sAa, set_reg; cbn [sregs]. tmiss. tmiss. exact LpcS. }
    assert (HsT : sTa = base_upd_a).
    { unfold sTa. rewrite Enpc. unfold sXa; cbv zeta. rewrite Epc1.
      unfold regval_into_reg, base_upd_a, sAa. reflexivity. }
    unfold sFa, sFca. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_a.(sregs) = register_lookup minstret s.(sregs)).
    { unfold base_upd_a, set_reg; cbn [sregs]. tmiss. tmiss. tmiss. tmiss. reflexivity. }
    rewrite Emst Lmst_a. reflexivity.
  Qed.

End ForwardAUIPC.

Section StepAUIPC.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context {dqc : dfrac}.
  Lemma wp_step_auipc (pc : mword 64) (w_a : mword 32) (imm_a : mword 20)
      (i_a : mword 5) (b1 : bool) (sp0a npc0a mstatus0a misa0 mdv0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0a : mword 1) E {dq : dfrac} (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint i_a = 2 ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (* the pure fetch side-conditions of [fetch_from_pts_minstret] *)
    pma_allows_all pmar0 ->
    pmp_allows_all pmpcfg0 ->
        is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w_a 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w_a) s0 = Some (UTYPE (imm_a, Regidx i_a, AUIPC), s0)) ->
    (* should_inc is now DETERMINED by the mcountinhibit/minstretcfg cells: *)
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0a) ('b"1") = false ->
    eq_vec elp0a (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ (R_bitvector_64 x2) ↦ᵣ sp0a -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0a -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
    elp ↦ᵣ elp0a -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_a j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        (R_bitvector_64 x2) ↦ᵣ regval_into_reg (add_vec pc (auipc_off imm_a)) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0a -∗
        elp ↦ᵣ elp0a -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w_a j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hia HS Hpmaall Hpmpf Hvalignf HnotRVCf Hda Hb1 HmIE Help)
      "#Hinv Hpc Hx2 Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    (* derive the state-specific fetch fact from the owned instruction bytes *)
    iDestruct (fetch_from_pts_minstret pc w_a region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    (* [apply empty_subseteq] not [set_solver]: the latter runs set_unfold over the
       whole context and blows up on heavy hypotheses (see WpLoad.v). *)
    iModIntro.
    iExists (sFca s pc imm_a b1 (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFa_eq s w_a pc imm_a b1 Hfetch_at Hsi_s (register_lookup minstret s.(sregs)) eq_refl Lpc).
      apply (forward_exec_auipc s w_a pc imm_a i_a b1 Hia Hfetch_at Hda Hsi_s Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 x2) _ (regval_into_reg (add_vec pc (auipc_off imm_a)))
            with "Hreg Hx2") as "[Hreg Hx2]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    unfold sFca, base_upd_a. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hx2 Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hx2 Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* Single-step WP for `ld rd,imm(rs1)` (rs1=rd=x2), via wp_exec_step +     *)
  (* forward_exec_ld + sFl_eq, discharging Hexec_spc via exec_execute_LOAD_8.*)
  (* ---------------------------------------------------------------------- *)
End StepAUIPC.
