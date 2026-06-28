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
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.


Lemma exec_execute_RTYPE_OR (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) -> exec (rX_bits rs2) s = Some (b, s) ->
  exec (wX_bits rd (or_vec a b)) s = Some (tt, s') ->
  exec (execute_RTYPE rs2 rs1 rd OR) s = Some (RETIRE_SUCCESS, s').
Proof. intros Ha Hb Hw. unfold execute_RTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (or_vec a b) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). rewrite (exec_bind_Some _ _ _ _ _ Hb). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm. Qed.
Lemma exec_execute_RTYPE_AND (rs2 rs1 rd : regidx) (a b : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) -> exec (rX_bits rs2) s = Some (b, s) ->
  exec (wX_bits rd (and_vec a b)) s = Some (tt, s') ->
  exec (execute_RTYPE rs2 rs1 rd AND) s = Some (RETIRE_SUCCESS, s').
Proof. intros Ha Hb Hw. unfold execute_RTYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (and_vec a b) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). rewrite (exec_bind_Some _ _ _ _ _ Hb). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm. Qed.
Lemma exec_execute_ITYPE_ORI (imm : mword 12) (rs1 rd : regidx) (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (or_vec a (sign_extend' 64 imm))) s = Some (tt, s') ->
  exec (execute (ITYPE (imm, rs1, rd, ORI))) s = Some (RETIRE_SUCCESS, s').
Proof. intros Ha Hw.
  change (execute (ITYPE (imm, rs1, rd, ORI))) with (execute_ITYPE imm rs1 rd ORI).
  unfold execute_ITYPE. cbn match.
  rewrite (exec_bind_Some _ _ _ (or_vec a (sign_extend' 64 imm)) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ Ha). apply exec_returnm. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm. Qed.

(* ===== OR ===== *)
Definition gpr_or_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  or_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (if Z.eqb (uint rs2) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)).

Lemma exec_execute_RTYPE_OR_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) OR) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_or_val rs2 rs1 s))).
Proof.
  unfold gpr_or_val.
  eapply exec_execute_RTYPE_OR.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_rX_bits_gpr rs2 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.
Section ForwardOrGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs2 rs1 rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR), s0).

  Definition sAor : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcor : mstate := set_reg sAor nextPC (add_vec_int pc 4).
  Definition sXor : mstate :=
    set_reg s_pcor (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (gpr_or_val rs2 rs1 s_pcor)).
  Definition sTor : mstate := set_reg sXor PC (register_lookup nextPC sXor.(sregs)).
  Definition sFor : mstate :=
    if b then set_reg sTor minstret (add_vec_int (register_lookup minstret sTor.(sregs)) 1)
         else sTor.

  Lemma forward_exec_or_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFor).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAor.(sregs) = pc).
    { unfold sAor, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAor.(sregs) = Machine).
    { unfold sAor, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAor.(sregs) = HART_ACTIVE tt).
    { unfold sAor, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAor.(sregs))) ('b"1") = true).
    { unfold sAor, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAor.(sregs))) ('b"1") = false).
    { unfold sAor, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAor.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAor, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAor = Some (None, sAor)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAor _ (exec_currentlyEnabled_S sAor) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAor = Some (F_Base w, sAor)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAor
              = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR), sAor))
      by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR))) s_pcor
              = Some (RETIRE_SUCCESS, sXor)).
    { change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) OR).
      rewrite (exec_execute_RTYPE_OR_gpr rs2 rs1 rd s_pcor).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      reflexivity. }
    assert (Hha : exec (run_hart_active 0) sAor
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXor)).
    { exact (exec_hart_active_progress sAor sAor sXor sAor w
               (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sXor w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXor, s_pcor, sAor; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXor, s_pcor, sAor; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardOrGpr.
Lemma gpr_or_val_lookup (rs2 rs1 : mword 5) (t : mstate) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  gpr_or_val rs2 rs1 t
  = or_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) t.(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) t.(sregs)).
Proof.
  intros H1 H2. unfold gpr_or_val.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (Z.eqb (uint rs2) 0) with false by (symmetry; apply Z.eqb_neq; exact H2).
  reflexivity.
Qed.

Lemma gpr_or_val_file (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 : mword 5) (va vb : mword 64) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs) = vb ->
  gpr_or_val rs2 rs1 (s_pcor s pc b) = or_vec va vb.
Proof.
  intros H1 H2 Lva Lvb.
  rewrite (gpr_or_val_lookup rs2 rs1 (s_pcor s pc b) H1 H2).
  unfold s_pcor, sAor. unfold set_reg; cbn [sregs].
  do 4 (gpr_trans). rewrite Lva. rewrite Lvb. reflexivity.
Qed.
Section CleanOrGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 rd : mword 5) (mst0 : mword 64).
  Definition base_upd_or : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (gpr_or_val rs2 rs1 (s_pcor s pc b))))
      PC (add_vec_int pc 4).
  Definition sFcor : mstate :=
    if b then set_reg base_upd_or minstret (add_vec_int mst0 1) else base_upd_or.

  Lemma sFor_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFor s pc b rs2 rs1 rd = sFcor.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXor s pc b rs2 rs1 rd).(sregs) = add_vec_int pc 4).
    { unfold sXor; cbv zeta. unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTor s pc b rs2 rs1 rd = base_upd_or).
    { unfold sTor. rewrite Enpc. unfold sXor, s_pcor, sAor; cbv zeta.
      unfold base_upd_or, s_pcor, sAor. reflexivity. }
    unfold sFor, sFcor. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_or.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_or, set_reg; cbn [sregs].
      do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanOrGpr.
Section WpOrGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma wp_or_gpr (pc : mword 64) (w : mword 32) (rs2 rs1 rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (va vb vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1 <> 0 -> uint rs2 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
    m !! gpr_of_Z (uint rs2) = Some vb ->
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
       exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (or_vec va vb)]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hr1 Hr2 Hrd Hm1 Hm2 Hmd HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    (* read rs1, rs2 values out of the register file (non-destructively) *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (reg_valid_dq with "Hreg Hr2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hrdv : gpr_or_val rs2 rs1 (s_pcor s pc b1) = or_vec va vb)
      by (apply (gpr_or_val_file s pc b1 rs2 rs1 va vb Hr1 Hr2 Lrs1 Lrs2)).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcor s pc b1 rs2 rs1 rd (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFor_eq s pc b1 rs2 rs1 rd (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_or_gpr s pc b1 w rs2 rs1 rd Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_or_val rs2 rs1 (s_pcor s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrdv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (or_vec va vb)) with "Hrdc") as "Hfile".
    unfold sFcor, base_upd_or. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpOrGpr.
Section WpOrGprDemo.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  (* `add x5, x6, x7` : rd=x5, rs1=x6, rs2=x7.  Same lemma, instantiated. *)
  Definition wp_or_x5_x6_x7 (pc : mword 64) (w : mword 32) :=
    wp_or_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 7) (mword_of_int 6) (mword_of_int 5).
  (* `add x28, x1, x2` : rd=x28, rs1=x1, rs2=x2.  SAME lemma, different regs. *)
  Definition wp_or_x28_x1_x2 (pc : mword 64) (w : mword 32) :=
    wp_or_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 2) (mword_of_int 1) (mword_of_int 28).

  (* The concrete register operands resolve to the intended file entries. *)
  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 7 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpOrGprDemo.

(* ===== AND ===== *)
Definition gpr_and_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  and_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (if Z.eqb (uint rs2) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)).

Lemma exec_execute_RTYPE_AND_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) AND) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_and_val rs2 rs1 s))).
Proof.
  unfold gpr_and_val.
  eapply exec_execute_RTYPE_AND.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_rX_bits_gpr rs2 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.
Section ForwardAndGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs2 rs1 rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND), s0).

  Definition sAand : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcand : mstate := set_reg sAand nextPC (add_vec_int pc 4).
  Definition sXand : mstate :=
    set_reg s_pcand (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (gpr_and_val rs2 rs1 s_pcand)).
  Definition sTand : mstate := set_reg sXand PC (register_lookup nextPC sXand.(sregs)).
  Definition sFand : mstate :=
    if b then set_reg sTand minstret (add_vec_int (register_lookup minstret sTand.(sregs)) 1)
         else sTand.

  Lemma forward_exec_and_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFand).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAand.(sregs) = pc).
    { unfold sAand, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAand.(sregs) = Machine).
    { unfold sAand, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAand.(sregs) = HART_ACTIVE tt).
    { unfold sAand, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAand.(sregs))) ('b"1") = true).
    { unfold sAand, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAand.(sregs))) ('b"1") = false).
    { unfold sAand, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAand.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAand, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAand = Some (None, sAand)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAand _ (exec_currentlyEnabled_S sAand) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAand = Some (F_Base w, sAand)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAand
              = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND), sAand))
      by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND))) s_pcand
              = Some (RETIRE_SUCCESS, sXand)).
    { change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) AND).
      rewrite (exec_execute_RTYPE_AND_gpr rs2 rs1 rd s_pcand).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      reflexivity. }
    assert (Hha : exec (run_hart_active 0) sAand
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXand)).
    { exact (exec_hart_active_progress sAand sAand sXand sAand w
               (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sXand w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXand, s_pcand, sAand; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXand, s_pcand, sAand; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardAndGpr.
Lemma gpr_and_val_lookup (rs2 rs1 : mword 5) (t : mstate) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  gpr_and_val rs2 rs1 t
  = and_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) t.(sregs))
            (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) t.(sregs)).
Proof.
  intros H1 H2. unfold gpr_and_val.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (Z.eqb (uint rs2) 0) with false by (symmetry; apply Z.eqb_neq; exact H2).
  reflexivity.
Qed.

Lemma gpr_and_val_file (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 : mword 5) (va vb : mword 64) :
  uint rs1 <> 0 -> uint rs2 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs) = vb ->
  gpr_and_val rs2 rs1 (s_pcand s pc b) = and_vec va vb.
Proof.
  intros H1 H2 Lva Lvb.
  rewrite (gpr_and_val_lookup rs2 rs1 (s_pcand s pc b) H1 H2).
  unfold s_pcand, sAand. unfold set_reg; cbn [sregs].
  do 4 (gpr_trans). rewrite Lva. rewrite Lvb. reflexivity.
Qed.
Section CleanAndGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs2 rs1 rd : mword 5) (mst0 : mword 64).
  Definition base_upd_and : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (gpr_and_val rs2 rs1 (s_pcand s pc b))))
      PC (add_vec_int pc 4).
  Definition sFcand : mstate :=
    if b then set_reg base_upd_and minstret (add_vec_int mst0 1) else base_upd_and.

  Lemma sFand_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFand s pc b rs2 rs1 rd = sFcand.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXand s pc b rs2 rs1 rd).(sregs) = add_vec_int pc 4).
    { unfold sXand; cbv zeta. unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTand s pc b rs2 rs1 rd = base_upd_and).
    { unfold sTand. rewrite Enpc. unfold sXand, s_pcand, sAand; cbv zeta.
      unfold base_upd_and, s_pcand, sAand. reflexivity. }
    unfold sFand, sFcand. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_and.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_and, set_reg; cbn [sregs].
      do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanAndGpr.
Section WpAndGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma wp_and_gpr (pc : mword 64) (w : mword 32) (rs2 rs1 rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (va vb vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1 <> 0 -> uint rs2 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
    m !! gpr_of_Z (uint rs2) = Some vb ->
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
       exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (and_vec va vb)]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hr1 Hr2 Hrd Hm1 Hm2 Hmd HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    (* read rs1, rs2 values out of the register file (non-destructively) *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfile") as "[Hr2c Hfb2]".
    iDestruct (reg_valid_dq with "Hreg Hr2c") as %Lrs2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hrdv : gpr_and_val rs2 rs1 (s_pcand s pc b1) = and_vec va vb)
      by (apply (gpr_and_val_file s pc b1 rs2 rs1 va vb Hr1 Hr2 Lrs1 Lrs2)).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcand s pc b1 rs2 rs1 rd (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFand_eq s pc b1 rs2 rs1 rd (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_and_gpr s pc b1 w rs2 rs1 rd Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_and_val rs2 rs1 (s_pcand s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrdv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (and_vec va vb)) with "Hrdc") as "Hfile".
    unfold sFcand, base_upd_and. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpAndGpr.
Section WpAndGprDemo.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  (* `add x5, x6, x7` : rd=x5, rs1=x6, rs2=x7.  Same lemma, instantiated. *)
  Definition wp_and_x5_x6_x7 (pc : mword 64) (w : mword 32) :=
    wp_and_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 7) (mword_of_int 6) (mword_of_int 5).
  (* `add x28, x1, x2` : rd=x28, rs1=x1, rs2=x2.  SAME lemma, different regs. *)
  Definition wp_and_x28_x1_x2 (pc : mword 64) (w : mword 32) :=
    wp_and_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 2) (mword_of_int 1) (mword_of_int 28).

  (* The concrete register operands resolve to the intended file entries. *)
  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 7 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpAndGprDemo.

(* ===== ORI ===== *)
Definition gpr_ori_val (rs1 : mword 5) (imm : mword 12) (s : mstate) : mword 64 :=
  or_vec (if Z.eqb (uint rs1) 0 then zero_reg
           else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
          (sign_extend' 64 imm).

Lemma exec_execute_ITYPE_ORI_gpr (rs1 rd : mword 5) (imm : mword 12) s :
  exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, ORI))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_ori_val rs1 imm s))).
Proof.
  unfold gpr_ori_val.
  eapply exec_execute_ITYPE_ORI.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

Lemma gpr_ori_val_lookup (rs1 : mword 5) (imm : mword 12) (t : mstate) :
  uint rs1 <> 0 ->
  gpr_ori_val rs1 imm t
  = or_vec (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) t.(sregs))
            (sign_extend' 64 imm).
Proof.
  intros H1. unfold gpr_ori_val.
  replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  reflexivity.
Qed.

(* exec-level register-generic ADDI step (32-bit, F_Base): one lemma, ANY rd/rs1. *)
Section ForwardOriGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1 rd : mword 5) (imm : mword 12).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, ORI), s0).

  Definition sAori : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcori : mstate := set_reg sAori nextPC (add_vec_int pc 4).
  Definition sXori : mstate :=
    set_reg s_pcori (R_bitvector_64 (gpr_of_Z (uint rd)))
      (regval_into_reg (gpr_ori_val rs1 imm s_pcori)).
  Definition sTori : mstate := set_reg sXori PC (register_lookup nextPC sXori.(sregs)).
  Definition sFori : mstate :=
    if b then set_reg sTori minstret (add_vec_int (register_lookup minstret sTori.(sregs)) 1)
         else sTori.

  Lemma forward_exec_ori_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs)))
           ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFori).
  Proof using All.
    intros Lpc Lpriv Lhs LS LmIE Lelp.
    assert (LpcA  : register_lookup PC sAori.(sregs) = pc).
    { unfold sAori, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAori.(sregs) = Machine).
    { unfold sAori, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAori.(sregs) = HART_ACTIVE tt).
    { unfold sAori, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LSA : eq_vec (_get_Misa_S (register_lookup misa sAori.(sregs))) ('b"1") = true).
    { unfold sAori, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LS | vm_compute; reflexivity ]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE
              (register_lookup (R_bitvector_64 mstatus) sAori.(sregs))) ('b"1") = false).
    { unfold sAori, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact LmIE | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAori.(sregs))
              (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAori, set_reg; cbn [sregs]. rewrite irrelevant_register_set;
        [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAori = Some (None, sAori)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAori _ (exec_currentlyEnabled_S sAori) LSA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAori = Some (F_Base w, sAori)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAori
              = Some (ITYPE (imm, Regidx rs1, Regidx rd, ORI), sAori))
      by (apply Hdec; exact LprivA).
    assert (HexecG : exec (execute (ITYPE (imm, Regidx rs1, Regidx rd, ORI))) s_pcori
              = Some (RETIRE_SUCCESS, sXori)).
    { rewrite (exec_execute_ITYPE_ORI_gpr rs1 rd imm s_pcori).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd0).
      reflexivity. }
    assert (Hha : exec (run_hart_active 0) sAori
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXori)).
    { exact (exec_hart_active_progress sAori sAori sXori sAori w
               (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecG I). }
    apply (exec_riscv_step_ADD s sXori w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXori, s_pcori, sAori; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXori, s_pcori, sAori; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardOriGpr.

Lemma gpr_ori_val_file (s : mstate) (pc : mword 64) (b : bool) (rs1 : mword 5) (imm : mword 12) (va : mword 64) :
  uint rs1 <> 0 ->
  register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs) = va ->
  gpr_ori_val rs1 imm (s_pcori s pc b) = or_vec va (sign_extend' 64 imm).
Proof.
  intros H1 Lva.
  rewrite (gpr_ori_val_lookup rs1 imm (s_pcori s pc b) H1).
  unfold s_pcori, sAori. unfold set_reg; cbn [sregs].
  do 2 gpr_trans. rewrite Lva. reflexivity.
Qed.

Section CleanOriGpr.
  Context (s : mstate) (pc : mword 64) (b : bool) (rs1 rd : mword 5) (imm : mword 12) (mst0 : mword 64).
  Definition base_upd_ori : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b)
                  nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (gpr_ori_val rs1 imm (s_pcori s pc b))))
      PC (add_vec_int pc 4).
  Definition sFcori : mstate :=
    if b then set_reg base_upd_ori minstret (add_vec_int mst0 1) else base_upd_ori.

  Lemma sFori_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFori s pc b rs1 rd imm = sFcori.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXori s pc b rs1 rd imm).(sregs) = add_vec_int pc 4).
    { unfold sXori; cbv zeta. unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTori s pc b rs1 rd imm = base_upd_ori).
    { unfold sTori. rewrite Enpc. unfold sXori, s_pcori, sAori; cbv zeta.
      unfold base_upd_ori, s_pcori, sAori. reflexivity. }
    unfold sFori, sFcori. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_ori.(sregs)
                   = register_lookup minstret s.(sregs)).
    { unfold base_upd_ori, set_reg; cbn [sregs]. do 4 tmig. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanOriGpr.

(* ====================================================================== *)
(* The register-GENERIC addi WP: ONE lemma for `addi rd,rs1,imm`, ANY      *)
(* rd/rs1, with all GPRs held as the single [gpr_file] resource.           *)
(* ====================================================================== *)
Section WpOriGpr.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.

  Lemma wp_ori_gpr (pc : mword 64) (w : mword 32) (rs1 rd : mword 5) (imm : mword 12)
      (m : gmap register_bitvector_64 (mword 64)) (va vd misa0 mdv0 : mword 64)
      (b1 : bool) (npc0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (elp0 : mword 1) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rs1 <> 0 -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rs1) = Some va ->
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
       exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, ORI), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ pc -∗ gpr_file m -∗ reg_pointsto misa dqc misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (or_vec va (sign_extend' 64 imm))]> m) -∗
        reg_pointsto misa dqc misa0 -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ reg_pointsto mcountinhibit dqc mc -∗ reg_pointsto minstretcfg dqc mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ reg_pointsto pma_regions dqc pmar0 -∗ reg_pointsto htif_tohost_base dqc None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hr1 Hrd Hm1 Hmd HS Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "#Hinv Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (fetch_pa pc) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid_dq with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid_dq with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhs")    as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmdl")   as %Lmdl.
    iDestruct (reg_valid_dq with "Hreg Hmisa")  as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid_dq with "Hreg Help")   as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmcinh") as %Lmc.
    iDestruct (reg_valid_dq with "Hreg Hmcfg")  as %Lmcfg.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfile") as "[Hr1c Hfb1]".
    iDestruct (reg_valid_dq with "Hreg Hr1c") as %Lrs1.
    iDestruct ("Hfb1" with "Hr1c") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hav : gpr_ori_val rs1 imm (s_pcori s pc b1) = or_vec va (sign_extend' 64 imm))
      by (apply (gpr_ori_val_file s pc b1 rs1 imm va Hr1 Lrs1)).
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iModIntro.
    iExists (sFcori s pc b1 rs1 rd imm (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (sFori_eq s pc b1 rs1 rd imm (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_ori_gpr s pc b1 w rs1 rd imm Hfetch_at Hsi_s Hrd Hdec
               Lpc Lpriv Lhs).
      - rewrite Lmisa. exact HS.
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (gpr_ori_val rs1 imm (s_pcori s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hav) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (or_vec va (sign_extend' 64 imm))) with "Hrdc") as "Hfile".
    unfold sFcori, base_upd_ori. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa Hnpc Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpOriGpr.

(* Demonstration: ONE lemma [wp_ori_gpr] serves many (rd,rs1) pairs. *)
Section WpOriGprDemo.
  Context `{!riscvGS Σ}.
  Context {dqc : dfrac}.
  Definition wp_ori_x5_x6 (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_ori_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 6) (mword_of_int 5) imm.   (* addi x5, x6, imm *)
  Definition wp_ori_x28_x1 (pc : mword 64) (w : mword 32) (imm : mword 12) :=
    wp_ori_gpr (dqc:=DfracOwn 1) pc w (mword_of_int 1) (mword_of_int 28) imm.  (* addi x28, x1, imm *)
  Goal gpr_of_Z (uint (mword_of_int 6 : mword 5)) = x6
    /\ gpr_of_Z (uint (mword_of_int 28 : mword 5)) = x28
    /\ uint (mword_of_int 1 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpOriGprDemo.
