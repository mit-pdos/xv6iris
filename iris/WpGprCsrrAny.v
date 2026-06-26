From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpEntry WpGpr WpGprCsrr.
Local Open Scope Z_scope.

(* Generic register-generic CSR-read step: csrr rd, csr  (= csrrs rd,csr,rs1z with
   rs1z = x0).  Parameterised over the CSR; the per-CSR facts (accessibility,
   read value, callback) are supplied as hypotheses. *)
Lemma csrr_read_step (csr : mword 12) (rs1z rd : mword 5) (readval : mword 64) (s s_w : mstate) :
  uint rs1z = 0 ->
  generic_eq (Regidx rs1z) zreg = true ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (check_CSR_result csr Machine CSRRead) s = Some (CSR_Check_OK tt, s) ->
  ext_check_CSR csr Machine CSRRead = true ->
  exec (read_CSR csr) s = Some (readval, s) ->
  eq_vec csr ((Ox"344") : mword 12) = false ->
  eq_vec csr ((Ox"144") : mword 12) = false ->
  exec (csr_id_read_callback csr readval) s = Some (tt, s) ->
  exec (wX_bits (Regidx rd) readval) s = Some (tt, s_w) ->
  exec (execute_CSRReg csr (Regidx rs1z) (Regidx rd) CSRRS) s = Some (RETIRE_SUCCESS, s_w).
Proof.
  intros Hrs1 Hz Hpriv Hchk Hext Hread H344 H144 Hcb Hwx.
  unfold execute_CSRReg.
  replace (generic_eq (Regidx rs1z) zreg) with true by (symmetry; exact Hz).
  rewrite csr_access_type_CSRRS_true.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_x0 rs1z s Hrs1)).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hext. cbn match.
  replace (if generic_neq CSRRead CSRWrite then read_CSR csr else returnM (zeros' 64))
    with (read_CSR csr) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hread).
  rewrite H344. rewrite H144. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM readval s)).
  replace (generic_eq CSRRead CSRRead) with true by reflexivity. cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _
    (_ : exec (Defs.bind0 (csr_id_read_callback csr readval) (wX_bits (Regidx rd) readval)) s
         = Some (tt, s_w))).
  2:{ rewrite (exec_bind0_Some _ _ _ _ _ Hcb). exact Hwx. }
  apply exec_returnM.
Qed.

(* ===== mstatus (0x300): machine CSR, accessible (vm), read = subrange of mstatus ===== *)
Definition csr_mstatus : mword 12 := Ox"300".
Definition mstatus_rdval (s : mstate) : mword 64 :=
  subrange_vec_dec (register_lookup mstatus s.(sregs)) (Z.sub xlen 1) 0.

Lemma exec_read_CSR_mstatus s :
  exec (read_CSR csr_mstatus) s = Some (mstatus_rdval s, s).
Proof.
  unfold read_CSR, csr_mstatus, mstatus_rdval.
  replace (eq_vec (Ox"300" : mword 12) (Ox"301")) with false by (vm_compute; reflexivity).
  cbn match.
  replace (andb (Z.eqb xlen 64) (eq_vec (Ox"300" : mword 12) (Ox"300"))) with true
    by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  apply exec_returnM.
Qed.

Lemma exec_check_CSR_result_mstatus s :
  exec (check_CSR_result csr_mstatus Machine CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  unfold check_CSR_result, csr_mstatus.
  assert (H : check_CSR (Ox"300") Machine CSRRead = returnM true) by (vm_compute; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (check_CSR (Ox"300") Machine CSRRead) s = Some (true, s))).
  2:{ rewrite H. apply exec_returnm. }
  apply (exec_returnM (CSR_Check_OK tt) s).
Qed.

Lemma exec_csr_id_read_callback_mstatus s d :
  exec (csr_id_read_callback csr_mstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_mstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_mstatus_gpr (rs1z rd : mword 5) s :
  uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec (execute_CSRReg csr_mstatus (Regidx rs1z) (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (mstatus_rdval s))).
Proof.
  intros Hrs1 Hz Hrd Hpriv.
  apply (csrr_read_step csr_mstatus rs1z rd (mstatus_rdval s) s _ Hrs1 Hz Hpriv).
  - apply exec_check_CSR_result_mstatus.
  - vm_compute; reflexivity.
  - apply exec_read_CSR_mstatus.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_mstatus.
  - rewrite (exec_wX_bits_gpr rd (mstatus_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* mstatus is untouched by the post-fetch sets, so its read value carries through. *)
Lemma mstatus_rdval_pcc (s : mstate) (mi : bool) (np : mword 64) :
  mstatus_rdval (set_reg (set_reg s (R_bool minstret_increment) mi) nextPC np) = mstatus_rdval s.
Proof.
  unfold mstatus_rdval, set_reg; cbn [sregs].
  do 2 (rewrite irrelevant_register_set; [|vm_compute; reflexivity]). reflexivity.
Qed.

Section ForwardCsrrMstatus.
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (rs1z rd : mword 5).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Machine) s = Some (b, s).
  Hypothesis Hrs1 : uint rs1z = 0.
  Hypothesis Hz : generic_eq (Regidx rs1z) zreg = true.
  Hypothesis Hrd0 : uint rd <> 0.
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
    exec (ext_decode w) s0 = Some (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS), s0).

  Definition sAm0 : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcm0 : mstate := set_reg sAm0 nextPC (add_vec_int pc 4).
  Definition sXm0 : mstate :=
    set_reg s_pcm0 (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (mstatus_rdval s_pcm0)).
  Definition sTm0 : mstate := set_reg sXm0 PC (register_lookup nextPC sXm0.(sregs)).
  Definition sFm0 : mstate :=
    if b then set_reg sTm0 minstret (add_vec_int (register_lookup minstret sTm0.(sregs)) 1) else sTm0.

  Lemma forward_exec_csrr_mstatus_gpr :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Machine ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    register_lookup (R_bitvector_64 mideleg) s.(sregs) = zeros' 64 ->
    eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) s.(sregs))) ('b"1") = false ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFm0).
  Proof using All.
    intros Lpc Lpriv Lhs Lmideleg LmIE Lelp.
    assert (LpcA  : register_lookup PC sAm0.(sregs) = pc).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (LprivA: register_lookup cur_privilege sAm0.(sregs) = Machine).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (LhsA  : register_lookup hart_state sAm0.(sregs) = HART_ACTIVE tt).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhs | vm_compute; reflexivity]. }
    assert (LmidA : register_lookup (R_bitvector_64 mideleg) sAm0.(sregs) = zeros' 64).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmideleg | vm_compute; reflexivity]. }
    assert (LmIEA : eq_vec (_get_Mstatus_MIE (register_lookup (R_bitvector_64 mstatus) sAm0.(sregs))) ('b"1") = false).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LmIE | vm_compute; reflexivity]. }
    assert (LelpA : eq_vec (register_lookup elp sAm0.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lelp | vm_compute; reflexivity]. }
    assert (HdispA : exec (dispatchInterrupt Machine) sAm0 = Some (None, sAm0)).
    { apply exec_dispatchInterrupt_none.
      apply (exec_getPendingSet_machine_none sAm0 _ (exec_currentlyEnabled_S sAm0) LmidA LmIEA). }
    assert (HfetchA : exec (fetch tt) sAm0 = Some (F_Base w, sAm0)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAm0 = Some (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS), sAm0))
      by (apply Hdec; exact LprivA).
    assert (LprivC : register_lookup cur_privilege s_pcm0.(sregs) = Machine).
    { unfold s_pcm0, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact LprivA | vm_compute; reflexivity]. }
    assert (HexecC : exec (execute (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS))) s_pcm0
              = Some (RETIRE_SUCCESS, sXm0)).
    { change (execute (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_mstatus (Regidx rs1z) (Regidx rd) CSRRS).
      unfold sXm0. exact (exec_execute_csrr_mstatus_gpr rs1z rd s_pcm0 Hrs1 Hz Hrd0 LprivC). }
    assert (Hha : exec (run_hart_active 0) sAm0
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sXm0)).
    { exact (exec_hart_active_progress sAm0 sAm0 sXm0 sAm0 w
               (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS)) pc RETIRE_SUCCESS
               LprivA HdispA HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecC I). }
    apply (exec_riscv_step_ADD s sXm0 w b pc).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXm0, s_pcm0, sAm0; cbn zeta. trans_mi. trans_mi. trans_mi. exact Lhs.
    - unfold sXm0, s_pcm0, sAm0; cbn zeta. trans_mi. trans_mi.
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.
End ForwardCsrrMstatus.

Ltac reg_ne_m := solve [ vm_compute; reflexivity | (unfold gpr_of_Z; repeat case_match; reflexivity) ].
Ltac tmim0 := rewrite irrelevant_register_set; [ | reg_ne_m ].

Section CleanCsrrMstatus.
  Context (s : mstate) (pc : mword 64) (b : bool) (rd : mword 5) (mst0 : mword 64).
  Definition base_upd_m0 : mstate :=
    set_reg
      (set_reg
         (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
         (R_bitvector_64 (gpr_of_Z (uint rd)))
         (regval_into_reg (mstatus_rdval (s_pcm0 s pc b))))
      PC (add_vec_int pc 4).
  Definition sFcm0 : mstate :=
    if b then set_reg base_upd_m0 minstret (add_vec_int mst0 1) else base_upd_m0.

  Lemma sFm0_eq :
    register_lookup PC s.(sregs) = pc ->
    register_lookup minstret s.(sregs) = mst0 ->
    sFm0 s pc b rd = sFcm0.
  Proof.
    intros LpcS LmstS.
    assert (Enpc : register_lookup nextPC (sXm0 s pc b rd).(sregs) = add_vec_int pc 4).
    { unfold sXm0; cbv zeta. unfold set_reg; cbn [sregs]. tmim0. rewrite register_lookup_set. reflexivity. }
    assert (HsT : sTm0 s pc b rd = base_upd_m0).
    { unfold sTm0. rewrite Enpc. unfold sXm0, s_pcm0, sAm0; cbv zeta.
      unfold base_upd_m0, s_pcm0, sAm0. reflexivity. }
    unfold sFm0, sFcm0. rewrite HsT. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret base_upd_m0.(sregs) = register_lookup minstret s.(sregs)).
    { unfold base_upd_m0, set_reg; cbn [sregs]. do 4 tmim0. reflexivity. }
    rewrite Emst LmstS. reflexivity.
  Qed.
End CleanCsrrMstatus.

Section WpCsrrMstatus.
  Context `{!riscvGS Σ}.
  Lemma wp_csrr_mstatus_gpr (pc : mword 64) (w : mword 32) (rs1z rd : mword 5)
      (m : gmap register_bitvector_64 (mword 64)) (vd : mword 64)
      (b1 : bool) (npc0 mst0 mstatus0 : mword 64)
      (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmar0 : list PMA_Region)
      (mi0 : bool) (elp0 : mword 1) E (Phi : mval -> iProp Σ) :
    uint rs1z = 0 -> generic_eq (Regidx rs1z) zreg = true -> uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    pma_allows_all pmar0 -> pmp_allows_all pmpcfg0 ->
    is_aligned_paddr (Physaddr (fetch_pa pc)) 4 = true ->
    neq_vec (access_vec_dec pc 0) ('b"0") = false ->
    neq_vec (access_vec_dec pc 1) ('b"0") = false ->
    is_aligned_vaddr (Virtaddr pc) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (forall s0, register_lookup cur_privilege (sregs s0) = Machine ->
       exec (ext_decode w) s0 = Some (CSRReg (csr_mstatus, Regidx rs1z, Regidx rd, CSRRS), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0")) (eq_vec (counter_priv_filter_bit mcfg Machine) ('b"0")) ->
    eq_vec (_get_Mstatus_MIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    PC ↦ᵣ pc -∗ gpr_file m -∗ nextPC ↦ᵣ npc0 -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗ minstret ↦ᵣ mst0 -∗
    cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int pc 4 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0)]> m) -∗
        nextPC ↦ᵣ add_vec_int pc 4 -∗ (R_bool minstret_increment) ↦ᵣ b1 -∗
        minstret ↦ᵣ (if b1 then add_vec_int mst0 1 else mst0) -∗
        cur_privilege ↦ᵣ Machine -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ zeros' 64 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (fetch_pa pc) j) ↦ₘ nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (Hrs1 Hz Hrd Hmd Hpmaall Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf Hdec Hb1 HmIE Help)
      "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes Hcont".
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
    assert (Hsi_s : exec (should_inc_minstret Machine) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_M mc mcfg s Lmc Lmcfg). }
    assert (Hrv : mstatus_rdval (s_pcm0 s pc b1) = subrange_vec_dec mstatus0 (Z.sub xlen 1) 0).
    { unfold s_pcm0, sAm0. rewrite mstatus_rdval_pcc. unfold mstatus_rdval. rewrite Lms. reflexivity. }
    iDestruct (fetch_from_pts_minstret pc w region_f pmpcfg0 pmar0 b1 s
                 Hmatchf Hexecf Hpmpf Halignf Hbit0f Hbit1f Hvalignf HnotRVCf
                 with "Hreg Hmem Hpc Hpriv Hpmpc Hpma Hhtif Hibytes") as %Hfetch_at.
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iExists (sFcm0 s pc b1 rd mst0). iSplitR.
    { iPureIntro.
      rewrite <- (sFm0_eq s pc b1 rd mst0 Lpc Lmst).
      apply (forward_exec_csrr_mstatus_gpr s pc b1 w rs1z rd Hfetch_at Hsi_s Hrs1 Hz Hrd Hdec
               Lpc Lpriv Lhs Lmdl).
      - rewrite Lms. exact HmIE.
      - rewrite Lelp. exact Help. }
    iIntros "!>".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (mstatus_rdval (s_pcm0 s pc b1))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpc") as "[Hreg Hpc]".
    iEval (rewrite Hrv) in "Hrdc".
    iDestruct ("Hfins" $! (regval_into_reg (subrange_vec_dec mstatus0 (Z.sub xlen 1) 0)) with "Hrdc") as "Hfile".
    unfold sFcm0, base_upd_m0. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int mst0 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
    - iMod "Hclose" as "_". iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iApply ("Hcont" with "Hpc Hfile Hnpc Hmi Hmst Hpriv Hhs Hmdl Hms Help Hmcinh Hmcfg Hpmpc Hpma Hhtif Hibytes").
  Qed.
End WpCsrrMstatus.

(* ===== read_CSR reductions for the other readable CSRs (deterministic reads).
   Their check_CSR (accessibility) needs Ext_U (menvcfg/mcounteren), Ext_S (sie),
   or Ext_Zicntr+counter_enabled (time), so the full csrr WP for these is gated on
   those currentlyEnabled facts (left to the chain).  The READ itself is pinned. *)
(* Use `replace ... by (vm_compute; reflexivity)` (NOT `change`): `change g with
   true` records a regular cast that the kernel re-verifies with its slow default
   conversion at Qed (>3 min EACH for the read_CSR guard chains — the cause of the
   ~12min compile); `replace ... by (vm_compute; reflexivity)` emits a vm-cast the
   kernel checks with the bytecode machine (0.09s).  See iris-build-perf CASE 4. *)
Ltac drive_csr :=
  unfold read_CSR;
  repeat (match goal with
          | |- context[if ?g then _ else _] =>
              let v := eval vm_compute in g in
              lazymatch v with
              | true  => replace g with true by (vm_compute; reflexivity)
              | false => replace g with false by (vm_compute; reflexivity)
              end
          end; cbn match).

Lemma exec_read_CSR_menvcfg s :
  exec (read_CSR (Ox"30A")) s
    = Some (subrange_vec_dec (register_lookup menvcfg s.(sregs)) (Z.sub xlen 1) 0, s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). apply exec_returnM. Qed.

Lemma exec_read_CSR_mcounteren s :
  exec (read_CSR (Ox"306")) s
    = Some (zero_extend' 64 (register_lookup mcounteren s.(sregs)), s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)). apply exec_returnM. Qed.

Lemma exec_read_CSR_sie s :
  exec (read_CSR (Ox"104")) s
    = Some (lower_mie (register_lookup mie s.(sregs)) (register_lookup mideleg s.(sregs)), s).
Proof.
  drive_csr.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)). apply exec_returnM.
Qed.

Lemma exec_read_CSR_time s :
  exec (read_CSR (Ox"C01")) s
    = Some (subrange_vec_dec (register_lookup mtime s.(sregs)) (Z.sub xlen 1) 0, s).
Proof. drive_csr. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mtime s)). apply exec_returnM. Qed.

(* ===== Demonstration: ONE wp_csrr_mstatus_gpr at two different destinations. ===== *)
Section WpCsrrMstatusDemo.
  Context `{!riscvGS Σ}.
  Definition wp_csrr_mstatus_x15 (pc : mword 64) (w : mword 32) := wp_csrr_mstatus_gpr pc w (mword_of_int 0) (mword_of_int 15).
  Definition wp_csrr_mstatus_x5  (pc : mword 64) (w : mword 32) := wp_csrr_mstatus_gpr pc w (mword_of_int 0) (mword_of_int 5).
End WpCsrrMstatusDemo.
