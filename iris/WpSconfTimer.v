(* WpSconfTimer.v -- the two Sstc timer leaves over [sconf]+[sie_cap]:

     wp_csrr_time_s_sconf      rdtime rd        (csrr rd, time     -- 0xC01)
     wp_csrw_stimecmp_s_sconf  csrw stimecmp,rs1                   (-- 0x14D)

   Both take the PERSISTENT [timer_cap] (TimerCap.v) and nothing else: it
   carries the mcounteren.TM = 1 pin that Supervisor access to both CSRs is
   gated on, and the invariant over the [stimecmp] cell that the write opens
   across its own step and reseals at the new deadline.  (The write's other
   gate, menvcfg.STCE = 1, [sconf] already gives us by pinning menvcfg =
   MENVCFG_S, whose bit 63 is set.)  So neither leaf threads any timer
   resource, and neither postcondition mentions one.

   The read value is NOT determined by anything the leaf owns: [time] reads
   mtime, which lives in the value-agnostic [clock_inv] and advances
   nondeterministically with the clock tick, so the continuation is
   ∀-quantified over the value read.  (No [clock_inv] opening is needed: the
   exec witness reads mtime straight off the abstract step state σ.)

   The exec-layer reductions below are S-mode instances of the
   privilege-generic CSR frameworks in WpGprCsrrCommon.v / WpGprCsrwCommon.v;
   the per-CSR pieces ([exec_read_CSR_time], [exec_write_CSR_stimecmp],
   the id write/read callbacks) are privilege-free and come from
   WpGprCsrrB.v / WpGprCsrwB.v unchanged. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var ghost_map invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import RegFile.
Require Import MinstretInv InstrBytes WpGpr ExecCommon.
Require Import WpGprCsrrCommon WpGprCsrrB.
Require Import WpGprCsrwCommon WpGprCsrwB.
Require Import SmodeCore WpMmodeLeafBase.
Require Import StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import TimerCap.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. exec layer: [csrr rd, time] at Supervisor.                          *)
(* ===================================================================== *)

(* At Supervisor, [counter_enabled] is exactly "the mcounteren bit is set"
   (scounteren is read but its value only matters at User). *)
Lemma exec_counter_enabled_S (index : Z) s :
  eq_vec (access_vec_dec (register_lookup mcounteren s.(sregs)) index) ('b"1") = true ->
  exec (counter_enabled index Supervisor) s = Some (true, s).
Proof.
  intro HTM.
  unfold counter_enabled.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg scounteren s)).
  unfold feature_enabled_for_priv_bool.
  rewrite (exec_bind_Some _ _ _ _ _
    (_ : exec (feature_enabled_for_priv Supervisor _ _ _) s = Some (FEATURE_ENABLED, s))).
  2:{ unfold feature_enabled_for_priv. cbn match. rewrite HTM. apply exec_returnM. }
  apply exec_returnM.
Qed.

Lemma exec_is_CSR_accessible_time_S s :
  eq_vec (_get_Counteren_TM (register_lookup mcounteren s.(sregs))) ('b"1") = true ->
  exec (is_CSR_accessible csr_time Supervisor CSRRead) s = Some (true, s).
Proof.
  intro HTM.
  assert (Hred : is_CSR_accessible csr_time Supervisor CSRRead
                 = Defs.and_boolM (currentlyEnabled Ext_Zicntr) (counter_enabled 1 Supervisor))
    by csr_dispatch_eq.
  rewrite Hred.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Zicntr s)). cbn match.
  apply exec_counter_enabled_S. rewrite counteren_TM_access. exact HTM.
Qed.

Lemma exec_check_CSR_result_time_S s :
  eq_vec (_get_Counteren_TM (register_lookup mcounteren s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_time Supervisor CSRRead) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HTM.
  apply exec_check_CSR_result_read_p. apply exec_check_CSR_read_p.
  - assert (H : check_CSR_priv csr_time Supervisor = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - apply exec_is_CSR_accessible_time_S. exact HTM.
  - assert (H : stateen_allows_CSR_access csr_time Supervisor CSRRead = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrr_time_gpr_S (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Counteren_TM (register_lookup mcounteren s.(sregs))) ('b"1") = true ->
  exec (execute_CSRReg csr_time zreg (Regidx rd) CSRRS) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (time_rdval s))).
Proof.
  intros Hrd Hpriv HTM.
  apply (csrr_read_step_p Supervisor csr_time rd (time_rdval s) s _ Hpriv).
  - apply (exec_check_CSR_result_time_S s HTM).
  - vm_compute; reflexivity.
  - apply exec_read_CSR_time.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_csr_id_read_callback_time.
  - rewrite (exec_wX_bits_gpr rd (time_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ===================================================================== *)
(* 2. exec layer: [csrw stimecmp, rs1] at Supervisor.                     *)
(* ===================================================================== *)

Lemma exec_hartSupports_Sstc s : exec (hartSupports Ext_Sstc) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Sstc s : exec (currentlyEnabled Ext_Sstc) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Sstc.
Qed.

Lemma exec_is_stimecmp_accessible_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Counteren_TM (register_lookup mcounteren s.(sregs))) ('b"1") = true ->
  eq_vec (_get_MEnvcfg_STCE (register_lookup menvcfg s.(sregs))) ('b"1") = true ->
  exec (is_stimecmp_accessible Supervisor) s = Some (true, s).
Proof.
  intros HS HTM HSTCE.
  unfold is_stimecmp_accessible.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_S s)). rewrite HS. cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_currentlyEnabled_Sstc s)). cbn match.
  match goal with |- context[Defs.and_boolM ?A _] =>
    assert (HA : exec A s = Some (true, s)) end.
  { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mcounteren s)).
    rewrite (exec_returnM _ s). rewrite HTM. reflexivity. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ HA). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
  rewrite (exec_returnM _ s). rewrite HSTCE. reflexivity.
Qed.

Lemma exec_check_CSR_result_csrw_stimecmp_S s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Counteren_TM (register_lookup mcounteren s.(sregs))) ('b"1") = true ->
  eq_vec (_get_MEnvcfg_STCE (register_lookup menvcfg s.(sregs))) ('b"1") = true ->
  exec (check_CSR_result csr_stimecmp Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intros HS HTM HSTCE.
  apply exec_check_CSR_result_csrw_p. apply exec_check_CSR_csrw_p.
  - assert (H : check_CSR_priv csr_stimecmp Supervisor = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
  - vm_compute; reflexivity.
  - assert (Hred : is_CSR_accessible csr_stimecmp Supervisor CSRWrite
                   = is_stimecmp_accessible Supervisor) by csr_dispatch_eq.
    rewrite Hred. apply exec_is_stimecmp_accessible_S; assumption.
  - assert (H : stateen_allows_CSR_access csr_stimecmp Supervisor CSRWrite = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_returnm.
Qed.

Lemma exec_execute_csrw_stimecmp_S (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  eq_vec (_get_Counteren_TM (register_lookup mcounteren s.(sregs))) ('b"1") = true ->
  eq_vec (_get_MEnvcfg_STCE (register_lookup menvcfg s.(sregs))) ('b"1") = true ->
  exec (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg s stimecmp
              (stimecmp_legalized (register_lookup stimecmp s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HS HTM HSTCE.
  change (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_stimecmp (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr_p Supervisor csr_stimecmp rs1 s _
           (subrange_vec_dec
              (stimecmp_legalized (register_lookup stimecmp s.(sregs))
                 (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))
              (Z.sub xlen 1) 0)).
  - exact Hpriv.
  - apply exec_check_CSR_result_csrw_stimecmp_S; assumption.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_stimecmp.
  - apply exec_csr_id_write_callback_stimecmp.
Qed.

(* ===================================================================== *)
(* 3. The two leaves.                                                     *)
(* ===================================================================== *)
Section WpSconfTimer.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  (* ---- rdtime rd: rd := (an arbitrary) mtime reading ---- *)
  Lemma wp_csrr_time_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd <> csp_rs1 ->
    timer_cap -∗
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) -∗
    ( ∀ tv : mword 64,
      sie_cap_gpr γ (<[Regidx rd := regval_into_reg tv]> m) n -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrd Hrdsp) "#Htcap Hcg Hpc Hinstr Hcont".
    iDestruct "Htcap" as "[Hen _]".
    iDestruct "Hen" as (mcen) "[#Hmcen %HTM]".
    iApply (wp_instr_s_sconf γ m n Φ pc false
              (CSRReg (csr_time, zreg, Regidx rd, CSRRS))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hrest)".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmcen") as %Lmcen.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmcen_spc : register_lookup mcounteren s_pc.(sregs) = mcen)
      by (unfold s_pc; tmig; exact Lmcen).
    set (tv := time_rdval s_pc).
    iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg tv) with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg tv)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg tv)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      change (execute (CSRReg (csr_time, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_time zreg (Regidx rd) CSRRS).
      apply (exec_execute_csrr_time_gpr_S rd s_pc Hrd Lpriv_spc).
      rewrite Lmcen_spc. exact HTM. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg tv)).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg tv]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iDestruct (sie_cap_retarget γ m
                 (<[Regidx rd := regval_into_reg tv]> m) n Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join with "Hhs' [$Hhw $Hminv $Hpriv $Hrest] Hcap Hfile") as "Hcg".
    iApply ("Hcont" $! tv with "Hcg [$Hpc' $Hnpc]").
  Qed.

  (* ---- csrw stimecmp,rs1.  The deadline cell is NOT threaded: it lives in
     [timer_cap]'s invariant, opened across this one instruction step and
     resealed at the new deadline, so the whole precondition is persistent and
     the postcondition says nothing about the timer at all. ---- *)
  Lemma wp_csrw_stimecmp_s_sconf (γ : gname) (Φ : mval -> iProp Σ)
      (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (n : nat) :
    uint rs1 <> 0 ->
    timer_cap -∗
    sie_cap_gpr γ m n -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) -∗
    ( sie_cap_gpr γ m n -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hrs1) "#Htcap Hcg Hpc Hinstr Hcont".
    iDestruct "Htcap" as "[Hen #Hsinv]".
    iDestruct "Hen" as (mcen) "[#Hmcen %HTM]".
    iApply (wp_instr_s_sconf γ m n Φ pc false
              (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW))
              with "Hcg Hpc Hinstr").
    iIntros (σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iMod (inv_acc (⊤ ∖ ↑minstretN) timerN with "Hsinv") as "[Hbody Hclose]";
      [solve_ndisj|].
    iDestruct "Hbody" as (sc0) ">Hstc".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid    with "Hreg Hstc")  as %Lstc.
    iDestruct (reg_valid_dq with "Hreg Hmcen") as %Lmcen.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmenv_spc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lstc_spc : register_lookup stimecmp s_pc.(sregs) = sc0)
      by (unfold s_pc; tmig; exact Lstc).
    assert (Lmcen_spc : register_lookup mcounteren s_pc.(sregs) = mcen)
      by (unfold s_pc; tmig; exact Lmcen).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* the rs1 value: the gpr file pins it in the step state *)
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfile") as "[Hr1c Hfb]".
    iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hr1c") as %Lva.
    iDestruct ("Hfb" with "Hr1c") as "Hfile".
    assert (Lrs1 : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                   = m !!! Regidx rs1).
    { rewrite rf_lookup -Lva.
      replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1).
      reflexivity. }
    iMod (reg_update _ stimecmp _ (stimecmp_legalized sc0 (m !!! Regidx rs1))
            with "Hreg Hstc") as "[Hreg Hstc]".
    iMod ("Hclose" with "[Hstc]") as "_".
    { iNext. iApply (stimecmp_free_intro with "Hstc"). }
    iModIntro.
    iExists (set_reg s_pc stimecmp (stimecmp_legalized sc0 (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      rewrite (exec_execute_csrw_stimecmp_S rs1 s_pc Hrs1 Lpriv_spc
                 ltac:(rewrite Lmisa_spc; exact HmisaS)
                 ltac:(rewrite Lmcen_spc; exact HTM)
                 ltac:(rewrite Lmenv_spc Hmenvval; vm_compute; reflexivity)).
      rewrite Lstc_spc Lrs1. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc stimecmp (stimecmp_legalized sc0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (sie_cap_gpr_join with "Hhs' [Hpriv Hmsx Hmiex Hmenv] Hcap Hfile") as "Hcg".
    { iFrame "Hhw Hminv Hpriv Hmsx Hmiex".
      iExists menvcfg0. iFrame "Hmenv". iPureIntro.
      repeat split; assumption. }
    iApply ("Hcont" with "Hcg [$Hpc' $Hnpc]").
  Qed.

End WpSconfTimer.
