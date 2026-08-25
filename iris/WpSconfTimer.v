(* ===================================================================== *)
(* THE PER-NODE PORT: THIS FILE IS DONE (2026-08-18).                     *)
(*                                                                        *)
(* Both leaves are converted, both statements unchanged, and each needed   *)
(* one shape that is new in this port:                                     *)
(*                                                                        *)
(* [wp_csrr_time_s_sconf]: Supervisor's [time] check is the one CSR        *)
(* legality check in the tree that mixes a PINNED read with an UNPINNED    *)
(* one -- mcounteren decides the answer and [TimerCap.sstc_enabled] pins   *)
(* it persistently, while scounteren is read and only matters at User -- so*)
(* it has no single [goodb] certificate ([hval_of_goodb] wants every read  *)
(* register owned) and no ∀-peel either (that cannot pin the one that      *)
(* matters).  At the [swp] layer the two mix freely, which is what          *)
(* [HartSCsr.swp_doCSR_r_obl_p]'s check OBLIGATION is for.  The read value *)
(* stays existential -- mtime is owned by nobody and the tick moves it --   *)
(* so the Q-carrying wrapper returns it and the leaf's own ∀ absorbs it;    *)
(* no clock cell and no [_clock] wrapper are needed.                       *)
(*                                                                        *)
(* [wp_csrw_stimecmp_s_sconf]: the deadline cell lives in [timerN] and the *)
(* model's [write_CSR 0x14D] touches it THREE times across a long stretch  *)
(* -- read old, write legalized, [clint_dispatch]'s own read, read back.   *)
(* Nothing has to span that: the invariant carries NO value information,   *)
(* so each touch is opened and closed on its own.  The two reads need no   *)
(* seam at all (a read of a register the caller does not own is ungated,   *)
(* [WpMmodeCsrSwp.swp_read_reg_any]) and the ONE write takes                *)
(* [HartSCsr.swp_write_reg_cellinv], which opens [timerN] around exactly   *)
(* that node.  What the leaf gives up is the ability to NAME the value the *)
(* write returns, which is why the engine is the existential-result one    *)
(* ([HartSCsr.swp_doCSR_w_ex_p]).  mip IS a clock cell, so this leaf takes *)
(* the [_clock] wrapper and hands [clock_res] back at the mip the CLINT    *)
(* refresh left.                                                          *)
(* ===================================================================== *)
(* WpSconfTimer.v -- the two Sstc timer leaves over [sconf]+[sie_cap]:

     wp_csrr_time_s_sconf rd        (csrr rd, time     -- 0xC01)
     wp_csrw_stimecmp_s_sconf stimecmp,rs1                   (-- 0x14D)

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
Require Import InstrBytes WpGpr ExecCommon.
Require Import WpGprCsrrCommon WpGprCsrrB.
Require Import WpGprCsrwCommon WpGprCsrwB.
Require Import WpMmodeLeafBase.
Require Import HartTp WpNext.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
(* the privilege-generic CSR swp engines and the frame kit at Supervisor *)
Require Import HartSCsr HartSwp HartMFrame HartLift HartSpan HartSpanChar
        HartMCycle HartRegNode HartGoodb WpDecodeBridge WpMmodeJump
        WpMmodeCsrSwp WpGprCsrwA.
Require Import TimerCap WpGprCsrwStimecmp MinstretInv.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
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
  exists mp : mword 64,
  exec (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg (set_reg s stimecmp
              (stimecmp_legalized (register_lookup stimecmp s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))) mip mp).
Proof.
  intros Hrs1 Hpriv HS HTM HSTCE.
  change (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_stimecmp (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false
          by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  destruct (WpGprCsrwB.exec_write_CSR_stimecmp
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) s)
    as [mp Hw].
  exists mp.
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
  - exact Hw.
  - apply exec_csr_id_write_callback_stimecmp.
Qed.

(* ===================================================================== *)
(* 3. The two leaves.                                                     *)
(* ===================================================================== *)
(* ===================================================================== *)
(* THE SUPERVISOR time CHECK, AT THE NODE LAYER.                          *)
(*                                                                        *)
(* This is the one CSR legality check in the tree that mixes a PINNED read *)
(* with an UNPINNED one: at Supervisor [counter_enabled] reads mcounteren  *)
(* -- whose TM bit decides the answer, and which [TimerCap.sstc_enabled]   *)
(* pins persistently -- and then reads scounteren, which nobody owns and   *)
(* whose value only matters at User.  So it has no single [goodb]          *)
(* certificate ([hval_of_goodb] wants every read register owned) and no    *)
(* ∀-peel either (that cannot pin the one that matters).  At the [swp]     *)
(* layer the two mix freely, which is what [HartSCsr.swp_doCSR_r_obl_p]'s  *)
(* check OBLIGATION exists for.                                           *)
(* ===================================================================== *)
Section TimeCheck.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Local Lemma hval_cE_Zicntr (D Drw : gset register) (rs : regstate) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (currentlyEnabled Ext_Zicntr) true rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    apply (hval_of_goodb D_m D Drw _ dstateS rs true
             (dm_sub D HD1 HD2 HD3) (agree_dm_S rs Hp Hs Hm)).
    - vm_compute. reflexivity.
    - apply exec_currentlyEnabled_Zicntr.
  Qed.

  Lemma swp_check_CSR_result_time_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (mcen : mword 32) :
    Drw ## Dro ->
    (R_bitvector_32 mcounteren : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_32 mcounteren) rs = mcen ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    eq_vec (_get_Counteren_TM mcen) ('b"1") = true ->
    gen_cert -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
    swp (check_CSR_result csr_time Supervisor CSRRead)
      (fun w => ⌜w = CSR_Check_OK tt⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmc HDpriv HDsec HDmisa Lmc Lpriv Lsec Lmisa HTM.
    iIntros "#Hcert Hrw Hro".
    unfold check_CSR_result.
    iApply (swp_bind_use _ _
              (fun w : bool => ⌜w = true⌝ ∗
                 hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
              _ with "[Hrw Hro] [-]").
    { unfold check_CSR, Defs.and_boolM.
      (* 1. the privilege gate: pure at this csr *)
      assert (H1 : check_CSR_priv csr_time Supervisor = returnM true)
        by (vm_compute; reflexivity).
      rewrite H1.
      iApply (swp_bind_use _ _
                (fun w : bool => ⌜w = true⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply swp_ret. by iFrame. }
      iIntros (x1) "(-> & Hrw & Hro)". cbn match.
      (* 2. the access-type gate: pure *)
      replace (check_CSR_access csr_time CSRRead) with true
        by (vm_compute; reflexivity).
      iApply (swp_bind_use _ _
                (fun w : bool => ⌜w = true⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply swp_ret. by iFrame. }
      iIntros (x2) "(-> & Hrw & Hro)". cbn match.
      (* 3. accessibility: Zicntr (goodb) AND the counter-enable bit *)
      assert (Hred : is_CSR_accessible csr_time Supervisor CSRRead
                     = Defs.and_boolM (currentlyEnabled Ext_Zicntr)
                         (counter_enabled 1 Supervisor)) by csr_dispatch_eq.
      rewrite Hred.
      iApply (swp_bind_use _ _
                (fun w : bool => ⌜w = true⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                _ with "[Hrw Hro] [-]").
      { unfold Defs.and_boolM.
        iApply (swp_bind_use _ _
                  (fun w : bool => ⌜w = true⌝ ∗
                     hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_span Drw Dro Df rs rs _ true Hdisj
                    (hval_cE_Zicntr (Drw ∪ Dro) Drw rs HDpriv HDsec HDmisa
                       Lpriv Lsec Lmisa) with "Hcert Hrw Hro"). }
        iIntros (y1) "(-> & Hrw & Hro)". cbn match.
        (* the counter-enable read: mcounteren PINNED, scounteren UNPINNED *)
        unfold counter_enabled.
        iApply (swp_bind_use _ _
                  (fun mc : mword 32 => ⌜mc = mcen⌝ ∗
                     hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_mono with "[] [-]");
            [| iApply (swp_read_reg_pinned Drw Dro Df rs
                         (R_bitvector_32 mcounteren) Hdisj HDmc
                         with "Hcert Hrw Hro") ].
          iIntros (mc) "(-> & Hrw & Hro)". rewrite Lmc. by iFrame. }
        iIntros (mc) "(-> & Hrw & Hro)".
        iApply (swp_bind_use _ _
                  (fun _ : mword 32 =>
                     hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_any (R_bitvector_32 scounteren) with "Hcert").
          iIntros (v). iFrame. }
        iIntros (sc) "[Hrw Hro]".
        unfold feature_enabled_for_priv_bool.
        iApply (swp_bind_use _ _
                  (fun f => ⌜f = FEATURE_ENABLED⌝ ∗
                     hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                  _ with "[Hrw Hro] [-]").
        { unfold feature_enabled_for_priv. cbn match.
          rewrite <- counteren_TM_access in HTM. rewrite HTM.
          iApply swp_ret. by iFrame. }
        iIntros (f) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame. }
      iIntros (x3) "(-> & Hrw & Hro)". cbn match.
      (* 4. the stateen gate: pure *)
      assert (H4 : stateen_allows_CSR_access csr_time Supervisor CSRRead
                   = returnM true) by (vm_compute; reflexivity).
      rewrite H4. iApply swp_ret. by iFrame. }
    iIntros (w) "(-> & Hrw & Hro)". cbn match.
    iApply swp_ret. by iFrame.
  Qed.

End TimeCheck.

(* ===================================================================== *)
(* THE stimecmp WRITE AT SUPERVISOR, AND THE SEAM THE SEALED CELL NEEDS.  *)
(*                                                                        *)
(* [TimerCap] keeps the deadline cell in an invariant, and the model's     *)
(* [write_CSR 0x14D] touches it THREE times across a long stretch: read    *)
(* old, write legalized, [clint_dispatch]'s own reads, read back.  Per     *)
(* node that is not a problem and needs no threading -- the invariant      *)
(* carries NO value information, so each touch is opened and closed on its *)
(* own: the two reads need nothing at all (a read of a register the caller *)
(* does not own is ungated, [WpMmodeCsrSwp.swp_read_reg_any]) and the one  *)
(* write takes [HartSCsr.swp_write_reg_cellinv].  What the leaf loses is   *)
(* the ability to NAME the value the write returns, which is why the       *)
(* engine here is [HartSCsr.swp_doCSR_w_ex_p].                             *)
(*                                                                        *)
(* [clint_dispatch] is [WpGprCsrwStimecmp.swp_clint_dispatch_false] one    *)
(* privilege over: the only thing in it that is not privilege-blind is the *)
(* three goodb transports, which are re-run at [dstateS] below.            *)
(* ===================================================================== *)
Section StimecmpSwp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Local Lemma hval_cE_Sstc_S (D Drw : gset register) (rs : regstate) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (currentlyEnabled Ext_Sstc) true rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    apply (hval_of_goodb D_m D Drw _ dstateS rs true
             (dm_sub D HD1 HD2 HD3) (agree_dm_S rs Hp Hs Hm)).
    - vm_compute. reflexivity.
    - apply exec_currentlyEnabled_Sstc.
  Qed.

  Local Lemma hval_cE_S_S (D Drw : gset register) (rs : regstate) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (currentlyEnabled Ext_S) true rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    apply (hval_of_goodb D_m D Drw _ dstateS rs true
             (dm_sub D HD1 HD2 HD3) (agree_dm_S rs Hp Hs Hm)).
    - vm_compute. reflexivity.
    - rewrite (exec_currentlyEnabled_S dstateS).
      replace (eq_vec (_get_Misa_S (register_lookup misa dstateS.(sregs)))
                 ('b"1")) with true by (vm_compute; reflexivity).
      reflexivity.
  Qed.

  Local Lemma hval_cb_mip_S (D Drw : gset register) (rs : regstate)
      (V : mword 64) :
    (cur_privilege : register) ∈ D -> (mseccfg : register) ∈ D ->
    (misa : register) ∈ D ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    hval D Drw rs (csr_name_write_callback "mip" V) tt rs.
  Proof.
    intros HD1 HD2 HD3 Hp Hs Hm.
    apply (hval_of_goodb D_m D Drw _ dstateS rs tt
             (dm_sub D HD1 HD2 HD3) (agree_dm_S rs Hp Hs Hm)).
    - vm_compute. reflexivity.
    - apply exec_csr_name_write_callback_mip.
  Qed.

  (* the CLINT refresh, ∀-peeled, at Supervisor.  Character-for-character
     [WpGprCsrwStimecmp.swp_clint_dispatch_false] with the three transports
     above in place of the Machine ones. *)
  Lemma swp_clint_dispatch_false_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (ip : mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    gen_cert -∗
    (R_bitvector_64 mip) ↦ᵣ ip -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (clint_dispatch false)
      (fun _ => (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpriv HDsec HDmisa Hpriv Hsec Hmisa.
    iIntros "#Hcert Hip Hrw Hro".
    unfold clint_dispatch.
    iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
    { iApply (swp_read_reg_any (R_bitvector_64 mip) with "Hcert").
      by iIntros (?). }
    iIntros (old_mip) "_".
    iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
    { iApply (swp_read_reg_any (R_bitvector_64 mip) with "Hcert").
      by iIntros (?). }
    iIntros (w0) "_".
    iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
    { iApply (swp_read_reg_any (R_bitvector_64 mtimecmp) with "Hcert").
      by iIntros (?). }
    iIntros (w1) "_".
    iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
    { iApply (swp_read_reg_any (R_bitvector_64 mtime) with "Hcert").
      by iIntros (?). }
    iIntros (w2) "_".
    iApply (swp_bind_use _ _
              (fun _ => (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                 hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
              with "[Hip Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => ∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z)%I _
                with "[Hip] [-]").
      { iApply (swp_mono with "[] [-]");
          [| iApply (swp_write_reg_cell (R_bitvector_64 mip) ip _
                       with "Hcert Hip") ].
        iIntros (u) "Hip". by iExists _. }
      iIntros (u) "Hip".
      unfold Defs.and_boolM.
      iApply (swp_bind_use _ _
                (fun b => ⌜b = true⌝ ∗ hreg_frame rs Drw ∗
                          hreg_frame_ro Df rs Dro)%I _ with "[Hrw Hro] [-]").
      { iApply (swp_span Drw Dro Df rs rs _ true Hdisj
                  (hval_cE_Sstc_S (Drw ∪ Dro) Drw rs HDpriv HDsec HDmisa
                     Hpriv Hsec Hmisa) with "Hcert Hrw Hro"). }
      iIntros (b) "(-> & Hrw & Hro)". cbn match.
      iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
      { iApply (swp_read_reg_any (R_bitvector_64 menvcfg) with "Hcert").
        by iIntros (?). }
      iIntros (w4) "_". iApply swp_ret. iFrame. }
    iIntros (w5) "(Hip & Hrw & Hro)".
    iApply (swp_bind_use _ _
              (fun _ => (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                 hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
              with "[Hip Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
                with "[Hip Hrw Hro] [-]").
      { iApply (swp_bind0_use _ _
                  (fun _ => ∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z)%I _
                  with "[Hip] [-]").
        { destruct w5.
          - iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
            { iApply (swp_read_reg_any (R_bitvector_64 mip) with "Hcert").
              by iIntros (?). }
            iIntros (w6) "_".
            iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
            { iApply (swp_read_reg_any (R_bitvector_64 stimecmp) with "Hcert").
              by iIntros (?). }
            iIntros (w7) "_".
            iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
            { iApply (swp_read_reg_any (R_bitvector_64 mtime) with "Hcert").
              by iIntros (?). }
            iIntros (w8) "_".
            iDestruct "Hip" as (z1) "Hip".
            iApply (swp_mono with "[] [-]");
              [| iApply (swp_write_reg_cell (R_bitvector_64 mip) z1 _
                           with "Hcert Hip") ].
            iIntros (u2) "Hip". by iExists _.
          - iApply swp_ret. iExact "Hip". }
        iIntros (u2) "Hip".
        change (get_config_print_clint tt) with false. cbn match.
        iApply swp_ret. iFrame. }
      iIntros (u3) "(Hip & Hrw & Hro)".
      unfold Defs.or_boolM.
      iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
      { iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
        { iApply (swp_read_reg_any (R_bitvector_64 mip) with "Hcert").
          by iIntros (?). }
        iIntros (w10) "_". iApply swp_ret. done. }
      iIntros (b2) "_". destruct b2; iApply swp_ret; iFrame. }
    iIntros (w11) "(Hip & Hrw & Hro)".
    destruct w11.
    - unfold read_mip.
      iApply (swp_bind_use _ _
                (fun _ => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
                with "[Hrw Hro] [-]").
      { iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
        { iApply (swp_read_reg_any (R_bitvector_64 mip) with "Hcert").
          by iIntros (?). }
        iIntros (w12) "_".
        unfold external_interrupts_pending.
        iApply (swp_bind_use _ _
                  (fun _ => hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
                  with "[Hrw Hro] [-]").
        { iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
          { iApply (swp_read_reg_any (R_bitvector_1 sig_meip) with "Hcert").
            by iIntros (?). }
          iIntros (w13) "_".
          iApply (swp_bind_use _ _
                    (fun b => ⌜b = true⌝ ∗ hreg_frame rs Drw ∗
                              hreg_frame_ro Df rs Dro)%I _
                    with "[Hrw Hro] [-]").
          { iApply (swp_span Drw Dro Df rs rs _ true Hdisj
                      (hval_cE_S_S (Drw ∪ Dro) Drw rs HDpriv HDsec HDmisa
                         Hpriv Hsec Hmisa) with "Hcert Hrw Hro"). }
          iIntros (b) "(-> & Hrw & Hro)". cbn match.
          iApply (swp_bind_use _ _ (fun _ => True)%I _ with "[] [-]").
          { iApply (swp_read_reg_any (R_bitvector_1 sig_seip) with "Hcert").
            by iIntros (?). }
          iIntros (w14) "_". iApply swp_ret. iFrame. }
        iIntros (w15) "(Hrw & Hro)". iApply swp_ret. iFrame. }
      iIntros (w16) "(Hrw & Hro)".
      iApply (swp_mono with "[Hip] [Hrw Hro]");
        [| iApply (swp_span Drw Dro Df rs rs _ tt Hdisj
                     (hval_cb_mip_S (Drw ∪ Dro) Drw rs w16 HDpriv HDsec HDmisa
                        Hpriv Hsec Hmisa) with "Hcert Hrw Hro") ].
      iIntros (u4) "(_ & Hrw & Hro)". iFrame.
    - iApply swp_ret. iFrame.
  Qed.

  (* the CSRWrite check at Supervisor: Ext_S and Ext_Sstc ride the goodb
     transports, and the two bits that actually gate the write -- mcounteren
     TM and menvcfg STCE -- are PINNED reads out of the five-cell frame. *)
  Lemma swp_check_CSR_result_stimecmp_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (mcen : mword 32) :
    Drw ## Dro ->
    (R_bitvector_32 mcounteren : register) ∈ Drw ∪ Dro ->
    (R_bitvector_64 menvcfg : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup (R_bitvector_32 mcounteren) rs = mcen ->
    register_lookup (R_bitvector_64 menvcfg) rs = MENVCFG_S ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    eq_vec (_get_Counteren_TM mcen) ('b"1") = true ->
    gen_cert -∗ hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
    swp (check_CSR_result csr_stimecmp Supervisor CSRWrite)
      (fun w => ⌜w = CSR_Check_OK tt⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDmc HDme HDpriv HDsec HDmisa Lmc Lme Lpriv Lsec Lmisa HTM.
    assert (HSTCE : eq_vec (_get_MEnvcfg_STCE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    iIntros "#Hcert Hrw Hro".
    unfold check_CSR_result.
    iApply (swp_bind_use _ _
              (fun w : bool => ⌜w = true⌝ ∗
                 hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
              _ with "[Hrw Hro] [-]").
    { unfold check_CSR, Defs.and_boolM.
      assert (H1 : check_CSR_priv csr_stimecmp Supervisor = returnM true)
        by (vm_compute; reflexivity).
      rewrite H1.
      iApply (swp_bind_use _ _
                (fun w : bool => ⌜w = true⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply swp_ret. by iFrame. }
      iIntros (x1) "(-> & Hrw & Hro)". cbn match.
      replace (check_CSR_access csr_stimecmp CSRWrite) with true
        by (vm_compute; reflexivity).
      iApply (swp_bind_use _ _
                (fun w : bool => ⌜w = true⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                _ with "[Hrw Hro] [-]").
      { iApply swp_ret. by iFrame. }
      iIntros (x2) "(-> & Hrw & Hro)". cbn match.
      assert (Hred : is_CSR_accessible csr_stimecmp Supervisor CSRWrite
                     = is_stimecmp_accessible Supervisor) by csr_dispatch_eq.
      rewrite Hred.
      iApply (swp_bind_use _ _
                (fun w : bool => ⌜w = true⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                _ with "[Hrw Hro] [-]").
      { unfold is_stimecmp_accessible, Defs.and_boolM.
        iApply (swp_bind_use _ _
                  (fun w : bool => ⌜w = true⌝ ∗
                     hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_span Drw Dro Df rs rs _ true Hdisj
                    (hval_cE_S_S (Drw ∪ Dro) Drw rs HDpriv HDsec HDmisa
                       Lpriv Lsec Lmisa) with "Hcert Hrw Hro"). }
        iIntros (y1) "(-> & Hrw & Hro)". cbn match.
        iApply (swp_bind_use _ _
                  (fun w : bool => ⌜w = true⌝ ∗
                     hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_span Drw Dro Df rs rs _ true Hdisj
                    (hval_cE_Sstc_S (Drw ∪ Dro) Drw rs HDpriv HDsec HDmisa
                       Lpriv Lsec Lmisa) with "Hcert Hrw Hro"). }
        iIntros (y2) "(-> & Hrw & Hro)". cbn match.
        (* the mcounteren TM bit *)
        iApply (swp_bind_use _ _
                  (fun w : bool => ⌜w = true⌝ ∗
                     hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_bind_use _ _
                    (fun mc : mword 32 => ⌜mc = mcen⌝ ∗
                       hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                    _ with "[Hrw Hro] [-]").
          { iApply (swp_mono with "[] [-]");
              [| iApply (swp_read_reg_pinned Drw Dro Df rs
                           (R_bitvector_32 mcounteren) Hdisj HDmc
                           with "Hcert Hrw Hro") ].
            iIntros (mc) "(-> & Hrw & Hro)". rewrite Lmc. by iFrame. }
          iIntros (mc) "(-> & Hrw & Hro)".
          rewrite HTM. iApply swp_ret. by iFrame. }
        iIntros (y3) "(-> & Hrw & Hro)". cbn match.
        (* the menvcfg STCE bit *)
        iApply (swp_bind_use _ _
                  (fun me : mword 64 => ⌜me = MENVCFG_S⌝ ∗
                     hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_mono with "[] [-]");
            [| iApply (swp_read_reg_pinned Drw Dro Df rs
                         (R_bitvector_64 menvcfg) Hdisj HDme
                         with "Hcert Hrw Hro") ].
          iIntros (me) "(-> & Hrw & Hro)". rewrite Lme. by iFrame. }
        iIntros (me) "(-> & Hrw & Hro)".
        rewrite HSTCE. iApply swp_ret. by iFrame. }
      iIntros (x3) "(-> & Hrw & Hro)". cbn match.
      assert (H4 : stateen_allows_CSR_access csr_stimecmp Supervisor CSRWrite
                   = returnM true) by (vm_compute; reflexivity).
      rewrite H4. iApply swp_ret. by iFrame. }
    iIntros (w) "(-> & Hrw & Hro)". cbn match.
    iApply swp_ret. by iFrame.
  Qed.

  (* the whole write: the three cell touches are opened and closed one at a
     time, and the value the read-back returns is therefore existential. *)
  Lemma swp_write_CSR_stimecmp_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate) (ip v : mword 64) :
    Drw ## Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (mseccfg : register) ∈ Drw ∪ Dro ->
    (misa : register) ∈ Drw ∪ Dro ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup mseccfg rs = mword_of_int 0 ->
    register_lookup misa rs = MISA_C ->
    stimecmp_inv -∗
    gen_cert -∗
    (R_bitvector_64 mip) ↦ᵣ ip -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (write_CSR csr_stimecmp v)
      (fun x => (∃ cf : mword 64, ⌜x = Ok cf⌝) ∗
         (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpriv HDsec HDmisa Hpriv Hsec Hmisa.
    iIntros "#Hinv #Hcert Hip Hrw Hro".
    rewrite write_CSR_stimecmp_red.
    (* 1. the old deadline: an UNOWNED read, so the value is arbitrary *)
    iApply (swp_bind_use _ _ (fun _ : mword 64 => True)%I _ with "[] [-]").
    { iApply (swp_read_reg_any (R_bitvector_64 stimecmp) with "Hcert").
      by iIntros (?). }
    iIntros (o) "_".
    (* 2. the write, the CLINT refresh and the read-back *)
    iApply (swp_bind_use _ _
              (fun c : mword 64 =>
                 (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                 hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
              with "[Hip Hrw Hro] [-]").
    { iApply (swp_bind0_use _ _
                (fun _ => (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
                with "[Hip Hrw Hro] [-]").
      { iApply (swp_bind0_use _ _
                  (fun _ => (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                     hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I _
                  with "[Hip Hrw Hro] [-]").
        { (* the ONE node that needs the seam *)
          iApply (swp_write_reg_cellinv timerN (R_bitvector_64 stimecmp)
                    (stimecmp_legalized o v) with "[] Hcert [Hip Hrw Hro]").
          { rewrite /stimecmp_inv /stimecmp_free. iExact "Hinv". }
          iFrame "Hrw Hro". iExists ip. iExact "Hip". }
        iIntros (u) "(Hip & Hrw & Hro)".
        iDestruct "Hip" as (z) "Hip".
        iApply (swp_clint_dispatch_false_S Drw Dro Df rs z Hdisj HDpriv HDsec
                  HDmisa Hpriv Hsec Hmisa with "Hcert Hip Hrw Hro"). }
      iIntros (u2) "(Hip & Hrw & Hro)".
      iApply (swp_read_reg_any (R_bitvector_64 stimecmp)
                (fun _ : mword 64 =>
                   (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z) ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I
                with "Hcert").
      iIntros (c). iFrame. }
    iIntros (c) "(Hip & Hrw & Hro)".
    iApply swp_ret. iSplitR; [iExists _; done|]. iFrame.
  Qed.

End StimecmpSwp.

Section WpSconfTimer.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Context {kt : ktier}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ---- rdtime rd: rd := (an arbitrary) mtime reading ---- *)
  Lemma wp_csrr_time_s_sconf
      (pc : mword 64) (rd : mword 5)
      (m : regfile) (n : nat) :
    uint rd <> 0 ->
    rd_ok rd ->
    timer_cap -∗
    sie_cap_gpr kt m n false p -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_time, zreg, Regidx rd, CSRRS)) -∗
    ( ∀ tv : mword 64,
      wp_next false p (fun (CID : CpuId) =>
        sie_cap_gpr kt (<[Regidx rd := regval_into_reg tv]> m) n false p -∗
        pc_is (add_vec_int pc 4) -∗
        WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok) "#Htcap Hcg Hpc Hinstr Hcont".
    pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
    pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
    iDestruct "Htcap" as "[Hen _]".
    iDestruct "Hen" as (mcen) "[#Hmcen %HTM]".
    assert (Hfresh : cw_fresh (R_bitvector_32 mcounteren))
      by (split_and!; vm_compute; reflexivity).
    (* THE READ VALUE IS NOT THE LEAF'S TO NAME: mtime lives in the clock
       invariant and the tick moves it, so it comes back EXISTENTIALLY out of
       the Q-carrying wrapper and the caller's own ∀ is instantiated at it. *)
    iApply (wp_instr_s_sconf m n false false pc false
              (CSRReg (csr_time, zreg, Regidx rd, CSRRS))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜n' = n⌝ ∗
                 ⌜∃ tv : mword 64,
                    m' = <[Regidx rd := regval_into_reg tv]> m⌝)%I
              with "Hcg Hpc Hinstr [Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl.
    iSplitR "Hcont".
    - (* ---- the instruction ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      iDestruct (pr_frames_in Supervisor (DfracOwn 1) DfracDiscarded
                   (R_bitvector_32 mcounteren) mcen Hfresh
                   with "Hmcen Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRReg (csr_time, zreg, Regidx rd, CSRRS)))
        with (execute_CSRReg csr_time zreg (Regidx rd) CSRRS).
      iApply (swp_mono with
                "[Hcap Hms Hhalf Hspp Hmie Hmdl Hmenv HPC HnPC Hresv]
                 [Hrw Hro Hfile]");
        [| iApply (swp_execute_CSRReg_r_obl_p ∅
                     (cr_Dro (R_bitvector_32 mcounteren))
                     (cr_Df (DfracOwn 1) DfracDiscarded
                        (R_bitvector_32 mcounteren))
                     (pw_rs Supervisor (R_bitvector_32 mcounteren) mcen)
                     (tp_pin m) csr_time Supervisor rd (fun _ => emp)%I
                     (cr_disj _) (cr_in_priv _)
                     (pw_rs_priv Supervisor (R_bitvector_32 mcounteren) mcen
                        Hfresh)
                     Hrd ltac:(by vm_compute)
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     ltac:(intro; by vm_compute)
                     with "Hcert Hfile Hrw Hro [Hcert] [Hcert]") ].
      + iIntros (e) "(-> & Hx)".
        iDestruct "Hx" as (tv) "(_ & Hf & Hrw & Hro)".
        iDestruct (pr_frames_out Supervisor (DfracOwn 1) DfracDiscarded
                     (R_bitvector_32 mcounteren) mcen Hfresh with "Hro")
          as "(_ & Hpriv & _ & _)".
        assert (Hsp : m !!! Regidx csp_rs1
                      = <[Regidx rd := regval_into_reg tv]> m !!! Regidx csp_rs1)
          by (symmetry; apply upd_ne; congruence).
        iSplitR; [done|].
        iExists (add_vec_int pc 4), ms0,
                (<[Regidx rd := regval_into_reg tv]> m), n.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf | exact Hmm]. }
        iSplitL "Hcap".
        { iApply (sie_cap_retarget m (<[Regidx rd := regval_into_reg tv]> m)
                    n false Hsp with "Hcap"). }
        iSplitL "Hf".
        { iEval (rewrite (tp_pin_upd m rd (regval_into_reg tv) Hrdtp)) in "Hf".
          iExact "Hf". }
        iSplitR; [done|]. iSplitR; [done|].
        iPureIntro. exists tv. reflexivity.
      + (* the legality check: mcounteren pinned, scounteren ∀-peeled *)
        iIntros "Hrw Hro".
        iApply (swp_check_CSR_result_time_S ∅
                  (cr_Dro (R_bitvector_32 mcounteren))
                  (cr_Df (DfracOwn 1) DfracDiscarded
                     (R_bitvector_32 mcounteren))
                  (pw_rs Supervisor (R_bitvector_32 mcounteren) mcen) mcen
                  (cr_disj _) (cr_in_r _) (cr_in_priv _) (cr_in_sec _)
                  (cr_in_misa _)
                  (pw_rs_r Supervisor (R_bitvector_32 mcounteren) mcen)
                  (pw_rs_priv Supervisor (R_bitvector_32 mcounteren) mcen Hfresh)
                  (pw_rs_sec Supervisor (R_bitvector_32 mcounteren) mcen Hfresh)
                  (pw_rs_misa Supervisor (R_bitvector_32 mcounteren) mcen Hfresh)
                  HTM with "Hcert Hrw Hro").
      + (* the mtime read: UNOWNED, so the value is whatever the machine has *)
        iIntros "Hrw Hro". rewrite read_CSR_time_red.
        iApply (swp_bind_use _ _
                  (fun _ : mword 64 =>
                     hreg_frame (pw_rs Supervisor (R_bitvector_32 mcounteren)
                                   mcen) ∅ ∗
                     hreg_frame_ro (cr_Df (DfracOwn 1) DfracDiscarded
                                      (R_bitvector_32 mcounteren))
                       (pw_rs Supervisor (R_bitvector_32 mcounteren) mcen)
                       (cr_Dro (R_bitvector_32 mcounteren)))%I
                  _ with "[Hrw Hro] [-]").
        { iApply (swp_read_reg_any (R_bitvector_64 mtime) with "Hcert").
          iIntros (v). iFrame. }
        iIntros (tv) "[Hrw Hro]". iApply swp_ret. by iFrame.
    - (* ---- the continuation ---- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & %Hex)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      destruct Hex as (tv & ->).
      iApply ("Hcont" $! tv cpu_id with "[%] Hcg' Hpc'"). done.
  Qed.

  (* ---- csrw stimecmp,rs1.  The deadline cell is NOT threaded: it lives in
     [timer_cap]'s invariant, opened across this one instruction step and
     resealed at the new deadline, so the whole precondition is persistent and
     the postcondition says nothing about the timer at all. ---- *)
  Lemma wp_csrw_stimecmp_s_sconf
      (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (n : nat) :
    uint rs1 <> 0 ->
    timer_cap -∗
    sie_cap_gpr kt m n false p -∗
    pc_is pc -∗
    instr pc false (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)) -∗
    wp_next false p (fun (CID : CpuId) =>
      sie_cap_gpr kt m n false p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrs1) "#Htcap Hcg Hpc Hinstr Hcont".
    iDestruct "Htcap" as "[Hen #Hstci]".
    iDestruct "Hen" as (mcen) "[#Hmcen %HTM]".
    assert (Hok : cw2_ok (R_bitvector_64 menvcfg) (R_bitvector_32 mcounteren)).
    { rewrite /cw2_ok /cw_fresh.
      split_and!; try (vm_compute; reflexivity). discriminate. }
    (* THE CLOCK VARIANT: [clint_dispatch] writes mip, which is a clock cell,
       so the wrapper lends [clock_res] for the instruction and takes it
       back. *)
    iApply (wp_instr_s_sconf_clock m n false false pc false
              (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW))
              (fun (_ : CpuId) npc ms' m' n' =>
                 ⌜npc = add_vec_int pc 4⌝ ∗ ⌜m' = m⌝ ∗ ⌜n' = n⌝)%I
              with "Hcg Hpc Hinstr [Hcont]").
    iNext. iApply wp_next_off_intro. rewrite /sconf_step_obl_clock.
    iSplitR "Hcont".
    - (* ---- the instruction ---- *)
      iIntros "Hsc Hcap Hfile HPC HnPC Hresv Hclk".
      iDestruct (sconf_to_cells with "Hsc") as (ms0 mdv0)
        "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Hspp & Hmie &
          Hmdl & Hmenv)".
      iDestruct "Hclk" as (cy ti ip) "(Hcy & Hti & Hip)".
      iDestruct (hw_config_cert with "Hhw") as "#Hcert".
      iPoseProof "Hhw" as "#Hhwc".
      iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
        "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
          %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
          %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
      subst misa0 mseccfg0.
      iDestruct (pw2_frames_in Supervisor (DfracOwn 1) DfracDiscarded
                   (R_bitvector_64 menvcfg) MENVCFG_S
                   (R_bitvector_32 mcounteren) mcen Hok
                   with "Hmenv Hmcen Hpriv Hmseccfg Hmisa") as "[Hrw Hro]".
      change (execute (CSRReg (csr_stimecmp, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_stimecmp (Regidx rs1) zreg CSRRW).
      iApply (swp_mono with
                "[Hcap Hms Hhalf Hspp Hmie Hmdl Hcy Hti HPC HnPC Hresv]
                 [Hrw Hro Hfile Hip]");
        [| iApply (swp_execute_CSRReg_w_ex_p
                     (cw_Drw (R_bitvector_64 menvcfg))
                     (cw2_Dro (R_bitvector_32 mcounteren))
                     (cw2_Df (DfracOwn 1) DfracDiscarded
                        (R_bitvector_32 mcounteren))
                     (pw2_rs Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                        (R_bitvector_32 mcounteren) mcen)
                     (pw2_rs Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                        (R_bitvector_32 mcounteren) mcen)
                     (tp_pin m) csr_stimecmp Supervisor rs1
                     (∃ z : mword 64, (R_bitvector_64 mip) ↦ᵣ z)%I
                     (cw2_disj _ _ Hok) (cw2_in_priv _ _)
                     (pw2_rs_priv Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                        (R_bitvector_32 mcounteren) mcen Hok)
                     ltac:(by vm_compute) ltac:(by vm_compute)
                     ltac:(by vm_compute) ltac:(intro; by vm_compute)
                     with "Hcert Hfile Hrw Hro [Hcert] [Hcert Hip]") ].
      + iIntros (e) "(-> & Hf & Hipz & Hrw & Hro)".
        iDestruct (pw2_frames_out Supervisor (DfracOwn 1) DfracDiscarded
                     (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen Hok with "[$Hrw $Hro]")
          as "(Hmenv & _ & Hpriv & _ & _)".
        iDestruct "Hipz" as (z) "Hip".
        iSplitR; [done|].
        iExists (add_vec_int pc 4), ms0, m, n.
        iFrame "HPC HnPC Hresv".
        iSplitL "Hcy Hti Hip". { iExists cy, ti, z. iFrame "Hcy Hti Hip". }
        iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
        { rewrite /sconf_at_priv. iExists mdv0.
          iFrame "Hhw Hminv Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
          iPureIntro. split; [exact Hmsf | exact Hmm]. }
        iFrame "Hcap Hf".
        iSplitR; [done|]. iSplitR; [done|]. done.
      + (* the legality check *)
        iIntros "Hrw Hro".
        iApply (swp_check_CSR_result_stimecmp_S
                  (cw_Drw (R_bitvector_64 menvcfg))
                  (cw2_Dro (R_bitvector_32 mcounteren))
                  (cw2_Df (DfracOwn 1) DfracDiscarded
                     (R_bitvector_32 mcounteren))
                  (pw2_rs Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen) mcen
                  (cw2_disj _ _ Hok) (cw2_in_r2 _ _) (cw2_in_r _ _)
                  (cw2_in_priv _ _) (cw2_in_sec _ _) (cw2_in_misa _ _)
                  (pw2_rs_r2 Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen)
                  (pw2_rs_r Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen Hok)
                  (pw2_rs_priv Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen Hok)
                  (pw2_rs_sec Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen Hok)
                  (pw2_rs_misa Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen Hok)
                  HTM with "Hcert Hrw Hro").
      + (* the write: the sealed cell, opened and closed one node at a time *)
        iIntros "Hrw Hro".
        iApply (swp_write_CSR_stimecmp_S
                  (cw_Drw (R_bitvector_64 menvcfg))
                  (cw2_Dro (R_bitvector_32 mcounteren))
                  (cw2_Df (DfracOwn 1) DfracDiscarded
                     (R_bitvector_32 mcounteren))
                  (pw2_rs Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen) ip _
                  (cw2_disj _ _ Hok) (cw2_in_priv _ _) (cw2_in_sec _ _)
                  (cw2_in_misa _ _)
                  (pw2_rs_priv Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen Hok)
                  (pw2_rs_sec Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen Hok)
                  (pw2_rs_misa Supervisor (R_bitvector_64 menvcfg) MENVCFG_S
                     (R_bitvector_32 mcounteren) mcen Hok)
                  with "Hstci Hcert Hip Hrw Hro").
    - (* ---- the continuation ---- *)
      iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & ->)".
      iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
      iApply ("Hcont" $! cpu_id with "[%] Hcg' Hpc'"). done.
  Qed.

End WpSconfTimer.
