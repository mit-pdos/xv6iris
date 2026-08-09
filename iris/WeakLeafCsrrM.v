(** * WeakLeafCsrrM.v — the remaining weak csrr leaves (M4, start/timerinit)

    Seams 4-8 of the weak [start()]/[timerinit()] port: the weak twins of
    [WpGprCsrrB.wp_csrr_menvcfg_gpr], [WpGprCsrrA.wp_csrr_mcounteren_gpr],
    [WpGprCsrrB.wp_csrr_sie_gpr], [WpGprCsrrA.wp_csrr_mhartid_gpr] and
    [WpGprCsrrA.wp_csrr_mstatus_gpr], at the batch-2 register-only recipe.

    [WeakLeafCsrrTime] did the hard part once: its CSR-GENERIC csrr spine
    [exec_eff_csrr_read_step_p] (plus the [drive_csr_eff] dispatch walk and
    the two [check_CSR]-read combinators [exec_eff_check_CSR_read_p] /
    [exec_eff_check_CSR_result_read_p]) is IMPORTED here, never cloned, so
    each further csrr leaf owes only its own [read_CSR] mirror, its own
    accessibility discharge and its own callback — 10-40 lines apiece.

    THE ONE STRUCTURAL SPLIT worth naming: four of the five leaves ride the
    PLAIN funnel [WeakFunnel.wwp_instr] (they own the CSR cell(s) they read
    and hand them straight back), but [csrr rd, mstatus] rides the CONFIG
    funnel [WeakFunnelCfg.wwp_instr_config] — not because it writes a config
    cell (it does not; it writes only [rd]) but because the READ VALUE is
    mstatus's WHOLE value, and [WeakFunnel.wcfg_regs] carries only mstatus's
    MIE/MPRV bits.  The config funnel's callback pins
    [register_lookup mstatus (wm_regs σ) = ms0], which is exactly what the
    conclusion needs; the surrendered config cells go back to the
    continuation per the config-funnel contract.

    Layout:

      §1  the READ-side check-kit dispatchers, csr-generic — the exact
          analogues of [WeakLeafRegOnly] §3's csrw dispatchers, at CSRRead
          ([_read_lit] / [_read_U] / [_read_U_and] / [_read_S]).  Candidates
          for a shared hoist next to the csrw four.
      §2  the five per-CSR [read_CSR] mirrors, at trace [[]].
      §3  the five callbacks and the five end-to-end [execute] mirrors,
          each through the imported spine.
      §4  the pre-write peels (each read value past the funnel's
          [minstret_increment] and [nextPC] pre-writes), the read-side twin
          of [WeakLeafCsrrTime.time_rdval_prewrite].
      §5  the five leaves, all alignment-generic ([al4] a parameter) through
          [WeakLeafRegOnly]'s [wP_eff_of_leaf_regonly] / [wcert_regonly],
          all CELL-based (they write the one [rd] cell, like the csrw
          family and like [WeakLeafCsrrTime]). *)
From Stdlib Require Import ZArith Zquot Zwf.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem WeakInterp WeakLang WeakGhost WeakBridge.
Require Import WeakView WeakVProp WeakFence.
Require Import WeakInstr WeakStore WeakCert WeakEff.
Require Import WeakEffSkel WeakPmpEff WeakTickEff WeakLeafEffCommon.
Require Import WeakFetchEff WeakFetch2.
Require Import WeakFunnel WeakFunnelCfg WpDecodeBridge.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import RegFile WpGpr.
Require Import WeakLeafWin.
Require Import ExecCommon WpDecode.
Require Import WpGprCsrrCommon WpGprCsrrA WpGprCsrrB.
Require Import WeakLeafCsrw WeakLeafRegOnly WeakLeafCsrrTime.

Import SailStdpp.Values.
Import Defs.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. THE READ-SIDE CHECK KIT, csr-generic

    [WeakLeafRegOnly] §3's four csrw dispatchers with [CSRWrite] replaced by
    [CSRRead] and [exec_eff_check_CSR_csrw_p] /
    [exec_eff_check_CSR_result_csrw_p] replaced by [WeakLeafCsrrTime]'s
    [exec_eff_check_CSR_read_p] / [exec_eff_check_CSR_result_read_p].  Each
    csrr leaf below discharges its [check_CSR_result] obligation from ONE of
    these plus per-csr [vm_compute] side conditions, exactly as the SC
    leaves do. *)

(** The literal case ([check_CSR] collapses to [returnM true] by
    computation): mstatus (0x300), mhartid (0xF14). *)
Lemma exec_eff_check_CSR_result_read_lit (csr : mword 12) s :
  check_CSR csr Machine CSRRead = returnM true ->
  exec_eff (check_CSR_result csr Machine CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intro H. unfold check_CSR_result. rewrite H.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM true s)).
  exact (exec_eff_returnM (CSR_Check_OK tt) s).
Qed.

(** Ext_S-gated CSRs at CSRRead: sie (0x104). *)
Lemma exec_eff_check_CSR_result_read_S (csr : mword 12) s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (check_CSR_priv csr Machine) s = Some (true, s, []) ->
  check_CSR_access csr CSRRead = true ->
  is_CSR_accessible csr Machine CSRRead = currentlyEnabled Ext_S ->
  exec_eff (stateen_allows_CSR_access csr Machine CSRRead) s
    = Some (true, s, []) ->
  exec_eff (check_CSR_result csr Machine CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intros HS Hpriv Hca Hacceq Hst.
  apply exec_eff_check_CSR_result_read_p.
  apply exec_eff_check_CSR_read_p; try assumption.
  rewrite Hacceq. rewrite (exec_eff_currentlyEnabled_S s). rewrite HS.
  reflexivity.
Qed.

(** Ext_U-gated CSRs at CSRRead: mcounteren (0x306). *)
Lemma exec_eff_check_CSR_result_read_U (csr : mword 12) s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (check_CSR_priv csr Machine) s = Some (true, s, []) ->
  check_CSR_access csr CSRRead = true ->
  is_CSR_accessible csr Machine CSRRead = currentlyEnabled Ext_U ->
  exec_eff (stateen_allows_CSR_access csr Machine CSRRead) s
    = Some (true, s, []) ->
  exec_eff (check_CSR_result csr Machine CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intros HU Hpriv Hca Hacceq Hst.
  apply exec_eff_check_CSR_result_read_p.
  apply exec_eff_check_CSR_read_p; try assumption.
  rewrite Hacceq. apply (exec_eff_currentlyEnabled_U s HU).
Qed.

(** U-gated CSRs whose accessibility conjoins a config predicate —
    menvcfg (0x30A). *)
Lemma exec_eff_check_CSR_result_read_U_and (csr : mword 12) (b : bool) s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (check_CSR_priv csr Machine) s = Some (true, s, []) ->
  check_CSR_access csr CSRRead = true ->
  is_CSR_accessible csr Machine CSRRead
    = Defs.and_boolM ((currentlyEnabled Ext_U) : M bool) (returnM b) ->
  b = true ->
  exec_eff (stateen_allows_CSR_access csr Machine CSRRead) s
    = Some (true, s, []) ->
  exec_eff (check_CSR_result csr Machine CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intros HU Hpriv Hca Hacceq Hb Hst.
  apply exec_eff_check_CSR_result_read_p.
  apply exec_eff_check_CSR_read_p; try assumption.
  rewrite Hacceq.
  rewrite (exec_eff_and_boolM_nil _ _ _ _ _ (exec_eff_currentlyEnabled_U s HU)).
  cbn match. rewrite Hb. apply exec_eff_returnM.
Qed.

(* ====================================================================== *)
(** ** 2. THE [read_CSR] MIRRORS (trace [])

    [WpGprCsrrA]/[WpGprCsrrB]'s [exec_read_CSR_*] under
    [exec_bind_Some] → [exec_eff_bind_nil], [exec_read_reg] →
    [exec_eff_read_reg], [drive_csr] → [WeakLeafCsrrTime.drive_csr_eff].
    The read VALUES are the SC files' ([menvcfg_rdval], [mcounteren_rdval],
    [sie_rdval], [mstatus_rdval]), never restated. *)

Lemma exec_eff_read_CSR_menvcfg s :
  exec_eff (read_CSR csr_menvcfg) s = Some (menvcfg_rdval s, s, []).
Proof.
  unfold csr_menvcfg, menvcfg_rdval. drive_csr_eff.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg menvcfg s)).
  apply exec_eff_returnM.
Qed.

Lemma exec_eff_read_CSR_mcounteren s :
  exec_eff (read_CSR csr_mcounteren) s = Some (mcounteren_rdval s, s, []).
Proof.
  unfold csr_mcounteren, mcounteren_rdval. drive_csr_eff.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mcounteren s)).
  apply exec_eff_returnM.
Qed.

(** sie is a VIEW of two registers ([lower_mie mie mideleg]), so its mirror
    peels two reads. *)
Lemma exec_eff_read_CSR_sie s :
  exec_eff (read_CSR csr_sie) s = Some (sie_rdval s, s, []).
Proof.
  unfold csr_sie, sie_rdval. drive_csr_eff.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mie s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mideleg s)).
  apply exec_eff_returnM.
Qed.

(** mstatus sits in the SECOND dispatch clause (0x301 = misa comes first),
    so its mirror peels by hand — [WpGprCsrrA.exec_read_CSR_mstatus]'s
    script — rather than walking the whole chain. *)
Lemma exec_eff_read_CSR_mstatus s :
  exec_eff (read_CSR csr_mstatus) s = Some (mstatus_rdval s, s, []).
Proof.
  unfold read_CSR, csr_mstatus, mstatus_rdval.
  replace (eq_vec (Ox"300" : mword 12) (Ox"301")) with false
    by (vm_compute; reflexivity).
  cbn match.
  replace (andb (Z.eqb xlen 64) (eq_vec (Ox"300" : mword 12) (Ox"300")))
    with true by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
  apply exec_eff_returnM.
Qed.

(** mhartid ([csr_csrr] = 0xF14): [ExecCommon.exec_read_CSR_csrr]'s mirror —
    the dispatch collapses to the bare register read by conversion. *)
Lemma exec_eff_read_CSR_csrr s :
  exec_eff (read_CSR csr_csrr) s
    = Some (register_lookup mhartid s.(sregs), s, []).
Proof. exact (exec_eff_read_reg (R_bitvector_64 mhartid) s). Qed.

(* ====================================================================== *)
(** ** 3. THE CALLBACKS AND THE END-TO-END [execute] MIRRORS

    Each [execute] mirror is the imported spine
    [WeakLeafCsrrTime.exec_eff_csrr_read_step_p] at [p := Machine] with the
    seven per-CSR facts plugged in — the SC [exec_execute_csrr_*_gpr]
    scripts, token for token. *)

Lemma exec_eff_csr_id_read_callback_menvcfg s (d : mword 64) :
  exec_eff (csr_id_read_callback csr_menvcfg d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_read_callback csr_menvcfg d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_read_callback_mcounteren s (d : mword 64) :
  exec_eff (csr_id_read_callback csr_mcounteren d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_read_callback csr_mcounteren d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_read_callback_sie s (d : mword 64) :
  exec_eff (csr_id_read_callback csr_sie d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_read_callback csr_sie d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_read_callback_mstatus s (d : mword 64) :
  exec_eff (csr_id_read_callback csr_mstatus d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_read_callback csr_mstatus d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

Lemma exec_eff_csr_id_read_callback_csrr s (d : mword 64) :
  exec_eff (csr_id_read_callback csr_csrr d) s = Some (tt, s, []).
Proof.
  assert (H : csr_id_read_callback csr_csrr d = returnM tt)
    by (vm_compute; reflexivity).
  rewrite H. apply exec_eff_returnM.
Qed.

(** *** 3a. menvcfg (0x30A): Ext_U-gated AND the xenvcfg-exists predicate *)

Lemma exec_eff_check_CSR_result_menvcfg s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (check_CSR_result csr_menvcfg Machine CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intro HU.
  apply (exec_eff_check_CSR_result_read_U_and csr_menvcfg
           xenvcfg_csrs_are_defined s HU).
  - assert (H : check_CSR_priv csr_menvcfg Machine = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_eff_returnm.
  - vm_compute; reflexivity.
  - csr_dispatch_eq.
  - vm_compute; reflexivity.
  - assert (H : stateen_allows_CSR_access csr_menvcfg Machine CSRRead
                = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_eff_returnm.
Qed.

Lemma exec_eff_execute_csrr_menvcfg_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (execute (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (menvcfg_rdval s)), []).
Proof.
  intros Hrd Hpriv HU.
  change (execute (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)))
    with (execute_CSRReg csr_menvcfg zreg (Regidx rd) CSRRS).
  apply (exec_eff_csrr_read_step_p Machine csr_menvcfg rd (menvcfg_rdval s) s _
           Hpriv).
  - exact (exec_eff_check_CSR_result_menvcfg s HU).
  - vm_compute; reflexivity.
  - apply exec_eff_read_CSR_menvcfg.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_csr_id_read_callback_menvcfg.
  - rewrite (exec_eff_wX_bits_gpr rd (menvcfg_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(** *** 3b. mcounteren (0x306): Ext_U-gated, 32-bit CSR *)

Lemma exec_eff_check_CSR_result_mcounteren s :
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (check_CSR_result csr_mcounteren Machine CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intro HU.
  apply (exec_eff_check_CSR_result_read_U csr_mcounteren s HU).
  - assert (H : check_CSR_priv csr_mcounteren Machine = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_eff_returnm.
  - vm_compute; reflexivity.
  - csr_dispatch_eq.
  - assert (H : stateen_allows_CSR_access csr_mcounteren Machine CSRRead
                = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_eff_returnm.
Qed.

Lemma exec_eff_execute_csrr_mcounteren_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_U (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (execute (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (mcounteren_rdval s)), []).
Proof.
  intros Hrd Hpriv HU.
  change (execute (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)))
    with (execute_CSRReg csr_mcounteren zreg (Regidx rd) CSRRS).
  apply (exec_eff_csrr_read_step_p Machine csr_mcounteren rd
           (mcounteren_rdval s) s _ Hpriv).
  - exact (exec_eff_check_CSR_result_mcounteren s HU).
  - vm_compute; reflexivity.
  - apply exec_eff_read_CSR_mcounteren.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_csr_id_read_callback_mcounteren.
  - rewrite (exec_eff_wX_bits_gpr rd (mcounteren_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(** *** 3c. sie (0x104): Ext_S-gated, a view of mie & mideleg *)

Lemma exec_eff_check_CSR_result_sie s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (check_CSR_result csr_sie Machine CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  intro HS.
  apply (exec_eff_check_CSR_result_read_S csr_sie s HS).
  - assert (H : check_CSR_priv csr_sie Machine = returnM true)
      by (vm_compute; reflexivity).
    rewrite H. apply exec_eff_returnm.
  - vm_compute; reflexivity.
  - csr_dispatch_eq.
  - assert (H : stateen_allows_CSR_access csr_sie Machine CSRRead
                = returnM true) by (vm_compute; reflexivity).
    rewrite H. apply exec_eff_returnm.
Qed.

Lemma exec_eff_execute_csrr_sie_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec_eff (execute (CSRReg (csr_sie, zreg, Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (sie_rdval s)), []).
Proof.
  intros Hrd Hpriv HS.
  change (execute (CSRReg (csr_sie, zreg, Regidx rd, CSRRS)))
    with (execute_CSRReg csr_sie zreg (Regidx rd) CSRRS).
  apply (exec_eff_csrr_read_step_p Machine csr_sie rd (sie_rdval s) s _ Hpriv).
  - exact (exec_eff_check_CSR_result_sie s HS).
  - vm_compute; reflexivity.
  - apply exec_eff_read_CSR_sie.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_csr_id_read_callback_sie.
  - rewrite (exec_eff_wX_bits_gpr rd (sie_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(** *** 3d. mstatus (0x300): no gate *)

Lemma exec_eff_check_CSR_result_mstatus s :
  exec_eff (check_CSR_result csr_mstatus Machine CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  apply exec_eff_check_CSR_result_read_lit. vm_compute; reflexivity.
Qed.

Lemma exec_eff_execute_csrr_mstatus_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (execute (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (mstatus_rdval s)), []).
Proof.
  intros Hrd Hpriv.
  change (execute (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)))
    with (execute_CSRReg csr_mstatus zreg (Regidx rd) CSRRS).
  apply (exec_eff_csrr_read_step_p Machine csr_mstatus rd (mstatus_rdval s) s _
           Hpriv).
  - apply exec_eff_check_CSR_result_mstatus.
  - vm_compute; reflexivity.
  - apply exec_eff_read_CSR_mstatus.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_csr_id_read_callback_mstatus.
  - rewrite (exec_eff_wX_bits_gpr rd (mstatus_rdval s) s).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(** *** 3e. mhartid (0xF14): no gate.  Statement-identical to
    [WkEntryEff.exec_eff_execute_CSRReg_gpr] (that file's private copy is
    proved from scratch; this one goes through the shared spine, and this
    file deliberately does not depend on the [_entry] chain / Kernel). *)

Lemma exec_eff_check_CSR_result_csrr s :
  exec_eff (check_CSR_result csr_csrr Machine CSRRead) s
    = Some (CSR_Check_OK tt, s, []).
Proof.
  apply exec_eff_check_CSR_result_read_lit. vm_compute; reflexivity.
Qed.

Lemma exec_eff_execute_csrr_mhartid_gpr (rd : mword 5) s :
  uint rd <> 0 ->
  register_lookup cur_privilege s.(sregs) = Machine ->
  exec_eff (execute (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
              (regval_into_reg (register_lookup mhartid s.(sregs))), []).
Proof.
  intros Hrd Hpriv.
  change (execute (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)))
    with (execute_CSRReg csr_csrr zreg (Regidx rd) CSRRS).
  apply (exec_eff_csrr_read_step_p Machine csr_csrr rd
           (register_lookup mhartid s.(sregs)) s _ Hpriv).
  - apply exec_eff_check_CSR_result_csrr.
  - vm_compute; reflexivity.
  - apply exec_eff_read_CSR_csrr.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_eff_csr_id_read_callback_csrr.
  - rewrite (exec_eff_wX_bits_gpr rd (register_lookup mhartid s.(sregs)) s).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
Qed.

(* ====================================================================== *)
(** ** 4. THE PRE-WRITE PEELS

    [WeakLeafCsrrTime.time_rdval_prewrite]'s twins: the funnel hands the
    [execute] a state with two pre-writes on top ([minstret_increment] and
    [nextPC]), and neither touches any CSR, so each read value at the
    pre-written state is the value the leaf's cell pins at [wm_regs σ] —
    which is what lets the CONFINED-state and the FLAT-state [execute]
    instantiations produce the SAME successor. *)

Lemma menvcfg_rdval_prewrite (s0 : mstate) (b : bool) (npc v : mword 64) :
  register_lookup menvcfg s0.(sregs) = v ->
  menvcfg_rdval
    (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc) = v.
Proof.
  intro H. unfold menvcfg_rdval.
  rewrite (set_lookup_ne menvcfg nextPC _ _ ltac:(reg_ne)).
  rewrite (set_lookup_ne menvcfg (R_bool minstret_increment) _ _ ltac:(reg_ne)).
  rewrite H. apply subrange64_id.
Qed.

Lemma mcounteren_rdval_prewrite (s0 : mstate) (b : bool)
    (npc : mword 64) (v : mword 32) :
  register_lookup mcounteren s0.(sregs) = v ->
  mcounteren_rdval
    (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
    = zero_extend' 64 v.
Proof.
  intro H. unfold mcounteren_rdval.
  rewrite (set_lookup_ne mcounteren nextPC _ _ ltac:(reg_ne)).
  rewrite (set_lookup_ne mcounteren (R_bool minstret_increment)
             _ _ ltac:(reg_ne)).
  by rewrite H.
Qed.

Lemma sie_rdval_prewrite (s0 : mstate) (b : bool) (npc v1 v2 : mword 64) :
  register_lookup mie s0.(sregs) = v1 ->
  register_lookup mideleg s0.(sregs) = v2 ->
  sie_rdval (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc)
    = lower_mie v1 v2.
Proof.
  intros H1 H2. unfold sie_rdval.
  rewrite (set_lookup_ne mie nextPC _ _ ltac:(reg_ne)).
  rewrite (set_lookup_ne mie (R_bool minstret_increment) _ _ ltac:(reg_ne)).
  rewrite (set_lookup_ne mideleg nextPC _ _ ltac:(reg_ne)).
  rewrite (set_lookup_ne mideleg (R_bool minstret_increment)
             _ _ ltac:(reg_ne)).
  by rewrite H1 H2.
Qed.

Lemma mstatus_rdval_prewrite (s0 : mstate) (b : bool) (npc v : mword 64) :
  register_lookup mstatus s0.(sregs) = v ->
  mstatus_rdval
    (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc) = v.
Proof.
  intro H. unfold mstatus_rdval.
  rewrite (set_lookup_ne mstatus nextPC _ _ ltac:(reg_ne)).
  rewrite (set_lookup_ne mstatus (R_bool minstret_increment) _ _ ltac:(reg_ne)).
  rewrite H. apply subrange64_id.
Qed.

Lemma mhartid_prewrite (s0 : mstate) (b : bool) (npc v : mword 64) :
  register_lookup mhartid s0.(sregs) = v ->
  register_lookup mhartid
    (sregs (set_reg (set_reg s0 (R_bool minstret_increment) b) nextPC npc))
    = v.
Proof.
  intro H.
  rewrite (set_lookup_ne mhartid nextPC _ _ ltac:(reg_ne)).
  rewrite (set_lookup_ne mhartid (R_bool minstret_increment) _ _ ltac:(reg_ne)).
  exact H.
Qed.

(* ====================================================================== *)
(** ** 5. THE LEAVES

    [WeakLeafCsrrTime.wwp_csrr_time_leaf]'s script, four times over on the
    PLAIN funnel and once on the CONFIG funnel.  The only per-leaf deltas
    are: which CSR cell(s) the leaf owns (read once off [Hreg], carried to
    [wm_regs σ] by [WeakLeafWin.reg_at_flat], handed straight back), which
    gate fact the [execute] mirror asks for (misa.U / misa.S, both derived
    from the funnel's [wcfg_regs] [misa = MISA_C]), and — for mstatus — that
    the pinned value comes from the CONFIG funnel's own
    [⌜register_lookup mstatus (wm_regs σ) = ms0⌝] rather than from a cell
    the leaf carries. *)

Section leaves_csrr.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Implicit Types Φ : mval -> iProp Σ.

  (** *** 5a. [csrr rd, menvcfg] — plain funnel, Ext_U-gated *)
  Lemma wwp_csrr_menvcfg_leaf Φ (al4 : bool)
      (pc : mword 64) (w : mword 32) (rd : mword 5)
      (menvcfg_in rd0 npc0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    (* the decode, in the two shapes its two consumers ask for *)
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    menvcfg ↦ᵣ menvcfg_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg menvcfg_in -∗
       menvcfg ↦ᵣ menvcfg_in -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hcsr Hrdc #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    iApply (wwp_instr Φ pc false (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    (* the CSR cell the funnel does not read *)
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat menvcfg σ b eq_refl)) Lcsr_a)
      as Lcsr.
    (* ---- premise (c): the execute mirror, at the CONFINED state ---- *)
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (HUc : eq_vec (_get_Misa_U (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      pose proof (exec_eff_execute_csrr_menvcfg_gpr rd
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrdnz Hprivc HUc) as He.
      rewrite (menvcfg_rdval_prewrite s0c b' (add_vec_int pc 4) menvcfg_in Lcsr)
        in He.
      destruct (load_sexec_facts s0c b' (add_vec_int pc 4) rd
                  (regval_into_reg menvcfg_in))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    (* ---- the certificate's precondition ---- *)
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_menvcfg, zreg, Regidx rd, CSRRS)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    (* ---- the run at the FLAT state ---- *)
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (HUf : eq_vec (_get_Misa_U (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    pose proof (exec_eff_execute_csrr_menvcfg_gpr rd
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrdnz Hprivf HUf) as Hef.
    rewrite (menvcfg_rdval_prewrite (wflat_st σ) b (add_vec_int pc 4)
               menvcfg_in Lcsr) in Hef.
    (* ---- the two register writes the [execute] performs ---- *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg menvcfg_in) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg menvcfg_in)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                (regval_into_reg menvcfg_in))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrdc Hcsr Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

  (** *** 5b. [csrr rd, mcounteren] — plain funnel, Ext_U-gated, 32-bit CSR
      (the read value is [zero_extend' 64] of the cell). *)
  Lemma wwp_csrr_mcounteren_leaf Φ (al4 : bool)
      (pc : mword 64) (w : mword 32) (rd : mword 5)
      (mcen_in : mword 32) (rd0 npc0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    mcounteren ↦ᵣ mcen_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ
         regval_into_reg (zero_extend' 64 mcen_in) -∗
       mcounteren ↦ᵣ mcen_in -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hcsr Hrdc #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    iApply (wwp_instr Φ pc false
              (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iDestruct (reg_valid with "Hreg Hcsr") as %Lcsr_a.
    pose proof (eq_trans (eq_sym (reg_at_flat mcounteren σ b eq_refl)) Lcsr_a)
      as Lcsr.
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (HUc : eq_vec (_get_Misa_U (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      pose proof (exec_eff_execute_csrr_mcounteren_gpr rd
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrdnz Hprivc HUc) as He.
      rewrite (mcounteren_rdval_prewrite s0c b' (add_vec_int pc 4) mcen_in Lcsr)
        in He.
      destruct (load_sexec_facts s0c b' (add_vec_int pc 4) rd
                  (regval_into_reg (zero_extend' 64 mcen_in)))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_mcounteren, zreg, Regidx rd, CSRRS)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (HUf : eq_vec (_get_Misa_U (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    pose proof (exec_eff_execute_csrr_mcounteren_gpr rd
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrdnz Hprivf HUf) as Hef.
    rewrite (mcounteren_rdval_prewrite (wflat_st σ) b (add_vec_int pc 4)
               mcen_in Lcsr) in Hef.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (zero_extend' 64 mcen_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (zero_extend' 64 mcen_in))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                (regval_into_reg (zero_extend' 64 mcen_in)))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrdc Hcsr Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

  (** *** 5c. [csrr rd, sie] — plain funnel, Ext_S-gated.  sie is a VIEW of
      [mie] and [mideleg], so the leaf carries BOTH cells and the read value
      is [lower_mie mie_in mideleg_in]. *)
  Lemma wwp_csrr_sie_leaf Φ (al4 : bool)
      (pc : mword 64) (w : mword 32) (rd : mword 5)
      (mie_in mideleg_in rd0 npc0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_sie, zreg, Regidx rd, CSRRS), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_sie, zreg, Regidx rd, CSRRS), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    mie ↦ᵣ mie_in -∗
    mideleg ↦ᵣ mideleg_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ
         regval_into_reg (lower_mie mie_in mideleg_in) -∗
       mie ↦ᵣ mie_in -∗
       mideleg ↦ᵣ mideleg_in -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hmie Hmdl Hrdc #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    iApply (wwp_instr Φ pc false (CSRReg (csr_sie, zreg, Regidx rd, CSRRS))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_sie, zreg, Regidx rd, CSRRS))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iDestruct (reg_valid with "Hreg Hmie") as %Lmie_a.
    iDestruct (reg_valid with "Hreg Hmdl") as %Lmdl_a.
    pose proof (eq_trans (eq_sym (reg_at_flat mie σ b eq_refl)) Lmie_a)
      as Lmie.
    pose proof (eq_trans (eq_sym (reg_at_flat mideleg σ b eq_refl)) Lmdl_a)
      as Lmdl.
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_sie, zreg, Regidx rd, CSRRS)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      assert (Hmisac : register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = MISA_C).
      { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup misa _ b' eq_refl). exact Lmisa. }
      assert (HSc : eq_vec (_get_Misa_S (register_lookup misa
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))))) ('b"1") = true)
        by (rewrite Hmisac; vm_compute; reflexivity).
      pose proof (exec_eff_execute_csrr_sie_gpr rd
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrdnz Hprivc HSc) as He.
      rewrite (sie_rdval_prewrite s0c b' (add_vec_int pc 4) mie_in mideleg_in
                 Lmie Lmdl) in He.
      destruct (load_sexec_facts s0c b' (add_vec_int pc 4) rd
                  (regval_into_reg (lower_mie mie_in mideleg_in)))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_sie, zreg, Regidx rd, CSRRS)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    assert (Hmisaf : register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = MISA_C).
    { rewrite (set_lookup_ne misa nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat misa σ b eq_refl). exact Lmisa. }
    assert (HSf : eq_vec (_get_Misa_S (register_lookup misa
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))))) ('b"1") = true)
      by (rewrite Hmisaf; vm_compute; reflexivity).
    pose proof (exec_eff_execute_csrr_sie_gpr rd
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrdnz Hprivf HSf) as Hef.
    rewrite (sie_rdval_prewrite (wflat_st σ) b (add_vec_int pc 4)
               mie_in mideleg_in Lmie Lmdl) in Hef.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (lower_mie mie_in mideleg_in))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg (lower_mie mie_in mideleg_in))).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                (regval_into_reg (lower_mie mie_in mideleg_in)))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrdc Hmie Hmdl Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

  (** *** 5d. [csrr rd, mhartid] — plain funnel, no gate.  This is the leaf
      form of [WkEntryNew]'s INLINE csrr-mhartid funnel block. *)
  Lemma wwp_csrr_mhartid_leaf Φ (al4 : bool)
      (pc : mword 64) (w : mword 32) (rd : mword 5)
      (mhartid_in rd0 npc0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS), dst) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    mhartid ↦ᵣ mhartid_in -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       mmode_config (DfracOwn q) -∗
       pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg mhartid_in -∗
       mhartid ↦ᵣ mhartid_in -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz Hdecf Hagree HDmi Hgood Hdec.
    iIntros "Hmm Hpmpc Hpc Hnpc Hmh Hrdc #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    iApply (wwp_instr Φ pc false (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS))
              pmpcfg0 (dq := DfracOwn q)
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hmm Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb. iIntros (σ b) "%Lpc0 %Hcfg Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    iDestruct (reg_valid with "Hreg Hmh") as %Lmh_a.
    pose proof (eq_trans (eq_sym (reg_at_flat mhartid σ b eq_refl)) Lmh_a)
      as Lmh.
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      pose proof (exec_eff_execute_csrr_mhartid_gpr rd
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrdnz Hprivc) as He.
      rewrite (mhartid_prewrite s0c b' (add_vec_int pc 4) mhartid_in Lmh)
        in He.
      destruct (load_sexec_facts s0c b' (add_vec_int pc 4) rd
                  (regval_into_reg mhartid_in))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_csrr, zreg, Regidx rd, CSRRS)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    pose proof (exec_eff_execute_csrr_mhartid_gpr rd
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrdnz Hprivf) as Hef.
    rewrite (mhartid_prewrite (wflat_st σ) b (add_vec_int pc 4) mhartid_in Lmh)
      in Hef.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg mhartid_in) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg mhartid_in)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hmm' Hpmpc' Hpc'".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                (regval_into_reg mhartid_in))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc'".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hmm' Hpmpc' [$Hpc' $Hnpc] Hrdc Hmh Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

  (** *** 5e. [csrr rd, mstatus] — the CONFIG funnel.

      The reason this one is not on the plain funnel: the read value is
      mstatus's WHOLE value, and [WeakFunnel.wcfg_regs] carries only
      mstatus's MIE/MPRV bits, so the plain funnel's callback cannot pin it.
      [WeakFunnelCfg.wwp_instr_config] does — its callback hands over
      [⌜register_lookup mstatus (wm_regs σ) = ms0⌝] together with the three
      surrendered config cells, which the continuation gives back per the
      config-funnel contract.  The leaf itself writes ONLY [rd]; mstatus is
      unchanged. *)
  Lemma wwp_csrr_mstatus_leaf Φ (al4 : bool)
      (pc : mword 64) (w : mword 32) (rd : mword 5)
      (ms0 rd0 npc0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (D : register -> bool) (dst : mstate) (ws : wstate) :
    gen_id = 0%nat ->
    pmp_allows_all pmpcfg0 ->
    is_aligned_vaddr (Virtaddr pc) 2 = true ->
    is_aligned_vaddr (Virtaddr pc) 4 = al4 ->
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false ->
    (forall t : mstate,
       priv_mSU (register_lookup cur_privilege t.(sregs)) = true ->
       eq_vec (_get_Misa_C (register_lookup misa t.(sregs))) ('b"1") = true ->
       eq_vec (_get_Misa_A (register_lookup misa t.(sregs))) ('b"1") = true ->
       register_lookup misa t.(sregs) = MISA_C ->
       cfg_ok t ->
       exec (decode_fetch (F_Base w)) t
         = Some (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS), t)) ->
    (forall rs : Riscv.rv64d_types.regstate,
       register_lookup cur_privilege rs = Machine ->
       register_lookup misa rs = MISA_C ->
       register_lookup mseccfg rs = mword_of_int 0 ->
       forall r, D r = true ->
         register_lookup r rs = register_lookup r dst.(sregs)) ->
    D (R_bool minstret_increment) = false ->
    goodb0 D (ext_decode w) dst = true ->
    exec (ext_decode w) dst
      = Some (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS), dst) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ npc0 -∗
    R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ rd0 -∗
    winstr_bytes pc (F_Base w) -∗
    hart_ws cpu_id ws -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       cur_privilege ↦ᵣ Machine -∗
       mstatus ↦ᵣ ms0 -∗
       pmpcfg_n ↦ᵣ pmpcfg0 -∗
       pc_is (add_vec_int pc 4) -∗
       R_bitvector_64 (gpr_of_Z (uint rd)) ↦ᵣ regval_into_reg ms0 -∗
       hart_ws cpu_id ws' -∗
       WP (Loop : expr weak_riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    intros Hgid Hpmp Hal2 Hal4 Hrdnz HmIE0 HMPRV Hdecf Hagree HDmi Hgood Hdec.
    iIntros "#Hhw #Hmiv Hhs Hpriv Hms0 Hpmpc Hpc Hnpc Hrdc #Hbs Hhws Hcont".
    iDestruct (winstr_bytes_acc_wf with "Hbs") as %Haccpc.
    assert (Hacc0 : acc_wf pc 0) by (unfold acc_wf in Haccpc |- *; lia).
    iAssert (⌜forall j : nat, (j < 4)%nat -> addr_is_ram (pa_add pc j)⌝)%I
      as %Hram.
    { iDestruct "Hbs" as "(_ & _ & %Hr & _)". by iPureIntro. }
    iAssert (⌜isRVC (subrange_vec_dec w 15 0) = false⌝)%I as %HnotRVC.
    { iDestruct "Hbs" as "(_ & _ & _ & Hbw)".
      iDestruct "Hbw" as (w0) "[%Hw0 _]". destruct Hw0 as [<- H].
      by iPureIntro. }
    iApply (wwp_instr_config Φ pc false
              (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)) pmpcfg0 ms0
              (wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc))
              wQ_pure Hgid Haccpc Hpmp HmIE0 HMPRV
              (wcert_regonly al4 (fin_to_nat cpu_id) pc)
              with "Hhw Hmiv Hhs Hpriv Hms0 Hpmpc Hpc [] ").
    { iApply (winstr_intro pc false
                (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS))
                (F_Base w) eq_refl eq_refl Hdecf with "Hbs"). }
    rewrite /wwp_cb_config.
    iIntros (σ b) "%Lpc0 %Hcfg %Lms0 Hpriv Hms Hpmpc Hlat Hreg Hnorg".
    iDestruct "Hnorg" as "(%Hbnd & %Hwf & Hdev & Hlogauth & Hwsauth)".
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsauth Hhws") as %Hws.
    destruct Hcfg as (Lpriv & Lhart & Lmisa & Lsec & Lpmpc & Lpma & Lhtif &
                      LmisaS & LmIE & Lmprv & Lpmm & Lelp).
    iDestruct (winstr_flat σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hfok.
    iDestruct (winstr_pinned σ pc (F_Base w) Hwf with "Hlat Hbs") as %Hpin.
    destruct Hfok as (_ & _ & w' & [Hww _] & Htext0). subst w'.
    assert (LmisaC : eq_vec (_get_Misa_C (register_lookup misa (wm_regs σ)))
                       ('b"1") = true)
      by (rewrite Lmisa; vm_compute; reflexivity).
    assert (Hc : forall b' : bool, exists s_exec : mstate,
       exec_eff (execute (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)))
         (set_reg (set_reg (MState (wm_regs σ)
                     (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ))
                     (R_bool minstret_increment) b')
                  nextPC (add_vec_int pc 4))
         = Some (RETIRE_SUCCESS, s_exec, [])
       /\ register_lookup hart_state (sregs s_exec) = HART_ACTIVE tt
       /\ register_lookup (R_bool minstret_increment) (sregs s_exec) = b'
       /\ dom (mem s_exec) ⊆ wwin pc pc 0).
    { intro b'.
      set (s0c := MState (wm_regs σ)
                    (wmem_restrict σ (wwin pc pc 0)) (wm_dev σ)).
      assert (Hprivc : register_lookup cur_privilege
                (sregs (set_reg (set_reg s0c (R_bool minstret_increment) b')
                          nextPC (add_vec_int pc 4))) = Machine).
      { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
        rewrite (set_mi_lookup cur_privilege _ b' eq_refl). exact Lpriv. }
      pose proof (exec_eff_execute_csrr_mstatus_gpr rd
                    (set_reg (set_reg s0c (R_bool minstret_increment) b')
                       nextPC (add_vec_int pc 4))
                    Hrdnz Hprivc) as He.
      rewrite (mstatus_rdval_prewrite s0c b' (add_vec_int pc 4) ms0 Lms0)
        in He.
      destruct (load_sexec_facts s0c b' (add_vec_int pc 4) rd
                  (regval_into_reg ms0))
        as (F1 & F2 & F3 & F4 & F5).
      eexists. split_and!.
      - exact He.
      - rewrite F1. exact Lhart.
      - exact F2.
      - rewrite F3. apply wmem_restrict_dom. }
    assert (HP : wP_eff (Some (fin_to_nat cpu_id)) (regonly_es al4 pc) σ).
    { apply (wP_eff_of_leaf_regonly al4 (fin_to_nat cpu_id) σ (wwin pc pc 0)
               pc w (CSRReg (csr_mstatus, zreg, Regidx rd, CSRRS)) D dst).
      - exact Hwf.
      - exact (wwin_nonzero pc pc 0 Hram (win0_absurd _)).
      - exact (wwin_pinned σ pc pc 0 Haccpc Hacc0 Hpin (win0_absurd _)).
      - exact Lpc0.
      - exact Lpriv.
      - rewrite Lpmpc. exact Hpmp.
      - exact Lpma.
      - exact Lhtif.
      - exact Lhart.
      - exact LmisaS.
      - exact LmisaC.
      - exact LmIE.
      - exact Lelp.
      - exact Hal2.
      - exact Hal4.
      - exact Hram.
      - exact (wwin_conf_text σ pc pc 0 w Htext0).
      - exact HnotRVC.
      - exact (Hagree (wm_regs σ) Lpriv Lmisa Lsec).
      - exact HDmi.
      - exact Hgood.
      - exact Hdec.
      - reflexivity.
      - exact Hc. }
    assert (Hprivf : register_lookup cur_privilege
              (sregs (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                        nextPC (add_vec_int pc 4))) = Machine).
    { rewrite (set_lookup_ne cur_privilege nextPC _ _ ltac:(reg_ne)).
      rewrite (reg_at_flat cur_privilege σ b eq_refl). exact Lpriv. }
    pose proof (exec_eff_execute_csrr_mstatus_gpr rd
                  (set_reg (set_reg (wflat_st σ) (R_bool minstret_increment) b)
                     nextPC (add_vec_int pc 4))
                  Hrdnz Hprivf) as Hef.
    rewrite (mstatus_rdval_prewrite (wflat_st σ) b (add_vec_int pc 4) ms0 Lms0)
      in Hef.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc")
      as "[Hreg Hnpc]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg ms0) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact HP|].
    iExists (set_reg (set_reg (set_reg (wflat_st σ)
                        (R_bool minstret_increment) b)
                      nextPC (add_vec_int pc 4))
                     (R_bitvector_64 (gpr_of_Z (uint rd)))
                     (regval_into_reg ms0)).
    iSplitR; [iPureIntro; exact (exec_eff_exec _ _ _ _ _ Hef)|].
    iFrame "Hreg".
    iNext. iIntros (tick σ' t) "%Hstep %Hdevt0 %Hpost %HQ Hhs Hpc".
    destruct Hpost as (Hregs & Hdevs & Hmems & Himgs & Hlogs & Hwsle & Hwf' &
                       Hbnd').
    destruct HQ as (HQi & HQl & HQw).
    destruct (load_sexec_facts (wflat_st σ) b (add_vec_int pc 4) rd
                (regval_into_reg ms0))
      as (G1 & G2 & G3 & G4 & G5).
    assert (Hdevflat : mdev t = wm_dev σ).
    { rewrite Hdevt0 -(wflat_st_dev σ). exact G4. }
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ')
            with "Hwsauth Hhws") as "[Hwsauth Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iEval (rewrite G5) in "Hpc".
    iSplitL "Hlat"; [by rewrite HQi HQl|].
    iSplitL "Hdev Hlogauth Hwsauth".
    { rewrite /wmstate_norg. iSplitR; [by iPureIntro|].
      iSplitR; [by iPureIntro|].
      rewrite Hdevs Hdevflat HQl. iFrame. }
    iApply ("Hcont" $! (wm_ws σ') with
              "[%] Hhs Hpriv Hms Hpmpc [$Hpc $Hnpc] Hrdc Hhws").
    rewrite Hws. exact Hwsle.
  Qed.

End leaves_csrr.

(* ====================================================================== *)
(** ** 6. Soundness check *)

Print Assumptions exec_eff_execute_csrr_menvcfg_gpr.
Print Assumptions exec_eff_execute_csrr_mcounteren_gpr.
Print Assumptions exec_eff_execute_csrr_sie_gpr.
Print Assumptions exec_eff_execute_csrr_mstatus_gpr.
Print Assumptions exec_eff_execute_csrr_mhartid_gpr.
