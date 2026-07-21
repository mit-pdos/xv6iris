(* WpSieFlipBits.v -- the pure SIE-flip characterizations for the
   csrci/csrsi sstatus leaves (interrupt-sweep stage 7): for a
   well-formed kernel mstatus [ms] (the [sconf_ms_facts] set),
     legalize_sstatus_val ms (sstatus_write_val     ms 2)   clears SIE,
     legalize_sstatus_val ms (sstatus_write_set_val ms 2)   sets   SIE,
   and BOTH preserve every other tracked bit.  Discharges the
   [csrci_sie_flip_ok]/[csrsi_sie_flip_ok] premises of WpSconfCsr.v.

   Proof shape (the monolithic testbit chase does NOT scale -- the
   legalize/lift/lower towers multiply out): per-field ladders in
   WpGprCsrwC's get-over-update style --
     rows  [qX_uY]              getter X through one setter Y;
     L4    [mstatus_legalized_X'] fields of the legalizer;
     L3    [lift_X]             fields of [lift_sstatus];
     L2    [sX_and2]/[sX_or2]   fields of the masked write value;
     L1    [sX_lower]           (imported) fields of the S-view;
   assembled per fact at the very end.                                   *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import WpIntrBits.
Require Import WpGprCsrwCommon WpGprCsrwC.
Require Import IntrDefs.
Local Open Scope Z_scope.

Definition sstatus_write_set_val (ms : mword 64) (imm5 : mword 5) : mword 64 :=
  or_vec (sstatus_read ms) (zero_extend' 64 imm5).

(* ---- get-over-update rows (fresh [q] namespace; the [g] rows of
   WpGprCsrwC are reused where they exist, these fill the gaps and are
   regenerated wholesale for uniformity). ---- *)
Local Ltac quu :=
  unfold _get_Mstatus_SIE, _get_Mstatus_MIE, _get_Mstatus_MPRV, _get_Mstatus_SXL,
         _get_Mstatus_MPP, _get_Mstatus_MXR, _get_Mstatus_TSR, _get_Mstatus_XS,
         _get_Mstatus_FS, _get_Mstatus_VS, _get_Mstatus_SD, _get_Mstatus_SUM,
         _get_Mstatus_TVM, _get_Mstatus_TW, _get_Mstatus_SPELP, _get_Mstatus_MPELP,
         _get_Mstatus_SPP, _get_Mstatus_SPIE, _get_Mstatus_MPIE, _get_Mstatus_UXL,
         _update_Mstatus_SD, _update_Mstatus_SIE, _update_Mstatus_MIE,
         _update_Mstatus_SPIE, _update_Mstatus_MPIE, _update_Mstatus_SPP,
         _update_Mstatus_MPP, _update_Mstatus_VS, _update_Mstatus_FS,
         _update_Mstatus_XS, _update_Mstatus_MPRV, _update_Mstatus_SUM,
         _update_Mstatus_MXR, _update_Mstatus_TVM, _update_Mstatus_TW,
         _update_Mstatus_TSR, _update_Mstatus_SPELP, _update_Mstatus_MPELP,
         _update_Mstatus_UXL;
  unfold subrange_vec_dec, update_subrange_vec_dec;
  rewrite !autocast_refl;
  unfold to_word_idx, to_word, get_word;
  rewrite !MachineWord.MachineWord.cast_idx_refl.

Local Ltac qu_disj :=
  quu;
  apply bv_extract_update_slice_disjoint;
  [ first [ left; vm_compute; let X := fresh in intro X; discriminate X
          | right; vm_compute; let X := fresh in intro X; discriminate X ]
  | vm_compute; let X := fresh in intro X; discriminate X ].

Local Ltac qu_same :=
  quu;
  apply bv_extract_update_slice_same;
  vm_compute; let X := fresh in intro X; discriminate X.


(* row SIE *)
Local Lemma qSIE_uSD (w : mword 64) x : _get_Mstatus_SIE (_update_Mstatus_SD w x) = _get_Mstatus_SIE w.
Proof. qu_disj. Qed.
Local Lemma qSIE_uSIE (w : mword 64) x : _get_Mstatus_SIE (_update_Mstatus_SIE w x) = x.
Proof. qu_same. Qed.

(* row MPRV *)
Local Lemma qMPRV_uSD (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SD w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uSIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SIE w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uMIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MIE w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uSPIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SPIE w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uMPIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MPIE w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uSPP (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SPP w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uMPP (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MPP w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uVS (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_VS w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uFS (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_FS w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uXS (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_XS w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uSUM (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SUM w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uMXR (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MXR w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uSPELP (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SPELP w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uUXL (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_UXL w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Local Lemma qMPRV_uMPRV (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MPRV w x) = x.
Proof. qu_same. Qed.

(* row MXR *)
Local Lemma qMXR_uSD (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_SD w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uSIE (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_SIE w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uMIE (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MIE w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uSPIE (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_SPIE w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uMPIE (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MPIE w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uSPP (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_SPP w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uMPP (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MPP w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uVS (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_VS w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uFS (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_FS w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uXS (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_XS w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uMPRV (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MPRV w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uSUM (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_SUM w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Local Lemma qMXR_uMXR (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MXR w x) = x.
Proof. qu_same. Qed.

(* row TSR *)
Local Lemma qTSR_uSD (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SD w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uSIE (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SIE w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uMIE (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MIE w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uSPIE (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SPIE w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uMPIE (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MPIE w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uSPP (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SPP w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uMPP (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MPP w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uVS (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_VS w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uFS (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_FS w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uXS (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_XS w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uMPRV (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MPRV w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uSUM (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SUM w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uMXR (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MXR w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uTVM (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_TVM w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uTW (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_TW w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uSPELP (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SPELP w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uUXL (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_UXL w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Local Lemma qTSR_uTSR (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_TSR w x) = x.
Proof. qu_same. Qed.

(* row XS *)
Local Lemma qXS_uSD (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_SD w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Local Lemma qXS_uSIE (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_SIE w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Local Lemma qXS_uMIE (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_MIE w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Local Lemma qXS_uSPIE (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_SPIE w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Local Lemma qXS_uMPIE (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_MPIE w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Local Lemma qXS_uSPP (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_SPP w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Local Lemma qXS_uMPP (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_MPP w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Local Lemma qXS_uVS (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_VS w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Local Lemma qXS_uFS (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_FS w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Local Lemma qXS_uXS (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_XS w x) = x.
Proof. qu_same. Qed.

(* row FS *)
Local Lemma qFS_uSD (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_SD w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Local Lemma qFS_uSIE (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_SIE w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Local Lemma qFS_uMIE (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_MIE w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Local Lemma qFS_uSPIE (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_SPIE w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Local Lemma qFS_uMPIE (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_MPIE w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Local Lemma qFS_uSPP (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_SPP w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Local Lemma qFS_uMPP (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_MPP w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Local Lemma qFS_uVS (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_VS w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Local Lemma qFS_uFS (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_FS w x) = x.
Proof. qu_same. Qed.

(* row VS *)
Local Lemma qVS_uSD (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_SD w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Local Lemma qVS_uSIE (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_SIE w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Local Lemma qVS_uMIE (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_MIE w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Local Lemma qVS_uSPIE (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_SPIE w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Local Lemma qVS_uMPIE (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_MPIE w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Local Lemma qVS_uSPP (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_SPP w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Local Lemma qVS_uMPP (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_MPP w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Local Lemma qVS_uVS (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_VS w x) = x.
Proof. qu_same. Qed.

(* row SD *)
Local Lemma qSD_uSD (w : mword 64) x : _get_Mstatus_SD (_update_Mstatus_SD w x) = x.
Proof. qu_same. Qed.

(* row MPP *)
Local Lemma qMPP_uSD (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SD w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uSIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SIE w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uMIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MIE w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uSPIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SPIE w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uMPIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MPIE w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uSPP (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SPP w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uVS (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_VS w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uFS (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_FS w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uXS (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_XS w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uSUM (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SUM w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uMXR (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MXR w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uSPELP (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SPELP w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uUXL (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_UXL w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Local Lemma qMPP_uMPP (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MPP w x) = x.
Proof. qu_same. Qed.

(* row SXL *)
Local Lemma qSXL_uSD (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SD w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uSIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SIE w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uMIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MIE w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uSPIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SPIE w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uMPIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPIE w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uSPP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SPP w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uMPP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPP w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uVS (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_VS w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uFS (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_FS w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uXS (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_XS w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uMPRV (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPRV w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uSUM (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SUM w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uMXR (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MXR w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uTVM (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_TVM w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uTW (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_TW w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uTSR (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_TSR w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uSPELP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SPELP w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Local Lemma qSXL_uMPELP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPELP w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.

(* ---- L4: fields of [mstatus_legalized o v] ---- *)
Local Lemma mstatus_legalized_SIE' (o v : mword 64) :
  _get_Mstatus_SIE (mstatus_legalized o v) = _get_Mstatus_SIE v.
Proof. unfold mstatus_legalized. cbn zeta. rewrite qSIE_uSD qSIE_uSIE. reflexivity. Qed.

Local Lemma mstatus_legalized_MPRV' (o v : mword 64) :
  _get_Mstatus_MPRV (mstatus_legalized o v) = _get_Mstatus_MPRV v.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qMPRV_uSD qMPRV_uSIE qMPRV_uMIE qMPRV_uSPIE qMPRV_uMPIE qMPRV_uSPP
          qMPRV_uMPP qMPRV_uVS qMPRV_uFS qMPRV_uXS qMPRV_uMPRV. reflexivity. Qed.

Local Lemma mstatus_legalized_SXL' (o v : mword 64) :
  _get_Mstatus_SXL (mstatus_legalized o v) = _get_Mstatus_SXL o.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qSXL_uSD qSXL_uSIE qSXL_uMIE qSXL_uSPIE qSXL_uMPIE qSXL_uSPP qSXL_uMPP qSXL_uVS qSXL_uFS qSXL_uXS qSXL_uMPRV qSXL_uSUM qSXL_uMXR qSXL_uTVM qSXL_uTW qSXL_uTSR qSXL_uSPELP qSXL_uMPELP. reflexivity. Qed.

Local Lemma mstatus_legalized_MXR' (o v : mword 64) :
  _get_Mstatus_MXR (mstatus_legalized o v) = _get_Mstatus_MXR v.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qMXR_uSD qMXR_uSIE qMXR_uMIE qMXR_uSPIE qMXR_uMPIE qMXR_uSPP
          qMXR_uMPP qMXR_uVS qMXR_uFS qMXR_uXS qMXR_uMPRV qMXR_uSUM qMXR_uMXR.
  reflexivity. Qed.

Local Lemma mstatus_legalized_TSR' (o v : mword 64) :
  _get_Mstatus_TSR (mstatus_legalized o v) = _get_Mstatus_TSR v.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qTSR_uSD qTSR_uSIE qTSR_uMIE qTSR_uSPIE qTSR_uMPIE qTSR_uSPP
          qTSR_uMPP qTSR_uVS qTSR_uFS qTSR_uXS qTSR_uMPRV qTSR_uSUM qTSR_uMXR
          qTSR_uTVM qTSR_uTW qTSR_uTSR. reflexivity. Qed.

Local Lemma mstatus_legalized_XS' (o v : mword 64) :
  _get_Mstatus_XS (mstatus_legalized o v) = extStatus_map_forwards Off.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qXS_uSD qXS_uSIE qXS_uMIE qXS_uSPIE qXS_uMPIE qXS_uSPP
          qXS_uMPP qXS_uVS qXS_uFS qXS_uXS. reflexivity. Qed.

Local Lemma mstatus_legalized_FS' (o v : mword 64) :
  _get_Mstatus_FS (mstatus_legalized o v)
  = legalize_extStatus plat_mstatus_legal_fs (_get_Mstatus_FS v).
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qFS_uSD qFS_uSIE qFS_uMIE qFS_uSPIE qFS_uMPIE qFS_uSPP
          qFS_uMPP qFS_uVS qFS_uFS. reflexivity. Qed.

Local Lemma mstatus_legalized_VS' (o v : mword 64) :
  _get_Mstatus_VS (mstatus_legalized o v)
  = legalize_extStatus plat_mstatus_legal_vs (_get_Mstatus_VS v).
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qVS_uSD qVS_uSIE qVS_uMIE qVS_uSPIE qVS_uMPIE qVS_uSPP
          qVS_uMPP qVS_uVS. reflexivity. Qed.

Local Lemma mstatus_legalized_SD' (o v : mword 64) :
  _get_Mstatus_SD (mstatus_legalized o v)
  = bool_to_bit
      (orb (generic_eq (extStatus_map_backwards
              (legalize_extStatus plat_mstatus_legal_fs (_get_Mstatus_FS v))) Dirty)
        (orb (generic_eq (extStatus_map_backwards (extStatus_map_forwards Off)) Dirty)
          (generic_eq (extStatus_map_backwards
              (legalize_extStatus plat_mstatus_legal_vs (_get_Mstatus_VS v))) Dirty))).
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qSD_uSD.
  rewrite qFS_uSIE qFS_uMIE qFS_uSPIE qFS_uMPIE qFS_uSPP qFS_uMPP qFS_uVS qFS_uFS.
  rewrite qXS_uSIE qXS_uMIE qXS_uSPIE qXS_uMPIE qXS_uSPP qXS_uMPP qXS_uVS qXS_uFS qXS_uXS.
  rewrite qVS_uSIE qVS_uMIE qVS_uSPIE qVS_uMPIE qVS_uSPP qVS_uMPP qVS_uVS.
  reflexivity. Qed.

Local Lemma mstatus_legalized_MPP' (o v : mword 64) :
  _get_Mstatus_MPP (mstatus_legalized o v)
  = (if have_nom_val (_get_Mstatus_MPP v)
     then _get_Mstatus_MPP v else privLevel_to_bits User).
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qMPP_uSD qMPP_uSIE qMPP_uMIE qMPP_uSPIE qMPP_uMPIE qMPP_uSPP qMPP_uMPP.
  reflexivity. Qed.

(* ---- L3: fields of [lift_sstatus m s] ---- *)
Local Lemma lift_SIE (m s : mword 64) :
  _get_Mstatus_SIE (lift_sstatus m s) = _get_Sstatus_SIE s.
Proof. unfold lift_sstatus. cbn zeta. rewrite qSIE_uSIE. reflexivity. Qed.

Local Lemma lift_MPRV (m s : mword 64) :
  _get_Mstatus_MPRV (lift_sstatus m s) = _get_Mstatus_MPRV m.
Proof. unfold lift_sstatus. cbn zeta.
  rewrite qMPRV_uSIE qMPRV_uSPIE qMPRV_uSPP qMPRV_uVS qMPRV_uFS qMPRV_uXS qMPRV_uSUM qMPRV_uMXR qMPRV_uSPELP qMPRV_uUXL qMPRV_uSD. reflexivity. Qed.

Local Lemma lift_MXR (m s : mword 64) :
  _get_Mstatus_MXR (lift_sstatus m s) = _get_Sstatus_MXR s.
Proof. unfold lift_sstatus. cbn zeta.
  rewrite qMXR_uSIE qMXR_uSPIE qMXR_uSPP qMXR_uVS qMXR_uFS qMXR_uXS qMXR_uSUM qMXR_uMXR. reflexivity. Qed.

Local Lemma lift_TSR (m s : mword 64) :
  _get_Mstatus_TSR (lift_sstatus m s) = _get_Mstatus_TSR m.
Proof. unfold lift_sstatus. cbn zeta.
  rewrite qTSR_uSIE qTSR_uSPIE qTSR_uSPP qTSR_uVS qTSR_uFS qTSR_uXS qTSR_uSUM qTSR_uMXR qTSR_uSPELP qTSR_uUXL qTSR_uSD. reflexivity. Qed.


Local Lemma lift_FS (m s : mword 64) :
  _get_Mstatus_FS (lift_sstatus m s) = _get_Sstatus_FS s.
Proof. unfold lift_sstatus. cbn zeta.
  rewrite qFS_uSIE qFS_uSPIE qFS_uSPP qFS_uVS qFS_uFS. reflexivity. Qed.

Local Lemma lift_VS (m s : mword 64) :
  _get_Mstatus_VS (lift_sstatus m s) = _get_Sstatus_VS s.
Proof. unfold lift_sstatus. cbn zeta.
  rewrite qVS_uSIE qVS_uSPIE qVS_uSPP qVS_uVS. reflexivity. Qed.

Local Lemma lift_MPP (m s : mword 64) :
  _get_Mstatus_MPP (lift_sstatus m s) = _get_Mstatus_MPP m.
Proof. unfold lift_sstatus. cbn zeta.
  rewrite qMPP_uSIE qMPP_uSPIE qMPP_uSPP qMPP_uVS qMPP_uFS qMPP_uXS qMPP_uSUM qMPP_uMXR qMPP_uSPELP qMPP_uUXL qMPP_uSD. reflexivity. Qed.

(* ---- L2: fields of the masked write values.  The mask is the CLOSED
   constant [not_vec (zext 2)] / [zext 2]; a generic land/lor testbit
   splitter reduces each field to a vm-computed mask bit. ---- *)
Local Ltac s_prep :=
  unfold _get_Sstatus_SIE, _get_Sstatus_MXR, _get_Sstatus_FS, _get_Sstatus_VS,
         _get_Sstatus_XS;
  unfold subrange_vec_dec;
  rewrite !autocast_refl;
  unfold to_word_idx, to_word, get_word;
  rewrite !MachineWord.MachineWord.cast_idx_refl;
  unfold MachineWord.MachineWord.slice.

Local Lemma and_vec_testbit (a b : mword 64) (p : Z) :
  Z.testbit (bv_unsigned (and_vec a b)) p
  = andb (Z.testbit (bv_unsigned a) p) (Z.testbit (bv_unsigned b) p).
Proof.
  unfold and_vec, word_binop, with_word', with_word, to_word, get_word.
  unfold MachineWord.MachineWord.and.
  rewrite bv_and_unsigned. apply Z.land_spec.
Qed.

Local Lemma or_vec_testbit (a b : mword 64) (p : Z) :
  Z.testbit (bv_unsigned (or_vec a b)) p
  = orb (Z.testbit (bv_unsigned a) p) (Z.testbit (bv_unsigned b) p).
Proof.
  unfold or_vec, word_binop, with_word', with_word, to_word, get_word.
  unfold MachineWord.MachineWord.or.
  rewrite bv_or_unsigned. apply Z.lor_spec.
Qed.

Local Definition mask2c : mword 64 := not_vec (zero_extend' 64 (mword_of_int 2 : mword 5)).
Local Definition mask2s : mword 64 := zero_extend' 64 (mword_of_int 2 : mword 5).

(* per-field transparency/forcing through the AND mask (csrci) *)
Local Ltac schase_and :=
  rewrite !bv_extract_unsigned;
  rewrite !bv_wrap_spec_low; [|lia|lia];
  rewrite !Z.shiftr_spec; [|lia|lia];
  rewrite and_vec_testbit;
  match goal with
  | |- context [Z.testbit (bv_unsigned mask2c) ?P] =>
      replace (Z.testbit (bv_unsigned mask2c) P) with true
        by (vm_compute; reflexivity)
  end;
  rewrite andb_true_r; reflexivity.

Local Ltac sfield_and1 :=
  s_prep;
  apply (bv_eq_testbit 1); intros k Hk;
  assert (k = 0) as -> by lia;
  schase_and.

Local Ltac sfield_and2w :=
  s_prep;
  apply (bv_eq_testbit 2); intros k Hk;
  (destruct (Z.eq_dec k 0) as [->|];
   [ schase_and | assert (k = 1) as -> by lia; schase_and ]).

Local Lemma sSIE_and2 (w : mword 64) :
  _get_Sstatus_SIE (and_vec w mask2c) = ('b"0" : mword 1).
Proof.
  s_prep.
  apply (bv_eq_testbit 1); intros k Hk.
  assert (k = 0) as -> by lia.
  rewrite bv_extract_unsigned.
  rewrite bv_wrap_spec_low; [|lia].
  rewrite Z.shiftr_spec; [|lia].
  rewrite and_vec_testbit.
  replace (Z.testbit (bv_unsigned mask2c) (0 + 1)) with false
    by (vm_compute; reflexivity).
  rewrite andb_false_r. vm_compute. reflexivity.
Qed.

Local Lemma sMXR_and2 (w : mword 64) :
  _get_Sstatus_MXR (and_vec w mask2c) = _get_Sstatus_MXR w.
Proof. sfield_and1. Qed.
Local Lemma sFS_and2 (w : mword 64) :
  _get_Sstatus_FS (and_vec w mask2c) = _get_Sstatus_FS w.
Proof. sfield_and2w. Qed.
Local Lemma sVS_and2 (w : mword 64) :
  _get_Sstatus_VS (and_vec w mask2c) = _get_Sstatus_VS w.
Proof. sfield_and2w. Qed.
Local Lemma sXS_and2 (w : mword 64) :
  _get_Sstatus_XS (and_vec w mask2c) = _get_Sstatus_XS w.
Proof. sfield_and2w. Qed.

(* the OR duals (csrsi) *)
Local Ltac schase_or :=
  rewrite !bv_extract_unsigned;
  rewrite !bv_wrap_spec_low; [|lia|lia];
  rewrite !Z.shiftr_spec; [|lia|lia];
  rewrite or_vec_testbit;
  match goal with
  | |- context [Z.testbit (bv_unsigned mask2s) ?P] =>
      replace (Z.testbit (bv_unsigned mask2s) P) with false
        by (vm_compute; reflexivity)
  end;
  rewrite orb_false_r; reflexivity.

Local Ltac sfield_or1 :=
  s_prep;
  apply (bv_eq_testbit 1); intros k Hk;
  assert (k = 0) as -> by lia;
  schase_or.

Local Ltac sfield_or2w :=
  s_prep;
  apply (bv_eq_testbit 2); intros k Hk;
  (destruct (Z.eq_dec k 0) as [->|];
   [ schase_or | assert (k = 1) as -> by lia; schase_or ]).

Local Lemma sSIE_or2 (w : mword 64) :
  _get_Sstatus_SIE (or_vec w mask2s) = ('b"1" : mword 1).
Proof.
  s_prep.
  apply (bv_eq_testbit 1); intros k Hk.
  assert (k = 0) as -> by lia.
  rewrite bv_extract_unsigned.
  rewrite bv_wrap_spec_low; [|lia].
  rewrite Z.shiftr_spec; [|lia].
  rewrite or_vec_testbit.
  replace (Z.testbit (bv_unsigned mask2s) (0 + 1)) with true
    by (vm_compute; reflexivity).
  rewrite orb_true_r. vm_compute. reflexivity.
Qed.

Local Lemma sMXR_or2 (w : mword 64) :
  _get_Sstatus_MXR (or_vec w mask2s) = _get_Sstatus_MXR w.
Proof. sfield_or1. Qed.
Local Lemma sFS_or2 (w : mword 64) :
  _get_Sstatus_FS (or_vec w mask2s) = _get_Sstatus_FS w.
Proof. sfield_or2w. Qed.
Local Lemma sVS_or2 (w : mword 64) :
  _get_Sstatus_VS (or_vec w mask2s) = _get_Sstatus_VS w.
Proof. sfield_or2w. Qed.
Local Lemma sXS_or2 (w : mword 64) :
  _get_Sstatus_XS (or_vec w mask2s) = _get_Sstatus_XS w.
Proof. sfield_or2w. Qed.

(* ---- assembly ---- *)
Section Assembly.

  (* the common per-field bridge: the write value's S-field, off bit 1,
     is the OLD mstatus field. *)
  Local Lemma wval_and_field :
    forall ms : mword 64,
      _get_Sstatus_MXR (sstatus_write_val ms (mword_of_int 2)) = _get_Mstatus_MXR ms /\
      _get_Sstatus_FS (sstatus_write_val ms (mword_of_int 2)) = _get_Mstatus_FS ms /\
      _get_Sstatus_VS (sstatus_write_val ms (mword_of_int 2)) = _get_Mstatus_VS ms /\
      _get_Sstatus_XS (sstatus_write_val ms (mword_of_int 2)) = _get_Mstatus_XS ms.
  Proof.
    intros ms. unfold sstatus_write_val.
    unfold sstatus_read. rewrite subrange_full.
    rewrite sMXR_and2 sFS_and2 sVS_and2 sXS_and2.
    rewrite sMXR_lower sFS_lower sVS_lower sXS_lower.
    auto.
  Qed.

  Local Lemma wval_or_field :
    forall ms : mword 64,
      _get_Sstatus_MXR (sstatus_write_set_val ms (mword_of_int 2)) = _get_Mstatus_MXR ms /\
      _get_Sstatus_FS (sstatus_write_set_val ms (mword_of_int 2)) = _get_Mstatus_FS ms /\
      _get_Sstatus_VS (sstatus_write_set_val ms (mword_of_int 2)) = _get_Mstatus_VS ms /\
      _get_Sstatus_XS (sstatus_write_set_val ms (mword_of_int 2)) = _get_Mstatus_XS ms.
  Proof.
    intros ms. unfold sstatus_write_set_val.
    unfold sstatus_read. rewrite subrange_full.
    rewrite sMXR_or2 sFS_or2 sVS_or2 sXS_or2.
    rewrite sMXR_lower sFS_lower sVS_lower sXS_lower.
    auto.
  Qed.

  (* one generic core covering both flips: the legalized write of a value
     whose S-fields off bit 1 mirror [ms] and whose SIE field is [b]. *)
  Local Lemma flip_core (ms W : mword 64) (b : mword 1) :
    sconf_ms_facts ms ->
    _get_Sstatus_SIE W = b ->
    _get_Sstatus_MXR W = _get_Mstatus_MXR ms ->
    _get_Sstatus_FS W = _get_Mstatus_FS ms ->
    _get_Sstatus_VS W = _get_Mstatus_VS ms ->
    _get_Sstatus_XS W = _get_Mstatus_XS ms ->
    _get_Mstatus_SIE (legalize_sstatus_val ms W) = b /\
    sconf_ms_facts (legalize_sstatus_val ms W).
  Proof.
    intros (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP)
           HbW HmxrW HfsW HvsW HxsW.
    unfold legalize_sstatus_val.
    rewrite zext64_id.
    unfold Mk_Sstatus.
    split.
    { rewrite mstatus_legalized_SIE' lift_SIE. exact HbW. }
    unfold sconf_ms_facts.
    rewrite mstatus_legalized_MPRV' lift_MPRV.
    rewrite mstatus_legalized_SXL'.
    rewrite mstatus_legalized_MXR' lift_MXR HmxrW.
    rewrite mstatus_legalized_TSR' lift_TSR.
    rewrite mstatus_legalized_XS'.
    rewrite mstatus_legalized_FS' lift_FS HfsW HFS.
    rewrite mstatus_legalized_VS' lift_VS HvsW HVS.
    rewrite mstatus_legalized_SD' lift_FS lift_VS HfsW HvsW HFS HVS.
    rewrite mstatus_legalized_MPP' lift_MPP HMPP.
    cbn match.
    repeat split; first [ assumption | vm_compute; reflexivity ].
  Qed.

  Lemma csrci_sie_flip (ms : mword 64) :
    sconf_ms_facts ms ->
    _get_Mstatus_SIE (legalize_sstatus_val ms (sstatus_write_val ms (mword_of_int 2)))
      = ('b"0" : mword 1) /\
    sconf_ms_facts (legalize_sstatus_val ms (sstatus_write_val ms (mword_of_int 2))).
  Proof.
    intros Hf.
    destruct (wval_and_field ms) as (Hmxr & Hfs & Hvs & Hxs).
    apply (flip_core ms _ ('b"0")); try assumption.
    unfold sstatus_write_val, sstatus_read. rewrite subrange_full. apply sSIE_and2.
  Qed.

  Lemma csrsi_sie_flip (ms : mword 64) :
    sconf_ms_facts ms ->
    _get_Mstatus_SIE (legalize_sstatus_val ms (sstatus_write_set_val ms (mword_of_int 2)))
      = ('b"1" : mword 1) /\
    sconf_ms_facts (legalize_sstatus_val ms (sstatus_write_set_val ms (mword_of_int 2))).
  Proof.
    intros Hf.
    destruct (wval_or_field ms) as (Hmxr & Hfs & Hvs & Hxs).
    apply (flip_core ms _ ('b"1")); try assumption.
    unfold sstatus_write_set_val, sstatus_read. rewrite subrange_full. apply sSIE_or2.
  Qed.

End Assembly.
