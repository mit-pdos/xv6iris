(* WpSieFlipBits.v -- the pure SIE-flip characterizations for the
   csrci/csrsi sstatus leaves (interrupt-sweep stage 7): for a
   well-formed kernel mstatus [ms] (the [sconf_ms_facts] set),
     legalize_sstatus_val ms (sstatus_write_val     ms 2)   clears SIE,
     legalize_sstatus_val ms (sstatus_write_set_val ms 2)   sets   SIE,
   and BOTH preserve every other tracked bit.  Discharges the
   [csrci_sie_flip_ok]/[csrsi_sie_flip_ok] premises of WpSconfCsr.v.

   Proof shape (the monolithic testbit chase does NOT scale -- the
   legalize/lift/lower towers multiply out): per-field ladders in
   WpGprCsrwC's get-over-update style.  The bottom TWO layers live in
   WpGprCsrwC.v (this file's rows and legalizer facts were moved there so the
   M-mode boot chain, which cannot see IntrDefs, can use them too); only L3
   and up are local:
     rows  [qX_uY]              getter X through one setter Y   (WpGprCsrwC)
     L4    [mstatus_legalized_X] fields of the legalizer         (WpGprCsrwC)
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
Require Import MstatusBits.
Require Import WpGprCsrwCommon WpGprCsrwC.
Require Import IntrDefs.
Local Open Scope Z_scope.

Definition sstatus_write_set_val (ms : mword 64) (imm5 : mword 5) : mword 64 :=
  or_vec (sstatus_read ms) (zero_extend' 64 imm5).


(* ---- L3: fields of [lift_sstatus m s] ---- *)
Local Lemma lift_SIE (m s : mword 64) :
  _get_Mstatus_SIE (lift_sstatus m s) = _get_Sstatus_SIE s.
Proof. unfold lift_sstatus. cbn zeta. rewrite qSIE_uSIE. reflexivity. Qed.

(* SPP / SPIE: the two fields an [sret] reads.  Like SIE they come from the
   WRITE value, not from [m] -- they are S-writable -- so a restore of a
   saved sstatus puts back exactly what was saved.  That is the whole
   content of kerneltrap's last instruction. *)
Local Lemma lift_SPP (m s : mword 64) :
  _get_Mstatus_SPP (lift_sstatus m s) = _get_Sstatus_SPP s.
Proof. unfold lift_sstatus. cbn zeta.
  rewrite qSPP_uSIE qSPP_uSPIE qSPP_uSPP. reflexivity. Qed.

Local Lemma lift_SPIE (m s : mword 64) :
  _get_Mstatus_SPIE (lift_sstatus m s) = _get_Sstatus_SPIE s.
Proof. unfold lift_sstatus. cbn zeta.
  rewrite qSPIE_uSIE qSPIE_uSPIE. reflexivity. Qed.

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


Local Lemma lift_TVM (m s : mword 64) :
  _get_Mstatus_TVM (lift_sstatus m s) = _get_Mstatus_TVM m.
Proof. unfold lift_sstatus. cbn zeta.
  rewrite qTVM_uSIE qTVM_uSPIE qTVM_uSPP qTVM_uVS qTVM_uFS qTVM_uXS qTVM_uSUM qTVM_uMXR qTVM_uSPELP qTVM_uUXL qTVM_uSD. reflexivity. Qed.

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

  (* ONE GENERIC CORE, and it is the reusable statement, not an internal
     step: the legalized write of ANY value [W] whose tracked S-fields
     mirror [ms] preserves [sconf_ms_facts] and lands SIE / SPP / SPIE at
     [W]'s own.  The two SIE flips below are the [W = sstatus_write_val ...]
     instances; [csrw sstatus] with a saved sstatus is the other consumer
     (kerneltrap restoring the trap state -- SPP and SPIE are what
     kernelvec's [sret] then reads), which is why this is NOT [Local]: a
     [Local Lemma] is invisible to every other file. *)
  Lemma flip_core (ms W : mword 64) (b : mword 1) :
    sconf_ms_facts ms ->
    _get_Sstatus_SIE W = b ->
    _get_Sstatus_MXR W = _get_Mstatus_MXR ms ->
    _get_Sstatus_FS W = _get_Mstatus_FS ms ->
    _get_Sstatus_VS W = _get_Mstatus_VS ms ->
    _get_Sstatus_XS W = _get_Mstatus_XS ms ->
    _get_Mstatus_SIE (legalize_sstatus_val ms W) = b /\
    _get_Mstatus_SPP (legalize_sstatus_val ms W) = _get_Sstatus_SPP W /\
    _get_Mstatus_SPIE (legalize_sstatus_val ms W) = _get_Sstatus_SPIE W /\
    sconf_ms_facts (legalize_sstatus_val ms W).
  Proof.
    intros (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM)
           HbW HmxrW HfsW HvsW HxsW.
    unfold legalize_sstatus_val.
    rewrite zext64_id.
    unfold Mk_Sstatus.
    split.
    { rewrite mstatus_legalized_SIE lift_SIE. exact HbW. }
    split.
    { rewrite mstatus_legalized_SPP lift_SPP. reflexivity. }
    split.
    { rewrite mstatus_legalized_SPIE lift_SPIE. reflexivity. }
    unfold sconf_ms_facts.
    rewrite mstatus_legalized_MPRV lift_MPRV.
    rewrite mstatus_legalized_SXL.
    rewrite mstatus_legalized_MXR lift_MXR HmxrW.
    rewrite mstatus_legalized_TSR lift_TSR.
    rewrite mstatus_legalized_TVM lift_TVM.
    rewrite mstatus_legalized_XS.
    rewrite mstatus_legalized_FS lift_FS HfsW HFS.
    rewrite mstatus_legalized_VS lift_VS HvsW HVS.
    rewrite mstatus_legalized_SD lift_FS lift_VS HfsW HvsW HFS HVS.
    rewrite mstatus_legalized_MPP lift_MPP HMPP.
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
    assert (Hsie : _get_Sstatus_SIE (sstatus_write_val ms (mword_of_int 2))
                   = ('b"0" : mword 1)).
    { unfold sstatus_write_val, sstatus_read. rewrite subrange_full. apply sSIE_and2. }
    destruct (flip_core ms _ ('b"0") Hf Hsie Hmxr Hfs Hvs Hxs) as (H1 & _ & _ & H4).
    exact (conj H1 H4).
  Qed.

  Lemma csrsi_sie_flip (ms : mword 64) :
    sconf_ms_facts ms ->
    _get_Mstatus_SIE (legalize_sstatus_val ms (sstatus_write_set_val ms (mword_of_int 2)))
      = ('b"1" : mword 1) /\
    sconf_ms_facts (legalize_sstatus_val ms (sstatus_write_set_val ms (mword_of_int 2))).
  Proof.
    intros Hf.
    destruct (wval_or_field ms) as (Hmxr & Hfs & Hvs & Hxs).
    assert (Hsie : _get_Sstatus_SIE (sstatus_write_set_val ms (mword_of_int 2))
                   = ('b"1" : mword 1)).
    { unfold sstatus_write_set_val, sstatus_read. rewrite subrange_full. apply sSIE_or2. }
    destruct (flip_core ms _ ('b"1") Hf Hsie Hmxr Hfs Hvs Hxs) as (H1 & _ & _ & H4).
    exact (conj H1 H4).
  Qed.

End Assembly.
