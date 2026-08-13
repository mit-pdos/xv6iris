(* WpGprCsrwC.v -- new-style WPs for the two CONFIG-WRITING csrw instructions
   xv6's start() executes and that were deliberately skipped by WpGprCsrwA/B:
     - csrw mstatus  (0x300) : writes the mstatus cell INSIDE [mmode_config];
     - csrw pmpcfg0  (0x3a0) : writes the pmpcfg_n cell threaded by [wp_instr].
   Both are built on [wp_instr_config] (InstrBytes.v), the engine that takes
   [mmode_config (DfracOwn 1)] + [pmpcfg_n ↦ᵣ pmpcfg0] at FULL ownership and
   lets the caller reg_update those cells while exhibiting [s_exec].

   Also THE HOME of the field-preservation facts of [mstatus_legalized] that
   let a chain REBUILD [mmode_config (DfracOwn 1)] after the mstatus write --
   all TWELVE fields the kernel's mstatus contract tracks (MIE plus
   [MstatusFacts.mstatus_kernel_facts]'s eleven):
     - MIE / MPRV / MXR / TSR / TVM / SIE of the legalized value depend ONLY
       on the written value [v];
     - XS is Off and SD / FS / VS are functions of [v] alone;
     - SXL is preserved from the OLD mstatus (never touched by the legalizer);
     - MPP of the legalized value depends only on [v] (the fact the boot chain
       uses to know MPP = Supervisor at the eventual MRET).
   Under them, ONE get-over-update row family ([q<FIELD>_u<SETTER>]) covering
   every field × every setter the legalizer and MRET perform. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RegFile WpGpr.
Require Import MinstretInv InstrBytes.
Require Import WpGprCsrwCommon WpGprCsrwA.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* Generic bit-window facts about [MachineWord.update_slice] (the stdpp-bv  *)
(* core of [update_subrange_vec_dec]): extracting a window DISJOINT from    *)
(* the updated window reads the original word; extracting EXACTLY the       *)
(* updated window reads the written value.                                  *)
(* ====================================================================== *)
Lemma bv_extract_update_slice_disjoint (m n : N) (w : bv m) (i t k : N) (x : bv n) :
  ((t + k <= i)%N \/ (i + n <= t)%N) ->
  (t + k <= m)%N ->
  bv_extract t k (MachineWord.MachineWord.update_slice (n:=n) w i x)
  = bv_extract t k w.
Proof.
  intros Hdisj Hlim.
  unfold MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  apply bv_eq.
  rewrite !bv_extract_unsigned !bv_concat_unsigned' !bv_extract_unsigned.
  rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus.
  apply Z.bits_inj'. intros j Hj.
  destruct (decide (j < Z.of_N k)) as [Hjk|Hjk].
  2: { rewrite !Z.mod_pow2_bits_high; lia. }
  rewrite !(Z.mod_pow2_bits_low _ (Z.of_N k)); [|lia|lia].
  rewrite !(Z.shiftr_spec _ (Z.of_N t)); [|lia|lia].
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N m)); [|lia].
  rewrite !Z.lor_spec.
  destruct Hdisj as [Hd|Hd].
  - (* window strictly below the update: only the low slice contributes *)
    rewrite (Z.shiftl_spec_low _ (Z.of_N (i+n))); [|lia].
    rewrite (Z.mod_pow2_bits_low _ (Z.of_N (i+n))); [|lia].
    rewrite Z.lor_spec.
    rewrite (Z.shiftl_spec_low _ (Z.of_N i)); [|lia].
    rewrite (Z.mod_pow2_bits_low _ (Z.of_N i)); [|lia].
    reflexivity.
  - (* window strictly above the update: only the high slice contributes *)
    rewrite (Z.mod_pow2_bits_high _ (Z.of_N (i+n))); [|lia].
    rewrite (Z.shiftl_spec _ (Z.of_N (i+n))); [|lia].
    rewrite (Z.mod_pow2_bits_low _ (Z.of_N (m-n-i))); [|lia].
    rewrite (Z.shiftr_spec _ (Z.of_N (i+n))); [|lia].
    replace (j + Z.of_N t - Z.of_N (i + n) + Z.of_N (i + n)) with (j + Z.of_N t) by lia.
    rewrite orb_false_r. reflexivity.
Qed.

Lemma bv_extract_update_slice_same (m n : N) (w : bv m) (i : N) (x : bv n) :
  ((i + n <= m)%N) ->
  bv_extract i n (MachineWord.MachineWord.update_slice (n:=n) w i x) = x.
Proof.
  intros Hlim.
  unfold MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  apply bv_eq.
  rewrite !bv_extract_unsigned !bv_concat_unsigned' !bv_extract_unsigned.
  rewrite Z.shiftr_0_r.
  pose proof (bv_unsigned_in_range _ x) as [Hx0 Hxhi].
  unfold bv_wrap, bv_modulus in *.
  apply Z.bits_inj'. intros j Hj.
  destruct (decide (j < Z.of_N n)) as [Hjn|Hjn].
  2: { rewrite Z.mod_pow2_bits_high; [|lia].
       symmetry. destruct (decide (bv_unsigned x = 0)) as [->|Hnz].
       - apply Z.bits_0.
       - apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2 in Hxhi; lia. }
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N n)); [|lia].
  rewrite (Z.shiftr_spec _ (Z.of_N i)); [|lia].
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N m)); [|lia].
  rewrite !Z.lor_spec.
  rewrite (Z.shiftl_spec_low _ (Z.of_N (i+n))); [|lia].
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N (i+n))); [|lia].
  rewrite Z.lor_spec.
  rewrite (Z.shiftl_spec _ (Z.of_N i)); [|lia].
  rewrite (Z.mod_pow2_bits_high _ (Z.of_N i)); [|lia].
  replace (j + Z.of_N i - Z.of_N i) with j by lia.
  rewrite orb_false_l orb_false_r. reflexivity.
Qed.

(* ---- get-over-update rows: getter X through one setter Y, one instance of
   the two bv window lemmas above at the concrete field positions, discharged
   by a uniform tactic.  ONE family for the whole tree ([q]): the rows for the
   eight fields beyond MIE/MPRV/SXL/MPP were proved in WpSieFlipBits.v (which
   requires IntrDefs and so is invisible to the M-mode boot chain) and live
   here now, together with the [mstatus_legalized] field lemmas over them --
   WpStartNew.v needs both to show that [start()]'s mstatus write preserves
   [MstatusFacts.mstatus_kernel_facts], and WpSieFlipBits reaches them through
   its existing [Require Import WpGprCsrwC].  The rows over the five setters
   MRET performs (MIE / MPIE / MPP / MPRV / MPELP -- WpGprMretWp's cms1..cms5)
   are here for the same reason.  The tactics are NOT [Local] because
   WpSieFlipBits's own remaining [lift_X] / [sX_and2] ladders use them. ---- *)
Ltac quu :=
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

Ltac qu_disj :=
  quu;
  apply bv_extract_update_slice_disjoint;
  [ first [ left; vm_compute; let X := fresh in intro X; discriminate X
          | right; vm_compute; let X := fresh in intro X; discriminate X ]
  | vm_compute; let X := fresh in intro X; discriminate X ].

Ltac qu_same :=
  quu;
  apply bv_extract_update_slice_same;
  vm_compute; let X := fresh in intro X; discriminate X.


(* row MIE (bit 3) *)
Lemma qMIE_uSD (w : mword 64) x : _get_Mstatus_MIE (_update_Mstatus_SD w x) = _get_Mstatus_MIE w.
Proof. qu_disj. Qed.
Lemma qMIE_uSIE (w : mword 64) x : _get_Mstatus_MIE (_update_Mstatus_SIE w x) = _get_Mstatus_MIE w.
Proof. qu_disj. Qed.
Lemma qMIE_uMIE (w : mword 64) x : _get_Mstatus_MIE (_update_Mstatus_MIE w x) = x.
Proof. qu_same. Qed.

(* row SIE *)
Lemma qSIE_uSD (w : mword 64) x : _get_Mstatus_SIE (_update_Mstatus_SD w x) = _get_Mstatus_SIE w.
Proof. qu_disj. Qed.
Lemma qSIE_uSIE (w : mword 64) x : _get_Mstatus_SIE (_update_Mstatus_SIE w x) = x.
Proof. qu_same. Qed.
Lemma qSIE_uMIE (w : mword 64) x : _get_Mstatus_SIE (_update_Mstatus_MIE w x) = _get_Mstatus_SIE w.
Proof. qu_disj. Qed.
Lemma qSIE_uMPIE (w : mword 64) x : _get_Mstatus_SIE (_update_Mstatus_MPIE w x) = _get_Mstatus_SIE w.
Proof. qu_disj. Qed.
Lemma qSIE_uMPP (w : mword 64) x : _get_Mstatus_SIE (_update_Mstatus_MPP w x) = _get_Mstatus_SIE w.
Proof. qu_disj. Qed.
Lemma qSIE_uMPRV (w : mword 64) x : _get_Mstatus_SIE (_update_Mstatus_MPRV w x) = _get_Mstatus_SIE w.
Proof. qu_disj. Qed.
Lemma qSIE_uMPELP (w : mword 64) x : _get_Mstatus_SIE (_update_Mstatus_MPELP w x) = _get_Mstatus_SIE w.
Proof. qu_disj. Qed.

(* row MPRV *)
Lemma qMPRV_uSD (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SD w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uSIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SIE w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uMIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MIE w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uSPIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SPIE w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uMPIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MPIE w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uSPP (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SPP w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uMPP (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MPP w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uVS (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_VS w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uFS (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_FS w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uXS (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_XS w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uSUM (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SUM w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uMXR (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MXR w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uSPELP (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SPELP w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uUXL (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_UXL w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.
Lemma qMPRV_uMPRV (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MPRV w x) = x.
Proof. qu_same. Qed.
Lemma qMPRV_uMPELP (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MPELP w x) = _get_Mstatus_MPRV w.
Proof. qu_disj. Qed.

(* row MXR *)
Lemma qMXR_uSD (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_SD w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uSIE (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_SIE w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uMIE (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MIE w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uSPIE (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_SPIE w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uMPIE (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MPIE w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uSPP (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_SPP w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uMPP (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MPP w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uVS (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_VS w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uFS (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_FS w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uXS (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_XS w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uMPRV (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MPRV w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uSUM (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_SUM w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.
Lemma qMXR_uMXR (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MXR w x) = x.
Proof. qu_same. Qed.
Lemma qMXR_uMPELP (w : mword 64) x : _get_Mstatus_MXR (_update_Mstatus_MPELP w x) = _get_Mstatus_MXR w.
Proof. qu_disj. Qed.

(* row TSR *)
Lemma qTSR_uSD (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SD w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uSIE (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SIE w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uMIE (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MIE w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uSPIE (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SPIE w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uMPIE (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MPIE w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uSPP (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SPP w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uMPP (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MPP w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uVS (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_VS w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uFS (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_FS w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uXS (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_XS w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uMPRV (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MPRV w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uSUM (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SUM w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uMXR (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MXR w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uTVM (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_TVM w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uTW (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_TW w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uSPELP (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_SPELP w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uUXL (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_UXL w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.
Lemma qTSR_uTSR (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_TSR w x) = x.
Proof. qu_same. Qed.
Lemma qTSR_uMPELP (w : mword 64) x : _get_Mstatus_TSR (_update_Mstatus_MPELP w x) = _get_Mstatus_TSR w.
Proof. qu_disj. Qed.

(* row TVM (rwx-kmap: sconf_ms_facts gains the TVM=0 conjunct) *)
Lemma qTVM_uSD (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_SD w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uSIE (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_SIE w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uMIE (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_MIE w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uSPIE (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_SPIE w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uMPIE (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_MPIE w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uSPP (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_SPP w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uMPP (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_MPP w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uVS (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_VS w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uFS (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_FS w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uXS (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_XS w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uMPRV (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_MPRV w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uSUM (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_SUM w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uMXR (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_MXR w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uSPELP (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_SPELP w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uUXL (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_UXL w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.
Lemma qTVM_uTVM (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_TVM w x) = x.
Proof. qu_same. Qed.
Lemma qTVM_uMPELP (w : mword 64) x : _get_Mstatus_TVM (_update_Mstatus_MPELP w x) = _get_Mstatus_TVM w.
Proof. qu_disj. Qed.

(* row XS *)
Lemma qXS_uSD (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_SD w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Lemma qXS_uSIE (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_SIE w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Lemma qXS_uMIE (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_MIE w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Lemma qXS_uSPIE (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_SPIE w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Lemma qXS_uMPIE (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_MPIE w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Lemma qXS_uSPP (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_SPP w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Lemma qXS_uMPP (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_MPP w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Lemma qXS_uVS (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_VS w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Lemma qXS_uFS (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_FS w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Lemma qXS_uXS (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_XS w x) = x.
Proof. qu_same. Qed.
Lemma qXS_uMPRV (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_MPRV w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.
Lemma qXS_uMPELP (w : mword 64) x : _get_Mstatus_XS (_update_Mstatus_MPELP w x) = _get_Mstatus_XS w.
Proof. qu_disj. Qed.

(* row FS *)
Lemma qFS_uSD (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_SD w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Lemma qFS_uSIE (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_SIE w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Lemma qFS_uMIE (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_MIE w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Lemma qFS_uSPIE (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_SPIE w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Lemma qFS_uMPIE (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_MPIE w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Lemma qFS_uSPP (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_SPP w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Lemma qFS_uMPP (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_MPP w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Lemma qFS_uVS (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_VS w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Lemma qFS_uFS (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_FS w x) = x.
Proof. qu_same. Qed.
Lemma qFS_uMPRV (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_MPRV w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.
Lemma qFS_uMPELP (w : mword 64) x : _get_Mstatus_FS (_update_Mstatus_MPELP w x) = _get_Mstatus_FS w.
Proof. qu_disj. Qed.

(* row VS *)
Lemma qVS_uSD (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_SD w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Lemma qVS_uSIE (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_SIE w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Lemma qVS_uMIE (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_MIE w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Lemma qVS_uSPIE (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_SPIE w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Lemma qVS_uMPIE (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_MPIE w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Lemma qVS_uSPP (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_SPP w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Lemma qVS_uMPP (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_MPP w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Lemma qVS_uVS (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_VS w x) = x.
Proof. qu_same. Qed.
Lemma qVS_uMPRV (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_MPRV w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.
Lemma qVS_uMPELP (w : mword 64) x : _get_Mstatus_VS (_update_Mstatus_MPELP w x) = _get_Mstatus_VS w.
Proof. qu_disj. Qed.

(* row SD *)
Lemma qSD_uSD (w : mword 64) x : _get_Mstatus_SD (_update_Mstatus_SD w x) = x.
Proof. qu_same. Qed.
Lemma qSD_uMIE (w : mword 64) x : _get_Mstatus_SD (_update_Mstatus_MIE w x) = _get_Mstatus_SD w.
Proof. qu_disj. Qed.
Lemma qSD_uMPIE (w : mword 64) x : _get_Mstatus_SD (_update_Mstatus_MPIE w x) = _get_Mstatus_SD w.
Proof. qu_disj. Qed.
Lemma qSD_uMPP (w : mword 64) x : _get_Mstatus_SD (_update_Mstatus_MPP w x) = _get_Mstatus_SD w.
Proof. qu_disj. Qed.
Lemma qSD_uMPRV (w : mword 64) x : _get_Mstatus_SD (_update_Mstatus_MPRV w x) = _get_Mstatus_SD w.
Proof. qu_disj. Qed.
Lemma qSD_uMPELP (w : mword 64) x : _get_Mstatus_SD (_update_Mstatus_MPELP w x) = _get_Mstatus_SD w.
Proof. qu_disj. Qed.

(* row MPP *)
Lemma qMPP_uSD (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SD w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uSIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SIE w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uMIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MIE w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uSPIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SPIE w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uMPIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MPIE w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uSPP (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SPP w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uVS (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_VS w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uFS (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_FS w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uXS (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_XS w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uSUM (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SUM w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uMXR (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MXR w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uSPELP (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SPELP w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uUXL (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_UXL w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uMPP (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MPP w x) = x.
Proof. qu_same. Qed.
Lemma qMPP_uMPRV (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MPRV w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.
Lemma qMPP_uMPELP (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MPELP w x) = _get_Mstatus_MPP w.
Proof. qu_disj. Qed.

(* row SXL *)
Lemma qSXL_uSD (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SD w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uSIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SIE w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uMIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MIE w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uSPIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SPIE w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uMPIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPIE w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uSPP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SPP w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uMPP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPP w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uVS (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_VS w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uFS (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_FS w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uXS (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_XS w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uMPRV (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPRV w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uSUM (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SUM w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uMXR (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MXR w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uTVM (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_TVM w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uTW (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_TW w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uTSR (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_TSR w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uSPELP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SPELP w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.
Lemma qSXL_uMPELP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPELP w x) = _get_Mstatus_SXL w.
Proof. qu_disj. Qed.

(* rows SPP (bit 8) and SPIE (bit 5).  Only the setters that sit OUTSIDE
   them in [mstatus_legalized] / [lift_sstatus] are needed -- the chains
   stop at the field's own setter -- which is why these two rows are short
   next to MPRV's or SXL's.  Both fields are what an [sret] reads, so the
   trap-handler contract ([projects/kerneltrap.md]) is what wants them. *)
Lemma qSPP_uSD (w : mword 64) x : _get_Mstatus_SPP (_update_Mstatus_SD w x) = _get_Mstatus_SPP w.
Proof. qu_disj. Qed.
Lemma qSPP_uSIE (w : mword 64) x : _get_Mstatus_SPP (_update_Mstatus_SIE w x) = _get_Mstatus_SPP w.
Proof. qu_disj. Qed.
Lemma qSPP_uMIE (w : mword 64) x : _get_Mstatus_SPP (_update_Mstatus_MIE w x) = _get_Mstatus_SPP w.
Proof. qu_disj. Qed.
Lemma qSPP_uSPIE (w : mword 64) x : _get_Mstatus_SPP (_update_Mstatus_SPIE w x) = _get_Mstatus_SPP w.
Proof. qu_disj. Qed.
Lemma qSPP_uMPIE (w : mword 64) x : _get_Mstatus_SPP (_update_Mstatus_MPIE w x) = _get_Mstatus_SPP w.
Proof. qu_disj. Qed.
Lemma qSPP_uSPP (w : mword 64) x : _get_Mstatus_SPP (_update_Mstatus_SPP w x) = x.
Proof. qu_same. Qed.

Lemma qSPIE_uSD (w : mword 64) x : _get_Mstatus_SPIE (_update_Mstatus_SD w x) = _get_Mstatus_SPIE w.
Proof. qu_disj. Qed.
Lemma qSPIE_uSIE (w : mword 64) x : _get_Mstatus_SPIE (_update_Mstatus_SIE w x) = _get_Mstatus_SPIE w.
Proof. qu_disj. Qed.
Lemma qSPIE_uMIE (w : mword 64) x : _get_Mstatus_SPIE (_update_Mstatus_MIE w x) = _get_Mstatus_SPIE w.
Proof. qu_disj. Qed.
Lemma qSPIE_uSPIE (w : mword 64) x : _get_Mstatus_SPIE (_update_Mstatus_SPIE w x) = x.
Proof. qu_same. Qed.

(* ---- L4: fields of [mstatus_legalized o v] ---- *)
Lemma mstatus_legalized_MIE (o v : mword 64) :
  _get_Mstatus_MIE (mstatus_legalized o v) = _get_Mstatus_MIE v.
Proof.
  unfold mstatus_legalized. cbn zeta.
  rewrite qMIE_uSD qMIE_uSIE qMIE_uMIE. reflexivity.
Qed.

Lemma mstatus_legalized_SIE (o v : mword 64) :
  _get_Mstatus_SIE (mstatus_legalized o v) = _get_Mstatus_SIE v.
Proof. unfold mstatus_legalized. cbn zeta. rewrite qSIE_uSD qSIE_uSIE. reflexivity. Qed.

Lemma mstatus_legalized_MPRV (o v : mword 64) :
  _get_Mstatus_MPRV (mstatus_legalized o v) = _get_Mstatus_MPRV v.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qMPRV_uSD qMPRV_uSIE qMPRV_uMIE qMPRV_uSPIE qMPRV_uMPIE qMPRV_uSPP
          qMPRV_uMPP qMPRV_uVS qMPRV_uFS qMPRV_uXS qMPRV_uMPRV. reflexivity. Qed.

Lemma mstatus_legalized_SPP (o v : mword 64) :
  _get_Mstatus_SPP (mstatus_legalized o v) = _get_Mstatus_SPP v.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qSPP_uSD qSPP_uSIE qSPP_uMIE qSPP_uSPIE qSPP_uMPIE qSPP_uSPP.
  reflexivity. Qed.

Lemma mstatus_legalized_SPIE (o v : mword 64) :
  _get_Mstatus_SPIE (mstatus_legalized o v) = _get_Mstatus_SPIE v.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qSPIE_uSD qSPIE_uSIE qSPIE_uMIE qSPIE_uSPIE. reflexivity. Qed.

Lemma mstatus_legalized_SXL (o v : mword 64) :
  _get_Mstatus_SXL (mstatus_legalized o v) = _get_Mstatus_SXL o.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qSXL_uSD qSXL_uSIE qSXL_uMIE qSXL_uSPIE qSXL_uMPIE qSXL_uSPP qSXL_uMPP qSXL_uVS qSXL_uFS qSXL_uXS qSXL_uMPRV qSXL_uSUM qSXL_uMXR qSXL_uTVM qSXL_uTW qSXL_uTSR qSXL_uSPELP qSXL_uMPELP. reflexivity. Qed.

Lemma mstatus_legalized_MXR (o v : mword 64) :
  _get_Mstatus_MXR (mstatus_legalized o v) = _get_Mstatus_MXR v.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qMXR_uSD qMXR_uSIE qMXR_uMIE qMXR_uSPIE qMXR_uMPIE qMXR_uSPP
          qMXR_uMPP qMXR_uVS qMXR_uFS qMXR_uXS qMXR_uMPRV qMXR_uSUM qMXR_uMXR.
  reflexivity. Qed.

Lemma mstatus_legalized_TSR (o v : mword 64) :
  _get_Mstatus_TSR (mstatus_legalized o v) = _get_Mstatus_TSR v.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qTSR_uSD qTSR_uSIE qTSR_uMIE qTSR_uSPIE qTSR_uMPIE qTSR_uSPP
          qTSR_uMPP qTSR_uVS qTSR_uFS qTSR_uXS qTSR_uMPRV qTSR_uSUM qTSR_uMXR
          qTSR_uTVM qTSR_uTW qTSR_uTSR. reflexivity. Qed.

Lemma mstatus_legalized_TVM (o v : mword 64) :
  _get_Mstatus_TVM (mstatus_legalized o v) = _get_Mstatus_TVM v.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qTVM_uSD qTVM_uSIE qTVM_uMIE qTVM_uSPIE qTVM_uMPIE qTVM_uSPP
          qTVM_uMPP qTVM_uVS qTVM_uFS qTVM_uXS qTVM_uMPRV qTVM_uSUM qTVM_uMXR
          qTVM_uTVM. reflexivity. Qed.

Lemma mstatus_legalized_XS (o v : mword 64) :
  _get_Mstatus_XS (mstatus_legalized o v) = extStatus_map_forwards Off.
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qXS_uSD qXS_uSIE qXS_uMIE qXS_uSPIE qXS_uMPIE qXS_uSPP
          qXS_uMPP qXS_uVS qXS_uFS qXS_uXS. reflexivity. Qed.

Lemma mstatus_legalized_FS (o v : mword 64) :
  _get_Mstatus_FS (mstatus_legalized o v)
  = legalize_extStatus plat_mstatus_legal_fs (_get_Mstatus_FS v).
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qFS_uSD qFS_uSIE qFS_uMIE qFS_uSPIE qFS_uMPIE qFS_uSPP
          qFS_uMPP qFS_uVS qFS_uFS. reflexivity. Qed.

Lemma mstatus_legalized_VS (o v : mword 64) :
  _get_Mstatus_VS (mstatus_legalized o v)
  = legalize_extStatus plat_mstatus_legal_vs (_get_Mstatus_VS v).
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qVS_uSD qVS_uSIE qVS_uMIE qVS_uSPIE qVS_uMPIE qVS_uSPP
          qVS_uMPP qVS_uVS. reflexivity. Qed.

Lemma mstatus_legalized_SD (o v : mword 64) :
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

Lemma mstatus_legalized_MPP (o v : mword 64) :
  _get_Mstatus_MPP (mstatus_legalized o v)
  = (if have_nom_val (_get_Mstatus_MPP v)
     then _get_Mstatus_MPP v else privLevel_to_bits User).
Proof. unfold mstatus_legalized. cbn zeta.
  rewrite qMPP_uSD qMPP_uSIE qMPP_uMIE qMPP_uSPIE qMPP_uMPIE qMPP_uSPP qMPP_uMPP.
  reflexivity. Qed.

(* ====================================================================== *)
(* pmpcfg0 written value: collapse the 8 per-byte [pmp_cfg_step]s of         *)
(* [pmpcfg0_final] into ONE [set_reg pmpcfg_n] with a pure vector value,     *)
(* so the WP can express the write as a single points-to update.            *)
(* ====================================================================== *)
Definition pmpcfg_written (v : mword 64) (cfg : type_of_register pmpcfg_n)
    : type_of_register pmpcfg_n :=
  pmpcfg0_vecupd v (pmpcfg0_vecupd v (pmpcfg0_vecupd v (pmpcfg0_vecupd v
    (pmpcfg0_vecupd v (pmpcfg0_vecupd v (pmpcfg0_vecupd v (pmpcfg0_vecupd v
      cfg 0) 1) 2) 3) 4) 5) 6) 7.

Lemma pmpcfg0_final_set (v : mword 64) (s : mstate) :
  pmpcfg0_final v s
  = set_reg s pmpcfg_n (pmpcfg_written v (register_lookup pmpcfg_n s.(sregs))).
Proof.
  unfold pmpcfg0_final, pmpcfg_written.
  assert (H0 : pmp_cfg_step v s 0
               = set_reg s pmpcfg_n
                   (pmpcfg0_vecupd v (register_lookup pmpcfg_n s.(sregs)) 0))
    by reflexivity.
  rewrite H0.
  rewrite !pmp_cfg_step_on_set. reflexivity.
Qed.

(* ====================================================================== *)
(* The two config-writing csrw WPs, on [wp_instr_config].                    *)
(* ====================================================================== *)
Section WpCsrwGprNewC.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- csrw mstatus (0x300): the continuation receives the RAW UNBUNDLED
     cells with the EXPLICIT legalized mstatus value, universally quantified
     over the (hidden) old mstatus [ms_old] together with its SXL invariant
     fact. A chain rebuilds [mmode_config (DfracOwn 1)] via
     [mmode_config_rebuild]: the MIE / MPRV facts on the new value come from
     [mstatus_legalized_MIE] / [mstatus_legalized_MPRV], which depend ONLY on
     the written value (which the chain knows concretely) -- so unlike SXL
     (preserved unconditionally from [ms_old] by the legalizer, hence still
     needing the old invariant fact here), no old-value MIE/MPRV fact is
     threaded through. ---- *)

  (* ---- csrw pmpcfg0 (0x3a0): writes the pmpcfg_n vector cell.  The fetch of
     THIS instruction happens under the OLD pmpcfg (premise [pmp_allows_all
     pmpcfg0] as usual); the continuation receives the NEW concrete value --
     the chain proves [pmp_allows_all (pmpcfg_written ...)] separately for the
     instructions that follow.  mstatus is unchanged, so the continuation gets
     an opaque REBUILT [mmode_config (DfracOwn 1)]. ---- *)

  (* ---- RAW variant of the csrw-mstatus WP: the caller supplies the config
     cells UNBUNDLED with the mstatus VALUE [ms0] explicit (a chain that
     unbundled its [mmode_config (DfracOwn 1)] at the top and has been
     pinning [ms0] with an outside fraction ever since).  The continuation
     receives the same raw cells with mstatus at the EXPLICIT legalized
     value -- no re-quantification over a hidden old value, so the chain
     keeps a single mstatus symbol end-to-end. ---- *)
  Lemma wp_csrw_mstatus_raw (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (ms0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Machine -∗
      mstatus ↦ᵣ mstatus_legalized ms0 (m !!! Regidx rs1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat HmIE) "#Hhw #Hinv Hhs Hpriv0 Hms0 Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_config pc false (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW))
              pmpcfg0 ms0 Hpmp HmIE Hstat
              with "Hhw Hinv Hhs Hpriv0 Hms0 Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hpriv Hms Hpmpc Hsi".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    assert (Hm1 : rf_to_gmap m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmisap : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    iMod (reg_update _ mstatus _ (mstatus_legalized ms0 (m !!! Regidx rs1))
            with "Hreg Hms") as "[Hreg Hms]".
    iModIntro.
    iExists (set_reg s_pc mstatus (mstatus_legalized ms0 (m !!! Regidx rs1))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_mstatus (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_mstatus rs1 s_pc Lprivp
                 ltac:(rewrite Lmisap; exact HmisaS)
                 ltac:(rewrite Lmisap; exact HmisaU)).
      rewrite Lmsp Lrs1u. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc mstatus (mstatus_legalized ms0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs Hpriv Hms Hpmpc [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- RAW variant of the csrw-pmpcfg0 WP: unbundled config cells with the
     mstatus VALUE [ms0] explicit and RETURNED UNCHANGED (the write does not
     touch mstatus), so a chain that pins the value across the write keeps
     it without a fresh existential.  pmpcfg_n itself is FULL (it is the
     written cell); the continuation receives the concrete written value. ---- *)
  Lemma wp_csrw_pmpcfg0_raw (pc : mword 64) (rs1 : mword 5)
      (m : regfile) (ms0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    pmp_allows_all pmpcfg0 ->
    (forall j, (j < 4)%nat -> KptPt.kmap_static (svpn_of (RiscvModelBytes.pa_add pc j)) KP_rx) ->
    eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Machine -∗
    mstatus ↦ᵣ ms0 -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW)) -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Machine -∗
      mstatus ↦ᵣ ms0 -∗
      pmpcfg_n ↦ᵣ pmpcfg_written (m !!! Regidx rs1) pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hpmp Hstat HmIE) "#Hhw #Hinv Hhs Hpriv0 Hms0 Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_config pc false (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW))
              pmpcfg0 ms0 Hpmp HmIE Hstat
              with "Hhw Hinv Hhs Hpriv0 Hms0 Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hpriv Hms Hpmpc Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hpmpc") as %Lcfg.
    assert (Hm1 : rf_to_gmap m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (rewrite rf_lookup; apply rf_to_gmap_lookup).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1u.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lcfgp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lcfg).
    iMod (reg_update _ pmpcfg_n _ (pmpcfg_written (m !!! Regidx rs1) pmpcfg0)
            with "Hreg Hpmpc") as "[Hreg Hpmpc]".
    iModIntro.
    iExists (set_reg s_pc pmpcfg_n (pmpcfg_written (m !!! Regidx rs1) pmpcfg0)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW)))
        with (execute_CSRReg csr_pmpcfg0 (Regidx rs1) zreg CSRRW).
      rewrite (exec_execute_csrw_pmpcfg0 rs1 s_pc Lprivp).
      rewrite Lrs1u pmpcfg0_final_set Lcfgp. reflexivity. }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc pmpcfg_n (pmpcfg_written (m !!! Regidx rs1) pmpcfg0)).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs Hpriv Hms Hpmpc [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpCsrwGprNewC.

(* ====================================================================== *)
(* CHAIN-FACING PMP FACTS: the boot [csrw pmpcfg0, a5] with a5 = 0xf keeps *)
(* [pmp_allows_all] (all entries UNLOCKED).  Entry 0 legalizes to byte     *)
(* 0x0f (A=TOR, RWX=111, L=0), entries 1..7 to 0x00, entries 8..63 keep    *)
(* their old (unlocked, by the premise) byte -- so the WRITTEN config is    *)
(* unlocked again and the instructions AFTER the write keep discharging    *)
(* their fetch-side [pmp_allows_all] premise.                              *)
(* ====================================================================== *)

(* list_update at a valid index is stdpp's insert. *)
Lemma list_update_insert {A} (xs : list A) (k : nat) (x : A) :
  (k < length xs)%nat -> list_update xs k x = <[k := x]> xs.
Proof. intros Hk. symmetry. apply insert_take_drop. exact Hk. Qed.

(* vec_access_dec over vec_update_dec, at ANY index j (including the
   out-of-range ones, where both sides read the same dummy). *)
Lemma pmpcfg_access_update (v : type_of_register pmpcfg_n) (m j : Z) (t : mword 8) :
  0 <= m < 64 ->
  vec_access_dec (vec_update_dec v m t) j
  = (if Z.eqb j m then t else vec_access_dec v j).
Proof.
  intros Hm. destruct v as [xs Hlen].
  assert (Hl : length xs = 64%nat) by (rewrite Hlen; reflexivity).
  unfold vec_update_dec.
  destruct (sumbool_of_bool (0 <=? m <? 64)) as [He|He].
  2:{ exfalso.
      assert (Ht : ((0 <=? m) && (m <? 64))%bool = true)
        by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      rewrite Ht in He. discriminate He. }
  unfold vec_access_dec. cbn [projT1].
  unfold update_list_dec, update_list_inc, access_list_dec, access_list_inc, length_list.
  rewrite !Hl.
  change (Z.of_nat 64 - 1) with 63.
  set (k := Z.to_nat (63 - m)).
  assert (Hk : (k < length xs)%nat) by (unfold k; rewrite Hl; lia).
  rewrite (list_update_insert xs k t Hk).
  rewrite length_insert. rewrite Hl.
  change (Z.of_nat 64 - 1) with 63.
  destruct (Z.ltb (63 - j) 0) eqn:Hg.
  - (* out of range below: both dummy; j > 63 > m *)
    apply Z.ltb_lt in Hg.
    replace (Z.eqb j m) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity.
  - apply Z.ltb_ge in Hg.
    destruct (Z.eqb j m) eqn:Hjm.
    + apply Z.eqb_eq in Hjm. subst j.
      rewrite nth_lookup.
      replace (Z.to_nat (63 - m)) with k by reflexivity.
      rewrite (list_lookup_insert xs k t Hk). reflexivity.
    + apply Z.eqb_neq in Hjm.
      rewrite nth_lookup.
      rewrite list_lookup_insert_ne.
      2:{ unfold k. lia. }
      rewrite <- nth_lookup. reflexivity.
Qed.

(* One legalized-byte write preserves all-unlocked, provided the NEW byte is
   itself unlocked. *)
Lemma pmpcfg0_vecupd_unlocked (v : mword 64) (cfg : type_of_register pmpcfg_n) (i : Z) :
  0 <= i < 8 ->
  (forall j, pmpLocked (vec_access_dec cfg j) = false) ->
  pmpLocked (pmpWriteCfg_val (vec_access_dec cfg (Z.add (Z.mul 0 4) i))
               (autocast (T := mword) (subrange_vec_dec v (Z.add (Z.mul 8 i) 7) (Z.mul 8 i))))
    = false ->
  forall j, pmpLocked (vec_access_dec (pmpcfg0_vecupd v cfg i) j) = false.
Proof.
  intros Hi Hunl Hnew j.
  unfold pmpcfg0_vecupd.
  assert (Hrng : 0 <= Z.add (Z.mul 0 4) i < 64) by lia.
  rewrite (pmpcfg_access_update cfg (Z.add (Z.mul 0 4) i) j _ Hrng).
  destruct (Z.eqb j (Z.add (Z.mul 0 4) i)); [exact Hnew | apply Hunl].
Qed.

(* THE preservation lemma: the concrete xv6 write (v = 15) keeps every
   entry unlocked.  Each of the eight written bytes legalizes -- from an
   unlocked old byte -- to a CONSTANT with L = 0 (0x0f for byte 0, 0x00 for
   bytes 1..7), so after rewriting the old byte's unlockedness the per-byte
   goal closes by vm_compute. *)
Lemma pmp_allows_all_written (cfg : type_of_register pmpcfg_n) :
  pmp_allows_all cfg ->
  pmp_allows_all (pmpcfg_written (mword_of_int 15) cfg).
Proof.
  intros Hunl. unfold pmp_allows_all in *. unfold pmpcfg_written.
  assert (S0 : forall j,
      pmpLocked (vec_access_dec (pmpcfg0_vecupd (mword_of_int 15) cfg 0) j) = false).
  { apply pmpcfg0_vecupd_unlocked; [lia | exact Hunl |].
    unfold pmpWriteCfg_val. rewrite (Hunl (Z.add (Z.mul 0 4) 0)).
    vm_compute. reflexivity. }
  assert (S1 : forall j,
      pmpLocked (vec_access_dec (pmpcfg0_vecupd (mword_of_int 15)
        (pmpcfg0_vecupd (mword_of_int 15) cfg 0) 1) j) = false).
  { apply pmpcfg0_vecupd_unlocked; [lia | exact S0 |].
    unfold pmpWriteCfg_val. rewrite (S0 (Z.add (Z.mul 0 4) 1)).
    vm_compute. reflexivity. }
  assert (S2 : forall j,
      pmpLocked (vec_access_dec (pmpcfg0_vecupd (mword_of_int 15)
        (pmpcfg0_vecupd (mword_of_int 15)
          (pmpcfg0_vecupd (mword_of_int 15) cfg 0) 1) 2) j) = false).
  { apply pmpcfg0_vecupd_unlocked; [lia | exact S1 |].
    unfold pmpWriteCfg_val. rewrite (S1 (Z.add (Z.mul 0 4) 2)).
    vm_compute. reflexivity. }
  assert (S3 : forall j,
      pmpLocked (vec_access_dec (pmpcfg0_vecupd (mword_of_int 15)
        (pmpcfg0_vecupd (mword_of_int 15)
          (pmpcfg0_vecupd (mword_of_int 15)
            (pmpcfg0_vecupd (mword_of_int 15) cfg 0) 1) 2) 3) j) = false).
  { apply pmpcfg0_vecupd_unlocked; [lia | exact S2 |].
    unfold pmpWriteCfg_val. rewrite (S2 (Z.add (Z.mul 0 4) 3)).
    vm_compute. reflexivity. }
  assert (S4 : forall j,
      pmpLocked (vec_access_dec (pmpcfg0_vecupd (mword_of_int 15)
        (pmpcfg0_vecupd (mword_of_int 15)
          (pmpcfg0_vecupd (mword_of_int 15)
            (pmpcfg0_vecupd (mword_of_int 15)
              (pmpcfg0_vecupd (mword_of_int 15) cfg 0) 1) 2) 3) 4) j) = false).
  { apply pmpcfg0_vecupd_unlocked; [lia | exact S3 |].
    unfold pmpWriteCfg_val. rewrite (S3 (Z.add (Z.mul 0 4) 4)).
    vm_compute. reflexivity. }
  assert (S5 : forall j,
      pmpLocked (vec_access_dec (pmpcfg0_vecupd (mword_of_int 15)
        (pmpcfg0_vecupd (mword_of_int 15)
          (pmpcfg0_vecupd (mword_of_int 15)
            (pmpcfg0_vecupd (mword_of_int 15)
              (pmpcfg0_vecupd (mword_of_int 15)
                (pmpcfg0_vecupd (mword_of_int 15) cfg 0) 1) 2) 3) 4) 5) j) = false).
  { apply pmpcfg0_vecupd_unlocked; [lia | exact S4 |].
    unfold pmpWriteCfg_val. rewrite (S4 (Z.add (Z.mul 0 4) 5)).
    vm_compute. reflexivity. }
  assert (S6 : forall j,
      pmpLocked (vec_access_dec (pmpcfg0_vecupd (mword_of_int 15)
        (pmpcfg0_vecupd (mword_of_int 15)
          (pmpcfg0_vecupd (mword_of_int 15)
            (pmpcfg0_vecupd (mword_of_int 15)
              (pmpcfg0_vecupd (mword_of_int 15)
                (pmpcfg0_vecupd (mword_of_int 15)
                  (pmpcfg0_vecupd (mword_of_int 15) cfg 0) 1) 2) 3) 4) 5) 6) j) = false).
  { apply pmpcfg0_vecupd_unlocked; [lia | exact S5 |].
    unfold pmpWriteCfg_val. rewrite (S5 (Z.add (Z.mul 0 4) 6)).
    vm_compute. reflexivity. }
  apply pmpcfg0_vecupd_unlocked; [lia | exact S6 |].
  unfold pmpWriteCfg_val. rewrite (S6 (Z.add (Z.mul 0 4) 7)).
  vm_compute. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Sanity: the boot all-zero pmpcfg is [pmp_all_off] (hence unlocked), and *)
(* the xv6 write on top of it stays [pmp_allows_all].                       *)





(* ====================================================================== *)
(* Idempotence of the S-mode SIE-clear (csrrci sstatus,2) on a well-formed *)
(* kernel mstatus: [legalize_sstatus_val m (sstatus_write_val m 2) = m].    *)
(* Proved WITHOUT axioms by reducing every mstatus/sstatus field op to the  *)
(* [MachineWord] bv layer.  Three phases: (1) the written S-view value      *)
(* equals [lower_mstatus m] (clearing an already-0 SIE bit is the identity);*)
(* (2) [lift_sstatus m (lower_mstatus m) = m] (each S-field round-trips to   *)
(* its M-position; SD stays 0 as FS/VS/XS = Off); (3) [mstatus_legalized m m *)
(* = m] (FS/VS legalize FourState = id, XS forced Off = XS m, MPP nominal).  *)
(* NB: this file uses ssreflect [rewrite] (via proofmode), hence no [by]     *)
(* clauses / comma lists -- side goals are discharged with [; [| tac]].      *)
(* ====================================================================== *)

(* set-a-field-to-its-current-value is the identity, at the bv layer *)
Lemma bv_update_slice_extract_id (m n : N) (w : bv m) (i : N) :
  (i + n <= m)%N ->
  MachineWord.MachineWord.update_slice (n:=n) w i (bv_extract i n w) = w.
Proof.
  intros Hlim.
  unfold MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
  apply bv_eq.
  pose proof (bv_unsigned_in_range _ w) as [Hw0 Hwhi].
  rewrite !bv_concat_unsigned'.
  rewrite !bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  apply Z.bits_inj'. intros j Hj.
  destruct (decide (j < Z.of_N m)) as [Hjm|Hjm].
  2:{ rewrite (Z.mod_pow2_bits_high _ (Z.of_N m)); [|lia]. symmetry.
      destruct (decide (bv_unsigned w = 0)) as [Hz|Hnz].
      - rewrite Hz. apply Z.bits_0.
      - apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2 in Hwhi; lia. }
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N m)); [|lia].
  rewrite !Z.lor_spec.
  destruct (decide (j < Z.of_N (i + n))) as [Hlo|Hhi].
  - rewrite (Z.shiftl_spec_low _ (Z.of_N (i+n))); [|lia].
    rewrite orb_false_l.
    rewrite (Z.mod_pow2_bits_low _ (Z.of_N (i+n))); [|lia].
    rewrite Z.lor_spec.
    destruct (decide (j < Z.of_N i)) as [Hji|Hji].
    + rewrite (Z.shiftl_spec_low _ (Z.of_N i)); [|lia].
      rewrite orb_false_l.
      rewrite Z.shiftr_0_r.
      rewrite (Z.mod_pow2_bits_low _ (Z.of_N i)); [|lia].
      reflexivity.
    + rewrite (Z.mod_pow2_bits_high _ (Z.of_N i)); [|lia].
      rewrite orb_false_r.
      rewrite (Z.shiftl_spec _ (Z.of_N i)); [|lia].
      rewrite (Z.mod_pow2_bits_low _ (Z.of_N n)); [|lia].
      rewrite (Z.shiftr_spec _ (Z.of_N i)); [|lia].
      f_equal. lia.
  - rewrite (Z.mod_pow2_bits_high _ (Z.of_N (i+n))); [|lia].
    rewrite orb_false_r.
    rewrite (Z.shiftl_spec _ (Z.of_N (i+n))); [|lia].
    rewrite (Z.mod_pow2_bits_low _ (Z.of_N (m - n - i))); [|lia].
    rewrite (Z.shiftr_spec _ (Z.of_N (i+n))); [|lia].
    f_equal. lia.
Qed.

Ltac us_id_tac :=
  unfold subrange_vec_dec, update_subrange_vec_dec;
  rewrite !autocast_refl;
  unfold to_word_idx, to_word, get_word;
  rewrite !MachineWord.MachineWord.cast_idx_refl;
  unfold MachineWord.MachineWord.slice;
  match goal with
  | |- @MachineWord.MachineWord.update_slice ?m ?n ?w ?i (@bv_extract ?m2 ?s ?l ?b) = _ =>
      change l with n; change s with i
  end;
  apply bv_update_slice_extract_id; apply N.leb_le; reflexivity.

(* [_update_Mstatus_X w (_get_Mstatus_X w) = w] for every field the legalizer/
   lifter touch. *)
Lemma uSIE_id (w : mword 64) : _update_Mstatus_SIE w (_get_Mstatus_SIE w) = w.
Proof. unfold _update_Mstatus_SIE, _get_Mstatus_SIE. us_id_tac. Qed.
Lemma uMIE_id (w : mword 64) : _update_Mstatus_MIE w (_get_Mstatus_MIE w) = w.
Proof. unfold _update_Mstatus_MIE, _get_Mstatus_MIE. us_id_tac. Qed.
Lemma uSPIE_id (w : mword 64) : _update_Mstatus_SPIE w (_get_Mstatus_SPIE w) = w.
Proof. unfold _update_Mstatus_SPIE, _get_Mstatus_SPIE. us_id_tac. Qed.
Lemma uMPIE_id (w : mword 64) : _update_Mstatus_MPIE w (_get_Mstatus_MPIE w) = w.
Proof. unfold _update_Mstatus_MPIE, _get_Mstatus_MPIE. us_id_tac. Qed.
Lemma uSPP_id (w : mword 64) : _update_Mstatus_SPP w (_get_Mstatus_SPP w) = w.
Proof. unfold _update_Mstatus_SPP, _get_Mstatus_SPP. us_id_tac. Qed.
Lemma uMPP_id (w : mword 64) : _update_Mstatus_MPP w (_get_Mstatus_MPP w) = w.
Proof. unfold _update_Mstatus_MPP, _get_Mstatus_MPP. us_id_tac. Qed.
Lemma uVS_id (w : mword 64) : _update_Mstatus_VS w (_get_Mstatus_VS w) = w.
Proof. unfold _update_Mstatus_VS, _get_Mstatus_VS. us_id_tac. Qed.
Lemma uFS_id (w : mword 64) : _update_Mstatus_FS w (_get_Mstatus_FS w) = w.
Proof. unfold _update_Mstatus_FS, _get_Mstatus_FS. us_id_tac. Qed.
Lemma uXS_id (w : mword 64) : _update_Mstatus_XS w (_get_Mstatus_XS w) = w.
Proof. unfold _update_Mstatus_XS, _get_Mstatus_XS. us_id_tac. Qed.
Lemma uMPRV_id (w : mword 64) : _update_Mstatus_MPRV w (_get_Mstatus_MPRV w) = w.
Proof. unfold _update_Mstatus_MPRV, _get_Mstatus_MPRV. us_id_tac. Qed.
Lemma uSUM_id (w : mword 64) : _update_Mstatus_SUM w (_get_Mstatus_SUM w) = w.
Proof. unfold _update_Mstatus_SUM, _get_Mstatus_SUM. us_id_tac. Qed.
Lemma uMXR_id (w : mword 64) : _update_Mstatus_MXR w (_get_Mstatus_MXR w) = w.
Proof. unfold _update_Mstatus_MXR, _get_Mstatus_MXR. us_id_tac. Qed.
Lemma uTVM_id (w : mword 64) : _update_Mstatus_TVM w (_get_Mstatus_TVM w) = w.
Proof. unfold _update_Mstatus_TVM, _get_Mstatus_TVM. us_id_tac. Qed.
Lemma uTW_id (w : mword 64) : _update_Mstatus_TW w (_get_Mstatus_TW w) = w.
Proof. unfold _update_Mstatus_TW, _get_Mstatus_TW. us_id_tac. Qed.
Lemma uTSR_id (w : mword 64) : _update_Mstatus_TSR w (_get_Mstatus_TSR w) = w.
Proof. unfold _update_Mstatus_TSR, _get_Mstatus_TSR. us_id_tac. Qed.
Lemma uSPELP_id (w : mword 64) : _update_Mstatus_SPELP w (_get_Mstatus_SPELP w) = w.
Proof. unfold _update_Mstatus_SPELP, _get_Mstatus_SPELP. us_id_tac. Qed.
Lemma uMPELP_id (w : mword 64) : _update_Mstatus_MPELP w (_get_Mstatus_MPELP w) = w.
Proof. unfold _update_Mstatus_MPELP, _get_Mstatus_MPELP. us_id_tac. Qed.
Lemma uUXL_id (w : mword 64) : _update_Mstatus_UXL w (_get_Mstatus_UXL w) = w.
Proof. unfold _update_Mstatus_UXL, _get_Mstatus_UXL. us_id_tac. Qed.
Lemma uSD_id (w : mword 64) : _update_Mstatus_SD w (_get_Mstatus_SD w) = w.
Proof. unfold _update_Mstatus_SD, _get_Mstatus_SD. us_id_tac. Qed.

(* ---- general reduction of Mstatus/Sstatus field ops to the bv layer ---- *)
Ltac to_bv :=
  unfold Mk_Mstatus, Mk_Sstatus,
    _get_Mstatus_SIE, _get_Mstatus_MIE, _get_Mstatus_SPIE, _get_Mstatus_MPIE,
    _get_Mstatus_SPP, _get_Mstatus_MPP, _get_Mstatus_VS, _get_Mstatus_FS,
    _get_Mstatus_XS, _get_Mstatus_MPRV, _get_Mstatus_SUM, _get_Mstatus_MXR,
    _get_Mstatus_TVM, _get_Mstatus_TW, _get_Mstatus_TSR, _get_Mstatus_SPELP,
    _get_Mstatus_MPELP, _get_Mstatus_SD, _get_Mstatus_UXL, _get_Mstatus_SXL,
    _update_Mstatus_SIE, _update_Mstatus_MIE, _update_Mstatus_SPIE,
    _update_Mstatus_MPIE, _update_Mstatus_SPP, _update_Mstatus_MPP,
    _update_Mstatus_VS, _update_Mstatus_FS, _update_Mstatus_XS,
    _update_Mstatus_MPRV, _update_Mstatus_SUM, _update_Mstatus_MXR,
    _update_Mstatus_TVM, _update_Mstatus_TW, _update_Mstatus_TSR,
    _update_Mstatus_SPELP, _update_Mstatus_MPELP, _update_Mstatus_SD,
    _get_Sstatus_SIE, _get_Sstatus_SPIE, _get_Sstatus_SPP, _get_Sstatus_VS,
    _get_Sstatus_FS, _get_Sstatus_XS, _get_Sstatus_SUM, _get_Sstatus_MXR,
    _get_Sstatus_SPELP, _get_Sstatus_UXL, _get_Sstatus_SD,
    _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP,
    _update_Sstatus_VS, _update_Sstatus_FS, _update_Sstatus_XS,
    _update_Sstatus_SUM, _update_Sstatus_MXR, _update_Sstatus_SPELP,
    _update_Sstatus_UXL, _update_Sstatus_SD;
  unfold subrange_vec_dec, update_subrange_vec_dec;
  rewrite ?autocast_refl;
  unfold to_word_idx, to_word, get_word;
  rewrite ?MachineWord.MachineWord.cast_idx_refl;
  unfold MachineWord.MachineWord.slice.

Ltac provN := apply N.leb_le; reflexivity.
Ltac provDisj := first [ (apply or_introl; provN) | (apply or_intror; provN) | (provN) ].

(* disjoint FIRST: at each layer [disjoint] peels immediately, so the
   (search-heavy, under ssr) [same] rewrite is attempted only once, at the
   target layer.  Putting [same] first makes ssr run an expensive failing
   match on every iteration -- quadratic, pathologically slow here. *)
Ltac bvcrush :=
  repeat first
    [ (rewrite bv_extract_update_slice_disjoint; [| provDisj | provDisj])
    | (rewrite bv_extract_update_slice_same; [| provDisj]) ].

(* [_get_Sstatus_Y (lower_mstatus m) = _get_Mstatus_Y m]: lower places each
   S-field at the SAME bit position it reads from m. *)
Lemma sSIE_lower (m : mword 64) : _get_Sstatus_SIE (lower_mstatus m) = _get_Mstatus_SIE m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.
Lemma sSPIE_lower (m : mword 64) : _get_Sstatus_SPIE (lower_mstatus m) = _get_Mstatus_SPIE m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.
Lemma sSPP_lower (m : mword 64) : _get_Sstatus_SPP (lower_mstatus m) = _get_Mstatus_SPP m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.
Lemma sVS_lower (m : mword 64) : _get_Sstatus_VS (lower_mstatus m) = _get_Mstatus_VS m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.
Lemma sFS_lower (m : mword 64) : _get_Sstatus_FS (lower_mstatus m) = _get_Mstatus_FS m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.
Lemma sXS_lower (m : mword 64) : _get_Sstatus_XS (lower_mstatus m) = _get_Mstatus_XS m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.
Lemma sSUM_lower (m : mword 64) : _get_Sstatus_SUM (lower_mstatus m) = _get_Mstatus_SUM m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.
Lemma sMXR_lower (m : mword 64) : _get_Sstatus_MXR (lower_mstatus m) = _get_Mstatus_MXR m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.
Lemma sSPELP_lower (m : mword 64) : _get_Sstatus_SPELP (lower_mstatus m) = _get_Mstatus_SPELP m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.
Lemma sUXL_lower (m : mword 64) : _get_Sstatus_UXL (lower_mstatus m) = _get_Mstatus_UXL m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.
Lemma mSIE_lower (m : mword 64) : _get_Mstatus_SIE (lower_mstatus m) = _get_Mstatus_SIE m.
Proof. unfold lower_mstatus. to_bv. bvcrush. reflexivity. Qed.

(* Phase 3: legalizing an mstatus that is already legal is the identity. *)
Lemma mstatus_legalized_self (m : mword 64)
  (HXS : _get_Mstatus_XS m = extStatus_map_forwards Off)
  (HFS : _get_Mstatus_FS m = extStatus_map_forwards Off)
  (HVS : _get_Mstatus_VS m = extStatus_map_forwards Off)
  (HSD : _get_Mstatus_SD m = 'b"0")
  (HMPP : have_nom_val (_get_Mstatus_MPP m) = true) :
  mstatus_legalized m m = m.
Proof.
  unfold mstatus_legalized. cbv zeta. unfold Mk_Mstatus.
  rewrite HMPP. cbn match.
  unfold plat_mstatus_legal_fs, plat_mstatus_legal_vs.
  cbn [legalize_extStatus].
  rewrite <- HXS.
  rewrite uMPELP_id uSPELP_id uTSR_id uTW_id uTVM_id uMXR_id uSUM_id
          uMPRV_id uXS_id uFS_id uVS_id uMPP_id uSPP_id uMPIE_id
          uSPIE_id uMIE_id uSIE_id.
  rewrite HFS HXS HVS.
  match goal with |- _update_Mstatus_SD m ?d = m =>
    assert (Hd : d = _get_Mstatus_SD m) by (rewrite HSD; vm_compute; reflexivity)
  end.
  rewrite Hd. apply uSD_id.
Qed.

(* Phase 2: lifting the S-view of m back into m is the identity. *)
Lemma lift_lower_self (m : mword 64)
  (HXS : _get_Mstatus_XS m = extStatus_map_forwards Off)
  (HFS : _get_Mstatus_FS m = extStatus_map_forwards Off)
  (HVS : _get_Mstatus_VS m = extStatus_map_forwards Off)
  (HSD : _get_Mstatus_SD m = 'b"0") :
  lift_sstatus m (lower_mstatus m) = m.
Proof.
  unfold lift_sstatus. cbv zeta.
  rewrite sSIE_lower sSPIE_lower sSPP_lower sVS_lower sFS_lower sXS_lower
          sSUM_lower sMXR_lower sSPELP_lower sUXL_lower.
  match goal with |- context [_update_Mstatus_SD m ?d] =>
    assert (Hd : d = _get_Mstatus_SD m)
      by (rewrite HFS HXS HVS HSD; vm_compute; reflexivity)
  end.
  rewrite Hd.
  rewrite uSD_id uUXL_id uSPELP_id uMXR_id uSUM_id uXS_id uFS_id uVS_id
          uSPP_id uSPIE_id uSIE_id.
  reflexivity.
Qed.

(* zero-extend of a full-width word is the identity *)
Lemma zext64_id (w : mword 64) : zero_extend' 64 w = w.
Proof.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       to_word get_word MachineWord.MachineWord.zero_extend].
  apply bv_zero_extend_idemp.
Qed.

(* full-width subrange is the identity *)
Lemma subrange_full (w : mword 64) : subrange_vec_dec w (Z.sub xlen 1) 0 = w.
Proof.
  unfold subrange_vec_dec.
  rewrite autocast_refl. unfold to_word_idx, to_word, get_word.
  rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice.
  apply bv_eq. rewrite bv_extract_unsigned. rewrite Z.shiftr_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma and_vec_unsigned (a b : mword 64) :
  bv_unsigned (and_vec a b) = Z.land (bv_unsigned a) (bv_unsigned b).
Proof.
  cbv [and_vec Operators_mwords.word_binop Operators_mwords.with_word'
       SailStdpp.Values.with_word to_word get_word].
  unfold MachineWord.MachineWord.and. apply bv_and_unsigned.
Qed.

(* ==================================================================== *)
(*  FIELDS OF A MASKED WORD.                                             *)
(*                                                                      *)
(*  [bvcrush] above extracts a field out of a nest of [update_slice]es,  *)
(*  which is what the mstatus/sstatus GETTERS need.  This block is its   *)
(*  counterpart for the other shape a kernel produces: a word built by   *)
(*  an [andi]/[ori] read-modify-write, whose fields have to be read      *)
(*  through the mask.  prepare_return's                                  *)
(*                                                                      *)
(*      x = r_sstatus(); x &= ~SSTATUS_SPP; x |= SSTATUS_SPIE;           *)
(*                                                                      *)
(*  is the case that forced them, and the reason to reason FIELD-WISE    *)
(*  rather than prove the whole-word identity [sstatus_read ms0 = x] is  *)
(*  that the field route needs no [update_slice] algebra at all: slicing  *)
(*  DISTRIBUTES over the bitwise ops, and each mask's own slice is a     *)
(*  closed computation.                                                  *)
(* ==================================================================== *)

(* [bv_wrap] is masking with [Z.ones] (stdpp's [bv_wrap_land]), so it
   commutes with both bitwise ops. *)
Lemma bv_wrap_land_distr (l : N) (x y : Z) :
  bv_wrap l (Z.land x y) = Z.land (bv_wrap l x) (bv_wrap l y).
Proof.
  rewrite !bv_wrap_land -!Z.land_assoc. f_equal.
  rewrite (Z.land_comm y) Z.land_assoc Z.land_diag. reflexivity.
Qed.

Lemma bv_wrap_lor_distr (l : N) (x y : Z) :
  bv_wrap l (Z.lor x y) = Z.lor (bv_wrap l x) (bv_wrap l y).
Proof. rewrite !bv_wrap_land. apply Z.land_lor_distr_l. Qed.

(* ...hence a FIELD of a combination is the combination of the fields *)
Lemma bv_extract_and (n i l : N) (a b : bv n) :
  bv_extract i l (bv_and a b) = bv_and (bv_extract i l a) (bv_extract i l b).
Proof.
  apply bv_eq. rewrite bv_and_unsigned !bv_extract_unsigned bv_and_unsigned.
  rewrite Z.shiftr_land. apply bv_wrap_land_distr.
Qed.

Lemma bv_extract_or (n i l : N) (a b : bv n) :
  bv_extract i l (bv_or a b) = bv_or (bv_extract i l a) (bv_extract i l b).
Proof.
  apply bv_eq. rewrite bv_or_unsigned !bv_extract_unsigned bv_or_unsigned.
  rewrite Z.shiftr_lor. apply bv_wrap_lor_distr.
Qed.

(* THE THREE ABSORPTIONS, and the reason they are stated on the operand's
   VALUE rather than as [b2 = zeros] / [b2 = ones]: at every use site the
   operand is a mask's own slice, so the side condition is a CLOSED
   computation and discharges by [vm_compute] without the caller having to
   name the slice's syntactic form.  (stdpp supplies [bv_or_0_r] in this
   same style; these are the three it lacks.) *)
Lemma bv_and_0_r (n : N) (b1 b2 : bv n) :
  bv_unsigned b2 = 0 -> bv_and b1 b2 = b2.
Proof. intro Hb. apply bv_eq. rewrite bv_and_unsigned Hb. apply Z.land_0_r. Qed.

Lemma bv_and_ones_r (n : N) (b1 b2 : bv n) :
  bv_unsigned b2 = Z.ones (Z.of_N n) -> bv_and b1 b2 = b1.
Proof.
  intro Hb. apply bv_eq. rewrite bv_and_unsigned Hb.
  rewrite Z.land_ones; [| lia].
  pose proof (bv_unsigned_in_range _ b1) as [Hlo Hhi].
  apply Z.mod_small. unfold bv_modulus in Hhi. lia.
Qed.

Lemma bv_or_ones_r (n : N) (b1 b2 : bv n) :
  bv_unsigned b2 = Z.ones (Z.of_N n) -> bv_or b1 b2 = b2.
Proof.
  intro Hb. apply bv_eq. rewrite bv_or_unsigned Hb.
  apply Z.bits_inj'. intros j Hj.
  rewrite Z.lor_spec. rewrite !Z.testbit_ones_nonneg; try lia.
  destruct (Z.ltb j (Z.of_N n)) eqn:E.
  - rewrite orb_true_r. reflexivity.
  - rewrite orb_false_r.
    pose proof (bv_unsigned_in_range _ b1) as [Hlo Hhi].
    unfold bv_modulus in Hhi. apply Z.ltb_ge in E.
    destruct (decide (bv_unsigned b1 = 0)) as [Hz|Hnz].
    + rewrite Hz. apply Z.bits_0.
    + apply Z.bits_above_log2; [lia|].
      apply Z.log2_lt_pow2 in Hhi; lia.
Qed.

(* SIE lives in bit 1 *)
Lemma sie_bit (m : mword 64) :
  _get_Mstatus_SIE m = 'b"0" -> Z.testbit (bv_unsigned m) 1 = false.
Proof.
  intro HS.
  apply (f_equal bv_unsigned) in HS.
  unfold _get_Mstatus_SIE, subrange_vec_dec in HS.
  rewrite autocast_refl in HS.
  unfold to_word_idx, to_word, get_word in HS.
  rewrite MachineWord.MachineWord.cast_idx_refl in HS.
  unfold MachineWord.MachineWord.slice in HS.
  rewrite bv_extract_unsigned in HS.
  change (bv_unsigned ('b"0" : mword 1)) with 0 in HS.
  apply (f_equal (fun z => Z.testbit z 0)) in HS.
  rewrite Z.bits_0 in HS.
  rewrite <- HS.
  unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N (MachineWord.MachineWord.Z_idx (1 - 1 + 1)))); [| vm_compute; reflexivity].
  rewrite Z.shiftr_spec; [| lia]. reflexivity.
Qed.

(* ==================================================================== *)
(*  THE SPP TEST, ONCE, FOR BOTH POLARITIES.                             *)
(*                                                                      *)
(*  Both trap handlers open by testing SPP of a FRESH [csrr sstatus]     *)
(*  with [andi a5,a5,256], and read the result the opposite way round:   *)
(*                                                                      *)
(*    kerneltrap  if ((sstatus & SPP) == 0) panic("not from supervisor") *)
(*    usertrap    if ((sstatus & SPP) != 0) panic("not from user mode")  *)
(*                                                                      *)
(*  so kerneltrap needs the masked word NONZERO from SPP = 1 and         *)
(*  usertrap needs it ZERO from SPP = 0.  Those were two near-identical  *)
(*  lemma PAIRS, one in each function's parts file, split only because   *)
(*  neither parts file may import the other's.  They are one equation    *)
(*  read at a literal bit, and this is it: no hypothesis, so each        *)
(*  handler's own refutation is one [rewrite] away                       *)
(*  ([ProofKerneltrapParts.kt_spp_set_neq],                              *)
(*   [ProofUsertrapParts.ut_spp_clear_eq]).                              *)
(* ==================================================================== *)

(* SPP lives in bit 8, which is what the sstatus GETTER extracts. *)
Lemma sstatus_spp_bit (w : mword 64) :
  Z.testbit (bv_unsigned w) 8
  = Z.testbit (bv_unsigned (_get_Sstatus_SPP w)) 0.
Proof.
  unfold _get_Sstatus_SPP, subrange_vec_dec.
  rewrite autocast_refl.
  unfold to_word_idx, to_word, get_word.
  rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned.
  unfold bv_wrap, bv_modulus.
  rewrite (Z.mod_pow2_bits_low _ (Z.of_N (MachineWord.MachineWord.Z_idx (8 - 8 + 1))));
    [| vm_compute; reflexivity].
  rewrite Z.shiftr_spec; [| lia]. reflexivity.
Qed.

(* [andi a5,a5,256] on a fresh sstatus read is zero exactly when SPP is. *)
Lemma sstatus_spp_mask (ms : mword 64) :
  eq_vec (and_vec (sstatus_read ms)
            (sign_extend' 64 (mword_of_int 256 : mword 12))) zero_reg
  = negb (Z.testbit (bv_unsigned (_get_Mstatus_SPP ms)) 0).
Proof.
  assert (Hmask : bv_unsigned
                    (sign_extend' 64 (mword_of_int 256 : mword 12) : mword 64) = 256)
    by (vm_compute; reflexivity).
  (* Move the goal's SPP FIELD onto the WORD's bit 8 first, so the case split
     below is on a term the goal contains and [Hb8] comes out of it already
     read at a literal.  Splitting on the field instead leaves two facts about
     the same boolean whose shapes depend on what [destruct ... eqn:] chose to
     abstract, which is exactly the kind of dependence not to write down. *)
  replace (Z.testbit (bv_unsigned (_get_Mstatus_SPP ms)) 0)
    with (Z.testbit (bv_unsigned (sstatus_read ms)) 8).
  2:{ rewrite sstatus_spp_bit. do 2 f_equal.
      unfold sstatus_read. rewrite subrange_full. apply sSPP_lower. }
  destruct (Z.testbit (bv_unsigned (sstatus_read ms)) 8) eqn:Hb8; simpl.
  - (* SPP set: the masked word has bit 8, so it is not zero *)
    apply not_true_iff_false. intro Heq.
    apply eq_vec_true_iff in Heq.
    apply (f_equal bv_unsigned) in Heq.
    rewrite and_vec_unsigned Hmask in Heq.
    change (bv_unsigned (zero_reg : mword 64)) with 0 in Heq.
    apply (f_equal (fun z => Z.testbit z 8)) in Heq.
    rewrite Z.land_spec Z.bits_0 Hb8 in Heq.
    change (Z.testbit 256 8) with true in Heq.
    discriminate Heq.
  - (* SPP clear: bit 8 is the only bit the mask keeps, so the word is zero *)
    apply eq_vec_true_iff. apply bv_eq.
    rewrite and_vec_unsigned Hmask.
    change (bv_unsigned (zero_reg : mword 64)) with 0.
    apply Z.bits_inj_0. intro n.
    destruct (Z_lt_le_dec n 0) as [Hn | Hn].
    { apply Z.testbit_neg_r. lia. }
    rewrite Z.land_spec.
    destruct (Z.eq_dec n 8) as [-> | Hne].
    + rewrite Hb8. reflexivity.
    + replace (Z.testbit 256 n) with false; [apply andb_false_r |].
      change 256 with (2 ^ 8). symmetry.
      rewrite Z.pow2_bits_eqb; [| lia].
      apply Z.eqb_neq. lia.
Qed.

(* Phase 1 core: ANDing with ~2 leaves a word whose SIE bit is already 0. *)
Lemma and_clear_sie (w : mword 64) :
  Z.testbit (bv_unsigned w) 1 = false ->
  and_vec w (not_vec (zero_extend' 64 (mword_of_int 2 : mword 5))) = w.
Proof.
  intro Hb1.
  assert (HC : bv_unsigned (not_vec (zero_extend' 64 (mword_of_int 2 : mword 5)) : mword 64)
               = bv_wrap 64 (Z.lnot 2)).
  { cbv [not_vec Operators_mwords.word_unop Operators_mwords.with_word'
         SailStdpp.Values.with_word to_word get_word MachineWord.MachineWord.not].
    rewrite bv_not_unsigned. f_equal. }
  apply bv_eq. rewrite and_vec_unsigned. rewrite HC.
  apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec.
  pose proof (bv_unsigned_in_range _ w) as [Hw0 Hwhi].
  destruct (decide (j < 64)) as [Hjlt|Hjge].
  - unfold bv_wrap, bv_modulus.
    rewrite (Z.mod_pow2_bits_low _ 64); [| lia].
    rewrite Z.lnot_spec; [| lia].
    replace 2 with (2^1) by reflexivity.
    rewrite Z.pow2_bits_eqb; [| lia].
    destruct (Z.eqb 1 j) eqn:E1.
    + apply Z.eqb_eq in E1. subst j. rewrite Hb1. reflexivity.
    + rewrite andb_true_r. reflexivity.
  - unfold bv_wrap, bv_modulus.
    rewrite (Z.mod_pow2_bits_high _ 64); [| lia].
    rewrite andb_false_r. symmetry.
    assert (Hwlt : bv_unsigned w < 2 ^ 64) by exact Hwhi.
    destruct (decide (bv_unsigned w = 0)) as [Hz|Hnz].
    + rewrite Hz. apply Z.bits_0.
    + apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2 in Hwlt; lia.
Qed.

(* Phase 1: the S-view value csrrci writes back equals [lower_mstatus m]. *)
Lemma phase1 (m : mword 64) (HSIE : _get_Mstatus_SIE m = 'b"0") :
  Mk_Sstatus (zero_extend' 64 (sstatus_write_val m (mword_of_int 2))) = lower_mstatus m.
Proof.
  unfold Mk_Sstatus, sstatus_write_val, sstatus_read.
  rewrite subrange_full.
  rewrite (and_clear_sie (lower_mstatus m)).
  2:{ apply sie_bit. rewrite mSIE_lower. exact HSIE. }
  apply zext64_id.
Qed.

(* THE lemma: clearing SIE on a well-formed kernel mstatus is idempotent. *)
Lemma legalize_sie_clear_idem (m : mword 64)
  (HSIE : _get_Mstatus_SIE m = 'b"0")
  (HXS : _get_Mstatus_XS m = extStatus_map_forwards Off)
  (HFS : _get_Mstatus_FS m = extStatus_map_forwards Off)
  (HVS : _get_Mstatus_VS m = extStatus_map_forwards Off)
  (HSD : _get_Mstatus_SD m = 'b"0")
  (HMPP : have_nom_val (_get_Mstatus_MPP m) = true) :
  legalize_sstatus_val m (sstatus_write_val m (mword_of_int 2)) = m.
Proof.
  unfold legalize_sstatus_val.
  rewrite (phase1 m HSIE).
  rewrite (lift_lower_self m HXS HFS HVS HSD).
  apply (mstatus_legalized_self m HXS HFS HVS HSD HMPP).
Qed.
