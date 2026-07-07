(* WpGprCsrwC.v -- new-style WPs for the two CONFIG-WRITING csrw instructions
   xv6's start() executes and that were deliberately skipped by WpGprCsrwA/B:
     - csrw mstatus  (0x300) : writes the mstatus cell INSIDE [mmode_config];
     - csrw pmpcfg0  (0x3a0) : writes the pmpcfg_n cell threaded by [wp_instr].
   Both are built on [wp_instr_config] (InstrBytes.v), the engine that takes
   [mmode_config (DfracOwn 1)] + [pmpcfg_n ↦ᵣ pmpcfg0] at FULL ownership and
   lets the caller reg_update those cells while exhibiting [s_exec].

   Also proves the field-preservation facts of [mstatus_legalized] that let a
   chain REBUILD [mmode_config (DfracOwn 1)] after the mstatus write:
     - MIE / MPRV of the legalized value depend ONLY on the written value [v];
     - SXL is preserved from the OLD mstatus (never touched by the legalizer);
     - MPP of the legalized value depends only on [v] (the fact the boot chain
       uses to know MPP = Supervisor at the eventual MRET). *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr.
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

(* ---- get-over-update pair facts for the Mstatus fields the legalizer
   touches.  Each is one instance of the two bv window lemmas above at the
   concrete field positions; discharged by a uniform tactic. ---- *)
Local Ltac guu :=
  unfold _get_Mstatus_MIE, _get_Mstatus_MPRV, _get_Mstatus_SXL, _get_Mstatus_MPP,
         _update_Mstatus_SD, _update_Mstatus_SIE, _update_Mstatus_MIE,
         _update_Mstatus_SPIE, _update_Mstatus_MPIE, _update_Mstatus_SPP,
         _update_Mstatus_MPP, _update_Mstatus_VS, _update_Mstatus_FS,
         _update_Mstatus_XS, _update_Mstatus_MPRV, _update_Mstatus_SUM,
         _update_Mstatus_MXR, _update_Mstatus_TVM, _update_Mstatus_TW,
         _update_Mstatus_TSR, _update_Mstatus_SPELP, _update_Mstatus_MPELP;
  unfold subrange_vec_dec, update_subrange_vec_dec;
  rewrite !autocast_refl;
  unfold to_word_idx, to_word, get_word;
  rewrite !MachineWord.MachineWord.cast_idx_refl.

Local Ltac gu_disj :=
  guu;
  apply bv_extract_update_slice_disjoint;
  [ first [ left; vm_compute; let X := fresh in intro X; discriminate X
          | right; vm_compute; let X := fresh in intro X; discriminate X ]
  | vm_compute; let X := fresh in intro X; discriminate X ].

Local Ltac gu_same :=
  guu;
  apply bv_extract_update_slice_same;
  vm_compute; let X := fresh in intro X; discriminate X.

(* MIE (bit 3) *)
Lemma gMIE_uSD (w : mword 64) x : _get_Mstatus_MIE (_update_Mstatus_SD w x) = _get_Mstatus_MIE w.
Proof. gu_disj. Qed.
Lemma gMIE_uSIE (w : mword 64) x : _get_Mstatus_MIE (_update_Mstatus_SIE w x) = _get_Mstatus_MIE w.
Proof. gu_disj. Qed.
Lemma gMIE_uMIE (w : mword 64) x : _get_Mstatus_MIE (_update_Mstatus_MIE w x) = x.
Proof. gu_same. Qed.

(* MPRV (bit 17) *)
Lemma gMPRV_uSD (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SD w x) = _get_Mstatus_MPRV w.
Proof. gu_disj. Qed.
Lemma gMPRV_uSIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SIE w x) = _get_Mstatus_MPRV w.
Proof. gu_disj. Qed.
Lemma gMPRV_uMIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MIE w x) = _get_Mstatus_MPRV w.
Proof. gu_disj. Qed.
Lemma gMPRV_uSPIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SPIE w x) = _get_Mstatus_MPRV w.
Proof. gu_disj. Qed.
Lemma gMPRV_uMPIE (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MPIE w x) = _get_Mstatus_MPRV w.
Proof. gu_disj. Qed.
Lemma gMPRV_uSPP (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_SPP w x) = _get_Mstatus_MPRV w.
Proof. gu_disj. Qed.
Lemma gMPRV_uMPP (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MPP w x) = _get_Mstatus_MPRV w.
Proof. gu_disj. Qed.
Lemma gMPRV_uVS (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_VS w x) = _get_Mstatus_MPRV w.
Proof. gu_disj. Qed.
Lemma gMPRV_uFS (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_FS w x) = _get_Mstatus_MPRV w.
Proof. gu_disj. Qed.
Lemma gMPRV_uXS (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_XS w x) = _get_Mstatus_MPRV w.
Proof. gu_disj. Qed.
Lemma gMPRV_uMPRV (w : mword 64) x : _get_Mstatus_MPRV (_update_Mstatus_MPRV w x) = x.
Proof. gu_same. Qed.

(* MPP (bits 12..11) *)
Lemma gMPP_uSD (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SD w x) = _get_Mstatus_MPP w.
Proof. gu_disj. Qed.
Lemma gMPP_uSIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SIE w x) = _get_Mstatus_MPP w.
Proof. gu_disj. Qed.
Lemma gMPP_uMIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MIE w x) = _get_Mstatus_MPP w.
Proof. gu_disj. Qed.
Lemma gMPP_uSPIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SPIE w x) = _get_Mstatus_MPP w.
Proof. gu_disj. Qed.
Lemma gMPP_uMPIE (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MPIE w x) = _get_Mstatus_MPP w.
Proof. gu_disj. Qed.
Lemma gMPP_uSPP (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_SPP w x) = _get_Mstatus_MPP w.
Proof. gu_disj. Qed.
Lemma gMPP_uMPP (w : mword 64) x : _get_Mstatus_MPP (_update_Mstatus_MPP w x) = x.
Proof. gu_same. Qed.

(* SXL (bits 35..34) -- never written by the legalizer *)
Lemma gSXL_uSD (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SD w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uSIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SIE w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uMIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MIE w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uSPIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SPIE w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uMPIE (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPIE w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uSPP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SPP w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uMPP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPP w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uVS (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_VS w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uFS (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_FS w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uXS (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_XS w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uMPRV (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPRV w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uSUM (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SUM w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uMXR (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MXR w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uTVM (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_TVM w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uTW (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_TW w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uTSR (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_TSR w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uSPELP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_SPELP w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.
Lemma gSXL_uMPELP (w : mword 64) x : _get_Mstatus_SXL (_update_Mstatus_MPELP w x) = _get_Mstatus_SXL w.
Proof. gu_disj. Qed.

(* ====================================================================== *)
(* Invariant preservation of [mstatus_legalized o v]:                       *)
(*   - MIE / MPRV / MPP of the result depend ONLY on the written value [v]  *)
(*     (so a caller that knows the concrete v discharges them by vm math);  *)
(*   - SXL of the result equals SXL of the OLD mstatus [o] (preserved       *)
(*     UNCONDITIONALLY: the legalizer never touches bits 35..34).           *)
(* ====================================================================== *)
Lemma mstatus_legalized_MIE (o v : mword 64) :
  _get_Mstatus_MIE (mstatus_legalized o v) = _get_Mstatus_MIE v.
Proof.
  unfold mstatus_legalized. cbn zeta.
  rewrite gMIE_uSD gMIE_uSIE gMIE_uMIE. reflexivity.
Qed.

Lemma mstatus_legalized_MPRV (o v : mword 64) :
  _get_Mstatus_MPRV (mstatus_legalized o v) = _get_Mstatus_MPRV v.
Proof.
  unfold mstatus_legalized. cbn zeta.
  rewrite gMPRV_uSD gMPRV_uSIE gMPRV_uMIE gMPRV_uSPIE gMPRV_uMPIE gMPRV_uSPP
          gMPRV_uMPP gMPRV_uVS gMPRV_uFS gMPRV_uXS gMPRV_uMPRV.
  reflexivity.
Qed.

Lemma mstatus_legalized_SXL (o v : mword 64) :
  _get_Mstatus_SXL (mstatus_legalized o v) = _get_Mstatus_SXL o.
Proof.
  unfold mstatus_legalized. cbn zeta.
  rewrite gSXL_uSD gSXL_uSIE gSXL_uMIE gSXL_uSPIE gSXL_uMPIE gSXL_uSPP
          gSXL_uMPP gSXL_uVS gSXL_uFS gSXL_uXS gSXL_uMPRV gSXL_uSUM gSXL_uMXR
          gSXL_uTVM gSXL_uTW gSXL_uTSR gSXL_uSPELP gSXL_uMPELP.
  reflexivity.
Qed.

(* MPP of the legalized mstatus is determined by [v] alone: the value the
   boot chain needs to know MPP = Supervisor at the eventual MRET. *)
Lemma mstatus_legalized_MPP (o v : mword 64) :
  _get_Mstatus_MPP (mstatus_legalized o v)
  = (if have_nom_val (_get_Mstatus_MPP v)
     then _get_Mstatus_MPP v else privLevel_to_bits User).
Proof.
  unfold mstatus_legalized. cbn zeta.
  rewrite gMPP_uSD gMPP_uSIE gMPP_uMIE gMPP_uSPIE gMPP_uMPIE gMPP_uSPP gMPP_uMPP.
  reflexivity.
Qed.

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
  Context `{CID : CpuId}.

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
  Lemma wp_csrw_mstatus_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW)) -∗
    ( ∀ (ms_old : mword 64)
        (HoSXL : _get_Mstatus_SXL ms_old = 'b"10"),
      hw_config -∗
      minstret_inv -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Machine -∗
      mstatus ↦ᵣ mstatus_legalized ms_old (m !!! Regidx rs1) -∗
      pmpcfg_n ↦ᵣ pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iDestruct (mmode_config_unbundle with "Hmm") as "(#Hhw & #Hinv & Hhs & Hpriv0 & Hmst)".
    iDestruct "Hmst" as (ms0) "(Hms0 & %HmIE & %HMPRV & %HSXL)".
    iApply (wp_instr_config E Φ pc false (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW))
              pmpcfg0 ms0 HN Hpmp HmIE
              with "Hhw Hinv Hhs Hpriv0 Hms0 Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hpriv Hms Hpmpc Hsi".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc mstatus (mstatus_legalized ms0 (m !!! Regidx rs1))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" $! ms0 HSXL
              with "Hhw Hinv Hhs Hpriv Hms Hpmpc [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- csrw pmpcfg0 (0x3a0): writes the pmpcfg_n vector cell.  The fetch of
     THIS instruction happens under the OLD pmpcfg (premise [pmp_allows_all
     pmpcfg0] as usual); the continuation receives the NEW concrete value --
     the chain proves [pmp_allows_all (pmpcfg_written ...)] separately for the
     instructions that follow.  mstatus is unchanged, so the continuation gets
     an opaque REBUILT [mmode_config (DfracOwn 1)]. ---- *)
  Lemma wp_csrw_pmpcfg0_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64))
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW)) -∗
    ( mmode_config (DfracOwn 1) -∗
      pmpcfg_n ↦ᵣ pmpcfg_written (m !!! Regidx rs1) pmpcfg0 -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iDestruct (mmode_config_unbundle with "Hmm") as "(#Hhw & #Hinv & Hhs & Hpriv0 & Hmst)".
    iDestruct "Hmst" as (ms0) "(Hms0 & %HmIE & %HMPRV & %HSXL)".
    iApply (wp_instr_config E Φ pc false (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW))
              pmpcfg0 ms0 HN Hpmp HmIE
              with "Hhw Hinv Hhs Hpriv0 Hms0 Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hpriv Hms Hpmpc Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hpmpc") as %Lcfg.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc pmpcfg_n (pmpcfg_written (m !!! Regidx rs1) pmpcfg0)).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iDestruct (mmode_config_rebuild (DfracOwn 1) ms0 HmIE HMPRV HSXL
                 with "Hhw Hinv Hhs Hpriv Hms") as "Hmm'".
    iApply ("Hcont" with "Hmm' Hpmpc [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- RAW variant of the csrw-mstatus WP: the caller supplies the config
     cells UNBUNDLED with the mstatus VALUE [ms0] explicit (a chain that
     unbundled its [mmode_config (DfracOwn 1)] at the top and has been
     pinning [ms0] with an outside fraction ever since).  The continuation
     receives the same raw cells with mstatus at the EXPLICIT legalized
     value -- no re-quantification over a hidden old value, so the chain
     keeps a single mstatus symbol end-to-end. ---- *)
  Lemma wp_csrw_mstatus_raw E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (ms0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
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
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp HmIE) "#Hhw #Hinv Hhs Hpriv0 Hms0 Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_config E Φ pc false (CSRReg (csr_mstatus, Regidx rs1, zreg, CSRRW))
              pmpcfg0 ms0 HN Hpmp HmIE
              with "Hhw Hinv Hhs Hpriv0 Hms0 Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hpriv Hms Hpmpc Hsi".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
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
  Lemma wp_csrw_pmpcfg0_raw E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 : mword 5)
      (m : gmap regidx (mword 64)) (ms0 : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
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
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp HmIE) "#Hhw #Hinv Hhs Hpriv0 Hms0 Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_config E Φ pc false (CSRReg (csr_pmpcfg0, Regidx rs1, zreg, CSRRW))
              pmpcfg0 ms0 HN Hpmp HmIE
              with "Hhw Hinv Hhs Hpriv0 Hms0 Hpmpc Hpc Hinstr").
    iIntros (σ Hpceq) "Hpriv Hms Hpmpc Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hpmpc") as %Lcfg.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
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
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
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



