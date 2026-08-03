(* WpStartNew.v -- the xv6 kernel [start()] (39 instructions at
   0x80000058 .. 0x800000cb), proved as ONE WP theorem [wp_start] by composing
   ONLY the new-style register-generic [wp_*_gpr] WPs, [wp_timerinit] (the
   jal-called subroutine), the raw config-writing WPs of WpGprCsrwC, and the
   [wp_mret_gpr] endpoint.

   start() writes menvcfg TWICE: its own [menvcfg |= MENVCFG_ADUE] (bit 61,
   the five-instruction "ADUE block" at 0x800000b0..0x800000bd -- csrr/c.li/
   c.slli/c.or/csrw), then timerinit's [menvcfg |= MENVCFG_STCE] (bit 63).  So
   the final S-mode menvcfg is 0xA000000000000000 = [MENVCFG_S].  Inserting the
   5-instruction (14-byte, odd-halfword) ADUE block flips the parity of the
   jal-to-timerinit and its return address (now 2-aligned), so the return uses
   the C-extension 2-aligned cret ([wp_cret_gpr_zca]) inside [wp_timerinit].

   The trace (ground truth: kernel-rocq/KernelInstrs.v):
     30 0x80000058 0x1141     c.addi  sp, -16          [RVC, 4-aligned]
     31 0x8000005a 0xe406     c.sdsp  ra, 8(sp)        [RVC, 8-byte STORE]
     32 0x8000005c 0xe022     c.sdsp  s0, 0(sp)        [RVC, 8-byte STORE]
     33 0x8000005e 0x0800     c.addi4spn s0, sp, 16    [RVC]
     34 0x80000060 0x300027f3 csrr    a5, mstatus      [F_Base, 4-aligned]
     35 0x80000064 0x7779     c.lui   a4, 0xffffe      [RVC]
     36 0x80000066 0x7ff70713 addi    a4, a4, 2047     [F_Base, 2-aligned]
     37 0x8000006a 0x8ff9     c.and   a5, a4           [RVC]
     38 0x8000006c 0x6705     c.lui   a4, 0x1          [RVC]
     39 0x8000006e 0x80070713 addi    a4, a4, -2048    [F_Base, 2-aligned]
     40 0x80000072 0x8fd9     c.or    a5, a4           [RVC]
     41 0x80000074 0x30079073 csrw    mstatus, a5      [F_Base, 4-aligned]
     42 0x80000078 0x00001797 auipc   a5, 0x1          [F_Base, 4-aligned]
     43 0x8000007c 0xdf878793 addi    a5, a5, -520     [F_Base, 4-aligned]
     44 0x80000080 0x34179073 csrw    mepc, a5         [F_Base, 4-aligned]
     45 0x80000084 0x4781     c.li    a5, 0            [RVC]
     46 0x80000086 0x18079073 csrw    satp, a5         [F_Base, 2-aligned]
     47 0x8000008a 0x67c1     c.lui   a5, 0x10         [RVC]
     48 0x8000008c 0x17fd     c.addi  a5, -1           [RVC]
     49 0x8000008e 0x30279073 csrw    medeleg, a5      [F_Base, 2-aligned]
     50 0x80000092 0x30379073 csrw    mideleg, a5      [F_Base, 2-aligned]
     51 0x80000096 0x104027f3 csrr    a5, sie          [F_Base, 2-aligned]
     52 0x8000009a 0x2207e793 ori     a5, a5, 544      [F_Base, 2-aligned]
     53 0x8000009e 0x10479073 csrw    sie, a5          [F_Base, 2-aligned]
     54 0x800000a2 0x57fd     c.li    a5, -1           [RVC]
     55 0x800000a4 0x83a9     c.srli  a5, 0xa          [RVC]
     56 0x800000a6 0x3b079073 csrw    pmpaddr0, a5     [F_Base, 2-aligned]
     57 0x800000aa 0x47bd     c.li    a5, 15           [RVC]
     58 0x800000ac 0x3a079073 csrw    pmpcfg0, a5      [F_Base, 4-aligned]
        0x800000b0 0x30a027f3 csrr    a5, menvcfg      [F_Base, 4-aligned] |
        0x800000b4 0x4705     c.li    a4, 1            [RVC]               | ADUE
        0x800000b6 0x1776     c.slli  a4, 0x3d         [RVC]               | block
        0x800000b8 0x8fd9     c.or    a5, a4           [RVC]               |
        0x800000ba 0x30a79073 csrw    menvcfg, a5      [F_Base, 2-aligned] |
     59 0x800000be 0xf5fff0ef jal     ra, timerinit    [F_Base, 2-aligned]
     60 0x800000c2 0xf14027f3 csrr    a5, mhartid      [F_Base, 2-aligned]
     61 0x800000c6 0x2781     c.addiw a5, 0 (sext.w)   [RVC]
     62 0x800000c8 0x823e     c.mv    tp, a5           [RVC]
     63 0x800000ca 0x30200073 mret                     [F_Base, 2-aligned]

   Fraction choreography: the caller's [mmode_config (DfracOwn 1)] is
   unbundled ONCE at the top (naming the entry mstatus value [ms0] with its
   invariant facts), split in half: a working bundle [mmode_config
   (DfracOwn (1/2))] runs the ordinary WPs, while the outside raw halves pin
   the mstatus VALUE.  At the three config-writing sites (csrw mstatus,
   csrw pmpcfg0, mret) the halves are recombined to full raw cells (value
   pinned by [reg_pointsto_agree]) and the RAW WPs of WpGprCsrwC /
   WpGprMretNew run at full ownership, after which the cells are re-split. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import StackOwn.
Require Import RegFile.
Require Import WpGprCsrwCommon.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpDecode ExecCommon WpGpr.
Require Import WpAuipc WpMmodeShiftiop WpMmodeJal.
Require Import WpMmodeLeafBase.
Require Import WpMmodeUtype.
Require Import WpMmodeAddiw.
Require Import WpMmodeItype.
Require Import WpMmodeRtype.
Require Import WpMmodeStore.
Require Import WpGprCsrrA WpGprCsrrB WpGprCsrwA WpGprCsrwB WpGprCsrwC.
Require Import WpGprMretWp.
Require Import WpMmodeLeafBase.
Require Import WpMmodeMret.
Require Import InstrBytes KernelText WpTimerinit.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Require Import CodeStart.
Require Import CodeTimerinit.

(* ===================================================================== *)
(* Symbolic values of the run (functions of the entry state).  start()'s *)
(* own 16-byte frame reuses timerinit's slot geometry: the frame base is  *)
(* [ti_sp1 sp0] and the slots are [ti_ea_ra sp0] / [ti_ea_s0 sp0];        *)
(* timerinit's (nested) frame slots are [ti_ea_ra (ti_sp1 sp0)] /         *)
(* [ti_ea_s0 (ti_sp1 sp0)].                                               *)
(* ===================================================================== *)

(* mstatus write mask: a5 := (mstatus & 0xffffffffffffe7ff) | 0x800
   (clear MPP[12:11], set MPP := 01 = Supervisor). *)
Definition st_mask_and : mword 64 := mword_of_int 0xffffffffffffe7ff.
Definition st_mask_or  : mword 64 := mword_of_int 0x800.
Definition st_va5_40 (ms : mword 64) : mword 64 :=
  or_vec (and_vec ms st_mask_and) st_mask_or.
(* the legalized mstatus after idx 41 *)
Definition st_ms1 (ms : mword 64) : mword 64 := mstatus_legalized ms (st_va5_40 ms).

Definition st_a42v : mword 64 := mword_of_int 0x80001078.  (* auipc a5,1 *)
Definition st_main : mword 64 := mword_of_int (KernelSyms.main).  (* <main> *)
Definition st_ffff : mword 64 := mword_of_int 0xffff.      (* medeleg/mideleg wval *)
Definition st_pmpw : mword 64 := mword_of_int 0x3fffffffffffff. (* pmpaddr0 wval *)
Definition st_ra_link : mword 64 := mword_of_int (KernelSyms.start + 0x6a).    (* jal link *)

(* the ADUE bit (menvcfg bit 61 = Svadu) and the menvcfg value start()'s ADUE
   write leaves: legalize(menv0, menv0 | (1<<61)).  This is the menvcfg
   timerinit's own STCE write then sees. *)
Definition st_adue_bit : mword 64 := mword_of_int 0x2000000000000000.
Definition st_menv_adue (menv0 : mword 64) : mword 64 :=
  menvcfg_legalized menv0 (or_vec menv0 st_adue_bit).

Definition st_mdl1 (mdl0 : mword 64) : mword 64 := mideleg_legalized mdl0 st_ffff.
Definition st_va5_52 (mie0 mdl0 : mword 64) : mword 64 :=
  or_vec (lower_mie mie0 (st_mdl1 mdl0)) (sign_extend' 64 si52).
Definition st_mie1 (mie0 mdl0 : mword 64) : mword 64 :=
  sie_new_mie mie0 (st_mdl1 mdl0) (st_va5_52 mie0 mdl0).
Definition st_pmpcfg1 (cfg0 : type_of_register pmpcfg_n) : type_of_register pmpcfg_n :=
  pmpcfg_written (mword_of_int 15) cfg0.
Definition st_pmpaddr1 (cfg0 : type_of_register pmpcfg_n)
    (pa0 : type_of_register pmpaddr_n) : type_of_register pmpaddr_n :=
  pmp0_newaddr cfg0 pa0 st_pmpw.
Definition st_tpv (mh : mword 64) : mword 64 :=
  sign_extend' 64 (subrange_vec_dec (add_vec mh (sign_extend' 64 si61)) 31 0).

(* s0 := sp + 16 after the -16 prologue is the ORIGINAL sp. *)
Lemma st_s0_16 (sp0 : mword 64) :
  add_vec (ti_sp1 sp0) (sign_extend' 64 (caddi4spn_imm nz12)) = sp0.
Proof.
  unfold ti_sp1. rewrite po_addv_assoc.
  replace (add_vec (sign_extend' 64 i9) (sign_extend' 64 (caddi4spn_imm nz12)))
    with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
  exact (avi0 sp0).
Qed.

(* ===================================================================== *)
(* Bit-window facts about the mstatus write mask, for SYMBOLIC ms:        *)
(*   - MIE (bit 3) / MPRV (bit 17) of the written value equal those of    *)
(*     the read mstatus (the AND mask keeps them, the OR mask misses);    *)
(*   - MPP (bits 12:11) of the written value is 01 (Supervisor bits)      *)
(*     UNCONDITIONALLY (AND clears them, OR sets bit 11).                  *)
(* ===================================================================== *)

Local Ltac st_bit_open :=
  cbv [st_va5_40 or_vec and_vec Operators_mwords.word_binop
       Operators_mwords.with_word' SailStdpp.Values.with_word];
  unfold MachineWord.MachineWord.and, MachineWord.MachineWord.or;
  unfold subrange_vec_dec; rewrite !autocast_id;
  unfold to_word_idx, to_word; rewrite !MachineWord.MachineWord.cast_idx_refl;
  unfold get_word, MachineWord.MachineWord.slice;
  apply bv_eq; rewrite !bv_extract_unsigned;
  rewrite bv_or_unsigned bv_and_unsigned;
  replace (bv_unsigned st_mask_and) with 0xffffffffffffe7ff
    by (vm_compute; reflexivity);
  replace (bv_unsigned st_mask_or) with 0x800 by (vm_compute; reflexivity);
  unfold bv_wrap, bv_modulus.

Lemma st_va5_40_MIE (x : mword 64) :
  _get_Mstatus_MIE (st_va5_40 x) = _get_Mstatus_MIE x.
Proof.
  unfold _get_Mstatus_MIE. st_bit_open.
  repeat match goal with
  | |- context[Z.of_N ?t] =>
      let v := eval vm_compute in (Z.of_N t) in
      progress (replace (Z.of_N t) with v by (vm_compute; reflexivity))
  end.
  apply Z.bits_inj'. intros j Hj.
  destruct (decide (j < 1)) as [Hj1 | Hj1].
  - replace j with 0 by lia.
    rewrite !Z.mod_pow2_bits_low; [| lia | lia].
    rewrite !Z.shiftr_spec; [| lia | lia].
    rewrite Z.lor_spec Z.land_spec.
    replace (Z.testbit 0xffffffffffffe7ff (0 + 3)) with true by (vm_compute; reflexivity).
    replace (Z.testbit 0x800 (0 + 3)) with false by (vm_compute; reflexivity).
    rewrite andb_true_r orb_false_r. reflexivity.
  - rewrite !Z.mod_pow2_bits_high; [reflexivity | lia | lia].
Qed.

Lemma st_va5_40_MPRV (x : mword 64) :
  _get_Mstatus_MPRV (st_va5_40 x) = _get_Mstatus_MPRV x.
Proof.
  unfold _get_Mstatus_MPRV. st_bit_open.
  repeat match goal with
  | |- context[Z.of_N ?t] =>
      let v := eval vm_compute in (Z.of_N t) in
      progress (replace (Z.of_N t) with v by (vm_compute; reflexivity))
  end.
  apply Z.bits_inj'. intros j Hj.
  destruct (decide (j < 1)) as [Hj1 | Hj1].
  - replace j with 0 by lia.
    rewrite !Z.mod_pow2_bits_low; [| lia | lia].
    rewrite !Z.shiftr_spec; [| lia | lia].
    rewrite Z.lor_spec Z.land_spec.
    replace (Z.testbit 0xffffffffffffe7ff (0 + 17)) with true by (vm_compute; reflexivity).
    replace (Z.testbit 0x800 (0 + 17)) with false by (vm_compute; reflexivity).
    rewrite andb_true_r orb_false_r. reflexivity.
  - rewrite !Z.mod_pow2_bits_high; [reflexivity | lia | lia].
Qed.

Lemma st_va5_40_MPP (x : mword 64) :
  _get_Mstatus_MPP (st_va5_40 x) = ('b"01" : mword 2).
Proof.
  unfold _get_Mstatus_MPP. st_bit_open.
  repeat match goal with
  | |- context[Z.of_N ?t] =>
      let v := eval vm_compute in (Z.of_N t) in
      progress (replace (Z.of_N t) with v by (vm_compute; reflexivity))
  end.
  replace (bv_unsigned ('b"01" : mword 2)) with 1 by (vm_compute; reflexivity).
  apply Z.bits_inj'. intros j Hj.
  destruct (decide (j < 2)) as [Hj2 | Hj2].
  - rewrite Z.mod_pow2_bits_low; [| lia].
    rewrite Z.shiftr_spec; [| lia].
    rewrite Z.lor_spec Z.land_spec.
    destruct (decide (j = 0)) as [-> | Hj0].
    + replace (Z.testbit 0xffffffffffffe7ff (0 + 11)) with false by (vm_compute; reflexivity).
      replace (Z.testbit 0x800 (0 + 11)) with true by (vm_compute; reflexivity).
      rewrite andb_false_r orb_true_r. vm_compute. reflexivity.
    + replace j with 1 by lia.
      replace (Z.testbit 0xffffffffffffe7ff (1 + 11)) with false by (vm_compute; reflexivity).
      replace (Z.testbit 0x800 (1 + 11)) with false by (vm_compute; reflexivity).
      rewrite andb_false_r orb_false_r. vm_compute. reflexivity.
  - rewrite Z.mod_pow2_bits_high; [| lia].
    symmetry. apply Z.bits_above_log2; [lia |].
    replace (Z.log2 1) with 0 by reflexivity. lia.
Qed.

(* ===================================================================== *)
(* menvcfg.LPE (bit 2) is never set by the boot flow: the legalizer's     *)
(* LPE field is written from the written value, whose bit 2 the           *)
(* [STCE |= bit63] OR does not touch.  Get-over-update ladder in the      *)
(* style of WpGprCsrwC's Mstatus family.                                  *)
(* ===================================================================== *)
Local Ltac st_guu :=
  unfold _get_MEnvcfg_LPE,
         _update_MEnvcfg_FIOM, _update_MEnvcfg_LPE, _update_MEnvcfg_SSE,
         _update_MEnvcfg_CBZE, _update_MEnvcfg_CBCFE, _update_MEnvcfg_CBIE,
         _update_MEnvcfg_STCE, _update_MEnvcfg_PMM, _update_MEnvcfg_ADUE,
         _update_MEnvcfg_PBMTE;
  unfold subrange_vec_dec, update_subrange_vec_dec;
  rewrite !autocast_refl;
  unfold to_word_idx, to_word, get_word;
  rewrite !MachineWord.MachineWord.cast_idx_refl.

Local Ltac st_gu_disj :=
  st_guu;
  apply bv_extract_update_slice_disjoint;
  [ first [ left; vm_compute; let X := fresh in intro X; discriminate X
          | right; vm_compute; let X := fresh in intro X; discriminate X ]
  | vm_compute; let X := fresh in intro X; discriminate X ].

Local Ltac st_gu_same :=
  st_guu;
  apply bv_extract_update_slice_same;
  vm_compute; let X := fresh in intro X; discriminate X.

Lemma gLPEe_uLPE (w : mword 64) x : _get_MEnvcfg_LPE (_update_MEnvcfg_LPE w x) = x.
Proof. st_gu_same. Qed.
Lemma gLPEe_uSSE (w : mword 64) x : _get_MEnvcfg_LPE (_update_MEnvcfg_SSE w x) = _get_MEnvcfg_LPE w.
Proof. st_gu_disj. Qed.
Lemma gLPEe_uCBZE (w : mword 64) x : _get_MEnvcfg_LPE (_update_MEnvcfg_CBZE w x) = _get_MEnvcfg_LPE w.
Proof. st_gu_disj. Qed.
Lemma gLPEe_uCBCFE (w : mword 64) x : _get_MEnvcfg_LPE (_update_MEnvcfg_CBCFE w x) = _get_MEnvcfg_LPE w.
Proof. st_gu_disj. Qed.
Lemma gLPEe_uCBIE (w : mword 64) x : _get_MEnvcfg_LPE (_update_MEnvcfg_CBIE w x) = _get_MEnvcfg_LPE w.
Proof. st_gu_disj. Qed.
Lemma gLPEe_uSTCE (w : mword 64) x : _get_MEnvcfg_LPE (_update_MEnvcfg_STCE w x) = _get_MEnvcfg_LPE w.
Proof. st_gu_disj. Qed.
Lemma gLPEe_uPMM (w : mword 64) x : _get_MEnvcfg_LPE (_update_MEnvcfg_PMM w x) = _get_MEnvcfg_LPE w.
Proof. st_gu_disj. Qed.
Lemma gLPEe_uADUE (w : mword 64) x : _get_MEnvcfg_LPE (_update_MEnvcfg_ADUE w x) = _get_MEnvcfg_LPE w.
Proof. st_gu_disj. Qed.
Lemma gLPEe_uPBMTE (w : mword 64) x : _get_MEnvcfg_LPE (_update_MEnvcfg_PBMTE w x) = _get_MEnvcfg_LPE w.
Proof. st_gu_disj. Qed.

Lemma menvcfg_legalized_LPE (o v : mword 64) :
  _get_MEnvcfg_LPE (menvcfg_legalized o v) = _get_MEnvcfg_LPE v.
Proof.
  unfold menvcfg_legalized. cbn zeta.
  rewrite gLPEe_uPBMTE gLPEe_uADUE gLPEe_uPMM gLPEe_uSTCE gLPEe_uCBIE
          gLPEe_uCBCFE gLPEe_uCBZE gLPEe_uSSE gLPEe_uLPE.
  unfold Mk_MEnvcfg. reflexivity.
Qed.

(* bit 2 of (x | (1<<63)) is bit 2 of x. *)
Lemma st_LPE_or_bit63 (x : mword 64) :
  _get_MEnvcfg_LPE (ti_menv1 x) = _get_MEnvcfg_LPE x.
Proof.
  unfold _get_MEnvcfg_LPE, ti_menv1.
  cbv [or_vec Operators_mwords.word_binop
       Operators_mwords.with_word' SailStdpp.Values.with_word].
  unfold MachineWord.MachineWord.or.
  unfold subrange_vec_dec. rewrite !autocast_id.
  unfold to_word_idx, to_word. rewrite !MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  apply bv_eq. rewrite !bv_extract_unsigned. rewrite bv_or_unsigned.
  replace (bv_unsigned ti_bit63) with 0x8000000000000000 by (vm_compute; reflexivity).
  unfold bv_wrap, bv_modulus.
  repeat match goal with
  | |- context[Z.of_N ?t] =>
      let v := eval vm_compute in (Z.of_N t) in
      progress (replace (Z.of_N t) with v by (vm_compute; reflexivity))
  end.
  apply Z.bits_inj'. intros j Hj.
  destruct (decide (j < 1)) as [Hj1 | Hj1].
  - replace j with 0 by lia.
    rewrite !Z.mod_pow2_bits_low; [| lia | lia].
    rewrite !Z.shiftr_spec; [| lia | lia].
    rewrite Z.lor_spec.
    replace (Z.testbit 0x8000000000000000 (0 + 2)) with false by (vm_compute; reflexivity).
    rewrite orb_false_r. reflexivity.
  - rewrite !Z.mod_pow2_bits_high; [reflexivity | lia | lia].
Qed.

(* the LPE bit of the FINAL menvcfg (post-timerinit) is 0, given it starts 0. *)
Lemma st_menvcfg_LPE_final (menv0 : mword 64) :
  _get_MEnvcfg_LPE menv0 = ('b"0") ->
  _get_MEnvcfg_LPE (menvcfg_legalized menv0 (ti_menv1 menv0)) = ('b"0").
Proof.
  intro H. rewrite menvcfg_legalized_LPE. rewrite st_LPE_or_bit63. exact H.
Qed.

(* the ADUE bit (61) does not touch LPE (bit 2), so start()'s [menvcfg |= 1<<61]
   write preserves LPE=0 -- exactly the hypothesis timerinit's own menvcfg write
   needs on its (now ADUE-written) input. *)
Lemma st_LPE_or_adue (x : mword 64) :
  _get_MEnvcfg_LPE (or_vec x st_adue_bit) = _get_MEnvcfg_LPE x.
Proof.
  unfold _get_MEnvcfg_LPE.
  cbv [or_vec Operators_mwords.word_binop
       Operators_mwords.with_word' SailStdpp.Values.with_word].
  unfold MachineWord.MachineWord.or.
  unfold subrange_vec_dec. rewrite !autocast_id.
  unfold to_word_idx, to_word. rewrite !MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  apply bv_eq. rewrite !bv_extract_unsigned. rewrite bv_or_unsigned.
  replace (bv_unsigned st_adue_bit) with 0x2000000000000000 by (vm_compute; reflexivity).
  unfold bv_wrap, bv_modulus.
  repeat match goal with
  | |- context[Z.of_N ?t] =>
      let v := eval vm_compute in (Z.of_N t) in
      progress (replace (Z.of_N t) with v by (vm_compute; reflexivity))
  end.
  apply Z.bits_inj'. intros j Hj.
  destruct (decide (j < 1)) as [Hj1 | Hj1].
  - replace j with 0 by lia.
    rewrite !Z.mod_pow2_bits_low; [| lia | lia].
    rewrite !Z.shiftr_spec; [| lia | lia].
    rewrite Z.lor_spec.
    replace (Z.testbit 0x2000000000000000 (0 + 2)) with false by (vm_compute; reflexivity).
    rewrite orb_false_r. reflexivity.
  - rewrite !Z.mod_pow2_bits_high; [reflexivity | lia | lia].
Qed.

Lemma st_menv_adue_LPE (menv0 : mword 64) :
  _get_MEnvcfg_LPE menv0 = ('b"0") -> _get_MEnvcfg_LPE (st_menv_adue menv0) = ('b"0").
Proof.
  intro H. unfold st_menv_adue. rewrite menvcfg_legalized_LPE. rewrite st_LPE_or_adue. exact H.
Qed.

(* c.li a4,1 then c.slli a4,0x3d builds exactly the ADUE bit (1<<61). *)
Lemma st_Hb61 :
  shift_bits_left (cli_wval sae_li) (subrange_vec_dec sae_slli (Z.sub log2_xlen 1) 0) = st_adue_bit.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* The MPP-at-MRET keystone: the target privilege decoded from the        *)
(* legalized-then-cms-updated mstatus is Supervisor.                      *)
(* ===================================================================== *)
Lemma st_mret_priv (ms : mword 64) :
  privLevel_bits_forwards (_get_Mstatus_MPP (cms2 (st_ms1 ms)), ('b"0"))
    = returnM Supervisor.
Proof.
  unfold cms2, cms1.
  change (update_subrange_vec_dec (st_ms1 ms) 3 3 (_get_Mstatus_MPIE (st_ms1 ms)))
    with (_update_Mstatus_MIE (st_ms1 ms) (_get_Mstatus_MPIE (st_ms1 ms))).
  match goal with |- context[update_subrange_vec_dec ?w 7 7 ?x] =>
    change (update_subrange_vec_dec w 7 7 x) with (_update_Mstatus_MPIE w x) end.
  rewrite gMPP_uMPIE gMPP_uMIE.
  unfold st_ms1. rewrite mstatus_legalized_MPP. rewrite st_va5_40_MPP.
  replace (have_nom_val ('b"01" : mword 2)) with true by (vm_compute; reflexivity).
  vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(* PMP facts of the WRITTEN config/addr: entry 0 of the written pmpcfg is *)
(* TOR + unlocked; the written pmpaddr0 is the CONCRETE 0x3fffffffffffff, *)
(* whose TOR region [0, 0xfffffffffffffc) covers any bounded access.      *)
(* ===================================================================== *)

(* vec_access over vec_update for the pmpaddr vector (64 x mword 64);      *)
(* verbatim clone of WpGprCsrwC.pmpcfg_access_update at the other type.   *)
Lemma pmpaddr_access_update (v : type_of_register pmpaddr_n) (m j : Z) (t : mword 64) :
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
  - apply Z.ltb_lt in Hg.
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

(* entry 0 of the written pmpaddr vector is the concrete legalized value
   (= st_pmpw itself: 54 low bits, all kept). *)
Lemma st_pmpaddr1_entry0 (cfg0 : type_of_register pmpcfg_n)
    (pa0 : type_of_register pmpaddr_n) :
  pmp_all_off cfg0 ->
  vec_access_dec (st_pmpaddr1 cfg0 pa0) 0 = st_pmpw.
Proof.
  intro Hoff.
  unfold st_pmpaddr1, pmp0_newaddr.
  rewrite (pmpaddr_access_update pa0 0 0 _ ltac:(lia)).
  replace (Z.eqb 0 0) with true by reflexivity.
  destruct (Hoff 0) as [_ HL0].
  unfold pmpWriteAddr.
  rewrite HL0.
  assert (HTL : pmpTORLocked (vec_access_dec cfg0 (Z.add 0 1)) = false).
  { destruct (Hoff (Z.add 0 1)) as [_ HL1].
    unfold pmpTORLocked. unfold pmpLocked in HL1. rewrite HL1. reflexivity. }
  rewrite HTL. cbn [orb].
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* entry 0 of the written pmpcfg is TOR + unlocked (byte 0x0f). *)
Lemma st_pmpcfg1_entry0 (cfg0 : type_of_register pmpcfg_n) :
  pmp_all_off cfg0 ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (st_pmpcfg1 cfg0) 0)) = TOR
  /\ pmpLocked (vec_access_dec (st_pmpcfg1 cfg0) 0) = false.
Proof.
  intro Hoff.
  assert (HE : vec_access_dec (st_pmpcfg1 cfg0) 0
               = pmpWriteCfg_val (vec_access_dec cfg0 (Z.add (Z.mul 0 4) 0))
                   (autocast (T := mword)
                      (subrange_vec_dec (mword_of_int 15 : mword 64)
                         (Z.add (Z.mul 8 0) 7) (Z.mul 8 0)))).
  { unfold st_pmpcfg1, pmpcfg_written.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 7) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 7)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 6) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 6)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 5) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 5)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 4) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 4)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 3) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 3)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 2) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 2)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 1) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 1)) with false by reflexivity.
    unfold pmpcfg0_vecupd at 1.
    rewrite (pmpcfg_access_update _ (Z.add (Z.mul 0 4) 0) 0 _ ltac:(lia)).
    replace (Z.eqb 0 (Z.add (Z.mul 0 4) 0)) with true by reflexivity.
    reflexivity. }
  rewrite HE.
  destruct (Hoff (Z.add (Z.mul 0 4) 0)) as [_ HL0].
  unfold pmpWriteCfg_val.
  rewrite HL0.
  split; vm_compute; reflexivity.
Qed.

(* THE data-side PMP fact wp_timerinit needs, for a bounded access. *)
Lemma st_pmp_tor0_grants (cfg0 : type_of_register pmpcfg_n)
    (pa0 : type_of_register pmpaddr_n) (ea : mword 64) (width : Z) :
  pmp_all_off cfg0 ->
  0 < width ->
  uint ea + width <= 0xfffffffffffffc ->
  pmp_tor0_grants (st_pmpcfg1 cfg0) (st_pmpaddr1 cfg0 pa0) ea width.
Proof.
  intros Hoff Hw Hbnd.
  destruct (st_pmpcfg1_entry0 cfg0 Hoff) as [HA HL].
  split; [exact HA | split; [exact HL | split; [exact Hw |]]].
  rewrite (st_pmpaddr1_entry0 cfg0 pa0 Hoff).
  replace (uint st_pmpw) with 0x3fffffffffffff by (vm_compute; reflexivity).
  lia.
Qed.

(* ===================================================================== *)
(* The gpr-file after each register write, as nested-insert abbreviations *)
(* over the abstract entry file [m] (WpTimerinit [ti_m*] style).          *)
(* ===================================================================== *)
Definition st_m30 (m : regfile) (sp0 : mword 64) :=
  <[Regidx csp_rs1 := regval_into_reg (ti_sp1 sp0)]> m.
Definition st_m33 (m : regfile) (sp0 : mword 64) :=
  <[Regidx ti_s0 := regval_into_reg sp0]> (st_m30 m sp0).
Definition st_m34 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg ms0]> (st_m33 m sp0).
Definition st_m35 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg (luival (sign_extend' 20 si35))]> (st_m34 m sp0 ms0).
Definition st_m36 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg st_mask_and]> (st_m35 m sp0 ms0).
Definition st_m37 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (and_vec ms0 st_mask_and)]> (st_m36 m sp0 ms0).
Definition st_m38 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg (luival (sign_extend' 20 si38))]> (st_m37 m sp0 ms0).
Definition st_m39 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg st_mask_or]> (st_m38 m sp0 ms0).
Definition st_m40 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (st_va5_40 ms0)]> (st_m39 m sp0 ms0).
Definition st_m42 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg st_a42v]> (st_m40 m sp0 ms0).
Definition st_m43 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg st_main]> (st_m42 m sp0 ms0).
Definition st_m45 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (mword_of_int 0)]> (st_m43 m sp0 ms0).
Definition st_m47 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (luival (sign_extend' 20 si47))]> (st_m45 m sp0 ms0).
Definition st_m48 (m : regfile) (sp0 ms0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg st_ffff]> (st_m47 m sp0 ms0).
Definition st_m51 (m : regfile) (sp0 ms0 mie0 mdl0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (lower_mie mie0 (st_mdl1 mdl0))]> (st_m48 m sp0 ms0).
Definition st_m52 (m : regfile) (sp0 ms0 mie0 mdl0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (st_va5_52 mie0 mdl0)]> (st_m51 m sp0 ms0 mie0 mdl0).
Definition st_m54 (m : regfile) (sp0 ms0 mie0 mdl0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (cli_wval si54)]> (st_m52 m sp0 ms0 mie0 mdl0).
Definition st_m55 (m : regfile) (sp0 ms0 mie0 mdl0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg st_pmpw]> (st_m54 m sp0 ms0 mie0 mdl0).
Definition st_m57 (m : regfile) (sp0 ms0 mie0 mdl0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (mword_of_int 15)]> (st_m55 m sp0 ms0 mie0 mdl0).
(* register state through the ADUE block (csrr a5,menvcfg; c.li a4,1;
   c.slli a4,0x3d; c.or a5,a4), staged like timerinit's ti_m13..16.  a4/a5 here
   are all overwritten by timerinit, so this feeds the pre-jal map only for the
   (untouched) sp/ra/s0 lookups. *)
Definition st_m_ae0 (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg menv0]> (st_m57 m sp0 ms0 mie0 mdl0).
Definition st_m_ae1 (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg (cli_wval sae_li)]> (st_m_ae0 m sp0 ms0 mie0 mdl0 menv0).
Definition st_m_ae2 (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64) :=
  <[Regidx ti_a4 := regval_into_reg st_adue_bit]> (st_m_ae1 m sp0 ms0 mie0 mdl0 menv0).
Definition st_m_ae3 (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (or_vec menv0 st_adue_bit)]> (st_m_ae2 m sp0 ms0 mie0 mdl0 menv0).
Definition st_m59 (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64) :=
  <[Regidx ti_ra := regval_into_reg st_ra_link]> (st_m_ae3 m sp0 ms0 mie0 mdl0 menv0).
Definition st_mti (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64)
    (mcen0 : mword 32) (mtime0 : mword 64) :=
  ti_mout (st_m59 m sp0 ms0 mie0 mdl0 menv0) (ti_sp1 sp0) (st_menv_adue menv0) mcen0 mtime0 st_ra_link sp0.
Definition st_m60 (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64)
    (mcen0 : mword 32) (mtime0 mh : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg mh]> (st_mti m sp0 ms0 mie0 mdl0 menv0 mcen0 mtime0).
Definition st_m61 (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64)
    (mcen0 : mword 32) (mtime0 mh : mword 64) :=
  <[Regidx ti_a5 := regval_into_reg (st_tpv mh)]> (st_m60 m sp0 ms0 mie0 mdl0 menv0 mcen0 mtime0 mh).
(* the FINAL file: sp = sp0-16 (the still-open start frame), s0 = sp0,
   ra = 0x800000b4, a4 = timerinit's interval, a5 = tp = sext32(mhartid). *)
Definition st_mout (m : regfile) (sp0 ms0 mie0 mdl0 menv0 : mword 64)
    (mcen0 : mword 32) (mtime0 mh : mword 64) :=
  <[Regidx st_tp := regval_into_reg (st_tpv mh)]> (st_m61 m sp0 ms0 mie0 mdl0 menv0 mcen0 mtime0 mh).

(* concrete-register-key disequality + total-lookup driver (ti_look clones). *)
Local Ltac st_reg_neq :=
  let H := fresh in intro H;
  apply (f_equal (fun r : regidx => uint (regidx_bits r))) in H;
  vm_compute in H; discriminate H.

Local Ltac st_look :=
  repeat first [ rewrite upd_eq
               | rewrite upd_ne; [ | st_reg_neq ] ];
  first [ reflexivity | assumption ].

Local Ltac st_unfold :=
  unfold st_mout, st_m61, st_m60, st_mti, st_m59,
         st_m_ae3, st_m_ae2, st_m_ae1, st_m_ae0, st_m57, st_m55, st_m54,
         st_m52, st_m51, st_m48, st_m47, st_m45, st_m43, st_m42, st_m40,
         st_m39, st_m38, st_m37, st_m36, st_m35, st_m34, st_m33, st_m30,
         ti_mout, ti_m27, ti_m26, ti_m24, ti_m23, ti_m22, ti_m21, ti_m19,
         ti_m18, ti_m16, ti_m15, ti_m14, ti_m13, ti_m12, ti_m1.

(* ===================================================================== *)
(* THE THEOREM: the whole start() body (including the timerinit call),   *)
(* one Qed, from [mmode_config (DfracOwn 1)] through the MRET into        *)
(* Supervisor mode at <main> (0x80000e82).                                *)
(* ===================================================================== *)
Section WpStartThm.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* two halves of a register cell rejoin to the full cell. *)
  Lemma reg_half_join (r : register) (v : type_of_register r) :
    r ↦ᵣ{DfracOwn (1/2)} v -∗ r ↦ᵣ{DfracOwn (1/2)} v -∗ r ↦ᵣ v.
  Proof.
    rewrite /reg_pointsto. iIntros "H1 H2".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
    rewrite dfrac_op_own Qp.half_half. iExact "H".
  Qed.

  (* [wp_start]: the whole-function spec over [stack_own_phys sp0 n] (n >= 4 =
     start's own 2-slot frame plus timerinit's 2-slot child frame). *)
  Lemma wp_start (Φ : mval -> iProp Σ)
      (m : regfile) (sp0 ra0 s00 : mword 64)
      (mepc0 satp0 medeleg0 mideleg0 mie0 menvcfg0 stimecmp0 mhartid_in : mword 64)
      (mcounteren0 : mword 32)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (n : nat) :
    (4 <= n)%nat ->
    (* the boot pmpcfg is all-OFF (fetches + the two prologue stores). *)
    pmp_all_off pmpcfg0 ->
    (* Zicfilp landing-pad enable of the initial menvcfg is off (the boot
       flow never sets it), so the MRET target check is a no-op. *)
    _get_MEnvcfg_LPE menvcfg0 = ('b"0") ->
    (* entry register file: sp / ra / s0. *)
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx ti_ra = ra0 ->
    m !!! Regidx ti_s0 = s00 ->
    (* timerinit's frame slots: inside the written TOR region
       [0, 0xfffffffffffffc). *)
    uint (ti_ea_ra (ti_sp1 sp0)) + 8 <= 0xfffffffffffffc ->
    uint (ti_ea_s0 (ti_sp1 sp0)) + 8 <= 0xfffffffffffffc ->
    mmode_config (DfracOwn 1) -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pc_is st_pc30 -∗
    gpr_file m -∗
    mhartid ↦ᵣ mhartid_in -∗
    mepc ↦ᵣ mepc0 -∗
    satp ↦ᵣ satp0 -∗
    medeleg ↦ᵣ medeleg0 -∗
    mideleg ↦ᵣ mideleg0 -∗
    mie ↦ᵣ mie0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    mcounteren ↦ᵣ mcounteren0 -∗
    stimecmp ↦ᵣ stimecmp0 -∗
    (* start's 4-slot stack region (own ra/s0 + child timerinit's ra/s0)
       as the bottom four slots of [stack_own_phys sp0 n] (any depth n >= 4). *)
    stack_own_phys sp0 n -∗
    kernel_text -∗
    (* the continuation is universally quantified over the (hidden) entry
       mstatus value [ms0] with its mmode_config invariant facts. *)
    ( ∀ (tv : mword 64) (ms0 : mword 64)
        (HoIE : eq_vec (_get_Mstatus_MIE ms0) ('b"1") = false)
        (HoPRV : eq_vec (_get_Mstatus_MPRV ms0) ('b"1") = false)
        (HoSXL : _get_Mstatus_SXL ms0 = ('b"10")),
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗
      mstatus ↦ᵣ cms5 (st_ms1 ms0) -∗
      pmpcfg_n ↦ᵣ st_pmpcfg1 pmpcfg0 -∗
      pmpaddr_n ↦ᵣ st_pmpaddr1 pmpcfg0 pmpaddr00 -∗
      pc_is st_main -∗
      gpr_file (st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in) -∗
      mhartid ↦ᵣ mhartid_in -∗
      mepc ↦ᵣ st_main -∗
      satp ↦ᵣ satp_legalized satp0 (mword_of_int 0) -∗
      medeleg ↦ᵣ legalize_medeleg medeleg0 st_ffff -∗
      mideleg ↦ᵣ st_mdl1 mideleg0 -∗
      mie ↦ᵣ st_mie1 mie0 mideleg0 -∗
      menvcfg ↦ᵣ menvcfg_legalized (st_menv_adue menvcfg0) (ti_menv1 (st_menv_adue menvcfg0)) -∗
      mcounteren ↦ᵣ legalize_mcounteren mcounteren0 (ti_mcen1 mcounteren0) -∗
      stimecmp ↦ᵣ stimecmp_legalized stimecmp0 (ti_deadline tv) -∗
      stack_own_phys sp0 n -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros Hn4 Hpmp HlpeE Hsp Hra Hs0 Hbnd_ra Hbnd_s0.
    iIntros "Hmm Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv Hmcen Hstc Hstk #Htext Hcont".
    iDestruct (stack_own_phys_split_1 sp0 4 n ltac:(lia) with "Hstk") as "[Htop Hdeep]".
    iDestruct (stack_own_phys_split_1 sp0 2 4 ltac:(lia) with "Htop") as "[Ht12 Ht34]".
    iDestruct (stack_own_phys_2_elim with "Ht12") as (vsra vss0) "[Hsra Hss0]".
    iDestruct (stack_own_phys_2_elim with "Ht34") as (vtra vts0) "[Htra Hts0]".
    iEval (rewrite (pa_stk_assoc sp0 2 1)) in "Htra".
    iEval (rewrite (pa_stk_assoc sp0 2 2)) in "Hts0".
    assert (Hb1 : ti_ea_ra sp0 = pa_stk sp0 1).
    { unfold ti_ea_ra, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : ti_ea_s0 sp0 = pa_stk sp0 2).
    { unfold ti_ea_s0, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : ti_ea_ra (ti_sp1 sp0) = pa_stk sp0 3).
    { unfold ti_ea_ra, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : ti_ea_s0 (ti_sp1 sp0) = pa_stk sp0 4).
    { unfold ti_ea_s0, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hsra". iEval (rewrite -Hb2) in "Hss0".
    iEval (rewrite -Hb3) in "Htra". iEval (rewrite -Hb4) in "Hts0".
    (* the 34 [instr] facts, off the persistent text image *)
    iPoseProof (st_instr30 with "Htext") as "Hi30".
    iPoseProof (st_instr31 with "Htext") as "Hi31".
    iPoseProof (st_instr32 with "Htext") as "Hi32".
    iPoseProof (st_instr33 with "Htext") as "Hi33".
    iPoseProof (st_instr34 with "Htext") as "Hi34".
    iPoseProof (st_instr35 with "Htext") as "Hi35".
    iPoseProof (st_instr36 with "Htext") as "Hi36".
    iPoseProof (st_instr37 with "Htext") as "Hi37".
    iPoseProof (st_instr38 with "Htext") as "Hi38".
    iPoseProof (st_instr39 with "Htext") as "Hi39".
    iPoseProof (st_instr40 with "Htext") as "Hi40".
    iPoseProof (st_instr41 with "Htext") as "Hi41".
    iPoseProof (st_instr42 with "Htext") as "Hi42".
    iPoseProof (st_instr43 with "Htext") as "Hi43".
    iPoseProof (st_instr44 with "Htext") as "Hi44".
    iPoseProof (st_instr45 with "Htext") as "Hi45".
    iPoseProof (st_instr46 with "Htext") as "Hi46".
    iPoseProof (st_instr47 with "Htext") as "Hi47".
    iPoseProof (st_instr48 with "Htext") as "Hi48".
    iPoseProof (st_instr49 with "Htext") as "Hi49".
    iPoseProof (st_instr50 with "Htext") as "Hi50".
    iPoseProof (st_instr51 with "Htext") as "Hi51".
    iPoseProof (st_instr52 with "Htext") as "Hi52".
    iPoseProof (st_instr53 with "Htext") as "Hi53".
    iPoseProof (st_instr54 with "Htext") as "Hi54".
    iPoseProof (st_instr55 with "Htext") as "Hi55".
    iPoseProof (st_instr56 with "Htext") as "Hi56".
    iPoseProof (st_instr57 with "Htext") as "Hi57".
    iPoseProof (st_instr58 with "Htext") as "Hi58".
    iPoseProof (st_instr_ae0 with "Htext") as "Hiae0".
    iPoseProof (st_instr_ae1 with "Htext") as "Hiae1".
    iPoseProof (st_instr_ae2 with "Htext") as "Hiae2".
    iPoseProof (st_instr_ae3 with "Htext") as "Hiae3".
    iPoseProof (st_instr_ae4 with "Htext") as "Hiae4".
    iPoseProof (st_instr59 with "Htext") as "Hi59".
    iPoseProof (st_instr60 with "Htext") as "Hi60".
    iPoseProof (st_instr61 with "Htext") as "Hi61".
    iPoseProof (st_instr62 with "Htext") as "Hi62".
    iPoseProof (st_instr63 with "Htext") as "Hi63".
    (* pure side conditions *)
    pose proof (pmp_all_off_allows_all _ Hpmp) as HpmpU.
    assert (Hpmp1 : pmp_allows_all (st_pmpcfg1 pmpcfg0))
      by (apply pmp_allows_all_written; exact HpmpU).
    assert (Htor_ra : pmp_tor0_grants (st_pmpcfg1 pmpcfg0) (st_pmpaddr1 pmpcfg0 pmpaddr00)
                        (ti_ea_ra (ti_sp1 sp0)) 8)
      by (apply st_pmp_tor0_grants; [exact Hpmp | lia | exact Hbnd_ra]).
    assert (Htor_s0 : pmp_tor0_grants (st_pmpcfg1 pmpcfg0) (st_pmpaddr1 pmpcfg0 pmpaddr00)
                        (ti_ea_s0 (ti_sp1 sp0)) 8)
      by (apply st_pmp_tor0_grants; [exact Hpmp | lia | exact Hbnd_s0]).
    assert (Hnz_sp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    assert (Hnz_ra : uint ti_ra <> 0) by (vm_compute; discriminate).
    assert (Hnz_s0 : uint ti_s0 <> 0) by (vm_compute; discriminate).
    assert (Hnz_a4 : uint ti_a4 <> 0) by (vm_compute; discriminate).
    assert (Hnz_a5 : uint ti_a5 <> 0) by (vm_compute; discriminate).
    assert (Hnz_tp : uint st_tp <> 0) by (vm_compute; discriminate).
    assert (Hcs0 : creg2reg_idx ti_cs0 = Regidx ti_s0) by (vm_compute; reflexivity).
    assert (Hca5 : creg2reg_idx ti_ca5 = Regidx ti_a5) by (vm_compute; reflexivity).
    assert (Hca4 : creg2reg_idx ti_ca4 = Regidx ti_a4) by (vm_compute; reflexivity).
    (* PC steps *)
    assert (P30 : add_vec_int st_pc30 2 = st_pc31) by (vm_compute; reflexivity).
    assert (P31 : add_vec_int st_pc31 2 = st_pc32) by (vm_compute; reflexivity).
    assert (P32 : add_vec_int st_pc32 2 = st_pc33) by (vm_compute; reflexivity).
    assert (P33 : add_vec_int st_pc33 2 = st_pc34) by (vm_compute; reflexivity).
    assert (P34 : add_vec_int st_pc34 4 = st_pc35) by (vm_compute; reflexivity).
    assert (P35 : add_vec_int st_pc35 2 = st_pc36) by (vm_compute; reflexivity).
    assert (P36 : add_vec_int st_pc36 4 = st_pc37) by (vm_compute; reflexivity).
    assert (P37 : add_vec_int st_pc37 2 = st_pc38) by (vm_compute; reflexivity).
    assert (P38 : add_vec_int st_pc38 2 = st_pc39) by (vm_compute; reflexivity).
    assert (P39 : add_vec_int st_pc39 4 = st_pc40) by (vm_compute; reflexivity).
    assert (P40 : add_vec_int st_pc40 2 = st_pc41) by (vm_compute; reflexivity).
    assert (P41 : add_vec_int st_pc41 4 = st_pc42) by (vm_compute; reflexivity).
    assert (P42 : add_vec_int st_pc42 4 = st_pc43) by (vm_compute; reflexivity).
    assert (P43 : add_vec_int st_pc43 4 = st_pc44) by (vm_compute; reflexivity).
    assert (P44 : add_vec_int st_pc44 4 = st_pc45) by (vm_compute; reflexivity).
    assert (P45 : add_vec_int st_pc45 2 = st_pc46) by (vm_compute; reflexivity).
    assert (P46 : add_vec_int st_pc46 4 = st_pc47) by (vm_compute; reflexivity).
    assert (P47 : add_vec_int st_pc47 2 = st_pc48) by (vm_compute; reflexivity).
    assert (P48 : add_vec_int st_pc48 2 = st_pc49) by (vm_compute; reflexivity).
    assert (P49 : add_vec_int st_pc49 4 = st_pc50) by (vm_compute; reflexivity).
    assert (P50 : add_vec_int st_pc50 4 = st_pc51) by (vm_compute; reflexivity).
    assert (P51 : add_vec_int st_pc51 4 = st_pc52) by (vm_compute; reflexivity).
    assert (P52 : add_vec_int st_pc52 4 = st_pc53) by (vm_compute; reflexivity).
    assert (P53 : add_vec_int st_pc53 4 = st_pc54) by (vm_compute; reflexivity).
    assert (P54 : add_vec_int st_pc54 2 = st_pc55) by (vm_compute; reflexivity).
    assert (P55 : add_vec_int st_pc55 2 = st_pc56) by (vm_compute; reflexivity).
    assert (P56 : add_vec_int st_pc56 4 = st_pc57) by (vm_compute; reflexivity).
    assert (P57 : add_vec_int st_pc57 2 = st_pc58) by (vm_compute; reflexivity).
    assert (P58 : add_vec_int st_pc58 4 = st_pc_ae0) by (vm_compute; reflexivity).
    assert (Pae0 : add_vec_int st_pc_ae0 4 = st_pc_ae1) by (vm_compute; reflexivity).
    assert (Pae1 : add_vec_int st_pc_ae1 2 = st_pc_ae2) by (vm_compute; reflexivity).
    assert (Pae2 : add_vec_int st_pc_ae2 2 = st_pc_ae3) by (vm_compute; reflexivity).
    assert (Pae3 : add_vec_int st_pc_ae3 2 = st_pc_ae4) by (vm_compute; reflexivity).
    assert (Pae4 : add_vec_int st_pc_ae4 4 = st_pc59) by (vm_compute; reflexivity).
    assert (P59 : add_vec st_pc59 (sign_extend' 64 sjimm59) = ti_pc9)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (P60 : add_vec_int st_pc60 4 = st_pc61) by (vm_compute; reflexivity).
    assert (P61 : add_vec_int st_pc61 2 = st_pc62) by (vm_compute; reflexivity).
    assert (P62 : add_vec_int st_pc62 2 = st_pc63) by (vm_compute; reflexivity).
    (* closed-value bridges *)
    assert (Hm1v : add_vec (luival (sign_extend' 20 si35)) (sign_extend' 64 si36) = st_mask_and)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hm2v : add_vec (luival (sign_extend' 20 si38)) (sign_extend' 64 si39) = st_mask_or)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ha42v : add_vec st_pc42 (auipc_off si42) = st_a42v)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ha43v : add_vec st_a42v (sign_extend' 64 si43) = st_main)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hmepcv : mepc_val st_main = st_main)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hz45 : sign_extend' 64 si45 = (mword_of_int 0 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hffv : add_vec (luival (sign_extend' 20 si47)) (sign_extend' 64 si48) = st_ffff)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hshv : shift_bits_right (cli_wval si54)
                     (subrange_vec_dec ssh55 (Z.sub log2_xlen 1) 0) = st_pmpw)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (H15v : sign_extend' 64 si57 = (mword_of_int 15 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlinkv : add_vec_int st_pc59 4 = st_ra_link) by (vm_compute; reflexivity).
    assert (Hjal_al : is_aligned_paddr (Physaddr (add_vec st_pc59 (sign_extend' 64 sjimm59))) 4 = true)
      by (vm_compute; reflexivity).
    assert (Hcretv : ret_pc st_ra_link = st_pc60)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Hctgtv : ret_pc st_main = st_main)
      by (apply bv_eq; vm_compute; reflexivity).
    pose proof (st_s0_16 sp0) as Hs016.

    (* ---- unbundle the FULL config once, naming the entry mstatus [ms0];
       split all cells in half: a working bundle at 1/2 + pinned halves. ---- *)
    iDestruct (mmode_config_unbundle with "Hmm") as "(#Hhw & #Hinv & Hhs & Hpriv & Hmst)".
    iDestruct "Hmst" as (ms0) "(Hms & %HoIE & %HoPRV & %HoSXL)".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) ms0 HoIE HoPRV HoSXL
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".
    (* invariant facts of the post-csrw mstatus value *)
    assert (HmIE1 : eq_vec (_get_Mstatus_MIE (st_ms1 ms0)) ('b"1") = false).
    { unfold st_ms1. rewrite mstatus_legalized_MIE. rewrite st_va5_40_MIE. exact HoIE. }
    assert (HMPRV1 : eq_vec (_get_Mstatus_MPRV (st_ms1 ms0)) ('b"1") = false).
    { unfold st_ms1. rewrite mstatus_legalized_MPRV. rewrite st_va5_40_MPRV. exact HoPRV. }
    assert (HSXL1 : _get_Mstatus_SXL (st_ms1 ms0) = ('b"10")).
    { unfold st_ms1. rewrite mstatus_legalized_SXL. exact HoSXL. }

    (* ---- 30. c.addi sp, -16 ---- *)
    iApply (wp_addi_gpr Φ st_pc30 true csp_rs1 csp_rs1 (sign_extend' 12 i9) m pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_sp
              with "Hmm HpcfA Hpc Hfile Hi30").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P30).
    iIntros "Hmm HpcfA Hpc Hfile".
    iEval (rewrite sext6_12_64 Hsp) in "Hfile".
    iEval (change (<[Regidx csp_rs1 := regval_into_reg (add_vec sp0 (sign_extend' 64 i9))]> m)
             with (st_m30 m sp0)) in "Hfile".

    (* ---- 31. c.sdsp ra, 8(sp) ---- *)
    assert (L31sp : st_m30 m sp0 !!! Regidx csp_rs1 = ti_sp1 sp0) by (st_unfold; st_look).
    assert (L31ra : st_m30 m sp0 !!! Regidx ti_ra = ra0) by (st_unfold; st_look).
    assert (Hea31 : add_vec (st_m30 m sp0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u10 ('b"000")))) = ti_ea_ra sp0)
      by (rewrite L31sp; reflexivity).
    iApply (wp_store_gpr Φ st_pc31 true csp_rs1 ti_ra
              (zero_extend' 12 (concat_vec u10 ('b"000"))) (st_m30 m sp0) vsra pmpcfg0 (1/2)%Qp
              Hpmp ltac:(boot_static) with "Hmm HpcfA Hpc Hfile Hi31 [Hsra]").
    { rewrite Hea31. iExact "Hsra". }
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P31 Hea31 L31ra).
    iIntros "Hmm HpcfA Hpc Hfile Hsra".

    (* ---- 32. c.sdsp s0, 0(sp) ---- *)
    assert (L32s0 : st_m30 m sp0 !!! Regidx ti_s0 = s00) by (st_unfold; st_look).
    assert (Hea32 : add_vec (st_m30 m sp0 !!! Regidx csp_rs1)
              (sign_extend' 64 (zero_extend' 12 (concat_vec u11 ('b"000")))) = ti_ea_s0 sp0)
      by (rewrite L31sp; reflexivity).
    iApply (wp_store_gpr Φ st_pc32 true csp_rs1 ti_s0
              (zero_extend' 12 (concat_vec u11 ('b"000"))) (st_m30 m sp0) vss0 pmpcfg0 (1/2)%Qp
              Hpmp ltac:(boot_static) with "Hmm HpcfA Hpc Hfile Hi32 [Hss0]").
    { rewrite Hea32. iExact "Hss0". }
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P32 Hea32 L32s0).
    iIntros "Hmm HpcfA Hpc Hfile Hss0".

    (* ---- 33. c.addi4spn s0, sp, 16 (s0 := sp0) ---- *)
    iApply (wp_addi_gpr Φ st_pc33 true csp_rs1 ti_s0 (caddi4spn_imm nz12) (st_m30 m sp0)
              pmpcfg0 (1/2)%Qp HpmpU ltac:(boot_static) Hnz_s0 with "Hmm HpcfA Hpc Hfile Hi33").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P33 L31sp Hs016). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_s0 := regval_into_reg sp0]> (st_m30 m sp0))
             with (st_m33 m sp0)) in "Hfile".

    (* ---- 34. csrr a5, mstatus (reads the PINNED outside half) ---- *)
    iApply (wp_csrr_mstatus_gpr Φ st_pc34 ti_a5 ms0 (st_m33 m sp0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile HmsK Hi34").
    iEval (rewrite P34). iIntros "Hmm HpcfA Hpc Hfile HmsK".
    iEval (change (<[Regidx ti_a5 := regval_into_reg ms0]> (st_m33 m sp0))
             with (st_m34 m sp0 ms0)) in "Hfile".

    (* ---- 35. c.lui a4, 0xffffe ---- *)
    iApply (wp_lui_gpr Φ st_pc35 true ti_a4 (sign_extend' 20 si35) (st_m34 m sp0 ms0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a4 with "Hmm HpcfA Hpc Hfile Hi35").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P35). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (luival (sign_extend' 20 si35))]>
                     (st_m34 m sp0 ms0))
             with (st_m35 m sp0 ms0)) in "Hfile".

    (* ---- 36. addi a4, a4, 2047 (a4 := 0xffffffffffffe7ff) ---- *)
    assert (L36a4 : st_m35 m sp0 ms0 !!! Regidx ti_a4 = luival (sign_extend' 20 si35))
      by (st_unfold; st_look).
    iApply (wp_addi_gpr Φ st_pc36 false ti_a4 ti_a4 si36 (st_m35 m sp0 ms0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a4 with "Hmm HpcfA Hpc Hfile Hi36").
    iEval (change (if false then 2%Z else 4%Z) with 4%Z). iEval (rewrite P36 L36a4 Hm1v). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg st_mask_and]> (st_m35 m sp0 ms0))
             with (st_m36 m sp0 ms0)) in "Hfile".

    (* ---- 37. c.and a5, a4 ---- *)
    assert (L37a5 : st_m36 m sp0 ms0 !!! Regidx ti_a5 = ms0) by (st_unfold; st_look).
    assert (L37a4 : st_m36 m sp0 ms0 !!! Regidx ti_a4 = st_mask_and) by (st_unfold; st_look).
    iApply (wp_and_gpr Φ st_pc37 true ti_a4 ti_a5 ti_a5 (st_m36 m sp0 ms0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hi37").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P37 L37a5 L37a4). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (and_vec ms0 st_mask_and)]> (st_m36 m sp0 ms0))
             with (st_m37 m sp0 ms0)) in "Hfile".

    (* ---- 38. c.lui a4, 1 ---- *)
    iApply (wp_lui_gpr Φ st_pc38 true ti_a4 (sign_extend' 20 si38) (st_m37 m sp0 ms0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a4 with "Hmm HpcfA Hpc Hfile Hi38").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P38). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (luival (sign_extend' 20 si38))]>
                     (st_m37 m sp0 ms0))
             with (st_m38 m sp0 ms0)) in "Hfile".

    (* ---- 39. addi a4, a4, -2048 (a4 := 0x800) ---- *)
    assert (L39a4 : st_m38 m sp0 ms0 !!! Regidx ti_a4 = luival (sign_extend' 20 si38))
      by (st_unfold; st_look).
    iApply (wp_addi_gpr Φ st_pc39 false ti_a4 ti_a4 si39 (st_m38 m sp0 ms0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a4 with "Hmm HpcfA Hpc Hfile Hi39").
    iEval (change (if false then 2%Z else 4%Z) with 4%Z). iEval (rewrite P39 L39a4 Hm2v). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg st_mask_or]> (st_m38 m sp0 ms0))
             with (st_m39 m sp0 ms0)) in "Hfile".

    (* ---- 40. c.or a5, a4 (a5 := the mstatus write mask value) ---- *)
    assert (L40a5 : st_m39 m sp0 ms0 !!! Regidx ti_a5 = and_vec ms0 st_mask_and) by (st_unfold; st_look).
    assert (L40a4 : st_m39 m sp0 ms0 !!! Regidx ti_a4 = st_mask_or) by (st_unfold; st_look).
    iApply (wp_or_gpr Φ st_pc40 true ti_a4 ti_a5 ti_a5 (st_m39 m sp0 ms0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hi40").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P40 L40a5 L40a4). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (or_vec (and_vec ms0 st_mask_and) st_mask_or)]>
                     (st_m39 m sp0 ms0))
             with (st_m40 m sp0 ms0)) in "Hfile".

    (* ---- 41. csrw mstatus, a5: recombine to FULL raw cells and run the
       RAW config-writing WP; the value stays a single symbol. ---- *)
    assert (L41a5 : st_m40 m sp0 ms0 !!! Regidx ti_a5 = st_va5_40 ms0) by (st_unfold; st_look).
    iDestruct (mmode_config_unbundle with "Hmm") as "(_ & _ & HhsA & HprivA & HmstA)".
    iDestruct "HmstA" as (ms0') "(HmsA & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "HmsA HmsK") as %->.
    iDestruct (reg_half_join with "HhsA HhsK") as "Hhs".
    iDestruct (reg_half_join with "HprivA HprivK") as "Hpriv".
    iDestruct (reg_half_join with "HmsA HmsK") as "Hms".
    iDestruct (reg_half_join with "HpcfA HpcfK") as "Hpcf".
    iApply (wp_csrw_mstatus_raw Φ st_pc41 ti_a5 (st_m40 m sp0 ms0) ms0 pmpcfg0
              HpmpU ltac:(boot_static) HoIE
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hfile Hi41").
    iEval (rewrite P41 L41a5).
    iIntros "Hhs Hpriv Hms Hpcf Hpc Hfile".
    iEval (change (mstatus_legalized ms0 (st_va5_40 ms0)) with (st_ms1 ms0)) in "Hms".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) (st_ms1 ms0) HmIE1 HMPRV1 HSXL1
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".

    (* ---- 42. auipc a5, 1 ---- *)
    iApply (wp_auipc_gpr Φ st_pc42 ti_a5 si42 (st_m40 m sp0 ms0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hi42").
    iEval (rewrite P42 Ha42v). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_a42v]> (st_m40 m sp0 ms0))
             with (st_m42 m sp0 ms0)) in "Hfile".

    (* ---- 43. addi a5, a5, -502 (a5 := <main>) ---- *)
    assert (L43a5 : st_m42 m sp0 ms0 !!! Regidx ti_a5 = st_a42v) by (st_unfold; st_look).
    iApply (wp_addi_gpr Φ st_pc43 false ti_a5 ti_a5 si43 (st_m42 m sp0 ms0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hi43").
    iEval (change (if false then 2%Z else 4%Z) with 4%Z). iEval (rewrite P43 L43a5 Ha43v). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_main]> (st_m42 m sp0 ms0))
             with (st_m43 m sp0 ms0)) in "Hfile".

    (* ---- 44. csrw mepc, a5 ---- *)
    assert (L44a5 : st_m43 m sp0 ms0 !!! Regidx ti_a5 = st_main) by (st_unfold; st_look).
    iApply (wp_csrw_mepc_gpr Φ st_pc44 ti_a5 (st_m43 m sp0 ms0) mepc0 pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hmepc Hi44").
    iEval (rewrite P44 L44a5 Hmepcv). iIntros "Hmm HpcfA Hpc Hfile Hmepc".

    (* ---- 45. c.li a5, 0 ---- *)
    iDestruct (gpr_file_x0 (st_m43 m sp0 ms0) cli_rs1 ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0_45 Hfile]".
    iApply (wp_addi_gpr Φ st_pc45 true cli_rs1 ti_a5 (sign_extend' 12 si45) (st_m43 m sp0 ms0)
              pmpcfg0 (1/2)%Qp HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hi45").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite sext6_12_64 P45 Hx0_45 add_vec_zero_l Hz45). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (mword_of_int 0)]> (st_m43 m sp0 ms0))
             with (st_m45 m sp0 ms0)) in "Hfile".

    (* ---- 46. csrw satp, a5 (Bare) ---- *)
    assert (L46a5 : st_m45 m sp0 ms0 !!! Regidx ti_a5 = (mword_of_int 0 : mword 64)) by (st_unfold; st_look).
    iApply (wp_csrw_satp_gpr Φ st_pc46 ti_a5 (st_m45 m sp0 ms0) satp0 pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hsatp Hi46").
    iEval (rewrite P46 L46a5). iIntros "Hmm HpcfA Hpc Hfile Hsatp".

    (* ---- 47. c.lui a5, 0x10 ---- *)
    iApply (wp_lui_gpr Φ st_pc47 true ti_a5 (sign_extend' 20 si47) (st_m45 m sp0 ms0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hi47").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P47). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (luival (sign_extend' 20 si47))]>
                     (st_m45 m sp0 ms0))
             with (st_m47 m sp0 ms0)) in "Hfile".

    (* ---- 48. c.addi a5, -1 (a5 := 0xffff) ---- *)
    assert (L48a5 : st_m47 m sp0 ms0 !!! Regidx ti_a5 = luival (sign_extend' 20 si47))
      by (st_unfold; st_look).
    iApply (wp_addi_gpr Φ st_pc48 true ti_a5 ti_a5 (sign_extend' 12 si48) (st_m47 m sp0 ms0)
              pmpcfg0 (1/2)%Qp HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hi48").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite sext6_12_64 P48 L48a5 Hffv). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_ffff]> (st_m47 m sp0 ms0))
             with (st_m48 m sp0 ms0)) in "Hfile".

    (* ---- 49. csrw medeleg, a5 ---- *)
    assert (L49a5 : st_m48 m sp0 ms0 !!! Regidx ti_a5 = st_ffff) by (st_unfold; st_look).
    iApply (wp_csrw_medeleg_gpr Φ st_pc49 ti_a5 (st_m48 m sp0 ms0) medeleg0 pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hmede Hi49").
    iEval (rewrite P49 L49a5). iIntros "Hmm HpcfA Hpc Hfile Hmede".

    (* ---- 50. csrw mideleg, a5 ---- *)
    iApply (wp_csrw_mideleg_gpr Φ st_pc50 ti_a5 (st_m48 m sp0 ms0) mideleg0 pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hmdl Hi50").
    iEval (rewrite P50 L49a5). iIntros "Hmm HpcfA Hpc Hfile Hmdl".
    iEval (change (mideleg_legalized mideleg0 st_ffff) with (st_mdl1 mideleg0)) in "Hmdl".

    (* ---- 51. csrr a5, sie (view over mie & mideleg) ---- *)
    iApply (wp_csrr_sie_gpr Φ st_pc51 ti_a5 mie0 (st_mdl1 mideleg0) (st_m48 m sp0 ms0)
              pmpcfg0 (1/2)%Qp HpmpU ltac:(boot_static) Hnz_a5
              with "Hmm HpcfA Hpc Hfile Hmie Hmdl Hi51").
    iEval (rewrite P51). iIntros "Hmm HpcfA Hpc Hfile Hmie Hmdl".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (lower_mie mie0 (st_mdl1 mideleg0))]>
                     (st_m48 m sp0 ms0))
             with (st_m51 m sp0 ms0 mie0 mideleg0)) in "Hfile".

    (* ---- 52. ori a5, a5, 544 ---- *)
    assert (L52a5 : st_m51 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5
                    = lower_mie mie0 (st_mdl1 mideleg0)) by (st_unfold; st_look).
    iApply (wp_ori_gpr Φ st_pc52 ti_a5 ti_a5 si52 (st_m51 m sp0 ms0 mie0 mideleg0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hi52").
    iEval (rewrite P52 L52a5). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg
                      (or_vec (lower_mie mie0 (st_mdl1 mideleg0)) (sign_extend' 64 si52))]>
                     (st_m51 m sp0 ms0 mie0 mideleg0))
             with (st_m52 m sp0 ms0 mie0 mideleg0)) in "Hfile".

    (* ---- 53. csrw sie, a5 ---- *)
    assert (L53a5 : st_m52 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5
                    = st_va5_52 mie0 mideleg0) by (st_unfold; st_look).
    iApply (wp_csrw_sie_gpr Φ st_pc53 ti_a5 (st_m52 m sp0 ms0 mie0 mideleg0)
              mie0 (st_mdl1 mideleg0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hmie Hmdl Hi53").
    iEval (rewrite P53 L53a5). iIntros "Hmm HpcfA Hpc Hfile Hmie Hmdl".
    iEval (change (sie_new_mie mie0 (st_mdl1 mideleg0) (st_va5_52 mie0 mideleg0))
             with (st_mie1 mie0 mideleg0)) in "Hmie".

    (* ---- 54. c.li a5, -1 ---- *)
    iDestruct (gpr_file_x0 (st_m52 m sp0 ms0 mie0 mideleg0) cli_rs1 ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0_54 Hfile]".
    iApply (wp_addi_gpr Φ st_pc54 true cli_rs1 ti_a5 (sign_extend' 12 si54)
              (st_m52 m sp0 ms0 mie0 mideleg0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hi54").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite sext6_12_64 P54 Hx0_54 add_vec_zero_l). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (cli_wval si54)]>
                     (st_m52 m sp0 ms0 mie0 mideleg0))
             with (st_m54 m sp0 ms0 mie0 mideleg0)) in "Hfile".

    (* ---- 55. c.srli a5, 10 (a5 := 0x3fffffffffffff) ---- *)
    assert (L55a5 : st_m54 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5 = cli_wval si54)
      by (st_unfold; st_look).
    iApply (wp_srli_gpr Φ st_pc55 true ti_a5 ti_a5 ssh55 (st_m54 m sp0 ms0 mie0 mideleg0)
              pmpcfg0 (1/2)%Qp HpmpU ltac:(boot_static) Hnz_a5
              with "Hmm HpcfA Hpc Hfile Hi55").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z). iEval (rewrite P55 L55a5 Hshv). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg st_pmpw]> (st_m54 m sp0 ms0 mie0 mideleg0))
             with (st_m55 m sp0 ms0 mie0 mideleg0)) in "Hfile".

    (* ---- 56. csrw pmpaddr0, a5 ---- *)
    assert (L56a5 : st_m55 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5 = st_pmpw)
      by (st_unfold; st_look).
    iApply (wp_csrw_pmpaddr0_gpr Φ st_pc56 ti_a5 (st_m55 m sp0 ms0 mie0 mideleg0)
              pmpaddr00 pmpcfg0 (1/2)%Qp HpmpU ltac:(boot_static) Hnz_a5
              with "Hmm HpcfA Hpc Hfile Hpaddr Hi56").
    iEval (rewrite P56 L56a5). iIntros "Hmm HpcfA Hpc Hfile Hpaddr".
    iEval (change (pmp0_newaddr pmpcfg0 pmpaddr00 st_pmpw)
             with (st_pmpaddr1 pmpcfg0 pmpaddr00)) in "Hpaddr".

    (* ---- 57. c.li a5, 15 ---- *)
    iDestruct (gpr_file_x0 (st_m55 m sp0 ms0 mie0 mideleg0) cli_rs1 ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0_57 Hfile]".
    iApply (wp_addi_gpr Φ st_pc57 true cli_rs1 ti_a5 (sign_extend' 12 si57)
              (st_m55 m sp0 ms0 mie0 mideleg0) pmpcfg0 (1/2)%Qp
              HpmpU ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hi57").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite sext6_12_64 P57 Hx0_57 add_vec_zero_l H15v). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (mword_of_int 15)]>
                     (st_m55 m sp0 ms0 mie0 mideleg0))
             with (st_m57 m sp0 ms0 mie0 mideleg0)) in "Hfile".

    (* ---- 58. csrw pmpcfg0, a5: recombine to FULL and run the RAW WP. ---- *)
    assert (L58a5 : st_m57 m sp0 ms0 mie0 mideleg0 !!! Regidx ti_a5 = (mword_of_int 15 : mword 64))
      by (st_unfold; st_look).
    iDestruct (mmode_config_unbundle with "Hmm") as "(_ & _ & HhsA & HprivA & HmstA)".
    iDestruct "HmstA" as (ms1') "(HmsA & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "HmsA HmsK") as %->.
    iDestruct (reg_half_join with "HhsA HhsK") as "Hhs".
    iDestruct (reg_half_join with "HprivA HprivK") as "Hpriv".
    iDestruct (reg_half_join with "HmsA HmsK") as "Hms".
    iDestruct (reg_half_join with "HpcfA HpcfK") as "Hpcf".
    iApply (wp_csrw_pmpcfg0_raw Φ st_pc58 ti_a5 (st_m57 m sp0 ms0 mie0 mideleg0)
              (st_ms1 ms0) pmpcfg0 HpmpU ltac:(boot_static) HmIE1
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hpc Hfile Hi58").
    iEval (rewrite P58 L58a5).
    iIntros "Hhs Hpriv Hms Hpcf Hpc Hfile".
    iEval (change (pmpcfg_written (mword_of_int 15) pmpcfg0) with (st_pmpcfg1 pmpcfg0)) in "Hpcf".
    iDestruct "Hhs" as "[HhsA HhsK]".
    iDestruct "Hpriv" as "[HprivA HprivK]".
    iDestruct "Hms" as "[HmsA HmsK]".
    iDestruct "Hpcf" as "[HpcfA HpcfK]".
    iPoseProof (mmode_config_rebuild (DfracOwn (1/2)) (st_ms1 ms0) HmIE1 HMPRV1 HSXL1
                  with "Hhw Hinv HhsA HprivA HmsA") as "Hmm".

    (* ---- ADUE write: [menvcfg |= 1<<61] (start+0x58..0x62) ---- *)
    (* ae0: csrr a5, menvcfg  (a5 := menvcfg0) *)
    iApply (wp_csrr_menvcfg_gpr Φ st_pc_ae0 ti_a5 menvcfg0 (st_m57 m sp0 ms0 mie0 mideleg0)
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hpmp1 ltac:(boot_static) Hnz_a5
              with "Hmm HpcfA Hpc Hfile Hmenv Hiae0").
    iEval (rewrite Pae0). iIntros "Hmm HpcfA Hpc Hfile Hmenv".
    iEval (change (<[Regidx ti_a5 := regval_into_reg menvcfg0]> (st_m57 m sp0 ms0 mie0 mideleg0))
             with (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    (* ae1: c.li a4, 1  (a4 := 1) *)
    iDestruct (gpr_file_x0 (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0) cli_rs1 ltac:(vm_compute; reflexivity)
                 with "Hfile") as "[%Hx0_ae1 Hfile]".
    iApply (wp_addi_gpr Φ st_pc_ae1 true cli_rs1 ti_a4 (sign_extend' 12 sae_li)
              (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0) (st_pmpcfg1 pmpcfg0) (1/2)%Qp
              Hpmp1 ltac:(boot_static) Hnz_a4 with "Hmm HpcfA Hpc Hfile Hiae1").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite Pae1 Hx0_ae1 add_vec_zero_l sext6_12_64). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg (cli_wval sae_li)]> (st_m_ae0 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    (* ae2: c.slli a4, 0x3d  (a4 := 1<<61) *)
    assert (L_ae2a4 : st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a4 = cli_wval sae_li)
      by (st_unfold; st_look).
    iApply (wp_slli_gpr Φ st_pc_ae2 true ti_a4 ti_a4 sae_slli (st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0)
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hpmp1 ltac:(boot_static) Hnz_a4 with "Hmm HpcfA Hpc Hfile Hiae2").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite Pae2 L_ae2a4 st_Hb61). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a4 := regval_into_reg st_adue_bit]> (st_m_ae1 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    (* ae3: c.or a5, a4  (a5 := menvcfg0 | (1<<61)) *)
    assert (L_ae3a5 : st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a5 = menvcfg0)
      by (st_unfold; st_look).
    assert (L_ae3a4 : st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a4 = st_adue_bit)
      by (st_unfold; st_look).
    iApply (wp_or_gpr Φ st_pc_ae3 true ti_a4 ti_a5 ti_a5 (st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0)
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hpmp1 ltac:(boot_static) Hnz_a5 with "Hmm HpcfA Hpc Hfile Hiae3").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite Pae3 L_ae3a5 L_ae3a4). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg (or_vec menvcfg0 st_adue_bit)]> (st_m_ae2 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".
    (* ae4: csrw menvcfg, a5  (menvcfg := st_menv_adue menvcfg0) *)
    assert (L_ae4a5 : st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_a5 = or_vec menvcfg0 st_adue_bit)
      by (st_unfold; st_look).
    iApply (wp_csrw_menvcfg_gpr Φ st_pc_ae4 ti_a5 (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0) menvcfg0
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hpmp1 ltac:(boot_static) Hnz_a5
              with "Hmm HpcfA Hpc Hfile Hmenv Hiae4").
    iEval (rewrite Pae4 L_ae4a5). iIntros "Hmm HpcfA Hpc Hfile Hmenv".
    iEval (change (menvcfg_legalized menvcfg0 (or_vec menvcfg0 st_adue_bit))
             with (st_menv_adue menvcfg0)) in "Hmenv".

    (* ---- 59. jal ra, timerinit (PC := timerinit entry) ---- *)
    iApply (wp_jal_gpr Φ st_pc59 ti_ra sjimm59 (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0)
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hpmp1 ltac:(boot_static) Hnz_ra Hjal_al
              with "Hmm HpcfA Hpc Hfile Hi59").
    iEval (rewrite P59 Hlinkv). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_ra := regval_into_reg st_ra_link]>
                     (st_m_ae3 m sp0 ms0 mie0 mideleg0 menvcfg0))
             with (st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0)) in "Hfile".

    (* ---- timerinit() (21 instructions), at q = 1/2 ---- *)
    assert (L59sp : st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx csp_rs1 = ti_sp1 sp0)
      by (st_unfold; st_look).
    assert (L59ra : st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_ra = st_ra_link)
      by (st_unfold; st_look).
    assert (L59s0 : st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0 !!! Regidx ti_s0 = sp0)
      by (st_unfold; st_look).
    iDestruct "Hpaddr" as "[HpaA HpaK]".
    (* bundle timerinit's 2-slot frame into [stack_own_phys (ti_sp1 sp0) 2] *)
    assert (Htb1 : ti_ea_ra (ti_sp1 sp0) = pa_stk (ti_sp1 sp0) 1).
    { unfold ti_ea_ra, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Htb2 : ti_ea_s0 (ti_sp1 sp0) = pa_stk (ti_sp1 sp0) 2).
    { unfold ti_ea_s0, ti_sp1, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite Htb1) in "Htra". iEval (rewrite Htb2) in "Hts0".
    iDestruct (stack_own_phys_2_intro with "Htra Hts0") as "Htistk".
    iApply (wp_timerinit Φ (1/2)%Qp (st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0) (ti_sp1 sp0)
              st_ra_link sp0 (st_menv_adue menvcfg0) stimecmp0 mcounteren0
              (st_pmpcfg1 pmpcfg0) (st_pmpaddr1 pmpcfg0 pmpaddr00) 2
              ltac:(lia) Hpmp1 Htor_ra Htor_s0 L59sp L59ra L59s0
              with "Hmm HpcfA HpaA Hpc Hfile Hmenv Hmcen Hstc Htistk Htext").
    iEval (rewrite Hcretv).
    iIntros (tv) "Hmm HpcfA HpaA Hpc Hfile Hmenv Hmcen Hstc Htistk".
    iDestruct (stack_own_phys_2_elim with "Htistk") as (v_tra v_ts0) "[Htra Hts0]".
    iEval (rewrite -Htb1) in "Htra". iEval (rewrite -Htb2) in "Hts0".
    iEval (change (ti_mout (st_m59 m sp0 ms0 mie0 mideleg0 menvcfg0) (ti_sp1 sp0)
                     (st_menv_adue menvcfg0) mcounteren0 tv st_ra_link sp0)
             with (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv)) in "Hfile".
    iDestruct (reg_half_join with "HpaA HpaK") as "Hpaddr".

    (* ---- 60. csrr a5, mhartid ---- *)
    iApply (wp_csrr_mhartid_gpr Φ st_pc60 ti_a5 mhartid_in
              (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv)
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hpmp1 ltac:(boot_static) Hnz_a5
              with "Hmm HpcfA Hpc Hfile Hmh Hi60").
    iEval (rewrite P60). iIntros "Hmm HpcfA Hpc Hfile Hmh".
    iEval (change (<[Regidx ti_a5 := regval_into_reg mhartid_in]>
                     (st_mti m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv))
             with (st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)) in "Hfile".

    (* ---- 61. c.addiw a5, 0 (sext.w) ---- *)
    assert (L61a5 : st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in
                      !!! Regidx ti_a5 = mhartid_in) by (st_unfold; st_look).
    iApply (wp_addiw_gpr Φ st_pc61 true ti_a5 ti_a5 (sign_extend' 12 si61)
              (st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hpmp1 ltac:(boot_static) Hnz_a5
              with "Hmm HpcfA Hpc Hfile Hi61").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite sext6_12_64 P61 L61a5). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx ti_a5 := regval_into_reg
                      (sign_extend' 64 (subrange_vec_dec
                         (add_vec mhartid_in (sign_extend' 64 si61)) 31 0))]>
                     (st_m60 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in))
             with (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)) in "Hfile".

    (* ---- 62. c.mv tp, a5 ---- *)
    assert (L62a5 : st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in
                      !!! Regidx ti_a5 = st_tpv mhartid_in) by (st_unfold; st_look).
    iDestruct (gpr_file_x0
                 (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)
                 cli_rs1 ltac:(vm_compute; reflexivity) with "Hfile") as "[%Hx0_62 Hfile]".
    iApply (wp_add_gpr Φ st_pc62 true ti_a5 cli_rs1 st_tp
              (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)
              (st_pmpcfg1 pmpcfg0) (1/2)%Qp Hpmp1 ltac:(boot_static) Hnz_tp
              with "Hmm HpcfA Hpc Hfile Hi62").
    iEval (change (if true then 2%Z else 4%Z) with 2%Z).
    iEval (rewrite P62 Hx0_62 add_vec_zero_l L62a5). iIntros "Hmm HpcfA Hpc Hfile".
    iEval (change (<[Regidx st_tp := regval_into_reg (st_tpv mhartid_in)]>
                     (st_m61 m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in))
             with (st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)) in "Hfile".

    (* ---- 63. MRET into Supervisor mode at <main>. ---- *)
    iDestruct (mmode_config_unbundle with "Hmm") as "(_ & _ & HhsA & HprivA & HmstA)".
    iDestruct "HmstA" as (ms1') "(HmsA & _ & _ & _)".
    iDestruct (reg_pointsto_agree with "HmsA HmsK") as %->.
    iDestruct (reg_half_join with "HhsA HhsK") as "Hhs".
    iDestruct (reg_half_join with "HprivA HprivK") as "Hpriv".
    iDestruct (reg_half_join with "HmsA HmsK") as "Hms".
    iDestruct (reg_half_join with "HpcfA HpcfK") as "Hpcf".
    assert (Hnp : privLevel_bits_forwards (_get_Mstatus_MPP (cms2 (st_ms1 ms0)), ('b"0"))
                  = returnM Supervisor) by (apply st_mret_priv).
    assert (HlpeF : _get_MEnvcfg_LPE (menvcfg_legalized (st_menv_adue menvcfg0) (ti_menv1 (st_menv_adue menvcfg0))) = ('b"0"))
      by (apply st_menvcfg_LPE_final; apply st_menv_adue_LPE; exact HlpeE).
    iApply (wp_mret_gpr Φ st_pc63 Supervisor (st_ms1 ms0) st_main
              (menvcfg_legalized (st_menv_adue menvcfg0) (ti_menv1 (st_menv_adue menvcfg0)))
              (st_mout m sp0 ms0 mie0 mideleg0 menvcfg0 mcounteren0 tv mhartid_in)
              (st_pmpcfg1 pmpcfg0)
              Hpmp1 ltac:(boot_static) HmIE1 Hnp eq_refl HlpeF
              with "Hhw Hinv Hhs Hpriv Hms Hpcf Hmenv Hpc Hfile Hmepc Hi63").
    iEval (rewrite Hctgtv).
    iIntros "Hhs Hpriv Hms Hpcf Hmenv Hpc Hfile Hmepc".

    (* re-bundle start's 4 frame slots back into [stack_own_phys sp0 n] and hand
       everything to the caller's continuation. *)
    iEval (rewrite Hb1) in "Hsra". iEval (rewrite Hb2) in "Hss0".
    iEval (rewrite Hb3) in "Htra". iEval (rewrite Hb4) in "Hts0".
    iEval (rewrite -(pa_stk_assoc sp0 2 1)) in "Htra".
    iEval (rewrite -(pa_stk_assoc sp0 2 2)) in "Hts0".
    iDestruct (stack_own_phys_2_intro with "Hsra Hss0") as "Ht12".
    iDestruct (stack_own_phys_2_intro with "Htra Hts0") as "Ht34".
    iDestruct (stack_own_phys_split_2 sp0 2 4 ltac:(lia) with "[$Ht12 $Ht34]") as "Htop".
    iDestruct (stack_own_phys_split_2 sp0 4 n ltac:(lia) with "[$Htop $Hdeep]") as "Hstk".
    iApply ("Hcont" $! tv ms0 HoIE HoPRV HoSXL with "Hhs Hpriv Hms Hpcf Hpaddr Hpc Hfile Hmh Hmepc Hsatp Hmede Hmdl Hmie Hmenv Hmcen Hstc Hstk").
  Qed.


End WpStartThm.
