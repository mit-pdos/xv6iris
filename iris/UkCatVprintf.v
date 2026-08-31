(* ===================================================================== *)
(* UkCatVprintf.v -- ulib's [vprintf(fd, fmt, ap)] for a format string    *)
(* containing no '%', which is what all four of cat's literals are.       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile WpGpr.
Require Import AlignBits WpMmodeLeafBase.
Require Import UserBits UserPtTree UserExec ProcPtOwn.
Require Import WpUmodeBranch.
Require Import UmodeMem UmodeFetch UmodeArith UmodeAbi.
Require Import UserPerm UsysMemOk UexecWp UexecSlot UexecRet.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import UCodeCat.
Require Import TsoCtx.
Require User.CatSyms User.InitInstrs.
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkCat.
Require Import UkCatPutc.
Require Import UkRunBr.

Section UkCatVprintf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs : gname).

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).

  Lemma wp_kcat_vprintf_epi0 (h : CpuId) (m : regfile)
      (sp0 vra vs0 vs1 : mword 64) (n : nat) :
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) ->
    uint sp0 mod 8 = 0 ->
    96 <= uint sp0 ->
    cat_code γt -∗
    uword γd (uint sp0 - 8) vra -∗
    uword γd (uint sp0 - 16) vs0 -∗
    uword γd (uint sp0 - 24) vs1 -∗
    (∃ w : mword 64, uword γd (uint sp0 - 32) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 40) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 48) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 56) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 64) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 72) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 80) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 88) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 96) w) -∗
    urun γt γd γs h m (mword_of_int 0x744) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = vs1 ⌝ -∗
       ⌜ forall r : mword 5,
           Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
           Regidx r <> Regidx s1_idx -> Regidx r <> Regidx ra_idx ->
           m' !!! Regidx r = m !!! Regidx r ⌝ -∗
       urun γt γd γs h' m' (ret_pc vra) (12 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hal8 Hlo. iIntros "#Hcode Hwra Hws0 Hws1 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hrun Hcont".
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    = uint sp0 - 96)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hd12 : (0 <= 8 * Z.of_nat 12)%Z) by (apply Z.leb_le; reflexivity).
    assert (Hlt12 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    + 8 * Z.of_nat 12 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    (8 * Z.of_nat 12) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                 (8 * Z.of_nat 12) Hd12 Hlt12).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Ho88 : uoff_sdsp (mword_of_int 11 : mword 6) = 88)
      by (vm_compute; reflexivity).
    assert (Ho80 : uoff_sdsp (mword_of_int 10 : mword 6) = 80)
      by (vm_compute; reflexivity).
    assert (Ho72 : uoff_sdsp (mword_of_int 9 : mword 6) = 72)
      by (vm_compute; reflexivity).
    (* ---- 0x744  c.ldsp ra,88(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h m (mword_of_int 0x744)
              (mword_of_int 11 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp96 Ho88; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hwra Hrun").
    { iApply (uis_cat_744 with "Hcode"). }
    iIntros "Hwra".
    assert (E70a : add_vec_int (mword_of_int 0x744 : mword 64) 2
                 = mword_of_int 0x746)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70a.
    iIntros (h1) "Hrun".
    set (mm1 := <[Regidx ra_idx := regval_into_reg vra]> m).
    assert (Hsp1 : mm1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx ra_idx) (Regidx csp_rs1) (regval_into_reg vra)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x746  c.ldsp s0,80(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h1 mm1 (mword_of_int 0x746)
              (mword_of_int 10 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp96 Ho80; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws0 Hrun").
    { iApply (uis_cat_746 with "Hcode"). }
    iIntros "Hws0".
    assert (E70c : add_vec_int (mword_of_int 0x746 : mword 64) 2
                 = mword_of_int 0x748)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70c.
    iIntros (h2) "Hrun".
    set (mm2 := <[Regidx s0_idx := regval_into_reg vs0]> mm1).
    assert (Hsp2 : mm2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp1.
      exact (upd_ne mm1 (Regidx s0_idx) (Regidx csp_rs1) (regval_into_reg vs0)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x748  c.ldsp s1,72(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h2 mm2 (mword_of_int 0x748)
              (mword_of_int 9 : mword 6) s1_idx (uint sp0 - 24) vs1 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp2 Hsp96 Ho72; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws1 Hrun").
    { iApply (uis_cat_748 with "Hcode"). }
    iIntros "Hws1".
    assert (E70e : add_vec_int (mword_of_int 0x748 : mword 64) 2
                 = mword_of_int 0x74a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70e.
    iIntros (h3) "Hrun".
    set (mm3 := <[Regidx s1_idx := regval_into_reg vs1]> mm2).
    assert (Hsp3 : mm3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp2.
      exact (upd_ne mm2 (Regidx s1_idx) (Regidx csp_rs1) (regval_into_reg vs1)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x74a  c.addi16sp sp,sp,96 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs h3 mm3 (mword_of_int 0x74a)
              (mword_of_int 6 : mword 6) 12 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hwra Hws0 Hws1 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12] Hrun").
    { iApply (uis_cat_74a with "Hcode"). }
    { rewrite Hsp3 Hup.
      iApply (ustack_12_close γd sp0 Hal8
                with "[Hwra] [Hws0] [Hws1] Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12").
      { iExists vra. iExact "Hwra". }
      { iExists vs0. iExact "Hws0". }
      { iExists vs1. iExact "Hws1". } }
    assert (E710 : add_vec_int (mword_of_int 0x74a : mword 64) 2
                   = mword_of_int 0x74c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp3 Hup E710.
    iIntros (h4) "Hrun".
    set (mm4 := <[Regidx csp_rs1 := regval_into_reg sp0]> mm3).
    assert (Hra4 : mm4 !!! Regidx ra_idx = vra).
    { rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx ra_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /mm3 (upd_ne mm2 (Regidx s1_idx) (Regidx ra_idx)
                     (regval_into_reg vs1) ltac:(vm_compute; discriminate)).
      rewrite /mm2 (upd_ne mm1 (Regidx s0_idx) (Regidx ra_idx)
                     (regval_into_reg vs0) ltac:(vm_compute; discriminate)).
      rewrite /mm1. exact (upd_eq m (Regidx ra_idx) (regval_into_reg vra)). }
    (* ---- 0x74c  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs h4 mm4 (mword_of_int 0x74c) ra_idx
              (ret_pc vra) (12 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra4; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_74c with "Hcode"). }
    iIntros (h5) "Hrun".
    iApply ("Hcont" $! h5 mm4 with "[] [] [] [] Hrun").
    { iPureIntro. rewrite /mm4.
      exact (upd_eq mm3 (Regidx csp_rs1) (regval_into_reg sp0)). }
    { iPureIntro.
      rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx s0_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /mm3 (upd_ne mm2 (Regidx s1_idx) (Regidx s0_idx)
                     (regval_into_reg vs1) ltac:(vm_compute; discriminate)).
      rewrite /mm2. exact (upd_eq mm1 (Regidx s0_idx) (regval_into_reg vs0)). }
    { iPureIntro.
      rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx s1_idx)
                     (regval_into_reg sp0) ltac:(vm_compute; discriminate)).
      rewrite /mm3. exact (upd_eq mm2 (Regidx s1_idx) (regval_into_reg vs1)). }
    { iPureIntro. intros r Hrsp Hrs0 Hrs1 Hrra.
      rewrite /mm4 (upd_ne mm3 (Regidx csp_rs1) (Regidx r)
                     (regval_into_reg sp0) Hrsp).
      rewrite /mm3 (upd_ne mm2 (Regidx s1_idx) (Regidx r)
                     (regval_into_reg vs1) Hrs1).
      rewrite /mm2 (upd_ne mm1 (Regidx s0_idx) (Regidx r)
                     (regval_into_reg vs0) Hrs0).
      rewrite /mm1. exact (upd_ne m (Regidx ra_idx) (Regidx r)
                             (regval_into_reg vra) Hrra). }
  Qed.





  (* --------------------------------------------------------------------- *)
  (* vprintf's FULL EPILOGUE @0x736: restore s2..s8, then fall into the      *)
  (* shared tail.  This is where [ucallee_saved] is assembled, because this  *)
  (* is where every spilled register is back at its entry value: the ten     *)
  (* frame words are PINNED to [m0]'s registers in the statement, [sp0] is   *)
  (* [m0]'s sp, and [Hfree] covers the five callee-saved registers vprintf   *)
  (* never touches (gp, tp, s9, s10, s11).  [ucs_cases] says there is no      *)
  (* sixteenth.                                                              *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_epi (h : CpuId) (m m0 : regfile) (sp0 : mword 64)
      (n : nat) :
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    uint sp0 mod 8 = 0 ->
    96 <= uint sp0 ->
    (forall r : mword 5, ucallee_saved_idx r = true ->
       uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27) ->
       m !!! Regidx r = m0 !!! Regidx r) ->
    cat_code γt -∗
    uword γd (uint sp0 - 8) (m0 !!! Regidx ra_idx) -∗
    uword γd (uint sp0 - 16) (m0 !!! Regidx s0_idx) -∗
    uword γd (uint sp0 - 24) (m0 !!! Regidx s1_idx) -∗
    uword γd (uint sp0 - 32) (m0 !!! Regidx s2_idx) -∗
    uword γd (uint sp0 - 40) (m0 !!! Regidx s3_idx) -∗
    uword γd (uint sp0 - 48) (m0 !!! Regidx s4_idx) -∗
    uword γd (uint sp0 - 56) (m0 !!! Regidx s5_idx) -∗
    uword γd (uint sp0 - 64) (m0 !!! Regidx s6_idx) -∗
    uword γd (uint sp0 - 72) (m0 !!! Regidx s7_idx) -∗
    uword γd (uint sp0 - 80) (m0 !!! Regidx s8_idx) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 88) w) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 96) w) -∗
    urun γt γd γs h m (mword_of_int 0x736) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m0 m' ⌝ -∗
       urun γt γd γs h' m' (ret_pc (m0 !!! Regidx ra_idx)) (12 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hsp0 Hal8 Hlo Hfree.
    iIntros "#Hcode Hwra Hws0 Hws1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw11 Hw12 Hrun Hcont".
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    = uint sp0 - 96)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho64 : uoff_sdsp (mword_of_int 8 : mword 6) = 64)
      by (vm_compute; reflexivity).
    assert (Ho56 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    assert (Ho48 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Ho40 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho32 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0x736  c.ldsp s2,64(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h m (mword_of_int 0x736)
              (mword_of_int 8 : mword 6) s2_idx (uint sp0 - 32)
              (m0 !!! Regidx s2_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp96 Ho64; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_cat_736 with "Hcode"). }
    iIntros "Hw2".
    assert (E6fc : add_vec_int (mword_of_int 0x736 : mword 64) 2
                 = mword_of_int 0x738)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6fc.
    iIntros (h1) "Hrun".
    set (me1 := <[Regidx s2_idx := regval_into_reg (m0 !!! Regidx s2_idx)]> m).
    assert (Hsp1 : me1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx s2_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s2_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x738  c.ldsp s3,56(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h1 me1 (mword_of_int 0x738)
              (mword_of_int 7 : mword 6) s3_idx (uint sp0 - 40)
              (m0 !!! Regidx s3_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp96 Ho56; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_cat_738 with "Hcode"). }
    iIntros "Hw3".
    assert (E6fe : add_vec_int (mword_of_int 0x738 : mword 64) 2
                 = mword_of_int 0x73a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E6fe.
    iIntros (h2) "Hrun".
    set (me2 := <[Regidx s3_idx := regval_into_reg (m0 !!! Regidx s3_idx)]> me1).
    assert (Hsp2 : me2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp1.
      exact (upd_ne me1 (Regidx s3_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s3_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x73a  c.ldsp s4,48(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h2 me2 (mword_of_int 0x73a)
              (mword_of_int 6 : mword 6) s4_idx (uint sp0 - 48)
              (m0 !!! Regidx s4_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp2 Hsp96 Ho48; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_cat_73a with "Hcode"). }
    iIntros "Hw4".
    assert (E700 : add_vec_int (mword_of_int 0x73a : mword 64) 2
                 = mword_of_int 0x73c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E700.
    iIntros (h3) "Hrun".
    set (me3 := <[Regidx s4_idx := regval_into_reg (m0 !!! Regidx s4_idx)]> me2).
    assert (Hsp3 : me3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp2.
      exact (upd_ne me2 (Regidx s4_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s4_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x73c  c.ldsp s5,40(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h3 me3 (mword_of_int 0x73c)
              (mword_of_int 5 : mword 6) s5_idx (uint sp0 - 56)
              (m0 !!! Regidx s5_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp3 Hsp96 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw5 Hrun").
    { iApply (uis_cat_73c with "Hcode"). }
    iIntros "Hw5".
    assert (E702 : add_vec_int (mword_of_int 0x73c : mword 64) 2
                 = mword_of_int 0x73e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E702.
    iIntros (h4) "Hrun".
    set (me4 := <[Regidx s5_idx := regval_into_reg (m0 !!! Regidx s5_idx)]> me3).
    assert (Hsp4 : me4 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp3.
      exact (upd_ne me3 (Regidx s5_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s5_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x73e  c.ldsp s6,32(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h4 me4 (mword_of_int 0x73e)
              (mword_of_int 4 : mword 6) s6_idx (uint sp0 - 64)
              (m0 !!! Regidx s6_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp4 Hsp96 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw6 Hrun").
    { iApply (uis_cat_73e with "Hcode"). }
    iIntros "Hw6".
    assert (E704 : add_vec_int (mword_of_int 0x73e : mword 64) 2
                 = mword_of_int 0x740)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E704.
    iIntros (h5) "Hrun".
    set (me5 := <[Regidx s6_idx := regval_into_reg (m0 !!! Regidx s6_idx)]> me4).
    assert (Hsp5 : me5 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp4.
      exact (upd_ne me4 (Regidx s6_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s6_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x740  c.ldsp s7,24(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h5 me5 (mword_of_int 0x740)
              (mword_of_int 3 : mword 6) s7_idx (uint sp0 - 72)
              (m0 !!! Regidx s7_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp5 Hsp96 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw7 Hrun").
    { iApply (uis_cat_740 with "Hcode"). }
    iIntros "Hw7".
    assert (E706 : add_vec_int (mword_of_int 0x740 : mword 64) 2
                 = mword_of_int 0x742)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E706.
    iIntros (h6) "Hrun".
    set (me6 := <[Regidx s7_idx := regval_into_reg (m0 !!! Regidx s7_idx)]> me5).
    assert (Hsp6 : me6 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp5.
      exact (upd_ne me5 (Regidx s7_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s7_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x742  c.ldsp s8,16(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h6 me6 (mword_of_int 0x742)
              (mword_of_int 2 : mword 6) s8_idx (uint sp0 - 80)
              (m0 !!! Regidx s8_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp6 Hsp96 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw8 Hrun").
    { iApply (uis_cat_742 with "Hcode"). }
    iIntros "Hw8".
    assert (E708 : add_vec_int (mword_of_int 0x742 : mword 64) 2
                 = mword_of_int 0x744)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E708.
    iIntros (h7) "Hrun".
    set (me7 := <[Regidx s8_idx := regval_into_reg (m0 !!! Regidx s8_idx)]> me6).
    assert (Hsp7 : me7 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp6.
      exact (upd_ne me6 (Regidx s8_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s8_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x744..0x74c: the shared tail ---- *)
    iApply (wp_kcat_vprintf_epi0 h7 me7 sp0 (m0 !!! Regidx ra_idx)
              (m0 !!! Regidx s0_idx) (m0 !!! Regidx s1_idx) n Hsp7 Hal8 Hlo
              with "Hcode Hwra Hws0 Hws1 [Hw2] [Hw3] [Hw4] [Hw5] [Hw6] [Hw7] [Hw8] Hw11 Hw12 Hrun").
    { iExists (m0 !!! Regidx s2_idx). iExact "Hw2". }
    { iExists (m0 !!! Regidx s3_idx). iExact "Hw3". }
    { iExists (m0 !!! Regidx s4_idx). iExact "Hw4". }
    { iExists (m0 !!! Regidx s5_idx). iExact "Hw5". }
    { iExists (m0 !!! Regidx s6_idx). iExact "Hw6". }
    { iExists (m0 !!! Regidx s7_idx). iExact "Hw7". }
    { iExists (m0 !!! Regidx s8_idx). iExact "Hw8". }
    assert (Hme2 : me7 !!! Regidx s2_idx = m0 !!! Regidx s2_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s5_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me3 (upd_ne me2 (Regidx s4_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s4_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me2 (upd_ne me1 (Regidx s3_idx) (Regidx s2_idx)
                     (regval_into_reg (m0 !!! Regidx s3_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me1.
      exact (upd_eq m (Regidx s2_idx) (regval_into_reg (m0 !!! Regidx s2_idx))). }
    assert (Hme3 : me7 !!! Regidx s3_idx = m0 !!! Regidx s3_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s5_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me3 (upd_ne me2 (Regidx s4_idx) (Regidx s3_idx)
                     (regval_into_reg (m0 !!! Regidx s4_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me2.
      exact (upd_eq me1 (Regidx s3_idx) (regval_into_reg (m0 !!! Regidx s3_idx))). }
    assert (Hme4 : me7 !!! Regidx s4_idx = m0 !!! Regidx s4_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx s4_idx)
                     (regval_into_reg (m0 !!! Regidx s5_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me3.
      exact (upd_eq me2 (Regidx s4_idx) (regval_into_reg (m0 !!! Regidx s4_idx))). }
    assert (Hme5 : me7 !!! Regidx s5_idx = m0 !!! Regidx s5_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s5_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s5_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx s5_idx)
                     (regval_into_reg (m0 !!! Regidx s6_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me4.
      exact (upd_eq me3 (Regidx s5_idx) (regval_into_reg (m0 !!! Regidx s5_idx))). }
    assert (Hme6 : me7 !!! Regidx s6_idx = m0 !!! Regidx s6_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s6_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx s6_idx)
                     (regval_into_reg (m0 !!! Regidx s7_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me5.
      exact (upd_eq me4 (Regidx s6_idx) (regval_into_reg (m0 !!! Regidx s6_idx))). }
    assert (Hme7 : me7 !!! Regidx s7_idx = m0 !!! Regidx s7_idx).
    {
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx s7_idx)
                     (regval_into_reg (m0 !!! Regidx s8_idx))
                     ltac:(vm_compute; discriminate)).
      rewrite /me6.
      exact (upd_eq me5 (Regidx s7_idx) (regval_into_reg (m0 !!! Regidx s7_idx))). }
    assert (Hme8 : me7 !!! Regidx s8_idx = m0 !!! Regidx s8_idx).
    {
      rewrite /me7.
      exact (upd_eq me6 (Regidx s8_idx) (regval_into_reg (m0 !!! Regidx s8_idx))). }
    assert (Hmeo : forall r : mword 5,
               (uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) ->
               me7 !!! Regidx r = m !!! Regidx r).
    { intros r Hr.
      (* NOT [vm_compute] on these: the goal carries the free [r], and
         [vm_compute] against a free variable is the documented hang.
         Compute the CONCRETE index only, then [lia] against [Hr]. *)
      assert (N18 : Regidx r <> Regidx s2_idx)
        by (apply uidx_ne;
            replace (uint s2_idx) with 18 by (vm_compute; reflexivity);
            lia).
      assert (N19 : Regidx r <> Regidx s3_idx)
        by (apply uidx_ne;
            replace (uint s3_idx) with 19 by (vm_compute; reflexivity);
            lia).
      assert (N20 : Regidx r <> Regidx s4_idx)
        by (apply uidx_ne;
            replace (uint s4_idx) with 20 by (vm_compute; reflexivity);
            lia).
      assert (N21 : Regidx r <> Regidx s5_idx)
        by (apply uidx_ne;
            replace (uint s5_idx) with 21 by (vm_compute; reflexivity);
            lia).
      assert (N22 : Regidx r <> Regidx s6_idx)
        by (apply uidx_ne;
            replace (uint s6_idx) with 22 by (vm_compute; reflexivity);
            lia).
      assert (N23 : Regidx r <> Regidx s7_idx)
        by (apply uidx_ne;
            replace (uint s7_idx) with 23 by (vm_compute; reflexivity);
            lia).
      assert (N24 : Regidx r <> Regidx s8_idx)
        by (apply uidx_ne;
            replace (uint s8_idx) with 24 by (vm_compute; reflexivity);
            lia).
      rewrite /me7 (upd_ne me6 (Regidx s8_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s8_idx)) N24).
      rewrite /me6 (upd_ne me5 (Regidx s7_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s7_idx)) N23).
      rewrite /me5 (upd_ne me4 (Regidx s6_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s6_idx)) N22).
      rewrite /me4 (upd_ne me3 (Regidx s5_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s5_idx)) N21).
      rewrite /me3 (upd_ne me2 (Regidx s4_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s4_idx)) N20).
      rewrite /me2 (upd_ne me1 (Regidx s3_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s3_idx)) N19).
      rewrite /me1 (upd_ne m (Regidx s2_idx) (Regidx r)
                     (regval_into_reg (m0 !!! Regidx s2_idx)) N18).
      reflexivity. }
    iIntros (h8 m2) "%Hspx %Hs0x %Hs1x %Hpres Hrun".
    iApply ("Hcont" $! h8 m2 with "[] Hrun").
    iPureIntro. intros r Hr.
    assert (Hpresx : uint r <> 2 -> uint r <> 8 -> uint r <> 9 -> uint r <> 1 ->
                       m2 !!! Regidx r = me7 !!! Regidx r).
    { intros H2 H8 H9 H1. apply Hpres; apply uidx_ne;
        [ replace (uint csp_rs1) with 2 by (vm_compute; reflexivity)
        | replace (uint s0_idx) with 8 by (vm_compute; reflexivity)
        | replace (uint s1_idx) with 9 by (vm_compute; reflexivity)
        | replace (uint ra_idx) with 1 by (vm_compute; reflexivity) ];
        assumption. }
    destruct (ucs_cases r Hr) as [E2 | [E3 | [E4 | [E8 | [E9 | E18]]]]].
    - assert (Er : Regidx r = Regidx csp_rs1)
        by (apply (uidx_eq r 2); [ exact E2 | vm_compute; reflexivity ]).
      rewrite Er Hspx. exact (eq_sym Hsp0).
    -
      assert (K2 : uint r <> 2) by lia.
      assert (K8 : uint r <> 8) by lia.
      assert (K9 : uint r <> 9) by lia.
      assert (K1 : uint r <> 1) by lia.
      rewrite (Hpresx K2 K8 K9 K1).
      assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
      rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
    -
      assert (K2 : uint r <> 2) by lia.
      assert (K8 : uint r <> 8) by lia.
      assert (K9 : uint r <> 9) by lia.
      assert (K1 : uint r <> 1) by lia.
      rewrite (Hpresx K2 K8 K9 K1).
      assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
      rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
    - assert (Er : Regidx r = Regidx s0_idx)
        by (apply (uidx_eq r 8); [ exact E8 | vm_compute; reflexivity ]).
      rewrite Er. exact Hs0x.
    - assert (Er : Regidx r = Regidx s1_idx)
        by (apply (uidx_eq r 9); [ exact E9 | vm_compute; reflexivity ]).
      rewrite Er. exact Hs1x.
    -
      assert (K2 : uint r <> 2) by lia.
      assert (K8 : uint r <> 8) by lia.
      assert (K9 : uint r <> 9) by lia.
      assert (K1 : uint r <> 1) by lia.
      rewrite (Hpresx K2 K8 K9 K1).
      assert (Ecase : uint r = 18 \/ uint r = 19 \/ uint r = 20 \/ uint r = 21 \/
                      uint r = 22 \/ uint r = 23 \/ uint r = 24 \/
                      uint r = 25 \/ uint r = 26 \/ uint r = 27) by lia.
      destruct Ecase as [E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]].
      + assert (Er : Regidx r = Regidx s2_idx)
          by (apply (uidx_eq r 18); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme2.
      + assert (Er : Regidx r = Regidx s3_idx)
          by (apply (uidx_eq r 19); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme3.
      + assert (Er : Regidx r = Regidx s4_idx)
          by (apply (uidx_eq r 20); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme4.
      + assert (Er : Regidx r = Regidx s5_idx)
          by (apply (uidx_eq r 21); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme5.
      + assert (Er : Regidx r = Regidx s6_idx)
          by (apply (uidx_eq r 22); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme6.
      + assert (Er : Regidx r = Regidx s7_idx)
          by (apply (uidx_eq r 23); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme7.
      + assert (Er : Regidx r = Regidx s8_idx)
          by (apply (uidx_eq r 24); [ exact E | vm_compute; reflexivity ]).
        rewrite Er. exact Hme8.
      + assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
        rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
      + assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
        rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
      + assert (Hd : uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27)) by lia.
        rewrite (Hmeo r Hd). exact (Hfree r Hr Hd).
  Qed.

  (* ===================================================================== *)
  (* THE LOOP.  For a format string with no '%', vprintf is                 *)
  (*                                                                        *)
  (*   0x566  sext.w a5,s1        ; a5 := the current character             *)
  (*   0x56a  bnez  s3,0x550      ; NOT taken: s3 is the pending-% state    *)
  (*   0x56e  bne   a5,s5,0x546   ; taken: the character is not '%'          *)
  (*   0x546  mv a1,s1 ; mv a0,s6 ; jal putc ; j 0x554                       *)
  (*   0x554  addiw a5,s2,1 ; mv s2,a5 ; mv a4,a5 ; add a5,a5,s4             *)
  (*   0x55e  lbu   s1,0(a5)      ; the NEXT character                       *)
  (*   0x562  beqz  s1,0x736      ; taken at the terminator                  *)
  (*                                                                        *)
  (* [vp_inv] is what survives a round: the frame pointer, the index, and    *)
  (* the four values the prologue parked in callee-saved registers.  It      *)
  (* survives the putc CALL for free -- every register it names is           *)
  (* callee-saved, which is the whole reason ulib parks them there.          *)
  (* ===================================================================== *)

  Definition vp_inv (m0 m : regfile) (sp0 : mword 64) (a : Z) (fd ap : mword 64)
      (i : nat) : Prop :=
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) /\
    m !!! Regidx s0_idx = sp0 /\
    m !!! Regidx s2_idx = mword_of_int (Z.of_nat i) /\
    m !!! Regidx s3_idx = zero_reg /\
    m !!! Regidx s4_idx = mword_of_int a /\
    m !!! Regidx s5_idx = mword_of_int 37 /\
    m !!! Regidx s6_idx = fd /\
    m !!! Regidx s7_idx = ap /\
    m !!! Regidx s8_idx = mword_of_int 100 /\
    (forall r : mword 5, ucallee_saved_idx r = true ->
       uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27) ->
       m !!! Regidx r = m0 !!! Regidx r).

  (* every register [vp_inv] names is callee-saved, so a call preserves it *)
  Lemma vp_inv_call (m0 m m' : regfile) (sp0 : mword 64) (a : Z)
      (fd ap : mword 64) (i : nat) :
    ucallee_saved m m' -> vp_inv m0 m sp0 a fd ap i -> vp_inv m0 m' sp0 a fd ap i.
  Proof.
    intros Hcs (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv.
    rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s0_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s5_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s6_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s7_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s8_idx ltac:(vm_compute; reflexivity)).
    repeat (split; [ assumption | ]).
    intros r Hr Hset. rewrite (Hcs r Hr). exact (Hfr r Hr Hset).
  Qed.


  (* which registers a step may write without disturbing [vp_inv]: anything
     that is neither one of the seven the invariant names (sp, s0, s2..s6)
     nor one of the five [Hfree] covers (gp, tp, s9..s11).  One
     [vm_compute] per call site instead of twelve. *)
  Definition vp_writable (r : mword 5) : bool :=
    negb (Z.eqb (uint r) 2 || Z.eqb (uint r) 3 || Z.eqb (uint r) 4 ||
          Z.eqb (uint r) 8 ||
          ((18 <=? uint r) && (uint r <=? 24)) ||
          ((25 <=? uint r) && (uint r <=? 27))).

  Lemma vp_writable_ne (r : mword 5) (z : Z) :
    vp_writable r = true ->
    (z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ (18 <= z <= 24) \/ (25 <= z <= 27)) ->
    uint r <> z.
  Proof.
    unfold vp_writable. intro H. apply negb_true_iff in H.
    rewrite !orb_false_iff in H.
    destruct H as [[[[[H1 H2] H3] H4] H5] H6].
    apply Z.eqb_neq in H1. apply Z.eqb_neq in H2.
    apply Z.eqb_neq in H3. apply Z.eqb_neq in H4.
    apply andb_false_iff in H5. apply andb_false_iff in H6.
    intros Hz He. rewrite He in H1, H2, H3, H4, H5, H6.
    destruct H5 as [H5 | H5]; try apply Z.leb_gt in H5;
      destruct H6 as [H6 | H6]; try apply Z.leb_gt in H6; lia.
  Qed.

  Lemma vp_inv_upd (m0 m : regfile) (sp0 : mword 64) (a : Z) (fd ap : mword 64)
      (i : nat) (r : mword 5) (v : mword 64) :
    vp_writable r = true ->
    vp_inv m0 m sp0 a fd ap i ->
    vp_inv m0 (<[Regidx r := regval_into_reg v]> m) sp0 a fd ap i.
  Proof.
    intros Hw (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv.
    rewrite (upd_ne m (Regidx r) (Regidx csp_rs1) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint csp_rs1) with 2
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s0_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s0_idx) with 8
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s2_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s3_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s3_idx) with 19
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s4_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s4_idx) with 20
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s5_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s5_idx) with 21
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s6_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s6_idx) with 22
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s7_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s7_idx) with 23
                       by (vm_compute; reflexivity); lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s8_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw);
                     replace (uint s8_idx) with 24
                       by (vm_compute; reflexivity); lia)).
    repeat (split; [ assumption | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx r) (Regidx q) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (vp_writable_ne r _ Hw); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* ...and the ONE write that changes it: s2, the loop index *)
  Lemma vp_inv_bump (m0 m : regfile) (sp0 : mword 64) (a : Z) (fd ap : mword 64)
      (i j : nat) (v : mword 64) :
    v = mword_of_int (Z.of_nat j) ->
    vp_inv m0 m sp0 a fd ap i ->
    vp_inv m0 (<[Regidx s2_idx := regval_into_reg v]> m) sp0 a fd ap j.
  Proof.
    intros -> (Hsp & Hs0 & _ & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hfr).
    unfold vp_inv.
    rewrite (upd_ne m (Regidx s2_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_ne m (Regidx s2_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq m (Regidx s2_idx) _).
    repeat (split; [ (assumption || reflexivity) | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx s2_idx) (Regidx q) _
               ltac:(apply uidx_ne; replace (uint s2_idx) with 18
                       by (vm_compute; reflexivity); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* --------------------------------------------------------------------- *)
  (* ONE ROUND, 0x566 -> 0x562.  It owns no frame word: putc's four are     *)
  (* BELOW sp, and the twelve vprintf spilled are untouched here.            *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_step (m0 : regfile) (sp0 fd ap : mword 64) (a : Z)
      (i : nat) (b0 b1 : mword 8) (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat i + 2 < 2 ^ 31 ->
    bv_unsigned b0 <> 37 ->
    vp_inv m0 m sp0 a fd ap i ->
    m !!! Regidx s1_idx = mword_of_int (bv_unsigned b0) ->
    cat_code γt -∗
    utext γt (a + Z.of_nat (S i)) b1 -∗
    urun γt γd γs h m (mword_of_int 0x566) (4 + n) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ vp_inv m0 m' sp0 a fd ap (S i) ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned b1) ⌝ -∗
       urun γt γd γs h' m' (mword_of_int 0x562) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hpct Hinv Hs1.
    destruct Hinv as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hfr).
    iIntros "#Hcode #Hb1 Hrun Hcont".
    assert (Hb0 : 0 <= bv_unsigned b0 < 256).
    { pose proof (bv_unsigned_in_range 8 b0) as HH.
      assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
      rewrite Em8 in HH. exact HH. }
    assert (Hi31 : 0 <= Z.of_nat i + 1 < Z31) by (unfold Z31; lia).
    (* ---- 0x566  sext.w a5,s1 ---- *)
    assert (Es0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                  = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ea5c : sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (m !!! Regidx s1_idx)
                           (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0)
                   = (mword_of_int (bv_unsigned b0) : mword 64)).
    { rewrite Hs1 Es0.
      assert (Hbw : 0 <= bv_unsigned b0 + 0 < Z31) by (unfold Z31; lia).
      rewrite (moi_addw (bv_unsigned b0) 0 Hbw).
      f_equal. lia. }
    iApply (wp_uk_addiw γt γd γs h m (mword_of_int 0x566)
              (mword_of_int 0 : mword 12) s1_idx a5_idx
              (mword_of_int (bv_unsigned b0)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea5c))
              with "[] Hrun").
    { iApply (uis_cat_566 with "Hcode"). }
    assert (E52c : add_vec_int (mword_of_int 0x566 : mword 64) 4
                   = mword_of_int 0x56a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E52c.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b0) : mword 64)]> m).
    assert (Ha5_1 : m1 !!! Regidx a5_idx = mword_of_int (bv_unsigned b0))
      by exact (upd_eq m (Regidx a5_idx) (regval_into_reg _)).
    assert (Hs3_1 : m1 !!! Regidx s3_idx = zero_reg).
    { rewrite <- Hs3.
      exact (upd_ne m (Regidx a5_idx) (Regidx s3_idx) (regval_into_reg _)
               ltac:(vm_compute; discriminate)). }
    assert (Hs5_1 : m1 !!! Regidx s5_idx = mword_of_int 37).
    { rewrite <- Hs5.
      exact (upd_ne m (Regidx a5_idx) (Regidx s5_idx) (regval_into_reg _)
               ltac:(vm_compute; discriminate)). }
    assert (Hs1_1 : m1 !!! Regidx s1_idx = mword_of_int (bv_unsigned b0)).
    { rewrite <- Hs1.
      exact (upd_ne m (Regidx a5_idx) (Regidx s1_idx) (regval_into_reg _)
               ltac:(vm_compute; discriminate)). }
    assert (Hs6_1 : m1 !!! Regidx s6_idx = fd).
    { rewrite <- Hs6.
      exact (upd_ne m (Regidx a5_idx) (Regidx s6_idx) (regval_into_reg _)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x56a  bnez s3,0x550 -- NOT taken, the state register is 0 ---- *)
    assert (Hnt : false = uv_btaken BNE (m1 !!! Regidx s3_idx) zero_reg)
      by (rewrite Hs3_1; vm_compute; reflexivity).
    iApply (wp_uk_btype0 γt γd γs h1 m1 (mword_of_int 0x56a)
              (mword_of_int 8166 : mword 13) s3_idx BNE false
              (add_vec (mword_of_int 0x56a : mword 64)
                 (sign_extend' 64 (mword_of_int 8166 : mword 13)))
              (4 + n) Hnt eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_56a with "Hcode"). }
    assert (E530 : add_vec_int (mword_of_int 0x56a : mword 64) 4
                   = mword_of_int 0x56e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E530.
    iIntros (h2) "Hrun".
    (* ---- 0x56e  bne a5,s5,0x546 -- TAKEN, the character is not '%' ---- *)
    assert (Ht : true = uv_btaken BNE (m1 !!! Regidx a5_idx) (m1 !!! Regidx s5_idx)).
    { rewrite Ha5_1 Hs5_1. cbn [uv_btaken].
      assert (Hb64 : 0 <= bv_unsigned b0 < Z64) by (unfold Z64; lia).
      assert (H3764 : 0 <= 37 < Z64) by (unfold Z64; lia).
      rewrite (moi_neq_vec (bv_unsigned b0) 37 Hb64 H3764).
      destruct (Z.eqb_spec (bv_unsigned b0) 37) as [He | _];
        [ exfalso; exact (Hpct He) | reflexivity ]. }
    assert (Etgt534 : add_vec (mword_of_int 0x56e : mword 64)
                        (sign_extend' 64 (mword_of_int 8152 : mword 13))
                      = mword_of_int 0x546)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_btype γt γd γs h2 m1 (mword_of_int 0x56e)
              (mword_of_int 8152 : mword 13) s5_idx a5_idx BNE true
              (mword_of_int 0x546) (4 + n) Ht (eq_sym Etgt534)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_56e with "Hcode"). }
    iIntros (h3) "Hrun".
    (* ---- 0x546  c.mv a1,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs h3 m1 (mword_of_int 0x546) a1_idx s1_idx
              (add_vec zero_reg (m1 !!! Regidx s1_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_546 with "Hcode"). }
    assert (E50c : add_vec_int (mword_of_int 0x546 : mword 64) 2
                   = mword_of_int 0x548)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E50c.
    iIntros (h4) "Hrun".
    set (m2 := <[Regidx a1_idx
                 := regval_into_reg (add_vec zero_reg (m1 !!! Regidx s1_idx))]> m1).
    (* ---- 0x548  c.mv a0,s6 ---- *)
    iApply (wp_uk_cmv γt γd γs h4 m2 (mword_of_int 0x548) a0_idx s6_idx
              (add_vec zero_reg (m2 !!! Regidx s6_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_548 with "Hcode"). }
    assert (E50e : add_vec_int (mword_of_int 0x548 : mword 64) 2
                   = mword_of_int 0x54a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E50e.
    iIntros (h5) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg (add_vec zero_reg (m2 !!! Regidx s6_idx))]> m2).
    (* ---- 0x54a  jal ra,0x454 <putc> ---- *)
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & Hputc & _ & _ & _ & _ & _).
    iApply (wp_uk_jal γt γd γs h5 m3 (mword_of_int 0x54a)
              (mword_of_int 2096906 : mword 21) ra_idx
              (mword_of_int CatSyms.putc) (mword_of_int 0x54e) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hputc; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hputc; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_54a with "Hcode"). }
    iIntros (h6) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x54e : mword 64)]> m3).
    assert (Hra4 : m4 !!! Regidx ra_idx = (mword_of_int 0x54e : mword 64))
      by exact (upd_eq m3 (Regidx ra_idx) (regval_into_reg _)).
    (* ---- putc(fd, c) ---- *)
    iApply (wp_kcat_putc γt γd γs h6 m4 n with "Hcode Hrun").
    iIntros (h7 m5) "%Hcs Hrun".
    assert (Eret : ret_pc (m4 !!! Regidx ra_idx) = (mword_of_int 0x54e : mword 64))
      by (rewrite Hra4; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    (* the invariant crossed the call, because every register it names is
       callee-saved -- which is why ulib parked them there *)
    assert (Hinv5 : vp_inv m0 m5 sp0 a fd ap i).
    { apply (vp_inv_call m0 m4 m5 sp0 a fd ap i Hcs).
      apply (vp_inv_upd _ _ _ _ _ _ _ ra_idx _ ltac:(vm_compute; reflexivity)).
      apply (vp_inv_upd _ _ _ _ _ _ _ a0_idx _ ltac:(vm_compute; reflexivity)).
      apply (vp_inv_upd _ _ _ _ _ _ _ a1_idx _ ltac:(vm_compute; reflexivity)).
      apply (vp_inv_upd _ _ _ _ _ _ _ a5_idx _ ltac:(vm_compute; reflexivity)).
      unfold vp_inv. repeat (split; [ assumption | ]). exact Hfr. }
    destruct Hinv5 as (Hsp5 & Hs05 & Hs25 & Hs35 & Hs45 & Hs55 & Hs65 & Hs75 & Hs85 & Hfr5).
    (* ---- 0x54e  c.j 0x554 ---- *)
    assert (Etgt514 : (mword_of_int 0x554 : mword 64)
                      = add_vec (mword_of_int 0x54e : mword 64)
                          (sign_extend' 64
                             (sign_extend' 21
                                (concat_vec (mword_of_int 3 : mword 11) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cj γt γd γs h7 m5 (mword_of_int 0x54e)
              (mword_of_int 3 : mword 11) (mword_of_int 0x554) (4 + n)
              Etgt514 ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_54e with "Hcode"). }
    iIntros (h8) "Hrun".
    (* ---- 0x554  addiw a5,s2,1 ---- *)
    assert (Es1_12 : (sign_extend' 64 (mword_of_int 1 : mword 12) : mword 64)
                     = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Ea5n : sign_extend' 64
                     (subrange_vec_dec
                        (add_vec (m5 !!! Regidx s2_idx)
                           (sign_extend' 64 (mword_of_int 1 : mword 12))) 31 0)
                   = (mword_of_int (Z.of_nat (S i)) : mword 64)).
    { rewrite Hs25 Es1_12.
      assert (Hiw : 0 <= Z.of_nat i + 1 < Z31) by (unfold Z31; lia).
      rewrite (moi_addw (Z.of_nat i) 1 Hiw).
      f_equal. lia. }
    iApply (wp_uk_addiw γt γd γs h8 m5 (mword_of_int 0x554)
              (mword_of_int 1 : mword 12) s2_idx a5_idx
              (mword_of_int (Z.of_nat (S i))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Ea5n))
              with "[] Hrun").
    { iApply (uis_cat_554 with "Hcode"). }
    assert (E51a : add_vec_int (mword_of_int 0x554 : mword 64) 4
                   = mword_of_int 0x558)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E51a.
    iIntros (h9) "Hrun".
    set (m6 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int (Z.of_nat (S i)) : mword 64)]> m5).
    assert (Ha56 : m6 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i)))
      by exact (upd_eq m5 (Regidx a5_idx) (regval_into_reg _)).
    assert (Hinv6 : vp_inv m0 m6 sp0 a fd ap i)
      by (apply (vp_inv_upd _ _ _ _ _ _ _ a5_idx _ ltac:(vm_compute; reflexivity));
          unfold vp_inv; repeat (split; [ assumption | ]); exact Hfr5).
    (* ---- 0x558  c.mv s2,a5 -- the index moves ---- *)
    assert (Ez6 : add_vec zero_reg (m6 !!! Regidx a5_idx)
                  = mword_of_int (Z.of_nat (S i)))
      by (rewrite Ha56; apply add_vec_zero_l).
    iApply (wp_uk_cmv γt γd γs h9 m6 (mword_of_int 0x558) s2_idx a5_idx
              (add_vec zero_reg (m6 !!! Regidx a5_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_558 with "Hcode"). }
    assert (E51e : add_vec_int (mword_of_int 0x558 : mword 64) 2
                   = mword_of_int 0x55a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E51e.
    iIntros (h10) "Hrun".
    set (m7 := <[Regidx s2_idx
                 := regval_into_reg (add_vec zero_reg (m6 !!! Regidx a5_idx))]> m6).
    assert (Hinv7 : vp_inv m0 m7 sp0 a fd ap (S i))
      by exact (vp_inv_bump m0 m6 sp0 a fd ap i (S i) _ Ez6 Hinv6).
    assert (Ha57 : m7 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite <- Ha56.
      exact (upd_ne m6 (Regidx s2_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x55a  c.mv a4,a5 ---- *)
    iApply (wp_uk_cmv γt γd γs h10 m7 (mword_of_int 0x55a) a4_idx a5_idx
              (add_vec zero_reg (m7 !!! Regidx a5_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_55a with "Hcode"). }
    assert (E520 : add_vec_int (mword_of_int 0x55a : mword 64) 2
                   = mword_of_int 0x55c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E520.
    iIntros (h11) "Hrun".
    set (m8 := <[Regidx a4_idx
                 := regval_into_reg (add_vec zero_reg (m7 !!! Regidx a5_idx))]> m7).
    assert (Hinv8 : vp_inv m0 m8 sp0 a fd ap (S i))
      by exact (vp_inv_upd m0 m7 sp0 a fd ap (S i) a4_idx _
                  ltac:(vm_compute; reflexivity) Hinv7).
    assert (Ha58 : m8 !!! Regidx a5_idx = mword_of_int (Z.of_nat (S i))).
    { rewrite <- Ha57.
      exact (upd_ne m7 (Regidx a4_idx) (Regidx a5_idx) _
               ltac:(vm_compute; discriminate)). }
    destruct Hinv8 as (Hsp8 & Hs08 & Hs28 & Hs38 & Hs48 & Hs58 & Hs68 & Hs78 & Hs88 & Hfr8).
    (* ---- 0x55c  c.add a5,a5,s4 -- the pointer ---- *)
    assert (Eadd8 : add_vec (m8 !!! Regidx a5_idx) (m8 !!! Regidx s4_idx)
                    = mword_of_int (a + Z.of_nat (S i))).
    { rewrite Ha58 Hs48. rewrite moi_add. f_equal. lia. }
    iApply (wp_uk_cadd γt γd γs h11 m8 (mword_of_int 0x55c) a5_idx s4_idx
              (add_vec (m8 !!! Regidx a5_idx) (m8 !!! Regidx s4_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_55c with "Hcode"). }
    assert (E522 : add_vec_int (mword_of_int 0x55c : mword 64) 2
                   = mword_of_int 0x55e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E522.
    iIntros (h12) "Hrun".
    set (m9 := <[Regidx a5_idx
                 := regval_into_reg
                      (add_vec (m8 !!! Regidx a5_idx)
                         (m8 !!! Regidx s4_idx))]> m8).
    assert (Hinv9 : vp_inv m0 m9 sp0 a fd ap (S i)).
    { apply (vp_inv_upd _ _ _ _ _ _ _ a5_idx _ ltac:(vm_compute; reflexivity)).
      unfold vp_inv. repeat (split; [ assumption | ]). exact Hfr8. }
    assert (Ha59 : m9 !!! Regidx a5_idx = mword_of_int (a + Z.of_nat (S i))).
    { rewrite (upd_eq m8 (Regidx a5_idx) (regval_into_reg _)). exact Eadd8. }
    (* ---- 0x55e  lbu s1,0(a5) -- the NEXT character, out of .rodata ---- *)
    assert (Haddr : (a + Z.of_nat (S i))%Z
                    = uint (m9 !!! Regidx a5_idx)
                      + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Ha59.
      assert (Hb64a : 0 <= a + Z.of_nat (S i) < Z64) by (unfold Z64; lia).
      rewrite (uint_moi (a + Z.of_nat (S i)) Hb64a).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iApply (wp_uk_lbu_text γt γd γs h12 m9 (mword_of_int 0x55e)
              (mword_of_int 0 : mword 12) a5_idx s1_idx
              (a + Z.of_nat (S i)) b1 (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr ltac:(vm_compute; discriminate)
              with "[] Hb1 Hrun").
    { iApply (uis_cat_55e with "Hcode"). }
    assert (E524 : add_vec_int (mword_of_int 0x55e : mword 64) 4
                   = mword_of_int 0x562)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E524.
    iIntros (h13) "Hrun".
    set (m10 := <[Regidx s1_idx
                  := regval_into_reg (zero_extend' 64 b1 : mword 64)]> m9).
    iApply ("Hcont" $! h13 m10 with "[] [] Hrun").
    { iPureIntro.
      exact (vp_inv_upd m0 m9 sp0 a fd ap (S i) s1_idx _
               ltac:(vm_compute; reflexivity) Hinv9). }
    { iPureIntro. rewrite /m10 (upd_eq m9 (Regidx s1_idx) (regval_into_reg _)).
      exact (zext8_moi b1). }
  Qed.


  (* --------------------------------------------------------------------- *)
  (* THE LOOP, by induction on the characters LEFT.  [k+1] of them remain,   *)
  (* the current one is [f i], and the round's own [beqz s1] at 0x562 is     *)
  (* what decides: at [k = 0] the byte it just loaded is the terminator, so  *)
  (* the branch is taken and the walk falls into the epilogue; otherwise it  *)
  (* is a body byte, the branch is not taken, and the head at 0x566 comes    *)
  (* round again one character further on.                                   *)
  (*                                                                        *)
  (* NOTE this is an ORDINARY induction, not a Löb: the string is finite and *)
  (* [utext_str] carries its length.  cat's two loops in main are the       *)
  (* unbounded ones.                                                         *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_loop (m0 : regfile) (sp0 fd ap : mword 64) (a : Z)
      (len : nat) (f : nat -> mword 8) (k : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (forall j : nat, (j < len)%nat -> bv_unsigned (f j) <> 37) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    uint sp0 mod 8 = 0 ->
    96 <= uint sp0 ->
    forall (i : nat) (h : CpuId) (m : regfile) (n : nat),
      (i + S k)%nat = len ->
      vp_inv m0 m sp0 a fd ap i ->
      m !!! Regidx s1_idx = mword_of_int (bv_unsigned (f i)) ->
      cat_code γt -∗
      utext_str γt a len f -∗
      uword γd (uint sp0 - 8) (m0 !!! Regidx ra_idx) -∗
      uword γd (uint sp0 - 16) (m0 !!! Regidx s0_idx) -∗
      uword γd (uint sp0 - 24) (m0 !!! Regidx s1_idx) -∗
      uword γd (uint sp0 - 32) (m0 !!! Regidx s2_idx) -∗
      uword γd (uint sp0 - 40) (m0 !!! Regidx s3_idx) -∗
      uword γd (uint sp0 - 48) (m0 !!! Regidx s4_idx) -∗
      uword γd (uint sp0 - 56) (m0 !!! Regidx s5_idx) -∗
      uword γd (uint sp0 - 64) (m0 !!! Regidx s6_idx) -∗
      uword γd (uint sp0 - 72) (m0 !!! Regidx s7_idx) -∗
      uword γd (uint sp0 - 80) (m0 !!! Regidx s8_idx) -∗
      (∃ w : mword 64, uword γd (uint sp0 - 88) w) -∗
      (∃ w : mword 64, uword γd (uint sp0 - 96) w) -∗
      urun γt γd γs h m (mword_of_int 0x566) (4 + n) -∗
      (∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m0 m' ⌝ -∗
         urun γt γd γs h' m' (ret_pc (m0 !!! Regidx ra_idx)) (12 + (4 + n)) -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hpct Hsp0 Hal8 Hlo.
    induction k as [| k IH ];
      intros i h m n Hik Hinv Hs1;
      iIntros "#Hcode #Hstr Hwra Hws0 Hws1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw11 Hw12 Hrun Hcont";
      iDestruct (utext_str_nonul with "Hstr") as %Hnn;
      assert (Hilt : (i < len)%nat) by lia.
    - (* the LAST character: the byte after it is the terminator *)
      assert (Ei : (S i)%nat = len) by lia.
      iDestruct (utext_str_nul with "Hstr") as "#Hnul".
      iApply (wp_kcat_vprintf_step m0 sp0 fd ap a i (f i) ubyte0 h m n
                Ha0 ltac:(lia) (Hpct i Hilt) Hinv Hs1
                with "Hcode [] Hrun").
      { rewrite Ei. iExact "Hnul". }
      iIntros (h1 m1) "%Hinv1 %Hs11 Hrun".
      (* ---- 0x562  beqz s1,0x736 -- TAKEN: this was the terminator ---- *)
      assert (Ht : true = uv_btaken BEQ (m1 !!! Regidx s1_idx) zero_reg).
      { rewrite Hs11. cbn [uv_btaken].
        replace (bv_unsigned ubyte0) with 0 by (vm_compute; reflexivity).
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      assert (Etgt : add_vec (mword_of_int 0x562 : mword 64)
                       (sign_extend' 64 (mword_of_int 468 : mword 13))
                     = mword_of_int 0x736)
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_uk_btype0 γt γd γs h1 m1 (mword_of_int 0x562)
                (mword_of_int 468 : mword 13) s1_idx BEQ true
                (mword_of_int 0x736) (4 + n) Ht (eq_sym Etgt)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_562 with "Hcode"). }
      iIntros (h2) "Hrun".
      destruct Hinv1 as (Hsp1 & _ & _ & _ & _ & _ & _ & _ & _ & Hfr1).
      iApply (wp_kcat_vprintf_epi h2 m1 m0 sp0 (4 + n)
                Hsp1 Hsp0 Hal8 Hlo Hfr1
                with "Hcode Hwra Hws0 Hws1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw11 Hw12 Hrun Hcont").
    - (* a BODY character: the byte after it is one too *)
      assert (Hslt : (S i < len)%nat) by lia.
      iDestruct (utext_str_byte γt a len f (S i) Hslt with "Hstr") as "#Hb1".
      iApply (wp_kcat_vprintf_step m0 sp0 fd ap a i (f i) (f (S i)) h m n
                Ha0 ltac:(lia) (Hpct i Hilt) Hinv Hs1
                with "Hcode Hb1 Hrun").
      iIntros (h1 m1) "%Hinv1 %Hs11 Hrun".
      (* ---- 0x562  beqz s1,0x736 -- NOT taken: a body byte is not NUL ---- *)
      assert (Hnz : bv_unsigned (f (S i)) <> 0).
      { intro He. apply (Hnn (S i) Hslt). apply bv_eq.
        rewrite He. vm_compute. reflexivity. }
      (* the inner assert is stated in the GOAL's spelling and closed by
         [exact]: [bv_unsigned_in_range 8] fixes the width index at [8 : N]
         while [f (S i) : mword 8] carries [Z_idx 8], and [lia] would see
         two atoms. *)
      assert (Hb1r : 0 <= bv_unsigned (f (S i)) < Z64).
      { assert (HH : 0 <= bv_unsigned (f (S i)) < 256).
        { pose proof (bv_unsigned_in_range 8 (f (S i))) as H0.
          assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
          rewrite Em8 in H0. exact H0. }
        unfold Z64. lia. }
      assert (Hnt : false = uv_btaken BEQ (m1 !!! Regidx s1_idx) zero_reg).
      { rewrite Hs11. cbn [uv_btaken].
        rewrite (moi_eq_zero (bv_unsigned (f (S i))) Hb1r).
        destruct (Z.eqb_spec (bv_unsigned (f (S i))) 0) as [He | _];
          [ exfalso; exact (Hnz He) | reflexivity ]. }
      iApply (wp_uk_btype0 γt γd γs h1 m1 (mword_of_int 0x562)
                (mword_of_int 468 : mword 13) s1_idx BEQ false
                (add_vec (mword_of_int 0x562 : mword 64)
                   (sign_extend' 64 (mword_of_int 468 : mword 13)))
                (4 + n) Hnt eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_cat_562 with "Hcode"). }
      assert (E528 : add_vec_int (mword_of_int 0x562 : mword 64) 4
                     = mword_of_int 0x566)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E528.
      iIntros (h2) "Hrun".
      iApply (IH (S i) h2 m1 n ltac:(lia) Hinv1 Hs11
                with "Hcode Hstr Hwra Hws0 Hws1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw11 Hw12 Hrun Hcont").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* THE PROLOGUE, 0x510 -> 0x566.  Forty instructions that say nothing     *)
  (* about the format string: the frame is carved, twelve callee-saved      *)
  (* words are spilled, the four registers the loop reads are parked, and    *)
  (* fmt[0] is in s1.  Both top-level entries -- the plain one below and     *)
  (* the one that walks a '%s' -- start here, so it is proved once.          *)
  (*                                                                        *)
  (* The contract asks for a NON-EMPTY string.  cat prints four literals    *)
  (* and none of them is empty, and taking [0 < len] deletes the whole       *)
  (* 0x51e arm -- the one that jumps straight to the shared tail with s2..s8 *)
  (* never spilled.  [wp_kcat_vprintf_epi0] still states that arm's shape,  *)
  (* so re-admitting it later is a branch, not a rewrite.                    *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf_pro (a : Z) (len : nat) (f : nat -> mword 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (0 < len)%nat ->
    m !!! Regidx a1_idx = mword_of_int a ->
    cat_code γt -∗
    utext_str γt a len f -∗
    urun γt γd γs h m (mword_of_int CatSyms.vprintf) (12 + (4 + n)) -∗
    (∀ (h' : CpuId) (m' : regfile) (fd ap : mword 64),
       ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0 ⌝ -∗
       ⌜ 96 <= uint (m !!! Regidx csp_rs1) ⌝ -∗
       ⌜ vp_inv m m' (m !!! Regidx csp_rs1) a fd ap 0%nat ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = mword_of_int (bv_unsigned (f 0%nat)) ⌝ -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 8) (m !!! Regidx ra_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 16) (m !!! Regidx s0_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 24) (m !!! Regidx s1_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 32) (m !!! Regidx s2_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 40) (m !!! Regidx s3_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 48) (m !!! Regidx s4_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 56) (m !!! Regidx s5_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 64) (m !!! Regidx s6_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 72) (m !!! Regidx s7_idx) -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 80) (m !!! Regidx s8_idx) -∗
       (∃ w : mword 64, uword γd (uint (m !!! Regidx csp_rs1) - 88) w) -∗
       (∃ w : mword 64, uword γd (uint (m !!! Regidx csp_rs1) - 96) w) -∗
       urun γt γd γs h' m' (mword_of_int 0x566) (4 + n) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hlen Ha1.
    iIntros "#Hcode #Hstr Hrun Hcont".
    iDestruct (utext_str_nonul with "Hstr") as %Hnn.
    destruct cat_syms_pins
      as (_ & _ & _ & _ & Hvprintf & _ & _ & _ & _ & _ & _).
    rewrite Hvprintf.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 96 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                   = bv_unsigned sp0 - 96).
    { replace (- (8 * Z.of_nat 12)) with (-96) by lia.
      exact (uv_avi_neg sp0 96 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp96 : uint (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    = uint sp0 - 96)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (Ho88 : uoff_sdsp (mword_of_int 11 : mword 6) = 88)
      by (vm_compute; reflexivity).
    assert (Ho80 : uoff_sdsp (mword_of_int 10 : mword 6) = 80)
      by (vm_compute; reflexivity).
    assert (Ho72 : uoff_sdsp (mword_of_int 9 : mword 6) = 72)
      by (vm_compute; reflexivity).
    assert (Ho64 : uoff_sdsp (mword_of_int 8 : mword 6) = 64)
      by (vm_compute; reflexivity).
    assert (Ho56 : uoff_sdsp (mword_of_int 7 : mword 6) = 56)
      by (vm_compute; reflexivity).
    assert (Ho48 : uoff_sdsp (mword_of_int 6 : mword 6) = 48)
      by (vm_compute; reflexivity).
    assert (Ho40 : uoff_sdsp (mword_of_int 5 : mword 6) = 40)
      by (vm_compute; reflexivity).
    assert (Ho32 : uoff_sdsp (mword_of_int 4 : mword 6) = 32)
      by (vm_compute; reflexivity).
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0x510  c.addi16sp sp,sp,-96 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs h m (mword_of_int 0x510)
              (mword_of_int 58 : mword 6) 12 (4 + n)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_510 with "Hcode"). }
    iIntros "Hframe".
    assert (E4d6 : add_vec_int (mword_of_int 0x510 : mword 64) 2
                   = mword_of_int 0x512)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E4d6.
    iIntros (h0) "Hrun".
    set (mp1 := <[Regidx csp_rs1
                  := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 12)))]> m).
    assert (Hspp1 : mp1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_12_open with "Hframe")
      as "(_ & [%w1 Hw1] & [%w2 Hw2] & [%w3 Hw3] & [%w4 Hw4] & [%w5 Hw5]
            & [%w6 Hw6] & [%w7 Hw7] & [%w8 Hw8] & [%w9 Hw9] & [%w10 Hw10]
            & Hw11 & Hw12)".
    (* ---- 0x512  c.sdsp ra,88(sp) ---- *)
    assert (Hrra_idx : mp1 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs h0 mp1 (mword_of_int 0x512)
              (mword_of_int 11 : mword 6) ra_idx (uint sp0 - 8) w1 (4 + n)
              ltac:(rewrite Hspp1 Hsp96 Ho88; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_cat_512 with "Hcode"). }
    iIntros "Hw1". rewrite Hrra_idx.
    assert (E4d8 : add_vec_int (mword_of_int 0x512 : mword 64) 2
                 = mword_of_int 0x514)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4d8.
    iIntros (h1) "Hrun".
    (* ---- 0x514  c.sdsp s0,80(sp) ---- *)
    assert (Hrs0_idx : mp1 !!! Regidx s0_idx = m !!! Regidx s0_idx).
    { rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs h1 mp1 (mword_of_int 0x514)
              (mword_of_int 10 : mword 6) s0_idx (uint sp0 - 16) w2 (4 + n)
              ltac:(rewrite Hspp1 Hsp96 Ho80; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_cat_514 with "Hcode"). }
    iIntros "Hw2". rewrite Hrs0_idx.
    assert (E4da : add_vec_int (mword_of_int 0x514 : mword 64) 2
                 = mword_of_int 0x516)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4da.
    iIntros (h2) "Hrun".
    (* ---- 0x516  c.sdsp s1,72(sp) ---- *)
    assert (Hrs1_idx : mp1 !!! Regidx s1_idx = m !!! Regidx s1_idx).
    { rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s1_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs h2 mp1 (mword_of_int 0x516)
              (mword_of_int 9 : mword 6) s1_idx (uint sp0 - 24) w3 (4 + n)
              ltac:(rewrite Hspp1 Hsp96 Ho72; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_cat_516 with "Hcode"). }
    iIntros "Hw3". rewrite Hrs1_idx.
    assert (E4dc : add_vec_int (mword_of_int 0x516 : mword 64) 2
                 = mword_of_int 0x518)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4dc.
    iIntros (h3) "Hrun".
    (* ---- 0x518  c.addi4spn s0,sp,96 -- s0 := the ENTRY sp ---- *)
    assert (Hlt12 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    + 8 * Z.of_nat 12 < Z64).
    { assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
      { pose proof (bv_unsigned_in_range 64 sp0) as H0.
        assert (Em : bv_modulus 64 = 18446744073709551616)
          by (vm_compute; reflexivity).
        rewrite Em in H0. exact H0. }
      clear -Hbsp HR. rewrite Hbsp. unfold Z64. lia. }
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                    (8 * Z.of_nat 12) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 12)))
                 (8 * Z.of_nat 12) ltac:(apply Z.leb_le; reflexivity) Hlt12).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Ec4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 24 : mword 8))
                   : mword 64) = mword_of_int (8 * Z.of_nat 12))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi4spn γt γd γs h3 mp1 (mword_of_int 0x518)
              (mword_of_int 0 : mword 3) (mword_of_int 24 : mword 8) s0_idx sp0
              (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hspp1 Ec4; exact (eq_sym Hup))
              with "[] Hrun").
    { iApply (uis_cat_518 with "Hcode"). }
    assert (E4de : add_vec_int (mword_of_int 0x518 : mword 64) 2
                   = mword_of_int 0x51a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4de.
    iIntros (h4) "Hrun".
    set (mp2 := <[Regidx s0_idx := regval_into_reg sp0]> mp1).
    (* ---- 0x51a  lbu s1,0(a1) -- the FIRST character, out of .rodata ---- *)
    assert (Ha1p : mp2 !!! Regidx a1_idx = mword_of_int a).
    { rewrite <- Ha1. rewrite /mp2
        (upd_ne mp1 (Regidx s0_idx) (Regidx a1_idx) _
           ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx a1_idx) _
                             ltac:(vm_compute; discriminate)). }
    assert (Ha64 : 0 <= a < Z64) by (unfold Z64; lia).
    assert (Haddr0 : a = uint (mp2 !!! Regidx a1_idx)
                         + uoff_i12 (mword_of_int 0 : mword 12)).
    { rewrite Ha1p (uint_moi a Ha64).
      replace (uoff_i12 (mword_of_int 0 : mword 12)) with 0
        by (vm_compute; reflexivity).
      lia. }
    iDestruct (utext_str_byte γt a len f 0%nat ltac:(lia) with "Hstr") as "#Hb0".
    replace (a + Z.of_nat 0)%Z with a in * by lia.
    iApply (wp_uk_lbu_text γt γd γs h4 mp2 (mword_of_int 0x51a)
              (mword_of_int 0 : mword 12) a1_idx s1_idx a (f 0%nat) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              Haddr0 ltac:(vm_compute; discriminate)
              with "[] Hb0 Hrun").
    { iApply (uis_cat_51a with "Hcode"). }
    assert (E4e0 : add_vec_int (mword_of_int 0x51a : mword 64) 4
                   = mword_of_int 0x51e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e0.
    iIntros (h5) "Hrun".
    set (mp3 := <[Regidx s1_idx
                  := regval_into_reg (zero_extend' 64 (f 0%nat) : mword 64)]> mp2).
    assert (Hs1p : mp3 !!! Regidx s1_idx = mword_of_int (bv_unsigned (f 0%nat))).
    { rewrite /mp3 (upd_eq mp2 (Regidx s1_idx) (regval_into_reg _)).
      exact (zext8_moi (f 0%nat)). }
    (* ---- 0x51e  beqz s1,0x744 -- NOT taken: the string is non-empty ---- *)
    assert (Hnz0 : bv_unsigned (f 0%nat) <> 0).
    { intro He. apply (Hnn 0%nat ltac:(lia)). apply bv_eq.
      rewrite He. vm_compute. reflexivity. }
    assert (Hb0r : 0 <= bv_unsigned (f 0%nat) < Z64).
    { assert (HH : 0 <= bv_unsigned (f 0%nat) < 256).
      { pose proof (bv_unsigned_in_range 8 (f 0%nat)) as H0.
        assert (Em8 : bv_modulus 8 = 256) by (vm_compute; reflexivity).
        rewrite Em8 in H0. exact H0. }
      unfold Z64. lia. }
    assert (Hnt0 : false = uv_btaken BEQ (mp3 !!! Regidx s1_idx) zero_reg).
    { rewrite Hs1p. cbn [uv_btaken].
      rewrite (moi_eq_zero (bv_unsigned (f 0%nat)) Hb0r).
      destruct (Z.eqb_spec (bv_unsigned (f 0%nat)) 0) as [He | _];
        [ exfalso; exact (Hnz0 He) | reflexivity ]. }
    iApply (wp_uk_btype0 γt γd γs h5 mp3 (mword_of_int 0x51e)
              (mword_of_int 550 : mword 13) s1_idx BEQ false
              (add_vec (mword_of_int 0x51e : mword 64)
                 (sign_extend' 64 (mword_of_int 550 : mword 13)))
              (4 + n) Hnt0 eq_refl ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_cat_51e with "Hcode"). }
    assert (E4e4 : add_vec_int (mword_of_int 0x51e : mword 64) 4
                   = mword_of_int 0x522)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e4.
    iIntros (h6) "Hrun".
    assert (Hspp3 : mp3 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hspp1.
      rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx csp_rs1) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mp2. exact (upd_ne mp1 (Regidx s0_idx) (Regidx csp_rs1) _
                             ltac:(vm_compute; discriminate)). }
    (* ---- 0x522  c.sdsp s2,64(sp) ---- *)
    assert (Hrs2_idx : mp3 !!! Regidx s2_idx = m !!! Regidx s2_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s2_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s2_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s2_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs h6 mp3 (mword_of_int 0x522)
              (mword_of_int 8 : mword 6) s2_idx (uint sp0 - 32) w4 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho64; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_cat_522 with "Hcode"). }
    iIntros "Hw4". rewrite Hrs2_idx.
    assert (E4e8 : add_vec_int (mword_of_int 0x522 : mword 64) 2
                 = mword_of_int 0x524)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4e8.
    iIntros (h7) "Hrun".
    (* ---- 0x524  c.sdsp s3,56(sp) ---- *)
    assert (Hrs3_idx : mp3 !!! Regidx s3_idx = m !!! Regidx s3_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s3_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs h7 mp3 (mword_of_int 0x524)
              (mword_of_int 7 : mword 6) s3_idx (uint sp0 - 40) w5 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho56; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_cat_524 with "Hcode"). }
    iIntros "Hw5". rewrite Hrs3_idx.
    assert (E4ea : add_vec_int (mword_of_int 0x524 : mword 64) 2
                 = mword_of_int 0x526)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4ea.
    iIntros (h8) "Hrun".
    (* ---- 0x526  c.sdsp s4,48(sp) ---- *)
    assert (Hrs4_idx : mp3 !!! Regidx s4_idx = m !!! Regidx s4_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s4_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs h8 mp3 (mword_of_int 0x526)
              (mword_of_int 6 : mword 6) s4_idx (uint sp0 - 48) w6 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho48; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_cat_526 with "Hcode"). }
    iIntros "Hw6". rewrite Hrs4_idx.
    assert (E4ec : add_vec_int (mword_of_int 0x526 : mword 64) 2
                 = mword_of_int 0x528)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4ec.
    iIntros (h9) "Hrun".
    (* ---- 0x528  c.sdsp s5,40(sp) ---- *)
    assert (Hrs5_idx : mp3 !!! Regidx s5_idx = m !!! Regidx s5_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s5_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs h9 mp3 (mword_of_int 0x528)
              (mword_of_int 5 : mword 6) s5_idx (uint sp0 - 56) w7 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw7 Hrun").
    { iApply (uis_cat_528 with "Hcode"). }
    iIntros "Hw7". rewrite Hrs5_idx.
    assert (E4ee : add_vec_int (mword_of_int 0x528 : mword 64) 2
                 = mword_of_int 0x52a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4ee.
    iIntros (h10) "Hrun".
    (* ---- 0x52a  c.sdsp s6,32(sp) ---- *)
    assert (Hrs6_idx : mp3 !!! Regidx s6_idx = m !!! Regidx s6_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s6_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs h10 mp3 (mword_of_int 0x52a)
              (mword_of_int 4 : mword 6) s6_idx (uint sp0 - 64) w8 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw8 Hrun").
    { iApply (uis_cat_52a with "Hcode"). }
    iIntros "Hw8". rewrite Hrs6_idx.
    assert (E4f0 : add_vec_int (mword_of_int 0x52a : mword 64) 2
                 = mword_of_int 0x52c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f0.
    iIntros (h11) "Hrun".
    (* ---- 0x52c  c.sdsp s7,24(sp) ---- *)
    assert (Hrs7_idx : mp3 !!! Regidx s7_idx = m !!! Regidx s7_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s7_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs h11 mp3 (mword_of_int 0x52c)
              (mword_of_int 3 : mword 6) s7_idx (uint sp0 - 72) w9 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw9 Hrun").
    { iApply (uis_cat_52c with "Hcode"). }
    iIntros "Hw9". rewrite Hrs7_idx.
    assert (E4f2 : add_vec_int (mword_of_int 0x52c : mword 64) 2
                 = mword_of_int 0x52e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f2.
    iIntros (h12) "Hrun".
    (* ---- 0x52e  c.sdsp s8,16(sp) ---- *)
    assert (Hrs8_idx : mp3 !!! Regidx s8_idx = m !!! Regidx s8_idx).
    { rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx s8_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_csdsp γt γd γs h12 mp3 (mword_of_int 0x52e)
              (mword_of_int 2 : mword 6) s8_idx (uint sp0 - 80) w10 (4 + n)
              ltac:(rewrite Hspp3 Hsp96 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw10 Hrun").
    { iApply (uis_cat_52e with "Hcode"). }
    iIntros "Hw10". rewrite Hrs8_idx.
    assert (E4f4 : add_vec_int (mword_of_int 0x52e : mword 64) 2
                 = mword_of_int 0x530)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f4.
    iIntros (h13) "Hrun".
    (* ---- 0x530  c.mv s6,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs h13 mp3 (mword_of_int 0x530) s6_idx a0_idx
              (add_vec zero_reg (mp3 !!! Regidx a0_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_530 with "Hcode"). }
    assert (E4f6 : add_vec_int (mword_of_int 0x530 : mword 64) 2
                 = mword_of_int 0x532)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f6.
    iIntros (h14) "Hrun".
    set (mp4 := <[Regidx s6_idx := regval_into_reg (add_vec zero_reg (mp3 !!! Regidx a0_idx))]> mp3).
    (* ---- 0x532  c.mv s4,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs h14 mp4 (mword_of_int 0x532) s4_idx a1_idx
              (add_vec zero_reg (mp4 !!! Regidx a1_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_532 with "Hcode"). }
    assert (E4f8 : add_vec_int (mword_of_int 0x532 : mword 64) 2
                 = mword_of_int 0x534)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4f8.
    iIntros (h15) "Hrun".
    set (mp5 := <[Regidx s4_idx := regval_into_reg (add_vec zero_reg (mp4 !!! Regidx a1_idx))]> mp4).
    (* ---- 0x534  c.mv s7,a2 ---- *)
    iApply (wp_uk_cmv γt γd γs h15 mp5 (mword_of_int 0x534) s7_idx a2_idx
              (add_vec zero_reg (mp5 !!! Regidx a2_idx)) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_534 with "Hcode"). }
    assert (E4fa : add_vec_int (mword_of_int 0x534 : mword 64) 2
                 = mword_of_int 0x536)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4fa.
    iIntros (h16) "Hrun".
    set (mp6 := <[Regidx s7_idx := regval_into_reg (add_vec zero_reg (mp5 !!! Regidx a2_idx))]> mp5).
    (* ---- 0x536  c.li s3,0 ---- *)
    iApply (wp_uk_cli γt γd γs h16 mp6 (mword_of_int 0x536)
              (mword_of_int 0 : mword 6) s3_idx (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_536 with "Hcode"). }
    assert (E4fc : add_vec_int (mword_of_int 0x536 : mword 64) 2
                 = mword_of_int 0x538)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4fc.
    iIntros (h17) "Hrun".
    set (mp7 := <[Regidx s3_idx := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> mp6).
    (* ---- 0x538  c.li s2,0 ---- *)
    iApply (wp_uk_cli γt γd γs h17 mp7 (mword_of_int 0x538)
              (mword_of_int 0 : mword 6) s2_idx (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_538 with "Hcode"). }
    assert (E4fe : add_vec_int (mword_of_int 0x538 : mword 64) 2
                 = mword_of_int 0x53a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E4fe.
    iIntros (h18) "Hrun".
    set (mp8 := <[Regidx s2_idx := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> mp7).
    (* ---- 0x53a  c.li a4,0 ---- *)
    iApply (wp_uk_cli γt γd γs h18 mp8 (mword_of_int 0x53a)
              (mword_of_int 0 : mword 6) a4_idx (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_53a with "Hcode"). }
    assert (E500 : add_vec_int (mword_of_int 0x53a : mword 64) 2
                 = mword_of_int 0x53c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E500.
    iIntros (h19) "Hrun".
    set (mp9 := <[Regidx a4_idx := regval_into_reg (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64)]> mp8).
    (* ---- 0x53c  li s5,37 ---- *)
    iApply (wp_uk_li γt γd γs h19 mp9 (mword_of_int 0x53c)
              (mword_of_int 37 : mword 12) s5_idx
              (add_vec zero_reg (sign_extend' 64 (mword_of_int 37 : mword 12))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_53c with "Hcode"). }
    assert (E502 : add_vec_int (mword_of_int 0x53c : mword 64) 4
                 = mword_of_int 0x540)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E502.
    iIntros (h20) "Hrun".
    set (mp10 := <[Regidx s5_idx := regval_into_reg (add_vec zero_reg (sign_extend' 64 (mword_of_int 37 : mword 12)))]> mp9).
    (* ---- 0x540  li s8,100 ---- *)
    iApply (wp_uk_li γt γd γs h20 mp10 (mword_of_int 0x540)
              (mword_of_int 100 : mword 12) s8_idx
              (add_vec zero_reg (sign_extend' 64 (mword_of_int 100 : mword 12))) (4 + n)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_540 with "Hcode"). }
    assert (E506 : add_vec_int (mword_of_int 0x540 : mword 64) 4
                 = mword_of_int 0x544)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E506.
    iIntros (h21) "Hrun".
    set (mp11 := <[Regidx s8_idx := regval_into_reg (add_vec zero_reg (sign_extend' 64 (mword_of_int 100 : mword 12)))]> mp10).
    (* ---- 0x544  c.j 0x566 -- into the loop ---- *)
    assert (Etgt50a : (mword_of_int 0x566 : mword 64)
                      = add_vec (mword_of_int 0x544 : mword 64)
                          (sign_extend' 64
                             (sign_extend' 21
                                (concat_vec (mword_of_int 17 : mword 11) ('b"0")))))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cj γt γd γs h21 mp11 (mword_of_int 0x544)
              (mword_of_int 17 : mword 11) (mword_of_int 0x566) (4 + n)
              Etgt50a ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_544 with "Hcode"). }
    iIntros (h22) "Hrun".

    (* the argument registers, as they stand when the moves read them *)
    assert (Ha1p4 : mp4 !!! Regidx a1_idx = mword_of_int a).
    { rewrite <- Ha1p.
      rewrite /mp4. exact (upd_ne mp3 (Regidx s6_idx) (Regidx a1_idx) _
                             ltac:(vm_compute; discriminate)). }
    assert (Hz_csp_rs1 : mp11 !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp4 (upd_ne mp3 (Regidx s6_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp1 (upd_eq m (Regidx csp_rs1) _).
      reflexivity.
    }
    assert (Hz_s0_idx : mp11 !!! Regidx s0_idx = sp0).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp4 (upd_ne mp3 (Regidx s6_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp2 (upd_eq mp1 (Regidx s0_idx) _).
      reflexivity.
    }
    assert (Hz_s2_idx : mp11 !!! Regidx s2_idx = mword_of_int (Z.of_nat 0)).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s2_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_eq mp7 (Regidx s2_idx) _).
      apply bv_eq; vm_compute; reflexivity.
    }
    assert (Hz_s3_idx : mp11 !!! Regidx s3_idx = zero_reg).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s3_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_eq mp6 (Regidx s3_idx) _).
      rewrite zero_reg_moi. apply bv_eq; vm_compute; reflexivity.
    }
    assert (Hz_s4_idx : mp11 !!! Regidx s4_idx = mword_of_int a).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx s4_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp5 (upd_eq mp4 (Regidx s4_idx) _).
      rewrite Ha1p4. apply add_vec_zero_l.
    }
    assert (Hz_s5_idx : mp11 !!! Regidx s5_idx = mword_of_int 37).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s5_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_eq mp9 (Regidx s5_idx) _).
      rewrite add_vec_zero_l. apply bv_eq; vm_compute; reflexivity.
    }
    assert (Hz_s6_idx : mp11 !!! Regidx s6_idx = add_vec zero_reg (mp3 !!! Regidx a0_idx)).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx s6_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp4 (upd_eq mp3 (Regidx s6_idx) _).
      reflexivity.
    }
    assert (Hz_s7_idx : mp11 !!! Regidx s7_idx
                        = add_vec zero_reg (mp5 !!! Regidx a2_idx)).
    {
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx s7_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_eq mp5 (Regidx s7_idx) _).
      reflexivity.
    }
    assert (Hz_s8_idx : mp11 !!! Regidx s8_idx = mword_of_int 100).
    {
      rewrite /mp11 (upd_eq mp10 (Regidx s8_idx) _).
      rewrite add_vec_zero_l. apply bv_eq; vm_compute; reflexivity.
    }
    assert (Hinv0 : vp_inv m mp11 sp0 a
                      (add_vec zero_reg (mp3 !!! Regidx a0_idx))
                      (add_vec zero_reg (mp5 !!! Regidx a2_idx)) 0%nat).
    { unfold vp_inv.
      split; [ exact Hz_csp_rs1 | ].
      split; [ exact Hz_s0_idx | ].
      split; [ exact Hz_s2_idx | ].
      split; [ exact Hz_s3_idx | ].
      split; [ exact Hz_s4_idx | ].
      split; [ exact Hz_s5_idx | ].
      split; [ exact Hz_s6_idx | ].
      split; [ exact Hz_s7_idx | ].
      split; [ exact Hz_s8_idx | ].
      intros r Hr Hset.
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s8_idx) with 24
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s5_idx) with 21
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint a4_idx) with 14
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s2_idx) with 18
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s3_idx) with 19
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s7_idx) with 23
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s4_idx) with 20
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp4 (upd_ne mp3 (Regidx s6_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s6_idx) with 22
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp3 (upd_ne mp2 (Regidx s1_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s1_idx) with 9
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint s0_idx) with 8
                         by (vm_compute; reflexivity); lia)).
      rewrite /mp1 (upd_ne m (Regidx csp_rs1) (Regidx r) _
                 ltac:(apply not_eq_sym; apply uidx_ne;
                       replace (uint csp_rs1) with 2
                         by (vm_compute; reflexivity); lia)).
      reflexivity. }
    assert (Hs1z : mp11 !!! Regidx s1_idx = mword_of_int (bv_unsigned (f 0%nat))).
    { rewrite <- Hs1p.
      rewrite /mp11 (upd_ne mp10 (Regidx s8_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp10 (upd_ne mp9 (Regidx s5_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp9 (upd_ne mp8 (Regidx a4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp8 (upd_ne mp7 (Regidx s2_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp7 (upd_ne mp6 (Regidx s3_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp6 (upd_ne mp5 (Regidx s7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp5 (upd_ne mp4 (Regidx s4_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /mp4 (upd_ne mp3 (Regidx s6_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      reflexivity. }
    iApply ("Hcont" $! h22 mp11
              (add_vec zero_reg (mp3 !!! Regidx a0_idx))
              (add_vec zero_reg (mp5 !!! Regidx a2_idx))
              with "[] [] [] [] Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10
                    Hw11 Hw12 Hrun").
    - iPureIntro. exact Hal8.
    - iPureIntro. exact Hlo.
    - iPureIntro. exact Hinv0.
    - iPureIntro. exact Hs1z.
  Qed.


  (* --------------------------------------------------------------------- *)
  (* vprintf(fd, fmt, ap) @0x510, for a format string with no '%'.           *)
  (*                                                                        *)
  (* The contract asks for a NON-EMPTY string.  cat prints four literals    *)
  (* and none of them is empty, and taking [0 < len] deletes the whole       *)
  (* 0x51e arm -- the one that jumps straight to the shared tail with s2..s8 *)
  (* never spilled.  [wp_kcat_vprintf_epi0] still states that arm's shape,  *)
  (* so re-admitting it later is a branch, not a rewrite.                    *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_vprintf (a : Z) (len : nat) (f : nat -> mword 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (0 < len)%nat ->
    (forall j : nat, (j < len)%nat -> bv_unsigned (f j) <> 37) ->
    m !!! Regidx a1_idx = mword_of_int a ->
    cat_code γt -∗
    utext_str γt a len f -∗
    urun γt γd γs h m (mword_of_int CatSyms.vprintf) (12 + (4 + n)) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs h' m' (ret_pc (m !!! Regidx ra_idx)) (12 + (4 + n)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hlen Hpct Ha1.
    iIntros "#Hcode #Hstr Hrun Hcont".
    iApply (wp_kcat_vprintf_pro a len f h m n Ha0 Habnd Hlen Ha1
              with "Hcode Hstr Hrun").
    iIntros (h' m' fd ap) "%Hal8 %Hlo %Hinv0 %Hs1z
                           Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10
                           Hw11 Hw12 Hrun".
    assert (Hk0 : (0 + S (len - 1))%nat = len) by lia.
    iApply (wp_kcat_vprintf_loop m (m !!! Regidx csp_rs1) fd ap a len f
              (len - 1)%nat Ha0 Habnd Hpct eq_refl Hal8 Hlo
              0%nat h' m' n Hk0 Hinv0 Hs1z
              with "Hcode Hstr Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12 Hrun Hcont").
  Qed.


End UkCatVprintf.
