(* ===================================================================== *)
(* UkCatFprintf.v -- ulib's [fprintf(fd, fmt, ...)], for a format string   *)
(* with no '%'.                                                            *)
(*                                                                        *)
(* fprintf is printf without the two moves: (fd, fmt) are ALREADY a0 and   *)
(* a1 on entry, so it only marshals the varargs it will not read and tail- *)
(* calls vprintf.  Its frame is ten words, not printf's twelve, and s0     *)
(* sits at sp0-48 rather than sp0-64 -- the spill area is [0(s0)]..        *)
(* [40(s0)] and the va_list is parked at [-24(s0)].                        *)
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
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeCat.
Require Import TsoCtx.
Require User.CatSyms User.InitInstrs.
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkCatVprintf.
Require Import UkCatVprintfS.

Local Open Scope Z_scope.
Import Defs.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Section UkCatFprintf.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

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
    urun γt γd γs γfd h m (mword_of_int 0x744) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = vs1 ⌝ -∗
       ⌜ forall r : mword 5,
           Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
           Regidx r <> Regidx s1_idx -> Regidx r <> Regidx ra_idx ->
           m' !!! Regidx r = m !!! Regidx r ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc vra) (12 + n) -∗
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
    iApply (wp_uk_cldsp γt γd γs γfd h m (mword_of_int 0x744)
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
    iApply (wp_uk_cldsp γt γd γs γfd h1 mm1 (mword_of_int 0x746)
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
    iApply (wp_uk_cldsp γt γd γs γfd h2 mm2 (mword_of_int 0x748)
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
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h3 mm3 (mword_of_int 0x74a)
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
    iApply (wp_uk_cjr γt γd γs γfd h4 mm4 (mword_of_int 0x74c) ra_idx
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
    urun γt γd γs γfd h m (mword_of_int 0x736) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m0 m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m0 !!! Regidx ra_idx)) (12 + n) -∗
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
    iApply (wp_uk_cldsp γt γd γs γfd h m (mword_of_int 0x736)
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
    iApply (wp_uk_cldsp γt γd γs γfd h1 me1 (mword_of_int 0x738)
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
    iApply (wp_uk_cldsp γt γd γs γfd h2 me2 (mword_of_int 0x73a)
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
    iApply (wp_uk_cldsp γt γd γs γfd h3 me3 (mword_of_int 0x73c)
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
    iApply (wp_uk_cldsp γt γd γs γfd h4 me4 (mword_of_int 0x73e)
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
    iApply (wp_uk_cldsp γt γd γs γfd h5 me5 (mword_of_int 0x740)
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
    iApply (wp_uk_cldsp γt γd γs γfd h6 me6 (mword_of_int 0x742)
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
  Local Notation a6_idx := (mword_of_int 16 : mword 5).

  (* --------------------------------------------------------------------- *)
  (* fprintf(fd, fmt) @0x7d0.  The frame, down from the entry sp:            *)
  (*                                                                        *)
  (*   sp0-8  a7   sp0-16 a6   sp0-24 a5   sp0-32 a4   sp0-40 a3            *)
  (*   sp0-48 a2   sp0-56 ra   sp0-64 s0   sp0-72 ap   sp0-80 --            *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_fprintf_gen (a : Z) (h : CpuId) (m : regfile) (n : nat) :
    m !!! Regidx a1_idx = mword_of_int a ->
    cat_code γt -∗
    (* the call at 0x7ee, left to the caller.  fprintf's own instructions
       say nothing about the format string -- they carve the frame, spill
       a2..a7 into it, point a2 at the spill area and jump -- and two
       callers want two different things out of that jump.  The word at
       sp0-48 is the a2 slot, which IS the va_list's first element, so it
       goes to the callee and comes back. *)
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ m' !!! Regidx a1_idx = mword_of_int a ⌝ -∗
       ⌜ m' !!! Regidx a2_idx
         = mword_of_int (uint (m !!! Regidx csp_rs1) - 48) ⌝ -∗
       ⌜ m' !!! Regidx ra_idx = (mword_of_int 0x7f2 : mword 64) ⌝ -∗
       uword γd (uint (m !!! Regidx csp_rs1) - 48) (m !!! Regidx a2_idx) -∗
       urun γt γd γs γfd h' m' (mword_of_int CatSyms.vprintf) (12 + (4 + n)) -∗
       (∀ (h'' : CpuId) (m'' : regfile),
          ⌜ ucallee_saved m' m'' ⌝ -∗
          uword γd (uint (m !!! Regidx csp_rs1) - 48) (m !!! Regidx a2_idx) -∗
          urun γt γd γs γfd h'' m'' (mword_of_int 0x7f2) (12 + (4 + n)) -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang)) -∗
    urun γt γd γs γfd h m (mword_of_int CatSyms.fprintf) (10 + (12 + (4 + n))) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + (12 + (4 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha1r.
    iIntros "#Hcode Hvp Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & _ & Hfprintf & Hvprintf & _ & _ & _ & _ & _ & _).
    rewrite Hfprintf.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 80 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                   = bv_unsigned sp0 - 80).
    { replace (- (8 * Z.of_nat 10)) with (-80) by lia.
      exact (uv_avi_neg sp0 80 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp80 : uint (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                    = uint sp0 - 80)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt10 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                    + 8 * Z.of_nat 10 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                    (8 * Z.of_nat 10) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                 (8 * Z.of_nat 10) ltac:(apply Z.leb_le; reflexivity) Hlt10).
      clear -Hbsp. rewrite Hbsp. lia. }
    assert (Ho24 : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
      by (vm_compute; reflexivity).
    assert (Ho16 : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
      by (vm_compute; reflexivity).
    (* ---- 0x7d0  c.addi16sp sp,sp,-80 ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x7d0)
              (mword_of_int 59 : mword 6) 10 (12 + (4 + n))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_7d0 with "Hcode"). }
    iIntros "Hframe".
    assert (E7d0 : add_vec_int (mword_of_int 0x7d0 : mword 64) 2
                   = mword_of_int 0x7d2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E7d0.
    iIntros (h0) "Hrun".
    set (mq1 := <[Regidx csp_rs1
                  := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 10)))]> m).
    assert (Hspq1 : mq1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 10)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_10_open with "Hframe")
      as "(_ & [%u1 Hu1] & [%u2 Hu2] & [%u3 Hu3] & [%u4 Hu4] & [%u5 Hu5]
            & [%u6 Hu6] & [%u7 Hu7] & [%u8 Hu8] & [%u9 Hu9] & Hu10)".
    (* ---- 0x7d2  c.sdsp ra,24(sp) ---- *)
    assert (Hraq1 : mq1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hs0q1 : mq1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uk_csdsp γt γd γs γfd h0 mq1 (mword_of_int 0x7d2)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 56) u7 (12 + (4 + n))
              ltac:(rewrite Hspq1 Hsp80 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu7 Hrun").
    { iApply (uis_cat_7d2 with "Hcode"). }
    iIntros "Hu7". rewrite Hraq1.
    assert (E7d2 : add_vec_int (mword_of_int 0x7d2 : mword 64) 2
                   = mword_of_int 0x7d4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d2.
    iIntros (h1) "Hrun".
    (* ---- 0x7d4  c.sdsp s0,16(sp) ---- *)
    iApply (wp_uk_csdsp γt γd γs γfd h1 mq1 (mword_of_int 0x7d4)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 64) u8 (12 + (4 + n))
              ltac:(rewrite Hspq1 Hsp80 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu8 Hrun").
    { iApply (uis_cat_7d4 with "Hcode"). }
    iIntros "Hu8". rewrite Hs0q1.
    assert (E7d4 : add_vec_int (mword_of_int 0x7d4 : mword 64) 2
                   = mword_of_int 0x7d6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d4.
    iIntros (h2) "Hrun".
    (* ---- 0x7d6  c.addi4spn s0,sp,32 -- s0 sits at sp0-48 ---- *)
    assert (Hs048 : add_vec (mq1 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8)))
                    = add_vec_int sp0 (- 48)).
    { rewrite Hspq1.
      assert (Ec32 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))
                      : mword 64) = mword_of_int 32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite Ec32.
      assert (Efold : add_vec (add_vec_int sp0 (- (8 * Z.of_nat 10)))
                        (mword_of_int 32)
                      = add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 10))) 32)
        by reflexivity.
      rewrite Efold. apply bv_eq.
      assert (H32 : (0 <= 32)%Z) by lia.
      assert (Hlt32 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 10))) + 32
                      < Z64)
        by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 10))) 32 H32 Hlt32).
      assert (Hlo48 : 48 <= bv_unsigned sp0)
        by (clear -Hlo; rewrite <- uint_unsigned; lia).
      assert (Eneg : bv_unsigned (add_vec_int sp0 (- 48)) = bv_unsigned sp0 - 48)
        by (exact (uv_avi_neg sp0 48 ltac:(apply Z.leb_le; reflexivity) Hlo48)).
      rewrite Eneg Hbsp. lia. }
    iApply (wp_uk_caddi4spn γt γd γs γfd h2 mq1 (mword_of_int 0x7d6)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx
              (add_vec_int sp0 (- 48)) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(exact (eq_sym Hs048))
              with "[] Hrun").
    { iApply (uis_cat_7d6 with "Hcode"). }
    assert (E7d6 : add_vec_int (mword_of_int 0x7d6 : mword 64) 2
                   = mword_of_int 0x7d8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d6.
    iIntros (h3) "Hrun".
    set (mq2 := <[Regidx s0_idx
                  := regval_into_reg (add_vec_int sp0 (- 48))]> mq1).
    assert (Hs0q2 : uint (mq2 !!! Regidx s0_idx) = uint sp0 - 48).
    { rewrite (upd_eq mq1 (Regidx s0_idx) (regval_into_reg _)).
      rewrite !uint_unsigned.
      exact (uv_avi_neg sp0 48 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hspq2 : mq2 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 10))).
    { rewrite <- Hspq1.
      exact (upd_ne mq1 (Regidx s0_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x7d8  c.sd a2,0(s0) ---- *)
    assert (Hoc0 : uoff_c8 (mword_of_int 0 : mword 5) = 0)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs γfd h3 mq2 (mword_of_int 0x7d8)
              (mword_of_int 0 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 4 : mword 3) s0_idx a2_idx
              (uint sp0 - 48) u6 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc0; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu6 Hrun").
    { iApply (uis_cat_7d8 with "Hcode"). }
    iIntros "Hu6".
    assert (E7d8 : add_vec_int (mword_of_int 0x7d8 : mword 64) 2
                 = mword_of_int 0x7da)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7d8.
    iIntros (h4) "Hrun".
    (* ---- 0x7da  c.sd a3,8(s0) ---- *)
    assert (Hoc8 : uoff_c8 (mword_of_int 1 : mword 5) = 8)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs γfd h4 mq2 (mword_of_int 0x7da)
              (mword_of_int 1 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 5 : mword 3) s0_idx a3_idx
              (uint sp0 - 40) u5 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu5 Hrun").
    { iApply (uis_cat_7da with "Hcode"). }
    iIntros "Hu5".
    assert (E7da : add_vec_int (mword_of_int 0x7da : mword 64) 2
                 = mword_of_int 0x7dc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7da.
    iIntros (h5) "Hrun".
    (* ---- 0x7dc  c.sd a4,16(s0) ---- *)
    assert (Hoc16 : uoff_c8 (mword_of_int 2 : mword 5) = 16)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs γfd h5 mq2 (mword_of_int 0x7dc)
              (mword_of_int 2 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 6 : mword 3) s0_idx a4_idx
              (uint sp0 - 32) u4 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu4 Hrun").
    { iApply (uis_cat_7dc with "Hcode"). }
    iIntros "Hu4".
    assert (E7dc : add_vec_int (mword_of_int 0x7dc : mword 64) 2
                 = mword_of_int 0x7de)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7dc.
    iIntros (h6) "Hrun".
    (* ---- 0x7de  c.sd a5,24(s0) ---- *)
    assert (Hoc24 : uoff_c8 (mword_of_int 3 : mword 5) = 24)
      by (vm_compute; reflexivity).
    iApply (wp_uk_csd γt γd γs γfd h6 mq2 (mword_of_int 0x7de)
              (mword_of_int 3 : mword 5) (mword_of_int 0 : mword 3)
              (mword_of_int 7 : mword 3) s0_idx a5_idx
              (uint sp0 - 24) u3 (12 + (4 + n))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs0q2 Hoc24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu3 Hrun").
    { iApply (uis_cat_7de with "Hcode"). }
    iIntros "Hu3".
    assert (E7de : add_vec_int (mword_of_int 0x7de : mword 64) 2
                 = mword_of_int 0x7e0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7de.
    iIntros (h7) "Hrun".
    (* ---- 0x7e0  sd a6,32(s0) ---- *)
    assert (Hoi32 : uoff_i12 (mword_of_int 32 : mword 12) = 32)
      by (vm_compute; reflexivity).
    iApply (wp_uk_sd γt γd γs γfd h7 mq2 (mword_of_int 0x7e0)
              (mword_of_int 32 : mword 12) s0_idx a6_idx
              (uint sp0 - 16) u2 (12 + (4 + n))
              ltac:(rewrite Hs0q2 Hoi32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu2 Hrun").
    { iApply (uis_cat_7e0 with "Hcode"). }
    iIntros "Hu2".
    assert (E7e0 : add_vec_int (mword_of_int 0x7e0 : mword 64) 4
                 = mword_of_int 0x7e4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e0.
    iIntros (h8) "Hrun".
    (* ---- 0x7e4  sd a7,40(s0) ---- *)
    assert (Hoi40 : uoff_i12 (mword_of_int 40 : mword 12) = 40)
      by (vm_compute; reflexivity).
    iApply (wp_uk_sd γt γd γs γfd h8 mq2 (mword_of_int 0x7e4)
              (mword_of_int 40 : mword 12) s0_idx a7_idx
              (uint sp0 - 8) u1 (12 + (4 + n))
              ltac:(rewrite Hs0q2 Hoi40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu1 Hrun").
    { iApply (uis_cat_7e4 with "Hcode"). }
    iIntros "Hu1".
    assert (E7e4 : add_vec_int (mword_of_int 0x7e4 : mword 64) 4
                 = mword_of_int 0x7e8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e4.
    iIntros (h9) "Hrun".
    (* ---- 0x7e8  c.mv a2,s0 -- the va_list ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h9 mq2 (mword_of_int 0x7e8) a2_idx s0_idx
              (add_vec zero_reg (mq2 !!! Regidx s0_idx)) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl
              with "[] Hrun").
    { iApply (uis_cat_7e8 with "Hcode"). }
    assert (E7e8 : add_vec_int (mword_of_int 0x7e8 : mword 64) 2
                   = mword_of_int 0x7ea)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7e8.
    iIntros (h10) "Hrun".
    set (mq3 := <[Regidx a2_idx
                  := regval_into_reg
                       (add_vec zero_reg (mq2 !!! Regidx s0_idx))]> mq2).
    assert (Hs0q3 : uint (mq3 !!! Regidx s0_idx) = uint sp0 - 48).
    { rewrite <- Hs0q2. f_equal;
        exact (upd_ne mq2 (Regidx a2_idx) (Regidx s0_idx) _
                 ltac:(vm_compute; discriminate)). }
    (* ---- 0x7ea  sd s0,-24(s0) -- park it ---- *)
    assert (Hoim24 : uoff_i12 (mword_of_int 4072 : mword 12) = -24)
      by (vm_compute; reflexivity).
    iApply (wp_uk_sd γt γd γs γfd h10 mq3 (mword_of_int 0x7ea)
              (mword_of_int 4072 : mword 12) s0_idx s0_idx
              (uint sp0 - 72) u9 (12 + (4 + n))
              ltac:(rewrite Hs0q3 Hoim24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hu9 Hrun").
    { iApply (uis_cat_7ea with "Hcode"). }
    iIntros "Hu9".
    assert (E7ea : add_vec_int (mword_of_int 0x7ea : mword 64) 4
                   = mword_of_int 0x7ee)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7ea.
    iIntros (h11) "Hrun".
    (* ---- 0x7ee  jal ra,0x510 <vprintf> ---- *)
    assert (Ha1q3 : mq3 !!! Regidx a1_idx = mword_of_int a).
    { rewrite <- Ha1r.
      rewrite /mq3 (upd_ne mq2 (Regidx a2_idx) (Regidx a1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq2 (upd_ne mq1 (Regidx s0_idx) (Regidx a1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq1. exact (upd_ne m (Regidx csp_rs1) (Regidx a1_idx) _
                             ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_jal γt γd γs γfd h11 mq3 (mword_of_int 0x7ee)
              (mword_of_int 2096418 : mword 21) ra_idx
              (mword_of_int CatSyms.vprintf) (mword_of_int 0x7f2) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hvprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hvprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_7ee with "Hcode"). }
    iIntros (h12) "Hrun".
    set (mq4 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x7f2 : mword 64)]> mq3).
    assert (Hraq4 : mq4 !!! Regidx ra_idx = (mword_of_int 0x7f2 : mword 64))
      by exact (upd_eq mq3 (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha1q4 : mq4 !!! Regidx a1_idx = mword_of_int a).
    { rewrite <- Ha1q3.
      exact (upd_ne mq3 (Regidx ra_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- vprintf(fd, fmt, ap) -- whichever one the caller brought ---- *)
    assert (Ha2q2 : mq2 !!! Regidx a2_idx = m !!! Regidx a2_idx).
    { rewrite /mq2 (upd_ne mq1 (Regidx s0_idx) (Regidx a2_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq1. exact (upd_ne m (Regidx csp_rs1) (Regidx a2_idx) _
                             ltac:(vm_compute; discriminate)). }
    iEval (rewrite Ha2q2) in "Hu6".
    assert (Ha2q4 : mq4 !!! Regidx a2_idx = mword_of_int (uint sp0 - 48)).
    { rewrite /mq4 (upd_ne mq3 (Regidx ra_idx) (Regidx a2_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq3 (upd_eq mq2 (Regidx a2_idx) (regval_into_reg _)).
      rewrite add_vec_zero_l.
      rewrite <- Hs0q2. symmetry.
      exact (moi_of_uint (mq2 !!! Regidx s0_idx)). }
    iApply ("Hvp" $! h12 mq4 with "[] [] [] Hu6 Hrun
              [Hu1 Hu2 Hu3 Hu4 Hu5 Hu7 Hu8 Hu9 Hu10 Hcont]").
    { iPureIntro. exact Ha1q4. }
    { iPureIntro. exact Ha2q4. }
    { iPureIntro. exact Hraq4. }
    iIntros (h13 mq5) "%Hcs Hu6 Hrun".
    (* ---- 0x7f2  c.ldsp ra,24(sp) ---- *)
    assert (Hspq5 : mq5 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 10))).
    { rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite <- Hspq2.
      rewrite /mq4 (upd_ne mq3 (Regidx ra_idx) (Regidx csp_rs1) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mq3. exact (upd_ne mq2 (Regidx a2_idx) (Regidx csp_rs1) _
                             ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_cldsp γt γd γs γfd h13 mq5 (mword_of_int 0x7f2)
              (mword_of_int 3 : mword 6) ra_idx (uint sp0 - 56)
              (m !!! Regidx ra_idx) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspq5 Hsp80 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hu7 Hrun").
    { iApply (uis_cat_7f2 with "Hcode"). }
    iIntros "Hu7".
    assert (E7f2 : add_vec_int (mword_of_int 0x7f2 : mword 64) 2
                   = mword_of_int 0x7f4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7f2.
    iIntros (h14) "Hrun".
    set (mq6 := <[Regidx ra_idx
                  := regval_into_reg (m !!! Regidx ra_idx)]> mq5).
    assert (Hspq6 : mq6 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 10))).
    { rewrite <- Hspq5.
      exact (upd_ne mq5 (Regidx ra_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x7f4  c.ldsp s0,16(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs γfd h14 mq6 (mword_of_int 0x7f4)
              (mword_of_int 2 : mword 6) s0_idx (uint sp0 - 64)
              (m !!! Regidx s0_idx) (12 + (4 + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hspq6 Hsp80 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hu8 Hrun").
    { iApply (uis_cat_7f4 with "Hcode"). }
    iIntros "Hu8".
    assert (E7f4 : add_vec_int (mword_of_int 0x7f4 : mword 64) 2
                   = mword_of_int 0x7f6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E7f4.
    iIntros (h15) "Hrun".
    set (mq7 := <[Regidx s0_idx
                  := regval_into_reg (m !!! Regidx s0_idx)]> mq6).
    assert (Hspq7 : mq7 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 10))).
    { rewrite <- Hspq6.
      exact (upd_ne mq6 (Regidx s0_idx) (Regidx csp_rs1) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x7f6  c.addi16sp sp,sp,80 -- the frame goes back ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h15 mq7 (mword_of_int 0x7f6)
              (mword_of_int 5 : mword 6) 10 (12 + (4 + n))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hu1 Hu2 Hu3 Hu4 Hu5 Hu6 Hu7 Hu8 Hu9 Hu10] Hrun").
    { iApply (uis_cat_7f6 with "Hcode"). }
    { rewrite Hspq7 Hup.
      iApply (ustack_10_close γd sp0 Hal8
                with "[Hu1] [Hu2] [Hu3] [Hu4] [Hu5] [Hu6] [Hu7] [Hu8] [Hu9] Hu10").
      { iExists (mq2 !!! Regidx a7_idx). iExact "Hu1". }
      { iExists (mq2 !!! Regidx a6_idx). iExact "Hu2". }
      { iExists (mq2 !!! Regidx a5_idx). iExact "Hu3". }
      { iExists (mq2 !!! Regidx a4_idx). iExact "Hu4". }
      { iExists (mq2 !!! Regidx a3_idx). iExact "Hu5". }
      { iExists (m !!! Regidx a2_idx). iExact "Hu6". }
      { iExists (m !!! Regidx ra_idx). iExact "Hu7". }
      { iExists (m !!! Regidx s0_idx). iExact "Hu8". }
      { iExists (mq3 !!! Regidx s0_idx). iExact "Hu9". } }
    assert (E7f6 : add_vec_int (mword_of_int 0x7f6 : mword 64) 2
                   = mword_of_int 0x7f8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hspq7 Hup E7f6.
    iIntros (h16) "Hrun".
    set (mq8 := <[Regidx csp_rs1 := regval_into_reg sp0]> mq7).
    assert (Hraq8 : mq8 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /mq8 (upd_ne mq7 (Regidx csp_rs1) (Regidx ra_idx) _
                       ltac:(vm_compute; discriminate)).
      rewrite /mq7 (upd_ne mq6 (Regidx s0_idx) (Regidx ra_idx) _
                       ltac:(vm_compute; discriminate)).
      rewrite /mq6. exact (upd_eq mq5 (Regidx ra_idx) (regval_into_reg _)). }
    (* ---- 0x7f8  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h16 mq8 (mword_of_int 0x7f8) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (10 + (12 + (4 + n)))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraq8; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_7f8 with "Hcode"). }
    iIntros (h17) "Hrun".
    iApply ("Hcont" $! h17 mq8 with "[] Hrun").
    iPureIntro. intros r Hr.
    assert (Kne : forall (q : mword 5) (z : Z),
               uint q = z -> uint r <> z -> Regidx r <> Regidx q).
    { intros q z Hq Hz. apply uidx_ne. rewrite Hq. exact Hz. }
    assert (Huntouched : uint r <> 1 -> uint r <> 2 -> uint r <> 8 ->
                         uint r <> 12 ->
                         mq8 !!! Regidx r = m !!! Regidx r).
    { intros K1 K2 K8 K12.
      rewrite /mq8 (upd_ne mq7 (Regidx csp_rs1) (Regidx r) _
                       (Kne csp_rs1 2 ltac:(vm_compute; reflexivity) K2)).
      rewrite /mq7 (upd_ne mq6 (Regidx s0_idx) (Regidx r) _
                       (Kne s0_idx 8 ltac:(vm_compute; reflexivity) K8)).
      rewrite /mq6 (upd_ne mq5 (Regidx ra_idx) (Regidx r) _
                       (Kne ra_idx 1 ltac:(vm_compute; reflexivity) K1)).
      rewrite (Hcs r Hr).
      rewrite /mq4 (upd_ne mq3 (Regidx ra_idx) (Regidx r) _
                       (Kne ra_idx 1 ltac:(vm_compute; reflexivity) K1)).
      rewrite /mq3 (upd_ne mq2 (Regidx a2_idx) (Regidx r) _
                       (Kne a2_idx 12 ltac:(vm_compute; reflexivity) K12)).
      rewrite /mq2 (upd_ne mq1 (Regidx s0_idx) (Regidx r) _
                       (Kne s0_idx 8 ltac:(vm_compute; reflexivity) K8)).
      rewrite /mq1. exact (upd_ne m (Regidx csp_rs1) (Regidx r) _
                             (Kne csp_rs1 2 ltac:(vm_compute; reflexivity) K2)). }
    destruct (ucs_cases r Hr) as [E2 | [E3 | [E4 | [E8 | [E9 | E18]]]]].
    - assert (Er : Regidx r = Regidx csp_rs1)
        by (apply (uidx_eq r 2); [ exact E2 | vm_compute; reflexivity ]).
      rewrite Er /mq8 (upd_eq mq7 (Regidx csp_rs1) (regval_into_reg sp0)).
      rewrite <- Hsp. reflexivity.
    - apply Huntouched; lia.
    - apply Huntouched; lia.
    - assert (Er : Regidx r = Regidx s0_idx)
        by (apply (uidx_eq r 8); [ exact E8 | vm_compute; reflexivity ]).
      rewrite Er /mq8 (upd_ne mq7 (Regidx csp_rs1) (Regidx s0_idx) _
                          ltac:(vm_compute; discriminate)).
      rewrite /mq7. exact (upd_eq mq6 (Regidx s0_idx) (regval_into_reg _)).
    - apply Huntouched; lia.
    - apply Huntouched; lia.
  Qed.

  (* --------------------------------------------------------------------- *)
  (* fprintf for a format with no directive -- cat's "write error" and      *)
  (* "read error" -- and for the one that has a '%s'.                       *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_fprintf (a : Z) (len : nat) (f : nat -> mword 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (0 < len)%nat ->
    (forall j : nat, (j < len)%nat -> bv_unsigned (f j) <> 37) ->
    m !!! Regidx a1_idx = mword_of_int a ->
    cat_code γt -∗
    utext_str γt a len f -∗
    urun γt γd γs γfd h m (mword_of_int CatSyms.fprintf) (10 + (12 + (4 + n))) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + (12 + (4 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hlen Hpct Ha1.
    iIntros "#Hcode #Hstr Hrun Hcont".
    iApply (wp_kcat_fprintf_gen a h m n Ha1 with "Hcode [] Hrun Hcont").
    iIntros (h' m') "%Ha1' %Ha2' %Hra' Hu6 Hrun Hk".
    iApply (wp_kcat_vprintf γt γd γs γfd a len f h' m' n
              Ha0 Habnd Hlen Hpct Ha1' with "Hcode Hstr Hrun").
    iIntros (h'' m'') "%Hcs Hrun".
    assert (Eret : ret_pc (m' !!! Regidx ra_idx)
                   = (mword_of_int 0x7f2 : mword 64))
      by (rewrite Hra'; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    iApply ("Hk" $! h'' m'' with "[] Hu6 Hrun"). iPureIntro. exact Hcs.
  Qed.

  Lemma wp_kcat_fprintf_s (a : Z) (len q : nat) (f : nat -> mword 8)
      (sa : Z) (slen : nat) (sf : nat -> bv 8)
      (h : CpuId) (m : regfile) (n : nat) :
    0 <= a -> a + Z.of_nat len + 2 < 2 ^ 31 ->
    (S (S q) < len)%nat ->
    bv_unsigned (f q) = 37 ->
    bv_unsigned (f (S q)) = 115 ->
    (forall j : nat, (j < len)%nat -> j <> q -> bv_unsigned (f j) <> 37) ->
    bv_unsigned (f (S (S q))) <> 100 ->
    bv_unsigned (f (S (S q))) <> 117 ->
    bv_unsigned (f (S (S q))) <> 120 ->
    ((S (S (S q)) < len)%nat ->
       bv_unsigned (f (S (S (S q)))) <> 100 /\
       bv_unsigned (f (S (S (S q)))) <> 117 /\
       bv_unsigned (f (S (S (S q)))) <> 120) ->
    sa <> 0 ->
    m !!! Regidx a1_idx = mword_of_int a ->
    m !!! Regidx a2_idx = mword_of_int sa ->
    cat_code γt -∗
    utext_str γt a len f -∗
    ustr γd DfracDiscarded sa slen sf -∗
    urun γt γd γs γfd h m (mword_of_int CatSyms.fprintf) (10 + (12 + (4 + n))) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m m' ⌝ -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + (12 + (4 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Habnd Hq2 Hfq Hfsq Hpct Hc1d Hc1u Hc1x Hc2set Hsanz Ha1 Ha2.
    iIntros "#Hcode #Hstr #Hsstr Hrun Hcont".
    iDestruct (urun_stack with "Hrun") as %[Hal8 _].
    assert (Hapal : (uint (m !!! Regidx csp_rs1) - 48) mod 8 = 0)
      by (rewrite Zminus_mod Hal8; reflexivity).
    iApply (wp_kcat_fprintf_gen a h m n Ha1 with "Hcode [] Hrun Hcont").
    iIntros (h' m') "%Ha1' %Ha2' %Hra' Hu6 Hrun Hk".
    rewrite Ha2.
    iApply (wp_kcat_vprintf_s γt γd γs γfd a len q f
              (uint (m !!! Regidx csp_rs1) - 48) sa (DfracOwn 1) slen sf
              h' m' n Ha0 Habnd Hq2 Hfq Hfsq Hpct Hc1d Hc1u Hc1x Hc2set
              Hapal Hsanz Ha1' Ha2'
              with "Hcode Hstr Hu6 Hsstr Hrun").
    iIntros (h'' m'') "Hu6 %Hcs Hrun".
    assert (Eret : ret_pc (m' !!! Regidx ra_idx)
                   = (mword_of_int 0x7f2 : mword 64))
      by (rewrite Hra'; apply bv_eq; vm_compute; reflexivity).
    rewrite Eret.
    iApply ("Hk" $! h'' m'' with "[] Hu6 Hrun"). iPureIntro. exact Hcs.
  Qed.

End UkCatFprintf.
