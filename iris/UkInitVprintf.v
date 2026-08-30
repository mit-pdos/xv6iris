(* ===================================================================== *)
(* UkInitVprintf.v -- ulib's [vprintf(fd, fmt, ap)] for a format string    *)
(* containing no '%', which is what all four of init's literals are.       *)
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
Require Import UCodeInit.
Require Import TsoCtx.
Require User.InitSyms User.InitInstrs.
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkInit.
Require Import UkInitPutc.

Section UkInitVprintf.
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

  Lemma wp_kinit_vprintf_epi0 (h : CpuId) (m : regfile)
      (sp0 vra vs0 vs1 : mword 64) (n : nat) :
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) ->
    uint sp0 mod 8 = 0 ->
    96 <= uint sp0 ->
    init_code γt -∗
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
    urun γt γd γs h m (mword_of_int 0x70a) n -∗
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
    (* ---- 0x70a  c.ldsp ra,88(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h m (mword_of_int 0x70a)
              (mword_of_int 11 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp96 Ho88; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hwra Hrun").
    { iApply (uis_init_70a with "Hcode"). }
    iIntros "Hwra".
    assert (E70a : add_vec_int (mword_of_int 0x70a : mword 64) 2
                 = mword_of_int 0x70c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70a.
    iIntros (h1) "Hrun".
    set (mm1 := <[Regidx ra_idx := regval_into_reg vra]> m).
    assert (Hsp1 : mm1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx ra_idx) (Regidx csp_rs1) (regval_into_reg vra)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x70c  c.ldsp s0,80(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h1 mm1 (mword_of_int 0x70c)
              (mword_of_int 10 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp96 Ho80; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws0 Hrun").
    { iApply (uis_init_70c with "Hcode"). }
    iIntros "Hws0".
    assert (E70c : add_vec_int (mword_of_int 0x70c : mword 64) 2
                 = mword_of_int 0x70e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70c.
    iIntros (h2) "Hrun".
    set (mm2 := <[Regidx s0_idx := regval_into_reg vs0]> mm1).
    assert (Hsp2 : mm2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp1.
      exact (upd_ne mm1 (Regidx s0_idx) (Regidx csp_rs1) (regval_into_reg vs0)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x70e  c.ldsp s1,72(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h2 mm2 (mword_of_int 0x70e)
              (mword_of_int 9 : mword 6) s1_idx (uint sp0 - 24) vs1 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp2 Hsp96 Ho72; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws1 Hrun").
    { iApply (uis_init_70e with "Hcode"). }
    iIntros "Hws1".
    assert (E70e : add_vec_int (mword_of_int 0x70e : mword 64) 2
                 = mword_of_int 0x710)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70e.
    iIntros (h3) "Hrun".
    set (mm3 := <[Regidx s1_idx := regval_into_reg vs1]> mm2).
    assert (Hsp3 : mm3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp2.
      exact (upd_ne mm2 (Regidx s1_idx) (Regidx csp_rs1) (regval_into_reg vs1)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x710  c.addi16sp sp,sp,96 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs h3 mm3 (mword_of_int 0x710)
              (mword_of_int 6 : mword 6) 12 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hwra Hws0 Hws1 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12] Hrun").
    { iApply (uis_init_710 with "Hcode"). }
    { rewrite Hsp3 Hup.
      iApply (ustack_12_close γd sp0 Hal8
                with "[Hwra] [Hws0] [Hws1] Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12").
      { iExists vra. iExact "Hwra". }
      { iExists vs0. iExact "Hws0". }
      { iExists vs1. iExact "Hws1". } }
    assert (E710 : add_vec_int (mword_of_int 0x710 : mword 64) 2
                   = mword_of_int 0x712)
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
    (* ---- 0x712  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs h4 mm4 (mword_of_int 0x712) ra_idx
              (ret_pc vra) (12 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra4; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_712 with "Hcode"). }
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
  (* vprintf's FULL EPILOGUE @0x6fc: restore s2..s8, then fall into the      *)
  (* shared tail.  This is where [ucallee_saved] is assembled, because this  *)
  (* is where every spilled register is back at its entry value: the ten     *)
  (* frame words are PINNED to [m0]'s registers in the statement, [sp0] is   *)
  (* [m0]'s sp, and [Hfree] covers the five callee-saved registers vprintf   *)
  (* never touches (gp, tp, s9, s10, s11).  [ucs_cases] says there is no      *)
  (* sixteenth.                                                              *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kinit_vprintf_epi (h : CpuId) (m m0 : regfile) (sp0 : mword 64)
      (n : nat) :
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 12)) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    uint sp0 mod 8 = 0 ->
    96 <= uint sp0 ->
    (forall r : mword 5, ucallee_saved_idx r = true ->
       uint r = 3 \/ uint r = 4 \/ (25 <= uint r <= 27) ->
       m !!! Regidx r = m0 !!! Regidx r) ->
    init_code γt -∗
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
    urun γt γd γs h m (mword_of_int 0x6fc) n -∗
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
    (* ---- 0x6fc  c.ldsp s2,64(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h m (mword_of_int 0x6fc)
              (mword_of_int 8 : mword 6) s2_idx (uint sp0 - 32)
              (m0 !!! Regidx s2_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp96 Ho64; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_init_6fc with "Hcode"). }
    iIntros "Hw2".
    assert (E6fc : add_vec_int (mword_of_int 0x6fc : mword 64) 2
                 = mword_of_int 0x6fe)
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
    (* ---- 0x6fe  c.ldsp s3,56(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h1 me1 (mword_of_int 0x6fe)
              (mword_of_int 7 : mword 6) s3_idx (uint sp0 - 40)
              (m0 !!! Regidx s3_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp96 Ho56; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_init_6fe with "Hcode"). }
    iIntros "Hw3".
    assert (E6fe : add_vec_int (mword_of_int 0x6fe : mword 64) 2
                 = mword_of_int 0x700)
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
    (* ---- 0x700  c.ldsp s4,48(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h2 me2 (mword_of_int 0x700)
              (mword_of_int 6 : mword 6) s4_idx (uint sp0 - 48)
              (m0 !!! Regidx s4_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp2 Hsp96 Ho48; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_init_700 with "Hcode"). }
    iIntros "Hw4".
    assert (E700 : add_vec_int (mword_of_int 0x700 : mword 64) 2
                 = mword_of_int 0x702)
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
    (* ---- 0x702  c.ldsp s5,40(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h3 me3 (mword_of_int 0x702)
              (mword_of_int 5 : mword 6) s5_idx (uint sp0 - 56)
              (m0 !!! Regidx s5_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp3 Hsp96 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw5 Hrun").
    { iApply (uis_init_702 with "Hcode"). }
    iIntros "Hw5".
    assert (E702 : add_vec_int (mword_of_int 0x702 : mword 64) 2
                 = mword_of_int 0x704)
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
    (* ---- 0x704  c.ldsp s6,32(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h4 me4 (mword_of_int 0x704)
              (mword_of_int 4 : mword 6) s6_idx (uint sp0 - 64)
              (m0 !!! Regidx s6_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp4 Hsp96 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw6 Hrun").
    { iApply (uis_init_704 with "Hcode"). }
    iIntros "Hw6".
    assert (E704 : add_vec_int (mword_of_int 0x704 : mword 64) 2
                 = mword_of_int 0x706)
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
    (* ---- 0x706  c.ldsp s7,24(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h5 me5 (mword_of_int 0x706)
              (mword_of_int 3 : mword 6) s7_idx (uint sp0 - 72)
              (m0 !!! Regidx s7_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp5 Hsp96 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw7 Hrun").
    { iApply (uis_init_706 with "Hcode"). }
    iIntros "Hw7".
    assert (E706 : add_vec_int (mword_of_int 0x706 : mword 64) 2
                 = mword_of_int 0x708)
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
    (* ---- 0x708  c.ldsp s8,16(sp) ---- *)
    iApply (wp_uk_cldsp γt γd γs h6 me6 (mword_of_int 0x708)
              (mword_of_int 2 : mword 6) s8_idx (uint sp0 - 80)
              (m0 !!! Regidx s8_idx) n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp6 Hsp96 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw8 Hrun").
    { iApply (uis_init_708 with "Hcode"). }
    iIntros "Hw8".
    assert (E708 : add_vec_int (mword_of_int 0x708 : mword 64) 2
                 = mword_of_int 0x70a)
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
    (* ---- 0x70a..0x712: the shared tail ---- *)
    iApply (wp_kinit_vprintf_epi0 h7 me7 sp0 (m0 !!! Regidx ra_idx)
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
End UkInitVprintf.
