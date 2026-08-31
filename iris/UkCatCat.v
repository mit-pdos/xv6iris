(* ===================================================================== *)
(* UkCatCat.v -- cat(fd): the READ/WRITE LOOP.                             *)
(*                                                                        *)
(*   0x22  mv a2,s4 ; mv a1,s2 ; mv a0,s3 ; jal <read>                     *)
(*   0x2c  mv s1,a0 ; blez a0,0x54          -- n <= 0 leaves the loop      *)
(*   0x32  mv a2,s1 ; mv a1,s2 ; mv a0,s5 ; jal <write>                    *)
(*   0x3c  beq a0,s1,0x22                   -- the back edge               *)
(*   0x40  "cat: write error" ; exit(1)                                     *)
(*   0x54  bltz a0,0x6a                     -- n < 0 is a read error        *)
(*   0x58  the epilogue, and cat() returns                                  *)
(*   0x6a  "cat: read error" ; exit(1)                                      *)
(*                                                                        *)
(* THE LOOP IS UNBOUNDED and its every arm is walked, because nothing is   *)
(* assumed about what read returns: it may fill the buffer, fill part of   *)
(* it, return zero at end of file, or fail.  What the proof carries round  *)
(* is the 512-byte buffer at SOME contents -- the read row does not say    *)
(* which bytes moved, so neither does the invariant -- and the six         *)
(* registers ulib parks the loop's state in.                              *)
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
Require Import UkCatVprintf.
Require Import UkCatLit.
Require Import UkCatFprintf.
Require Import UkRunBr.
Require Import UkRunBr.

Local Open Scope Z_scope.
Import Defs.

Local Open Scope Z_scope.
Import Defs.

Section UkCatCat.
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





  Lemma wp_kcat_cat_die_cw (hcw : CpuId) (mcw0 : regfile) (n : nat) :
    cat_code γt -∗ cat_rodata γt -∗
    urun γt γd γs hcw mcw0 (mword_of_int 0x40) (10 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun".
    destruct cat_syms_pins
      as (_ & _ & _ & Hfprintf & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokcw : cat_lit_ok 0x9b0 17%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (cat_lit_str γt 0x9b0 17%nat Hokcw
                 ltac:(vm_compute; reflexivity) with "Hro") as "#Hstrcw".
    (* ---- 0x40  auipc a1 ; 0x44  addi a1 -- the literal ---- *)
    assert (Eacw : add_vec (add_vec (mword_of_int 0x40 : mword 64)
                      (auipc_off (mword_of_int 1 : mword 20)))
                    (sign_extend' 64 (mword_of_int 2416 : mword 12))
                  = mword_of_int 0x9b0)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc γt γd γs hcw mcw0 (mword_of_int 0x40)
              (mword_of_int 1 : mword 20) a1_idx
              (add_vec (mword_of_int 0x40 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_40 with "Hcode"). }
    assert (Eucw : add_vec_int (mword_of_int 0x40 : mword 64) 4
                    = mword_of_int 0x44)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eucw.
    iIntros (hcwa) "Hrun".
    set (cwa := <[Regidx a1_idx := regval_into_reg
                     (add_vec (mword_of_int 0x40 : mword 64)
                        (auipc_off (mword_of_int 1 : mword 20)))]> mcw0).
    iApply (wp_uk_addi γt γd γs hcwa cwa (mword_of_int 0x44)
              (mword_of_int 2416 : mword 12) a1_idx a1_idx
              (mword_of_int 0x9b0) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mcw0 (Regidx a1_idx) (regval_into_reg _));
                    exact (eq_sym Eacw))
              with "[] Hrun").
    { iApply (uis_cat_44 with "Hcode"). }
    assert (Eicw : add_vec_int (mword_of_int 0x44 : mword 64) 4
                    = mword_of_int 0x48)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eicw.
    iIntros (hcwb) "Hrun".
    set (cwb := <[Regidx a1_idx := regval_into_reg
                     (mword_of_int 0x9b0 : mword 64)]> cwa).
    assert (Ha1cw : cwb !!! Regidx a1_idx = mword_of_int 0x9b0)
      by exact (upd_eq cwa (Regidx a1_idx) (regval_into_reg _)).
    (* ---- 0x48  c.li a0,2 -- stderr ---- *)
    iApply (wp_uk_cli γt γd γs hcwb cwb (mword_of_int 0x48)
              (mword_of_int 2 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_48 with "Hcode"). }
    assert (Elcw : add_vec_int (mword_of_int 0x48 : mword 64) 2
                    = mword_of_int 0x4a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Elcw.
    iIntros (hcwc) "Hrun".
    set (cwc := <[Regidx a0_idx := regval_into_reg
                     (sign_extend' 64 (mword_of_int 2 : mword 6)
                      : mword 64)]> cwb).
    assert (Ha1ccw : cwc !!! Regidx a1_idx = mword_of_int 0x9b0).
    { rewrite <- Ha1cw.
      exact (upd_ne cwb (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x4a  jal ra,0x7d0 <fprintf> ---- *)
    iApply (wp_uk_jal γt γd γs hcwc cwc (mword_of_int 0x4a)
              (mword_of_int 1926 : mword 21) ra_idx
              (mword_of_int CatSyms.fprintf) (mword_of_int 0x4e) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hfprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hfprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_4a with "Hcode"). }
    iIntros (hcwd) "Hrun".
    set (cwd := <[Regidx ra_idx := regval_into_reg
                     (mword_of_int 0x4e : mword 64)]> cwc).
    assert (Hracw : cwd !!! Regidx ra_idx = (mword_of_int 0x4e : mword 64))
      by exact (upd_eq cwc (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha1dcw : cwd !!! Regidx a1_idx = mword_of_int 0x9b0).
    { rewrite <- Ha1ccw.
      exact (upd_ne cwc (Regidx ra_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_kcat_fprintf γt γd γs 0x9b0 17%nat (cat_lit 0x9b0)
              hcwd cwd n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia)
              (fun j Hj => cat_lit_nopct 0x9b0 17%nat j Hokcw Hj) Ha1dcw
              with "Hcode Hstrcw Hrun").
    iIntros (hcwe cwm) "%Hcscw Hrun".
    assert (Eretcw : ret_pc (cwd !!! Regidx ra_idx)
                      = (mword_of_int 0x4e : mword 64))
      by (rewrite Hracw; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretcw.
    (* ---- 0x4e  c.li a0,1 ---- *)
    iApply (wp_uk_cli γt γd γs hcwe cwm (mword_of_int 0x4e)
              (mword_of_int 1 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_4e with "Hcode"). }
    assert (Excw : add_vec_int (mword_of_int 0x4e : mword 64) 2
                    = mword_of_int 0x50)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Excw.
    iIntros (hcwf) "Hrun".
    (* ---- 0x50  jal ra,0x3ac <exit> -- no continuation ---- *)
    iApply (wp_uk_jal γt γd γs hcwf _ (mword_of_int 0x50)
              (mword_of_int 860 : mword 21) ra_idx
              (mword_of_int CatSyms.exit) (mword_of_int 0x54) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_50 with "Hcode"). }
    iIntros (hcwg) "Hrun".
    iApply (wp_kcat_exit γt γd γs hcwg _ (10 + (12 + (4 + n))) with "Hcode Hrun").
  Qed.

  Lemma wp_kcat_cat_die_cr (hcr : CpuId) (mcr0 : regfile) (n : nat) :
    cat_code γt -∗ cat_rodata γt -∗
    urun γt γd γs hcr mcr0 (mword_of_int 0x6a) (10 + (12 + (4 + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode #Hro Hrun".
    destruct cat_syms_pins
      as (_ & _ & _ & Hfprintf & _ & _ & _ & _ & _ & _ & Hexit).
    assert (Hokcr : cat_lit_ok 0x9c8 16%nat = true)
      by (vm_compute; reflexivity).
    iDestruct (cat_lit_str γt 0x9c8 16%nat Hokcr
                 ltac:(vm_compute; reflexivity) with "Hro") as "#Hstrcr".
    (* ---- 0x6a  auipc a1 ; 0x6e  addi a1 -- the literal ---- *)
    assert (Eacr : add_vec (add_vec (mword_of_int 0x6a : mword 64)
                      (auipc_off (mword_of_int 1 : mword 20)))
                    (sign_extend' 64 (mword_of_int 2398 : mword 12))
                  = mword_of_int 0x9c8)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc γt γd γs hcr mcr0 (mword_of_int 0x6a)
              (mword_of_int 1 : mword 20) a1_idx
              (add_vec (mword_of_int 0x6a : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20))) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_6a with "Hcode"). }
    assert (Eucr : add_vec_int (mword_of_int 0x6a : mword 64) 4
                    = mword_of_int 0x6e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eucr.
    iIntros (hcra) "Hrun".
    set (cra := <[Regidx a1_idx := regval_into_reg
                     (add_vec (mword_of_int 0x6a : mword 64)
                        (auipc_off (mword_of_int 1 : mword 20)))]> mcr0).
    iApply (wp_uk_addi γt γd γs hcra cra (mword_of_int 0x6e)
              (mword_of_int 2398 : mword 12) a1_idx a1_idx
              (mword_of_int 0x9c8) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mcr0 (Regidx a1_idx) (regval_into_reg _));
                    exact (eq_sym Eacr))
              with "[] Hrun").
    { iApply (uis_cat_6e with "Hcode"). }
    assert (Eicr : add_vec_int (mword_of_int 0x6e : mword 64) 4
                    = mword_of_int 0x72)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eicr.
    iIntros (hcrb) "Hrun".
    set (crb := <[Regidx a1_idx := regval_into_reg
                     (mword_of_int 0x9c8 : mword 64)]> cra).
    assert (Ha1cr : crb !!! Regidx a1_idx = mword_of_int 0x9c8)
      by exact (upd_eq cra (Regidx a1_idx) (regval_into_reg _)).
    (* ---- 0x72  c.li a0,2 -- stderr ---- *)
    iApply (wp_uk_cli γt γd γs hcrb crb (mword_of_int 0x72)
              (mword_of_int 2 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_72 with "Hcode"). }
    assert (Elcr : add_vec_int (mword_of_int 0x72 : mword 64) 2
                    = mword_of_int 0x74)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Elcr.
    iIntros (hcrc) "Hrun".
    set (crc := <[Regidx a0_idx := regval_into_reg
                     (sign_extend' 64 (mword_of_int 2 : mword 6)
                      : mword 64)]> crb).
    assert (Ha1ccr : crc !!! Regidx a1_idx = mword_of_int 0x9c8).
    { rewrite <- Ha1cr.
      exact (upd_ne crb (Regidx a0_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x74  jal ra,0x7d0 <fprintf> ---- *)
    iApply (wp_uk_jal γt γd γs hcrc crc (mword_of_int 0x74)
              (mword_of_int 1884 : mword 21) ra_idx
              (mword_of_int CatSyms.fprintf) (mword_of_int 0x78) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hfprintf; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hfprintf; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_74 with "Hcode"). }
    iIntros (hcrd) "Hrun".
    set (crd := <[Regidx ra_idx := regval_into_reg
                     (mword_of_int 0x78 : mword 64)]> crc).
    assert (Hracr : crd !!! Regidx ra_idx = (mword_of_int 0x78 : mword 64))
      by exact (upd_eq crc (Regidx ra_idx) (regval_into_reg _)).
    assert (Ha1dcr : crd !!! Regidx a1_idx = mword_of_int 0x9c8).
    { rewrite <- Ha1ccr.
      exact (upd_ne crc (Regidx ra_idx) (Regidx a1_idx) _
               ltac:(vm_compute; discriminate)). }
    iApply (wp_kcat_fprintf γt γd γs 0x9c8 16%nat (cat_lit 0x9c8)
              hcrd crd n
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia)
              (fun j Hj => cat_lit_nopct 0x9c8 16%nat j Hokcr Hj) Ha1dcr
              with "Hcode Hstrcr Hrun").
    iIntros (hcre crm) "%Hcscr Hrun".
    assert (Eretcr : ret_pc (crd !!! Regidx ra_idx)
                      = (mword_of_int 0x78 : mword 64))
      by (rewrite Hracr; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretcr.
    (* ---- 0x78  c.li a0,1 ---- *)
    iApply (wp_uk_cli γt γd γs hcre crm (mword_of_int 0x78)
              (mword_of_int 1 : mword 6) a0_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_78 with "Hcode"). }
    assert (Excr : add_vec_int (mword_of_int 0x78 : mword 64) 2
                    = mword_of_int 0x7a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Excr.
    iIntros (hcrf) "Hrun".
    (* ---- 0x7a  jal ra,0x3ac <exit> -- no continuation ---- *)
    iApply (wp_uk_jal γt γd γs hcrf _ (mword_of_int 0x7a)
              (mword_of_int 818 : mword 21) ra_idx
              (mword_of_int CatSyms.exit) (mword_of_int 0x7e) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hexit; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hexit; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_7a with "Hcode"). }
    iIntros (hcrg) "Hrun".
    iApply (wp_kcat_exit γt γd γs hcrg _ (10 + (12 + (4 + n))) with "Hcode Hrun").
  Qed.

End UkCatCat.
