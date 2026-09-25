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
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeCat.
Require Import CtxIdDefs.
Require User.CatSyms User.InitInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UkProgAbi.
Require Import UkCat.
Require Import UkCatLit.
Require Import UkCatFprintf.
Require Import UkRunBr.

Local Open Scope Z_scope.
Import Defs.

Local Open Scope Z_scope.
Import Defs.

Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkCatCat.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT PAYLOAD DOES NOT READ ITS STATUS (lane CAT-WALK,
     W2), as a CLASS so that it reaches the exit ecall without an argument
     at every call site ([UkRun.ukn_const]).  It used to be [ukn_triv] --
     "cat owes its parent nothing" -- which pinned the payload at [True]
     and so made cat's exit incapable of handing the shell the deed
     fraction, the advanced console credential or the filed alternative.
     What cat actually needs of
     its own payload is only that its two exits -- 0 on the content arm,
     1 on the diagnostic arm -- owe the SAME thing, which is exactly this
     class; echo's walk is stated at it for the same reason. *)
  Context `{Hpay : !ukn_const N}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS THIS PROGRAM ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis, so no lemma statement in this file names it and the ~570
     [urun] sites did not move; the program's kernel-side constructor
     discharges it.
     AT THE FREE NUMBERS AND NO MORE (lane SUPPLY-SPLIT).  It used to read
     "every number but exec", which at the generic instance is true and at
     a VERIFIED program's instance is not: a program whose supplier is the
     application's ([AppInv.app_sup] -- for the echo application, the
     TAINT) could only ever be entered tainted.  What a verified program
     admits is [UexecSG.free_num] -- every number whose bundle is [emp],
     plus chdir, whose branch is a closed fact -- and at
     [UexecExecInst.uprogSG_free] this hypothesis is the identity.  A call
     at a number OUTSIDE that set takes its own deposit as a premise
     ([UkRun.udepw_law]) and is named at its site. *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

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
    urun N h m (mword_of_int 0x74c) n -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ m' !!! Regidx csp_rs1 = sp0 ⌝ -∗
       ⌜ m' !!! Regidx s0_idx = vs0 ⌝ -∗
       ⌜ m' !!! Regidx s1_idx = vs1 ⌝ -∗
       ⌜ forall r : mword 5,
           Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
           Regidx r <> Regidx s1_idx -> Regidx r <> Regidx ra_idx ->
           m' !!! Regidx r = m !!! Regidx r ⌝ -∗
       urun N h' m' (ret_pc vra) (12 + n) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
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
    (* ---- 0x74c  c.ldsp ra,88(sp) ---- *)
    iApply (wp_uk_cldsp N h m (mword_of_int 0x74c)
              (mword_of_int 11 : mword 6) ra_idx (uint sp0 - 8) vra n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp96 Ho88; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hwra Hrun").
    { iApply (uis_cat_74c with "Hcode"). }
    iIntros "Hwra".
    assert (E70a : add_vec_int (mword_of_int 0x74c : mword 64) 2
                 = mword_of_int 0x74e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70a.
    iIntros (h1) "Hrun".
    set (mm1 := <[Regidx ra_idx := regval_into_reg vra]> m).
    assert (Hsp1 : mm1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx ra_idx) (Regidx csp_rs1) (regval_into_reg vra)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x74e  c.ldsp s0,80(sp) ---- *)
    iApply (wp_uk_cldsp N h1 mm1 (mword_of_int 0x74e)
              (mword_of_int 10 : mword 6) s0_idx (uint sp0 - 16) vs0 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp96 Ho80; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws0 Hrun").
    { iApply (uis_cat_74e with "Hcode"). }
    iIntros "Hws0".
    assert (E70c : add_vec_int (mword_of_int 0x74e : mword 64) 2
                 = mword_of_int 0x750)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70c.
    iIntros (h2) "Hrun".
    set (mm2 := <[Regidx s0_idx := regval_into_reg vs0]> mm1).
    assert (Hsp2 : mm2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp1.
      exact (upd_ne mm1 (Regidx s0_idx) (Regidx csp_rs1) (regval_into_reg vs0)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x750  c.ldsp s1,72(sp) ---- *)
    iApply (wp_uk_cldsp N h2 mm2 (mword_of_int 0x750)
              (mword_of_int 9 : mword 6) s1_idx (uint sp0 - 24) vs1 n
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp2 Hsp96 Ho72; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hws1 Hrun").
    { iApply (uis_cat_750 with "Hcode"). }
    iIntros "Hws1".
    assert (E70e : add_vec_int (mword_of_int 0x750 : mword 64) 2
                 = mword_of_int 0x752)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E70e.
    iIntros (h3) "Hrun".
    set (mm3 := <[Regidx s1_idx := regval_into_reg vs1]> mm2).
    assert (Hsp3 : mm3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 12))).
    { rewrite <- Hsp2.
      exact (upd_ne mm2 (Regidx s1_idx) (Regidx csp_rs1) (regval_into_reg vs1)
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x752  c.addi16sp sp,sp,96 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up N h3 mm3 (mword_of_int 0x752)
              (mword_of_int 6 : mword 6) 12 n
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hwra Hws0 Hws1 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12] Hrun").
    { iApply (uis_cat_752 with "Hcode"). }
    { rewrite Hsp3 Hup.
      iApply (ustack_12_close γd sp0 Hal8
                with "[Hwra] [Hws0] [Hws1] Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hw10 Hw11 Hw12").
      { iExists vra. iExact "Hwra". }
      { iExists vs0. iExact "Hws0". }
      { iExists vs1. iExact "Hws1". } }
    assert (E710 : add_vec_int (mword_of_int 0x752 : mword 64) 2
                   = mword_of_int 0x754)
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
    (* ---- 0x754  c.jr ra ---- *)
    iApply (wp_uk_cjr N h4 mm4 (mword_of_int 0x754) ra_idx
              (ret_pc vra) (12 + n)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra4; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_754 with "Hcode"). }
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
  (* THE LOOP'S INVARIANT.  Six registers and the frame pointer; ulib parks  *)
  (* the fd, the buffer, the count and the constant 1 in callee-saved        *)
  (* registers precisely so that they survive the two calls.                 *)
  (* --------------------------------------------------------------------- *)
  Definition cv_inv (m0 m : regfile) (sp0 fdv : mword 64) : Prop :=
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 8)) /\
    m !!! Regidx s0_idx = sp0 /\
    m !!! Regidx s2_idx = mword_of_int CatSyms.buf /\
    m !!! Regidx s3_idx = fdv /\
    m !!! Regidx s4_idx = mword_of_int 512 /\
    m !!! Regidx s5_idx = mword_of_int 1 /\
    (forall r : mword 5, ucallee_saved_idx r = true ->
       uint r = 3 \/ uint r = 4 \/ (22 <= uint r <= 27) ->
       m !!! Regidx r = m0 !!! Regidx r).

  Lemma cv_inv_call (m0 m m' : regfile) (sp0 fdv : mword 64) :
    ucallee_saved m m' -> cv_inv m0 m sp0 fdv -> cv_inv m0 m' sp0 fdv.
  Proof using .
    intros Hcs (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hfr).
    unfold cv_inv.
    rewrite (Hcs csp_rs1 ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s0_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s2_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s3_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s4_idx ltac:(vm_compute; reflexivity)).
    rewrite (Hcs s5_idx ltac:(vm_compute; reflexivity)).
    repeat (split; [ assumption | ]).
    intros r Hr Hset. rewrite (Hcs r Hr). exact (Hfr r Hr Hset).
  Qed.

  (* which registers a step may write without disturbing it *)
  Definition cv_writable (r : mword 5) : bool :=
    negb (Z.eqb (uint r) 2 || Z.eqb (uint r) 3 || Z.eqb (uint r) 4 ||
          Z.eqb (uint r) 8 ||
          ((18 <=? uint r) && (uint r <=? 21)) ||
          ((22 <=? uint r) && (uint r <=? 27))).

  Lemma cv_writable_ne (r : mword 5) (z : Z) :
    cv_writable r = true ->
    (z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ (18 <= z <= 21) \/ (22 <= z <= 27)) ->
    uint r <> z.
  Proof using .
    unfold cv_writable. intro H. apply negb_true_iff in H.
    rewrite !orb_false_iff in H.
    destruct H as [[[[[H1 H2] H3] H4] H5] H6].
    apply Z.eqb_neq in H1. apply Z.eqb_neq in H2.
    apply Z.eqb_neq in H3. apply Z.eqb_neq in H4.
    apply andb_false_iff in H5. apply andb_false_iff in H6.
    intros Hz He. rewrite He in H1, H2, H3, H4, H5, H6.
    destruct H5 as [H5 | H5]; try apply Z.leb_gt in H5;
      destruct H6 as [H6 | H6]; try apply Z.leb_gt in H6; lia.
  Qed.

  Lemma cv_inv_upd (m0 m : regfile) (sp0 fdv : mword 64)
      (r : mword 5) (v : mword 64) :
    cv_writable r = true ->
    cv_inv m0 m sp0 fdv ->
    cv_inv m0 (<[Regidx r := regval_into_reg v]> m) sp0 fdv.
  Proof using .
    intros Hw (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hfr).
    unfold cv_inv.
    rewrite (upd_ne m (Regidx r) (Regidx csp_rs1) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cv_writable_ne r _ Hw);
                     replace (uint csp_rs1) with 2 by (vm_compute; reflexivity);
                     lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s0_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cv_writable_ne r _ Hw);
                     replace (uint s0_idx) with 8 by (vm_compute; reflexivity);
                     lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s2_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cv_writable_ne r _ Hw);
                     replace (uint s2_idx) with 18 by (vm_compute; reflexivity);
                     lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s3_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cv_writable_ne r _ Hw);
                     replace (uint s3_idx) with 19 by (vm_compute; reflexivity);
                     lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s4_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cv_writable_ne r _ Hw);
                     replace (uint s4_idx) with 20 by (vm_compute; reflexivity);
                     lia)).
    rewrite (upd_ne m (Regidx r) (Regidx s5_idx) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cv_writable_ne r _ Hw);
                     replace (uint s5_idx) with 21 by (vm_compute; reflexivity);
                     lia)).
    repeat (split; [ assumption | ]).
    intros q Hq Hset.
    rewrite (upd_ne m (Regidx r) (Regidx q) (regval_into_reg v)
               ltac:(apply not_eq_sym; apply uidx_ne;
                     apply (cv_writable_ne r _ Hw); lia)).
    exact (Hfr q Hq Hset).
  Qed.

  (* ===================================================================== *)
  (* WHAT cat's LOOP SPENDS (lane CAT-WALK, W1).                            *)
  (*                                                                       *)
  (* The loop is UNBOUNDED and the counts it writes at are its own reads'   *)
  (* returns, so no finite chain can pay it.  What pays it is a ROUND LAW:  *)
  (* one persistent obligation that funds a whole turn -- the read, and     *)
  (* then, at whatever the read returned, the branch the return selects --  *)
  (* and hands the invariant back for the next turn.  [I] is the payer's    *)
  (* own cursor (at the file application, the output cursor at the          *)
  (* position the round's output has reached) and the walk reads none of    *)
  (* it; [Cend] is what the loop's NORMAL exit -- read returned zero --     *)
  (* hands to cat's caller.                                                 *)
  (*                                                                       *)
  (* THE TWO DIAGNOSTIC TAILS ARE IN IT, because they are exits of the      *)
  (* loop and each ends in the program's own exit payload: cat's `write     *)
  (* error` after a short write, and its `read error` after a failed read.  *)
  (* The read-error arm is the one lane READ-RELAY will refute at the       *)
  (* kernel; until then it is an ARM of the payment, not a stop -- a payer  *)
  (* that cannot fund it simply cannot build a round.                      *)
  (* ===================================================================== *)
  (* ...AND EACH TAIL ENDS IN THE EXIT HOLE AT STATUS 1 (program-specs
     cut 3), not in the payload: the diagnostic is [exit(1)], and a payer
     of cat's interaction tree funds exactly [UkCat.kcat_exit N 1] there. *)
  Definition kcat_dg_cw : iProp Σ :=
    UkCat.kcat_pay_seq N (mword_of_int 2) (cat_lit 0x9b0) 0%nat 17%nat
      emp%I (UkCat.kcat_exit N 1).

  Definition kcat_dg_cr : iProp Σ :=
    UkCat.kcat_pay_seq N (mword_of_int 2) (cat_lit 0x9c8) 0%nat 16%nat
      emp%I (UkCat.kcat_exit N 1).

  (* ===================================================================== *)
  (* RULING (g) (lane CAT-ENTRY-2): THE WRITE ARM IS COUNT-EXACT, AND THE    *)
  (* `cat: write error` TAIL IS AN ARM THE PAYER MAY REFUTE.                *)
  (*                                                                       *)
  (* The write output used to be [(I ∧ kcat_dg_cw) ∗ buffer]: an ADDITIVE  *)
  (* pair the payer owed on EVERY turn, because the walk takes whichever    *)
  (* arm of [beq a0,s1] the return value picks and the payment could not    *)
  (* say which.  A cursor's step can only fund a byte the MODEL's          *)
  (* continuation holds at the cursor, and "cat: write error" is not in it  *)
  (* at any position -- so a claim-bearing payer could never build a round. *)
  (*                                                                       *)
  (* What replaces it is a DISJUNCTION THE PAYER PICKS, over the write's    *)
  (* own returned word ([UkCat.kcat_wr]):                                   *)
  (*                                                                       *)
  (*   - the NO-SHORT arm -- the call returned exactly the count it was     *)
  (*     given, so [beq a0,s1] is TAKEN and the diagnostic branch is        *)
  (*     REFUTED at the leaf.  [UkWriteLeaf.uwrite_no_short] is where that  *)
  (*     fact comes from: a console write of a run the CALLER OWNS returns  *)
  (*     the full count, which is lane READ-RELAY's move one syscall over.  *)
  (*     A deed payer picks this one and never funds the tail.              *)
  (*                                                                       *)
  (*   - the DIAGNOSTIC arm -- the old additive pair, unchanged.  The FREE  *)
  (*     write law has a short arm and says nothing about the return, so    *)
  (*     [kcat_round_of_law] picks this one and the claim-free chain is     *)
  (*     exactly what it was.                                              *)
  (*                                                                       *)
  (* The walk funds both, so [kcat_dg_cw] is still a payment of this file   *)
  (* and the `cat: write error` code is still WALKED -- it is only no       *)
  (* longer an OBLIGATION of every payer.                                   *)
  (* ===================================================================== *)
  (* ...RESTATED (program-specs cut 3) SO THAT A PAYER WHO KNOWS THE
     WRITE'S RETURN CAN FUND IT.  The disjunction above made the payer pick
     an arm without seeing the returned word; a payer of cat's interaction
     tree sees it (the tree branches on it) and owes the invariant at the
     full count and the tail otherwise.  [kcat_wpost] is that ADDITIVE
     pair, each half under the fact that selects it; both landed arms are
     instances of it ([kcat_wpost_of_eq], [kcat_wpost_of_both]).  And the
     write arm is stated at the SIGNED reading of the read's return: the
     old [ret = mword_of_int nb] admitted an [nb] past 2^63 that no tree
     can fund. *)
  Definition kcat_wpost (nb : nat) (I : iProp Σ) (wret : mword 64) : iProp Σ :=
    ((⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗ I)
     ∧ (⌜wret <> (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗ kcat_dg_cw))%I.

  Lemma kcat_wpost_of_eq (nb : nat) (I : iProp Σ) (wret : mword 64) :
    ⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝ ∗ I -∗ kcat_wpost nb I wret.
  Proof using .
    iIntros "[%Hw HI]". iSplit.
    - iIntros "_". iExact "HI".
    - iIntros "%Hne". by exfalso.
  Qed.

  Lemma kcat_wpost_of_both (nb : nat) (I : iProp Σ) (wret : mword 64) :
    I ∧ kcat_dg_cw -∗ kcat_wpost nb I wret.
  Proof using .
    iIntros "H". iSplit.
    - iIntros "_". iDestruct "H" as "[$ _]".
    - iIntros "_". iDestruct "H" as "[_ $]".
  Qed.

  Definition kcat_round (fdv : mword 64) (I Cend : iProp Σ) : iProp Σ :=
    (□ UkCat.kcat_r N fdv CatSyms.buf 512 I
         (fun (ret : mword 64) (g : nat -> bv 8) =>
            ((⌜bv_signed ret < 0⌝ -∗ kcat_dg_cr)
             ∧ (⌜bv_signed ret = 0⌝ -∗ Cend)
             ∧ (∀ nb : nat,
                  ⌜bv_signed ret = Z.of_nat nb⌝ -∗
                  ⌜(0 < nb)%nat⌝ -∗
                  UkCat.kcat_wr N (mword_of_int 1)
                    (mword_of_int CatSyms.buf) nb
                    (ubytes γd CatSyms.buf 512 g)
                    (fun wret : mword 64 =>
                       kcat_wpost nb I wret
                       ∗ ubytes γd CatSyms.buf 512 g)))))%I.

  Global Instance kcat_round_persistent fdv I Cend :
    Persistent (kcat_round fdv I Cend).
  Proof using . rewrite /kcat_round. apply _. Qed.

  (* ...AND THE FREE ROUND (lane CAT-WALK, W1).  This is the whole of what
     the landed, claim-free loop said, as ONE corollary at the free laws:
     the read pays from [udepw_law 5], every write from [udepw_law 16],
     nothing is carried and nothing is claimed.  A program entering on the
     generic path builds its round with this and gets the old statement
     back; it is also the VACUITY GUARD for the restatement -- the
     obligations above are satisfiable, so [wp_kcat_cat_loop] is not
     vacuously true. *)
  (* ...AND THE PAYLOAD IS A PERSISTENT RESOURCE (lane CAT-GEOM-4; see
     [UkCat.kcat_pay_seq_of_law]'s note).  What this buys is the TAINT:
     a payer whose payload is a claim-bearing output cursor holds it
     persistently at a tainted era and could not hand it in as [(⊢ _)]. *)
  Lemma kcat_round_of_law (fdv : mword 64) :
    □ (ukn_pay N (-1)) -∗
    udepw_law 5 -∗ udepw_law 16 -∗ kcat_round fdv emp%I emp%I.
  Proof using Hpay.
    iIntros "#HC0 #Hrd #Hwr".
    iAssert (□ UkCat.kcat_exit N 1)%I as "#HC".
    { iModIntro. iApply (UkCat.kcat_exit_of_pay with "HC0"). }
    rewrite /kcat_round. iModIntro.
    iIntros (h m avail f) "_ %Ha1 %Ha2 #Hcode _ Hbuf Hrun Hcont".
    iApply (UkCat.wp_kcat_read N CatSyms.buf 512 f h m avail Ha1 Ha2
              with "Hrd Hcode Hbuf Hrun").
    iIntros (h' ret g) "Hbuf Hrun".
    iApply ("Hcont" $! h' ret g with "[] Hbuf Hrun").
    iSplit; [| iSplit ].
    - iIntros "_". rewrite /kcat_dg_cr.
      iApply (UkCat.kcat_pay_seq_of_law N (mword_of_int 2) (cat_lit 0x9c8)
                16%nat (UkCat.kcat_exit N 1) 0%nat with "HC Hwr").
    - by iIntros "_".
    - iIntros (nb) "_ _".
      (* THE FREE PAYER PICKS THE DIAGNOSTIC ARM: the free write law has a
         short arm and hands back no return value, so the no-short
         disjunct is not available to it -- and the claim-free round is
         then exactly the additive pair this file paid before. *)
      iApply (UkCat.kcat_wr_mono N (mword_of_int 1)
                (mword_of_int CatSyms.buf) nb
                (ubytes γd CatSyms.buf 512 g)
                (fun _ : mword 64 =>
                   ((emp ∧ kcat_dg_cw) ∗ ubytes γd CatSyms.buf 512 g)%I)
                _ with "[]").
      { iIntros (r) "[Hd Hb]". iSplitR "Hb"; [ | iExact "Hb" ].
        iApply (kcat_wpost_of_both with "Hd"). }
      iApply UkCat.kcat_wr_of_w.
      iApply (UkCat.kcat_w_mono N (mword_of_int 1)
                (mword_of_int CatSyms.buf) nb
                (ubytes γd CatSyms.buf 512 g)
                (ubytes γd CatSyms.buf 512 g)
                ((emp ∧ kcat_dg_cw) ∗ ubytes γd CatSyms.buf 512 g)%I
                with "[] []").
      + iIntros "Hb". iSplitR "Hb"; [ | iExact "Hb" ].
        iSplit; [ done | ]. rewrite /kcat_dg_cw.
        iApply (UkCat.kcat_pay_seq_of_law N (mword_of_int 2) (cat_lit 0x9b0)
                  17%nat (UkCat.kcat_exit N 1) 0%nat with "HC Hwr").
      + iApply (UkCat.kcat_w_of_law N (mword_of_int 1)
                  (mword_of_int CatSyms.buf) nb
                  (ubytes γd CatSyms.buf 512 g)
                  (ubytes γd CatSyms.buf 512 g)
                  ltac:(reflexivity) with "Hwr").
  Qed.

  Lemma wp_kcat_cat_die_cw (hcw : CpuId) (mcw0 : regfile) (n : nat) :
    kcat_dg_cw -∗
    cat_code γt -∗ cat_rodata γt -∗
    urun N hcw mcw0 (mword_of_int 0x40) (10 + (12 + (4 + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "Hdg #Hcode #Hro Hrun".
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
    iApply (wp_uk_auipc N hcw mcw0 (mword_of_int 0x40)
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
    iApply (wp_uk_addi N hcwa cwa (mword_of_int 0x44)
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
    iApply (wp_uk_cli N hcwb cwb (mword_of_int 0x48)
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
    (* ---- 0x4a  jal ra,0x7d8 <fprintf> ---- *)
    iApply (wp_uk_jal N hcwc cwc (mword_of_int 0x4a)
              (mword_of_int 1934 : mword 21) ra_idx
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
    assert (Ha0dcw : cwd !!! Regidx a0_idx = (mword_of_int 2 : mword 64)).
    { rewrite /cwd (upd_ne cwc (Regidx ra_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /cwc (upd_eq cwb (Regidx a0_idx) (regval_into_reg _)).
      apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_kcat_fprintf N 0x9b0 17%nat (cat_lit 0x9b0)
              hcwd cwd n emp%I (UkCat.kcat_exit N 1)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia)
              (fun j Hj => cat_lit_nopct 0x9b0 17%nat j Hokcw Hj) Ha1dcw
              with "[Hdg] Hcode Hstrcw [] Hrun").
    { rewrite Ha0dcw. iExact "Hdg". }
    { done. }
    iIntros (hcwe cwm) "%Hcscw Hpayv Hrun".
    assert (Eretcw : ret_pc (cwd !!! Regidx ra_idx)
                      = (mword_of_int 0x4e : mword 64))
      by (rewrite Hracw; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretcw.
    (* ---- 0x4e  c.li a0,1 ---- *)
    iApply (wp_uk_cli N hcwe cwm (mword_of_int 0x4e)
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
    iApply (wp_uk_jal N hcwf _ (mword_of_int 0x50)
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
    (* THE EXIT HOLE, at the status [c.li a0,1] left in a0 *)
    iApply ("Hpayv" $! hcwg _ (10 + (12 + (4 + n)))%nat with "[%] Hcode Hrun").
    rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq _ (Regidx a0_idx) (regval_into_reg _)).
    vm_compute. reflexivity.
  Qed.

  Lemma wp_kcat_cat_die_cr (hcr : CpuId) (mcr0 : regfile) (n : nat) :
    kcat_dg_cr -∗
    cat_code γt -∗ cat_rodata γt -∗
    urun N hcr mcr0 (mword_of_int 0x6a) (10 + (12 + (4 + n))) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    iIntros "Hdg #Hcode #Hro Hrun".
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
    iApply (wp_uk_auipc N hcr mcr0 (mword_of_int 0x6a)
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
    iApply (wp_uk_addi N hcra cra (mword_of_int 0x6e)
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
    iApply (wp_uk_cli N hcrb crb (mword_of_int 0x72)
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
    (* ---- 0x74  jal ra,0x7d8 <fprintf> ---- *)
    iApply (wp_uk_jal N hcrc crc (mword_of_int 0x74)
              (mword_of_int 1892 : mword 21) ra_idx
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
    assert (Ha0dcr : crd !!! Regidx a0_idx = (mword_of_int 2 : mword 64)).
    { rewrite /crd (upd_ne crc (Regidx ra_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /crc (upd_eq crb (Regidx a0_idx) (regval_into_reg _)).
      apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_kcat_fprintf N 0x9c8 16%nat (cat_lit 0x9c8)
              hcrd crd n emp%I (UkCat.kcat_exit N 1)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(lia)
              (fun j Hj => cat_lit_nopct 0x9c8 16%nat j Hokcr Hj) Ha1dcr
              with "[Hdg] Hcode Hstrcr [] Hrun").
    { rewrite Ha0dcr. iExact "Hdg". }
    { done. }
    iIntros (hcre crm) "%Hcscr Hpayv Hrun".
    assert (Eretcr : ret_pc (crd !!! Regidx ra_idx)
                      = (mword_of_int 0x78 : mword 64))
      by (rewrite Hracr; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretcr.
    (* ---- 0x78  c.li a0,1 ---- *)
    iApply (wp_uk_cli N hcre crm (mword_of_int 0x78)
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
    iApply (wp_uk_jal N hcrf _ (mword_of_int 0x7a)
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
    (* THE EXIT HOLE, at the status [c.li a0,1] left in a0 *)
    iApply ("Hpayv" $! hcrg _ (10 + (12 + (4 + n)))%nat with "[%] Hcode Hrun").
    rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)).
    rewrite (upd_eq _ (Regidx a0_idx) (regval_into_reg _)).
    vm_compute. reflexivity.
  Qed.


  (* --------------------------------------------------------------------- *)
  (* cat()'s EPILOGUE @0x58: restore ra, s0..s5, pop the 64-byte frame,     *)
  (* return.  This is where [ucallee_saved] is assembled, for the same      *)
  (* reason as vprintf's: it is the one point where every spilled register  *)
  (* is back at its entry value.                                            *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_cat_epi (h : CpuId) (m m0 : regfile) (sp0 : mword 64) (n : nat) :
    m !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 8)) ->
    m0 !!! Regidx csp_rs1 = sp0 ->
    uint sp0 mod 8 = 0 ->
    64 <= uint sp0 ->
    (forall r : mword 5, ucallee_saved_idx r = true ->
       uint r = 3 \/ uint r = 4 \/ (22 <= uint r <= 27) ->
       m !!! Regidx r = m0 !!! Regidx r) ->
    cat_code γt -∗
    uword γd (uint sp0 - 8) (m0 !!! Regidx ra_idx) -∗
    uword γd (uint sp0 - 16) (m0 !!! Regidx s0_idx) -∗
    uword γd (uint sp0 - 24) (m0 !!! Regidx s1_idx) -∗
    uword γd (uint sp0 - 32) (m0 !!! Regidx s2_idx) -∗
    uword γd (uint sp0 - 40) (m0 !!! Regidx s3_idx) -∗
    uword γd (uint sp0 - 48) (m0 !!! Regidx s4_idx) -∗
    uword γd (uint sp0 - 56) (m0 !!! Regidx s5_idx) -∗
    (∃ w : mword 64, uword γd (uint sp0 - 64) w) -∗
    urun N h m (mword_of_int 0x58) (10 + (12 + (4 + n))) -∗
    (∀ (h' : CpuId) (m' : regfile),
       ⌜ ucallee_saved m0 m' ⌝ -∗
       urun N h' m' (ret_pc (m0 !!! Regidx ra_idx)) (8 + (10 + (12 + (4 + n)))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hsp Hsp0 Hal8 Hlo Hfree.
    iIntros "#Hcode Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hrun Hcont".
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                   = bv_unsigned sp0 - 64).
    { replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp64 : uint (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                    = uint sp0 - 64)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt8 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                   + 8 * Z.of_nat 8 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                    (8 * Z.of_nat 8) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                 (8 * Z.of_nat 8) ltac:(apply Z.leb_le; reflexivity) Hlt8).
      clear -Hbsp. rewrite Hbsp. lia. }
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
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    (* ---- 0x58  c.ldsp ra,56(sp) ---- *)
    iApply (wp_uk_cldsp N h m (mword_of_int 0x58)
              (mword_of_int 7 : mword 6) ra_idx (uint sp0 - 8)
              (m0 !!! Regidx ra_idx) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp Hsp64 Ho56; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw1 Hrun").
    { iApply (uis_cat_58 with "Hcode"). }
    iIntros "Hw1".
    assert (E58 : add_vec_int (mword_of_int 0x58 : mword 64) 2
                 = mword_of_int 0x5a)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E58.
    iIntros (h1) "Hrun".
    set (me1 := <[Regidx ra_idx := regval_into_reg (m0 !!! Regidx ra_idx)]> m).
    assert (Hsp1 : me1 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite <- Hsp.
      exact (upd_ne m (Regidx ra_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx ra_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x5a  c.ldsp s0,48(sp) ---- *)
    iApply (wp_uk_cldsp N h1 me1 (mword_of_int 0x5a)
              (mword_of_int 6 : mword 6) s0_idx (uint sp0 - 16)
              (m0 !!! Regidx s0_idx) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp1 Hsp64 Ho48; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw2 Hrun").
    { iApply (uis_cat_5a with "Hcode"). }
    iIntros "Hw2".
    assert (E5a : add_vec_int (mword_of_int 0x5a : mword 64) 2
                 = mword_of_int 0x5c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5a.
    iIntros (h2) "Hrun".
    set (me2 := <[Regidx s0_idx := regval_into_reg (m0 !!! Regidx s0_idx)]> me1).
    assert (Hsp2 : me2 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite <- Hsp1.
      exact (upd_ne me1 (Regidx s0_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s0_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x5c  c.ldsp s1,40(sp) ---- *)
    iApply (wp_uk_cldsp N h2 me2 (mword_of_int 0x5c)
              (mword_of_int 5 : mword 6) s1_idx (uint sp0 - 24)
              (m0 !!! Regidx s1_idx) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp2 Hsp64 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw3 Hrun").
    { iApply (uis_cat_5c with "Hcode"). }
    iIntros "Hw3".
    assert (E5c : add_vec_int (mword_of_int 0x5c : mword 64) 2
                 = mword_of_int 0x5e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5c.
    iIntros (h3) "Hrun".
    set (me3 := <[Regidx s1_idx := regval_into_reg (m0 !!! Regidx s1_idx)]> me2).
    assert (Hsp3 : me3 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite <- Hsp2.
      exact (upd_ne me2 (Regidx s1_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s1_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x5e  c.ldsp s2,32(sp) ---- *)
    iApply (wp_uk_cldsp N h3 me3 (mword_of_int 0x5e)
              (mword_of_int 4 : mword 6) s2_idx (uint sp0 - 32)
              (m0 !!! Regidx s2_idx) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp3 Hsp64 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw4 Hrun").
    { iApply (uis_cat_5e with "Hcode"). }
    iIntros "Hw4".
    assert (E5e : add_vec_int (mword_of_int 0x5e : mword 64) 2
                 = mword_of_int 0x60)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E5e.
    iIntros (h4) "Hrun".
    set (me4 := <[Regidx s2_idx := regval_into_reg (m0 !!! Regidx s2_idx)]> me3).
    assert (Hsp4 : me4 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite <- Hsp3.
      exact (upd_ne me3 (Regidx s2_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s2_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x60  c.ldsp s3,24(sp) ---- *)
    iApply (wp_uk_cldsp N h4 me4 (mword_of_int 0x60)
              (mword_of_int 3 : mword 6) s3_idx (uint sp0 - 40)
              (m0 !!! Regidx s3_idx) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp4 Hsp64 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw5 Hrun").
    { iApply (uis_cat_60 with "Hcode"). }
    iIntros "Hw5".
    assert (E60 : add_vec_int (mword_of_int 0x60 : mword 64) 2
                 = mword_of_int 0x62)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E60.
    iIntros (h5) "Hrun".
    set (me5 := <[Regidx s3_idx := regval_into_reg (m0 !!! Regidx s3_idx)]> me4).
    assert (Hsp5 : me5 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite <- Hsp4.
      exact (upd_ne me4 (Regidx s3_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s3_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x62  c.ldsp s4,16(sp) ---- *)
    iApply (wp_uk_cldsp N h5 me5 (mword_of_int 0x62)
              (mword_of_int 2 : mword 6) s4_idx (uint sp0 - 48)
              (m0 !!! Regidx s4_idx) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp5 Hsp64 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw6 Hrun").
    { iApply (uis_cat_62 with "Hcode"). }
    iIntros "Hw6".
    assert (E62 : add_vec_int (mword_of_int 0x62 : mword 64) 2
                 = mword_of_int 0x64)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E62.
    iIntros (h6) "Hrun".
    set (me6 := <[Regidx s4_idx := regval_into_reg (m0 !!! Regidx s4_idx)]> me5).
    assert (Hsp6 : me6 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite <- Hsp5.
      exact (upd_ne me5 (Regidx s4_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s4_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x64  c.ldsp s5,8(sp) ---- *)
    iApply (wp_uk_cldsp N h6 me6 (mword_of_int 0x64)
              (mword_of_int 1 : mword 6) s5_idx (uint sp0 - 56)
              (m0 !!! Regidx s5_idx) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hsp6 Hsp64 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              ltac:(vm_compute; discriminate)
              with "[] Hw7 Hrun").
    { iApply (uis_cat_64 with "Hcode"). }
    iIntros "Hw7".
    assert (E64 : add_vec_int (mword_of_int 0x64 : mword 64) 2
                 = mword_of_int 0x66)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E64.
    iIntros (h7) "Hrun".
    set (me7 := <[Regidx s5_idx := regval_into_reg (m0 !!! Regidx s5_idx)]> me6).
    assert (Hsp7 : me7 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8))).
    { rewrite <- Hsp6.
      exact (upd_ne me6 (Regidx s5_idx) (Regidx csp_rs1)
               (regval_into_reg (m0 !!! Regidx s5_idx))
               ltac:(vm_compute; discriminate)). }
    (* ---- 0x66  c.addi16sp sp,sp,64 -- the frame goes back ---- *)
    iApply (wp_uk_caddi16sp_up N h7 me7 (mword_of_int 0x66)
              (mword_of_int 4 : mword 6) 8 (10 + (12 + (4 + n)))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8] Hrun").
    { iApply (uis_cat_66 with "Hcode"). }
    { rewrite Hsp7 Hup.
      iApply (ustack_8_close γd sp0 Hal8
                with "[Hw1] [Hw2] [Hw3] [Hw4] [Hw5] [Hw6] [Hw7] Hw8").
      { iExists (m0 !!! Regidx ra_idx). iFrame. }
      { iExists (m0 !!! Regidx s0_idx). iFrame. }
      { iExists (m0 !!! Regidx s1_idx). iFrame. }
      { iExists (m0 !!! Regidx s2_idx). iFrame. }
      { iExists (m0 !!! Regidx s3_idx). iFrame. }
      { iExists (m0 !!! Regidx s4_idx). iFrame. }
      { iExists (m0 !!! Regidx s5_idx). iFrame. }
      }
    assert (E66 : add_vec_int (mword_of_int 0x66 : mword 64) 2
                  = mword_of_int 0x68)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp7 Hup E66.
    iIntros (h8) "Hrun".
    set (me8 := <[Regidx csp_rs1 := regval_into_reg sp0]> me7).
    assert (Hra8 : me8 !!! Regidx ra_idx = m0 !!! Regidx ra_idx).
    { rewrite /me8 (upd_ne me7 (Regidx csp_rs1) (Regidx ra_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me7 (upd_ne me6 (Regidx s5_idx) (Regidx ra_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s4_idx) (Regidx ra_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s3_idx) (Regidx ra_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s2_idx) (Regidx ra_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me3 (upd_ne me2 (Regidx s1_idx) (Regidx ra_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me2 (upd_ne me1 (Regidx s0_idx) (Regidx ra_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me1. exact (upd_eq m (Regidx ra_idx) (regval_into_reg _)). }
    (* ---- 0x68  c.jr ra ---- *)
    iApply (wp_uk_cjr N h8 me8 (mword_of_int 0x68) ra_idx
              (ret_pc (m0 !!! Regidx ra_idx)) (8 + (10 + (12 + (4 + n))))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra8; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_68 with "Hcode"). }
    iIntros (h9) "Hrun".
    iApply ("Hcont" $! h9 me8 with "[] Hrun").
    iPureIntro. intros r Hr.
    (* the seven spilled registers are back; the rest never moved *)
    assert (Hme : forall (q : mword 5) (z : Z),
               uint q = z -> uint r <> z -> Regidx r <> Regidx q).
    { intros q z Hq Hz. apply uidx_ne. rewrite Hq. exact Hz. }
    assert (Hfree' : uint r = 3 \/ uint r = 4 \/ (22 <= uint r <= 27) ->
                     me8 !!! Regidx r = m0 !!! Regidx r).
    { intro Hset.
      rewrite /me8 (upd_ne me7 (Regidx csp_rs1) (Regidx r) _
                      (Hme csp_rs1 2 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /me7 (upd_ne me6 (Regidx s5_idx) (Regidx r) _
                      (Hme s5_idx 21 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /me6 (upd_ne me5 (Regidx s4_idx) (Regidx r) _
                      (Hme s4_idx 20 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /me5 (upd_ne me4 (Regidx s3_idx) (Regidx r) _
                      (Hme s3_idx 19 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /me4 (upd_ne me3 (Regidx s2_idx) (Regidx r) _
                      (Hme s2_idx 18 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /me3 (upd_ne me2 (Regidx s1_idx) (Regidx r) _
                      (Hme s1_idx 9 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /me2 (upd_ne me1 (Regidx s0_idx) (Regidx r) _
                      (Hme s0_idx 8 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /me1 (upd_ne m (Regidx ra_idx) (Regidx r) _
                      (Hme ra_idx 1 ltac:(vm_compute; reflexivity) ltac:(lia))).
      exact (Hfree r Hr Hset). }
    destruct (ucs_cases r Hr) as [E2 | [E3 | [E4 | [E8 | [E9 | E18]]]]].
    - assert (Er : Regidx r = Regidx csp_rs1)
        by (apply (uidx_eq r 2); [ exact E2 | vm_compute; reflexivity ]).
      rewrite Er /me8 (upd_eq me7 (Regidx csp_rs1) (regval_into_reg sp0)).
      rewrite <- Hsp0. reflexivity.
    - apply Hfree'; lia.
    - apply Hfree'; lia.
    - assert (Er : Regidx r = Regidx s0_idx)
        by (apply (uidx_eq r 8); [ exact E8 | vm_compute; reflexivity ]).
      rewrite Er /me8 (upd_ne me7 (Regidx csp_rs1) (Regidx s0_idx) _
                         ltac:(vm_compute; discriminate)).
      rewrite /me7 (upd_ne me6 (Regidx s5_idx) (Regidx s0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s4_idx) (Regidx s0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s3_idx) (Regidx s0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s2_idx) (Regidx s0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me3 (upd_ne me2 (Regidx s1_idx) (Regidx s0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me2. exact (upd_eq me1 (Regidx s0_idx) (regval_into_reg _)).
    - assert (Er : Regidx r = Regidx s1_idx)
        by (apply (uidx_eq r 9); [ exact E9 | vm_compute; reflexivity ]).
      rewrite Er /me8 (upd_ne me7 (Regidx csp_rs1) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)).
      rewrite /me7 (upd_ne me6 (Regidx s5_idx) (Regidx s1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me6 (upd_ne me5 (Regidx s4_idx) (Regidx s1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me5 (upd_ne me4 (Regidx s3_idx) (Regidx s1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me4 (upd_ne me3 (Regidx s2_idx) (Regidx s1_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /me3. exact (upd_eq me2 (Regidx s1_idx) (regval_into_reg _)).
    - assert (Ecase : uint r = 18 \/ uint r = 19 \/ uint r = 20 \/
                      uint r = 21 \/ (22 <= uint r <= 27)) by lia.
      destruct Ecase as [E|[E|[E|[E|E]]]].
      + assert (Er : Regidx r = Regidx s2_idx)
          by (apply (uidx_eq r 18); [ exact E | vm_compute; reflexivity ]).
        rewrite Er /me8 (upd_ne me7 (Regidx csp_rs1) (Regidx s2_idx) _
                           ltac:(vm_compute; discriminate)).
        rewrite /me7 (upd_ne me6 (Regidx s5_idx) (Regidx s2_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /me6 (upd_ne me5 (Regidx s4_idx) (Regidx s2_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /me5 (upd_ne me4 (Regidx s3_idx) (Regidx s2_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /me4. exact (upd_eq me3 (Regidx s2_idx) (regval_into_reg _)).
      + assert (Er : Regidx r = Regidx s3_idx)
          by (apply (uidx_eq r 19); [ exact E | vm_compute; reflexivity ]).
        rewrite Er /me8 (upd_ne me7 (Regidx csp_rs1) (Regidx s3_idx) _
                           ltac:(vm_compute; discriminate)).
        rewrite /me7 (upd_ne me6 (Regidx s5_idx) (Regidx s3_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /me6 (upd_ne me5 (Regidx s4_idx) (Regidx s3_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /me5. exact (upd_eq me4 (Regidx s3_idx) (regval_into_reg _)).
      + assert (Er : Regidx r = Regidx s4_idx)
          by (apply (uidx_eq r 20); [ exact E | vm_compute; reflexivity ]).
        rewrite Er /me8 (upd_ne me7 (Regidx csp_rs1) (Regidx s4_idx) _
                           ltac:(vm_compute; discriminate)).
        rewrite /me7 (upd_ne me6 (Regidx s5_idx) (Regidx s4_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /me6. exact (upd_eq me5 (Regidx s4_idx) (regval_into_reg _)).
      + assert (Er : Regidx r = Regidx s5_idx)
          by (apply (uidx_eq r 21); [ exact E | vm_compute; reflexivity ]).
        rewrite Er /me8 (upd_ne me7 (Regidx csp_rs1) (Regidx s5_idx) _
                           ltac:(vm_compute; discriminate)).
        rewrite /me7. exact (upd_eq me6 (Regidx s5_idx) (regval_into_reg _)).
      + apply Hfree'; lia.
  Qed.



  (* --------------------------------------------------------------------- *)
  (* THE READ/WRITE LOOP @0x22.  Unbounded, and every arm is walked: read    *)
  (* may fill the buffer, fill part of it, return zero at end of file, or    *)
  (* fail; write may return the count or anything else.  What goes round is  *)
  (* the 512-byte buffer at SOME contents -- read's row does not say which   *)
  (* bytes moved, so neither does the invariant -- and the six registers.    *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_cat_loop (m0 : regfile) (sp0 fdv : mword 64) (n : nat)
      (I Cend : iProp Σ) :
    m0 !!! Regidx csp_rs1 = sp0 ->
    uint sp0 mod 8 = 0 ->
    64 <= uint sp0 ->
    kcat_round fdv I Cend -∗
    cat_code γt -∗ cat_rodata γt -∗
    (∀ (h : CpuId) (m : regfile) (f : nat -> bv 8),
       ⌜ cv_inv m0 m sp0 fdv ⌝ -∗
       I -∗
       uword γd (uint sp0 - 8) (m0 !!! Regidx ra_idx) -∗
       uword γd (uint sp0 - 16) (m0 !!! Regidx s0_idx) -∗
       uword γd (uint sp0 - 24) (m0 !!! Regidx s1_idx) -∗
       uword γd (uint sp0 - 32) (m0 !!! Regidx s2_idx) -∗
       uword γd (uint sp0 - 40) (m0 !!! Regidx s3_idx) -∗
       uword γd (uint sp0 - 48) (m0 !!! Regidx s4_idx) -∗
       uword γd (uint sp0 - 56) (m0 !!! Regidx s5_idx) -∗
       (∃ w : mword 64, uword γd (uint sp0 - 64) w) -∗
       ubytes γd CatSyms.buf 512 f -∗
       urun N h m (mword_of_int 0x22) (10 + (12 + (4 + n))) -∗
       (∀ (h' : CpuId) (m' : regfile) (g : nat -> bv 8),
          ⌜ ucallee_saved m0 m' ⌝ -∗
          Cend -∗
          ubytes γd CatSyms.buf 512 g -∗
          urun N h' m' (ret_pc (m0 !!! Regidx ra_idx))
            (8 + (10 + (12 + (4 + n)))) -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang)).
  Proof using .
    intros Hsp0 Hal8 Hlo. iIntros "#Hround #Hcode #Hro".
    destruct cat_syms_pins
      as (_ & _ & _ & _ & _ & _ & Hread & Hwrite & _ & _ & _).
    iLöb as "IH".
    iIntros (h m f)
      "%Hinv HI Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hbuf Hrun Hcont".
    destruct Hinv as (Hsp & Hs0 & Hs2 & Hs3 & Hs4 & Hs5 & Hfr).
    (* ---- 0x22  c.mv a2,s4 -- the count ---- *)
    iApply (wp_uk_cmv N h m (mword_of_int 0x22) a2_idx s4_idx
              (add_vec zero_reg (m !!! Regidx s4_idx)) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_22 with "Hcode"). }
    assert (E22 : add_vec_int (mword_of_int 0x22 : mword 64) 2
                  = mword_of_int 0x24)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E22. iIntros (h1) "Hrun".
    set (ma := <[Regidx a2_idx
                 := regval_into_reg
                      (add_vec zero_reg (m !!! Regidx s4_idx))]> m).
    (* ---- 0x24  c.mv a1,s2 -- the buffer ---- *)
    iApply (wp_uk_cmv N h1 ma (mword_of_int 0x24) a1_idx s2_idx
              (add_vec zero_reg (ma !!! Regidx s2_idx)) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_24 with "Hcode"). }
    assert (E24 : add_vec_int (mword_of_int 0x24 : mword 64) 2
                  = mword_of_int 0x26)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E24. iIntros (h2) "Hrun".
    set (mb := <[Regidx a1_idx
                 := regval_into_reg
                      (add_vec zero_reg (ma !!! Regidx s2_idx))]> ma).
    (* ---- 0x26  c.mv a0,s3 -- the fd ---- *)
    iApply (wp_uk_cmv N h2 mb (mword_of_int 0x26) a0_idx s3_idx
              (add_vec zero_reg (mb !!! Regidx s3_idx)) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_26 with "Hcode"). }
    assert (E26 : add_vec_int (mword_of_int 0x26 : mword 64) 2
                  = mword_of_int 0x28)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E26. iIntros (h3) "Hrun".
    set (mc := <[Regidx a0_idx
                 := regval_into_reg
                      (add_vec zero_reg (mb !!! Regidx s3_idx))]> mb).
    (* ---- 0x28  jal ra,0x3c4 <read> ---- *)
    iApply (wp_uk_jal N h3 mc (mword_of_int 0x28)
              (mword_of_int 924 : mword 21) ra_idx
              (mword_of_int CatSyms.read) (mword_of_int 0x2c)
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hread; apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Hread; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_28 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (md := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x2c : mword 64)]> mc).
    assert (Hrad : md !!! Regidx ra_idx = (mword_of_int 0x2c : mword 64))
      by exact (upd_eq mc (Regidx ra_idx) (regval_into_reg _)).
    (* the two arguments read's stub asks about *)
    assert (Ha1d : md !!! Regidx a1_idx = (mword_of_int CatSyms.buf : mword 64)).
    { rewrite /md (upd_ne mc (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mc (upd_ne mb (Regidx a0_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mb (upd_eq ma (Regidx a1_idx) (regval_into_reg _)).
      rewrite /ma (upd_ne m (Regidx a2_idx) (Regidx s2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite Hs2. apply add_vec_zero_l. }
    assert (Ha2d : bv_signed (subrange_vec_dec (md !!! Regidx a2_idx) 31 0
                              : mword 32) = Z.of_nat 512).
    { rewrite /md (upd_ne mc (Regidx ra_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mc (upd_ne mb (Regidx a0_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mb (upd_ne ma (Regidx a1_idx) (Regidx a2_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /ma (upd_eq m (Regidx a2_idx) (regval_into_reg _)).
      rewrite Hs4 add_vec_zero_l. vm_compute. reflexivity. }
    (* ---- read(fd, buf, 512) -- THE ROUND'S OWN OBLIGATION ---- *)
    assert (Ha0d : md !!! Regidx a0_idx = fdv).
    { rewrite /md (upd_ne mc (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /mc (upd_eq mb (Regidx a0_idx) (regval_into_reg _)).
      rewrite /mb (upd_ne ma (Regidx a1_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /ma (upd_ne m (Regidx a2_idx) (Regidx s3_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite Hs3. apply add_vec_zero_l. }
    iApply ("Hround" $! h4 md (10 + (12 + (4 + n)))%nat f
              with "[%] [%] [%] Hcode HI Hbuf Hrun");
      [ exact Ha0d | exact Ha1d | exact Ha2d | ].
    iIntros (h5 ret g) "Hpick Hbuf Hrun".
    assert (Eretr : ret_pc (md !!! Regidx ra_idx)
                    = (mword_of_int 0x2c : mword 64))
      by (rewrite Hrad; apply bv_eq; vm_compute; reflexivity).
    rewrite Eretr.
    set (me := <[Regidx a0_idx := ret]>
                 (<[Regidx a7_idx := (mword_of_int 5 : mword 64)]> md)).
    assert (Ha0e : me !!! Regidx a0_idx = ret)
      by exact (upd_eq _ (Regidx a0_idx) ret).
    (* the invariant survived read: everything it names is callee-saved,
       and read wrote only a0, a7 and ra *)
    assert (Hinve : cv_inv m0 me sp0 fdv).
    { apply (cv_inv_upd _ _ _ _ a0_idx ret ltac:(vm_compute; reflexivity)).
      apply (cv_inv_upd _ _ _ _ a7_idx _ ltac:(vm_compute; reflexivity)).
      apply (cv_inv_upd _ _ _ _ ra_idx _ ltac:(vm_compute; reflexivity)).
      apply (cv_inv_upd _ _ _ _ a0_idx _ ltac:(vm_compute; reflexivity)).
      apply (cv_inv_upd _ _ _ _ a1_idx _ ltac:(vm_compute; reflexivity)).
      apply (cv_inv_upd _ _ _ _ a2_idx _ ltac:(vm_compute; reflexivity)).
      unfold cv_inv. repeat (split; [ assumption | ]). exact Hfr. }
    (* ---- 0x2c  c.mv s1,a0 -- n ---- *)
    iApply (wp_uk_cmv N h5 me (mword_of_int 0x2c) s1_idx a0_idx
              (add_vec zero_reg (me !!! Regidx a0_idx)) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_2c with "Hcode"). }
    assert (E2c : add_vec_int (mword_of_int 0x2c : mword 64) 2
                  = mword_of_int 0x2e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E2c. iIntros (h6) "Hrun".
    set (mf := <[Regidx s1_idx
                 := regval_into_reg
                      (add_vec zero_reg (me !!! Regidx a0_idx))]> me).
    assert (Ha0f : mf !!! Regidx a0_idx = ret).
    { rewrite <- Ha0e.
      exact (upd_ne me (Regidx s1_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hs1f : mf !!! Regidx s1_idx = add_vec zero_reg ret).
    { rewrite (upd_eq me (Regidx s1_idx) (regval_into_reg _)).
      rewrite Ha0e. reflexivity. }
    assert (Hinvf : cv_inv m0 mf sp0 fdv)
      by exact (cv_inv_upd _ _ _ _ s1_idx _ ltac:(vm_compute; reflexivity) Hinve).
    (* ---- 0x2e  blez a0,0x54 -- n <= 0 leaves the loop ---- *)
    assert (Etgt2e : add_vec (mword_of_int 0x2e : mword 64)
                       (sign_extend' 64 (mword_of_int 38 : mword 13))
                     = mword_of_int 0x54)
      by (apply bv_eq; vm_compute; reflexivity).
    (* the two tests, in the payment's spelling *)
    assert (Hsz : sint (zero_reg : mword 64) = 0)
      by (vm_compute; reflexivity).
    assert (Hbge : uv_btaken BGE zero_reg (mf !!! Regidx a0_idx)
                   = Z.geb 0 (bv_signed ret)).
    { rewrite Ha0f. cbn [uv_btaken]. unfold zopz0zKzJ_s. rewrite Hsz.
      reflexivity. }
    assert (Hbltz : uv_btaken BLT (mf !!! Regidx a0_idx) zero_reg
                    = Z.ltb (bv_signed ret) 0).
    { rewrite Ha0f. cbn [uv_btaken]. unfold zopz0zI_s. rewrite Hsz.
      reflexivity. }
    destruct (Z.geb 0 (bv_signed ret)) eqn:Hble.
    - (* n <= 0: out of the loop, and 0x54 decides error from end-of-file *)
      iApply (wp_uk_btype0l N h6 mf (mword_of_int 0x2e)
                (mword_of_int 38 : mword 13) a0_idx BGE true
                (mword_of_int 0x54) (10 + (12 + (4 + n)))
                (eq_sym Hbge) (eq_sym Etgt2e)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_2e with "Hcode"). }
      iIntros (h7) "Hrun".
      (* ---- 0x54  bltz a0,0x6a ---- *)
      assert (Etgt54 : add_vec (mword_of_int 0x54 : mword 64)
                         (sign_extend' 64 (mword_of_int 22 : mword 13))
                       = mword_of_int 0x6a)
        by (apply bv_eq; vm_compute; reflexivity).
      destruct (Z.ltb (bv_signed ret) 0) eqn:Hblt.
      + (* n < 0: the read error *)
        iApply (wp_uk_btype0 N h7 mf (mword_of_int 0x54)
                  (mword_of_int 22 : mword 13) a0_idx BLT true
                  (mword_of_int 0x6a) (10 + (12 + (4 + n)))
                  (eq_sym Hbltz) (eq_sym Etgt54)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_cat_54 with "Hcode"). }
        iIntros (h8) "Hrun".
        assert (Hneg : bv_signed ret < 0) by (apply Z.ltb_lt; exact Hblt).
        iDestruct "Hpick" as "[Hcr _]".
        iApply (wp_kcat_cat_die_cr h8 mf n with "[Hcr] Hcode Hro Hrun").
        iApply "Hcr". iPureIntro. exact Hneg.
      + (* n = 0: end of file, and cat() returns *)
        iApply (wp_uk_btype0 N h7 mf (mword_of_int 0x54)
                  (mword_of_int 22 : mword 13) a0_idx BLT false
                  (add_vec (mword_of_int 0x54 : mword 64)
                     (sign_extend' 64 (mword_of_int 22 : mword 13)))
                  (10 + (12 + (4 + n)))
                  (eq_sym Hbltz) eq_refl ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_cat_54 with "Hcode"). }
        assert (E54 : add_vec_int (mword_of_int 0x54 : mword 64) 4
                      = mword_of_int 0x58)
          by (apply bv_eq; vm_compute; reflexivity).
        rewrite E54. iIntros (h8) "Hrun".
        destruct Hinvf as (Hspf & _ & _ & _ & _ & _ & Hfrf).
        assert (Hzero : bv_signed ret = 0).
        { rewrite Z.geb_leb in Hble. apply Z.leb_le in Hble.
          apply Z.ltb_ge in Hblt. lia. }
        iDestruct "Hpick" as "[_ [Hend _]]".
        iDestruct ("Hend" with "[%]") as "HCend"; [ exact Hzero | ].
        iApply (wp_kcat_cat_epi h8 mf m0 sp0 n Hspf Hsp0 Hal8 Hlo Hfrf
                  with "Hcode Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hrun
                        [Hbuf HCend Hcont]").
        iIntros (h9 m') "%Hcs Hrun".
        iApply ("Hcont" $! h9 m' g with "[] HCend Hbuf Hrun").
        iPureIntro. exact Hcs.
    - (* n > 0: write it out *)
      iApply (wp_uk_btype0l N h6 mf (mword_of_int 0x2e)
                (mword_of_int 38 : mword 13) a0_idx BGE false
                (add_vec (mword_of_int 0x2e : mword 64)
                   (sign_extend' 64 (mword_of_int 38 : mword 13)))
                (10 + (12 + (4 + n)))
                (eq_sym Hbge) eq_refl ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_cat_2e with "Hcode"). }
      assert (E2e : add_vec_int (mword_of_int 0x2e : mword 64) 4
                    = mword_of_int 0x32)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E2e. iIntros (h7) "Hrun".
      destruct Hinvf as (Hspf & Hs0f & Hs2f & Hs3f & Hs4f & Hs5f & Hfrf).
      (* ---- 0x32  c.mv a2,s1 ; 0x34  c.mv a1,s2 ; 0x36  c.mv a0,s5 ---- *)
      iApply (wp_uk_cmv N h7 mf (mword_of_int 0x32) a2_idx s1_idx
                (add_vec zero_reg (mf !!! Regidx s1_idx)) (10 + (12 + (4 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
      { iApply (uis_cat_32 with "Hcode"). }
      assert (E32 : add_vec_int (mword_of_int 0x32 : mword 64) 2
                    = mword_of_int 0x34)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E32. iIntros (h8) "Hrun".
      set (mg := <[Regidx a2_idx
                   := regval_into_reg
                        (add_vec zero_reg (mf !!! Regidx s1_idx))]> mf).
      iApply (wp_uk_cmv N h8 mg (mword_of_int 0x34) a1_idx s2_idx
                (add_vec zero_reg (mg !!! Regidx s2_idx)) (10 + (12 + (4 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
      { iApply (uis_cat_34 with "Hcode"). }
      assert (E34 : add_vec_int (mword_of_int 0x34 : mword 64) 2
                    = mword_of_int 0x36)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E34. iIntros (h9) "Hrun".
      set (mh := <[Regidx a1_idx
                   := regval_into_reg
                        (add_vec zero_reg (mg !!! Regidx s2_idx))]> mg).
      iApply (wp_uk_cmv N h9 mh (mword_of_int 0x36) a0_idx s5_idx
                (add_vec zero_reg (mh !!! Regidx s5_idx)) (10 + (12 + (4 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
      { iApply (uis_cat_36 with "Hcode"). }
      assert (E36 : add_vec_int (mword_of_int 0x36 : mword 64) 2
                    = mword_of_int 0x38)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E36. iIntros (h10) "Hrun".
      set (mi := <[Regidx a0_idx
                   := regval_into_reg
                        (add_vec zero_reg (mh !!! Regidx s5_idx))]> mh).
      (* ---- 0x38  jal ra,0x3cc <write> ---- *)
      iApply (wp_uk_jal N h10 mi (mword_of_int 0x38)
                (mword_of_int 916 : mword 21) ra_idx
                (mword_of_int CatSyms.write) (mword_of_int 0x3c)
                (10 + (12 + (4 + n)))
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hwrite; apply bv_eq; vm_compute; reflexivity)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Hwrite; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_cat_38 with "Hcode"). }
      iIntros (h11) "Hrun".
      set (mj := <[Regidx ra_idx
                   := regval_into_reg (mword_of_int 0x3c : mword 64)]> mi).
      assert (Hraj : mj !!! Regidx ra_idx = (mword_of_int 0x3c : mword 64))
        by exact (upd_eq mi (Regidx ra_idx) (regval_into_reg _)).
      (* ---- write(1, buf, n) -- THE ROUND'S OWN OBLIGATION ---- *)
      assert (Hpos : 0 < bv_signed ret).
      { rewrite Z.geb_leb in Hble. apply Z.leb_gt in Hble. lia. }
      set (nb := Z.to_nat (bv_signed ret)).
      assert (Hnbz : ret = (mword_of_int (Z.of_nat nb) : mword 64)).
      { unfold nb. rewrite (Z2Nat.id (bv_signed ret) ltac:(lia)).
        symmetry. apply UkCat.moi_of_sint. }
      assert (Hnbpos : (0 < nb)%nat) by (unfold nb; lia).
      assert (Ha0j : mj !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
      { rewrite /mj (upd_ne mi (Regidx ra_idx) (Regidx a0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mi (upd_eq mh (Regidx a0_idx) (regval_into_reg _)).
        rewrite /mh (upd_ne mg (Regidx a1_idx) (Regidx s5_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mg (upd_ne mf (Regidx a2_idx) (Regidx s5_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite Hs5f. apply add_vec_zero_l. }
      assert (Ha1j : mj !!! Regidx a1_idx
                     = (mword_of_int CatSyms.buf : mword 64)).
      { rewrite /mj (upd_ne mi (Regidx ra_idx) (Regidx a1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mi (upd_ne mh (Regidx a0_idx) (Regidx a1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mh (upd_eq mg (Regidx a1_idx) (regval_into_reg _)).
        rewrite /mg (upd_ne mf (Regidx a2_idx) (Regidx s2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite Hs2f. apply add_vec_zero_l. }
      assert (Ha2j : mj !!! Regidx a2_idx
                     = (mword_of_int (Z.of_nat nb) : mword 64)).
      { rewrite /mj (upd_ne mi (Regidx ra_idx) (Regidx a2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mi (upd_ne mh (Regidx a0_idx) (Regidx a2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mh (upd_ne mg (Regidx a1_idx) (Regidx a2_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mg (upd_eq mf (Regidx a2_idx) (regval_into_reg _)).
        rewrite Hs1f !add_vec_zero_l. exact Hnbz. }
      iDestruct "Hpick" as "[_ [_ Hwr]]".
      iDestruct ("Hwr" $! nb with "[%] [%]") as "Hw";
        [ unfold nb; rewrite Z2Nat.id; lia | exact Hnbpos | ].
      iApply ("Hw" $! h11 mj (10 + (12 + (4 + n)))%nat
                with "[%] [%] [%] Hcode Hbuf Hrun");
        [ exact Ha0j | exact Ha1j | exact Ha2j | ].
      iIntros (h12 wret) "[Hpick Hbuf] Hrun".
      assert (Eretw : ret_pc (mj !!! Regidx ra_idx)
                      = (mword_of_int 0x3c : mword 64))
        by (rewrite Hraj; apply bv_eq; vm_compute; reflexivity).
      rewrite Eretw.
      set (mk := <[Regidx a0_idx := wret]>
                   (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> mj)).
      assert (Hinvk : cv_inv m0 mk sp0 fdv).
      { apply (cv_inv_upd _ _ _ _ a0_idx wret ltac:(vm_compute; reflexivity)).
        apply (cv_inv_upd _ _ _ _ a7_idx _ ltac:(vm_compute; reflexivity)).
        apply (cv_inv_upd _ _ _ _ ra_idx _ ltac:(vm_compute; reflexivity)).
        apply (cv_inv_upd _ _ _ _ a0_idx _ ltac:(vm_compute; reflexivity)).
        apply (cv_inv_upd _ _ _ _ a1_idx _ ltac:(vm_compute; reflexivity)).
        apply (cv_inv_upd _ _ _ _ a2_idx _ ltac:(vm_compute; reflexivity)).
        unfold cv_inv. repeat (split; [ assumption | ]). exact Hfrf. }
      (* ---- 0x3c  beq a0,s1,0x22 -- THE BACK EDGE ---- *)
      assert (Etgt3c : add_vec (mword_of_int 0x3c : mword 64)
                         (sign_extend' 64 (mword_of_int 8166 : mword 13))
                       = mword_of_int 0x22)
        by (apply bv_eq; vm_compute; reflexivity).
      (* the two registers the branch compares, so that the NO-SHORT
         disjunct of the payment can decide it (RULING (g)) *)
      assert (Ha0k : mk !!! Regidx a0_idx = wret)
        by exact (upd_eq _ (Regidx a0_idx) wret).
      assert (Hs1k : mk !!! Regidx s1_idx = add_vec zero_reg ret).
      { rewrite /mk (upd_ne
                       (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> mj)
                       (Regidx a0_idx) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite (upd_ne mj (Regidx a7_idx) (Regidx s1_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite /mj (upd_ne mi (Regidx ra_idx) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mi (upd_ne mh (Regidx a0_idx) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mh (upd_ne mg (Regidx a1_idx) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /mg (upd_ne mf (Regidx a2_idx) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        exact Hs1f. }
      destruct (uv_btaken BEQ (mk !!! Regidx a0_idx) (mk !!! Regidx s1_idx))
        eqn:Hbeq.
      + (* write wrote all of it: round again *)
        iApply (wp_uk_btype_later N h12 mk (mword_of_int 0x3c)
                  (mword_of_int 8166 : mword 13) s1_idx a0_idx BEQ true
                  (mword_of_int 0x22) (10 + (12 + (4 + n)))
                  (eq_sym Hbeq) (eq_sym Etgt3c)
                  ltac:(intros _; vm_compute; reflexivity)
                  with "[] Hrun").
        { iApply (uis_cat_3c with "Hcode"). }
        iNext. iIntros (h13) "Hrun".
        (* EITHER disjunct funds the back edge: the no-short arm carries
           the invariant beside its equation, the diagnostic arm has it as
           the left conjunct of the additive pair. *)
        iAssert I with "[Hpick]" as "HI".
        { iDestruct "Hpick" as "[HI _]". iApply "HI". iPureIntro.
          pose proof Hbeq as Hbeq'.
          rewrite Ha0k Hs1k add_vec_zero_l in Hbeq'. cbn [uv_btaken] in Hbeq'.
          apply eq_vec_true_iff in Hbeq'. rewrite Hbeq'. exact Hnbz. }
        iApply ("IH" $! h13 mk g with "[] HI Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8
                                       Hbuf Hrun Hcont").
        iPureIntro. exact Hinvk.
      + (* it did not: the write error *)
        iApply (wp_uk_btype_later N h12 mk (mword_of_int 0x3c)
                  (mword_of_int 8166 : mword 13) s1_idx a0_idx BEQ false
                  (add_vec (mword_of_int 0x3c : mword 64)
                     (sign_extend' 64 (mword_of_int 8166 : mword 13)))
                  (10 + (12 + (4 + n)))
                  (eq_sym Hbeq) eq_refl ltac:(discriminate)
                  with "[] Hrun").
        { iApply (uis_cat_3c with "Hcode"). }
        assert (E3c : add_vec_int (mword_of_int 0x3c : mword 64) 4
                      = mword_of_int 0x40)
          by (apply bv_eq; vm_compute; reflexivity).
        iNext. rewrite E3c. iIntros (h13) "Hrun".
        (* ...AND THE SHORT BRANCH IS REFUTED FROM THE NO-SHORT DISJUNCT:
           a payer that took it says the call returned exactly [nb], which
           is the value [s1] holds, so this branch was not taken.  A payer
           that took the diagnostic arm funds the tail as before. *)
        iAssert kcat_dg_cw with "[Hpick]" as "Hdg".
        { iDestruct "Hpick" as "[_ Hdg]". iApply "Hdg". iPureIntro.
          intros Hws.
          assert (Hbeqt : uv_btaken BEQ (mk !!! Regidx a0_idx)
                            (mk !!! Regidx s1_idx) = true).
          { rewrite Ha0k Hs1k Hws add_vec_zero_l Hnbz.
            cbn [uv_btaken]. apply eq_vec_refl. }
          rewrite Hbeqt in Hbeq. discriminate. }
        iApply (wp_kcat_cat_die_cw h13 mk n with "Hdg Hcode Hro Hrun").
  Qed.


  (* --------------------------------------------------------------------- *)
  (* cat(fd) @0x0.  Eight words of frame, ra and s0..s5 spilled, then the    *)
  (* four loop constants into callee-saved registers and into the loop.      *)
  (* --------------------------------------------------------------------- *)
  Lemma wp_kcat_cat (fdv : mword 64) (f : nat -> bv 8)
      (h : CpuId) (m : regfile) (n : nat) (I Cend : iProp Σ) :
    m !!! Regidx a0_idx = fdv ->
    kcat_round fdv I Cend -∗
    cat_code γt -∗ cat_rodata γt -∗
    I -∗
    ubytes γd CatSyms.buf 512 f -∗
    urun N h m (mword_of_int CatSyms.cat) (8 + (10 + (12 + (4 + n)))) -∗
    (∀ (h' : CpuId) (m' : regfile) (g : nat -> bv 8),
       ⌜ ucallee_saved m m' ⌝ -∗
       Cend -∗
       ubytes γd CatSyms.buf 512 g -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (8 + (10 + (12 + (4 + n)))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0.
    iIntros "#Hround #Hcode #Hro HI Hbuf Hrun Hcont".
    destruct cat_syms_pins
      as (_ & _ & Hcat & _ & _ & _ & _ & _ & _ & _ & _).
    rewrite Hcat.
    iDestruct (urun_stack with "Hrun") as %[Hal8' Hroom'].
    remember (m !!! Regidx csp_rs1) as sp0 eqn:Hsp0e.
    assert (Hsp : m !!! Regidx csp_rs1 = sp0) by (symmetry; exact Hsp0e).
    clear Hsp0e.
    assert (Hal8 : uint sp0 mod 8 = 0) by exact Hal8'.
    assert (Hlo : 64 <= uint sp0) by (clear -Hroom'; lia).
    assert (Hbsp : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                   = bv_unsigned sp0 - 64).
    { replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(apply Z.leb_le; reflexivity)
               ltac:(rewrite <- uint_unsigned; exact Hlo)). }
    assert (Hsp64 : uint (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                    = uint sp0 - 64)
      by (rewrite !uint_unsigned; exact Hbsp).
    assert (HR : 0 <= bv_unsigned sp0 < 18446744073709551616).
    { pose proof (bv_unsigned_in_range 64 sp0) as H0.
      assert (Em : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite Em in H0. exact H0. }
    assert (Hlt8 : bv_unsigned (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                   + 8 * Z.of_nat 8 < Z64)
      by (clear -Hbsp HR; rewrite Hbsp; unfold Z64; lia).
    assert (Hup : add_vec_int (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                    (8 * Z.of_nat 8) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos (add_vec_int sp0 (- (8 * Z.of_nat 8)))
                 (8 * Z.of_nat 8) ltac:(apply Z.leb_le; reflexivity) Hlt8).
      clear -Hbsp. rewrite Hbsp. lia. }
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
    assert (Ho8 : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
      by (vm_compute; reflexivity).
    (* ---- 0x0  c.addi16sp sp,sp,-64 ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x0)
              (mword_of_int 60 : mword 6) 8 (10 + (12 + (4 + n)))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_cat_00 with "Hcode"). }
    iIntros "Hframe".
    assert (E00 : add_vec_int (mword_of_int 0x0 : mword 64) 2
                  = mword_of_int 0x2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsp E00.
    iIntros (hp0) "Hrun".
    set (mp1 := <[Regidx csp_rs1
                  := regval_into_reg (add_vec_int sp0 (- (8 * Z.of_nat 8)))]> m).
    assert (Hspp1 : mp1 !!! Regidx csp_rs1
                    = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg _)).
    iDestruct (ustack_8_open with "Hframe")
      as "(_ & [%v1 Hw1] & [%v2 Hw2] & [%v3 Hw3] & [%v4 Hw4] & [%v5 Hw5]
            & [%v6 Hw6] & [%v7 Hw7] & Hw8)".
    (* ---- 0x2  c.sdsp ra,56(sp) ---- *)
    assert (Hrra_idx : mp1 !!! Regidx ra_idx = m !!! Regidx ra_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uk_csdsp N hp0 mp1 (mword_of_int 0x2)
              (mword_of_int 7 : mword 6) ra_idx (uint sp0 - 8) v1 (10 + (12 + (4 + n)))
              ltac:(rewrite Hspp1 Hsp64 Ho56; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw1 Hrun").
    { iApply (uis_cat_02 with "Hcode"). }
    iIntros "Hw1". rewrite Hrra_idx.
    assert (E02 : add_vec_int (mword_of_int 0x2 : mword 64) 2
                  = mword_of_int 0x4)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E02.
    iIntros (hp1) "Hrun".
    (* ---- 0x4  c.sdsp s0,48(sp) ---- *)
    assert (Hrs0_idx : mp1 !!! Regidx s0_idx = m !!! Regidx s0_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s0_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uk_csdsp N hp1 mp1 (mword_of_int 0x4)
              (mword_of_int 6 : mword 6) s0_idx (uint sp0 - 16) v2 (10 + (12 + (4 + n)))
              ltac:(rewrite Hspp1 Hsp64 Ho48; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw2 Hrun").
    { iApply (uis_cat_04 with "Hcode"). }
    iIntros "Hw2". rewrite Hrs0_idx.
    assert (E04 : add_vec_int (mword_of_int 0x4 : mword 64) 2
                  = mword_of_int 0x6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E04.
    iIntros (hp2) "Hrun".
    (* ---- 0x6  c.sdsp s1,40(sp) ---- *)
    assert (Hrs1_idx : mp1 !!! Regidx s1_idx = m !!! Regidx s1_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s1_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uk_csdsp N hp2 mp1 (mword_of_int 0x6)
              (mword_of_int 5 : mword 6) s1_idx (uint sp0 - 24) v3 (10 + (12 + (4 + n)))
              ltac:(rewrite Hspp1 Hsp64 Ho40; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw3 Hrun").
    { iApply (uis_cat_06 with "Hcode"). }
    iIntros "Hw3". rewrite Hrs1_idx.
    assert (E06 : add_vec_int (mword_of_int 0x6 : mword 64) 2
                  = mword_of_int 0x8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E06.
    iIntros (hp3) "Hrun".
    (* ---- 0x8  c.sdsp s2,32(sp) ---- *)
    assert (Hrs2_idx : mp1 !!! Regidx s2_idx = m !!! Regidx s2_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s2_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uk_csdsp N hp3 mp1 (mword_of_int 0x8)
              (mword_of_int 4 : mword 6) s2_idx (uint sp0 - 32) v4 (10 + (12 + (4 + n)))
              ltac:(rewrite Hspp1 Hsp64 Ho32; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw4 Hrun").
    { iApply (uis_cat_08 with "Hcode"). }
    iIntros "Hw4". rewrite Hrs2_idx.
    assert (E08 : add_vec_int (mword_of_int 0x8 : mword 64) 2
                  = mword_of_int 0xa)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E08.
    iIntros (hp4) "Hrun".
    (* ---- 0xa  c.sdsp s3,24(sp) ---- *)
    assert (Hrs3_idx : mp1 !!! Regidx s3_idx = m !!! Regidx s3_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s3_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uk_csdsp N hp4 mp1 (mword_of_int 0xa)
              (mword_of_int 3 : mword 6) s3_idx (uint sp0 - 40) v5 (10 + (12 + (4 + n)))
              ltac:(rewrite Hspp1 Hsp64 Ho24; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw5 Hrun").
    { iApply (uis_cat_0a with "Hcode"). }
    iIntros "Hw5". rewrite Hrs3_idx.
    assert (E0a : add_vec_int (mword_of_int 0xa : mword 64) 2
                  = mword_of_int 0xc)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0a.
    iIntros (hp5) "Hrun".
    (* ---- 0xc  c.sdsp s4,16(sp) ---- *)
    assert (Hrs4_idx : mp1 !!! Regidx s4_idx = m !!! Regidx s4_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s4_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uk_csdsp N hp5 mp1 (mword_of_int 0xc)
              (mword_of_int 2 : mword 6) s4_idx (uint sp0 - 48) v6 (10 + (12 + (4 + n)))
              ltac:(rewrite Hspp1 Hsp64 Ho16; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw6 Hrun").
    { iApply (uis_cat_0c with "Hcode"). }
    iIntros "Hw6". rewrite Hrs4_idx.
    assert (E0c : add_vec_int (mword_of_int 0xc : mword 64) 2
                  = mword_of_int 0xe)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0c.
    iIntros (hp6) "Hrun".
    (* ---- 0xe  c.sdsp s5,8(sp) ---- *)
    assert (Hrs5_idx : mp1 !!! Regidx s5_idx = m !!! Regidx s5_idx)
      by exact (upd_ne m (Regidx csp_rs1) (Regidx s5_idx) _
                  ltac:(vm_compute; discriminate)).
    iApply (wp_uk_csdsp N hp6 mp1 (mword_of_int 0xe)
              (mword_of_int 1 : mword 6) s5_idx (uint sp0 - 56) v7 (10 + (12 + (4 + n)))
              ltac:(rewrite Hspp1 Hsp64 Ho8; lia)
              ltac:(rewrite Zminus_mod Hal8; reflexivity)
              with "[] Hw7 Hrun").
    { iApply (uis_cat_0e with "Hcode"). }
    iIntros "Hw7". rewrite Hrs5_idx.
    assert (E0e : add_vec_int (mword_of_int 0xe : mword 64) 2
                  = mword_of_int 0x10)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0e.
    iIntros (hp7) "Hrun".
    (* ---- 0x10  c.addi4spn s0,sp,64 -- s0 := the ENTRY sp ---- *)
    assert (Ec4 : (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))
                   : mword 64) = mword_of_int (8 * Z.of_nat 8))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi4spn N hp7 mp1 (mword_of_int 0x10)
              (mword_of_int 0 : mword 3) (mword_of_int 16 : mword 8) s0_idx sp0
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hspp1 Ec4; exact (eq_sym Hup))
              with "[] Hrun").
    { iApply (uis_cat_10 with "Hcode"). }
    assert (E10 : add_vec_int (mword_of_int 0x10 : mword 64) 2
                  = mword_of_int 0x12)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E10. iIntros (hp8) "Hrun".
    set (mp2 := <[Regidx s0_idx := regval_into_reg sp0]> mp1).
    (* ---- 0x12  c.mv s3,a0 -- the fd ---- *)
    assert (Ha0p2 : mp2 !!! Regidx a0_idx = fdv).
    { rewrite <- Ha0.
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx a0_idx) _
                      ltac:(vm_compute; discriminate)).
      rewrite /mp1. exact (upd_ne m (Regidx csp_rs1) (Regidx a0_idx) _
                             ltac:(vm_compute; discriminate)). }
    iApply (wp_uk_cmv N hp8 mp2 (mword_of_int 0x12) s3_idx a0_idx
              (add_vec zero_reg (mp2 !!! Regidx a0_idx)) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_12 with "Hcode"). }
    assert (E12 : add_vec_int (mword_of_int 0x12 : mword 64) 2
                  = mword_of_int 0x14)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E12. iIntros (hp9) "Hrun".
    set (mp3 := <[Regidx s3_idx
                  := regval_into_reg
                       (add_vec zero_reg (mp2 !!! Regidx a0_idx))]> mp2).
    (* ---- 0x14  li s4,512 ---- *)
    iApply (wp_uk_li N hp9 mp3 (mword_of_int 0x14)
              (mword_of_int 512 : mword 12) s4_idx
              (add_vec zero_reg (sign_extend' 64 (mword_of_int 512 : mword 12)))
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_14 with "Hcode"). }
    assert (E14 : add_vec_int (mword_of_int 0x14 : mword 64) 4
                  = mword_of_int 0x18)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E14. iIntros (hp10) "Hrun".
    set (mp4 := <[Regidx s4_idx
                  := regval_into_reg
                       (add_vec zero_reg
                          (sign_extend' 64 (mword_of_int 512 : mword 12)))]> mp3).
    (* ---- 0x18  auipc s2,0x1 ; 0x1c  addi s2,s2,-8 -- buf ---- *)
    assert (Ebuf : add_vec (add_vec (mword_of_int 0x18 : mword 64)
                              (auipc_off (mword_of_int 1 : mword 20)))
                     (sign_extend' 64 (mword_of_int 4088 : mword 12))
                   = mword_of_int CatSyms.buf)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_auipc N hp10 mp4 (mword_of_int 0x18)
              (mword_of_int 1 : mword 20) s2_idx
              (add_vec (mword_of_int 0x18 : mword 64)
                 (auipc_off (mword_of_int 1 : mword 20)))
              (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_cat_18 with "Hcode"). }
    assert (E18 : add_vec_int (mword_of_int 0x18 : mword 64) 4
                  = mword_of_int 0x1c)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E18. iIntros (hp11) "Hrun".
    set (mp5 := <[Regidx s2_idx := regval_into_reg
                    (add_vec (mword_of_int 0x18 : mword 64)
                       (auipc_off (mword_of_int 1 : mword 20)))]> mp4).
    iApply (wp_uk_addi N hp11 mp5 (mword_of_int 0x1c)
              (mword_of_int 4088 : mword 12) s2_idx s2_idx
              (mword_of_int CatSyms.buf) (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mp4 (Regidx s2_idx) (regval_into_reg _));
                    exact (eq_sym Ebuf))
              with "[] Hrun").
    { iApply (uis_cat_1c with "Hcode"). }
    assert (E1c : add_vec_int (mword_of_int 0x1c : mword 64) 4
                  = mword_of_int 0x20)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1c. iIntros (hp12) "Hrun".
    set (mp6 := <[Regidx s2_idx
                  := regval_into_reg
                       (mword_of_int CatSyms.buf : mword 64)]> mp5).
    (* ---- 0x20  c.li s5,1 ---- *)
    iApply (wp_uk_cli N hp12 mp6 (mword_of_int 0x20)
              (mword_of_int 1 : mword 6) s5_idx (10 + (12 + (4 + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_cat_20 with "Hcode"). }
    assert (E20 : add_vec_int (mword_of_int 0x20 : mword 64) 2
                  = mword_of_int 0x22)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E20. iIntros (hp13) "Hrun".
    set (mp7 := <[Regidx s5_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 1 : mword 6)
                        : mword 64)]> mp6).
    (* the loop invariant, at the head *)
    assert (Hinv0 : cv_inv m mp7 sp0 fdv).
    { unfold cv_inv.
      (* sp *)
      split.
      { rewrite /mp7 (upd_ne mp6 (Regidx s5_idx) (Regidx csp_rs1) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp6 (upd_ne mp5 (Regidx s2_idx) (Regidx csp_rs1) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp5 (upd_ne mp4 (Regidx s2_idx) (Regidx csp_rs1) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp4 (upd_ne mp3 (Regidx s4_idx) (Regidx csp_rs1) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp3 (upd_ne mp2 (Regidx s3_idx) (Regidx csp_rs1) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx csp_rs1) _
                        ltac:(vm_compute; discriminate)).
        exact Hspp1. }
      (* s0 *)
      split.
      { rewrite /mp7 (upd_ne mp6 (Regidx s5_idx) (Regidx s0_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp6 (upd_ne mp5 (Regidx s2_idx) (Regidx s0_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp5 (upd_ne mp4 (Regidx s2_idx) (Regidx s0_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp4 (upd_ne mp3 (Regidx s4_idx) (Regidx s0_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp3 (upd_ne mp2 (Regidx s3_idx) (Regidx s0_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp2. exact (upd_eq mp1 (Regidx s0_idx) (regval_into_reg sp0)). }
      (* s2 = buf *)
      split.
      { rewrite /mp7 (upd_ne mp6 (Regidx s5_idx) (Regidx s2_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp6. exact (upd_eq mp5 (Regidx s2_idx) (regval_into_reg _)). }
      (* s3 = fd *)
      split.
      { rewrite /mp7 (upd_ne mp6 (Regidx s5_idx) (Regidx s3_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp6 (upd_ne mp5 (Regidx s2_idx) (Regidx s3_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp5 (upd_ne mp4 (Regidx s2_idx) (Regidx s3_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp4 (upd_ne mp3 (Regidx s4_idx) (Regidx s3_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp3 (upd_eq mp2 (Regidx s3_idx) (regval_into_reg _)).
        rewrite Ha0p2. apply add_vec_zero_l. }
      (* s4 = 512 *)
      split.
      { rewrite /mp7 (upd_ne mp6 (Regidx s5_idx) (Regidx s4_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp6 (upd_ne mp5 (Regidx s2_idx) (Regidx s4_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp5 (upd_ne mp4 (Regidx s2_idx) (Regidx s4_idx) _
                        ltac:(vm_compute; discriminate)).
        rewrite /mp4 (upd_eq mp3 (Regidx s4_idx) (regval_into_reg _)).
        rewrite add_vec_zero_l. apply bv_eq; vm_compute; reflexivity. }
      (* s5 = 1 *)
      split.
      { rewrite /mp7 (upd_eq mp6 (Regidx s5_idx) (regval_into_reg _)).
        apply bv_eq; vm_compute; reflexivity. }
      (* everything else is untouched *)
      intros r Hr Hset.
      assert (Kne : forall (q : mword 5) (z : Z),
                 uint q = z ->
                 (z = 2 \/ z = 8 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21) ->
                 Regidx r <> Regidx q).
      { intros q z Hq Hz. apply uidx_ne. rewrite Hq. lia. }
      rewrite /mp7 (upd_ne mp6 (Regidx s5_idx) (Regidx r) _
                      (Kne s5_idx 21 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /mp6 (upd_ne mp5 (Regidx s2_idx) (Regidx r) _
                      (Kne s2_idx 18 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /mp5 (upd_ne mp4 (Regidx s2_idx) (Regidx r) _
                      (Kne s2_idx 18 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /mp4 (upd_ne mp3 (Regidx s4_idx) (Regidx r) _
                      (Kne s4_idx 20 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /mp3 (upd_ne mp2 (Regidx s3_idx) (Regidx r) _
                      (Kne s3_idx 19 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /mp2 (upd_ne mp1 (Regidx s0_idx) (Regidx r) _
                      (Kne s0_idx 8 ltac:(vm_compute; reflexivity) ltac:(lia))).
      rewrite /mp1 (upd_ne m (Regidx csp_rs1) (Regidx r) _
                      (Kne csp_rs1 2 ltac:(vm_compute; reflexivity) ltac:(lia))).
      reflexivity. }
    iDestruct (wp_kcat_cat_loop m sp0 fdv n I Cend Hsp Hal8 Hlo
                 with "Hround Hcode Hro") as "Hloop".
    iApply ("Hloop" $! hp13 mp7 f with "[] HI Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8
                                        Hbuf Hrun Hcont").
    iPureIntro. exact Hinv0.
  Qed.

End UkCatCat.
