(* ===================================================================== *)
(* UkShGettoken.v -- gettoken AND peek AT THE REFERENCE PARSER, ONCE       *)
(* (design/user-once.md SS2, worklist A2a).                                *)
(*                                                                        *)
(* sh's [gettoken] used to be walked three times -- UkShParseTok under     *)
(* [ushp_no_symbols], UkShRedirGtk under [ushs_gt_ok], UkShPipeTok under   *)
(* [ushq_sym_ok] -- with the SAME statement modulo the shape premise and   *)
(* the three pure answer functions, each over a different DISPATCH lemma  *)
(* for the switch at 0x332.  This file is that walk once, stated at the    *)
(* reference parser [RefParse.ref_gettoken], and the landed statements    *)
(* are its corollaries through RefParseSym.ref_gettoken_ushs.              *)
(*                                                                        *)
(* (1) THE ARMS OF THE SWITCH.  [wp_kshp_gtk_disp_gt] (the '>' arm, the    *)
(*     '>>' lookahead refuted; was UkShRedirTok), [wp_kshp_gtk_disp_bar]  *)
(*     (the '|' arm, no lookahead; was UkShPipeTok), [wp_kshp_gtk_disp_ns] *)
(*     (the NUL / default dichotomy at a cursor whose byte is not a       *)
(*     symbol; was UkShRedirGtk) and [wp_kshp_gtk_disp_sym], the ONE       *)
(*     dispatch over the symbol scope: both symbol arms land on 0x364 with *)
(*     the cursor advanced by one and s5 holding the byte itself.  Their   *)
(*     text is the landed text; only the premises are spelled with        *)
(*     [RefParse.rb_bar] / [rb_gt].                                        *)
(*                                                                        *)
(* (2) [wp_ref_gettoken] -- gettoken end to end.  Its ONE shape premise is *)
(*     [ref_sym_scope len f] (the walked arms: NUL, word, '|', a single    *)
(*     '>'); its answer is the equation                                    *)
(*     [ref_gettoken len f off = (ret, q, e, fin)]: the code returns       *)
(*     [ret], writes [q] and [e] through the two out-pointers and leaves   *)
(*     the cursor at [fin].  [ref_nonnul] is NOT a premise: it is the      *)
(*     first pure conjunct of [ustr] and is read off the resource.  The    *)
(*     proof is the landed walk (UkShPipeTok's, the widest) with the      *)
(*     reference's four components substituted at the top.                *)
(*     [wp_ref_gettoken_ushs] is the same lemma with the answer spelled    *)
(*     [ushs_gettok_res] / [_end] / [_fin]; the two symbol tiers          *)
(*     (UkShRedirGtk.wp_kshp_gettoken_sym, UkShPipeTok.wp_kshp_gettoken_   *)
(*     syms) are one-line instances of it at their scope premises.        *)
(*     UkShParseTok.wp_kshp_gettoken keeps its own proof: its consumers   *)
(*     (UkShParseExec, UkShParseRedir) sit below this file.               *)
(*                                                                        *)
(* (3) [wp_ref_peek] -- UkShParseLex.wp_kshp_peek, whose walk was already  *)
(*     general, with the answer spelled through [RefParse.ref_peek]: the   *)
(*     table the walk holds as [tlen] bytes at [tf] is the reference's    *)
(*     list [tf <$> seq 0 tlen], and a0 is 1 exactly on a hit.            *)
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
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseTok.
Require Import UkShParseLex.
Require Import RefParse.
Require Import RefParseSym.

Require Import UexecSG.


Section UkShGettoken.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation s9_idx := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).

  (* ---- what the earlier files define, at this file's ghost names ---- *)
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation wp_kshp_fp := (UkShParse.wp_kshp_fp N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).
  Local Notation ushp_cell := (UkShParseTok.ushp_cell N).
  Local Notation wp_kshp_gtk_388 := (UkShParseTok.wp_kshp_gtk_388 N).
  Local Notation wp_kshp_gtk_424 := (UkShParseTok.wp_kshp_gtk_424 N).
  Local Notation wp_kshp_gtk_fin := (UkShParseTok.wp_kshp_gtk_fin N).
  Local Notation wp_kshp_gtk_qst := (UkShParseTok.wp_kshp_gtk_qst N).
  Local Notation wp_kshp_tok_scan := (UkShParseTok.wp_kshp_tok_scan N).
  Local Notation wp_kshp_ws_enter := (UkShParseTok.wp_kshp_ws_enter N).
  Local Notation ushp_sstr := (UkShParse.ushp_sstr N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).


  (* ===================================================================== *)
  (* (1) THE ARMS OF THE SWITCH                                            *)
  (* ===================================================================== *)

  (* the '>' arm: 0x332..0x33e, 0x3a6..0x3be; the '>>' lookahead at 0x3b6
     refuted from the byte after the '>' *)
  Lemma wp_kshp_gtk_disp_gt (dq : dfrac) (s0 : Z) (len k : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (S k < len)%nat ->
    f k = Z_to_bv 8 62 ->
    f (S k) <> Z_to_bv 8 62 ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    urun N h mc (mword_of_int 0x332) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, Regidx t <> Regidx a4_idx ->
             Regidx t <> Regidx a5_idx -> Regidx t <> Regidx s5_idx ->
             Regidx t <> Regidx s1_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s5_idx = mword_of_int 62 ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat (S k)) ⌝ -∗
         urun N h' mc' (mword_of_int 0x364) (2 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hk Hfk Hfk1 Hs0 Hs64 Hs1.
    iIntros "#Hcode Hstr Hrun Hcont".
    assert (Hbu : bv_unsigned (f k) = 62)
      by (rewrite Hfk; vm_compute; reflexivity).
    (* ---- 0x332  lbu a5,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f k ltac:(lia) with "Hstr")
      as "[Hb Hcl]".
    iApply (wp_uk_lbu N h mc (mword_of_int 0x332)
              (mword_of_int 0 : mword 12) s1_idx a5_idx dq
              (s0 + Z.of_nat k) (f k) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat k)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_332 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x332 4). iIntros (h1) "Hrun".
    set (n1 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 ((f k) : mword 8)
                                     : mword 64)]> mc).
    assert (Hn1 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    n1 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; exact (upd_ne mc (Regidx a5_idx) (Regidx t) _ Ht)).
    assert (Ha5_1 : n1 !!! Regidx a5_idx = mword_of_int 62).
    { rewrite (upd_eq mc (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 ((f k) : mword 8)
                                   : mword 64))).
      rewrite (zext8_moi (f k)) Hbu. reflexivity. }
    assert (Hs1_1 : n1 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1).
    (* ---- 0x336  sext.w s5,a5 ---- *)
    iApply (wp_uk_addiw N h1 n1 (mword_of_int 0x336)
              (mword_of_int 0 : mword 12) a5_idx s5_idx
              (mword_of_int 62) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_1; symmetry;
                    exact (ushp_sextw_byte 62 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shp_336 with "Hcode"). }
    rewrite (ushp_pc_step 0x336 4). iIntros (h2) "Hrun".
    set (n2 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 62 : mword 64)]> n1).
    assert (Hn2 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    n2 !!! Regidx t = n1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n1 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Ha5_2 : n2 !!! Regidx a5_idx = mword_of_int 62)
      by (rewrite (Hn2 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_1).
    assert (Hs1_2 : n2 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn2 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_1).
    (* ---- 0x33a  li a4,60 ---- *)
    iApply (wp_uk_li N h2 n2 (mword_of_int 0x33a)
              (mword_of_int 60 : mword 12) a4_idx (mword_of_int 60) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_33a with "Hcode"). }
    rewrite (ushp_pc_step 0x33a 4). iIntros (h3) "Hrun".
    set (n3 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 60 : mword 64)]> n2).
    assert (Hn3 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n3 !!! Regidx t = n2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n2 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_3 : n3 !!! Regidx a4_idx = mword_of_int 60)
      by exact (upd_eq n2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 60 : mword 64))).
    assert (Ha5_3 : n3 !!! Regidx a5_idx = mword_of_int 62)
      by (rewrite (Hn3 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_2).
    assert (Hs1_3 : n3 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn3 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_2).
    (* ---- 0x33e  bltu a4,a5,0x3a6 -- TAKEN: 60 < 62 ---- *)
    iApply (wp_uk_btype N h3 n3 (mword_of_int 0x33e)
              (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU true
              (mword_of_int 0x3a6) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_3 Ha5_3;
                    rewrite (moi_lt_u 60 62 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_33e with "Hcode"). }
    iIntros (h4) "Hrun".
    (* ---- 0x3a6  li a4,62 ---- *)
    iApply (wp_uk_li N h4 n3 (mword_of_int 0x3a6)
              (mword_of_int 62 : mword 12) a4_idx (mword_of_int 62) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3a6 with "Hcode"). }
    rewrite (ushp_pc_step 0x3a6 4). iIntros (h5) "Hrun".
    set (n4 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 62 : mword 64)]> n3).
    assert (Hn4 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n4 !!! Regidx t = n3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n3 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_4 : n4 !!! Regidx a4_idx = mword_of_int 62)
      by exact (upd_eq n3 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 62 : mword 64))).
    assert (Ha5_4 : n4 !!! Regidx a5_idx = mword_of_int 62)
      by (rewrite (Hn4 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_3).
    assert (Hs1_4 : n4 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn4 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_3).
    (* ---- 0x3aa  bne a5,a4,0x3c0 -- NOT taken: the byte IS '>' ---- *)
    iApply (wp_uk_btype N h5 n4 (mword_of_int 0x3aa)
              (mword_of_int 22 : mword 13) a4_idx a5_idx BNE false
              (mword_of_int 0x3c0) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_4 Ha5_4;
                    rewrite (ushp_moi_neq 62 62 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_3aa with "Hcode"). }
    rewrite (ushp_pc_step 0x3aa 4). iIntros (h6) "Hrun".
    (* ---- 0x3ae  lbu a4,1(s1) -- THE '>>' LOOKAHEAD ---- *)
    iDestruct (ustr_byte γd dq s0 len f (S k) ltac:(lia) with "Hstr")
      as "[Hb1 Hcl1]".
    iApply (wp_uk_lbu N h6 n4 (mword_of_int 0x3ae)
              (mword_of_int 1 : mword 12) s1_idx a4_idx dq
              (s0 + Z.of_nat (S k)) (f (S k)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1_4 (uint_moi (s0 + Z.of_nat k)
                                    ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb1 Hrun").
    { iApply (uis_shp_3ae with "Hcode"). }
    iIntros "Hb1". iDestruct ("Hcl1" with "Hb1") as "Hstr".
    rewrite (ushp_pc_step 0x3ae 4). iIntros (h7) "Hrun".
    set (n5 := <[Regidx a4_idx
                 := regval_into_reg (zero_extend' 64 ((f (S k)) : mword 8)
                                     : mword 64)]> n4).
    assert (Hn5 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n5 !!! Regidx t = n4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n4 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_5 : n5 !!! Regidx a4_idx
                    = mword_of_int (bv_unsigned (f (S k)))).
    { rewrite (upd_eq n4 (Regidx a4_idx)
                 (regval_into_reg (zero_extend' 64 ((f (S k)) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f (S k))). }
    assert (Hs1_5 : n5 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn5 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_4).
    (* ---- 0x3b2  li a5,62 ---- *)
    iApply (wp_uk_li N h7 n5 (mword_of_int 0x3b2)
              (mword_of_int 62 : mword 12) a5_idx (mword_of_int 62) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3b2 with "Hcode"). }
    rewrite (ushp_pc_step 0x3b2 4). iIntros (h8) "Hrun".
    set (n6 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 62 : mword 64)]> n5).
    assert (Hn6 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    n6 !!! Regidx t = n5 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n5 (Regidx a5_idx) (Regidx t) _ Ht)).
    assert (Ha5_6 : n6 !!! Regidx a5_idx = mword_of_int 62)
      by exact (upd_eq n5 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 62 : mword 64))).
    assert (Ha4_6 : n6 !!! Regidx a4_idx
                    = mword_of_int (bv_unsigned (f (S k))))
      by (rewrite (Hn6 a4_idx ltac:(vm_compute; discriminate)); exact Ha4_5).
    assert (Hs1_6 : n6 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn6 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_5).
    (* ---- 0x3b6  beq a4,a5,0x406 -- NOT taken: this is not '>>' ---- *)
    assert (Hne1 : bv_unsigned (f (S k)) <> 62).
    { intro He. apply Hfk1. apply bv_eq. rewrite He.
      vm_compute. reflexivity. }
    pose proof (ushp_byte_rng (f (S k))) as Hrng1.
    iApply (wp_uk_btype N h8 n6 (mword_of_int 0x3b6)
              (mword_of_int 80 : mword 13) a5_idx a4_idx BEQ false
              (mword_of_int 0x406) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_6 Ha5_6;
                    rewrite (moi_eq_vec (bv_unsigned (f (S k))) 62
                               ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    symmetry; apply Z.eqb_neq; exact Hne1)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_3b6 with "Hcode"). }
    rewrite (ushp_pc_step 0x3b6 4). iIntros (h9) "Hrun".
    (* ---- 0x3ba  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi N h9 n6 (mword_of_int 0x3ba)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S k))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_6 E1 moi_add;
                    replace (s0 + Z.of_nat (S k)) with (s0 + Z.of_nat k + 1)
                      by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3ba with "Hcode"). }
    rewrite (ushp_pc_step 0x3ba 2). iIntros (hA) "Hrun".
    set (n7 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat (S k))
                                     : mword 64)]> n6).
    assert (Hn7 : forall t : mword 5, Regidx t <> Regidx s1_idx ->
                    n7 !!! Regidx t = n6 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n6 (Regidx s1_idx) (Regidx t) _ Ht)).
    assert (Hs1_7 : n7 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat (S k)))
      by exact (upd_eq n6 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (s0 + Z.of_nat (S k))
                                    : mword 64))).
    assert (Ha5_7 : n7 !!! Regidx a5_idx = mword_of_int 62)
      by (rewrite (Hn7 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_6).
    (* ---- 0x3bc  c.mv s5,a5 -- ret = '>' ---- *)
    iApply (wp_uk_cmv N hA n7 (mword_of_int 0x3bc) s5_idx a5_idx
              (mword_of_int 62) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_7; symmetry; exact (ushp_mv_val 62))
              with "[] Hrun").
    { iApply (uis_shp_3bc with "Hcode"). }
    rewrite (ushp_pc_step 0x3bc 2). iIntros (hB) "Hrun".
    set (n8 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 62 : mword 64)]> n7).
    assert (Hn8 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    n8 !!! Regidx t = n7 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n7 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Hs5_8 : n8 !!! Regidx s5_idx = mword_of_int 62)
      by exact (upd_eq n7 (Regidx s5_idx)
                  (regval_into_reg (mword_of_int 62 : mword 64))).
    assert (Hs1_8 : n8 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat (S k)))
      by (rewrite (Hn8 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_7).
    (* ---- 0x3be  c.j 0x364 -- into gettoken's shared tail ---- *)
    iApply (wp_uk_cj N hB n8 (mword_of_int 0x3be)
              (mword_of_int 2003 : mword 11) (mword_of_int 0x364) (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3be with "Hcode"). }
    iIntros (hC) "Hrun".
    iApply ("Hcont" with "Hstr [] [] [] Hrun").
    - iPureIntro. intros t Ht4 Ht5 Hts5 Hts1.
      rewrite (Hn8 t Hts5) (Hn7 t Hts1) (Hn6 t Ht5) (Hn5 t Ht4)
              (Hn4 t Ht4) (Hn3 t Ht4) (Hn2 t Hts5).
      exact (Hn1 t Ht5).
    - iPureIntro. exact Hs5_8.
    - iPureIntro. exact Hs1_8.
  Qed.

  (* the NUL / default dichotomy at a cursor whose byte is not a symbol:
     [UkShParseTok.wp_kshp_gtk_disp] at the premise it actually uses *)
  Lemma wp_kshp_gtk_disp_ns (dq : dfrac) (s0 : Z) (len k : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (k <= len)%nat -> ((k < len)%nat -> ushp_is_sym (f k) = false) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    urun N h mc (mword_of_int 0x332) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, Regidx t <> Regidx a4_idx ->
             Regidx t <> Regidx a5_idx -> Regidx t <> Regidx s5_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ (len <= k)%nat ->
             mc' !!! Regidx s5_idx = mword_of_int 0 ⌝ -∗
         urun N h' mc'
           (mword_of_int (if bool_decide (k < len)%nat then 0x3c8 else 0x364))
           (2 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hkle Hnsk Hs0 Hs64 Hs1.
    iIntros "#Hcode Hstr Hrun Hcont".
    iDestruct (ustr_nonul with "Hstr") as %Hnonul.
    iAssert (∃ b : bv 8,
               ⌜ (k < len)%nat -> b = f k ⌝ ∗ ⌜ k = len -> b = ubyte0 ⌝ ∗
               ubyteq γd dq (s0 + Z.of_nat k) b ∗
               (ubyteq γd dq (s0 + Z.of_nat k) b -∗ ustr γd dq s0 len f))%I
      with "[Hstr]" as (b Hbk Hb0) "[Hb Hcl]".
    { destruct (Nat.eq_dec k len) as [ He | Hne ].
      - iDestruct (ustr_nul with "Hstr") as "[Hb Hcl]".
        rewrite He. iExists ubyte0.
        iSplitR; [ iPureIntro; intro; lia | ].
        iSplitR; [ iPureIntro; intro; reflexivity | ].
        iFrame "Hb Hcl".
      - iDestruct (ustr_byte γd dq s0 len f k ltac:(lia) with "Hstr")
          as "[Hb Hcl]".
        iExists (f k).
        iSplitR; [ iPureIntro; intro; reflexivity | ].
        iSplitR; [ iPureIntro; intro; lia | ].
        iFrame "Hb Hcl". }
    pose proof (ushp_byte_rng b) as Hvb.
    assert (Hz : k = len -> bv_unsigned b = 0)
      by (intro He; rewrite (Hb0 He); vm_compute; reflexivity).
    assert (Hnz : (k < len)%nat -> bv_unsigned b <> 0).
    { intros Hk Hzz. apply (Hnonul k Hk). rewrite <- (Hbk Hk).
      apply bv_eq. rewrite Hzz. vm_compute; reflexivity. }
    assert (Hns : (k < len)%nat -> ushp_is_sym b = false)
      by (intros Hk; rewrite (Hbk Hk); exact (Hnsk Hk)).
    (* ---- 0x332  lbu a5,0(s1) ---- *)
    iApply (wp_uk_lbu N h mc (mword_of_int 0x332)
              (mword_of_int 0 : mword 12) s1_idx a5_idx dq
              (s0 + Z.of_nat k) b (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat k)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_332 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x332 4). iIntros (h1) "Hrun".
    set (n1 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 (b : mword 8)
                                     : mword 64)]> mc).
    assert (Hn1 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    n1 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; exact (upd_ne mc (Regidx a5_idx) (Regidx t) _ Ht)).
    assert (Ha5_1 : n1 !!! Regidx a5_idx = mword_of_int (bv_unsigned b)).
    { rewrite (upd_eq mc (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 (b : mword 8) : mword 64))).
      exact (zext8_moi b). }
    (* ---- 0x336  sext.w s5,a5 -- [ret = *s] ---- *)
    iApply (wp_uk_addiw N h1 n1 (mword_of_int 0x336)
              (mword_of_int 0 : mword 12) a5_idx s5_idx
              (mword_of_int (bv_unsigned b)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_1; symmetry;
                    exact (ushp_sextw_byte (bv_unsigned b) Hvb))
              with "[] Hrun").
    { iApply (uis_shp_336 with "Hcode"). }
    rewrite (ushp_pc_step 0x336 4). iIntros (h2) "Hrun".
    set (n2 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int (bv_unsigned b)
                                     : mword 64)]> n1).
    assert (Hn2 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    n2 !!! Regidx t = n1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n1 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Hs5_2 : n2 !!! Regidx s5_idx = mword_of_int (bv_unsigned b))
      by exact (upd_eq n1 (Regidx s5_idx)
                  (regval_into_reg (mword_of_int (bv_unsigned b) : mword 64))).
    assert (Ha5_2 : n2 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hn2 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_1).
    (* ---- 0x33a  li a4,60 ---- *)
    iApply (wp_uk_li N h2 n2 (mword_of_int 0x33a)
              (mword_of_int 60 : mword 12) a4_idx (mword_of_int 60) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_33a with "Hcode"). }
    rewrite (ushp_pc_step 0x33a 4). iIntros (h3) "Hrun".
    set (n3 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 60 : mword 64)]> n2).
    assert (Hn3 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n3 !!! Regidx t = n2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n2 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_3 : n3 !!! Regidx a4_idx = mword_of_int 60)
      by exact (upd_eq n2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 60 : mword 64))).
    assert (Ha5_3 : n3 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hn3 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_2).
    assert (Hs5_3 : n3 !!! Regidx s5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hn3 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_2).
    (* ---- 0x33e  bltu a4,a5,0x3a6 -- '<' and above go out of line ---- *)
    destruct (Z_lt_ge_dec 60 (bv_unsigned b)) as [ Hhi | Hlo ].
    { (* the byte is ABOVE '<': it is '>', '|', or an ordinary character *)
      assert (Hklt : (k < len)%nat).
      { destruct (Nat.eq_dec k len) as [ He | Hne2 ];
          [ exfalso; pose proof (Hz He); lia | lia ]. }
      destruct (ushp_nsym_bv b (Hns Hklt))
        as (N60 & N124 & N62 & N38 & N59 & N40 & N41).
      assert (Htk : true = uv_btaken BLTU (n3 !!! Regidx a4_idx)
                             (n3 !!! Regidx a5_idx)).
      { cbn [uv_btaken]. rewrite Ha4_3 Ha5_3.
        rewrite (moi_lt_u 60 (bv_unsigned b) ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.ltb_lt. lia. }
      iApply (wp_uk_btype N h3 n3 (mword_of_int 0x33e)
                (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU true
                (mword_of_int 0x3a6) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_33e with "Hcode"). }
      iIntros (h4) "Hrun".
      (* ---- 0x3a6  li a4,62 ---- *)
      iApply (wp_uk_li N h4 n3 (mword_of_int 0x3a6)
                (mword_of_int 62 : mword 12) a4_idx (mword_of_int 62) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_3a6 with "Hcode"). }
      rewrite (ushp_pc_step 0x3a6 4). iIntros (h5) "Hrun".
      set (n4 := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 62 : mword 64)]> n3).
      assert (Hn4 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                      n4 !!! Regidx t = n3 !!! Regidx t)
        by (intros t Ht; exact (upd_ne n3 (Regidx a4_idx) (Regidx t) _ Ht)).
      assert (Ha4_4 : n4 !!! Regidx a4_idx = mword_of_int 62)
        by exact (upd_eq n3 (Regidx a4_idx)
                    (regval_into_reg (mword_of_int 62 : mword 64))).
      assert (Ha5_4 : n4 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
        by (rewrite (Hn4 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_3).
      (* ---- 0x3aa  bne a5,a4,0x3c0 -- NOT '>' ---- *)
      assert (Htk2 : true = uv_btaken BNE (n4 !!! Regidx a5_idx)
                              (n4 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha4_4 Ha5_4.
        rewrite (ushp_moi_neq (bv_unsigned b) 62 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        assert (Hq : (bv_unsigned b =? 62) = false)
          by (apply Z.eqb_neq; exact N62).
        rewrite Hq. reflexivity. }
      iApply (wp_uk_btype N h5 n4 (mword_of_int 0x3aa)
                (mword_of_int 22 : mword 13) a4_idx a5_idx BNE true
                (mword_of_int 0x3c0) (2 + nn)
                Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_3aa with "Hcode"). }
      iIntros (h6) "Hrun".
      (* ---- 0x3c0  li a4,124 ---- *)
      iApply (wp_uk_li N h6 n4 (mword_of_int 0x3c0)
                (mword_of_int 124 : mword 12) a4_idx (mword_of_int 124)
                (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_3c0 with "Hcode"). }
      rewrite (ushp_pc_step 0x3c0 4). iIntros (h7) "Hrun".
      set (n5 := <[Regidx a4_idx
                   := regval_into_reg (mword_of_int 124 : mword 64)]> n4).
      assert (Hn5 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                      n5 !!! Regidx t = n4 !!! Regidx t)
        by (intros t Ht; exact (upd_ne n4 (Regidx a4_idx) (Regidx t) _ Ht)).
      assert (Ha4_5 : n5 !!! Regidx a4_idx = mword_of_int 124)
        by exact (upd_eq n4 (Regidx a4_idx)
                    (regval_into_reg (mword_of_int 124 : mword 64))).
      assert (Ha5_5 : n5 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
        by (rewrite (Hn5 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_4).
      (* ---- 0x3c4  beq a5,a4,0x362 -- NOT '|', so the DEFAULT arm ---- *)
      assert (Htk3 : false = uv_btaken BEQ (n5 !!! Regidx a5_idx)
                               (n5 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha4_5 Ha5_5.
        rewrite (moi_eq_vec (bv_unsigned b) 124 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. exact N124. }
      iApply (wp_uk_btype N h7 n5 (mword_of_int 0x3c4)
                (mword_of_int 8094 : mword 13) a4_idx a5_idx BEQ false
                (mword_of_int 0x362) (2 + nn)
                Htk3
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_3c4 with "Hcode"). }
      rewrite (ushp_pc_step' 0x3c4 4 0x3c8 ltac:(reflexivity)).
      iIntros (h8) "Hrun".
      rewrite (bool_decide_eq_true_2 (k < len)%nat Hklt).
      iApply ("Hcont" with "Hstr [] [] Hrun").
      - iPureIntro. intros t Ht4 Ht5 Hts5.
        rewrite (Hn5 t Ht4) (Hn4 t Ht4) (Hn3 t Ht4) (Hn2 t Hts5).
        exact (Hn1 t Ht5).
      - iPureIntro. intro Hge. lia. }
    (* the byte is AT MOST '<' *)
    assert (Hle58 : bv_unsigned b <= 58).
    { destruct (Nat.eq_dec k len) as [ He | Hne2 ].
      - pose proof (Hz He). lia.
      - destruct (ushp_nsym_bv b (Hns ltac:(lia)))
          as (N60 & N124 & N62 & N38 & N59 & N40 & N41). lia. }
    assert (Htk : false = uv_btaken BLTU (n3 !!! Regidx a4_idx)
                            (n3 !!! Regidx a5_idx)).
    { cbn [uv_btaken]. rewrite Ha4_3 Ha5_3.
      rewrite (moi_lt_u 60 (bv_unsigned b) ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_ge. lia. }
    iApply (wp_uk_btype N h3 n3 (mword_of_int 0x33e)
              (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU false
              (mword_of_int 0x3a6) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_33e with "Hcode"). }
    rewrite (ushp_pc_step 0x33e 4). iIntros (h4) "Hrun".
    (* ---- 0x342  li a4,58 ---- *)
    iApply (wp_uk_li N h4 n3 (mword_of_int 0x342)
              (mword_of_int 58 : mword 12) a4_idx (mword_of_int 58) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_342 with "Hcode"). }
    rewrite (ushp_pc_step 0x342 4). iIntros (h5) "Hrun".
    set (p4 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 58 : mword 64)]> n3).
    assert (Hp4 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    p4 !!! Regidx t = n3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n3 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Hb4_4 : p4 !!! Regidx a4_idx = mword_of_int 58)
      by exact (upd_eq n3 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 58 : mword 64))).
    assert (Hb5_4 : p4 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hp4 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_3).
    assert (Hb55_4 : p4 !!! Regidx s5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hp4 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_3).
    (* ---- 0x346  bltu a4,a5,0x362 -- ';' and '<' are refuted ---- *)
    assert (Htk2 : false = uv_btaken BLTU (p4 !!! Regidx a4_idx)
                             (p4 !!! Regidx a5_idx)).
    { cbn [uv_btaken]. rewrite Hb4_4 Hb5_4.
      rewrite (moi_lt_u 58 (bv_unsigned b) ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_ge. lia. }
    iApply (wp_uk_btype N h5 p4 (mword_of_int 0x346)
              (mword_of_int 28 : mword 13) a5_idx a4_idx BLTU false
              (mword_of_int 0x362) (2 + nn)
              Htk2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_346 with "Hcode"). }
    rewrite (ushp_pc_step 0x346 4). iIntros (h6) "Hrun".
    (* ---- 0x34a  c.beqz a5,0x364 -- THE NUL ARM ---- *)
    destruct (Z.eq_dec (bv_unsigned b) 0) as [ Hbz | Hbnz ].
    { assert (Hkeq : k = len).
      { destruct (Nat.eq_dec k len) as [ He | Hne2 ];
          [ exact He | exfalso; exact (Hnz ltac:(lia) Hbz) ]. }
      assert (Htk3 : true = eq_vec (p4 !!! Regidx a5_idx) zero_reg).
      { rewrite Hb5_4 Hbz.
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_cbeqz N h6 p4 (mword_of_int 0x34a)
                (mword_of_int 13 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx true (mword_of_int 0x364) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk3
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_34a with "Hcode"). }
      iIntros (h7) "Hrun".
      rewrite (bool_decide_eq_false_2 (k < len)%nat ltac:(lia)).
      iApply ("Hcont" with "Hstr [] [] Hrun").
      - iPureIntro. intros t Ht4 Ht5 Hts5.
        rewrite (Hp4 t Ht4) (Hn3 t Ht4) (Hn2 t Hts5). exact (Hn1 t Ht5).
      - iPureIntro. intros _. rewrite Hb55_4 Hbz. reflexivity. }
    (* an ORDINARY character: the default arm, through the range test *)
    assert (Hklt : (k < len)%nat).
    { destruct (Nat.eq_dec k len) as [ He | Hne2 ];
        [ exfalso; exact (Hbnz (Hz He)) | lia ]. }
    destruct (ushp_nsym_bv b (Hns Hklt))
      as (N60 & N124 & N62 & N38 & N59 & N40 & N41).
    assert (Htk3 : false = eq_vec (p4 !!! Regidx a5_idx) zero_reg).
    { rewrite Hb5_4.
      rewrite (moi_eq_zero (bv_unsigned b) ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. exact Hbnz. }
    iApply (wp_uk_cbeqz N h6 p4 (mword_of_int 0x34a)
              (mword_of_int 13 : mword 8) (mword_of_int 7 : mword 3)
              a5_idx false (mword_of_int 0x364) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_34a with "Hcode"). }
    rewrite (ushp_pc_step 0x34a 2). iIntros (h7) "Hrun".
    (* ---- 0x34c  li a4,38 ---- *)
    iApply (wp_uk_li N h7 p4 (mword_of_int 0x34c)
              (mword_of_int 38 : mword 12) a4_idx (mword_of_int 38) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_34c with "Hcode"). }
    rewrite (ushp_pc_step 0x34c 4). iIntros (h8) "Hrun".
    set (p5 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 38 : mword 64)]> p4).
    assert (Hp5 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    p5 !!! Regidx t = p4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne p4 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Hb4_5 : p5 !!! Regidx a4_idx = mword_of_int 38)
      by exact (upd_eq p4 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 38 : mword 64))).
    assert (Hb5_5 : p5 !!! Regidx a5_idx = mword_of_int (bv_unsigned b))
      by (rewrite (Hp5 a5_idx ltac:(vm_compute; discriminate)); exact Hb5_4).
    (* ---- 0x350  beq a5,a4,0x362 -- '&' is refuted ---- *)
    assert (Htk4 : false = uv_btaken BEQ (p5 !!! Regidx a5_idx)
                             (p5 !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Hb4_5 Hb5_5.
      rewrite (moi_eq_vec (bv_unsigned b) 38 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. exact N38. }
    iApply (wp_uk_btype N h8 p5 (mword_of_int 0x350)
              (mword_of_int 18 : mword 13) a4_idx a5_idx BEQ false
              (mword_of_int 0x362) (2 + nn)
              Htk4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_350 with "Hcode"). }
    rewrite (ushp_pc_step 0x350 4). iIntros (h9) "Hrun".
    (* ---- 0x354  addiw a5,a5,-40 ---- *)
    iApply (wp_uk_addiw N h9 p5 (mword_of_int 0x354)
              (mword_of_int 4056 : mword 12) a5_idx a5_idx
              (sign_extend' 64
                 (subrange_vec_dec
                    (add_vec (mword_of_int (bv_unsigned b) : mword 64)
                       (sign_extend' 64 (mword_of_int 4056 : mword 12)))
                    31 0 : mword 32))
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hb5_5; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_354 with "Hcode"). }
    rewrite (ushp_pc_step 0x354 4). iIntros (h10) "Hrun".
    set (p6 := <[Regidx a5_idx
                 := regval_into_reg
                      (sign_extend' 64
                         (subrange_vec_dec
                            (add_vec (mword_of_int (bv_unsigned b) : mword 64)
                               (sign_extend' 64
                                  (mword_of_int 4056 : mword 12)))
                            31 0 : mword 32))]> p5).
    assert (Hp6 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    p6 !!! Regidx t = p5 !!! Regidx t)
      by (intros t Ht; exact (upd_ne p5 (Regidx a5_idx) (Regidx t) _ Ht)).
    (* ---- 0x358  zext.b a5,a5 -- the wrap is undone here ---- *)
    iApply (wp_uk_andi N h10 p6 (mword_of_int 0x358)
              (mword_of_int 255 : mword 12) a5_idx a5_idx
              (mword_of_int ((bv_unsigned b - 40) mod 256)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq p5 (Regidx a5_idx) _); symmetry;
                    exact (ushp_addiw_andi (bv_unsigned b) Hvb))
              with "[] Hrun").
    { iApply (uis_shp_358 with "Hcode"). }
    rewrite (ushp_pc_step 0x358 4). iIntros (h11) "Hrun".
    set (p7 := <[Regidx a5_idx
                 := regval_into_reg
                      (mword_of_int ((bv_unsigned b - 40) mod 256)
                       : mword 64)]> p6).
    assert (Hp7 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    p7 !!! Regidx t = p6 !!! Regidx t)
      by (intros t Ht; exact (upd_ne p6 (Regidx a5_idx) (Regidx t) _ Ht)).
    assert (Hb5_7 : p7 !!! Regidx a5_idx
                    = mword_of_int ((bv_unsigned b - 40) mod 256))
      by exact (upd_eq p6 (Regidx a5_idx)
                  (regval_into_reg
                     (mword_of_int ((bv_unsigned b - 40) mod 256)
                      : mword 64))).
    (* ---- 0x35c  c.li a4,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli N h11 p7 (mword_of_int 0x35c)
              (mword_of_int 1 : mword 6) a4_idx (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_35c with "Hcode"). }
    rewrite (ushp_pc_step 0x35c 2). iIntros (h12) "Hrun".
    set (p8 := <[Regidx a4_idx
                 := regval_into_reg (sign_extend' 64
                                       (mword_of_int 1 : mword 6)
                                     : mword 64)]> p7).
    assert (Hp8 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    p8 !!! Regidx t = p7 !!! Regidx t)
      by (intros t Ht; exact (upd_ne p7 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Hb4_8 : p8 !!! Regidx a4_idx = mword_of_int 1).
    { rewrite (upd_eq p7 (Regidx a4_idx)
                 (regval_into_reg (sign_extend' 64 (mword_of_int 1 : mword 6)
                                   : mword 64))).
      exact E1. }
    assert (Hb5_8 : p8 !!! Regidx a5_idx
                    = mword_of_int ((bv_unsigned b - 40) mod 256))
      by (rewrite (Hp8 a5_idx ltac:(vm_compute; discriminate)); exact Hb5_7).
    (* ---- 0x35e  bltu a4,a5,0x3c8 -- '(' and ')' are the only 0 and 1 --- *)
    assert (Hgt : 1 < (bv_unsigned b - 40) mod 256).
    { destruct (Z_lt_ge_dec (bv_unsigned b) 40) as [ Hlt40 | Hge40 ].
      - assert (E : (bv_unsigned b - 40) mod 256 = bv_unsigned b + 216).
        { replace (bv_unsigned b - 40)
            with ((bv_unsigned b + 216) + (-1) * 256) by lia.
          rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
        rewrite E. lia.
      - rewrite (Z.mod_small (bv_unsigned b - 40) 256 ltac:(lia)). lia. }
    assert (Hmr : 0 <= (bv_unsigned b - 40) mod 256 < 256)
      by (apply Z.mod_pos_bound; lia).
    assert (Htk5 : true = uv_btaken BLTU (p8 !!! Regidx a4_idx)
                            (p8 !!! Regidx a5_idx)).
    { cbn [uv_btaken]. rewrite Hb4_8 Hb5_8.
      rewrite (moi_lt_u 1 ((bv_unsigned b - 40) mod 256)
                 ltac:(unfold Z64; lia) ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_lt. lia. }
    iApply (wp_uk_btype N h12 p8 (mword_of_int 0x35e)
              (mword_of_int 106 : mword 13) a5_idx a4_idx BLTU true
              (mword_of_int 0x3c8) (2 + nn)
              Htk5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_35e with "Hcode"). }
    iIntros (h13) "Hrun".
    rewrite (bool_decide_eq_true_2 (k < len)%nat Hklt).
    iApply ("Hcont" with "Hstr [] [] Hrun").
    - iPureIntro. intros t Ht4 Ht5 Hts5.
      rewrite (Hp8 t Ht4) (Hp7 t Ht5) (Hp6 t Ht5) (Hp5 t Ht4) (Hp4 t Ht4)
              (Hn3 t Ht4) (Hn2 t Hts5). exact (Hn1 t Ht5).
    - iPureIntro. intro Hge. lia.
  Qed.

  (* the '|' arm: TEN instructions, no lookahead, into 0x364 *)
  Lemma wp_kshp_gtk_disp_bar (dq : dfrac) (s0 : Z) (len k : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (k < len)%nat ->
    f k = rb_bar ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    urun N h mc (mword_of_int 0x332) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, Regidx t <> Regidx a4_idx ->
             Regidx t <> Regidx a5_idx -> Regidx t <> Regidx s5_idx ->
             Regidx t <> Regidx s1_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s5_idx = mword_of_int 124 ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat (S k)) ⌝ -∗
         urun N h' mc' (mword_of_int 0x364) (2 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hk Hfk Hs0 Hs64 Hs1.
    iIntros "#Hcode Hstr Hrun Hcont".
    assert (Hbu : bv_unsigned (f k) = 124)
      by (rewrite Hfk; vm_compute; reflexivity).
    (* ---- 0x332  lbu a5,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f k ltac:(lia) with "Hstr")
      as "[Hb Hcl]".
    iApply (wp_uk_lbu N h mc (mword_of_int 0x332)
              (mword_of_int 0 : mword 12) s1_idx a5_idx dq
              (s0 + Z.of_nat k) (f k) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat k)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_332 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x332 4). iIntros (h1) "Hrun".
    set (n1 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 ((f k) : mword 8)
                                     : mword 64)]> mc).
    assert (Hn1 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    n1 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; exact (upd_ne mc (Regidx a5_idx) (Regidx t) _ Ht)).
    assert (Ha5_1 : n1 !!! Regidx a5_idx = mword_of_int 124).
    { rewrite (upd_eq mc (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 ((f k) : mword 8)
                                   : mword 64))).
      rewrite (zext8_moi (f k)) Hbu. reflexivity. }
    assert (Hs1_1 : n1 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1).
    (* ---- 0x336  sext.w s5,a5  --  ret = *s ---- *)
    iApply (wp_uk_addiw N h1 n1 (mword_of_int 0x336)
              (mword_of_int 0 : mword 12) a5_idx s5_idx
              (mword_of_int 124) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_1; symmetry;
                    exact (ushp_sextw_byte 124 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shp_336 with "Hcode"). }
    rewrite (ushp_pc_step 0x336 4). iIntros (h2) "Hrun".
    set (n2 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 124 : mword 64)]> n1).
    assert (Hn2 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    n2 !!! Regidx t = n1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n1 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Ha5_2 : n2 !!! Regidx a5_idx = mword_of_int 124)
      by (rewrite (Hn2 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_1).
    assert (Hs1_2 : n2 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn2 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_1).
    assert (Hs5_2 : n2 !!! Regidx s5_idx = mword_of_int 124)
      by exact (upd_eq n1 (Regidx s5_idx)
                  (regval_into_reg (mword_of_int 124 : mword 64))).
    (* ---- 0x33a  li a4,60 ---- *)
    iApply (wp_uk_li N h2 n2 (mword_of_int 0x33a)
              (mword_of_int 60 : mword 12) a4_idx (mword_of_int 60) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_33a with "Hcode"). }
    rewrite (ushp_pc_step 0x33a 4). iIntros (h3) "Hrun".
    set (n3 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 60 : mword 64)]> n2).
    assert (Hn3 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n3 !!! Regidx t = n2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n2 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_3 : n3 !!! Regidx a4_idx = mword_of_int 60)
      by exact (upd_eq n2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 60 : mword 64))).
    assert (Ha5_3 : n3 !!! Regidx a5_idx = mword_of_int 124)
      by (rewrite (Hn3 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_2).
    assert (Hs1_3 : n3 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn3 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_2).
    assert (Hs5_3 : n3 !!! Regidx s5_idx = mword_of_int 124)
      by (rewrite (Hn3 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_2).
    (* ---- 0x33e  bltu a4,a5,0x3a6 -- TAKEN: 60 < 124 ---- *)
    iApply (wp_uk_btype N h3 n3 (mword_of_int 0x33e)
              (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU true
              (mword_of_int 0x3a6) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_3 Ha5_3;
                    rewrite (moi_lt_u 60 124 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_33e with "Hcode"). }
    iIntros (h4) "Hrun".
    (* ---- 0x3a6  li a4,62 ---- *)
    iApply (wp_uk_li N h4 n3 (mword_of_int 0x3a6)
              (mword_of_int 62 : mword 12) a4_idx (mword_of_int 62) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3a6 with "Hcode"). }
    rewrite (ushp_pc_step 0x3a6 4). iIntros (h5) "Hrun".
    set (n4 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 62 : mword 64)]> n3).
    assert (Hn4 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n4 !!! Regidx t = n3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n3 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_4 : n4 !!! Regidx a4_idx = mword_of_int 62)
      by exact (upd_eq n3 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 62 : mword 64))).
    assert (Ha5_4 : n4 !!! Regidx a5_idx = mword_of_int 124)
      by (rewrite (Hn4 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_3).
    assert (Hs1_4 : n4 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn4 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_3).
    assert (Hs5_4 : n4 !!! Regidx s5_idx = mword_of_int 124)
      by (rewrite (Hn4 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_3).
    (* ---- 0x3aa  bne a5,a4,0x3c0 -- TAKEN: the byte is not '>' ---- *)
    iApply (wp_uk_btype N h5 n4 (mword_of_int 0x3aa)
              (mword_of_int 22 : mword 13) a4_idx a5_idx BNE true
              (mword_of_int 0x3c0) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_4 Ha5_4;
                    rewrite (ushp_moi_neq 124 62 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3aa with "Hcode"). }
    iIntros (h6) "Hrun".
    (* ---- 0x3c0  li a4,124 ---- *)
    iApply (wp_uk_li N h6 n4 (mword_of_int 0x3c0)
              (mword_of_int 124 : mword 12) a4_idx (mword_of_int 124)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3c0 with "Hcode"). }
    rewrite (ushp_pc_step 0x3c0 4). iIntros (h7) "Hrun".
    set (n5 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 124 : mword 64)]> n4).
    assert (Hn5 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n5 !!! Regidx t = n4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n4 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_5 : n5 !!! Regidx a4_idx = mword_of_int 124)
      by exact (upd_eq n4 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 124 : mword 64))).
    assert (Ha5_5 : n5 !!! Regidx a5_idx = mword_of_int 124)
      by (rewrite (Hn5 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_4).
    assert (Hs1_5 : n5 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn5 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_4).
    assert (Hs5_5 : n5 !!! Regidx s5_idx = mword_of_int 124)
      by (rewrite (Hn5 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_4).
    (* ---- 0x3c4  beq a5,a4,0x362 -- TAKEN: it IS '|' ---- *)
    iApply (wp_uk_btype N h7 n5 (mword_of_int 0x3c4)
              (mword_of_int 8094 : mword 13) a4_idx a5_idx BEQ true
              (mword_of_int 0x362) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_5 Ha5_5;
                    rewrite (moi_eq_vec 124 124 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3c4 with "Hcode"). }
    iIntros (h8) "Hrun".
    (* ---- 0x362  c.addi s1,s1,1  --  s++, and fall into 0x364 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi N h8 n5 (mword_of_int 0x362)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S k))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_5 E1 moi_add;
                    replace (s0 + Z.of_nat (S k)) with (s0 + Z.of_nat k + 1)
                      by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_362 with "Hcode"). }
    rewrite (ushp_pc_step 0x362 2). iIntros (h9) "Hrun".
    set (n6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat (S k))
                                     : mword 64)]> n5).
    assert (Hn6 : forall t : mword 5, Regidx t <> Regidx s1_idx ->
                    n6 !!! Regidx t = n5 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n5 (Regidx s1_idx) (Regidx t) _ Ht)).
    assert (Hs1_6 : n6 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat (S k)))
      by exact (upd_eq n5 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (s0 + Z.of_nat (S k))
                                    : mword 64))).
    assert (Hs5_6 : n6 !!! Regidx s5_idx = mword_of_int 124)
      by (rewrite (Hn6 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_5).
    iApply ("Hcont" with "Hstr [] [] [] Hrun").
    - iPureIntro. intros t Ht4 Ht5 Hts5 Hts1.
      rewrite (Hn6 t Hts1) (Hn5 t Ht4) (Hn4 t Ht4) (Hn3 t Ht4) (Hn2 t Hts5).
      exact (Hn1 t Ht5).
    - iPureIntro. exact Hs5_6.
    - iPureIntro. exact Hs1_6.
  Qed.

  (* both symbol arms under ONE statement: the byte itself in s5, the
     cursor one past it, 0x364 *)
  Lemma wp_kshp_gtk_disp_sym (dq : dfrac) (s0 : Z) (len k : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (k < len)%nat ->
    (f k = rb_bar
     \/ (f k = rb_gt /\ (S k < len)%nat /\ f (S k) <> rb_gt)) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    urun N h mc (mword_of_int 0x332) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, Regidx t <> Regidx a4_idx ->
             Regidx t <> Regidx a5_idx -> Regidx t <> Regidx s5_idx ->
             Regidx t <> Regidx s1_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s5_idx
             = mword_of_int (bv_unsigned (f k)) ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat (S k)) ⌝ -∗
         urun N h' mc' (mword_of_int 0x364) (2 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hk Hdisj Hs0 Hs64 Hs1.
    iIntros "#Hcode Hstr Hrun Hcont".
    destruct Hdisj as [ Hbar | (Hgt & Hk1 & Hnd) ].
    - assert (Hbu : bv_unsigned (f k) = 124)
        by (rewrite Hbar; vm_compute; reflexivity).
      iApply (wp_kshp_gtk_disp_bar dq s0 len k f nn h mc Hk Hbar Hs0 Hs64 Hs1
                with "Hcode Hstr Hrun").
      iIntros "Hstr" (h' mc') "%Hpres %Hs5 %Hs1' Hrun".
      iApply ("Hcont" with "Hstr [] [] [] Hrun").
      + iPureIntro. exact Hpres.
      + iPureIntro. rewrite Hbu. exact Hs5.
      + iPureIntro. exact Hs1'.
    - assert (Hbu : bv_unsigned (f k) = 62)
        by (rewrite Hgt; vm_compute; reflexivity).
      iApply (wp_kshp_gtk_disp_gt dq s0 len k f nn h mc Hk1 Hgt Hnd
                Hs0 Hs64 Hs1 with "Hcode Hstr Hrun").
      iIntros "Hstr" (h' mc') "%Hpres %Hs5 %Hs1' Hrun".
      iApply ("Hcont" with "Hstr [] [] [] Hrun").
      + iPureIntro. exact Hpres.
      + iPureIntro. rewrite Hbu. exact Hs5.
      + iPureIntro. exact Hs1'.
  Qed.


  (* ===================================================================== *)
  (* (2) gettoken, THE WHOLE FUNCTION, AT THE REFERENCE                    *)
  (* ===================================================================== *)

  Lemma wp_ref_gettoken (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps qp eqp s0 : Z) (len off : nat) (f : nat -> bv 8)
      (w0 wq weq : mword 64) (nn : nat)
      (ret : Z) (q e fin : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx a2_idx = mword_of_int qp ->
    m !!! Regidx a3_idx = mword_of_int eqp ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ref_sym_scope_from len f off ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    ref_gettoken len f off = (ret, q, e, fin) ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ushp_cell qp wq -∗
    ushp_cell eqp weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h m (mword_of_int ShSyms.gettoken) (8 + (2 + nn)) -∗
    (uword γd ps (mword_of_int (s0 + Z.of_nat fin)) -∗
     ushp_cell qp (mword_of_int (s0 + Z.of_nat q)) -∗
     ushp_cell eqp (mword_of_int (s0 + Z.of_nat e)) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int ret ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx))
           (8 + (2 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Ha2 Ha3 Hoffle Hw0 Hsymok Hs0 Hs64 Hps0 Hps8 Hpssz Href.
    iIntros "#Hcode Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
    (* the reference's answer IS the landed one: [ref_nonnul] is read off
       the line resource, and the four components are substituted so the
       rest of this proof is the landed walk, verbatim *)
    iDestruct (ustr_nonul with "Hstr") as %Hnonul.
    rewrite (ref_gettoken_ushs len f off Hsymok Hnonul Hoffle) in Href.
    injection Href as Eret Eq Ee Efin. subst ret q e fin.
    rewrite shpp_gettoken.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 64 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    set (kk := (off + ushp_skipws (len - off) off f)%nat).
    assert (Hkk : (kk <= len)%nat).
    { unfold kk. pose proof (ushp_skipws_le (len - off) off f). lia. }
    (* ---- 0x2ec  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x2ec)
              (mword_of_int 60 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_2ec with "Hcode"). }
    rewrite (ushp_pc_step 0x2ec 2). iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 8))).
    assert (Hspu : uint spn = uint sp0 - 64).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall t : mword 5, Regidx t <> Regidx csp_rs1 ->
                    m1 !!! Regidx t = m !!! Regidx t)
      by (intros t Ht; exact (upd_ne m (Regidx csp_rs1) (Regidx t) _ Ht)).
    set (spl := (mword_of_int (uint sp0 - 64) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 64)
      by (unfold spl; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 0
                 [(ra_idx, mword_of_int 7 : mword 6);
                  (s0_idx, mword_of_int 6 : mword 6);
                  (s1_idx, mword_of_int 5 : mword 6);
                  (s2_idx, mword_of_int 4 : mword 6);
                  (s3_idx, mword_of_int 3 : mword 6);
                  (s4_idx, mword_of_int 2 : mword 6);
                  (s5_idx, mword_of_int 1 : mword 6);
                  (s6_idx, mword_of_int 0 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | 5%nat => m !!! Regidx s4_idx
                   | 6%nat => m !!! Regidx s5_idx
                   | _ => m !!! Regidx s6_idx end).
    (* ---- 0x2ee..0x2fc  the eight spills ---- *)
    iApply (wp_kshp_spill spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6);
               (s6_idx, mword_of_int 0 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x2ee | 1%nat => 0x2f0
                              | 2%nat => 0x2f2 | 3%nat => 0x2f4
                              | 4%nat => 0x2f6 | 5%nat => 0x2f8
                              | 6%nat => 0x2fa | 7%nat => 0x2fc
                              | _ => 0x2fe end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h1 m1 Hsp1
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ exact (ushp_slot_al (uint sp0) _ Hal8)
                       | unfold vals; cbn;
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_2ee with "Hcode") | ].
      iSplit; [ iApply (uis_shp_2f0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_2f2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_2f4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_2f6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_2f8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_2fa with "Hcode") | ].
      iSplit; [ iApply (uis_shp_2fc with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x2fe  c.addi4spn s0,sp,64 ---- *)
    iApply (wp_kshp_fp h2 m1 0x2fe (mword_of_int 16 : mword 8) (2 + nn)
              with "[] Hrun").
    { iApply (uis_shp_2fe with "Hcode"). }
    iIntros (h3 v322) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v322]> m1).
    assert (Hm2 : forall t : mword 5, Regidx t <> Regidx s0_idx ->
                    m2 !!! Regidx t = m1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m1 (Regidx s0_idx) (Regidx t) _ Ht)).
    (* ---- 0x300  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv N h3 m2 (mword_of_int 0x300) s4_idx a0_idx
              (mword_of_int ps) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_300 with "Hcode"). }
    rewrite (ushp_pc_step 0x300 2). iIntros (h4) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall t : mword 5, Regidx t <> Regidx s4_idx ->
                    m3 !!! Regidx t = m2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m2 (Regidx s4_idx) (Regidx t) _ Ht)).
    (* ---- 0x302  c.mv s2,a1 ---- *)
    iApply (wp_uk_cmv N h4 m3 (mword_of_int 0x302) s2_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_302 with "Hcode"). }
    rewrite (ushp_pc_step 0x302 2). iIntros (h5) "Hrun".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                     : mword 64)]> m3).
    assert (Hm4 : forall t : mword 5, Regidx t <> Regidx s2_idx ->
                    m4 !!! Regidx t = m3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m3 (Regidx s2_idx) (Regidx t) _ Ht)).
    (* ---- 0x304  c.mv s5,a2 ---- *)
    iApply (wp_uk_cmv N h5 m4 (mword_of_int 0x304) s5_idx a2_idx
              (mword_of_int qp) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val qp))
              with "[] Hrun").
    { iApply (uis_shp_304 with "Hcode"). }
    rewrite (ushp_pc_step 0x304 2). iIntros (h6) "Hrun".
    set (m5 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int qp : mword 64)]> m4).
    assert (Hm5 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    m5 !!! Regidx t = m4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m4 (Regidx s5_idx) (Regidx t) _ Ht)).
    (* ---- 0x306  c.mv s6,a3 ---- *)
    iApply (wp_uk_cmv N h6 m5 (mword_of_int 0x306) s6_idx a3_idx
              (mword_of_int eqp) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm5 a3_idx ltac:(vm_compute; discriminate))
                      (Hm4 a3_idx ltac:(vm_compute; discriminate))
                      (Hm3 a3_idx ltac:(vm_compute; discriminate))
                      (Hm2 a3_idx ltac:(vm_compute; discriminate))
                      (Hm1 a3_idx ltac:(vm_compute; discriminate)) Ha3;
                    symmetry; exact (ushp_mv_val eqp))
              with "[] Hrun").
    { iApply (uis_shp_306 with "Hcode"). }
    rewrite (ushp_pc_step 0x306 2). iIntros (h7) "Hrun".
    set (m6 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int eqp : mword 64)]> m5).
    assert (Hm6 : forall t : mword 5, Regidx t <> Regidx s6_idx ->
                    m6 !!! Regidx t = m5 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m5 (Regidx s6_idx) (Regidx t) _ Ht)).
    assert (Ha0_6 : m6 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm6 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0x308  c.ld s1,0(a0) -- the cursor ---- *)
    iApply (wp_uk_cld N h7 m6 (mword_of_int 0x308)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 1 : mword 3) a0_idx s1_idx ps w0 (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_6 (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              Hps8 ltac:(vm_compute; discriminate)
              with "[] Hcur Hrun").
    { iApply (uis_shp_308 with "Hcode"). }
    iIntros "Hcur". rewrite (ushp_pc_step 0x308 2). iIntros (h8) "Hrun".
    set (m7 := <[Regidx s1_idx := regval_into_reg w0]> m6).
    assert (Hm7 : forall t : mword 5, Regidx t <> Regidx s1_idx ->
                    m7 !!! Regidx t = m6 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m6 (Regidx s1_idx) (Regidx t) _ Ht)).
    (* ---- 0x30a  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc N h8 m7 (mword_of_int 0x30a)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x230a)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_30a with "Hcode"). }
    rewrite (ushp_pc_step 0x30a 4). iIntros (h9) "Hrun".
    set (m8 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x230a : mword 64)]> m7).
    assert (Hm8 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m8 !!! Regidx t = m7 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m7 (Regidx s3_idx) (Regidx t) _ Ht)).
    (* ---- 0x30e  addi s3,s3,-770  -- s3 = &whitespace ---- *)
    iApply (wp_uk_addi N h9 m8 (mword_of_int 0x30e)
              (mword_of_int 3326 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m7 (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x230a
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_30e with "Hcode"). }
    rewrite (ushp_pc_step 0x30e 4). iIntros (h10) "Hrun".
    set (m9 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m8).
    assert (Hm9 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m9 !!! Regidx t = m8 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m8 (Regidx s3_idx) (Regidx t) _ Ht)).
    (* the register file the leading scan starts from *)
    assert (Hs1_9 : m9 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat off)).
    { rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m6 (Regidx s1_idx) (regval_into_reg w0)). exact Hw0. }
    assert (Hs2_9 : m9 !!! Regidx s2_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s2_idx)
               (regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                 : mword 64))). }
    assert (Hs3_9 : m9 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq m8 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    assert (Ha1_9 : m9 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    assert (Hs4_9 : m9 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hm9 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs5_9 : m9 !!! Regidx s5_idx = mword_of_int qp).
    { rewrite (Hm9 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s5_idx)
               (regval_into_reg (mword_of_int qp : mword 64))). }
    assert (Hs6_9 : m9 !!! Regidx s6_idx = mword_of_int eqp).
    { rewrite (Hm9 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s6_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m5 (Regidx s6_idx)
               (regval_into_reg (mword_of_int eqp : mword 64))). }
    assert (Hsp9 : m9 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm9 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    assert (Hkeep9 : forall t : mword 5,
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              m9 !!! Regidx t = m !!! Regidx t).
    { intros t H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (Hm9 t H19) (Hm8 t H19) (Hm7 t H9) (Hm6 t H22) (Hm5 t H21)
              (Hm4 t H18) (Hm3 t H20) (Hm2 t H8). exact (Hm1 t H2). }
    (* ---- 0x312..0x328  the LEADING whitespace scan ---- *)
    iApply (wp_kshp_ws_enter 0x312 a1_idx (mword_of_int 1858 : mword 21)
              dq dw s0 len off f nn h10 m9
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Hoffle Hs0 Hs64 Hs1_9 Hs2_9 Hs3_9 Ha1_9
              with "[] [] [] [] [] [] [] [] Hcode Hstr Hws Hrun").
    { iApply (uis_shp_312 with "Hcode"). }
    { iApply (uis_shp_316 with "Hcode"). }
    { iApply (uis_shp_31a with "Hcode"). }
    { iApply (uis_shp_31c with "Hcode"). }
    { iApply (uis_shp_320 with "Hcode"). }
    { iApply (uis_shp_322 with "Hcode"). }
    { iApply (uis_shp_324 with "Hcode"). }
    { iApply (uis_shp_328 with "Hcode"). }
    iIntros "Hstr Hws" (h11 mA) "%HpresA %Hs1A Hrun".
    assert (Hkkd : (off + ushp_skipws (len - off) off f)%nat = kk)
      by reflexivity.
    rewrite Hkkd in Hs1A.
    assert (Hs2_A : mA !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (HpresA s2_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs2_9).
    assert (Hs4_A : mA !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (HpresA s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs4_9).
    assert (Hs5_A : mA !!! Regidx s5_idx = mword_of_int qp)
      by (rewrite (HpresA s5_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs5_9).
    assert (Hs6_A : mA !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (HpresA s6_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs6_9).
    assert (Hsp_A : mA !!! Regidx csp_rs1 = spn)
      by (rewrite (HpresA csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hsp9).
    (* ---- 0x32a..0x32e  [if(q) *q = s] ---- *)
    iApply (wp_kshp_gtk_qst s0 qp kk wq nn h11 mA Hs0
              ltac:(unfold Z64 in *; lia) Hs1A Hs5_A with "Hcode Hq Hrun").
    iIntros "Hq" (h12) "Hrun".
    (* ---- 0x332..0x362 (and 0x3a6..0x3c4)  THE SWITCH ---- *)
    (* THREE ARMS, and the byte at the blank-scanned cursor decides which.
       The SYMBOL arm is [wp_kshp_gtk_disp_sym] -- the '|' walk and lane
       SH-REDIR's '>' walk under one statement, because both land on 0x364
       with the cursor advanced by one and s5 holding the byte -- and is
       taken OUT OF LINE first; the other two are the landed dichotomy,
       driven through [UkShRedirGtk.wp_kshp_gtk_disp_ns] -- the same walk as
       [UkShParseTok.wp_kshp_gtk_disp] at the premise it actually uses. *)
    destruct (andb (bool_decide (kk < len)%nat) (ushp_is_sym (f kk)))
      eqn:Egt.
    { (* ---- THE SYMBOL ARM, either byte ---- *)
      apply andb_true_iff in Egt as [ Ekkb Esym ].
      apply bool_decide_eq_true in Ekkb.
      pose proof (Hsymok kk (conj (Nat.le_add_r off (ushp_skipws (len - off) off f)) Ekkb) Esym) as Hdisj.
      assert (Hres : ushs_gettok_res len f kk = bv_unsigned (f kk)).
      { unfold ushs_gettok_res.
        rewrite (bool_decide_eq_true_2 _ Ekkb) Esym. reflexivity. }
      assert (Hend : ushs_gettok_end len f kk = S kk).
      { unfold ushs_gettok_end.
        rewrite (bool_decide_eq_true_2 _ Ekkb) Esym. reflexivity. }
      assert (Hfin : ushs_gettok_fin len f kk
                     = (S kk + ushp_skipws (len - S kk) (S kk) f)%nat)
        by (unfold ushs_gettok_fin; rewrite Hend; reflexivity).
      iApply (wp_kshp_gtk_disp_sym dq s0 len kk f nn h12 mA
                Ekkb Hdisj Hs0 Hs64 Hs1A with "Hcode Hstr Hrun").
      iIntros "Hstr" (h13 mG) "%HpresG %Hs5G %Hs1G Hrun".
      assert (Hs2_G : mG !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
        by (rewrite (HpresG s2_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs2_A).
      assert (Hs4_G : mG !!! Regidx s4_idx = mword_of_int ps)
        by (rewrite (HpresG s4_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs4_A).
      assert (Hs6_G : mG !!! Regidx s6_idx = mword_of_int eqp)
        by (rewrite (HpresG s6_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs6_A).
      assert (Hsp_G : mG !!! Regidx csp_rs1 = spn)
        by (rewrite (HpresG csp_rs1 ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hsp_A).
      assert (HkeepG : forall t : mword 5, ucallee_saved_idx t = true ->
                Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
                Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
                Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
                Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
                mG !!! Regidx t = m !!! Regidx t).
      { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
        rewrite (HpresG t (ushp_cs_ne t a4_idx Ht
                             ltac:(vm_compute; reflexivity))
                   (ushp_cs_ne t a5_idx Ht ltac:(vm_compute; reflexivity))
                   H21 H9).
        rewrite (HpresA t Ht H9).
        exact (Hkeep9 t H2 H8 H9 H18 H19 H20 H21 H22). }
      (* ---- 0x364: [if(eq) *eq = s], then the trailing blank scan ---- *)
      iApply (wp_kshp_gtk_388 dq dw s0 eqp len (S kk) f weq nn h13 mG
                ltac:(lia) Hs0 Hs64 Hs1G Hs2_G Hs6_G
                with "Hcode Heq Hstr Hws Hrun").
      iIntros "Heq Hstr Hws" (h14 mC) "%HpresC %Hs1C Hrun".
      iApply (wp_kshp_gtk_fin m sp0 spl vals ps (bv_unsigned (f kk))
                (s0 + Z.of_nat (S kk + ushp_skipws (len - S kk) (S kk) f))
                w0 nn
                h14 mC Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
                eq_refl eq_refl
                ltac:(rewrite (HpresC csp_rs1 ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hsp_G)
                ltac:(rewrite (HpresC s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4_G)
                Hs1C
                ltac:(rewrite (HpresC s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs5G)
                ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                      rewrite (HpresC t Ht H9 H19);
                      exact (HkeepG t Ht H2 H8 H9 H18 H19 H20 H21 H22))
                with "Hcode Hcur Hsl Hloc Hrun").
      iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
      rewrite Hfin Hend Hres.
      iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
      - iPureIntro. exact Hcs.
      - iPureIntro. exact Hafin. }
    (* ---- the byte at the cursor is NOT a symbol: the landed dichotomy -- *)
    assert (Hnsk : (kk < len)%nat -> ushp_is_sym (f kk) = false).
    { intro Hk. rewrite (bool_decide_eq_true_2 _ Hk) in Egt.
      cbn [andb] in Egt. exact Egt. }
    iApply (wp_kshp_gtk_disp_ns dq s0 len kk f nn h12 mA
              Hkk Hnsk Hs0 Hs64 Hs1A with "Hcode Hstr Hrun").
    iIntros "Hstr" (h13 mB) "%HpresB %Hs5B Hrun".
    assert (Hs1_B : mB !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat kk))
      by (rewrite (HpresB s1_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs1A).
    assert (Hs2_B : mB !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (HpresB s2_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs2_A).
    assert (Hs4_B : mB !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (HpresB s4_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs4_A).
    assert (Hs6_B : mB !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (HpresB s6_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs6_A).
    assert (Hsp_B : mB !!! Regidx csp_rs1 = spn)
      by (rewrite (HpresB csp_rs1 ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp_A).
    assert (HkeepB : forall t : mword 5, ucallee_saved_idx t = true ->
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              mB !!! Regidx t = m !!! Regidx t).
    { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (HpresB t (ushp_cs_ne t a4_idx Ht
                           ltac:(vm_compute; reflexivity))
                 (ushp_cs_ne t a5_idx Ht ltac:(vm_compute; reflexivity))
                 H21).
      rewrite (HpresA t Ht H9).
      exact (Hkeep9 t H2 H8 H9 H18 H19 H20 H21 H22). }
    destruct (lt_dec kk len) as [ Hklt | Hkge ].
    2: { (* THE NUL ARM: the cursor is at [es] and gettoken returns 0 ---- *)
      rewrite (bool_decide_eq_false_2 (kk < len)%nat Hkge).
      assert (Hkeq : kk = len) by lia.
      assert (Hend : ushs_gettok_end len f kk = len).
      { unfold ushs_gettok_end.
        rewrite (bool_decide_eq_false_2 (kk < len)%nat Hkge). exact Hkeq. }
      assert (Hfin : ushs_gettok_fin len f kk = len).
      { unfold ushs_gettok_fin. rewrite Hend.
        assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_skipws_zero len f). lia. }
      assert (Hres : ushs_gettok_res len f kk = 0).
      { unfold ushs_gettok_res.
        rewrite (bool_decide_eq_false_2 (kk < len)%nat Hkge). reflexivity. }
      rewrite Hkeq in Hs1_B.
      iApply (wp_kshp_gtk_388 dq dw s0 eqp len len f weq nn h13 mB
                ltac:(lia) Hs0 Hs64 Hs1_B Hs2_B Hs6_B
                with "Hcode Heq Hstr Hws Hrun").
      iIntros "Heq Hstr Hws" (h14 mC) "%HpresC %Hs1C Hrun".
      assert (Hz : (len - len)%nat = 0%nat) by lia.
      rewrite Hz (ushp_skipws_zero len f) in Hs1C.
      assert (Hlen0 : (len + 0)%nat = len) by lia.
      rewrite Hlen0 in Hs1C.
      iApply (wp_kshp_gtk_fin m sp0 spl vals ps 0 (s0 + Z.of_nat len) w0 nn
                h14 mC Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
                eq_refl eq_refl
                ltac:(rewrite (HpresC csp_rs1 ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hsp_B)
                ltac:(rewrite (HpresC s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4_B)
                Hs1C
                ltac:(rewrite (HpresC s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact (Hs5B ltac:(lia)))
                ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                      rewrite (HpresC t Ht H9 H19);
                      exact (HkeepB t Ht H2 H8 H9 H18 H19 H20 H21 H22))
                with "Hcode Hcur Hsl Hloc Hrun").
      iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
      rewrite <- Hkkd. rewrite Hkkd.
      rewrite Hfin Hend Hres.
      iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
      - iPureIntro. exact Hcs.
      - iPureIntro. exact Hafin. }
    (* THE DEFAULT ARM: an ordinary token ---- *)
    rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt).
    assert (Hres : ushs_gettok_res len f kk = 97).
    { unfold ushs_gettok_res.
      rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt) (Hnsk Hklt).
      reflexivity. }
    assert (Hendd : ushs_gettok_end len f kk
                    = (kk + ushp_toklen (len - kk) kk f)%nat).
    { unfold ushs_gettok_end.
      rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt) (Hnsk Hklt).
      reflexivity. }
    (* ---- 0x3c8  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc N h13 mB (mword_of_int 0x3c8)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x23c8)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3c8 with "Hcode"). }
    rewrite (ushp_pc_step 0x3c8 4). iIntros (h14) "Hrun".
    set (d1 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x23c8 : mword 64)]> mB).
    assert (Hd1 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    d1 !!! Regidx t = mB !!! Regidx t)
      by (intros t Ht; exact (upd_ne mB (Regidx s3_idx) (Regidx t) _ Ht)).
    (* ---- 0x3cc  addi s3,s3,-960 ---- *)
    iApply (wp_uk_addi N h14 d1 (mword_of_int 0x3cc)
              (mword_of_int 3136 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mB (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x23c8
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3cc with "Hcode"). }
    rewrite (ushp_pc_step 0x3cc 4). iIntros (h15) "Hrun".
    set (d2 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> d1).
    assert (Hd2 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    d2 !!! Regidx t = d1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d1 (Regidx s3_idx) (Regidx t) _ Ht)).
    assert (Hs3_d2 : d2 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq d1 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    (* ---- 0x3d0  auipc s5,0x2 ---- *)
    iApply (wp_uk_auipc N h15 d2 (mword_of_int 0x3d0)
              (mword_of_int 2 : mword 20) s5_idx (mword_of_int 0x23d0)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3d0 with "Hcode"). }
    rewrite (ushp_pc_step 0x3d0 4). iIntros (h16) "Hrun".
    set (d3 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 0x23d0 : mword 64)]> d2).
    assert (Hd3 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    d3 !!! Regidx t = d2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d2 (Regidx s5_idx) (Regidx t) _ Ht)).
    (* ---- 0x3d4  addi s5,s5,-976  -- s5 = &symbols ---- *)
    iApply (wp_uk_addi N h16 d3 (mword_of_int 0x3d4)
              (mword_of_int 3120 : mword 12) s5_idx s5_idx
              (mword_of_int ushp_symbols) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq d2 (Regidx s5_idx)
                               (regval_into_reg (mword_of_int 0x23d0
                                                 : mword 64)));
                    unfold ushp_symbols;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3d4 with "Hcode"). }
    rewrite (ushp_pc_step 0x3d4 4). iIntros (h17) "Hrun".
    set (d4 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int ushp_symbols
                                     : mword 64)]> d3).
    assert (Hd4 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    d4 !!! Regidx t = d3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d3 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Hs5_d4 : d4 !!! Regidx s5_idx = mword_of_int ushp_symbols)
      by exact (upd_eq d3 (Regidx s5_idx)
                  (regval_into_reg (mword_of_int ushp_symbols : mword 64))).
    assert (Hs1_d4 : d4 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat kk))
      by (rewrite (Hd4 s1_idx ltac:(vm_compute; discriminate))
                  (Hd3 s1_idx ltac:(vm_compute; discriminate))
                  (Hd2 s1_idx ltac:(vm_compute; discriminate))
                  (Hd1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_B).
    assert (Hs2_d4 : d4 !!! Regidx s2_idx
                     = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hd4 s2_idx ltac:(vm_compute; discriminate))
                  (Hd3 s2_idx ltac:(vm_compute; discriminate))
                  (Hd2 s2_idx ltac:(vm_compute; discriminate))
                  (Hd1 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_B).
    assert (Hs3_d4 : d4 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hd4 s3_idx ltac:(vm_compute; discriminate))
                  (Hd3 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_d2).
    assert (Hs4_d4 : d4 !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (Hd4 s4_idx ltac:(vm_compute; discriminate))
                  (Hd3 s4_idx ltac:(vm_compute; discriminate))
                  (Hd2 s4_idx ltac:(vm_compute; discriminate))
                  (Hd1 s4_idx ltac:(vm_compute; discriminate)); exact Hs4_B).
    assert (Hs6_d4 : d4 !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (Hd4 s6_idx ltac:(vm_compute; discriminate))
                  (Hd3 s6_idx ltac:(vm_compute; discriminate))
                  (Hd2 s6_idx ltac:(vm_compute; discriminate))
                  (Hd1 s6_idx ltac:(vm_compute; discriminate)); exact Hs6_B).
    assert (Hsp_d4 : d4 !!! Regidx csp_rs1 = spn)
      by (rewrite (Hd4 csp_rs1 ltac:(vm_compute; discriminate))
                  (Hd3 csp_rs1 ltac:(vm_compute; discriminate))
                  (Hd2 csp_rs1 ltac:(vm_compute; discriminate))
                  (Hd1 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp_B).
    assert (Hkeep_d4 : forall t : mword 5, ucallee_saved_idx t = true ->
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              d4 !!! Regidx t = m !!! Regidx t).
    { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (Hd4 t H21) (Hd3 t H21) (Hd2 t H19) (Hd1 t H19).
      exact (HkeepB t Ht H2 H8 H9 H18 H19 H20 H21 H22). }
    (* ---- 0x3d8  bgeu s1,s2,0x41a -- refuted: the cursor is inside ---- *)
    assert (Htk : false = uv_btaken BGEU (d4 !!! Regidx s1_idx)
                            (d4 !!! Regidx s2_idx)).
    { cbn [uv_btaken]. rewrite Hs1_d4 Hs2_d4.
      rewrite (moi_ge_u (s0 + Z.of_nat kk) (s0 + Z.of_nat len)
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype N h17 d4 (mword_of_int 0x3d8)
              (mword_of_int 66 : mword 13) s2_idx s1_idx BGEU false
              (mword_of_int 0x41a) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_3d8 with "Hcode"). }
    rewrite (ushp_pc_step 0x3d8 4). iIntros (h18) "Hrun".
    (* ---- 0x3dc..0x3f6  THE TOKEN-BODY SCAN ---- *)
    iApply (wp_kshp_tok_scan dq dw dv s0 len f nn (len - kk)%nat kk h18 d4
              eq_refl Hklt Hs0 Hs64 Hs1_d4 Hs2_d4 Hs3_d4 Hs5_d4
              with "Hcode Hstr Hws Hsy Hrun").
    iIntros "Hstr Hws Hsy" (h19 mE) "%HpresE %Hs1E %Hs5E Hrun".
    set (ee := ushs_gettok_end len f kk).
    assert (Heed : (kk + ushp_toklen (len - kk) kk f)%nat = ee)
      by (unfold ee; rewrite Hendd; reflexivity).
    rewrite Heed in Hs1E.
    assert (Heele : (ee <= len)%nat).
    { rewrite <- Heed. pose proof (ushp_toklen_le (len - kk) kk f). lia. }
    assert (Hexit : ushp_tok_exit len f kk
                    = if bool_decide (ee < len)%nat then 0x364 else 0x400)
      by (unfold ushp_tok_exit; rewrite Heed; reflexivity).
    rewrite Hexit.
    assert (Hs2_E : mE !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (HpresE s2_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs2_d4).
    assert (Hs4_E : mE !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (HpresE s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs4_d4).
    assert (Hs6_E : mE !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (HpresE s6_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs6_d4).
    assert (Hsp_E : mE !!! Regidx csp_rs1 = spn)
      by (rewrite (HpresE csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp_d4).
    assert (Hkeep_E : forall t : mword 5, ucallee_saved_idx t = true ->
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              mE !!! Regidx t = m !!! Regidx t).
    { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (HpresE t Ht H9 H21).
      exact (Hkeep_d4 t Ht H2 H8 H9 H18 H19 H20 H21 H22). }
    destruct (bool_decide (ee < len)%nat) eqn:Eee.
    { (* the token was ended by a byte: 0x364, then the trailing scan *)
      apply bool_decide_eq_true in Eee.
      iApply (wp_kshp_gtk_388 dq dw s0 eqp len ee f weq nn h19 mE
                ltac:(lia) Hs0 Hs64 Hs1E Hs2_E Hs6_E
                with "Hcode Heq Hstr Hws Hrun").
      iIntros "Heq Hstr Hws" (h20 mF) "%HpresF %Hs1F Hrun".
      assert (Hfin : ushs_gettok_fin len f kk
                     = (ee + ushp_skipws (len - ee) ee f)%nat)
        by (unfold ushs_gettok_fin; rewrite Hendd Heed; reflexivity).
      iApply (wp_kshp_gtk_fin m sp0 spl vals ps 97
                (s0 + Z.of_nat (ee + ushp_skipws (len - ee) ee f)) w0 nn
                h20 mF Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
                eq_refl eq_refl
                ltac:(rewrite (HpresF csp_rs1 ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hsp_E)
                ltac:(rewrite (HpresF s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4_E)
                Hs1F
                ltac:(rewrite (HpresF s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs5E)
                ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                      rewrite (HpresF t Ht H9 H19);
                      exact (Hkeep_E t Ht H2 H8 H9 H18 H19 H20 H21 H22))
                with "Hcode Hcur Hsl Hloc Hrun").
      iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
      rewrite Hfin Hres.
      iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
      - iPureIntro. exact Hcs.
      - iPureIntro. exact Hafin. }
    (* the token ran to [es]: 0x400, and the trailing scan is empty *)
    apply bool_decide_eq_false in Eee.
    assert (Heeq : ee = len) by lia.
    rewrite Heeq in Hs1E.
    assert (Hfin : ushs_gettok_fin len f kk = len).
    { assert (H1 : ushs_gettok_fin len f kk
                   = (ee + ushp_skipws (len - ee) ee f)%nat)
        by (unfold ushs_gettok_fin; rewrite Hendd Heed; reflexivity).
      rewrite H1 Heeq.
      assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
      rewrite (ushp_skipws_zero len f). lia. }
    iApply (wp_kshp_gtk_424 dq dw s0 eqp len f weq nn h19 mE
              Hs0 Hs64 Hs1E Hs2_E Hs6_E with "Hcode Heq Hstr Hws Hrun").
    iIntros "Heq Hstr Hws" (h20 mF) "%HpresF %Hs1F Hrun".
    iApply (wp_kshp_gtk_fin m sp0 spl vals ps 97 (s0 + Z.of_nat len) w0 nn
              h20 mF Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
              eq_refl eq_refl
              ltac:(rewrite (HpresF csp_rs1 ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hsp_E)
              ltac:(rewrite (HpresF s4_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs4_E)
              Hs1F
              ltac:(rewrite (HpresF s5_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs5E)
              ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                    rewrite (HpresF t Ht H9 H19);
                    exact (Hkeep_E t Ht H2 H8 H9 H18 H19 H20 H21 H22))
              with "Hcode Hcur Hsl Hloc Hrun").
    iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
    rewrite Hfin Hres Heeq.
    iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Hafin.
  Qed.

  (* the same walk with the answer in the landed spelling: what the two
     symbol tiers instantiate *)
  Lemma wp_ref_gettoken_ushs (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps qp eqp s0 : Z) (len off : nat) (f : nat -> bv 8)
      (w0 wq weq : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx a2_idx = mword_of_int qp ->
    m !!! Regidx a3_idx = mword_of_int eqp ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ref_sym_scope_from len f off ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ushp_cell qp wq -∗
    ushp_cell eqp weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h m (mword_of_int ShSyms.gettoken) (8 + (2 + nn)) -∗
    (uword γd ps
       (mword_of_int
          (s0 + Z.of_nat
                  (ushs_gettok_fin len f
                     (off + ushp_skipws (len - off) off f)))) -∗
     ushp_cell qp
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ushp_cell eqp
       (mword_of_int
          (s0 + Z.of_nat
                  (ushs_gettok_end len f
                     (off + ushp_skipws (len - off) off f)))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
             = mword_of_int
                 (ushs_gettok_res len f
                    (off + ushp_skipws (len - off) off f)) ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx))
           (8 + (2 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Ha2 Ha3 Hoffle Hw0 Hsymok Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
    iDestruct (ustr_nonul with "Hstr") as %Hnonul.
    iApply (wp_ref_gettoken h m dq dw dv ps qp eqp s0 len off f w0 wq weq nn
              _ _ _ _ Ha0 Ha1 Ha2 Ha3 Hoffle Hw0 Hsymok Hs0 Hs64 Hps0 Hps8 Hpssz
              (ref_gettoken_ushs len f off Hsymok Hnonul Hoffle)
              with "Hcode Hcur Hq Heq Hstr Hws Hsy Hrun Hcont").
  Qed.


  (* ===================================================================== *)
  (* (3) peek, AT THE REFERENCE                                            *)
  (* ===================================================================== *)

  (* peek's landed answer is 0 or 1, so it is the bit of its own equation
     to 1 *)
  Lemma ushp_peek_res_bool (len k tlen : nat) (f tf : nat -> bv 8) :
    (if bool_decide (ushp_peek_res len f k tlen tf = 1) then 1 else 0)
    = ushp_peek_res len f k tlen tf.
  Proof using .
    unfold ushp_peek_res.
    destruct (bool_decide (k < len)%nat);
      [ destruct (ushp_find tlen 0%nat tf (f k)) | ]; reflexivity.
  Qed.

  (* [RefParseSym.ref_peek_find] at [ushp_peek_res]'s spelling *)
  Lemma ref_peek_ushp (len off tlen : nat) (f tf : nat -> bv 8)
      (tl : list (bv 8)) :
    ref_nonnul len f -> (off <= len)%nat -> tl = tf <$> seq 0%nat tlen ->
    ref_peek len f off tl
    = (bool_decide
         (ushp_peek_res len f (off + ushp_skipws (len - off) off f) tlen tf = 1),
       (off + ushp_skipws (len - off) off f)%nat).
  Proof using .
    intros Hnn Hoff Htl.
    rewrite (ref_peek_find len f off tlen tf tl Hnn Hoff Htl).
    unfold ushp_peek_res.
    destruct (lt_dec (off + ushp_skipws (len - off) off f) len) as [ Hlt | Hge ].
    - rewrite !(bool_decide_eq_true_2 _ Hlt).
      destruct (ushp_find tlen 0%nat tf (f _)); reflexivity.
    - rewrite !(bool_decide_eq_false_2 _ Hge). reflexivity.
  Qed.

  Lemma wp_ref_peek (h : CpuId) (m : regfile) (dq dw : dfrac)
      (tt : bool) (dt : dfrac)
      (ps s0 toks : Z) (len off tlen : nat) (f tf : nat -> bv 8)
      (w0 : mword 64) (nn : nat)
      (tl : list (bv 8)) (hit : bool) (s : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx a2_idx = mword_of_int toks ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < toks -> toks + Z.of_nat tlen < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    tl = tf <$> seq 0%nat tlen ->
    ref_peek len f off tl = (hit, s) ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ushp_sstr tt dt toks tlen tf -∗
    urun N h m (mword_of_int ShSyms.peek) (8 + (2 + nn)) -∗
    (uword γd ps (mword_of_int (s0 + Z.of_nat s)) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ushp_sstr tt dt toks tlen tf -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int (if hit then 1 else 0) ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (8 + (2 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Hs0 Hs64 Ht0 Ht64 Hps0 Hps8 Hpssz Htl Href.
    iIntros "#Hcode Hcur Hstr Hws Htoks Hrun Hcont".
    iDestruct (ustr_nonul with "Hstr") as %Hnonul.
    rewrite (ref_peek_ushp len off tlen f tf tl Hnonul Hoffle Htl) in Href.
    injection Href as Ehit Es. subst hit s.
    iApply (wp_kshp_peek h m dq dw tt dt ps s0 toks len off tlen f tf w0 nn
              Ha0 Ha1 Ha2 Hoffle Hw0 Hs0 Hs64 Ht0 Ht64 Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws Htoks Hrun").
    iIntros "Hcur Hstr Hws Htoks" (h' m') "%Hcs %Ha0' Hrun".
    iApply ("Hcont" with "Hcur Hstr Hws Htoks [] [] Hrun").
    - iPureIntro. exact Hcs.
    - iPureIntro. rewrite ushp_peek_res_bool. exact Ha0'.
  Qed.

End UkShGettoken.
