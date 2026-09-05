(* ===================================================================== *)
(* UkShParseTok.v -- SH LANE STAGE 4, part 3: gettoken.                    *)
(*                                                                        *)
(*   gettoken @0x310  -- 104 instructions, an EIGHT-word frame, THREE      *)
(*                       scans and a jump-table-free dispatch on the       *)
(*                       first non-blank byte.                             *)
(*                                                                        *)
(* It is the function [parseexec]'s argument loop calls once per token,    *)
(* and the one that turns a cursor into a token's two BOUNDARIES -- which  *)
(* is what the execcmd node records and what [nulterminate] later cuts at. *)
(* Its blank scan is peek's, re-stated once here because the pc-relative   *)
(* offset differs.                                                         *)
(*                                                                        *)
(* See iris/UkShParse.v's header for why stage 4 is six files.            *)
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
Require Import UserBits.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UkStep.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShK UCodeShP.
Require Import UkSh.
Require Import TsoCtx.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseLex.

Section UkShParseTok.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context (γt γd γs γfd : gname).

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


(*ALIASES-BEGIN*)
  (* ---- what the earlier files of the parser define, at this
         file's own ghost names.  Everything else they export is a
         PURE constant and comes in with the [Require Import]. ---- *)
  Local Notation urun_x0 := (UkShParse.urun_x0 γt γd γs γfd).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join γd).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split γd).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty γt γd γs γfd).
  Local Notation wp_kshp_fp := (UkShParse.wp_kshp_fp γt γd γs γfd).
  Local Notation wp_kshp_peek_epi := (UkShParseLex.wp_kshp_peek_epi γt γd γs γfd).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore γt γd γs γfd).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill γt γd γs γfd).
  Local Notation wp_kshp_strchr := (UkShParse.wp_kshp_strchr γt γd γs γfd).

  (* stage 4's one Hypothesis, at the type the base file names *)
  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.

(*ALIASES-END*)


  (* ===================================================================== *)
  (* §9 gettoken @0x310 -- 104 instructions, an EIGHT-word frame, THREE      *)
  (* scans and a switch.                                                    *)
  (*                                                                       *)
  (*   int gettoken(char **ps, char *es, char **q, char **eq) {             *)
  (*     char *s = *ps;  int ret;                                          *)
  (*     while(s < es && strchr(whitespace, *s)) s++;                       *)
  (*     if(q) *q = s;                                                     *)
  (*     ret = *s;                                                         *)
  (*     switch( *s ){ case 0: break;                                        *)
  (*       case '|': case '(': case ')': case ';': case '&': case '<':     *)
  (*         s++; break;                                                   *)
  (*       case '>': s++; if( *s == '>'){ ret = '+'; s++; } break;          *)
  (*       default: ret = 'a';                                             *)
  (*         while(s < es && !strchr(whitespace, *s)                       *)
  (*                      && !strchr(symbols, *s)) s++;                    *)
  (*         break; }                                                      *)
  (*     if(eq) *eq = s;                                                   *)
  (*     while(s < es && strchr(whitespace, *s)) s++;                       *)
  (*     *ps = s;  return ret; }                                           *)
  (*                                                                       *)
  (* THE LEXER PROPER: peek only LOOKS, gettoken CONSUMES.  It moves the    *)
  (* cursor past one token and reports what kind it was, and its two out    *)
  (* parameters [q] / [eq] are what [parseexec] records as the token's      *)
  (* boundary pair -- which is why the tree predicate indexes tokens by     *)
  (* PAIRS OF INDEXES and not by strings.                                   *)
  (*                                                                       *)
  (* SCOPED BY [ushp_no_symbols], AND THAT IS WHAT MAKES IT TRACTABLE.      *)
  (* The switch has eight arms in the source and four in the object code    *)
  (* (a NUL arm, a six-value symbol arm, a '>' arm with its own '>>'        *)
  (* lookahead, and a default).  On a line with no symbol byte only TWO of  *)
  (* them are reachable, and WHICH ONE is decided by a single fact: the     *)
  (* byte at the cursor is NUL exactly when the cursor has reached [es],    *)
  (* because a [ustr]'s body bytes are all non-NUL.  So the postcondition   *)
  (* is a dichotomy on [k = len], not an eight-way case analysis -- and     *)
  (* the six symbol arms and the '>' arm are REFUTED, at the branch, from   *)
  (* [ushp_nsym_bv]'s seven numeric disequalities.                          *)
  (*                                                                       *)
  (* THREE SCANS, TWO MOULDS.  The leading and trailing whitespace scans    *)
  (* are the SAME CODE as peek's, at 0x33a and 0x39c rather than 0x46e --   *)
  (* identical widths, identical branch immediates, only the [jal]'s        *)
  (* pc-relative offset differs -- so §8's scan is re-stated once over its  *)
  (* base pc and its [jal] immediate ([wp_kshp_ws_scan]) and applied three  *)
  (* times.  The token-body scan at 0x400 is the new one: the same loop     *)
  (* with TWO [strchr] calls per turn, measured by [ushp_toklen].            *)
  (* ===================================================================== *)

  (* ---- the two pieces of 32-bit algebra the switch needs ---------------- *)

  (* what [sign_extend'] DOES to a 32-bit word, as a Z.  [sext32_small] is
     the special case that fits; gettoken's [addiw a5,a5,-40] does NOT fit
     when the byte is below 40, and the following [andi] is what makes that
     harmless -- so what is needed is the unconditional formula. *)
  Lemma ushp_sext32_unsigned (w : mword 32) :
    bv_unsigned (sign_extend' 64 w : mword 64)
    = (((bv_unsigned w + Z31) mod Z32) - Z31) mod Z64.
  Proof.
    cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec
         to_word get_word MachineWord.MachineWord.sign_extend].
    rewrite bv_sign_extend_unsigned.
    unfold bv_signed, bv_swrap, bv_wrap.
    assert (Eh32 : bv_half_modulus 32 = Z31) by (vm_compute; reflexivity).
    rewrite Zmod32 Eh32 Zmod64. reflexivity.
  Qed.

  (* ...and why the sign extension is harmless: [zext.b] keeps the low eight
     bits, and sign extension does not touch them. *)
  Lemma ushp_and255_sext (w : mword 32) :
    and_vec (sign_extend' 64 w : mword 64) (mword_of_int 255)
    = mword_of_int (bv_unsigned w mod 256).
  Proof.
    apply bv_eq. rewrite and_vec64_unsigned.
    assert (H255 : bv_unsigned (mword_of_int 255 : mword 64) = 255)
      by (vm_compute; reflexivity).
    rewrite H255 ushp_sext32_unsigned !moi_unsigned.
    set (u := bv_unsigned w).
    assert (Ho : (255 = Z.ones 8)) by (vm_compute; reflexivity).
    rewrite Ho.
    rewrite (Z.land_ones ((((u + Z31) mod Z32) - Z31) mod Z64) 8 ltac:(lia)).
    assert (E8 : 2 ^ 8 = 256) by (vm_compute; reflexivity). rewrite E8.
    rewrite <- (Znumtheory.Zmod_div_mod 256 Z64 (((u + Z31) mod Z32) - Z31)
                  ltac:(lia) ltac:(unfold Z64; lia)
                  ltac:(exists 72057594037927936; unfold Z64; reflexivity)).
    rewrite Zminus_mod.
    rewrite <- (Znumtheory.Zmod_div_mod 256 Z32 (u + Z31)
                  ltac:(lia) ltac:(unfold Z32; lia)
                  ltac:(exists 16777216; unfold Z32; reflexivity)).
    assert (EZ31 : Z31 mod 256 = 0) by (vm_compute; reflexivity).
    rewrite EZ31 Z.sub_0_r Zmod_mod Zplus_mod EZ31 Z.add_0_r Zmod_mod.
    rewrite (Z.mod_small (u mod 256) Z64
               ltac:(pose proof (Z.mod_pos_bound u 256 ltac:(lia));
                     unfold Z64; lia)).
    reflexivity.
  Qed.

  (* [sext.w s5,a5] on a byte: the value is already in range, so it is the
     identity -- which is why [ret] and the compared byte are the same Z. *)
  Lemma ushp_sextw_byte (v : Z) :
    0 <= v < 256 ->
    (sign_extend' 64
       (subrange_vec_dec
          (add_vec (mword_of_int v : mword 64)
             (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0 : mword 32)
     : mword 64)
    = mword_of_int v.
  Proof.
    intro Hv.
    assert (E0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
                 = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 (moi_addw v 0 ltac:(unfold Z31; lia)).
    f_equal. lia.
  Qed.

  (* [addiw a5,a5,-40 ; zext.b a5,a5] -- the switch's range test, as a Z.
     Below 40 the [addiw] wraps and the [zext.b] unwraps it; the composite
     is exactly [(v - 40) mod 256], which is 0 or 1 on precisely the two
     bytes '(' and ')' -- both of them symbols. *)
  Lemma ushp_addiw_andi (v : Z) :
    0 <= v < 256 ->
    and_vec
      (sign_extend' 64
         (subrange_vec_dec
            (add_vec (mword_of_int v : mword 64)
               (sign_extend' 64 (mword_of_int 4056 : mword 12))) 31 0
          : mword 32) : mword 64)
      (sign_extend' 64 (mword_of_int 255 : mword 12))
    = mword_of_int ((v - 40) mod 256).
  Proof.
    intro Hv.
    assert (Ei : (sign_extend' 64 (mword_of_int 4056 : mword 12) : mword 64)
                 = mword_of_int (-40))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : (sign_extend' 64 (mword_of_int 255 : mword 12) : mword 64)
                 = mword_of_int 255)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ei Em moi_add.
    rewrite (ushp_and255_sext
               (subrange_vec_dec (mword_of_int (v + -40) : mword 64) 31 0)).
    rewrite low32_moi.
    f_equal.
    rewrite <- (Znumtheory.Zmod_div_mod 256 Z32 (v + -40)
                  ltac:(lia) ltac:(unfold Z32; lia)
                  ltac:(exists 16777216; unfold Z32; reflexivity)).
    f_equal; lia.
  Qed.

  (* ---- the scan mould, over its base pc --------------------------------- *)

  (* [ushp_pc_step] at a pc the caller wants NAMED rather than summed: the
     walks below run at [p + 4], [p + 6], ... and every step would otherwise
     leave an [p + 6 + 4] the next [uinstr_is] does not match. *)
  (* THE WHITESPACE SCAN, ONCE, FOR ALL THREE OF ITS COPIES.
       p+0   lbu a1,0(s1)     p+4   c.mv a0,s3      p+6   jal strchr
       p+10  c.beqz a0,p+20   p+12  c.addi s1,s1,1  p+14  bne s2,s1,p
       p+18  c.mv s1,s2       p+20  the exit
     peek's is at p = 0x46e and gettoken's two at p = 0x33a and p = 0x39c --
     the SAME widths and the SAME branch immediates, gcc having emitted the
     same loop three times; only the [jal]'s pc-relative offset differs, and
     that is the parameter [ji].  What a call site owes instead of the four
     [vm_compute]s this proof used to do inline is four pure facts at
     CONCRETE numbers ([Hjt], [Hjr], [Hal20], [Halp]) -- the §4b bargain. *)
  Lemma wp_kshp_ws_scan (p : Z) (ji : mword 21) (dq dw : dfrac)
      (s0 : Z) (len : nat) (f : nat -> bv 8) (nn : nat) :
    (mword_of_int 0xa82 : mword 64)
      = add_vec (mword_of_int (p + 6)) (sign_extend' 64 ji) ->
    ret_pc (mword_of_int (p + 10) : mword 64) = mword_of_int (p + 10) ->
    eq_vec (access_vec_dec (mword_of_int (p + 20) : mword 64) 0) ('b"0")
      = true ->
    eq_vec (access_vec_dec (mword_of_int p : mword 64) 0) ('b"0") = true ->
    forall (r j : nat) (h : CpuId) (mc : regfile),
    (len - j = r)%nat -> (j < len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s3_idx = mword_of_int ushp_whitespace ->
    uinstr_is γt (mword_of_int p) false
      (LOAD (mword_of_int 0 : mword 12, Regidx s1_idx, Regidx a1_idx,
             true, 1)) -∗
    uinstr_is γt (mword_of_int (p + 4)) true
      (C_MV (Regidx a0_idx, Regidx s3_idx)) -∗
    uinstr_is γt (mword_of_int (p + 6)) false (JAL (ji, Regidx ra_idx)) -∗
    uinstr_is γt (mword_of_int (p + 10)) true
      (C_BEQZ (mword_of_int 5 : mword 8, Cregidx (mword_of_int 2))) -∗
    uinstr_is γt (mword_of_int (p + 12)) true
      (C_ADDI (mword_of_int 1 : mword 6, Regidx s1_idx)) -∗
    uinstr_is γt (mword_of_int (p + 14)) false
      (BTYPE (mword_of_int 8178 : mword 13, Regidx s1_idx, Regidx s2_idx,
              BNE)) -∗
    uinstr_is γt (mword_of_int (p + 18)) true
      (C_MV (Regidx s1_idx, Regidx s2_idx)) -∗
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int p) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
             Regidx q <> Regidx s1_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int (p + 20)) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjt Hjr Hal20 Halp.
    assert (Ebz : (mword_of_int (p + 20) : mword 64)
                  = add_vec (mword_of_int (p + 10))
                      (sign_extend' 64 (sign_extend' 13
                         (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))).
    { assert (E : (sign_extend' 64 (sign_extend' 13
                     (concat_vec (mword_of_int 5 : mword 8) ('b"0")))
                   : mword 64) = mword_of_int 10)
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E moi_add. f_equal; lia. }
    assert (Ebn : (mword_of_int p : mword 64)
                  = add_vec (mword_of_int (p + 14))
                      (sign_extend' 64 (mword_of_int 8178 : mword 13))).
    { assert (E : (sign_extend' 64 (mword_of_int 8178 : mword 13)
                   : mword 64) = mword_of_int (-14))
        by (apply bv_eq; vm_compute; reflexivity).
      rewrite E moi_add. f_equal; lia. }
    intros r. induction r as [| r IH ];
      intros j h mc Hr Hj Hs0 Hs64 Hs1 Hs2 Hs3;
      iIntros "#Hi0 #Hi1 #Hi2 #Hi3 #Hi4 #Hi5 #Hi6 #Hcode Hstr Hws Hrun Hcont";
      [ lia | ].
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    (* ---- p+0  lbu a1,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f j Hj with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs γfd h mc (mword_of_int p)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat j) (f j) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat j)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "Hi0 Hb Hrun").
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step' p 4 (p + 4) ltac:(lia)). iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                     : mword 64)]> mc).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                    m1 !!! Regidx q = mc !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc (Regidx a1_idx) (Regidx q) _ Hq)).
    assert (Ha1_1 : m1 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (upd_eq mc (Regidx a1_idx)
                 (regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f j)). }
    (* ---- p+4  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 m1 (mword_of_int (p + 4)) a0_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)) Hs3;
                    symmetry; exact (ushp_mv_val ushp_whitespace))
              with "Hi1 Hrun").
    rewrite (ushp_pc_step' (p + 4) 2 (p + 6) ltac:(lia)). iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- p+6  jal a82 <strchr> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h2 m2 (mword_of_int (p + 6))
              ji ra_idx (mword_of_int 0xa82) (mword_of_int (p + 10)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              Hjt
              ltac:(symmetry;
                    exact (ushp_pc_step' (p + 6) 4 (p + 10) ltac:(lia)))
              ltac:(vm_compute; reflexivity)
              with "Hi2 Hrun").
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int (p + 10) : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int ushp_whitespace).
    { rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m1 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ushp_whitespace : mword 64))). }
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)). exact Ha1_1. }
    assert (Eret : ret_pc (m3 !!! Regidx ra_idx) = mword_of_int (p + 10)).
    { rewrite (upd_eq m2 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int (p + 10) : mword 64))).
      exact Hjr. }
    assert (Hcs3 : forall q : mword 5, ucallee_saved_idx q = true ->
                     m3 !!! Regidx q = mc !!! Regidx q).
    { intros q Hq.
      rewrite (Hm3 q (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm2 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
      exact (Hm1 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity))). }
    rewrite <- shpp_strchr.
    iApply (wp_kshp_strchr h3 m3 false dw ushp_whitespace 5 ushp_ws_f (f j) nn
              Ha0_3 Ha1_3 ltac:(unfold ushp_whitespace; lia)
              ltac:(unfold ushp_whitespace, Z64; lia)
              with "Hcode Hws Hrun").
    iIntros "Hws" (h4 m4) "%Hcs34 %Ha0_4 Hrun".
    rewrite Eret.
    assert (Hcs4 : forall q : mword 5, ucallee_saved_idx q = true ->
                     m4 !!! Regidx q = mc !!! Regidx q)
      by (intros q Hq; rewrite (Hcs34 q Hq); exact (Hcs3 q Hq)).
    assert (Hs1_4 : m4 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j))
      by (rewrite (Hcs4 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (Hs2_4 : m4 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hcs4 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2).
    assert (Hs3_4 : m4 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hcs4 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3).
    (* ---- p+10  c.beqz a0,p+20 -- the byte's membership decides ---- *)
    destruct (ushp_is_ws (f j)) eqn:Ews.
    2: { (* NOT whitespace: the scan stops here and [s1] never moved *)
      assert (Htk : true = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 (ushp_ws_chr_z (f j) Ews).
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_cbeqz γt γd γs γfd h4 m4 (mword_of_int (p + 10))
                (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int (p + 20)) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk Ebz
                ltac:(intros _; exact Hal20)
                with "Hi3 Hrun").
      iIntros (h5) "Hrun".
      iApply ("Hcont" with "Hstr Hws [] [] Hrun").
      - iPureIntro. intros q Hq _. exact (Hcs4 q Hq).
      - iPureIntro. rewrite Hs1_4.
        rewrite (ushp_skipws_stop (len - j) j f Ews). f_equal; lia. }
    (* WHITESPACE: the loop goes round *)
    destruct (ushp_ws_chr_nz (f j) Ews) as [ k [ Hk Hchr ] ].
    assert (Htk : false = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0_4 Hchr.
      rewrite (moi_eq_zero (ushp_whitespace + Z.of_nat k)
                 ltac:(unfold ushp_whitespace, Z64; lia)).
      symmetry. apply Z.eqb_neq. unfold ushp_whitespace. lia. }
    iApply (wp_uk_cbeqz γt γd γs γfd h4 m4 (mword_of_int (p + 10))
              (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int (p + 20)) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk Ebz
              ltac:(discriminate)
              with "Hi3 Hrun").
    rewrite (ushp_pc_step' (p + 10) 2 (p + 12) ltac:(lia)).
    iIntros (h5) "Hrun".
    (* ---- p+12  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h5 m4 (mword_of_int (p + 12))
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S j))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_4 E1 moi_add;
                    replace (s0 + Z.of_nat (S j)) with (s0 + Z.of_nat j + 1)
                      by lia;
                    reflexivity)
              with "Hi4 Hrun").
    rewrite (ushp_pc_step' (p + 12) 2 (p + 14) ltac:(lia)).
    iIntros (h6) "Hrun".
    set (m5 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat (S j))
                                     : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Hs1_5 : m5 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat (S j)))
      by exact (upd_eq m4 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (s0 + Z.of_nat (S j))
                                    : mword 64))).
    assert (Hs2_5 : m5 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hm5 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_4).
    assert (Hs3_5 : m5 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hm5 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_4).
    (* ---- p+14  bne s2,s1,p ---- *)
    destruct (Nat.eq_dec (S j) len) as [ Hend | Hend ].
    { (* the scan ran to [es]: fall through to p+18, which is a no-op *)
      assert (Htk2 : false = uv_btaken BNE (m5 !!! Regidx s2_idx)
                               (m5 !!! Regidx s1_idx)).
      { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5 Hend.
        rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(lia) ltac:(lia)).
        rewrite Z.eqb_refl. reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h6 m5 (mword_of_int (p + 14))
                (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE false
                (mword_of_int p) (2 + nn)
                Htk2 Ebn ltac:(discriminate)
                with "Hi5 Hrun").
      rewrite (ushp_pc_step' (p + 14) 4 (p + 18) ltac:(lia)).
      iIntros (h7) "Hrun".
      (* ---- p+18  c.mv s1,s2 -- [s = es], which it already is ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h7 m5 (mword_of_int (p + 18))
                s1_idx s2_idx (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_5; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "Hi6 Hrun").
      rewrite (ushp_pc_step' (p + 18) 2 (p + 20) ltac:(lia)).
      iIntros (h8) "Hrun".
      iApply ("Hcont" with "Hstr Hws [] [] Hrun").
      - iPureIntro. intros q Hq Hqs1.
        rewrite (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hqs1).
        rewrite (Hm5 q Hqs1). exact (Hcs4 q Hq).
      - iPureIntro.
        rewrite (upd_eq m5 (Regidx s1_idx)
                   (regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                     : mword 64))).
        rewrite Hr (ushp_skipws_step r j f Ews).
        assert (Hz : r = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_skipws_zero (S j) f).
        assert (Ee : (s0 + Z.of_nat len) = (s0 + Z.of_nat (j + 1))) by lia.
        rewrite Ee. reflexivity. }
    (* ...or the loop goes round *)
    assert (Hj1 : (S j < len)%nat) by lia.
    assert (Htk2 : true = uv_btaken BNE (m5 !!! Regidx s2_idx)
                            (m5 !!! Regidx s1_idx)).
    { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5.
      rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat (S j))
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      assert (Hne2 : (s0 + Z.of_nat len =? s0 + Z.of_nat (S j)) = false)
        by (apply Z.eqb_neq; lia).
      rewrite Hne2. reflexivity. }
    iApply (wp_uk_btype γt γd γs γfd h6 m5 (mword_of_int (p + 14))
              (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE true
              (mword_of_int p) (2 + nn)
              Htk2 Ebn ltac:(intros _; exact Halp)
              with "Hi5 Hrun").
    iIntros (h7) "Hrun".
    iApply (IH (S j) h7 m5 ltac:(lia) Hj1 Hs0 Hs64 Hs1_5 Hs2_5 Hs3_5
              with "Hi0 Hi1 Hi2 Hi3 Hi4 Hi5 Hi6 Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h8 mc') "%Hpres %Hret2 Hrun".
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. intros q Hq Hqs1.
      rewrite (Hpres q Hq Hqs1). rewrite (Hm5 q Hqs1). exact (Hcs4 q Hq).
    - iPureIntro. rewrite Hret2 Hr (ushp_skipws_step r j f Ews).
      assert (Er : (len - S j)%nat = r) by lia. rewrite Er.
      f_equal; lia.
  Qed.

  (* the scan's ENTRY test, folded in FRONT so the cursor's index ranges over
     [0..len] and the whole of [q .. q+24] has ONE postcondition.  The
     compared register is a PARAMETER: gettoken's first copy tests against
     [a1] (the argument is still live) and its second against [s2], and
     peek's tests against [a1] -- same instruction, different rs2. *)
  Lemma wp_kshp_ws_enter (q : Z) (re : mword 5) (ji : mword 21)
      (dq dw : dfrac) (s0 : Z) (len j : nat) (f : nat -> bv 8) (nn : nat)
      (h : CpuId) (mc : regfile) :
    (mword_of_int 0xa82 : mword 64)
      = add_vec (mword_of_int (q + 10)) (sign_extend' 64 ji) ->
    ret_pc (mword_of_int (q + 14) : mword 64) = mword_of_int (q + 14) ->
    eq_vec (access_vec_dec (mword_of_int (q + 24) : mword 64) 0) ('b"0")
      = true ->
    eq_vec (access_vec_dec (mword_of_int (q + 4) : mword 64) 0) ('b"0")
      = true ->
    (j <= len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s3_idx = mword_of_int ushp_whitespace ->
    mc !!! Regidx re = mword_of_int (s0 + Z.of_nat len) ->
    uinstr_is γt (mword_of_int q) false
      (BTYPE (mword_of_int 24 : mword 13, Regidx re, Regidx s1_idx, BGEU)) -∗
    uinstr_is γt (mword_of_int (q + 4)) false
      (LOAD (mword_of_int 0 : mword 12, Regidx s1_idx, Regidx a1_idx,
             true, 1)) -∗
    uinstr_is γt (mword_of_int (q + 8)) true
      (C_MV (Regidx a0_idx, Regidx s3_idx)) -∗
    uinstr_is γt (mword_of_int (q + 10)) false (JAL (ji, Regidx ra_idx)) -∗
    uinstr_is γt (mword_of_int (q + 14)) true
      (C_BEQZ (mword_of_int 5 : mword 8, Cregidx (mword_of_int 2))) -∗
    uinstr_is γt (mword_of_int (q + 16)) true
      (C_ADDI (mword_of_int 1 : mword 6, Regidx s1_idx)) -∗
    uinstr_is γt (mword_of_int (q + 18)) false
      (BTYPE (mword_of_int 8178 : mword 13, Regidx s1_idx, Regidx s2_idx,
              BNE)) -∗
    uinstr_is γt (mword_of_int (q + 22)) true
      (C_MV (Regidx s1_idx, Regidx s2_idx)) -∗
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int q) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int (q + 24)) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjt Hjr Hal24 Hal4 Hjle Hs0 Hs64 Hs1 Hs2 Hs3 Hre.
    iIntros "#Hib #Hi0 #Hi1 #Hi2 #Hi3 #Hi4 #Hi5 #Hi6 #Hcode Hstr Hws Hrun Hcont".
    assert (Ebg : (mword_of_int (q + 24) : mword 64)
                  = add_vec (mword_of_int q)
                      (sign_extend' 64 (mword_of_int 24 : mword 13))).
    { assert (E : (sign_extend' 64 (mword_of_int 24 : mword 13) : mword 64)
                  = mword_of_int 24) by (apply bv_eq; vm_compute; reflexivity).
      rewrite E moi_add. f_equal; lia. }
    destruct (Nat.eq_dec j len) as [ Hend | Hne ].
    { (* the cursor is already at [es]: the scan is skipped entirely *)
      assert (Htk : true = uv_btaken BGEU (mc !!! Regidx s1_idx)
                             (mc !!! Regidx re)).
      { cbn [uv_btaken]. rewrite Hs1 Hre Hend.
        rewrite (moi_ge_u (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
        symmetry. apply Z.geb_le. lia. }
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int q)
                (mword_of_int 24 : mword 13) re s1_idx BGEU true
                (mword_of_int (q + 24)) (2 + nn)
                Htk Ebg ltac:(intros _; exact Hal24)
                with "Hib Hrun").
      iIntros (h1) "Hrun".
      iApply ("Hcont" with "Hstr Hws [] [] Hrun").
      - iPureIntro. intros t _ _. reflexivity.
      - iPureIntro. rewrite Hs1.
        assert (Hz : (len - j)%nat = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_skipws_zero j f). f_equal; lia. }
    (* ...otherwise the scan runs *)
    assert (Hjlt : (j < len)%nat) by lia.
    assert (Htk : false = uv_btaken BGEU (mc !!! Regidx s1_idx)
                            (mc !!! Regidx re)).
    { cbn [uv_btaken]. rewrite Hs1 Hre.
      rewrite (moi_ge_u (s0 + Z.of_nat j) (s0 + Z.of_nat len)
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int q)
              (mword_of_int 24 : mword 13) re s1_idx BGEU false
              (mword_of_int (q + 24)) (2 + nn)
              Htk Ebg ltac:(discriminate)
              with "Hib Hrun").
    rewrite (ushp_pc_step' q 4 (q + 4) ltac:(lia)). iIntros (h1) "Hrun".
    iApply (wp_kshp_ws_scan (q + 4) ji dq dw s0 len f nn
              ltac:(replace (q + 4 + 6) with (q + 10) by lia; exact Hjt)
              ltac:(replace (q + 4 + 10) with (q + 14) by lia; exact Hjr)
              ltac:(replace (q + 4 + 20) with (q + 24) by lia; exact Hal24)
              Hal4
              (len - j)%nat j h1 mc
              eq_refl Hjlt Hs0 Hs64 Hs1 Hs2 Hs3
              with "[] [] [] [] [] [] [] Hcode Hstr Hws Hrun").
    { replace (q + 4 + 0) with (q + 4) by lia. iApply "Hi0". }
    { replace (q + 4 + 4) with (q + 8) by lia. iApply "Hi1". }
    { replace (q + 4 + 6) with (q + 10) by lia. iApply "Hi2". }
    { replace (q + 4 + 10) with (q + 14) by lia. iApply "Hi3". }
    { replace (q + 4 + 12) with (q + 16) by lia. iApply "Hi4". }
    { replace (q + 4 + 14) with (q + 18) by lia. iApply "Hi5". }
    { replace (q + 4 + 18) with (q + 22) by lia. iApply "Hi6". }
    iIntros "Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    replace (q + 4 + 20) with (q + 24) by lia.
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* ---- the token-body scan, 0x400..0x41a -------------------------------- *)


  (* WHERE THE TOKEN SCAN COMES OUT.  Its two live exits are the SAME
     instruction pair -- [li s5,97 ; c.j 0x388] at 0x432 and again at 0x438,
     gcc having duplicated the tail -- so a byte that ends the token (either
     table) leaves the scan at 0x388 with the answer already in s5, and only
     running off the end of the line leaves it anywhere else (0x424, past
     the third copy of [li s5,97] at 0x420).  Folding the three stubs into
     the scan is what makes the caller's case analysis TWO arms and not
     four. *)
  Definition ushp_tok_exit (len : nat) (f : nat -> bv 8) (j : nat) : Z :=
    if bool_decide ((j + ushp_toklen (len - j) j f) < len)%nat
    then 0x388 else 0x424.

  (* [while(s < es && !strchr(whitespace, *s) && !strchr(symbols, *s)) s++].
     TWO calls a turn, so the register promise is thinner than the
     whitespace scan's by one more register: s5 holds [&symbols] through
     the loop and the ANSWER after it. *)
  Lemma wp_kshp_tok_scan (dq dw dv : dfrac) (s0 : Z) (len : nat)
      (f : nat -> bv 8) (nn : nat) :
    forall (r j : nat) (h : CpuId) (mc : regfile),
    (len - j = r)%nat -> (j < len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s3_idx = mword_of_int ushp_whitespace ->
    mc !!! Regidx s5_idx = mword_of_int ushp_symbols ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x400) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s5_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_toklen (len - j) j f)) ⌝ -∗
         ⌜ mc' !!! Regidx s5_idx = mword_of_int 97 ⌝ -∗
         urun γt γd γs γfd h' mc'
           (mword_of_int (ushp_tok_exit len f j)) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros r. induction r as [| r IH ];
      intros j h mc Hr Hj Hs0 Hs64 Hs1 Hs2 Hs3 Hs5;
      iIntros "#Hcode Hstr Hws Hsy Hrun Hcont"; [ lia | ].
    (* ---- 0x400  lbu a1,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f j Hj with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs γfd h mc (mword_of_int 0x400)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat j) (f j) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat j)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_400 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x400 4). iIntros (h1) "Hrun".
    set (m1 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                     : mword 64)]> mc).
    assert (Hm1 : forall t : mword 5, Regidx t <> Regidx a1_idx ->
                    m1 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; exact (upd_ne mc (Regidx a1_idx) (Regidx t) _ Ht)).
    assert (Ha1_1 : m1 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (upd_eq mc (Regidx a1_idx)
                 (regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f j)). }
    (* ---- 0x404  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 m1 (mword_of_int 0x404) a0_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)) Hs3;
                    symmetry; exact (ushp_mv_val ushp_whitespace))
              with "[] Hrun").
    { iApply (uis_shp_404 with "Hcode"). }
    rewrite (ushp_pc_step 0x404 2). iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m1).
    assert (Hm2 : forall t : mword 5, Regidx t <> Regidx a0_idx ->
                    m2 !!! Regidx t = m1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m1 (Regidx a0_idx) (Regidx t) _ Ht)).
    (* ---- 0x406  jal a82 <strchr> -- the WHITESPACE table ---- *)
    iApply (wp_uk_jal γt γd γs γfd h2 m2 (mword_of_int 0x406)
              (mword_of_int 1660 : mword 21) ra_idx
              (mword_of_int 0xa82) (mword_of_int 0x40a) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_406 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x40a : mword 64)]> m2).
    assert (Hm3 : forall t : mword 5, Regidx t <> Regidx ra_idx ->
                    m3 !!! Regidx t = m2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m2 (Regidx ra_idx) (Regidx t) _ Ht)).
    assert (Ha0_3 : m3 !!! Regidx a0_idx = mword_of_int ushp_whitespace).
    { rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m1 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ushp_whitespace : mword 64))). }
    assert (Ha1_3 : m3 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)). exact Ha1_1. }
    assert (Eret3 : ret_pc (m3 !!! Regidx ra_idx) = mword_of_int 0x40a).
    { rewrite (upd_eq m2 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x40a : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hcs3 : forall t : mword 5, ucallee_saved_idx t = true ->
                     m3 !!! Regidx t = mc !!! Regidx t).
    { intros t Ht.
      rewrite (Hm3 t (ushp_cs_ne t ra_idx Ht ltac:(vm_compute; reflexivity))).
      rewrite (Hm2 t (ushp_cs_ne t a0_idx Ht ltac:(vm_compute; reflexivity))).
      exact (Hm1 t (ushp_cs_ne t a1_idx Ht ltac:(vm_compute; reflexivity))). }
    rewrite <- shpp_strchr.
    iApply (wp_kshp_strchr h3 m3 false dw ushp_whitespace 5 ushp_ws_f (f j) nn
              Ha0_3 Ha1_3 ltac:(unfold ushp_whitespace; lia)
              ltac:(unfold ushp_whitespace, Z64; lia)
              with "Hcode Hws Hrun").
    iIntros "Hws" (h4 m4) "%Hcs34 %Ha0_4 Hrun".
    rewrite Eret3.
    assert (Hcs4 : forall t : mword 5, ucallee_saved_idx t = true ->
                     m4 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; rewrite (Hcs34 t Ht); exact (Hcs3 t Ht)).
    assert (Hs1_4 : m4 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j))
      by (rewrite (Hcs4 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (Hs2_4 : m4 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hcs4 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2).
    assert (Hs3_4 : m4 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hcs4 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3).
    assert (Hs5_4 : m4 !!! Regidx s5_idx = mword_of_int ushp_symbols)
      by (rewrite (Hcs4 s5_idx ltac:(vm_compute; reflexivity)); exact Hs5).
    (* ---- 0x40a  c.bnez a0,0x438 -- a whitespace byte ENDS the token ---- *)
    destruct (ushp_is_ws (f j)) eqn:Ews.
    { destruct (ushp_ws_chr_nz (f j) Ews) as [ k [ Hk Hchr ] ].
      assert (Htk : true = neq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 Hchr.
        rewrite (moi_neq_zero (ushp_whitespace + Z.of_nat k)
                   ltac:(unfold ushp_whitespace, Z64; lia)).
        assert (Hz : (ushp_whitespace + Z.of_nat k =? 0) = false)
          by (apply Z.eqb_neq; unfold ushp_whitespace; lia).
        rewrite Hz. reflexivity. }
      iApply (wp_uk_cbnez γt γd γs γfd h4 m4 (mword_of_int 0x40a)
                (mword_of_int 23 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x438) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_40a with "Hcode"). }
      iIntros (h5) "Hrun".
      (* ---- 0x438  li s5,97 ---- *)
      iApply (wp_uk_li γt γd γs γfd h5 m4 (mword_of_int 0x438)
                (mword_of_int 97 : mword 12) s5_idx (mword_of_int 97) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_438 with "Hcode"). }
      rewrite (ushp_pc_step 0x438 4). iIntros (h6) "Hrun".
      (* ---- 0x43c  c.j 0x388 ---- *)
      iApply (wp_uk_cj γt γd γs γfd h6
                (<[Regidx s5_idx
                   := regval_into_reg (mword_of_int 97 : mword 64)]> m4)
                (mword_of_int 0x43c) (mword_of_int 1958 : mword 11)
                (mword_of_int 0x388) (2 + nn)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_43c with "Hcode"). }
      iIntros (h7) "Hrun".
      assert (Etl : ushp_toklen (len - j) j f = 0%nat)
        by (apply (ushp_toklen_stop (len - j) j f);
            rewrite Ews; reflexivity).
      assert (Eex : ushp_tok_exit len f j = 0x388).
      { unfold ushp_tok_exit. rewrite Etl.
        rewrite (bool_decide_eq_true_2 ((j + 0)%nat < len)%nat
                   ltac:(lia)). reflexivity. }
      rewrite <- Eex.
      iApply ("Hcont" with "Hstr Hws Hsy [] [] [] Hrun").
      - iPureIntro. intros t Ht _ Hts5.
        rewrite (upd_ne m4 (Regidx s5_idx) (Regidx t) _ Hts5).
        exact (Hcs4 t Ht).
      - iPureIntro.
        rewrite (upd_ne m4 (Regidx s5_idx) (Regidx s1_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite Hs1_4 Etl. f_equal; lia.
      - iPureIntro.
        exact (upd_eq m4 (Regidx s5_idx)
                 (regval_into_reg (mword_of_int 97 : mword 64))). }
    (* not whitespace: the second table is consulted *)
    assert (Htk : false = neq_vec (m4 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0_4 (ushp_ws_chr_z (f j) Ews).
      rewrite (moi_neq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    iApply (wp_uk_cbnez γt γd γs γfd h4 m4 (mword_of_int 0x40a)
              (mword_of_int 23 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x438) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_40a with "Hcode"). }
    rewrite (ushp_pc_step 0x40a 2). iIntros (h5) "Hrun".
    (* ---- 0x40c  lbu a1,0(s1) -- the same byte, read again ---- *)
    iDestruct (ustr_byte γd dq s0 len f j Hj with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs γfd h5 m4 (mword_of_int 0x40c)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat j) (f j) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1_4 (uint_moi (s0 + Z.of_nat j)
                                    ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_40c with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x40c 4). iIntros (h6) "Hrun".
    set (n1 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                     : mword 64)]> m4).
    assert (Hn1 : forall t : mword 5, Regidx t <> Regidx a1_idx ->
                    n1 !!! Regidx t = m4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m4 (Regidx a1_idx) (Regidx t) _ Ht)).
    assert (Hb1_1 : n1 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (upd_eq m4 (Regidx a1_idx)
                 (regval_into_reg (zero_extend' 64 ((f j) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f j)). }
    (* ---- 0x410  c.mv a0,s5 -- the SYMBOLS table ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h6 n1 (mword_of_int 0x410) a0_idx s5_idx
              (mword_of_int ushp_symbols) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hn1 s5_idx ltac:(vm_compute; discriminate))
                      Hs5_4; symmetry; exact (ushp_mv_val ushp_symbols))
              with "[] Hrun").
    { iApply (uis_shp_410 with "Hcode"). }
    rewrite (ushp_pc_step 0x410 2). iIntros (h7) "Hrun".
    set (n2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ushp_symbols
                                     : mword 64)]> n1).
    assert (Hn2 : forall t : mword 5, Regidx t <> Regidx a0_idx ->
                    n2 !!! Regidx t = n1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n1 (Regidx a0_idx) (Regidx t) _ Ht)).
    (* ---- 0x412  jal a82 <strchr> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h7 n2 (mword_of_int 0x412)
              (mword_of_int 1648 : mword 21) ra_idx
              (mword_of_int 0xa82) (mword_of_int 0x416) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_412 with "Hcode"). }
    iIntros (h8) "Hrun".
    set (n3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x416 : mword 64)]> n2).
    assert (Hn3 : forall t : mword 5, Regidx t <> Regidx ra_idx ->
                    n3 !!! Regidx t = n2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n2 (Regidx ra_idx) (Regidx t) _ Ht)).
    assert (Hc0_3 : n3 !!! Regidx a0_idx = mword_of_int ushp_symbols).
    { rewrite (Hn3 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n1 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ushp_symbols : mword 64))). }
    assert (Hc1_3 : n3 !!! Regidx a1_idx = mword_of_int (bv_unsigned (f j))).
    { rewrite (Hn3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn2 a1_idx ltac:(vm_compute; discriminate)). exact Hb1_1. }
    assert (Eret7 : ret_pc (n3 !!! Regidx ra_idx) = mword_of_int 0x416).
    { rewrite (upd_eq n2 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x416 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hcs7 : forall t : mword 5, ucallee_saved_idx t = true ->
                     n3 !!! Regidx t = m4 !!! Regidx t).
    { intros t Ht.
      rewrite (Hn3 t (ushp_cs_ne t ra_idx Ht ltac:(vm_compute; reflexivity))).
      rewrite (Hn2 t (ushp_cs_ne t a0_idx Ht ltac:(vm_compute; reflexivity))).
      exact (Hn1 t (ushp_cs_ne t a1_idx Ht ltac:(vm_compute; reflexivity))). }
    rewrite <- shpp_strchr.
    iApply (wp_kshp_strchr h8 n3 false dv ushp_symbols 7 ushp_sym_f (f j) nn
              Hc0_3 Hc1_3 ltac:(unfold ushp_symbols; lia)
              ltac:(unfold ushp_symbols, Z64; lia)
              with "Hcode Hsy Hrun").
    iIntros "Hsy" (h9 n4) "%Hcs78 %Hc0_4 Hrun".
    rewrite Eret7.
    assert (Hcs8 : forall t : mword 5, ucallee_saved_idx t = true ->
                     n4 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; rewrite (Hcs78 t Ht) (Hcs7 t Ht); exact (Hcs4 t Ht)).
    assert (Hs1_8 : n4 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j))
      by (rewrite (Hcs8 s1_idx ltac:(vm_compute; reflexivity)); exact Hs1).
    assert (Hs2_8 : n4 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hcs8 s2_idx ltac:(vm_compute; reflexivity)); exact Hs2).
    assert (Hs3_8 : n4 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hcs8 s3_idx ltac:(vm_compute; reflexivity)); exact Hs3).
    assert (Hs5_8 : n4 !!! Regidx s5_idx = mword_of_int ushp_symbols)
      by (rewrite (Hcs8 s5_idx ltac:(vm_compute; reflexivity)); exact Hs5).
    (* ---- 0x416  c.bnez a0,0x432 -- a symbol byte ENDS the token too ---- *)
    destruct (ushp_is_sym (f j)) eqn:Esy.
    { destruct (ushp_sym_chr_nz (f j) Esy) as [ k [ Hk Hchr ] ].
      assert (Htk2 : true = neq_vec (n4 !!! Regidx a0_idx) zero_reg).
      { rewrite Hc0_4 Hchr.
        rewrite (moi_neq_zero (ushp_symbols + Z.of_nat k)
                   ltac:(unfold ushp_symbols, Z64; lia)).
        assert (Hz : (ushp_symbols + Z.of_nat k =? 0) = false)
          by (apply Z.eqb_neq; unfold ushp_symbols; lia).
        rewrite Hz. reflexivity. }
      iApply (wp_uk_cbnez γt γd γs γfd h9 n4 (mword_of_int 0x416)
                (mword_of_int 14 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x432) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_416 with "Hcode"). }
      iIntros (h10) "Hrun".
      (* ---- 0x432  li s5,97 ---- *)
      iApply (wp_uk_li γt γd γs γfd h10 n4 (mword_of_int 0x432)
                (mword_of_int 97 : mword 12) s5_idx (mword_of_int 97) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_432 with "Hcode"). }
      rewrite (ushp_pc_step 0x432 4). iIntros (h11) "Hrun".
      (* ---- 0x436  c.j 0x388 ---- *)
      iApply (wp_uk_cj γt γd γs γfd h11
                (<[Regidx s5_idx
                   := regval_into_reg (mword_of_int 97 : mword 64)]> n4)
                (mword_of_int 0x436) (mword_of_int 1961 : mword 11)
                (mword_of_int 0x388) (2 + nn)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_436 with "Hcode"). }
      iIntros (h12) "Hrun".
      assert (Etl : ushp_toklen (len - j) j f = 0%nat)
        by (apply (ushp_toklen_stop (len - j) j f);
            rewrite Ews Esy; reflexivity).
      assert (Eex : ushp_tok_exit len f j = 0x388).
      { unfold ushp_tok_exit. rewrite Etl.
        rewrite (bool_decide_eq_true_2 ((j + 0)%nat < len)%nat
                   ltac:(lia)). reflexivity. }
      rewrite <- Eex.
      iApply ("Hcont" with "Hstr Hws Hsy [] [] [] Hrun").
      - iPureIntro. intros t Ht _ Hts5.
        rewrite (upd_ne n4 (Regidx s5_idx) (Regidx t) _ Hts5).
        exact (Hcs8 t Ht).
      - iPureIntro.
        rewrite (upd_ne n4 (Regidx s5_idx) (Regidx s1_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite Hs1_8 Etl. f_equal; lia.
      - iPureIntro.
        exact (upd_eq n4 (Regidx s5_idx)
                 (regval_into_reg (mword_of_int 97 : mword 64))). }
    (* neither table: the byte is IN the token and the cursor advances *)
    assert (Hnn : ushp_is_ws (f j) || ushp_is_sym (f j) = false)
      by (rewrite Ews Esy; reflexivity).
    assert (Htk2 : false = neq_vec (n4 !!! Regidx a0_idx) zero_reg).
    { rewrite Hc0_4 (ushp_sym_chr_z (f j) Esy).
      rewrite (moi_neq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
    iApply (wp_uk_cbnez γt γd γs γfd h9 n4 (mword_of_int 0x416)
              (mword_of_int 14 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x432) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_416 with "Hcode"). }
    rewrite (ushp_pc_step 0x416 2). iIntros (h10) "Hrun".
    (* ---- 0x418  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h10 n4 (mword_of_int 0x418)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S j))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_8 E1 moi_add;
                    replace (s0 + Z.of_nat (S j)) with (s0 + Z.of_nat j + 1)
                      by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_418 with "Hcode"). }
    rewrite (ushp_pc_step 0x418 2). iIntros (h11) "Hrun".
    set (n5 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat (S j))
                                     : mword 64)]> n4).
    assert (Hn5 : forall t : mword 5, Regidx t <> Regidx s1_idx ->
                    n5 !!! Regidx t = n4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n4 (Regidx s1_idx) (Regidx t) _ Ht)).
    assert (Hs1_5 : n5 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat (S j)))
      by exact (upd_eq n4 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (s0 + Z.of_nat (S j))
                                    : mword 64))).
    assert (Hs2_5 : n5 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hn5 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_8).
    assert (Hs3_5 : n5 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hn5 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_8).
    assert (Hs5_5 : n5 !!! Regidx s5_idx = mword_of_int ushp_symbols)
      by (rewrite (Hn5 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_8).
    (* ---- 0x41a  bne s2,s1,0x400 ---- *)
    destruct (Nat.eq_dec (S j) len) as [ Hend | Hend ].
    { (* the token ran to [es] *)
      assert (Htk3 : false = uv_btaken BNE (n5 !!! Regidx s2_idx)
                               (n5 !!! Regidx s1_idx)).
      { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5 Hend.
        rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(lia) ltac:(lia)).
        rewrite Z.eqb_refl. reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h11 n5 (mword_of_int 0x41a)
                (mword_of_int 8166 : mword 13) s1_idx s2_idx BNE false
                (mword_of_int 0x400) (2 + nn)
                Htk3
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_41a with "Hcode"). }
      rewrite (ushp_pc_step 0x41a 4). iIntros (h12) "Hrun".
      (* ---- 0x41e  c.mv s1,s2 ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h12 n5 (mword_of_int 0x41e)
                s1_idx s2_idx (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_5; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_41e with "Hcode"). }
      rewrite (ushp_pc_step 0x41e 2). iIntros (h13) "Hrun".
      set (n6 := <[Regidx s1_idx
                   := regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                       : mword 64)]> n5).
      (* ---- 0x420  li s5,97 ---- *)
      iApply (wp_uk_li γt γd γs γfd h13 n6 (mword_of_int 0x420)
                (mword_of_int 97 : mword 12) s5_idx (mword_of_int 97) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_420 with "Hcode"). }
      rewrite (ushp_pc_step' 0x420 4 0x424 ltac:(reflexivity)).
      iIntros (h14) "Hrun".
      assert (Etl : ushp_toklen (len - j) j f = 1%nat).
      { rewrite Hr (ushp_toklen_step r j f Hnn).
        assert (Hz : r = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_toklen_zero (S j) f). reflexivity. }
      assert (Eex : ushp_tok_exit len f j = 0x424).
      { unfold ushp_tok_exit. rewrite Etl.
        rewrite (bool_decide_eq_false_2 ((j + 1)%nat < len)%nat
                   ltac:(lia)). reflexivity. }
      rewrite <- Eex.
      iApply ("Hcont" with "Hstr Hws Hsy [] [] [] Hrun").
      - iPureIntro. intros t Ht Hts1 Hts5.
        rewrite (upd_ne n6 (Regidx s5_idx) (Regidx t) _ Hts5).
        rewrite /n6 (upd_ne n5 (Regidx s1_idx) (Regidx t) _ Hts1).
        rewrite (Hn5 t Hts1). exact (Hcs8 t Ht).
      - iPureIntro.
        rewrite (upd_ne n6 (Regidx s5_idx) (Regidx s1_idx) _
                   ltac:(vm_compute; discriminate)).
        rewrite /n6 (upd_eq n5 (Regidx s1_idx)
                       (regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                         : mword 64))).
        rewrite Etl.
        assert (Ee : (s0 + Z.of_nat len) = (s0 + Z.of_nat (j + 1))) by lia.
        rewrite Ee. reflexivity.
      - iPureIntro.
        exact (upd_eq n6 (Regidx s5_idx)
                 (regval_into_reg (mword_of_int 97 : mword 64))). }
    (* ...or the loop goes round *)
    assert (Hj1 : (S j < len)%nat) by lia.
    assert (Htk3 : true = uv_btaken BNE (n5 !!! Regidx s2_idx)
                            (n5 !!! Regidx s1_idx)).
    { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5.
      rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat (S j))
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      assert (Hne2 : (s0 + Z.of_nat len =? s0 + Z.of_nat (S j)) = false)
        by (apply Z.eqb_neq; lia).
      rewrite Hne2. reflexivity. }
    iApply (wp_uk_btype γt γd γs γfd h11 n5 (mword_of_int 0x41a)
              (mword_of_int 8166 : mword 13) s1_idx s2_idx BNE true
              (mword_of_int 0x400) (2 + nn)
              Htk3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_41a with "Hcode"). }
    iIntros (h12) "Hrun".
    assert (Eex : ushp_tok_exit len f j = ushp_tok_exit len f (S j)).
    { unfold ushp_tok_exit. rewrite Hr (ushp_toklen_step r j f Hnn).
      assert (Er : (len - S j)%nat = r) by lia. rewrite Er.
      replace ((j + S (ushp_toklen r (S j) f))%nat)
        with ((S j + ushp_toklen r (S j) f)%nat) by lia.
      reflexivity. }
    rewrite Eex.
    iApply (IH (S j) h12 n5 ltac:(lia) Hj1 Hs0 Hs64 Hs1_5 Hs2_5 Hs3_5 Hs5_5
              with "Hcode Hstr Hws Hsy Hrun").
    iIntros "Hstr Hws Hsy" (h13 mc') "%Hpres %Hret %Hans Hrun".
    iApply ("Hcont" with "Hstr Hws Hsy [] [] [] Hrun").
    - iPureIntro. intros t Ht Hts1 Hts5.
      rewrite (Hpres t Ht Hts1 Hts5) (Hn5 t Hts1). exact (Hcs8 t Ht).
    - iPureIntro. rewrite Hret Hr (ushp_toklen_step r j f Hnn).
      assert (Er : (len - S j)%nat = r) by lia. rewrite Er.
      f_equal; lia.
    - iPureIntro. exact Hans.
  Qed.

  (* ---- the tail: the [*eq] store, the trailing scan, the epilogue ------- *)

  (* AN OPTIONAL OUT PARAMETER.  gettoken is called BOTH ways -- parseexec
     passes [&q, &eq] and parseredirs/parsepipe/parseline pass [0, 0] -- so
     the cell is a disjunction, not a [uword], and the address hygiene rides
     INSIDE it rather than as a premise a null caller could not meet. *)
  Definition ushp_cell (p : Z) (v : mword 64) : iProp Σ :=
    (⌜ p = 0 ⌝ ∨
     (⌜ 0 < p /\ p mod 8 = 0 /\ p + 8 < Z64 ⌝ ∗ uword γd p v))%I.

  (* THE TRAILING WHITESPACE SCAN, 0x390..0x3ae, with its table setup.
     [s3] is reloaded with [&whitespace] here even though it already holds
     it -- gcc rematerialises the address rather than keeping it live across
     the switch -- so s3 is written and drops out of the register promise. *)
  Lemma wp_kshp_gtk_ws2 (dq dw : dfrac) (s0 : Z) (len j : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (j <= len)%nat -> 0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x390) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s3_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x3b0) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjle Hs0 Hs64 Hs1 Hs2.
    iIntros "#Hcode Hstr Hws Hrun Hcont".
    (* ---- 0x390  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h mc (mword_of_int 0x390)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x2390)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_390 with "Hcode"). }
    rewrite (ushp_pc_step 0x390 4). iIntros (h1) "Hrun".
    set (m1 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x2390 : mword 64)]> mc).
    assert (Hm1 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m1 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; exact (upd_ne mc (Regidx s3_idx) (Regidx t) _ Ht)).
    (* ---- 0x394  addi s3,s3,-904  -- s3 = &whitespace ---- *)
    iApply (wp_uk_addi γt γd γs γfd h1 m1 (mword_of_int 0x394)
              (mword_of_int 3192 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mc (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x2390
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_394 with "Hcode"). }
    rewrite (ushp_pc_step 0x394 4). iIntros (h2) "Hrun".
    set (m2 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m1).
    assert (Hm2 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m2 !!! Regidx t = m1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m1 (Regidx s3_idx) (Regidx t) _ Ht)).
    assert (Hs1_2 : m2 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j))
      by (rewrite (Hm2 s1_idx ltac:(vm_compute; discriminate))
                  (Hm1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1).
    assert (Hs2_2 : m2 !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hm2 s2_idx ltac:(vm_compute; discriminate))
                  (Hm1 s2_idx ltac:(vm_compute; discriminate)); exact Hs2).
    assert (Hs3_2 : m2 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq m1 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    (* ---- 0x398..0x3ae  the entry test and the scan ---- *)
    iApply (wp_kshp_ws_enter 0x398 s2_idx (mword_of_int 1760 : mword 21)
              dq dw s0 len j f nn h2 m2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Hjle Hs0 Hs64 Hs1_2 Hs2_2 Hs3_2 Hs2_2
              with "[] [] [] [] [] [] [] [] Hcode Hstr Hws Hrun").
    { iApply (uis_shp_398 with "Hcode"). }
    { iApply (uis_shp_39c with "Hcode"). }
    { iApply (uis_shp_3a0 with "Hcode"). }
    { iApply (uis_shp_3a2 with "Hcode"). }
    { iApply (uis_shp_3a6 with "Hcode"). }
    { iApply (uis_shp_3a8 with "Hcode"). }
    { iApply (uis_shp_3aa with "Hcode"). }
    { iApply (uis_shp_3ae with "Hcode"). }
    iIntros "Hstr Hws" (h3 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. intros t Ht Hts1 Hts3.
      rewrite (Hpres t Ht Hts1) (Hm2 t Hts3). exact (Hm1 t Hts3).
    - iPureIntro. exact Hret.
  Qed.

  (* [*eq = s], then the trailing scan.  0x38c is reached TWO ways -- from
     0x388's [beqz s6] falling through, and from 0x424's [bnez s6] being
     taken -- so it is stated once. *)
  Lemma wp_kshp_gtk_eqst (dq dw : dfrac) (s0 eqp : Z) (len j : nat)
      (f : nat -> bv 8) (v0 : mword 64) (nn : nat)
      (h : CpuId) (mc : regfile) :
    (j <= len)%nat -> 0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < eqp -> eqp mod 8 = 0 -> eqp + 8 < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int eqp ->
    shp_code γt -∗
    uword γd eqp v0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x38c) (2 + nn) -∗
    (uword γd eqp (mword_of_int (s0 + Z.of_nat j)) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s3_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x3b0) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjle Hs0 Hs64 Heq0 Heq8 Heqsz Hs1 Hs2 Hs6.
    iIntros "#Hcode Hcell Hstr Hws Hrun Hcont".
    (* ---- 0x38c  sd s1,0(s6)  --  *eq = s ---- *)
    iApply (wp_uk_sd γt γd γs γfd h mc (mword_of_int 0x38c)
              (mword_of_int 0 : mword 12) s6_idx s1_idx eqp v0 (2 + nn)
              ltac:(rewrite Hs6 (uint_moi eqp ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Heq8
              with "[] Hcell Hrun").
    { iApply (uis_shp_38c with "Hcode"). }
    iIntros "Hcell". rewrite Hs1.
    rewrite (ushp_pc_step 0x38c 4). iIntros (h1) "Hrun".
    iApply (wp_kshp_gtk_ws2 dq dw s0 len j f nn h1 mc
              Hjle Hs0 Hs64 Hs1 Hs2 with "Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hcell Hstr Hws [] [] Hrun").
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* 0x388: [if(eq) *eq = s], the NUL and symbol-free arms' way in. *)
  Lemma wp_kshp_gtk_388 (dq dw : dfrac) (s0 eqp : Z) (len j : nat)
      (f : nat -> bv 8) (v0 : mword 64) (nn : nat)
      (h : CpuId) (mc : regfile) :
    (j <= len)%nat -> 0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int eqp ->
    shp_code γt -∗
    ushp_cell eqp v0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x388) (2 + nn) -∗
    (ushp_cell eqp (mword_of_int (s0 + Z.of_nat j)) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s3_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x3b0) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjle Hs0 Hs64 Hs1 Hs2 Hs6.
    iIntros "#Hcode Hcell Hstr Hws Hrun Hcont".
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    iDestruct "Hcell" as "[ %Hnull | [%Hrng Hw] ]".
    { (* eq == 0: the store is skipped *)
      assert (Htk : true = uv_btaken BEQ (mc !!! Regidx s6_idx)
                             (mc !!! Regidx x0_idx)).
      { cbn [uv_btaken]. rewrite Hs6 Hx0 Hnull.
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x388)
                (mword_of_int 8 : mword 13) x0_idx s6_idx BEQ true
                (mword_of_int 0x390) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_388 with "Hcode"). }
      iIntros (h1) "Hrun".
      iApply (wp_kshp_gtk_ws2 dq dw s0 len j f nn h1 mc
                Hjle Hs0 Hs64 Hs1 Hs2 with "Hcode Hstr Hws Hrun").
      iIntros "Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
      iApply ("Hcont" with "[] Hstr Hws [] [] Hrun").
      - iLeft. iPureIntro. exact Hnull.
      - iPureIntro. exact Hpres.
      - iPureIntro. exact Hret. }
    (* eq != 0: the store runs *)
    destruct Hrng as [ Heq0 [ Heq8 Heqsz ] ].
    assert (Htk : false = uv_btaken BEQ (mc !!! Regidx s6_idx)
                            (mc !!! Regidx x0_idx)).
    { cbn [uv_btaken]. rewrite Hs6 Hx0.
      rewrite (moi_eq_zero eqp ltac:(unfold Z64 in *; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x388)
              (mword_of_int 8 : mword 13) x0_idx s6_idx BEQ false
              (mword_of_int 0x390) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_388 with "Hcode"). }
    rewrite (ushp_pc_step 0x388 4). iIntros (h1) "Hrun".
    iApply (wp_kshp_gtk_eqst dq dw s0 eqp len j f v0 nn h1 mc
              Hjle Hs0 Hs64 Heq0 Heq8 Heqsz Hs1 Hs2 Hs6
              with "Hcode Hw Hstr Hws Hrun").
    iIntros "Hw Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "[Hw] Hstr Hws [] [] Hrun").
    - iRight. iSplitR; [ iPureIntro; split; [ exact Heq0 | split; assumption ]
                       | iExact "Hw" ].
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* 0x424: the SAME [if(eq)] test, at the copy the default arm reaches when
     the token ran to [es].  The cursor is already at the end there, so the
     [c.j 0x3b0] that skips the trailing scan skips a no-op -- which is why
     this lemma is stated at [j = len] and lands on the same postcondition. *)
  Lemma wp_kshp_gtk_424 (dq dw : dfrac) (s0 eqp : Z) (len : nat)
      (f : nat -> bv 8) (v0 : mword 64) (nn : nat)
      (h : CpuId) (mc : regfile) :
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int eqp ->
    shp_code γt -∗
    ushp_cell eqp v0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x424) (2 + nn) -∗
    (ushp_cell eqp (mword_of_int (s0 + Z.of_nat len)) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, ucallee_saved_idx t = true ->
             Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s3_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat len) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x3b0) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hs0 Hs64 Hs1 Hs2 Hs6.
    iIntros "#Hcode Hcell Hstr Hws Hrun Hcont".
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    assert (Etl : (s0 + Z.of_nat (len + ushp_skipws (len - len) len f))
                  = (s0 + Z.of_nat len)).
    { assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
      rewrite (ushp_skipws_zero len f). f_equal. lia. }
    iDestruct "Hcell" as "[ %Hnull | [%Hrng Hw] ]".
    { (* eq == 0: straight to 0x3b0 ---- *)
      assert (Htk : false = uv_btaken BNE (mc !!! Regidx s6_idx)
                              (mc !!! Regidx x0_idx)).
      { cbn [uv_btaken]. rewrite Hs6 Hx0 Hnull.
        rewrite (moi_neq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x424)
                (mword_of_int 8040 : mword 13) x0_idx s6_idx BNE false
                (mword_of_int 0x38c) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_424 with "Hcode"). }
      rewrite (ushp_pc_step 0x424 4). iIntros (h1) "Hrun".
      (* ---- 0x428  c.j 0x3b0 ---- *)
      iApply (wp_uk_cj γt γd γs γfd h1 mc (mword_of_int 0x428)
                (mword_of_int 1988 : mword 11) (mword_of_int 0x3b0) (2 + nn)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_428 with "Hcode"). }
      iIntros (h2) "Hrun".
      iApply ("Hcont" with "[] Hstr Hws [] [] Hrun").
      - iLeft. iPureIntro. exact Hnull.
      - iPureIntro. intros t _ _ _. reflexivity.
      - iPureIntro. exact Hs1. }
    (* eq != 0: the store runs, then the (empty) trailing scan *)
    destruct Hrng as [ Heq0 [ Heq8 Heqsz ] ].
    assert (Htk : true = uv_btaken BNE (mc !!! Regidx s6_idx)
                           (mc !!! Regidx x0_idx)).
    { cbn [uv_btaken]. rewrite Hs6 Hx0.
      rewrite (moi_neq_zero eqp ltac:(unfold Z64 in *; lia)).
      assert (Hz : (eqp =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite Hz. reflexivity. }
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x424)
              (mword_of_int 8040 : mword 13) x0_idx s6_idx BNE true
              (mword_of_int 0x38c) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_424 with "Hcode"). }
    iIntros (h1) "Hrun".
    iApply (wp_kshp_gtk_eqst dq dw s0 eqp len len f v0 nn h1 mc
              ltac:(lia) Hs0 Hs64 Heq0 Heq8 Heqsz Hs1 Hs2 Hs6
              with "Hcode Hw Hstr Hws Hrun").
    iIntros "Hw Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    rewrite Etl in Hret.
    iApply ("Hcont" with "[Hw] Hstr Hws [] [] Hrun").
    - iRight. iSplitR; [ iPureIntro; split; [ exact Heq0 | split; assumption ]
                       | iExact "Hw" ].
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* gettoken's epilogue, 0x3b6..0x3c8: the EIGHT restores, the pop and the
     [c.jr].  [wp_kshp_peek_epi]'s twin at k = 8, j = 8 -- so the frame has
     no locals at all and [ushp_frame_join] puts it back at [n = 0]. *)
  Lemma wp_kshp_gtk_epi (sp0 spl : mword 64) (vals : nat -> mword 64)
      (nn : nat) :
    forall (h : CpuId) (me : regfile),
    uint sp0 mod 8 = 0 -> 64 <= uint sp0 -> uint sp0 < Z64 ->
    uint spl = uint sp0 - 64 ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 8)) ->
    shp_code γt -∗
    ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 7 : mword 6);
                       (s0_idx, mword_of_int 6 : mword 6);
                       (s1_idx, mword_of_int 5 : mword 6);
                       (s2_idx, mword_of_int 4 : mword 6);
                       (s3_idx, mword_of_int 3 : mword 6);
                       (s4_idx, mword_of_int 2 : mword 6);
                       (s5_idx, mword_of_int 1 : mword 6);
                       (s6_idx, mword_of_int 0 : mword 6)],
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd spl 0 -∗
    urun γt γd γs γfd h me (mword_of_int 0x3b6) (2 + nn) -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx csp_rs1 := regval_into_reg sp0]>
            (ushp_spillback [(ra_idx, mword_of_int 7 : mword 6);
                             (s0_idx, mword_of_int 6 : mword 6);
                             (s1_idx, mword_of_int 5 : mword 6);
                             (s2_idx, mword_of_int 4 : mword 6);
                             (s3_idx, mword_of_int 3 : mword 6);
                             (s4_idx, mword_of_int 2 : mword 6);
                             (s5_idx, mword_of_int 1 : mword 6);
                             (s6_idx, mword_of_int 0 : mword 6)] vals me))
         (ret_pc (vals 0%nat)) (8 + (2 + nn)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros h me Hal8 Hlo Hhi Hsplu Hsp.
    iIntros "#Hcode Hsl Hloc Hrun Hcont".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 8))).
    assert (Hspu : uint spn = uint sp0 - 64).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    assert (Hoff : forall (i : nat) (r : mword 5) (u : mword 6),
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6);
               (s6_idx, mword_of_int 0 : mword 6)] !! i = Some (r, u) ->
              (uint sp0 - 8 * (Z.of_nat i + 1)) = uint spn + uoff_sdsp u /\
              (uint sp0 - 8 * (Z.of_nat i + 1)) mod 8 = 0 /\
              unot_sp r /\ uint r <> 0).
    { intros i r u Hi.
      destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]]; cbn in Hi;
        try discriminate; injection Hi as Hr Hu0; subst;
        (split;
         [ rewrite Hspu; vm_compute uoff_sdsp; lia
         | split;
           [ exact (ushp_slot_al (uint sp0) _ Hal8)
           | split; [ unfold unot_sp; vm_compute; discriminate
                    | vm_compute; discriminate ] ] ]). }
    (* ---- 0x3b6..0x3c4  the eight restores ---- *)
    iApply (wp_kshp_restore spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6);
               (s6_idx, mword_of_int 0 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x3b6 | 1%nat => 0x3b8
                              | 2%nat => 0x3ba | 3%nat => 0x3bc
                              | 4%nat => 0x3be | 5%nat => 0x3c0
                              | 6%nat => 0x3c2 | 7%nat => 0x3c4
                              | _ => 0x3c6 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h me Hsp
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              Hoff
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_3b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3bc with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3be with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3c0 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3c2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_3c4 with "Hcode") | done ]. }
    iIntros "Hsl" (h1) "Hrun". cbn [length].
    set (mr := ushp_spillback
                 [(ra_idx, mword_of_int 7 : mword 6);
                  (s0_idx, mword_of_int 6 : mword 6);
                  (s1_idx, mword_of_int 5 : mword 6);
                  (s2_idx, mword_of_int 4 : mword 6);
                  (s3_idx, mword_of_int 3 : mword 6);
                  (s4_idx, mword_of_int 2 : mword 6);
                  (s5_idx, mword_of_int 1 : mword 6);
                  (s6_idx, mword_of_int 0 : mword 6)] vals me).
    assert (Hspr : mr !!! Regidx csp_rs1 = spn).
    { rewrite /mr (ushp_spillback_ne
                     [(ra_idx, mword_of_int 7 : mword 6);
                      (s0_idx, mword_of_int 6 : mword 6);
                      (s1_idx, mword_of_int 5 : mword 6);
                      (s2_idx, mword_of_int 4 : mword 6);
                      (s3_idx, mword_of_int 3 : mword 6);
                      (s4_idx, mword_of_int 2 : mword 6);
                      (s5_idx, mword_of_int 1 : mword 6);
                      (s6_idx, mword_of_int 0 : mword 6)] vals me csp_rs1
                     ltac:(intros i r u Hi;
                           destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                           cbn in Hi; try discriminate;
                           injection Hi as Hr Hu0; subst;
                           vm_compute; discriminate)).
      exact Hsp. }
    assert (Hrar : mr !!! Regidx ra_idx = vals 0%nat).
    { rewrite /mr. cbn [ushp_spillback fst].
      rewrite (upd_ne _ (Regidx s6_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s5_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s4_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s3_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s2_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq me (Regidx ra_idx) (regval_into_reg (vals 0%nat))). }
    assert (Hup : add_vec_int spn (8 * Z.of_nat 8) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos spn (8 * Z.of_nat 8) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    (* ---- 0x3c6  c.addi16sp sp,sp,64 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h1 mr (mword_of_int 0x3c6)
              (mword_of_int 4 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hsl Hloc] Hrun").
    { iApply (uis_shp_3c6 with "Hcode"). }
    { rewrite Hspr Hup.
      iApply (ushp_frame_join sp0 spl 0
                [(ra_idx, mword_of_int 7 : mword 6);
                 (s0_idx, mword_of_int 6 : mword 6);
                 (s1_idx, mword_of_int 5 : mword 6);
                 (s2_idx, mword_of_int 4 : mword 6);
                 (s3_idx, mword_of_int 3 : mword 6);
                 (s4_idx, mword_of_int 2 : mword 6);
                 (s5_idx, mword_of_int 1 : mword 6);
                 (s6_idx, mword_of_int 0 : mword 6)]
                vals ltac:(cbn [length]; lia) with "Hsl Hloc"). }
    rewrite Hspr Hup (ushp_pc_step 0x3c6 2). iIntros (h2) "Hrun".
    (* ---- 0x3c8  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h2
              (<[Regidx csp_rs1 := regval_into_reg sp0]> mr)
              (mword_of_int 0x3c8) ra_idx (ret_pc (vals 0%nat)) (8 + (2 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_ne mr (Regidx csp_rs1) (Regidx ra_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite Hrar; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3c8 with "Hcode"). }
    iIntros (h3) "Hrun". iApply ("Hcont" $! h3 with "Hrun").
  Qed.

  (* ---- the [*q] store and the switch ------------------------------------ *)

  (* 0x34e: [if(q) *q = s].  It writes NO register, so the continuation gets
     the SAME register file back -- which is what lets the switch below be
     stated at one entry state rather than two. *)
  Lemma wp_kshp_gtk_qst (s0 qp : Z) (k : nat) (v0 : mword 64)
      (nn : nat) (h : CpuId) (mc : regfile) :
    0 <= s0 -> s0 + Z.of_nat k < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k) ->
    mc !!! Regidx s5_idx = mword_of_int qp ->
    shp_code γt -∗
    ushp_cell qp v0 -∗
    urun γt γd γs γfd h mc (mword_of_int 0x34e) (2 + nn) -∗
    (ushp_cell qp (mword_of_int (s0 + Z.of_nat k)) -∗
       ∀ h' : CpuId,
         urun γt γd γs γfd h' mc (mword_of_int 0x356) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hs0 Hs64 Hs1 Hs5.
    iIntros "#Hcode Hcell Hrun Hcont".
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    iDestruct "Hcell" as "[ %Hnull | [%Hrng Hw] ]".
    { assert (Htk : true = uv_btaken BEQ (mc !!! Regidx s5_idx)
                             (mc !!! Regidx x0_idx)).
      { cbn [uv_btaken]. rewrite Hs5 Hx0 Hnull.
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x34e)
                (mword_of_int 8 : mword 13) x0_idx s5_idx BEQ true
                (mword_of_int 0x356) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_34e with "Hcode"). }
      iIntros (h1) "Hrun".
      iApply ("Hcont" with "[] Hrun"). iLeft. iPureIntro. exact Hnull. }
    destruct Hrng as [ Hq0 [ Hq8 Hqsz ] ].
    assert (Htk : false = uv_btaken BEQ (mc !!! Regidx s5_idx)
                            (mc !!! Regidx x0_idx)).
    { cbn [uv_btaken]. rewrite Hs5 Hx0.
      rewrite (moi_eq_zero qp ltac:(unfold Z64 in *; lia)).
      symmetry. apply Z.eqb_neq. lia. }
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x34e)
              (mword_of_int 8 : mword 13) x0_idx s5_idx BEQ false
              (mword_of_int 0x356) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_34e with "Hcode"). }
    rewrite (ushp_pc_step 0x34e 4). iIntros (h1) "Hrun".
    (* ---- 0x352  sd s1,0(s5)  --  *q = s ---- *)
    iApply (wp_uk_sd γt γd γs γfd h1 mc (mword_of_int 0x352)
              (mword_of_int 0 : mword 12) s5_idx s1_idx qp v0 (2 + nn)
              ltac:(rewrite Hs5 (uint_moi qp ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hq8
              with "[] Hw Hrun").
    { iApply (uis_shp_352 with "Hcode"). }
    iIntros "Hw". rewrite Hs1.
    rewrite (ushp_pc_step 0x352 4). iIntros (h2) "Hrun".
    iApply ("Hcont" with "[Hw] Hrun").
    iRight. iSplitR; [ iPureIntro; split; [ exact Hq0 | split; assumption ]
                     | iExact "Hw" ].
  Qed.

  (* gettoken's ANSWER, on a line stage 4 accepts: 'a' at a real token and 0
     at the end of the line.  The six symbol arms and the '>' / '>>' arm are
     not weakened away -- they are REFUTED at the branch, from the seven
     numeric disequalities of [ushp_nsym_bv]. *)
  Definition ushp_gettok_res (len : nat) (f : nat -> bv 8) (k : nat) : Z :=
    if bool_decide (k < len)%nat then 97 else 0.

  (* where the token ends: the maximal non-whitespace, non-symbol run *)
  Definition ushp_gettok_end (len : nat) (f : nat -> bv 8) (k : nat) : nat :=
    (k + ushp_toklen (len - k) k f)%nat.

  (* THE SWITCH, 0x356..0x386 and its two out-of-line halves 0x3ca..0x3e8.
     Under [ushp_no_symbols] the eight-arm switch has TWO live arms and the
     byte at the cursor decides which: it is NUL exactly when the cursor has
     reached [es], because a [ustr]'s body bytes are all non-NUL.  Nothing
     here moves the cursor -- s1 is untouched -- and only a4, a5 and s5 are
     written. *)
  Lemma wp_kshp_gtk_disp (dq : dfrac) (s0 : Z) (len k : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (k <= len)%nat -> ushp_no_symbols len f ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x356) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, Regidx t <> Regidx a4_idx ->
             Regidx t <> Regidx a5_idx -> Regidx t <> Regidx s5_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ (len <= k)%nat ->
             mc' !!! Regidx s5_idx = mword_of_int 0 ⌝ -∗
         urun γt γd γs γfd h' mc'
           (mword_of_int (if bool_decide (k < len)%nat then 0x3ec else 0x388))
           (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkle Hnosym Hs0 Hs64 Hs1.
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
      by (intros Hk; rewrite (Hbk Hk); exact (Hnosym k Hk)).
    (* ---- 0x356  lbu a5,0(s1) ---- *)
    iApply (wp_uk_lbu γt γd γs γfd h mc (mword_of_int 0x356)
              (mword_of_int 0 : mword 12) s1_idx a5_idx dq
              (s0 + Z.of_nat k) b (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat k)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_356 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x356 4). iIntros (h1) "Hrun".
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
    (* ---- 0x35a  sext.w s5,a5 -- [ret = *s] ---- *)
    iApply (wp_uk_addiw γt γd γs γfd h1 n1 (mword_of_int 0x35a)
              (mword_of_int 0 : mword 12) a5_idx s5_idx
              (mword_of_int (bv_unsigned b)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_1; symmetry;
                    exact (ushp_sextw_byte (bv_unsigned b) Hvb))
              with "[] Hrun").
    { iApply (uis_shp_35a with "Hcode"). }
    rewrite (ushp_pc_step 0x35a 4). iIntros (h2) "Hrun".
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
    (* ---- 0x35e  li a4,60 ---- *)
    iApply (wp_uk_li γt γd γs γfd h2 n2 (mword_of_int 0x35e)
              (mword_of_int 60 : mword 12) a4_idx (mword_of_int 60) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_35e with "Hcode"). }
    rewrite (ushp_pc_step 0x35e 4). iIntros (h3) "Hrun".
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
    (* ---- 0x362  bltu a4,a5,0x3ca -- '<' and above go out of line ---- *)
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
      iApply (wp_uk_btype γt γd γs γfd h3 n3 (mword_of_int 0x362)
                (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU true
                (mword_of_int 0x3ca) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_362 with "Hcode"). }
      iIntros (h4) "Hrun".
      (* ---- 0x3ca  li a4,62 ---- *)
      iApply (wp_uk_li γt γd γs γfd h4 n3 (mword_of_int 0x3ca)
                (mword_of_int 62 : mword 12) a4_idx (mword_of_int 62) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_3ca with "Hcode"). }
      rewrite (ushp_pc_step 0x3ca 4). iIntros (h5) "Hrun".
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
      (* ---- 0x3ce  bne a5,a4,0x3e4 -- NOT '>' ---- *)
      assert (Htk2 : true = uv_btaken BNE (n4 !!! Regidx a5_idx)
                              (n4 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha4_4 Ha5_4.
        rewrite (ushp_moi_neq (bv_unsigned b) 62 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        assert (Hq : (bv_unsigned b =? 62) = false)
          by (apply Z.eqb_neq; exact N62).
        rewrite Hq. reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h5 n4 (mword_of_int 0x3ce)
                (mword_of_int 22 : mword 13) a4_idx a5_idx BNE true
                (mword_of_int 0x3e4) (2 + nn)
                Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_3ce with "Hcode"). }
      iIntros (h6) "Hrun".
      (* ---- 0x3e4  li a4,124 ---- *)
      iApply (wp_uk_li γt γd γs γfd h6 n4 (mword_of_int 0x3e4)
                (mword_of_int 124 : mword 12) a4_idx (mword_of_int 124)
                (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_3e4 with "Hcode"). }
      rewrite (ushp_pc_step 0x3e4 4). iIntros (h7) "Hrun".
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
      (* ---- 0x3e8  beq a5,a4,0x386 -- NOT '|', so the DEFAULT arm ---- *)
      assert (Htk3 : false = uv_btaken BEQ (n5 !!! Regidx a5_idx)
                               (n5 !!! Regidx a4_idx)).
      { cbn [uv_btaken]. rewrite Ha4_5 Ha5_5.
        rewrite (moi_eq_vec (bv_unsigned b) 124 ltac:(unfold Z64; lia)
                   ltac:(unfold Z64; lia)).
        symmetry. apply Z.eqb_neq. exact N124. }
      iApply (wp_uk_btype γt γd γs γfd h7 n5 (mword_of_int 0x3e8)
                (mword_of_int 8094 : mword 13) a4_idx a5_idx BEQ false
                (mword_of_int 0x386) (2 + nn)
                Htk3
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_3e8 with "Hcode"). }
      rewrite (ushp_pc_step' 0x3e8 4 0x3ec ltac:(reflexivity)).
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
    iApply (wp_uk_btype γt γd γs γfd h3 n3 (mword_of_int 0x362)
              (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU false
              (mword_of_int 0x3ca) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_362 with "Hcode"). }
    rewrite (ushp_pc_step 0x362 4). iIntros (h4) "Hrun".
    (* ---- 0x366  li a4,58 ---- *)
    iApply (wp_uk_li γt γd γs γfd h4 n3 (mword_of_int 0x366)
              (mword_of_int 58 : mword 12) a4_idx (mword_of_int 58) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_366 with "Hcode"). }
    rewrite (ushp_pc_step 0x366 4). iIntros (h5) "Hrun".
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
    (* ---- 0x36a  bltu a4,a5,0x386 -- ';' and '<' are refuted ---- *)
    assert (Htk2 : false = uv_btaken BLTU (p4 !!! Regidx a4_idx)
                             (p4 !!! Regidx a5_idx)).
    { cbn [uv_btaken]. rewrite Hb4_4 Hb5_4.
      rewrite (moi_lt_u 58 (bv_unsigned b) ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.ltb_ge. lia. }
    iApply (wp_uk_btype γt γd γs γfd h5 p4 (mword_of_int 0x36a)
              (mword_of_int 28 : mword 13) a5_idx a4_idx BLTU false
              (mword_of_int 0x386) (2 + nn)
              Htk2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_36a with "Hcode"). }
    rewrite (ushp_pc_step 0x36a 4). iIntros (h6) "Hrun".
    (* ---- 0x36e  c.beqz a5,0x388 -- THE NUL ARM ---- *)
    destruct (Z.eq_dec (bv_unsigned b) 0) as [ Hbz | Hbnz ].
    { assert (Hkeq : k = len).
      { destruct (Nat.eq_dec k len) as [ He | Hne2 ];
          [ exact He | exfalso; exact (Hnz ltac:(lia) Hbz) ]. }
      assert (Htk3 : true = eq_vec (p4 !!! Regidx a5_idx) zero_reg).
      { rewrite Hb5_4 Hbz.
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_cbeqz γt γd γs γfd h6 p4 (mword_of_int 0x36e)
                (mword_of_int 13 : mword 8) (mword_of_int 7 : mword 3)
                a5_idx true (mword_of_int 0x388) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk3
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_36e with "Hcode"). }
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
    iApply (wp_uk_cbeqz γt γd γs γfd h6 p4 (mword_of_int 0x36e)
              (mword_of_int 13 : mword 8) (mword_of_int 7 : mword 3)
              a5_idx false (mword_of_int 0x388) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk3
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_36e with "Hcode"). }
    rewrite (ushp_pc_step 0x36e 2). iIntros (h7) "Hrun".
    (* ---- 0x370  li a4,38 ---- *)
    iApply (wp_uk_li γt γd γs γfd h7 p4 (mword_of_int 0x370)
              (mword_of_int 38 : mword 12) a4_idx (mword_of_int 38) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_370 with "Hcode"). }
    rewrite (ushp_pc_step 0x370 4). iIntros (h8) "Hrun".
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
    (* ---- 0x374  beq a5,a4,0x386 -- '&' is refuted ---- *)
    assert (Htk4 : false = uv_btaken BEQ (p5 !!! Regidx a5_idx)
                             (p5 !!! Regidx a4_idx)).
    { cbn [uv_btaken]. rewrite Hb4_5 Hb5_5.
      rewrite (moi_eq_vec (bv_unsigned b) 38 ltac:(unfold Z64; lia)
                 ltac:(unfold Z64; lia)).
      symmetry. apply Z.eqb_neq. exact N38. }
    iApply (wp_uk_btype γt γd γs γfd h8 p5 (mword_of_int 0x374)
              (mword_of_int 18 : mword 13) a4_idx a5_idx BEQ false
              (mword_of_int 0x386) (2 + nn)
              Htk4
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_374 with "Hcode"). }
    rewrite (ushp_pc_step 0x374 4). iIntros (h9) "Hrun".
    (* ---- 0x378  addiw a5,a5,-40 ---- *)
    iApply (wp_uk_addiw γt γd γs γfd h9 p5 (mword_of_int 0x378)
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
    { iApply (uis_shp_378 with "Hcode"). }
    rewrite (ushp_pc_step 0x378 4). iIntros (h10) "Hrun".
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
    (* ---- 0x37c  zext.b a5,a5 -- the wrap is undone here ---- *)
    iApply (wp_uk_andi γt γd γs γfd h10 p6 (mword_of_int 0x37c)
              (mword_of_int 255 : mword 12) a5_idx a5_idx
              (mword_of_int ((bv_unsigned b - 40) mod 256)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq p5 (Regidx a5_idx) _); symmetry;
                    exact (ushp_addiw_andi (bv_unsigned b) Hvb))
              with "[] Hrun").
    { iApply (uis_shp_37c with "Hcode"). }
    rewrite (ushp_pc_step 0x37c 4). iIntros (h11) "Hrun".
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
    (* ---- 0x380  c.li a4,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_cli γt γd γs γfd h11 p7 (mword_of_int 0x380)
              (mword_of_int 1 : mword 6) a4_idx (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_380 with "Hcode"). }
    rewrite (ushp_pc_step 0x380 2). iIntros (h12) "Hrun".
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
    (* ---- 0x382  bltu a4,a5,0x3ec -- '(' and ')' are the only 0 and 1 --- *)
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
    iApply (wp_uk_btype γt γd γs γfd h12 p8 (mword_of_int 0x382)
              (mword_of_int 106 : mword 13) a5_idx a4_idx BLTU true
              (mword_of_int 0x3ec) (2 + nn)
              Htk5
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_382 with "Hcode"). }
    iIntros (h13) "Hrun".
    rewrite (bool_decide_eq_true_2 (k < len)%nat Hklt).
    iApply ("Hcont" with "Hstr [] [] Hrun").
    - iPureIntro. intros t Ht4 Ht5 Hts5.
      rewrite (Hp8 t Ht4) (Hp7 t Ht5) (Hp6 t Ht5) (Hp5 t Ht4) (Hp4 t Ht4)
              (Hn3 t Ht4) (Hn2 t Hts5). exact (Hn1 t Ht5).
    - iPureIntro. intro Hge. lia.
  Qed.

  (* ---- the common landing, 0x3b0..0x3c8 --------------------------------- *)

  (* All THREE ways out of the switch converge here -- the NUL arm, the
     default arm's whitespace exit and its end-of-line exit -- so [*ps = s],
     [a0 = ret] and the epilogue are walked once, and so is the [ucallee_
     saved] read-back the caller needs.  Every callee-saved register except
     sp is either spilled (ra, s0..s6, restored by [ushp_spillback] to the
     value it had at entry) or never written at all (gp, tp, s7..s11), which
     is what makes that read-back a theorem rather than a promise. *)
  Lemma wp_kshp_gtk_fin (m : regfile) (sp0 spl : mword 64)
      (vals : nat -> mword 64) (ps res cur : Z) (w0 : mword 64) (nn : nat)
      (h : CpuId) (me : regfile) :
    uint sp0 mod 8 = 0 -> 64 <= uint sp0 -> uint sp0 < Z64 ->
    uint spl = uint sp0 - 64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    vals = (fun i : nat => match i with
                           | 0%nat => m !!! Regidx ra_idx
                           | 1%nat => m !!! Regidx s0_idx
                           | 2%nat => m !!! Regidx s1_idx
                           | 3%nat => m !!! Regidx s2_idx
                           | 4%nat => m !!! Regidx s3_idx
                           | 5%nat => m !!! Regidx s4_idx
                           | 6%nat => m !!! Regidx s5_idx
                           | _ => m !!! Regidx s6_idx end) ->
    sp0 = m !!! Regidx csp_rs1 ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 8)) ->
    me !!! Regidx s4_idx = mword_of_int ps ->
    me !!! Regidx s1_idx = mword_of_int cur ->
    me !!! Regidx s5_idx = mword_of_int res ->
    (forall t : mword 5, ucallee_saved_idx t = true ->
       Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
       Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
       Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
       Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
       me !!! Regidx t = m !!! Regidx t) ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 7 : mword 6);
                       (s0_idx, mword_of_int 6 : mword 6);
                       (s1_idx, mword_of_int 5 : mword 6);
                       (s2_idx, mword_of_int 4 : mword 6);
                       (s3_idx, mword_of_int 3 : mword 6);
                       (s4_idx, mword_of_int 2 : mword 6);
                       (s5_idx, mword_of_int 1 : mword 6);
                       (s6_idx, mword_of_int 0 : mword 6)],
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd spl 0 -∗
    urun γt γd γs γfd h me (mword_of_int 0x3b0) (2 + nn) -∗
    (uword γd ps (mword_of_int cur) -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx = mword_of_int res ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
           (8 + (2 + nn)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hal8 Hlo Hhi Hsplu Hps0 Hps8 Hpssz Hvals Hsp0 Hsp Hs4 Hs1 Hs5
           Hkeep.
    iIntros "#Hcode Hcur Hsl Hloc Hrun Hcont".
    (* ---- 0x3b0  sd s1,0(s4)  --  *ps = s ---- *)
    iApply (wp_uk_sd γt γd γs γfd h me (mword_of_int 0x3b0)
              (mword_of_int 0 : mword 12) s4_idx s1_idx ps w0 (2 + nn)
              ltac:(rewrite Hs4 (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hps8
              with "[] Hcur Hrun").
    { iApply (uis_shp_3b0 with "Hcode"). }
    iIntros "Hcur". rewrite Hs1.
    rewrite (ushp_pc_step 0x3b0 4). iIntros (h1) "Hrun".
    (* ---- 0x3b4  c.mv a0,s5  -- the return value ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 me (mword_of_int 0x3b4) a0_idx s5_idx
              (mword_of_int res) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5; symmetry; exact (ushp_mv_val res))
              with "[] Hrun").
    { iApply (uis_shp_3b4 with "Hcode"). }
    rewrite (ushp_pc_step 0x3b4 2). iIntros (h2) "Hrun".
    set (mg := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int res : mword 64)]> me).
    assert (Hmg : forall t : mword 5, Regidx t <> Regidx a0_idx ->
                    mg !!! Regidx t = me !!! Regidx t)
      by (intros t Ht; exact (upd_ne me (Regidx a0_idx) (Regidx t) _ Ht)).
    assert (Hspg : mg !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 8)))
      by (rewrite (Hmg csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp).
    (* ---- 0x3b6..0x3c8  the epilogue ---- *)
    iApply (wp_kshp_gtk_epi sp0 spl vals nn h2 mg
              Hal8 Hlo Hhi Hsplu Hspg with "Hcode Hsl Hloc Hrun").
    iIntros (h3) "Hrun".
    subst vals.
    iApply ("Hcont" with "Hcur [] [] Hrun").
    - iPureIntro. intros q Hq. cbn [ushp_spillback fst].
      destruct (Z.eq_dec (uint q) 2) as [ E2 | E2 ].
      { rewrite (ushp_ridx_eq q csp_rs1
                   ltac:(rewrite E2; vm_compute; reflexivity)).
        rewrite (upd_eq _ (Regidx csp_rs1) (regval_into_reg sp0)).
        exact Hsp0. }
      assert (Hq2 : Regidx q <> Regidx csp_rs1)
        by (apply ushp_ridx_ne;
            assert (Hc : uint csp_rs1 = 2) by (vm_compute; reflexivity);
            rewrite Hc; exact E2).
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx q) _ Hq2).
      destruct (Z.eq_dec (uint q) 22) as [ E22 | E22 ].
      { rewrite (ushp_ridx_eq q s6_idx
                   ltac:(rewrite E22; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s6_idx)
                 (regval_into_reg (m !!! Regidx s6_idx))). }
      assert (Hq22 : Regidx q <> Regidx s6_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s6_idx = 22) by (vm_compute; reflexivity);
            rewrite Hc; exact E22).
      rewrite (upd_ne _ (Regidx s6_idx) (Regidx q) _ Hq22).
      destruct (Z.eq_dec (uint q) 21) as [ E21 | E21 ].
      { rewrite (ushp_ridx_eq q s5_idx
                   ltac:(rewrite E21; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s5_idx)
                 (regval_into_reg (m !!! Regidx s5_idx))). }
      assert (Hq21 : Regidx q <> Regidx s5_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s5_idx = 21) by (vm_compute; reflexivity);
            rewrite Hc; exact E21).
      rewrite (upd_ne _ (Regidx s5_idx) (Regidx q) _ Hq21).
      destruct (Z.eq_dec (uint q) 20) as [ E20 | E20 ].
      { rewrite (ushp_ridx_eq q s4_idx
                   ltac:(rewrite E20; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s4_idx)
                 (regval_into_reg (m !!! Regidx s4_idx))). }
      assert (Hq20 : Regidx q <> Regidx s4_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s4_idx = 20) by (vm_compute; reflexivity);
            rewrite Hc; exact E20).
      rewrite (upd_ne _ (Regidx s4_idx) (Regidx q) _ Hq20).
      destruct (Z.eq_dec (uint q) 19) as [ E19 | E19 ].
      { rewrite (ushp_ridx_eq q s3_idx
                   ltac:(rewrite E19; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s3_idx)
                 (regval_into_reg (m !!! Regidx s3_idx))). }
      assert (Hq19 : Regidx q <> Regidx s3_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s3_idx = 19) by (vm_compute; reflexivity);
            rewrite Hc; exact E19).
      rewrite (upd_ne _ (Regidx s3_idx) (Regidx q) _ Hq19).
      destruct (Z.eq_dec (uint q) 18) as [ E18 | E18 ].
      { rewrite (ushp_ridx_eq q s2_idx
                   ltac:(rewrite E18; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s2_idx)
                 (regval_into_reg (m !!! Regidx s2_idx))). }
      assert (Hq18 : Regidx q <> Regidx s2_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s2_idx = 18) by (vm_compute; reflexivity);
            rewrite Hc; exact E18).
      rewrite (upd_ne _ (Regidx s2_idx) (Regidx q) _ Hq18).
      destruct (Z.eq_dec (uint q) 9) as [ E9 | E9 ].
      { rewrite (ushp_ridx_eq q s1_idx
                   ltac:(rewrite E9; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s1_idx)
                 (regval_into_reg (m !!! Regidx s1_idx))). }
      assert (Hq9 : Regidx q <> Regidx s1_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s1_idx = 9) by (vm_compute; reflexivity);
            rewrite Hc; exact E9).
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx q) _ Hq9).
      destruct (Z.eq_dec (uint q) 8) as [ E8 | E8 ].
      { rewrite (ushp_ridx_eq q s0_idx
                   ltac:(rewrite E8; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx s0_idx)
                 (regval_into_reg (m !!! Regidx s0_idx))). }
      assert (Hq8 : Regidx q <> Regidx s0_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s0_idx = 8) by (vm_compute; reflexivity);
            rewrite Hc; exact E8).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx q) _ Hq8).
      assert (Hqra : Regidx q <> Regidx ra_idx)
        by exact (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx q) _ Hqra).
      rewrite (Hmg q (ushp_cs_ne q a0_idx Hq
                        ltac:(vm_compute; reflexivity))).
      exact (Hkeep q Hq Hq2 Hq8 Hq9 Hq18 Hq19 Hq20 Hq21 Hq22).
    - iPureIntro. cbn [ushp_spillback fst].
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s6_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s5_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s4_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s3_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s2_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq me (Regidx a0_idx)
               (regval_into_reg (mword_of_int res : mword 64))).
  Qed.

  (* ---- gettoken, the whole function ------------------------------------- *)

  (* where the cursor ends up: past the token, then past the whitespace
     after it.  At the end of the line both runs are empty, so the same
     expression covers the NUL arm. *)
  Definition ushp_gettok_fin (len : nat) (f : nat -> bv 8) (k : nat) : nat :=
    let e := ushp_gettok_end len f k in (e + ushp_skipws (len - e) e f)%nat.

  Lemma wp_kshp_gettoken (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps qp eqp s0 : Z) (len off : nat) (f : nat -> bv 8)
      (w0 wq weq : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx a2_idx = mword_of_int qp ->
    m !!! Regidx a3_idx = mword_of_int eqp ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushp_no_symbols len f ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ushp_cell qp wq -∗
    ushp_cell eqp weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.gettoken) (8 + (2 + nn)) -∗
    (uword γd ps
       (mword_of_int
          (s0 + Z.of_nat
                  (ushp_gettok_fin len f
                     (off + ushp_skipws (len - off) off f)))) -∗
     ushp_cell qp
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ushp_cell eqp
       (mword_of_int
          (s0 + Z.of_nat
                  (ushp_gettok_end len f
                     (off + ushp_skipws (len - off) off f)))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
             = mword_of_int
                 (ushp_gettok_res len f
                    (off + ushp_skipws (len - off) off f)) ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx))
           (8 + (2 + nn)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Ha2 Ha3 Hoffle Hw0 Hnosym Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
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
    (* ---- 0x310  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x310)
              (mword_of_int 60 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_310 with "Hcode"). }
    rewrite (ushp_pc_step 0x310 2). iIntros "Hstk" (h1) "Hrun".
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
    (* ---- 0x312..0x320  the eight spills ---- *)
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
                              | 0%nat => 0x312 | 1%nat => 0x314
                              | 2%nat => 0x316 | 3%nat => 0x318
                              | 4%nat => 0x31a | 5%nat => 0x31c
                              | 6%nat => 0x31e | 7%nat => 0x320
                              | _ => 0x322 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h1 m1 Hsp1
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate;
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
      iSplit; [ iApply (uis_shp_312 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_314 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_316 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_318 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_31a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_31c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_31e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_320 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x322  c.addi4spn s0,sp,64 ---- *)
    iApply (wp_kshp_fp h2 m1 0x322 (mword_of_int 16 : mword 8) (2 + nn)
              with "[] Hrun").
    { iApply (uis_shp_322 with "Hcode"). }
    iIntros (h3 v322) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v322]> m1).
    assert (Hm2 : forall t : mword 5, Regidx t <> Regidx s0_idx ->
                    m2 !!! Regidx t = m1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m1 (Regidx s0_idx) (Regidx t) _ Ht)).
    (* ---- 0x324  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m2 (mword_of_int 0x324) s4_idx a0_idx
              (mword_of_int ps) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_324 with "Hcode"). }
    rewrite (ushp_pc_step 0x324 2). iIntros (h4) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall t : mword 5, Regidx t <> Regidx s4_idx ->
                    m3 !!! Regidx t = m2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m2 (Regidx s4_idx) (Regidx t) _ Ht)).
    (* ---- 0x326  c.mv s2,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h4 m3 (mword_of_int 0x326) s2_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_326 with "Hcode"). }
    rewrite (ushp_pc_step 0x326 2). iIntros (h5) "Hrun".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                     : mword 64)]> m3).
    assert (Hm4 : forall t : mword 5, Regidx t <> Regidx s2_idx ->
                    m4 !!! Regidx t = m3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m3 (Regidx s2_idx) (Regidx t) _ Ht)).
    (* ---- 0x328  c.mv s5,a2 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h5 m4 (mword_of_int 0x328) s5_idx a2_idx
              (mword_of_int qp) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val qp))
              with "[] Hrun").
    { iApply (uis_shp_328 with "Hcode"). }
    rewrite (ushp_pc_step 0x328 2). iIntros (h6) "Hrun".
    set (m5 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int qp : mword 64)]> m4).
    assert (Hm5 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    m5 !!! Regidx t = m4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m4 (Regidx s5_idx) (Regidx t) _ Ht)).
    (* ---- 0x32a  c.mv s6,a3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h6 m5 (mword_of_int 0x32a) s6_idx a3_idx
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
    { iApply (uis_shp_32a with "Hcode"). }
    rewrite (ushp_pc_step 0x32a 2). iIntros (h7) "Hrun".
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
    (* ---- 0x32c  c.ld s1,0(a0) -- the cursor ---- *)
    iApply (wp_uk_cld γt γd γs γfd h7 m6 (mword_of_int 0x32c)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 1 : mword 3) a0_idx s1_idx ps w0 (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_6 (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              Hps8 ltac:(vm_compute; discriminate)
              with "[] Hcur Hrun").
    { iApply (uis_shp_32c with "Hcode"). }
    iIntros "Hcur". rewrite (ushp_pc_step 0x32c 2). iIntros (h8) "Hrun".
    set (m7 := <[Regidx s1_idx := regval_into_reg w0]> m6).
    assert (Hm7 : forall t : mword 5, Regidx t <> Regidx s1_idx ->
                    m7 !!! Regidx t = m6 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m6 (Regidx s1_idx) (Regidx t) _ Ht)).
    (* ---- 0x32e  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h8 m7 (mword_of_int 0x32e)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x232e)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_32e with "Hcode"). }
    rewrite (ushp_pc_step 0x32e 4). iIntros (h9) "Hrun".
    set (m8 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x232e : mword 64)]> m7).
    assert (Hm8 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m8 !!! Regidx t = m7 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m7 (Regidx s3_idx) (Regidx t) _ Ht)).
    (* ---- 0x332  addi s3,s3,-806  -- s3 = &whitespace ---- *)
    iApply (wp_uk_addi γt γd γs γfd h9 m8 (mword_of_int 0x332)
              (mword_of_int 3290 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m7 (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x232e
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_332 with "Hcode"). }
    rewrite (ushp_pc_step 0x332 4). iIntros (h10) "Hrun".
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
    (* ---- 0x336..0x34c  the LEADING whitespace scan ---- *)
    iApply (wp_kshp_ws_enter 0x336 a1_idx (mword_of_int 1858 : mword 21)
              dq dw s0 len off f nn h10 m9
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Hoffle Hs0 Hs64 Hs1_9 Hs2_9 Hs3_9 Ha1_9
              with "[] [] [] [] [] [] [] [] Hcode Hstr Hws Hrun").
    { iApply (uis_shp_336 with "Hcode"). }
    { iApply (uis_shp_33a with "Hcode"). }
    { iApply (uis_shp_33e with "Hcode"). }
    { iApply (uis_shp_340 with "Hcode"). }
    { iApply (uis_shp_344 with "Hcode"). }
    { iApply (uis_shp_346 with "Hcode"). }
    { iApply (uis_shp_348 with "Hcode"). }
    { iApply (uis_shp_34c with "Hcode"). }
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
    (* ---- 0x34e..0x352  [if(q) *q = s] ---- *)
    iApply (wp_kshp_gtk_qst s0 qp kk wq nn h11 mA Hs0
              ltac:(unfold Z64 in *; lia) Hs1A Hs5_A with "Hcode Hq Hrun").
    iIntros "Hq" (h12) "Hrun".
    (* ---- 0x356..0x386 (and 0x3ca..0x3e8)  THE SWITCH ---- *)
    iApply (wp_kshp_gtk_disp dq s0 len kk f nn h12 mA
              Hkk Hnosym Hs0 Hs64 Hs1A with "Hcode Hstr Hrun").
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
      assert (Hfin : ushp_gettok_fin len f kk = len).
      { unfold ushp_gettok_fin, ushp_gettok_end. rewrite Hkeq.
        assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_toklen_zero len f).
        assert (Hz2 : (len + 0)%nat = len) by lia. rewrite Hz2 Hz.
        rewrite (ushp_skipws_zero len f). lia. }
      assert (Hend : ushp_gettok_end len f kk = len).
      { unfold ushp_gettok_end. rewrite Hkeq.
        assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_toklen_zero len f). lia. }
      assert (Hres : ushp_gettok_res len f kk = 0).
      { unfold ushp_gettok_res.
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
    assert (Hres : ushp_gettok_res len f kk = 97).
    { unfold ushp_gettok_res.
      rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt). reflexivity. }
    (* ---- 0x3ec  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h13 mB (mword_of_int 0x3ec)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x23ec)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3ec with "Hcode"). }
    rewrite (ushp_pc_step 0x3ec 4). iIntros (h14) "Hrun".
    set (d1 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x23ec : mword 64)]> mB).
    assert (Hd1 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    d1 !!! Regidx t = mB !!! Regidx t)
      by (intros t Ht; exact (upd_ne mB (Regidx s3_idx) (Regidx t) _ Ht)).
    (* ---- 0x3f0  addi s3,s3,-996 ---- *)
    iApply (wp_uk_addi γt γd γs γfd h14 d1 (mword_of_int 0x3f0)
              (mword_of_int 3100 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mB (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x23ec
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3f0 with "Hcode"). }
    rewrite (ushp_pc_step 0x3f0 4). iIntros (h15) "Hrun".
    set (d2 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> d1).
    assert (Hd2 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    d2 !!! Regidx t = d1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d1 (Regidx s3_idx) (Regidx t) _ Ht)).
    assert (Hs3_d2 : d2 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq d1 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    (* ---- 0x3f4  auipc s5,0x2 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h15 d2 (mword_of_int 0x3f4)
              (mword_of_int 2 : mword 20) s5_idx (mword_of_int 0x23f4)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3f4 with "Hcode"). }
    rewrite (ushp_pc_step 0x3f4 4). iIntros (h16) "Hrun".
    set (d3 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 0x23f4 : mword 64)]> d2).
    assert (Hd3 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    d3 !!! Regidx t = d2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d2 (Regidx s5_idx) (Regidx t) _ Ht)).
    (* ---- 0x3f8  addi s5,s5,-1012  -- s5 = &symbols ---- *)
    iApply (wp_uk_addi γt γd γs γfd h16 d3 (mword_of_int 0x3f8)
              (mword_of_int 3084 : mword 12) s5_idx s5_idx
              (mword_of_int ushp_symbols) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq d2 (Regidx s5_idx)
                               (regval_into_reg (mword_of_int 0x23f4
                                                 : mword 64)));
                    unfold ushp_symbols;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3f8 with "Hcode"). }
    rewrite (ushp_pc_step 0x3f8 4). iIntros (h17) "Hrun".
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
    (* ---- 0x3fc  bgeu s1,s2,0x43e -- refuted: the cursor is inside ---- *)
    assert (Htk : false = uv_btaken BGEU (d4 !!! Regidx s1_idx)
                            (d4 !!! Regidx s2_idx)).
    { cbn [uv_btaken]. rewrite Hs1_d4 Hs2_d4.
      rewrite (moi_ge_u (s0 + Z.of_nat kk) (s0 + Z.of_nat len)
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype γt γd γs γfd h17 d4 (mword_of_int 0x3fc)
              (mword_of_int 66 : mword 13) s2_idx s1_idx BGEU false
              (mword_of_int 0x43e) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_3fc with "Hcode"). }
    rewrite (ushp_pc_step 0x3fc 4). iIntros (h18) "Hrun".
    (* ---- 0x400..0x41a  THE TOKEN-BODY SCAN ---- *)
    iApply (wp_kshp_tok_scan dq dw dv s0 len f nn (len - kk)%nat kk h18 d4
              eq_refl Hklt Hs0 Hs64 Hs1_d4 Hs2_d4 Hs3_d4 Hs5_d4
              with "Hcode Hstr Hws Hsy Hrun").
    iIntros "Hstr Hws Hsy" (h19 mE) "%HpresE %Hs1E %Hs5E Hrun".
    set (ee := ushp_gettok_end len f kk).
    assert (Heed : (kk + ushp_toklen (len - kk) kk f)%nat = ee)
      by reflexivity.
    rewrite Heed in Hs1E.
    assert (Heele : (ee <= len)%nat).
    { unfold ee, ushp_gettok_end.
      pose proof (ushp_toklen_le (len - kk) kk f). lia. }
    assert (Hexit : ushp_tok_exit len f kk
                    = if bool_decide (ee < len)%nat then 0x388 else 0x424)
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
    { (* the token was ended by a byte: 0x388, then the trailing scan *)
      apply bool_decide_eq_true in Eee.
      iApply (wp_kshp_gtk_388 dq dw s0 eqp len ee f weq nn h19 mE
                ltac:(lia) Hs0 Hs64 Hs1E Hs2_E Hs6_E
                with "Hcode Heq Hstr Hws Hrun").
      iIntros "Heq Hstr Hws" (h20 mF) "%HpresF %Hs1F Hrun".
      assert (Hfin : ushp_gettok_fin len f kk
                     = (ee + ushp_skipws (len - ee) ee f)%nat)
        by reflexivity.
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
    (* the token ran to [es]: 0x424, and the trailing scan is empty *)
    apply bool_decide_eq_false in Eee.
    assert (Heeq : ee = len) by lia.
    rewrite Heeq in Hs1E.
    assert (Hfin : ushp_gettok_fin len f kk = len).
    { assert (H1 : ushp_gettok_fin len f kk
                   = (ee + ushp_skipws (len - ee) ee f)%nat) by reflexivity.
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

End UkShParseTok.
