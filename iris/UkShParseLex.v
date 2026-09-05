(* ===================================================================== *)
(* UkShParseLex.v -- SH LANE STAGE 4, part 2: the LOOKAHEAD and the one    *)
(* constructor a symbol-free line reaches.                                 *)
(*                                                                        *)
(*   peek     @0x448  -- 40 instructions, an EIGHT-word frame, one scan.   *)
(*                       the parser's one-token lookahead, and what        *)
(*                       [ushp_no_symbols] answers "no" to at four of the  *)
(*                       five sites that ask.  It is also the only lexer   *)
(*                       function that MOVES THE CURSOR AS A SIDE EFFECT   *)
(*                       ([*ps = s]), which is why the cursor cell is a    *)
(*                       [uword] in the contract rather than a value.      *)
(*   the seven token tables, as one persistent premise                     *)
(*   execcmd  @0x1d2  -- 19 instructions, a four-word frame, NO branch.    *)
(*                       [malloc(168); memset(cmd,0,168); cmd->type=EXEC]  *)
(*                                                                        *)
(* THIS IS WHERE THE ALLOCATOR ENTERS.  [ushp_malloc_ok] is declared here  *)
(* at the type the base file names ([UkShParse.ushp_malloc_ty]) and        *)
(* [wp_kshp_execcmd] is its only consumer in the whole parser; every file  *)
(* after this one carries it through and says so.                         *)
(*                                                                        *)
(* See iris/UkShParse.v's header for why stage 4 is six files and what a   *)
(* split costs.                                                            *)
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

Section UkShParseLex.
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


  (* ---- what the earlier files of the parser define, at this
         file's own ghost names.  Everything else they export is a
         PURE constant and comes in with the [Require Import]. ---- *)
  Local Notation urun_x0 := (UkShParse.urun_x0 γt γd γs γfd).
  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at γd).
  Local Notation ushp_exec_pre := (UkShParse.ushp_exec_pre γd).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join γd).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split γd).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty γt γd γs γfd).
  Local Notation ushp_peel0 := (UkShParse.ushp_peel0 γd).
  Local Notation ushp_slots_nil0 := (UkShParse.ushp_slots_nil0 γd).
  Local Notation ushp_sstr := (UkShParse.ushp_sstr γt γd).
  Local Notation ushp_sstr_text := (UkShParse.ushp_sstr_text γt γd).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at γd).
  Local Notation ushp_ubytes_ext := (UkShParse.ushp_ubytes_ext γd).
  Local Notation wp_kshp_fp := (UkShParse.wp_kshp_fp γt γd γs γfd).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore γt γd γs γfd).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill γt γd γs γfd).
  Local Notation wp_kshp_strchr := (UkShParse.wp_kshp_strchr γt γd γs γfd).
  Local Notation wp_kshp_strlen := (UkShParse.wp_kshp_strlen γt γd γs γfd).


  (* ===================================================================== *)
  (* §6 THE ONE HYPOTHESIS OF STAGE 4: MALLOC.                              *)
  (*                                                                       *)
  (* All five cmd constructors begin [cmd = malloc(sizeof( *cmd))], and     *)
  (* malloc (0x118c, 91 instructions) -> morecore -> sbrk (0xc52) ->        *)
  (* sys_sbrk (0xd0e) is STAGE 3, which is blocked on the second unbuilt    *)
  (* consumer leaf, [wp_uk_ecall_sbrk] -- and that one moves [pi] and [sz], *)
  (* so it is strictly harder than the window row stage 2 needed.           *)
  (*                                                                       *)
  (* So malloc's contract is stated HERE, once, as a named local            *)
  (* Hypothesis, at the idiom of the landed function contracts in UkSh.v    *)
  (* ([wp_ksh_memset]'s binder order, [ucallee_saved] read-back, [ret_pc]   *)
  (* return) so that stage 3's discharge is [intros] + [exact] or a thin    *)
  (* adapter.  IT CONSUMES THE RUN AT MALLOC'S ENTRY PC AND HANDS IT BACK   *)
  (* AT THE RETURN ADDRESS, so no instruction of the allocator is ever      *)
  (* fetched by this walk and none is in tools/ucode_shp.txt.               *)
  (*                                                                       *)
  (* THE STACK BUDGET IS THE CALL CHAIN SPELLED OUT, as the durable notes   *)
  (* require: malloc's own frame is 64 bytes (8 words) and the deepest       *)
  (* thing it calls is [free] or [sbrk], 16 bytes (2 words) each, so it is  *)
  (* [10 + avail] -- not a round number.                                    *)
  (*                                                                       *)
  (* WHAT IT DOES NOT SAY, and why that is honest rather than convenient:   *)
  (* THERE IS NO FAILURE ARM.  sh's constructors do not test malloc's       *)
  (* result -- [execcmd] goes straight into [memset(cmd, 0, 168)] -- so a   *)
  (* NULL return is a FAULT in sh, not a branch, and a contract with a NULL *)
  (* arm would be unusable by the very code it is for.  The first           *)
  (* generation drew the line in the same place and named it: its           *)
  (* [wp_sh_malloc_first_body] is FIRST-CALL-ONLY ([freep == 0], so the     *)
  (* [morecore] path), which is the only call sh's parse of one line makes. *)
  (*                                                                       *)
  (* WHAT IT TAINTS, TODAY: exactly one lemma, [wp_kshp_execcmd] in §7,     *)
  (* which is the only caller of a constructor this file has.  Everything   *)
  (* else -- the pure vocabulary, the frame runs of §4b, [wp_kshp_strchr],  *)
  (* [wp_kshp_strlen], the tree algebra -- is UNCONDITIONAL, and            *)
  (* [Print Assumptions] on any of them is the standing three or *closed    *)
  (* under the global context*.  When [parseexec], [parsepipe],             *)
  (* [parseline] and [parsecmd] land they will carry it THROUGH §7, each    *)
  (* labelled in its own header the way stage 2 labelled its seven.         *)
  (* ===================================================================== *)
  (* stage 4's one Hypothesis, at the type the base file names *)
  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.

  (* ===================================================================== *)
  (* §8 peek @0x448 -- 40 instructions, an EIGHT-word frame, one scan.      *)
  (*                                                                       *)
  (*   int peek(char **ps, char *es, char *toks) {                          *)
  (*     char *s = *ps;                                                     *)
  (*     while(s < es && strchr(whitespace, *s)) s++;                       *)
  (*     *ps = s;                                                           *)
  (*     return *s && strchr(toks, *s);  }                                  *)
  (*                                                                       *)
  (* THE PARSER'S ONE-TOKEN LOOKAHEAD: every one of parsecmd, parseline,    *)
  (* parsepipe, parseexec and parseredirs asks it whether the next          *)
  (* non-blank byte is in a given set, and it is what [ushp_no_symbols]     *)
  (* answers "no" to at four of those five sites.  It is also the only      *)
  (* function in the parser that MOVES THE LEXER'S CURSOR AS A SIDE         *)
  (* EFFECT -- [*ps = s] -- which is why the cursor cell is a [uword] in    *)
  (* the contract rather than a value.                                      *)
  (*                                                                       *)
  (* THE SCAN IS A BOUNDED ROCQ INDUCTION AND WHAT BOUNDS IT IS [es]:       *)
  (* [s2] holds the end pointer and the back edge tests against it, so the  *)
  (* scan reads only BODY bytes of the line and the terminator never enters *)
  (* it -- unlike strchr's loop, which is bounded by the NUL.  The measure  *)
  (* is [len - j] and the answer is [ushp_skipws], the ported spelling.     *)
  (* ===================================================================== *)

  (* peek's whitespace scan, 0x46e..0x47c:
       lbu a1,0(s1) ; c.mv a0,s3 ; jal strchr ; c.beqz a0,0x482 ;
       c.addi s1,s1,1 ; bne s2,s1,0x46e
     [j] is the index the scan has reached.  Only the CALLEE-SAVED half of
     the register file is promised across it, because every turn calls
     strchr and that is all strchr's contract gives; s1 is excluded because
     the scan is what moves it. *)
  Lemma wp_kshp_peek_scan (dq dw : dfrac) (s0 : Z) (len : nat)
      (f : nat -> bv 8) (nn : nat) :
    forall (r j : nat) (h : CpuId) (mc : regfile),
    (len - j = r)%nat -> (j < len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s3_idx = mword_of_int ushp_whitespace ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x46e) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
             Regidx q <> Regidx s1_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x482) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros r. induction r as [| r IH ];
      intros j h mc Hr Hj Hs0 Hs64 Hs1 Hs2 Hs3;
      iIntros "#Hcode Hstr Hws Hrun Hcont"; [ lia | ].
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    (* ---- 0x46e  lbu a1,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f j Hj with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs γfd h mc (mword_of_int 0x46e)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat j) (f j) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat j)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_46e with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x46e 4). iIntros (h1) "Hrun".
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
    (* ---- 0x472  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h1 m1 (mword_of_int 0x472) a0_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)) Hs3;
                    symmetry; exact (ushp_mv_val ushp_whitespace))
              with "[] Hrun").
    { iApply (uis_shp_472 with "Hcode"). }
    rewrite (ushp_pc_step 0x472 2). iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x474  jal a82 <strchr> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h2 m2 (mword_of_int 0x474)
              (mword_of_int 1550 : mword 21) ra_idx
              (mword_of_int 0xa82) (mword_of_int 0x478) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_474 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x478 : mword 64)]> m2).
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
    assert (Eret : ret_pc (m3 !!! Regidx ra_idx) = mword_of_int 0x478).
    { rewrite (upd_eq m2 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x478 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* the callee-saved half of [mc] survives all three writes *)
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
    (* ---- 0x478  c.beqz a0,0x482 -- the byte's membership decides ---- *)
    destruct (ushp_is_ws (f j)) eqn:Ews.
    2: { (* NOT whitespace: the scan stops here and [s1] never moved *)
      assert (Htk : true = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 (ushp_ws_chr_z (f j) Ews).
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_cbeqz γt γd γs γfd h4 m4 (mword_of_int 0x478)
                (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x482) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_478 with "Hcode"). }
      iIntros (h5) "Hrun".
      iApply ("Hcont" with "Hstr Hws [] [] Hrun").
      - iPureIntro. intros q Hq _. exact (Hcs4 q Hq).
      - iPureIntro. rewrite Hs1_4.
        rewrite (ushp_skipws_stop (len - j) j f Ews). f_equal. lia. }
    (* WHITESPACE: the loop goes round *)
    destruct (ushp_ws_chr_nz (f j) Ews) as [ k [ Hk Hchr ] ].
    assert (Htk : false = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
    { rewrite Ha0_4 Hchr.
      rewrite (moi_eq_zero (ushp_whitespace + Z.of_nat k)
                 ltac:(unfold ushp_whitespace, Z64; lia)).
      symmetry. apply Z.eqb_neq. unfold ushp_whitespace. lia. }
    iApply (wp_uk_cbeqz γt γd γs γfd h4 m4 (mword_of_int 0x478)
              (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x482) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_478 with "Hcode"). }
    rewrite (ushp_pc_step 0x478 2). iIntros (h5) "Hrun".
    (* ---- 0x47a  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi γt γd γs γfd h5 m4 (mword_of_int 0x47a)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S j))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_4 E1 moi_add;
                    replace (s0 + Z.of_nat (S j)) with (s0 + Z.of_nat j + 1)
                      by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_47a with "Hcode"). }
    rewrite (ushp_pc_step 0x47a 2). iIntros (h6) "Hrun".
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
    (* ---- 0x47c  bne s2,s1,0x46e ---- *)
    destruct (Nat.eq_dec (S j) len) as [ Hend | Hend ].
    { (* the scan ran to [es]: fall through to 0x480, which is a no-op *)
      assert (Htk2 : false = uv_btaken BNE (m5 !!! Regidx s2_idx)
                               (m5 !!! Regidx s1_idx)).
      { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5 Hend.
        rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(lia) ltac:(lia)).
        rewrite Z.eqb_refl. reflexivity. }
      iApply (wp_uk_btype γt γd γs γfd h6 m5 (mword_of_int 0x47c)
                (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE false
                (mword_of_int 0x46e) (2 + nn)
                Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_47c with "Hcode"). }
      rewrite (ushp_pc_step 0x47c 4). iIntros (h7) "Hrun".
      (* ---- 0x480  c.mv s1,s2 -- [s = es], which it already is ---- *)
      iApply (wp_uk_cmv γt γd γs γfd h7 m5 (mword_of_int 0x480) s1_idx s2_idx
                (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_5; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_480 with "Hcode"). }
      rewrite (ushp_pc_step 0x480 2). iIntros (h8) "Hrun".
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
    iApply (wp_uk_btype γt γd γs γfd h6 m5 (mword_of_int 0x47c)
              (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE true
              (mword_of_int 0x46e) (2 + nn)
              Htk2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_47c with "Hcode"). }
    iIntros (h7) "Hrun".
    iApply (IH (S j) h7 m5 ltac:(lia) Hj1 Hs0 Hs64 Hs1_5 Hs2_5 Hs3_5
              with "Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h8 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. intros q Hq Hqs1.
      rewrite (Hpres q Hq Hqs1). rewrite (Hm5 q Hqs1). exact (Hcs4 q Hq).
    - iPureIntro. rewrite Hret Hr (ushp_skipws_step r j f Ews).
      assert (Er : (len - S j)%nat = r) by lia. rewrite Er.
      f_equal. lia.
  Qed.

  (* the scan's ENTRY test, 0x46a: [bgeu s1,a1,0x482] is the [s < es] half of
     the [&&], and it is what makes the cursor's index [j] range over
     [0..len] rather than [0..len-1].  Folding it in here rather than at the
     call site is what lets everything from 0x46a to 0x482 be ONE lemma with
     ONE postcondition, so peek's body has no branch until 0x48c. *)
  Lemma wp_kshp_peek_enter (dq dw : dfrac) (s0 : Z) (len j : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (j <= len)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat j) ->
    mc !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s3_idx = mword_of_int ushp_whitespace ->
    mc !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun γt γd γs γfd h mc (mword_of_int 0x46a) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
             Regidx q <> Regidx s1_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun γt γd γs γfd h' mc' (mword_of_int 0x482) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hjle Hs0 Hs64 Hs1 Hs2 Hs3 Ha1.
    iIntros "#Hcode Hstr Hws Hrun Hcont".
    destruct (Nat.eq_dec j len) as [ Hend | Hne ].
    { (* the cursor is already at [es]: the scan is skipped entirely *)
      assert (Htk : true = uv_btaken BGEU (mc !!! Regidx s1_idx)
                             (mc !!! Regidx a1_idx)).
      { cbn [uv_btaken]. rewrite Hs1 Ha1 Hend.
        rewrite (moi_ge_u (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
        symmetry. apply Z.geb_le. lia. }
      iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x46a)
                (mword_of_int 24 : mword 13) a1_idx s1_idx BGEU true
                (mword_of_int 0x482) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_46a with "Hcode"). }
      iIntros (h1) "Hrun".
      iApply ("Hcont" with "Hstr Hws [] [] Hrun").
      - iPureIntro. intros q _ _. reflexivity.
      - iPureIntro. rewrite Hs1.
        assert (Hz : (len - j)%nat = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_skipws_zero j f). f_equal. lia. }
    (* ...otherwise the scan runs *)
    assert (Hjlt : (j < len)%nat) by lia.
    assert (Htk : false = uv_btaken BGEU (mc !!! Regidx s1_idx)
                            (mc !!! Regidx a1_idx)).
    { cbn [uv_btaken]. rewrite Hs1 Ha1.
      rewrite (moi_ge_u (s0 + Z.of_nat j) (s0 + Z.of_nat len)
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype γt γd γs γfd h mc (mword_of_int 0x46a)
              (mword_of_int 24 : mword 13) a1_idx s1_idx BGEU false
              (mword_of_int 0x482) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_46a with "Hcode"). }
    rewrite (ushp_pc_step 0x46a 4). iIntros (h1) "Hrun".
    iApply (wp_kshp_peek_scan dq dw s0 len f nn (len - j)%nat j h1 mc
              eq_refl Hjlt Hs0 Hs64 Hs1 Hs2 Hs3 with "Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* peek's epilogue, 0x48e..0x49e.  It is reached BOTH ways -- with a0
     already 0 because the byte at the cursor is the line's terminator, and
     with a0 the [snez] of a second strchr because it is not -- so it is
     stated once, at whatever a0 holds.  Nothing it runs touches a0, so the
     caller reads the result back through [ushp_spillback_ne]. *)
  Lemma wp_kshp_peek_epi (sp0 spl : mword 64) (vals : nat -> mword 64)
      (nn : nat) :
    forall (h : CpuId) (me : regfile),
    uint sp0 mod 8 = 0 -> 64 <= uint sp0 -> uint sp0 < Z64 ->
    uint spl = uint sp0 - 56 ->
    me !!! Regidx csp_rs1 = add_vec_int sp0 (- (8 * Z.of_nat 8)) ->
    shp_code γt -∗
    ([∗ list] i ↦ _ ∈ [(ra_idx, mword_of_int 7 : mword 6);
                       (s0_idx, mword_of_int 6 : mword 6);
                       (s1_idx, mword_of_int 5 : mword 6);
                       (s2_idx, mword_of_int 4 : mword 6);
                       (s3_idx, mword_of_int 3 : mword 6);
                       (s4_idx, mword_of_int 2 : mword 6);
                       (s5_idx, mword_of_int 1 : mword 6)],
       uword γd (uint sp0 - 8 * (Z.of_nat i + 1)) (vals i)) -∗
    ustack γd spl 1 -∗
    urun γt γd γs γfd h me (mword_of_int 0x48e) (2 + nn) -∗
    (∀ h' : CpuId,
       urun γt γd γs γfd h'
         (<[Regidx csp_rs1 := regval_into_reg sp0]>
            (ushp_spillback [(ra_idx, mword_of_int 7 : mword 6);
                             (s0_idx, mword_of_int 6 : mword 6);
                             (s1_idx, mword_of_int 5 : mword 6);
                             (s2_idx, mword_of_int 4 : mword 6);
                             (s3_idx, mword_of_int 3 : mword 6);
                             (s4_idx, mword_of_int 2 : mword 6);
                             (s5_idx, mword_of_int 1 : mword 6)] vals me))
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
               (s5_idx, mword_of_int 1 : mword 6)] !! i = Some (r, u) ->
              (uint sp0 - 8 * (Z.of_nat i + 1)) = uint spn + uoff_sdsp u /\
              (uint sp0 - 8 * (Z.of_nat i + 1)) mod 8 = 0 /\
              unot_sp r /\ uint r <> 0).
    { intros i r u Hi.
      destruct i as [| [| [| [| [| [| [| i ]]]]]]]; cbn in Hi;
        try discriminate Hi; injection Hi as Hr Hu0; subst;
        (split;
         [ rewrite Hspu; vm_compute uoff_sdsp; lia
         | split;
           [ exact (ushp_slot_al (uint sp0) _ Hal8)
           | split; [ unfold unot_sp; vm_compute; discriminate
                    | vm_compute; discriminate ] ] ]). }
    (* ---- 0x48e..0x49a  the seven restores ---- *)
    iApply (wp_kshp_restore spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x48e | 1%nat => 0x490
                              | 2%nat => 0x492 | 3%nat => 0x494
                              | 4%nat => 0x496 | 5%nat => 0x498
                              | 6%nat => 0x49a | _ => 0x49c end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h me Hsp
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              Hoff
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_48e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_490 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_492 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_494 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_496 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_498 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_49a with "Hcode") | done ]. }
    iIntros "Hsl" (h1) "Hrun". cbn [length].
    set (mr := ushp_spillback
                 [(ra_idx, mword_of_int 7 : mword 6);
                  (s0_idx, mword_of_int 6 : mword 6);
                  (s1_idx, mword_of_int 5 : mword 6);
                  (s2_idx, mword_of_int 4 : mword 6);
                  (s3_idx, mword_of_int 3 : mword 6);
                  (s4_idx, mword_of_int 2 : mword 6);
                  (s5_idx, mword_of_int 1 : mword 6)] vals me).
    assert (Hspr : mr !!! Regidx csp_rs1 = spn).
    { rewrite /mr (ushp_spillback_ne
                     [(ra_idx, mword_of_int 7 : mword 6);
                      (s0_idx, mword_of_int 6 : mword 6);
                      (s1_idx, mword_of_int 5 : mword 6);
                      (s2_idx, mword_of_int 4 : mword 6);
                      (s3_idx, mword_of_int 3 : mword 6);
                      (s4_idx, mword_of_int 2 : mword 6);
                      (s5_idx, mword_of_int 1 : mword 6)] vals me csp_rs1
                     ltac:(ushp_ne_vm)).
      exact Hsp. }
    assert (Hrar : mr !!! Regidx ra_idx = vals 0%nat).
    { rewrite /mr. cbn [ushp_spillback fst].
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
    (* ---- 0x49c  c.addi16sp sp,sp,64 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h1 mr (mword_of_int 0x49c)
              (mword_of_int 4 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hsl Hloc] Hrun").
    { iApply (uis_shp_49c with "Hcode"). }
    { rewrite Hspr Hup.
      iApply (ushp_frame_join sp0 spl 1
                [(ra_idx, mword_of_int 7 : mword 6);
                 (s0_idx, mword_of_int 6 : mword 6);
                 (s1_idx, mword_of_int 5 : mword 6);
                 (s2_idx, mword_of_int 4 : mword 6);
                 (s3_idx, mword_of_int 3 : mword 6);
                 (s4_idx, mword_of_int 2 : mword 6);
                 (s5_idx, mword_of_int 1 : mword 6)]
                vals ltac:(cbn [length]; lia) with "Hsl Hloc"). }
    rewrite Hspr Hup (ushp_pc_step 0x49c 2). iIntros (h2) "Hrun".
    (* ---- 0x49e  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h2
              (<[Regidx csp_rs1 := regval_into_reg sp0]> mr)
              (mword_of_int 0x49e) ra_idx (ret_pc (vals 0%nat)) (8 + (2 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_ne mr (Regidx csp_rs1) (Regidx ra_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite Hrar; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_49e with "Hcode"). }
    iIntros (h3) "Hrun". iApply ("Hcont" $! h3 with "Hrun").
  Qed.

  (* peek's ANSWER.  0 once the cursor has run to [es] -- the byte there is
     the line's terminator and C's [&&] short-circuits -- and otherwise
     whether the byte at the cursor is one of [toks]. *)
  Definition ushp_peek_res (len : nat) (f : nat -> bv 8) (k tlen : nat)
      (tf : nat -> bv 8) : Z :=
    if bool_decide (k < len)%nat
    then (match ushp_find tlen 0%nat tf (f k) with
          | Some _ => 1 | None => 0 end)
    else 0.


  (* ---- peek, the whole function --------------------------------------- *)
  Lemma wp_kshp_peek (h : CpuId) (m : regfile) (dq dw : dfrac)
      (tt : bool) (dt : dfrac)
      (ps s0 toks : Z) (len off tlen : nat) (f tf : nat -> bv 8)
      (w0 : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx a2_idx = mword_of_int toks ->
    (off <= len)%nat ->
    (* the cursor cell currently holds the lexer's position: this is
       what the postcondition's [off] REFERS TO, and without it the
       statement does not mention where the scan starts. *)
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < toks -> toks + Z.of_nat tlen < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ushp_sstr tt dt toks tlen tf -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.peek) (8 + (2 + nn)) -∗
    (uword γd ps
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ushp_sstr tt dt toks tlen tf -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
             = mword_of_int
                 (ushp_peek_res len f
                    (off + ushp_skipws (len - off) off f) tlen tf) ⌝ -∗
         urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (8 + (2 + nn)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ha0 Ha1 Ha2 Hoffle Hw0 Hs0 Hs64 Ht0 Ht64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode Hcur Hstr Hws Htoks Hrun Hcont".
    rewrite shpp_peek.
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
    (* ---- 0x448  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn γt γd γs γfd h m (mword_of_int 0x448)
              (mword_of_int 60 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_448 with "Hcode"). }
    rewrite (ushp_pc_step 0x448 2). iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 8))).
    assert (Hspu : uint spn = uint sp0 - 64).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    set (spl := (mword_of_int (uint sp0 - 56) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 56)
      by (unfold spl; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 1
                 [(ra_idx, mword_of_int 7 : mword 6);
                  (s0_idx, mword_of_int 6 : mword 6);
                  (s1_idx, mword_of_int 5 : mword 6);
                  (s2_idx, mword_of_int 4 : mword 6);
                  (s3_idx, mword_of_int 3 : mword 6);
                  (s4_idx, mword_of_int 2 : mword 6);
                  (s5_idx, mword_of_int 1 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | 5%nat => m !!! Regidx s4_idx
                   | _ => m !!! Regidx s5_idx end).
    (* ---- 0x44a..0x456  the seven spills ---- *)
    iApply (wp_kshp_spill spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x44a | 1%nat => 0x44c
                              | 2%nat => 0x44e | 3%nat => 0x450
                              | 4%nat => 0x452 | 5%nat => 0x454
                              | 6%nat => 0x456 | _ => 0x458 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h1 m1 Hsp1
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ exact (ushp_slot_al (uint sp0) _ Hal8)
                       | unfold vals; cbn;
                         (* NOT [exact (eq_sym (Hm1 _ ltac:(...)))]: with the
                            register left as [_] the nested [ltac:] runs
                            [vm_compute] on a goal whose register is still an
                            EVAR, and that is the 17 GB.  [refine] fixes the
                            evar by unification FIRST and leaves the side
                            condition as a goal.  Measured: 60 s+ vs 0.19 s. *)
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_44a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_44c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_44e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_450 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_452 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_454 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_456 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x458  c.addi4spn s0,sp,64 ---- *)
    iApply (wp_kshp_fp h2 m1 0x458 (mword_of_int 16 : mword 8) (2 + nn)
              with "[] Hrun").
    { iApply (uis_shp_458 with "Hcode"). }
    iIntros (h3 v458) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v458]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    (* ---- 0x45a  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h3 m2 (mword_of_int 0x45a) s4_idx a0_idx
              (mword_of_int ps) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_45a with "Hcode"). }
    rewrite (ushp_pc_step 0x45a 2). iIntros (h4) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x45c  c.mv s2,a1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h4 m3 (mword_of_int 0x45c) s2_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_45c with "Hcode"). }
    rewrite (ushp_pc_step 0x45c 2). iIntros (h5) "Hrun".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                     : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x45e  c.mv s5,a2 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h5 m4 (mword_of_int 0x45e) s5_idx a2_idx
              (mword_of_int toks) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val toks))
              with "[] Hrun").
    { iApply (uis_shp_45e with "Hcode"). }
    rewrite (ushp_pc_step 0x45e 2). iIntros (h6) "Hrun".
    set (m5 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int toks : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx s5_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx s5_idx) (Regidx q) _ Hq)).
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0x460  c.ld s1,0(a0) -- the cursor ---- *)
    iApply (wp_uk_cld γt γd γs γfd h6 m5 (mword_of_int 0x460)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 1 : mword 3) a0_idx s1_idx ps w0 (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_5 (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              Hps8 ltac:(vm_compute; discriminate)
              with "[] Hcur Hrun").
    { iApply (uis_shp_460 with "Hcode"). }
    iIntros "Hcur". rewrite (ushp_pc_step 0x460 2). iIntros (h7) "Hrun".
    set (m6 := <[Regidx s1_idx := regval_into_reg w0]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x462  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc γt γd γs γfd h7 m6 (mword_of_int 0x462)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x2462) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_462 with "Hcode"). }
    rewrite (ushp_pc_step 0x462 4). iIntros (h8) "Hrun".
    set (m7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x2462 : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x466  addi s3,s3,-1114  -- s3 = &whitespace ---- *)
    iApply (wp_uk_addi γt γd γs γfd h8 m7 (mword_of_int 0x466)
              (mword_of_int 2982 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m6 (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x2462
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_466 with "Hcode"). }
    rewrite (ushp_pc_step 0x466 4). iIntros (h9) "Hrun".
    set (m8 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* the register file the scan starts from *)
    assert (Hs1_8 : m8 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat off)).
    { rewrite (Hm8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m5 (Regidx s1_idx) (regval_into_reg w0)).
      exact Hw0. }
    assert (Hs2_8 : m8 !!! Regidx s2_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s2_idx)
               (regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                 : mword 64))). }
    assert (Hs3_8 : m8 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq m7 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    assert (Ha1_8 : m8 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm8 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    assert (Hs4_8 : m8 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hm8 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs5_8 : m8 !!! Regidx s5_idx = mword_of_int toks).
    { rewrite (Hm8 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s5_idx)
               (regval_into_reg (mword_of_int toks : mword 64))). }
    assert (Hsp8 : m8 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    (* the callee-saved registers the prologue and the setup did NOT write *)
    assert (Hkeep8 : forall q : mword 5,
              Regidx q <> Regidx csp_rs1 -> Regidx q <> Regidx s0_idx ->
              Regidx q <> Regidx s1_idx -> Regidx q <> Regidx s2_idx ->
              Regidx q <> Regidx s3_idx -> Regidx q <> Regidx s4_idx ->
              Regidx q <> Regidx s5_idx ->
              m8 !!! Regidx q = m !!! Regidx q).
    { intros q H2 H8 H9 H18 H19 H20 H21.
      rewrite (Hm8 q H19) (Hm7 q H19) (Hm6 q H9) (Hm5 q H21) (Hm4 q H18)
              (Hm3 q H20) (Hm2 q H8). exact (Hm1 q H2). }
    (* ---- 0x46a..0x480  the entry test and the scan ---- *)
    iApply (wp_kshp_peek_enter dq dw s0 len off f nn h9 m8
              Hoffle Hs0 Hs64 Hs1_8 Hs2_8 Hs3_8 Ha1_8
              with "Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h10 mc') "%Hpres %Hs1c Hrun".
    (* [set] folded [kk] into the goal but [Hs1c] is fresh, so fold it too --
       otherwise [lia] sees [kk] and the expansion as two unrelated atoms *)
    assert (Hkkd : (off + ushp_skipws (len - off) off f)%nat = kk)
      by reflexivity.
    rewrite Hkkd in Hs1c.
    assert (Hs4_c : mc' !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (Hpres s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs4_8).
    assert (Hs5_c : mc' !!! Regidx s5_idx = mword_of_int toks)
      by (rewrite (Hpres s5_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs5_8).
    assert (Hsp_c : mc' !!! Regidx csp_rs1 = spn)
      by (rewrite (Hpres csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hsp8).
    (* ---- 0x482  sd s1,0(s4)  --  *ps = s ---- *)
    iApply (wp_uk_sd γt γd γs γfd h10 mc' (mword_of_int 0x482)
              (mword_of_int 0 : mword 12) s4_idx s1_idx ps w0 (2 + nn)
              ltac:(rewrite Hs4_c (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hps8
              with "[] Hcur Hrun").
    { iApply (uis_shp_482 with "Hcode"). }
    iIntros "Hcur". rewrite Hs1c.
    rewrite (ushp_pc_step 0x482 4). iIntros (h11) "Hrun".
    (* ---- 0x486  lbu a1,0(s1) -- a BODY byte, or the terminator ---- *)
    destruct (Nat.eq_dec kk len) as [ Hkend | Hkne ].
    { (* the cursor ran to [es]: the byte is the NUL and peek answers 0 *)
      iDestruct (ustr_nul with "Hstr") as "[Hb Hcl]".
      iApply (wp_uk_lbu γt γd γs γfd h11 mc' (mword_of_int 0x486)
                (mword_of_int 0 : mword 12) s1_idx a1_idx dq
                (s0 + Z.of_nat len) ubyte0 (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs1c Hkend
                        (uint_moi (s0 + Z.of_nat len)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(vm_compute; discriminate)
                with "[] Hb Hrun").
      { iApply (uis_shp_486 with "Hcode"). }
      iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
      rewrite (ushp_pc_step 0x486 4). iIntros (h12) "Hrun".
      set (n9 := <[Regidx a1_idx
                   := regval_into_reg (zero_extend' 64 (ubyte0 : mword 8)
                                       : mword 64)]> mc').
      assert (Hn9 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                      n9 !!! Regidx q = mc' !!! Regidx q)
        by (intros q Hq; exact (upd_ne mc' (Regidx a1_idx) (Regidx q) _ Hq)).
      (* ---- 0x48a  c.li a0,0 ---- *)
      iApply (wp_uk_cli γt γd γs γfd h12 n9 (mword_of_int 0x48a)
                (mword_of_int 0 : mword 6) a0_idx (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_48a with "Hcode"). }
      rewrite (ushp_pc_step 0x48a 2). iIntros (h13) "Hrun".
      set (n10 := <[Regidx a0_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 0 : mword 6)
                          : mword 64)]> n9).
      assert (Hn10 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                       n10 !!! Regidx q = n9 !!! Regidx q)
        by (intros q Hq; exact (upd_ne n9 (Regidx a0_idx) (Regidx q) _ Hq)).
      (* ---- 0x48c  c.bnez a1,0x4a0 -- NOT taken ---- *)
      assert (Ha1_10 : n10 !!! Regidx a1_idx
                       = mword_of_int (bv_unsigned ubyte0)).
      { rewrite (Hn10 a1_idx ltac:(vm_compute; discriminate)).
        rewrite (upd_eq mc' (Regidx a1_idx)
                   (regval_into_reg (zero_extend' 64 (ubyte0 : mword 8)
                                     : mword 64))).
        exact (zext8_moi ubyte0). }
      assert (Htk : false = neq_vec (n10 !!! Regidx a1_idx) zero_reg).
      { rewrite Ha1_10. unfold neq_vec. rewrite (ushp_zext_nul ubyte0).
        rewrite (bool_decide_eq_true_2 (ubyte0 = ubyte0) eq_refl).
        reflexivity. }
      iApply (wp_uk_cbnez γt γd γs γfd h13 n10 (mword_of_int 0x48c)
                (mword_of_int 10 : mword 8) (mword_of_int 3 : mword 3)
                a1_idx false (mword_of_int 0x4a0) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_48c with "Hcode"). }
      rewrite (ushp_pc_step 0x48c 2). iIntros (h14) "Hrun".
      assert (Hspn10 : n10 !!! Regidx csp_rs1 = spn).
      { rewrite (Hn10 csp_rs1 ltac:(vm_compute; discriminate)).
        rewrite (Hn9 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp_c. }
      iApply (wp_kshp_peek_epi sp0 spl vals nn h14 n10
                Hal8 Hlo ltac:(lia) Hsplu Hspn10
                with "Hcode Hsl Hloc Hrun").
      iIntros (hf) "Hrun".
      iApply ("Hcont" with "Hcur Hstr Hws Htoks [] [] Hrun").
      - iPureIntro. intros q Hq.
        cbn [ushp_spillback fst].
        destruct (Z.eq_dec (uint q) 2) as [ E2 | E2 ].
        { rewrite (ushp_ridx_eq q csp_rs1
                     ltac:(rewrite E2; vm_compute; reflexivity)).
          exact (upd_eq _ (Regidx csp_rs1) (regval_into_reg sp0)). }
        assert (Hq2 : Regidx q <> Regidx csp_rs1)
          by (apply ushp_ridx_ne;
              assert (Hc : uint csp_rs1 = 2) by (vm_compute; reflexivity);
              rewrite Hc; exact E2).
        rewrite (upd_ne _ (Regidx csp_rs1) (Regidx q) _ Hq2).
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
        rewrite (Hn10 q (ushp_cs_ne q a0_idx Hq
                           ltac:(vm_compute; reflexivity))).
        rewrite (Hn9 q (ushp_cs_ne q a1_idx Hq
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hpres q Hq Hq9).
        exact (Hkeep8 q Hq2 Hq8 Hq9 Hq18 Hq19 Hq20 Hq21).
      - iPureIntro. cbn [ushp_spillback fst].
        rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
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
        rewrite (upd_eq n9 (Regidx a0_idx)
                   (regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64))).
        unfold ushp_peek_res.
        rewrite (bool_decide_eq_false_2 (kk < len)%nat ltac:(lia)).
        apply bv_eq; vm_compute; reflexivity. }
    (* THE CURSOR IS ON A BODY BYTE: peek asks the token table ---- *)
    assert (Hklt : (kk < len)%nat) by lia.
    iDestruct (ustr_nonul with "Hstr") as %Hnenul.
    iDestruct (ustr_byte γd dq s0 len f kk Hklt with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu γt γd γs γfd h11 mc' (mword_of_int 0x486)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat kk) (f kk) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1c
                      (uint_moi (s0 + Z.of_nat kk)
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_486 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x486 4). iIntros (h12) "Hrun".
    set (n9 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 ((f kk) : mword 8)
                                     : mword 64)]> mc').
    assert (Hn9 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                    n9 !!! Regidx q = mc' !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc' (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x48a  c.li a0,0 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h12 n9 (mword_of_int 0x48a)
              (mword_of_int 0 : mword 6) a0_idx (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_48a with "Hcode"). }
    rewrite (ushp_pc_step 0x48a 2). iIntros (h13) "Hrun".
    set (n10 := <[Regidx a0_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 0 : mword 6)
                        : mword 64)]> n9).
    assert (Hn10 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     n10 !!! Regidx q = n9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n9 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Ha1_10 : n10 !!! Regidx a1_idx
                     = mword_of_int (bv_unsigned (f kk))).
    { rewrite (Hn10 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq mc' (Regidx a1_idx)
                 (regval_into_reg (zero_extend' 64 ((f kk) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f kk)). }
    (* ---- 0x48c  c.bnez a1,0x4a0 -- TAKEN ---- *)
    assert (Htk : true = neq_vec (n10 !!! Regidx a1_idx) zero_reg).
    { rewrite Ha1_10. unfold neq_vec. rewrite (ushp_zext_nul (f kk)).
      rewrite (bool_decide_eq_false_2 (f kk = ubyte0) (Hnenul kk Hklt)).
      reflexivity. }
    iApply (wp_uk_cbnez γt γd γs γfd h13 n10 (mword_of_int 0x48c)
              (mword_of_int 10 : mword 8) (mword_of_int 3 : mword 3)
              a1_idx true (mword_of_int 0x4a0) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_48c with "Hcode"). }
    iIntros (h14) "Hrun".
    (* ---- 0x4a0  c.mv a0,s5 ---- *)
    assert (Hs5_10 : n10 !!! Regidx s5_idx = mword_of_int toks).
    { rewrite (Hn10 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn9 s5_idx ltac:(vm_compute; discriminate)). exact Hs5_c. }
    iApply (wp_uk_cmv γt γd γs γfd h14 n10 (mword_of_int 0x4a0) a0_idx s5_idx
              (mword_of_int toks) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5_10; symmetry; exact (ushp_mv_val toks))
              with "[] Hrun").
    { iApply (uis_shp_4a0 with "Hcode"). }
    rewrite (ushp_pc_step 0x4a0 2). iIntros (h15) "Hrun".
    set (n11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int toks : mword 64)]> n10).
    assert (Hn11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     n11 !!! Regidx q = n10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x4a2  jal a82 <strchr> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h15 n11 (mword_of_int 0x4a2)
              (mword_of_int 1504 : mword 21) ra_idx
              (mword_of_int 0xa82) (mword_of_int 0x4a6) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4a2 with "Hcode"). }
    iIntros (h16) "Hrun".
    set (n12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x4a6 : mword 64)]> n11).
    assert (Hn12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     n12 !!! Regidx q = n11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Ha0_12 : n12 !!! Regidx a0_idx = mword_of_int toks).
    { rewrite (Hn12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq n10 (Regidx a0_idx)
               (regval_into_reg (mword_of_int toks : mword 64))). }
    assert (Ha1_12 : n12 !!! Regidx a1_idx
                     = mword_of_int (bv_unsigned (f kk))).
    { rewrite (Hn12 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn11 a1_idx ltac:(vm_compute; discriminate)). exact Ha1_10. }
    assert (Eret : ret_pc (n12 !!! Regidx ra_idx) = mword_of_int 0x4a6).
    { rewrite (upd_eq n11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x4a6 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_strchr.
    iApply (wp_kshp_strchr h16 n12 tt dt toks tlen tf (f kk) nn
              Ha0_12 Ha1_12 ltac:(lia) ltac:(unfold Z64 in *; lia)
              with "Hcode Htoks Hrun").
    iIntros "Htoks" (h17 n13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret.
    (* ---- 0x4a6  snez a0,a0  --  sltu a0,x0,a0 ---- *)
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    assert (Hchrb : 0 <= ushp_chr toks tlen 0%nat tf (f kk) < Z64).
    { unfold ushp_chr.
      destruct (ushp_find tlen 0%nat tf (f kk)) as [ jj | ] eqn:Ej;
        [ | unfold Z64; lia ].
      pose proof (ushp_find_ge tlen 0%nat tf (f kk) jj Ej) as Hjr.
      unfold Z64 in *. lia. }
    iApply (wp_uk_sltu γt γd γs γfd h17 n13 (mword_of_int 0x4a6)
              x0_idx a0_idx a0_idx
              (mword_of_int (if Z.ltb 0 (ushp_chr toks tlen 0%nat tf (f kk))
                             then 1 else 0)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hx0 Ha0_13; symmetry;
                    exact (ushp_snez_val
                             (ushp_chr toks tlen 0%nat tf (f kk)) Hchrb))
              with "[] Hrun").
    { iApply (uis_shp_4a6 with "Hcode"). }
    rewrite (ushp_pc_step 0x4a6 4). iIntros (h18) "Hrun".
    set (n14 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int
                          (if Z.ltb 0 (ushp_chr toks tlen 0%nat tf (f kk))
                           then 1 else 0) : mword 64)]> n13).
    assert (Hn14 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     n14 !!! Regidx q = n13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n13 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x4aa  c.j 0x48e ---- *)
    iApply (wp_uk_cj γt γd γs γfd h18 n14 (mword_of_int 0x4aa)
              (mword_of_int 2034 : mword 11) (mword_of_int 0x48e) (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_4aa with "Hcode"). }
    iIntros (h19) "Hrun".
    assert (Hspn14 : n14 !!! Regidx csp_rs1 = spn).
    { rewrite (Hn14 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hn12 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn11 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn10 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hn9 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp_c. }
    iApply (wp_kshp_peek_epi sp0 spl vals nn h19 n14
              Hal8 Hlo ltac:(lia) Hsplu Hspn14
              with "Hcode Hsl Hloc Hrun").
    iIntros (hf) "Hrun".
    iApply ("Hcont" with "Hcur Hstr Hws Htoks [] [] Hrun").
    - iPureIntro. intros q Hq.
      cbn [ushp_spillback fst].
      destruct (Z.eq_dec (uint q) 2) as [ E2 | E2 ].
      { rewrite (ushp_ridx_eq q csp_rs1
                   ltac:(rewrite E2; vm_compute; reflexivity)).
        exact (upd_eq _ (Regidx csp_rs1) (regval_into_reg sp0)). }
      assert (Hq2 : Regidx q <> Regidx csp_rs1)
        by (apply ushp_ridx_ne;
            assert (Hc : uint csp_rs1 = 2) by (vm_compute; reflexivity);
            rewrite Hc; exact E2).
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx q) _ Hq2).
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
      rewrite (Hn14 q (ushp_cs_ne q a0_idx Hq
                         ltac:(vm_compute; reflexivity))).
      rewrite (Hcs1213 q Hq).
      rewrite (Hn12 q Hqra).
      rewrite (Hn11 q (ushp_cs_ne q a0_idx Hq
                         ltac:(vm_compute; reflexivity))).
      rewrite (Hn10 q (ushp_cs_ne q a0_idx Hq
                         ltac:(vm_compute; reflexivity))).
      rewrite (Hn9 q (ushp_cs_ne q a1_idx Hq
                        ltac:(vm_compute; reflexivity))).
      rewrite (Hpres q Hq Hq9).
      exact (Hkeep8 q Hq2 Hq8 Hq9 Hq18 Hq19 Hq20 Hq21).
    - iPureIntro. cbn [ushp_spillback fst].
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
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
      rewrite (upd_eq n13 (Regidx a0_idx)
                 (regval_into_reg
                    (mword_of_int
                       (if Z.ltb 0 (ushp_chr toks tlen 0%nat tf (f kk))
                        then 1 else 0) : mword 64))).
      unfold ushp_peek_res.
      rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt).
      unfold ushp_chr.
      destruct (ushp_find tlen 0%nat tf (f kk)) as [ jj | ] eqn:Ej.
      + assert (Hgt : (0 <? toks + Z.of_nat jj) = true)
          by (apply Z.ltb_lt; lia).
        rewrite Hgt. reflexivity.
      + assert (Hgt : (0 <? 0) = false) by reflexivity.
        rewrite Hgt. reflexivity.
  Qed.



  (* ===================================================================== *)
  (* §8b THE SEVEN TOKEN TABLES, AS ONE PERSISTENT PREMISE.                 *)
  (*                                                                       *)
  (* peek's third argument is a string literal at all seven call sites, and *)
  (* §2c established that a literal is a TEXT-half string.  All seven come  *)
  (* out of the SAME resource -- [UCodeShP.shp_rodata], the read-only image *)
  (* -- which is persistent, so a walk carries ONE premise for all of them  *)
  (* and never has to thread a table in and out of a call.                  *)
  (*                                                                       *)
  (* THE BYTES ARE NOT WRITTEN OUT.  [ushp_lit base] reads them out of the  *)
  (* dump, [ushp_lit_ok] decides whether that is a C string of that length, *)
  (* and [ushp_lit_sym] decides whether every byte of it is one of sh-s     *)
  (* seven symbol characters -- one [vm_compute] each, and the two together *)
  (* are exactly what a REFUTED peek needs.  UkShDiag.v does the same for   *)
  (* the printer's format strings; this is that idiom at a second consumer, *)
  (* which is the third leg of relocation ask 3.                            *)
  (* ===================================================================== *)

  (* the byte function of the literal based at [base] *)
  Definition ushp_lit (base : Z) : nat -> bv 8 :=
    fun j => default ubyte0 (shp_ro !! (base + Z.of_nat j)%Z).

  (* ...and what makes it a C string of length [len] *)
  Definition ushp_lit_ok (base : Z) (len : nat) : bool :=
    forallb (fun j => match shp_ro !! (base + Z.of_nat j)%Z with
                      | Some b => negb (Z.eqb (bv_unsigned b) 0)
                      | None => false
                      end)
            (seq 0 len)
    && match shp_ro !! (base + Z.of_nat len)%Z with
       | Some b => Z.eqb (bv_unsigned b) 0
       | None => false
       end.

  (* ...and that every byte of it is one of [ushp_sym_bytes] *)
  Definition ushp_lit_sym (base : Z) (len : nat) : bool :=
    forallb (fun j => ushp_is_sym (ushp_lit base j)) (seq 0 len).

  Lemma ushp_lit_ok_body (base : Z) (len j : nat) :
    ushp_lit_ok base len = true -> (j < len)%nat ->
    shp_ro !! (base + Z.of_nat j)%Z = Some (ushp_lit base j)
    /\ ushp_lit base j <> ubyte0.
  Proof.
    unfold ushp_lit_ok, ushp_lit. intros H Hj.
    apply andb_true_iff in H as [ H _ ].
    rewrite forallb_forall in H.
    specialize (H j ltac:(apply in_seq; lia)).
    destruct (shp_ro !! (base + Z.of_nat j)%Z) as [ b | ] eqn:Hb;
      [ | discriminate ].
    apply negb_true_iff, Z.eqb_neq in H.
    cbn [default from_option id]. split; [ reflexivity | ].
    intro He. apply H. rewrite He. vm_compute. reflexivity.
  Qed.

  Lemma ushp_lit_ok_nul (base : Z) (len : nat) :
    ushp_lit_ok base len = true ->
    shp_ro !! (base + Z.of_nat len)%Z = Some ubyte0.
  Proof.
    unfold ushp_lit_ok. intro H.
    apply andb_true_iff in H as [ _ H ].
    destruct (shp_ro !! (base + Z.of_nat len)%Z) as [ b | ] eqn:Hb;
      [ | discriminate ].
    apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H.
    vm_compute. reflexivity.
  Qed.

  (* THE TABLE, AS THE RESOURCE peek TAKES.  [true] is the text half. *)
  Lemma ushp_lit_str (base : Z) (len : nat) (dq : dfrac) :
    ushp_lit_ok base len = true ->
    Z.of_nat len < 2 ^ 31 ->
    shp_rodata γt -∗ ushp_sstr true dq base len (ushp_lit base).
  Proof.
    intros Hok Hlen. iIntros "#Hro".
    rewrite ushp_sstr_text /shp_rodata.
    iApply (utext_str_of_img γt shp_ro base len (ushp_lit base)).
    - intros j Hj. exact (proj2 (ushp_lit_ok_body base len j Hok Hj)).
    - exact Hlen.
    - intros j Hj. exact (proj1 (ushp_lit_ok_body base len j Hok Hj)).
    - exact (ushp_lit_ok_nul base len Hok).
    - iExact "Hro".
  Qed.

  (* [strchr] misses a table none of whose bytes is the one looked for *)
  Lemma ushp_find_none (n i : nat) (f : nat -> bv 8) (b : bv 8) :
    (forall j : nat, (i <= j < i + n)%nat -> f j <> b) ->
    ushp_find n i f b = None.
  Proof.
    revert i. induction n as [| n IH ]; intros i Hne; [ reflexivity | ].
    cbn [ushp_find].
    destruct (bool_decide (f i = b)) eqn:Hb.
    { apply bool_decide_eq_true in Hb. exfalso. exact (Hne i ltac:(lia) Hb). }
    apply IH. intros j Hj. exact (Hne j ltac:(lia)).
  Qed.

  (* THE ONE FACT THE FIVE REFUTED PEEKS NEED.  On a line with no symbol
     byte, a peek for a table of symbol bytes is 0 -- at the end of the
     line because the cursor has run out, and inside it because the byte
     there is not in the table. *)
  Lemma ushp_peek_res_sym (len : nat) (f : nat -> bv 8) (k tlen : nat)
      (base : Z) :
    ushp_no_symbols len f -> ushp_lit_sym base tlen = true ->
    ushp_peek_res len f k tlen (ushp_lit base) = 0.
  Proof.
    intros Hnos Hsym. rewrite /ushp_peek_res.
    destruct (bool_decide (k < len)%nat) eqn:Hk; [ | reflexivity ].
    apply bool_decide_eq_true in Hk.
    rewrite (ushp_find_none tlen 0%nat (ushp_lit base) (f k)).
    - reflexivity.
    - intros j Hj He.
      rewrite /ushp_lit_sym forallb_forall in Hsym.
      specialize (Hsym j ltac:(apply in_seq; lia)).
      rewrite He (Hnos k Hk) in Hsym. discriminate.
  Qed.

  (* ---- the seven bases, named ------------------------------------------ *)
  Definition ushp_T_redir : Z := 0x12f0.   (* the two redirection bytes, parseredirs *)
  Definition ushp_T_block : Z := 0x12f8.   (* the open paren, parseexec *)
  Definition ushp_T_arg   : Z := 0x1318.   (* the four argument-loop stoppers, parseexec *)
  Definition ushp_T_pipe  : Z := 0x1320.   (* the pipe byte, parsepipe *)
  Definition ushp_T_back  : Z := 0x1328.   (* the ampersand, parseline *)
  Definition ushp_T_list  : Z := 0x1330.   (* the semicolon, parseline *)
  Definition ushp_T_none  : Z := 0x1288.   (* the empty table, parsecmd *)

  (* ...and the two decidable checks, discharged once each *)
  Lemma ushp_T_redir_ok : ushp_lit_ok ushp_T_redir 2 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_block_ok : ushp_lit_ok ushp_T_block 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_arg_ok   : ushp_lit_ok ushp_T_arg 4 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_pipe_ok  : ushp_lit_ok ushp_T_pipe 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_back_ok  : ushp_lit_ok ushp_T_back 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_list_ok  : ushp_lit_ok ushp_T_list 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_none_ok  : ushp_lit_ok ushp_T_none 0 = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma ushp_T_redir_sym : ushp_lit_sym ushp_T_redir 2 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_block_sym : ushp_lit_sym ushp_T_block 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_arg_sym   : ushp_lit_sym ushp_T_arg 4 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_pipe_sym  : ushp_lit_sym ushp_T_pipe 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_back_sym  : ushp_lit_sym ushp_T_back 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_list_sym  : ushp_lit_sym ushp_T_list 1 = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma ushp_T_none_sym  : ushp_lit_sym ushp_T_none 0 = true.
  Proof. reflexivity. Qed.

  (* ===================================================================== *)
  (* §7 execcmd @0x1d2 -- 19 instructions, a four-word frame, NO branch.    *)
  (*                                                                       *)
  (*   struct cmd *execcmd(void) {                                          *)
  (*     struct execcmd *cmd;                                               *)
  (*     cmd = malloc(sizeof( *cmd));                                       *)
  (*     memset(cmd, 0, sizeof( *cmd));                                     *)
  (*     cmd->type = EXEC;                                                  *)
  (*     return (struct cmd * )cmd;  }                                      *)
  (*                                                                       *)
  (* THE FIRST LEMMA IN THIS FILE THAT CARRIES [ushp_malloc_ok], and the    *)
  (* only one that carries it directly: parseexec, parsepipe, parseline and *)
  (* parsecmd will carry it THROUGH this lemma.  Everything above §7 is     *)
  (* unconditional; this one is not, and says so here rather than only in   *)
  (* the lane report.                                                       *)
  (*                                                                       *)
  (* WHAT THE POSTCONDITION SAYS, and why it is the honest reading.  The    *)
  (* node comes back as [ushp_exec_at s0 p []] -- an EXEC node whose token  *)
  (* list is EMPTY.  That is not a weakening: parseexec fills the slots     *)
  (* itself, one per [gettoken], and the invariant it runs its argument     *)
  (* loop on is this predicate at the tokens recorded SO FAR.  The empty    *)
  (* list is the loop's base case, and the NULL cap it demands at slot 0 is *)
  (* exactly what the [memset] zeroed -- which is why the whole stage was   *)
  (* blocked on [wp_ksh_memset]'s postcondition and is not any more.  [s0]  *)
  (* is unconstrained because an empty token list mentions no line at all.  *)
  (*                                                                       *)
  (* THE BUDGET IS THE CALL CHAIN: four words of execcmd's own frame on top *)
  (* of malloc's ten (its 64-byte frame plus [free]/[sbrk]'s two), and      *)
  (* memset's two fit inside those ten.                                     *)
  (* ===================================================================== *)

  Lemma shpp_malloc : ShSyms.malloc = 0x118c.
  Proof. unfold ShSyms.malloc. reflexivity. Qed.
  Lemma shpp_memset : ShSyms.memset = 0xa5c.
  Proof. unfold ShSyms.memset. reflexivity. Qed.

  Lemma wp_kshp_execcmd (h : CpuId) (m : regfile) (s0 : Z) (nn : nat) :
    shp_code γt -∗
    UMalloc -∗
    urun γt γd γs γfd h m (mword_of_int ShSyms.execcmd) (4 + (10 + nn)) -∗
    (∀ (h' : CpuId) (m' : regfile) (p : Z),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
       ⌜ 0 < p /\ p mod 16 = 0 /\ p + 168 < 2 ^ 38 ⌝ -∗
       ushp_exec_pre s0 p [] -∗
       UMalloc' -∗
       urun γt γd γs γfd h' m' (ret_pc (m !!! Regidx ra_idx)) (4 + (10 + nn)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode HM Hrun Hcont".
    iDestruct (ushp_code_shk γt with "Hcode") as "#Hkcode".
    rewrite shpp_execcmd.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 32 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    (* ---- 0x1d2  c.addi sp,sp,-32 -- THE PUSH ---- *)
    iApply (wp_uk_caddi_sp_dn γt γd γs γfd h m (mword_of_int 0x1d2)
              (mword_of_int 32 : mword 6) 4 (10 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_1d2 with "Hcode"). }
    rewrite (ushp_pc_step 0x1d2 2). iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 4))).
    assert (Hspu : uint spn = uint sp0 - 32).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 4)) with (-32) by lia.
      exact (uv_avi_neg sp0 32 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    (* ---- the frame: three spill slots on top of one unused local ---- *)
    set (spl := (mword_of_int (uint sp0 - 24) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 24)
      by (unfold spl; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 1
                 [(ra_idx, mword_of_int 3 : mword 6);
                  (s0_idx, mword_of_int 2 : mword 6);
                  (s1_idx, mword_of_int 1 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    (* the one pure fact per spill instruction, at concrete numbers *)
    assert (Hoff : forall (i : nat) (r : mword 5) (u : mword 6),
              [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)] !! i = Some (r, u) ->
              (uint sp0 - 8 * (Z.of_nat i + 1)) = uint spn + uoff_sdsp u /\
              (uint sp0 - 8 * (Z.of_nat i + 1)) mod 8 = 0 /\
              unot_sp r /\ uint r <> 0).
    { intros i r u Hi.
      destruct i as [| [| [| i ]]]; cbn in Hi; try discriminate Hi;
        injection Hi as Hr Hu0; subst.
      - assert (Hu : uoff_sdsp (mword_of_int 3 : mword 6) = 24)
          by (vm_compute; reflexivity).
        rewrite Hu Hspu.
        repeat split; [ lia | exact (ushp_slot_al (uint sp0) 0 Hal8)
                      | unfold unot_sp; vm_compute; discriminate
                      | vm_compute; discriminate ].
      - assert (Hu : uoff_sdsp (mword_of_int 2 : mword 6) = 16)
          by (vm_compute; reflexivity).
        rewrite Hu Hspu.
        repeat split; [ lia | exact (ushp_slot_al (uint sp0) 1 Hal8)
                      | unfold unot_sp; vm_compute; discriminate
                      | vm_compute; discriminate ].
      - assert (Hu : uoff_sdsp (mword_of_int 1 : mword 6) = 8)
          by (vm_compute; reflexivity).
        rewrite Hu Hspu.
        repeat split; [ lia | exact (ushp_slot_al (uint sp0) 2 Hal8)
                      | unfold unot_sp; vm_compute; discriminate
                      | vm_compute; discriminate ]. }
    (* ---- 0x1d4..0x1d8  the three spills ---- *)
    iApply (wp_kshp_spill spn (10 + nn)
              [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x1d4 | 1%nat => 0x1d6
                              | 2%nat => 0x1d8 | _ => 0x1da end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              (fun i : nat => match i with
                              | 0%nat => m !!! Regidx ra_idx
                              | 1%nat => m !!! Regidx s0_idx
                              | _ => m !!! Regidx s1_idx end)
              h1 m1 Hsp1
              ltac:(intros i Hi; destruct i as [| [| [| i ]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct (Hoff i r u Hi) as [ H1 [ H2 [ H3 H4 ]]];
                    split; [ exact H1 | split; [ exact H2 | ] ];
                    destruct i as [| [| [| i ]]]; cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst; cbn;
                    [ exact (eq_sym (Hm1 ra_idx ltac:(vm_compute; discriminate)))
                    | exact (eq_sym (Hm1 s0_idx ltac:(vm_compute; discriminate)))
                    | exact (eq_sym (Hm1 s1_idx ltac:(vm_compute; discriminate))) ])
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_1d4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1d6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1d8 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x1da  c.addi4spn s0,sp,32 ---- *)
    iApply (wp_uk_caddi4spn γt γd γs γfd h2 m1 (mword_of_int 0x1da)
              (mword_of_int 0 : mword 3) (mword_of_int 8 : mword 8) s0_idx
              (add_vec (m1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))
              (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              eq_refl
              with "[] Hrun").
    { iApply (uis_shp_1da with "Hcode"). }
    rewrite (ushp_pc_step 0x1da 2). iIntros (h3) "Hrun".
    set (m2 := <[Regidx s0_idx
                 := regval_into_reg
                      (add_vec (m1 !!! Regidx csp_rs1)
                         (sign_extend' 64
                            (caddi4spn_imm (mword_of_int 8 : mword 8))))]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = spn)
      by (rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp1).
    (* ---- 0x1dc  li a0,168 ---- *)
    assert (E168 : (sign_extend' 64 (mword_of_int 168 : mword 12) : mword 64)
                   = mword_of_int 168)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_li γt γd γs γfd h3 m2 (mword_of_int 0x1dc)
              (mword_of_int 168 : mword 12) a0_idx (mword_of_int 168) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite E168; symmetry; exact (ushp_mv_val 168))
              with "[] Hrun").
    { iApply (uis_shp_1dc with "Hcode"). }
    rewrite (ushp_pc_step 0x1dc 4). iIntros (h4) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 168 : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x1e0  jal 118c <malloc> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h4 m3 (mword_of_int 0x1e0)
              (mword_of_int 4012 : mword 21) ra_idx
              (mword_of_int 0x118c) (mword_of_int 0x1e4) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_1e0 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x1e4 : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int 168).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx a0_idx)
               (regval_into_reg (mword_of_int 168 : mword 64))). }
    assert (Eret1 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x1e4).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x1e4 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_malloc.
    (* ---- malloc(168) -- THE HYPOTHESIS, and this lemma's only taint ---- *)
    iApply (ushp_malloc_ok h5 m4 168 nn Ha0_4 ltac:(lia)
              ltac:(lia) with "Hcode HM Hrun").
    iIntros (h6 m5 p g) "%Hcs45 %Ha0_5 %Hpb Hbs HM' Hrun".
    rewrite Eret1.
    destruct Hpb as [ Hp0 [ Hp16 Hpsz ] ].
    assert (H38 : (2:Z) ^ 38 = 274877906944) by (vm_compute; reflexivity).
    assert (Hp64 : 0 <= p < Z64)
      by (rewrite H38 in Hpsz; unfold Z64; lia).
    assert (Hp8 : p mod 8 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 8 16 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp16 ]. }
    assert (Hp4 : p mod 4 = 0).
    { apply Z.mod_divide; [ lia | ].
      apply (Z.divide_trans 4 8 p); [ exists 2; lia | ].
      apply Z.mod_divide; [ lia | exact Hp8 ]. }
    assert (E168n : Z.to_nat 168 = 168%nat) by (vm_compute; reflexivity).
    rewrite E168n.
    (* ---- 0x1e4  c.mv s1,a0 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h6 m5 (mword_of_int 0x1e4) s1_idx a0_idx
              (mword_of_int p) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_5; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_1e4 with "Hcode"). }
    rewrite (ushp_pc_step 0x1e4 2). iIntros (h7) "Hrun".
    set (m6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int p : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hq)).
    assert (Hs1_6 : m6 !!! Regidx s1_idx = mword_of_int p)
      by exact (upd_eq m5 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int p : mword 64))).
    (* ---- 0x1e6  li a2,168 ---- *)
    iApply (wp_uk_li γt γd γs γfd h7 m6 (mword_of_int 0x1e6)
              (mword_of_int 168 : mword 12) a2_idx (mword_of_int 168) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite E168; symmetry; exact (ushp_mv_val 168))
              with "[] Hrun").
    { iApply (uis_shp_1e6 with "Hcode"). }
    rewrite (ushp_pc_step 0x1e6 4). iIntros (h8) "Hrun".
    set (m7 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 168 : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x1ea  c.li a1,0 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h8 m7 (mword_of_int 0x1ea)
              (mword_of_int 0 : mword 6) a1_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_1ea with "Hcode"). }
    rewrite (ushp_pc_step 0x1ea 2). iIntros (h9) "Hrun".
    set (m8 := <[Regidx a1_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x1ec  jal a5c <memset> ---- *)
    iApply (wp_uk_jal γt γd γs γfd h9 m8 (mword_of_int 0x1ec)
              (mword_of_int 2160 : mword 21) ra_idx
              (mword_of_int 0xa5c) (mword_of_int 0x1f0) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_1ec with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m9 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x1f0 : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Ha1_9 : m9 !!! Regidx a1_idx = (mword_of_int 0 : mword 64)).
    { rewrite (Hm9 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m7 (Regidx a1_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_9 : m9 !!! Regidx a0_idx = mword_of_int p).
    { rewrite (Hm9 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 a0_idx ltac:(vm_compute; discriminate)). exact Ha0_5. }
    assert (Ha2_9 : m9 !!! Regidx a2_idx = mword_of_int (Z.of_nat 168)).
    { rewrite (Hm9 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 a2_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m6 (Regidx a2_idx)
                 (regval_into_reg (mword_of_int 168 : mword 64))).
      now f_equal. }
    assert (Eret2 : ret_pc (m9 !!! Regidx ra_idx) = mword_of_int 0x1f0).
    { rewrite (upd_eq m8 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x1f0 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_memset.
    (* ---- memset(cmd, 0, 168) -- UkSh.v's, across the code bridge ---- *)
    iApply (wp_ksh_memset γt γd γs γfd h10 m9 p 168%nat g (8 + nn)
              Ha0_9 Ha2_9 ltac:(lia) ltac:(unfold Z31; lia)
              with "Hkcode Hbs Hrun").
    iIntros "Hbs" (h11 m10) "%Hcs910 Hrun".
    rewrite Eret2 Ha1_9.
    assert (Eb0 : nth_byte (mword_of_int 0 : mword 64) 0%nat = ubyte0)
      by (vm_compute; reflexivity).
    rewrite Eb0.
    (* ---- the node's four slices: type, padding, argv, eargv ---- *)
    iDestruct (ushp_peel0 p (p + 4) 4 164 ltac:(lia) with "Hbs")
      as "[Hty Hbs]".
    iDestruct (ushp_peel0 (p + 4) (p + 8) 4 160 ltac:(lia) with "Hbs")
      as "[Hpad Hbs]".
    iDestruct (ushp_peel0 (p + 8) (p + 88) 80 80 ltac:(lia) with "Hbs")
      as "[Hav Hev]".
    (* ---- 0x1f0  c.li a5,1 ---- *)
    iApply (wp_uk_cli γt γd γs γfd h11 m10 (mword_of_int 0x1f0)
              (mword_of_int 1 : mword 6) a5_idx (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_1f0 with "Hcode"). }
    rewrite (ushp_pc_step 0x1f0 2). iIntros (h12) "Hrun".
    set (m11 := <[Regidx a5_idx
                  := regval_into_reg
                       (sign_extend' 64 (mword_of_int 1 : mword 6)
                        : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_11 : m11 !!! Regidx a5_idx = (mword_of_int 1 : mword 64)).
    { rewrite (upd_eq m10 (Regidx a5_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hs1_11 : m11 !!! Regidx s1_idx = mword_of_int p).
    { rewrite (Hm11 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 s1_idx ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_6. }
    (* ---- 0x1f2  c.sw a5,0(s1)  --  cmd->type = EXEC ---- *)
    iApply (wp_uk_csw γt γd γs γfd h12 m11 (mword_of_int 0x1f2)
              (mword_of_int 0 : mword 5) (mword_of_int 1 : mword 3)
              (mword_of_int 7 : mword 3) s1_idx a5_idx p
              (mword_of_int 0 : mword 64) (10 + nn)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Hs1_11 (uint_moi p Hp64);
                    vm_compute uoff_c4; lia)
              Hp4
              with "[] [Hty] Hrun").
    { iApply (uis_shp_1f2 with "Hcode"). }
    { iApply (ushp_ubytes_ext p 4 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hty").
      intros j Hj. rewrite (ushp_nth_byte_zero j ltac:(lia)). reflexivity. }
    iIntros "Hty". rewrite Ha5_11.
    rewrite (ushp_pc_step 0x1f2 2). iIntros (h13) "Hrun".
    (* ---- 0x1f4  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv γt γd γs γfd h13 m11 (mword_of_int 0x1f4) a0_idx s1_idx
              (mword_of_int p) (10 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_11; symmetry; exact (ushp_mv_val p))
              with "[] Hrun").
    { iApply (uis_shp_1f4 with "Hcode"). }
    rewrite (ushp_pc_step 0x1f4 2). iIntros (h14) "Hrun".
    set (m12 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int p : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hsp12 : m12 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm12 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm11 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs910 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm9 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs45 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
    (* ---- 0x1f6..0x1fa  the three restores ---- *)
    iApply (wp_kshp_restore spn (10 + nn)
              [(ra_idx, mword_of_int 3 : mword 6);
               (s0_idx, mword_of_int 2 : mword 6);
               (s1_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x1f6 | 1%nat => 0x1f8
                              | 2%nat => 0x1fa | _ => 0x1fc end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              (fun i : nat => match i with
                              | 0%nat => m !!! Regidx ra_idx
                              | 1%nat => m !!! Regidx s0_idx
                              | _ => m !!! Regidx s1_idx end)
              h14 m12 Hsp12
              ltac:(intros i Hi; destruct i as [| [| [| i ]]];
                    cbn in Hi |- *; try reflexivity; lia)
              Hoff
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_1f6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1f8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_1fa with "Hcode") | done ]. }
    iIntros "Hsl" (h15) "Hrun". cbn [length ushp_spillback fst].
    set (me := <[Regidx s1_idx := regval_into_reg (m !!! Regidx s1_idx)]>
                 (<[Regidx s0_idx := regval_into_reg (m !!! Regidx s0_idx)]>
                    (<[Regidx ra_idx := regval_into_reg (m !!! Regidx ra_idx)]>
                       m12))).
    assert (Hspe : me !!! Regidx csp_rs1 = spn).
    { rewrite /me.
      rewrite (upd_ne _ (Regidx s1_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx csp_rs1) _
                 ltac:(vm_compute; discriminate)). exact Hsp12. }
    assert (Hup : add_vec_int spn (8 * Z.of_nat 4) = sp0).
    { apply bv_eq.
      rewrite (uv_avi_pos spn (8 * Z.of_nat 4) ltac:(lia)
                 ltac:(rewrite <- uint_unsigned; lia)).
      rewrite <- !uint_unsigned. lia. }
    (* ---- 0x1fc  c.addi16sp sp,sp,32 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up γt γd γs γfd h15 me (mword_of_int 0x1fc)
              (mword_of_int 2 : mword 6) 4 (10 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hsl Hloc] Hrun").
    { iApply (uis_shp_1fc with "Hcode"). }
    { rewrite Hspe Hup.
      iApply (ushp_frame_join sp0 spl 1
                [(ra_idx, mword_of_int 3 : mword 6);
                 (s0_idx, mword_of_int 2 : mword 6);
                 (s1_idx, mword_of_int 1 : mword 6)]
                (fun i : nat => match i with
                                | 0%nat => m !!! Regidx ra_idx
                                | 1%nat => m !!! Regidx s0_idx
                                | _ => m !!! Regidx s1_idx end)
                ltac:(cbn [length]; lia) with "Hsl Hloc"). }
    rewrite Hspe Hup (ushp_pc_step 0x1fc 2). iIntros (h16) "Hrun".
    set (mf := <[Regidx csp_rs1 := regval_into_reg sp0]> me).
    assert (Hraf : mf !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { rewrite /mf (upd_ne me (Regidx csp_rs1) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /me (upd_ne _ (Regidx s1_idx) (Regidx ra_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx ra_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m12 (Regidx ra_idx)
               (regval_into_reg (m !!! Regidx ra_idx))). }
    (* ---- 0x1fe  c.jr ra ---- *)
    iApply (wp_uk_cjr γt γd γs γfd h16 mf (mword_of_int 0x1fe) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) (4 + (10 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hraf; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_1fe with "Hcode"). }
    iIntros (h17) "Hrun".
    (* ---- what the caller reads back ---- *)
    iApply ("Hcont" $! h17 mf p with "[] [] [] [Hty Hpad Hav Hev] HM' Hrun").
    - iPureIntro. intros q Hq.
      destruct (Z.eq_dec (uint q) 2) as [ Eq2 | Eq2 ].
      { rewrite (ushp_ridx_eq q csp_rs1
                   ltac:(rewrite Eq2; vm_compute; reflexivity)).
        rewrite /mf. exact (upd_eq me (Regidx csp_rs1)
                              (regval_into_reg sp0)). }
      destruct (Z.eq_dec (uint q) 8) as [ Eq8 | Eq8 ].
      { rewrite (ushp_ridx_eq q s0_idx
                   ltac:(rewrite Eq8; vm_compute; reflexivity)).
        rewrite /mf (upd_ne me (Regidx csp_rs1) (Regidx s0_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /me (upd_ne _ (Regidx s1_idx) (Regidx s0_idx) _
                       ltac:(vm_compute; discriminate)).
        exact (upd_eq _ (Regidx s0_idx)
                 (regval_into_reg (m !!! Regidx s0_idx))). }
      destruct (Z.eq_dec (uint q) 9) as [ Eq9 | Eq9 ].
      { rewrite (ushp_ridx_eq q s1_idx
                   ltac:(rewrite Eq9; vm_compute; reflexivity)).
        rewrite /mf (upd_ne me (Regidx csp_rs1) (Regidx s1_idx) _
                       ltac:(vm_compute; discriminate)).
        rewrite /me. exact (upd_eq _ (Regidx s1_idx)
                              (regval_into_reg (m !!! Regidx s1_idx))). }
      assert (Hqsp : Regidx q <> Regidx csp_rs1)
        by (apply ushp_ridx_ne;
            assert (Hc : uint csp_rs1 = 2) by (vm_compute; reflexivity);
            rewrite Hc; exact Eq2).
      assert (Hqs0 : Regidx q <> Regidx s0_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s0_idx = 8) by (vm_compute; reflexivity);
            rewrite Hc; exact Eq8).
      assert (Hqs1 : Regidx q <> Regidx s1_idx)
        by (apply ushp_ridx_ne;
            assert (Hc : uint s1_idx = 9) by (vm_compute; reflexivity);
            rewrite Hc; exact Eq9).
      assert (Hqra : Regidx q <> Regidx ra_idx)
        by exact (ushp_cs_ne q ra_idx Hq ltac:(vm_compute; reflexivity)).
      rewrite /mf (upd_ne me (Regidx csp_rs1) (Regidx q) _ Hqsp).
      rewrite /me (upd_ne _ (Regidx s1_idx) (Regidx q) _ Hqs1).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx q) _ Hqs0).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx q) _ Hqra).
      rewrite (Hm12 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm11 q (ushp_cs_ne q a5_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hcs910 q Hq).
      rewrite (Hm9 q Hqra).
      rewrite (Hm8 q (ushp_cs_ne q a1_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm7 q (ushp_cs_ne q a2_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm6 q Hqs1).
      rewrite (Hcs45 q Hq).
      rewrite (Hm4 q Hqra).
      rewrite (Hm3 q (ushp_cs_ne q a0_idx Hq ltac:(vm_compute; reflexivity))).
      rewrite (Hm2 q Hqs0). exact (Hm1 q Hqsp).
    - iPureIntro.
      rewrite /mf (upd_ne me (Regidx csp_rs1) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /me (upd_ne _ (Regidx s1_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx s0_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite (upd_ne _ (Regidx ra_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      exact (upd_eq m11 (Regidx a0_idx)
               (regval_into_reg (mword_of_int p : mword 64))).
    - iPureIntro. exact (conj Hp0 (conj Hp16 Hpsz)).
    - rewrite /ushp_exec_pre /ushp_type_at.
      iSplitR; [ iPureIntro; cbn [length]; lia | ].
      iSplitR; [ iPureIntro; exact Hp0 | ].
      iSplitR; [ iPureIntro; exact Hp8 | ].
      iSplitL "Hty Hpad".
      + iSplitL "Hty".
        * iApply (ushp_ubytes_ext p 4
                    (nth_byte (mword_of_int 1 : mword 64))
                    (nth_byte (mword_of_int 1 : mword 32)) with "Hty").
          intros j Hj. destruct j as [| [| [| [| j ]]]];
            [ vm_compute; reflexivity | vm_compute; reflexivity
            | vm_compute; reflexivity | vm_compute; reflexivity | lia ].
        * iExists (fun _ : nat => ubyte0). iExact "Hpad".
      + iSplitL "Hav".
        * iApply (ushp_slots_nil0 s0 (p + 8) fst (fun _ : nat => ubyte0)
                    ltac:(intros j _; reflexivity) with "Hav").
        * iApply (ushp_slots_nil0 s0 (p + 88) snd (fun _ : nat => ubyte0)
                    ltac:(intros j _; reflexivity) with "Hev").
  Qed.
End UkShParseLex.
