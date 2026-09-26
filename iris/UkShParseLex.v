(* ===================================================================== *)
(* UkShParseLex.v -- SH LANE STAGE 4, part 2: the LOOKAHEAD and the one    *)
(* constructor a symbol-free line reaches.                                 *)
(*                                                                        *)
(*   peek     @0x424  -- 40 instructions, an EIGHT-word frame, one scan.   *)
(*                       the parser's one-token lookahead, and what        *)
(*                       [ushp_no_symbols] answers "no" to at four of the  *)
(*                       five sites that ask.  It is also the only lexer   *)
(*                       function that MOVES THE CURSOR AS A SIDE EFFECT   *)
(*                       ([*ps = s]), which is why the cursor cell is a    *)
(*                       [uword] in the contract rather than a value.      *)
(*   the seven token tables, as one persistent premise                     *)
(*   execcmd  @0x20a  -- 12 instructions, a two-word frame, NO branch.     *)
(*                       [cmdalloc(168); cmd->type=EXEC]                   *)
(*                                                                        *)
(* THIS IS WHERE THE ALLOCATOR ENTERS.  [ushp_malloc_ok] is declared here  *)
(* at the type the base file names -- [UkShParse.ushp_malloc_ty_le] at     *)
(* [B = 168], the BOUNDED contract (lane SH-MALLOC-3), because 168 is the  *)
(* only size this file's call site asks for and the unbounded one does     *)
(* not chain -- and [wp_kshp_execcmd] is its only consumer in the whole    *)
(* parser (through [UkShCmdalloc.wp_kshp_cmdalloc]); every file after this *)
(* one carries it through and says so, beside the out-of-memory law        *)
(* [UkShCmdalloc.ushp_oom] that [cmdalloc]'s NULL arm hands its run to.    *)
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
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShP.
Require Import UkSh.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require UkShCmdalloc.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Section UkShParseLex.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_const]). *)
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
  Local Notation urun_x0 := (UkShParse.urun_x0 N).
  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at N).
  Local Notation ushp_exec_pre := (UkShParse.ushp_exec_pre N).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join N).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation ushp_peel0 := (UkShParse.ushp_peel0 N).
  Local Notation ushp_slots_nil0 := (UkShParse.ushp_slots_nil0 N).
  Local Notation ushp_sstr := (UkShParse.ushp_sstr N).
  Local Notation ushp_sstr_text := (UkShParse.ushp_sstr_text N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation ushp_ubytes_ext := (UkShParse.ushp_ubytes_ext N).
  Local Notation wp_kshp_fp := (UkShParse.wp_kshp_fp N).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).
  Local Notation wp_kshp_strchr := (UkShParse.wp_kshp_strchr N).
  Local Notation wp_kshp_strlen := (UkShParse.wp_kshp_strlen N).


  (* ===================================================================== *)
  (* §6 THE ONE HYPOTHESIS OF STAGE 4: MALLOC.                              *)
  (*                                                                       *)
  (* All five cmd constructors begin [cmd = cmdalloc(sizeof( *cmd))], and   *)
  (* [cmdalloc] (iris/UkShCmdalloc.v) calls malloc; and                     *)
  (* malloc (0x1170, 91 instructions) -> morecore -> sbrk (0xc2e) ->        *)
  (* sys_sbrk (0xcea) is STAGE 3, which is blocked on the second unbuilt    *)
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
  (* IT HAS A FAILURE ARM SINCE lane SELF-KILL's step 5, and that is what   *)
  (* retired the sh lane's last memory assumption.  Until upstream d66e41c  *)
  (* sh did not test malloc's result and a NULL walked into memset's first  *)
  (* store and DIED ([UkSh.wp_ksh_memset_null]); now [cmdalloc] tests it    *)
  (* and calls [panic("out of memory")], which the walk hands to the        *)
  (* caller's law [UkShCmdalloc.ushp_oom].  The allocator's own             *)
  (* theorem is FIRST-CALL-ONLY ([freep == 0], so the [morecore] path),     *)
  (* which is the only call sh's parse of one line makes.                   *)
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
  (* stage 4's one Hypothesis, at the type the base file names -- BOUNDED
     at 168, [execcmd]'s own request (lane SH-MALLOC-3): the notation above
     is [UkShParse.ushp_malloc_ty_le N 168], and the call site below passes
     [168 <= 168].  Bounding it is what lets two of these CHAIN from one
     [ushm_fresh]; see iris/UkShParse.v at [ushp_malloc_ty_le]. *)
  Context (UMalloc UMalloc' : iProp Σ).
  Hypothesis ushp_malloc_ok : ushp_malloc_ty UMalloc UMalloc'.

  (* ...AND THE ONE FACT THE FAILURE ARM COSTS (lane SELF-KILL, step 5).
     On the NULL arm the walk stores through the null pointer and the
     kernel KILLS the process, and the deposit at a killing cause is the
     process's own exit payload at -1 ([UexecRet.ukill_cred_at]'s right
     side).  A Coq-level premise rather than a resource, because it is
     FREE at the record of every process that runs this code: [execcmd] is
     reached only from [parsecmd], and only sh's FORKED CHILD parses, at a
     trivial payload ([UkRun.ukn_pay_free_of_triv]).  Exactly the shape
     [UkShRun]'s exit walks already take. *)
  (* [ushp_pay_free] IS GONE (lane IO-LEAF, M3c): it said "the exit
     payload is free at this record", which is true only while sh's
     children are forked at [fun _ => True].  What the walk needs it for
     is the NULL store's death arm, and that arm takes the payload as a
     RESOURCE now -- carried in at [wp_kshp_execcmd] and handed back where
     the allocation succeeded. *)

  (* ===================================================================== *)
  (* §8 peek @0x424 -- 40 instructions, an EIGHT-word frame, one scan.      *)
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

  (* peek's whitespace scan, 0x44a..0x458:
       lbu a1,0(s1) ; c.mv a0,s3 ; jal strchr ; c.beqz a0,0x45e ;
       c.addi s1,s1,1 ; bne s2,s1,0x44a
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
    urun N h mc (mword_of_int 0x44a) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
             Regidx q <> Regidx s1_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun N h' mc' (mword_of_int 0x45e) (2 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros r. induction r as [| r IH ];
      intros j h mc Hr Hj Hs0 Hs64 Hs1 Hs2 Hs3;
      iIntros "#Hcode Hstr Hws Hrun Hcont"; [ lia | ].
    iDestruct (ustr_nonul with "Hstr") as %Hne.
    (* ---- 0x44a  lbu a1,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f j Hj with "Hstr") as "[Hb Hcl]".
    iApply (wp_uk_lbu N h mc (mword_of_int 0x44a)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat j) (f j) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat j)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_44a with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x44a 4). iIntros (h1) "Hrun".
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
    (* ---- 0x44e  c.mv a0,s3 ---- *)
    iApply (wp_uk_cmv N h1 m1 (mword_of_int 0x44e) a0_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm1 s3_idx ltac:(vm_compute; discriminate)) Hs3;
                    symmetry; exact (ushp_mv_val ushp_whitespace))
              with "[] Hrun").
    { iApply (uis_shp_44e with "Hcode"). }
    rewrite (ushp_pc_step 0x44e 2). iIntros (h2) "Hrun".
    set (m2 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x450  jal a5e <strchr> ---- *)
    iApply (wp_uk_jal N h2 m2 (mword_of_int 0x450)
              (mword_of_int 1550 : mword 21) ra_idx
              (mword_of_int 0xa5e) (mword_of_int 0x454) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_450 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x454 : mword 64)]> m2).
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
    assert (Eret : ret_pc (m3 !!! Regidx ra_idx) = mword_of_int 0x454).
    { rewrite (upd_eq m2 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x454 : mword 64))).
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
    (* ---- 0x454  c.beqz a0,0x45e -- the byte's membership decides ---- *)
    destruct (ushp_is_ws (f j)) eqn:Ews.
    2: { (* NOT whitespace: the scan stops here and [s1] never moved *)
      assert (Htk : true = eq_vec (m4 !!! Regidx a0_idx) zero_reg).
      { rewrite Ha0_4 (ushp_ws_chr_z (f j) Ews).
        rewrite (moi_eq_zero 0 ltac:(unfold Z64; lia)). reflexivity. }
      iApply (wp_uk_cbeqz N h4 m4 (mword_of_int 0x454)
                (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3)
                a0_idx true (mword_of_int 0x45e) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_454 with "Hcode"). }
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
    iApply (wp_uk_cbeqz N h4 m4 (mword_of_int 0x454)
              (mword_of_int 5 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx false (mword_of_int 0x45e) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_454 with "Hcode"). }
    rewrite (ushp_pc_step 0x454 2). iIntros (h5) "Hrun".
    (* ---- 0x456  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi N h5 m4 (mword_of_int 0x456)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S j))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_4 E1 moi_add;
                    replace (s0 + Z.of_nat (S j)) with (s0 + Z.of_nat j + 1)
                      by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_456 with "Hcode"). }
    rewrite (ushp_pc_step 0x456 2). iIntros (h6) "Hrun".
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
    (* ---- 0x458  bne s2,s1,0x44a ---- *)
    destruct (Nat.eq_dec (S j) len) as [ Hend | Hend ].
    { (* the scan ran to [es]: fall through to 0x45c, which is a no-op *)
      assert (Htk2 : false = uv_btaken BNE (m5 !!! Regidx s2_idx)
                               (m5 !!! Regidx s1_idx)).
      { cbn [uv_btaken]. rewrite Hs2_5 Hs1_5 Hend.
        rewrite (ushp_moi_neq (s0 + Z.of_nat len) (s0 + Z.of_nat len)
                   ltac:(lia) ltac:(lia)).
        rewrite Z.eqb_refl. reflexivity. }
      iApply (wp_uk_btype N h6 m5 (mword_of_int 0x458)
                (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE false
                (mword_of_int 0x44a) (2 + nn)
                Htk2
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_458 with "Hcode"). }
      rewrite (ushp_pc_step 0x458 4). iIntros (h7) "Hrun".
      (* ---- 0x45c  c.mv s1,s2 -- [s = es], which it already is ---- *)
      iApply (wp_uk_cmv N h7 m5 (mword_of_int 0x45c) s1_idx s2_idx
                (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                ltac:(rewrite Hs2_5; symmetry;
                      exact (ushp_mv_val (s0 + Z.of_nat len)))
                with "[] Hrun").
      { iApply (uis_shp_45c with "Hcode"). }
      rewrite (ushp_pc_step 0x45c 2). iIntros (h8) "Hrun".
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
    iApply (wp_uk_btype N h6 m5 (mword_of_int 0x458)
              (mword_of_int 8178 : mword 13) s1_idx s2_idx BNE true
              (mword_of_int 0x44a) (2 + nn)
              Htk2
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_458 with "Hcode"). }
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

  (* the scan's ENTRY test, 0x446: [bgeu s1,a1,0x45e] is the [s < es] half of
     the [&&], and it is what makes the cursor's index [j] range over
     [0..len] rather than [0..len-1].  Folding it in here rather than at the
     call site is what lets everything from 0x446 to 0x45e be ONE lemma with
     ONE postcondition, so peek's body has no branch until 0x468. *)
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
    urun N h mc (mword_of_int 0x446) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall q : mword 5, ucallee_saved_idx q = true ->
             Regidx q <> Regidx s1_idx ->
             mc' !!! Regidx q = mc !!! Regidx q ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx
             = mword_of_int
                 (s0 + Z.of_nat (j + ushp_skipws (len - j) j f)) ⌝ -∗
         urun N h' mc' (mword_of_int 0x45e) (2 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
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
      iApply (wp_uk_btype N h mc (mword_of_int 0x446)
                (mword_of_int 24 : mword 13) a1_idx s1_idx BGEU true
                (mword_of_int 0x45e) (2 + nn)
                Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(intros _; vm_compute; reflexivity)
                with "[] Hrun").
      { iApply (uis_shp_446 with "Hcode"). }
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
    iApply (wp_uk_btype N h mc (mword_of_int 0x446)
              (mword_of_int 24 : mword 13) a1_idx s1_idx BGEU false
              (mword_of_int 0x45e) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_446 with "Hcode"). }
    rewrite (ushp_pc_step 0x446 4). iIntros (h1) "Hrun".
    iApply (wp_kshp_peek_scan dq dw s0 len f nn (len - j)%nat j h1 mc
              eq_refl Hjlt Hs0 Hs64 Hs1 Hs2 Hs3 with "Hcode Hstr Hws Hrun").
    iIntros "Hstr Hws" (h2 mc') "%Hpres %Hret Hrun".
    iApply ("Hcont" with "Hstr Hws [] [] Hrun").
    - iPureIntro. exact Hpres.
    - iPureIntro. exact Hret.
  Qed.

  (* peek's epilogue, 0x46a..0x47a.  It is reached BOTH ways -- with a0
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
    urun N h me (mword_of_int 0x46a) (2 + nn) -∗
    (∀ h' : CpuId,
       urun N h'
         (<[Regidx csp_rs1 := regval_into_reg sp0]>
            (ushp_spillback [(ra_idx, mword_of_int 7 : mword 6);
                             (s0_idx, mword_of_int 6 : mword 6);
                             (s1_idx, mword_of_int 5 : mword 6);
                             (s2_idx, mword_of_int 4 : mword 6);
                             (s3_idx, mword_of_int 3 : mword 6);
                             (s4_idx, mword_of_int 2 : mword 6);
                             (s5_idx, mword_of_int 1 : mword 6)] vals me))
         (ret_pc (vals 0%nat)) (8 + (2 + nn)) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
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
    (* ---- 0x46a..0x476  the seven restores ---- *)
    iApply (wp_kshp_restore spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x46a | 1%nat => 0x46c
                              | 2%nat => 0x46e | 3%nat => 0x470
                              | 4%nat => 0x472 | 5%nat => 0x474
                              | 6%nat => 0x476 | _ => 0x478 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h me Hsp
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              Hoff
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_46a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_46c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_46e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_470 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_472 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_474 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_476 with "Hcode") | done ]. }
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
    (* ---- 0x478  c.addi16sp sp,sp,64 -- THE POP ---- *)
    iApply (wp_uk_caddi16sp_up N h1 mr (mword_of_int 0x478)
              (mword_of_int 4 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] [Hsl Hloc] Hrun").
    { iApply (uis_shp_478 with "Hcode"). }
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
    rewrite Hspr Hup (ushp_pc_step 0x478 2). iIntros (h2) "Hrun".
    (* ---- 0x47a  c.jr ra ---- *)
    iApply (wp_uk_cjr N h2
              (<[Regidx csp_rs1 := regval_into_reg sp0]> mr)
              (mword_of_int 0x47a) ra_idx (ret_pc (vals 0%nat)) (8 + (2 + nn))
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_ne mr (Regidx csp_rs1) (Regidx ra_idx) _
                               ltac:(vm_compute; discriminate));
                    rewrite Hrar; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_47a with "Hcode"). }
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
    urun N h m (mword_of_int ShSyms.peek) (8 + (2 + nn)) -∗
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
         urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (8 + (2 + nn)) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
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
    (* ---- 0x424  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x424)
              (mword_of_int 60 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_424 with "Hcode"). }
    rewrite (ushp_pc_step 0x424 2). iIntros "Hstk" (h1) "Hrun".
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
    (* ---- 0x426..0x432  the seven spills ---- *)
    iApply (wp_kshp_spill spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x426 | 1%nat => 0x428
                              | 2%nat => 0x42a | 3%nat => 0x42c
                              | 4%nat => 0x42e | 5%nat => 0x430
                              | 6%nat => 0x432 | _ => 0x434 end)
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
      iSplit; [ iApply (uis_shp_426 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_428 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_42a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_42c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_42e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_430 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_432 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x434  c.addi4spn s0,sp,64 ---- *)
    iApply (wp_kshp_fp h2 m1 0x434 (mword_of_int 16 : mword 8) (2 + nn)
              with "[] Hrun").
    { iApply (uis_shp_434 with "Hcode"). }
    iIntros (h3 v458) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v458]> m1).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    m2 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    (* ---- 0x436  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv N h3 m2 (mword_of_int 0x436) s4_idx a0_idx
              (mword_of_int ps) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_436 with "Hcode"). }
    rewrite (ushp_pc_step 0x436 2). iIntros (h4) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x438  c.mv s2,a1 ---- *)
    iApply (wp_uk_cmv N h4 m3 (mword_of_int 0x438) s2_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_438 with "Hcode"). }
    rewrite (ushp_pc_step 0x438 2). iIntros (h5) "Hrun".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                     : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x43a  c.mv s5,a2 ---- *)
    iApply (wp_uk_cmv N h5 m4 (mword_of_int 0x43a) s5_idx a2_idx
              (mword_of_int toks) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val toks))
              with "[] Hrun").
    { iApply (uis_shp_43a with "Hcode"). }
    rewrite (ushp_pc_step 0x43a 2). iIntros (h6) "Hrun".
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
    (* ---- 0x43c  c.ld s1,0(a0) -- the cursor ---- *)
    iApply (wp_uk_cld N h6 m5 (mword_of_int 0x43c)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 1 : mword 3) a0_idx s1_idx ps w0 (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_5 (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              Hps8 ltac:(vm_compute; discriminate)
              with "[] Hcur Hrun").
    { iApply (uis_shp_43c with "Hcode"). }
    iIntros "Hcur". rewrite (ushp_pc_step 0x43c 2). iIntros (h7) "Hrun".
    set (m6 := <[Regidx s1_idx := regval_into_reg w0]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x43e  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc N h7 m6 (mword_of_int 0x43e)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x243e) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_43e with "Hcode"). }
    rewrite (ushp_pc_step 0x43e 4). iIntros (h8) "Hrun".
    set (m7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x243e : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x442  addi s3,s3,-1078  -- s3 = &whitespace ---- *)
    iApply (wp_uk_addi N h8 m7 (mword_of_int 0x442)
              (mword_of_int 3018 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m6 (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x243e
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_442 with "Hcode"). }
    rewrite (ushp_pc_step 0x442 4). iIntros (h9) "Hrun".
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
    (* ---- 0x446..0x45c  the entry test and the scan ---- *)
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
    (* ---- 0x45e  sd s1,0(s4)  --  *ps = s ---- *)
    iApply (wp_uk_sd N h10 mc' (mword_of_int 0x45e)
              (mword_of_int 0 : mword 12) s4_idx s1_idx ps w0 (2 + nn)
              ltac:(rewrite Hs4_c (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              Hps8
              with "[] Hcur Hrun").
    { iApply (uis_shp_45e with "Hcode"). }
    iIntros "Hcur". rewrite Hs1c.
    rewrite (ushp_pc_step 0x45e 4). iIntros (h11) "Hrun".
    (* ---- 0x462  lbu a1,0(s1) -- a BODY byte, or the terminator ---- *)
    destruct (Nat.eq_dec kk len) as [ Hkend | Hkne ].
    { (* the cursor ran to [es]: the byte is the NUL and peek answers 0 *)
      iDestruct (ustr_nul with "Hstr") as "[Hb Hcl]".
      iApply (wp_uk_lbu N h11 mc' (mword_of_int 0x462)
                (mword_of_int 0 : mword 12) s1_idx a1_idx dq
                (s0 + Z.of_nat len) ubyte0 (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(rewrite Hs1c Hkend
                        (uint_moi (s0 + Z.of_nat len)
                           ltac:(unfold Z64 in *; lia));
                      vm_compute uoff_i12; lia)
                ltac:(vm_compute; discriminate)
                with "[] Hb Hrun").
      { iApply (uis_shp_462 with "Hcode"). }
      iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
      rewrite (ushp_pc_step 0x462 4). iIntros (h12) "Hrun".
      set (n9 := <[Regidx a1_idx
                   := regval_into_reg (zero_extend' 64 (ubyte0 : mword 8)
                                       : mword 64)]> mc').
      assert (Hn9 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                      n9 !!! Regidx q = mc' !!! Regidx q)
        by (intros q Hq; exact (upd_ne mc' (Regidx a1_idx) (Regidx q) _ Hq)).
      (* ---- 0x466  c.li a0,0 ---- *)
      iApply (wp_uk_cli N h12 n9 (mword_of_int 0x466)
                (mword_of_int 0 : mword 6) a0_idx (2 + nn)
                ltac:(unfold unot_sp; vm_compute; discriminate)
                ltac:(vm_compute; discriminate)
                with "[] Hrun").
      { iApply (uis_shp_466 with "Hcode"). }
      rewrite (ushp_pc_step 0x466 2). iIntros (h13) "Hrun".
      set (n10 := <[Regidx a0_idx
                    := regval_into_reg
                         (sign_extend' 64 (mword_of_int 0 : mword 6)
                          : mword 64)]> n9).
      assert (Hn10 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                       n10 !!! Regidx q = n9 !!! Regidx q)
        by (intros q Hq; exact (upd_ne n9 (Regidx a0_idx) (Regidx q) _ Hq)).
      (* ---- 0x468  c.bnez a1,0x47c -- NOT taken ---- *)
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
      iApply (wp_uk_cbnez N h13 n10 (mword_of_int 0x468)
                (mword_of_int 10 : mword 8) (mword_of_int 3 : mword 3)
                a1_idx false (mword_of_int 0x47c) (2 + nn)
                ltac:(vm_compute; reflexivity) Htk
                ltac:(apply bv_eq; vm_compute; reflexivity)
                ltac:(discriminate)
                with "[] Hrun").
      { iApply (uis_shp_468 with "Hcode"). }
      rewrite (ushp_pc_step 0x468 2). iIntros (h14) "Hrun".
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
    iApply (wp_uk_lbu N h11 mc' (mword_of_int 0x462)
              (mword_of_int 0 : mword 12) s1_idx a1_idx dq
              (s0 + Z.of_nat kk) (f kk) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1c
                      (uint_moi (s0 + Z.of_nat kk)
                         ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_462 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x462 4). iIntros (h12) "Hrun".
    set (n9 := <[Regidx a1_idx
                 := regval_into_reg (zero_extend' 64 ((f kk) : mword 8)
                                     : mword 64)]> mc').
    assert (Hn9 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                    n9 !!! Regidx q = mc' !!! Regidx q)
      by (intros q Hq; exact (upd_ne mc' (Regidx a1_idx) (Regidx q) _ Hq)).
    (* ---- 0x466  c.li a0,0 ---- *)
    iApply (wp_uk_cli N h12 n9 (mword_of_int 0x466)
              (mword_of_int 0 : mword 6) a0_idx (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_466 with "Hcode"). }
    rewrite (ushp_pc_step 0x466 2). iIntros (h13) "Hrun".
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
    (* ---- 0x468  c.bnez a1,0x47c -- TAKEN ---- *)
    assert (Htk : true = neq_vec (n10 !!! Regidx a1_idx) zero_reg).
    { rewrite Ha1_10. unfold neq_vec. rewrite (ushp_zext_nul (f kk)).
      rewrite (bool_decide_eq_false_2 (f kk = ubyte0) (Hnenul kk Hklt)).
      reflexivity. }
    iApply (wp_uk_cbnez N h13 n10 (mword_of_int 0x468)
              (mword_of_int 10 : mword 8) (mword_of_int 3 : mword 3)
              a1_idx true (mword_of_int 0x47c) (2 + nn)
              ltac:(vm_compute; reflexivity) Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_468 with "Hcode"). }
    iIntros (h14) "Hrun".
    (* ---- 0x47c  c.mv a0,s5 ---- *)
    assert (Hs5_10 : n10 !!! Regidx s5_idx = mword_of_int toks).
    { rewrite (Hn10 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hn9 s5_idx ltac:(vm_compute; discriminate)). exact Hs5_c. }
    iApply (wp_uk_cmv N h14 n10 (mword_of_int 0x47c) a0_idx s5_idx
              (mword_of_int toks) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs5_10; symmetry; exact (ushp_mv_val toks))
              with "[] Hrun").
    { iApply (uis_shp_47c with "Hcode"). }
    rewrite (ushp_pc_step 0x47c 2). iIntros (h15) "Hrun".
    set (n11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int toks : mword 64)]> n10).
    assert (Hn11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     n11 !!! Regidx q = n10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x47e  jal a5e <strchr> ---- *)
    iApply (wp_uk_jal N h15 n11 (mword_of_int 0x47e)
              (mword_of_int 1504 : mword 21) ra_idx
              (mword_of_int 0xa5e) (mword_of_int 0x482) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_47e with "Hcode"). }
    iIntros (h16) "Hrun".
    set (n12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x482 : mword 64)]> n11).
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
    assert (Eret : ret_pc (n12 !!! Regidx ra_idx) = mword_of_int 0x482).
    { rewrite (upd_eq n11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x482 : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- shpp_strchr.
    iApply (wp_kshp_strchr h16 n12 tt dt toks tlen tf (f kk) nn
              Ha0_12 Ha1_12 ltac:(lia) ltac:(unfold Z64 in *; lia)
              with "Hcode Htoks Hrun").
    iIntros "Htoks" (h17 n13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret.
    (* ---- 0x482  snez a0,a0  --  sltu a0,x0,a0 ---- *)
    iDestruct (urun_x0 with "Hrun") as "[%Hx0 Hrun]".
    assert (Hchrb : 0 <= ushp_chr toks tlen 0%nat tf (f kk) < Z64).
    { unfold ushp_chr.
      destruct (ushp_find tlen 0%nat tf (f kk)) as [ jj | ] eqn:Ej;
        [ | unfold Z64; lia ].
      pose proof (ushp_find_ge tlen 0%nat tf (f kk) jj Ej) as Hjr.
      unfold Z64 in *. lia. }
    iApply (wp_uk_sltu N h17 n13 (mword_of_int 0x482)
              x0_idx a0_idx a0_idx
              (mword_of_int (if Z.ltb 0 (ushp_chr toks tlen 0%nat tf (f kk))
                             then 1 else 0)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hx0 Ha0_13; symmetry;
                    exact (ushp_snez_val
                             (ushp_chr toks tlen 0%nat tf (f kk)) Hchrb))
              with "[] Hrun").
    { iApply (uis_shp_482 with "Hcode"). }
    rewrite (ushp_pc_step 0x482 4). iIntros (h18) "Hrun".
    set (n14 := <[Regidx a0_idx
                  := regval_into_reg
                       (mword_of_int
                          (if Z.ltb 0 (ushp_chr toks tlen 0%nat tf (f kk))
                           then 1 else 0) : mword 64)]> n13).
    assert (Hn14 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     n14 !!! Regidx q = n13 !!! Regidx q)
      by (intros q Hq; exact (upd_ne n13 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x486  c.j 0x46a ---- *)
    iApply (wp_uk_cj N h18 n14 (mword_of_int 0x486)
              (mword_of_int 2034 : mword 11) (mword_of_int 0x46a) (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_486 with "Hcode"). }
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
  Proof using .
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
  Proof using .
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
  Proof using .
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
  Proof using .
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
  Proof using .
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
  Definition ushp_T_none  : Z := 0x1278.   (* the empty table, parsecmd *)

  (* ...and the two decidable checks, discharged once each *)
  Lemma ushp_T_redir_ok : ushp_lit_ok ushp_T_redir 2 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_block_ok : ushp_lit_ok ushp_T_block 1 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_arg_ok   : ushp_lit_ok ushp_T_arg 4 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_pipe_ok  : ushp_lit_ok ushp_T_pipe 1 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_back_ok  : ushp_lit_ok ushp_T_back 1 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_list_ok  : ushp_lit_ok ushp_T_list 1 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_none_ok  : ushp_lit_ok ushp_T_none 0 = true.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma ushp_T_redir_sym : ushp_lit_sym ushp_T_redir 2 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_block_sym : ushp_lit_sym ushp_T_block 1 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_arg_sym   : ushp_lit_sym ushp_T_arg 4 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_pipe_sym  : ushp_lit_sym ushp_T_pipe 1 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_back_sym  : ushp_lit_sym ushp_T_back 1 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_list_sym  : ushp_lit_sym ushp_T_list 1 = true.
  Proof using . vm_compute. reflexivity. Qed.
  Lemma ushp_T_none_sym  : ushp_lit_sym ushp_T_none 0 = true.
  Proof using . reflexivity. Qed.

  (* ===================================================================== *)
  (* §7 execcmd @0x20a -- 12 instructions, a two-word frame, NO branch.     *)
  (*                                                                       *)
  (*   struct cmd *execcmd(void) {                                          *)
  (*     struct execcmd *cmd;                                               *)
  (*     cmd = cmdalloc(sizeof( *cmd));                                     *)
  (*     cmd->type = EXEC;                                                  *)
  (*     return (struct cmd * )cmd;  }                                      *)
  (*                                                                       *)
  (* THE FIRST LEMMA IN THIS FILE THAT CARRIES [ushp_malloc_ok], and the    *)
  (* only one that carries it directly: parseexec, parsepipe, parseline and *)
  (* parsecmd carry it THROUGH this lemma.  Everything above §7 is          *)
  (* unconditional; this one is not, and says so here rather than only in   *)
  (* the lane report.                                                       *)
  (*                                                                       *)
  (* THE ALLOCATION IS [UkShCmdalloc.wp_kshp_cmdalloc] (upstream d66e41c),  *)
  (* which tests malloc's answer: the node comes back ZEROED and owned, or  *)
  (* the run goes to [panic("out of memory")], which this walk hands to the *)
  (* caller's law [ushp_oom] unopened.                                      *)
  (*                                                                       *)
  (* WHAT THE POSTCONDITION SAYS, and why it is the honest reading.  The    *)
  (* node comes back as [ushp_exec_at s0 p []] -- an EXEC node whose token  *)
  (* list is EMPTY.  That is not a weakening: parseexec fills the slots     *)
  (* itself, one per [gettoken], and the invariant it runs its argument     *)
  (* loop on is this predicate at the tokens recorded SO FAR.  The empty    *)
  (* list is the loop's base case, and the NULL cap it demands at slot 0 is *)
  (* exactly what [cmdalloc]'s memset zeroed.  [s0] is unconstrained        *)
  (* because an empty token list mentions no line at all.                   *)
  (*                                                                       *)
  (* THE BUDGET IS THE CALL CHAIN: two words of execcmd's own frame on top  *)
  (* of cmdalloc's four and malloc's ten.                                   *)
  (* ===================================================================== *)

  Lemma shpp_malloc : ShSyms.malloc = 0x1170.
  Proof using . unfold ShSyms.malloc. reflexivity. Qed.
  Lemma shpp_memset : ShSyms.memset = 0xa38.
  Proof using . unfold ShSyms.memset. reflexivity. Qed.

  Local Notation ushp_oom := (UkShCmdalloc.ushp_oom N).
  Local Notation wp_kshp_cmdalloc :=
    (UkShCmdalloc.wp_kshp_cmdalloc N UMalloc UMalloc' ushp_malloc_ok).
  Local Notation wp_kshp_frame_pro_ci := (UkShParse.wp_kshp_frame_pro_ci N).
  Local Notation wp_kshp_frame_epi_ci := (UkShParse.wp_kshp_frame_epi_ci N).

  Lemma wp_kshp_execcmd {Pex : iProp Σ} (h : CpuId) (m : regfile) (s0 : Z) (nn : nat) :
    shp_code γt -∗
    UMalloc -∗
    (* THE OUT-OF-MEMORY LAW (upstream d66e41c): [cmdalloc] panics when
       [malloc] returns NULL, and what that death prints and pays is the
       caller's -- the walk hands it the run at [panic]'s entry and the
       exit resource [Pex] it was lent. *)
    ushp_oom Pex (10 + nn) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.execcmd) (2 + (4 + (10 + nn))) -∗
    (∀ (h' : CpuId) (m' : regfile) (p : Z),
       ⌜ ucallee_saved m m' ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = mword_of_int p ⌝ -∗
       ⌜ 0 < p /\ p mod 16 = 0 /\ p + 168 < 2 ^ 38 ⌝ -∗
       ushp_exec_pre s0 p [] -∗
       UMalloc' -∗
       Pex -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (2 + (4 + (10 + nn))) -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok.
    iIntros "#Hcode HM #Hoom Hpay Hrun Hcont".
    rewrite shpp_execcmd.
    set (rs := [(ra_idx, mword_of_int 1 : mword 6);
                (s0_idx, mword_of_int 0 : mword 6)]).
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | _ => m !!! Regidx s0_idx end).
    (* ---- 0x20a..0x210  the prologue: k = 2, two spills, no pad ---- *)
    iApply (wp_kshp_frame_pro_ci 2 0 rs 0x20a
              (fun i : nat => match i with
                              | 0%nat => 0x20c | 1%nat => 0x20e | _ => 0x210 end)
              (mword_of_int 48 : mword 6) (mword_of_int 4 : mword 8)
              vals (4 + (10 + nn)) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| i ]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| i ]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_20a with "Hcode"). }
    { unfold rs. rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_20c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_20e with "Hcode") | done ]. }
    { iApply (uis_shp_210 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 2))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (m2 := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall r : mword 5, Regidx r <> Regidx csp_rs1 ->
                    m1 !!! Regidx r = m !!! Regidx r)
      by (intros r Hr; exact (upd_ne m (Regidx csp_rs1) (Regidx r) _ Hr)).
    assert (Hm2 : forall r : mword 5, Regidx r <> Regidx s0_idx ->
                    m2 !!! Regidx r = m1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m1 (Regidx s0_idx) (Regidx r) _ Hr)).
    assert (Hsp2 : m2 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x212  li a0,168 ---- *)
    assert (E168 : (sign_extend' 64 (mword_of_int 168 : mword 12) : mword 64)
                   = mword_of_int 168)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_li N h1 m2 (mword_of_int 0x212)
              (mword_of_int 168 : mword 12) a0_idx (mword_of_int 168)
              (4 + (10 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite E168; symmetry; exact (ushp_mv_val 168))
              with "[] Hrun").
    { iApply (uis_shp_212 with "Hcode"). }
    rewrite (ushp_pc_step 0x212 4). iIntros (h2) "Hrun".
    set (m3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int 168 : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x216  jal 1d2 <cmdalloc> ---- *)
    iApply (wp_uk_jal N h2 m3 (mword_of_int 0x216)
              (mword_of_int 2097084 : mword 21) ra_idx
              (mword_of_int 0x1d2) (mword_of_int 0x21a) (4 + (10 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_216 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x21a : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = mword_of_int 168).
    { rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx a0_idx)
               (regval_into_reg (mword_of_int 168 : mword 64))). }
    assert (Eret1 : ret_pc (m4 !!! Regidx ra_idx) = mword_of_int 0x21a).
    { rewrite (upd_eq m3 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x21a : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    rewrite <- UkShParse.shpp_cmdalloc.
    (* ---- cmdalloc(168) ---- *)
    iApply (wp_kshp_cmdalloc h3 m4 168 nn Ha0_4 ltac:(lia) ltac:(lia)
              with "Hcode HM Hoom Hpay Hrun").
    iIntros (h4 m5 p) "%Hcs45 %Ha0_5 %Hpb Hbs HM' Hpay Hrun".
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
    (* ---- the node's four slices: type, padding, argv, eargv ---- *)
    iDestruct (ushp_peel0 p (p + 4) 4 164 ltac:(lia) with "Hbs")
      as "[Hty Hbs]".
    iDestruct (ushp_peel0 (p + 4) (p + 8) 4 160 ltac:(lia) with "Hbs")
      as "[Hpad Hbs]".
    iDestruct (ushp_peel0 (p + 8) (p + 88) 80 80 ltac:(lia) with "Hbs")
      as "[Hav Hev]".
    (* ---- 0x21a  c.li a5,1 ---- *)
    iApply (wp_uk_cli N h4 m5 (mword_of_int 0x21a)
              (mword_of_int 1 : mword 6) a5_idx (4 + (10 + nn))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_21a with "Hcode"). }
    rewrite (ushp_pc_step 0x21a 2). iIntros (h5) "Hrun".
    set (m6 := <[Regidx a5_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 1 : mword 6)
                       : mword 64)]> m5).
    assert (Hm6 : forall q : mword 5, Regidx q <> Regidx a5_idx ->
                    m6 !!! Regidx q = m5 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m5 (Regidx a5_idx) (Regidx q) _ Hq)).
    assert (Ha5_6 : m6 !!! Regidx a5_idx = (mword_of_int 1 : mword 64)).
    { rewrite (upd_eq m5 (Regidx a5_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_6 : m6 !!! Regidx a0_idx = mword_of_int p)
      by (rewrite (Hm6 a0_idx ltac:(vm_compute; discriminate)); exact Ha0_5).
    (* ---- 0x21c  c.sw a5,0(a0)  --  cmd->type = EXEC ---- *)
    iApply (wp_uk_csw N h5 m6 (mword_of_int 0x21c)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 7 : mword 3) a0_idx a5_idx p
              (mword_of_int 0 : mword 64) (4 + (10 + nn))
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_6 (uint_moi p Hp64);
                    vm_compute uoff_c4; lia)
              Hp4
              with "[] [Hty] Hrun").
    { iApply (uis_shp_21c with "Hcode"). }
    { iApply (ushp_ubytes_ext p 4 (fun _ : nat => ubyte0)
                (nth_byte (mword_of_int 0 : mword 64)) with "Hty").
      intros j Hj. rewrite (ushp_nth_byte_zero j ltac:(lia)). reflexivity. }
    iIntros "Hty". rewrite Ha5_6.
    rewrite (ushp_pc_step 0x21c 2). iIntros (h6) "Hrun".
    assert (Hspe : m6 !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 2))).
    { rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hcs45 csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp2. }
    (* ---- 0x21e..0x224  the epilogue, popped with [c.addi sp,sp,16] ---- *)
    iApply (wp_kshp_frame_epi_ci 2 0 rs (mword_of_int 1 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x21e | 1%nat => 0x220 | _ => 0x222 end)
              (mword_of_int 16 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 2)) vals
              (4 + (10 + nn)) h6 m6
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| i ]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| i ]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { unfold rs. rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_21e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_220 with "Hcode") | done ]. }
    { iApply (uis_shp_222 with "Hcode"). }
    { iApply (uis_shp_224 with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! hf _ p
              with "[] [] [] [Hty Hpad Hav Hev] HM' Hpay Hrun").
    - iPureIntro.
      apply (ushp_frame_cs rs vals m m6 sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| i ]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros r Hr Hrsp Hmiss.
        rewrite (Hm6 r (ushp_cs_ne r a5_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hcs45 r Hr).
        rewrite (Hm4 r (Hmiss 0%nat ra_idx (mword_of_int 1 : mword 6)
                          eq_refl)).
        rewrite (Hm3 r (ushp_cs_ne r a0_idx Hr
                          ltac:(vm_compute; reflexivity))).
        rewrite (Hm2 r (Hmiss 1%nat s0_idx (mword_of_int 0 : mword 6)
                          eq_refl)).
        exact (Hm1 r Hrsp).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _. exact Ha0_6.
      + intros i r u Hi He.
        destruct i as [| [| i ]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
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
