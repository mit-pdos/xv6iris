(* ===================================================================== *)
(* UkShPipeEx.v -- THE ARGUMENT LOOP'S EXIT AT THE '|', lane SH-PARSE-PIPE *)
(* (design/app-pipe.md SS5.1, the parser paragraph).                        *)
(*                                                                        *)
(* [parseexec]'s argument loop is                                          *)
(*                                                                        *)
(*   while (!peek(ps, es, "|)&;")) { ... }          (user/sh.c:445)        *)
(*                                                                        *)
(* and on a symbol-free line that guard is REFUTED at every round, so the  *)
(* landed walks ([UkShParseExec.wp_kshp_pex_loop], SH-PARSE-2's            *)
(* [UkShRedirEx.wp_kshp_pex_loop_gt]) only ever take the NOT-TAKEN arm of  *)
(* the branch at 0x62c.  The pipe line is the first line that makes the    *)
(* guard TRUE, and this file is that arm.                                  *)
(*                                                                        *)
(* THE FINDING: it is ONE INSTRUCTION of new code.                         *)
(* 0x62c's taken arm goes to 0x662 -- which is exactly where the loop's    *)
(* exhausted-line exit goes too (0x63a's [c.beqz a0], and                  *)
(* [UkShRedirEx.wp_kshp_pex_end] lands there) -- so the argv terminator    *)
(* stores and [parseexec]'s whole epilogue are ALREADY WALKED, by the      *)
(* landed walk, unchanged.  What the pipe line needs above this lemma is a *)
(* RE-STATEMENT of the loop at [UkShParseSym.ushs_toks] (as SH-PARSE-2     *)
(* re-stated it for the redirect line), not a new walk: the only round     *)
(* that differs is the last one, and this is it.                            *)
(*                                                                        *)
(* The round is CHEAPER than [wp_kshp_pex_end] as well as shorter: it      *)
(* never reaches [gettoken], so it touches neither of the frame's two      *)
(* out-cells ([q], [eq]) nor the symbols table, and the statement is       *)
(* stated over none of them.                                              *)
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
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseLex.
Require Import UkShRedirLex.
Require Import UkShPipeLex.
Require Import UexecSG.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 THE TWO TABLE HITS, PURE                                            *)
(*                                                                        *)
(* [UkShParseLex.wp_kshp_peek] is fully general and its answer is the      *)
(* computed [ushp_peek_res], so a table HIT is a pure lemma and not a      *)
(* walk -- UkShRedirLex's finding, at the other byte.  Both tables are     *)
(* read off the image dump: entry 0 of the four argument-loop stoppers at  *)
(* 0x1328 is '|' (the four are "|)&;"), and so is the one byte of the      *)
(* pipe table at 0x1330.                                                  *)
(* ===================================================================== *)

Lemma ushp_T_arg_bar : ushp_lit ushp_T_arg 0%nat = ushq_bar.
Proof using. vm_compute. reflexivity. Qed.

Lemma ushp_T_pipe_bar : ushp_lit ushp_T_pipe 0%nat = ushq_bar.
Proof using. vm_compute. reflexivity. Qed.

(* the fact [parseexec]'s argument loop STOPS on, and the one thing no
   landed walk could ever produce (every landed peek at this table is
   refuted from [ushp_no_symbols]) *)
Lemma ushp_peek_arg_hit (len : nat) (f : nat -> bv 8) (k : nat) :
  (k < len)%nat -> f k = ushq_bar ->
  ushp_peek_res len f k 4 (ushp_lit ushp_T_arg) = 1.
Proof using.
  intros Hk Hf.
  apply (ushp_peek_res_hit len f k 4 (ushp_lit ushp_T_arg) 0%nat Hk
           ltac:(lia)).
  rewrite ushp_T_arg_bar. rewrite Hf. reflexivity.
Qed.

(* ...and the fact [parsepipe]'s guard TURNS on, which is what makes the
   pipe line's parse a pipe at all *)
Lemma ushp_peek_pipe_hit (len : nat) (f : nat -> bv 8) (k : nat) :
  (k < len)%nat -> f k = ushq_bar ->
  ushp_peek_res len f k 1 (ushp_lit ushp_T_pipe) = 1.
Proof using.
  intros Hk Hf.
  apply (ushp_peek_res_hit len f k 1 (ushp_lit ushp_T_pipe) 0%nat Hk
           ltac:(lia)).
  rewrite ushp_T_pipe_bar. rewrite Hf. reflexivity.
Qed.

(* the pipe shape's instance of each, at the '|' the line names *)
Lemma ushq_peek_arg_hit_pipe (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e ->
  ushp_peek_res len f p 4 (ushp_lit ushp_T_arg) = 1.
Proof using.
  intro Hq.
  exact (ushp_peek_arg_hit len f p (ushq_pipe_lt len f p e Hq)
           (ushq_pipe_bar len f p e Hq)).
Qed.

Lemma ushq_peek_pipe_hit_pipe (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e ->
  ushp_peek_res len f p 1 (ushp_lit ushp_T_pipe) = 1.
Proof using.
  intro Hq.
  exact (ushp_peek_pipe_hit len f p (ushq_pipe_lt len f p e Hq)
           (ushq_pipe_bar len f p e Hq)).
Qed.


(* ===================================================================== *)
(* §1½ AND THE MISS THE LEFT COMMAND'S LAST parseredirs NEEDS             *)
(*                                                                        *)
(* [parseexec]'s loop calls [parseredirs] after EVERY argument, so on the  *)
(* pipe line the last of those calls sits on the '|' -- and it must not    *)
(* turn: peek's table there is the two redirection bytes, and a '|' is     *)
(* neither of them.  The landed zero-turn walk                             *)
(* [UkShRedirPr.wp_kshp_parseredirs_ns] cannot serve it: its premise is    *)
(* that the byte at the cursor is NOT A SYMBOL, which the '|' falsifies,   *)
(* and it spends that premise through                                     *)
(* [UkShRedirPr.ushs_peek_res_nsym] in ONE line.  So the re-statement      *)
(* wants the weakest fact instead, and here it is: the peek misses         *)
(* because the BYTE IS NOT IN THE TABLE.  [ushp_peek_res_miss] is the      *)
(* mirror of [UkShRedirLex.ushp_peek_res_hit] and is strictly more         *)
(* general than [ushs_peek_res_nsym].                                     *)
(* ===================================================================== *)

Lemma ushp_peek_res_miss (len : nat) (f : nat -> bv 8) (k tlen : nat)
    (tf : nat -> bv 8) :
  (forall j : nat, (j < tlen)%nat -> tf j <> f k) ->
  ushp_peek_res len f k tlen tf = 0.
Proof using.
  intro Hne. rewrite /ushp_peek_res.
  destruct (bool_decide (k < len)%nat) eqn:Hk; [ | reflexivity ].
  rewrite (ushp_find_none tlen 0%nat tf (f k)); [ reflexivity | ].
  intros j Hj. exact (Hne j ltac:(lia)).
Qed.

(* ...at the '|', for the redirect table "<>" (0x1300) *)
Lemma ushp_peek_redir_miss_bar (len : nat) (f : nat -> bv 8) (k : nat) :
  f k = ushq_bar -> ushp_peek_res len f k 2 (ushp_lit ushp_T_redir) = 0.
Proof using.
  intro Hf. apply ushp_peek_res_miss. intros j Hj. rewrite Hf.
  destruct j as [| [| j ]]; [ | | lia ].
  - rewrite ushp_T_redir_lt. vm_compute. discriminate.
  - rewrite ushp_T_redir_gt. vm_compute. discriminate.
Qed.

Lemma ushq_peek_redir_miss_pipe (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e ->
  ushp_peek_res len f p 2 (ushp_lit ushp_T_redir) = 0.
Proof using.
  intro Hq.
  exact (ushp_peek_redir_miss_bar len f p (ushq_pipe_bar len f p e Hq)).
Qed.

Section UkShPipeEx.
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

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).

  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).

  (* ===================================================================== *)
  (* §2 THE ROUND THAT FINDS THE '|'                                        *)
  (*                                                                        *)
  (*   0x622  c.mv a2,s6        the table "|)&;"                            *)
  (*   0x624  c.mv a1,s5        es                                          *)
  (*   0x626  c.mv a0,s4        &s                                          *)
  (*   0x628  jal  448 <peek>   ...which ANSWERS 1                          *)
  (*   0x62c  c.bnez a0,0x662   TAKEN -- the loop is done                   *)
  (*                                                                        *)
  (* and 0x662 is the landed exit ([UkShRedirEx.wp_kshp_pex_end]'s).         *)
  (* ===================================================================== *)

  Lemma wp_kshp_pex_bar (dq dw : dfrac) (s0 ps : Z)
      (len : nat) (f : nat -> bv 8) (nn cur : nat) (h : CpuId)
      (mc : regfile) :
    (cur <= len)%nat ->
    ((cur + ushp_skipws (len - cur) cur f)%nat < len)%nat ->
    f (cur + ushp_skipws (len - cur) cur f)%nat = ushq_bar ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    mc !!! Regidx s4_idx = mword_of_int ps ->
    mc !!! Regidx s5_idx = mword_of_int (s0 + Z.of_nat len) ->
    mc !!! Regidx s6_idx = mword_of_int ushp_T_arg ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat cur)) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    urun N h mc (mword_of_int 0x622) (24 + nn) -∗
    (uword γd ps
       (mword_of_int
          (s0 + Z.of_nat (cur + ushp_skipws (len - cur) cur f))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall r : mword 5, ucallee_saved_idx r = true ->
             mc' !!! Regidx r = mc !!! Regidx r ⌝ -∗
         urun N h' mc' (mword_of_int 0x662) (24 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hcur Hklt Hbar Hs0 Hs64 Hps0 Hps8 Hpssz Hs4v Hs5v Hs6v.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hrun Hcont".
    (* ---- 0x622  c.mv a2,s6 ---- *)
    iApply (wp_uk_cmv N h mc (mword_of_int 0x622) a2_idx
              s6_idx (mword_of_int ushp_T_arg) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs6v; symmetry;
                    exact (ushp_mv_val ushp_T_arg))
              with "[] Hrun").
    { iApply (uis_shp_622 with "Hcode"). }
    iIntros (h1) "Hrun".
    set (n1 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_arg : mword 64)]> mc).
    assert (Hk1 : forall r : mword 5, ucallee_saved_idx r = true ->
                    n1 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          exact (upd_ne mc (Regidx a2_idx) (Regidx r) _
                   (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))).
    (* ---- 0x624  c.mv a1,s5 ---- *)
    iApply (wp_uk_cmv N h1 n1 (mword_of_int 0x624) a1_idx
              s5_idx (mword_of_int (s0 + Z.of_nat len)) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hk1 s5_idx ltac:(vm_compute; reflexivity))
                      Hs5v; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_624 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (n2 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> n1).
    assert (Hk2 : forall r : mword 5, ucallee_saved_idx r = true ->
                    n2 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n1 (Regidx a1_idx) (Regidx r) _
                     (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk1 r Hr)).
    (* ---- 0x626  c.mv a0,s4 ---- *)
    iApply (wp_uk_cmv N h2 n2 (mword_of_int 0x626) a0_idx
              s4_idx (mword_of_int ps) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hk2 s4_idx ltac:(vm_compute; reflexivity))
                      Hs4v; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_626 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (n3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> n2).
    assert (Hk3 : forall r : mword 5, ucallee_saved_idx r = true ->
                    n3 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n2 (Regidx a0_idx) (Regidx r) _
                     (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk2 r Hr)).
    (* ---- 0x628  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h3 n3 (mword_of_int 0x628)
              (mword_of_int 2096672 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x62c) (24 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_628 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (n4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x62c : mword 64)]> n3).
    assert (Hk4 : forall r : mword 5, ucallee_saved_idx r = true ->
                    n4 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr;
          rewrite (upd_ne n3 (Regidx ra_idx) (Regidx r) _
                     (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)));
          exact (Hk3 r Hr)).
    assert (Eret4 : ret_pc (n4 !!! Regidx ra_idx) = mword_of_int 0x62c);
      [ rewrite (upd_eq n3 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x62c : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    assert (Ha0_4 : n4 !!! Regidx a0_idx = mword_of_int ps);
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a0_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n2 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int ps : mword 64))) | ].
    assert (Ha1_4 : n4 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len));
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a1_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq n1 (Regidx a1_idx)
                 (regval_into_reg
                    (mword_of_int (s0 + Z.of_nat len) : mword 64))) | ].
    assert (Ha2_4 : n4 !!! Regidx a2_idx = mword_of_int ushp_T_arg);
      [ rewrite (upd_ne n3 (Regidx ra_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n2 (Regidx a0_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        rewrite (upd_ne n1 (Regidx a1_idx) (Regidx a2_idx) _
                   ltac:(vm_compute; discriminate));
        exact (upd_eq mc (Regidx a2_idx)
                 (regval_into_reg
                    (mword_of_int ushp_T_arg : mword 64))) | ].
    rewrite <- shpp_peek.
    iApply (wp_kshp_peek h4 n4 dq dw true DfracDiscarded ps s0
              ushp_T_arg len cur 4 f (ushp_lit ushp_T_arg)
              (mword_of_int (s0 + Z.of_nat cur)) (14 + nn)
              Ha0_4 Ha1_4 Ha2_4 Hcur eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_arg; lia)
              ltac:(unfold ushp_T_arg, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_arg 4 DfracDiscarded
                ushp_T_arg_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h5 n5) "%Hcs45 %Ha0_5 Hrun".
    rewrite Eret4.
    rewrite (ushp_peek_arg_hit len f
               (cur + ushp_skipws (len - cur) cur f)%nat Hklt Hbar) in Ha0_5.
    assert (Hk5 : forall r : mword 5, ucallee_saved_idx r = true ->
                    n5 !!! Regidx r = mc !!! Regidx r)
      by (intros r Hr; rewrite (Hcs45 r Hr); exact (Hk4 r Hr)).
    (* ---- 0x62c  c.bnez a0 -- TAKEN: the guard HOLDS, the loop is done -- *)
    iApply (wp_uk_cbnez N h5 n5 (mword_of_int 0x62c)
              (mword_of_int 27 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx true (mword_of_int 0x662) (24 + nn)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_5; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_62c with "Hcode"). }
    iIntros (h6) "Hrun".
    iApply ("Hcont" with "Hcur Hstr Hws [] Hrun").
    iPureIntro. exact Hk5.
  Qed.

End UkShPipeEx.
