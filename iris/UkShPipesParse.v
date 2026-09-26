(* ===================================================================== *)
(* UkShPipesParse.v -- [parsepipe] ON A PIPELINE OF ANY LENGTH, lane     *)
(* PIPES-C3 (design/pipes-general.md §1.1 and §5, cut C3).                *)
(*                                                                        *)
(* sh.c's parsepipe (sh.c:367-378):                                       *)
(*                                                                        *)
(*   cmd = parseexec(ps, es);                                             *)
(*   if(peek(ps, es, "|")){                                               *)
(*     gettoken(ps, es, 0, 0);                                            *)
(*     cmd = pipecmd(cmd, parsepipe(ps, es));                             *)
(*   }                                                                    *)
(*                                                                        *)
(* is RIGHT-RECURSIVE, so the walk of a line of k bars is an induction on *)
(* k, and nothing about it is new code:                                   *)
(*                                                                        *)
(*   base  no bar: [UkShPipeRight.wp_kshp_parsepipe_tail], the landed     *)
(*         symbol-free walk on the line's suffix;                         *)
(*   step  a bar: [UkShPipeCm.wp_kshp_parsepipe_bar_g], the landed turn   *)
(*         re-stated at a bar read locally ([UkShPipesLex.ushq_barw]),    *)
(*         whose recursion premise (iii) IS the induction hypothesis,     *)
(*         whose left [parseexec] is [UkShPipePex.wp_kshp_parseexec_barw] *)
(*         from the cursor the previous bar left, and whose [pipecmd] is  *)
(*         the landed [UkShPipeCm.ushq_pipecmd_call_holds].               *)
(*                                                                        *)
(* THE ALLOCATION ORDER, READ OFF THE CODE.  The turn calls parsepipe at  *)
(* 0x6ae and pipecmd at 0x6b6 (and parseexec, whose execcmd allocates, at *)
(* 0x674, before either): C evaluates both arguments of pipecmd before    *)
(* the call, and cmd is already computed.  So a line of N stages mallocs  *)
(* execcmd N times, left to right, and THEN pipecmd N-1 times, innermost  *)
(* first -- 2N-1 calls.  The walk threads ONE allocator chain [UM] in     *)
(* exactly that order: the stage opened at link [i] with k bars after it  *)
(* spends links [i .. i+2k], its own execcmd at [i], its suffix's at      *)
(* [i+1 .. i+2k-1], and its pipecmd LAST, at [i+2k].                      *)
(*                                                                        *)
(* THE ANSWER IS THE PARSER'S OWN TREE ([UkShParse.ushp_tree]) at the     *)
(* right spine [ushq_ptree], so every level hands the level above one     *)
(* resource and [UkShPipesSeam] converts it in one induction.             *)
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
Require Import UserHeap UkRun.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UserFd.
Require Import UkShParse.
Require UkShCmdalloc.
Require Import UkShParseSym.
Require Import UkShParseCmd.
Require Import UkShPipeLex.
Require Import UkShPipeParse.
Require Import UkShPipeRight.
Require Import UkShPipePex.
Require Import UkShPipeCm.
Require Import UkShPipesLex.
Require Import UexecSG.
Local Open Scope Z_scope.
Import Defs.

(* the parse's answer: the right spine of EXEC nodes *)
Fixpoint ushq_ptree (a : list (nat * nat)) (rest : list (list (nat * nat)))
    : ushp_cmd :=
  match rest with
  | [] => UshpExec a
  | b :: rest' => UshpPipe (UshpExec a) (ushq_ptree b rest')
  end.

Section UkShPipesParse.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation ushp_oom := (UkShCmdalloc.ushp_oom N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at N).
  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_pipe_node := (UkShPipeParse.ushp_pipe_node N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).

  (* ===================================================================== *)
  (* §1 THE ALLOCATOR CHAIN: [K] links, each one [malloc] at the parser's    *)
  (* bound ([UkShPipesSeam.ushq_um_chain] is the landed allocator's).        *)
  (* ===================================================================== *)
  Context (UM : nat -> iProp Σ) (K : nat).
  Hypothesis ushq_malloc_chain :
    forall i : nat, (i < K)%nat -> ushp_malloc_ty (UM i) (UM (S i)).

  (* ===================================================================== *)
  (* §2 THE LEFT [parseexec] OF A STAGE, FROM ITS OWN CURSOR                 *)
  (* [UkShPipeCm.ushq_pex_left_holds] at a bar read locally and at any       *)
  (* cursor: every stage of a pipeline but the last.                         *)
  (* ===================================================================== *)
  Lemma ushq_pex_left_at_holds {Pex : iProp Σ} (UM0 UM1 : iProp Σ)
      (dq dw dv : dfrac) (ps s0 : Z) (len c gp : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (nn : nat) :
    ushp_malloc_ty UM0 UM1 ->
    (c <= len)%nat ->
    ushq_barw len f gp ->
    ushs_toks len f gp c args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    ⊢ UkShPipeCm.ushq_pex_left_at N UM0 UM1 dq dw dv ps s0
        (mword_of_int (s0 + Z.of_nat c)) len gp f args Pex
        (16 + (24 + (8 + nn))).
  Proof using .
    intros Hmal Hcle Hbw Htoks Hpos Hlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros (h m rpc)
      "%Ha0 %Ha1 %Erpc #Hcode #Hro Hcur Hstr Hws Hsy HM0 #Hpx Hpay Hrun Hcont".
    rewrite <- Erpc.
    iApply (UkShPipePex.wp_kshp_parseexec_barw N UM0 UM1 Hmal h m dq dw dv
              ps s0 len c f (mword_of_int (s0 + Z.of_nat c)) args gp nn
              Ha0 Ha1 Hcle eq_refl Hbw Htoks Hpos Hlen Hs0 Hs64 Hps0 Hps8
              Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM0 Hpx Hpay Hrun").
    iIntros (pl) "%Hplsz Hnodel Hcur Hstr Hws Hsy".
    iIntros (h' m') "%Hcs %Ha0' HM1 Hpay Hrun".
    iApply ("Hcont" $! pl with "[] Hnodel Hcur Hstr Hws Hsy [] [] HM1 Hpay Hrun").
    - iPureIntro. exact Hplsz.
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
  Qed.

  (* ===================================================================== *)
  (* §3 A PIPE NODE AND ITS TWO CHILDREN ARE THE PARSER'S TREE               *)
  (* ===================================================================== *)
  Lemma ushq_tree_pipe (s0 t pl pr : Z) (a : list (nat * nat))
      (r : ushp_cmd) :
    ushp_pipe_node t pl pr -∗
    ushp_exec_at s0 pl a -∗
    ushp_tree s0 pr r -∗
    ushp_tree s0 t (UshpPipe (UshpExec a) r).
  Proof using .
    iIntros "Hn Hl Hr". rewrite /UkShPipeParse.ushp_pipe_node.
    iDestruct "Hn" as "(%Ht0 & %Ht8 & %Htz & [Hty Hpad] & Hwl & Hwr)".
    cbn [UkShParse.ushp_tree].
    iSplitR; [ iPureIntro; exact Ht0 | ].
    iSplitR; [ iPureIntro; exact Ht8 | ].
    iSplitL "Hty Hpad".
    { rewrite /UkShParse.ushp_type_at. cbn [UkShParse.ushp_ty].
      iFrame "Hty Hpad". }
    iSplitL "Hwl Hl".
    - iExists pl. iFrame "Hwl". iExact "Hl".
    - iExists pr. iFrame "Hwr Hr".
  Qed.

  (* ===================================================================== *)
  (* §4 THE WALK, BY INDUCTION ON THE NUMBER OF BARS                         *)
  (*                                                                        *)
  (* At [length rest] bars the budget is the landed turn's plus six words   *)
  (* per further bar (one [parsepipe] frame each), and the chain is entered  *)
  (* at link [i] and left at link [i + 2 * length rest + 1].  At one bar it  *)
  (* is [UkShPipeCm.wp_kshp_parsepipe_bar_closed]'s own walk.               *)
  (* ===================================================================== *)
  Lemma wp_kshp_parsepipe_bars {Pex : iProp Σ} (dq dw dv : dfrac)
      (ps s0 : Z) (len : nat) (f : nat -> bv 8) :
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    forall (c : nat) (a : list (nat * nat)) (rest : list (list (nat * nat))),
    ushq_bars len f c a rest ->
    forall (i nn : nat) (h : CpuId) (m : regfile),
    (i + 2 * length rest + 1 <= K)%nat ->
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat c)) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM i -∗
    ushp_oom Pex (20 + nn) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsepipe)
      (6 + (16 + (24 + (2 + (length rest * 6 + nn))))) -∗
    (∀ t : Z,
       ushp_tree s0 t (ushq_ptree a rest) -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM (i + 2 * length rest + 1) -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + (2 + (length rest * 6 + nn))))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushq_malloc_chain.
    intros Hs0 Hs64 Hps0 Hps8 Hpssz.
    induction 1 as [ c toks Hcle Hns Htoks Htlen
                   | c gp toks b rest Hcle Hbw Htoks Hpos Htlen Hbars IH ];
      intros i nn h m HK Ha0 Ha1;
      iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    - (* ---- NO BAR LEFT: the symbol-free walk on the line's suffix ---- *)
      destruct (ushs_toks_rel len c f c toks Htoks (le_n c))
        as (rel & Hrel & ->).
      rewrite Nat.sub_diag in Hrel.
      rewrite ushq_rebase_length in Htlen.
      assert (E1 : (i + 2 * length (@nil (list (nat * nat))) + 1)%nat = S i)
        by (cbn [length]; lia).
      assert (E2 : (6 + (16 + (24 + (2 + (length (@nil (list (nat * nat))) * 6
                                           + nn)))))%nat
                   = (6 + (16 + (24 + (2 + nn))))%nat)
        by (cbn [length]; lia).
      rewrite E1 E2.
      iApply (UkShPipeRight.wp_kshp_parsepipe_tail N (UM i) (UM (S i))
                (ushq_malloc_chain i ltac:(cbn [length] in HK; lia))
                h m dq dw dv ps s0 len c f rel (2 + nn)
                Ha0 Ha1 Hcle Hns (ushs_toks_tokens _ _ _ _ Hrel) Htlen
                Hs0 Hs64 Hps0 Hps8 Hpssz
                with "Hcode Hro Hcur Hstr Hws Hsy HM Hpx Hpay Hrun").
      iIntros (q) "%Hqsz Hnode".
      assert (Esh : UkShPipeRight.ushq_shift c rel = ushq_rebase c rel)
        by reflexivity.
      rewrite Esh.
      iApply ("Hcont" $! q with "[Hnode]").
      cbn [ushq_ptree UkShParse.ushp_tree]. iExact "Hnode".
    - (* ---- A BAR: the turn, its recursion the induction hypothesis ---- *)
      assert (HK' : (S i + 2 * length rest + 1 + 1 <= K)%nat)
        by (cbn [length] in HK; lia).
      assert (E2 : (6 + (16 + (24 + (2 + (length (b :: rest) * 6 + nn)))))%nat
                   = (6 + (16 + (24 + (8 + (length rest * 6 + nn)))))%nat)
        by (cbn [length]; lia).
      assert (E3 : (i + 2 * length (b :: rest) + 1)%nat
                   = S (S i + 2 * length rest + 1)) by (cbn [length]; lia).
      rewrite E2 E3.
      iDestruct (UkShCmdalloc.ushp_oom_mono N Pex (20 + nn)
                   (20 + (length rest * 6 + nn)) ltac:(lia) with "Hpx") as "#Hpxb".
      iApply (UkShPipeCm.wp_kshp_parsepipe_bar_g N (UM i) (UM (S i))
                (UM (S i + 2 * length rest + 1))
                (UM (S (S i + 2 * length rest + 1)))
                h m dq dw dv ps s0 (mword_of_int (s0 + Z.of_nat c)) len gp f
                toks (fun pr : Z => ushp_tree s0 pr (ushq_ptree b rest))
                (length rest * 6 + nn)
                Ha0 Ha1 Hbw Hs0 Hs64 Hps0 Hps8 Hpssz
                with "Hcode Hro Hcur Hstr Hws Hsy HM Hpxb Hpay [] [] [] Hrun
                      [Hcont]").
      + (* (i) the stage's own parseexec, from its cursor *)
        iApply (ushq_pex_left_at_holds (UM i) (UM (S i)) dq dw dv ps s0 len c
                  gp f toks (length rest * 6 + nn)
                  (ushq_malloc_chain i ltac:(lia))
                  Hcle Hbw Htoks Hpos Htlen Hs0 Hs64 Hps0 Hps8 Hpssz).
      + (* (iii) THE RECURSION IS THE INDUCTION HYPOTHESIS *)
        iIntros (h1 m1) "%Ha0' %Ha1' Hcode' Hro' Hcur Hstr Hws Hsy HM1 Hpx'
                         Hpay Hrun Hk".
        assert (E4 : (16 + (24 + (8 + (length rest * 6 + nn))))%nat
                     = (6 + (16 + (24 + (2 + (length rest * 6 + nn)))))%nat)
          by lia.
        rewrite E4.
        (* the recursion's own law is the one this walk holds: the call
           premise's is at the outer stage's (larger) budget *)
        iApply (IH (S i) nn h1 m1 ltac:(lia) Ha0' Ha1'
                  with "Hcode' Hro' Hcur Hstr Hws Hsy HM1 Hpx Hpay Hrun").
        iIntros (t) "Ht". iApply ("Hk" $! t with "Ht").
      + (* (ii) pipecmd, the stage's LAST allocation *)
        iApply (UkShPipeCm.ushq_pipecmd_call_holds N
                  (UM (S i + 2 * length rest + 1))
                  (UM (S (S i + 2 * length rest + 1)))
                  (length rest * 6 + nn)
                  (ushq_malloc_chain (S i + 2 * length rest + 1)
                     ltac:(lia))).
      + iIntros (t pl pr) "%Hplsz Hpnode Hnodel Hnoder".
        iApply ("Hcont" $! t with "[Hpnode Hnodel Hnoder]").
        cbn [ushq_ptree].
        iApply (ushq_tree_pipe s0 t pl pr toks (ushq_ptree b rest)
                  with "Hpnode Hnodel Hnoder").
  Qed.

  (* ...and the one-bar line through it, as a check that the induction's
     base and step compose at the landed shape *)
  Corollary wp_kshp_parsepipe_bars_pipe {Pex : iProp Σ} (h : CpuId)
      (m : regfile) (dq dw dv : dfrac) (ps s0 : Z) (len gp ge : nat)
      (f : nat -> bv 8) (args : list (nat * nat)) (i nn : nat) :
    (i + 2 * 1 + 1 <= K)%nat ->
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    ushs_toks len f len (S (S gp)) [(S (S gp), ge)] ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int (s0 + Z.of_nat 0)) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM i -∗
    ushp_oom Pex (20 + nn) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsepipe)
      (6 + (16 + (24 + (2 + (1 * 6 + nn))))) -∗
    (∀ t : Z,
       ushp_tree s0 t (UshpPipe (UshpExec args) (UshpExec [(S (S gp), ge)])) -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM (i + 2 * 1 + 1) -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + (2 + (1 * 6 + nn))))) -∗
           mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using ushq_malloc_chain.
    intros HK Ha0 Ha1 Hq Ht Hpos Hlt Hr Hs0 Hs64 Hps0 Hps8 Hpssz.
    exact (wp_kshp_parsepipe_bars dq dw dv ps s0 len f Hs0 Hs64 Hps0 Hps8
             Hpssz 0%nat args [[(S (S gp), ge)]]
             (ushq_bars_of_pipe len f gp ge args Hq Ht Hpos Hlt Hr)
             i nn h m HK Ha0 Ha1).
  Qed.

End UkShPipesParse.
