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
Require Import UkShPipeLex.
Require Import UkShPipesLex.
Require Import RefParseBridge.  (* [ushq_ptree], [ref_parsecmd_bars] *)
Require Import RefParseSym.
Require Import UkShRedirs.      (* [ushp_malloc_chain] *)
Require Import UkShParser.      (* [wp_ref_parsepipe]: THE general parsepipe *)
Require Import UexecSG.
Require Import UkShPipeNode.
Local Open Scope Z_scope.
Import Defs.

(* the parse's answer: the right spine of EXEC nodes -- the reference
   parser's answer on the line ([RefParseBridge.ref_parsecmd_bars]), so it
   lives there; the name is kept here for every consumer *)
Notation ushq_ptree := RefParseBridge.ushq_ptree.

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
  Local Notation ushp_pipe_node := (UkShPipeNode.ushp_pipe_node N).
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

  (* ===================================================================== *)
  (* §3 A PIPE NODE AND ITS TWO CHILDREN ARE THE PARSER'S TREE               *)
  (* ===================================================================== *)

  (* ===================================================================== *)
  (* §4 THE WALK, BY INDUCTION ON THE NUMBER OF BARS                         *)
  (*                                                                        *)
  (* At [length rest] bars the budget is the landed turn's plus six words   *)
  (* per further bar (one [parsepipe] frame each), and the chain is entered  *)
  (* at link [i] and left at link [i + 2 * length rest + 1].  At one bar it  *)
  (* is [UkShPipeCm.wp_kshp_parsepipe_bar_closed]'s own walk.               *)
  (* ===================================================================== *)
  (* ===================================================================== *)
  (* THE SPINE AT THE GENERAL WALK (user-once N).  [wp_kshp_parsepipe_bars]  *)
  (* below is [UkShParser.wp_ref_parsepipe] at the reference's answer on    *)
  (* the bars ([RefParseBridge.ushq_bars_parsepipe]): its room is the        *)
  (* spine's [ushp_pp_room] (46 + 6 per bar) plus two words, its allocator  *)
  (* chain is the indexed chain's [2 * bars + 1] links, and its scope is    *)
  (* the stage's own cursor's ([ushq_bars_scope]).                          *)
  (* ===================================================================== *)
  Lemma ushq_ptree_pp_room (a : list (nat * nat)) (rest : list (list (nat * nat))) :
    UkShParser.ushp_pp_room (ushq_ptree a rest) = (46 + 6 * length rest)%nat.
  Proof using .
    revert a. induction rest as [| b rest IH ]; intro a;
      cbn [ushq_ptree UkShParser.ushp_pp_room length].
    - unfold UkShParser.ushp_pex_room, UkShParser.ushp_pex_extra. cbn [ref_has_redir]. lia.
    - rewrite IH. unfold UkShParser.ushp_pex_room, UkShParser.ushp_pex_extra.
      cbn [ref_has_redir]. lia.
  Qed.

  (* ...and its deepest out-of-memory panic ([UkShParser.ushp_pp_deep]):
     eighteen fewer than the room at every bar, so the general walk's law
     at the room less it is exactly this walk's [20 + nn] *)
  Lemma ushq_ptree_pp_deep (a : list (nat * nat)) (rest : list (list (nat * nat))) :
    UkShParser.ushp_pp_deep (ushq_ptree a rest) = (28 + 6 * length rest)%nat.
  Proof using .
    revert a. induction rest as [| b rest IH ]; intro a;
      cbn [ushq_ptree UkShParser.ushp_pp_deep length].
    - unfold UkShArgs.ushp_pex_deep. cbn [ref_has_redir]. lia.
    - rewrite IH. unfold UkShArgs.ushp_pex_deep. cbn [ref_has_redir]. lia.
  Qed.

  (* the indexed chain, as the general walk's chain predicate *)
  Lemma ushq_UM_chain (k i : nat) :
    (i + k <= K)%nat -> UkShRedirs.ushp_malloc_chain N k (UM i) (UM (i + k)).
  Proof using ushq_malloc_chain.
    induction k as [| k IH ]; intro Hk.
    - cbn [UkShRedirs.ushp_malloc_chain]. rewrite Nat.add_0_r. reflexivity.
    - replace (S k) with (k + 1)%nat by lia.
      apply (UkShRedirs.ushp_malloc_chain_app N k 1 _ (UM (i + k))); [ apply IH; lia | ].
      apply UkShRedirs.ushp_malloc_chain_1.
      replace (i + (k + 1))%nat with (S (i + k)) by lia.
      apply ushq_malloc_chain. lia.
  Qed.

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
    intros Hs0 Hs64 Hps0 Hps8 Hpssz c a rest Hbars i nn h m HK Ha0 Ha1.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM #Hpx Hpay Hrun Hcont".
    iDestruct (ustr_nonul with "Hstr") as %Hnn.
    pose proof (ushq_bars_le _ _ _ _ _ Hbars) as Hcle.
    replace (6 + (16 + (24 + (2 + (length rest * 6 + nn)))))%nat
      with (UkShParser.ushp_pp_room (ushq_ptree a rest) + (2 + nn))%nat
      by (rewrite ushq_ptree_pp_room; lia).
    (* the law at the general walk's budget: the room less the spine's depth *)
    iDestruct (UkShCmdalloc.ushp_oom_mono N Pex (20 + nn)
                 (UkShParser.ushp_pp_room (ushq_ptree a rest) + (2 + nn)
                  - UkShParser.ushp_pp_deep (ushq_ptree a rest))
                 ltac:(rewrite ushq_ptree_pp_room ushq_ptree_pp_deep; lia)
                 with "Hpx") as "#Hpxg".
    iApply (UkShParser.wp_ref_parsepipe N dq dw dv ps s0 len f (len + length rest + 1)
              h m c len (mword_of_int (s0 + Z.of_nat c)) (ushq_ptree a rest)
              (UM i) (UM (i + 2 * length rest + 1)) (2 + nn)
              Ha0 Ha1 Hcle eq_refl (ushq_bars_scope len f c a rest Hbars)
              (ushq_bars_parsepipe len f Hnn c a rest Hbars (len + length rest + 1) ltac:(lia))
              ltac:(rewrite ushq_ptree_nodes;
                    replace (i + 2 * length rest + 1)%nat with (i + (2 * length rest + 1))%nat by lia;
                    exact (ushq_UM_chain (2 * length rest + 1) i ltac:(lia)))
              Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM Hpxg Hpay Hrun").
    iIntros (root) "Hot Hcur Hstr Hws Hsy".
    iIntros (h' m') "%Hcs %Ha0' HM' Hpay Hrun".
    iApply ("Hcont" $! root with "[Hot] Hcur Hstr Hws Hsy [%//] [%//] HM' Hpay Hrun").
    iApply (UkShParser.ushp_otree_close N with "Hot").
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
