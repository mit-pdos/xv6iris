(* ===================================================================== *)
(* UkShPipesSeam.v -- A PIPELINE'S PARSE TREE BECOMES THE RUNNER'S TREE,  *)
(* lane PIPES-C3 (design/pipes-general.md §5, cut C3).                    *)
(*                                                                        *)
(* [UkShPipeSeam.ush_cmd_of_ushp_pipe] at any length: the parser's right  *)
(* spine [UkShPipesParse.ushq_ptree a rest] -- what                       *)
(* [UkShPipesParse.wp_kshp_parsepipe_bars] answers -- is converted to     *)
(* [UkShRun.ush_cmd] at [UkShPipe.ush_pipes], the runner's right-nested   *)
(* pipeline, by ONE induction on the stages.  Each level is the landed    *)
(* seam's own step: the node's type word and two child pointers           *)
(* PERSISTED, its address bound read off the run's heap, the EXEC child   *)
(* by [UkShMain.ush_cmd_of_ushp_gen] and the right child by the           *)
(* induction.  Every stage is cut from THE SAME line, as the landed seam  *)
(* cuts both of its sides.                                                *)
(*                                                                        *)
(* §2 is the ALLOCATOR CHAIN the parse walk threads, at the landed        *)
(* allocator: [UShPipeLaw.pl_malloc23]'s link at every index.  A line of  *)
(* N stages spends 2N-1 links (execcmd N times, then pipecmd N-1 times,   *)
(* innermost first -- UkShPipesParse's header), twelve units each out of  *)
(* the 4096 the first [morecore] inserts: [ushq_um_chain] funds 340       *)
(* links, so every pipeline of up to 170 stages.                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile.
Require Import UserPtTree.
Require Import UserPerm.     (* [usz_ok] *)
Require Import UserHeap UkRun.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShRun.
Require Import UkShMain.
Require Import UkShMalloc.
Require Import UkShPipe.     (* [ush_pipes] *)
Require Import UkShPipeSeam.
Require Import UkShSeam.        (* [ush_cmd_of_ushp_tree]: THE seam, once *)
Require Import RefParseBridge.  (* [ushq_ptree] *)
Require Import UexecSG.
Local Open Scope Z_scope.
Import Defs.

(* the three cut facts at every stage *)
Fixpoint ushq_cuts_ok (len : nat) (g : nat -> bv 8) (a : list (nat * nat))
    (rest : list (list (nat * nat))) : Prop :=
  match rest with
  | [] => ushq_cut_ok len g a
  | b :: rest' => ushq_cut_ok len g a /\ ushq_cuts_ok len g b rest'
  end.


(* ===================================================================== *)
(* THE SPINE AT THE GENERAL SEAM (user-once N): the cut facts stage by     *)
(* stage ARE [UkShSeam.ushp_cut_ok] on the spine, and the runner's         *)
(* pipeline IS [UkShSeam.ushcmd_of_tree] of it.                            *)
(* ===================================================================== *)
Lemma ushq_cuts_ok_cut_ok (len : nat) (g : nat -> bv 8) :
  forall (rest : list (list (nat * nat))) (a : list (nat * nat)),
    ushq_cuts_ok len g a rest -> UkShSeam.ushp_cut_ok len g (ushq_ptree a rest).
Proof using.
  induction rest as [| b rest IH ]; intros a H; cbn [ushq_cuts_ok ushq_ptree UkShSeam.ushp_cut_ok] in *.
  - exact H.
  - destruct H as [ Ha Hr ]. exact (conj Ha (IH b Hr)).
Qed.

Lemma ushq_ptree_ushcmd (s0 : Z) (g : nat -> bv 8) :
  forall (rest : list (list (nat * nat))) (a : list (nat * nat)),
    UkShSeam.ushcmd_of_tree s0 g (ushq_ptree a rest)
    = ush_pipes (UkShSeam.ush_args s0 g a) (List.map (UkShSeam.ush_args s0 g) rest).
Proof using.
  induction rest as [| b rest IH ]; intro a; cbn [ushq_ptree UkShSeam.ushcmd_of_tree ush_pipes List.map];
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Section UkShPipesSeam.
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
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ush_args := (UkShMain.ush_args).
  Local Notation ush_cmd_of_ushp_gen := (UkShMain.ush_cmd_of_ushp_gen N).
  Local Notation ubytes_persist := (UkShMain.ubytes_persist).
  Local Notation uword_persist := (UkShMain.uword_persist).
  Local Notation urun_ubytes_bnd := (UkShMain.urun_ubytes_bnd N).

  (* ===================================================================== *)
  (* §1 THE SEAM                                                            *)
  (* ===================================================================== *)

  (* a parser PIPE node, taken apart at its two children *)

  (* ...and a runner PIPE node put together from its persisted words *)

  Lemma ush_cmd_of_ushp_pipes (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (s0 : Z) (len : nat) (g : nat -> bv 8) :
    Z.of_nat len < 2 ^ 31 ->
    0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 ->
    forall (rest : list (list (nat * nat))) (a : list (nat * nat)) (p : Z),
    ushq_cuts_ok len g a rest ->
    urun N h m pc avail -∗
    ushp_tree s0 p (ushq_ptree a rest) -∗
    ubytesq γd DfracDiscarded s0 (S len) g ==∗
    urun N h m pc avail ∗
    ush_cmd γd p (ush_pipes (ush_args s0 g a) (map (ush_args s0 g) rest)).
  Proof using .
    intros Hlen31 Hs0 Hs0hi rest a p Hcuts.
    iIntros "Hrun Ht #Hline".
    iMod (UkShSeam.ush_cmd_of_ushp_tree N h m pc avail s0 len g (ushq_ptree a rest)
            (ushq_cuts_ok_cut_ok len g rest a Hcuts) Hlen31 Hs0 Hs0hi p
            with "Hrun Ht Hline") as "[Hrun Hcmd]".
    iModIntro. iFrame "Hrun". rewrite ushq_ptree_ushcmd. iExact "Hcmd".
  Qed.

  (* ...at the parse's own shape: the runner's tree is a right-nested
     pipeline, which is [UkShPipe.wp_kshr_runcmd_rpipe_closed]'s scope *)

  (* ===================================================================== *)
  (* §2 THE ALLOCATOR CHAIN, AT THE LANDED ALLOCATOR                        *)
  (*                                                                        *)
  (* [UShPipeLaw.pl_malloc23] (4072 -> 4060) at EVERY link: the first is    *)
  (* [UkShMalloc.ushm_malloc_le_exec] (the fresh state -> 4084), and link   *)
  (* [S j] is [UkShMalloc.ushm_malloc_le_one] at [4084 - 12 j], one         *)
  (* request of the parser's bound (168 bytes, twelve units) each.          *)
  (* ===================================================================== *)
  Definition ushq_um (sz : Z) (i : nat) : iProp Σ :=
    match i with
    | O => UkShMalloc.ushm_fresh N sz
    | S j => UkShMalloc.ushm_one_ge N (sz + 65536) (4084 - 12 * Z.of_nat j)
    end.

  Lemma ushq_um_chain (sz : Z) :
    8328 + 16 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    forall i : nat, (i < 340)%nat ->
      UkShParse.ushp_malloc_ty_le N 168 (ushq_um sz i) (ushq_um sz (S i)).
  Proof using Hpsok_free.
    intros Hszlo Hszal Hszok i Hi.
    assert (E12 : ((168 + 15) / 16 + 1)%Z = 12%Z) by (vm_compute; reflexivity).
    destruct i as [| j ].
    - cbn [ushq_um].
      replace (4084 - 12 * Z.of_nat 0) with 4084 by lia.
      exact (UkShMalloc.ushm_malloc_le_exec N Hpsok_free sz
               Hszlo Hszal Hszok).
    - cbn [ushq_um].
      replace (4084 - 12 * Z.of_nat (S j))
        with ((4084 - 12 * Z.of_nat j) - ((168 + 15) / 16 + 1))
        by (rewrite E12; lia).
      exact (UkShMalloc.ushm_malloc_le_one N 168 (sz + 65536)
               (4084 - 12 * Z.of_nat j) ltac:(lia) ltac:(lia)
               ltac:(rewrite E12; lia)).
  Qed.

  (* the landed pipe line's three links are the chain's first three *)
  Lemma ushq_um_landed (sz : Z) :
    ushq_um sz 0 = UkShMalloc.ushm_fresh N sz
    /\ ushq_um sz 1 = UkShMalloc.ushm_one_ge N (sz + 65536) 4084
    /\ ushq_um sz 2 = UkShMalloc.ushm_one_ge N (sz + 65536) 4072
    /\ ushq_um sz 3 = UkShMalloc.ushm_one_ge N (sz + 65536) 4060.
  Proof using . split_and!; reflexivity. Qed.

End UkShPipesSeam.
