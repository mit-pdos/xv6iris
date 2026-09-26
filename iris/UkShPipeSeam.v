(* ===================================================================== *)
(* UkShPipeSeam.v -- THE PIPE NODE BECOMES THE RUNNER'S TREE,             *)
(* lane SH-PARSE-PIPE (design/app-pipe.md SS5.1: the node catalogue        *)
(* [UkShRun.ush_cmd g t (UPipe (UExec l) (UExec r))] built from the two    *)
(* EXEC nodes).                                                           *)
(*                                                                        *)
(* [UkShMain.ush_cmd_of_ushp_gen] is the EXEC conversion at what it        *)
(* actually needs -- the line ALREADY PERSISTED plus three facts about it  *)
(* (each token is inside the line, its END byte is zero, no byte of its    *)
(* BODY is) -- and being stated that way is exactly what lets this file    *)
(* call it TWICE on one line, once per side of the pipe.  So the PIPE      *)
(* conversion is forty lines and no new mathematics:                       *)
(*                                                                        *)
(*   - the type word and the two child pointers are DISCARDED here (that   *)
(*     is what makes the runner's tree persistent, hence what lets it      *)
(*     cross sh's two forks as a payload -- [UkShRun.ush_cmd_forkable]);   *)
(*   - the node's address bound [p < 2 ^ 38] is read off the RUN's own     *)
(*     heap, as the EXEC conversion reads it, not assumed;                 *)
(*   - the two [ush_args] lists are cut from THE SAME line [g], which is   *)
(*     what [nulterminate]'s PIPE row ([UkShParser.wp_ref_nulterminate])   *)
(*     leaves behind                                                       *)
(*     ([ushp_nulfold toksr (ushp_nulfold toksl g)]), so the caller hands  *)
(*     one line and gets both commands.                                    *)
(*                                                                        *)
(* This is a LEAF and it is the node lane SH-PIPE consumes: everything     *)
(* above it (parseexec at the pipe line, parsepipe's turn, the parser      *)
(* theorem) is reported, not landed.                                      *)
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
Require Import UmodeAbi.
Require Import UserHeap UkRun.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseCmd.
Require Import UkShRun.
Require Import UkShMain.
Require Import UkShMalloc.
Require Import UkShPipeLex.
Require Import UkShPipeNode.    (* the pipe node predicate and its close *)
Require Import UkShSeam.        (* THE SEAM, once *)
Require Import UexecSG.
Local Open Scope Z_scope.
Import Defs.

Section UkShPipeSeam.
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

  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_pipe_node := (UkShPipeNode.ushp_pipe_node N).
  Local Notation ush_args := (UkShMain.ush_args).
  Local Notation ush_cmd_of_ushp_gen := (UkShMain.ush_cmd_of_ushp_gen N).
  Local Notation ubytes_persist := (UkShMain.ubytes_persist).
  Local Notation uword_persist := (UkShMain.uword_persist).
  Local Notation urun_ubytes_bnd := (UkShMain.urun_ubytes_bnd N).

  (* the three facts the EXEC conversion needs about ONE token list in the
     line, named once so the statement below reads *)
  Definition ushq_cut_ok (len : nat) (g : nat -> bv 8)
      (toks : list (nat * nat)) : Prop :=
    (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
       (fst tk < snd tk)%nat /\ (snd tk <= len)%nat)
    /\ (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
          g (snd tk) = ubyte0)
    /\ (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
          forall j : nat, (j < snd tk - fst tk)%nat ->
            g (fst tk + j)%nat <> ubyte0).

  Lemma ush_cmd_of_ushp_pipe (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (s0 p pl pr : Z) (len : nat) (g : nat -> bv 8)
      (toksl toksr : list (nat * nat)) :
    ushq_cut_ok len g toksl ->
    ushq_cut_ok len g toksr ->
    Z.of_nat len < 2 ^ 31 ->
    0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 ->
    urun N h m pc avail -∗
    ushp_pipe_node p pl pr -∗
    ushp_tree s0 pl (UshpExec toksl) -∗
    ushp_tree s0 pr (UshpExec toksr) -∗
    ubytesq γd DfracDiscarded s0 (S len) g ==∗
    urun N h m pc avail ∗
    ush_cmd γd p (UPipe (UExec (ush_args s0 g toksl))
                        (UExec (ush_args s0 g toksr))).
  Proof using .
    intros Hl Hr Hlen31 Hs0 Hs0hi.
    iIntros "Hrun Hn Hl Hr #Hline".
    (* the three nodes are the tree, closed; [ushq_cut_ok] at each side IS
       the general seam's EXEC case, conjunct for conjunct *)
    iDestruct (UkShPipeNode.ushp_pipe_close N s0 p pl pr (UshpExec toksl) (UshpExec toksr)
                 with "Hn Hl Hr") as "Htree".
    iApply (UkShSeam.ush_cmd_of_ushp_tree N h m pc avail s0 len g
              (UshpPipe (UshpExec toksl) (UshpExec toksr)) (conj Hl Hr)
              Hlen31 Hs0 Hs0hi p with "Hrun Htree Hline").
  Qed.

  (* ===================================================================== *)
  (* §2 THE THIRD ALLOCATION IS FREE, AND THE STOP RULE IS ANSWERED         *)
  (*                                                                        *)
  (* A pipe line makes THREE constructor calls, not two: [parseexec] runs   *)
  (* TWICE (once per side of the '|') and each run calls [execcmd], and     *)
  (* [parsepipe]'s turn calls [pipecmd] -- 168, 168 and 24 bytes, all       *)
  (* under the bound 168 the thirteen parser files carry                    *)
  (* ([UkShParse.ushp_malloc_ty_le N 168], SH-MALLOC-3).  The brief's STOP  *)
  (* rule asks whether that exceeds what [UkShMalloc.ushm_fresh]'s landed   *)
  (* chain funds.  IT DOES NOT, and no chain has to be extended:            *)
  (* [UkShMalloc.ushm_malloc_le_one] is already GENERAL in the free list's  *)
  (* remaining count [R], so every call after the first is an INSTANCE of   *)
  (* one landed theorem.  SH-MALLOC-3 bounds the REQUEST -- the parser's    *)
  (* capability is at 168 bytes -- and not the number of calls.             *)
  (* ===================================================================== *)

  (* the THIRD link, charged at the bound the parser carries: 4072 - 12.
     With [UkShMalloc.ushm_malloc_le_exec] (fresh -> 4084) and
     [ushm_malloc_le_next] (4084 -> 4072) this is the pipe line's whole
     parse -- THIRTY-SIX of the chunk's 4096 units. *)
  Corollary ushq_malloc_le_third (sz : Z) :
    UkShParse.ushp_malloc_ty_le N 168
      (UkShMalloc.ushm_one_ge N sz 4072)
      (UkShMalloc.ushm_one_ge N sz 4060).
  Proof using .
    assert (E : (4072 - ((168 + 15) / 16 + 1))%Z = 4060%Z)
      by (vm_compute; reflexivity).
    rewrite <- E.
    exact (UkShMalloc.ushm_malloc_le_one N 168 sz 4072 ltac:(lia) ltac:(lia)
             ltac:(vm_compute; reflexivity)).
  Qed.


  (* ===================================================================== *)
  (* §3 THE SEAM IS NOT VACUOUS                                             *)
  (*                                                                        *)
  (* [ushq_cut_ok] is a PREMISE of the conversion twice over, so a lane     *)
  (* that never instantiates it cannot tell a threaded premise from an      *)
  (* unsatisfiable one (durable-notes, Vacuity).  Here it is at the         *)
  (* application's own line and at the cut                                  *)
  (* [nulterminate]'s PIPE row leaves behind -- the right                   *)
  (* command's fold OVER the left command's, on one buffer.                 *)
  (* ===================================================================== *)

  Definition ushq_demo_toksl : list (nat * nat) :=
    [(0, 4)%nat; (5, 10)%nat; (11, 16)%nat].
  Definition ushq_demo_toksr : list (nat * nat) := [(19, 22)%nat].

  Definition ushq_demo_cut : nat -> bv 8 :=
    UkShParseCmd.ushp_nulfold ushq_demo_toksr
      (UkShParseCmd.ushp_nulfold ushq_demo_toksl
         (UkShParseCmd.ushp_ext 23
            (fun j : nat => UkShPipeLex.ushq_demo_f (0 + j)%nat))).

  Lemma ushq_demo_cut_ok_l : ushq_cut_ok 23 ushq_demo_cut ushq_demo_toksl.
  Proof using .
    rewrite /ushq_cut_ok /ushq_demo_toksl. split_and!;
      intros i tk Hi;
      destruct i as [| [| [| i ]]]; cbn in Hi; try discriminate Hi;
      injection Hi as <-; cbn [fst snd].
    - lia.
    - lia.
    - lia.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - intros j Hj; destruct j as [| [| [| [| j ]]]];
        [ | | | | lia ]; vm_compute; discriminate.
    - intros j Hj; destruct j as [| [| [| [| [| j ]]]]];
        [ | | | | | lia ]; vm_compute; discriminate.
    - intros j Hj; destruct j as [| [| [| [| [| j ]]]]];
        [ | | | | | lia ]; vm_compute; discriminate.
  Qed.

  Lemma ushq_demo_cut_ok_r : ushq_cut_ok 23 ushq_demo_cut ushq_demo_toksr.
  Proof using .
    rewrite /ushq_cut_ok /ushq_demo_toksr. split_and!;
      intros i tk Hi;
      destruct i as [| i ]; cbn in Hi; try discriminate Hi;
      injection Hi as <-; cbn [fst snd].
    - lia.
    - vm_compute; reflexivity.
    - intros j Hj; destruct j as [| [| [| j ]]];
        [ | | | lia ]; vm_compute; discriminate.
  Qed.

End UkShPipeSeam.
