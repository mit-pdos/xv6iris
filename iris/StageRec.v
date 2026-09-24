(* ===================================================================== *)
(*  StageRec.v -- THE STAGE RECORD: the console cursor a PAID CHILD runs  *)
(*  at, off the era that lent it.                                        *)
(*                                                                       *)
(*  Lane LINK-GEN-3 (claude-notes/projects/app-file.md, LINK-GEN's        *)
(*  findings section 5, "WHAT COULD NOT BE ABSTRACTED").  [LinkRec.v]     *)
(*  abstracts the era's CREDENTIAL FAMILIES, which is everything the      *)
(*  seven console files need except two: [UEchoOut] and [UShEchoPay] read *)
(*  an EXPLICIT STAGE -- [UEchoOut.ech v ps0 cs0 I0 P p] names [ps0],     *)
(*  [cs0], [I0] and [P] OUTSIDE any existential, because a forked child   *)
(*  writes its block byte by byte at a cursor its parent handed it, and   *)
(*  a credential whose stage is existentially quantified cannot be        *)
(*  stepped.  This file names that stage.                                 *)
(*                                                                       *)
(*  TWO RECORDS, and the split is what makes the FRAMED form possible:    *)
(*                                                                       *)
(*   - [CurRec L] is the CURSOR and its byte step alone: an opaque stage  *)
(*     type [ck_stg], the stage's admissibility [ck_ok st ws] at the      *)
(*     LINE the round answers, the bytes the program writes [ck_alt ws],  *)
(*     the cursor [ck_cur k v st p] and the step [ck_step].  It is all    *)
(*     [UEchoOut] takes.                                                  *)
(*   - [cur_hold S R] is [S] with a LINEAR resource [R] riding the        *)
(*     cursor.  This is why the cursor is a record of its own: sh's round *)
(*     at the file application lends its child [Wcf I 3 = Wcl I 3 * hold  *)
(*     I] and is owed [Wcf I 0 = Wcl I 0 * hold I] back, so the deed      *)
(*     FRACTION has to cross echo's whole walk -- and the walk's exit     *)
(*     wand is PERSISTENT ([UEchoOut.echo_uexec_slot_at]'s [box]), so a   *)
(*     linear resource can only reach the exit by riding the cursor,      *)
(*     which is the one linear thing the walk already threads.            *)
(*   - [StageRec L] adds the ONE law that ties the cursor to the record's *)
(*     families: [sk_lend_stage], which opens the era's LEND              *)
(*     ([LinkRec.lk_lend], echo's [EchoLinksLine.ewc_blk_0_lend]) into a  *)
(*     stage, the cursor at offset zero, and -- persistently -- what the  *)
(*     block's END pays ([EchoLinksLine.ewc_post_of_ech]).                *)
(*                                                                       *)
(*  THE LINE IS AN INDEX, NOT A COMPONENT OF THE STAGE.  [ck_ok st ws]    *)
(*  and [ck_alt ws] take the word list separately, which is what makes    *)
(*  [UEchoOut.ech] and [UEchoOut.echo_stage] recoverable BY CONVERSION    *)
(*  at the echo instance: echo's stage record is exactly the brief's      *)
(*  [list nat * list nat * list (bv 8) * nat] and carries no line.        *)
(*                                                                       *)
(*  ONE ALTERNATIVE, NOT FOUR.  [ck_alt] is the alternative the PROGRAM   *)
(*  writes -- alternative 0, the "good" one -- and not a family indexed   *)
(*  by [a]: the shell's own diagnostics go through [LinkRec]'s            *)
(*  [lk_blk_step] and never through a cursor.                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import EchoOut.
Require Import EchoLinks.
Require Import EchoLinksLine.
Require Import LinkRec.
(* as in LinkRec: the Sail imports leave string_scope on top and [++]
   would elaborate as String.append. *)
Local Open Scope list_scope.

(* ===================================================================== *)
(*  THE PURE HALF OF ECHO'S STAGE (it was [UEchoOut]'s S0; it moves here  *)
(*  because the record's echo instance is what needs it, and [UEchoOut]   *)
(*  sits above this file).                                                *)
(* ===================================================================== *)

(* THE STAGE echo RUNS AT.  The era stands at a LINE BOUNDARY -- the input
   [I0] has no partial line -- with every line before the last already
   resolved, its last body the line [ws] echo was exec'd for, and echo's
   cursor the first byte the stream owes at that boundary.  This is
   [EchoLinks.wr_blk] with the line named: the shell's fork lends exactly
   that credential. *)
Definition echo_stage (ps0 cs0 : list nat) (I0 : list (bv 8))
    (ws : list (list (bv 8))) (P : nat) : Prop :=
  rest_of I0 = []
  /\ nlines I0 = S (length cs0)
  /\ last_ws I0 = ws
  /\ P = length (proc_before ps0 cs0 I0)
  /\ pro_pin ps0 cs0 I0.

Lemma echo_stage_blk (ps0 cs0 : list nat) (I0 : list (bv 8))
    (ws : list (list (bv 8))) (P : nat) :
  echo_stage ps0 cs0 I0 ws P -> EchoLinks.wr_blk ps0 cs0 I0 P.
Proof using. intros (Hr & Hn & _ & HP & Hpin). by split_and!. Qed.

Lemma echo_stage_nonnil (ps0 cs0 : list nat) (I0 : list (bv 8))
    (ws : list (list (bv 8))) (P : nat) :
  echo_stage ps0 cs0 I0 ws P -> I0 <> [].
Proof using.
  intro Hst.
  exact (EchoLinks.wr_blk_nonnil ps0 cs0 I0 P (echo_stage_blk _ _ _ _ _ Hst)).
Qed.

(* the choice list echo's first byte extends still pins every round below
   the boundary: the blocks it reads are the ones already there *)
Lemma echo_stage_pin0 (ps0 cs0 : list nat) (I0 : list (bv 8))
    (ws : list (list (bv 8))) (P : nat) :
  echo_stage ps0 cs0 I0 ws P -> pro_pin ps0 (cs0 ++ [0%nat]) I0.
Proof using.
  intro Hst.
  exact (EchoLinksLine.wr_blk_pin_snoc ps0 cs0 I0 P 0%nat
           (echo_stage_blk _ _ _ _ _ Hst)).
Qed.

(* WHAT THE ORDINARY WRITE LINK ASKS FOR, once the choice is filed: the
   stream up to the next boundary is what it was, and then this line's
   whole alternative.  It IS [EchoLinksLine.wr_blk_byte] at [a = 0] -- the
   block step the shell's own diagnostics take at their own alternative. *)
Lemma proc_stream_alt0 (ps0 cs0 : list nat) (I0 : list (bv 8))
    (ws : list (list (bv 8))) (P j : nat) (b : bv 8) :
  echo_stage ps0 cs0 I0 ws P ->
  line_alts_of ws !!! 0%nat !! j = Some b ->
  proc_stream ps0 (cs0 ++ [0%nat]) I0 !! (P + j)%nat = Some b.
Proof using.
  intros Hst Hb.
  pose proof Hst as (_ & _ & Hws & _ & _).
  apply (EchoLinksLine.wr_blk_byte ps0 cs0 I0 P 0%nat j b
           (echo_stage_blk _ _ _ _ _ Hst)).
  rewrite Hws. exact Hb.
Qed.

(* THE CHOICE LIST GROWS AT THE FIRST BYTE AND NOT BEFORE, which is the
   whole content of [echcs] ([EchoLinksLine.blkcs] at [a = 0]). *)
Definition echcs (cs0 : list nat) (p : nat) : list nat :=
  match p with O => cs0 | S _ => cs0 ++ [0%nat] end.

Lemma echcs_pos (cs0 : list nat) (p : nat) :
  (0 < p)%nat -> echcs cs0 p = cs0 ++ [0%nat].
Proof using. intro Hp. destruct p as [| p']; [ lia | reflexivity ]. Qed.

(* ECHO'S STAGE AS A TYPE -- the brief's [list nat * list nat *
   list (bv 8) * nat], with the four names written out. *)
Record echo_stg := MkEchoStg {
  es_ps : list nat;
  es_cs : list nat;
  es_I : list (bv 8);
  es_P : nat;
}.

(* ===================================================================== *)
(*  THE TWO RECORDS                                                       *)
(* ===================================================================== *)
Section stagerec.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context `{HRg : !riscvGS Σ}.

  Record CurRec (L : LinkRec Σ) := MkCurRec {
    (* the stage the child runs at: opaque, and carried by VALUE through
       the walk (the cursor's own index is the only thing that moves) *)
    ck_stg : Type;
    (* ...its admissibility AT THE LINE the round answers *)
    ck_ok : ck_stg -> list (list (bv 8)) -> Prop;
    (* ...and the bytes the program's own alternative writes *)
    ck_alt : list (list (bv 8)) -> list (bv 8);
    (* THE INPUTS THIS CURSOR IS ABOUT (the program stream).  [ck_alt] is
       a function of the LINE alone, and at an era with more than one line
       shape that is only true of SOME inputs: the file application's
       redirect child writes nothing to the console and its [cat] child
       writes cat's own bytes, so [line_alts_of ws !!! 0] is the block
       only at an [LEcho] line.  echo's era has one shape and takes
       [fun _ => True]. *)
    ck_lineok : list (bv 8) -> Prop;
    (* THE CURSOR: [p] of those bytes are out, and the era's bundle says
       so -- or the era is tainted (the disjunction is inside). *)
    ck_cur : nat -> era_pins -> ck_stg -> nat -> iProp Σ;
    ck_cur_tl : forall k v st p, Timeless (ck_cur k v st p);
    (* ONE BYTE, through the era's write link *)
    ck_step : forall (k : nat) (v : era_pins) (st : ck_stg)
                     (ws : list (list (bv 8))) (i : nat) (b : bv 8)
                     (Φ : iProp Σ),
      ck_ok st ws -> ck_alt ws !! i = Some b ->
      ⊢ lk_pin L k v -∗ lk_links L -∗ ck_cur k v st i -∗
        (ck_cur k v st (S i) -∗ Φ) -∗ out_link Uart0 k b Φ;
  }.

  Record StageRec (L : LinkRec Σ) := MkStageRec {
    sk_cur : CurRec L;
    (* THE CODE THE PROGRAM'S CURSOR FILES at input [I]: the alternative
       whose continuation is the program's own output.  [0] at the echo
       and file models, whose code [0] IS that output; the N-stage
       pipeline model encodes the block itself ([PipesDisc.plalt_code
       (PLRun _)]), so its code is a function of the line (cut C8). *)
    sk_code : list (bv 8) -> nat;
    (* WHAT SH'S FORK LENDS ITS CHILD, OPENED.  [LinkRec.lk_lend] is the
       era's lend as a credential; this is the same thing as a STAGE, the
       cursor at offset zero, and -- persistently, so that it survives the
       exit wand's box -- what the block's END pays. *)
    sk_lend_stage : forall (k : nat) (v : era_pins) (I : list (bv 8)),
      ck_lineok L sk_cur I ->
      ⊢ lk_lend L k v I -∗
        (∃ st : ck_stg L sk_cur,
           ⌜ck_ok L sk_cur st (last_ws I)⌝
           (* THE GOOD ALTERNATIVE OF A LINE IS ECHO'S OWN OUTPUT.  It is
              the same list at either application -- what the era's model
              differs about is the OTHER alternatives -- so the program
              tier may read it off [EchoDisc.line_alts_of] and only the
              cursor is abstract. *)
           ∗ ⌜ck_alt L sk_cur (last_ws I)
              = line_alts_of (last_ws I) !!! 0%nat⌝
           ∗ ck_cur L sk_cur k v st 0%nat
           ∗ □ (ck_cur L sk_cur k v st
                  (length (wl_line (drop 1 (last_ws I)))) -∗
                lk_post L k v I (sk_code I)))
        ∨ lk_T L;
    (* ...AND THAT ALTERNATIVE ENDS WITH THE SHELL'S PROMPT, which is what
       makes the block a BOUNDARY credential when the child exits
       ([LinkRec.lk_lcred_of_post_a]).  echo's is [0 < 3]. *)
    (* ...AND IT IS THE SAME GUARD (the program stream): at an era with
       more than one line shape, alternative 0 is admissible only at the
       lines the cursor is about. *)
    sk_apr0 : forall I : list (bv 8), ck_lineok L sk_cur I -> lk_apr L I (sk_code I);
  }.

End stagerec.

Global Arguments CurRec {_ _ _} _.
Global Arguments StageRec {_ _ _} _.
Global Arguments ck_stg {_ _ _ _} _.
Global Arguments ck_ok {_ _ _ _} _ _ _.
Global Arguments ck_alt {_ _ _ _} _ _.
Global Arguments ck_lineok {_ _ _ _} _ _.
Global Arguments ck_cur {_ _ _ _} _ _ _ _ _.
Global Arguments ck_cur_tl {_ _ _ _} _ _ _ _ _.
Global Arguments ck_step {_ _ _ _} _ _ _ _ _ _ _ _.
Global Arguments sk_cur {_ _ _ _} _.
Global Arguments sk_code {_ _ _ _} _ _.
Global Arguments sk_lend_stage {_ _ _ _} _ _ _ _ _.
Global Arguments sk_apr0 {_ _ _ _} _ _.
Global Arguments MkCurRec {_ _ _} _.
Global Arguments MkStageRec {_ _ _} _.

Global Existing Instance ck_cur_tl.

(* ===================================================================== *)
(*  THE CURSOR WITH A LINEAR RESOURCE RIDING IT                           *)
(*                                                                       *)
(*  [R] crosses the whole walk untouched: the step frames it, and the     *)
(*  walk's exit wand -- which is a BOX and therefore cannot produce a     *)
(*  linear resource on its own -- receives it from the cursor it is       *)
(*  applied to.  That is how sh's deed fraction reaches the child's exit  *)
(*  payload at the file application ([UShRound]'s [Wcf I p := Wcl I p *   *)
(*  sh_hold I]).                                                          *)
(* ===================================================================== *)
Section cur_hold.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context `{HRg : !riscvGS Σ}.
  Context (L : LinkRec Σ) (C : CurRec L) (R : iProp Σ).
  Context (HRT : Timeless R).

  Local Lemma ch_cur_tl (k : nat) (v : era_pins) (st : ck_stg C) (p : nat) :
    Timeless (ck_cur C k v st p ∗ R)%I.
  Proof using HRT. pose proof HRT. apply _. Qed.

  Local Lemma ch_step (k : nat) (v : era_pins) (st : ck_stg C)
      (ws : list (list (bv 8))) (i : nat) (b : bv 8) (Φ : iProp Σ) :
    ck_ok C st ws -> ck_alt C ws !! i = Some b ->
    ⊢ lk_pin L k v -∗ lk_links L -∗ (ck_cur C k v st i ∗ R) -∗
      ((ck_cur C k v st (S i) ∗ R) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hok Hb. iIntros "#Hpin #Hlk [Hc HR] HΦ".
    iApply (ck_step C k v st ws i b Φ Hok Hb with "Hpin Hlk Hc").
    iIntros "Hc". iApply "HΦ". iFrame "Hc HR".
  Qed.

  Definition cur_hold : CurRec L :=
    MkCurRec L (ck_stg C) (ck_ok C) (ck_alt C) (ck_lineok C)
      (fun k v st p => (ck_cur C k v st p ∗ R)%I)
      ch_cur_tl ch_step.

End cur_hold.

Global Arguments cur_hold {_ _ _ _} _ _ _.

(* ===================================================================== *)
(*  THE ECHO INSTANCE, DEFINITIONALLY (LinkRec's pattern).                *)
(* ===================================================================== *)
Section echo_stage_inst.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.
  Context `{HRg : !riscvGS Σ}.

  Local Notation LE := (echo_link_inst T γ).

  (* [UEchoOut.ech]'s body, at the stage record *)
  Definition echo_cur (k : nat) (v : era_pins) (st : echo_stg) (p : nat)
    : iProp Σ :=
    ((turn v (es_P st + p)%nat ∗ ps_lb v (es_ps st)
      ∗ cs_lb v (echcs (es_cs st) p) ∗ inp_lb v (es_I st)) ∨ T)%I.

  Local Lemma ei_cur_tl (k : nat) (v : era_pins) (st : echo_stg) (p : nat) :
    Timeless (echo_cur k v st p).
  Proof using HTT. rewrite /echo_cur. apply _. Qed.

  (* [UEchoOut.ech_step]'s content: the block-FIRST byte files the
     alternative through [EchoLinks.echo_link_blk], every byte after it
     goes through the ordinary link at the choice list the first one
     extended, and the taint arm continues the tower on its own. *)
  Local Lemma ei_step (k : nat) (v : era_pins) (st : echo_stg)
      (ws : list (list (bv 8))) (i : nat) (b : bv 8) (Φ : iProp Σ) :
    echo_stage (es_ps st) (es_cs st) (es_I st) ws (es_P st) ->
    line_alts_of ws !!! 0%nat !! i = Some b ->
    ⊢ era_pin γ k v -∗ EchoLinks.echo_links T γ -∗ echo_cur k v st i -∗
      (echo_cur k v st (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using HPT.
    destruct st as [ps0 cs0 I0 P]. cbn [es_ps es_cs es_I es_P].
    intros Hst Hb.
    iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (EchoLinks.echo_links_w with "Hlk") as "#Hw".
    iDestruct (EchoLinks.echo_links_blk with "Hlk") as "#Hblk".
    iDestruct (EchoLinks.echo_links_taint with "Hlk") as "#Ht".
    pose proof (echo_stage_nonnil ps0 cs0 I0 ws P Hst) as Hnn.
    pose proof (echo_stage_pin0 ps0 cs0 I0 ws P Hst) as Hpin0.
    pose proof Hst as (Hrest & Hnl & Hws & HP & Hpin).
    rewrite /echo_cur. cbn [es_ps es_cs es_I es_P].
    iDestruct "Hc" as "[(Htn & Hps & Hcs & HE) | #HT]".
    - destruct i as [| p']; cbn [echcs].
      + (* THE BLOCK-FIRST BYTE: it files the alternative *)
        rewrite Nat.add_0_r.
        iApply ("Hblk" $! k v P 0%nat b ps0 cs0 I0 Φ
                  with "[%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
        { exact Hnn. }
        { exact Hrest. }
        { rewrite Hnl. lia. }
        { exact Hpin. }
        { exact HP. }
        { lia. }
        { rewrite Hws. exact Hb. }
        iIntros "Hres". iApply "HΦ". cbn [echcs].
        replace (P + 1)%nat with (S P) by lia.
        iExact "Hres".
      + (* every byte after it, at the choice list the first one extended *)
        iApply ("Hw" $! k v (P + S p')%nat b ps0 (cs0 ++ [0%nat]) I0 Φ
                  with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
        { rewrite length_app Hnl. cbn [length]. lia. }
        { exact Hpin0. }
        { exact (proc_stream_alt0 ps0 cs0 I0 ws P (S p') b Hst Hb). }
        iIntros "Hres". iApply "HΦ". cbn [echcs].
        replace (P + S (S p'))%nat with (S (P + S p')) by lia.
        iExact "Hres".
    - (* THE TAINT ARM continues the tower on its own *)
      iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iRight.
  Qed.

  Definition echo_cur_inst : CurRec LE :=
    MkCurRec LE echo_stg
      (fun st ws => echo_stage (es_ps st) (es_cs st) (es_I st) ws (es_P st))
      (fun ws => line_alts_of ws !!! 0%nat)
      (fun _ => True)
      echo_cur ei_cur_tl ei_step.

  (* THE LEND, OPENED.  [EchoLinksLine.ewc_blk_0_lend] gives the turn
     bundle and [wr_blk_t_stage] reads echo's own stage off it;
     [ewc_post_of_ech] is what the block's end pays, and it needs nothing
     linear, so it goes under the box. *)
  Local Lemma ei_lend_stage (k : nat) (v : era_pins) (I : list (bv 8)) :
    True ->
    ⊢ echo_lend T v I -∗
      (∃ st : echo_stg,
         ⌜echo_stage (es_ps st) (es_cs st) (es_I st) (last_ws I) (es_P st)⌝
         ∗ ⌜line_alts_of (last_ws I) !!! 0%nat
            = line_alts_of (last_ws I) !!! 0%nat⌝
         ∗ echo_cur k v st 0%nat
         ∗ □ (echo_cur k v st (length (wl_line (drop 1 (last_ws I)))) -∗
              EchoLinksLine.ewc_post T v I 0%nat))
      ∨ T.
  Proof using HPT.
    intros _.
    rewrite /echo_lend. iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct (EchoLinksLine.wr_blk_t_stage ps cs I P Hw)
      as (Hrest & Hn0 & HP & Hpin & Htail).
    iLeft. iExists (MkEchoStg ps cs I P). cbn [es_ps es_cs es_I es_P].
    iSplitR.
    { iPureIntro. rewrite /echo_stage. split_and!;
        [ exact Hrest | exact Hn0 | reflexivity | exact HP | exact Hpin ]. }
    iSplitR; [ by iPureIntro | ].
    iSplitL "Htn".
    - rewrite /echo_cur. cbn [es_ps es_cs es_I es_P echcs].
      rewrite Nat.add_0_r. iLeft. iFrame "Htn Hps Hcs HE".
    - iIntros "!> Hc".
      iApply (EchoLinksLine.ewc_post_of_ech T v ps cs I (last_ws I) P
                Hrest Hn0 eq_refl HP Hpin Htail).
      iEval (rewrite /echo_cur; cbn [es_ps es_cs es_I es_P];
             rewrite (echcs_pos cs (length (wl_line (drop 1 (last_ws I))))
                        (wl_line_pos (drop 1 (last_ws I))))) in "Hc".
      iExact "Hc".
  Qed.

  Local Lemma ei_apr0 (I : list (bv 8)) : True -> (0 < 3)%nat.
  Proof using . intros _. lia. Qed.

  Definition echo_stage_inst : StageRec LE :=
    MkStageRec LE echo_cur_inst (fun _ => 0%nat) ei_lend_stage ei_apr0.

  (* =================================================================== *)
  (*  THE DEFINITIONAL CHECK (LinkRec's).  If any of these ever needs a   *)
  (*  tactic, an echo statement has moved.                                *)
  (* =================================================================== *)
  Lemma echo_stage_inst_cur :
    ck_cur (sk_cur echo_stage_inst) = echo_cur.
  Proof using . reflexivity. Qed.
  Lemma echo_stage_inst_ok (st : echo_stg) (ws : list (list (bv 8))) :
    ck_ok (sk_cur echo_stage_inst) st ws
    = echo_stage (es_ps st) (es_cs st) (es_I st) ws (es_P st).
  Proof using . reflexivity. Qed.
  Lemma echo_stage_inst_alt (ws : list (list (bv 8))) :
    ck_alt (sk_cur echo_stage_inst) ws = line_alts_of ws !!! 0%nat.
  Proof using . reflexivity. Qed.
  Lemma echo_stage_inst_cur_body (k : nat) (v : era_pins)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (P p : nat) :
    ck_cur (sk_cur echo_stage_inst) k v (MkEchoStg ps0 cs0 I0 P) p
    = ((turn v (P + p)%nat ∗ ps_lb v ps0 ∗ cs_lb v (echcs cs0 p)
        ∗ inp_lb v I0) ∨ T)%I.
  Proof using . reflexivity. Qed.
  Lemma echo_stage_inst_ok_body (ps0 cs0 : list nat) (I0 : list (bv 8))
      (ws : list (list (bv 8))) (P : nat) :
    ck_ok (sk_cur echo_stage_inst) (MkEchoStg ps0 cs0 I0 P) ws
    = echo_stage ps0 cs0 I0 ws P.
  Proof using . reflexivity. Qed.

End echo_stage_inst.
