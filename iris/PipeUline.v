(* PipeUline.v -- THE BRIDGE from the PIPELINE application's line type
   [PipeDisc.pline] to the FILE application's [FileDisc.uline] (lane
   ULINE-LPIPE; design claude-notes/design/app-pipe.md section 5.8, STOP A).

   WHY A BRIDGE AND NOT ONE TYPE.  [PipeDisc.pline] is the pipe model's own
   line -- the thing [parse_pline], [palt_ok], [pcont] and the whole pipe
   discipline are stated at -- while [FileDisc.uline] is what the SHELL's
   loop reads: [UkSh.ush_line_at] and [UkSh.ush_rest_line_at]'s payload
   quantify over [FileDisc.uline], and their [D] parameter is how an era
   says which constructors it admits.  So the pipe era has to hand the loop
   a [FileDisc.uline], and [FileDisc.LPipe] (lane ULINE-LPIPE) is the
   constructor it hands it.  [uline_of_pline] is the injection, and the
   three lemmas below are the three projections [ush_line_at] reads,
   AGREEING with [PipeDisc]'s own readings -- which is what lets
   SH-PIPE-ROUND-2 state its [D] at [PipeDisc]'s reading of the line and
   still apply the shell's landed loop.

   This is a NEW file rather than a section of [PipeDisc.v] on purpose:
   [PipeDisc] does not read [FileDisc] (the dependency goes the other way
   for [FileDisc.LPipe]'s spelling, which is copied, not imported), the two
   modules share the constructor name [LEcho] and the definition names
   [line_body]/[line_bytes], and importing one into the other shadows them.
   Everything here is written qualified. *)

From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require FileDisc.
Require PipeDisc.
From stdpp Require Import ssreflect.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  THE INJECTION                                                         *)
(* ===================================================================== *)

Definition uline_of_pline (l : PipeDisc.pline) : FileDisc.uline :=
  match l with
  | PipeDisc.LEcho ws => FileDisc.LEcho ws
  | PipeDisc.LPipe ws => FileDisc.LPipe ws 1
  end.

Lemma uline_of_pline_inj : Inj eq eq uline_of_pline.
Proof using.
  intros l1 l2. destruct l1 as [ws1 | ws1]; destruct l2 as [ws2 | ws2];
    cbn [uline_of_pline]; intro H; try discriminate H; by injection H as ->.
Qed.

(* ===================================================================== *)
(*  THE THREE PROJECTIONS [UkSh.ush_line_at] READS                        *)
(* ===================================================================== *)

(* (1) the BODY and the BYTES agree on the nose -- [FileDisc.suf_barcat]
   and [PipeDisc.suf_pipecat] are the same six bytes, spelled twice. *)
Lemma line_body_of_pline (l : PipeDisc.pline) :
  FileDisc.line_body (uline_of_pline l) = PipeDisc.line_body l.
Proof using. by destruct l as [ws | ws]. Qed.

Lemma line_bytes_of_pline (l : PipeDisc.pline) :
  FileDisc.line_bytes (uline_of_pline l) = PipeDisc.line_bytes l.
Proof using. by destruct l as [ws | ws]. Qed.

(* (2) ...and so does ADMISSIBILITY, in both directions *)
Lemma uline_ok_of_pline (l : PipeDisc.pline) :
  PipeDisc.pline_ok l -> FileDisc.uline_ok (uline_of_pline l).
Proof using.
  destruct l as [ws | ws]; [done |]. intros [H1 H2].
  split; [exact H1 | split; [lia | exact H2]].
Qed.

Lemma pline_ok_of_uline (l : PipeDisc.pline) :
  FileDisc.uline_ok (uline_of_pline l) -> PipeDisc.pline_ok l.
Proof using.
  destruct l as [ws | ws]; [done |]. intros (H1 & _ & H2). split; [exact H1 | exact H2].
Qed.

(* (3) THE WORDS.  This is the one that is NOT a conversion, and it is the
   one [UkSh]'s [Hdsc_line] is about: its conclusion is
   [FileDisc.uline_ws lu = wl_words (rest_of I)], the WHOLE body's word
   list -- five words at [echo a b | cat] -- while [PipeDisc.pline_ws] is
   the LEFT command's three.  A lane that read [pline_ws] into the arm
   would get an [Hdsc_line] no era can satisfy and nothing in the build
   would see it (durable-notes, Vacuity).  [FileDisc.uline_ws_pipe] is
   what makes the spelling [ws ++ [bar; cat]] the body's own parse. *)
Lemma uline_ws_of_pline (l : PipeDisc.pline) :
  PipeDisc.pline_ok l ->
  FileDisc.uline_ws (uline_of_pline l) = wl_words (PipeDisc.line_body l).
Proof using.
  destruct l as [ws | ws].
  - intro Hok. cbn [uline_of_pline FileDisc.uline_ws PipeDisc.line_body].
    symmetry. exact (wl_words_body ws (line_ok_wf _ Hok)).
  - intros [Hok _]. symmetry. exact (FileDisc.uline_ws_pipe ws 1 Hok).
Qed.

(* ...and the left command's words are still there, as the prefix they are *)
Lemma uline_ws_of_pline_pipe (ws : list (list (bv 8))) :
  FileDisc.uline_ws (uline_of_pline (PipeDisc.LPipe ws))
  = PipeDisc.pline_ws (PipeDisc.LPipe ws) ++ [FileDisc.fd_w_bar; FileDisc.fd_w_cat].
Proof using. reflexivity. Qed.

(* ===================================================================== *)
(*  THE PIPE ERA'S LINES ARE EXACTLY THE ONES THE FILE ERA REFUSES        *)
(* ===================================================================== *)

(* the era discipline [UkSh]'s [Dl] is instantiated at, on the pipe side:
   every line the pipe parser files, and nothing else *)
Definition ush_line_pipe (l : FileDisc.uline) : Prop :=
  exists lp : PipeDisc.pline, l = uline_of_pline lp.

Lemma ush_line_pipe_of (lp : PipeDisc.pline) : ush_line_pipe (uline_of_pline lp).
Proof using. by exists lp. Qed.

(* [FileDisc.LPipe] is out of [FileDisc.parse_line]'s range and [LEchoF]
   and [LCat] are out of [PipeDisc.parse_pline]'s: the two eras' line sets
   meet exactly at [LEcho], which is what makes the constructor additive. *)
Lemma ush_line_pipe_not_file (l : FileDisc.uline) :
  ush_line_pipe l ->
  FileDisc.uline_nopipe l -> exists ws, l = FileDisc.LEcho ws.
Proof using.
  intros [[ws | ws] ->] Hnp; [ by exists ws | by destruct (Hnp ws 1%nat eq_refl) ].
Qed.

(* ===================================================================== *)
(*  THE VACUITY CHECK (durable-notes, "Vacuity")                          *)
(* ===================================================================== *)

(* A new arm of an admissibility predicate is worth nothing if nothing
   satisfies it, and nothing in the build would say so.  Here is one line
   that does, computed end to end: [echo hello | cat] is [FileDisc]-
   admissible, its [uline_ws] IS its body's parse, and that parse is the
   FOUR words -- which is the shape [UkSh]'s [Hdsc_line] asks for and the
   one [PipeDisc.pline_ws]'s two would have got wrong. *)
Definition demo_ws : list (list (bv 8)) := [sb "echo"%string; sb "hello"%string].

Lemma demo_pline_ok : PipeDisc.pline_ok (PipeDisc.LPipe demo_ws).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma demo_uline_ok :
  FileDisc.uline_ok (uline_of_pline (PipeDisc.LPipe demo_ws)).
Proof using. exact (uline_ok_of_pline _ demo_pline_ok). Qed.

Lemma demo_uline_ws :
  FileDisc.uline_ws (uline_of_pline (PipeDisc.LPipe demo_ws))
  = [sb "echo"%string; sb "hello"%string; sb "|"%string; sb "cat"%string].
Proof using. reflexivity. Qed.

Lemma demo_uline_ws_is_the_parse :
  FileDisc.uline_ws (uline_of_pline (PipeDisc.LPipe demo_ws))
  = wl_words (PipeDisc.line_body (PipeDisc.LPipe demo_ws)).
Proof using. exact (uline_ws_of_pline _ demo_pline_ok). Qed.

Lemma demo_line_bytes :
  FileDisc.line_bytes (uline_of_pline (PipeDisc.LPipe demo_ws))
  = sb "echo hello | cat"%string ++ [wl_nl].
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ...and the FILE era still refuses it, which is what keeps every FILE
   statement meaning what it meant *)
Lemma demo_not_file : FileDisc.parse_line (FileDisc.line_body
                        (uline_of_pline (PipeDisc.LPipe demo_ws))) = None.
Proof using. by vm_compute. Qed.
