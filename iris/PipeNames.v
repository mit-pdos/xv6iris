(* PipeNames.v -- the plain data of a pipe's ghost state: its five ghost
   names and the abstract STATE its byte queue is tracked at.  No Iris, no
   Sail: this sits below [Xv6Cameras] (which builds the queue's camera over
   [pipe_st]) and below [FdSlots] (whose [FdPipe] carries the names), so
   that a descriptor's state can name the pipe it is an end of.

   Design of record: claude-notes/design/pipe.md, "The byte queue". *)
From Stdlib Require Import ZArith List.
From stdpp Require Import base gmap list bitvector.definitions.
From transfinite.base_logic.lib Require Import own.   (* [gname] *)
From xv6iris Require Import StepIndex.

(* THE ABSTRACT STATE OF A PIPE: every byte ever written, in order; the
   read pointer -- [ws !! rp] is the next byte a read delivers -- and the
   two OPEN FLAGS, [struct pipe]'s [readopen] / [writeopen] as bools.  The
   flags are in the EXACT state so that a fragment holder knows, at every
   instant, whether the other end is still open -- which is what predicts
   an end-of-file ([pst_eof]) -- and so closing an end is a ghost step
   like writing a byte ([pst_close]), paid by the closer. *)
Record pipe_st := MkPipeSt
  { ps_ws : list (bv 8); ps_rp : nat; ps_ro : bool; ps_wo : bool }.

Global Instance pipe_st_eq_dec : EqDecision pipe_st.
Proof. solve_decision. Defined.
Global Instance pipe_st_inhabited : Inhabited pipe_st :=
  populate (MkPipeSt [] 0 true true).

(* the birth state, and the three steps *)
Definition pst0 : pipe_st := MkPipeSt [] 0 true true.
Definition pst_write (b : bv 8) (s : pipe_st) : pipe_st :=
  MkPipeSt (ps_ws s ++ [b]) (ps_rp s) (ps_ro s) (ps_wo s).
Definition pst_read (s : pipe_st) : pipe_st :=
  MkPipeSt (ps_ws s) (S (ps_rp s)) (ps_ro s) (ps_wo s).
(* closing end [w] -- [w] is the [struct file]'s writable flag, pipeclose's
   own argument: [true] closes the write end *)
Definition pst_close (w : bool) (s : pipe_st) : pipe_st :=
  if w then MkPipeSt (ps_ws s) (ps_rp s) (ps_ro s) false
       else MkPipeSt (ps_ws s) (ps_rp s) false (ps_wo s).
(* the open flag of end [w] *)
Definition pst_open (w : bool) (s : pipe_st) : bool :=
  if w then ps_wo s else ps_ro s.
(* the queue is empty: nothing written past the pointer *)
Definition pst_empty (s : pipe_st) : Prop := ps_rp s = length (ps_ws s).
(* end of file: empty, and nobody can write any more *)
Definition pst_eof (s : pipe_st) : Prop := pst_empty s /\ ps_wo s = false.
(* the next byte, when there is one *)
Definition pst_next (s : pipe_st) : option (bv 8) := ps_ws s !! ps_rp s.

Lemma pst_write_ws b s : ps_ws (pst_write b s) = ps_ws s ++ [b].
Proof. reflexivity. Qed.
Lemma pst_write_rp b s : ps_rp (pst_write b s) = ps_rp s.
Proof. reflexivity. Qed.
Lemma pst_read_ws s : ps_ws (pst_read s) = ps_ws s.
Proof. reflexivity. Qed.
Lemma pst_read_rp s : ps_rp (pst_read s) = S (ps_rp s).
Proof. reflexivity. Qed.
Lemma pst_close_open w s : pst_open w (pst_close w s) = false.
Proof. destruct w; reflexivity. Qed.
Lemma pst_close_other w s : pst_open (negb w) (pst_close w s) = pst_open (negb w) s.
Proof. destruct w; reflexivity. Qed.
Lemma pst_close_ws w s : ps_ws (pst_close w s) = ps_ws s.
Proof. destruct w; reflexivity. Qed.
Lemma pst_close_rp w s : ps_rp (pst_close w s) = ps_rp s.
Proof. destruct w; reflexivity. Qed.

(* A PIPE'S GHOST IDENTITY: per end, the reference fraction and the "still
   open" marker ([PipeInvDefs]), and the byte queue ([PipeQueue]).  Moved
   here from [PipeInvDefs] so that [FdSlots.FdPipe] can carry it: a
   descriptor's state names the pipe it is an end of, and both ends of one
   pipe carry the SAME record. *)
Record pipe_names := MkPipeNames
  { pn_read : gname; pn_write : gname;
    pn_mread : gname; pn_mwrite : gname;
    pn_queue : gname }.

Global Instance pipe_names_eq_dec : EqDecision pipe_names.
Proof. solve_decision. Defined.
Global Instance pipe_names_inhabited : Inhabited pipe_names :=
  populate (MkPipeNames 1%positive 1%positive 1%positive 1%positive 1%positive).
