(* PidEv.v -- the PURE event vocabulary of the pid ledger.

   Every pid allocation and release the kernel performs under [pid_lock]
   appends one ACTOR-LABELLED event to a ghost history [h : list pev]:

     PAlloc a p -- allocproc's inlined allocpid, run by actor [a] (the
                   hart's current proc word), handed out pid [p],
     PFree a p  -- freeproc's [p->pid = 0], run by actor [a], released
                   pid [p].

   The history is appended at the END ([h ++ [e]]), so both readings of it
   are LEFT FOLDS, and the snoc equations are [foldl_app] one-liners:

     live_of h  -- the live set: allocs insert the pid's value, frees
                   remove it;
     next_of pidmax h -- the allocation counter: an alloc of [p] moves it
                   to [p + 1], wrapping to 1 at [pidmax]; frees leave it.

   [next_step] / [next_of] take the bound [pidmax] as an explicit
   parameter: [ProcGeom.PIDMAX] lives in a file that imports Iris, and this
   file stays pure.  The lemma files instantiate it with [ProcGeom.PIDMAX].
   No Iris, no ghost state, no gname.

   Design: claude-notes/design/ni-pid-ledger.md (§2 D1, §3 W1). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import list countable gmap bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Instances.

(* ---------------------------------------------------------------------- *)
(* 1. The events.                                                          *)
(* ---------------------------------------------------------------------- *)

Inductive pev :=
  | PAlloc (act : mword 64) (pid : mword 32)
  | PFree (act : mword 64) (pid : mword 32).

(* the label: the actor that ran the call *)
Definition pev_actor (e : pev) : mword 64 :=
  match e with PAlloc a _ | PFree a _ => a end.

(* the pid the event carries *)
Definition pev_pid (e : pev) : mword 32 :=
  match e with PAlloc _ p | PFree _ p => p end.

Global Instance pev_eq_dec : EqDecision pev.
Proof. solve_decision. Defined.

Global Instance pev_countable : Countable pev.
Proof.
  refine (inj_countable'
    (fun e => match e with
              | PAlloc a p => (true, a, p) | PFree a p => (false, a, p)
              end)
    (fun '(b, a, p) => if b then PAlloc a p else PFree a p) _).
  by intros [].
Defined.

(* ---------------------------------------------------------------------- *)
(* 2. The live set and the counter, as left folds over the history.        *)
(* ---------------------------------------------------------------------- *)

Definition live_step (S : gset Z) (e : pev) : gset Z :=
  match e with
  | PAlloc _ p => {[bv_unsigned p]} ∪ S
  | PFree _ p => S ∖ {[bv_unsigned p]}
  end.

Definition live_of (h : list pev) : gset Z := foldl live_step ∅ h.

Definition next_step (pidmax : Z) (n : Z) (e : pev) : Z :=
  match e with
  | PAlloc _ p => if decide (bv_unsigned p = pidmax) then 1%Z else (bv_unsigned p + 1)%Z
  | PFree _ _ => n
  end.

Definition next_of (pidmax : Z) (h : list pev) : Z := foldl (next_step pidmax) 1%Z h.

(* ---------------------------------------------------------------------- *)
(* 3. The snoc equations.                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma live_of_nil : live_of [] = ∅.
Proof using . done. Qed.

Lemma live_of_snoc h e : live_of (h ++ [e]) = live_step (live_of h) e.
Proof using . unfold live_of. by rewrite foldl_app. Qed.

Lemma live_of_snoc_alloc h a p :
  live_of (h ++ [PAlloc a p]) = {[bv_unsigned p]} ∪ live_of h.
Proof using . by rewrite live_of_snoc. Qed.

Lemma live_of_snoc_free h a p :
  live_of (h ++ [PFree a p]) = live_of h ∖ {[bv_unsigned p]}.
Proof using . by rewrite live_of_snoc. Qed.

Lemma next_of_nil pidmax : next_of pidmax [] = 1%Z.
Proof using . done. Qed.

Lemma next_of_snoc pidmax h e :
  next_of pidmax (h ++ [e]) = next_step pidmax (next_of pidmax h) e.
Proof using . unfold next_of. by rewrite foldl_app. Qed.

Lemma next_of_snoc_alloc pidmax h a p :
  next_of pidmax (h ++ [PAlloc a p]) =
    if decide (bv_unsigned p = pidmax) then 1%Z else (bv_unsigned p + 1)%Z.
Proof using . by rewrite next_of_snoc. Qed.

Lemma next_of_snoc_free pidmax h a p :
  next_of pidmax (h ++ [PFree a p]) = next_of pidmax h.
Proof using . by rewrite next_of_snoc. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The counter stays in [1, pidmax] when every pid does.                *)
(* ---------------------------------------------------------------------- *)

Lemma next_of_bound pidmax h :
  (1 <= pidmax)%Z ->
  (forall e, e ∈ h -> (1 <= bv_unsigned (pev_pid e) <= pidmax)%Z) ->
  (1 <= next_of pidmax h <= pidmax)%Z.
Proof using .
  intros Hmax. induction h as [|e h IH] using rev_ind; intros Hin.
  - rewrite next_of_nil. lia.
  - rewrite next_of_snoc.
    assert (Hh : forall e', e' ∈ h -> (1 <= bv_unsigned (pev_pid e') <= pidmax)%Z).
    { intros e' He'. apply Hin. set_solver. }
    specialize (IH Hh).
    assert (He : (1 <= bv_unsigned (pev_pid e) <= pidmax)%Z) by (apply Hin; set_solver).
    destruct e as [a p|a p]; simpl in *; [|exact IH].
    case_decide; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. The rewrite forms the invariant's tie uses.                          *)
(* ---------------------------------------------------------------------- *)

Lemma live_of_snoc_alloc_dom S h a p :
  live_of h = S -> live_of (h ++ [PAlloc a p]) = {[bv_unsigned p]} ∪ S.
Proof using . intros <-. apply live_of_snoc_alloc. Qed.

Lemma live_of_snoc_free_dom S h a p :
  live_of h = S -> live_of (h ++ [PFree a p]) = S ∖ {[bv_unsigned p]}.
Proof using . intros <-. apply live_of_snoc_free. Qed.
