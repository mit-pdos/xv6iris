(* ZombEv.v -- the PURE event vocabulary of the zombie ledger.

   Every exit and every reap the kernel performs under [wait_lock] appends
   one ACTOR-LABELLED event to a ghost history [h : list zev]:

     ZExit a p xs -- kexit's ZOMBIE store, run by actor [a] (the hart's
                     current proc word, the exiting process itself), with
                     pid [p] and exit status [xs] (ruling R1: the status
                     rides in the event because the parent reads it),
     ZReap a p    -- kwait's reap, run by actor [a] (the parent), which
                     took the zombie with pid [p].

   The history is appended at the END ([h ++ [e]]), so both readings of it
   are LEFT FOLDS, and the snoc equations are [foldl_app] one-liners:

     zombies_of h -- the zombie set: exits insert the pid's value, reaps
                     remove it;
     status_of h  -- the readable status per zombie pid: exits record the
                     status, reaps forget it.

   [status_of_dom] ties the two: the map's domain IS the zombie set.  No
   fork event (ruling R3: the pid ledger's [PAlloc parent pid] is the
   fork).  No Iris, no ghost state, no gname.

   Design: claude-notes/design/ni-zombie-ledger.md (§2 D1, §3 W1). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import list countable gmap bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Instances.

(* ---------------------------------------------------------------------- *)
(* 1. The events.                                                          *)
(* ---------------------------------------------------------------------- *)

Inductive zev :=
  | ZExit (act : mword 64) (pid : mword 32) (xs : Z)
  | ZReap (act : mword 64) (pid : mword 32).

(* the label: the actor that ran the transition *)
Definition zev_actor (e : zev) : mword 64 :=
  match e with ZExit a _ _ | ZReap a _ => a end.

(* the pid the event carries *)
Definition zev_pid (e : zev) : mword 32 :=
  match e with ZExit _ p _ | ZReap _ p => p end.

Global Instance zev_eq_dec : EqDecision zev.
Proof. solve_decision. Defined.

Global Instance zev_countable : Countable zev.
Proof.
  refine (inj_countable'
    (fun e => match e with
              | ZExit a p xs => (true, a, p, xs) | ZReap a p => (false, a, p, 0%Z)
              end)
    (fun '(b, a, p, xs) => if b then ZExit a p xs else ZReap a p) _).
  by intros [].
Defined.

(* ---------------------------------------------------------------------- *)
(* 2. The zombie set and the status map, as left folds over the history.  *)
(* ---------------------------------------------------------------------- *)

Definition zomb_step (S : gset Z) (e : zev) : gset Z :=
  match e with
  | ZExit _ p _ => {[bv_unsigned p]} ∪ S
  | ZReap _ p => S ∖ {[bv_unsigned p]}
  end.

Definition zombies_of (h : list zev) : gset Z := foldl zomb_step ∅ h.

Definition status_step (m : gmap Z Z) (e : zev) : gmap Z Z :=
  match e with
  | ZExit _ p xs => <[bv_unsigned p := xs]> m
  | ZReap _ p => delete (bv_unsigned p) m
  end.

Definition status_of (h : list zev) : gmap Z Z := foldl status_step ∅ h.

(* ---------------------------------------------------------------------- *)
(* 3. The snoc equations.                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma zombies_of_nil : zombies_of [] = ∅.
Proof using . done. Qed.

Lemma zombies_of_snoc h e : zombies_of (h ++ [e]) = zomb_step (zombies_of h) e.
Proof using . unfold zombies_of. by rewrite foldl_app. Qed.

Lemma zombies_of_snoc_exit h a p xs :
  zombies_of (h ++ [ZExit a p xs]) = {[bv_unsigned p]} ∪ zombies_of h.
Proof using . by rewrite zombies_of_snoc. Qed.

Lemma zombies_of_snoc_reap h a p :
  zombies_of (h ++ [ZReap a p]) = zombies_of h ∖ {[bv_unsigned p]}.
Proof using . by rewrite zombies_of_snoc. Qed.

Lemma status_of_nil : status_of [] = ∅.
Proof using . done. Qed.

Lemma status_of_snoc h e : status_of (h ++ [e]) = status_step (status_of h) e.
Proof using . unfold status_of. by rewrite foldl_app. Qed.

Lemma status_of_snoc_exit h a p xs :
  status_of (h ++ [ZExit a p xs]) = <[bv_unsigned p := xs]> (status_of h).
Proof using . by rewrite status_of_snoc. Qed.

Lemma status_of_snoc_reap h a p :
  status_of (h ++ [ZReap a p]) = delete (bv_unsigned p) (status_of h).
Proof using . by rewrite status_of_snoc. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The status map's domain is the zombie set.                           *)
(* ---------------------------------------------------------------------- *)

Lemma status_of_dom h : dom (status_of h) = zombies_of h.
Proof using .
  induction h as [|e h IH] using rev_ind.
  - rewrite status_of_nil, zombies_of_nil. apply dom_empty_L.
  - rewrite status_of_snoc, zombies_of_snoc.
    destruct e as [a p xs|a p]; simpl.
    + by rewrite dom_insert_L, IH.
    + by rewrite dom_delete_L, IH.
Qed.
