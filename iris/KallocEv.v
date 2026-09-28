(* KallocEv.v -- the PURE event vocabulary of the kalloc/kfree ledger.

   Every call of the page allocator appends one ACTOR-LABELLED event to a
   ghost history [h : list kev] kept inside [kmem_avail_auth]:

     KAlloc p   -- a [kalloc] run by actor [p] that returned a page,
     KNull p    -- a [kalloc] run by actor [p] that returned null (the pool
                   was empty), recorded so the outcome is POSITIONAL in the
                   history,
     KFree p    -- a [kfree] run by actor [p].

   The label is the actor only ([c->proc] of the calling hart's
   [cpu_own]), never the page address.  This file gives the two counts
   [allocs] / [frees], the emptiness predicate [pool_empty h := allocs h =
   frees h], the outcome-to-event map [kev_of], and the counting lemmas the
   invariant's tie

       npages + allocs h = frees h

   steps through at birth, at each of the three appends, and when reading
   emptiness off the history.  No Iris, no ghost state.

   Design: claude-notes/design/ni-kalloc-ledger.md (§2, D2 and D4). *)
From Stdlib Require Import Lia.
From stdpp Require Import list countable.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Instances.
Require Import PageGeom.
(* the counts are [nat]; the Sail imports leave another numeral scope on top *)
Local Open Scope nat_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The events.                                                          *)
(* ---------------------------------------------------------------------- *)

Inductive kev := KAlloc (p : mword 64) | KNull (p : mword 64) | KFree (p : mword 64).

(* the label: the actor that ran the call *)
Definition kev_actor (e : kev) : mword 64 :=
  match e with KAlloc p | KNull p | KFree p => p end.

Global Instance kev_eq_dec : EqDecision kev.
Proof. solve_decision. Defined.

Global Instance kev_countable : Countable kev.
Proof.
  refine (inj_countable'
    (fun e => match e with
              | KAlloc p => (0%nat, p) | KNull p => (1%nat, p) | KFree p => (2%nat, p)
              end)
    (fun '(n, p) => match n with
                    | 0%nat => KAlloc p | 1%nat => KNull p | _ => KFree p
                    end) _).
  by intros [] .
Defined.

(* ---------------------------------------------------------------------- *)
(* 2. The counts, emptiness, and the outcome map.                          *)
(*    Plain structural recursion (not [filter]+[length]) so [simpl]/[cbn]  *)
(*    compute on literal cons/nil.                                          *)
(* ---------------------------------------------------------------------- *)

Fixpoint allocs (h : list kev) : nat :=
  match h with
  | [] => 0
  | KAlloc _ :: h' => S (allocs h')
  | _ :: h' => allocs h'
  end.

Fixpoint frees (h : list kev) : nat :=
  match h with
  | [] => 0
  | KFree _ :: h' => S (frees h')
  | _ :: h' => frees h'
  end.

Definition pool_empty (h : list kev) : Prop := allocs h = frees h.

Definition kev_of (p r : mword 64) : kev :=
  if decide (r = nullp) then KNull p else KAlloc p.

(* ---------------------------------------------------------------------- *)
(* 3. Counting lemmas.                                                     *)
(* ---------------------------------------------------------------------- *)

Lemma allocs_nil : allocs [] = 0.
Proof using . done. Qed.
Lemma frees_nil : frees [] = 0.
Proof using . done. Qed.

Lemma allocs_app h1 h2 : allocs (h1 ++ h2) = allocs h1 + allocs h2.
Proof using . induction h1 as [|[] h1 IH]; simpl; lia. Qed.
Lemma frees_app h1 h2 : frees (h1 ++ h2) = frees h1 + frees h2.
Proof using . induction h1 as [|[] h1 IH]; simpl; lia. Qed.

Lemma allocs_alloc p : allocs [KAlloc p] = 1.
Proof using . done. Qed.
Lemma allocs_null p : allocs [KNull p] = 0.
Proof using . done. Qed.
Lemma allocs_free p : allocs [KFree p] = 0.
Proof using . done. Qed.
Lemma frees_alloc p : frees [KAlloc p] = 0.
Proof using . done. Qed.
Lemma frees_null p : frees [KNull p] = 0.
Proof using . done. Qed.
Lemma frees_free p : frees [KFree p] = 1.
Proof using . done. Qed.

Lemma allocs_snoc_alloc h p : allocs (h ++ [KAlloc p]) = S (allocs h).
Proof using . rewrite allocs_app; simpl. lia. Qed.
Lemma allocs_snoc_null h p : allocs (h ++ [KNull p]) = allocs h.
Proof using . rewrite allocs_app; simpl. lia. Qed.
Lemma allocs_snoc_free h p : allocs (h ++ [KFree p]) = allocs h.
Proof using . rewrite allocs_app; simpl. lia. Qed.
Lemma frees_snoc_alloc h p : frees (h ++ [KAlloc p]) = frees h.
Proof using . rewrite frees_app; simpl. lia. Qed.
Lemma frees_snoc_null h p : frees (h ++ [KNull p]) = frees h.
Proof using . rewrite frees_app; simpl. lia. Qed.
Lemma frees_snoc_free h p : frees (h ++ [KFree p]) = S (frees h).
Proof using . rewrite frees_app; simpl. lia. Qed.

Lemma allocs_replicate_free n p : allocs (replicate n (KFree p)) = 0.
Proof using . induction n; simpl; done. Qed.
Lemma frees_replicate_free n p : frees (replicate n (KFree p)) = n.
Proof using . induction n; simpl; lia. Qed.

Lemma kev_of_null p : kev_of p nullp = KNull p.
Proof using . unfold kev_of. by rewrite decide_True. Qed.
Lemma kev_of_page p r : r <> nullp -> kev_of p r = KAlloc p.
Proof using . intros Hr. unfold kev_of. by rewrite decide_False. Qed.
Lemma kev_actor_of p r : kev_actor (kev_of p r) = p.
Proof using . unfold kev_of. by case_decide. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The tie steps: [npages + allocs h = frees h] across birth, the three *)
(*    appends, and the reading of emptiness off the history.               *)
(* ---------------------------------------------------------------------- *)

Lemma tie_birth n p :
  n + allocs (replicate n (KFree p)) = frees (replicate n (KFree p)).
Proof using . rewrite allocs_replicate_free, frees_replicate_free. lia. Qed.

Lemma tie_alloc npages h p :
  S npages + allocs h = frees h ->
  npages + allocs (h ++ [KAlloc p]) = frees (h ++ [KAlloc p]).
Proof using . rewrite allocs_snoc_alloc, frees_snoc_alloc. lia. Qed.

Lemma tie_null h p :
  0 + allocs h = frees h ->
  0 + allocs (h ++ [KNull p]) = frees (h ++ [KNull p]).
Proof using . rewrite allocs_snoc_null, frees_snoc_null. lia. Qed.

Lemma tie_free npages h p :
  npages + allocs h = frees h ->
  S npages + allocs (h ++ [KFree p]) = frees (h ++ [KFree p]).
Proof using . rewrite allocs_snoc_free, frees_snoc_free. lia. Qed.

Lemma tie_empty h : 0 + allocs h = frees h -> pool_empty h.
Proof using . unfold pool_empty. lia. Qed.

Lemma tie_nonempty npages h : S npages + allocs h = frees h -> ~ pool_empty h.
Proof using . unfold pool_empty. lia. Qed.

Lemma pool_empty_iff npages h :
  npages + allocs h = frees h -> (npages = 0 <-> pool_empty h).
Proof using . unfold pool_empty. lia. Qed.
