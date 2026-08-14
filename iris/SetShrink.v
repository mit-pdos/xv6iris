(* ====================================================================== *)
(* SetShrink.v                                                             *)
(*                                                                         *)
(* The relevance filter behind this tree's [set_solver] override.  Read     *)
(* FastSetSolver.v first: it states the problem and the measurements; this  *)
(* file is only the analysis that decides which hypotheses to throw away.   *)
(*                                                                         *)
(* Deliberately imports NOTHING but Ltac2 and [stdpp.base], so it can sit   *)
(* at the very bottom of the tree.                                         *)
(* ====================================================================== *)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Std List Array Ident Int Bool Message.
From stdpp Require Import base.

(* ------------------------------------------------------------------ *)
(** ** Syntactic helpers *)

(** [mentions_any ids c] — does [c] contain a free occurrence of any of [ids]?

    Implemented with two kernel primitives instead of an Ltac traversal:
    [closenl] turns the named occurrences into de Bruijn indices [1..n], and
    [noccur_between] then answers in one pass over the term. *)
Ltac2 mentions_any (ids : ident list) (c : constr) : bool :=
  let n := List.length ids in
  match Int.equal n 0 with
  | true => false
  | false =>
      Bool.neg (Constr.Unsafe.noccur_between 1 n (Constr.Unsafe.closenl ids 1 c))
  end.

(** The set vocabulary.  A hypothesis mentioning any of these is kept whatever
    variables it talks about, so that a context which is contradictory *about
    sets* still refutes a goal it shares no variable with.  These are stdpp's
    set-theoretic classes; the list is closed and has not changed in years. *)
Ltac2 set_ops () : constr list :=
  [ constr:(@elem_of); constr:(@subseteq); constr:(@disjoint);
    constr:(@union); constr:(@intersection); constr:(@difference);
    constr:(@singleton); constr:(@empty); constr:(@equiv) ].

(** The logical connectives the skeleton walk is allowed to descend through.

    [@eq] MUST be here.  Under [LeibnizEquiv] a large fraction of set facts are
    stated as equations — [{[i]} ∪ default ∅ (f m) = ∅] — and without [eq] the
    walk sees head [eq], finds it in neither list, and returns [false] without
    ever looking at the union inside.  stdpp's [fin_maps.v:4258] is exactly that
    proof: goal [False], so variable-connectivity keeps nothing, and the set
    equation was the only hypothesis that could have saved it.

    Descending through [eq] does NOT re-open the cost it looks like it might.
    The worry was [rg (upd (upd m …) …) r = w], the shape a whole-function
    context is full of — but the walk descends ONE level into the equation and
    then meets [upd], which is in neither list, so it stops immediately.  The
    walk only ever follows the logical skeleton; it never enters a data term.
    Measured: no change on either the 80-hypothesis benchmark or stdpp. *)
Ltac2 logic_ops () : constr list :=
  [ constr:(not); constr:(and); constr:(or); constr:(iff); constr:(ex);
    constr:(@eq) ].

Ltac2 head_mem (ops : constr list) (c : constr) : bool :=
  List.exist (fun o => Constr.equal o c) ops.

(** [mentions_set ops conn fuel ty] — does [ty]'s LOGICAL SKELETON mention a set
    operation?  We walk binders and connectives only, never into data subterms,
    so the cost is a handful of node visits per hypothesis instead of a full
    traversal of its type.  (Ltac2's [Constr.Unsafe.iter] costs tens of
    microseconds per node, so a full traversal of an 80-hypothesis context was
    itself slower than the set reasoning it was protecting.) *)
Ltac2 rec mentions_set_aux (ops : constr list) (conn : constr list)
                           (fuel : int) (c : constr) : bool :=
  match Int.le fuel 0 with
  | true => false
  | false =>
      let rec_ := mentions_set_aux ops conn (Int.sub fuel 1) in
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.Cast c _ _ => rec_ c
      | Constr.Unsafe.Prod b body => Bool.or (rec_ (Constr.Binder.type b)) (rec_ body)
      | Constr.Unsafe.Lambda _ body => rec_ body
      | Constr.Unsafe.LetIn _ _ body => rec_ body
      | Constr.Unsafe.App f args =>
          match head_mem ops f with
          | true => true
          | false =>
              match head_mem conn f with
              | true => List.exist rec_ (Array.to_list args)
              | false => false
              end
          end
      | _ => head_mem ops c
      end
  end.

(** A hypothesis of type [False] is the filter's one structural blind spot: it
    shares no variable with anything and mentions no set operation, so nothing
    can make it relevant — yet it proves the goal outright.  Keeping it is free
    (there is at most one) and it is exactly what the ex-falso proofs in
    stdpp's own library need.  Found by recompiling stdpp against a
    no-fallback build of this override; those two proofs are the ONLY
    regressions in stdpp's 373 [set_solver] call sites. *)
Ltac2 is_false (c : constr) : bool := Constr.equal c constr:(False).

Ltac2 mentions_set (ops : constr list) (conn : constr list) (c : constr) : bool :=
  Bool.or (is_false c) (mentions_set_aux ops conn 12 c).

(** [vars_of c acc] — the local variables occurring in [c], added to [acc].

    AN EVAR'S INSTANCE IS SKIPPED, and that one line is what makes the tactic
    work in ARGUMENT position.  A goal reached through [ltac:(set_solver)]
    inside a term is an evar, and an evar carries an instance listing EVERY
    variable in scope; walking into it makes the goal "mention" the whole
    context, the relevance closure keeps everything, and the filter silently
    degrades to upstream.  That is not hypothetical — it is why
    [ProofSysDup.v:836]'s [ltac:(set_solver)] measured 102 s, indistinguishable
    from the 106 s that made someone write the workaround.  Skipping the
    instance takes the same call to 0.018 s.  The instance is anyway no
    evidence of relevance: it is "everything in scope", the same for every
    evar. *)
Ltac2 rec vars_of (c : constr) (acc : ident list ref) : unit :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id =>
      match List.mem Ident.equal id (acc.(contents)) with
      | true => ()
      | false => acc.(contents) := id :: acc.(contents)
      end
  | Constr.Unsafe.Evar _ _ => ()
  | _ => Constr.Unsafe.iter (fun c' => vars_of c' acc) c
  end.

(** The variables of a term, together with the variables of the types of those
    variables.  Including the types keeps the filter from clearing a type
    parameter that a surviving hypothesis still refers to. *)
Ltac2 seed_vars (c : constr) : ident list :=
  let acc := { contents := [] } in
  vars_of c acc;
  let direct := acc.(contents) in
  List.iter
    (fun (id, _, ty) =>
       match List.mem Ident.equal id direct with
       | true => vars_of ty acc
       | false => ()
       end)
    (Control.hyps ());
  acc.(contents).

(* ------------------------------------------------------------------ *)
(** ** The relevance filter *)

(** How many rounds of transitive closure the filter performs.  One round
    keeps every hypothesis sharing a variable with the goal; each further
    round also keeps the hypotheses sharing a variable with those.

    Rounds cost almost nothing, but in a proof whose context is one long chain
    of register facts (each mentioning the previous map) a high round count
    re-admits the whole chain, which is precisely what we are trying to
    avoid.  Two rounds is the default: it covers the usual
    [H1 : X ⊆ Y, H2 : b ∈ X, H3 : a = b ⊢ a ∈ Y] indirection without
    following long chains. *)
Ltac2 mutable set_solver_rounds () : int := 2.

(** One round: given the currently-relevant variable set, return the enlarged
    variable set and the list of hypotheses that are relevant. *)
Ltac2 relevant_step (tagged : (bool * (ident * constr option * constr)) list)
                    (vars : ident list) : ident list * ident list :=
  let kept := { contents := [] } in
  let acc := { contents := vars } in
  List.iter
    (fun (is_set, (id, body, ty)) =>
       let touches :=
         Bool.or is_set
           (Bool.or (mentions_any vars ty)
                    (match body with
                     | Some b => mentions_any vars b
                     | None => false
                     end)) in
       match touches with
       | true =>
           kept.(contents) := id :: kept.(contents);
           vars_of ty acc;
           match body with Some b => vars_of b acc | None => () end
       | false => ()
       end)
    tagged;
  (acc.(contents), kept.(contents)).

(** Contexts at or below this size are left alone: upstream's sweeps are cheap
    there, and the analysis is not free (~9 ms per call, measured over 62 small
    goals).  Measured at both 2 and 8 the difference is inside the noise, so it
    is set low — a five-hypothesis context can still be lethal if one of those
    hypotheses carries a 4096-conjunct big-op. *)
Ltac2 mutable set_shrink_min () : int := 2.

(** [clear_greedily names] — clear as many of [names] as will go.

    [Std.clear] is ALL-OR-NOTHING: one name Coq refuses (something outside the
    analysis still depends on it — a section variable, a hypothesis mentioned
    only in another's body, a let-bound name) fails the whole call, and then
    NOTHING is cleared and the filter silently degrades to upstream.  That is
    not a hypothetical: it is what made the filter a no-op at
    [ProofSysDup.v:836], where the analysis ran in 0.05 s and the solve still
    took 105 s.  So on failure we bisect and keep the halves that do go.  The
    common case is one successful call; the recursion only costs anything when
    something is genuinely unclearable. *)
Ltac2 rec clear_greedily (names : ident list) : unit :=
  match names with
  | [] => ()
  | _ :: _ =>
      Control.plus
        (fun () => Std.clear names)
        (fun _ =>
           match names with
           | [] => ()
           | [_] => ()          (* this single one is unclearable; skip it *)
           | _ =>
               let n := List.length names in
               let k := Int.div n 2 in
               clear_greedily (List.firstn k names);
               clear_greedily (List.skipn k names)
           end)
  end.

(** [set_shrink ()] clears every hypothesis that cannot reach the goal.

    A hypothesis is dropped only if (a) it is not relevant and (b) no
    surviving hypothesis and not the goal mentions its name, so the resulting
    [clear] is always well-formed.  If it nevertheless fails, we leave the
    context alone rather than fail the whole tactic. *)
Ltac2 set_shrink () : unit :=
  let hyps := Control.hyps () in
  match Int.le (List.length hyps) (set_shrink_min ()) with
  | true => ()   (* nothing to gain; skip the analysis entirely *)
  | false =>
      let goal := Control.goal () in
      let ops := set_ops () in
      let conn := logic_ops () in
      (* [mentions_set] does not depend on [vars], so tag each hypothesis once
         here rather than re-traversing every type on every round. *)
      let tagged :=
        List.map (fun (id, body, ty) => (mentions_set ops conn ty, (id, body, ty)))
                 hyps in
      let rec loop n vars kept :=
        match Int.le n 0 with
        | true => (vars, kept)
        | false =>
            let (vars', kept') := relevant_step tagged vars in
            match Int.equal (List.length vars) (List.length vars') with
            | true => (vars', kept')             (* fixpoint reached *)
            | false => loop (Int.sub n 1) vars' kept'
            end
        end in
      let (vars, kept) := loop (set_solver_rounds ()) (seed_vars goal) [] in
      (* [vars] is the live variable set: it was seeded from the goal and grown
         with the variables of every surviving hypothesis, so a name absent
         from it is referred to by nothing that stays.  That makes the drop
         test a single O(1) membership check per hypothesis rather than a
         quadratic scan. *)
      let doomed :=
        List.filter_out
          (fun (id, _, _) =>
             Bool.or (List.mem Ident.equal id kept)
                     (List.mem Ident.equal id vars))
          hyps in
      let names := List.map (fun (id, _, _) => id) doomed in
      (* [once] so a failure further down the tactic chain cannot backtrack
         into the "did not clear" branch and silently re-run on the full
         context — the fallback to the upstream tactic is spelled out in
         [set_solver] instead, where it is visible. *)
      Control.once (fun () => clear_greedily names)
  end.

(** Ltac1 entry point.

    [Control.enter] is NOT optional.  [Control.hyps]/[Control.goal] demand
    exactly one focused goal, and an Ltac2 quotation spliced into an Ltac1 [;]
    chain is handed whatever goals are live — zero when an earlier step closed
    the goal, several under [all:] or after a [destruct].  Without [enter] those
    raise [Init.Not_focussed], which is THROWN rather than failed, so the
    [first [ set_solver_fast | set_solver_slow ]] fallback cannot catch it and
    the whole proof dies.  Found by recompiling stdpp against this override:
    [stdpp/sets.v:421] and [:672] both hit it. *)
Ltac set_shrink := ltac2:(Control.enter set_shrink).

(** [From Ltac2 Require Import Ltac2] switches the default proof mode; this file
    is re-exported to the whole tree, so put it back. *)
Set Default Proof Mode "Classic".
