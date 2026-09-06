(* ====================================================================== *)
(* FastLia.v                                                              *)
(*                                                                        *)
(* A drop-in replacement for [lia] whose cost does not depend on the size  *)
(* of the proof context.                                                   *)
(*                                                                        *)
(* THE PROBLEM.  [lia] reifies the hypotheses it is handed: [Zify.zify]    *)
(* walks the whole local context, and [xlia]'s atom scan is over whatever  *)
(* survives that.  A whole-function proof in this tree carries ~180        *)
(* hypotheses, ~45 of them arithmetic, and the goal is usually one or two  *)
(* equations away from trivial -- so nearly all of the work is reifying    *)
(* facts that cannot bear on the goal.  It is the same shape as the        *)
(* [set_solver] problem FastSetSolver.v fixes, one tactic over.            *)
(*                                                                        *)
(* The tree already carries 187 hand-written [clear - H..; lia] workarounds *)
(* across 51 files, plus per-file [Tactic Notation "zlia" hyp_list(Hs)]    *)
(* keep-lists.  Every one of them is this fix, applied by hand at one site. *)
(*                                                                        *)
(* AND [clear -] CANNOT REACH THE WORST CASE.  A [ltac:(lia)] spliced into *)
(* ARGUMENT POSITION has an evar goal whose instance names every variable  *)
(* in scope, so there is nothing for a hand-written [clear -] to keep --   *)
(* the documented advice is "you cannot; hoist it to a named assert".      *)
(* [SetShrink.vars_of] SKIPS AN EVAR'S INSTANCE (the line that made the    *)
(* set_solver override work in the same position), so the filter below     *)
(* works there, and the hoist stops being obligatory.                      *)
(*                                                                        *)
(* THE FIX.  Before solving, clear every hypothesis [lia] could not have   *)
(* read anyway.  [lia] sees a hypothesis only through [zify], which        *)
(* translates arithmetic propositions over Z/nat/N/positive/bool and       *)
(* nothing else, so dropping a hypothesis whose type mentions no such      *)
(* operation cannot lose provability -- this filter is sound by            *)
(* construction rather than by relevance heuristics.  Only [Prop]s are     *)
(* dropped: clearing a non-Prop restricts every undefined evar's context   *)
(* and breaks sibling goals silently -- see [keeps_for_lia] below.  What   *)
(* the filter is not is                                                    *)
(* COMPLETE with respect to zify's extension classes (this tree loads      *)
(* [bitvector.tactics]'s hook), which is why the vocabulary below is       *)
(* deliberately generous and why the fallback exists.                      *)
(*                                                                        *)
(* THE FALLBACK IS NOT A SAFETY NET, AND A GREEN TREE PROVES NOTHING.      *)
(* [lia] is [first [ lia_fast | lia_slow ]], so a filter that drops        *)
(* something needed SHOULD cost only a retry -- but a hypothesis-starved   *)
(* [lia] does not reliably fail fast.  Starved of the one hypothesis that  *)
(* refuted it, the call at ProofCreateMkdir.v:1750 ran past 400s without   *)
(* answering, where unfiltered it takes a moment.  A gap in the vocabulary *)
(* below is therefore a HANG, not a slowdown, and [first] cannot catch it. *)
(* So: check the filter with the fallback DELETED (FastLiaTests.v proves    *)
(* one inequality per numeric type that way), and never hand-write a       *)
(* constant name into the vocabulary -- see [arith_ops].                   *)
(* ====================================================================== *)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Std List Array Ident Int Bool.
From Stdlib Require Import ZArith Lia.
Require Export SetShrink.

(** [head_of c] — the head of an application, [c] itself otherwise. *)
Ltac2 head_of (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => f
  | _ => c
  end.

(** The types whose (in)equations [zify] can read.  [bool] is here because
    zify translates it through [Z.b2z], so [H : Nat.eqb a b = true] is a fact
    [lia] can use and must not be dropped. *)
Ltac2 num_types () : constr list :=
  [ constr:(Z); constr:(nat); constr:(N); constr:(positive); constr:(bool) ].

(** The arithmetic vocabulary: a hypothesis whose logical skeleton mentions any
    of these heads is KEPT.  Generous on purpose -- a false positive costs one
    reified hypothesis, a false negative costs a fallback to upstream.

    EVERY ENTRY IS THE HEAD OF A SAMPLE APPLICATION, NEVER A CONSTANT NAME.  The
    two are not the same term: [(0 <= 0)%nat] elaborates to [Peano.le], and
    [Nat.le] is a different constant that no goal in this tree ever carries.  A
    list naming [Nat.le] therefore drops EVERY nat inequality -- including a
    literal [1 <= 0] -- while looking entirely correct, and the fallback hides
    it, because a hypothesis-starved [lia] does not fail fast: at
    ProofCreateMkdir.v:1750 it ran for over 400s without answering.  A wrong
    entry here is a HANG, not a slowdown, so do not hand-write constant names.
    FastLiaTests.v pins one inequality per numeric type for this reason. *)
Ltac2 arith_ops () : constr list :=
  List.map head_of
    [ constr:((0 <= 0)%nat); constr:((0 < 0)%nat); constr:((0 >= 0)%nat);
      constr:((0 > 0)%nat); constr:((0 + 0)%nat); constr:((0 - 0)%nat);
      constr:((0 * 0)%nat); constr:(Nat.div 0 0); constr:(Nat.modulo 0 0);
      constr:(Nat.pow 0 0); constr:(Nat.max 0 0); constr:(Nat.min 0 0);
      constr:(Nat.ltb 0 0); constr:(Nat.leb 0 0); constr:(Nat.eqb 0 0);
      constr:(S 0); constr:(Nat.pred 0); constr:(Nat.double 0);
      constr:((0 <= 0)%Z); constr:((0 < 0)%Z); constr:((0 >= 0)%Z);
      constr:((0 > 0)%Z); constr:((0 + 0)%Z); constr:((0 - 0)%Z);
      constr:((0 * 0)%Z); constr:((- 0)%Z); constr:((0 / 0)%Z);
      constr:((0 mod 0)%Z); constr:((0 ^ 0)%Z); constr:(Z.succ 0);
      constr:(Z.pred 0); constr:(Z.max 0 0); constr:(Z.min 0 0);
      constr:(Z.abs 0); constr:(Z.of_nat 0); constr:(Z.to_nat 0);
      constr:(Z.of_N 0); constr:(Z.to_N 0); constr:(Z.b2z true);
      constr:(Z.ltb 0 0); constr:(Z.leb 0 0); constr:(Z.eqb 0 0);
      constr:(Z.quot 0 0); constr:(Z.rem 0 0); constr:(Z.div2 0);
      constr:(N.le 0 0); constr:(N.lt 0 0); constr:(N.ge 0 0);
      constr:(N.gt 0 0); constr:(N.add 0 0); constr:(N.sub 0 0);
      constr:(N.mul 0 0); constr:(N.div 0 0); constr:(N.modulo 0 0);
      constr:(N.max 0 0); constr:(N.min 0 0); constr:(N.succ 0);
      constr:(N.pred 0); constr:(N.of_nat 0); constr:(N.to_nat 0);
      constr:(N.ltb 0 0); constr:(N.leb 0 0); constr:(N.eqb 0 0);
      constr:(Pos.le 1 1); constr:(Pos.lt 1 1); constr:(Pos.ge 1 1);
      constr:(Pos.gt 1 1); constr:(Pos.add 1 1); constr:(Pos.sub 1 1);
      constr:(Pos.mul 1 1); constr:(Pos.max 1 1); constr:(Pos.min 1 1);
      constr:(Pos.succ 1); constr:(Pos.pred 1); constr:(Pos.to_nat 1);
      constr:(Pos.of_nat 0); constr:(Pos.of_succ_nat 0) ].

(** The connectives the skeleton walk descends through.  Sample-derived for the
    same reason.  [@eq] is here as in SetShrink's list, and additionally because
    an equation is arithmetic by its TYPE argument rather than by its sides:
    [H : m = n] over [Z] is a fact [lia] uses though neither side mentions an
    operator. *)
Ltac2 logic_conn () : constr list :=
  List.map head_of
    [ constr:(~ True); constr:(True /\ True); constr:(True \/ True);
      constr:(True <-> True); constr:(exists _ : nat, True) ].

Ltac2 mem_c (ops : constr list) (c : constr) : bool :=
  List.exist (fun o => Constr.equal o c) ops.

(** [eq_at_num nums f args] — is this an equation at a numeric type? *)
Ltac2 eq_at_num (nums : constr list) (f : constr) (args : constr array) : bool :=
  match Bool.and (Constr.equal f constr:(@eq)) (Int.ge (Array.length args) 1) with
  | true => mem_c nums (Array.get args 0)
  | false => false
  end.

(** The three vocabularies are passed in rather than rebuilt per node: each is a
    list of [constr]s that would otherwise be reconstructed once for every
    subterm of every hypothesis. *)
Ltac2 rec mentions_arith_aux (ops : constr list) (conn : constr list)
                             (nums : constr list) (fuel : int) (c : constr) : bool :=
  match Int.le fuel 0 with
  | true => true            (* out of fuel: KEEP, never drop on ignorance *)
  | false =>
      let rec_ := mentions_arith_aux ops conn nums (Int.sub fuel 1) in
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.Cast c _ _ => rec_ c
      | Constr.Unsafe.Prod b body =>
          (* nested, not [Bool.or]: see [keeps_for_lia] on eager arguments *)
          match rec_ (Constr.Binder.type b) with
          | true => true
          | false => rec_ body
          end
      | Constr.Unsafe.Lambda _ body => rec_ body
      | Constr.Unsafe.LetIn _ _ body => rec_ body
      | Constr.Unsafe.App f args =>
          match mem_c ops f with
          | true => true
          | false =>
              match eq_at_num nums f args with
              | true => true
              | false =>
                  match mem_c conn f with
                  | true => List.exist rec_ (Array.to_list args)
                  | false => false
                  end
              end
          end
      | _ => mem_c ops c
      end
  end.

(** ONLY A [Prop] IS EVER DROPPED, AND THAT IS NOT AN OPTIMISATION -- IT IS
    WHAT KEEPS THE FILTER FROM CORRUPTING A SIBLING GOAL.

    A hypothesis whose type is not a [Prop] is data: a section variable, a
    typeclass instance ([XI : CurCtx], [GEN : GenId], [riscvGS0]), a ghost name,
    an index.  [lia] cannot read one -- but clearing one RESTRICTS the context of
    every undefined evar that mentions it, and Coq does that silently rather than
    refusing.  The sibling goal then fails to unify long after this tactic
    reported success, naming neither: [rewrite (_ : 2%nat = (1 + 1)%nat); [| lia]]
    at ProofInitlog.v:2293 dies as "Unable to unify ?b with bslots (1 + 1)",
    which reads as a broken rewrite and is a cleared [CurCtx] instance.

    (The tree already knew half of this: the hand-written keep-lists all carry
    [clear - XI Hs] for the same instance, and the note explaining why says the
    error is "a scoping accident". This is that accident's other face.)

    So: keep everything that is not a Prop, and among Props keep the arithmetic
    ones.  Dropping a non-arithmetic Prop is sound -- [zify] cannot read it --
    and a Prop appears in no evar's context, only in its own hypothesis slot.

    A hypothesis of type [False] proves any goal and shares no variable and no
    operator with anything, so keeping it is free; SetShrink records the same
    blind spot.

    Ltac2's [Bool.or] is a FUNCTION, so both its arguments are evaluated: the
    tests are nested as [match]es instead, and [is_prop] -- a retyping call, the
    dearest of the three -- runs only on a hypothesis already headed for the
    doomed list. *)
Ltac2 is_prop (ty : constr) : bool :=
  match Control.case (fun () => Constr.type ty) with
  | Val (s, _) => Constr.equal s constr:(Prop)
  | Err _ => false            (* cannot tell: keep *)
  end.

Ltac2 keeps_for_lia (ops : constr list) (conn : constr list) (nums : constr list)
                    (ty : constr) : bool :=
  match Constr.equal ty constr:(False) with
  | true => true
  | false =>
      match mentions_arith_aux ops conn nums 12 ty with
      | true => true
      | false => Bool.neg (is_prop ty)
      end
  end.

(** [lia_shrink ()] — clear every hypothesis [zify] could not read.

    Unlike [set_shrink] this needs no relevance closure: the criterion is a
    property of the hypothesis alone, so there is nothing to iterate.  What it
    does still need is the live-variable set, so that the [clear] is
    well-formed -- a dropped hypothesis must not be named by the goal, by a
    surviving hypothesis's type, or by such a hypothesis's body. *)
Ltac2 lia_shrink () : unit :=
  let hyps := Control.hyps () in
  match Int.le (List.length hyps) 2 with
  | true => ()
  | false =>
      let ops := arith_ops () in
      let conn := logic_conn () in
      let nums := num_types () in
      let keep := { contents := [] } in
      let live := { contents := [] } in
      SetShrink.vars_of (Control.goal ()) live;
      List.iter
        (fun (id, body, ty) =>
           match keeps_for_lia ops conn nums ty with
           | true =>
               keep.(contents) := id :: keep.(contents);
               SetShrink.vars_of ty live;
               match body with
               | Some b => SetShrink.vars_of b live
               | None => ()
               end
           | false => ()
           end)
        hyps;
      let doomed :=
        List.filter_out
          (fun (id, _, _) =>
             match List.mem Ident.equal id (keep.(contents)) with
             | true => true
             | false => List.mem Ident.equal id (live.(contents))
             end)
          hyps in
      Control.once
        (fun () => SetShrink.clear_greedily (List.map (fun (id,_,_) => id) doomed))
  end.

(** [Control.enter] for the reason SetShrink records: [Control.hyps] demands
    exactly one focused goal, and [Init.Not_focussed] is THROWN rather than
    failed, so a [first [...]] fallback could not catch it. *)
Ltac lia_shrink := ltac2:(Control.enter lia_shrink).

Set Default Proof Mode "Classic".

(** The upstream tactics, kept reachable under names of their own. *)
Ltac lia_slow := Lia.lia.
Ltac nia_slow := Lia.nia.

(** The filtered arms.  No [assert]-isolation wrapper: the sibling-evar hazard
    it was written for is handled at the source by [keeps_for_lia] refusing to
    drop non-[Prop]s, and an extra beta-redex per site across ~20k sites is term
    size for nothing. *)
Ltac lia_fast := lia_shrink; Lia.lia.
Ltac nia_fast := lia_shrink; Lia.nia.

(** THE FILTER IS TRIED SECOND, NOT FIRST, AND THAT ORDER IS THE WHOLE DESIGN.

    Nearly every [lia] in this tree is already cheap; the ~20k call sites are
    dominated by one-hop goals that upstream closes in milliseconds.  The filter
    is not free -- it walks every hypothesis's type and then [clear]s -- so
    charging it to all of them to rescue the few hundred expensive ones is a
    LOSING trade: measured over a clean tree-wide build, filtering every call
    cost more than it saved (ΣCPU +0.7%, 100 files slower against 51 faster).

    So the unfiltered tactic runs first under a short timeout, and the filter
    runs only for a call that has already proved itself slow.  A cheap call
    never pays the analysis; an expensive one pays a bounded [lia_gate] second
    before the filter takes over.  Same filter, same tree, only the order
    changed: ΣCPU -1.6%, 82 files faster against 22 slower.

    The gate cannot go below a second -- [timeout] counts whole seconds -- so a
    call that trips it has already spent one before the filter starts.  That is
    priced in above.

    THE THIRD ARM IS LOAD-BEARING.  If the filter drops something [zify] could
    have read, the second arm fails (or, per the header, hangs); the unbounded
    unfiltered arm is what keeps this override from turning a provable goal into
    a failing one.  Do not drop it to save a retry.

    The gate is wall-clock, so which arm proves a given goal is not reproducible
    across machines.  That is sound here -- every arm is the same decision
    procedure and the result is a proof or a failure either way -- but it does
    mean a timing regression can move between builds. *)
Ltac lia_gate := timeout 1 Lia.lia.
Ltac nia_gate := timeout 1 Lia.nia.

(** The drop-ins.  Shadow Lia's notations for every importer of this file. *)
Tactic Notation "lia" := first [ lia_gate | lia_fast | lia_slow ].
Tactic Notation "nia" := first [ nia_gate | nia_fast | nia_slow ].
