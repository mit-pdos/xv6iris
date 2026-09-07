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
(* COMPLETE with respect to zify's extension classes, which is why the     *)
(* vocabulary below is deliberately generous and why the fallback exists.  *)
(* (This tree registers no zify instances of its own, and neither does     *)
(* stdpp: [bitvector.tactics] replaces only [zify_post_hook].)             *)
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
(*                                                                        *)
(* THE FILTER RUNS ON EVERY CALL, AND WHAT PAYS FOR THAT IS §"COST".       *)
(* An earlier version ran the filter only for a call that had already      *)
(* proved itself slow, behind a [timeout 1] gate.  That gate is gone.  It  *)
(* made WHICH ARM proved a given goal a function of wall-clock time, so    *)
(* the same source could build here and fail there and a timing wobble     *)
(* could move a proof between arms with no source change to explain it --  *)
(* and it did not even pay: it existed to hide a filter costing ~60 ms a   *)
(* call, and measured against upstream over two cold full builds of        *)
(* iris/ (1533 files, per-file min of two) it was worth +0.06%.  Making    *)
(* the filter cost ~6 ms instead is worth -0.41%, and -0.48% against the   *)
(* gated version.  Read §"COST" before changing any of the data structures *)
(* that got it there.                                                      *)
(* ====================================================================== *)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Std List Array Ident Int Bool FSet.
From Stdlib Require Import ZArith Lia.
Require Export SetShrink.

(* ---------------------------------------------------------------------- *)
(** ** COST

    The filter is charged to all ~20k [lia] call sites in this tree, so its
    per-call cost is the whole design constraint.  Measured on ProofBmap.v
    (96 calls, mean context 190 hypotheses), the first version cost 60 ms a
    call against a filtered [lia] of 10 ms, and every millisecond of it was
    Ltac2 interpretation of one of three loops:

      - 18 ms  the skeleton walk, because recognising a head meant
               [List.exist Constr.equal] down a 78-element [constr list] AT
               EVERY NODE.  Now the vocabulary is three [FSet]s keyed by
               [constant]/[inductive]/[constructor] and a head costs one
               [Constr.Unsafe.kind] and one [FSet.mem].
      - 19 ms  [SetShrink.vars_of] over the type of every hypothesis KEPT, to
               build the live-variable set.  Gone: only the GOAL is scanned
               (it is small, and [vars_of] skips an evar's instance), and a
               hypothesis-to-hypothesis dependency -- rare, and the only
               other way a [clear] can be ill-formed -- is left to
               [SetShrink.clear_greedily], which bisects and keeps the halves
               that do go.  That is the same answer Coq's own [clear] check
               gives, obtained without traversing the context in Ltac2.
      - 14 ms  the [doomed] scan, [List.mem] over a keep-list and a
               live-list that had grown to every variable in the context.
               With the live set down to the goal's variables this is a scan
               over a handful of names.

      -  7 ms  [is_prop], one [Constr.type] retyping per non-arithmetic
               hypothesis -- load-bearing, so it could not go, but it could
               get cheaper: retyping the HEAD of an application and reading
               the sort off its arity settles the question for almost every
               hypothesis at a ninth of the price.  See [is_prop].

    That is 60 ms a call down to ~6, against a filtered [lia] of ~10.

    THE RULE THIS LEAVES BEHIND: never put a [constr:(...)] quotation, a
    [constr list] scan, or a [SetShrink.vars_of] on a path that runs once per
    hypothesis or once per node.  A quotation is re-elaborated at every
    evaluation, so [Constr.equal f constr:(@eq)] inside the walk was a
    pretyping call per node; every such term is now hoisted into the
    per-call [vocab] built once at the top of [lia_shrink]. *)

(** [head_of c] — the head of an application, [c] itself otherwise. *)
Ltac2 head_of (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => f
  | _ => c
  end.

(** A vocabulary is a set of global heads, split by what kind of global each
    one is because [FSet] is keyed by type.  Membership is then one
    [Constr.Unsafe.kind] and one lookup, independent of the vocabulary size. *)
Ltac2 Type vocab := {
  mutable vconst : constant FSet.t;
  mutable vind   : inductive FSet.t;
  mutable vctor  : constructor FSet.t;
}.

Ltac2 empty_vocab () : vocab :=
  { vconst := FSet.empty FSet.Tags.constant_tag;
    vind   := FSet.empty FSet.Tags.inductive_tag;
    vctor  := FSet.empty FSet.Tags.constructor_tag }.

(** Add the HEAD of a sample term to a vocabulary.

    A sample whose head is neither a constant, an inductive nor a constructor
    is a mistake in the list below rather than a term this filter could ever
    meet, so it is thrown rather than silently ignored -- a silently ignored
    entry is a hypothesis class dropped tree-wide, which the header explains
    is a hang. *)
Ltac2 vocab_add (v : vocab) (c : constr) : unit :=
  match Constr.Unsafe.kind (head_of c) with
  | Constr.Unsafe.Constant k _ => v.(vconst) := FSet.add k (v.(vconst))
  | Constr.Unsafe.Ind i _      => v.(vind)   := FSet.add i (v.(vind))
  | Constr.Unsafe.Constructor k _ => v.(vctor) := FSet.add k (v.(vctor))
  | _ => Control.throw
           (Tactic_failure (Some (Message.of_string
              "FastLia: vocabulary sample whose head is not a global")))
  end.

Ltac2 mk_vocab (cs : constr list) : vocab :=
  let v := empty_vocab () in List.iter (fun c => vocab_add v c) cs; v.

(** Is [c]'s own head in [v]?  [c] is expected to be a head already. *)
Ltac2 in_vocab (v : vocab) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant k _ => FSet.mem k (v.(vconst))
  | Constr.Unsafe.Ind i _      => FSet.mem i (v.(vind))
  | Constr.Unsafe.Constructor k _ => FSet.mem k (v.(vctor))
  | _ => false
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
    same reason. *)
Ltac2 logic_conn () : constr list :=
    [ constr:(~ True); constr:(True /\ True); constr:(True \/ True);
      constr:(True <-> True); constr:(exists _ : nat, True) ].

(** Everything the walk needs, elaborated ONCE per [lia] call.

    [heq], [hfalse] and [hprop] are here rather than written as [constr:(@eq)] /
    [constr:(Prop)] at their use sites because a [constr:] quotation is
    re-elaborated at every evaluation and those sites run once per node or
    once per hypothesis.  See §COST. *)
Ltac2 Type kit := {
  ops  : vocab;                 (* arithmetic heads *)
  conn : vocab;                 (* connectives to descend through *)
  nums : vocab;                 (* the types an equation may be at *)
  heq  : constr;                (* [@eq] *)
  hfalse : constr;              (* [False] *)
  hprop  : constr;              (* [Prop] *)
}.

Ltac2 mk_kit () : kit :=
  { ops  := mk_vocab (arith_ops ());
    conn := mk_vocab (logic_conn ());
    nums := mk_vocab (num_types ());
    heq  := constr:(@eq);
    hfalse := constr:(False);
    hprop  := constr:(Prop) }.

(** [eq_at_num k f args] — is this an equation at a numeric type?

    An equation is arithmetic by its TYPE argument rather than by its sides:
    [H : m = n] over [Z] is a fact [lia] uses though neither side mentions an
    operator. *)
Ltac2 eq_at_num (k : kit) (f : constr) (args : constr array) : bool :=
  match Bool.and (Constr.equal f (k.(heq))) (Int.ge (Array.length args) 1) with
  | true => in_vocab (k.(nums)) (Array.get args 0)
  | false => false
  end.

Ltac2 rec mentions_arith_aux (k : kit) (fuel : int) (c : constr) : bool :=
  match Int.le fuel 0 with
  | true => true            (* out of fuel: KEEP, never drop on ignorance *)
  | false =>
      let rec_ := mentions_arith_aux k (Int.sub fuel 1) in
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
          match in_vocab (k.(ops)) f with
          | true => true
          | false =>
              match eq_at_num k f args with
              | true => true
              | false =>
                  match in_vocab (k.(conn)) f with
                  | true => List.exist rec_ (Array.to_list args)
                  | false => false
                  end
              end
          end
      | _ => in_vocab (k.(ops)) c
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
(** [retype_is_prop] is the honest question, and the dear one: [Constr.type]
    over a whole hypothesis type is ~30 us, and it is asked of every
    non-arithmetic hypothesis.  [is_prop] below asks it of the HEAD instead
    wherever that settles the matter, which is ~9x cheaper (measured: 6.1 ms
    against 0.7 ms over a 203-hypothesis context). *)
Ltac2 retype_is_prop (k : kit) (ty : constr) : bool :=
  match Control.case (fun () => Constr.type ty) with
  | Val (s, _) => Constr.equal s (k.(hprop))
  | Err _ => false            (* cannot tell: keep *)
  end.

(** [codomain n t] — strip [n] leading [Prod]s off [t] and return what is
    under them, or [None] if [t] does not have that many.  What comes back is
    under [n] binders, so it is usable ONLY when it is closed -- which is why
    the caller looks at it only to ask whether it is a [Sort]. *)
Ltac2 rec codomain (n : int) (t : constr) : constr option :=
  match Int.le n 0 with
  | true => Some t
  | false =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.Cast t _ _ => codomain n t
      | Constr.Unsafe.Prod _ body => codomain (Int.sub n 1) body
      | _ => None
      end
  end.

(** [is_prop k ty] — is [ty] a [Prop]?

    FALSE MUST MEAN "NOT A PROP", NEVER "DID NOT WORK OUT": a false positive
    clears a non-Prop, which is the silent evar corruption [keeps_for_lia]
    exists to prevent.  A false NEGATIVE only keeps a hypothesis, so every
    inconclusive path here falls back to the retyping.

    The shortcut: if [ty] is [f a1..an] and [f]'s type is [forall x1..xn, s]
    with [s] a SORT, then [s] is closed and no substitution can change it, so
    [ty]'s sort is [s] exactly.  Anything else -- too few [Prod]s (a partial
    application, whose sort is a [Type] anyway), a codomain that is not a
    sort, a head that will not retype -- goes to [retype_is_prop]. *)
Ltac2 is_prop (k : kit) (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App f args =>
      match Control.case (fun () => Constr.type f) with
      | Val (tf, _) =>
          match codomain (Array.length args) tf with
          | Some s =>
              match Constr.Unsafe.kind s with
              | Constr.Unsafe.Sort _ => Constr.equal s (k.(hprop))
              | _ => retype_is_prop k ty
              end
          | None => retype_is_prop k ty
          end
      | Err _ => retype_is_prop k ty
      end
  | _ => retype_is_prop k ty   (* atomic: the retyping is cheap anyway *)
  end.

Ltac2 keeps_for_lia (k : kit) (ty : constr) : bool :=
  match Constr.equal ty (k.(hfalse)) with
  | true => true
  | false =>
      match mentions_arith_aux k 12 ty with
      | true => true
      | false => Bool.neg (is_prop k ty)
      end
  end.

(** [lia_shrink ()] — clear every hypothesis [zify] could not read.

    Unlike [set_shrink] this needs no relevance closure: the criterion is a
    property of the hypothesis alone, so there is nothing to iterate.

    WHAT MAKES THE [clear] WELL-FORMED.  A dropped hypothesis must be named by
    nothing that stays.  Only the GOAL is scanned for that here; a dependency
    from a surviving HYPOTHESIS onto a dropped one -- which needs a
    [Prop]-typed hypothesis to appear in another's type or body, so it is rare
    -- is not looked for, and [SetShrink.clear_greedily] catches it instead by
    bisecting on the failure Coq raises and keeping the halves that do go.
    Scanning every kept type in Ltac2 to predict that answer cost more than
    the whole rest of the filter; see §COST. *)
Ltac2 lia_shrink () : unit :=
  let hyps := Control.hyps () in
  match Int.le (List.length hyps) 2 with
  | true => ()
  | false =>
      let k := mk_kit () in
      let doomed :=
        List.filter_out (fun (_, _, ty) => keeps_for_lia k ty) hyps in
      match doomed with
      | [] => ()          (* nothing to drop: do not even look at the goal *)
      | _ :: _ =>
          let live := { contents := [] } in
          SetShrink.vars_of (Control.goal ()) live;
          let names :=
            List.filter_out
              (fun (id, _, _) => List.mem Ident.equal id (live.(contents)))
              doomed in
          Control.once
            (fun () =>
               SetShrink.clear_greedily (List.map (fun (id,_,_) => id) names))
      end
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

(** THE SECOND ARM IS LOAD-BEARING.  If the filter drops something [zify] could
    have read, the first arm fails (or, per the header, hangs); the unfiltered
    arm is what keeps this override from turning a provable goal into a failing
    one.  Do not drop it to save a retry.

    THERE IS NO TIMEOUT HERE, AND THERE MUST NOT BE.  The version this replaced
    ran [first [ timeout 1 lia | lia_fast | lia_slow ]] so that a call upstream
    closes in milliseconds never paid for the analysis.  Two things are wrong
    with that.

    It is a WALL-CLOCK reading, so which arm proves a given goal depends on how
    loaded the machine is: the same source can build here and fail there, and a
    timing wobble moves a proof between arms with nothing in the source to
    explain it.  The margin is not comfortable either -- five interleaved
    compiles of ProofBmap.v under the gate ranged over 54.3-59.5 s, so calls
    sitting near one second cross the gate or not depending on the run.

    AND IT DID NOT PAY.  Over two cold full builds of iris/ (1533 files,
    per-file min of the two, all arms sequential on one machine): upstream
    9596 s, gated 9602 s (+0.06%), this ungated filter 9556 s (-0.41%).  The
    gate loses on the arm-count alone -- a [lia] the tree EXPECTS to fail (a
    [try lia], a [first [ lia | ... ]]) runs the decision procedure three times
    under the gate and twice here.  Tree-wide it fired 1568 times, and 1565 of
    those were such a failing call: it rescued three.

    So the gate was hiding a ~60 ms filter, not buying anything.  The filter now
    costs ~6 ms.  If it ever gets expensive again, make it cheap -- do not
    reintroduce a clock. *)

(** The drop-ins.  Shadow Lia's notations for every importer of this file. *)
Tactic Notation "lia" := first [ lia_fast | lia_slow ].
Tactic Notation "nia" := first [ nia_fast | nia_slow ].
