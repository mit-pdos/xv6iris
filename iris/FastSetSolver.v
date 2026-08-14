(* ====================================================================== *)
(* FastSetSolver.v                                                         *)
(*                                                                         *)
(* A drop-in replacement for stdpp's [set_solver] whose cost does not       *)
(* depend on the size of the proof context.                                 *)
(*                                                                         *)
(* THE PROBLEM.  stdpp's [set_solver] (stdpp/sets.v) is                     *)
(*                                                                         *)
(*     try fast_done; intros; setoid_subst; set_unfold;                     *)
(*     intros; setoid_subst; try (apply dec_stable); naive_solver eauto     *)
(*                                                                         *)
(* and three of those steps sweep the WHOLE local context no matter what    *)
(* the goal says:                                                           *)
(*                                                                         *)
(*   - [setoid_subst]              scans and rewrites in every hypothesis;  *)
(*   - [set_unfold]'s [csimpl in *] runs [simpl] over every hypothesis;     *)
(*   - [naive_solver]'s [unfold iff, not in *] and its [simplify_eq/=]      *)
(*                                do it twice more, inside a [repeat] loop. *)
(*                                                                         *)
(* Measured with [time] on a synthetic whole-function context (80           *)
(* hypotheses stating register facts over depth-20 insert towers, i.e. the  *)
(* shape of a capstone proof) against the goal [a in X -> a in X u Y]:      *)
(*                                                                         *)
(*     setoid_subst          5.5 s + 1.3 s                                  *)
(*     csimpl in *           9.5 s                                          *)
(*     naive_solver          3.0 s                                          *)
(*     set_unfold proper     0.5 s   <-- the only step that reasons         *)
(*                          -------       about sets at all                 *)
(*                          19.9 s                                          *)
(*                                                                          *)
(* So ~97 % of the time normalises hypotheses that contain no sets, and it  *)
(* grows quadratically-to-cubically in the context: at 160 such hypotheses  *)
(* [csimpl in *] alone takes 76 s and the whole call takes 105 s.  That is  *)
(* the "[set_solver] IS QUADRATIC IN THE PROOF CONTEXT" trap recorded in    *)
(* claude-notes/optimization.md, and the reason a dozen files in this tree  *)
(* carry hand-written blocks of set lemmas ([bmset_*], [wiset_*], [cr_*],   *)
(* [gset_disj_*], ...) proved at the top of the file where the context is   *)
(* empty.                                                                   *)
(*                                                                          *)
(* THE FIX.  Throw the irrelevant hypotheses away before solving.  A        *)
(* hypothesis can only bear on a set goal if it is connected to it through  *)
(* a shared local variable, so [set_shrink] (SetShrink.v) keeps the         *)
(* connected component of the goal in the "hypothesis mentions variable"    *)
(* graph -- plus every hypothesis that mentions a set operation at all, so  *)
(* that a context contradictory ABOUT SETS still refutes a goal it shares   *)
(* no variable with -- and clears the rest.  stdpp's own pipeline then runs *)
(* on what is left.                                                         *)
(*                                                                          *)
(* On the benchmark above: 19.9 s -> 0.10 s, and the cost becomes LINEAR    *)
(* in the context size (640 hypotheses: 0.10 s, where upstream needs 105 s  *)
(* at 160).  Solving power is unchanged -- see FastSetSolverTests.v, which  *)
(* runs every set-goal shape this tree discharges, or works around, under   *)
(* both tactics and gets the same answer on all of them.                    *)
(*                                                                          *)
(* ON A REAL SITE.  ProofSysDup.v:836 carries the workaround                *)
(* [ltac:(apply not_elem_of_empty)] with a comment saying [set_solver] there *)
(* cost 106 s.  Putting [ltac:(set_solver)] back: 105.2 s with upstream,     *)
(* 0.73 s with this (0.49 s filtering + 0.23 s solving) -- 144x.            *)
(*                                                                          *)
(* HOW COMPLETENESS WAS ESTABLISHED.  Not by the clean build below -- with   *)
(* the fallback in place [set_solver] cannot fail, so a green tree would     *)
(* prove nothing.  The real check was to recompile the WHOLE stdpp 1.12.0    *)
(* library against this override with [set_solver := set_solver_fast], i.e.  *)
(* with the fallback DELETED, so that any hypothesis this filter wrongly     *)
(* drops surfaces as a build error.  Result: all 55 files build clean and    *)
(* all 23 of stdpp's own test files produce output BYTE-IDENTICAL to         *)
(* baseline.  The filtered path alone therefore discharges all 373           *)
(* [set_solver] call sites in stdpp.                                        *)
(*                                                                          *)
(* That exercise is also what found three of this file's four subtleties --  *)
(* the [Control.enter] in SetShrink.v, the [False] hypothesis, and [@eq] in  *)
(* [logic_ops] -- each of which the fallback would have silently absorbed as *)
(* a slow path.  If you change the filter, re-run it that way; a green tree  *)
(* is not evidence.                                                         *)
(*                                                                          *)
(* WHEN THE FILTER IS WRONG.  [set_solver] tries the filtered pipeline and  *)
(* falls back to the unfiltered upstream one, so nothing that used to be    *)
(* provable stops being provable.  The fallback costs what upstream always  *)
(* cost, so a proof that hits it is worth looking at; [set_solver_fast]     *)
(* and [set_solver_slow] name the two halves if you want to know which one  *)
(* is running.                                                              *)
(* ====================================================================== *)

(* [Import], NOT [Export].  This file is re-exported from RiscvModelBytes.v to
   the whole tree, and exporting [stdpp.sets] from there changes which [Forall2_
   length] (and friends) are in scope for every importer: stdpp's takes the
   predicate as an EXPLICIT argument where Stdlib's leaves it implicit, so
   [pose proof (Forall2_length Hr)] in VirtioModel.v stopped elaborating.  The
   tactic notations below resolve their bodies at definition time, so importers
   need nothing from [sets] to call [set_solver]. *)
From stdpp Require Import sets.
Require Export SetShrink.

(* ------------------------------------------------------------------ *)
(** ** The replacement tactic *)

(** The upstream tactic, kept reachable under a name of its own: a proof that
    genuinely needs a hypothesis the filter dropped can still say
    [set_solver_slow]. *)
Tactic Notation "set_solver_slow" "by" tactic3(tac) :=
  try fast_done;
  intros; setoid_subst;
  set_unfold;
  intros; setoid_subst;
  try match goal with |- _ ∈ _ => apply dec_stable end;
  naive_solver tac.
Tactic Notation "set_solver_slow" := set_solver_slow by eauto.

(** The fast path: shrink, then run the upstream pipeline on what is left. *)
Tactic Notation "set_solver_fast" "by" tactic3(tac) :=
  try fast_done;
  intros;
  set_shrink;
  setoid_subst;
  set_unfold;
  intros; setoid_subst;
  try match goal with |- _ ∈ _ => apply dec_stable end;
  naive_solver tac.
Tactic Notation "set_solver_fast" := set_solver_fast by eauto.

(** The drop-in.  Shadows stdpp's notation for every importer of this file. *)
Tactic Notation "set_solver" "by" tactic3(tac) :=
  first [ set_solver_fast by tac | set_solver_slow by tac ].
Tactic Notation "set_solver" := set_solver by eauto.
Tactic Notation "set_solver" "-" hyp_list(Hs) "by" tactic3(tac) :=
  clear Hs; set_solver by tac.
Tactic Notation "set_solver" "+" hyp_list(Hs) "by" tactic3(tac) :=
  clear -Hs; set_solver by tac.
Tactic Notation "set_solver" "-" hyp_list(Hs) := clear Hs; set_solver.
Tactic Notation "set_solver" "+" hyp_list(Hs) := clear -Hs; set_solver.
