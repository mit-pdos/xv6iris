/-
**The pipeline model's hooks, and the merge decider's owner** (Rocq
`PipesDiscDec.v`, 668 lines, pinned `1900b8a43`).  Pure.

## DU9 (classical decidability) — what is and is not here

Rocq's file writes constructive deciders for the pipeline model
(`stage_outs`, `sfx_runs`, `line_runs`, `line_blocksb`, `sfx_terms`,
`line_terms`, `line_termb`, the `Decision` instances `line_blocks_dec`,
`plalt_ok_dec`, `pipes_lm_ok_dec`) and the file `PipesDecE.v` more of them.
Their only consumer is the union's ledger taint counter (a `decide` on the
discipline) and `LmHooks`' decider field; DU9 replaces both by classical
decidability, and Lean's `LmHooks` has NO decider field.  So none of those
is ported, and `PipesDecE.v` is dropped whole.  What the union reaches that
is NOT a decider is kept:

* `picks`, `picks_spec`, the merge facts (`merge_all_cons_nil`,
  `merge_all_concat`, `merge_all_nil_inv`, `merge_all_of_nils`,
  `merge_all_2nil`) and the COMPUTABLE prefix test of a terminal block
  `ptermb`/`ptermb_spec` (spent by `mergeN_ptermb`): in `Xv6/PipesMerge.lean`;
* `pipes_hooks` and its `phk_*` lemmas: here.

`forallb_nil_iff` (a `forallb`/`Forall` bridge) is absorbed by `simp`
(`List.all_eq_true`, `List.isEmpty_iff`) in `ptermb_spec`.  The demos
(`fc0`, `fc1`, `demo_*`) are unreached and not ported.
-/
import Xv6.PipesDisc
import Xv6.LineModelLinks

namespace Xv6

open Pline' PLAlt

section pipesHooks
variable (fc : List (BitVec 8) → Option (List (BitVec 8))) (adm : Pline' → Bool)

theorem phk_free_term (a : PLAlt) (h : (!plterm a) = true) : plterm a = false := by
  simpa using h

theorem phk_pan_ok (s : Unit) (l : Pline') :
    (pipesLm fc adm).lmOk s l ((pipesLm fc adm).lmDec (plaltCode PLPanic)) :=
  Or.inl (Or.inl (plaltOf_code PLPanic))

theorem phk_exf_ok (s : Unit) (l : Pline') :
    (pipesLm fc adm).lmOk s l ((pipesLm fc adm).lmDec (plaltCode (PLRun (plExfb l)))) :=
  Or.inl (Or.inr (Or.inr (plaltOf_code _)))

theorem phk_noc_ok (s : Unit) (l : Pline') :
    (pipesLm fc adm).lmOk s l ((pipesLm fc adm).lmDec (plaltCode (PLRun []))) :=
  Or.inl (Or.inr (Or.inl (plaltOf_code (PLRun []))))

theorem phk_code_free (a : PLAlt) :
    (!plterm ((pipesLm fc adm).lmDec (plaltCode a))) = !plterm a := by
  show (!plterm (plaltOf (plaltCode a))) = _; rw [plaltOf_code]

theorem phk_code_panic (a : PLAlt) :
    (pipesLm fc adm).lmPanic ((pipesLm fc adm).lmDec (plaltCode a)) = plpanic a := by
  show plpanic (plaltOf (plaltCode a)) = _; rw [plaltOf_code]

theorem phk_code_cont (s : Unit) (l : Pline') (a : PLAlt) :
    (pipesLm fc adm).lmCont s l ((pipesLm fc adm).lmDec (plaltCode a)) = plcont a := by
  show plcont (plaltOf (plaltCode a)) = _; rw [plaltOf_code]

theorem phk_cont_prompt (s : Unit) (l : Pline') (a : PLAlt) (_ : (pipesLm fc adm).lmOk s l a)
    (hp : (pipesLm fc adm).lmPanic a = false) (ht : (pipesLm fc adm).lmTerm a = false) :
    ∃ u, (pipesLm fc adm).lmCont s l a = u ++ uPrompt := by
  cases a with
  | PLPanic => cases hp
  | PLRun b => exact ⟨b, rfl⟩
  | PLTerm _ => cases ht

theorem phk_cont_nonnil (s : Unit) (l : Pline') (a : PLAlt)
    (ha : (pipesLm fc adm).lmOk s l a ∨ a = (pipesLm fc adm).lmDec 0) :
    (pipesLm fc adm).lmCont s l a ≠ [] := by
  show plcont a ≠ []
  cases a with
  | PLPanic => simp [plcont, altPanic, wlLine]
  | PLRun b => simp [plcont, uPrompt]
  | PLTerm b =>
    rcases ha with hok | hq
    · exact ((pipesLm_ok_term fc adm s l b).1 hok).2.1
    · exfalso; revert hq; simp [pipesLm, plaltOf]

/-- **Rocq `pipes_hooks`**: the model's hooks — the free alternatives are the
non-terminal ones; the shell's three per line are its fork panic, the exec
failure of the round's first process ([plExfb]) and the silent round.  Rocq's
decider field (`pipes_lm_ok_dec`) has no Lean counterpart (DU9: `LmHooks`
carries none). -/
noncomputable def pipesHooks : LmHooks (pipesLm fc adm) where
  lmhFree a := !plterm a
  lmhSt0 := ()
  lmhPan _ := plaltCode PLPanic
  lmhExf l := plaltCode (PLRun (plExfb l))
  lmhExfb l := plExfb l ++ uPrompt
  lmhNoc _ := plaltCode (PLRun [])
  lmhFreeCont _ _ _ _ _ := rfl
  lmhFreeTerm a h := phk_free_term a h
  lmhFreeOk _ _ _ _ _ h := h
  lmhPanOk := phk_pan_ok fc adm
  lmhPanFree _ := (phk_code_free fc adm PLPanic).trans rfl
  lmhPanPanic _ := (phk_code_panic fc adm PLPanic).trans rfl
  lmhExfOk := phk_exf_ok fc adm
  lmhExfFree l := (phk_code_free fc adm (PLRun (plExfb l))).trans rfl
  lmhExfNopanic l := (phk_code_panic fc adm (PLRun (plExfb l))).trans rfl
  lmhExfCont s l := phk_code_cont fc adm s l (PLRun (plExfb l))
  lmhNocOk := phk_noc_ok fc adm
  lmhNocFree _ := (phk_code_free fc adm (PLRun [])).trans rfl
  lmhNocNopanic _ := (phk_code_panic fc adm (PLRun [])).trans rfl
  lmhNocCont s l := phk_code_cont fc adm s l (PLRun [])
  lmhContPrompt := phk_cont_prompt fc adm
  lmhContNonnil := phk_cont_nonnil fc adm

end pipesHooks

end Xv6
