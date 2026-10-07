/-
Weak: **the SAME-HART order clause of `AxSched`'s scheduler** — an ever-deferred event precedes
every processed PO-LATER, GMO-LATER event of its hart — and the corollary lifting `AxTierA3`'s
GATE-FREE restriction for the deviation-2 (`gpoloc ∧ gmoLt`) arm of `flowDev2` (AxSL tier).

Rocq: `iris/AxSchedSH.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE FINDING: `AxSched.stepFlush` releases a pending read under `Hfirst` (no pending same-hart
po-earlier read), so flushing is forced into PO order per hart.  Hence the clause with only
`e1.1 = e2.1 ∧ gmoLt e1 e2` is FALSE for this step relation (two same-hart plain reads, the
po-later one gmo-earlier, both deferred: `Hfirst` forces the po-first one out first).

WHAT HOLDS, AND SUFFICES: with the premise `gpo e1 e2 ∧ gmoLt e1 e2` the clause is preserved by
every step — commit uses `Hclear` (same hart, from `gpo`), defer uses `gmoLt` (the successor is
not yet visited), flush uses `Hfirst` (with `gpo`).  Deviation 2's arm is `gpoloc ∧ gmoLt` and
`gpoloc ⊆ gpo`, which is exactly what `AxTierA3.gatefreeAxpolWfProc` needed `Hgatefree` for.

  §1 `InvSH` + `InvSHStep` + `schedOrdSh` (rtc form).
  §2 with `invOrdFresh`: `schedOrdShProc` (any reachable state, both processed),
     `schedOrdShFull` (completed run), `schedOrdShTake` (the `takeL` form).
  §3 `schedAxpolWfProcDev2`: `axpolWfL GD st.sProc` for ANY completed (possibly deferring) run
     from `flowDev2`-bounded policies — no `Hgatefree`.  (The general `gmoLt`-bounded premise of
     `gatefreeAxpolWfProc` can NOT be lifted this way.)

Nothing here mentions fetches (Stage C does not touch this file).

## Deviations from Rocq

1. NAMES: camelCase (map below).  No name is in `notes/weak-port-dupnames.json`; no Lean-only
   helpers.  Vocabulary as AxSchedGD (deviation 2): `gpo` ↦ `WeakRvwmoGraph.gpo`, `dom D` ↦
   `AxSched.domG D`, `s_*` ↦ `st.s*`, `take_L` ↦ `takeL`, `gd_g GD` ↦ `GD.gdG`.
2. The Rocq section `SchedSH` (context `G`, `Hgwf`, `Hcat6gmo`) is unfolded: every §1/§2 lemma
   takes `G Hgwf Hcat6gmo` explicitly, also `InvSHSst0` (Rocq `Proof using Type`) does not.

**Rocq → Lean name map.**  `InvSH` `InvSH`, `InvSH_sst0` `InvSHSst0`, `InvSH_step` `InvSHStep`,
`sched_ord_sh` `schedOrdSh`, `sched_ord_sh_proc` `schedOrdShProc`, `sched_ord_sh_full`
`schedOrdShFull`, `sched_ord_sh_take` `schedOrdShTake`, `sched_axpol_wf_proc_dev2`
`schedAxpolWfProcDev2`.

**Dropped:** only the two `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSchedGD
import Weak.AxTierA3

namespace Weak

open Iris Iris.Std MachCSL MachCSL.Stdpp

/-! # 1. The clause and its preservation -/

/-- An ever-deferred `e1` precedes every processed po-later, gmo-later `e2`. -/
def InvSH (G : Gexec) (st : Sstate) : Prop :=
  ∀ e1 e2, e1 ∈ st.sEverD → WeakRvwmoGraph.gpo G e1 e2 → gmoLt G e1 e2 →
    e2 ∈ st.sProc → ltIn st.sProc e1 e2

theorem InvSHSst0 (G : Gexec) : InvSH G sst0 := by
  intro e1 e2 Hin _ _ _
  exact absurd Hin notElemOfEmpty

theorem InvSHStep (G : Gexec) (Hgwf : gwf G) (Hcat6gmo : gppoCat6Gmo G) (st st' : Sstate) :
    AxSched.Inv G st → InvSH G st → schedStep G st st' → InvSH G st' := by
  intro HI HIsh Hstep
  cases Hstep with
  | stepCommit n D everD proc e He Hclear =>
    have Hpart : ∀ x, x ∈ visited G n ↔ x ∈ proc ∨ x ∈ AxSched.domG D := HI.invPart
    have HeDvis : ∀ x, x ∈ everD → x ∈ visited G n := elemOfSubseteq.1 HI.invEverDVis
    obtain ⟨Hfp, _⟩ := freshAt G Hgwf Hcat6gmo _ HI e He
    have Hnd' : (proc ++ [e]).Nodup := by
      refine NoDup_app.2 ⟨HI.invNodup, fun x hx hx' => ?_, NoDup_singleton⟩
      rw [List.mem_singleton] at hx'
      rw [hx'] at hx
      exact Hfp hx
    intro e1 e2 He1 Hpo Hlt He2
    change e1 ∈ everD at He1
    change e2 ∈ proc ++ [e] at He2
    change ltIn (proc ++ [e]) e1 e2
    rcases List.mem_append.1 He2 with He2 | He2
    · exact ltInAppL G Hgwf Hcat6gmo proc [e] e1 e2 Hnd' (HIsh e1 e2 He1 Hpo Hlt He2)
    · rw [List.mem_singleton] at He2
      subst He2
      by_cases He1D : e1 ∈ AxSched.domG D
      · exact absurd Hpo.1 (Hclear e1 He1D)
      · have He1p : e1 ∈ proc := by
          rcases (Hpart e1).1 (HeDvis e1 He1) with h | h
          · exact h
          · exact absurd h He1D
        exact ltInAppLast G Hgwf Hcat6gmo proc e1 e2 Hnd' He1p
  | stepDefer n D everD proc e He Hr HgateOK =>
    have Hpart : ∀ x, x ∈ visited G n ↔ x ∈ proc ∨ x ∈ AxSched.domG D := HI.invPart
    intro e1 e2 He1 Hpo Hlt He2
    change e1 ∈ ({e} ∪ everD : GSet Geid) at He1
    change e2 ∈ proc at He2
    change ltIn proc e1 e2
    rw [elemOfUnion, elemOfSingleton] at He1
    rcases He1 with Hee | He1
    · exfalso
      subst Hee
      have Hlt0 := Hlt.2.2
      have Hlt1 : gpos G e2 < n := visitedElemGposLt G Hgwf Hcat6gmo n e2 ((Hpart e2).2 (.inl He2))
      rw [gposOfLookup G n e1 Hgwf.1 He] at Hlt0
      omega
    · exact HIsh e1 e2 He1 Hpo Hlt He2
  | stepFlush n D everD proc r m HD Hfirst =>
    have Hpart : ∀ x, x ∈ visited G n ↔ x ∈ proc ∨ x ∈ AxSched.domG D := HI.invPart
    have HeDvis : ∀ x, x ∈ everD → x ∈ visited G n := elemOfSubseteq.1 HI.invEverDVis
    have Hr0dom : r ∈ AxSched.domG D := AxSched.memDomG.2 (by rw [HD]; rfl)
    have Hr0notp : r ∉ proc := fun h => HI.invDisj r h Hr0dom
    have Hnd' : (proc ++ [r]).Nodup := by
      refine NoDup_app.2 ⟨HI.invNodup, fun x hx hx' => ?_, NoDup_singleton⟩
      rw [List.mem_singleton] at hx'
      rw [hx'] at hx
      exact Hr0notp hx
    intro e1 e2 He1 Hpo Hlt He2
    change e1 ∈ everD at He1
    change e2 ∈ proc ++ [r] at He2
    change ltIn (proc ++ [r]) e1 e2
    rcases List.mem_append.1 He2 with He2 | He2
    · exact ltInAppL G Hgwf Hcat6gmo proc [r] e1 e2 Hnd' (HIsh e1 e2 He1 Hpo Hlt He2)
    · rw [List.mem_singleton] at He2
      subst He2
      by_cases He1p : e1 ∈ proc
      · exact ltInAppLast G Hgwf Hcat6gmo proc e1 e2 Hnd' He1p
      · exfalso
        rcases (Hpart e1).1 (HeDvis e1 He1) with h | He1D
        · exact He1p h
        · obtain ⟨m', Hm'⟩ := Option.isSome_iff_exists.1 (AxSched.memDomG.1 He1D)
          exact Hfirst e1 m' Hm' Hpo.1 Hpo

/-- The rtc form. -/
theorem schedOrdSh (G : Gexec) (Hgwf : gwf G) (Hcat6gmo : gppoCat6Gmo G) (st : Sstate) :
    rtc (schedStep G) sst0 st → InvSH G st := by
  intro h
  exact rtc_ind_r (fun st => InvSH G st) sst0 (InvSHSst0 G)
    (fun y z Hrun Hstep IH =>
      InvSHStep G Hgwf Hcat6gmo y z (invRtc G Hgwf Hcat6gmo y Hrun) IH Hstep) st h

/-! # 2. Combined with `invOrdFresh` -/

/-- Any reachable state: a processed po-earlier, gmo-earlier event of the same hart is
processed first — deferred (`schedOrdSh`) or not (`invOrdFresh`). -/
theorem schedOrdShProc (G : Gexec) (Hgwf : gwf G) (Hcat6gmo : gppoCat6Gmo G) (st : Sstate)
    (Hrun : rtc (schedStep G) sst0 st) (e1 e2 : Geid) :
    e1 ∈ st.sProc → e2 ∈ st.sProc → WeakRvwmoGraph.gpo G e1 e2 → gmoLt G e1 e2 →
    ltIn st.sProc e1 e2 := by
  intro He1 He2 Hpo Hlt
  by_cases HeD : e1 ∈ st.sEverD
  · exact schedOrdSh G Hgwf Hcat6gmo st Hrun e1 e2 HeD Hpo Hlt He2
  · exact (invRtc G Hgwf Hcat6gmo st Hrun).invOrdFresh e1 e2 He1 He2 HeD Hlt.2.2

/-- Completed run: both are processed automatically. -/
theorem schedOrdShFull (G : Gexec) (Hgwf : gwf G) (Hcat6gmo : gppoCat6Gmo G) (st : Sstate)
    (Hrun : rtc (schedStep G) sst0 st)
    (Hfull : st.sN = G.gxGmo.length) (Hdone : st.sD = ∅) (e1 e2 : Geid) :
    WeakRvwmoGraph.gpo G e1 e2 → gmoLt G e1 e2 → ltIn st.sProc e1 e2 := by
  intro Hpo Hlt
  obtain ⟨Hmem, _⟩ := schedCorrect G Hgwf Hcat6gmo st Hrun Hfull Hdone
  exact schedOrdShProc G Hgwf Hcat6gmo st Hrun e1 e2 ((Hmem e1).2 Hlt.1) ((Hmem e2).2 Hlt.2.1)
    Hpo Hlt

/-- The `takeL` form: `e1` sits in the prefix before `e2`'s position. -/
theorem schedOrdShTake (G : Gexec) (Hgwf : gwf G) (Hcat6gmo : gppoCat6Gmo G) (st : Sstate)
    (Hrun : rtc (schedStep G) sst0 st)
    (Hfull : st.sN = G.gxGmo.length) (Hdone : st.sD = ∅) (n : Nat) (e1 e2 : Geid) :
    st.sProc[n]? = some e2 → WeakRvwmoGraph.gpo G e1 e2 → gmoLt G e1 e2 →
    e1 ∈ takeL st.sProc n := by
  intro Hn Hpo Hlt
  obtain ⟨_, Hnd, _⟩ := schedCorrect G Hgwf Hcat6gmo st Hrun Hfull Hdone
  exact ltInTakeL st.sProc n e2 e1 Hnd Hn
    (schedOrdShFull G Hgwf Hcat6gmo st Hrun Hfull Hdone e1 e2 Hpo Hlt)

/-! # 3. `flowDev2`-bounded policies on any completed run -/

/-- `AxTierA3.gatefreeAxpolWfProc` without `Hgatefree`, for policies bounded by `flowDev2` (its
`gobCatFlow` arm via `gobCatFlowOrd`, its `gpoloc ∧ gmoLt` arm via `schedOrdShFull`). -/
theorem schedAxpolWfProcDev2 [Axpol] (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (HsPolDev2 : ∀ e e', e' ∈ Axpol.sPol GD e → flowDev2 GD e' e)
    (HlobpDev2 : ∀ e e', e' ∈ Axpol.lobp GD e → flowDev2 GD e' e) :
    axpolWfL GD st.sProc := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  have HI := invRtc GD.gdG HGw HC6 st Hrun
  have HI2 := Inv2Rtc GD Hcons st Hrun
  obtain ⟨Hmem, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  have Hdev : ∀ n e e', st.sProc[n]? = some e → flowDev2 GD e' e →
      e' ∈ takeL st.sProc n := by
    intro n e e' Hn Hf
    refine ltInTakeL st.sProc n e e' HndP Hn ?_
    rcases Hf with Hf | ⟨Hpl, Hlt⟩
    · exact gobCatFlowOrd GD Hcons st HI HI2 Hmem e' e Hf
    · exact schedOrdShFull GD.gdG HGw HC6 st Hrun Hfull Hdone e' e Hpl.1 Hlt
  intro n e Hn
  exact ⟨fun e' He' => Hdev n e e' Hn (HsPolDev2 e e' He'),
    fun e' He' => Hdev n e e' Hn (HlobpDev2 e e' He')⟩

end Weak
