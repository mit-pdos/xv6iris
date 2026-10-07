/-
Weak: **the STORE-FORWARDING case for scheduler adequacy: a NEGATIVE result** (AxSL tier).
PURE (no Iris).

Rocq: `iris/AxSchedFwd.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE QUESTION.  In RVWMO a load `r` may read (rfi) from a po-earlier same-address store `w` of its
own hart while being gmo-BEFORE it (ppo rule 1 exempts st→ld same address).  Every epilogue
theorem assumes `gmoLt spill reload`, excluding exactly this.  Does `AxSched`'s scheduler process
`w` before `r` in such a case (so that a policy with a forwarding arm `w ∈ sPol r` could be
`axpolWfL`)?

THE ANSWER: NO — the opposite holds on EVERY run.  `stepCommit` has no "rf-source processed"
guard; `stepDefer` never applies to a write; `Hclear` blocks EVERY commit of a locked hart
(including po-EARLIER events).  So when the walker reaches `r` (before `w`, as `gmoLt r w`),
either `r` commits at once or it is deferred and its hart locked until `r`'s flush.  Either way
`r` precedes `w` in `sProc`.

  §1 the invariant `InvFW` (a same-hart event gmo-before a NEVER-deferred processed event is
     processed before it) and its preservation.
  §2 the forwarding corollary `schedOrdFwdRev` (completed run: `ltIn st.sProc r w`) and
     `schedOrdFwdFalse`.
  §3 the refutation `schedAxpolWfProcFwdFalse`: ANY policy with `w ∈ sPol GD r` (or `lobp`) for a
     gmo-inverted same-hart write `w` is NOT `axpolWfL` on ANY completed run of this scheduler.

MISSING GUARDS (what a forwarding-capable scheduler would need; kept from Rocq).  (1) `Hclear`
relaxed to block only po-LATER same-hart commits — `InvFW` would then fail.  (2) `r` must be
DEFERRED, and `stepDefer`'s `HgateOK` is a real obligation a forwarded reload need not satisfy.
(3) A deferred read's flow equation fires against the snapshot at ITS OWN gmo position, which
does not contain `w`'s deposit: forwarding needs a different read rule, not just a reordering.

**Fetches / Stage C.**  Nothing here mentions fetches (pure scheduler combinatorics).

## Deviations from Rocq

1. NAMES: camelCase (map below).  No name is in `notes/weak-port-dupnames.json`; no Lean-only
   helpers.
2. SECTION: Rocq's `Section SchedFwd` (`Context G Hgwf Hcat6gmo`, `Proof using All`): every §1–§2
   theorem takes `G Hgwf Hcat6gmo` (`include … in`, as in `AxSched`); `InvFW` takes `G` only.
3. VOCABULARY (as `AxSched`/`AxSchedGD`): `gd_g GD` ↦ `GD.gdG`, `s_*` ↦ `st.s*`, `gx_gmo G !! n`
   ↦ `G.gxGmo[n]?`, `gpo` ↦ `WeakRvwmoGraph.gpo`, `s_pol`/`lobp` ↦ `Axpol.sPol`/`Axpol.lobp`.

**Rocq → Lean name map.**  `InvFW` `InvFW`, `InvFW_sst0` `InvFWSst0`, `gmo_lt_visited`
`gmoLtVisited`, `InvFW_step` `InvFWStep`, `sched_ord_fw` `schedOrdFw`, `write_not_everD`
`writeNotEverD`, `sched_ord_fwd_rev` `schedOrdFwdRev`, `sched_ord_fwd_false` `schedOrdFwdFalse`,
`take_L_not_after` `takeLNotAfter`, `sched_axpol_wf_proc_fwd_false` `schedAxpolWfProcFwdFalse`.

**Dropped:** only the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxSchedGD

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

set_option linter.unusedSectionVars false

/-! # 1. `InvFW`: same-hart gmo-predecessors of a never-deferred event -/

def InvFW (G : Gexec) (st : Sstate) : Prop :=
  ∀ e1 e2, e2 ∈ st.sProc → e2 ∉ st.sEverD → e1.1 = e2.1 → gmoLt G e1 e2 →
    ltIn st.sProc e1 e2

section SchedFwd

variable (G : Gexec) (Hgwf : gwf G) (Hcat6gmo : gppoCat6Gmo G)

include Hgwf Hcat6gmo in
theorem InvFWSst0 : InvFW G sst0 := by
  intro e1 e2 He2
  exact absurd He2 List.not_mem_nil

include Hgwf Hcat6gmo in
theorem gmoLtVisited (n : Nat) (e1 e : Geid) :
    G.gxGmo[n]? = some e → gmoLt G e1 e → e1 ∈ visited G n := by
  rintro Hn ⟨He1, _, Hlt⟩
  rw [gposOfLookup G n e Hgwf.1 Hn] at Hlt
  exact (elemOfVisited G Hgwf Hcat6gmo n e1).2
    (elem_of_take.2 ⟨gpos G e1, gposElemLookup G e1 He1, Hlt⟩)

include Hgwf Hcat6gmo in
theorem InvFWStep (st st' : Sstate) :
    AxSched.Inv G st → InvFW G st → schedStep G st st' → InvFW G st' := by
  intro HI HIfw Hstep
  cases Hstep with
  | stepCommit n D everD proc e He Hclear =>
    -- `Hclear` forbids a pending same-hart `e1`.
    obtain ⟨Hfp, _⟩ := freshAt G Hgwf Hcat6gmo _ HI e He
    have Hnd' : (proc ++ [e]).Nodup := by
      refine NoDup_app.2 ⟨HI.invNodup, fun x hx hx' => ?_, NoDup_singleton⟩
      rw [List.mem_singleton] at hx'
      rw [hx'] at hx
      exact Hfp hx
    intro e1 e2 He2 HnD Hh Hlt
    rcases List.mem_append.1 He2 with He2 | He2
    · exact ltInAppL G Hgwf Hcat6gmo proc [e] e1 e2 Hnd' (HIfw e1 e2 He2 HnD Hh Hlt)
    · rw [List.mem_singleton] at He2
      subst He2
      have He1v : e1 ∈ visited G n := gmoLtVisited G Hgwf Hcat6gmo n e1 e2 He Hlt
      rcases (HI.invPart e1).1 He1v with He1p | He1D
      · exact ltInAppLast G Hgwf Hcat6gmo proc e1 e2 Hnd' He1p
      · exact absurd Hh (Hclear e1 He1D)
  | stepDefer n D everD proc e He Hr HgateOK =>
    -- `sProc` unchanged, `sEverD` only grows.
    intro e1 e2 He2 HnD Hh Hlt
    exact HIfw e1 e2 He2 (fun h => HnD (elemOfUnion.2 (.inr h))) Hh Hlt
  | stepFlush n D everD proc r m HD Hfirst =>
    -- the flushed `r` is ever-deferred, so it is never `e2`.
    have Hr0dom : r ∈ AxSched.domG D := AxSched.memDomG.2 (by rw [HD]; rfl)
    have Hr0notp : r ∉ proc := fun h => HI.invDisj r h Hr0dom
    have Hnd' : (proc ++ [r]).Nodup := by
      refine NoDup_app.2 ⟨HI.invNodup, fun x hx hx' => ?_, NoDup_singleton⟩
      rw [List.mem_singleton] at hx'
      rw [hx'] at hx
      exact Hr0notp hx
    intro e1 e2 He2 HnD Hh Hlt
    rcases List.mem_append.1 He2 with He2 | He2
    · exact ltInAppL G Hgwf Hcat6gmo proc [r] e1 e2 Hnd' (HIfw e1 e2 He2 HnD Hh Hlt)
    · rw [List.mem_singleton] at He2
      subst He2
      exact absurd (elemOfSubseteq.1 HI.invDEverD _ Hr0dom) HnD

include Hgwf Hcat6gmo in
theorem schedOrdFw (st : Sstate) : rtc (schedStep G) sst0 st → InvFW G st := by
  intro h
  exact rtc_ind_r (fun st => InvFW G st) sst0 (InvFWSst0 G Hgwf Hcat6gmo)
    (fun y z Hrun Hs Hy =>
      InvFWStep G Hgwf Hcat6gmo y z (invRtc G Hgwf Hcat6gmo y Hrun) Hy Hs) st h

include Hgwf Hcat6gmo in
/-- A write is never ever-deferred (`invEverDR`). -/
theorem writeNotEverD (st : Sstate) (Hrun : rtc (schedStep G) sst0 st) (w : Geid) :
    glblIs G w lbIsW → w ∉ st.sEverD := by
  rintro ⟨l, Hl, Hw⟩ HwD
  obtain ⟨l', Hl', _, Hw'⟩ := (invRtc G Hgwf Hcat6gmo st Hrun).invEverDR w HwD
  rw [Hl] at Hl'
  cases Option.some.inj Hl'
  rw [Hw] at Hw'
  exact Bool.noConfusion Hw'

/-! # 2. THE FORWARDING CASE: `r` IS PROCESSED BEFORE `w` -/

include Hgwf Hcat6gmo in
/-- Completed run (gate-free OR deferring): a same-hart read `r` gmo-before a write `w` is
processed BEFORE `w` — the OPPOSITE of what a forwarding policy arm needs.  No `gpo`/`grf`
premise is needed at all. -/
theorem schedOrdFwdRev (st : Sstate) (Hrun : rtc (schedStep G) sst0 st)
    (Hfull : st.sN = G.gxGmo.length) (Hdone : st.sD = ∅) (r w : Geid) :
    glblIs G w lbIsW → r.1 = w.1 → gmoLt G r w → ltIn st.sProc r w := by
  intro Hw Hh Hlt
  obtain ⟨Hmem, _⟩ := schedCorrect G Hgwf Hcat6gmo st Hrun Hfull Hdone
  exact schedOrdFw G Hgwf Hcat6gmo st Hrun r w ((Hmem w).2 Hlt.2.1)
    (writeNotEverD G Hgwf Hcat6gmo st Hrun w Hw) Hh Hlt

include Hgwf Hcat6gmo in
/-- Hence `w` is NEVER processed before `r` (the literal `sched_ord_fwd` is refuted on every
completed run). -/
theorem schedOrdFwdFalse (st : Sstate) (Hrun : rtc (schedStep G) sst0 st)
    (Hfull : st.sN = G.gxGmo.length) (Hdone : st.sD = ∅) (r w : Geid) :
    glblIs G w lbIsW → WeakRvwmoGraph.gpo G w r → gmoLt G r w → ¬ ltIn st.sProc w r := by
  rintro Hw Hpo Hlt ⟨_, _, Hwr⟩
  obtain ⟨_, _, Hrw⟩ :=
    schedOrdFwdRev G Hgwf Hcat6gmo st Hrun Hfull Hdone r w Hw Hpo.1.symm Hlt
  omega

end SchedFwd

/-! # 3. A FORWARDING POLICY ARM IS NEVER `axpolWfL` ON THIS SCHEDULER -/

/-- `takeL`-membership against a later-positioned element. -/
theorem takeLNotAfter (L : List Geid) (n : Nat) (r w : Geid) :
    L.Nodup → L[n]? = some r → ltIn L r w → w ∉ takeL L n := by
  rintro Hnd Hn ⟨_, _, Hlt⟩ Hw
  obtain ⟨j, Hj, Hjn⟩ := elem_of_take.1 (elemOfListToSet.1 Hw)
  rw [lposOfLookup L n r Hnd Hn, lposOfLookup L j w Hnd Hj] at Hlt
  omega

/-- THE REFUTATION.  If the policy hands a gmo-inverted same-hart write `w` to `r` (in particular
the forwarding arm: `gpo w r`, `r` reads from `w`, `gmoLt r w`), then `axpolWfL GD st.sProc`
FAILS for every completed run `st` of `AxSched`'s scheduler — gate-free or deferring alike. -/
theorem schedAxpolWfProcFwdFalse [Axpol] (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (r w : Geid) (Hw : glblIs GD.gdG w lbIsW) (Hh : r.1 = w.1)
    (Hlt : gmoLt GD.gdG r w)
    (Hpol : w ∈ Axpol.sPol GD r ∨ w ∈ Axpol.lobp GD r) :
    ¬ axpolWfL GD st.sProc := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmem, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  intro Hwf
  have Hg1 : r ∈ st.sProc := (Hmem r).2 Hlt.1
  obtain ⟨n, Hn, _⟩ := lposLookup st.sProc r Hg1
  have Hord := schedOrdFwdRev GD.gdG HGw HC6 st Hrun Hfull Hdone r w Hw Hh Hlt
  have Hnot := takeLNotAfter st.sProc n r w HndP Hn Hord
  obtain ⟨Hs, Hl⟩ := Hwf n r Hn
  rcases Hpol with Hp | Hp
  · exact Hnot (elemOfSubseteq.1 Hs w Hp)
  · exact Hnot (elemOfSubseteq.1 Hl w Hp)

end Weak
