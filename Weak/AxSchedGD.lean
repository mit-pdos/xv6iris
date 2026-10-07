/-
Weak: **`AxSched`'s scheduler WRAPPED over a `Gdexec` `GD`, and the `gppoCat` rule-12 /
`gdepsRel` arms of `AxAdequacyL.LPredClosedFlow`** (AxSL tier; LB/AxSL ctrl-gate scheduler).

Rocq: `iris/AxSchedGD.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxSched`'s scheduler section is parametric in a bare `Gexec`, so `AxAdequacyL`'s §6 left the
rule-12 (`gppo12`) and `gdepsRel` arms of the flow closure OPEN: they need `GD.gdDeps` of a real
`Gdexec`.  This file reuses every `AxSched` name as exported, at `G := GD.gdG`.

  §0 the two `AxSched` section hypotheses (`gwf`, `gppoCat6Gmo`) from `rvwmoCatConsistent GD`.
  §1 `gdepsEdge` (rule 12 OR `gdepsRel`) is same-hart, gmo-forward AND genuine program order
     (`gppo12Gpo`: a NEW argument — the RVWMO⁻ proof via `gpoloc` R→W does not port to the cat
     model; instead pin `a` (the dep source) against `b` by rule 1 + `gppoCatGmo` and nat
     trichotomy).
  §2 a SECOND scheduler invariant `Inv2` (kept separate from `AxSched.Inv`), preserved by
     `schedStep` by re-running `AxSched.invStep`'s `invOrdPpo` case with `gdepsEdge`.
  §3 `schedLPredClosedFlow`: for ANY completed scheduler run, `LPredClosedFlow GD st.sProc`
     holds with no hypothesis beyond `rvwmoCatConsistent GD` — `AxAdequacyL`'s §6 FINDING closed.
  §4 `schedProcAdequate`: `AxSchedIris.procAdequate`'s placeholder restated concretely and
     proved, via `axpolWfLOfPredClosedFlow` and `adequacyOrdL` at `L := st.sProc`.
     `deferredSnapAvail` is threaded through UNCONSUMED (a per-instance obligation, as in Rocq).

**Fetches / WP step clause.**  Nothing here mentions fetches or introduces/eliminates the WP step
clause: §4 only applies `AxAdequacyL.adequacyOrdL` as a black box (phase 2, `flowEqEa`), so the
pending Q8 `fetchPin` rework does not touch this file.

## Deviations from Rocq

1. NAMES: camelCase (map below).  No name is in `notes/weak-port-dupnames.json`; no Lean-only
   helpers.
2. VOCABULARY (as `AxSched`/`AxAdequacyL`): `gd_g GD` ↦ `GD.gdG`, `gd_deps` ↦ `gdDeps`, `gpo` ↦
   `WeakRvwmoGraph.gpo`, `grf` ↦ `WeakRvwmoAcyc.grf`, `dom D` ↦ `AxSched.domG D`, `s_*` ↦
   `st.s*`, `list_to_set` ↦ `LawfulSet.ofList`, `≡ₚ` ↦ `List.Perm`, `from_option id emp` ↦
   `AxWp.fromOption (fun P => P) iprop(emp)`, `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`.
3. `schedProcAdequate`: Rocq's `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc` (as
   `AxAdequacyL.adequacyOrdL`); the wand chain is stated `⊢ A -∗ B -∗ C`.  `Hdefer` is unused, as
   in Rocq (the unused-variable linter is silenced for that theorem).
4. `gobCatFlowOrd`: `tc` is Lean's tail-style `TransGen`, so the induction splits at the LAST
   step (`ltInTrans ih (single)`) instead of Rocq's first step; same statement.

**Rocq → Lean name map.**  `sched_HGwf` `schedHGwf`, `sched_HCat6gmo` `schedHCat6gmo`,
`gdeps_edge` `gdepsEdge`, `gppo12_gpo` `gppo12Gpo`, `gdeps_edge_same_hart` `gdepsEdgeSameHart`,
`gdeps_edge_gmo` `gdepsEdgeGmo`, `gdeps_edge_gpo` `gdepsEdgeGpo`, `Inv2` `Inv2`, `Inv2_sst0`
`Inv2Sst0`, `Inv2_step` `Inv2Step`, `Inv2_rtc` `Inv2Rtc`, `lt_in_trans` `ltInTrans`,
`gobr_cat_flow_single` `gobrCatFlowSingle`, `gob_cat_flow_ord` `gobCatFlowOrd`,
`sched_L_pred_closed_flow` `schedLPredClosedFlow`, `sched_axpol_wf_proc` `schedAxpolWfProc`,
`sched_proc_adequate` `schedProcAdequate`.

**Dropped:** only the §5 `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxAdequacyL
import Weak.AxSchedIris

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp

/-! # 0. `AxSched`'s section hypotheses at `G := GD.gdG` -/

theorem schedHGwf (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) : gwf GD.gdG := Hcons.1

theorem schedHCat6gmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) : gppoCat6Gmo GD.gdG :=
  (catImpliesCat6 GD Hcons).2.1

/-! # 1. `gdepsEdge`: the `Gdexec`-level same-hart arms, and `gpo` for rule 12 -/

/-- Rule 12 (`gppo12`) or the untagged dep relation (`gdepsRel`). -/
def gdepsEdge (GD : Gdexec) (x y : Geid) : Prop :=
  gppo12 GD.gdG GD.gdDeps x y ∨ gdepsRel GD x y

/-- THE NEW ARGUMENT: a rule-12 edge `a → b` is genuine program order, even under the cat model.
If `b.2 ≤ a.2` then `b` is po-before `m` (`a.2 < m.2`), so rule 1 orders `b` gmo-before `m`,
contradicting either disjunct of `gvisible m b`. -/
theorem gppo12Gpo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (a b : Geid) :
    gppo12 GD.gdG GD.gdDeps a b → WeakRvwmoGraph.gpo GD.gdG a b := by
  rintro ⟨Hag, m, Hd, Hrf⟩
  obtain ⟨_, Hppo, Hlv, _, Hdw, _⟩ := Hcons
  obtain ⟨Ham, Halt, Har, Hmw⟩ := Hdw (a, m) Hd
  simp only at Ham Halt
  obtain ⟨la, Hla, _⟩ := Har
  obtain ⟨lm, Hlm, _⟩ := Hmw
  obtain ⟨a1, t1, v1, Hrdb, Hwat⟩ := Hrf
  have Hlb : (gxLbl GD.gdG b).isSome := by
    obtain ⟨lb, base, ts, vs, j, Hlb0, _⟩ := Hrdb
    simp [Hlb0]
  have Hcase := (Hlv b a1 t1 v1 Hrdb).1
  cases t1 with
  | zero => simp [gwriteAt] at Hwat
  | succ t1' =>
    obtain ⟨w, Hw, Hwb, Hvis⟩ := Hcase
    have Heqwm : w = m := by
      rw [Hwat] at Hw
      exact (Option.some.inj Hw).symm
    subst Heqwm
    by_cases Hle : b.2 ≤ a.2
    · exfalso
      have Hbm : WeakRvwmoGraph.gpo GD.gdG b w :=
        ⟨by rw [← Hag]; exact Ham, by omega, Hlb, by simp [Hlm]⟩
      have Hacc : gaccesses GD.gdG b a1 := Or.inr ⟨t1' + 1, v1, Hrdb⟩
      have Hp1 : gppo1 GD.gdG b w := ⟨Hbm, a1, Hacc, v1, Hwb⟩
      have Hmobm := Hppo b w (Or.inl (Or.inl Hp1))
      rcases Hvis with Hmomb | Hpombm
      · have h1 := Hmomb.2.2
        have h2 := Hmobm.2.2
        omega
      · have h3 := Hpombm.2.1
        have h4 := Hbm.2.1
        omega
    · exact ⟨Hag, by omega, by simp [Hla], Hlb⟩

theorem gdepsEdgeSameHart (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (x y : Geid) :
    gdepsEdge GD x y → x.1 = y.1 := by
  rintro (Hp | Hd)
  · exact Hp.1
  · exact (Hcons.2.2.2.2.1 (x, y) Hd).1

theorem gdepsEdgeGmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (x y : Geid) :
    gdepsEdge GD x y → gmoLt GD.gdG x y := by
  rintro (Hp | Hd)
  · exact Hcons.2.1 x y (Or.inr Hp)
  · exact Hcons.2.2.2.2.2 (x, y) Hd

theorem gdepsEdgeGpo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (x y : Geid) :
    gdepsEdge GD x y → WeakRvwmoGraph.gpo GD.gdG x y := by
  rintro (Hp | Hd)
  · exact gppo12Gpo GD Hcons x y Hp
  · obtain ⟨Ham, Halt, ⟨la, Hla, _⟩, ⟨lb, Hlb, _⟩⟩ := Hcons.2.2.2.2.1 (x, y) Hd
    exact ⟨Ham, Halt, by simp [Hla], by simp [Hlb]⟩

/-! # 2. `Inv2`: a second scheduler invariant for `gdepsEdge` -/

/-- The general form of `AxSched.Inv.invOrdPpo`, for `gdepsEdge` instead of `gppoCat6`. -/
def Inv2 (GD : Gdexec) (st : Sstate) : Prop :=
  ∀ e1 e2, e1 ∈ st.sEverD → gdepsEdge GD e1 e2 → e2 ∈ st.sProc → ltIn st.sProc e1 e2

theorem Inv2Sst0 (GD : Gdexec) : Inv2 GD sst0 := by
  intro e1 e2 Hin _ _
  exact absurd Hin notElemOfEmpty

/-- `AxSched.invStep`'s `invOrdPpo` case, with `gppoCat6`/`Hcat6gmo` replaced by
`gdepsEdge`/`gdepsEdgeGmo`/`gdepsEdgeGpo`. -/
theorem Inv2Step (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (st st' : Sstate) :
    AxSched.Inv GD.gdG st → Inv2 GD st → schedStep GD.gdG st st' → Inv2 GD st' := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  intro HI HI2 Hstep
  cases Hstep with
  | stepCommit n D everD proc e He Hclear =>
    have Hpart : ∀ x, x ∈ visited GD.gdG n ↔ x ∈ proc ∨ x ∈ AxSched.domG D := HI.invPart
    have HeDvis : ∀ x, x ∈ everD → x ∈ visited GD.gdG n := elemOfSubseteq.1 HI.invEverDVis
    obtain ⟨Hfp, _⟩ := freshAt GD.gdG HGw HC6 _ HI e He
    have Hnd' : (proc ++ [e]).Nodup := by
      refine NoDup_app.2 ⟨HI.invNodup, fun x hx hx' => ?_, NoDup_singleton⟩
      rw [List.mem_singleton] at hx'
      rw [hx'] at hx
      exact Hfp hx
    intro e1 e2 He1 Hedge He2
    change e1 ∈ everD at He1
    change e2 ∈ proc ++ [e] at He2
    change ltIn (proc ++ [e]) e1 e2
    rcases List.mem_append.1 He2 with He2 | He2
    · exact ltInAppL GD.gdG HGw HC6 proc [e] e1 e2 Hnd' (HI2 e1 e2 He1 Hedge He2)
    · rw [List.mem_singleton] at He2
      subst He2
      by_cases He1D : e1 ∈ AxSched.domG D
      · exact absurd (gdepsEdgeSameHart GD Hcons e1 e2 Hedge) (Hclear e1 He1D)
      · have He1p : e1 ∈ proc := by
          rcases (Hpart e1).1 (HeDvis e1 He1) with h | h
          · exact h
          · exact absurd h He1D
        exact ltInAppLast GD.gdG HGw HC6 proc e1 e2 Hnd' He1p
  | stepDefer n D everD proc e He Hr HgateOK =>
    have Hpart : ∀ x, x ∈ visited GD.gdG n ↔ x ∈ proc ∨ x ∈ AxSched.domG D := HI.invPart
    intro e1 e2 He1 Hedge He2
    change e1 ∈ ({e} ∪ everD : GSet Geid) at He1
    change e2 ∈ proc at He2
    change ltIn proc e1 e2
    rw [elemOfUnion, elemOfSingleton] at He1
    rcases He1 with Hee | He1
    · exfalso
      subst Hee
      have Hlt0 := (gdepsEdgeGmo GD Hcons e1 e2 Hedge).2.2
      have Hlt1 : gpos GD.gdG e2 < n :=
        visitedElemGposLt GD.gdG HGw HC6 n e2 ((Hpart e2).2 (.inl He2))
      rw [gposOfLookup GD.gdG n e1 HGw.1 He] at Hlt0
      omega
    · exact HI2 e1 e2 He1 Hedge He2
  | stepFlush n D everD proc r m HD Hfirst =>
    have Hpart : ∀ x, x ∈ visited GD.gdG n ↔ x ∈ proc ∨ x ∈ AxSched.domG D := HI.invPart
    have HeDvis : ∀ x, x ∈ everD → x ∈ visited GD.gdG n := elemOfSubseteq.1 HI.invEverDVis
    have Hr0dom : r ∈ AxSched.domG D := AxSched.memDomG.2 (by rw [HD]; rfl)
    have Hr0notp : r ∉ proc := fun h => HI.invDisj r h Hr0dom
    have Hnd' : (proc ++ [r]).Nodup := by
      refine NoDup_app.2 ⟨HI.invNodup, fun x hx hx' => ?_, NoDup_singleton⟩
      rw [List.mem_singleton] at hx'
      rw [hx'] at hx
      exact Hr0notp hx
    intro e1 e2 He1 Hedge He2
    change e1 ∈ everD at He1
    change e2 ∈ proc ++ [r] at He2
    change ltIn (proc ++ [r]) e1 e2
    rcases List.mem_append.1 He2 with He2 | He2
    · exact ltInAppL GD.gdG HGw HC6 proc [r] e1 e2 Hnd' (HI2 e1 e2 He1 Hedge He2)
    · rw [List.mem_singleton] at He2
      subst He2
      by_cases He1p : e1 ∈ proc
      · exact ltInAppLast GD.gdG HGw HC6 proc e1 e2 Hnd' He1p
      · exfalso
        rcases (Hpart e1).1 (HeDvis e1 He1) with h | He1D
        · exact He1p h
        · obtain ⟨m', Hm'⟩ := Option.isSome_iff_exists.1 (AxSched.memDomG.1 He1D)
          exact Hfirst e1 m' Hm' (gdepsEdgeSameHart GD Hcons e1 e2 Hedge)
            (gdepsEdgeGpo GD Hcons e1 e2 Hedge)

theorem Inv2Rtc (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (st : Sstate) :
    rtc (schedStep GD.gdG) sst0 st → Inv2 GD st := by
  intro h
  exact rtc_ind_r (fun st => Inv2 GD st) sst0 (Inv2Sst0 GD)
    (fun y z Hrun Hstep IH2 =>
      Inv2Step GD Hcons y z
        (invRtc GD.gdG (schedHGwf GD Hcons) (schedHCat6gmo GD Hcons) y Hrun) IH2 Hstep) st h

/-! # 3. `LPredClosedFlow GD st.sProc`, unconditionally -/

theorem ltInTrans (L : List Geid) (x y z : Geid) : ltIn L x y → ltIn L y z → ltIn L x z := by
  rintro ⟨Hx, _, Hlt1⟩ ⟨_, Hz, Hlt2⟩
  exact ⟨Hx, Hz, by omega⟩

/-- THE PER-EDGE DISPATCH: `e1 ∈ sEverD` or not.  Not deferred ⇒ `invOrdFresh`; deferred ⇒ `e1`
is a plain read, which rules out every write/RMW-sourced arm and leaves `gppoCat6` (via
`invOrdPpo`) and `gppo12`/`gdepsRel` (via `Inv2`). -/
theorem gobrCatFlowSingle (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (HI : AxSched.Inv GD.gdG st) (HI2 : Inv2 GD st)
    (Hmemiff : ∀ e, e ∈ st.sProc ↔ e ∈ GD.gdG.gxGmo)
    (e1 e2 : Geid) (Hedge : gobrCatFlow GD e1 e2) :
    ltIn st.sProc e1 e2 := by
  have Hmo : gmoLt GD.gdG e1 e2 := gobrCatGmo GD e1 e2 Hcons (gobrCatFlowSub GD e1 e2 Hedge)
  obtain ⟨He1mem, He2mem, Hltpos⟩ := Hmo
  have He1p : e1 ∈ st.sProc := (Hmemiff e1).2 He1mem
  have He2p : e2 ∈ st.sProc := (Hmemiff e2).2 He2mem
  by_cases HeD : e1 ∈ st.sEverD
  · obtain ⟨l1, Hl1, _, Hw1⟩ := HI.invEverDR e1 HeD
    have Hnw : gisW GD.gdG e1 ≠ true := by
      simp [gisW, Hl1, Hw1]
    rcases Hedge with Hpp | Hdr | Hrfe | Hco | ⟨_, Hisw⟩
    · rcases Hpp with Hpp6 | Hpp12
      · exact HI.invOrdPpo e1 e2 HeD Hpp6 He2p
      · exact HI2 e1 e2 HeD (Or.inl Hpp12) He2p
    · exact HI2 e1 e2 HeD (Or.inr Hdr) He2p
    · exact absurd (grfGisW GD.gdG e1 e2 Hrfe.1) Hnw
    · obtain ⟨a0, v0, _, Hwb, _⟩ := Hco
      exact absurd (WeakRvwmoGraph.gwritesByteGisW GD.gdG e1 a0 v0 Hwb) Hnw
    · exact absurd Hisw Hnw
  · exact HI.invOrdFresh e1 e2 He1p He2p HeD Hltpos

theorem gobCatFlowOrd (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (st : Sstate)
    (HI : AxSched.Inv GD.gdG st) (HI2 : Inv2 GD st)
    (Hmemiff : ∀ e, e ∈ st.sProc ↔ e ∈ GD.gdG.gxGmo) (e1 e2 : Geid) :
    gobCatFlow GD e1 e2 → ltIn st.sProc e1 e2 := by
  intro h
  induction h with
  | single H => exact gobrCatFlowSingle GD Hcons st HI HI2 Hmemiff _ _ H
  | tail _ H IH =>
    exact ltInTrans st.sProc _ _ _ IH (gobrCatFlowSingle GD Hcons st HI HI2 Hmemiff _ _ H)

/-- THE MAIN RESULT: for ANY completed scheduler run, `st.sProc` satisfies `LPredClosedFlow` —
`AxAdequacyL`'s §6 FINDING, closed. -/
theorem schedLPredClosedFlow (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅) :
    LPredClosedFlow GD st.sProc := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  have HI := invRtc GD.gdG HGw HC6 st Hrun
  have HI2 := Inv2Rtc GD Hcons st Hrun
  obtain ⟨Hmemiff, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  intro n e Hn e' Hedge
  exact ltInTakeL st.sProc n e e' HndP Hn (gobCatFlowOrd GD Hcons st HI HI2 Hmemiff e' e Hedge)

/-! # 4. `procAdequate`, concretely -/

/-- `axpolWfProc GD st.sProc`, via `AxAdequacyL.axpolWfLOfPredClosedFlow`. -/
theorem schedAxpolWfProc [Axpol] (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (HsPolSub : ∀ e e', e' ∈ Axpol.sPol GD e → gobCatFlow GD e' e)
    (HlobpSub : ∀ e e', e' ∈ Axpol.lobp GD e → gobCatFlow GD e' e) :
    axpolWfProc GD st.sProc := by
  intro n e Hn
  exact axpolWfLOfPredClosedFlow GD st.sProc HsPolSub HlobpSub
    (schedLPredClosedFlow GD Hcons st Hrun Hfull Hdone) n e Hn

section ProcAdequate
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

set_option linter.unusedVariables false in
/-- THE TARGET, DISCHARGED: `AxSchedIris.procAdequate`'s placeholder, restated concretely at
`L := st.sProc` and proved by `adequacyOrdL`.  `Hdefer` is carried through UNCONSUMED. -/
theorem schedProcAdequate (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (HsPolSub : ∀ e e', e' ∈ Axpol.sPol GD e → gobCatFlow GD e' e)
    (HlobpSub : ∀ e e', e' ∈ Axpol.lobp GD e → gobCatFlow GD e' e)
    (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm → (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodoL GD ea na st.sProc 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) := by
  have HGw := schedHGwf GD Hcons
  have HC6 := schedHCat6gmo GD Hcons
  obtain ⟨Hmemiff, HndP, _⟩ := schedCorrect GD.gdG HGw HC6 st Hrun Hfull Hdone
  have Hperm : st.sProc.Perm GD.gdG.gxGmo := NoDup_Permutation HndP HGw.1 Hmemiff
  have Hpol : axpolWfL GD st.sProc := by
    intro n e Hn
    exact schedAxpolWfProc GD Hcons st Hrun Hfull Hdone HsPolSub HlobpSub n e Hn
  exact adequacyOrdL GD Hcons st.sProc Hperm Hpol na ea HdomEq Hdom HeaLob σ0

end ProcAdequate

end Weak
