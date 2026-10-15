/-
Weak: **W11-C2′ [OWN.82][OWN.97] — the release-tag chain over the PRIMED log.**

The primed machine (`Weak/WbPrimed.lean`) differs from the registered one only in the
release bookkeeping of the walker's write-back; its log is the registered log with some classes
re-tagged.  This file carries the release-tag chain onto that log, leaving every registered
definition untouched ([OWN.97]):

* §1 — W2's memory relation does not see classes (`WbPrimed.rmemRetag`), so W11-C's realized read
  and its refutation hold verbatim at the primed configuration (`WbPrimed.readAtPrimed`,
  `WbPrimed.ownedUnpubRefutedPrimed`): `ownedUnpubRefuted` is generic in the configuration and
  needs only `relSiteWCrel` OF THE PRIMED LOG.
* §2 — the primed run RECORDED along W4's record (`WbPrimed.chainW`,
  `WbPrimed.chainOfContR`): same agents, labels and kinds, configurations related by
  `WbPrimed.cfgRel`; hence the SAME issuing-pc log (`WbPrimed.recPcLogRel`).
* §3 — (a3)'s step obligation on the primed record gives the pf half of the interface over the
  primed log (`WbPrimed.relPcWCrelOfStepsW`).
* §4 — the composition: (a1) `RelSiteProv.relProvExport σ (recPcLog r)` and (a3) on the primed
  record give `relSiteWCrel σ` of the primed log (`WbPrimed.relSiteWCrelPrimed`).

Lean-only (no Rocq counterpart); every name is file-qualified (`WbPrimed.*`).
-/
import Weak.WbPrimed
import Weak.RelSiteProvPc

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open MachOfPf RelSiteProvPc PfStepTsoMem
open Wlabel

/-! ## 1. W2's memory relation and W11-C's realized read, over a re-tagged log -/

theorem WbPrimed.tidsRetag (f : Nat → WmClass) (log : List Wmsg) :
    (retagLog f log).map Wmsg.wmTid = log.map Wmsg.wmTid := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map, retagLogLookup]
  cases log[i]? <;> rfl

theorem WbPrimed.histOfRetag (f : Nat → WmClass) (img : Image) (log : List Wmsg) (a : Int) :
    TsoOfPf.histOf img (retagLog f log) a = TsoOfPf.histOf img log a := by
  unfold TsoOfPf.histOf
  rw [retagLogLength]
  congr 2
  apply filterMapCongr
  intro i _
  rw [retagLogLookup]
  cases log[i]? <;> rfl

/-- **W2's memory relation does not see classes.** -/
theorem WbPrimed.rmemRetag {P D : Type} (c c' : Wpcfg P D) (f : Nat → WmClass)
    (st : List (Nat × Wlabel)) (σ : MState) :
    c'.pcImg = c.pcImg → c'.pcLog = retagLog f c.pcLog → rmem c st σ → rmem c' st σ := by
  rintro himg hlog ⟨⟨htid, hle⟩, hi, ⟨hh1, hh2⟩, hres⟩
  refine ⟨⟨by rw [hlog, WbPrimed.tidsRetag]; exact htid, hle⟩, by rw [himg]; exact hi,
    ⟨fun pa hpa => ?_, fun pa hpa => ?_⟩, hres⟩
  · rw [hh1 pa hpa, hlog, himg, WbPrimed.histOfRetag]
  · exact hh2 pa hpa

/-- **W11-C's realized read at the primed configuration.**  Every conjunct but the release-site
fact is read off the registered configuration; the release-site fact is the PRIMED log's. -/
theorem WbPrimed.readAtPrimed (log' : List Wmsg) (c c' : Wpcfg Pexv6 Efab)
    (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg) :
    rmem c st σ → WbPrimed.cfgRel c c' → Xv6.AccessDiscipline.xv6AccessDisc σ →
    relSiteWCrel σ c'.pcLog → c'.pcLog <+: log' → c.pcLog[p]? = some m →
    (msgByte m (paZ pa)).isSome → inRam pa 1 → (σ.hr j).coh pa = p + 1 →
    ∃ m', c'.pcLog[p]? = some m' ∧ m'.wmPa = m.wmPa ∧ m'.wmData = m.wmData ∧
      m'.wmTid = m.wmTid ∧ readAt log' c' st σ j pa p m' := by
  rintro hR hrel hD hsite hpre hp hv hram hcoh
  obtain ⟨himg, -, ⟨f, hlog⟩, -⟩ := hrel
  have hp' := retagLogLookupSome f c.pcLog p m hp
  rw [← hlog] at hp'
  refine ⟨_, hp', rfl, rfl, rfl, WbPrimed.rmemRetag c c' f st σ himg hlog hR, hD, hsite, hpre, hp',
    ?_, hram, hcoh⟩
  rw [retagMsgByte]; exact hv

/-- **W11-C's refutation over the primed log** (`ownedUnpubRefuted` at the primed
configuration). -/
theorem WbPrimed.ownedUnpubRefutedPrimed (log' : List Wmsg) (c c' : Wpcfg Pexv6 Efab)
    (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg) (i : Nat)
    (hR : rmem c st σ) (hrel : WbPrimed.cfgRel c c') (hD : Xv6.AccessDiscipline.xv6AccessDisc σ)
    (hsite : relSiteWCrel σ c'.pcLog) (hpre : c'.pcLog <+: log') (hp : c.pcLog[p]? = some m)
    (hv : (msgByte m (paZ pa)).isSome) (hram : inRam pa 1) (hcoh : (σ.hr j).coh pa = p + 1)
    (hi : m.wmTid = some i) (hiN : i < NCPU) (hij : i ≠ hartAgent j) :
    ∃ m', c'.pcLog[p]? = some m' ∧ m'.wmTid = m.wmTid ∧
      (benignAt σ pa (p + 1) ∨ ¬ (m'.wmAk = .WCplain ∧ ¬ wpublished log' m'.wmTid p)) := by
  obtain ⟨m', hp', -, -, htid, hrd⟩ :=
    WbPrimed.readAtPrimed log' c c' st σ j pa p m hR hrel hD hsite hpre hp hv hram hcoh
  exact ⟨m', hp', htid, ownedUnpubRefuted log' c' st σ j pa p m' i hrd (by rw [htid]; exact hi) hiN hij⟩

/-! ## 2. The primed run, recorded along W4's record -/

/-- **A primed run, recorded** (the primed twin of the `pre`/agent/label/kind skeleton of
`MachOfPf.contRC`). -/
inductive WbPrimed.chainW : Wpcfg Pexv6 Efab → List PfRec → Wpcfg Pexv6 Efab → Prop where
  | nil (c : Wpcfg Pexv6 Efab) : WbPrimed.chainW c [] c
  | cons (c c' : Wpcfg Pexv6 Efab) (i : Nat) (l : Wlabel) (k : SKind) (r : List PfRec)
      (cN : Wpcfg Pexv6 Efab) :
      WbPrimed.pfStepEvW i l c c' → WbPrimed.chainW c' r cN →
      WbPrimed.chainW c (⟨c, i, l, k⟩ :: r) cN

/-- Two record entries correspond: same agent, label and kind; related pre-configurations. -/
def WbPrimed.recRel (x y : PfRec) : Prop :=
  y.ag = x.ag ∧ y.lb = x.lb ∧ y.kind = x.kind ∧ WbPrimed.cfgRel x.pre y.pre

/-- **THE PRIMED RECORD** of a registered record: every registered run W4 records has a primed
twin, step for step. -/
theorem WbPrimed.chainOfContR {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : contRC fok fcutT c st r cN) :
    ∀ c', WbPrimed.cfgRel c c' → ∃ (r' : List PfRec) (cN' : Wpcfg Pexv6 Efab),
      WbPrimed.chainW c' r' cN' ∧ WbPrimed.cfgRel cN cN' ∧ List.Forall₂ WbPrimed.recRel r r' := by
  induction h with
  | nil c st => intro c' hR; exact ⟨[], c', .nil c', hR, .nil⟩
  | cons c c1 st i l k r cN hs _ _ _ _ _ ih =>
    intro c' hR
    obtain ⟨c1', hs', hR1⟩ := WbPrimed.stepFwd pstepEv pclsEv WbPrimed.pwbEv i l c c1 c' hs hR
    obtain ⟨r', cN', hc, hRN, hF⟩ := ih c1' hR1
    exact ⟨⟨c', i, l, k⟩ :: r', cN', .cons c' c1' i l k r' cN' hs' hc, hRN,
      .cons ⟨rfl, rfl, rfl, hR⟩ hF⟩

/-- Corresponding entries issue at the same pc. -/
theorem WbPrimed.recPcRel (x y : PfRec) (h : WbPrimed.recRel x y) : recPc y = recPc x := by
  obtain ⟨hag, hlb, -, hR⟩ := h
  have hlen := hR.2.2.2.1
  unfold recPc
  rw [hlb, hag]
  cases ha : lbAppends x.lb
  · rfl
  · simp only [if_true]
    cases hs : lbStore x.lb
    · rfl
    simp only [if_true]
    cases hx : x.pre.pcAgs[x.ag]? with
    | none =>
      have : y.pre.pcAgs[x.ag]? = none := by
        rw [List.getElem?_eq_none_iff] at hx ⊢
        omega
      rw [this]
    | some ag =>
      obtain ⟨ag', h1, h2, -, -⟩ := hR.2.2.2.2 x.ag ag hx
      rw [h1]
      simp only [Option.elim, h2]

/-- **The same issuing-pc log.** -/
theorem WbPrimed.recPcLogRel {r r' : List PfRec} (h : List.Forall₂ WbPrimed.recRel r r') :
    recPcLog r' = recPcLog r := by
  induction h with
  | nil => rfl
  | cons hxy _ ih =>
    rw [recPcLogCons, recPcLogCons, WbPrimed.recPcRel _ _ hxy, ih]

/-! ## 3. (a3) on the primed record ⇒ the pf half over the primed log -/

/-- A primed step's log effect (`RelSiteProvPc.stepLog`'s twin). -/
theorem WbPrimed.stepLogW {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (pwb : P → Bool) (i : Nat) (l : Wlabel)
    (c c' : Wpcfg P D) (h : WbPrimed.wpPfStepW pstep pcls pwb i l c c') :
    (lbAppends l = false → c'.pcLog = c.pcLog) ∧
    (lbAppends l = true → ∃ (ag : Wpagent P) (m : Wmsg), c.pcAgs[i]? = some ag ∧
      c'.pcLog = c.pcLog ++ [m] ∧ m.wmAk = pcls ag.paSt l ag.paWs) := by
  cases h with
  | PFStore _ ag _ _ _ _ _ k _ _ hlk _ _ hk =>
    exact ⟨(fun h => by cases h), fun _ => ⟨ag, _, hlk, rfl, hk⟩⟩
  | PFRmw _ ag _ _ _ _ _ _ _ k _ _ hlk _ _ _ _ _ hk =>
    exact ⟨(fun h => by cases h), fun _ => ⟨ag, _, hlk, rfl, hk⟩⟩
  | PFExStore _ ag _ _ _ _ _ k _ _ _ hlk _ _ _ _ _ _ hk =>
    exact ⟨(fun h => by cases h), fun _ => ⟨ag, _, hlk, rfl, hk⟩⟩
  | PFSilent => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFLoad => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFFence => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFDev => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFRegW => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFCtrl => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFInstr => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFExLoad => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFIFetch => exact ⟨fun _ => rfl, fun h => by cases h⟩

theorem WbPrimed.chainPrefix {c : Wpcfg Pexv6 Efab} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : WbPrimed.chainW c r cN) : c.pcLog <+: cN.pcLog := by
  induction h with
  | nil => exact List.prefix_refl _
  | cons c c' i l k r cN hs _ ih =>
    refine List.IsPrefix.trans ?_ ih
    obtain ⟨h0, h1⟩ := WbPrimed.stepLogW _ _ _ _ _ _ _ hs
    cases ha : lbAppends l
    · rw [h0 ha]; exact List.prefix_refl _
    · obtain ⟨_, m, _, he, _⟩ := h1 ha
      rw [he]; exact List.prefix_append _ _

theorem WbPrimed.relPcWCrelOffW {c : Wpcfg Pexv6 Efab} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : WbPrimed.chainW c r cN) (hob : relStepWCrel r) :
    ∀ (q : Nat) (mq : Wmsg) (pc : Int), cN.pcLog[c.pcLog.length + q]? = some mq →
      (recPcLog r)[q]? = some pc → pc ∈ releasePcs → mq.wmAk = .WCrel := by
  induction h with
  | nil => intro q mq pc _ hp; simp [recPcLog] at hp
  | cons c c' i l k r cN hs hr ih =>
    intro q mq pc hm hp hrel
    have hob' : relStepWCrel r := fun x hx => hob x (List.mem_cons_of_mem _ hx)
    obtain ⟨h0, h1⟩ := WbPrimed.stepLogW _ _ _ _ _ _ _ hs
    rw [recPcLogCons] at hp
    cases ha : lbAppends l
    · have hp' : (recPcLog r)[q]? = some pc := by simpa [recPc, ha] using hp
      exact ih hob' q mq pc (by rw [h0 ha]; exact hm) hp' hrel
    · obtain ⟨ag, m, hlk, he, hk⟩ := h1 ha
      have hpre := WbPrimed.chainPrefix hr
      cases q with
      | zero =>
        have hpc : pc = if lbStore l then (c.pcAgs[i]?).elim (-1) (fun ag => pcOfSt ag.paSt)
            else -1 := by
          simpa [recPc, ha] using hp.symm
        cases hst : lbStore l with
        | false => simp [hst] at hpc; exact absurd (hpc ▸ hrel) negOneNotRelease
        | true =>
        rw [hst, if_pos rfl, hlk] at hpc
        simp only [Option.elim] at hpc
        have hm' : cN.pcLog[c.pcLog.length]? = some m := by
          rw [he] at hpre
          obtain ⟨tl, htl⟩ := hpre
          rw [← htl]
          simp
        rw [Nat.add_zero, hm'] at hm
        cases hm
        rw [hk]
        exact hob ⟨c, i, l, k⟩ (List.mem_cons_self) hst ag hlk (hpc ▸ hrel)
      | succ q =>
        have hp' : (recPcLog r)[q]? = some pc := by simpa [recPc, ha] using hp
        have hlen : c'.pcLog.length = c.pcLog.length + 1 := by rw [he]; simp
        exact ih hob' q mq pc (by rw [hlen, Nat.add_right_comm]; exact hm) hp' hrel

/-- **(a3) reduced to single PRIMED steps.** -/
theorem WbPrimed.relPcWCrelOfStepsW {c : Wpcfg Pexv6 Efab} {r : List PfRec}
    {cN : Wpcfg Pexv6 Efab} (h : WbPrimed.chainW c r cN) (h0 : c.pcLog = [])
    (hob : relStepWCrel r) : RelSiteProv.relPcWCrel cN.pcLog (recPcLog r) := by
  intro q mq pc hm hp hrel
  exact WbPrimed.relPcWCrelOffW h hob q mq pc (by rw [h0]; simpa using hm) hp hrel

/-! ## 4. The composition -/

/-- **THE RELEASE-SITE FACT OF THE PRIMED LOG**, from (a1) at the registered record's issuing-pc
log (the same as the primed record's) and (a3) on the primed record. -/
theorem WbPrimed.relSiteWCrelPrimed (σ : MState) (r r' : List PfRec) (c' cN' : Wpcfg Pexv6 Efab)
    (hc : WbPrimed.chainW c' r' cN') (h0 : c'.pcLog = []) (hF : List.Forall₂ WbPrimed.recRel r r')
    (ha1 : RelSiteProv.relProvExport σ (recPcLog r)) (ha3 : relStepWCrel r') :
    relSiteWCrel σ cN'.pcLog := by
  refine RelSiteProv.relSiteWCrelOfProv σ _ _ ha1 ?_
  rw [← WbPrimed.recPcLogRel hF]
  exact WbPrimed.relPcWCrelOfStepsW hc h0 ha3

end Weak
