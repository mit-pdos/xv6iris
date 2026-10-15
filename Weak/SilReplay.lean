/-
Weak: **(c) [OWN.100], increment 4c-iii — the twin program-carrying replay** (`PROGRESS-W10N2p.md`).
Lean-only, no Rocq twin.

**`SilReplay.progOk`**: the twin of the shaped conformance predicate (`execProgOk'SC`) over a twin
candidate's states `SilCand.stAt`: per step the program's leading administrative star (its fetches at
their view-0 check `ifetchOk … 0`, which M2's cut form `fcutM2` implies), then an ORDINARY step realized
by one label (`lblRealizes`) or a PAIR (`lblRealizesPair`: `LExLoad`, a fetch-free star, `LExStore`); a
SILENT step only by the pair.  No shadow, cut or single-copy clauses (the twin replay needs none: it
produces a pf run, not the TSO projection).

**`SilReplay.prefixRun` / `SilReplay.run`**: every prefix of a valid twin candidate (`SilCand.validS`)
supplied by `progOk` is matched (`cfgMatchd`) by a twin pf run (`rtc SilPf.wpPfRunS`) from the booted
configuration, at the supplied program states and fabric.

Spec: FAITHFUL (the registered replay's program data at the twin states; the silent step is the pair
whose write half is silent, `SilPair.pairSimS`).
-/
import Weak.SilPair

namespace Weak

open MachCSL MachCSL.Stdpp

section twin

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- **THE TWIN PROGRAM DATA.** -/
def SilReplay.progOk (pst : Nat → List P) (dv : Nat → D) (c : SilCand.CandS) : Prop :=
  ∀ (k : Nat) (s : Estep), c.tr[k]? = some s →
    ∃ (p pa : P) (da : D) (p' : P) (ls : List Wlabel),
      (pst k)[s.esAg]? = some p ∧
      pst (k + 1) = (pst k).set s.esAg p' ∧
      admRunG pstep true p (dv k) ls pa da ∧
      (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
        ifetchOk (SilCand.stAt c k).msImg (SilCand.stAt c k).msLog 0 base tvs) ∧
      ((c.sil.getD k none = none ∧ ∃ l, lblRealizes pcls pa (SilCand.stAt c k) s.esAg s.esLb l ∧
          pstep pa da l p' (dv (k + 1)))
       ∨ (∃ (pm : P) (dm : D) (ls2 : List Wlabel) (pm2 : P) (dm2 : D) (l1 l2 : Wlabel),
            lblRealizesPair pcls pa pm2 (SilCand.stAt c k) s.esAg s.esLb l1 l2 ∧
            pstep pa da l1 pm dm ∧
            admRunG pstep false pm dm ls2 pm2 dm2 ∧
            pstep pm2 dm2 l2 p' (dv (k + 1))))

theorem SilReplay.stAtSucc (c : SilCand.CandS) (k : Nat) (s : Estep) :
    c.tr[k]? = some s →
    SilCand.stAt c (k + 1) = SilCand.nextS (SilCand.stAt c k) s (c.sil.getD k none) := by
  intro hs
  show (match c.tr[k]? with
    | some s => SilCand.nextS (SilCand.stAt c k) s (c.sil.getD k none)
    | none => SilCand.stAt c k) = _
  rw [hs]

theorem SilReplay.nextSNone (S : Mstate) (s : Estep) :
    SilCand.nextS S s none = mnext S s.esAg s.esLb := by
  unfold SilCand.nextS
  cases s.esLb <;> rfl

/-- **THE TWIN REPLAY, prefix form.** -/
theorem SilReplay.prefixRun (pst : Nat → List P) (dv : Nat → D) (c : SilCand.CandS) (n : Nat) :
    pclsEqr pcls → SilCand.validS c → SilReplay.progOk pstep pcls pst dv c →
    n ≤ c.tr.length →
    ∃ cf : Wpcfg P D,
      rtc (SilPf.wpPfRunS pstep pcls) (wpInit c.img (dv 0) (pst 0)) cf ∧
      cf.pcAgs.map Wpagent.paSt = pst n ∧ cf.pcDev = dv n ∧
      cfgMatchd cf (SilCand.stAt c n) := by
  intro hce hv hpr
  induction n with
  | zero =>
    intro _
    refine ⟨wpInit c.img (dv 0) (pst 0), rtc_refl _,
      by simp [wpInit, List.map_map, Function.comp_def], rfl, ⟨rfl, rfl, ?_⟩⟩
    intro i ag hlk
    simp only [wpInit, List.getElem?_map] at hlk
    cases hp : (pst 0)[i]? with
    | none => rw [hp] at hlk; cases hlk
    | some p =>
      rw [hp] at hlk; injection hlk with hlk; subst hlk
      exact wsEqrRefl _
  | succ n ih =>
    intro hn
    obtain ⟨cf, hrun, hst, hdev, hm⟩ := ih (by omega)
    obtain ⟨s, hs⟩ : ∃ s, c.tr[n]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hnx := SilReplay.stAtSucc c n s hs
    obtain ⟨hold, hsil⟩ := hv n s hs
    obtain ⟨p, pa, da, p', ls, hp, hnext, hstar, hfetch, hsup⟩ := hpr n s hs
    have hex : ∃ ag, cf.pcAgs[s.esAg]? = some ag ∧ ag.paSt = p := by
      rw [← hst, List.getElem?_map] at hp
      cases hag : cf.pcAgs[s.esAg]? with
      | none => rw [hag] at hp; cases hp
      | some ag => rw [hag] at hp; injection hp with hp; exact ⟨ag, rfl, hp⟩
    obtain ⟨ag, hag, hagp⟩ := hex
    obtain ⟨c0, ag0, hrun0, heq0, hd0, hlk0, hs0, _, _, hfm0⟩ :=
      SilPair.admRunRtc pstep pcls true p (dv n) ls pa da hstar cf s.esAg ag hag hagp hdev
        (fun b t hmem => by rw [← hm.1, ← hm.2.1]; exact hfetch b t hmem)
    have hm0 : cfgMatchd c0 (SilCand.stAt c n) := cfgEqrMatchd _ _ _ heq0 hm
    have hrunA : rtc (SilPf.wpPfRunS pstep pcls) (wpInit c.img (dv 0) (pst 0)) c0 :=
      rtc_transitive hrun (SilPf.rtcOfOld pstep pcls _ _ hrun0)
    have hfin : ∀ c2 : Wpcfg P D,
        rtc (SilPf.wpPfRunS pstep pcls) c0 c2 →
        c2.pcAgs.map Wpagent.paSt = (c0.pcAgs.map Wpagent.paSt).set s.esAg p' →
        c2.pcDev = dv (n + 1) → cfgMatchd c2 (SilCand.stAt c (n + 1)) →
        ∃ cf : Wpcfg P D,
          rtc (SilPf.wpPfRunS pstep pcls) (wpInit c.img (dv 0) (pst 0)) cf ∧
          cf.pcAgs.map Wpagent.paSt = pst (n + 1) ∧ cf.pcDev = dv (n + 1) ∧
          cfgMatchd cf (SilCand.stAt c (n + 1)) := by
      intro c2 hr2 hst2 hdev2 hm2
      refine ⟨c2, rtc_transitive hrunA hr2, ?_, hdev2, hm2⟩
      rw [hst2, hfm0, hst, list_insert_insert, ← hnext]
    cases ho : c.sil.getD n none with
    | none =>
      have hms : mstep (SilCand.stAt c n) s.esAg s.esLb (SilCand.stAt c (n + 1)) := by
        rw [hnx, ho, SilReplay.nextSNone]
        exact mstepOkStep _ _ _ (hold ho)
      rcases hsup with ⟨-, l, hre, hps⟩ | ⟨pm, dm, ls2, pm2, dm2, l1, l2, hre, hps1, hstar2, hps2⟩
      · obtain ⟨c2, hstep, hm2, hst2, hdev2⟩ :=
          mstepWpPfStepProg pstep pcls (SilCand.stAt c n) (SilCand.stAt c (n + 1)) s.esAg s.esLb
            c0 ag0 pa p' l (dv (n + 1)) hce hm0 hlk0 hs0 hre (by rw [hd0]; exact hps) hms
        exact hfin c2 (rtc_once ⟨s.esAg, l, .old l _ _ hstep⟩) hst2 hdev2 hm2
      · obtain ⟨c2, hstepP, -, hm2, hst2, hdev2⟩ :=
          mstepWpPfStepPairS (pstepPin c0.pcImg pstep) pcls (fun _ _ _ _ _ => True)
            (SilCand.stAt c n) (SilCand.stAt c (n + 1)) s.esAg s.esLb c0 ag0 pa pm pm2 p' l1 l2
            ls2 dm dm2 (dv (n + 1)) hce (pstepPinPinned _ _) hm0 hlk0 hs0 hre
            ⟨by rw [hd0]; exact hps1, by
              obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := hre; trivial⟩
            (PfRunUnpinned.admRunGPin pstep c0.pcImg _ _ _ _ _ hstar2)
            ⟨hps2, by obtain ⟨_, _, _, _, _, _, _, _, -, rfl, -⟩ := hre; trivial⟩ hms
        exact hfin c2 (SilPf.rtcOfOld pstep pcls _ _
          (pfRunSRtc pstep pcls _ _ _ _ (pfRunSPinSub pstep pcls _ c0.pcImg _ _ _ hstepP)))
          hst2 hdev2 hm2
    | some q =>
      obtain ⟨aq, base, ts, rvs, wvs, kc, hl, hok⟩ := hsil q ho
      have hnx' : SilCand.stAt c (n + 1)
          = SilCand.silentNext (SilCand.stAt c n) s.esAg aq base ts wvs q := by
        rw [hnx, ho]; unfold SilCand.nextS; rw [hl]
      rcases hsup with ⟨hn0, -⟩ | ⟨pm, dm, ls2, pm2, dm2, l1, l2, hre, hps1, hstar2, hps2⟩
      · rw [ho] at hn0; cases hn0
      · rw [hl] at hre
        obtain ⟨c2, hr2, hm2, hst2, hdev2⟩ :=
          SilPair.pairSimS pstep pcls (SilCand.stAt c n) s.esAg c0 ag0 pm pm2 p' l1 l2 ls2 dm dm2
            (dv (n + 1)) aq base ts rvs wvs kc q hm0 hlk0 (by rw [hs0]; exact hre)
            (by rw [hs0, hd0]; exact hps1) hstar2 hps2 hok
        exact hfin c2 hr2 hst2 hdev2 (by rw [hnx']; exact hm2)

/-- **THE TWIN REPLAY**: the whole twin candidate. -/
theorem SilReplay.run (pst : Nat → List P) (dv : Nat → D) (c : SilCand.CandS) :
    pclsEqr pcls → SilCand.validS c → SilReplay.progOk pstep pcls pst dv c →
    ∃ cf : Wpcfg P D,
      rtc (SilPf.wpPfRunS pstep pcls) (wpInit c.img (dv 0) (pst 0)) cf ∧
      cf.pcAgs.map Wpagent.paSt = pst c.tr.length ∧ cf.pcDev = dv c.tr.length ∧
      cfgMatchd cf (SilCand.stAt c c.tr.length) :=
  fun hce hv hpr => SilReplay.prefixRun pstep pcls pst dv c c.tr.length hce hv hpr (Nat.le_refl _)

end twin

section run

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **THE TWIN ERASED RUN** (`runErasedZ`'s twin): a valid twin candidate supplied by `progOk` at the
booted state is an erased run of the TWIN thread pool (`SilLang.epowerForkS`) ending at the log of the
candidate's projection.  The fetch-view premise is `runErasedZ`'s, at the twin machine. -/
theorem SilReplay.runErased (gen : Nat) (σ0 : WGState) (c : SilCand.CandS) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) :
    freshEra gen σ0 →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    c.img = imgZ σ0.wgimg → pst 0 = epsInit σ0 → dv 0 = efInit σ0.wgdev →
    SilCand.validS c → SilReplay.progOk pstepEv pclsEv pst dv c →
    ∃ (t2 : List SilLang.EExprS) (σ2 : WGState),
      (SilLang.epowerForkS gen, σ0) -·->ₜₚ* (t2, σ2) ∧
      σ2.wglog = cdLog (SilCand.proj c) c.tr.length := by
  rintro ⟨hgen, hpow, hgen0, hlog, hws⟩ hcov himg hpst0 hdv0 hv hpr
  have hlive : ethreadLive σ0 gen := ⟨hpow, by rw [hgen0, hgen]⟩
  obtain ⟨cf, hrun, -, -, hm⟩ := SilReplay.run pstepEv pclsEv pst dv c pclsEvEqr hv hpr
  rw [himg, hpst0, hdv0, ← ecfgOfInit gen σ0 hlog hws] at hrun
  obtain ⟨P', σ', hr, heq⟩ := SilPf.wpPfRtcEpfRtcS (epInit gen) σ0 cf hlive hcov hrun
  refine ⟨SilEpf.wrap (epoolList P'), σ', SilEpf.epfRtcErasedS (epInit gen, σ0) (P', σ') hr, ?_⟩
  obtain ⟨-, hlg, -⟩ := hm
  rw [← ecfgOfLog P' σ', heq, ← hlg]
  exact ((SilCand.projLog c c.tr.length (Nat.le_refl _)).1).symm

end run

end Weak
