/-
Weak: **(c) [OWN.100], increment 4b-i — the twin promise-free pf machine** (`PROGRESS-W10N2p.md`).
Lean-only, no Rocq twin.

**`SilPf.wpPfStepS`**: the registered `wpPfStep`, or a SILENT exclusive store (`exStoreSilent`): the
`LExStore` of a reservation whose window is clean up to `q` (`exclOkTs … (q + 1)`), whose bytes equal the
bytes at the reservation's timestamps, `q` passing the write's ordering bounds (coherence, the
dependency bound `SilCand.depView` — PARM's exclusive-store fulfil pre-view — and `SilCand.ownExcl`), not `rl` — the agent's views move as a store at `q` with the read/write-ordering views
raised (`SilCand.aqRaise`), NO message.  `SilPf.wpPfRunS`, and the embedding of registered runs.

Spec: FAITHFUL (the pf-level form of the silent AMO, `SilCand.silentOk` / `SilLang.silentWrite`).
-/
import Weak.SilEpf

namespace Weak

open MachCSL MachCSL.Stdpp

section twin

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

inductive SilPf.wpPfStepS (i : Nat) : Wlabel → Wpcfg P D → Wpcfg P D → Prop
  | old (l : Wlabel) (c c' : Wpcfg P D) : wpPfStep pstep pcls i l c c' → SilPf.wpPfStepS i l c c'
  | exStoreSilent (cfg : Wpcfg P D) (ag : Wpagent P) (base : Int) (data : List (BitVec 8))
      (asrc vsrc : List Dsrc) (R : Wresv) (q : Nat) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LExStore false base data asrc vsrc) st' d' →
      data ≠ [] →
      ag.paWs.wRes = some R → R.rvBase = base → R.rvTs.length = data.length →
      (∀ (j t : Nat), R.rvTs[j]? = some t →
        t ≤ q ∧ logByte cfg.pcImg cfg.pcLog t (base + (j : Int)) = data[j]?) →
      exclOkTs cfg.pcLog i base R.rvTs (q + 1) →
      q ≤ cfg.pcLog.length →
      (∀ j, j < data.length → coh ag.paWs (base + (j : Int)) ≤ q) →
      SilCand.depView ag.paWs asrc vsrc ≤ q → SilCand.ownExcl cfg.pcLog i ≤ q →
      SilPf.wpPfStepS i (.LExStore false base data asrc vsrc) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st',
           storePostRunD (SilCand.aqRaise ag.paWs q) false (srcsView ag.paWs asrc)
             (srcsView ag.paWs vsrc) base data.length q,
           ag.paProm⟩⟩

def SilPf.wpPfRunS (c c' : Wpcfg P D) : Prop := ∃ i l, SilPf.wpPfStepS pstep pcls i l c c'

/-- Every registered pf run is a twin pf run. -/
theorem SilPf.rtcOfOld (c c' : Wpcfg P D) :
    rtc (wpPfRun pstep pcls) c c' → rtc (SilPf.wpPfRunS pstep pcls) c c' := by
  intro h
  induction h with
  | refl => exact rtc_refl _
  | tail _ hs ih =>
    obtain ⟨i, l, hs⟩ := hs
    exact rtc_r ih ⟨i, l, .old l _ _ hs⟩

/-- A twin step keeps the image and keeps or extends the log. -/
theorem SilPf.stepSImg (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    SilPf.wpPfStepS pstep pcls i l c c' → c'.pcImg = c.pcImg := by
  intro h
  cases h with
  | old l c c' h => cases h <;> rfl
  | exStoreSilent => rfl

end twin

end Weak
