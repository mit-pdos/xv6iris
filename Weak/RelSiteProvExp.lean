/-
Weak: **(a1) of `RelSiteProv`, discharged** (mcslrec (2) [OWN.82] (a1); Q-MCSL2-DYN ruled (i)):
the MachCSL provenance export `RelSiteProv.relProvExport σ pl` from W8's access-discipline export
`Xv6.AccessDiscipline.xv6AccessDisc` (its ninth conjunct, `relProvAt`), at the machine's own
per-store pc record (`MState.pcAt`).

* `RelSiteProvExp.pcLogOf σ` — the issuing-pc log of `σ`: one entry per store position `q + 1`
  (`σ.pcAt (q + 1)`: the storing hart's `PC` at a PLAIN store, `-1` at an exclusive / AMO write and
  at the disk), aligned with `σ.log`.
* `RelSiteProvExp.releasePcsEq` — Weak's `releasePcs` IS the machine record's `KernelRsv.relPcs`
  (the Xv6 copy `Xv6.xv6RelPcs`).
* `RelSiteProvExp.relProvExportOf` — `xv6AccessDisc σ → RelSiteProv.relProvExport σ (pcLogOf σ)`.

No primed twin of `RvwmoXv6Adequacy.relEntAt` is needed: its hop arm is over
`Xv6.AccessDiscipline.hopByteAt`, whose dynamic arm now carries the pc clause the winning AMO's hop
certificate records (`MachCSL.relBelowOk`, the ruled (i)), so `relEntAt` IS the export's
`Xv6.AccessDiscipline.relEntAtX` (by definition).

Lean-only (no Rocq counterpart); every name is file-qualified (`RelSiteProvExp.*`).
-/
import Weak.RelSiteProv

namespace Weak

open MachCSL

/-- **The issuing-pc log of `σ`** (mcslrec (2) [OWN.82] (a1)): the machine's per-store pc
record, one entry per store position, in log order. -/
def RelSiteProvExp.pcLogOf (σ : MState) : List Int :=
  (List.range σ.log.length).map (fun q => σ.pcAt (q + 1))

/-- Weak's release sites are the machine record's (the Xv6 copy). -/
theorem RelSiteProvExp.releasePcsEq : releasePcs = (KernelRsv.relPcs : List Int) := rfl

/-- `RvwmoXv6Adequacy.relEntAt` is the export's `relEntAtX`. -/
theorem RelSiteProvExp.relEntAtEq (σ : MState) (r : Nat) :
    RvwmoXv6Adequacy.relEntAt σ r ↔ Xv6.AccessDiscipline.relEntAtX σ r := Iff.rfl

/-- **(a1), discharged**: W8's export gives the provenance export at the machine's own pc log. -/
theorem RelSiteProvExp.relProvExportOf (σ : MState) (h : Xv6.AccessDiscipline.xv6AccessDisc σ) :
    RelSiteProv.relProvExport σ (RelSiteProvExp.pcLogOf σ) := by
  refine ⟨by simp [RelSiteProvExp.pcLogOf], fun q hq => ?_⟩
  obtain ⟨hle, hpc⟩ := h.2.2.2.2.2.2.2.2.1 (q + 1) (by omega) ((RelSiteProvExp.relEntAtEq σ (q + 1)).1 hq)
  have hq' : q < σ.log.length := by simp only [MState.top] at hle; omega
  refine ⟨σ.pcAt (q + 1), ?_, by rw [RelSiteProvExp.releasePcsEq]; exact hpc⟩
  simp [RelSiteProvExp.pcLogOf, List.getElem?_range hq']

end Weak
