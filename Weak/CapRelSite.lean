/-
Weak: **`relSiteWCrel` at the end of a W4 run record, from the machine's pc record** (W11-C2′
[OWN.82]; mcslrec (2)).  Lean-only, no Rocq twin.

The release-site fact `relSiteWCrel σ log` (`Weak/RvwmoXv6Adequacy.lean`) is composed from
* (a1) the MachCSL export `relProvAt` (`Xv6.AccessDiscipline.xv6AccessDisc`'s ninth conjunct), read
  as `RelSiteProv.relProvExport σ (RelSiteProvExp.pcLogOf σ)` (`RelSiteProvExp.relProvExportOf`);
* (a3) the arming fact `WbPrimed.relArmed r` on W4's record (`relArmedOf`, `Weak/PinRelArmAsm.lean`);
* the composition `WbPrimed.relSiteWCrelArmed` (the primed twin of the record);
* and (a2), the ONE link between the two pc logs, stated here exactly and NAMED:
  `CapRelSite.pcLogAgree r σ` -- the record's issuing-pc log (`RelSiteProvPc.recPcLog r`, the pf
  side) IS the machine's (`σ.pcAt (q + 1)` at position `q`).  `RelSiteProvPc.recPcLockstep` proves
  its per-store half (the recorded pc is the `PC` of the simulating MachCSL hart at the store); the
  remaining step is that the simulating MachCSL store at position `q + 1` is that store (W4's
  log-order lock-step, `rmem`'s `R-log`), and that later steps keep old positions' pcs
  (`MachCSL.relPc_storeOld`).

Spec: FAITHFUL (proof organisation; the pc record is the Sail `PC` at each `memWrite`).
Names: `CapRelSite.*`.
-/
import Weak.RelSiteProvExp
import Weak.WbPrimedArm

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open MachOfPf RelSiteProvPc

/-- **(a2) NAMED, exactly**: the record's issuing-pc log is the machine's per-store pc record. -/
def CapRelSite.pcLogAgree (r : List PfRec) (σ : MState) : Prop :=
  recPcLog r = RelSiteProvExp.pcLogOf σ

/-- (a1) at the record's pc log, given (a2). -/
theorem CapRelSite.provAtRec (r : List PfRec) (σ : MState) (hD : Xv6.AccessDiscipline.xv6AccessDisc σ)
    (ha2 : CapRelSite.pcLogAgree r σ) : RelSiteProv.relProvExport σ (recPcLog r) := by
  rw [ha2]
  exact RelSiteProvExp.relProvExportOf σ hD

/-- **`relSiteWCrel` at the end of a W4 record** (the primed twin's final log), from the export,
(a2) and (a3). -/
theorem CapRelSite.relSiteWCrelOf {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : contRC fok fcutT c st r cN) (h0 : c.pcLog = []) (σ : MState)
    (hD : Xv6.AccessDiscipline.xv6AccessDisc σ) (ha2 : CapRelSite.pcLogAgree r σ)
    (ha3 : WbPrimed.relArmed r) :
    ∃ cN', WbPrimed.cfgRel cN cN' ∧ relSiteWCrel σ cN'.pcLog :=
  WbPrimed.relSiteWCrelArmed h h0 σ (CapRelSite.provAtRec r σ hD ha2) ha3

end Weak
