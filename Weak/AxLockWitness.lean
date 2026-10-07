/-
Weak: **satisfiability of `lockSliceSound''` on a concrete witness graph** (AxSL tier, lock
slice).

Rocq: `iris/AxLockWitness.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`lockSliceSound''` (`Weak/AxLockAdeq2.lean` §6) is a Prop-level implication with ~25 graph
hypotheses.  To certify they are jointly SATISFIABLE (so the theorem is not vacuous) this file
builds `race4` := `AxLockRace.race` WITH HART C REMOVED — the plain 4-event two-hart lock
handoff `[w_x; w_rel; acq; r_x]` — checks `rvwmoCatConsistent race4` with the computable checker
(`catConsistentBSound` + `decide +kernel`), discharges EVERY named hypothesis for it under a
local policy `witnessAxpol` (both fields `witnessPol`, the lob predecessor along the handoff
chain), and instantiates the theorem: `race4Sound` — `r_x`'s only legal source is `w_x`, value
`b1`.  The write order is w_x=1, w_rel=2, acq=3 (the RMW reads write index 2, `r_x` index 1).

**Fetches.** None: the graph has only store/fence/rmw/load labels.

**Ghost state.** `race4Sound` takes `[InvGpreS GF] [AxlogG GF Hent] [AxLockG GF]` as Rocq;
the allocation is `lockSliceSound''`'s own (`lockInitialAlloc`).

## Deviations from Rocq

1. VOCABULARY (as `Weak/AxLock3.lean` deviation 2): `gd_g GD` ↦ `GD.gdG`; `Z` ↦ `Int`; `vmr` /
   `vm_compute` ↦ `decide +kernel` / `rfl`; `≡ₚ` ↦ `List.Perm`; `{[a; b]}` ↦
   `({a} : GSet Geid) ∪ {b}`; `Lr` ↦ `lr`, `xr` ↦ `AxLockRace.xr`; Rocq's `Local Notation
   B0/B1` ↦ `b0`/`b1` directly.
2. The policy: Rocq's global `Instance witness_axpol` ↦ a plain `def witnessAxpol : Axpol`,
   passed explicitly (`(self := witnessAxpol)`, `@lockSliceSound'' GF _ witnessAxpol …`), so it
   never competes with `AxProtInst.axprotPol` in instance resolution.
3. NAMES: camelCase, Rocq's `H…` lemma names lower-cased (as AxLock3). Duplicated Rocq names,
   file-qualified: `AxLockWitness.eWx`, `AxLockWitness.eRx` (also in AxLock3).

**Rocq → Lean name map.**  `race4` `race4`, `e_wx` `AxLockWitness.eWx`, `e_wrel` `eWrel`,
`e_acq` `eAcq`, `e_rx` `AxLockWitness.eRx`, `race4_cat` `race4Cat`, `witness_pol`
`witnessPol`, `witness_axpol` `witnessAxpol`, `Hspol_eq` `hspolEq`, `Hlobp_wx4` `hlobpWx4`,
`Hlobp_wrel4` `hlobpWrel4`, `Hlobp_acq4` `hlobpAcq4`, `Hlobp_rx4` `hlobpRx4`, `Hspol_wx4`
`hspolWx4`, `Hspol_wrel4` `hspolWrel4`, `Hspol_acq4` `hspolAcq4`, `Hspol_rx4` `hspolRx4`,
`Hpol4` `hpol4`, `wr_single_addr` `wrSingleAddr`, `Hxl4` `hxl4`, `Hwx4` `hwx4`, `Hsingle_wx4`
`hsingleWx4`, `Hgd_wx4` `hgdWx4`, `Hfence4` `hfence4`, `Hwb04` `hwb04`, `Hsingle_rel4`
`hsingleRel4`, `Hrf4` `hrf4`, `Hwb14` `hwb14`, `Hsingle_acq4` `hsingleAcq4`, `Hval_acq4`
`hvalAcq4`, `Hacq_po4` `hacqPo4`, `Hnw4` `hnw4`, `Hrd4` `hrd4`, `Hgmo_perm4` `hgmoPerm4`,
`race4_sound` `race4Sound`.

**Not ported:** the `Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxLockAdeq2
import Weak.AxLockRace
import Weak.AxGraphDec
import Weak.AxGraphWit
import Weak.WeakLitmus

namespace Weak

open Iris MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. `race4`: `AxLockRace.race` with hart C removed -/

def race4 : Gdexec :=
  AxGraphWit.mkgd
    [[LStore false AxLockRace.xr [b1] .WCplain,
      LFence true true false true,
      LStore false lr [b0] .WCplain],
     [LRmw true false lr [2] [b0] [b1] .WCplain,
      LLoad false AxLockRace.xr [1] [b1]]]
    [(0, 0), (0, 2), (1, 0), (1, 1)]
    []

def AxLockWitness.eWx : Geid := (0, 0)
def eWrel : Geid := (0, 2)
def eAcq : Geid := (1, 0)
def AxLockWitness.eRx : Geid := (1, 1)

theorem race4Cat : rvwmoCatConsistent race4 :=
  catConsistentBSound _ (by decide +kernel)

/-! # 2. A local policy, tailored to `race4`'s four events -/

def witnessPol (_ : Gdexec) (e : Geid) : GSet Geid :=
  if e = eWrel then {AxLockWitness.eWx}
  else if e = eAcq then {eWrel}
  else if e = AxLockWitness.eRx then {eAcq}
  else ∅

@[reducible] def witnessAxpol : Axpol := ⟨witnessPol, witnessPol⟩

theorem hspolEq (GD : Gdexec) (e : Geid) :
    Axpol.sPol (self := witnessAxpol) GD e = Axpol.lobp (self := witnessAxpol) GD e := rfl

theorem hlobpWx4 : Axpol.lobp (self := witnessAxpol) race4 AxLockWitness.eWx = (∅ : GSet Geid) :=
  rfl

theorem hlobpWrel4 :
    Axpol.lobp (self := witnessAxpol) race4 eWrel = ({AxLockWitness.eWx} : GSet Geid) := rfl

theorem hlobpAcq4 : Axpol.lobp (self := witnessAxpol) race4 eAcq = ({eWrel} : GSet Geid) := rfl

theorem hlobpRx4 :
    Axpol.lobp (self := witnessAxpol) race4 AxLockWitness.eRx = ({eAcq} : GSet Geid) := rfl

theorem hspolWx4 :
    Axpol.sPol (self := witnessAxpol) race4 AxLockWitness.eWx ⊆ (∅ : GSet Geid) := by
  rw [hspolEq, hlobpWx4]

theorem hspolWrel4 :
    Axpol.sPol (self := witnessAxpol) race4 eWrel ⊆ ({AxLockWitness.eWx} : GSet Geid) := by
  rw [hspolEq, hlobpWrel4]

theorem hspolAcq4 :
    Axpol.sPol (self := witnessAxpol) race4 eAcq ⊆
      (({AxLockWitness.eWx} : GSet Geid) ∪ {eWrel}) := by
  rw [hspolEq, hlobpAcq4]
  intro e he
  exact elemOfUnionR he

theorem hspolRx4 :
    Axpol.sPol (self := witnessAxpol) race4 AxLockWitness.eRx ⊆
      ((({AxLockWitness.eWx} : GSet Geid) ∪ {eWrel}) ∪ {eAcq}) := by
  rw [hspolEq, hlobpRx4]
  intro e he
  exact elemOfUnionR he

theorem hpol4 : eWrel ∈ Axpol.sPol (self := witnessAxpol) race4 eAcq := by
  rw [hspolEq, hlobpAcq4]
  exact elemOfSingleton.2 rfl

/-! # 3. A single-value write pins its address -/

theorem wrSingleAddr (G : Gexec) (e : Geid) (a0 : Int) (v0 : BitVec 8) (l : Lbl)
    (hlbl : gxLbl G e = some l) (hwr : lbWr l = some (a0, [v0])) :
    ∀ a' v', gwritesByte G e a' v' → a' = a0 := by
  rintro a' v' ⟨l', base, vs, j, hl', hwr', hvs, hacc⟩
  rw [hlbl] at hl'
  obtain rfl := Option.some.inj hl'
  rw [hwr] at hwr'
  simp only [Option.some.injEq, Prod.mk.injEq] at hwr'
  obtain ⟨rfl, rfl⟩ := hwr'
  cases j with
  | zero => unfold accAddr at hacc; omega
  | succ j => simp at hvs

/-! # 4. Every named hypothesis of `lockSliceSound''`, for `race4` -/

theorem hxl4 : AxLockRace.xr ≠ lr := by decide

theorem hwx4 : gwritesByte race4.gdG AxLockWitness.eWx AxLockRace.xr b1 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

theorem hsingleWx4 :
    ∀ a' v', gwritesByte race4.gdG AxLockWitness.eWx a' v' → a' = AxLockRace.xr :=
  wrSingleAddr _ _ AxLockRace.xr b1 (LStore false AxLockRace.xr [b1] .WCplain)
    (by decide +kernel) rfl

theorem hgdWx4 : graphData race4 AxLockWitness.eWx = some [b1] := by decide +kernel

theorem hfence4 : gppoCat race4 AxLockWitness.eWx eWrel :=
  (gppoCatBSpec _ _ _).1 (by decide +kernel)

theorem hwb04 : gwritesByte race4.gdG eWrel lr b0 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

theorem hsingleRel4 : ∀ a' v', gwritesByte race4.gdG eWrel a' v' → a' = lr :=
  wrSingleAddr _ _ lr b0 (LStore false lr [b0] .WCplain) (by decide +kernel) rfl

theorem hrf4 : grfe race4.gdG eWrel eAcq :=
  (grfeBSpec _ _ _).1 (by decide +kernel)

theorem hwb14 : gwritesByte race4.gdG eAcq lr b1 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

theorem hsingleAcq4 : ∀ a' v', gwritesByte race4.gdG eAcq a' v' → a' = lr :=
  wrSingleAddr _ _ lr b1 (LRmw true false lr [2] [b0] [b1] .WCplain) (by decide +kernel) rfl

theorem hvalAcq4 : graphData race4 eAcq = some [b1] := by decide +kernel

theorem hacqPo4 : gacqPo race4.gdG eAcq AxLockWitness.eRx :=
  (gacqBSpec _ _ _).1 (by decide +kernel)

theorem hnw4 : gisW race4.gdG AxLockWitness.eRx = false := by decide +kernel

theorem hrd4 : ∃ t v, greadsByte race4.gdG AxLockWitness.eRx AxLockRace.xr t v :=
  ⟨1, b1, (grbBSpec _ _ _ _ _).1 (by decide +kernel)⟩

theorem hgmoPerm4 :
    [AxLockWitness.eWx, eWrel, eAcq, AxLockWitness.eRx].Perm race4.gdG.gxGmo :=
  List.Perm.refl _

/-! # 5. Instantiating `lockSliceSound''` on `race4` -/

theorem race4Sound {GF : BundledGFunctors} [InvGpreS GF] [AxlogG GF Hent] [AxLockG GF] :
    ∀ t v, greadsByte race4.gdG AxLockWitness.eRx AxLockRace.xr t v → v = b1 := by
  intro t v hread
  exact @lockSliceSound'' GF _ witnessAxpol _ _ lr AxLockRace.xr hxl4 race4 0 1 2 0
    AxLockWitness.eWx AxLockWitness.eRx b1 race4Cat hwx4 hsingleWx4 hgdWx4 hfence4 hwb04
    hsingleRel4 hrf4 hwb14 hsingleAcq4 hvalAcq4 hpol4 hacqPo4 hnw4 hrd4 hlobpWx4 hlobpWrel4
    hlobpAcq4 hlobpRx4 hspolWx4 hspolWrel4 hspolAcq4 hspolRx4 hgmoPerm4 t v hread

end Weak
