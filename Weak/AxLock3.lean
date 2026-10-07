/-
Weak: **the 3-hart lock-client mutual-exclusion certificates** (AxSL tier, lock slice) — pure
graph facts, no Iris.

Rocq: `iris/AxLock3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Harts A, B, C all use lock `L`; each does `acq; write x; covering fence; rel`, and B reads `x`
inside its critical section after acquiring from A's release.  The full Prop-level `lock3_sound`
(AxLockAdeq's §5 induction re-derived over three structured critical sections) is NOT attempted
(as in Rocq); instead:

  §1  CERTIFICATE (a): a consistent 8-event 3-hart graph `lock3` with C's critical section
      strictly AFTER B's.  `csOwnedWrite`'s discipline is discharged VACUOUSLY for C's write
      (`hnvisWCRx3`: it is not `gvisible` to `r_x`), giving `lock3WitnessGrf` and the value-level
      `lock3WitnessSound`.
  §2  CERTIFICATE (b): on `AxLockRace.race` (C writes without the lock) `csOwnedWrite`'s
      discipline is FALSIFIED by `w_c` (`raceViolatesDisc`, a pure graph fact); the ownership
      reading is `AxLockRace.raceWcExcludedAtWxWrelSlot`, re-exported as `raceWcHasNoToken`.
  §3  THE STRONG WITNESS `lock3s`: C's critical section FIRST, C's write genuinely visible to B's
      read (`lock3sWCVisible`); discharged through `csHandoffLast` with C's write routed through
      its own critical section (`hdiscX3s`), giving `lock3sWitnessGrf` / `lock3sSound`.

**Fetches.** Nothing here relies on instruction fetches: the graphs have only store/fence/rmw/
load labels (`Lbl` has no fetch constructor).

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq names, file-qualified: `AxLock3.l3` (also in
   AxSpinJ2), `AxLock3.eWx`, `AxLock3.eRx` (also in AxLockWitness).  Rocq's `Local Notation
   B0/B1/B2` ↦ `b0`/`b1`/`b2` directly.
2. VOCABULARY (as AxLockRace deviation 2): `gd_g GD` ↦ `GD.gdG`; `Z` ↦ `Int`; `vmr` ↦
   `decide +kernel`; `≡ₚ` ↦ `List.Perm`; `gwrites_byte_gis_w` ↦
   `WeakRvwmoGraph.gwritesByteGisW`; `grf` ↦ `WeakRvwmoAcyc.grf`.
3. `race_wc_has_no_token` is a Rocq `Notation` for `AxLockRace.race_wc_excluded_at_wx_wrel_slot`;
   in Lean it is a `theorem` with the same statement, proved by that lemma.

**Rocq → Lean name map.**  `x3` `x3`, `L3` `AxLock3.l3`, `lock3` `lock3`, `e_wx` `AxLock3.eWx`,
`e_wrelA` `eWrelA`, `e_acqB` `eAcqB`, `e_rx` `AxLock3.eRx`, `e_wrelB` `eWrelB`, `e_acqC` `eAcqC`,
`e_wC` `eWC`, `e_wrelC` `eWrelC`, `lock3_cat` `lock3Cat`, `wr_single_addr3` `wrSingleAddr3`,
`Hxl3` `hxl3`, `Hwx3` `hwx3`, `Hsingle_wx3` `hsingleWx3`, `Hfence3` `hfence3`,
`Hsingle_wrelA3` `hsingleWrelA3`, `Hrfe3` `hrfe3`, `Hgacq_poB3` `hgacqPoB3`,
`Hsingle_acqB3` `hsingleAcqB3`, `Hrd3` `hrd3`, `Hnw_rx3` `hnwRx3`, `Hsingle_wrelB3`
`hsingleWrelB3`, `Hsingle_acqC3` `hsingleAcqC3`, `Hsingle_wrelC3` `hsingleWrelC3`, `L3list`
`l3list`, `Hgmo_perm3` `hgmoPerm3`, `Hwonly3` `hwonly3`, `Hnvis_wC_rx3` `hnvisWCRx3`, `Hdisc3`
`hdisc3`, `lock3_witness_grf` `lock3WitnessGrf`, `lock3_witness_sound` `lock3WitnessSound`,
`Hwc_gwrites_race` `hwcGwritesRace`, `Hvis_wc_rx_race` `hvisWcRxRace`, `Hdisc_fails_race`
`hdiscFailsRace`, `race_violates_disc` `raceViolatesDisc`, `race_wc_has_no_token`
`raceWcHasNoToken`, `lock3s` `lock3s`, `e_acqC3s` `eAcqC3s`, `e_wC3s` `eWC3s`, `e_relC3s`
`eRelC3s`, `e_acqA3s` `eAcqA3s`, `e_wxA3s` `eWxA3s`, `e_relA3s` `eRelA3s`, `e_acqB3s`
`eAcqB3s`, `e_rxB3s` `eRxB3s`, `e_relB3s` `eRelB3s`, `lock3s_cat` `lock3sCat`,
`lock3s_wC_visible` `lock3sWCVisible`, `Hsingle_<e>3s` `hsingle<E>3s` (8 lemmas),
`Hnw_rxB3s` `hnwRxB3s`, `L3list_s` `l3listS`, `Hgmo_perm3s` `hgmoPerm3s`, `Hwonly_L3s`
`hwonlyL3s`, `Hwonly_x3s` `hwonlyX3s`, `Hpattern3s` `hpattern3s`, `Hcs_acqC_relC3s`
`hcsAcqCRelC3s`, `Hcs_acqA_relA3s` `hcsAcqARelA3s`, `Hcs_acqB_relB3s` `hcsAcqBRelB3s`,
`Hpaired3s` `hpaired3s`, `HaqC3s` `haqC3s`, `HaqA3s` `haqA3s`, `HaqB3s` `haqB3s`,
`Hpo_acqC_wC3s` `hpoAcqCWC3s`, `Hfence_wC_relC3s` `hfenceWCRelC3s`, `Hwb_wxA3s` `hwbWxA3s`,
`Hpo_acqA_wxA3s` `hpoAcqAWxA3s`, `Hfence_wxA_relA3s` `hfenceWxARelA3s`, `Hrd_acqB3s`
`hrdAcqB3s`, `Hwriteat_relA3s` `hwriteatRelA3s`, `Hpo_acqB_rxB3s` `hpoAcqBRxB3s`, `Hrd_rxB3s`
`hrdRxB3s`, `Hfence_rxB_relB3s` `hfenceRxBRelB3s`, `Hdisc_x3s` `hdiscX3s`,
`lock3s_witness_grf` `lock3sWitnessGrf`, `lock3s_sound` `lock3sSound`.

**Not ported:** the `Print Assumptions` audits (the lint's axiom check covers them).
-/
import Weak.AxLockSerial
import Weak.AxLockRace
import Weak.AxGraphDec
import Weak.AxGraphWit
import Weak.WeakLitmus

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. CERTIFICATE (a): C's critical section strictly AFTER B's

H0 (A): W x=b1 (0,0); fence rw,w (0,1); W L=b0 (0,2) — release.
H1 (B): RMW.aq L: b0→b1 (1,0), reading A's release (write-idx 2); R x (1,1); fence rw,w (1,2);
  W L=b0 (1,3).
H2 (C): RMW.aq L: b0→b1 (2,0), reading B's release (write-idx 4); W x=b2 (2,1); fence rw,w (2,2);
  W L=b0 (2,3).
gmo = [w_x; w_relA; acqB; r_x; w_relB; acqC; w_C; w_relC]. -/

def x3 : Int := 0
def AxLock3.l3 : Int := 1

def lock3 : Gdexec :=
  AxGraphWit.mkgd
    [[LStore false x3 [b1] .WCplain,
      LFence true true false true,
      LStore false AxLock3.l3 [b0] .WCplain],
     [LRmw true false AxLock3.l3 [2] [b0] [b1] .WCplain,
      LLoad false x3 [1] [b1],
      LFence true true false true,
      LStore false AxLock3.l3 [b0] .WCplain],
     [LRmw true false AxLock3.l3 [4] [b0] [b1] .WCplain,
      LStore false x3 [b2] .WCplain,
      LFence true true false true,
      LStore false AxLock3.l3 [b0] .WCplain]]
    [(0, 0), (0, 2), (1, 0), (1, 1), (1, 3), (2, 0), (2, 1), (2, 3)]
    []

def AxLock3.eWx : Geid := (0, 0)
def eWrelA : Geid := (0, 2)
def eAcqB : Geid := (1, 0)
def AxLock3.eRx : Geid := (1, 1)
def eWrelB : Geid := (1, 3)
def eAcqC : Geid := (2, 0)
def eWC : Geid := (2, 1)
def eWrelC : Geid := (2, 3)

theorem lock3Cat : rvwmoCatConsistent lock3 :=
  catConsistentBSound _ (by decide +kernel)

/-- A single-value write pins its address. -/
theorem wrSingleAddr3 (G : Gexec) (e : Geid) (a0 : Int) (v0 : BitVec 8) (l : Lbl)
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

theorem hxl3 : x3 ≠ AxLock3.l3 := by decide

theorem hwx3 : gwritesByte lock3.gdG AxLock3.eWx x3 b1 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

theorem hsingleWx3 : ∀ a' v', gwritesByte lock3.gdG AxLock3.eWx a' v' → a' = x3 :=
  wrSingleAddr3 _ _ x3 b1 (LStore false x3 [b1] .WCplain) (by decide +kernel) rfl

theorem hfence3 : gppoCat lock3 AxLock3.eWx eWrelA :=
  (gppoCatBSpec _ _ _).1 (by decide +kernel)

theorem hsingleWrelA3 : ∀ a' v', gwritesByte lock3.gdG eWrelA a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b0 (LStore false AxLock3.l3 [b0] .WCplain) (by decide +kernel) rfl

theorem hrfe3 : grfe lock3.gdG eWrelA eAcqB :=
  (grfeBSpec _ _ _).1 (by decide +kernel)

theorem hgacqPoB3 : gacqPo lock3.gdG eAcqB AxLock3.eRx :=
  (gacqBSpec _ _ _).1 (by decide +kernel)

theorem hsingleAcqB3 : ∀ a' v', gwritesByte lock3.gdG eAcqB a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b1 (LRmw true false AxLock3.l3 [2] [b0] [b1] .WCplain)
    (by decide +kernel) rfl

theorem hrd3 : greadsByte lock3.gdG AxLock3.eRx x3 1 b1 :=
  (grbBSpec _ _ _ _ _).1 (by decide +kernel)

theorem hnwRx3 : gisW lock3.gdG AxLock3.eRx = false := by decide +kernel

theorem hsingleWrelB3 : ∀ a' v', gwritesByte lock3.gdG eWrelB a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b0 (LStore false AxLock3.l3 [b0] .WCplain) (by decide +kernel) rfl

theorem hsingleAcqC3 : ∀ a' v', gwritesByte lock3.gdG eAcqC a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b1 (LRmw true false AxLock3.l3 [4] [b0] [b1] .WCplain)
    (by decide +kernel) rfl

theorem hsingleWrelC3 : ∀ a' v', gwritesByte lock3.gdG eWrelC a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b0 (LStore false AxLock3.l3 [b0] .WCplain) (by decide +kernel) rfl

def l3list : List Geid :=
  [AxLock3.eWx, eWrelA, eAcqB, AxLock3.eRx, eWrelB, eAcqC, eWC, eWrelC]

theorem hgmoPerm3 : List.Perm l3list lock3.gdG.gxGmo := List.Perm.refl _

/-- The only two writers to `x3` in `lock3` are `eWx` and `eWC`. -/
theorem hwonly3 : ∀ w v, gwritesByte lock3.gdG w x3 v → w = AxLock3.eWx ∨ w = eWC := by
  intro w v hw
  obtain ⟨hwf, _, _, _, _, _⟩ := lock3Cat
  have hin : w ∈ l3list := hgmoPerm3.mem_iff.2 (gwritesByteGmo _ w x3 v hwf hw)
  simp only [l3list, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact (hxl3 (hsingleWrelA3 x3 v hw)).elim
  · exact (hxl3 (hsingleAcqB3 x3 v hw)).elim
  · have hisw := WeakRvwmoGraph.gwritesByteGisW _ _ x3 v hw
    rw [hnwRx3] at hisw
    exact Bool.noConfusion hisw
  · exact (hxl3 (hsingleWrelB3 x3 v hw)).elim
  · exact (hxl3 (hsingleAcqC3 x3 v hw)).elim
  · exact Or.inr rfl
  · exact (hxl3 (hsingleWrelC3 x3 v hw)).elim

/-- C's write is NOT `gvisible` to `r_x` (gmo-after it, cross-hart). -/
theorem hnvisWCRx3 : ¬ gvisible lock3.gdG eWC AxLock3.eRx := fun hvis =>
  absurd ((gvisBSpec _ _ _).2 hvis) (by decide +kernel)

/-- `csOwnedWrite`'s discipline, discharged for `lock3` (C's write never reaches the guard). -/
theorem hdisc3 : ∀ w vw, gwritesByte lock3.gdG w x3 vw →
    gvisible lock3.gdG w AxLock3.eRx → w = AxLock3.eWx ∨ gmoLt lock3.gdG w AxLock3.eWx := by
  intro w vw hw hvis
  rcases hwonly3 w vw hw with rfl | rfl
  · exact Or.inl rfl
  · exact (hnvisWCRx3 hvis).elim

/-- THE CERTIFICATE: `csOwnedWrite` applies to `lock3`. -/
theorem lock3WitnessGrf : WeakRvwmoAcyc.grf lock3.gdG AxLock3.eWx AxLock3.eRx := by
  obtain ⟨hpo3, hisr3, haq3, _⟩ := hgacqPoB3
  exact (csOwnedWrite lock3 x3 AxLock3.eWx AxLock3.eRx eWrelA eAcqB b1 b1 1
    lock3Cat hwx3 hfence3 hrfe3 hisr3 haq3 hpo3 hrd3 hdisc3).1

/-- THE VALUE-LEVEL CONCLUSION: any read `r_x` performs of `x3` sees A's `b1`. -/
theorem lock3WitnessSound : ∀ t v, greadsByte lock3.gdG AxLock3.eRx x3 t v → v = b1 := by
  intro t v hrd
  exact (greadsByteDet _ _ _ t v 1 b1 hrd hrd3).2

/-! # 2. CERTIFICATE (b): `race` violates `csOwnedWrite`'s discipline at `w_c` -/

theorem hwcGwritesRace : gwritesByte race.gdG wCR AxLockRace.xr b2 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

/-- `w_c` sits gmo-between `w_x` and `w_rel`, hence `gvisible` to `r_x`. -/
theorem hvisWcRxRace : gvisible race.gdG wCR rXR :=
  (gvisBSpec _ _ _).1 (by decide +kernel)

/-- Neither disjunct of the discipline's conclusion holds of `w_c` against `w_x`. -/
theorem hdiscFailsRace : ¬ (wCR = wXR ∨ gmoLt race.gdG wCR wXR) := by
  rintro (heq | hmo)
  · exact absurd heq (by decide)
  · exact absurd ((gmoLtBSpec _ _ _).2 hmo) (by decide +kernel)

/-- THE CERTIFICATE: the discipline cannot be discharged on `race` (a pure graph fact). -/
theorem raceViolatesDisc :
    ¬ (∀ w vw, gwritesByte race.gdG w AxLockRace.xr vw → gvisible race.gdG w rXR →
        w = wXR ∨ gmoLt race.gdG w wXR) := fun hdisc =>
  hdiscFailsRace (hdisc wCR b2 hwcGwritesRace hvisWcRxRace)

section NoToken
open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap

/-- THE OWNERSHIP READING: `AxLockRace.raceWcExcludedAtWxWrelSlot`, re-exported. -/
theorem raceWcHasNoToken {GF : BundledGFunctors} [AxlogG GF Hent] (γ : GName)
    (Hl_c : List Hent) :
    tokTie (GF := GF) race γ AxLockRace.xr [(wXR, b1)] {[wXR := (1 : Qp)]} ∗
      histAuth γ AxLockRace.xr 1 Hl_c ⊢ False :=
  raceWcExcludedAtWxWrelSlot γ Hl_c

end NoToken

/-! # 3. THE STRONG WITNESS `lock3s`: C's critical section FIRST, C's write visible to B's read

C: acq L (reads the image, t=0); W x=b2; fence rw,w; rel L.  A: acq L (reads C's release, t=3);
W x=b1; fence rw,w; rel L.  B: acq L (reads A's release, t=6); R x (t=5, A's write); fence rw,w;
rel L.  gmo = [acqC; w_C; relC; acqA; w_x; relA; acqB; r_x; relB]. -/

def lock3s : Gdexec :=
  AxGraphWit.mkgd
    [[LRmw true false AxLock3.l3 [0] [b0] [b1] .WCplain,
      LStore false x3 [b2] .WCplain,
      LFence true true false true,
      LStore false AxLock3.l3 [b0] .WCplain],
     [LRmw true false AxLock3.l3 [3] [b0] [b1] .WCplain,
      LStore false x3 [b1] .WCplain,
      LFence true true false true,
      LStore false AxLock3.l3 [b0] .WCplain],
     [LRmw true false AxLock3.l3 [6] [b0] [b1] .WCplain,
      LLoad false x3 [5] [b1],
      LFence true true false true,
      LStore false AxLock3.l3 [b0] .WCplain]]
    [(0, 0), (0, 1), (0, 3), (1, 0), (1, 1), (1, 3), (2, 0), (2, 1), (2, 3)]
    []

def eAcqC3s : Geid := (0, 0)
def eWC3s : Geid := (0, 1)
def eRelC3s : Geid := (0, 3)
def eAcqA3s : Geid := (1, 0)
def eWxA3s : Geid := (1, 1)
def eRelA3s : Geid := (1, 3)
def eAcqB3s : Geid := (2, 0)
def eRxB3s : Geid := (2, 1)
def eRelB3s : Geid := (2, 3)

theorem lock3sCat : rvwmoCatConsistent lock3s :=
  catConsistentBSound _ (by decide +kernel)

/-- THE NON-TRIVIALITY WITNESS: `w_C` IS `gvisible` to `r_x` here. -/
theorem lock3sWCVisible : gvisible lock3s.gdG eWC3s eRxB3s :=
  (gvisBSpec _ _ _).1 (by decide +kernel)

theorem hsingleAcqC3s : ∀ a' v', gwritesByte lock3s.gdG eAcqC3s a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b1 (LRmw true false AxLock3.l3 [0] [b0] [b1] .WCplain)
    (by decide +kernel) rfl

theorem hsingleWC3s : ∀ a' v', gwritesByte lock3s.gdG eWC3s a' v' → a' = x3 :=
  wrSingleAddr3 _ _ x3 b2 (LStore false x3 [b2] .WCplain) (by decide +kernel) rfl

theorem hsingleRelC3s : ∀ a' v', gwritesByte lock3s.gdG eRelC3s a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b0 (LStore false AxLock3.l3 [b0] .WCplain) (by decide +kernel) rfl

theorem hsingleAcqA3s : ∀ a' v', gwritesByte lock3s.gdG eAcqA3s a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b1 (LRmw true false AxLock3.l3 [3] [b0] [b1] .WCplain)
    (by decide +kernel) rfl

theorem hsingleWxA3s : ∀ a' v', gwritesByte lock3s.gdG eWxA3s a' v' → a' = x3 :=
  wrSingleAddr3 _ _ x3 b1 (LStore false x3 [b1] .WCplain) (by decide +kernel) rfl

theorem hsingleRelA3s : ∀ a' v', gwritesByte lock3s.gdG eRelA3s a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b0 (LStore false AxLock3.l3 [b0] .WCplain) (by decide +kernel) rfl

theorem hsingleAcqB3s : ∀ a' v', gwritesByte lock3s.gdG eAcqB3s a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b1 (LRmw true false AxLock3.l3 [6] [b0] [b1] .WCplain)
    (by decide +kernel) rfl

theorem hsingleRelB3s : ∀ a' v', gwritesByte lock3s.gdG eRelB3s a' v' → a' = AxLock3.l3 :=
  wrSingleAddr3 _ _ AxLock3.l3 b0 (LStore false AxLock3.l3 [b0] .WCplain) (by decide +kernel) rfl

theorem hnwRxB3s : gisW lock3s.gdG eRxB3s = false := by decide +kernel

def l3listS : List Geid :=
  [eAcqC3s, eWC3s, eRelC3s, eAcqA3s, eWxA3s, eRelA3s, eAcqB3s, eRxB3s, eRelB3s]

theorem hgmoPerm3s : List.Perm l3listS lock3s.gdG.gxGmo := List.Perm.refl _

/-- The only writers of `L3` are the three acquires and three releases. -/
theorem hwonlyL3s : ∀ w v, gwritesByte lock3s.gdG w AxLock3.l3 v →
    w = eAcqC3s ∨ w = eRelC3s ∨ w = eAcqA3s ∨ w = eRelA3s ∨ w = eAcqB3s ∨ w = eRelB3s := by
  intro w v hw
  obtain ⟨hwf, _, _, _, _, _⟩ := lock3sCat
  have hin : w ∈ l3listS := hgmoPerm3s.mem_iff.2 (gwritesByteGmo _ w AxLock3.l3 v hwf hw)
  simp only [l3listS, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact (hxl3 (hsingleWC3s AxLock3.l3 v hw).symm).elim
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact (hxl3 (hsingleWxA3s AxLock3.l3 v hw).symm).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · have hisw := WeakRvwmoGraph.gwritesByteGisW _ _ AxLock3.l3 v hw
    rw [hnwRxB3s] at hisw
    exact Bool.noConfusion hisw
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- The only writers of `x3` are `w_C` and `w_x`. -/
theorem hwonlyX3s : ∀ w v, gwritesByte lock3s.gdG w x3 v → w = eWC3s ∨ w = eWxA3s := by
  intro w v hw
  obtain ⟨hwf, _, _, _, _, _⟩ := lock3sCat
  have hin : w ∈ l3listS := hgmoPerm3s.mem_iff.2 (gwritesByteGmo _ w x3 v hwf hw)
  simp only [l3listS, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hxl3 (hsingleAcqC3s x3 v hw)).elim
  · exact Or.inl rfl
  · exact (hxl3 (hsingleRelC3s x3 v hw)).elim
  · exact (hxl3 (hsingleAcqA3s x3 v hw)).elim
  · exact Or.inr rfl
  · exact (hxl3 (hsingleRelA3s x3 v hw)).elim
  · exact (hxl3 (hsingleAcqB3s x3 v hw)).elim
  · have hisw := WeakRvwmoGraph.gwritesByteGisW _ _ x3 v hw
    rw [hnwRxB3s] at hisw
    exact Bool.noConfusion hisw
  · exact (hxl3 (hsingleRelB3s x3 v hw)).elim

/-- `lockPattern`: every `L3`-write is an acquire reading `lockFree`, or a release. -/
theorem hpattern3s : lockPattern lock3s.gdG AxLock3.l3 := by
  refine ⟨fun v0 h => (Option.some.inj h).symm, ?_⟩
  intro w v hw
  have hb1ne : b1 ≠ lockFree := by decide
  rcases hwonlyL3s w v hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine Or.inl ⟨(glblBSpec _ _ _).1 (by decide +kernel), ?_,
      ⟨0, (grbBSpec _ _ _ _ _).1 (by decide +kernel)⟩⟩
    rw [gwritesByteDet _ _ _ v b1 hw ((gwbBSpec _ _ _ _).1 (by decide +kernel))]
    exact hb1ne
  · exact Or.inr (gwritesByteDet _ _ _ _ _ hw ((gwbBSpec _ _ _ _).1 (by decide +kernel)))
  · refine Or.inl ⟨(glblBSpec _ _ _).1 (by decide +kernel), ?_,
      ⟨3, (grbBSpec _ _ _ _ _).1 (by decide +kernel)⟩⟩
    rw [gwritesByteDet _ _ _ v b1 hw ((gwbBSpec _ _ _ _).1 (by decide +kernel))]
    exact hb1ne
  · exact Or.inr (gwritesByteDet _ _ _ _ _ hw ((gwbBSpec _ _ _ _).1 (by decide +kernel)))
  · refine Or.inl ⟨(glblBSpec _ _ _).1 (by decide +kernel), ?_,
      ⟨6, (grbBSpec _ _ _ _ _).1 (by decide +kernel)⟩⟩
    rw [gwritesByteDet _ _ _ v b1 hw ((gwbBSpec _ _ _ _).1 (by decide +kernel))]
    exact hb1ne
  · exact Or.inr (gwritesByteDet _ _ _ _ _ hw ((gwbBSpec _ _ _ _).1 (by decide +kernel)))

/-- The three critical sections (the same-hart exclusion clause is vacuous in each). -/
theorem hcsAcqCRelC3s : lockCs lock3s.gdG AxLock3.l3 eAcqC3s eRelC3s := by
  refine ⟨⟨b1, (gwbBSpec _ _ _ _).1 (by decide +kernel), by decide⟩,
    (gwbBSpec _ _ _ _).1 (by decide +kernel), rfl, by decide +kernel, ?_⟩
  intro x v hxw
  rcases hwonlyL3s x v hxw with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem hcsAcqARelA3s : lockCs lock3s.gdG AxLock3.l3 eAcqA3s eRelA3s := by
  refine ⟨⟨b1, (gwbBSpec _ _ _ _).1 (by decide +kernel), by decide⟩,
    (gwbBSpec _ _ _ _).1 (by decide +kernel), rfl, by decide +kernel, ?_⟩
  intro x v hxw
  rcases hwonlyL3s x v hxw with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem hcsAcqBRelB3s : lockCs lock3s.gdG AxLock3.l3 eAcqB3s eRelB3s := by
  refine ⟨⟨b1, (gwbBSpec _ _ _ _).1 (by decide +kernel), by decide⟩,
    (gwbBSpec _ _ _ _).1 (by decide +kernel), rfl, by decide +kernel, ?_⟩
  intro x v hxw
  rcases hwonlyL3s x v hxw with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- `lockPaired`: every release closes one of the three critical sections. -/
theorem hpaired3s : lockPaired lock3s.gdG AxLock3.l3 := by
  intro R hR
  have hb1ne : b1 ≠ lockFree := by decide
  rcases hwonlyL3s R lockFree hR with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hb1ne (gwritesByteDet _ eAcqC3s AxLock3.l3 b1 lockFree
      ((gwbBSpec _ _ _ _).1 (by decide +kernel)) hR)).elim
  · exact ⟨eAcqC3s, hcsAcqCRelC3s⟩
  · exact (hb1ne (gwritesByteDet _ eAcqA3s AxLock3.l3 b1 lockFree
      ((gwbBSpec _ _ _ _).1 (by decide +kernel)) hR)).elim
  · exact ⟨eAcqA3s, hcsAcqARelA3s⟩
  · exact (hb1ne (gwritesByteDet _ eAcqB3s AxLock3.l3 b1 lockFree
      ((gwbBSpec _ _ _ _).1 (by decide +kernel)) hR)).elim
  · exact ⟨eAcqB3s, hcsAcqBRelB3s⟩

/-! The remaining named facts `csHandoffLast` asks for. -/

theorem haqC3s : glblIs lock3s.gdG eAcqC3s lbAq := (glblBSpec _ _ _).1 (by decide +kernel)
theorem haqA3s : glblIs lock3s.gdG eAcqA3s lbAq := (glblBSpec _ _ _).1 (by decide +kernel)
theorem haqB3s : glblIs lock3s.gdG eAcqB3s lbAq := (glblBSpec _ _ _).1 (by decide +kernel)

theorem hpoAcqCWC3s : WeakRvwmoGraph.gpo lock3s.gdG eAcqC3s eWC3s :=
  (gpoBSpec _ _ _).1 (by decide +kernel)

theorem hfenceWCRelC3s : gppoCat lock3s eWC3s eRelC3s :=
  (gppoCatBSpec _ _ _).1 (by decide +kernel)

theorem hwbWxA3s : gwritesByte lock3s.gdG eWxA3s x3 b1 :=
  (gwbBSpec _ _ _ _).1 (by decide +kernel)

theorem hpoAcqAWxA3s : WeakRvwmoGraph.gpo lock3s.gdG eAcqA3s eWxA3s :=
  (gpoBSpec _ _ _).1 (by decide +kernel)

theorem hfenceWxARelA3s : gppoCat lock3s eWxA3s eRelA3s :=
  (gppoCatBSpec _ _ _).1 (by decide +kernel)

theorem hrdAcqB3s : greadsByte lock3s.gdG eAcqB3s AxLock3.l3 6 b0 :=
  (grbBSpec _ _ _ _ _).1 (by decide +kernel)

theorem hwriteatRelA3s : gwriteAt lock3s.gdG 6 = some eRelA3s := by decide +kernel

theorem hpoAcqBRxB3s : WeakRvwmoGraph.gpo lock3s.gdG eAcqB3s eRxB3s :=
  (gpoBSpec _ _ _).1 (by decide +kernel)

theorem hrdRxB3s : greadsByte lock3s.gdG eRxB3s x3 5 b1 :=
  (grbBSpec _ _ _ _ _).1 (by decide +kernel)

theorem hfenceRxBRelB3s : gppoCat lock3s eRxB3s eRelB3s :=
  (gppoCatBSpec _ _ _).1 (by decide +kernel)

/-- THE DISCIPLINE, discharged: the only other writer of `x3` is `w_C`, routed through C's own
critical section on a hart neither A's nor B's. -/
theorem hdiscX3s : ∀ w vw, gwritesByte lock3s.gdG w x3 vw → w = eWxA3s ∨
    (∃ acqk relk, lockCs lock3s.gdG AxLock3.l3 acqk relk ∧ glblIs lock3s.gdG acqk lbAq ∧
       acqk.1 ≠ eAcqA3s.1 ∧ acqk.1 ≠ eAcqB3s.1 ∧
       WeakRvwmoGraph.gpo lock3s.gdG acqk w ∧ gppoCat lock3s w relk) := by
  intro w vw hw
  rcases hwonlyX3s w vw hw with rfl | rfl
  · exact Or.inr ⟨eAcqC3s, eRelC3s, hcsAcqCRelC3s, haqC3s, by decide, by decide,
      hpoAcqCWC3s, hfenceWCRelC3s⟩
  · exact Or.inl rfl

/-- THE CERTIFICATE: `csHandoffLast` applies to `lock3s`. -/
theorem lock3sWitnessGrf : WeakRvwmoAcyc.grf lock3s.gdG eWxA3s eRxB3s :=
  (csHandoffLast lock3s AxLock3.l3 x3 eAcqA3s eRelA3s eAcqB3s eRelB3s eWxA3s eRxB3s
    b1 b1 b0 6 5
    lock3sCat hpattern3s hpaired3s
    hcsAcqARelA3s haqA3s hwbWxA3s hpoAcqAWxA3s hfenceWxARelA3s
    hcsAcqBRelB3s haqB3s (by decide)
    hrdAcqB3s hwriteatRelA3s
    hpoAcqBRxB3s hrdRxB3s hfenceRxBRelB3s
    hdiscX3s).1

/-- THE VALUE-LEVEL CONCLUSION: `r_x` sees A's `b1`, not C's `b2`, despite `w_C` being
visible (`lock3sWCVisible`). -/
theorem lock3sSound : ∀ t v, greadsByte lock3s.gdG eRxB3s x3 t v → v = b1 := by
  intro t v hrd
  exact (greadsByteDet _ _ _ t v 5 b1 hrd hrdRxB3s).2

end Weak
