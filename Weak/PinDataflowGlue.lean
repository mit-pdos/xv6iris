/-
Weak: **W9a (B) B1 — the emission ↔ clause glue** (plan `notes/weak-allocproc-plan.md` rev 49 §C
"W9a (B)" (B1): "the `grpOkb` glue"; spike `notes/W9aB-spike.md` §4).  Lean-only.

`dfB` follows the emission's own bookkeeping, so it can be run ALONG the hart's real steps:

* `dfNodeStep` / `dfHwStep`: one `pstepEv` step of a hart (`WeakEvProv.pstepHw`: a Sail node, a
  parked fence firing, a PLIC wire write) that is not an instruction boundary or announce
  (`ann = false`), from a tree satisfying `dfB P` at a state matching the hart's channel
  (`st.ro = depsOfIb ib.ibBits`, `st.rds = ib.ibRds`) and with an `Rboot`-admitted register file,
  lands on a tree satisfying `dfB P` again, the channel still matched, the slot bookkeeping moved by
  the step's LABEL (`dfLab`), the register file still `Rboot`-admitted.
* `dfPhrun` / `dfPevrun`: the same along a run with no boundary/announce step: the slots move by
  the scan of the run's labels (`dfScan`).
* `dfScanGrp` / `dfScanGrpOkb`: a label list that scans from empty slots to FULL slots with no bad
  write is split `g = g1 ++ g2` with `WeakRvwmoPinBridge2.grpOkb pc g1 g2` at any pc whose decoded
  role is the role (`krole pc = ro`, the announced word = `kword pc` -- that equation is (B4)'s).
* `dfNoneNeutral`: before the announce (`ib.ibBits = none`, role `ORnone`) no step emits an
  `LRegW`, for ANY tree -- the boundary, the fetch and the interrupt trap step are
  provenance-neutral (the `Ibch` reset; spike §4's "trap step" check).

Every helper is `Weak.PinDataflow.*`.
-/
import Weak.PinDataflowCsr
import Weak.WeakEvProv

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel

namespace PinDataflow
open SailCycleOrderK

/-! ## 1. One step -/

/-- An `Rboot`-admitted register file. -/
def RbootAll (rs : RegFile) : Prop := ∀ r, Rboot r (rs r)

theorem rbootAllSet (rs : RegFile) (r : Register) (v : RegisterType r) (h : RbootAll rs)
    (hv : Rboot r v) : RbootAll (rs.set r v) := by
  intro r'
  by_cases e : r' = r
  · subst e; rw [RegFile.set_same]; exact hv
  · rw [RegFile.set_other _ _ _ _ e]; exact h r'

/-- A non-`LRegW` label moves no slot. -/
theorem dfLabNeutral (ro : OpRoles) (n : Nat) (ok : Bool) (l : Wlabel)
    (h : ∀ rd srcs, l ≠ LRegW rd srcs) : dfLab ro n ok l = (n, ok) := by
  cases l <;> first | rfl | exact absurd rfl (h _ _)

/-- The conclusion of a step: a state for the new tree, matched to the new channel. -/
def dfStepOk (P : Unit → DfSt → Prop) (st : DfSt) (l : Wlabel) (m' : SailM Unit) (ib' : Ibch)
    (rs' : RegFile) : Prop :=
  ∃ st', dfB P m' st' ∧ st'.ro = st.ro ∧ st'.ro = depsOfIb ib'.ibBits ∧ st'.rds = ib'.ibRds ∧
    (st'.n, st'.ok) = dfLab st.ro st.n st.ok l ∧ RbootAll rs'

theorem dfStepStay (P : Unit → DfSt → Prop) (st : DfSt) (l : Wlabel) (m' : SailM Unit) (ib : Ibch)
    (rs : RegFile) (hdf : dfB P m' st) (hro : st.ro = depsOfIb ib.ibBits) (hrds : st.rds = ib.ibRds)
    (hrb : RbootAll rs) (hl : ∀ rd srcs, l ≠ LRegW rd srcs) : dfStepOk P st l m' ib rs :=
  ⟨st, hdf, rfl, hro, hrds, (dfLabNeutral _ _ _ l hl).symm, hrb⟩

/-- **One Sail node** (header). -/
theorem dfNodeStep (P : Unit → DfSt → Prop) (m : SailM Unit) (rs : RegFile) (ib : Ibch)
    (d : DevStates) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (st : DfSt)
    (hstep : pnodeStep m rs ib d l m' ors fn' d' oib obar) (hann : ibnAnn m = false)
    (hdf : dfB P m st) (hro : st.ro = depsOfIb ib.ibBits) (hrds : st.rds = ib.ibRds)
    (hrb : RbootAll rs) : dfStepOk P st l m' (oib.getD ib) (ors.getD rs) := by
  match m, hstep with
  | .pure _, _ => simp [ibnAnn] at hann
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | regRead r =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      refine ⟨dfRd st r, hdf (rs r) (hrb r), rfl, ?_, ?_, rfl, hrb⟩
      · show st.ro = depsOfIb (ibRd ib r).ibBits
        rw [ibRdBits]; exact hro
      · show dfRdsAdd st.rds (eregNum r) = (ibRd ib r).ibRds
        rw [hrds]; exact (dfRdsAddIb ib (eregNum r)).symm
    | regWrite r v =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      refine ⟨dfWr st r, hdf.2 (), rfl, hro, hrds, ?_, rbootAllSet rs r v hrb hdf.1⟩
      simp only [dfWr, hro, hrds]
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · obtain ⟨w, -, rfl, rfl, rfl, -, rfl, -⟩ := h
        exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
      · rcases h with ⟨-, w, tvs, -, -, rfl, rfl, rfl, -, -, rfl, -⟩ |
          ⟨-, ⟨-, w, tvs, -, -, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, w, tvs, -, -, rfl, rfl, rfl, -, -, rfl, -⟩⟩
        all_goals exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨-, rfl, rfl, rfl, -, rfl, -⟩ := h
          exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
        · exact h.elim
      · split at h
        · obtain ⟨-, h⟩ := h
          rcases h with ⟨-, rfl, rfl, rfl, -, -, rfl, -⟩ |
            ⟨-, ⟨rfl, rfl, rfl, -, -, rfl, -⟩ | ⟨rfl, rfl, rfl, -, -, rfl, -⟩⟩
          · exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
          · exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
          · exact dfStepStay P st _ _ ib rs hdf hro hrds hrb (fun _ _ e => by cases e)
        · exact h.elim
    | barrier b =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      refine dfStepStay P st _ _ ib rs (hdf ()) hro hrds hrb (fun _ _ e => ?_)
      unfold ebarLabel at e
      split at e <;> cases e
    | instrAnnounce n w => simp [ibnAnn] at hann
    | choose s =>
      obtain ⟨ch, rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf ch) hro hrds hrb (fun _ _ e => by cases e)
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | getCycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
    | branchAnnounce =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
    | cacheOp =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
    | tlbi =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
    | takeException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
    | returnException =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
    | translationStart =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
    | translationEnd =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
    | cycleCount =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)
    | message =>
      obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := h
      exact dfStepStay P st _ _ ib rs (hdf _) hro hrds hrb (fun _ _ e => by cases e)

/-- **One hart step** (header): a node, a parked fence, or a PLIC wire write. -/
theorem dfHwStep (P : Unit → DfSt → Prop) (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel) (rds : List Nat)
    (ws : List Register) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) (st : DfSt)
    (hstep : pstepHw cpu m rs fn ib d l rds ws false m' ors fn' d' oib obar)
    (hdf : dfB P m st) (hro : st.ro = depsOfIb ib.ibBits) (hrds : st.rds = ib.ibRds)
    (hrb : RbootAll rs) : dfStepOk P st l m' (oib.getD ib) (ors.getD rs) := by
  rcases hstep with ⟨-, ⟨H, -⟩, -, -, hann⟩ | ⟨pr, pw, sr, sw, rfl, ⟨H, -⟩, -, -, -⟩ | ⟨H, -, -, -⟩
  · exact dfNodeStep P m rs ib _ l m' ors fn' _ oib obar st H hann.symm hdf hro hrds hrb
  · obtain ⟨rfl, rfl, rfl, -, -, rfl, -⟩ := H
    exact dfStepStay P st _ _ ib rs hdf hro hrds hrb (fun _ _ e => by cases e)
  · obtain ⟨mm, b, k, -, rfl, rfl, -, -, rfl, -, rfl⟩ := H
    refine dfStepStay P st _ _ ib _ hdf hro hrds ?_ (fun _ _ e => by cases e)
    unfold pinSet
    split
    · exact rbootAllSet rs _ _ hrb trivial
    · exact rbootAllSet rs _ _ hrb trivial

/-! ## 2. A run with no boundary or announce -/

/-- The slot scan of a label list. -/
def dfScan (ro : OpRoles) : Nat × Bool → List Wlabel → Nat × Bool
  | p, [] => p
  | p, l :: ls => dfScan ro (dfLab ro p.1 p.2 l) ls

theorem dfScanApp (ro : OpRoles) (p : Nat × Bool) (l1 l2 : List Wlabel) :
    dfScan ro p (l1 ++ l2) = dfScan ro (dfScan ro p l1) l2 := by
  induction l1 generalizing p with
  | nil => rfl
  | cons l l1 ih => exact ih _

/-- **The run** (header). -/
theorem dfPhrun (P : Unit → DfSt → Prop) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m' : SailM Unit)
    (rs' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' → ann = false →
    ∀ st, dfB P m st → st.ro = depsOfIb ib.ibBits → st.rds = ib.ibRds → RbootAll rs →
    ∃ st', dfB P m' st' ∧ st'.ro = st.ro ∧ st'.ro = depsOfIb ib'.ibBits ∧ st'.rds = ib'.ibRds ∧
      (st'.n, st'.ok) = dfScan st.ro (st.n, st.ok) ls ∧ RbootAll rs' := by
  intro h
  induction h with
  | nil m rs fn ib d =>
    intro _ st hdf hro hrds hrb
    exact ⟨st, hdf, rfl, hro, hrds, rfl, hrb⟩
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d m1 ors fn1 oib obar d1 m2 rs2 fn2 ib2 d2
      hstep _ ih =>
    intro hann st hdf hro hrds hrb
    rw [Bool.or_eq_false_iff] at hann
    obtain ⟨ha1, ha2⟩ := hann
    subst ha1
    obtain ⟨st1, hdf1, hr1, hro1, hrds1, hnk1, hrb1⟩ :=
      dfHwStep P cpu m rs fn ib d l rds ws m1 ors fn1 d1 oib obar st hstep hdf hro hrds hrb
    obtain ⟨st2, hdf2, hr2, hro2, hrds2, hnk2, hrb2⟩ := ih ha2 st1 hdf1 hro1 hrds1 hrb1
    refine ⟨st2, hdf2, hr2.trans hr1, hro2, hrds2, ?_, hrb2⟩
    rw [hnk2, hr1, hnk1]
    rfl

/-- The run lemma over the plain chain, the boundary/announce exclusion read off the labels (as
`WeakEvProv.instrDagreeEv`). -/
theorem dfPevrun (P : Unit → DfSt → Prop) (cpu : CPU) (ls : List Wlabel) (m : SailM Unit)
    (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch)
    (d' : Efab) :
    pevrun ls (.PHart cpu m rs fn ib) d (.PHart cpu m' rs' fn' ib') d' →
    LInstr ∉ ls → LFence false false false false ∉ ls →
    ∀ st, dfB P m st → st.ro = depsOfIb ib.ibBits → st.rds = ib.ibRds → RbootAll rs →
    ∃ st', dfB P m' st' ∧ st'.ro = st.ro ∧ st'.ro = depsOfIb ib'.ibBits ∧ st'.rds = ib'.ibRds ∧
      (st'.n, st'.ok) = dfScan st.ro (st.n, st.ok) ls ∧ RbootAll rs' := by
  intro hrun hni hnf
  obtain ⟨rds, ws, ann, hh⟩ := pevrunPhrun ls _ d _ d' hrun cpu m rs fn ib m' rs' fn' ib' rfl rfl
  exact dfPhrun P cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' hh
    (phrunNoInstr cpu ls rds ws ann m rs fn ib d m' rs' fn' ib' d' hh hni hnf)

/-! ## 3. Before the announce: no `LRegW` at all -/

/-- **The role-free channel is provenance-neutral** (header): at `ib.ibBits = none` no hart step
emits an `LRegW`, whatever the tree. -/
theorem dfNoneNeutral (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab)
    (oib : Option Ibch) (obar : Option barrier_kind) (hib : ib.ibBits = none)
    (hstep : pstepHart cpu m rs fn ib d l m' ors fn' d' oib obar) :
    ∀ rd srcs, l ≠ LRegW rd srcs := by
  intro rd srcs e
  subst e
  rcases hstep with ⟨H, -⟩ | H
  · cases fn with
    | some f => obtain ⟨_, _, _, _⟩ := f; exact absurd H.1 (by intro e; cases e)
    | none =>
      match m, H with
      | .pure _, H => obtain ⟨_, e, -⟩ := H; cases e
      | .impure (.error _) _, H => exact H.elim
      | .impure (.ok o) k, H =>
        cases o with
        | regWrite r v =>
          obtain ⟨e, -⟩ := H
          rw [hib, depsOfIbNone] at e
          unfold erwOf erwLabel at e
          by_cases hn : r = .nextPC
          · simp only [hn, ↓reduceIte] at e; cases e
          · simp only [hn, ↓reduceIte, depsRdNone, erwDest] at e
            have : depsRd2 OpRoles.ORnone = none := rfl
            rw [this] at e
            cases e
        | regRead r => obtain ⟨e, -⟩ := H; cases e
        | memRead n va req =>
          simp only [pstepNode, pnodeStep] at H
          split at H
          · obtain ⟨_, -, e, -⟩ := H; cases e
          · rcases H with ⟨-, _, _, -, -, e, -⟩ | ⟨-, ⟨-, _, _, -, -, e, -⟩ | ⟨-, _, _, -, -, e, -⟩⟩
            all_goals cases e
        | memWrite n va req =>
          simp only [pstepNode, pnodeStep] at H
          split at H
          · split at H
            · obtain ⟨-, e, -⟩ := H; cases e
            · exact H.elim
          · split at H
            · obtain ⟨-, H⟩ := H
              rcases H with ⟨-, e, -⟩ | ⟨-, ⟨e, -⟩ | ⟨e, -⟩⟩
              all_goals cases e
            · exact H.elim
        | barrier b =>
          obtain ⟨e, -⟩ := H
          unfold ebarLabel at e
          split at e <;> cases e
        | instrAnnounce n w =>
          obtain ⟨e, -⟩ := H
          unfold annLabel at e
          split at e <;> cases e
        | choose s => obtain ⟨_, e, -⟩ := H; cases e
        | readRam => exact H.elim
        | writeRam => exact H.elim
        | getCycleCount => obtain ⟨e, -⟩ := H; cases e
        | branchAnnounce => obtain ⟨e, -⟩ := H; cases e
        | cacheOp => obtain ⟨e, -⟩ := H; cases e
        | tlbi => obtain ⟨e, -⟩ := H; cases e
        | takeException => obtain ⟨e, -⟩ := H; cases e
        | returnException => obtain ⟨e, -⟩ := H; cases e
        | translationStart => obtain ⟨e, -⟩ := H; cases e
        | translationEnd => obtain ⟨e, -⟩ := H; cases e
        | cycleCount => obtain ⟨e, -⟩ := H; cases e
        | message => obtain ⟨e, -⟩ := H; cases e
  · obtain ⟨_, _, _, -, e, -⟩ := H; cases e

/-! ## 4. Full slots → `grpOkb` -/

theorem dfScanMono (ro : OpRoles) (ls : List Wlabel) :
    ∀ n ok n' ok', dfScan ro (n, ok) ls = (n', ok') → n ≤ n' ∧ (ok' = true → ok = true) := by
  induction ls with
  | nil => intro n ok n' ok' h; cases h; exact ⟨Nat.le_refl _, id⟩
  | cons l ls ih =>
    intro n ok n' ok' h
    simp only [dfScan] at h
    unfold dfLab at h
    split at h
    · split at h
      · obtain ⟨h1, h2⟩ := ih _ _ _ _ h
        exact ⟨by omega, h2⟩
      · obtain ⟨h1, h2⟩ := ih _ _ _ _ h
        exact ⟨h1, fun e => absurd (h2 e) Bool.false_ne_true⟩
    · exact ih _ _ _ _ h

/-- No slot moved, no bad write: no `LRegW` at all. -/
theorem dfScanNone (ro : OpRoles) (g : List Eitem) (n : Nat)
    (h : dfScan ro (n, true) (g.map Prod.fst) = (n, true)) : g.all provNeutralb = true := by
  induction g with
  | nil => rfl
  | cons it g ih =>
    obtain ⟨l, k⟩ := it
    simp only [List.map_cons, dfScan] at h
    rw [List.all_cons, Bool.and_eq_true]
    cases l
    case LRegW rd srcs =>
      exfalso
      simp only [dfLab] at h
      split at h
      · have := (dfScanMono ro _ _ _ _ _ h).1; omega
      · exact Bool.false_ne_true ((dfScanMono ro _ _ _ _ _ h).2 rfl)
    all_goals exact ⟨rfl, ih h⟩

/-- One slot moved, no bad write: exactly one `LRegW`, the slot's. -/
theorem dfScanOne (ro : OpRoles) (g : List Eitem) (n rd : Nat) (dec : List Dsrc)
    (hd : (dfDests ro)[n]? = some (rd, dec))
    (h : dfScan ro (n, true) (g.map Prod.fst) = (n + 1, true)) : regwSeg rd dec g = true := by
  induction g with
  | nil => simp only [List.map_nil, dfScan, Prod.mk.injEq] at h; omega
  | cons it g ih =>
    obtain ⟨l, k⟩ := it
    simp only [List.map_cons, dfScan] at h
    cases l
    case LRegW rd' srcs =>
      simp only [dfLab] at h
      split at h
      · rename_i hs
        simp only [slotOk, hd, Bool.and_eq_true] at hs
        obtain ⟨h1, h2⟩ := hs
        simp only [regwSeg, h1, h2, Bool.true_and]
        exact dfScanNone ro g (n + 1) h
      · exact absurd ((dfScanMono ro _ _ _ _ _ h).2 rfl) Bool.false_ne_true
    all_goals exact ih h

/-- Two slots moved: split after the first `LRegW`. -/
theorem dfScanTwo (ro : OpRoles) (g : List Eitem) (n : Nat)
    (h : dfScan ro (n, true) (g.map Prod.fst) = (n + 2, true)) :
    ∃ g1 g2, g = g1 ++ g2 ∧ dfScan ro (n, true) (g1.map Prod.fst) = (n + 1, true) ∧
      dfScan ro (n + 1, true) (g2.map Prod.fst) = (n + 2, true) := by
  induction g with
  | nil => simp only [List.map_nil, dfScan, Prod.mk.injEq] at h; omega
  | cons it g ih =>
    obtain ⟨l, k⟩ := it
    simp only [List.map_cons, dfScan] at h
    cases l
    case LRegW rd' srcs =>
      simp only [dfLab] at h
      split at h
      · rename_i hs
        refine ⟨[(LRegW rd' srcs, k)], g, rfl, ?_, h⟩
        simp only [List.map_cons, List.map_nil, dfScan, dfLab, hs, ↓reduceIte]
      · exact absurd ((dfScanMono ro _ _ _ _ _ h).2 rfl) Bool.false_ne_true
    all_goals
      obtain ⟨g1, g2, rfl, h1, h2⟩ := ih h
      exact ⟨_ :: g1, g2, rfl, by simpa only [List.map_cons, dfScan, dfLab] using h1, h2⟩

/-- **FULL SLOTS GIVE THE GROUP TEST** (header). -/
theorem dfScanGrp (ro : OpRoles) (g : List Eitem)
    (h : dfScan ro (0, true) (g.map Prod.fst) = ((dfDests ro).length, true)) :
    ∃ g1 g2, g = g1 ++ g2 ∧
      (realizesb (depsRd ro) g1 && realizesb (depsRd2 ro) g2) = true := by
  suffices H : ∃ g1 g2, g = g1 ++ g2 ∧ realizesb (depsRd ro) g1 = true ∧
      realizesb (depsRd2 ro) g2 = true by
    obtain ⟨g1, g2, e, a, b⟩ := H
    exact ⟨g1, g2, e, by rw [a, b]⟩
  cases h1 : depsRd ro with
  | none =>
    cases h2 : depsRd2 ro with
    | none =>
      simp only [dfDests, h1, h2, Option.toList, List.append_nil, List.length_nil] at h
      exact ⟨g, [], (List.append_nil g).symm, dfScanNone ro g 0 h, rfl⟩
    | some d2 =>
      obtain ⟨rd2, dec2⟩ := d2
      simp only [dfDests, h1, h2, Option.toList, List.nil_append, List.length_singleton] at h
      refine ⟨[], g, rfl, rfl, dfScanOne ro g 0 rd2 dec2 ?_ h⟩
      simp only [dfDests, h1, h2, Option.toList, List.nil_append, List.getElem?_cons_zero]
  | some d1 =>
    obtain ⟨rd1, dec1⟩ := d1
    cases h2 : depsRd2 ro with
    | none =>
      simp only [dfDests, h1, h2, Option.toList, List.append_nil, List.length_singleton] at h
      refine ⟨g, [], (List.append_nil g).symm, dfScanOne ro g 0 rd1 dec1 ?_ h, rfl⟩
      simp only [dfDests, h1, h2, Option.toList, List.append_nil, List.getElem?_cons_zero]
    | some d2 =>
      obtain ⟨rd2, dec2⟩ := d2
      simp only [dfDests, h1, h2, Option.toList, List.singleton_append, List.length_cons] at h
      obtain ⟨g1, g2, rfl, hg1, hg2⟩ := dfScanTwo ro g 0 h
      refine ⟨g1, g2, rfl, dfScanOne ro g1 0 rd1 dec1 ?_ hg1, dfScanOne ro g2 1 rd2 dec2 ?_ hg2⟩
      · simp only [dfDests, h1, h2, Option.toList, List.singleton_append, List.getElem?_cons_zero]
      · simp only [dfDests, h1, h2, Option.toList, List.singleton_append,
          List.getElem?_cons_succ, List.getElem?_cons_zero]

/-- ... at a pc whose decoded role is the role (`grpOkb`, `WeakRvwmoPinBridge2`). -/
theorem dfScanGrpOkb (pc : Int) (g : List Eitem)
    (h : dfScan (krole pc) (0, true) (g.map Prod.fst) =
      ((dfDests (krole pc)).length, true)) :
    ∃ g1 g2, g = g1 ++ g2 ∧ grpOkb pc g1 g2 = true :=
  dfScanGrp _ g h

end PinDataflow
end Weak
