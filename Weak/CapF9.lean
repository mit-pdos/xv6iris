/-
Weak: **W11-F [OWN.102], (ii) increment 1 — every pf store's footprint is RAM: the label inversions
and the message predicate** (coordinator decision (ii) for `readAt`'s `inRam`).  Lean-only, no Rocq twin.

* `CapF9.msgRam m` (every byte message `m` writes is a RAM byte), `CapF9.logRam log`, and
  `CapF9.msgRamOf` (a message over a `ramBytes` footprint is `msgRam`);
* the hart-node inversions `CapF9.pnodeStoreInv` (an `LStore` comes from a non-device `memWrite`
  node; `SilPf.pnodeExStoreInv`'s twin) and `CapF9.pnodeRmwFalse` (no hart node emits `LRmw`);
* the disk inversion `CapF9.pstepDiskStore` (a disk `LStore` is `DWriteDev`'s store, whose
  footprint the disk program checked `ramBytes`).

The realization half (the hart's RAM footprint from the MachCSL thread's reducibility, `ramOfSafe`,
at every recorded step) is the next increment.

Spec: FAITHFUL (proof organisation).  Names: `CapF9.*`.
-/
import Weak.SilPfBridge
import Weak.PfStepTsoView

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open LeanRV64D
open Wlabel

/-- Every byte the message writes is a RAM byte. -/
def CapF9.msgRam (m : Wmsg) : Prop :=
  ∀ a, (msgByte m a).isSome → ∃ pa : PAddr, paZ pa = a ∧ inRam pa 1

/-- Every message of the log writes RAM bytes only. -/
def CapF9.logRam (log : List Wmsg) : Prop := ∀ m, m ∈ log → CapF9.msgRam m

theorem CapF9.logRamNil : CapF9.logRam [] := fun _ h => absurd h List.not_mem_nil

theorem CapF9.logRamSnoc (log : List Wmsg) (m : Wmsg) :
    CapF9.logRam log → CapF9.msgRam m → CapF9.logRam (log ++ [m]) := by
  intro h hm x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · rw [List.mem_singleton] at hx; subst hx; exact hm

/-- A message over a `ramBytes` footprint writes RAM bytes only. -/
theorem CapF9.msgRamOf (pa : PAddr) (data : List (BitVec 8)) (tid : Option Nat) (k : WmClass)
    (hram : ramBytes pa data.length) : CapF9.msgRam ⟨paZ pa, data, tid, k⟩ := by
  intro a h
  unfold msgByte at h
  dsimp only at h
  split at h
  · rename_i hle
    have hj : (a - paZ pa).toNat < data.length := by
      cases hx : data[(a - paZ pa).toNat]? with
      | none => rw [hx] at h; cases h
      | some _ => exact lookup_lt_Some hx
    have hfit := PfStepTsoView.ramBytesFit hram
    refine ⟨pa + BitVec.ofNat 64 (a - paZ pa).toNat, ?_, hram _ hj⟩
    rw [PfStepTsoMem.paZAddJ pa data.length _ (by omega) hj]
    unfold accAddr
    omega
  · cases h

theorem CapF9.pnodeStoreInv (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d (LStore rl base data asrc vsrc) m' ors fn' d' oib obar →
    ∃ n va req k, m = .impure (.ok (.memWrite n va req)) k ∧ devAddr req.pa = false ∧
      ∃ v, req.value = some v ∧ n ≠ 0 ∧
        rl = (classify req.access_kind).akSync ∧ base = paZ req.pa ∧
        data = WeakInterpProj.wbytes n v ∧ asrc = depsAsrc (depsOfIb ib.ibBits) ∧
        vsrc = depsVsrc (depsOfIb ib.ibBits) ∧ m' = k (.Ok (some true)) ∧ ors = none ∧
        fn' = none ∧ d' = d ∧ oib = none ∧ obar = none := by
  intro h
  match m, h with
  | .pure _, h => obtain ⟨_, h, _⟩ := h; exact nomatch h
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · obtain ⟨_, _, h, _⟩ := h; exact nomatch h
      · rcases h with ⟨_, _, _, _, _, h, _⟩ | ⟨_, ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, h, _⟩⟩ <;>
          exact nomatch h
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, h, _⟩ := h; exact nomatch h
        · exact h.elim
      · rename_i hdev
        split at h
        · rename_i v hv
          rcases h with ⟨hn, ⟨_, hl, hm, ho, hf, hd, hib, hbar⟩ | ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩⟩
          · simp only [LStore.injEq] at hl
            obtain ⟨h1, h2, h3, h4, h5⟩ := hl
            exact ⟨n, va, req, k, rfl, by simpa using hdev, v, hv, hn, h1, h2, h3, h4, h5, hm, ho,
              hf, hd, hib, hbar⟩
          · exact nomatch h
          · exact nomatch h
        · exact h.elim
    | regWrite r v =>
      obtain ⟨h, _⟩ := h
      rcases erwLabelCases (erwOf (depsOfIb ib.ibBits) ib.ibRds r) with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;>
        rw [h'] at h <;> exact nomatch h
    | barrier b =>
      obtain ⟨h, _⟩ := h
      obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b
      rw [h'] at h; exact nomatch h
    | choose p => obtain ⟨_, h, _⟩ := h; exact nomatch h
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | regRead => exact nomatch h.1
    | cacheOp => exact nomatch h.1
    | tlbi => exact nomatch h.1
    | translationStart => exact nomatch h.1
    | translationEnd => exact nomatch h.1
    | takeException => exact nomatch h.1
    | returnException => exact nomatch h.1
    | cycleCount => exact nomatch h.1
    | getCycleCount => exact nomatch h.1
    | message => exact nomatch h.1
    | instrAnnounce n w =>
      have h1 := h.1
      rcases annLabelOr n w with e | e <;> rw [e] at h1 <;> exact nomatch h1
    | branchAnnounce => exact nomatch h.1

theorem CapF9.pnodeRmwFalse (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
    (asrc vsrc : List Dsrc) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d (LRmw aq rl base tvs data asrc vsrc) m' ors fn' d' oib obar → False := by
  intro h
  match m, h with
  | .pure _, h => obtain ⟨_, h, _⟩ := h; exact nomatch h
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · obtain ⟨_, _, h, _⟩ := h; exact nomatch h
      · rcases h with ⟨_, _, _, _, _, h, _⟩ | ⟨_, ⟨_, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, h, _⟩⟩ <;>
          exact nomatch h
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, h, _⟩ := h; exact nomatch h
        · exact h.elim
      · rename_i hdev
        split at h
        · rename_i v hv
          rcases h with ⟨hn, ⟨_, h, _⟩ | ⟨ht, ⟨h, _⟩ | ⟨h, _⟩⟩⟩
          · exact nomatch h
          · exact nomatch h
          · exact nomatch h
        · exact h.elim
    | regWrite r v =>
      obtain ⟨h, _⟩ := h
      rcases erwLabelCases (erwOf (depsOfIb ib.ibBits) ib.ibRds r) with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩ <;>
        rw [h'] at h <;> exact nomatch h
    | barrier b =>
      obtain ⟨h, _⟩ := h
      obtain ⟨_, _, _, _, h'⟩ := ebarLabelFence b
      rw [h'] at h; exact nomatch h
    | choose p => obtain ⟨_, h, _⟩ := h; exact nomatch h
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | regRead => exact nomatch h.1
    | cacheOp => exact nomatch h.1
    | tlbi => exact nomatch h.1
    | translationStart => exact nomatch h.1
    | translationEnd => exact nomatch h.1
    | takeException => exact nomatch h.1
    | returnException => exact nomatch h.1
    | cycleCount => exact nomatch h.1
    | getCycleCount => exact nomatch h.1
    | message => exact nomatch h.1
    | instrAnnounce n w =>
      have h1 := h.1
      rcases annLabelOr n w with e | e <;> rw [e] at h1 <;> exact nomatch h1
    | branchAnnounce => exact nomatch h.1

/-- **A disk `LStore` is the `DWriteDev` store**, whose footprint is RAM. -/
theorem CapF9.pstepDiskStore (dp : Option (DM Dres)) (d : Efab) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (dp' : Option (DM Dres)) (d' : Efab) :
    pstepDisk dp d (LStore rl base data asrc vsrc) dp' d' →
    ∃ pa : PAddr, base = paZ pa ∧ ramBytes pa data.length := by
  rintro (⟨h, -⟩ | ⟨-, h, -⟩)
  · rcases h with ⟨-, hl, -⟩ | ⟨_, _, _, _, _, _, _, hl, _⟩ | ⟨_, _, hl, _⟩ |
      ⟨_, _, pa, bs, _, s, _, _, _, _, hram, _, hl, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hl, _⟩ |
      ⟨_, _, _, _, _, _, _, _, hl, _⟩ | ⟨_, _, _, _, hl, _⟩ | ⟨_, _, _, _, hl, _⟩ |
      ⟨_, hl, _⟩ | ⟨_, hl, _⟩
    · exact nomatch hl
    · exact nomatch hl
    · exact nomatch hl
    · simp only [LStore.injEq] at hl
      obtain ⟨-, rfl, rfl, -, -⟩ := hl
      exact ⟨pa s, rfl, hram⟩
    all_goals exact nomatch hl
  · exact nomatch h

end Weak
