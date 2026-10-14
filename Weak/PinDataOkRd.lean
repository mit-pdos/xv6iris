/-
Weak: **`dataOkR` (3d) — the PTE reads under `dkB`**: `read_pte` / `read_pte_exclusive` at a walk
slot (RAM, aligned) answer `Ok w` with `w` `dAns`-admitted, never `Err`.  Mirrors
`Weak/PinFetchPaRd.lean`; `PROGRESS-dataOk.md`.  Lean-only.  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkPmp
import Weak.PinFetchPaRd

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinFetchPaFp

variable {c : DCfg}

/-- Two `dkB` facts of one tree. -/
theorem dkAnd {X : Type} (P Q : X → Prop) :
    ∀ (m : SailM X), dkB c P m → dkB c Q m → dkB c (fun x => P x ∧ Q x) m := by
  intro m
  induction m with
  | pure y => exact fun h1 h2 => ⟨h1, h2⟩
  | impure call k ih =>
    intro h1 h2
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead => exact fun w hw => ih _ (h1 w hw) (h2 w hw)
      case memWrite => exact ih _ h1 h2
      case regRead => exact fun v hv => ih v (h1 v hv) (h2 v hv)
      all_goals exact fun v => ih v (h1 v) (h2 v)

/-- `dAns` reads the answer's number only. -/
theorem dAnsOfNat {pa : BitVec 64} (n : Nat) (w : BitVec (8 * n)) (d : BitVec 64) (hn : n = 8)
    (h : d.toNat = w.toNat) (hw : dAns c pa n w) : dAns c pa 8 d := by
  intro _
  obtain ⟨h2, h1, h0⟩ := hw hn
  refine ⟨fun e => h.trans (h2 e), fun e => h.trans (h1 e), fun e => ?_⟩
  obtain ⟨a, d', e'⟩ := h0 e
  exact ⟨a, d', h.trans e'⟩

/-- **The RAM read leaf**: the answer is `dAns`-admitted at the request's address. -/
theorem dkReadRam (rk : read_kind) (pa : BitVec 64) (n : Nat) :
    dkB c (fun r => dAns c pa n r.1) (read_ram rk (.Physaddr pa) n false) := by
  cases rk <;>
  simp only [read_ram, PreSail.sail_mem_read, PreSail.emit, pure_bind, bind_assoc] <;>
  first
    | (intro w hw; exact hw)
    | trivial
    | (simp only [internal_error]; trivial)

set_option maxHeartbeats 40000000 in
/-- `checked_mem_read` of a PTE: `Ok (d, _)` only after ONE read at `pa` answering `d`. -/
theorem dkCheckedMemReadPteVal (pa : BitVec 64) (hram : 0x80000000 ≤ pa.toNat) (hal : pa.toNat % 8 = 0)
    (res : Bool) :
    dkB c (fun r => ∀ d m, r = .Ok (d, m) → dAns c pa 8 d)
      (checked_mem_read (.Load .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr pa) 8 false false res false) := by
  cases res <;>
  simp only [checked_mem_read, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM,
    bind_assoc, pure_bind, ExceptT.run_pure, read_kind_of_flags] <;>
  refine dkXfBind _ _ _ _ (PinFetchPa.xfCheckPmaPmp _ _ _ _ _ _) (fun r _ => ?_)
  all_goals
    cases r with
    | Err e =>
      simp only [run_SailME_throw, pure_bind]
      intro d m h; cases h
    | Ok info =>
      simp only [ExceptT.run_pure, pure_bind]
      rw [bind_assoc]
      have htm : Int.tmod (BitVec.toNatInt pa) 8 = 0 := by
        simp only [BitVec.toNatInt]
        rw [Int.ofNat_eq_natCast, show (8 : Int) = ((8 : Nat) : Int) from rfl, ← Int.ofNat_tmod, hal]; rfl
      refine dkXfBind _ _ _ _ (xfSplitAligned pa 8 _ _ htm) (fun p hp => ?_)
      subst hp
      simp only [untilFuelM, misaligned_order, sys_misaligned_order_decreasing,
        Bool.false_eq_true, ↓reduceIte]
      rw [show Int.toNat 1 = 0 + 1 from rfl]
      simp only [untilFuelM.go, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine dkXfBind _ _ _ _ (PinDataOk.xfAssertTrue _) (fun _ _ => ?_)
      refine dkXfBind _ _ _ _ (xfPmpCheck _ _ _ _) (fun o _ => ?_)
      have hr0 : 0x80000000 ≤ (bits_of_physaddr (physaddr.Physaddr
          (BitVec.addInt (bits_of_physaddr (physaddr.Physaddr pa)) (↑(Int.toNat 0) * ↑8)))).toNat := by
        rw [SailCycleOrderFp.addInt0]; exact hram
      cases o with
      | some e =>
        simp only []
        intro d m h; cases h
      | none =>
        simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
        refine dkXfBind _ _ _ _ (xfWithinMmioRam _ _ hr0) (fun b hb => ?_)
        subst hb
        simp only [Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
        refine dkBind _ _ _ _ (dkReadRam _ _ _) (fun r hr => ?_)
        have hc : (Int.toNat 0 == (1 - 1 : Int).toNat) = true := by decide
        simp only [hc, ↓reduceIte, ExceptT.run_pure, pure_bind]
        intro d m h
        injection h with h
        injection h with h1 _
        subst h1
        refine dAnsOfNat _ _ _ rfl ?_ (by rw [SailCycleOrderFp.addInt0] at hr; exact hr)
        show (BitVec.setWidth 64 (BitVec.setWidth 64 (BitVec.setWidth 64 (Sail.BitVec.updateSubrange
          (BitVec.setWidth 64 (zeros (n := 64))) 63 0 (BitVec.setWidth 64 r.1))))).toNat = r.1.toNat
        exact congrArg BitVec.toNat (PinFetchPa.cmrVal8 r.1)

/-- The PTE read's post: never `Err`, `Ok w` with `w` filter-admitted. -/
def pteRdPost (c : DCfg) (pa : BitVec 64) (r : Result (BitVec (8 * 8)) (physaddr × ExceptionType)) : Prop :=
  (∀ e, r ≠ .Err e) ∧ ∀ w, r = .Ok w → dAns c pa 8 w

theorem PinDataOk.ramOf8 {pa : BitVec 64} (hram : 0x80000000 ≤ pa.toNat) (hhi : pa.toNat + 8 ≤ 0x88000000) :
    inRam pa 8 := ⟨hram, hhi⟩

set_option maxHeartbeats 40000000 in
theorem dkReadPteGen (pa : BitVec 64) (hram : 0x80000000 ≤ pa.toNat) (hhi : pa.toNat + 8 ≤ 0x88000000)
    (hal : pa.toNat % 8 = 0) (res : Bool) :
    dkB c (fun r => (∀ e, (MemoryOpResult_drop_meta r) ≠ .Err e) ∧
        ∀ w, MemoryOpResult_drop_meta r = .Ok w → dAns c pa 8 w)
      (mem_read_priv_meta (.Load .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr pa) 8 false false res false) := by
  simp only [mem_read_priv_meta]
  cases res <;> (try simp only [bind_assoc, pure_bind]) <;>
  refine dkBind _ _ _ _ (dkAnd _ _ _ (dkCheckedMemReadOk pa 8 _ _ (Or.inr rfl) ⟨hram, hhi⟩ (by decide)
    (by decide) hal .Supervisor) (dkCheckedMemReadPteVal pa hram hal _)) (fun r h => ?_) <;>
  (refine ⟨fun e he => ?_, fun w hw => ?_⟩ <;>
    cases r with
    | Ok q =>
      obtain ⟨d, m⟩ := q
      first
        | (simp only [MemoryOpResult_drop_meta] at he; cases he)
        | (simp only [MemoryOpResult_drop_meta] at hw
           injection hw with hw
           subst hw
           exact h.2 _ m rfl)
    | Err e' =>
      first
        | (exact absurd rfl (h.1 e'))
        | (simp [MemoryOpResult_drop_meta] at hw))

/-- **`read_pte`** at a walk slot: never `Err`, the answer filter-admitted. -/
theorem dkReadPte (pa : BitVec 64) (hram : 0x80000000 ≤ pa.toNat) (hhi : pa.toNat + 8 ≤ 0x88000000)
    (hal : pa.toNat % 8 = 0) : dkB c (pteRdPost c pa) (read_pte (.Physaddr pa) 8) := by
  simp only [read_pte, mem_read_priv]
  exact dkBind _ _ _ _ (dkReadPteGen pa hram hhi hal false) (fun r h => h)

/-- **`read_pte_exclusive`** (the Svadu re-read): as `read_pte`. -/
theorem dkReadPteExclusive (pa : BitVec 64) (hram : 0x80000000 ≤ pa.toNat) (hhi : pa.toNat + 8 ≤ 0x88000000)
    (hal : pa.toNat % 8 = 0) : dkB c (pteRdPost c pa) (read_pte_exclusive (.Physaddr pa) 8) := by
  simp only [read_pte_exclusive, mem_read_priv]
  exact dkBind _ _ _ _ (dkReadPteGen pa hram hhi hal true) (fun r h => h)

end PinDataOk
end Weak
