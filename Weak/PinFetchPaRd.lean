/-
Weak: **W9a (B) B5 r2 part (B) — the PTE read's value chain under `tvB`** (`read_pte`,
`read_pte_exclusive` at a RAM, 8-aligned slot: `Ok w` only after ONE memory read at the slot
answering `w`, so `w` is `tvAns`-admitted; plan rev 52 §D Q-B5-FETCH (r2-a), `PROGRESS-r2.md`).
Lean-only.  Every helper is `Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPa
import Weak.PinFetchPaXf

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchPa
open SailCycleOrderK PinFetchPaFp

variable {c : TCfg}

/-- `tvAns` reads the answer's number only. -/
theorem tvAnsCongr {pa : BitVec 64} {n : Nat} {w d : BitVec (8 * n)} (h : d.toNat = w.toNat)
    (hw : tvAns c pa n w) : tvAns c pa n d := by
  intro hn
  obtain ⟨h2, h1, h0⟩ := hw hn
  exact ⟨fun e => h ▸ h2 e, fun e => h ▸ h1 e, fun e => h ▸ h0 e⟩

/-- `tvAns` at a width-`n` read with `n = 8`, transported to a 64-bit word of the same number. -/
theorem tvAnsOfNat {pa : BitVec 64} (n : Nat) (w : BitVec (8 * n)) (d : BitVec 64) (hn : n = 8)
    (h : d.toNat = w.toNat) (hw : tvAns c pa n w) : tvAns c pa 8 d := by
  intro _
  obtain ⟨h2, h1, h0⟩ := hw hn
  refine ⟨fun e => h.trans (h2 e), fun e => h.trans (h1 e), fun e => ?_⟩
  obtain ⟨a, d', e'⟩ := h0 e
  exact ⟨a, d', h.trans e'⟩

/-- The loop's one-chunk assembly is the chunk (width 8). -/
theorem cmrVal8 (v : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 64 (BitVec.setWidth 64 (Sail.BitVec.updateSubrange
      (BitVec.setWidth 64 (zeros (n := 64))) 63 0 (BitVec.setWidth 64 v)))) = v := by
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros]
  bv_decide

/-- **The RAM read leaf**: the answer is `tvAns`-admitted at the request's address. -/
theorem tvReadRam (rk : read_kind) (pa : BitVec 64) (n : Nat) :
    tvB c (fun r => tvAns c pa n r.1) (read_ram rk (.Physaddr pa) n false) := by
  cases rk <;>
  simp only [read_ram, PreSail.sail_mem_read, PreSail.emit, pure_bind, bind_assoc] <;>
  first
    | (intro w hw; exact hw)
    | trivial
    | (simp only [internal_error]; trivial)
    | trace_state

set_option maxHeartbeats 40000000 in
/-- The PMA-with-PMP check: a footprint. -/
@[xf_reg] theorem xfCheckPmaPmp (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (priv : Privilege) (pa : physaddr) (w : Nat) (rc : Bool) :
    xfT (check_pma_with_pmp_priority acc pbmt priv pa w rc) := by
  unfold check_pma_with_pmp_priority
  xf_walk

set_option maxHeartbeats 40000000 in
/-- **`checked_mem_read` of a PTE** (8 bytes, RAM, aligned): `Ok (d, _)` only after ONE read at
`pa` answering `d`. -/
theorem tvCheckedMemReadPte (pa : BitVec 64) (hram : 0x80000000 ≤ pa.toNat) (hal : pa.toNat % 8 = 0)
    (res : Bool) :
    tvB c (fun r => ∀ d m, r = .Ok (d, m) → tvAns c pa 8 d)
      (checked_mem_read (.Load .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr pa) 8 false false res false) := by
  cases res <;>
  simp only [checked_mem_read, SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM,
    bind_assoc, pure_bind, ExceptT.run_pure, read_kind_of_flags] <;>
  refine tvXfBind _ _ _ _ (xfCheckPmaPmp _ _ _ _ _ _) (fun r _ => ?_)
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
      refine tvXfBind _ _ _ _ (xfSplitAligned pa 8 _ _ htm) (fun p hp => ?_)
      subst hp
      simp only [untilFuelM, misaligned_order, sys_misaligned_order_decreasing,
        Bool.false_eq_true, ↓reduceIte]
      rw [show Int.toNat 1 = 0 + 1 from rfl]
      simp only [untilFuelM.go, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
      refine tvXfBind _ _ _ _ (by xf_walk : xfT (assert true "loop dummy assert")) (fun _ _ => ?_)
      refine tvXfBind _ _ _ _ (xfPmpCheck _ _ _ _) (fun o _ => ?_)
      have hr0 : 0x80000000 ≤ (bits_of_physaddr (physaddr.Physaddr
          (BitVec.addInt (bits_of_physaddr (physaddr.Physaddr pa)) (↑(Int.toNat 0) * ↑8)))).toNat := by
        rw [SailCycleOrderFp.addInt0]; exact hram
      cases o with
      | some e =>
        simp only []
        intro d m h; cases h
      | none =>
        simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
        refine tvXfBind _ _ _ _ (xfWithinMmioRam _ _ hr0) (fun b hb => ?_)
        subst hb
        simp only [Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
        refine tvBind _ _ _ _ (tvReadRam _ _ _) (fun r hr => ?_)
        have hc : (Int.toNat 0 == (1 - 1 : Int).toNat) = true := by decide
        simp only [hc, ↓reduceIte, ExceptT.run_pure, pure_bind]
        intro d m h
        injection h with h
        injection h with h1 _
        subst h1
        refine tvAnsOfNat _ _ _ rfl ?_ (by rw [SailCycleOrderFp.addInt0] at hr; exact hr)
        show (BitVec.setWidth 64 (BitVec.setWidth 64 (BitVec.setWidth 64 (Sail.BitVec.updateSubrange
          (BitVec.setWidth 64 (zeros (n := 64))) 63 0 (BitVec.setWidth 64 r.1))))).toNat = r.1.toNat
        exact congrArg BitVec.toNat (cmrVal8 r.1)

set_option maxHeartbeats 40000000 in
/-- **`read_pte`** (8 bytes, RAM, aligned): `Ok w` only with `w` `tvAns`-admitted at `pa`. -/
theorem tvReadPte (pa : BitVec 64) (hram : 0x80000000 ≤ pa.toNat) (hal : pa.toNat % 8 = 0) :
    tvB c (fun r => ∀ w, r = .Ok w → tvAns c pa 8 w) (read_pte (.Physaddr pa) 8) := by
  simp only [read_pte, mem_read_priv, mem_read_priv_meta, bind_assoc, pure_bind]
  refine tvBind _ _ _ _ (tvCheckedMemReadPte pa hram hal false) (fun r h => ?_)
  intro w hw
  cases r with
  | Ok q =>
    obtain ⟨d, m⟩ := q
    simp only [MemoryOpResult_drop_meta] at hw
    injection hw with hw
    subst hw
    exact h _ m rfl
  | Err e => simp [MemoryOpResult_drop_meta] at hw

set_option maxHeartbeats 40000000 in
/-- **`read_pte_exclusive`** (the Svadu re-read): as `read_pte`. -/
theorem tvReadPteExclusive (pa : BitVec 64) (hram : 0x80000000 ≤ pa.toNat) (hal : pa.toNat % 8 = 0) :
    tvB c (fun r => ∀ w, r = .Ok w → tvAns c pa 8 w) (read_pte_exclusive (.Physaddr pa) 8) := by
  simp only [read_pte_exclusive, mem_read_priv, mem_read_priv_meta, bind_assoc, pure_bind]
  refine tvBind _ _ _ _ (tvCheckedMemReadPte pa hram hal true) (fun r h => ?_)
  intro w hw
  cases r with
  | Ok q =>
    obtain ⟨d, m⟩ := q
    simp only [MemoryOpResult_drop_meta] at hw
    injection hw with hw
    subst hw
    exact h _ m rfl
  | Err e => simp [MemoryOpResult_drop_meta] at hw

end PinFetchPa
end Weak
