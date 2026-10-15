/-
Weak: **r2 glue (C) — THE FETCH'S ADDRESSES, the walk of `fetch ()`** (`PROGRESS-r2glue.md`).
Lean-only.  `fqFetch`: from no fetch read at `PC = pc` in kernel-text pages, every fetch read of
`fetch ()` (`Fetch.lean:233-288`) is the `k`-th at `pc + 2k` — the 4-byte arm's one read at `PC`,
the 2-byte arm's first at `PC` and (a 32-bit word) second at `PC + 2`.  Every helper is
`Weak.PinFetchPa.*`.
-/
import Weak.PinFetchPaFq

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinFetchPa
open SailCycleOrderK SailCycleOrderFp PinFetchPaFp

section fetch
variable {c : TCfg} {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop} {pc : Int}


theorem toNatOfInt (pc : Int) (h0 : 0 ≤ pc) (h1 : pc < 2 ^ 64) :
    ((BitVec.ofInt 64 pc).toNat : Int) = pc := by
  rw [BitVec.toNat_ofInt]
  have : pc % (2 ^ 64 : Nat) = pc := Int.emod_eq_of_lt h0 (by simpa using h1)
  omega

theorem toNatOfInt2 (pc : Int) (h0 : 0 ≤ pc) (h1 : pc + 2 < 2 ^ 64) :
    ((BitVec.addInt (BitVec.ofInt 64 pc) 2).toNat : Int) = pc + 2 := by
  rw [BitVec.addInt, ← BitVec.ofInt_add]
  exact toNatOfInt (pc + 2) (by omega) h1


/-- A leaf under the trivial post. -/
theorem fqTrueLeaf {X : Type} (x : X) (i : Nat) : fqB c D pc (fun _ _ => True) (pure x) i := trivial

/-- **The 4-byte / first 2-byte arm's read** at `PC` (count 0). -/
theorem fqFBAt0 {Y : Type} (P : Y → Nat → Prop) (w : Nat) (c1 : TCfg)
    (hc1 : fqCfg c D (BitVec.ofInt 64 pc) c1)
    (hg1 : ((BitVec.ofInt 64 pc).toNat : Int) = pc + 2 * ((0 : Nat) : Int))
    (f : FetchBytes_Result w → SailM Y)
    (h : ∀ r i', (∀ b, r = .FetchBytes_Success b → i' = 1) → fqB c D pc P (f r) i') :
    fqB c D pc P (fetch_bytes (BitVec.ofInt 64 pc) (BitVec.ofInt 64 pc) w >>= f) 0 :=
  fqBind _ _ _ _ 0 (fqFetchBytes _ _ w 0 c1 hc1 hg1) h

/-- **The second 2-byte read** at `PC + 2` (count 1). -/
theorem fqFBAt1 {Y : Type} (P : Y → Nat → Prop) (c2 : TCfg)
    (hc2 : fqCfg c D (BitVec.addInt (BitVec.ofInt 64 pc) 2) c2)
    (hg2 : ((BitVec.addInt (BitVec.ofInt 64 pc) 2).toNat : Int) = pc + 2 * ((1 : Nat) : Int))
    (f : FetchBytes_Result 2 → SailM Y)
    (h : ∀ r i', fqB c D pc P (f r) i') :
    fqB c D pc P (fetch_bytes (BitVec.ofInt 64 pc) (BitVec.addInt (BitVec.ofInt 64 pc) 2) 2 >>= f) 1 :=
  fqBind _ _ _ _ 1 (fqFetchBytes _ _ 2 1 c2 hc2 hg2) (fun r i' _ => h r i')

/-- The 4-byte arm after its `PC` reads (one read at `PC`). -/
macro "fq_arm4" c1:term:max hc1:term:max hg1:term:max : tactic => `(tactic| (
  refine fqFBAt0 _ 4 $c1 $hc1 $hg1 _ (fun r i' _ => ?_)
  cases r with
  | FetchBytes_Ext_Error e => exact fqTrueLeaf _ _
  | FetchBytes_Exception e =>
    simp only [ExceptT.run_bind, run_liftM, bind_assoc, ExceptT.run_pure]
    exact fqReadPC _ _ _ (fqTrueLeaf _ _)
  | FetchBytes_Success b =>
    simp only []
    split <;> exact fqTrueLeaf _ _))

/-- The 2-byte arm after its `PC` reads (a read at `PC`, a second at `PC + 2`). -/
macro "fq_arm2" c1:term:max hc1:term:max hg1:term:max c2:term:max hc2:term:max hg2:term:max :
    tactic => `(tactic| (
  refine fqFBAt0 _ 2 $c1 $hc1 $hg1 _ (fun r i' hr => ?_)
  cases r with
  | FetchBytes_Ext_Error e => exact fqTrueLeaf _ _
  | FetchBytes_Exception e =>
    simp only [ExceptT.run_bind, run_liftM, bind_assoc, ExceptT.run_pure]
    exact fqReadPC _ _ _ (fqTrueLeaf _ _)
  | FetchBytes_Success b =>
    have e := hr _ rfl
    subst e
    simp only []
    split
    · exact fqTrueLeaf _ _
    · simp only [ExceptT.run_bind, run_liftM, bind_assoc, ExceptT.run_pure, pure_bind]
      refine fqReadPC _ _ _ (fqReadPC _ _ _ ?_)
      refine fqFBAt1 _ $c2 $hc2 $hg2 _ (fun r i' => ?_)
      cases r with
      | FetchBytes_Ext_Error e => exact fqTrueLeaf _ _
      | FetchBytes_Exception e =>
        simp only [ExceptT.run_bind, run_liftM, bind_assoc, ExceptT.run_pure]
        exact fqReadPC _ _ _ (fqTrueLeaf _ _)
      | FetchBytes_Success b' => exact fqTrueLeaf _ _))

set_option maxHeartbeats 40000000 in
/-- **THE FETCH'S ADDRESSES** (header). -/
theorem fqFetch (pc : Int) (h0 : 0 ≤ pc) (hlt : pc + 2 < 2 ^ 64) (c1 c2 : TCfg)
    (hc1 : fqCfg c D (BitVec.ofInt 64 pc) c1) (hc2 : fqCfg c D (BitVec.addInt (BitVec.ofInt 64 pc) 2) c2) :
    fqB c D pc (fun _ _ => True) (fetch ()) 0 := by
  have hg1 : ((BitVec.ofInt 64 pc).toNat : Int) = pc + 2 * ((0 : Nat) : Int) := by
    rw [toNatOfInt pc h0 (by omega)]; simp
  have hg2 : ((BitVec.addInt (BitVec.ofInt 64 pc) 2).toNat : Int) = pc + 2 * ((1 : Nat) : Int) := by
    rw [toNatOfInt2 pc h0 hlt]; simp
  simp only [fetch, ext_fetch_check_pc, get_config_rvfi, SailME.run, PreSail.PreSailME.run,
    ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, Bool.false_eq_true, ↓reduceIte]
  refine fqReadPC _ _ _ ?_
  refine fqReadPC _ _ _ ?_
  refine fqReadPC _ _ _ ?_
  refine fqBind (fun _ _ => True) _ _ _ 0 ?_ ?_
  rotate_left
  · intro r i' _
    rcases r with (e | e) | e <;> exact trivial
  simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure,
    PinFetchVal.runIte, PinFetchVal.iteBind, Bool.false_eq_true, ↓reduceIte]
  -- the arms
  split
  · exact fqReadPC _ _ _ (fqTrueLeaf _ _)
  · refine fqReadPC _ _ _ ?_
    try dsimp only
    split
    · refine fqXfBind _ _ _ _ _ (xfCurrentlyEnabled _) (fun _ _ => ?_)
      split
      · exact fqReadPC _ _ _ (fqTrueLeaf _ _)
      · refine fqReadPC _ _ _ ?_
        try dsimp only
        split
        · refine fqXfBind _ _ _ _ _ (xfCurrentlyEnabled _) (fun _ _ => ?_)
          split
          · refine fqReadPC _ _ _ (fqReadPC _ _ _ ?_)
            fq_arm4 c1 hc1 hg1
          · refine fqReadPC _ _ _ (fqReadPC _ _ _ ?_)
            fq_arm2 c1 hc1 hg1 c2 hc2 hg2
        · refine fqReadPC _ _ _ (fqReadPC _ _ _ ?_)
          fq_arm2 c1 hc1 hg1 c2 hc2 hg2
    · refine fqReadPC _ _ _ ?_
      try dsimp only
      split
      · refine fqXfBind _ _ _ _ _ (xfCurrentlyEnabled _) (fun _ _ => ?_)
        split
        · refine fqReadPC _ _ _ (fqReadPC _ _ _ ?_)
          fq_arm4 c1 hc1 hg1
        · refine fqReadPC _ _ _ (fqReadPC _ _ _ ?_)
          fq_arm2 c1 hc1 hg1 c2 hc2 hg2
      · refine fqReadPC _ _ _ (fqReadPC _ _ _ ?_)
        fq_arm2 c1 hc1 hg1 c2 hc2 hg2

end fetch

end PinFetchPa
end Weak
