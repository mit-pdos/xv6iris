/-
Weak: **W11-C2′ (a3) relArmed — the two release sites' instructions** (`PROGRESS-relArmed.md`).
Lean-only.

The arming fences `release+0x16`, `main+0xac` (`fence rw,w`, word `0x0310000f`) and the release
stores `release+0x1a` (`sw zero,0(s1)`, `0x0004a023`) and `main+0xb0` (`c.sw`, a compressed
store), decided over the image; the FENCE's execute under `amB` arms the flag.

Every helper is `Weak.PinRelArm.*`.
-/
import Weak.PinRelArmSail

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel KernelPinsDef

namespace PinRelArm
open SailCycleOrderK PinCycRun PinRelArmFp PinDataflow

/-! ## 1. The FENCE arms -/

theorem armBarRwW (a : Bool) : armBar .Barrier_RISCV_rw_w a = true := by
  cases a <;> rfl

set_option maxHeartbeats 4000000 in
/-- **`fence rw,w` under `amB`** (header): it retires with the flag ARMED (its barrier is
`Barrier_RISCV_rw_w` whatever `menvcfg.FIOM`, `effective_fence_set` only ORs the I/O bits into
the R/W bits). -/
theorem amExecFence {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop} (fm : BitVec 4)
    (rs rd : regidx) (st : AmSt) (ha : st.amo = false) :
    amB A Aa (execPostAm true) (uxaExecAs (.FENCE (fm, 3#4, 1#4, rs, rd))) st := by
  unfold uxaExecAs
  simp only [execute, execute_FENCE, is_fiom_active, bind_assoc]
  refine amReadBind _ _ _ _ (fun p _ hg => ?_)
  obtain rfl : p = Privilege.Supervisor := hg _ rfl
  simp only
  refine amReadBind _ _ _ _ (fun me _ _ => ?_)
  generalize (_get_MEnvcfg_FIOM me == 1#1) = b
  dsimp only
  have he : (Sail.BitVec.extractLsb (effective_fence_set (3#4) b) 1 0,
      Sail.BitVec.extractLsb (effective_fence_set (1#4) b) 1 0) = (3#2, 1#2) := by
    cases b <;> decide
  rw [he]
  exact Or.inl ⟨rfl, ha, fun _ => armBarRwW st.armed⟩

/-! ## 2. The arming fences, decided -/

/-- The arming fences of the two release sites. -/
def relFencePcs : List Int := [(KernelSyms.«release» : Int) + 0x16, (KernelSyms.«main» : Int) + 0xac]

theorem relFenceText : ∀ pc ∈ relFencePcs, textLo ≤ pc ∧ pc + 3 < textHi := by decide +kernel

/-- The decoded instruction is a `fence rw,w`. -/
def isFenceRwW : Option instruction → Bool
  | some (.FENCE (_, p, s, _, _)) => p == 3#4 && s == 1#4
  | _ => false

theorem isFenceRwWOf (o : Option instruction) (h : isFenceRwW o = true) :
    ∃ fm rs rd, o = some (.FENCE (fm, 3#4, 1#4, rs, rd)) := by
  match o, h with
  | some (.FENCE (fm, p, s, rs, rd)), h =>
    simp only [isFenceRwW, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fm, rs, rd, rfl⟩

theorem relFenceDecB : ∀ pc ∈ relFencePcs, isFenceRwW (PinWalkTab.decS pc) = true := by
  decide +kernel

theorem relFenceRvc : ∀ pc ∈ relFencePcs, wIsRvc (kw pc) = false := by decide +kernel

theorem relFenceAmo : ∀ pc ∈ relFencePcs, WbPrimed.ibAmo (ibAnn (ibOfBvn (kword pc))) = false := by
  decide +kernel

/-- **THE FENCE CYCLE** (header): at an arming fence, every cycle started with an empty log and
no AMO bit ends (if it ends) with the flag ARMED. -/
theorem fenceCycle (pc : Int) (hpc : pc ∈ relFencePcs) (tick : Bool) (st : AmSt) (hfe : st.fe = [])
    (ha : st.amo = false) :
    amB kA (kAa pc) (fun _ st' => true = true → st'.armed = true) (riscvStep tick) st := by
  obtain ⟨fm, rs, rd, hd⟩ := isFenceRwWOf _ (relFenceDecB pc hpc)
  exact amSailOf pc (relFenceText pc hpc) _ hd (relFenceRvc pc hpc) (relFenceAmo pc hpc)
    false true (fun st' ha' _ => amExecFence _ _ _ st' ha') tick st hfe ha (fun h => by cases h)

end PinRelArm
end Weak
