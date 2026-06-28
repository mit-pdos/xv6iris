/-
The xv6 kernel's first two instructions encoded as a **weakest-precondition**
over the program logic (Plan 1: full-state pinning), rather than a direct `exec`
statement. The boot config (Machine mode, fixed PMA, etc.) is baked into a custom
`stateInterp`; the WP owns the registers that change (`PC`, `sp`, `minstret`); the
real instruction semantics are discharged by kernel reduction (`with_unfolding_all
rfl`) of the generated `try_step`.

Self-contained GS (own register/memory `gen_heap`s) so it doesn't clash with the
`IrisGS` instance in `RealPtsto.lean`.
-/
import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.BI.Lib.GenHeap
import Iris.ProofMode
import Xv6Iris.Model
import Xv6Iris.RealRegs
import Xv6Iris.RealPtsto

open Iris Iris.BI Iris.ProgramLogic Std
open LeanRV64D.Defs

-- Reuse `RealPtsto`'s ghost-state (`RiscvGS`, `regPt`, `reg_valid`/`reg_update`,
-- `stateInterpDef`); the boot `stateInterp`/`IrisGS` instances below are given high
-- priority so they win over `RealPtsto`'s (the boot config is pinned in the state
-- interpretation).

set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000000

namespace Xv6Iris.Model.KernelWP

/-! ## Boot machine image -/

noncomputable def ramPMA : PMA := { (default : PMA) with
  executable := true, readable := true, writable := true }
noncomputable def ramRegion : PMA_Region :=
  { base := 0x80000000#64, size := 0x10000000#64, attributes := ramPMA, include_in_device_tree := false }

/-- `auipc sp,0xa` (0x0000a117) at 0x80000000, `ld sp,472(sp)` (0x1d813103) at
0x80000004, and the 8-byte value 0x0123456789ABCDEF at sp+472 = 0x8000A1D8. -/
noncomputable def mem0 : Nat → Option (BitVec 8) := fun a =>
  if a = 0x80000000 then some 0x17 else if a = 0x80000001 then some 0xa1
  else if a = 0x80000002 then some 0x00 else if a = 0x80000003 then some 0x00
  else if a = 0x80000004 then some 0x03 else if a = 0x80000005 then some 0x31
  else if a = 0x80000006 then some 0x81 else if a = 0x80000007 then some 0x1d
  else if a = 0x8000A1D8 then some 0xEF else if a = 0x8000A1D9 then some 0xCD
  else if a = 0x8000A1DA then some 0xAB else if a = 0x8000A1DB then some 0x89
  else if a = 0x8000A1DC then some 0x67 else if a = 0x8000A1DD then some 0x45
  else if a = 0x8000A1DE then some 0x23 else if a = 0x8000A1DF then some 0x01
  else some 0#8

/-- The fixed boot register values for every register *except* the ones that
change during the two instructions (`PC`, `x2`, `minstret`, `minstret_increment`). -/
noncomputable def bootRegs : (r : Register) → Option (RegisterType r) := fun r =>
  match r with
  | .cur_privilege => some Privilege.Machine
  | .misa => some (BitVec.allOnes 64)
  | .pma_regions => some [ramRegion]
  | r => some (decReg r 0)

/-- The boot machine state, parameterized by the registers that change across the
two instructions: `PC`, `sp`(=x2), `minstret`, `minstret_increment`, `nextPC`. -/
noncomputable def mkBoot (pc sp m : BitVec 64) (mi : Bool) (npc : BitVec 64) : MState where
  regs r := match r with
    | .PC => some pc
    | .x2 => some sp
    | .minstret => some m
    | .minstret_increment => some mi
    | .nextPC => some npc
    | r => bootRegs r
  mem := mem0

/-! ## The two real-instruction reduction lemmas (kernel reduction of `try_step`)

Each is a *full-state* transition: the result is again a `mkBoot`. The write set
`{PC, x2, minstret, minstret_increment, nextPC}` was found by `funext`; `mem` is
untouched. Proved by kernel reduction once (`exec` is shared across the 180
register cases), so this is feasible despite the size. -/

/-- Step 1 — `auipc sp,0xa`: `PC,nextPC := entry+4`, `sp := entry+0xa000`,
`minstret += 1`. Independent of the old `sp`/`minstret_increment`/`nextPC`. -/
theorem red_auipc (sp m : BitVec 64) (mi : Bool) (npc : BitVec 64) :
    (exec riscv_step (mkBoot 0x80000000 sp m mi npc)).map (fun p => p.2)
      = some (mkBoot 0x80000004 0x8000A000 (m + 1) true 0x80000004) := by
  have hs : (exec riscv_step (mkBoot 0x80000000 sp m mi npc)).map (fun p => p.2)
      = some ((exec riscv_step (mkBoot 0x80000000 sp m mi npc)).get (by with_unfolding_all rfl)).2 := by
    with_unfolding_all rfl
  rw [hs]; congr 1
  apply MState.ext
  · funext r; cases r <;> with_unfolding_all rfl
  · with_unfolding_all rfl

/-- Step 2 — `ld sp,472(sp)`: loads the doubleword at `sp+472`. Here `sp` is the
concrete post-auipc value `0x8000A000` (ld reads it as the base address). -/
theorem red_ld (m : BitVec 64) (mi : Bool) (npc : BitVec 64) :
    (exec riscv_step (mkBoot 0x80000004 0x8000A000 m mi npc)).map (fun p => p.2)
      = some (mkBoot 0x80000008 0x0123456789ABCDEF (m + 1) true 0x80000008) := by
  have hs : (exec riscv_step (mkBoot 0x80000004 0x8000A000 m mi npc)).map (fun p => p.2)
      = some ((exec riscv_step (mkBoot 0x80000004 0x8000A000 m mi npc)).get (by with_unfolding_all rfl)).2 := by
    with_unfolding_all rfl
  rw [hs]; congr 1
  apply MState.ext
  · funext r; cases r <;> with_unfolding_all rfl
  · with_unfolding_all rfl

/-! ## Boot state interpretation + WP

The state interp pins the machine to boot form (`σ = mkBoot …`); the WP owns the
five registers the two instructions touch (`PC, x2, minstret, nextPC` are
bit-vectors and visible; `minstret_increment` is `Bool`, encoded as junk `0` and
hence invisible to the heap — so the WP need not own it). -/

section BootWP
variable {GF : BundledGFunctors} {hlc : HasLC} [D : RiscvGS hlc GF]

/-- `stateInterpDef` depends on the state only through the *encoded* register
values and memory, so states agreeing there have equal interpretations. This is
what makes `minstret_increment`'s change (junk-encoded) invisible. -/
theorem stateInterpDef_eq {σ σ' : MState}
    (hr : ∀ r, (σ.regs r).map (encReg r) = (σ'.regs r).map (encReg r))
    (hm : σ.mem = σ'.mem) :
    (stateInterpDef σ : IProp GF) = stateInterpDef σ' := by
  have er : (fun rm => regAgree rm σ.regs) = (fun rm => regAgree rm σ'.regs) := by
    funext rm; unfold regAgree; simp only [hr]
  unfold stateInterpDef
  rw [show (fun (rm : RegF (BitVec 64)) => iprop(∃ mm, genHeapInterp (G := D.reg) rm ∗
        genHeapInterp (G := D.mem) mm ∗ ⌜regAgree rm σ.regs⌝ ∗ ⌜memAgree mm σ.mem⌝))
      = (fun rm => iprop(∃ mm, genHeapInterp (G := D.reg) rm ∗
        genHeapInterp (G := D.mem) mm ∗ ⌜regAgree rm σ'.regs⌝ ∗ ⌜memAgree mm σ'.mem⌝)) from ?_]
  funext rm; congr 1; funext mm; rw [hm]
  have : regAgree rm σ.regs = regAgree rm σ'.regs := congrFun er rm
  rw [this]

/-- Boot state interpretation: the heap agreement plus the pin `σ = mkBoot …`. -/
def stateInterpBoot (σ : MState) : IProp GF :=
  iprop(stateInterpDef σ ∗ ⌜∃ (pc sp m npc : BitVec 64) (mi : Bool), σ = mkBoot pc sp m mi npc⌝)

/-- Split the boot interp at the Lean level (the proofmode `icases` won't unfold
the `stateInterp` typeclass projection, but lemma application does). -/
theorem boot_split {σ : MState} :
    (stateInterpBoot σ : IProp GF) ⊢
      stateInterpDef σ ∗ ⌜∃ (pc sp m npc : BitVec 64) (mi : Bool), σ = mkBoot pc sp m mi npc⌝ := by
  unfold stateInterpBoot; iintro H; iexact H

/-- Rebuild the boot interp for a state `σ'` that is heap-equal to `σ` and in boot
form — used after the register updates to re-establish `stateInterp` for the
result (which differs from the four-write state only in `minstret_increment`). -/
theorem boot_merge {σ σ' : MState}
    (hr : ∀ r, (σ.regs r).map (encReg r) = (σ'.regs r).map (encReg r))
    (hm : σ.mem = σ'.mem)
    (hb : ∃ (pc sp m npc : BitVec 64) (mi : Bool), σ' = mkBoot pc sp m mi npc) :
    (stateInterpDef σ : IProp GF) ⊢ stateInterpBoot σ' := by
  rw [stateInterpDef_eq hr hm]; unfold stateInterpBoot
  iintro H; isplitl [H]
  · iexact H
  · ipureintro; exact hb

instance (priority := 10000) instStateInterpBoot : StateInterp MState Empty GF where
  stateInterp σ _ _ _ := stateInterpBoot σ

instance (priority := 10000) instIrisGSBoot : IrisGS_gen hlc RiscvExpr GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

/-! ### `encReg` is the identity on the four 64-bit registers the WP owns -/
@[simp] theorem encReg_PC (v : BitVec 64) : encReg Register.PC v = v := by
  simp [encReg, BitVec.setWidth_eq]
@[simp] theorem encReg_x2 (v : BitVec 64) : encReg Register.x2 v = v := by
  simp [encReg, BitVec.setWidth_eq]
@[simp] theorem encReg_minstret (v : BitVec 64) : encReg Register.minstret v = v := by
  simp [encReg, BitVec.setWidth_eq]
@[simp] theorem encReg_nextPC (v : BitVec 64) : encReg Register.nextPC v = v := by
  simp [encReg, BitVec.setWidth_eq]
@[simp] theorem decReg_PC (v : BitVec 64) : decReg Register.PC v = v := by
  simp [decReg, BitVec.setWidth_eq]
@[simp] theorem decReg_x2 (v : BitVec 64) : decReg Register.x2 v = v := by
  simp [decReg, BitVec.setWidth_eq]
@[simp] theorem decReg_minstret (v : BitVec 64) : decReg Register.minstret v = v := by
  simp [decReg, BitVec.setWidth_eq]
@[simp] theorem decReg_nextPC (v : BitVec 64) : decReg Register.nextPC v = v := by
  simp [decReg, BitVec.setWidth_eq]

/-- **One real instruction, as a WP rule.** Given the model's full-state transition
on a boot state (`Hred`, supplied by `red_auipc`/`red_ld`), owning the four touched
bit-vector registers steps `Loop` once and hands back their updated points-to. The
`minstret_increment` write is invisible to the heap, so it isn't owned. -/
theorem wp_boot_step {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF}
    {pc sp m npc pc' sp' m' npc' : BitVec 64}
    (Hred : ∀ (mi : Bool), (exec riscv_step (mkBoot pc sp m mi npc)).map (fun p => p.2)
              = some (mkBoot pc' sp' m' true npc')) :
    Register.PC ↦ᵣ pc -∗ Register.x2 ↦ᵣ sp -∗ Register.minstret ↦ᵣ m -∗ Register.nextPC ↦ᵣ npc -∗
      ▷ (Register.PC ↦ᵣ pc' -∗ Register.x2 ↦ᵣ sp' -∗ Register.minstret ↦ᵣ m' -∗
          Register.nextPC ↦ᵣ npc' -∗ WP RiscvExpr.Loop @ s; E {{ Φ }}) -∗
      WP RiscvExpr.Loop @ s; E {{ Φ }} := by
  iintro HPC HX HMI HN Hcont
  iapply wp_lift_step (e₁ := RiscvExpr.Loop) rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases boot_split $$ [$Hσ] with ⟨Hσ, %Hbt⟩
  obtain ⟨pc₀, sp₀, m₀, npc₀, mi₀, rfl⟩ := Hbt
  have Hex : exec riscv_step (mkBoot pc sp m mi₀ npc)
      = some ((), mkBoot pc' sp' m' true npc') := by
    obtain ⟨⟨u, σ'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp (Hred mi₀)
    cases u; cases h2; exact h1
  -- pin the four owned registers to their values (mkBoot.regs r = some r₀; encReg = id)
  ihave %Hpc : ⌜pc₀ = pc⌝ $$ [Hσ HPC]
  · ihave >%H := reg_valid $$ [$Hσ $HPC]; ipureintro; simpa [mkBoot] using H
  ihave %Hsp : ⌜sp₀ = sp⌝ $$ [Hσ HX]
  · ihave >%H := reg_valid $$ [$Hσ $HX]; ipureintro; simpa [mkBoot] using H
  ihave %Hm : ⌜m₀ = m⌝ $$ [Hσ HMI]
  · ihave >%H := reg_valid $$ [$Hσ $HMI]; ipureintro; simpa [mkBoot] using H
  ihave %Hnpc : ⌜npc₀ = npc⌝ $$ [Hσ HN]
  · ihave >%H := reg_valid $$ [$Hσ $HN]; ipureintro; simpa [mkBoot] using H
  subst Hpc Hsp Hm Hnpc
  -- the step result is the boot state `mkBoot pc' sp' m' true npc'`
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    have Hstep : PrimStep.primStep (RiscvExpr.Loop, mkBoot pc₀ sp₀ m₀ mi₀ npc₀) ([] : List Empty)
        (RiscvExpr.Loop, mkBoot pc' sp' m' true npc', []) :=
      ⟨rfl, rfl, rfl, rfl, (), Hex⟩
    cases s <;> first
      | exact ⟨_, _, _, _, Hstep⟩
      | trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨_, rfl, rfl, rfl, _, Hex'⟩ := Hstep
  have Hσ₂ : σ₂ = mkBoot pc' sp' m' true npc' :=
    congrArg Prod.snd (Option.some.inj (Hex'.symm.trans Hex))
  subst Hσ₂
  imod Hclose
  -- update the four owned registers; the heap interp for the result follows by
  -- `stateInterpDef_eq` (it differs from the four-write state only in the
  -- junk-encoded `minstret_increment`).
  imod reg_update (v₂ := pc') (by simp) $$ [$Hσ $HPC] with ⟨Hσ, HPC'⟩
  imod reg_update (v₂ := sp') (by simp) $$ [$Hσ $HX] with ⟨Hσ, HX'⟩
  imod reg_update (v₂ := m') (by simp) $$ [$Hσ $HMI] with ⟨Hσ, HMI'⟩
  imod reg_update (v₂ := npc') (by simp) $$ [$Hσ $HN] with ⟨Hσ, HN'⟩
  icases (boot_merge (σ := MState.setReg (MState.setReg (MState.setReg (MState.setReg
        (mkBoot pc₀ sp₀ m₀ mi₀ npc₀) Register.PC (decReg Register.PC pc'))
        Register.x2 (decReg Register.x2 sp')) Register.minstret (decReg Register.minstret m'))
        Register.nextPC (decReg Register.nextPC npc'))
      (σ' := mkBoot pc' sp' m' true npc')
      (by intro r; cases r <;> simp [mkBoot, MState.setReg, encReg]) rfl
      ⟨pc', sp', m', npc', true, rfl⟩) $$ [$Hσ] with Hσ
  imodintro
  iframe Hσ
  isplitl [Hcont HPC' HX' HMI' HN']
  · iapply Hcont $$ HPC' HX' HMI' HN'
  · simp only [Algebra.BigOpL.bigOpL_nil]; itrivial

/-- **The xv6 kernel's first two instructions, as a WP over the program logic.**
Owning the boot registers (`PC` at the entry, `sp`, `minstret`, `nextPC`), after the
two real `try_step`s (`auipc sp,0xa; ld sp,472(sp)`) the continuation gets `PC` at
`entry+8` and `sp` holding the loaded doubleword `0x0123456789ABCDEF`. -/
theorem wp_kernel_first_two {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF}
    {m npc : BitVec 64} :
    Register.PC ↦ᵣ 0x80000000 -∗ Register.x2 ↦ᵣ 0xdead -∗ Register.minstret ↦ᵣ m -∗
      Register.nextPC ↦ᵣ npc -∗
      ▷ ▷ (Register.PC ↦ᵣ 0x80000008 -∗ Register.x2 ↦ᵣ 0x0123456789ABCDEF -∗
            Register.minstret ↦ᵣ (m + 1 + 1) -∗ Register.nextPC ↦ᵣ 0x80000008 -∗
            WP RiscvExpr.Loop @ s; E {{ Φ }}) -∗
      WP RiscvExpr.Loop @ s; E {{ Φ }} := by
  iintro HPC HX HMI HN Hcont
  iapply (wp_boot_step (fun mi => red_auipc 0xdead m mi npc)) $$ HPC HX HMI HN
  inext
  iintro HPC HX HMI HN
  iapply (wp_boot_step (fun mi => red_ld (m + 1) mi 0x80000004)) $$ HPC HX HMI HN
  inext
  iintro HPC HX HMI HN
  iapply Hcont $$ HPC HX HMI HN

end BootWP

end Xv6Iris.Model.KernelWP
