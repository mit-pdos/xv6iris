/-
The whole xv6 `_entry` (= `_start`) boot sequence as a weakest-precondition over
the program logic — extending `KernelWP.lean` from the first two instructions to
all eight, ending at the `jal start` (PC := 0x80000058). Hart 0 (`mhartid = 0`).

    _entry: auipc sp,0xa        # 80000000 : 0000a117   sp := pc+0xa000
            ld    sp,472(sp)    # 80000004 : 1d813103   sp := *(sp+472) = stack0
            lui   a0,0x1        # 80000008 : 6505 (RVC) a0 := 0x1000
            csrr  a1,mhartid    # 8000000a : f1402573   a1 := 0
            addi  a1,a1,1       # 8000000e : 0585 (RVC) a1 := 1
            mul   a0,a0,a1      # 80000010 : 02b50533   a0 := 0x1000
            add   sp,sp,a0      # 80000014 : 912a (RVC) sp := sp+0x1000
            jal   start         # 80000016 : 040200ef   ra := pc+4; PC := start

Self-contained; built with `make kernel-entry` (large `--tstack`). Each per-
instruction reduction is a full-state transition of the real `try_step`, proved by
kernel reduction; the write set across the sequence is
`{PC, nextPC, minstret, minstret_increment, x1(ra), x2(sp), x10(a0), x11(a1)}`.
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

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000000

namespace Xv6Iris.Model.KernelEntry

/-! ## Boot machine image -/

noncomputable def ramPMA : PMA := { (default : PMA) with
  executable := true, readable := true, writable := true }
noncomputable def ramRegion : PMA_Region :=
  { base := 0x80000000#64, size := 0x10000000#64, attributes := ramPMA, include_in_device_tree := false }

/-- The eight `_entry` instructions in memory + the `stack0` GOT word (value
`0x0123456789ABCDEF`) at `0x8000a1d8`. -/
noncomputable def mem0 : Nat → Option (BitVec 8) := fun a =>
  if a = 0x80000000 then some 0x17 else if a = 0x80000001 then some 0xa1
  else if a = 0x80000002 then some 0x00 else if a = 0x80000003 then some 0x00
  else if a = 0x80000004 then some 0x03 else if a = 0x80000005 then some 0x31
  else if a = 0x80000006 then some 0x81 else if a = 0x80000007 then some 0x1d
  else if a = 0x80000008 then some 0x05 else if a = 0x80000009 then some 0x65
  else if a = 0x8000000a then some 0xf3 else if a = 0x8000000b then some 0x25
  else if a = 0x8000000c then some 0x40 else if a = 0x8000000d then some 0xf1
  else if a = 0x8000000e then some 0x85 else if a = 0x8000000f then some 0x05
  else if a = 0x80000010 then some 0x33 else if a = 0x80000011 then some 0x05
  else if a = 0x80000012 then some 0xb5 else if a = 0x80000013 then some 0x02
  else if a = 0x80000014 then some 0x2a else if a = 0x80000015 then some 0x91
  else if a = 0x80000016 then some 0xef else if a = 0x80000017 then some 0x00
  else if a = 0x80000018 then some 0x20 else if a = 0x80000019 then some 0x04
  else if a = 0x8000A1D8 then some 0xEF else if a = 0x8000A1D9 then some 0xCD
  else if a = 0x8000A1DA then some 0xAB else if a = 0x8000A1DB then some 0x89
  else if a = 0x8000A1DC then some 0x67 else if a = 0x8000A1DD then some 0x45
  else if a = 0x8000A1DE then some 0x23 else if a = 0x8000A1DF then some 0x01
  else some 0#8

/-- Fixed boot register values for every register except the eight that change
(PC, nextPC, minstret, minstret_increment, x1, x2, x10, x11). `mhartid = 0`. -/
noncomputable def bootRegs : (r : Register) → Option (RegisterType r) := fun r =>
  match r with
  | .cur_privilege => some Privilege.Machine
  | .misa => some (BitVec.allOnes 64)
  | .pma_regions => some [ramRegion]
  | r => some (decReg r 0)

/-- The boot machine state parameterized by the changeable registers. -/
noncomputable def eBoot (pc npc mr ra sp a0 a1 : BitVec 64) (mi : Bool) : MState where
  regs r := match r with
    | .PC => some pc
    | .nextPC => some npc
    | .minstret => some mr
    | .minstret_increment => some mi
    | .x1 => some ra
    | .x2 => some sp
    | .x10 => some a0
    | .x11 => some a1
    | r => bootRegs r
  mem := mem0

/-! ## Per-instruction full-state reduction lemmas (kernel reduction of `try_step`)

Each step writes `{PC, nextPC, minstret, minstret_increment}` plus its destination
register; everything else (and memory) is unchanged, so the result is again an
`eBoot`. The architectural register trace (hart 0):

      ra  sp                  a0      a1
  →0: 0   0                   0       0
  →1: 0   0x8000a000          0       0     (auipc sp)
  →2: 0   0x0123456789ABCDEF  0       0     (ld sp)
  →3: 0   "                   0x1000  0     (lui a0)
  →4: 0   "                   0x1000  0     (csrr a1 ← mhartid=0)
  →5: 0   "                   0x1000  1     (addi a1)
  →6: 0   "                   0x1000  1     (mul a0 = 0x1000*1)
  →7: 0   0x0123456789ABDDEF  0x1000  1     (add sp += a0)
  →8: 0x8000001a "            0x1000  1     (jal: ra := 0x8000001a, PC := start)
-/

/-- Shared funext skeleton: the result is `eBoot <out>` (kernel reduction; `exec`
shared across the 180 register cases). -/
private theorem step_eq {pcI npcI mrI raI spI a0I a1I : BitVec 64} {miI : Bool}
    {out : MState} (h : (exec riscv_step (eBoot pcI npcI mrI raI spI a0I a1I miI)).isSome = true)
    (hreg : ∀ r, (((exec riscv_step (eBoot pcI npcI mrI raI spI a0I a1I miI)).get h).2).regs r = out.regs r)
    (hmem : (((exec riscv_step (eBoot pcI npcI mrI raI spI a0I a1I miI)).get h).2).mem = out.mem) :
    (exec riscv_step (eBoot pcI npcI mrI raI spI a0I a1I miI)).map (fun p => p.2) = some out := by
  have hs : (exec riscv_step (eBoot pcI npcI mrI raI spI a0I a1I miI)).map (fun p => p.2)
      = some (((exec riscv_step (eBoot pcI npcI mrI raI spI a0I a1I miI)).get h).2) := by
    rw [Option.map_eq_some_iff]; exact ⟨_, (Option.some_get h).symm, rfl⟩
  rw [hs]; congr 1; exact MState.ext (funext hreg) hmem

theorem red_e1 (mr npc : BitVec 64) (mi : Bool) :
    (exec riscv_step (eBoot 0x80000000 npc mr 0 0 0 0 mi)).map (fun p => p.2)
      = some (eBoot 0x80000004 0x80000004 (mr + 1) 0 0x8000a000 0 0 true) := by
  refine step_eq (by with_unfolding_all rfl) (fun r => ?_) (by with_unfolding_all rfl)
  cases r <;> with_unfolding_all rfl

theorem red_e2 (mr npc : BitVec 64) (mi : Bool) :
    (exec riscv_step (eBoot 0x80000004 npc mr 0 0x8000a000 0 0 mi)).map (fun p => p.2)
      = some (eBoot 0x80000008 0x80000008 (mr + 1) 0 0x0123456789ABCDEF 0 0 true) := by
  refine step_eq (by with_unfolding_all rfl) (fun r => ?_) (by with_unfolding_all rfl)
  cases r <;> with_unfolding_all rfl

theorem red_e3 (mr npc sp : BitVec 64) (mi : Bool) :
    (exec riscv_step (eBoot 0x80000008 npc mr 0 sp 0 0 mi)).map (fun p => p.2)
      = some (eBoot 0x8000000a 0x8000000a (mr + 1) 0 sp 0x1000 0 true) := by
  refine step_eq (by with_unfolding_all rfl) (fun r => ?_) (by with_unfolding_all rfl)
  cases r <;> with_unfolding_all rfl

theorem red_e4 (mr npc sp : BitVec 64) (mi : Bool) :
    (exec riscv_step (eBoot 0x8000000a npc mr 0 sp 0x1000 0 mi)).map (fun p => p.2)
      = some (eBoot 0x8000000e 0x8000000e (mr + 1) 0 sp 0x1000 0 true) := by
  refine step_eq (by with_unfolding_all rfl) (fun r => ?_) (by with_unfolding_all rfl)
  cases r <;> with_unfolding_all rfl

theorem red_e5 (mr npc sp : BitVec 64) (mi : Bool) :
    (exec riscv_step (eBoot 0x8000000e npc mr 0 sp 0x1000 0 mi)).map (fun p => p.2)
      = some (eBoot 0x80000010 0x80000010 (mr + 1) 0 sp 0x1000 1 true) := by
  refine step_eq (by with_unfolding_all rfl) (fun r => ?_) (by with_unfolding_all rfl)
  cases r <;> with_unfolding_all rfl

theorem red_e6 (mr npc sp : BitVec 64) (mi : Bool) :
    (exec riscv_step (eBoot 0x80000010 npc mr 0 sp 0x1000 1 mi)).map (fun p => p.2)
      = some (eBoot 0x80000014 0x80000014 (mr + 1) 0 sp 0x1000 1 true) := by
  refine step_eq (by with_unfolding_all rfl) (fun r => ?_) (by with_unfolding_all rfl)
  cases r <;> with_unfolding_all rfl

theorem red_e7 (mr npc : BitVec 64) (mi : Bool) :
    (exec riscv_step (eBoot 0x80000014 npc mr 0 0x0123456789ABCDEF 0x1000 1 mi)).map (fun p => p.2)
      = some (eBoot 0x80000016 0x80000016 (mr + 1) 0 0x0123456789ABDDEF 0x1000 1 true) := by
  refine step_eq (by with_unfolding_all rfl) (fun r => ?_) (by with_unfolding_all rfl)
  cases r <;> with_unfolding_all rfl

theorem red_e8 (mr npc sp : BitVec 64) (mi : Bool) :
    (exec riscv_step (eBoot 0x80000016 npc mr 0 sp 0x1000 1 mi)).map (fun p => p.2)
      = some (eBoot 0x80000058 0x80000058 (mr + 1) 0x8000001a sp 0x1000 1 true) := by
  refine step_eq (by with_unfolding_all rfl) (fun r => ?_) (by with_unfolding_all rfl)
  cases r <;> with_unfolding_all rfl

/-! ## Boot state interpretation + WP (append to KernelEntry.lean before final `end`) -/

section EntryWP
variable {GF : BundledGFunctors} {hlc : HasLC} [D : RiscvGS hlc GF]

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

def stateInterpEntry (σ : MState) : IProp GF :=
  iprop(stateInterpDef σ ∗ ⌜∃ (pc npc mr ra sp a0 a1 : BitVec 64) (mi : Bool),
    σ = eBoot pc npc mr ra sp a0 a1 mi⌝)

instance (priority := 10000) instStateInterpEntry : StateInterp MState Empty GF where
  stateInterp σ _ _ _ := stateInterpEntry σ

instance (priority := 10000) instIrisGSEntry : IrisGS_gen hlc RiscvExpr GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

theorem entry_split {σ : MState} :
    (stateInterpEntry σ : IProp GF) ⊢ stateInterpDef σ ∗ ⌜∃ (pc npc mr ra sp a0 a1 : BitVec 64)
      (mi : Bool), σ = eBoot pc npc mr ra sp a0 a1 mi⌝ := by
  unfold stateInterpEntry; iintro H; iexact H

theorem entry_merge {σ σ' : MState}
    (hr : ∀ r, (σ.regs r).map (encReg r) = (σ'.regs r).map (encReg r))
    (hm : σ.mem = σ'.mem)
    (hb : ∃ (pc npc mr ra sp a0 a1 : BitVec 64) (mi : Bool), σ' = eBoot pc npc mr ra sp a0 a1 mi) :
    (stateInterpDef σ : IProp GF) ⊢ stateInterpEntry σ' := by
  rw [stateInterpDef_eq hr hm]; unfold stateInterpEntry
  iintro H; isplitl [H]
  · iexact H
  · ipureintro; exact hb

@[simp] theorem encReg_PC (v : BitVec 64) : encReg Register.PC v = v := by simp [encReg, BitVec.setWidth_eq]
@[simp] theorem encReg_nextPC (v : BitVec 64) : encReg Register.nextPC v = v := by simp [encReg, BitVec.setWidth_eq]
@[simp] theorem encReg_minstret (v : BitVec 64) : encReg Register.minstret v = v := by simp [encReg, BitVec.setWidth_eq]
@[simp] theorem encReg_x1 (v : BitVec 64) : encReg Register.x1 v = v := by simp [encReg, BitVec.setWidth_eq]
@[simp] theorem encReg_x2 (v : BitVec 64) : encReg Register.x2 v = v := by simp [encReg, BitVec.setWidth_eq]
@[simp] theorem encReg_x10 (v : BitVec 64) : encReg Register.x10 v = v := by simp [encReg, BitVec.setWidth_eq]
@[simp] theorem encReg_x11 (v : BitVec 64) : encReg Register.x11 v = v := by simp [encReg, BitVec.setWidth_eq]
@[simp] theorem decReg_PC (v : BitVec 64) : decReg Register.PC v = v := by simp [decReg, BitVec.setWidth_eq]
@[simp] theorem decReg_nextPC (v : BitVec 64) : decReg Register.nextPC v = v := by simp [decReg, BitVec.setWidth_eq]
@[simp] theorem decReg_minstret (v : BitVec 64) : decReg Register.minstret v = v := by simp [decReg, BitVec.setWidth_eq]
@[simp] theorem decReg_x1 (v : BitVec 64) : decReg Register.x1 v = v := by simp [decReg, BitVec.setWidth_eq]
@[simp] theorem decReg_x2 (v : BitVec 64) : decReg Register.x2 v = v := by simp [decReg, BitVec.setWidth_eq]
@[simp] theorem decReg_x10 (v : BitVec 64) : decReg Register.x10 v = v := by simp [decReg, BitVec.setWidth_eq]
@[simp] theorem decReg_x11 (v : BitVec 64) : decReg Register.x11 v = v := by simp [decReg, BitVec.setWidth_eq]

/-- **One real instruction, as a WP rule** (owns the 7 visible changeable
registers; `minstret_increment` is junk-encoded, hence invisible). -/
theorem wp_estep {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF}
    {pc npc mr ra sp a0 a1 pc' npc' mr' ra' sp' a0' a1' : BitVec 64}
    (Hred : ∀ (mi : Bool), (exec riscv_step (eBoot pc npc mr ra sp a0 a1 mi)).map (fun p => p.2)
              = some (eBoot pc' npc' mr' ra' sp' a0' a1' true)) :
    Register.PC ↦ᵣ pc -∗ Register.nextPC ↦ᵣ npc -∗ Register.minstret ↦ᵣ mr -∗
      Register.x1 ↦ᵣ ra -∗ Register.x2 ↦ᵣ sp -∗ Register.x10 ↦ᵣ a0 -∗ Register.x11 ↦ᵣ a1 -∗
      ▷ (Register.PC ↦ᵣ pc' -∗ Register.nextPC ↦ᵣ npc' -∗ Register.minstret ↦ᵣ mr' -∗
          Register.x1 ↦ᵣ ra' -∗ Register.x2 ↦ᵣ sp' -∗ Register.x10 ↦ᵣ a0' -∗ Register.x11 ↦ᵣ a1' -∗
          WP RiscvExpr.Loop @ s; E {{ Φ }}) -∗
      WP RiscvExpr.Loop @ s; E {{ Φ }} := by
  iintro HPC HN HM H1 H2 H10 H11 Hcont
  iapply wp_lift_step (e₁ := RiscvExpr.Loop) rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases entry_split $$ [$Hσ] with ⟨Hσ, %Hbt⟩
  obtain ⟨pc₀, npc₀, mr₀, ra₀, sp₀, a0₀, a1₀, mi₀, rfl⟩ := Hbt
  have Hex : exec riscv_step (eBoot pc npc mr ra sp a0 a1 mi₀)
      = some ((), eBoot pc' npc' mr' ra' sp' a0' a1' true) := by
    obtain ⟨⟨u, σ'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp (Hred mi₀); cases u; cases h2; exact h1
  ihave %Hpc : ⌜pc₀ = pc⌝ $$ [Hσ HPC]
  · ihave >%H := reg_valid $$ [$Hσ $HPC]; ipureintro; simpa [eBoot] using H
  ihave %Hnpc : ⌜npc₀ = npc⌝ $$ [Hσ HN]
  · ihave >%H := reg_valid $$ [$Hσ $HN]; ipureintro; simpa [eBoot] using H
  ihave %Hmr : ⌜mr₀ = mr⌝ $$ [Hσ HM]
  · ihave >%H := reg_valid $$ [$Hσ $HM]; ipureintro; simpa [eBoot] using H
  ihave %Hra : ⌜ra₀ = ra⌝ $$ [Hσ H1]
  · ihave >%H := reg_valid $$ [$Hσ $H1]; ipureintro; simpa [eBoot] using H
  ihave %Hsp : ⌜sp₀ = sp⌝ $$ [Hσ H2]
  · ihave >%H := reg_valid $$ [$Hσ $H2]; ipureintro; simpa [eBoot] using H
  ihave %Ha0 : ⌜a0₀ = a0⌝ $$ [Hσ H10]
  · ihave >%H := reg_valid $$ [$Hσ $H10]; ipureintro; simpa [eBoot] using H
  ihave %Ha1 : ⌜a1₀ = a1⌝ $$ [Hσ H11]
  · ihave >%H := reg_valid $$ [$Hσ $H11]; ipureintro; simpa [eBoot] using H
  subst Hpc Hnpc Hmr Hra Hsp Ha0 Ha1
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    have Hstep : PrimStep.primStep (RiscvExpr.Loop, eBoot pc₀ npc₀ mr₀ ra₀ sp₀ a0₀ a1₀ mi₀)
        ([] : List Empty) (RiscvExpr.Loop, eBoot pc' npc' mr' ra' sp' a0' a1' true, []) :=
      ⟨rfl, rfl, rfl, rfl, (), Hex⟩
    cases s <;> first | exact ⟨_, _, _, _, Hstep⟩ | trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨_, rfl, rfl, rfl, _, Hex'⟩ := Hstep
  have Hσ₂ : σ₂ = eBoot pc' npc' mr' ra' sp' a0' a1' true :=
    congrArg Prod.snd (Option.some.inj (Hex'.symm.trans Hex))
  subst Hσ₂
  imod Hclose
  imod reg_update (v₂ := pc') (by simp) $$ [$Hσ $HPC] with ⟨Hσ, HPC'⟩
  imod reg_update (v₂ := npc') (by simp) $$ [$Hσ $HN] with ⟨Hσ, HN'⟩
  imod reg_update (v₂ := mr') (by simp) $$ [$Hσ $HM] with ⟨Hσ, HM'⟩
  imod reg_update (v₂ := ra') (by simp) $$ [$Hσ $H1] with ⟨Hσ, H1'⟩
  imod reg_update (v₂ := sp') (by simp) $$ [$Hσ $H2] with ⟨Hσ, H2'⟩
  imod reg_update (v₂ := a0') (by simp) $$ [$Hσ $H10] with ⟨Hσ, H10'⟩
  imod reg_update (v₂ := a1') (by simp) $$ [$Hσ $H11] with ⟨Hσ, H11'⟩
  icases (entry_merge
      (σ := MState.setReg (MState.setReg (MState.setReg (MState.setReg (MState.setReg
        (MState.setReg (MState.setReg (eBoot pc₀ npc₀ mr₀ ra₀ sp₀ a0₀ a1₀ mi₀)
        Register.PC (decReg Register.PC pc')) Register.nextPC (decReg Register.nextPC npc'))
        Register.minstret (decReg Register.minstret mr')) Register.x1 (decReg Register.x1 ra'))
        Register.x2 (decReg Register.x2 sp')) Register.x10 (decReg Register.x10 a0'))
        Register.x11 (decReg Register.x11 a1'))
      (σ' := eBoot pc' npc' mr' ra' sp' a0' a1' true)
      (by intro r; cases r <;> simp [eBoot, MState.setReg, encReg]) rfl
      ⟨pc', npc', mr', ra', sp', a0', a1', true, rfl⟩) $$ [$Hσ] with Hσ
  imodintro
  iframe Hσ
  isplitl [Hcont HPC' HN' HM' H1' H2' H10' H11']
  · iapply Hcont $$ HPC' HN' HM' H1' H2' H10' H11'
  · simp only [Algebra.BigOpL.bigOpL_nil]; itrivial

/-- **The xv6 `_entry` boot code, as a WP over the program logic.** Owning the boot
registers at the entry point (hart 0), after the eight real `try_step`s the
continuation gets `PC = start (0x80000058)`, `ra = 0x8000001a`, `sp = stack0+0x1000`,
`a0 = 0x1000`, `a1 = 1`. -/
theorem wp_entry {s : Stuckness} {E : CoPset} {Φ : Empty → IProp GF} {mr npc : BitVec 64} :
    Register.PC ↦ᵣ 0x80000000 -∗ Register.nextPC ↦ᵣ npc -∗ Register.minstret ↦ᵣ mr -∗
      Register.x1 ↦ᵣ 0 -∗ Register.x2 ↦ᵣ 0 -∗ Register.x10 ↦ᵣ 0 -∗ Register.x11 ↦ᵣ 0 -∗
      (▷ ▷ ▷ ▷ ▷ ▷ ▷ ▷ (Register.PC ↦ᵣ 0x80000058 -∗ Register.nextPC ↦ᵣ 0x80000058 -∗
            Register.minstret ↦ᵣ (mr+1+1+1+1+1+1+1+1) -∗ Register.x1 ↦ᵣ 0x8000001a -∗
            Register.x2 ↦ᵣ 0x0123456789ABDDEF -∗ Register.x10 ↦ᵣ 0x1000 -∗ Register.x11 ↦ᵣ 1 -∗
            WP RiscvExpr.Loop @ s; E {{ Φ }})) -∗
      WP RiscvExpr.Loop @ s; E {{ Φ }} := by
  iintro HPC HN HM H1 H2 H10 H11 Hcont
  iapply (wp_estep (fun mi => red_e1 mr npc mi)) $$ HPC HN HM H1 H2 H10 H11; inext
  iintro HPC HN HM H1 H2 H10 H11
  iapply (wp_estep (fun mi => red_e2 (mr+1) 0x80000004 mi)) $$ HPC HN HM H1 H2 H10 H11; inext
  iintro HPC HN HM H1 H2 H10 H11
  iapply (wp_estep (fun mi => red_e3 (mr+1+1) 0x80000008 0x0123456789ABCDEF mi)) $$ HPC HN HM H1 H2 H10 H11; inext
  iintro HPC HN HM H1 H2 H10 H11
  iapply (wp_estep (fun mi => red_e4 (mr+1+1+1) 0x8000000a 0x0123456789ABCDEF mi)) $$ HPC HN HM H1 H2 H10 H11; inext
  iintro HPC HN HM H1 H2 H10 H11
  iapply (wp_estep (fun mi => red_e5 (mr+1+1+1+1) 0x8000000e 0x0123456789ABCDEF mi)) $$ HPC HN HM H1 H2 H10 H11; inext
  iintro HPC HN HM H1 H2 H10 H11
  iapply (wp_estep (fun mi => red_e6 (mr+1+1+1+1+1) 0x80000010 0x0123456789ABCDEF mi)) $$ HPC HN HM H1 H2 H10 H11; inext
  iintro HPC HN HM H1 H2 H10 H11
  iapply (wp_estep (fun mi => red_e7 (mr+1+1+1+1+1+1) 0x80000014 mi)) $$ HPC HN HM H1 H2 H10 H11; inext
  iintro HPC HN HM H1 H2 H10 H11
  iapply (wp_estep (fun mi => red_e8 (mr+1+1+1+1+1+1+1) 0x80000016 0x0123456789ABDDEF mi)) $$ HPC HN HM H1 H2 H10 H11; inext
  iintro HPC HN HM H1 H2 H10 H11
  iapply Hcont $$ HPC HN HM H1 H2 H10 H11

end EntryWP

end Xv6Iris.Model.KernelEntry
