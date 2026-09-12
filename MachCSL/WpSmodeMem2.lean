/-
MachCSL: more supervisor-mode memory stages: `lwu`.
-/
import MachCSL.WpSmodeMem
import MachCSL.WpSmodeRules

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `lwu rd, imm(rs1)` from a 4-aligned RAM address: zero-extended. -/
theorem execSpecF_lwu [CurCtx] (cpu : CPU) (dq dq' : DFrac) (c : MConf) (sie : Bool) (hok : SConfBare (GF := GF) c sie)
    (pc npc₀ : BitVec 64) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rd ≠ 0#5) (R : RegMap)
    (w : BitVec 32) (hram : inRam (RegMap.get R rs1 + BitVec.signExtend 64 imm) 4)
    (hal : (RegMap.get R rs1 + BitVec.signExtend 64 imm).toNat % 4 = 0) :
    execSpecPP (GF := GF) cpu dq Privilege.Supervisor c Privilege.Supervisor c
      (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, true, 4)) pc npc₀ npc₀
      iprop(gprFile cpu R ∗ ctxTok cpu curCtx ∗ bytesPointsTo (RegMap.get R rs1 + BitVec.signExtend 64 imm) 4 dq' w)
      iprop(gprFile cpu (RegMap.set R rd (BitVec.setWidth 64 w)) ∗ ctxTok cpu curCtx ∗
        bytesPointsTo (RegMap.get R rs1 + BitVec.signExtend 64 imm) 4 dq' w) := by
  have hva := is_aligned_vaddr_of (RegMap.get R rs1 + BitVec.signExtend 64 imm) 4 hal
  have hsplit := split_on_page_boundary_4 (RegMap.get R rs1 + BitVec.signExtend 64 imm) hal
  load_file_S_proof swp_checked_mem_read_load4_S hrd

/-- `lwu rd, imm(rs1)`: the word at `rs1 + imm` (4-aligned), zero-extended
(the raw form: a byte window plus the facts; clients use `wp_s_lwu`). -/
theorem wp_s_lwu_bytes [CurCtx] [KernelGeom] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (dq' : DFrac) (w : BitVec 32) (hram : inRam (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4)
    (hal : (k.rget cpu rs1 + BitVec.signExtend 64 imm).toNat % 4 = 0) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, true, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 dq' w ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (BitVec.setWidth 64 w)) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗
          bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 dq' w -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_setReg_mem' cpu k hsie htier pc _ is_rvc _ rd hrd _ _ _
    (fun c hok _ => execSpecF_lwu cpu (DFrac.own 1) dq' c false hok pc _ imm rd rs1 hrd.1
      (tpPin cpu k.regs) w hram hal)

/-- `lwu rd, imm(rs1)`: the word at `rs1 + imm`, zero-extended. -/
theorem wp_s_lwu [CurCtx] [KernelGeom] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (dq' : DFrac) (w : BitVec 32) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, true, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 dq' w ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (BitVec.setWidth 64 w)) -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 dq' w -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨Hi, Hk, Hpc, Hw, Hnext⟩
  icases wordPointsTo_cases _ _ _ _ $$ Hw with ⟨%⟨hram, hal⟩, Hm⟩
  iapply (wp_s_lwu_bytes cpu k hsie htier pc is_rvc imm rd rs1 hrd dq' w hram hal)
  iframe Hi Hk Hpc Hm
  inext
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK Hk Hpc Hm
  ihave Hw := wordPointsTo_intro _ _ _ _ hram hal $$ Hm
  iapply HK $$ Hk Hpc Hw

end MachCSL
