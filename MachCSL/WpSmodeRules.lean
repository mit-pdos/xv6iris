/-
MachCSL: the supervisor-mode instruction rules over the kernel execution
context `kctx` for memory, control flow and the stack: `wp_s_lbu`,
`wp_s_ld`, `wp_s_sb`, `wp_s_sd`, `wp_s_branch`, `wp_s_j`, `wp_s_jal`,
`wp_s_ret`, `wp_s_subw`, `wp_s_addw`, `wp_s_push`, `wp_s_pop`.  All are
instances of one schema, `wpLoop_k_gen`: an execute stage over the
register file (plus some memory), run in the kernel context (Bare tier,
interrupts off for now), delivering `wpNext`.
-/
import MachCSL.WpSmodeMem
import MachCSL.WpSmodeCtl
import MachCSL.WpSmodeCsr


namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- Framing an execute stage. -/
theorem execSpecPP.frame {cpu : CPU} {dq : DFrac} {p : Privilege} {c : MConf} {p' : Privilege} {c' : MConf}
    {ast : instruction} {pc npc₀ npc : BitVec 64} {P Q : IProp GF}
    (h : execSpecPP cpu dq p c p' c' ast pc npc₀ npc P Q) (F : IProp GF) :
    execSpecPP cpu dq p c p' c' ast pc npc₀ npc iprop(P ∗ F) iprop(Q ∗ F) := by
  intro Φ
  iintro ⟨HmConf, HPC, HnextPC, ⟨HP, HF⟩, HΦ⟩
  iapply (h Φ)
  iframe
  inext
  iintro HmConf HPC HnextPC HQ
  iapply HΦ $$ HmConf HPC HnextPC [HQ HF]
  iframe

/-- `wpNext` is monotone in its continuation. -/
theorem wpNext_mono (sie : Bool) (p : BitVec 64) (cpu : CPU) (K K' : CPU → IProp GF) :
    wpNext sie p cpu K ⊢ (∀ cpu', K cpu' -∗ K' cpu') -∗ wpNext sie p cpu K' := by
  unfold wpNext
  iintro H HK %cpu' %h
  iapply HK $$ %cpu'
  iapply H $$ %cpu' %h

set_option maxHeartbeats 4000000 in
/-- The general schema: an instruction whose execute stage, over the whole
register file and the resources `P`, leaves the file at `R'` (same `sp`)
and `Q`, run in the kernel context. -/
theorem wpLoop_k_gen [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (htier : k.tier = KTier.bare) (pc npc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (R' : RegMap) (hsp : R' 2#5 = k.regs 2#5) (P Q : IProp GF)
    (hexec : ∀ c : MConf, SConfBare (GF := GF) c false → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c i pc
        (pc + instrLen is_rvc) npc
        iprop(gprFile cpu (tpPin cpu k.regs) ∗ P) iprop(gprFile cpu (tpPin cpu R') ∗ Q)) :
    instr (GF := GF) pc is_rvc i ∗ kctx cpu k ∗ pcIs cpu pc ∗ P ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.withRegs R') -∗ pcIs cpu' npc -∗ Q -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  have hsp' := KCtx.withRegs_sp k R' hsp
  iintro ⟨HI, Hk, Hpc, HP, HΦ⟩
  icases kctx_cases cpu k $$ Hk with ⟨%hwf, HConf, HF, Hstack, Htrans, Harm, Hcpu, Htok, Hclock, #Hro⟩
  icases kConf_cases cpu _ _ _ $$ HConf with ⟨%ms, %mdl, %mepc, %stc, %⟨hsm, hmdl⟩, HmConf⟩
  rw [hsie] at hsm
  simp only [hsie, htier]
  have hok := SConfBare_sConfOf_bare (GF := GF) k.root ms mdl mepc stc hsm
  iapply (wpLoop_s_instr cpu (DFrac.own 1) _ _ hok hmdl rfl pc npc is_rvc i _ _ (hexec _ hok rfl))
  iframe
  inext
  iintro HmConf Hclock Hpc ⟨HF, HQ⟩
  ihave HΦ' := wpNext_off _ _ _ $$ HΦ
  ihave HConf := kConf_intro cpu KTier.bare k.root false ms mdl mepc stc ⟨hsm, hmdl⟩ $$ HmConf
  iapply HΦ' $$ [HConf HF Hstack Htrans Harm Hcpu Htok Hclock] Hpc HQ
  iapply (kctx_intro' cpu (k.withRegs R') ((KCtx.wf_withRegs k R').mpr hwf))
  simp only [KCtx.withRegs_regs, KCtx.withRegs_sie, KCtx.withRegs_avail, KCtx.withRegs_noff,
    KCtx.withRegs_intena, KCtx.withRegs_locks, KCtx.withRegs_tier, KCtx.withRegs_root, KCtx.withRegs_proc,
    hsp', hsie, htier]
  iframe
  iexact Hro

set_option maxHeartbeats 4000000 in
/-- The general schema for a memory instruction: as `wpLoop_k_gen`, with the
context token lent to the execute stage. -/
theorem wpLoop_k_mem [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (htier : k.tier = KTier.bare) (pc npc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (R' : RegMap) (hsp : R' 2#5 = k.regs 2#5) (P Q : IProp GF)
    (hexec : ∀ c : MConf, SConfBare (GF := GF) c false → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c i pc
        (pc + instrLen is_rvc) npc
        iprop(gprFile cpu (tpPin cpu k.regs) ∗ ctxToken cpu ∗ P)
        iprop(gprFile cpu (tpPin cpu R') ∗ ctxToken cpu ∗ Q)) :
    instr (GF := GF) pc is_rvc i ∗ kctx cpu k ∗ pcIs cpu pc ∗ P ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.withRegs R') -∗ pcIs cpu' npc -∗ Q -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  have hsp' := KCtx.withRegs_sp k R' hsp
  iintro ⟨HI, Hk, Hpc, HP, HΦ⟩
  icases kctx_cases cpu k $$ Hk with ⟨%hwf, HConf, HF, Hstack, Htrans, Harm, Hcpu, Htok, Hclock, #Hro⟩
  icases kConf_cases cpu _ _ _ $$ HConf with ⟨%ms, %mdl, %mepc, %stc, %⟨hsm, hmdl⟩, HmConf⟩
  rw [hsie] at hsm
  simp only [hsie, htier]
  have hok := SConfBare_sConfOf_bare (GF := GF) k.root ms mdl mepc stc hsm
  iapply (wpLoop_s_instr cpu (DFrac.own 1) _ _ hok hmdl rfl pc npc is_rvc i _ _ (hexec _ hok rfl))
  iframe
  inext
  iintro HmConf Hclock Hpc ⟨HF, Htok, HQ⟩
  ihave HΦ' := wpNext_off _ _ _ $$ HΦ
  ihave HConf := kConf_intro cpu KTier.bare k.root false ms mdl mepc stc ⟨hsm, hmdl⟩ $$ HmConf
  iapply HΦ' $$ [HConf HF Hstack Htrans Harm Hcpu Htok Hclock] Hpc HQ
  iapply (kctx_intro' cpu (k.withRegs R') ((KCtx.wf_withRegs k R').mpr hwf))
  simp only [KCtx.withRegs_regs, KCtx.withRegs_sie, KCtx.withRegs_avail, KCtx.withRegs_noff,
    KCtx.withRegs_intena, KCtx.withRegs_locks, KCtx.withRegs_tier, KCtx.withRegs_root, KCtx.withRegs_proc,
    hsp', hsie, htier]
  iframe
  iexact Hro

/-- `wpLoop_k_mem` for an execute stage that leaves the file alone. -/
theorem wpLoop_k_keep_mem [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (htier : k.tier = KTier.bare) (pc npc : BitVec 64) (is_rvc : Bool) (i : instruction) (P Q : IProp GF)
    (hexec : ∀ c : MConf, SConfBare (GF := GF) c false → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c i pc
        (pc + instrLen is_rvc) npc
        iprop(gprFile cpu (tpPin cpu k.regs) ∗ ctxToken cpu ∗ P)
        iprop(gprFile cpu (tpPin cpu k.regs) ∗ ctxToken cpu ∗ Q)) :
    instr (GF := GF) pc is_rvc i ∗ kctx cpu k ∗ pcIs cpu pc ∗ P ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' npc -∗ Q -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  have := wpLoop_k_mem cpu k hsie htier pc npc is_rvc i k.regs rfl P Q hexec
  rw [KCtx.withRegs_self] at this
  exact this

/-- The schema for an execute stage that leaves the file alone. -/
theorem wpLoop_k_keep [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (htier : k.tier = KTier.bare) (pc npc : BitVec 64) (is_rvc : Bool) (i : instruction) (P Q : IProp GF)
    (hexec : ∀ c : MConf, SConfBare (GF := GF) c false → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c i pc
        (pc + instrLen is_rvc) npc
        iprop(gprFile cpu (tpPin cpu k.regs) ∗ P) iprop(gprFile cpu (tpPin cpu k.regs) ∗ Q)) :
    instr (GF := GF) pc is_rvc i ∗ kctx cpu k ∗ pcIs cpu pc ∗ P ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' npc -∗ Q -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  have := wpLoop_k_gen cpu k hsie htier pc npc is_rvc i k.regs rfl P Q hexec
  rw [KCtx.withRegs_self] at this
  exact this

/-- The schema for an execute stage that touches nothing but the file (and
leaves it alone). -/
theorem wpLoop_k_keep0 [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (htier : k.tier = KTier.bare) (pc npc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (hexec : ∀ c : MConf, SConfBare (GF := GF) c false → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c i pc
        (pc + instrLen is_rvc) npc (gprFile cpu (tpPin cpu k.regs)) (gprFile cpu (tpPin cpu k.regs))) :
    instr (GF := GF) pc is_rvc i ∗ kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' npc -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, HΦ⟩
  iapply (wpLoop_k_keep cpu k hsie htier pc npc is_rvc i emp emp (fun c h1 h2 => (hexec c h1 h2).frame emp))
  iframe
  isplitl []
  · iempintro
  · inext
    iapply wpNext_mono $$ HΦ
    iintro %cpu' HK Hk Hpc _
    iapply HK $$ Hk Hpc

/-- The schema for an execute stage that writes one register `rd` (not
`x0`, `sp`, `tp`) and touches the resources `P`/`Q`. -/
theorem wpLoop_k_setReg' [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (htier : k.tier = KTier.bare) (pc npc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (rd : BitVec 5) (hrd : rdOk rd) (v : BitVec 64) (P Q : IProp GF)
    (hexec : ∀ c : MConf, SConfBare (GF := GF) c false → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c i pc
        (pc + instrLen is_rvc) npc
        iprop(gprFile cpu (tpPin cpu k.regs) ∗ P) iprop(gprFile cpu ((tpPin cpu k.regs).set rd v) ∗ Q)) :
    instr (GF := GF) pc is_rvc i ∗ kctx cpu k ∗ pcIs cpu pc ∗ P ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd v) -∗ pcIs cpu' npc -∗ Q -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  obtain ⟨hrd0, hrdsp, hrdtp⟩ := hrd
  have htp := tpPin_set cpu k.regs rd v hrdtp
  rw [htp] at hexec
  exact wpLoop_k_gen cpu k hsie htier pc npc is_rvc i (k.regs.set rd v)
    (RegMap.set_other _ _ _ _ (Ne.symm hrdsp)) P Q hexec

/-- `wpLoop_k_setReg'` for a memory instruction (the token lent). -/
theorem wpLoop_k_setReg_mem' [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (htier : k.tier = KTier.bare) (pc npc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (rd : BitVec 5) (hrd : rdOk rd) (v : BitVec 64) (P Q : IProp GF)
    (hexec : ∀ c : MConf, SConfBare (GF := GF) c false → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c i pc
        (pc + instrLen is_rvc) npc
        iprop(gprFile cpu (tpPin cpu k.regs) ∗ ctxToken cpu ∗ P)
        iprop(gprFile cpu ((tpPin cpu k.regs).set rd v) ∗ ctxToken cpu ∗ Q)) :
    instr (GF := GF) pc is_rvc i ∗ kctx cpu k ∗ pcIs cpu pc ∗ P ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd v) -∗ pcIs cpu' npc -∗ Q -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  obtain ⟨hrd0, hrdsp, hrdtp⟩ := hrd
  have htp := tpPin_set cpu k.regs rd v hrdtp
  rw [htp] at hexec
  exact wpLoop_k_mem cpu k hsie htier pc npc is_rvc i (k.regs.set rd v)
    (RegMap.set_other _ _ _ _ (Ne.symm hrdsp)) P Q hexec

/-! ## Memory -/

/-- `lbu rd, imm(rs1)`: the byte at `rs1 + imm`, zero-extended (the raw form: a byte window plus the RAM fact; clients use `wp_s_lbu`). -/
theorem wp_s_lbu_bytes [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (dq' : DFrac) (b : BitVec 8) (hram : inRam (k.rget cpu rs1 + BitVec.signExtend 64 imm) 1) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, true, 1)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 1 dq' b ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (BitVec.setWidth 64 b)) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗
          bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 1 dq' b -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_setReg_mem' cpu k hsie htier pc _ is_rvc _ rd hrd _ _ _
    (fun c hok _ => execSpecF_lbu cpu (DFrac.own 1) dq' c false hok pc _ imm rd rs1 hrd.1
      (tpPin cpu k.regs) b hram)

/-- `lbu rd, imm(rs1)`: the byte at `rs1 + imm`, zero-extended. -/
theorem wp_s_lbu [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (dq' : DFrac) (b : BitVec 8) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, true, 1)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 1 dq' b ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (BitVec.setWidth 64 b)) -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 1 dq' b -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨Hi, Hk, Hpc, Hw, Hnext⟩
  icases wordPointsTo_cases _ _ _ _ $$ Hw with ⟨%⟨hram, hal⟩, Hm⟩
  iapply (wp_s_lbu_bytes cpu k hsie htier pc is_rvc imm rd rs1 hrd dq' b hram)
  iframe Hi Hk Hpc Hm
  inext
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK Hk Hpc Hm
  ihave Hw := wordPointsTo_intro _ _ _ _ hram hal $$ Hm
  iapply HK $$ Hk Hpc Hw

/-- `ld rd, imm(rs1)`: the word at `rs1 + imm` (8-aligned) (the raw form: a byte window plus the facts; clients use `wp_s_ld`). -/
theorem wp_s_ld_bytes [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (dq' : DFrac) (v : BitVec 64) (hram : inRam (k.rget cpu rs1 + BitVec.signExtend 64 imm) 8)
    (hal : (k.rget cpu rs1 + BitVec.signExtend 64 imm).toNat % 8 = 0) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, false, 8)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 8 dq' v ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd v) -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 8 dq' v -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_setReg_mem' cpu k hsie htier pc _ is_rvc _ rd hrd _ _ _
    (fun c hok _ => execSpecF_ld cpu (DFrac.own 1) dq' c false hok pc _ imm rd rs1 hrd.1
      (tpPin cpu k.regs) v hram hal)

/-- `ld rd, imm(rs1)`: the word at `rs1 + imm`. -/
theorem wp_s_ld [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (dq' : DFrac) (v : BitVec 64) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, false, 8)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 8 dq' v ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd v) -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 8 dq' v -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨Hi, Hk, Hpc, Hw, Hnext⟩
  icases wordPointsTo_cases _ _ _ _ $$ Hw with ⟨%⟨hram, hal⟩, Hm⟩
  iapply (wp_s_ld_bytes cpu k hsie htier pc is_rvc imm rd rs1 hrd dq' v hram hal)
  iframe Hi Hk Hpc Hm
  inext
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK Hk Hpc Hm
  ihave Hw := wordPointsTo_intro _ _ _ _ hram hal $$ Hm
  iapply HK $$ Hk Hpc Hw

/-- `sb rs2, imm(rs1)`: the low byte of `rs2` to `rs1 + imm` (the raw form: a byte window plus the RAM fact; clients use `wp_s_sb`). -/
theorem wp_s_sb_bytes [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 rs2 : BitVec 5)
    (old : BitVec 8) (hram : inRam (k.rget cpu rs1 + BitVec.signExtend 64 imm) 1) :
    instr (GF := GF) pc is_rvc (instruction.STORE (imm, regidx.Regidx rs2, regidx.Regidx rs1, 1)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 1 (DFrac.own 1) old ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 1 (DFrac.own 1)
            (BitVec.extractLsb' 0 8 (k.rget cpu rs2)) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_keep_mem cpu k hsie htier pc _ is_rvc _ _ _
    (fun c hok _ => execSpecF_sb cpu (DFrac.own 1) c false hok pc _ imm rs1 rs2 (tpPin cpu k.regs) old hram)

/-- `sb rs2, imm(rs1)`: the low byte of `rs2` to the byte at `rs1 + imm`. -/
theorem wp_s_sb [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 rs2 : BitVec 5) (old : BitVec 8) :
    instr (GF := GF) pc is_rvc (instruction.STORE (imm, regidx.Regidx rs2, regidx.Regidx rs1, 1)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 1 (DFrac.own 1) old ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 1 (DFrac.own 1)
            (BitVec.extractLsb' 0 8 (k.rget cpu rs2)) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨Hi, Hk, Hpc, Hw, Hnext⟩
  icases wordPointsTo_cases _ _ _ _ $$ Hw with ⟨%⟨hram, hal⟩, Hm⟩
  iapply (wp_s_sb_bytes cpu k hsie htier pc is_rvc imm rs1 rs2 old hram)
  iframe Hi Hk Hpc Hm
  inext
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK Hk Hpc Hm
  ihave Hw := wordPointsTo_intro _ _ _ _ hram hal $$ Hm
  iapply HK $$ Hk Hpc Hw

/-- `sd rs2, imm(rs1)`: `rs2` to `rs1 + imm` (8-aligned) (the raw form: a byte window plus the facts; clients use `wp_s_sd`). -/
theorem wp_s_sd_bytes [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 rs2 : BitVec 5)
    (old : BitVec 64) (hram : inRam (k.rget cpu rs1 + BitVec.signExtend 64 imm) 8)
    (hal : (k.rget cpu rs1 + BitVec.signExtend 64 imm).toNat % 8 = 0) :
    instr (GF := GF) pc is_rvc (instruction.STORE (imm, regidx.Regidx rs2, regidx.Regidx rs1, 8)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 8 (DFrac.own 1) old ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 8 (DFrac.own 1) (k.rget cpu rs2) -∗
          wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_keep_mem cpu k hsie htier pc _ is_rvc _ _ _
    (fun c hok _ => execSpecF_sd cpu (DFrac.own 1) c false hok pc _ imm rs1 rs2 (tpPin cpu k.regs) old hram hal)

/-- `sd rs2, imm(rs1)`: `rs2` to the word at `rs1 + imm`. -/
theorem wp_s_sd [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 rs2 : BitVec 5) (old : BitVec 64) :
    instr (GF := GF) pc is_rvc (instruction.STORE (imm, regidx.Regidx rs2, regidx.Regidx rs1, 8)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 8 (DFrac.own 1) old ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 8 (DFrac.own 1) (k.rget cpu rs2) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨Hi, Hk, Hpc, Hw, Hnext⟩
  icases wordPointsTo_cases _ _ _ _ $$ Hw with ⟨%⟨hram, hal⟩, Hm⟩
  iapply (wp_s_sd_bytes cpu k hsie htier pc is_rvc imm rs1 rs2 old hram hal)
  iframe Hi Hk Hpc Hm
  inext
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK Hk Hpc Hm
  ihave Hw := wordPointsTo_intro _ _ _ _ hram hal $$ Hm
  iapply HK $$ Hk Hpc Hw

/-! ## Control flow -/

/-- The conditional branches. -/
theorem wp_s_branch [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 13) (rs1 rs2 : BitVec 5) (hrs1 : rs1 ≠ 0#5) (op : bop) :
    instr (GF := GF) pc is_rvc (instruction.BTYPE (imm, regidx.Regidx rs2, regidx.Regidx rs1, op)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗
          pcIs cpu' (if bcond op (k.rget cpu rs1) (k.rget cpu rs2) then pc + BitVec.signExtend 64 imm
            else pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  instr_pure_elim pc is_rvc _ _ _ (fun hpc hwf =>
    wpLoop_k_keep0 cpu k hsie htier pc _ is_rvc _
      (fun c _ _ => execSpecF_btype cpu (DFrac.own 1) c pc (pc + instrLen is_rvc) imm rs1 rs2 hrs1 op
        (tpPin cpu k.regs) (jumpTgt_even_13 pc imm hpc (instrWf_btype hwf))))

/-- `j off`. -/
theorem wp_s_j [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 21) :
    instr (GF := GF) pc is_rvc (instruction.JAL (imm, regidx.Regidx 0#5)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' (pc + BitVec.signExtend 64 imm) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  instr_pure_elim pc is_rvc _ _ _ (fun hpc hwf =>
    wpLoop_k_keep0 cpu k hsie htier pc _ is_rvc _
      (fun c _ _ => execSpecF_j cpu (DFrac.own 1) c pc (pc + instrLen is_rvc) imm (tpPin cpu k.regs)
        (jumpTgt_even_21 pc imm hpc (instrWf_jal hwf))))

/-- `jal rd, off` (`rd` not `x0`/`sp`/`tp`, e.g. `ra`): link, jump. -/
theorem wp_s_jal [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 21) (rd : BitVec 5) (hrd : rdOk rd) :
    instr (GF := GF) pc is_rvc (instruction.JAL (imm, regidx.Regidx rd)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (pc + instrLen is_rvc)) -∗
          pcIs cpu' (pc + BitVec.signExtend 64 imm) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  instr_pure_elim pc is_rvc _ _ _ (fun hpc hwf =>
    wpLoop_k_setReg cpu k hsie htier pc _ is_rvc _ rd hrd _
      (fun c _ _ => execSpecF_jal cpu (DFrac.own 1) c pc _ imm rd hrd.1 (tpPin cpu k.regs)
        (jumpTgt_even_21 pc imm hpc (instrWf_jal hwf))))

/-- `ret` (`jalr x0, 0(rs1)`, `rs1 = ra`): jump to `rs1` with bit 0 cleared. -/
theorem wp_s_ret [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (rs1 : BitVec 5) :
    instr (GF := GF) pc is_rvc (instruction.JALR (0#12, regidx.Regidx rs1, regidx.Regidx 0#5)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' (jumpPc (k.rget cpu rs1)) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_keep0 cpu k hsie htier pc _ is_rvc _
    (fun c hok _ => execSpecF_ret cpu (DFrac.own 1) c false hok pc (pc + instrLen is_rvc) rs1 (tpPin cpu k.regs))

/-! ## Word arithmetic -/

/-- `subw rd, rs1, rs2`. -/
theorem wp_s_subw [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (rd rs1 rs2 : BitVec 5) (hrd : rdOk rd) :
    instr (GF := GF) pc is_rvc (instruction.RTYPEW (regidx.Regidx rs2, regidx.Regidx rs1, regidx.Regidx rd, ropw.SUBW)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (BitVec.signExtend 64
          (BitVec.extractLsb' 0 32 (k.rget cpu rs1) - BitVec.extractLsb' 0 32 (k.rget cpu rs2)))) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_setReg cpu k hsie htier pc _ is_rvc _ rd hrd _
    (fun c _ _ => execSpecF_subw cpu (DFrac.own 1) c pc _ rd rs1 rs2 hrd.1 (tpPin cpu k.regs))

/-- `addw rd, rs1, rs2`. -/
theorem wp_s_addw [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (rd rs1 rs2 : BitVec 5) (hrd : rdOk rd) :
    instr (GF := GF) pc is_rvc (instruction.RTYPEW (regidx.Regidx rs2, regidx.Regidx rs1, regidx.Regidx rd, ropw.ADDW)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (BitVec.signExtend 64
          (BitVec.extractLsb' 0 32 (k.rget cpu rs1) + BitVec.extractLsb' 0 32 (k.rget cpu rs2)))) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_setReg cpu k hsie htier pc _ is_rvc _ rd hrd _
    (fun c _ _ => execSpecF_addw cpu (DFrac.own 1) c pc _ rd rs1 rs2 hrd.1 (tpPin cpu k.regs))

/-! ## The stack -/

set_option maxHeartbeats 4000000 in
/-- `addi sp, sp, -8m`: push `m` slots (out of the `avail`); the slots
`[sp - 8m, sp)` become the caller's frame. -/
theorem wp_s_push [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (m : Nat) (hm : m ≤ k.avail)
    (himm : BitVec.signExtend 64 imm = -(8#64 * BitVec.ofNat 64 m)) :
    instr (GF := GF) pc is_rvc (instruction.ITYPE (imm, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.push m) -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          stackOwn k.sp m -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  have hval : RegMap.get (tpPin cpu k.regs) 2#5 + BitVec.signExtend 64 imm = k.sp - 8#64 * BitVec.ofNat 64 m := by
    rw [himm, ← BitVec.sub_eq_add_neg]
    have := KCtx.rget_ne cpu k 2#5 (by decide) (by decide)
    simp only [KCtx.rget] at this
    rw [this]; rfl
  have htp := tpPin_set cpu k.regs 2#5 (k.sp - 8#64 * BitVec.ofNat 64 m) (by decide)
  iintro ⟨HI, Hk, Hpc, HΦ⟩
  icases kctx_cases cpu k $$ Hk with ⟨%hwf, HConf, HF, Hstack, Htrans, Harm, Hcpu, Htok, Hclock, #Hro⟩
  icases kConf_cases cpu _ _ _ $$ HConf with ⟨%ms, %mdl, %mepc, %stc, %⟨hsm, hmdl⟩, HmConf⟩
  rw [hsie] at hsm
  simp only [hsie, htier, trapRes_off]
  have hsplit : k.avail = m + (k.avail - m) := by omega
  rw [hsplit]
  icases stackOwn_split k.sp m (k.avail - m) $$ Hstack with ⟨Hframe, Hstack⟩
  have hok := SConfBare_sConfOf_bare (GF := GF) k.root ms mdl mepc stc hsm
  have hexec := execSpecF_addi (GF := GF) cpu (DFrac.own 1) (sConfOf KTier.bare k.root ms mdl mepc stc) pc
    (pc + instrLen is_rvc) imm 2#5 2#5 (by decide) (tpPin cpu k.regs) Privilege.Supervisor
  rw [hval, htp] at hexec
  iapply (wpLoop_s_instr cpu (DFrac.own 1) _ _ hok hmdl rfl pc _ is_rvc _ _ _ hexec)
  iframe
  inext
  iintro HmConf Hclock Hpc HF
  ihave HΦ' := wpNext_off _ _ _ $$ HΦ
  ihave HConf := kConf_intro cpu KTier.bare k.root false ms mdl mepc stc ⟨hsm, hmdl⟩ $$ HmConf
  iapply HΦ' $$ [HConf HF Hstack Htrans Harm Hcpu Htok Hclock] Hpc Hframe
  iapply (kctx_intro' cpu (k.push m) ((KCtx.wf_push k m).mpr hwf))
  simp only [KCtx.push_regs, KCtx.push_sie, KCtx.push_avail, KCtx.push_noff, KCtx.push_intena,
    KCtx.push_locks, KCtx.push_tier, KCtx.push_root, KCtx.push_proc, KCtx.push_sp, hsie, htier, trapRes_off]
  iframe
  iexact Hro

set_option maxHeartbeats 4000000 in
/-- `addi sp, sp, 8m`: pop `m` slots; the frame `[sp, sp + 8m)` returns to
the `avail`. -/
theorem wp_s_pop [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (m : Nat)
    (himm : BitVec.signExtend 64 imm = 8#64 * BitVec.ofNat 64 m) :
    instr (GF := GF) pc is_rvc (instruction.ITYPE (imm, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗ stackOwn (k.sp + 8#64 * BitVec.ofNat 64 m) m ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.pop m) -∗ pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  have hval : RegMap.get (tpPin cpu k.regs) 2#5 + BitVec.signExtend 64 imm = k.sp + 8#64 * BitVec.ofNat 64 m := by
    rw [himm]
    have := KCtx.rget_ne cpu k 2#5 (by decide) (by decide)
    simp only [KCtx.rget] at this
    rw [this]; rfl
  have htp := tpPin_set cpu k.regs 2#5 (k.sp + 8#64 * BitVec.ofNat 64 m) (by decide)
  have hback : k.sp + 8#64 * BitVec.ofNat 64 m - 8#64 * BitVec.ofNat 64 m = k.sp := by bv_omega
  iintro ⟨HI, Hk, Hpc, Hframe, HΦ⟩
  icases kctx_cases cpu k $$ Hk with ⟨%hwf, HConf, HF, Hstack, Htrans, Harm, Hcpu, Htok, Hclock, #Hro⟩
  icases kConf_cases cpu _ _ _ $$ HConf with ⟨%ms, %mdl, %mepc, %stc, %⟨hsm, hmdl⟩, HmConf⟩
  rw [hsie] at hsm
  simp only [hsie, htier, trapRes_off]
  ihave Hstack := (show stackOwn (GF := GF) k.sp k.avail ⊢
      stackOwn (k.sp + 8#64 * BitVec.ofNat 64 m - 8#64 * BitVec.ofNat 64 m) k.avail by rw [hback]) $$ Hstack
  ihave Hstack := stackOwn_join _ m k.avail $$ [Hframe Hstack]
  case' _ => iframe
  have hok := SConfBare_sConfOf_bare (GF := GF) k.root ms mdl mepc stc hsm
  have hexec := execSpecF_addi (GF := GF) cpu (DFrac.own 1) (sConfOf KTier.bare k.root ms mdl mepc stc) pc
    (pc + instrLen is_rvc) imm 2#5 2#5 (by decide) (tpPin cpu k.regs) Privilege.Supervisor
  rw [hval, htp] at hexec
  iapply (wpLoop_s_instr cpu (DFrac.own 1) _ _ hok hmdl rfl pc _ is_rvc _ _ _ hexec)
  iframe
  inext
  iintro HmConf Hclock Hpc HF
  ihave HΦ' := wpNext_off _ _ _ $$ HΦ
  ihave HConf := kConf_intro cpu KTier.bare k.root false ms mdl mepc stc ⟨hsm, hmdl⟩ $$ HmConf
  iapply HΦ' $$ [HConf HF Hstack Htrans Harm Hcpu Htok Hclock] Hpc
  iapply (kctx_intro' cpu (k.pop m) ((KCtx.wf_pop k m).mpr hwf))
  simp only [KCtx.pop_regs, KCtx.pop_sie, KCtx.pop_avail, KCtx.pop_noff, KCtx.pop_intena,
    KCtx.pop_locks, KCtx.pop_tier, KCtx.pop_root, KCtx.pop_proc, KCtx.pop_sp, hsie, htier, trapRes_off,
    Nat.add_comm m]
  iframe
  iexact Hro

/-! ## Value-dependent writes -/

set_option maxHeartbeats 4000000 in
/-- The schema for an instruction that writes a value `f c` computed from
the (hidden) configuration into the file: the continuation gets the value
`v` with the fact `P v` (`P` holds of `f c` at every context configuration). -/
theorem wpLoop_k_genv [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (htier : k.tier = KTier.bare) (pc npc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (f : MConf → BitVec 64) (P : BitVec 64 → Prop)
    (hP : ∀ c : MConf, SConfBare (GF := GF) c false → c.menvcfg = menvcfgS → P (f c))
    (R' : BitVec 64 → RegMap) (hsp : ∀ v, R' v 2#5 = k.regs 2#5)
    (hexec : ∀ c : MConf, SConfBare (GF := GF) c false → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c i pc
        (pc + instrLen is_rvc) npc
        (gprFile cpu (tpPin cpu k.regs)) (gprFile cpu (tpPin cpu (R' (f c))))) :
    instr (GF := GF) pc is_rvc i ∗ kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(∀ v : BitVec 64, ⌜P v⌝ -∗ kctx cpu' (k.withRegs (R' v)) -∗ pcIs cpu' npc -∗
          wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, HΦ⟩
  icases kctx_cases cpu k $$ Hk with ⟨%hwf, HConf, HF, Hstack, Htrans, Harm, Hcpu, Htok, Hclock, #Hro⟩
  icases kConf_cases cpu _ _ _ $$ HConf with ⟨%ms, %mdl, %mepc, %stc, %⟨hsm, hmdl⟩, HmConf⟩
  rw [hsie] at hsm
  simp only [hsie, htier]
  have hok := SConfBare_sConfOf_bare (GF := GF) k.root ms mdl mepc stc hsm
  have hsp' := KCtx.withRegs_sp k (R' (f (sConfOf KTier.bare k.root ms mdl mepc stc))) (hsp _)
  have hv := hP _ hok rfl
  iapply (wpLoop_s_instr cpu (DFrac.own 1) _ _ hok hmdl rfl pc npc is_rvc i _ _ (hexec _ hok rfl))
  iframe
  inext
  iintro HmConf Hclock Hpc HF
  ihave HΦ' := wpNext_off _ _ _ $$ HΦ
  ihave HConf := kConf_intro cpu KTier.bare k.root false ms mdl mepc stc ⟨hsm, hmdl⟩ $$ HmConf
  iapply HΦ' $$ %_ %hv [HConf HF Hstack Htrans Harm Hcpu Htok Hclock] Hpc
  iapply (kctx_intro' cpu (k.withRegs _) ((KCtx.wf_withRegs k _).mpr hwf))
  simp only [KCtx.withRegs_regs, KCtx.withRegs_sie, KCtx.withRegs_avail, KCtx.withRegs_noff,
    KCtx.withRegs_intena, KCtx.withRegs_locks, KCtx.withRegs_tier, KCtx.withRegs_root, KCtx.withRegs_proc,
    hsp', hsie, htier]
  iframe
  iexact Hro

/-- `sstatus` as the kernel reads it: its `SIE` bit is the context's index. -/
def sstatusAt (sie : Bool) (v : BitVec 64) : Prop :=
  BitVec.extractLsb' 1 1 v = (if sie then 1#1 else 0#1)

/-- `csrr rd, sstatus`: some value whose `SIE` bit is the context's. -/
theorem wp_s_csrr_sstatus [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (rd : BitVec 5) (hrd : rdOk rd) :
    instr (GF := GF) pc is_rvc (instruction.CSRReg (0x100#12, regidx.Regidx 0#5, regidx.Regidx rd, csrop.CSRRS)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(∀ v : BitVec 64, ⌜sstatusAt k.sie v⌝ -∗ kctx cpu' (k.setReg rd v) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  have htp := fun v => tpPin_set cpu k.regs rd v hrd.2.2
  have h := wpLoop_k_genv cpu k hsie htier pc (pc + instrLen is_rvc) is_rvc _
    (fun c => lower_mstatus c.mstatus) (sstatusAt k.sie)
    (fun c hok _ => by
      unfold sstatusAt; rw [lower_mstatus_sie, hsie]; exact hok.1.2.1.1)
    (fun v => k.regs.set rd v) (fun v => RegMap.set_other _ _ _ _ (Ne.symm hrd.2.1))
    (fun c hok _ => by
      have e := execSpecF_csrr_sstatus (GF := GF) cpu (DFrac.own 1) c false hok pc (pc + instrLen is_rvc) rd hrd.1
        (tpPin cpu k.regs)
      rw [htp] at e; exact e)
  simpa only [KCtx.setReg_eq_withRegs] using h

/-- `csrrci rd, sstatus, SIE` with interrupts off: reads `sstatus` (its `SIE`
bit is `0`), leaves the configuration alone (`intr_off` at `SIE = 0`). -/
theorem wp_s_csrrci_sstatus [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (rd : BitVec 5) (hrd : rdOk rd) :
    instr (GF := GF) pc is_rvc (instruction.CSRImm (0x100#12, 2#5, regidx.Regidx rd, csrop.CSRRC)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(∀ v : BitVec 64, ⌜sstatusAt k.sie v⌝ -∗ kctx cpu' (k.setReg rd v) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  have htp := fun v => tpPin_set cpu k.regs rd v hrd.2.2
  have h := wpLoop_k_genv cpu k hsie htier pc (pc + instrLen is_rvc) is_rvc _
    (fun c => lower_mstatus c.mstatus) (sstatusAt k.sie)
    (fun c hok _ => by
      unfold sstatusAt; rw [lower_mstatus_sie, hsie]; exact hok.1.2.1.1)
    (fun v => k.regs.set rd v) (fun v => RegMap.set_other _ _ _ _ (Ne.symm hrd.2.1))
    (fun c hok _ => by
      have e := execSpecF_csrrci_sstatus (GF := GF) cpu c hok pc (pc + instrLen is_rvc) rd hrd.1 (tpPin cpu k.regs)
      rw [htp] at e; exact e)
  simpa only [KCtx.setReg_eq_withRegs] using h

/-! ## Words -/

/-- `lw rd, imm(rs1)`: the sign-extended word at `rs1 + imm` (4-aligned) (the raw form: a byte window plus the facts; clients use `wp_s_lw`). -/
theorem wp_s_lw_bytes [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (dq' : DFrac) (w : BitVec 32) (hram : inRam (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4)
    (hal : (k.rget cpu rs1 + BitVec.signExtend 64 imm).toNat % 4 = 0) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, false, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 dq' w ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (BitVec.signExtend 64 w)) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗
          bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 dq' w -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_setReg_mem' cpu k hsie htier pc _ is_rvc _ rd hrd _ _ _
    (fun c hok _ => execSpecF_lw cpu (DFrac.own 1) dq' c false hok pc _ imm rd rs1 hrd.1
      (tpPin cpu k.regs) w hram hal)

/-- `lw rd, imm(rs1)`: the sign-extended word at `rs1 + imm`. -/
theorem wp_s_lw [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (dq' : DFrac) (w : BitVec 32) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, false, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 dq' w ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (BitVec.signExtend 64 w)) -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 dq' w -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨Hi, Hk, Hpc, Hw, Hnext⟩
  icases wordPointsTo_cases _ _ _ _ $$ Hw with ⟨%⟨hram, hal⟩, Hm⟩
  iapply (wp_s_lw_bytes cpu k hsie htier pc is_rvc imm rd rs1 hrd dq' w hram hal)
  iframe Hi Hk Hpc Hm
  inext
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK Hk Hpc Hm
  ihave Hw := wordPointsTo_intro _ _ _ _ hram hal $$ Hm
  iapply HK $$ Hk Hpc Hw

/-- `sw rs2, imm(rs1)`: the low word of `rs2` to `rs1 + imm` (4-aligned) (the raw form: a byte window plus the facts; clients use `wp_s_sw`). -/
theorem wp_s_sw_bytes [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 rs2 : BitVec 5)
    (old : BitVec 32) (hram : inRam (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4)
    (hal : (k.rget cpu rs1 + BitVec.signExtend 64 imm).toNat % 4 = 0) :
    instr (GF := GF) pc is_rvc (instruction.STORE (imm, regidx.Regidx rs2, regidx.Regidx rs1, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 (DFrac.own 1) old ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          bytesPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 (DFrac.own 1)
            (BitVec.extractLsb' 0 32 (k.rget cpu rs2)) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  wpLoop_k_keep_mem cpu k hsie htier pc _ is_rvc _ _ _
    (fun c hok _ => execSpecF_sw cpu (DFrac.own 1) c false hok pc _ imm rs1 rs2 (tpPin cpu k.regs) old hram hal)

/-- `sw rs2, imm(rs1)`: the low word of `rs2` to the word at `rs1 + imm`. -/
theorem wp_s_sw [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 rs2 : BitVec 5) (old : BitVec 32) :
    instr (GF := GF) pc is_rvc (instruction.STORE (imm, regidx.Regidx rs2, regidx.Regidx rs1, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 (DFrac.own 1) old ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗
          wordPointsTo (k.rget cpu rs1 + BitVec.signExtend 64 imm) 4 (DFrac.own 1)
            (BitVec.extractLsb' 0 32 (k.rget cpu rs2)) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨Hi, Hk, Hpc, Hw, Hnext⟩
  icases wordPointsTo_cases _ _ _ _ $$ Hw with ⟨%⟨hram, hal⟩, Hm⟩
  iapply (wp_s_sw_bytes cpu k hsie htier pc is_rvc imm rs1 rs2 old hram hal)
  iframe Hi Hk Hpc Hm
  inext
  iapply wpNext_mono $$ Hnext
  iintro %cpu' HK Hk Hpc Hm
  ihave Hw := wordPointsTo_intro _ _ _ _ hram hal $$ Hm
  iapply HK $$ Hk Hpc Hw

/-- The conditional branches against `x0` as `rs1` (`blez`, `bgtz`, ...). -/
theorem wp_s_branch0 [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 13) (rs2 : BitVec 5) (hrs2 : rs2 ≠ 0#5) (op : bop) :
    instr (GF := GF) pc is_rvc (instruction.BTYPE (imm, regidx.Regidx rs2, regidx.Regidx 0#5, op)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' k -∗
          pcIs cpu' (if bcond op 0#64 (k.rget cpu rs2) then pc + BitVec.signExtend 64 imm
            else pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu :=
  instr_pure_elim pc is_rvc _ _ _ (fun hpc hwf =>
    wpLoop_k_keep0 cpu k hsie htier pc _ is_rvc _
      (fun c _ _ => execSpecF_btype0 cpu (DFrac.own 1) c pc (pc + instrLen is_rvc) imm rs2 hrs2 op
        (tpPin cpu k.regs) (jumpTgt_even_13 pc imm hpc (instrWf_btype hwf))))

/-! ## The per-cpu cells -/

/-- The context with `noff`/`intena` replaced (the registers too). -/
def KCtx.withCpu (k : KCtx) (R : RegMap) (noff : Nat) (intena : Bool) : KCtx :=
  { k with regs := R, noff := noff, intena := intena }

@[simp] theorem KCtx.withCpu_regs (k : KCtx) (R : RegMap) (n : Nat) (b : Bool) : (k.withCpu R n b).regs = R := rfl
@[simp] theorem KCtx.withCpu_sie (k : KCtx) (R : RegMap) (n : Nat) (b : Bool) : (k.withCpu R n b).sie = k.sie := rfl
@[simp] theorem KCtx.withCpu_avail (k : KCtx) (R : RegMap) (n : Nat) (b : Bool) : (k.withCpu R n b).avail = k.avail := rfl
@[simp] theorem KCtx.withCpu_noff (k : KCtx) (R : RegMap) (n : Nat) (b : Bool) : (k.withCpu R n b).noff = n := rfl
@[simp] theorem KCtx.withCpu_intena (k : KCtx) (R : RegMap) (n : Nat) (b : Bool) : (k.withCpu R n b).intena = b := rfl
@[simp] theorem KCtx.withCpu_locks (k : KCtx) (R : RegMap) (n : Nat) (b : Bool) : (k.withCpu R n b).locks = k.locks := rfl
@[simp] theorem KCtx.withCpu_tier (k : KCtx) (R : RegMap) (n : Nat) (b : Bool) : (k.withCpu R n b).tier = k.tier := rfl
@[simp] theorem KCtx.withCpu_root (k : KCtx) (R : RegMap) (n : Nat) (b : Bool) : (k.withCpu R n b).root = k.root := rfl
@[simp] theorem KCtx.withCpu_proc (k : KCtx) (R : RegMap) (n : Nat) (b : Bool) : (k.withCpu R n b).proc = k.proc := rfl
@[simp] theorem KCtx.withCpu_sp (k : KCtx) (R : RegMap) (n : Nat) (b : Bool) : (k.withCpu R n b).sp = R 2#5 := rfl
theorem KCtx.withCpu_self [CurCtx] (k : KCtx) (R : RegMap) : k.withCpu R k.noff k.intena = k.withRegs R := rfl

set_option maxHeartbeats 4000000 in
/-- The schema for an instruction that reads or writes this hart's
`struct cpu` cells (through the accessor `hacc` on `cpuCells`), possibly
moving the context to depth `noff'` / saved enable `intena'` (which must
keep it well formed). -/
theorem wpLoop_k_cpu [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false)
    (htier : k.tier = KTier.bare) (pc npc : BitVec 64) (is_rvc : Bool) (i : instruction)
    (R' : RegMap) (hsp : R' 2#5 = k.regs 2#5) (noff' : Nat) (intena' : Bool)
    (hwf' : (k.withCpu R' noff' intena').wf) (P Q : IProp GF)
    (hacc : cpuCells (GF := GF) cpu k.noff k.intena k.proc ⊢ P ∗ (Q -∗ cpuCells cpu noff' intena' k.proc))
    (hexec : ∀ c : MConf, SConfBare (GF := GF) c false → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c i pc
        (pc + instrLen is_rvc) npc
        iprop(gprFile cpu (tpPin cpu k.regs) ∗ ctxToken cpu ∗ P)
        iprop(gprFile cpu (tpPin cpu R') ∗ ctxToken cpu ∗ Q)) :
    instr (GF := GF) pc is_rvc i ∗ kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.withCpu R' noff' intena') -∗ pcIs cpu' npc -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, HΦ⟩
  icases kctx_cases cpu k $$ Hk with ⟨%hwf, HConf, HF, Hstack, Htrans, Harm, Hcpu, Htok, Hclock, #Hro⟩
  icases kConf_cases cpu _ _ _ $$ HConf with ⟨%ms, %mdl, %mepc, %stc, %⟨hsm, hmdl⟩, HmConf⟩
  unfold cpuOwn
  icases Hcpu with ⟨Hcells, Hlocks, Hcsrs⟩
  icases hacc $$ Hcells with ⟨HP, Hclose⟩
  rw [hsie] at hsm
  simp only [hsie, htier]
  have hok := SConfBare_sConfOf_bare (GF := GF) k.root ms mdl mepc stc hsm
  iapply (wpLoop_s_instr cpu (DFrac.own 1) _ _ hok hmdl rfl pc npc is_rvc i _ _ (hexec _ hok rfl))
  iframe
  inext
  iintro HmConf Hclock Hpc ⟨HF, Htok, HQ⟩
  ihave Hcells := Hclose $$ HQ
  ihave HΦ' := wpNext_off _ _ _ $$ HΦ
  ihave HConf := kConf_intro cpu KTier.bare k.root false ms mdl mepc stc ⟨hsm, hmdl⟩ $$ HmConf
  iapply HΦ' $$ [HConf HF Hstack Htrans Harm Hcells Hlocks Hcsrs Htok Hclock] Hpc
  iapply (kctx_intro' cpu (k.withCpu R' noff' intena') hwf')
  unfold cpuOwn
  simp only [KCtx.withCpu_regs, KCtx.withCpu_sie, KCtx.withCpu_avail, KCtx.withCpu_noff, KCtx.withCpu_intena,
    KCtx.withCpu_locks, KCtx.withCpu_tier, KCtx.withCpu_root, KCtx.withCpu_proc, KCtx.withCpu_sp, hsp, hsie, htier,
    KCtx.sp]
  iframe
  iexact Hro

/-- A sign-extended 32-bit count below `2^31` is the count. -/
theorem signExtend_ofNat32 (n : Nat) (hn : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  have hmsb : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; rw [Nat.mod_eq_of_lt (by omega)]
    simp; omega
  rw [hmsb]
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega : n < 4294967296), Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]

/-- `c->noff` as a 64-bit value: the depth. -/
theorem signExtend_noff (k : KCtx) (hwf : k.wf) :
    BitVec.signExtend 64 (BitVec.ofNat 32 k.noff) = BitVec.ofNat 64 k.noff :=
  signExtend_ofNat32 _ hwf.2.2.2.2

/-- `c->intena` as a 64-bit value. -/
theorem signExtend_intena (b : Bool) :
    BitVec.signExtend 64 (intenaVal b) = if b then 1#64 else 0#64 := by
  cases b <;> rfl

/-- `lw rd, imm(rs1)` of `c->noff` (`rs1 + imm = &c->noff`): the depth. -/
theorem wp_s_lw_noff [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = aCpuNoff cpu) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, false, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (BitVec.ofNat 64 k.noff)) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, HΦ⟩
  icases kctx_cases cpu k $$ Hk with ⟨%hwf, Hrest⟩
  ihave Hk := kctx_intro' cpu k hwf $$ Hrest
  icases kctx_cpu_facts cpu k $$ Hk with ⟨%hf, Hk⟩
  have ⟨hram, hal⟩ := hf.2.1
  rw [← haddr] at hram hal
  have htp := tpPin_set cpu k.regs rd (BitVec.ofNat 64 k.noff) hrd.2.2
  have hsx := signExtend_noff k hwf
  iapply (wpLoop_k_cpu cpu k hsie htier pc (pc + instrLen is_rvc) is_rvc _ (k.regs.set rd (BitVec.ofNat 64 k.noff))
    (RegMap.set_other _ _ _ _ (Ne.symm hrd.2.1)) k.noff k.intena (by rw [KCtx.withCpu_self]; exact hwf)
    (bytesPointsTo (aCpuNoff cpu) 4 (DFrac.own 1) (BitVec.ofNat 32 k.noff))
    (bytesPointsTo (aCpuNoff cpu) 4 (DFrac.own 1) (BitVec.ofNat 32 k.noff))
    (by
      unfold cpuCells
      iintro ⟨Hp, Hn, Hi⟩
      icases wordPointsTo_cases _ _ _ _ $$ Hn with ⟨%⟨hr, ha⟩, Hn⟩
      iframe Hn
      iintro Hn
      ihave Hn := wordPointsTo_intro _ _ _ _ hr ha $$ Hn
      iframe)
    (fun c hok _ => by
      have e := execSpecF_lw (GF := GF) cpu (DFrac.own 1) (DFrac.own 1) c false hok pc (pc + instrLen is_rvc) imm rd rs1
        hrd.1 (tpPin cpu k.regs) (BitVec.ofNat 32 k.noff) hram hal
      rw [hsx, htp] at e
      simp only [KCtx.rget] at haddr
      rw [haddr] at e
      exact e))
  iframe
  inext
  simp only [KCtx.withCpu_self, ← KCtx.setReg_eq_withRegs]
  iexact HΦ

/-- `lw rd, imm(rs1)` of `c->intena`: the saved enable state. -/
theorem wp_s_lw_intena [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = aCpuIntena cpu) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, false, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd (if k.intena then 1#64 else 0#64)) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, HΦ⟩
  icases kctx_cases cpu k $$ Hk with ⟨%hwf, Hrest⟩
  ihave Hk := kctx_intro' cpu k hwf $$ Hrest
  icases kctx_cpu_facts cpu k $$ Hk with ⟨%hf, Hk⟩
  have ⟨hram, hal⟩ := hf.2.2
  rw [← haddr] at hram hal
  have htp := tpPin_set cpu k.regs rd (if k.intena then 1#64 else 0#64) hrd.2.2
  have hsx := signExtend_intena k.intena
  iapply (wpLoop_k_cpu cpu k hsie htier pc (pc + instrLen is_rvc) is_rvc _
    (k.regs.set rd (if k.intena then 1#64 else 0#64))
    (RegMap.set_other _ _ _ _ (Ne.symm hrd.2.1)) k.noff k.intena (by rw [KCtx.withCpu_self]; exact hwf)
    (bytesPointsTo (aCpuIntena cpu) 4 (DFrac.own 1) (intenaVal k.intena))
    (bytesPointsTo (aCpuIntena cpu) 4 (DFrac.own 1) (intenaVal k.intena))
    (by
      unfold cpuCells
      iintro ⟨Hp, Hn, Hi⟩
      icases wordPointsTo_cases _ _ _ _ $$ Hi with ⟨%⟨hr, ha⟩, Hi⟩
      iframe Hi
      iintro Hi
      ihave Hi := wordPointsTo_intro _ _ _ _ hr ha $$ Hi
      iframe)
    (fun c hok _ => by
      have e := execSpecF_lw (GF := GF) cpu (DFrac.own 1) (DFrac.own 1) c false hok pc (pc + instrLen is_rvc) imm rd rs1
        hrd.1 (tpPin cpu k.regs) (intenaVal k.intena) hram hal
      rw [hsx, htp] at e
      simp only [KCtx.rget] at haddr
      rw [haddr] at e
      exact e))
  iframe
  inext
  simp only [KCtx.withCpu_self, ← KCtx.setReg_eq_withRegs]
  iexact HΦ

/-- `sw rs2, imm(rs1)` to `c->noff`: the depth becomes `n'` (the value
stored), which must keep the context well formed. -/
theorem wp_s_sw_noff [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 rs2 : BitVec 5)
    (haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = aCpuNoff cpu) (n' : Nat)
    (hval : BitVec.extractLsb' 0 32 (k.rget cpu rs2) = BitVec.ofNat 32 n')
    (hwf' : (k.withCpu k.regs n' k.intena).wf) :
    instr (GF := GF) pc is_rvc (instruction.STORE (imm, regidx.Regidx rs2, regidx.Regidx rs1, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.withCpu k.regs n' k.intena) -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, HΦ⟩
  icases kctx_cpu_facts cpu k $$ Hk with ⟨%hf, Hk⟩
  have ⟨hram, hal⟩ := hf.2.1
  rw [← haddr] at hram hal
  iapply (wpLoop_k_cpu cpu k hsie htier pc (pc + instrLen is_rvc) is_rvc _ k.regs rfl n' k.intena hwf'
    (bytesPointsTo (aCpuNoff cpu) 4 (DFrac.own 1) (BitVec.ofNat 32 k.noff))
    (bytesPointsTo (aCpuNoff cpu) 4 (DFrac.own 1) (BitVec.ofNat 32 n'))
    (by
      unfold cpuCells
      iintro ⟨Hp, Hn, Hi⟩
      icases wordPointsTo_cases _ _ _ _ $$ Hn with ⟨%⟨hr, ha⟩, Hn⟩
      iframe Hn
      iintro Hn
      ihave Hn := wordPointsTo_intro _ _ _ _ hr ha $$ Hn
      iframe)
    (fun c hok _ => by
      have e := execSpecF_sw (GF := GF) cpu (DFrac.own 1) c false hok pc (pc + instrLen is_rvc) imm rs1 rs2
        (tpPin cpu k.regs) (BitVec.ofNat 32 k.noff) hram hal
      simp only [KCtx.rget] at haddr hval
      rw [haddr, hval] at e
      exact e))
  iframe

/-- `sw rs2, imm(rs1)` to `c->intena`: the saved enable state becomes `b'`
(the value stored), which must keep the context well formed. -/
theorem wp_s_sw_intena [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 rs2 : BitVec 5)
    (haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = aCpuIntena cpu) (b' : Bool)
    (hval : BitVec.extractLsb' 0 32 (k.rget cpu rs2) = intenaVal b')
    (hwf' : (k.withCpu k.regs k.noff b').wf) :
    instr (GF := GF) pc is_rvc (instruction.STORE (imm, regidx.Regidx rs2, regidx.Regidx rs1, 4)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.withCpu k.regs k.noff b') -∗
          pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, HΦ⟩
  icases kctx_cpu_facts cpu k $$ Hk with ⟨%hf, Hk⟩
  have ⟨hram, hal⟩ := hf.2.2
  rw [← haddr] at hram hal
  iapply (wpLoop_k_cpu cpu k hsie htier pc (pc + instrLen is_rvc) is_rvc _ k.regs rfl k.noff b' hwf'
    (bytesPointsTo (aCpuIntena cpu) 4 (DFrac.own 1) (intenaVal k.intena))
    (bytesPointsTo (aCpuIntena cpu) 4 (DFrac.own 1) (intenaVal b'))
    (by
      unfold cpuCells
      iintro ⟨Hp, Hn, Hi⟩
      icases wordPointsTo_cases _ _ _ _ $$ Hi with ⟨%⟨hr, ha⟩, Hi⟩
      iframe Hi
      iintro Hi
      ihave Hi := wordPointsTo_intro _ _ _ _ hr ha $$ Hi
      iframe)
    (fun c hok _ => by
      have e := execSpecF_sw (GF := GF) cpu (DFrac.own 1) c false hok pc (pc + instrLen is_rvc) imm rs1 rs2
        (tpPin cpu k.regs) (intenaVal k.intena) hram hal
      simp only [KCtx.rget] at haddr hval
      rw [haddr, hval] at e
      exact e))
  iframe

/-- `ld rd, imm(rs1)` of `c->proc`: the running proc. -/
theorem wp_s_ld_proc [CurCtx] [KernelGeom] [KernelImage GF] (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rd rs1 : BitVec 5) (hrd : rdOk rd)
    (haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = aCpuProc cpu) :
    instr (GF := GF) pc is_rvc (instruction.LOAD (imm, regidx.Regidx rs1, regidx.Regidx rd, false, 8)) ∗
    kctx cpu k ∗ pcIs cpu pc ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctx cpu' (k.setReg rd k.proc) -∗ pcIs cpu' (pc + instrLen is_rvc) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, HΦ⟩
  icases kctx_cases cpu k $$ Hk with ⟨%hwf, Hrest⟩
  ihave Hk := kctx_intro' cpu k hwf $$ Hrest
  icases kctx_cpu_facts cpu k $$ Hk with ⟨%hf, Hk⟩
  have ⟨hram, hal⟩ := hf.1
  rw [← haddr] at hram hal
  have htp := tpPin_set cpu k.regs rd k.proc hrd.2.2
  iapply (wpLoop_k_cpu cpu k hsie htier pc (pc + instrLen is_rvc) is_rvc _ (k.regs.set rd k.proc)
    (RegMap.set_other _ _ _ _ (Ne.symm hrd.2.1)) k.noff k.intena (by rw [KCtx.withCpu_self]; exact hwf)
    (bytesPointsTo (aCpuProc cpu) 8 (DFrac.own 1) k.proc)
    (bytesPointsTo (aCpuProc cpu) 8 (DFrac.own 1) k.proc)
    (by
      unfold cpuCells
      iintro ⟨Hp, Hn, Hi⟩
      icases wordPointsTo_cases _ _ _ _ $$ Hp with ⟨%⟨hr, ha⟩, Hp⟩
      iframe Hp
      iintro Hp
      ihave Hp := wordPointsTo_intro _ _ _ _ hr ha $$ Hp
      iframe)
    (fun c hok _ => by
      have e := execSpecF_ld (GF := GF) cpu (DFrac.own 1) (DFrac.own 1) c false hok pc (pc + instrLen is_rvc) imm rd rs1
        hrd.1 (tpPin cpu k.regs) k.proc hram hal
      rw [htp] at e
      simp only [KCtx.rget] at haddr
      rw [haddr] at e
      exact e))
  iframe
  inext
  simp only [KCtx.withCpu_self, ← KCtx.setReg_eq_withRegs]
  iexact HΦ

end MachCSL
