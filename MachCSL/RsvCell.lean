/-
MachCSL: STORES INTO A RESERVED WORD (W8-β′).

A reserved word is held at HALF (`MachCSL.cpuCell`; the state interpretation
holds the other half, `MachCSL.rsvModelAt`), so the owned-memory store rules
(`execSpecF_sw`/`execSpecF_sd`, which take the whole cell) cannot write it.
These are the dedicated stores: the accessor stage lemmas
(`execSpecF_sw_au`/`execSpecF_sd_au`) with a RESERVED-mode accessor
(`writeAURsv`) built from the half cell (`ctxBytes_writeAURsv`), whose
obligation (`rsvWordOk`: the word is a word of a static region and the store
keeps that region's discipline) the caller states -- for `cpus[h]`'s cells,
any store by hart `h` (`cpuCellOk_wordOk`, `MachCSL.cpuRegion_store`).

`execSpecF_sw_rsv` / `execSpecF_sd_rsv` have the owned stage lemmas' shape:
the cell (with its identity claim and the obligation) in, the cell at the
stored value out, the hart's translation token threaded.
-/
import MachCSL.WpSmodeAtomic
import MachCSL.CtxKeyMint
import MachCSL.BytesFree
import MachCSL.KCtx

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std Std
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- **A reserved word store's obligation, history-free**: `(pa, n)` is word `k`
of static region `i`, and any store of `w` there by `cpu` keeps the region's
discipline. -/
def rsvWordOk (cpu : CPU) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) : Prop :=
  ∃ (i k : Nat) (R : RsvRegion), (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))[i]? = some R ∧
    R.words[k]? = some (pa, n) ∧ (∀ w', R.kind ≠ .pub w') ∧ (∀ cb, R.kind ≠ .lock cb) ∧
    ∀ (m : FlatMem) (t : Nat), 0 < t → regionOk m R → regionOk (m.writeBytes pa n w t (hartAgent cpu)) R

theorem rsvWordOk_storeOk (cpu : CPU) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (Hs : Nat → Hist)
    (h : rsvWordOk (hlc := hlc) (GF := GF) cpu pa n w) : rsvStoreOk (hlc := hlc) (GF := GF) cpu pa n w Hs [] := by
  obtain ⟨i, k, R, hi, hk, hnp, -, hp⟩ := h
  exact ⟨i, k, R, hi, hk, hnp, fun m t ht _ _ hR => hp m t ht hR⟩

/-- ...and it makes no release entry. -/
theorem rsvWordOk_relFree (cpu : CPU) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (Hs : Nat → Hist)
    (h : rsvWordOk (hlc := hlc) (GF := GF) cpu pa n w) :
    rsvRelFree (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) pa n w Hs := by
  obtain ⟨i, k, R, hi, hk, hnp, hnl, -⟩ := h
  exact rsvRelFree_word (MachFixedGS.rsvStatic_wf (hlc := hlc) (GF := GF)).1 hi hk w Hs
    (fun cb hc => absurd hc (hnl cb)) hnp

theorem aCpuProc_eq [KernelGeom] (cpu : CPU) : aCpuProc cpu = cpuAddr cpu := by
  unfold aCpuProc procOff; simp

/-- A `cpus[cpu]` cell's side facts make any store into it by `cpu` a legal
reserved store. -/
theorem cpuCellOk_wordOk [KernelGeom] {cpu : CPU} {va : PAddr} {n : Nat}
    (h : cpuCellOk (hlc := hlc) (GF := GF) cpu va n) (w : BitVec (8 * n)) :
    rsvWordOk (hlc := hlc) (GF := GF) cpu va n w := by
  obtain ⟨⟨i, hi⟩, hw⟩ := h
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hw
  exact ⟨i, k, _, hi, hk, fun _ h => RsvKind.noConfusion h, fun _ h => RsvKind.noConfusion h,
    fun m t _ hR => cpuRegion_store rfl m _ n w t hR⟩

/-- The three cells are words of the region. -/
theorem cpuWords_mem [KernelGeom] (cpu : CPU) :
    (aCpuProc cpu, 8) ∈ RsvRegion.words ⟨cpuAddr cpu, .cpu cpu⟩ ∧
    (aCpuNoff cpu, 4) ∈ RsvRegion.words ⟨cpuAddr cpu, .cpu cpu⟩ ∧
    (aCpuIntena cpu, 4) ∈ RsvRegion.words ⟨cpuAddr cpu, .cpu cpu⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [RsvRegion.words, aCpuProc_eq, aCpuNoff, aCpuIntena, noffOff, intenaOff] <;> rfl

/-- `ctxBytesOfKeyed` (`MachCSL.ctxBytes_of_keyed`, `WpDmaCtx`, re-proved here
below the S-mode rules). -/
theorem RsvCell.ctxBytesOfKeyed (ξ : CtxId) (pa : PAddr) (dq : DFrac) (t : Nat) (ag : Agent)
    (Hs : Nat → Hist) (bs : Nat → BitVec 8) :
    ∀ n : Nat, keyAt (MachGS.era (hlc := hlc) (GF := GF)) ξ t ∗
        ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dq} (⟨t, ag, bs j⟩ :: Hs j))
      ⊢@{IProp GF} [∗list] j ∈ List.range n, ctxByte ξ (pa + BitVec.ofNat 64 j) dq (bs j)
  | 0 => by
    iintro ⟨_, _⟩
    simp only [List.range_zero]
    exact BigSepL.bigSepL_nil_intro
  | n + 1 => by
    rw [List.range_succ]
    iintro ⟨#Hkey, H⟩
    icases BigSepL.bigSepL_snoc.1 $$ H with ⟨H1, H2⟩
    iapply BigSepL.bigSepL_snoc.2
    isplitl [H1]
    · iapply RsvCell.ctxBytesOfKeyed ξ pa dq t ag Hs bs n
      iframe H1
      iexact Hkey
    · unfold ctxByte
      iexists ⟨t, ag, bs n⟩, (Hs n)
      iframe H2
      isplit
      · ipureintro; rfl
      · iexact Hkey

/-- **The reserved-mode accessor of a half context window**: the store of `w`
by `cpu`, the window coming back at `w`, keyed at the store's position. -/
theorem ctxBytes_writeAURsv [CurCtx] (cpu : CPU) (pa : PAddr) (n : Nat) (w0 w : BitVec (8 * n))
    (hok : rsvWordOk (hlc := hlc) (GF := GF) cpu pa n w) :
    ctxBytes curCtx pa n (DFrac.own (1 : Qp).half) w0 ⊢@{IProp GF}
      ownCtx cpu curCtx -∗
        writeAU cpu pa n w iprop(ownCtx cpu curCtx ∗ ctxBytes curCtx pa n (DFrac.own (1 : Qp).half) w) := by
  iintro Hb Hctx
  iapply writeAU_of_rsv
  unfold writeAURsv
  icases histBytes_of_wordBytes curCtx pa n (DFrac.own (1 : Qp).half) w0 $$ Hb with ⟨%Hs, Hb⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists Hs, [], none
  iframe Hb
  isplitr
  · unfold compBytes; iempintro
  isplit
  · ipureintro; exact rsvWordOk_storeOk cpu pa n w Hs hok
  isplitr
  · unfold rsvPcCell; iempintro
  isplit
  · ipureintro; exact rsvWordOk_relFree cpu pa n w Hs hok
  inext
  iintro %t %_ Hb _ _ #Hau #Htop
  imod Hmask
  imod ctx_key_mint cpu curCtx t $$ [Hctx Hau Htop] with ⟨Hctx, #Hkey⟩
  · iframe Hctx
    isplit
    · iexact Hau
    · iexact Htop
  imodintro
  iframe Hctx
  unfold ctxBytes histBytes
  iapply RsvCell.ctxBytesOfKeyed curCtx pa _ t (hartAgent cpu) Hs (nthByte w) n
  iframe Hb
  iexact Hkey

set_option maxHeartbeats 4000000 in
/-- **`sw rs2, imm(rs1)` into a reserved word** (the owned `execSpecF_sw`'s
shape, over `execSpecF_sw_au`): the half cell, its identity claim and the
store's obligation in; the half cell at the stored value out. -/
theorem execSpecF_sw_rsv [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (root : BitVec 44) (hok : SConfAt (GF := GF) curTier c root sie)
    (pc npc₀ : BitVec 64) (imm : BitVec 12) (rs1 rs2 : BitVec 5) (R : RegMap) (old : BitVec 32) :
    execSpecPP (GF := GF) cpu dq Privilege.Supervisor c Privilege.Supervisor c
      (instruction.STORE (imm, regidx.Regidx rs2, regidx.Regidx rs1, 4)) pc npc₀ npc₀
      iprop(transTok cpu curTier root ∗ gprFile cpu R ∗
        (wordPointsTo (RegMap.get R rs1 + BitVec.signExtend 64 imm) 4 (DFrac.own (1 : Qp).half) old ∗
         kmapId (RegMap.get R rs1 + BitVec.signExtend 64 imm) ∗
         ⌜rsvWordOk (hlc := hlc) (GF := GF) cpu (RegMap.get R rs1 + BitVec.signExtend 64 imm) 4
           (BitVec.extractLsb' 0 32 (RegMap.get R rs2))⌝))
      iprop(transTok cpu curTier root ∗ gprFile cpu R ∗
        wordPointsTo (RegMap.get R rs1 + BitVec.signExtend 64 imm) 4 (DFrac.own (1 : Qp).half)
          (BitVec.extractLsb' 0 32 (RegMap.get R rs2))) := by
  intro Φ
  iintro ⟨HmConf, HPC, HnextPC, ⟨HT, HF, Hw, #Hcl, %hrsv⟩, HΦ⟩
  ihave Hp := wordPointsTo_phys _ 4 _ old $$ Hcl Hw
  icases pwordPointsTo_cases _ 4 _ old $$ Hp with ⟨%⟨hram, hal⟩, Hb⟩
  have e := execSpecF_sw_au (GF := GF) cpu dq c sie root hok pc npc₀ imm rs1 rs2 R
    iprop(ownCtx cpu curCtx ∗ ctxBytes curCtx (RegMap.get R rs1 + BitVec.signExtend 64 imm) 4
      (DFrac.own (1 : Qp).half) (BitVec.extractLsb' 0 32 (RegMap.get R rs2))) hram hal
  iapply (e Φ)
  iframe HmConf HPC HnextPC HT HF Hcl
  isplitl [Hb]
  · iapply ctxBytes_writeAURsv cpu _ 4 old _ hrsv $$ Hb
  · inext
    iintro HmConf HPC HnextPC ⟨Htrans, Hfrag, HF, Hctx, Hb⟩
    ihave Htok := ctxTok_introB cpu curCtx none false $$ [Hctx Hfrag]
    · iframe
    ihave HT := transTok_intro cpu curTier root $$ [Htrans Htok]
    · iframe
    iapply HΦ $$ HmConf HPC HnextPC
    iframe HT HF
    iapply wordPointsTo_intro_id _ 4 _ _ hram hal $$ Hcl Hb

set_option maxHeartbeats 4000000 in
/-- **`sd rs2, imm(rs1)` into a reserved word.** -/
theorem execSpecF_sd_rsv [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (root : BitVec 44) (hok : SConfAt (GF := GF) curTier c root sie)
    (pc npc₀ : BitVec 64) (imm : BitVec 12) (rs1 rs2 : BitVec 5) (R : RegMap) (old : BitVec 64) :
    execSpecPP (GF := GF) cpu dq Privilege.Supervisor c Privilege.Supervisor c
      (instruction.STORE (imm, regidx.Regidx rs2, regidx.Regidx rs1, 8)) pc npc₀ npc₀
      iprop(transTok cpu curTier root ∗ gprFile cpu R ∗
        (wordPointsTo (RegMap.get R rs1 + BitVec.signExtend 64 imm) 8 (DFrac.own (1 : Qp).half) old ∗
         kmapId (RegMap.get R rs1 + BitVec.signExtend 64 imm) ∗
         ⌜rsvWordOk (hlc := hlc) (GF := GF) cpu (RegMap.get R rs1 + BitVec.signExtend 64 imm) 8
           (RegMap.get R rs2)⌝))
      iprop(transTok cpu curTier root ∗ gprFile cpu R ∗
        wordPointsTo (RegMap.get R rs1 + BitVec.signExtend 64 imm) 8 (DFrac.own (1 : Qp).half)
          (RegMap.get R rs2)) := by
  intro Φ
  iintro ⟨HmConf, HPC, HnextPC, ⟨HT, HF, Hw, #Hcl, %hrsv⟩, HΦ⟩
  ihave Hp := wordPointsTo_phys _ 8 _ old $$ Hcl Hw
  icases pwordPointsTo_cases _ 8 _ old $$ Hp with ⟨%⟨hram, hal⟩, Hb⟩
  have e := execSpecF_sd_au (GF := GF) cpu dq c sie root hok pc npc₀ imm rs1 rs2 R
    iprop(ownCtx cpu curCtx ∗ ctxBytes curCtx (RegMap.get R rs1 + BitVec.signExtend 64 imm) 8
      (DFrac.own (1 : Qp).half) (RegMap.get R rs2)) hram hal
  iapply (e Φ)
  iframe HmConf HPC HnextPC HT HF Hcl
  isplitl [Hb]
  · iapply ctxBytes_writeAURsv cpu _ 8 old _ hrsv $$ Hb
  · inext
    iintro HmConf HPC HnextPC ⟨Htrans, Hfrag, HF, Hctx, Hb⟩
    ihave Htok := ctxTok_introB cpu curCtx none false $$ [Hctx Hfrag]
    · iframe
    ihave HT := transTok_intro cpu curTier root $$ [Htrans Htok]
    · iframe
    iapply HΦ $$ HmConf HPC HnextPC
    iframe HT HF
    iapply wordPointsTo_intro_id _ 8 _ _ hram hal $$ Hcl Hb

end MachCSL
