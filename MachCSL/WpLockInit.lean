/-
MachCSL: a lock's raw words before `initlock`, and `initlock`'s stores into
a RESERVED lock (W8-β′).

A static (reserved, `lkRsvIn`) lock's two words are never owned: the state
interpretation keeps half of every byte from power-on, the client the other
half (`wordCellH`, over the image's tails).  So the words a lock is made
from (`lkRaw`) are, by the address, either the ordinary owned words (a
dynamic lock: `initlock`'s mint stores, `MachCSL.WpSmodeMint`) or the half
cells (`lkFreshR`: every entry since power-on a hart's zero), and
`initlock`'s two zero stores into a reserved lock are the dedicated rules
below (`wp_s_sw_zero_lkInitR`, `wp_s_sd_zero_lkInitR`): the reserved
accessor (`writeAURsv`), lending the other word as companion, with the
region discipline's obligation (`lkRsv_storeOkW`/`lkRsv_storeOkC`) -- a zero
written while the lock is free keeps it free.
-/
import MachCSL.WpSmodeMint
import MachCSL.KCtxMove

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std Std
open LeanRV64D

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
variable [KernelGeom] {lent : Bool}

/-! ## The pure facts of a fresh reserved lock -/

theorem lkZero_disc {W : WordHist 4} {W' : WordHist 8} (hW : lkZeroW W) (hW' : lkZeroW W') :
    lockWordAt none 0 W ∧ lkCpuAt none W' ∧ lockRsvW none W W' := by
  refine ⟨?_, ⟨fun e he => Or.inl (hW' e he).2.2, fun c _ e hl => ?_, fun _ h => by cases h⟩, ?_⟩
  · show curVal W 0 = 0
    cases W with
    | nil => rfl
    | cons e W => exact (hW e List.mem_cons_self).2.2
  · obtain ⟨W1, W2, hW2, _, _⟩ := hl
    exact (hW' e (by rw [hW2]; exact List.mem_append_right _ List.mem_cons_self)).2.2
  · exact ⟨fun e he => ⟨(hW e he).1, (hW e he).2.1, Or.inl (hW e he).2.2⟩,
      fun e he => ⟨(hW' e he).1, (hW' e he).2.1⟩, lkFold_zeros (fun e he => (hW e he).2.2)⟩

theorem lkZeroW_cons {n : Nat} {W : WordHist n} (hW : lkZeroW W) {t : Nat} (ht : t ≠ 0) (c : CPU) :
    lkZeroW (⟨t, hartAgent c, 0⟩ :: W) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨ht, c.isLt, rfl⟩
  · exact hW e he

theorem lkZeroW_nil {n : Nat} : lkZeroW ([] : WordHist n) := fun _ h => by cases h

/-! ## The raw words -/

/-- A RESERVED lock's fresh half cells, with the address facts. -/
def lkInitR [CurCtx] (lk : BitVec 64) : IProp GF := iprop%
  ⌜lockAddrOk lk ∧ lkRsvIn (hlc := hlc) (GF := GF) lk⌝ ∗ lkFreshR lk

/-- **A lock's two raw words** (`locked`, `cpu`) as `initlock` finds them: the
owned words at a dynamic lock, the half cells (`lkInitR`) at a reserved one. -/
def lkRaw [CurCtx] (lk : BitVec 64) (vlock : BitVec 32) (vcpu : BitVec 64) : IProp GF :=
  if lkRsvIn (hlc := hlc) (GF := GF) lk then lkInitR lk
  else iprop(wordPointsTo lk 4 (DFrac.own 1) vlock ∗ wordPointsTo (lk + 16#64) 8 (DFrac.own 1) vcpu)

theorem lkRaw_dyn [CurCtx] {lk : BitVec 64} {vlock : BitVec 32} {vcpu : BitVec 64}
    (hm : ¬ lkRsvIn (hlc := hlc) (GF := GF) lk) :
    lkRaw (GF := GF) lk vlock vcpu =
      iprop(wordPointsTo lk 4 (DFrac.own 1) vlock ∗ wordPointsTo (lk + 16#64) 8 (DFrac.own 1) vcpu) := by
  unfold lkRaw; rw [if_neg hm]

theorem lkRaw_rsv [CurCtx] {lk : BitVec 64} {vlock : BitVec 32} {vcpu : BitVec 64}
    (hm : lkRsvIn (hlc := hlc) (GF := GF) lk) :
    lkRaw (GF := GF) lk vlock vcpu = lkInitR lk := by
  unfold lkRaw; rw [if_pos hm]

theorem lkRaw_intro [CurCtx] (lk : BitVec 64) (vlock : BitVec 32) (vcpu : BitVec 64)
    (hm : ¬ lkRsvIn (hlc := hlc) (GF := GF) lk) :
    wordPointsTo (GF := GF) lk 4 (DFrac.own 1) vlock ∗ wordPointsTo (lk + 16#64) 8 (DFrac.own 1) vcpu ⊢
      lkRaw lk vlock vcpu := by
  rw [lkRaw_dyn hm]

/-- A reserved lock's half cells at the image (no entry yet). -/
theorem lkRaw_introR [CurCtx] (lk : BitVec 64) (vlock : BitVec 32) (vcpu : BitVec 64)
    (hok : lockAddrOk lk) (hm : lkRsvIn (hlc := hlc) (GF := GF) lk) :
    wordCellH (GF := GF) lk 4 [] ∗ wordCellH (lk + 16#64) 8 [] ⊢ lkRaw lk vlock vcpu := by
  rw [lkRaw_rsv hm]
  unfold lkInitR lkFreshR
  iintro ⟨Hw, Hc⟩
  isplitr
  · ipureintro; exact ⟨hok, hm⟩
  iexists [], []
  iframe Hw Hc
  isplit
  · ipureintro; exact ⟨lkZeroW_nil, lkZeroW_nil⟩
  · unfold lkHeadKey; ileft; ipureintro; rfl

/-- What `initlock` leaves at a reserved lock is fresh. -/
theorem lkFresh_of_initR [CurCtx] (lk : BitVec 64) : lkInitR (GF := GF) lk ⊢ lkFresh lk := by
  unfold lkInitR
  iintro ⟨%h, Hf⟩
  iapply lkFresh_introR lk h.1 h.2 $$ Hf

/-! ## `initlock`'s zero stores into a reserved lock -/

set_option maxHeartbeats 4000000 in
/-- `sw x0, imm(rs1)` into a RESERVED lock's word (`initlock`'s
`lk->locked = 0`): the half cells stay fresh. -/
theorem wp_s_sw_zero_lkInitR [CurCtx] [KernelImage GF] (cpu : CPU) (k : KCtx)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 : BitVec 5) (hrs1 : rs1 ≠ 4#5)
    (lk : BitVec 64) (hok : lockAddrOk lk) (hm : lkRsvIn (hlc := hlc) (GF := GF) lk)
    (haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = lk) :
    instr (GF := GF) pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) ∗
    kctxL lent cpu k ∗ pcIs cpu pc ∗ kmapId lk ∗ lkFreshR lk ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctxL lent cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗ lkFreshR lk -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, #Hcl, Hf, HΦ⟩
  have hexec : ∀ (cpu' : CPU) (c : MConf), (k.sie = false ∨ k.proc = 0#64 → cpu' = cpu) →
      SConfAt (GF := GF) curTier c k.root k.sie → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu' (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c
        (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) pc (pc + instrLen is_rvc)
        (pc + instrLen is_rvc)
        iprop(transTok cpu' curTier k.root ∗ gprFile cpu' (tpPin cpu' k.regs) ∗ (kmapId lk ∗ lkFreshR lk))
        iprop(transTok cpu' curTier k.root ∗ gprFile cpu' (tpPin cpu' k.regs) ∗ lkFreshR lk) := by
    intro cpu' c hpin hok' hmenv Φ
    iintro ⟨HmConf, HPC, HnextPC, ⟨HT, HF, #Hcl, Hf⟩, HΦ⟩
    have haddr' : RegMap.get (tpPin cpu' k.regs) rs1 + BitVec.signExtend 64 imm = lk := by
      rw [KCtx.rget_hart cpu cpu' k rs1 hrs1]; exact haddr
    have hram : inRam (RegMap.get (tpPin cpu' k.regs) rs1 + BitVec.signExtend 64 imm) 4 := by
      rw [haddr']; exact hok.1
    have hal : (RegMap.get (tpPin cpu' k.regs) rs1 + BitVec.signExtend 64 imm).toNat % 4 = 0 := by
      rw [haddr']; exact hok.2.1
    have e := execSpecF_sw_au (GF := GF) cpu' (DFrac.own 1) c k.sie k.root hok' pc (pc + instrLen is_rvc)
      imm rs1 0#5 (tpPin cpu' k.regs) iprop(ownCtx cpu' curCtx ∗ lkFreshR lk) hram hal
    have hz : BitVec.extractLsb' 0 32 (RegMap.get (tpPin cpu' k.regs) 0#5) = 0#32 := by
      rw [RegMap.get_zero]; rfl
    rw [haddr', hz] at e
    iapply (e Φ)
    iframe HmConf HPC HnextPC HT HF Hcl
    isplitl [Hf]
    · iintro Hctx
      unfold lkFreshR
      icases Hf with ⟨%W, %W', Hw, Hc, %⟨hW, hW'⟩, #Hkey⟩
      icases wordCellH_cases lk 4 W $$ Hw with ⟨%Hold, Hb, %htail⟩
      icases wordCellH_cases (lk + 16#64) 8 W' $$ Hc with ⟨%HoldW, HbW, %htailW⟩
      iapply writeAU_of_rsv
      unfold writeAURsv
      iapply fupd_mask_intro LawfulSet.empty_subset
      iintro Hmask
      iexists W.hist Hold, [(lk + 16#64, 8, W'.hist HoldW)], none
      iframe Hb
      isplitl [HbW]
      · unfold compBytes; iapply BigSepL.bigSepL_singleton.2; iexact HbW
      isplitr
      · ipureintro
        exact lkRsv_storeOkW hm cpu' _ W W' Hold HoldW htail htailW (fun t ht => ⟨none, 0,
          lkZero_disc (lkZeroW_cons (t := t) hW (Nat.pos_iff_ne_zero.mp ht) cpu') hW'⟩)
      isplitr
      · unfold rsvPcCell; iempintro
      isplitr
      · ipureintro
        exact lkRsv_relFreeZ hm _ W Hold (fun e he => (hW e he).2.2) htail
      inext
      iintro %t %ht Hb HbW _ #Hau #Htop
      unfold compBytes
      ihave HbW := BigSepL.bigSepL_singleton.1 $$ HbW
      ihave Hc := wordCellH_intro (lk + 16#64) 8 W' HoldW htailW $$ HbW
      ihave Hw := wordCellH_push lk 4 W Hold htail t (hartAgent cpu') 0#32 $$ Hb
      imod ctx_key_mint cpu' curCtx t $$ [Hctx] with ⟨Hctx, #Hk⟩
      · iframe Hctx Hau Htop
      imod Hmask
      imodintro
      iframe Hctx
      iexists (⟨t, hartAgent cpu', 0#32⟩ :: W), W'
      iframe Hw Hc
      isplit
      · ipureintro; exact ⟨lkZeroW_cons (t := t) hW (Nat.pos_iff_ne_zero.mp ht) cpu', hW'⟩
      · unfold lkHeadKey; iright
        iexists ⟨t, hartAgent cpu', 0#32⟩, W
        isplit
        · ipureintro; rfl
        · unfold lkFloor; iexact Hk
    · inext
      iintro HmConf HPC HnextPC ⟨Htrans, Hfrag, HF, Hctx, Hf⟩
      ihave Htok := ctxTok_introB cpu' curCtx none false $$ [Hctx Hfrag]
      case' _ => iframe
      ihave HT := transTok_intro cpu' curTier k.root $$ [Htrans Htok]
      case' _ => iframe
      iapply HΦ $$ HmConf HPC HnextPC
      iframe HT HF Hf
  iapply (wpLoop_k_keep_mem cpu k pc (fun _ => pc + instrLen is_rvc) is_rvc _
    iprop(kmapId lk ∗ lkFreshR lk) (fun _ => lkFreshR (GF := GF) lk) hexec)
  iframe HI Hk Hpc Hcl Hf HΦ

set_option maxHeartbeats 4000000 in
/-- `sd x0, imm(rs1)` into a RESERVED lock's owner word (`initlock`'s
`lk->cpu = 0`): the half cells stay fresh. -/
theorem wp_s_sd_zero_lkInitR [CurCtx] [KernelImage GF] (cpu : CPU) (k : KCtx)
    (pc : BitVec 64) (is_rvc : Bool) (imm : BitVec 12) (rs1 : BitVec 5) (hrs1 : rs1 ≠ 4#5)
    (lk : BitVec 64) (hok : lockAddrOk lk) (hm : lkRsvIn (hlc := hlc) (GF := GF) lk)
    (haddr : k.rget cpu rs1 + BitVec.signExtend 64 imm = lk + 16#64) :
    instr (GF := GF) pc is_rvc (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 8)) ∗
    kctxL lent cpu k ∗ pcIs cpu pc ∗ kmapId (lk + 16#64) ∗ lkFreshR lk ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctxL lent cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗ lkFreshR lk -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, #Hcl, Hf, HΦ⟩
  have hexec : ∀ (cpu' : CPU) (c : MConf), (k.sie = false ∨ k.proc = 0#64 → cpu' = cpu) →
      SConfAt (GF := GF) curTier c k.root k.sie → c.menvcfg = menvcfgS →
      execSpecPP (GF := GF) cpu' (DFrac.own 1) Privilege.Supervisor c Privilege.Supervisor c
        (instruction.STORE (imm, regidx.Regidx 0#5, regidx.Regidx rs1, 8)) pc (pc + instrLen is_rvc)
        (pc + instrLen is_rvc)
        iprop(transTok cpu' curTier k.root ∗ gprFile cpu' (tpPin cpu' k.regs) ∗ (kmapId (lk + 16#64) ∗ lkFreshR lk))
        iprop(transTok cpu' curTier k.root ∗ gprFile cpu' (tpPin cpu' k.regs) ∗ lkFreshR lk) := by
    intro cpu' c hpin hok' hmenv Φ
    iintro ⟨HmConf, HPC, HnextPC, ⟨HT, HF, #Hcl, Hf⟩, HΦ⟩
    have haddr' : RegMap.get (tpPin cpu' k.regs) rs1 + BitVec.signExtend 64 imm = lk + 16#64 := by
      rw [KCtx.rget_hart cpu cpu' k rs1 hrs1]; exact haddr
    have hram : inRam (RegMap.get (tpPin cpu' k.regs) rs1 + BitVec.signExtend 64 imm) 8 := by
      rw [haddr']; exact hok.2.2.1
    have hal : (RegMap.get (tpPin cpu' k.regs) rs1 + BitVec.signExtend 64 imm).toNat % 8 = 0 := by
      rw [haddr']; exact hok.2.2.2
    have e := execSpecF_sd_au (GF := GF) cpu' (DFrac.own 1) c k.sie k.root hok' pc (pc + instrLen is_rvc)
      imm rs1 0#5 (tpPin cpu' k.regs) iprop(ownCtx cpu' curCtx ∗ lkFreshR lk) hram hal
    rw [haddr', RegMap.get_zero] at e
    iapply (e Φ)
    iframe HmConf HPC HnextPC HT HF Hcl
    isplitl [Hf]
    · iintro Hctx
      unfold lkFreshR
      icases Hf with ⟨%W, %W', Hw, Hc, %⟨hW, hW'⟩, #Hkey⟩
      icases wordCellH_cases lk 4 W $$ Hw with ⟨%HoldW, HbW, %htailW⟩
      icases wordCellH_cases (lk + 16#64) 8 W' $$ Hc with ⟨%Hold, Hb, %htail⟩
      iapply writeAU_of_rsv
      unfold writeAURsv
      iapply fupd_mask_intro LawfulSet.empty_subset
      iintro Hmask
      iexists W'.hist Hold, [(lk, 4, W.hist HoldW)], none
      iframe Hb
      isplitl [HbW]
      · unfold compBytes; iapply BigSepL.bigSepL_singleton.2; iexact HbW
      isplitr
      · ipureintro
        exact lkRsv_storeOkC hm cpu' _ W W' HoldW Hold htailW htail (fun t ht => ⟨none, 0,
          lkZero_disc hW (lkZeroW_cons (t := t) hW' (Nat.pos_iff_ne_zero.mp ht) cpu')⟩)
      isplitr
      · unfold rsvPcCell; iempintro
      isplitr
      · ipureintro
        exact lkRsv_relFreeC hm _ _
      inext
      iintro %t %ht Hb HbW _ _ _
      unfold compBytes
      ihave HbW := BigSepL.bigSepL_singleton.1 $$ HbW
      ihave Hw := wordCellH_intro lk 4 W HoldW htailW $$ HbW
      ihave Hc := wordCellH_push (lk + 16#64) 8 W' Hold htail t (hartAgent cpu') 0#64 $$ Hb
      imod Hmask
      imodintro
      iframe Hctx
      iexists W, (⟨t, hartAgent cpu', 0#64⟩ :: W')
      iframe Hw Hc Hkey
      ipureintro; exact ⟨hW, lkZeroW_cons (t := t) hW' (Nat.pos_iff_ne_zero.mp ht) cpu'⟩
    · inext
      iintro HmConf HPC HnextPC ⟨Htrans, Hfrag, HF, Hctx, Hf⟩
      ihave Htok := ctxTok_introB cpu' curCtx none false $$ [Hctx Hfrag]
      case' _ => iframe
      ihave HT := transTok_intro cpu' curTier k.root $$ [Htrans Htok]
      case' _ => iframe
      iapply HΦ $$ HmConf HPC HnextPC
      iframe HT HF Hf
  iapply (wpLoop_k_keep_mem cpu k pc (fun _ => pc + instrLen is_rvc) is_rvc _
    iprop(kmapId (lk + 16#64) ∗ lkFreshR lk) (fun _ => lkFreshR (GF := GF) lk) hexec)
  iframe HI Hk Hpc Hcl Hf HΦ

/-- `initlock`'s `sw zero,0(a0)` at a reserved lock. -/
theorem wp_s_sw_zero_lkInit0 [CurCtx] [KernelImage GF] (cpu : CPU) (k : KCtx)
    (pc : BitVec 64) (is_rvc : Bool) (rs1 : BitVec 5) (hrs1 : rs1 ≠ 4#5) :
    instr (GF := GF) pc is_rvc (instruction.STORE (0#12, regidx.Regidx 0#5, regidx.Regidx rs1, 4)) ∗
    kctxL lent cpu k ∗ pcIs cpu pc ∗ kmapId (k.rget cpu rs1) ∗ lkInitR (k.rget cpu rs1) ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctxL lent cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗ lkInitR (k.rget cpu rs1) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, #Hcl, Hf, HΦ⟩
  unfold lkInitR
  icases Hf with ⟨%h, Hf⟩
  have haddr : k.rget cpu rs1 + BitVec.signExtend 64 (0#12) = k.rget cpu rs1 := by
    rw [show BitVec.signExtend 64 (0#12) = 0#64 from by decide]; simp
  iapply (wp_s_sw_zero_lkInitR cpu k pc is_rvc 0#12 rs1 hrs1 _ h.1 h.2 haddr)
  iframe HI Hk Hpc Hcl Hf
  inext
  iapply wpNext_mono _ _ _ _ _ $$ HΦ
  iintro %cpu' HK Hk Hpc Hf
  iapply HK $$ Hk Hpc
  iframe Hf
  ipureintro; exact h

/-- `initlock`'s `sd zero,16(a0)` at a reserved lock. -/
theorem wp_s_sd_zero_lkInit16 [CurCtx] [KernelImage GF] (cpu : CPU) (k : KCtx)
    (pc : BitVec 64) (is_rvc : Bool) (rs1 : BitVec 5) (hrs1 : rs1 ≠ 4#5) :
    instr (GF := GF) pc is_rvc (instruction.STORE (16#12, regidx.Regidx 0#5, regidx.Regidx rs1, 8)) ∗
    kctxL lent cpu k ∗ pcIs cpu pc ∗ kmapId (k.rget cpu rs1 + 16#64) ∗ lkInitR (k.rget cpu rs1) ∗
    ▷ wpNext k.sie k.proc cpu (fun cpu' =>
        iprop(kctxL lent cpu' k -∗ pcIs cpu' (pc + instrLen is_rvc) -∗ lkInitR (k.rget cpu rs1) -∗ wpLoop cpu'))
    ⊢ wpLoop cpu := by
  iintro ⟨HI, Hk, Hpc, #Hcl, Hf, HΦ⟩
  unfold lkInitR
  icases Hf with ⟨%h, Hf⟩
  have haddr : k.rget cpu rs1 + BitVec.signExtend 64 (16#12) = k.rget cpu rs1 + 16#64 := by
    rw [show BitVec.signExtend 64 (16#12) = 16#64 from by decide]
  iapply (wp_s_sd_zero_lkInitR cpu k pc is_rvc 16#12 rs1 hrs1 _ h.1 h.2 haddr)
  iframe HI Hk Hpc Hcl Hf
  inext
  iapply wpNext_mono _ _ _ _ _ $$ HΦ
  iintro %cpu' HK Hk Hpc Hf
  iapply HK $$ Hk Hpc
  iframe Hf
  ipureintro; exact h

/-! ## The raw words as a function of the context -/

/-- The fresh head's key transports between contexts (D10 (d'')). -/
instance instCtxMorphLkHeadKey (tier : KTier) (W : WordHist 4) :
    CtxMorph (GF := GF) (fun ξ => @lkHeadKey hlc GF _ ⟨ξ, tier⟩ W) where
  morph ξ ξ' := by
    unfold lkHeadKey
    iintro ⟨Hd, (%h | ⟨%e, %W2, %h, #H⟩)⟩
    · imodintro
      iframe Hd
      ileft; ipureintro; exact h
    · imod (instCtxMorphLkFloor (GF := GF) e.t).morph ξ ξ' $$ [Hd H] with ⟨Hd, #H'⟩
      · iframe Hd; iexact H
      imodintro
      iframe Hd
      iright
      iexists e, W2
      iframe H'
      ipureintro; exact h

/-- A reserved lock's fresh half cells transport (their head's key does). -/
instance instCtxMorphLkInitR (tier : KTier) (lk : BitVec 64) :
    CtxMorph (GF := GF) (fun ξ => @lkInitR hlc GF _ _ ⟨ξ, tier⟩ lk) where
  morph ξ ξ' := by
    unfold lkInitR lkFreshR
    iintro ⟨Hd, %ha, %W, %W', Hw, Hc, %hz, Hk⟩
    imod (instCtxMorphLkHeadKey (GF := GF) tier W).morph ξ ξ' $$ [Hd Hk] with ⟨Hd, Hk⟩
    · iframe Hd Hk
    imodintro
    iframe Hd
    isplitr
    · ipureintro; exact ha
    iexists W, W'
    iframe Hw Hc Hk
    ipureintro; exact hz


/-- A lock's raw words at a fixed tier: the owned words (a dynamic lock) or
the context-free half cells (a reserved one). -/
instance instCtxMorphLkRaw (tier : KTier) (lk : BitVec 64) (vlock : BitVec 32) (vcpu : BitVec 64) :
    CtxMorph (GF := GF) (fun ξ => @lkRaw hlc GF _ _ ⟨ξ, tier⟩ lk vlock vcpu) := by
  by_cases hm : lkRsvIn (hlc := hlc) (GF := GF) lk
  · have e : (fun ξ => @lkRaw hlc GF _ _ ⟨ξ, tier⟩ lk vlock vcpu) = fun ξ => @lkInitR hlc GF _ _ ⟨ξ, tier⟩ lk :=
      funext fun ξ => @lkRaw_rsv hlc GF _ _ ⟨ξ, tier⟩ lk vlock vcpu hm
    rw [e]
    exact instCtxMorphLkInitR tier lk
  · have e : (fun ξ => @lkRaw hlc GF _ _ ⟨ξ, tier⟩ lk vlock vcpu) = fun ξ =>
        iprop(@wordPointsTo hlc GF _ ⟨ξ, tier⟩ lk 4 (DFrac.own 1) vlock ∗
          @wordPointsTo hlc GF _ ⟨ξ, tier⟩ (lk + 16#64) 8 (DFrac.own 1) vcpu) :=
      funext fun ξ => @lkRaw_dyn hlc GF _ _ ⟨ξ, tier⟩ lk vlock vcpu hm
    rw [e]
    exact @instCtxMorphSep hlc GF _ _ _ (instCtxMorphWordAt _ _ _ _ _) (instCtxMorphWordAt _ _ _ _ _)

end MachCSL
