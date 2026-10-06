/-
Weak: **the PTE A/D WRITE-BACK cone at `execEff`** (M4 batch 6a, update): the
walker's atomic A/D compare-and-swap -- the exclusive PTE read, the conditional PTE
write, `update_and_write_pte`'s outcome arms, the TLB fill/refresh, the three
write-back translate heads, the `translateAddr` composition, and the certificates
for the CAS pair -- every statement with its EXACT trace.

Rocq: `iris/WeakUpdEff.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The mirror of the S-mode translation UPDATE path at
the instrumented interpreter `WeakCert.execEff` (SC originals: `SmodePte`'s
exclusive PTE read, `PtTree`'s exclusive slot read, `PtTreeAdue` §§1-4; Lean SC
twins `Weak/ExecSC4.execReadPteExclusiveS`, `Weak/ExecSC8.execWritePteConditionalRam`).
`Weak/WeakWalkEff.lean` is the READ cone this file extends (its `wpte*` predicates,
walks, dispatchers and front heads are consumed as-is).  The model's update path:
`update_PTE_Bits stale = none` ⇒ no events at all (O-UNCHANGED); otherwise (Svadu,
`menvcfg.ADUE = 1`) the exclusive read, the re-check `check_leaf_pte` on the fresh
word, then either nothing more (O-FRESH, read only -- reachable only on the TLB-hit
path) or the conditional write (O-WRITTEN, the ADJACENT pair).  The three `Err`
funnels are result-generic composers whose failing step is a premise.
THE TRACE: `read_pte_exclusive` reads with `Read_RISCV_reserved` (`AK_explicit
{AV_exclusive, AS_normal}`), `write_pte_conditional` writes with
`Write_RISCV_conditional` (same kind); both classify `⟨false, true, false⟩` (latest,
not synchronising; Rocq's `AkInfo false true false` literally, also in Lean -- unlike
the plain walk reads, which are `wakPlain` under O2).  The O-WRITTEN trace is
`[.WEread ⟨false, true, false⟩ a 8, .WEwrite ⟨false, true, false⟩ a 8 w']`, which §9
certifies as a width-8 STORE (`wQStoreW 8`): the read is pinned by kind, not
`akSync`, so there is no acquire gain to certify (`WeakEff.wcertNowrite` covers the
quiet outcomes).

**Deviations from Rocq.**
1. VOCABULARY as `Weak/WeakWalkEff.lean` deviation 1 (`register_lookup r s.(sregs)` ↦
   `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`, `uint` ↦ `toNat`, `Z` ↦ `Nat`,
   `tt` ↦ `()`, `mword_of_int 0` ↦ `0#16`, `autocast (PPN_of_PTE p)` ↦ `ppn0 p`,
   `set_reg s tlb v` ↦ `s.setReg .tlb v`, the byte window ↦ `BytesAt s a 8 w`), plus
   `MState s.(sregs) (write_bytes s.(mem) a 8 v) s.(mdev)` ↦
   `s.setMem (bmWrite s.mem a 8 v)`, `AkInfo false true false` ↦ `⟨false, true, false⟩`,
   `Arch.pa` ↦ `PAddr`, `register_lookup menvcfg … = menvcfg0` ↦ `s.regs .menvcfg =
   menvcfg0`; Rocq's `(es2 ++ es1 ++ es0) ++ es_x ++ es_w` is
   `(es2 ++ (es1 ++ es0)) ++ (es_x ++ es_w)`.  Section variables/hypotheses
   (`UpdArmsEff`, `PtUpdEff`, `PtUpdFrontEff`) are theorem arguments.
2. §5: the Lean model's Svadu/ADUE gate has an extra `else` arm (`not Svadu → not
   Svade`), dead under the same premises; the `Local Ltac uawp_gate` has no twin: the
   scripts use `exec_eff_run` with `WeakWalkEff.execEffCurrentlyEnabledSvadu`.
3. §3/§4 slot facts as `WeakWalkEff` deviation 6: Rocq's `addr_is_ram a ∧
   addr_is_ram (pa_add a 7)` ↦ `inRam a 8`, `ram_base + ram_size ≤ uint pmpaddr0 * 4`
   ↦ `ramEnd ≤ … .toNat * 4`; the CLINT/SIG/dev side conditions come from `inRam`.
4. The pure `PtTreeAdue`/`PtTree`/`PtAdBits` facts the heads use: `pt_fill_ent_uwe` ↦
   the Lean-only `WeakUpdEff.ptFillEntUwe`, `tlb_set_pte_uwe` ↦ `WeakUpdEff.tlbSetPteUwe`
   (not in the Lean tree; file-qualified twins over `ExecSC6.ptFillEnt`/`ExecSC9.uWalkEntry`),
   `update_PTE_Bits_set_ad` ↦ `PtAdBits.updatePTEBitsSetAd` (WeakVariant),
   `pte_set_ad_absorb` ↦ `MachCSL.pteSetAD_pteSetAD`, `uwe_pte`/`uwe_ppn` ↦
   `tlbGetPteUwe`/`tlbGetPpnUwe` (ExecSC9).  The Lean hit path reads the entry's level
   (`tlb_get_level 39 ent`): Lean-only `WeakUpdEff.tlbGetLevelUwe` (it is 0).
5. §8: the `translateAddr` premises are `WeakWalkEff.execEffTranslateAddrPtFront`'s
   (`WeakWalkEff` deviation 7).
6. `exec_eff_write_ram_cond_8` is the width-8 instance of `WeakLeafAmo4`'s
   `execEffWriteRamCond`; the conditional write's MMIO window is
   `WeakLeafAmo4.execEffWithinMmioWritableFalse`.
7. Rocq's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_read_ram_resv_8` `execEffReadRamResv8`,
`exec_eff_write_ram_cond_8` `execEffWriteRamCond8`, `exec_eff_is_mag_applicable_store_pte`
`execEffIsMagApplicableStorePte`, `exec_eff_pmaCheck_ram_wpte` `execEffPmaCheckRamWpte`,
`exec_eff_pmpCheck_supervisor_grant_wpte` `execEffPmpCheckSupervisorGrantWpte`,
`exec_eff_read_pte_exclusive_S` `execEffReadPteExclusiveS`, `wpt_read_pte_exclusive_slot`
`wptReadPteExclusiveSlot`, `exec_eff_write_pte_conditional_ram`
`execEffWritePteConditionalRam`, `exec_eff_update_and_write_pte_none`
`execEffUpdateAndWritePteNone`, `exec_eff_update_and_write_pte_fresh`
`execEffUpdateAndWritePteFresh`, `exec_eff_update_and_write_pte_written`
`execEffUpdateAndWritePteWritten`, `exec_eff_update_and_write_pte_read_err`
`execEffUpdateAndWritePteReadErr`, `exec_eff_update_and_write_pte_recheck_err`
`execEffUpdateAndWritePteRecheckErr`, `exec_eff_update_and_write_pte_write_err`
`execEffUpdateAndWritePteWriteErr`, `exec_eff_add_to_TLB_pt` `execEffAddToTLBPt`,
`exec_eff_write_TLB` `execEffWriteTLB`, `exec_eff_translate_TLB_miss_user_upd`
`execEffTranslateTLBMissUserUpd`, `exec_eff_translate_TLB_hit_pt_upd`
`execEffTranslateTLBHitPtUpd`, `exec_eff_translate_TLB_hit_pt_refresh`
`execEffTranslateTLBHitPtRefresh`, `exec_eff_translateAddr_pt_miss_upd`
`execEffTranslateAddrPtMissUpd`, `wcert_ptw_upd_gen` `wcertPtwUpdGen`,
`wcert_ptw_upd_pin` `wcertPtwUpdPin`.  Lean-only (file-qualified):
`WeakUpdEff.uGbitSetAd`, `WeakUpdEff.ptFillEntUwe`, `WeakUpdEff.tlbSetPteUwe`,
`WeakUpdEff.tlbGetLevelUwe`.

**Dropped:** nothing -- 22 Rocq `Lemma`s, all ported (22 Lean declarations, plus the 4
Lean-only ones); the `Local Ltac uawp_gate` is replaced by `exec_eff_run` (deviation 2).
-/
import Weak.WeakWalkEff
import Weak.WeakLeafAmo4

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The two exclusive-kind RAM steps at width 8 -/

/-- Rocq `exec_eff_read_ram_resv_8`: the reserved read emits
`WEread ⟨false, true, false⟩` -- not an ifetch, latest, not synchronising. -/
theorem execEffReadRamResv8 (addr w : BitVec 64) (s : ExecSt) (hdev : devAddr addr = false)
    (hb : BytesAt s addr 8 w) :
    execEff (read_ram .Read_RISCV_reserved (.Physaddr addr) 8 false) s =
      some ((w, default_meta), s, [.WEread ⟨false, true, false⟩ addr 8]) := by
  have hr : bmRead s.mem addr 8 = some w := bmRead_of_bytes _ _ _ _ hb
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  unfold read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read
  exec_eff_run [hm, hr]
  rfl

/-- Rocq `exec_eff_write_ram_cond_8` (the width-8 instance of
`WeakLeafAmo4.execEffWriteRamCond`). -/
theorem execEffWriteRamCond8 (addr data : BitVec 64) (s : ExecSt) (hdev : devAddr addr = false) :
    execEff (write_ram .Write_RISCV_conditional (.Physaddr addr) 8 data ()) s =
      some (true, s.setMem (bmWrite s.mem addr 8 data), [.WEwrite ⟨false, true, false⟩ addr 8 data]) :=
  execEffWriteRamCond addr 8 data s hdev

/-! ## 2. The PTE-STORE gates -/

/-- Rocq `exec_eff_is_mag_applicable_store_pte`. -/
theorem execEffIsMagApplicableStorePte (width : Nat) (s : ExecSt) :
    execEff (is_mag_applicable_access (.Store .PageTableEntry) width) s = some (false, s, []) := rfl

/-- Rocq `exec_eff_pmaCheck_ram_wpte` (`res_or_con`-generic). -/
theorem execEffPmaCheckRamWpte (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (roc : Bool) (s : ExecSt)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).supports_pte_write = true) :
    execEff (pmaCheck (.Physaddr addr) 8 (.Store .PageTableEntry) pbmt roc) s =
      some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hm hw (execEffIsMagApplicableStorePte 8 s) hal

/-- Rocq `exec_eff_pmpCheck_supervisor_grant_wpte`. -/
theorem execEffPmpCheckSupervisorGrantWpte (a : BitVec 64) (width : Nat) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match)
    (hW : (_get_Pmpcfg_ent_W (s.regs .pmpcfg_n)[0]! == 1#1) = true) :
    execEff (pmpCheck (.Physaddr a) width (.Store .PageTableEntry) .Supervisor) s = some (none, s, []) := by
  have hA' : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[(0 : Int)]!) =
      .TOR := hA
  have hm := execEffPmpMatchAddrTORMatch a (to_bits (l := 64) width) _ (s.regs .pmpaddr_n)[0]!
    (zeros (n := 64)) s hA' hlt hr
  have hrd : execEff (pmpReadAddrReg (0 : Int).toNat) s = some ((s.regs .pmpaddr_n)[0]!, s, []) :=
    execEffPmpReadAddrReg 0 s
  have hrwx : execEff (pmpCheckRWX (s.regs .pmpcfg_n)[(0 : Int)]! (.Store .PageTableEntry)) s =
      some (true, s, []) := by
    unfold pmpCheckRWX
    have hW' : (_get_Pmpcfg_ent_W (s.regs .pmpcfg_n)[(0 : Int)]! == 1#1) = true := hW
    rw [hW']; rfl
  unfold pmpCheck
  rw [execEffCatchEarlyReturn]
  have hc : (sys_pmp_count == 0) = false := by decide
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  rw [execREffBindEq, WeakWalkEff.execREffForInFirstEarly _ _ s s none [] (by decide)]
  dsimp only
  rw [if_neg (by decide)]
  rw [execREffBindNil _ _ _ _ _ (wpeExecREffReturnmFwd _ s),
    execREffLiftRSeq _ _ _ _ _ (execEffReadReg .pmpcfg_n s),
    execREffBindNil _ _ _ _ _ (wpeExecREffReturnmFwd _ s),
    execREffLiftRSeq _ _ _ _ _ hrd, execREffLiftRSeq _ _ _ _ _ hm]
  dsimp only
  rw [execREffLiftRSeq _ _ _ _ _ hrwx]
  rfl

/-! ## 3. THE EXCLUSIVE PTE READ -- the CAS's read half -/

/-- Rocq `exec_eff_read_pte_exclusive_S`. -/
theorem execEffReadPteExclusiveS (addr : BitVec 64) (region : PMA_Region) (w : BitVec 64) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hpte : (override_PMA region.attributes .PBMT_PMA).supports_pte_read = true)
    (hc : execEff (within_clint (.Physaddr addr) 8) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 8) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 8) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 8 w) :
    execEff (read_pte_exclusive (.Physaddr addr) 8) s =
      some (.Ok w, s, [.WEread ⟨false, true, false⟩ addr 8]) := by
  have hpma := execEffPmaCheckRamPte addr region true s hm hal hpte
  have hpmp := execEffPmpCheckSupervisorGrantLoad addr 8 s hA hlt hr hR
  have hmm := execEffWithinMmioReadableFalse addr 8 s hc hsig hh
  have hrr := execEffReadRamResv8 addr w s hdev hb
  have hck : execEff (checked_mem_read (.Load .PageTableEntry) .PBMT_PMA .Supervisor (.Physaddr addr) 8
      false false true false) s = some (.Ok (w, default_meta), s, [.WEread ⟨false, true, false⟩ addr 8]) := by
    unfold checked_mem_read check_pma_with_pmp_priority
    rw [execEffCatchEarlyReturn]
    exec_eff_mem [hpma]
    exec_eff_mem [hpmp, hmm, hrr, read_kind_of_flags]
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
    congr
    simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
    bv_decide
  unfold read_pte_exclusive mem_read_priv mem_read_priv_meta
  exec_eff_run [hck]
  rfl

/-- Rocq `wpt_read_pte_exclusive_slot` (`WeakWalkEff.wptReadPteSlot` with the
exclusive brick). -/
theorem wptReadPteExclusiveSlot (sg : ExecSt) (a w : BitVec 64) (region : PMA_Region)
    (hslot : WeakWalkEff.ptSlotMem sg a w)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false)
    (hR : (_get_Pmpcfg_ent_R (sg.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hcov : ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4)
    (hm : matching_pma_region (sg.regs .pma_regions) (.Physaddr a) 8 = some region)
    (hpte : (override_PMA region.attributes .PBMT_PMA).supports_pte_read = true)
    (hhtif : sg.regs .htif_tohost_base = none) :
    execEff (read_pte_exclusive (.Physaddr a) 8) sg =
      some (.Ok w, sg, [.WEread ⟨false, true, false⟩ a 8]) := by
  obtain ⟨hb, hram, hal⟩ := hslot
  have hz : (zeros (n := 64)).toNat = 0 := rfl
  have h8 : (to_bits (l := 64) 8).toNat = 8 := by decide
  have hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((sg.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match := by
    rw [hz, h8]
    exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) (by decide) (by have := hram.2; omega)
  have hc : execEff (within_clint (.Physaddr a) 8) sg = some (false, sg, []) := by
    rw [within_clint_ram a 8 hram]; rfl
  have hsig : execEff (within_sig (.Physaddr a) 8) sg = some (false, sg, []) := by
    first
    | rfl
    | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)
  exact execEffReadPteExclusiveS a region w sg hA hlt hr hR hm hal hpte hc hsig
    (execEffWithinHtifFalse a 8 sg hhtif) (devAddrRam a 8 hram) hb

/-! ## 4. THE CONDITIONAL PTE WRITE -- the CAS's write half -/

/-- Rocq `exec_eff_write_pte_conditional_ram` (deviation 3: `addr_is_ram a ∧
addr_is_ram (pa_add a 7)` ↦ `inRam a 8`). -/
theorem execEffWritePteConditionalRam (a w' : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (hram : inRam a 8) (hal : is_aligned_paddr (.Physaddr a) 8 = true)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hW : (_get_Pmpcfg_ent_W (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hcov : ramEnd ≤ (s.regs .pmpaddr_n)[0]!.toNat * 4)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr a) 8 = some region)
    (hwr : (override_PMA region.attributes .PBMT_PMA).supports_pte_write = true)
    (hhtif : s.regs .htif_tohost_base = none) :
    execEff (write_pte_conditional (.Physaddr a) 8 w') s =
      some (.Ok true, s.setMem (bmWrite s.mem a 8 w'), [.WEwrite ⟨false, true, false⟩ a 8 w']) := by
  have hz : (zeros (n := 64)).toNat = 0 := rfl
  have h8 : (to_bits (l := 64) 8).toNat = 8 := by decide
  have hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match := by
    rw [hz, h8]
    exact pmpRangeMatch_full _ _ _ _ (Nat.zero_le _) (by decide) (by have := hram.2; omega)
  have hc : execEff (within_clint (.Physaddr a) 8) s = some (false, s, []) := by
    rw [within_clint_ram a 8 hram]; rfl
  have hsig : execEff (within_sig (.Physaddr a) 8) s = some (false, s, []) := by
    first
    | rfl
    | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)
  have hh := execEffWithinHtifWFalse a 8 s hhtif
  have hdev := devAddrRam a 8 hram
  have hpma := execEffPmaCheckRamWpte a .PBMT_PMA region true s hm hal hwr
  have hpmp := execEffPmpCheckSupervisorGrantWpte a 8 s hA hlt hr hW
  have hmm := WeakLeafAmo4.execEffWithinMmioWritableFalse a 8 s hc hsig hh
  have hw : ∀ k (d : BitVec (8 * k)), execEff (write_ram .Write_RISCV_conditional (.Physaddr a) k d ()) s =
      some (true, s.setMem (bmWrite s.mem a k d), [.WEwrite ⟨false, true, false⟩ a k d]) :=
    fun k d => execEffWriteRamCond a k d s hdev
  have hck : execEff (checked_mem_write (.Physaddr a) 8 w' (.Store .PageTableEntry) .PBMT_PMA .Supervisor ()
      false false true) s =
      some (.Ok true, s.setMem (bmWrite s.mem a 8 w'), [.WEwrite ⟨false, true, false⟩ a 8 w']) := by
    unfold checked_mem_write check_pma_with_pmp_priority
    rw [execEffCatchEarlyReturn]
    amo_eff_mem [hpma]
    amo_eff_mem [hpmp, hmm, write_kind_of_flags, hw]
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
    have hd : ∀ x : BitVec 64, Sail.BitVec.extractLsb x 63 0 = x := by
      intro x; simp only [Sail.BitVec.extractLsb]; bv_decide
    simp only [hd]
  unfold write_pte_conditional mem_write_value_priv mem_write_value_priv_meta
  simp only [Nat.reduceMul, BitVec.setWidth_eq]
  exec_eff_run [hck, default_meta]

/-! ## 5. `update_and_write_pte`'s OUTCOME ARMS, level-generic -/

/-- Rocq `exec_eff_update_and_write_pte_none` (O-UNCHANGED: no events at all). -/
theorem execEffUpdateAndWritePteNone (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (a : physaddr) (stale : BitVec 64) (lvl : Nat) (s : ExecSt)
    (hnoupd : update_PTE_Bits stale acc = none) :
    execEff (update_and_write_pte 39 vpn a stale lvl acc p mxr dosum ()) s = some (.Ok (none, ()), s, []) := by
  unfold update_and_write_pte
  exec_eff_run
  erw [hnoupd]
  rfl

/-- Rocq `exec_eff_update_and_write_pte_fresh` (O-FRESH: read only). -/
theorem execEffUpdateAndWritePteFresh (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (a : BitVec 64) (stale g fresh : BitVec 64) (lvl : Nat) (ppnv : BitVec 44)
    (pb : page_based_mem_type) (menvcfg0 : BitVec 64) (es_x : List Weff) (s : ExecSt)
    (hgate : update_PTE_Bits stale acc = some g) (hmenv : s.regs .menvcfg = menvcfg0)
    (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hrdx : execEff (read_pte_exclusive (.Physaddr a) 8) s = some (.Ok fresh, s, es_x))
    (hchk : execEff (check_leaf_pte 39 vpn acc p mxr dosum fresh (.Physaddr a) lvl ()) s =
      some (.Ok (ppnv, pb, ()), s, []))
    (hupd : update_PTE_Bits fresh acc = none) :
    execEff (update_and_write_pte 39 vpn (.Physaddr a) stale lvl acc p mxr dosum ()) s =
      some (.Ok (some fresh, ()), s, es_x) := by
  unfold update_and_write_pte
  exec_eff_run
  erw [hgate]
  exec_eff_run [WeakWalkEff.execEffCurrentlyEnabledSvadu, hmenv, hadue]
  erw [hrdx]
  exec_eff_run
  erw [hchk]
  exec_eff_run
  erw [hupd]
  exec_eff_run
  show some (Result.Ok (some (BitVec.setWidth 64 fresh), ()), s, es_x) = _
  rw [BitVec.setWidth_eq]
  rfl

/-- Rocq `exec_eff_update_and_write_pte_written` (O-WRITTEN: the adjacent CAS pair). -/
theorem execEffUpdateAndWritePteWritten (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (a : BitVec 64) (stale g fresh fresh' : BitVec 64) (lvl : Nat) (ppnv : BitVec 44)
    (pb : page_based_mem_type) (menvcfg0 : BitVec 64) (es_x es_w : List Weff) (sw : ExecSt) (s : ExecSt)
    (hgate : update_PTE_Bits stale acc = some g) (hmenv : s.regs .menvcfg = menvcfg0)
    (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hrdx : execEff (read_pte_exclusive (.Physaddr a) 8) s = some (.Ok fresh, s, es_x))
    (hchk : execEff (check_leaf_pte 39 vpn acc p mxr dosum fresh (.Physaddr a) lvl ()) s =
      some (.Ok (ppnv, pb, ()), s, []))
    (hupd : update_PTE_Bits fresh acc = some fresh')
    (hwrite : execEff (write_pte_conditional (.Physaddr a) 8 fresh') s = some (.Ok true, sw, es_w)) :
    execEff (update_and_write_pte 39 vpn (.Physaddr a) stale lvl acc p mxr dosum ()) s =
      some (.Ok (some fresh', ()), sw, es_x ++ es_w) := by
  unfold update_and_write_pte
  exec_eff_run
  erw [hgate]
  exec_eff_run [WeakWalkEff.execEffCurrentlyEnabledSvadu, hmenv, hadue]
  erw [hrdx]
  exec_eff_run
  erw [hchk]
  exec_eff_run
  erw [hupd]
  exec_eff_run
  erw [hwrite]
  exec_eff_run
  show some (Result.Ok (some (BitVec.setWidth 64 fresh'), ()), sw, es_x ++ es_w) = _
  rw [BitVec.setWidth_eq]
  rfl

/-- Rocq `exec_eff_update_and_write_pte_read_err` (the exclusive read faults). -/
theorem execEffUpdateAndWritePteReadErr (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (a : physaddr) (stale g : BitVec 64) (lvl : Nat) (menvcfg0 : BitVec 64)
    (ex : physaddr × ExceptionType) (es_x : List Weff) (s s' : ExecSt)
    (hgate : update_PTE_Bits stale acc = some g) (hmenv : s.regs .menvcfg = menvcfg0)
    (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hrdx : execEff (read_pte_exclusive a 8) s = some (.Err ex, s', es_x)) :
    execEff (update_and_write_pte 39 vpn a stale lvl acc p mxr dosum ()) s =
      some (.Err (.PTW_No_Access (), ()), s', es_x) := by
  unfold update_and_write_pte
  exec_eff_run
  erw [hgate]
  exec_eff_run [WeakWalkEff.execEffCurrentlyEnabledSvadu, hmenv, hadue]
  erw [hrdx]
  exec_eff_run

/-- Rocq `exec_eff_update_and_write_pte_recheck_err` (the re-check fails on the
fresh word). -/
theorem execEffUpdateAndWritePteRecheckErr (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr dosum : Bool) (vpn : BitVec 27) (a : BitVec 64) (stale g fresh : BitVec 64) (lvl : Nat)
    (menvcfg0 : BitVec 64) (e : PTW_Error) (es_x : List Weff) (s : ExecSt)
    (hgate : update_PTE_Bits stale acc = some g) (hmenv : s.regs .menvcfg = menvcfg0)
    (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hrdx : execEff (read_pte_exclusive (.Physaddr a) 8) s = some (.Ok fresh, s, es_x))
    (hchk : execEff (check_leaf_pte 39 vpn acc p mxr dosum fresh (.Physaddr a) lvl ()) s =
      some (.Err (e, ()), s, [])) :
    execEff (update_and_write_pte 39 vpn (.Physaddr a) stale lvl acc p mxr dosum ()) s =
      some (.Err (e, ()), s, es_x) := by
  unfold update_and_write_pte
  exec_eff_run
  erw [hgate]
  exec_eff_run [WeakWalkEff.execEffCurrentlyEnabledSvadu, hmenv, hadue]
  erw [hrdx]
  exec_eff_run
  erw [hchk]
  exec_eff_run

/-- Rocq `exec_eff_update_and_write_pte_write_err` (the conditional write faults). -/
theorem execEffUpdateAndWritePteWriteErr (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (a : BitVec 64) (stale g fresh fresh' : BitVec 64) (lvl : Nat) (ppnv : BitVec 44)
    (pb : page_based_mem_type) (menvcfg0 : BitVec 64) (ex : physaddr × ExceptionType)
    (es_x es_w : List Weff) (sw : ExecSt) (s : ExecSt)
    (hgate : update_PTE_Bits stale acc = some g) (hmenv : s.regs .menvcfg = menvcfg0)
    (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hrdx : execEff (read_pte_exclusive (.Physaddr a) 8) s = some (.Ok fresh, s, es_x))
    (hchk : execEff (check_leaf_pte 39 vpn acc p mxr dosum fresh (.Physaddr a) lvl ()) s =
      some (.Ok (ppnv, pb, ()), s, []))
    (hupd : update_PTE_Bits fresh acc = some fresh')
    (hwrite : execEff (write_pte_conditional (.Physaddr a) 8 fresh') s = some (.Err ex, sw, es_w)) :
    execEff (update_and_write_pte 39 vpn (.Physaddr a) stale lvl acc p mxr dosum ()) s =
      some (.Err (.PTW_No_Access (), ()), sw, es_x ++ es_w) := by
  unfold update_and_write_pte
  exec_eff_run
  erw [hgate]
  exec_eff_run [WeakWalkEff.execEffCurrentlyEnabledSvadu, hmenv, hadue]
  erw [hrdx]
  exec_eff_run
  erw [hchk]
  exec_eff_run
  erw [hupd]
  exec_eff_run
  erw [hwrite]
  exec_eff_run

/-! ## 6. The TLB plumbing: the generic level-0 fill and `write_TLB` -/

/-- Rocq `exec_eff_add_to_TLB_pt`. -/
theorem execEffAddToTLBPt (asid : BitVec 16) (vpn : BitVec 27) (pp : BitVec 44) (pte : BitVec 64)
    (ptea : physaddr) (g : Bool) (s : ExecSt) :
    execEff (add_to_TLB 39 asid vpn pp pte ptea 0 g) s =
      some ((), s.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn)
        (some (ptFillEnt asid vpn pp pte ptea g))), []) := by
  unfold add_to_TLB
  exec_eff_run
  rfl

/-- Rocq `exec_eff_write_TLB`. -/
theorem execEffWriteTLB (ix : Nat) (en : TLB_Entry) (s : ExecSt) :
    execEff (write_TLB ix en) s = some ((), s.setReg .tlb (vectorUpdate (s.regs .tlb) ix (some en)), []) := by
  unfold write_TLB
  exec_eff_run

/-! ### The `PtTreeAdue` entry identifications (Lean-only twins, deviation 4) -/

/-- The G bit survives an A/D update (Lean-only). -/
theorem WeakUpdEff.uGbitSetAd (w : BitVec 64) (a d : BitVec 1) : uGbit (pteSetAD w a d) = uGbit w := by
  simp only [uGbit, pteSetAD, Mk_PTE_Flags, _get_PTE_Flags_G, _update_PTE_Flags_A, _update_PTE_Flags_D,
    Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.extractLsb]
  congr 1
  bv_decide

/-- Rocq `PtTreeAdue.pt_fill_ent_uwe` (Lean-only twin): the level-0 fill with an
A/D variant of the walked leaf is the walk entry of that variant. -/
theorem WeakUpdEff.ptFillEntUwe (vpn : BitVec 27) (p2 p1 p0 q : BitVec 64) (asid : BitVec 16)
    (a d : BitVec 1) (h : q = pteSetAD p0 a d) :
    ptFillEnt asid vpn (ppn0 p0) q (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)))
      (uGlobal p2 p1 p0) = uWalkEntry vpn p2 p1 q asid := by
  subst h
  unfold uWalkEntry uGlobal
  rw [WeakUpdEff.uGbitSetAd]
  have hp : ppn0 (pteSetAD p0 a d) = ppn0 p0 := ppn_of_pteSetAD p0 a d
  rw [hp]

/-- Rocq `PtTreeAdue.tlb_set_pte_uwe` (Lean-only twin): refreshing a walk entry
with an A/D variant of its word is the walk entry of that variant. -/
theorem WeakUpdEff.tlbSetPteUwe (vpn : BitVec 27) (q2 q1 q0 q0' : BitVec 64) (asid : BitVec 16)
    (a d : BitVec 1) (h : q0' = pteSetAD q0 a d) :
    tlb_set_pte (k_n := 8) (uWalkEntry vpn q2 q1 q0 asid) q0' = uWalkEntry vpn q2 q1 q0' asid := by
  subst h
  unfold tlb_set_pte uWalkEntry uGlobal ptFillEnt
  rw [WeakUpdEff.uGbitSetAd]
  have hp : ppn0 (pteSetAD q0 a d) = ppn0 q0 := ppn_of_pteSetAD q0 a d
  rw [hp]

/-- A walk entry is a level-0 entry (Lean-only). -/
theorem WeakUpdEff.tlbGetLevelUwe (vpn : BitVec 27) (q2 q1 q0 : BitVec 64) (asid : BitVec 16) :
    tlb_get_level 39 (uWalkEntry vpn q2 q1 q0 asid) = 0 := by
  have h : (uWalkEntry vpn q2 q1 q0 asid).levelMask = 0#45 := by
    show zero_extend (m := 57 - 12) (ones (n := 0)) = 0#45
    decide
  unfold tlb_get_level
  simp only [h]
  decide +kernel

/-! ## 7. THE WRITE-BACK TRANSLATE HEADS -/

/-- Rocq `exec_eff_translate_TLB_miss_user_upd`: a MISS whose walked leaf needs
bits -- the walk, the CAS pair, the fill with the UPDATED word. -/
theorem execEffTranslateTLBMissUserUpd (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (root : BitVec 44) (p2 p1 p0 p0' : BitVec 64) (menvcfg0 : BitVec 64) (asid : BitVec 16)
    (es2 es1 es0 es_x es_w : List Weff) (sw : ExecSt) (s : ExecSt)
    (hv2 : wpteValid p2) (hn2 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p2 7 0)) = true)
    (hv1 : wpteValid p1) (hn1 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p1 7 0)) = true)
    (hv0 : wpteValid p0) (hl0 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p0 7 0)) = false)
    (hchk : wpteCheckOk acc p mxr dosum p0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE p0) == 1#1) = false)
    (hupd : update_PTE_Bits p0 acc = some p0')
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok p2, s, es2))
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok p1, s, es1))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok p0, s, es0))
    (hrdx : execEff (read_pte_exclusive (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok p0, s, es_x))
    (hmisa : s.regs .misa = misaC) (hmenv : s.regs .menvcfg = menvcfg0)
    (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true)
    (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hwrite : execEff (write_pte_conditional (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)))
      8 p0') s = some (.Ok true, sw, es_w))
    (hswregs : sw.regs = s.regs) :
    execEff (translate_TLB_miss 39 asid root vpn acc p mxr dosum ()) s =
      some (.Ok (ppn0 p0, .PBMT_PMA, ()),
        sw.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 p0' asid))),
        (es2 ++ (es1 ++ es0)) ++ (es_x ++ es_w)) := by
  have hu := execEffUpdateAndWritePteWritten acc p mxr dosum vpn
    (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) p0 p0' p0 p0' 0 (ppn0 p0) .PBMT_PMA menvcfg0
    es_x es_w sw s hupd hmenv hadue hrdx
    (execEffCheckLeafPteLeaf0 vpn p0 acc p mxr dosum hv0 hl0 hchk h0N _ menvcfg0 s hmisa hmenv hpbmte) hupd hwrite
  obtain ⟨a, d, hq⟩ := PtAdBits.updatePTEBitsSetAd _ _ _ hupd
  unfold translate_TLB_miss
  exec_eff_run
  erw [execEffPtWalkUser vpn root p2 p1 p0 acc p mxr dosum hv2 hn2 hv1 hn1 hv0 hl0 hchk h0N menvcfg0
    es2 es1 es0 s hmisa hrd2 hrd1 hrd0 hmenv hpbmte]
  unfold uWalkOut
  exec_eff_run
  erw [hu]
  exec_eff_run
  erw [execEffAddToTLBPt asid vpn (ppn0 p0) p0' _ (uGlobal p2 p1 p0) sw]
  rw [WeakUpdEff.ptFillEntUwe vpn p2 p1 p0 p0' asid a d hq, hswregs]
  simp only [List.append_nil]

/-- Rocq `exec_eff_translate_TLB_hit_pt_upd`: a HIT whose cached word needs bits
and whose memory word still does -- the CAS pair, the in-place refresh with the
word DERIVED FROM MEMORY. -/
theorem execEffTranslateTLBHitPtUpd (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (q2 q1 q0 q0g m0 m0' : BitVec 64) (menvcfg0 : BitVec 64) (asid : BitVec 16) (idx : Nat)
    (es_x es_w : List Weff) (sw : ExecSt) (s : ExecSt)
    (hchk : wpteCheckOk acc p mxr dosum q0) (hgate : update_PTE_Bits q0 acc = some q0g) (hpb : ptePbmt0 q0)
    (hmenv : s.regs .menvcfg = menvcfg0) (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hrdx : execEff (read_pte_exclusive (.Physaddr (uPteAddr (uNextBase q1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok m0, s, es_x))
    (hv0 : wpteValid m0) (hl0 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb m0 7 0)) = false)
    (hchkm : wpteCheckOk acc p mxr dosum m0)
    (hmN : (_get_PTE_Ext_N (ext_bits_of_PTE m0) == 1#1) = false)
    (hmisa : s.regs .misa = misaC) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true)
    (hvar : ∃ a2 d2 : BitVec 1, m0 = pteSetAD q0 a2 d2)
    (hupd : update_PTE_Bits m0 acc = some m0')
    (hwrite : execEff (write_pte_conditional (.Physaddr (uPteAddr (uNextBase q1) (Sail.BitVec.extractLsb vpn 8 0)))
      8 m0') s = some (.Ok true, sw, es_w))
    (hswregs : sw.regs = s.regs) :
    execEff (translate_TLB_hit 39 asid vpn acc p mxr dosum () idx (uWalkEntry vpn q2 q1 q0 asid)) s =
      some (.Ok (ppn0 q0, .PBMT_PMA, ()),
        sw.setReg .tlb (vectorUpdate (s.regs .tlb) idx (some (uWalkEntry vpn q2 q1 m0' asid))),
        es_x ++ es_w) := by
  have hu := execEffUpdateAndWritePteWritten acc p mxr dosum vpn
    (uPteAddr (uNextBase q1) (Sail.BitVec.extractLsb vpn 8 0)) q0 q0g m0 m0' 0 (ppn0 m0) .PBMT_PMA menvcfg0
    es_x es_w sw s hgate hmenv hadue hrdx
    (execEffCheckLeafPteLeaf0 vpn m0 acc p mxr dosum hv0 hl0 hchkm hmN _ menvcfg0 s hmisa hmenv hpbmte) hupd hwrite
  obtain ⟨a2, d2, hm0⟩ := hvar
  obtain ⟨a, d, hq⟩ := PtAdBits.updatePTEBitsSetAd _ _ _ hupd
  have hqc : m0' = pteSetAD q0 a d := by rw [hq, hm0, pteSetAD_pteSetAD]
  have hlvl := WeakUpdEff.tlbGetLevelUwe vpn q2 q1 q0 asid
  have hadr : (uWalkEntry vpn q2 q1 q0 asid).pteAddr =
      .Physaddr (uPteAddr (uNextBase q1) (Sail.BitVec.extractLsb vpn 8 0)) := rfl
  unfold translate_TLB_hit
  simp only [tlbGetPteUwe, tlbGetPpnUwe, hlvl, hadr]
  exec_eff_run
  erw [hchk s]
  exec_eff_run
  erw [hu]
  exec_eff_run
  erw [execEffWriteTLB idx _ sw]
  exec_eff_run
  erw [execEffUwePbmt vpn q2 q1 q0 asid _ hpb]
  erw [WeakUpdEff.tlbSetPteUwe vpn q2 q1 q0 m0' asid a d hqc]
  rw [hswregs]
  simp only [List.append_nil]

/-- Rocq `exec_eff_translate_TLB_hit_pt_refresh`: a HIT whose memory word already
has the bits -- no write, the entry refreshed with the MEMORY word, trace the CAS
read alone. -/
theorem execEffTranslateTLBHitPtRefresh (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr dosum : Bool)
    (vpn : BitVec 27) (q2 q1 q0 q0g m0 : BitVec 64) (menvcfg0 : BitVec 64) (asid : BitVec 16) (idx : Nat)
    (es_x : List Weff) (s : ExecSt)
    (hchk : wpteCheckOk acc p mxr dosum q0) (hgate : update_PTE_Bits q0 acc = some q0g) (hpb : ptePbmt0 q0)
    (hmenv : s.regs .menvcfg = menvcfg0) (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hrdx : execEff (read_pte_exclusive (.Physaddr (uPteAddr (uNextBase q1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok m0, s, es_x))
    (hv0 : wpteValid m0) (hl0 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb m0 7 0)) = false)
    (hchkm : wpteCheckOk acc p mxr dosum m0)
    (hmN : (_get_PTE_Ext_N (ext_bits_of_PTE m0) == 1#1) = false)
    (hmisa : s.regs .misa = misaC) (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true)
    (hvar : ∃ a2 d2 : BitVec 1, m0 = pteSetAD q0 a2 d2)
    (hupd : update_PTE_Bits m0 acc = none) :
    execEff (translate_TLB_hit 39 asid vpn acc p mxr dosum () idx (uWalkEntry vpn q2 q1 q0 asid)) s =
      some (.Ok (ppn0 q0, .PBMT_PMA, ()),
        s.setReg .tlb (vectorUpdate (s.regs .tlb) idx (some (uWalkEntry vpn q2 q1 m0 asid))),
        es_x) := by
  have hu := execEffUpdateAndWritePteFresh acc p mxr dosum vpn
    (uPteAddr (uNextBase q1) (Sail.BitVec.extractLsb vpn 8 0)) q0 q0g m0 0 (ppn0 m0) .PBMT_PMA menvcfg0
    es_x s hgate hmenv hadue hrdx
    (execEffCheckLeafPteLeaf0 vpn m0 acc p mxr dosum hv0 hl0 hchkm hmN _ menvcfg0 s hmisa hmenv hpbmte) hupd
  obtain ⟨a2, d2, hm0⟩ := hvar
  have hlvl := WeakUpdEff.tlbGetLevelUwe vpn q2 q1 q0 asid
  have hadr : (uWalkEntry vpn q2 q1 q0 asid).pteAddr =
      .Physaddr (uPteAddr (uNextBase q1) (Sail.BitVec.extractLsb vpn 8 0)) := rfl
  unfold translate_TLB_hit
  simp only [tlbGetPteUwe, tlbGetPpnUwe, hlvl, hadr]
  exec_eff_run
  erw [hchk s]
  exec_eff_run
  erw [hu]
  exec_eff_run
  erw [execEffWriteTLB idx _ s]
  exec_eff_run
  erw [execEffUwePbmt vpn q2 q1 q0 asid _ hpb]
  erw [WeakUpdEff.tlbSetPteUwe vpn q2 q1 q0 m0 asid a2 d2 hm0]
  simp only [List.append_nil]

/-! ## 8. THE `translateAddr`-LEVEL COMPOSITION -/

/-- Rocq `exec_eff_translateAddr_pt_miss_upd`: the MISS whose leaf needs bits,
through `WeakWalkEff`'s outcome-generic front head (deviation 5). -/
theorem execEffTranslateAddrPtMissUpd (acc : MemoryAccessType mem_payload) (p : Privilege) (vpn : BitVec 27)
    (root : BitVec 44) (p2 p1 p0 p0' : BitVec 64) (satp0 va pa menvcfg0 : BitVec 64)
    (es2 es1 es0 es_x es_w : List Weff) (sw : ExecSt) (s : ExecSt)
    (heff : execEff (effectivePrivilege acc (s.regs .mstatus) p) s = some (p, s, []))
    (hss : execEff (is_shadow_stack_access acc) s = some (false, s, []))
    (hcp : s.regs .cur_privilege = p)
    (htm : execEff (translationMode p) s = some (.Sv39, s, []))
    (hsatp : s.regs .satp = satp0)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = root)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hcanon : (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false)
    (hvpn : BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38 Functions.pagesize_bits) =
      vpn)
    (hlk : execEff (lookup_TLB 39 0#16 vpn) s = some (none, s, []))
    (hv2 : wpteValid p2) (hn2 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p2 7 0)) = true)
    (hv1 : wpteValid p1) (hn1 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p1 7 0)) = true)
    (hv0 : wpteValid p0) (hl0 : pte_is_non_leaf (Mk_PTE_Flags (Sail.BitVec.extractLsb p0 7 0)) = false)
    (hchkall : ∀ mxr dosum, wpteCheckOk acc p mxr dosum p0)
    (h0N : (_get_PTE_Ext_N (ext_bits_of_PTE p0) == 1#1) = false)
    (hupd : update_PTE_Bits p0 acc = some p0')
    (hrd2 : execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) s =
      some (.Ok p2, s, es2))
    (hrd1 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) s =
      some (.Ok p1, s, es1))
    (hrd0 : execEff (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok p0, s, es0))
    (hrdx : execEff (read_pte_exclusive (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) s =
      some (.Ok p0, s, es_x))
    (hmisa : s.regs .misa = misaC) (hmenv : s.regs .menvcfg = menvcfg0)
    (hpbmte : (_get_MEnvcfg_PBMTE menvcfg0 == 0#1) = true)
    (hadue : (_get_MEnvcfg_ADUE menvcfg0 == 1#1) = true)
    (hwrite : execEff (write_pte_conditional (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)))
      8 p0') s = some (.Ok true, sw, es_w))
    (hswregs : sw.regs = s.regs)
    (hident : zero_extend (m := 64) (ppn0 p0 +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa) :
    execEff (translateAddr (.Virtaddr va) acc) s =
      some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw),
        sw.setReg .tlb (vectorUpdate (s.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 p0' 0#16))),
        (es2 ++ (es1 ++ es0)) ++ (es_x ++ es_w)) :=
  execEffTranslateAddrPtFront acc p vpn root (ppn0 p0) satp0 va pa _ s _ heff hss hcp htm hsatp hppn hasid hcanon
    hvpn (fun mxr dosum => execEffTranslateMissUser vpn root 0#16 acc p mxr dosum _ s _ _ hlk
      (execEffTranslateTLBMissUserUpd acc p mxr dosum vpn root p2 p1 p0 p0' menvcfg0 0#16 es2 es1 es0 es_x es_w
        sw s hv2 hn2 hv1 hn1 hv0 hl0 (hchkall mxr dosum) h0N hupd hrd2 hrd1 hrd0 hrdx hmisa hmenv hpbmte hadue
        hwrite hswregs)) hident

/-! ## 9. THE CERTIFICATES for the CAS pair -/

/-- Rocq `wcert_ptw_upd_gen`: the adjacent CAS pair with write-free surroundings
certifies a width-8 STORE (`wQStoreW 8`), whole-window form. -/
theorem wcertPtwUpdGen (cid : Nat) (pc : BitVec 64) (pre post : List Weff) (akx akw : AkInfo) (ea : PAddr)
    (v : BitVec 64) :
    nowriteTrace pre → nowriteTrace post →
    wstepCert cid pc (wPEff (some cid) (pre ++ .WEread akx ea 8 :: .WEwrite akw ea 8 v :: post))
      (wQStoreW 8 (some cid) ea v) := by
  intro hpre hpost
  apply wstepCertEff
  intro s s' hi hl hws
  have hle : wsLe s.wmWs s'.wmWs := by rw [hws]; exact weffsWsLe _ _ _
  have hl1 : (weffs (some cid) s pre).wmLog = s.wmLog := weffsNowriteLog _ _ _ hpre
  rw [weffsApp, weffsCons, weffsCons, weffApplyRead, weffApplyWrite] at hl hws
  rw [cohTsLog _ s ea 8 hl1] at hl hws
  rw [weffsNowriteLog _ _ _ hpost, wwritePostLog, wreadPostLog, hl1] at hl
  unfold wQStoreW wVStoreW
  refine ⟨hi, ⟨_, hl, fun hr => WeakInstr.wmClassOfRelp _ _
    (by rw [WeakInstr.wreadPostRelp]; exact weffsNowriteRelp _ _ _ hpre hr)⟩, hle, fun j hj => ?_⟩
  -- the floor reached at the write's own step survives the write-free tail
  have h2 := flrWsLe _ _ (WeakInterp.accAddr ea j)
    (weffsWsLe (some cid)
      (wwritePost (some cid) (wreadPost (weffs (some cid) s pre) akx ea (cohTs s ea 8)) akw ea 8 v) post)
  rw [← hws, wwritePostWs, flr_wsView, wreadPostLog, hl1] at h2
  have := storePostRunCoh (wreadPost (weffs (some cid) s pre) akx ea (cohTs s ea 8)).wmWs
    akw.akSync (paZ ea) 8 (s.wmLog.length + 1) j hj
  simp only [WeakInterp.accAddr] at h2 ⊢
  omega

/-- Rocq `wcert_ptw_upd_pin`: the trace-pinned form (the CAS pair is pinned by
kind). -/
theorem wcertPtwUpdPin (cid : Nat) (pc : BitVec 64) (pre post : List Weff) (akx akw : AkInfo) (ea : PAddr)
    (v : BitVec 64) :
    nowriteTrace pre → nowriteTrace post →
    wstepCert cid pc (wPEffPin (some cid) (pre ++ .WEread akx ea 8 :: .WEwrite akw ea 8 v :: post))
      (wQStoreW 8 (some cid) ea v) := by
  intro hpre hpost
  apply wstepCertEffPin
  intro s s' hi hl hws
  have hle : wsLe s.wmWs s'.wmWs := by rw [hws]; exact weffsWsLe _ _ _
  have hl1 : (weffs (some cid) s pre).wmLog = s.wmLog := weffsNowriteLog _ _ _ hpre
  rw [weffsApp, weffsCons, weffsCons, weffApplyRead, weffApplyWrite] at hl hws
  rw [cohTsLog _ s ea 8 hl1] at hl hws
  rw [weffsNowriteLog _ _ _ hpost, wwritePostLog, wreadPostLog, hl1] at hl
  unfold wQStoreW wVStoreW
  refine ⟨hi, ⟨_, hl, fun hr => WeakInstr.wmClassOfRelp _ _
    (by rw [WeakInstr.wreadPostRelp]; exact weffsNowriteRelp _ _ _ hpre hr)⟩, hle, fun j hj => ?_⟩
  have h2 := flrWsLe _ _ (WeakInterp.accAddr ea j)
    (weffsWsLe (some cid)
      (wwritePost (some cid) (wreadPost (weffs (some cid) s pre) akx ea (cohTs s ea 8)) akw ea 8 v) post)
  rw [← hws, wwritePostWs, flr_wsView, wreadPostLog, hl1] at h2
  have := storePostRunCoh (wreadPost (weffs (some cid) s pre) akx ea (cohTs s ea 8)).wmWs
    akw.akSync (paZ ea) 8 (s.wmLog.length + 1) j hj
  simp only [WeakInterp.accAddr] at h2 ⊢
  omega

end Weak
