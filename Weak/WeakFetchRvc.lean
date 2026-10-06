/-
Weak: **the compressed fetch arm, at `execEff`** (M4 batch 0b): the `Ext_Zca`
enablement chain at the EMPTY trace, the `F_RVC` arm of the fetch at a
4-ALIGNED pc, its `fetchFlatOk` wrapper, the self-bridge `execEffOfGoodb0Self`,
and the recipe `wPEffOfLeafRvc4` for a compressed instruction.

Rocq: `iris/WeakFetchRvc.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakFetchEff` mirrors the 4-aligned `F_Base`
arm of `WeakFunnel.execFetchFlat`.  This file adds the cheapest of the other
three: the `F_RVC` arm AT A 4-ALIGNED pc.  A 4-aligned fetch reads the whole
32-bit word whatever the instruction turns out to be (`WeakFetchEff.execEffFetch4`
covers both outcomes of the final `isRVC` test over the SAME
`execEffFetchBytes4`), so the trace is IDENTICAL -- in Lean (O2,
`Weak/WeakFetchEff.lean` deviation 2) `[.WEread WeakFetchEff.wakIfetch pc 4]`
-- and every certificate stated at that element applies verbatim.  New is only
the `Ext_Zca` enablement probe the compressed path runs in `run_hart_active`
(register-only, empty trace) and the `F_RVC` result.  STILL NOT COVERED: the
2-ALIGNED arms (the Lean model, like Rocq's, fetches a pc ≡ 2 mod 4 as TWO
halfword reads, so the trace has two elements).

Sections: §1 the `Ext_Zca` enablement chain at the empty trace; §2
`execEffFetchRVC4` and its `fetchFlatOk` wrapper; the self-bridge; §3
`wPEffOfLeafRvc4`.

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below), and
   `Weak/WeakFetchEff.lean` deviation 1's vocabulary (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `subrange_vec_dec w 15 0` ↦ `Sail.BitVec.extractLsb w 15 0`, `set_reg` ↦
   `ExecSt.setReg`, `RETIRE_SUCCESS` ↦ `.Retire_Success ()`, `add_vec_int` ↦
   `BitVec.addInt`, the byte window ↦ `BytesAt`, `dom (mem s) ⊆ W` ↦
   `bmDomSub s.mem W`).
2. O2: every fetch trace element is `.WEread WeakFetchEff.wakIfetch …` (Rocq
   `WEread wak_plain …`), as `Weak/WeakFetchEff.lean` deviation 2.
3. `hartSupports` is pure in Lean (`Weak/WeakFetchEff.lean` deviation 4):
   Rocq `exec_eff (hartSupports X) s = Some (true, s, [])` ↦ `hartSupports .X =
   true`.  Rocq's fuelled `exec_eff_rec_cE_C_misa k acc` (premise `k ≥ 0`) is
   stated on `currentlyEnabled .Ext_C` (no fuel, no premise).  Rocq's Ltac
   `ehs_leaf_eff` (a local proof helper for the fuelled `hartSupports`) has no
   Lean counterpart (`decide +kernel` closes the pure facts).
4. `exec_eff_fetch_flat_rvc4`: Rocq's `pma_allows_all` is `pma_regions =
   bootPMA` and `pmp_allows_all` is `WeakFunnel.pmpAllowsAll` (as
   `WeakFetchEff.execEffFetchFlatBase4`, its deviation 5).
5. `wPEffOfLeafRvc4`: the extra O2 premise `fetchPin σ es` (as
   `WeakFetchEff.wPEffOfLeafBase`, its deviation 9); `∀ j < 4, addr_is_ram
   (pa_add pc j)` is `inRam pc 4`; the confined state is `⟨σ.wmRegs,
   wmemRestrict σ W, σ.wmDev⟩`; `pma_allows_all` as 4.  The assembly is proved
   through the Lean-only `WeakFetchRvc.execEffStepOfLeafRvc4St` (the run fact
   over an arbitrary state, as `WeakFetchEff.execEffStepOfLeafBaseSt`).
   Rocq's `W : _` is `W : GSet PAddr`.
6. Rocq §4's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_hartSupports_Zca`
`WeakFetchRvc.execEffHartSupportsZca` (duplicated name),
`exec_eff_hartSupports_C` `execEffHartSupportsC`, `exec_eff_rec_cE_C_misa`
`execEffRecCECMisa`, `exec_eff_currentlyEnabled_Zca`
`execEffCurrentlyEnabledZca`, `exec_eff_fetch_RVC_4` `execEffFetchRVC4`,
`exec_eff_fetch_flat_rvc4` `execEffFetchFlatRvc4`, `exec_eff_of_goodb0_self`
`execEffOfGoodb0Self`, `wP_eff_of_leaf_rvc4` `wPEffOfLeafRvc4`.  Lean-only
(file-qualified): `WeakFetchRvc.execEffStepOfLeafRvc4St`.

**Dropped:** the Ltac `ehs_leaf_eff` (deviation 3; a proof-local helper, no
downstream use).  Rocq 8 lemmas + 1 `Local Ltac`; Lean 8 + 1 Lean-only.

**Statements checked** (by hand, against Rocq): all; the changed ones are
listed under the deviations.
-/
import Weak.WeakFetchEff

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE `Ext_Zca` ENABLEMENT CHAIN, AT THE EMPTY TRACE -/

/-- Rocq `exec_eff_hartSupports_Zca` (duplicated name; deviation 3). -/
theorem WeakFetchRvc.execEffHartSupportsZca : hartSupports .Ext_Zca = true := by decide +kernel

/-- Rocq `exec_eff_hartSupports_C` (deviation 3). -/
theorem execEffHartSupportsC : hartSupports .Ext_C = true := by decide +kernel

/-- Rocq `exec_eff_rec_cE_C_misa` (deviation 3: no fuel). -/
theorem execEffRecCECMisa (s : ExecSt) :
    execEff (currentlyEnabled .Ext_C) s = some (_get_Misa_C (s.regs .misa) == 1#1, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsC, ↓reduceIte]
  exec_eff_run

/-- Rocq `exec_eff_currentlyEnabled_Zca`. -/
theorem execEffCurrentlyEnabledZca (s : ExecSt) (hC : (_get_Misa_C (s.regs .misa) == 1#1) = true) :
    execEff (currentlyEnabled .Ext_Zca) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [WeakFetchRvc.execEffHartSupportsZca, ↓reduceIte]
  exec_eff_run [execEffRecCECMisa s, hC, Bool.true_or]

/-! ## 2. THE COMPRESSED FETCH AT A 4-ALIGNED pc

The SAME 4-byte read as `WeakFetchEff.execEffFetchDone`, with the final
`isRVC` test taken the other way. -/

/-- Rocq `exec_eff_fetch_RVC_4` (deviation 2). -/
theorem execEffFetchRVC4 (pc : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (hpcPC : s.regs .PC = pc) (hpriv : s.regs .cur_privilege = .Machine)
    (hpmp : execEff (pmpCheck (.Physaddr (fetchPa pc)) 4 (.InstructionFetch ()) .Machine) s =
      some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (fetchPa pc)) 4 = some region)
    (hexec : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : execEff (within_clint (.Physaddr (fetchPa pc)) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (fetchPa pc)) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr (fetchPa pc)) 4) s = some (false, s, []))
    (hdev : devAddr (fetchPa pc) = false) (hb : BytesAt s (fetchPa pc) 4 w)
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = true)
    (hisRVC : isRVC (Sail.BitVec.extractLsb w 15 0) = true) :
    execEff (fetch ()) s =
      some (.F_RVC (Sail.BitVec.extractLsb w 15 0), s, [.WEread WeakFetchEff.wakIfetch (fetchPa pc) 4]) := by
  rw [WeakFetchEff.execEffFetch4 pc w s s _ hpcPC hvalign
    (execEffFetchBytes4 pc region w s hpriv hpmp hmatch hexec hc hsig hh hdev hb hvalign), hisRVC]
  rfl

/-- Rocq `exec_eff_fetch_flat_rvc4` (deviation 4): the `F_RVC` twin of
`WeakFetchEff.execEffFetchFlatBase4`. -/
theorem execEffFetchFlatRvc4 (t : ExecSt) (pc : BitVec 64) (h : BitVec 16) :
    pmpAllowsAll (t.regs .pmpcfg_n) →
    t.regs .pma_regions = bootPMA →
    t.regs .PC = pc →
    t.regs .cur_privilege = .Machine →
    t.regs .htif_tohost_base = none →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    fetchFlatOk t pc (.F_RVC h) →
    execEff (fetch ()) t = some (.F_RVC h, t, [.WEread WeakFetchEff.wakIfetch pc 4]) := by
  rintro hpmp hpma lpc lpriv lhtif hal ⟨_, hram, w, hr, hbytes⟩
  obtain ⟨hsub, hisRVC⟩ := hr
  have halign : is_aligned_paddr (.Physaddr (fetchPa pc)) 4 = true := by rw [fetchPa_eq]; exact hal
  have hmatch : matching_pma_region (t.regs .pma_regions) (.Physaddr (fetchPa pc)) 4 = some ramRegion := by
    rw [hpma, fetchPa_eq]; exact matching_pma_ram pc 4 hram (by decide) (by decide)
  have hc : execEff (within_clint (.Physaddr (fetchPa pc)) 4) t = some (false, t, []) := by
    rw [fetchPa_eq, within_clint_ram pc 4 hram]; rfl
  have hsig : execEff (within_sig (.Physaddr (fetchPa pc)) 4) t = some (false, t, []) := by
    first
    | rfl
    | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)
  have hb : BytesAt t (fetchPa pc) 4 w := by rw [fetchPa_eq]; exact hbytes
  have hisRVC' : isRVC (Sail.BitVec.extractLsb w 15 0) = true := by rw [hsub]; exact hisRVC
  have hf := execEffFetchRVC4 pc ramRegion w t lpc lpriv
    (execEffPmpCheckMachineUnlockedIfetch4 (fetchPa pc) t hpmp halign) hmatch ramRegionExec hc hsig
    (execEffWithinHtifFalse _ 4 t lhtif) (by rw [fetchPa_eq]; exact devAddrRam pc 4 hram) hb hal hisRVC'
  rw [fetchPa_eq, hsub] at hf
  exact hf

/-- Rocq `exec_eff_of_goodb0_self`: a run certified `goodb0` AT ITS OWN STATE is
trace-free there (`execEffDecodeBridge` with `dst := s`). -/
theorem execEffOfGoodb0Self (D : Register → Bool) {X : Type} (m : SailM X) (s : ExecSt) (x : X) :
    goodb0 D m s = true → exec m s = some (x, s) → execEff m s = some (x, s, []) :=
  fun hg he => execEffDecodeBridge D m s s x (fun _ _ => rfl) hg he

/-! ## 3. `wPEffOfLeafRvc4` -- THE RECIPE FOR A COMPRESSED INSTRUCTION -/

/-- The run-assembly half over an arbitrary state (Lean-only, deviation 5). -/
theorem WeakFetchRvc.execEffStepOfLeafRvc4St (s : ExecSt) (W : GSet PAddr)
    (pc : BitVec 64) (h : BitVec 16) (w : BitVec 32) (i0 i : instruction) (es_x : List Weff)
    (D D0 : Register → Bool) (dst : ExecSt) :
    s.regs .PC = pc →
    s.regs .cur_privilege = .Machine →
    pmpAllowsAll (s.regs .pmpcfg_n) →
    s.regs .pma_regions = bootPMA →
    s.regs .htif_tohost_base = none →
    s.regs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    (_get_Misa_C (s.regs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (s.regs .mstatus) == 1#1) = false →
    (s.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → s.mem (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    Sail.BitVec.extractLsb w 15 0 = h →
    isRVC h = true →
    (∀ r, D r = true → s.regs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s' : ExecSt, goodb0 D0 (execute i0) s' = true) →
    (∀ s' : ExecSt, exec (execute i0) s' = some (.ExecuteAs i, s')) →
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i) ((s.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2)) =
        some (.Retire_Success (), sExec, es_x) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    ∀ tick : Bool, ∃ t' : ExecSt,
      execEff (riscvStep tick) s = some ((), t', [.WEread WeakFetchEff.wakIfetch pc 4] ++ es_x) ∧
      bmDomSub t'.mem W := by
  intro lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal hram htext hsub hisRVC hagree hDmi
    hgood hdec hgood0 hexp hexec tick
  obtain ⟨b, hsi⟩ := execEffShouldIncMinstretSome (s.regs .cur_privilege) s
  obtain ⟨sExec, hex, hhe, hmie, hdom⟩ := hexec b
  have lpriv_a : (hartActiveSA s b).regs .cur_privilege = .Machine := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpriv
  have lpc_a : (hartActiveSA s b).regs .PC = pc := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpc
  have lhart_a : (hartActiveSA s b).regs .hart_state = .HART_ACTIVE () := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhart
  have lelp_a : ((hartActiveSA s b).regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lelp
  have hdisp : execEff (dispatchInterrupt .Machine) (hartActiveSA s b) =
      some (none, hartActiveSA s b, []) :=
    execEffDispatchInterruptMachineNone _
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaS)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmIE)
  have hzca : execEff (currentlyEnabled .Ext_Zca) (hartActiveSA s b) =
      some (true, hartActiveSA s b, []) :=
    execEffCurrentlyEnabledZca _ (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaC)
  have hfetch : execEff (fetch ()) (hartActiveSA s b) =
      some (.F_RVC h, hartActiveSA s b, [.WEread WeakFetchEff.wakIfetch pc 4]) :=
    execEffFetchFlatRvc4 _ pc h
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpmp)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpma)
      lpc_a lpriv_a
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhtif)
      hal ⟨align4Align2 pc hal, hram, w, ⟨hsub, hisRVC⟩, htext⟩
  have hdec_a : execEff (ext_decode_compressed h) (hartActiveSA s b) =
      some (i0, hartActiveSA s b, []) := by
    refine execEffDecodeBridge D (ext_decode_compressed h) dst _ i0 ?_ hgood hdec
    intro r hD
    have hne : r ≠ .minstret_increment := by
      rintro rfl
      rw [hDmi] at hD
      exact absurd hD (by decide)
    rw [WeakFetchEff.saLookup r s b hne]
    exact hagree r hD
  -- the expansion, through the SAME bridge at the state itself
  have hexp_a : execEff (execute i0) ((hartActiveSA s b).setReg .nextPC (BitVec.addInt pc 2)) =
      some (.ExecuteAs i, (hartActiveSA s b).setReg .nextPC (BitVec.addInt pc 2), []) :=
    execEffOfGoodb0Self D0 (execute i0) _ _ (hgood0 _) (hexp _)
  have hstep := execEffRiscvStepRvc s sExec h i0 i pc b [.WEread WeakFetchEff.wakIfetch pc 4] es_x hsi
    lhart_a lpriv_a hdisp hfetch hdec_a lelp_a lpc_a hzca hexp_a hex hhe hmie
  obtain ⟨t', ht', hmt'⟩ := execEffRiscvStepAllTicks s _ _ hstep tick
  refine ⟨t', ht', ?_⟩
  rw [hmt']
  cases b <;> exact hdom

/-- Rocq `wP_eff_of_leaf_rvc4` (deviation 5: the extra O2 premise `fetchPin`):
`WeakFetchEff.wPEffOfLeafBase` for a compressed instruction -- the fetch is
§2's (the SAME one-element trace), the decode is `ext_decode_compressed h`
through the same bridge, the expansion `execute i0 = ExecuteAs i` is carried
state-generically at a read-set `D0`, plus `misa.C` for the `Ext_Zca` probe. -/
theorem wPEffOfLeafRvc4 (cid : Nat) (σ : Wmstate) (W : GSet PAddr)
    (pc : BitVec 64) (h : BitVec 16) (w : BitVec 32) (i0 i : instruction) (es_x : List Weff)
    (D D0 : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ a, a ∈ W → pinnedRead σ (paZ a)) →
    fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc 4] ++ es_x) →
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Misa_C (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- (a) the text word, IN THE CONFINED MEMORY, at a 4-aligned pc
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    Sail.BitVec.extractLsb w 15 0 = h →
    isRVC h = true →
    -- (b) the COMPRESSED decode, and the expansion
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode_compressed h) dst = true →
    exec (ext_decode_compressed h) dst = some (i0, dst) →
    (∀ s : ExecSt, goodb0 D0 (execute i0) s = true) →
    (∀ s : ExecSt, exec (execute i0) s = some (.ExecuteAs i, s)) →
    -- (c) the EXPANDED instruction's `execute`, at `execEff`
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg .nextPC
          (BitVec.addInt pc 2)) = some (.Retire_Success (), sExec, es_x) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ es_x) σ := by
  intro hwf hW0 hWp hfp lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal hram htext hsub
    hisRVC hagree hDmi hgood hdec hgood0 hexp hexec
  exact wPEffOfWindow cid _ σ W hwf hW0 hWp hfp
    (WeakFetchRvc.execEffStepOfLeafRvc4St ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ W pc h w i0 i es_x D D0 dst
      lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal hram htext hsub hisRVC hagree hDmi hgood
      hdec hgood0 hexp hexec)

end Weak
