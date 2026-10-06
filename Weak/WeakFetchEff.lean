/-
Weak: **the fetch's own `execEff` reduction** (M4 batch 0b): the register-only
cone at the EMPTY trace, the one effect of the fetch, the chain up to `fetch`,
the funnel's 4-aligned `F_Base` arm, the interrupt gate, the decode bridge, the
`tick_clock` mirror, and the batch-2 recipe `wPEffOfLeafBase`.

Rocq: `iris/WeakFetchEff.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakEffSkel` §6b named two facts between the
step assembly (`execEffRiscvStepBase`) and `WeakCert.wPEff`: (i) the FETCH's
own `execEff` reduction -- the one place a `WEread` is emitted for EVERY
instruction -- and (ii) the `tick_clock` mirror, which turns the assembly's
`riscvStep false` fact into the `∀ tick` shape `WeakCert.wstepConfEff` asks
for.  This file is both, plus the recipe they unlock: `wPEffOfLeafBase`, the
one-statement rule that turns a leaf's (a) text bytes, (b) decode fact and (c)
`execute`'s `execEff` fact into its `wPEff` obligation, with no hand-peeling.
The fetch cannot be DETECTED (`WeakEff.execEffQuietOfEmpty` needs the empty
memory, and the fetch reads the text), and every register-only sub-lemma is
restated at the EMPTY trace (the detector only gives `quietTrace`, which admits
a zero-width write).  WHAT SHIPPED: the 4-aligned `F_Base` arm of
`WeakFunnel.execFetchFlat`; the other three arms (2-aligned `F_Base` -- which
the Lean model, like Rocq's, fetches as TWO halfword reads at `pc ≡ 2 mod 4`
-- and `F_RVC` at either alignment) are NOT mirrored here, and §8's recipe
takes the 4-alignment as an explicit premise.

Sections: §1 the register-only cone at the empty trace; §2 the one effect
(`read_ram` of the text word); §3 the chain `checked_mem_read` → `mem_read` →
`fetch_bytes` → `fetch`; §4 `execEffFetchFlatBase4`; §5 the interrupt gate;
§6 the decode bridge (`goodb0`); §7 the `tick_clock` mirror; §8 the recipe;
§9 the end-to-end check against `WeakCert`'s certificates.

**O2 (owner decision; `Weak/WeakCert.lean` deviation 4).**  The Lean model tags
a fetch `AK_ifetch` (`read_ram .Read_ifetch`), and `WeakInterp.classify` maps it
to the i-cache read `⟨true, false, false⟩` (`WeakFetchEff.wakIfetch`), NOT
Rocq's plain `wak_plain`.  So the fetch's trace element is
`.WEread wakIfetch pc 4` everywhere Rocq has `WEread wak_plain pc 4`
(`notes/weak-port-o2-design.md` §1.5 table).  `wakPlain` itself is kept (Rocq
definition; it is still what walker and data reads classify to).

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below); as `Weak/ExecSC*.lean`
   and `Weak/WeakEffSkel.lean` deviation 1 (`register_lookup r s.(sregs)` ↦
   `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`, `mword n` ↦ `BitVec n`,
   `tt` ↦ `()`, `set_reg` ↦ `ExecSt.setReg`, `subrange_vec_dec w 15 0` ↦
   `Sail.BitVec.extractLsb w 15 0`, `RETIRE_SUCCESS` ↦ `.Retire_Success ()`,
   `add_vec_int` ↦ `BitVec.addInt`, `Defs.catch_early_return` ↦ `SailME.run`);
   the byte window `∀ j < n, s.(mem) !! pa_add a j = Some (nth_byte w j)` ↦
   `BytesAt s a n w`; `dom (mem s) ⊆ W` ↦ `bmDomSub s.mem W`.
2. O2 (above): every fetch trace element is `.WEread WeakFetchEff.wakIfetch …`;
   the read is `read_ram .Read_ifetch` (the Lean-only
   `WeakFetchEff.execEffReadRamIfetch4`).  `WeakFetchEff.execEffReadRamPlain4`
   keeps Rocq's statement (a `Read_plain` read, `wakPlain`) but is not on the
   fetch path.  §9's certificates are stated at the `wakIfetch` element.
3. `exec_eff_within_clint_false`/`_sig_false`: Rocq's `not_in_clint a` /
   `not_in_sig a` are spelled out on `toNat` (`RiscvPtsto`'s definitions;
   `uint` ↦ `toNat`); widths are `Nat`.
4. `hartSupports` is pure in Lean (ExecSC convention): Rocq `exec_eff
   (hartSupports X) s = Some (true, s, [])` ↦ `hartSupports .X = true`; Rocq's
   fuelled `_rec_currentlyEnabled Ext_Zicsr 0 acc` fact is stated on
   `currentlyEnabled .Ext_Zicsr`; `exec_eff_currentlyEnabled_S`'s value is
   `_get_Misa_S (s.regs .misa) == 1#1`.
5. §4: Rocq's `pma_allows_all` is `pma_regions = bootPMA` and `pmp_allows_all`
   is `WeakFunnel.pmpAllowsAll` (as `WeakFunnel.execFetchFlat`); the
   CLINT/SIG side conditions are discharged from `inRam` (Rocq
   `addr_is_ram_not_in_clint`/`_sig`).
6. §5: the section `ExecPendingEff`'s hypotheses are premises.
   `exec_eff_mIE_false`/`_sIE_false` are stated on the Lean model's inline
   `if`/`||` shapes (the Lean model has no `and_boolM`/`or_boolM`,
   `Weak/WeakLeafEffCommon.lean` deviation 2) -- the `mIE`/`sIE` computations
   of `getPendingSet .Machine`.
7. §6: `goodb0` is over Lean's `Outcome` events (as `ExecSC7.goodb`, deviation
   5 there): `goodb` with the `barrier` arm closed.  Rocq `agree_on D s dst`
   (WpDecodeBridge, not in the Lean tree) is inlined as `∀ r, D r = true →
   s.regs r = dst.regs r`.  The Ltac `decode_bridge_eff` is a Lean macro; its
   `vm_compute`s are `decide +kernel` (the `goodb0` Boolean) and `rfl` (the
   `exec` equation, whose state type has no `DecidableEq`), as
   `MachCSL.DecodeBridge`.
8. §8: Rocq `∀ j < 4, addr_is_ram (pa_add pc j)` is `inRam pc 4` (WeakFunnel
   deviation 2); the confined state `MState (wm_regs σ) (wmem_restrict σ W)
   (wm_dev σ)` is `⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩`.  The assembly is
   proved through the Lean-only `WeakFetchEff.execEffStepOfLeafBaseSt` (the
   same statement over an arbitrary state; Rocq's `set sconf`).
9. `wPEffOfLeafBase` / `wPLoadOfLeafBase`: Lean's `wPEff` carries the O2 fetch
   obligation, so they take the extra premise `fetchPin σ es` (as
   `WeakEffSkel.wPEffOfWindow`, its deviation 6).  `wPEffPinOfLeafBase` is
   unchanged (`tracePin` already includes `fetchFresh`).
10. Rocq's `W : _` binder trick (the leaked `Countable` instance) has no Lean
   counterpart: `W : GSet PAddr`.
11. Rocq §10's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `exec_eff_within_clint_false` `execEffWithinClintFalse`,
`exec_eff_within_sig_false` `execEffWithinSigFalse`, `exec_eff_within_htif_false`
`execEffWithinHtifFalse`, `exec_eff_within_htif_w_false` `execEffWithinHtifWFalse`,
`exec_eff_effectivePrivilege_fetch` `execEffEffectivePrivilegeFetch`,
`exec_eff_is_shadow_stack_fetch` `execEffIsShadowStackFetch`,
`exec_eff_translateAddr_identity` `execEffTranslateAddrIdentity`,
`exec_eff_pmaCheck_ram` `execEffPmaCheckRam`, `exec_eff_hartSupports_Ziccif`
`execEffHartSupportsZiccif`, `exec_eff_currentlyEnabled_Ziccif`
`execEffCurrentlyEnabledZiccif`, `wak_plain` `wakPlain`,
`exec_eff_read_ram_plain_4` `WeakFetchEff.execEffReadRamPlain4` (duplicated
name), `avi0_mul4` `WeakFetchEff.avi0Mul4` (duplicated name),
`exec_eff_checked_mem_read_ram` `execEffCheckedMemReadRam`,
`exec_eff_mem_read_fetch` `execEffMemReadFetch`, `exec_eff_fetch_bytes_4`
`execEffFetchBytes4`, `exec_eff_fetch_done` `execEffFetchDone`,
`exec_eff_fetch_flat_base4` `execEffFetchFlatBase4`, `exec_eff_hartSupports_S`
`WeakFetchEff.execEffHartSupportsS` (duplicated name),
`exec_eff_hartSupports_Zicsr` `WeakFetchEff.execEffHartSupportsZicsr`
(duplicated name), `exec_eff_rec_cE_Zicsr` `execEffRecCEZicsr`,
`exec_eff_currentlyEnabled_S` `WeakFetchEff.execEffCurrentlyEnabledS`
(duplicated name), `exec_eff_cE_S_true` `execEffCESTrue`,
`exec_eff_ext_int_some` `execEffExtIntSome`, `exec_eff_read_mip_some`
`execEffReadMipSome`, `exec_eff_mIE_false` `execEffMIEFalse`,
`exec_eff_sIE_false` `execEffSIEFalse`, `exec_eff_getPendingSet_machine_none`
`execEffGetPendingSetMachineNone`, `exec_eff_dispatchInterrupt_machine_none`
`execEffDispatchInterruptMachineNone`, `goodb0` `goodb0`, `goodb0_goodb`
`goodb0Goodb`, `exec_eff_goodb0_congr` `execEffGoodb0Congr`,
`exec_eff_decode_bridge` `execEffDecodeBridge`, `decode_bridge_eff` (Ltac)
`decode_bridge_eff` (macro), `exec_eff_bind_None` `execEffBindNone`,
`exec_eff_riscv_step_tick` `execEffRiscvStepTick`,
`exec_eff_riscv_step_all_ticks` `execEffRiscvStepAllTicks`,
`exec_eff_should_inc_minstret_Some` `execEffShouldIncMinstretSome`,
`align4_align2` `align4Align2`, `exec_eff_step_of_leaf_base`
`execEffStepOfLeafBase`, `wP_eff_of_leaf_base` `wPEffOfLeafBase`,
`wP_eff_pin_of_leaf_base` `wPEffPinOfLeafBase`, `wcert_load_base4`
`wcertLoadBase4`, `wcert_store_base4` `wcertStoreBase4`, `wcert_amo_aq_base4`
`wcertAmoAqBase4`, `wcert_amo_aq_pin_base4` `wcertAmoAqPinBase4`,
`wP_load_of_leaf_base` `wPLoadOfLeafBase`.  Lean-only (file-qualified):
`WeakFetchEff.wakIfetch`, `WeakFetchEff.classifyIfetchWak`, `WeakFetchEff.execEffReadRamIfetch4`,
`WeakFetchEff.execEffFetchBytesOk`, `WeakFetchEff.execEffFetch4`,
`WeakFetchEff.saLookup`, `WeakFetchEff.execEffStepOfLeafBaseSt`, and one
`example` exercising `decode_bridge_eff`.

**Dropped:** nothing -- every Rocq definition and lemma has a Lean twin (46
Rocq `Definition`/`Fixpoint`/`Lemma`s, one of them `Local`, + 1 `Ltac`; Lean 46
+ 1 macro + 7 Lean-only).

**Statements checked** (by hand, against Rocq): all; the changed ones are
listed under the deviations.
-/
import Weak.WeakFunnel
import Weak.WeakTickEff
import Weak.WeakPmpEff
import Weak.WeakLeafEff8

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE REGISTER-ONLY CONE, AT THE EMPTY TRACE -/

/-- Rocq `exec_eff_within_clint_false` (deviation 3). -/
theorem execEffWithinClintFalse (a : BitVec 64) (w : Nat) (s : ExecSt)
    (hnc : a.toNat < plat_clint_base.toNat ∨ plat_clint_base.toNat + plat_clint_size.toNat ≤ a.toNat)
    (hw : 0 < w) :
    execEff (within_clint (.Physaddr a) w) s = some (false, s, []) := by
  have h : within_clint (.Physaddr a) w = pure false := by
    rw [plat_clint_base_eq, plat_clint_size_eq] at hnc
    simp only [within_clint, plat_have_clint, plat_clint_base_eq, plat_clint_size_eq, Sail.BitVec.toNatInt,
      Functions.not, Bool.not_true, Bool.false_eq_true, if_false]
    congr 1
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_le, Int.ofNat_eq_natCast]
    bv_omega
  rw [h]
  rfl

/-- Rocq `exec_eff_within_sig_false` (deviation 3; the premises are unused, the
platform has no SIG window). -/
theorem execEffWithinSigFalse (a : BitVec 64) (w : Nat) (s : ExecSt)
    (_hns : a.toNat < plat_sig_base.toNat ∨ plat_sig_base.toNat + plat_sig_size.toNat ≤ a.toNat)
    (_hw : 0 < w) :
    execEff (within_sig (.Physaddr a) w) s = some (false, s, []) := by
  first
  | rfl
  | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)

/-- Rocq `exec_eff_within_htif_false`. -/
theorem execEffWithinHtifFalse (a : BitVec 64) (w : Nat) (s : ExecSt)
    (hn : s.regs .htif_tohost_base = none) :
    execEff (within_htif_readable (.Physaddr a) w) s = some (false, s, []) := by
  unfold within_htif_readable within_htif_writable
  exec_eff_run [hn]

/-- Rocq `exec_eff_within_htif_w_false`: the WRITE twin, the gate every
store/AMO leaf probes. -/
theorem execEffWithinHtifWFalse (a : BitVec 64) (w : Nat) (s : ExecSt)
    (hn : s.regs .htif_tohost_base = none) :
    execEff (within_htif_writable (.Physaddr a) w) s = some (false, s, []) := by
  unfold within_htif_writable
  exec_eff_run [hn]

/-- Rocq `exec_eff_effectivePrivilege_fetch`. -/
theorem execEffEffectivePrivilegeFetch (m : BitVec 64) (p : Privilege) (s : ExecSt) :
    execEff (effectivePrivilege (.InstructionFetch ()) m p) s = some (p, s, []) := rfl

/-- Rocq `exec_eff_is_shadow_stack_fetch`. -/
theorem execEffIsShadowStackFetch (s : ExecSt) :
    execEff (is_shadow_stack_access (.InstructionFetch ())) s = some (false, s, []) := rfl

/-- Rocq `exec_eff_translateAddr_identity`: at Machine, a fetch translates to
itself. -/
theorem execEffTranslateAddrIdentity (a : BitVec 64) (s : ExecSt)
    (hcp : s.regs .cur_privilege = .Machine) :
    execEff (translateAddr (.Virtaddr a) (.InstructionFetch ())) s =
      some (.Ok (.Physaddr (zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr a))), .PBMT_PMA,
        init_ext_ptw), s, []) := by
  unfold translateAddr
  rw [execEffCatchEarlyReturn]
  exec_eff_run [hcp, execEffEffectivePrivilegeFetch, execEffTranslationModeM, execEffIsShadowStackFetch]

/-- Rocq `exec_eff_pmaCheck_ram`. -/
theorem execEffPmaCheckRam (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (halign : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hexec : (override_PMA region.attributes pbmt).executable = true) :
    execEff (pmaCheck (.Physaddr addr) 4 (.InstructionFetch ()) pbmt false) s =
      some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hmatch hexec (execEffIsMagApplicableFetch 4 s) halign

/-- Rocq `exec_eff_hartSupports_Ziccif` (deviation 4). -/
theorem execEffHartSupportsZiccif : hartSupports .Ext_Ziccif = true := by decide +kernel

/-- Rocq `exec_eff_currentlyEnabled_Ziccif`. -/
theorem execEffCurrentlyEnabledZiccif (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Ziccif) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsZiccif, execEffReturnm]

/-! ## 2. THE ONE EFFECT: `read_ram` at width 4 (deviation 2) -/

/-- Rocq `wak_plain`: the plain read class (walker and data reads). -/
def wakPlain : AkInfo := ⟨false, false, false⟩

/-- O2 (Lean-only): the i-cache read class, what `classify` makes of the
fetch's `AK_ifetch`. -/
def WeakFetchEff.wakIfetch : AkInfo := ⟨true, false, false⟩

theorem WeakFetchEff.classifyIfetchWak : classify (.AK_ifetch ()) = WeakFetchEff.wakIfetch := rfl

/-- Rocq `exec_eff_read_ram_plain_4` (duplicated name; deviation 2: Rocq's
statement, not on the Lean fetch path). -/
theorem WeakFetchEff.execEffReadRamPlain4 (addr : BitVec 64) (w : BitVec 32) (s : ExecSt)
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    execEff (read_ram .Read_plain (.Physaddr addr) 4 false) s =
      some ((w, default_meta), s, [.WEread wakPlain addr 4]) := by
  have hr : bmRead s.mem addr 4 = some w := bmRead_of_bytes _ _ _ _ hb
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  unfold read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read
  exec_eff_run [hm, hr]
  rfl

/-- THE fetch's one trace element (Lean-only, O2): the text word read as an
i-cache read. -/
theorem WeakFetchEff.execEffReadRamIfetch4 (addr : BitVec 64) (w : BitVec 32) (s : ExecSt)
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    execEff (read_ram .Read_ifetch (.Physaddr addr) 4 false) s =
      some ((w, default_meta), s, [.WEread WeakFetchEff.wakIfetch addr 4]) := by
  have hr : bmRead s.mem addr 4 = some w := bmRead_of_bytes _ _ _ _ hb
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  unfold read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read
  exec_eff_run [hm, hr]
  rfl

/-! ## 3. THE CHAIN, replayed -/

/-- Rocq `avi0_mul4` (duplicated name; a Rocq `Local` restatement). -/
theorem WeakFetchEff.avi0Mul4 (a : BitVec 64) : Sail.BitVec.addInt a (0 * 4) = a := by
  simp [Sail.BitVec.addInt]

/-- Rocq `exec_eff_checked_mem_read_ram` (deviation 2). -/
theorem execEffCheckedMemReadRam (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.InstructionFetch ()) .Machine) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (halign : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hexec : (override_PMA region.attributes pbmt).executable = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    execEff (checked_mem_read (.InstructionFetch ()) pbmt .Machine (.Physaddr addr) 4 false false false false) s =
      some (.Ok (w, default_meta), s, [.WEread WeakFetchEff.wakIfetch addr 4]) := by
  have hpma := execEffPmaCheckRam addr pbmt region s hmatch halign hexec
  have hmm := execEffWithinMmioReadableFalse addr 4 s hc hsig hh
  have hrr := WeakFetchEff.execEffReadRamIfetch4 addr w s hdev hb
  unfold checked_mem_read check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  exec_eff_mem [hpma]
  exec_eff_mem [hpmp, hmm, hrr, read_kind_of_flags]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
  congr
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  bv_decide

/-- Rocq `exec_eff_mem_read_fetch`. -/
theorem execEffMemReadFetch (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 4 (.InstructionFetch ()) .Machine) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (halign : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hexec : (override_PMA region.attributes pbmt).executable = true)
    (hc : execEff (within_clint (.Physaddr addr) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 4) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w)
    (hpriv : s.regs .cur_privilege = .Machine) :
    execEff (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) 4 false false false) s =
      some (.Ok w, s, [.WEread WeakFetchEff.wakIfetch addr 4]) := by
  have hck := execEffCheckedMemReadRam pbmt addr region w s hpmp hmatch halign hexec hc hsig hh hdev hb
  unfold mem_read mem_read_priv mem_read_priv_meta
  exec_eff_run [hpriv, execEffEffectivePrivilegeFetch, hck]
  first
  | rfl
  | simp only [Nat.reduceMul, BitVec.setWidth_eq]

/-- A chunk whose translation and read succeed, at `execEff` (Lean-only; the
twin of `ExecSC5.execFetchBytesOk`). -/
theorem WeakFetchEff.execEffFetchBytesOk (fs gs pa : BitVec 64) (n : Nat) (pbmt : page_based_mem_type)
    (w : BitVec (8 * n)) (s s1 : ExecSt) (es : List Weff)
    (htr : execEff (translateAddr (.Virtaddr gs) (.InstructionFetch ())) s =
      some (.Ok (.Physaddr pa, pbmt, ()), s1, []))
    (hmr : execEff (mem_read (.InstructionFetch ()) pbmt (.Physaddr pa) n false false false) s1 =
      some (.Ok w, s1, es)) :
    execEff (fetch_bytes fs gs n) s = some (.FetchBytes_Success w, s1, es) := by
  unfold fetch_bytes ext_fetch_check_pc
  rw [execEffCatchEarlyReturn]
  exec_eff_run [htr, hmr]

/-- Rocq `exec_eff_fetch_bytes_4`. -/
theorem execEffFetchBytes4 (pc : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (hpriv : s.regs .cur_privilege = .Machine)
    (hpmp : execEff (pmpCheck (.Physaddr (fetchPa pc)) 4 (.InstructionFetch ()) .Machine) s =
      some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (fetchPa pc)) 4 = some region)
    (hexec : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : execEff (within_clint (.Physaddr (fetchPa pc)) 4) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (fetchPa pc)) 4) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr (fetchPa pc)) 4) s = some (false, s, []))
    (hdev : devAddr (fetchPa pc) = false) (hb : BytesAt s (fetchPa pc) 4 w)
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = true) :
    execEff (fetch_bytes pc pc 4) s =
      some (.FetchBytes_Success w, s, [.WEread WeakFetchEff.wakIfetch (fetchPa pc) 4]) := by
  have halign : is_aligned_paddr (.Physaddr (fetchPa pc)) 4 = true := by rw [fetchPa_eq]; exact hvalign
  exact WeakFetchEff.execEffFetchBytesOk pc pc (fetchPa pc) 4 .PBMT_PMA w s s _
    (execEffTranslateAddrIdentity pc s hpriv)
    (execEffMemReadFetch .PBMT_PMA (fetchPa pc) region w s hpmp hmatch halign hexec hc hsig hh hdev hb hpriv)

/-- A 4-aligned fetch whose word read succeeds, at `execEff` (Lean-only; the
twin of `ExecSC5.execFetch4`). -/
theorem WeakFetchEff.execEffFetch4 (pc : BitVec 64) (w : BitVec 32) (s s1 : ExecSt) (es : List Weff)
    (hpc : s.regs .PC = pc) (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = true)
    (hfb : execEff (fetch_bytes pc pc 4) s = some (.FetchBytes_Success w, s1, es)) :
    execEff (fetch ()) s = some (if isRVC (Sail.BitVec.extractLsb w 15 0) then
      .F_RVC (Sail.BitVec.extractLsb w 15 0) else .F_Base w, s1, es) := by
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execEffCatchEarlyReturn]
  cases hr : isRVC (Sail.BitVec.extractLsb w 15 0) <;>
  exec_eff_run [hpc, bit0ClearOfAligned4 pc hvalign, bit1ClearOfAligned4 pc hvalign, hvalign,
    execEffCurrentlyEnabledZiccif, hfb, hr]

/-- Rocq `exec_eff_fetch_done`: everything above `fetch_bytes` is PC reads and
extension probes, hence trace-free; the whole fetch's trace is the ONE
text-word read. -/
theorem execEffFetchDone (pc : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
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
    (hnotRVC : isRVC (Sail.BitVec.extractLsb w 15 0) = false) :
    execEff (fetch ()) s = some (.F_Base w, s, [.WEread WeakFetchEff.wakIfetch (fetchPa pc) 4]) := by
  rw [WeakFetchEff.execEffFetch4 pc w s s _ hpcPC hvalign
    (execEffFetchBytes4 pc region w s hpriv hpmp hmatch hexec hc hsig hh hdev hb hvalign), hnotRVC]
  rfl

/-! ## 4. THE FUNNEL'S FETCH, AT `execEff` -- the 4-aligned `F_Base` arm

`WeakFunnel.execFetchFlat` dispatches on the alignment and on the
`FetchResult` constructor; THIS mirror covers the 4-aligned `F_Base` arm only
(every 4-aligned 32-bit instruction, the funnel's main case).  The other three
arms emit DIFFERENT traces (two 2-byte reads for the split fetch) and are not
mirrored; §8 takes the 4-alignment as a premise. -/

/-- Rocq `exec_eff_fetch_flat_base4` (deviation 5). -/
theorem execEffFetchFlatBase4 (t : ExecSt) (pc : BitVec 64) (w : BitVec 32) :
    pmpAllowsAll (t.regs .pmpcfg_n) →
    t.regs .pma_regions = bootPMA →
    t.regs .PC = pc →
    t.regs .cur_privilege = .Machine →
    t.regs .htif_tohost_base = none →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    fetchFlatOk t pc (.F_Base w) →
    execEff (fetch ()) t = some (.F_Base w, t, [.WEread WeakFetchEff.wakIfetch pc 4]) := by
  rintro hpmp hpma lpc lpriv lhtif hal ⟨_, hram, w0, hr, hbytes⟩
  obtain ⟨rfl, hnotRVC⟩ := hr
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
  have hf := execEffFetchDone pc ramRegion w t lpc lpriv
    (execEffPmpCheckMachineUnlockedIfetch4 (fetchPa pc) t hpmp halign) hmatch ramRegionExec hc hsig
    (execEffWithinHtifFalse _ 4 t lhtif) (by rw [fetchPa_eq]; exact devAddrRam pc 4 hram) hb hal hnotRVC
  rw [fetchPa_eq] at hf
  exact hf

/-! ## 5. THE INTERRUPT GATE, AT THE EMPTY TRACE

`RiscvTryStep`'s section `ExecPending` replayed (deviation 6).  Everything here
reads registers only, so every trace is `[]`. -/

/-- Rocq `exec_eff_hartSupports_S` (duplicated name; deviation 4). -/
theorem WeakFetchEff.execEffHartSupportsS : hartSupports .Ext_S = true := by decide +kernel

/-- Rocq `exec_eff_hartSupports_Zicsr` (duplicated name; deviation 4). -/
theorem WeakFetchEff.execEffHartSupportsZicsr : hartSupports .Ext_Zicsr = true := by decide +kernel

/-- Rocq `exec_eff_rec_cE_Zicsr` (deviation 4: no fuel). -/
theorem execEffRecCEZicsr (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Zicsr) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [WeakFetchEff.execEffHartSupportsZicsr, execEffReturnm]

/-- Rocq `exec_eff_currentlyEnabled_S` (duplicated name; deviation 4). -/
theorem WeakFetchEff.execEffCurrentlyEnabledS (s : ExecSt) :
    execEff (currentlyEnabled .Ext_S) s = some (_get_Misa_S (s.regs .misa) == 1#1, s, []) :=
  WeakLeafEffCommon.execEffCurrentlyEnabledS s

/-- Rocq `exec_eff_cE_S_true`. -/
theorem execEffCESTrue (s : ExecSt) (hmisaS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    execEff (currentlyEnabled .Ext_S) s = some (true, s, []) := by
  rw [WeakFetchEff.execEffCurrentlyEnabledS, hmisaS]

/-- Rocq `exec_eff_ext_int_some`. -/
theorem execEffExtIntSome (s : ExecSt) (hmisaS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    ∃ ev, execEff (external_interrupts_pending ()) s = some (ev, s, []) := by
  unfold external_interrupts_pending
  exec_eff_run [execEffCESTrue s hmisaS]
  exact ⟨_, rfl⟩

/-- Rocq `exec_eff_read_mip_some`. -/
theorem execEffReadMipSome (s : ExecSt) (hmisaS : (_get_Misa_S (s.regs .misa) == 1#1) = true) :
    ∃ v, execEff (read_mip .IncludePlatformInterrupts) s = some (v, s, []) := by
  obtain ⟨ev, hext⟩ := execEffExtIntSome s hmisaS
  unfold read_mip
  exec_eff_run [hext]
  exact ⟨_, rfl⟩

/-- Rocq `exec_eff_mIE_false` (deviation 6: the Lean model's inline shape). -/
theorem execEffMIEFalse (s : ExecSt) (hmIE : (_get_Mstatus_MIE (s.regs .mstatus) == 1#1) = false) :
    execEff ((if (Privilege.Machine == Privilege.Machine) = true then
        (readReg .mstatus >>= fun w => pure (_get_Mstatus_MIE w == 1#1)) else pure false) >>=
      fun b => (pure (b || ((Privilege.Machine == Privilege.Supervisor) ||
        (Privilege.Machine == Privilege.User))) : SailM Bool)) s = some (false, s, []) := by
  exec_eff_run [hmIE]
  rfl

/-- Rocq `exec_eff_sIE_false` (deviation 6: the Lean model's inline shape). -/
theorem execEffSIEFalse (s : ExecSt) :
    execEff ((if (Privilege.Machine == Privilege.Supervisor) = true then
        (readReg .mstatus >>= fun w => pure (_get_Mstatus_SIE w == 1#1)) else pure false) >>=
      fun b => (pure (b || (Privilege.Machine == Privilege.User)) : SailM Bool)) s =
      some (false, s, []) := by
  exec_eff_run
  rfl

/-- Rocq `exec_eff_getPendingSet_machine_none`. -/
theorem execEffGetPendingSetMachineNone (s : ExecSt)
    (hmisaS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (hmIE : (_get_Mstatus_MIE (s.regs .mstatus) == 1#1) = false) :
    execEff (getPendingSet .Machine) s = some (none, s, []) := by
  obtain ⟨mipv, hmip⟩ := execEffReadMipSome s hmisaS
  have hmm : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hms : (Privilege.Machine == Privilege.Supervisor) = false := rfl
  have hmu : (Privilege.Machine == Privilege.User) = false := rfl
  unfold getPendingSet
  exec_eff_run [execEffCESTrue s hmisaS, hmip, hmm, hms, hmu, hmIE, Bool.or_false, Bool.false_or]

/-- Rocq `exec_eff_dispatchInterrupt_machine_none`. -/
theorem execEffDispatchInterruptMachineNone (s : ExecSt)
    (hmisaS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (hmIE : (_get_Mstatus_MIE (s.regs .mstatus) == 1#1) = false) :
    execEff (dispatchInterrupt .Machine) s = some (none, s, []) :=
  execEffDispatchInterruptNone _ s (execEffGetPendingSetMachineNone s hmisaS hmIE)

/-! ## 6. THE REGISTER-ONLY BRIDGE -- a leaf's DECODE fact at `execEff`

`ExecSC7.goodb` is a SYNTACTIC witness that a run performs no memory outcome;
its one gap here is the `barrier` arm (read-only, but it emits a `WEbar`).
`goodb0` closes that arm; `goodb0Goodb` says it is strictly stronger. -/

/-- Rocq `goodb0` (deviation 7): `goodb` with the `barrier` arm closed. -/
def goodb0 (D : Register → Bool) {X : Type} : SailM X → ExecSt → Bool
  | .pure _, _ => true
  | .impure (.error _) _, _ => false
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => D r && goodb0 D (k (s.regs r)) s
    | .instrAnnounce _ _, k => goodb0 D (k ()) s
    | .branchAnnounce _ _, k => goodb0 D (k ()) s
    | .cacheOp _, k => goodb0 D (k ()) s
    | .tlbi _, k => goodb0 D (k ()) s
    | .takeException _, k => goodb0 D (k ()) s
    | .returnException _, k => goodb0 D (k ()) s
    | .translationStart _, k => goodb0 D (k ()) s
    | .translationEnd _, k => goodb0 D (k ()) s
    | .cycleCount, k => goodb0 D (k ()) s
    | .message _, k => goodb0 D (k ()) s
    | .getCycleCount, k => goodb0 D (k (0 : Nat)) s
    | _, _ => false

/-- Rocq `goodb0_goodb`. -/
theorem goodb0Goodb (D : Register → Bool) {X : Type} (m : SailM X) (s : ExecSt) :
    goodb0 D m s = true → goodb D m s = true := by
  induction m generalizing s with
  | pure x => intro _; rfl
  | impure call k ih =>
    intro hg
    cases call with
    | error e => simp [goodb0] at hg
    | ok o =>
      cases o <;> simp only [goodb0] at hg <;> simp only [goodb] <;> first
        | exact ih _ s hg
        | exact absurd hg (by decide)
        | skip
      case regRead r =>
        simp only [Bool.and_eq_true] at hg ⊢
        exact ⟨hg.1, ih _ s hg.2⟩

/-- Rocq `exec_eff_goodb0_congr`: the read-frame congruence of
`ExecSC7.execGoodbCongr`, at `execEff`, with the empty trace. -/
theorem execEffGoodb0Congr (D : Register → Bool) {X : Type} (m : SailM X) (s1 s2 : ExecSt) :
    (∀ r, D r = true → s1.regs r = s2.regs r) →
    goodb0 D m s1 = true →
    ∃ x, execEff m s1 = some (x, s1, []) ∧ execEff m s2 = some (x, s2, []) := by
  intro hag
  induction m with
  | pure x => intro _; exact ⟨x, rfl, rfl⟩
  | impure call k ih =>
    intro hg
    cases call with
    | error e => simp [goodb0] at hg
    | ok o =>
      cases o <;> simp only [goodb0] at hg <;> first
        | (obtain ⟨x, h1, h2⟩ := ih _ hg; exact ⟨x, h1, h2⟩)
        | exact absurd hg (by decide)
        | skip
      case regRead r =>
        simp only [Bool.and_eq_true] at hg
        obtain ⟨x, h1, h2⟩ := ih _ hg.2
        refine ⟨x, h1, ?_⟩
        show execEff (k (s2.regs r)) s2 = _
        rw [← hag r hg.1]
        exact h2

/-- Rocq `exec_eff_decode_bridge` (deviation 7: `agree_on` inlined): THE
bridge a batch-2 leaf applies. -/
theorem execEffDecodeBridge (D : Register → Bool) {X : Type} (m : SailM X) (dst s : ExecSt) (i : X) :
    (∀ r, D r = true → s.regs r = dst.regs r) →
    goodb0 D m dst = true →
    exec m dst = some (i, dst) →
    execEff m s = some (i, s, []) := by
  intro hag hgood hdst
  obtain ⟨x, hd, hs⟩ := execEffGoodb0Congr D m dst s (fun r hD => (hag r hD).symm) hgood
  have hd' := execEffExec _ _ _ _ _ hd
  rw [hdst] at hd'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hd')
  exact hs

/-- Rocq's Ltac `decode_bridge_eff` (deviation 7): the decode files' recipe at
`execEff`. -/
syntax "decode_bridge_eff" term:max term:max : tactic
macro_rules
  | `(tactic| decode_bridge_eff $D $dst) => `(tactic|
      (refine execEffDecodeBridge $D _ $dst _ _ ?_ ?_ ?_
       · assumption
       · first | decide +kernel | rfl
       · rfl))

example (s dst : ExecSt) (hag : ∀ r, (fun _ => false) r = true → s.regs r = dst.regs r) :
    execEff (pure (3 : Nat) : SailM Nat) s = some (3, s, []) := by
  decode_bridge_eff (fun _ => false) dst

/-! ## 7. THE `tick_clock` MIRROR -- `riscvStep false` to `∀ tick` -/

/-- Rocq `exec_eff_bind_None`. -/
theorem execEffBindNone {X Y : Type} (m : SailM X) (f : X → SailM Y) (s : ExecSt) :
    execEff m s = none → execEff (m >>= f) s = none := by
  intro hm
  rw [execEffBindEq, hm]
  rfl

/-- Rocq `exec_eff_riscv_step_tick`. -/
theorem execEffRiscvStepTick (s s' s'' : ExecSt) (es : List Weff) :
    execEff (riscvStep false) s = some ((), s', es) →
    execEff (tick_clock ()) s' = some ((), s'', []) →
    execEff (riscvStep true) s = some ((), s'', es) := by
  intro h1 h2
  unfold riscvStep at h1 ⊢
  rw [execEffBindEq] at h1 ⊢
  rcases h : execEff (try_step 0 false) s with _ | ⟨b, s1, es1⟩
  · rw [h] at h1
    exact absurd h1 (by simp [effThen])
  · rw [h] at h1
    have e : s1 = s' ∧ es1 = es := by
      simpa [effThen, execEffReturnm] using h1
    obtain ⟨rfl, rfl⟩ := e
    simp [effThen, h2]

/-- Rocq `exec_eff_riscv_step_all_ticks`: the shape `WeakCert.wstepConfEff`
asks for, from the ONE `riscvStep false` fact. -/
theorem execEffRiscvStepAllTicks (s t0 : ExecSt) (es : List Weff) :
    execEff (riscvStep false) s = some ((), t0, es) →
    ∀ tick : Bool, ∃ t' : ExecSt, execEff (riscvStep tick) s = some ((), t', es) ∧ t'.mem = t0.mem := by
  intro h0 tick
  cases tick
  · exact ⟨t0, h0, rfl⟩
  · obtain ⟨c, ti, p, htick⟩ := execEffTickClock t0
    exact ⟨_, execEffRiscvStepTick s t0 _ es h0 htick, rfl⟩

/-- Rocq `exec_eff_should_inc_minstret_Some`. -/
theorem execEffShouldIncMinstretSome (priv : Privilege) (s : ExecSt) :
    ∃ b : Bool, execEff (should_inc_minstret priv) s = some (b, s, []) := by
  unfold should_inc_minstret
  wte_run
  split <;> exact ⟨_, rfl⟩

/-! ## 8. `wPEffOfLeafBase` -- THE BATCH-2 RECIPE, IN ONE STATEMENT -/

/-- Rocq `align4_align2`. -/
theorem align4Align2 (pc : BitVec 64) :
    is_aligned_vaddr (.Virtaddr pc) 4 = true → is_aligned_vaddr (.Virtaddr pc) 2 = true := by
  intro h
  have := isAlignedVaddrMod pc 4 (by decide) h
  exact is_aligned_vaddr_of pc 2 (by omega)

/-- A register other than `minstret_increment` survives the wrapper's pre-write
(Lean-only). -/
theorem WeakFetchEff.saLookup (r : Register) (s : ExecSt) (b : Bool) (h : r ≠ .minstret_increment) :
    (hartActiveSA s b).regs r = s.regs r :=
  setMiLookup r s b h

/-- The run-assembly half over an arbitrary state (Lean-only, deviation 8):
`execEffStepOfLeafBase` is its instance at the confined state. -/
theorem WeakFetchEff.execEffStepOfLeafBaseSt (s : ExecSt) (W : GSet PAddr)
    (pc : BitVec 64) (w : BitVec 32) (i : instruction) (es_x : List Weff)
    (D : Register → Bool) (dst : ExecSt) :
    s.regs .PC = pc →
    s.regs .cur_privilege = .Machine →
    pmpAllowsAll (s.regs .pmpcfg_n) →
    s.regs .pma_regions = bootPMA →
    s.regs .htif_tohost_base = none →
    s.regs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (s.regs .mstatus) == 1#1) = false →
    (s.regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → s.mem (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    (∀ r, D r = true → s.regs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (i, dst) →
    is_lpad_instruction i = false →
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i) ((s.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 4)) =
        some (.Retire_Success (), sExec, es_x) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    ∀ tick : Bool, ∃ t' : ExecSt,
      execEff (riscvStep tick) s = some ((), t', [.WEread WeakFetchEff.wakIfetch pc 4] ++ es_x) ∧
      bmDomSub t'.mem W := by
  intro lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lelp hal hram htext hnotRVC hagree hDmi hgood hdec
    hnlpad hexec tick
  -- the funnel's own choice of the `minstret_increment` flag
  obtain ⟨b, hsi⟩ := execEffShouldIncMinstretSome (s.regs .cur_privilege) s
  obtain ⟨sExec, hex, hhe, hmie, hdom⟩ := hexec b
  -- every register fact, moved past the `minstret_increment` pre-write
  have lpriv_a : (hartActiveSA s b).regs .cur_privilege = .Machine := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpriv
  have lpc_a : (hartActiveSA s b).regs .PC = pc := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpc
  have lhart_a : (hartActiveSA s b).regs .hart_state = .HART_ACTIVE () := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhart
  have lelp_a : ((hartActiveSA s b).regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lelp
  -- the interrupt gate (§5)
  have hdisp : execEff (dispatchInterrupt .Machine) (hartActiveSA s b) =
      some (none, hartActiveSA s b, []) :=
    execEffDispatchInterruptMachineNone _
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaS)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmIE)
  -- the fetch (§4), at the post-write state: only the MEMORY matters
  have hfetch : execEff (fetch ()) (hartActiveSA s b) =
      some (.F_Base w, hartActiveSA s b, [.WEread WeakFetchEff.wakIfetch pc 4]) :=
    execEffFetchFlatBase4 _ pc w
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpmp)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpma)
      lpc_a lpriv_a
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhtif)
      hal ⟨align4Align2 pc hal, hram, w, ⟨rfl, hnotRVC⟩, htext⟩
  -- the decode, through §6's bridge
  have hdec_a : execEff (ext_decode w) (hartActiveSA s b) = some (i, hartActiveSA s b, []) := by
    refine execEffDecodeBridge D (ext_decode w) dst _ i ?_ hgood hdec
    intro r hD
    have hne : r ≠ .minstret_increment := by
      rintro rfl
      rw [hDmi] at hD
      exact absurd hD (by decide)
    rw [WeakFetchEff.saLookup r s b hne]
    exact hagree r hD
  -- the whole step, from the fetch's trace and the `execute`'s (WeakEffSkel §5)
  have hstep := execEffRiscvStepBase s sExec w i pc b [.WEread WeakFetchEff.wakIfetch pc 4] es_x hsi
    lhart_a lpriv_a hdisp hfetch hdec_a lelp_a hnlpad lpc_a hex hhe hmie
  -- ... at BOTH ticks, with the SAME trace (§7)
  obtain ⟨t', ht', hmt'⟩ := execEffRiscvStepAllTicks s _ _ hstep tick
  refine ⟨t', ht', ?_⟩
  rw [hmt']
  cases b <;> exact hdom

/-- Rocq `exec_eff_step_of_leaf_base`: THE RUN-ASSEMBLY HALF, standalone --
the wrapper, the fetch, the decode bridge and the tick assembled into the
`∀ tick` run fact (pinnedness-free). -/
theorem execEffStepOfLeafBase (σ : Wmstate) (W : GSet PAddr)
    (pc : BitVec 64) (w : BitVec 32) (i : instruction) (es_x : List Weff)
    (D : Register → Bool) (dst : ExecSt) :
    -- the M-mode config tower: the SAME facts `wwpInstr` collects
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- (a) the text word, IN THE CONFINED MEMORY, at a 4-aligned pc
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    -- (b) the DECODE, exactly as the decode library states it
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (i, dst) →
    is_lpad_instruction i = false →
    -- (c) the `execute`'s own `execEff` fact, and its register frame
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg .nextPC
          (BitVec.addInt pc 4)) = some (.Retire_Success (), sExec, es_x) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    -- the per-tick run fact
    ∀ tick : Bool, ∃ t' : ExecSt,
      execEff (riscvStep tick) ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ =
        some ((), t', [.WEread WeakFetchEff.wakIfetch pc 4] ++ es_x) ∧
      bmDomSub t'.mem W :=
  WeakFetchEff.execEffStepOfLeafBaseSt ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ W pc w i es_x D dst

/-- Rocq `wP_eff_of_leaf_base` (deviation 9: the extra O2 premise `fetchPin`):
THE WHOLE-WINDOW PACKAGING, the recipe every owned-data leaf applies. -/
theorem wPEffOfLeafBase (cid : Nat) (σ : Wmstate) (W : GSet PAddr)
    (pc : BitVec 64) (w : BitVec 32) (i : instruction) (es_x : List Weff)
    (D : Register → Bool) (dst : ExecSt) :
    -- the window
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ a, a ∈ W → pinnedRead σ (paZ a)) →
    fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc 4] ++ es_x) →
    -- the M-mode config tower
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    -- (a) the text word
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    -- (b) the decode
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (i, dst) →
    is_lpad_instruction i = false →
    -- (c) the `execute`
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg .nextPC
          (BitVec.addInt pc 4)) = some (.Retire_Success (), sExec, es_x) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    -- the certificate's whole obligation
    wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ es_x) σ := by
  intro hwf hW0 hWp hfp lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lelp hal hram htext hnotRVC hagree
    hDmi hgood hdec hnlpad hexec
  exact wPEffOfWindow cid _ σ W hwf hW0 hWp hfp
    (execEffStepOfLeafBase σ W pc w i es_x D dst lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lelp hal hram
      htext hnotRVC hagree hDmi hgood hdec hnlpad hexec)

/-- Rocq `wP_eff_pin_of_leaf_base`: THE PIN PACKAGING, with the TRACE-KEYED
pinnedness in place of the whole-window premise (the invariant-form AMO
leaf's shape). -/
theorem wPEffPinOfLeafBase (cid : Nat) (σ : Wmstate) (W : GSet PAddr)
    (pc : BitVec 64) (w : BitVec 32) (i : instruction) (es_x : List Weff)
    (D : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    tracePin σ ([.WEread WeakFetchEff.wakIfetch pc 4] ++ es_x) →
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (i, dst) →
    is_lpad_instruction i = false →
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg .nextPC
          (BitVec.addInt pc 4)) = some (.Retire_Success (), sExec, es_x) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    wPEffPin (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ es_x) σ := by
  intro hwf hW0 htp lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lelp hal hram htext hnotRVC hagree
    hDmi hgood hdec hnlpad hexec
  exact wPEffPinOfWindow cid _ σ W hwf hW0 htp
    (execEffStepOfLeafBase σ W pc w i es_x D dst lpc lpriv lpmp lpma lhtif lhart lmisaS lmIE lelp hal hram
      htext hnotRVC hagree hDmi hgood hdec hnlpad hexec)

/-! ## 9. THE END-TO-END CHECK: `WeakCert` certificates at the fetch element
this file produces (`[a] ++ [b]` IS `[a, b]`, so each is one `exact`) -/

/-- Rocq `wcert_load_base4` (deviation 2). -/
theorem wcertLoadBase4 (cid : Nat) (pc : BitVec 64) (akl : AkInfo) (ea : PAddr) :
    akl.akIfetch = false →
    wstepCert cid pc
      (wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread akl ea 4])) (wQLoad ea) :=
  fun hcoh => wcertLoad cid pc WeakFetchEff.wakIfetch pc 4 akl ea hcoh

/-- Rocq `wcert_store_base4` (deviation 2). -/
theorem wcertStoreBase4 (cid : Nat) (pc : BitVec 64) (akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    wstepCert cid pc
      (wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEwrite akw ea 4 v]))
      (wQStore (some cid) ea v) :=
  wcertStore cid pc WeakFetchEff.wakIfetch pc 4 akw ea v

/-- Rocq `wcert_amo_aq_base4` (deviation 2). -/
theorem wcertAmoAqBase4 (cid : Nat) (pc : BitVec 64) (aka akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    aka.akIfetch = false → aka.akSync = true → akw.akLatest = true →
    wstepCert cid pc
      (wPEff (some cid)
        ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread aka ea 4, .WEwrite akw ea 4 v]))
      (wQAmoAq (some cid) ea v) :=
  fun hcoh hsync hlat => wcertAmoAq cid pc WeakFetchEff.wakIfetch pc 4 aka akw ea v hcoh hsync hlat

/-- Rocq `wcert_amo_aq_pin_base4` (deviation 2): the PIN form at the same
fetch element. -/
theorem wcertAmoAqPinBase4 (cid : Nat) (pc : BitVec 64) (aka akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    aka.akIfetch = false → aka.akSync = true → akw.akLatest = true →
    wstepCert cid pc
      (wPEffPin (some cid)
        ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread aka ea 4, .WEwrite akw ea 4 v]))
      (wQAmoAq (some cid) ea v) :=
  fun hcoh hsync hlat => wcertAmoAqPin cid pc WeakFetchEff.wakIfetch pc 4 aka akw ea v hcoh hsync hlat

/-- Rocq `wP_load_of_leaf_base` (deviation 9): the recipe at the LOAD shape,
`exact (wPEffOfLeafBase …)` on the nose. -/
theorem wPLoadOfLeafBase (cid : Nat) (σ : Wmstate) (W : GSet PAddr)
    (pc : BitVec 64) (w : BitVec 32) (i : instruction) (akl : AkInfo) (ea : PAddr)
    (D : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ a, a ∈ W → pinnedRead σ (paZ a)) →
    fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread akl ea 4]) →
    σ.wmRegs .PC = pc →
    σ.wmRegs .cur_privilege = .Machine →
    pmpAllowsAll (σ.wmRegs .pmpcfg_n) →
    σ.wmRegs .pma_regions = bootPMA →
    σ.wmRegs .htif_tohost_base = none →
    σ.wmRegs .hart_state = .HART_ACTIVE () →
    (_get_Misa_S (σ.wmRegs .misa) == 1#1) = true →
    (_get_Mstatus_MIE (σ.wmRegs .mstatus) == 1#1) = false →
    (σ.wmRegs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false →
    is_aligned_vaddr (.Virtaddr pc) 4 = true →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    (∀ r, D r = true → σ.wmRegs r = dst.regs r) →
    D .minstret_increment = false →
    goodb0 D (ext_decode w) dst = true →
    exec (ext_decode w) dst = some (i, dst) →
    is_lpad_instruction i = false →
    (∀ b : Bool, ∃ sExec : ExecSt,
      execEff (execute i)
        (((⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ : ExecSt).setReg .minstret_increment b).setReg .nextPC
          (BitVec.addInt pc 4)) = some (.Retire_Success (), sExec, [.WEread akl ea 4]) ∧
      sExec.regs .hart_state = .HART_ACTIVE () ∧
      sExec.regs .minstret_increment = b ∧
      bmDomSub sExec.mem W) →
    wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 4] ++ [.WEread akl ea 4]) σ :=
  wPEffOfLeafBase cid σ W pc w i _ D dst

end Weak
