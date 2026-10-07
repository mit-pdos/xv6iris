/-
Weak: **the two 2-aligned fetch arms, at `execEff`** (M4 batch 0b gap): the
width-2 memory chain, `fetch` at a pc that is 2- but NOT 4-aligned (`F_RVC`:
one halfword read; `F_Base`: two halfword reads), their `fetchFlatOk`
wrappers, the recipes `wPEffOfLeafBase2` / `wPEffOfLeafRvc2`, and the
certificates at the 2-aligned fetch prefixes.

Rocq: `iris/WeakFetch2.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakFetchEff` mirrors the 4-aligned `F_Base`
arm of `WeakFunnel.execFetchFlat` and `WeakFetchRvc` the `F_RVC` arm at a
4-aligned pc.  This file closes the remaining gap: the two arms at a pc ≡ 2
mod 4, which xv6's kernel text reaches after an odd number of compressed
instructions.
* `F_Base` at a 2-aligned pc performs TWO 2-byte reads (the low half at `pc`,
  then -- `isRVC` of the low half being false -- the high half at `pc + 2`) and
  reassembles the word.  Its trace has TWO elements, and a leaf over it uses
  the `WeakEff.wcert*Gen` family (the 2-element prefix is write-free).
* `F_RVC` at a 2-aligned pc performs ONE 2-byte read; its trace is a single
  element, so `WeakCert`'s own certificates apply at `nf := 2` verbatim.
Everything register-only is REUSED: the PMP cone (`WeakPmpEff`), the interrupt
gate and the `within_*`/`translateAddr` prefix (`WeakFetchEff` §1/§5), the
`Ext_Zca` probe (`WeakFetchRvc` §1 -- the misaligned-pc guard evaluates it,
which is why both arms take the misa.C bit), the tick (`WeakFetchEff` §7) and
the decode bridge (`WeakFetchEff` §6).  New is the width-2 memory chain at
`execEff` and the two-chunk trace composition.

Sections: §1 the width-2 memory chain; §2 the two fetch arms; §3 the
`fetchFlatOk` wrappers; §4 the recipes; §5 the certificates and the join check.

**Deviations from Rocq.**
1. NAMES / VOCABULARY: the tree's camelCase (map below) and
   `Weak/WeakFetchEff.lean` deviation 1's vocabulary (`register_lookup r
   s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `neq_vec (access_vec_dec pc i) 'b"0" = b` ↦ `(Sail.BitVec.access pc i !=
   0#1) = b`, `subrange_vec_dec w hi lo` ↦ `Sail.BitVec.extractLsb w hi lo`,
   `concat_vec` ↦ `++`, `add_vec_int` ↦ `BitVec.addInt`, `set_reg` ↦
   `ExecSt.setReg`, `RETIRE_SUCCESS` ↦ `.Retire_Success ()`, the byte window ↦
   `BytesAt`, `dom (mem s) ⊆ W` ↦ `bmDomSub s.mem W`, `fetch_pa` ↦ `fetchPa`).
2. O2 (owner decision; `Weak/WeakFetchEff.lean` deviation 2): every fetch trace
   element is `.WEread WeakFetchEff.wakIfetch …` (Rocq `WEread wak_plain …`):
   the chunk read is `read_ram .Read_ifetch` (the Lean-only
   `WeakFetch2.execEffReadRamIfetch2`).  `execEffReadRamPlain2` keeps Rocq's
   statement (a `Read_plain` read, `wakPlain`) but is not on the fetch path.
   `checked_mem_read`/`mem_read`/`fetch_bytes` and both arms emit the
   `wakIfetch` element; §5's certificates are stated at it, and the load/AMO
   certificates' `ak_coh … = false` premise is `….akIfetch = false` (as
   `WeakCert.wcertLoad`).
3. Rocq's section hypotheses (`FetchRVC2Eff`, `FetchFBase2Eff`) are premises;
   the section `Let`s (`addr`, `addrh`, `ilo`, `ihi`) are inlined.
4. §3: Rocq's `pma_allows_all` is `pma_regions = bootPMA` and `pmp_allows_all`
   is `WeakFunnel.pmpAllowsAll` (as `WeakFetchEff.execEffFetchFlatBase4`, its
   deviation 5); the per-chunk PMA/CLINT/SIG/device side conditions are
   discharged from `inRam` through the Lean-only
   `WeakFetch2.execEffFetchBytes2Ram` (Rocq `pma_all_ram`, `addr_is_ram_*`,
   `InstrBytes.align2_*`, `nth_byte_subrange_lo/_hi`, which are inlined there
   as `WeakFunnel.execFetchFlat` does).
5. §4: the extra O2 premise `fetchPin σ es` (as `WeakFetchEff.wPEffOfLeafBase`,
   its deviation 9); `∀ j < 4, addr_is_ram (pa_add pc j)` is `inRam pc 4`; the
   confined state is `⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩`; Rocq's `W : _` is
   `W : GSet PAddr`.  The assemblies are proved through the Lean-only
   `WeakFetch2.execEffStepOfLeafBase2St` / `execEffStepOfLeafRvc2St` (the run
   fact over an arbitrary state, as `WeakFetchEff.execEffStepOfLeafBaseSt`).
6. `exec_eff_fetch_F_Base_2`: Rocq's `concat_vec ihi ilo = w` premise holds
   outright and is dropped (as `ExecSC5.execFetchFBase2`, its deviation 3).
7. Rocq §6's `Print Assumptions` commands are not declarations.

Q10 (owner ruling, Lean-only): §6 — the `noSfAnn` twins of the width-2 `F_RVC` fetch (`WeakFetch2.noSfAnnFetchFlatRvc2` & co.) and of `WeakFetch2.execEffStepOfLeafRvc2St` (`WeakFetch2.noSfAnnStepOfLeafRvc2St`; no word fact: a width-16 announce is never an sfence announce).

**Rocq → Lean name map.**  `exec_eff_pmpCheck_machine_unlocked_ifetch2`
`execEffPmpCheckMachineUnlockedIfetch2`, `exec_eff_read_ram_plain_2`
`execEffReadRamPlain2`, `exec_eff_pmaCheck_ram_2` `execEffPmaCheckRam2`,
`avi0_mul2` `WeakFetch2.avi0Mul2` (a Rocq `Local` restatement of
`RiscvFetchExec`'s, file-qualified defensively), `exec_eff_checked_mem_read_ram_2`
`execEffCheckedMemReadRam2`, `exec_eff_mem_read_fetch_2` `execEffMemReadFetch2`,
`exec_eff_fetch_bytes_2` `execEffFetchBytes2`, `exec_eff_fetch_RVC_2`
`execEffFetchRVC2`, `exec_eff_fetch_F_Base_2` `execEffFetchFBase2`,
`exec_eff_fetch_flat_base2` `execEffFetchFlatBase2`, `exec_eff_fetch_flat_rvc2`
`execEffFetchFlatRvc2`, `wP_eff_of_leaf_base2` `wPEffOfLeafBase2`,
`wP_eff_of_leaf_rvc2` `wPEffOfLeafRvc2`, `nowrite_nil` `nowriteNil`,
`nowrite_fetch2` `nowriteFetch2`, `wcert_load_base2` `wcertLoadBase2`,
`wcert_store_base2` `wcertStoreBase2`, `wcert_amo_aq_base2` `wcertAmoAqBase2`,
`wcert_fence_base2` `wcertFenceBase2`, `wcert_load_rvc2` `wcertLoadRvc2`,
`wcert_store_rvc2` `wcertStoreRvc2`, `wcert_amo_aq_rvc2` `wcertAmoAqRvc2`,
`wP_load_of_leaf_base2` `wPLoadOfLeafBase2`.  Lean-only (file-qualified):
`WeakFetch2.execEffReadRamIfetch2`, `WeakFetch2.execEffFetch2Rvc`,
`WeakFetch2.execEffFetch2Base`,
`WeakFetch2.execEffFetchBytes2Ram`, `WeakFetch2.execEffStepOfLeafBase2St`,
`WeakFetch2.execEffStepOfLeafRvc2St`.

**Dropped:** nothing (Rocq 23 `Lemma`s, one `Local`; Lean 23 + 6 Lean-only).

**Statements checked** (by hand, against Rocq): all; the changed ones are
listed under the deviations.
-/
import Weak.WeakFetchRvc
import Weak.WeakEff

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. THE WIDTH-2 MEMORY CHAIN, with the trace threaded through -/

/-- Rocq `exec_eff_pmpCheck_machine_unlocked_ifetch2`: a 2-byte access at a
2-aligned address stays inside one aligned 4-byte grain cell. -/
theorem execEffPmpCheckMachineUnlockedIfetch2 (addr : BitVec 64) (s : ExecSt)
    (hunl : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hal : is_aligned_paddr (.Physaddr addr) 2 = true) :
    execEff (pmpCheck (.Physaddr addr) 2 (.InstructionFetch ()) .Machine) s = some (none, s, []) := by
  have h2 := isAlignedVaddrMod addr 2 (by decide) hal
  exact execEffPmpCheckMachineUnlocked _ 2 _ s hunl (fun ent => ⟨_, rfl⟩)
    (by show addr.toNat % 4 + (to_bits (l := 64) 2).toNat ≤ 4
        rw [show (to_bits (l := 64) 2).toNat = 2 from rfl]; omega)

/-- Rocq `exec_eff_read_ram_plain_2` (deviation 2: Rocq's statement, not on the
Lean fetch path). -/
theorem execEffReadRamPlain2 (addr : BitVec 64) (w : BitVec 16) (s : ExecSt)
    (hdev : devAddr addr = false) (hb : BytesAt s addr 2 w) :
    execEff (read_ram .Read_plain (.Physaddr addr) 2 false) s =
      some ((w, default_meta), s, [.WEread wakPlain addr 2]) := by
  have hr : bmRead s.mem addr 2 = some w := bmRead_of_bytes _ _ _ _ hb
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  unfold read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read
  exec_eff_run [hm, hr]
  rfl

/-- THE chunk's one trace element (Lean-only, O2): a text halfword read as an
i-cache read. -/
theorem WeakFetch2.execEffReadRamIfetch2 (addr : BitVec 64) (w : BitVec 16) (s : ExecSt)
    (hdev : devAddr addr = false) (hb : BytesAt s addr 2 w) :
    execEff (read_ram .Read_ifetch (.Physaddr addr) 2 false) s =
      some ((w, default_meta), s, [.WEread WeakFetchEff.wakIfetch addr 2]) := by
  have hr : bmRead s.mem addr 2 = some w := bmRead_of_bytes _ _ _ _ hb
  have hm : ∀ k, mmioAcc addr k = false := fun k => by simp [mmioAcc, hdev]
  unfold read_ram LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read PreSail.sail_mem_read
  exec_eff_run [hm, hr]
  rfl

/-- Rocq `exec_eff_pmaCheck_ram_2`. -/
theorem execEffPmaCheckRam2 (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 2 = some region)
    (halign : is_aligned_paddr (.Physaddr addr) 2 = true)
    (hexec : (override_PMA region.attributes pbmt).executable = true) :
    execEff (pmaCheck (.Physaddr addr) 2 (.InstructionFetch ()) pbmt false) s =
      some (.Ok pmaOkAligned, s, []) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  pma_ok_eff_peel hmatch hexec (execEffIsMagApplicableFetch 2 s) halign

/-- Rocq `avi0_mul2` (a Rocq `Local` restatement). -/
theorem WeakFetch2.avi0Mul2 (a : BitVec 64) : Sail.BitVec.addInt a (0 * 2) = a := by
  simp [Sail.BitVec.addInt]

/-- Rocq `exec_eff_checked_mem_read_ram_2` (deviation 2). -/
theorem execEffCheckedMemReadRam2 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 16) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 2 (.InstructionFetch ()) .Machine) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 2 = some region)
    (halign : is_aligned_paddr (.Physaddr addr) 2 = true)
    (hexec : (override_PMA region.attributes pbmt).executable = true)
    (hc : execEff (within_clint (.Physaddr addr) 2) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 2) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 2) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 2 w) :
    execEff (checked_mem_read (.InstructionFetch ()) pbmt .Machine (.Physaddr addr) 2 false false false false) s =
      some (.Ok (w, default_meta), s, [.WEread WeakFetchEff.wakIfetch addr 2]) := by
  have hpma := execEffPmaCheckRam2 addr pbmt region s hmatch halign hexec
  have hmm := execEffWithinMmioReadableFalse addr 2 s hc hsig hh
  have hrr := WeakFetch2.execEffReadRamIfetch2 addr w s hdev hb
  unfold checked_mem_read check_pma_with_pmp_priority
  rw [execEffCatchEarlyReturn]
  exec_eff_mem [hpma]
  exec_eff_mem [hpmp, hmm, hrr, read_kind_of_flags]
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
  congr
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  bv_decide

/-- Rocq `exec_eff_mem_read_fetch_2`. -/
theorem execEffMemReadFetch2 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 16) (s : ExecSt)
    (hpmp : execEff (pmpCheck (.Physaddr addr) 2 (.InstructionFetch ()) .Machine) s = some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 2 = some region)
    (halign : is_aligned_paddr (.Physaddr addr) 2 = true)
    (hexec : (override_PMA region.attributes pbmt).executable = true)
    (hc : execEff (within_clint (.Physaddr addr) 2) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr addr) 2) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr addr) 2) s = some (false, s, []))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 2 w)
    (hpriv : s.regs .cur_privilege = .Machine) :
    execEff (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) 2 false false false) s =
      some (.Ok w, s, [.WEread WeakFetchEff.wakIfetch addr 2]) := by
  have hck := execEffCheckedMemReadRam2 pbmt addr region w s hpmp hmatch halign hexec hc hsig hh hdev hb
  unfold mem_read mem_read_priv mem_read_priv_meta
  exec_eff_run [hpriv, execEffEffectivePrivilegeFetch, hck]
  first
  | rfl
  | simp only [Nat.reduceMul, BitVec.setWidth_eq]

/-- Rocq `exec_eff_fetch_bytes_2`: generalised over the fetched address `pc2`,
so ONE lemma serves the low chunk (`pc2 := pc`) and the high chunk
(`pc2 := pc + 2`) of the split fetch. -/
theorem execEffFetchBytes2 (pc pc2 : BitVec 64) (region : PMA_Region) (w : BitVec 16) (s : ExecSt)
    (hpriv : s.regs .cur_privilege = .Machine)
    (hpmp : execEff (pmpCheck (.Physaddr (fetchPa pc2)) 2 (.InstructionFetch ()) .Machine) s =
      some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (fetchPa pc2)) 2 = some region)
    (halign : is_aligned_paddr (.Physaddr (fetchPa pc2)) 2 = true)
    (hexec : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : execEff (within_clint (.Physaddr (fetchPa pc2)) 2) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (fetchPa pc2)) 2) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr (fetchPa pc2)) 2) s = some (false, s, []))
    (hdev : devAddr (fetchPa pc2) = false) (hb : BytesAt s (fetchPa pc2) 2 w) :
    execEff (fetch_bytes pc pc2 2) s =
      some (.FetchBytes_Success w, s, [.WEread WeakFetchEff.wakIfetch (fetchPa pc2) 2]) :=
  WeakFetchEff.execEffFetchBytesOk pc pc2 (fetchPa pc2) 2 .PBMT_PMA w s s _
    (execEffTranslateAddrIdentity pc2 s hpriv)
    (execEffMemReadFetch2 .PBMT_PMA (fetchPa pc2) region w s hpmp hmatch halign hexec hc hsig hh hdev hb hpriv)

/-! ## 2. THE TWO FETCH ARMS -/

/-- A 2-mod-4 fetch whose halfword is compressed, at `execEff` (Lean-only; the
twin of `ExecSC5.execFetch2Rvc`). -/
theorem WeakFetch2.execEffFetch2Rvc (pc : BitVec 64) (h : BitVec 16) (s s1 : ExecSt) (es : List Weff)
    (hpc : s.regs .PC = pc)
    (hbit0 : (Sail.BitVec.access pc 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access pc 1 != 0#1) = true)
    (hzca : execEff (currentlyEnabled .Ext_Zca) s = some (true, s, []))
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = false)
    (hfb : execEff (fetch_bytes pc pc 2) s = some (.FetchBytes_Success h, s1, es)) (hrvc : isRVC h = true) :
    execEff (fetch ()) s = some (.F_RVC h, s1, es) := by
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execEffCatchEarlyReturn]
  exec_eff_run [hpc, hbit0, hbit1, hzca, hvalign, hfb, hrvc, Functions.not]

/-- A 2-mod-4 fetch of a 32-bit instruction at `execEff`: two halfword chunks,
the second from where the first left the state, the traces joined (Lean-only;
the twin of `ExecSC5.execFetch2Base`). -/
theorem WeakFetch2.execEffFetch2Base (pc : BitVec 64) (lo hi : BitVec 16) (s s1 s2 : ExecSt)
    (es1 es2 : List Weff) (hpc : s.regs .PC = pc)
    (hbit0 : (Sail.BitVec.access pc 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access pc 1 != 0#1) = true)
    (hzca : execEff (currentlyEnabled .Ext_Zca) s = some (true, s, []))
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = false)
    (hfb1 : execEff (fetch_bytes pc pc 2) s = some (.FetchBytes_Success lo, s1, es1)) (hnr : isRVC lo = false)
    (hpc1 : s1.regs .PC = pc)
    (hfb2 : execEff (fetch_bytes pc (BitVec.addInt pc 2) 2) s1 = some (.FetchBytes_Success hi, s2, es2)) :
    execEff (fetch ()) s = some (.F_Base (hi ++ lo), s2, es1 ++ es2) := by
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execEffCatchEarlyReturn]
  exec_eff_run [hpc, hbit0, hbit1, hzca, hvalign, hfb1, hnr, Functions.not, hpc1, hfb2]

/-- Rocq `exec_eff_fetch_RVC_2` (deviations 2, 3). -/
theorem execEffFetchRVC2 (pc : BitVec 64) (region : PMA_Region) (w : BitVec 16) (s : ExecSt)
    (hpcPC : s.regs .PC = pc) (hpriv : s.regs .cur_privilege = .Machine)
    (hpmp : execEff (pmpCheck (.Physaddr (fetchPa pc)) 2 (.InstructionFetch ()) .Machine) s =
      some (none, s, []))
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (fetchPa pc)) 2 = some region)
    (halign : is_aligned_paddr (.Physaddr (fetchPa pc)) 2 = true)
    (hexec : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : execEff (within_clint (.Physaddr (fetchPa pc)) 2) s = some (false, s, []))
    (hsig : execEff (within_sig (.Physaddr (fetchPa pc)) 2) s = some (false, s, []))
    (hh : execEff (within_htif_readable (.Physaddr (fetchPa pc)) 2) s = some (false, s, []))
    (hdev : devAddr (fetchPa pc) = false) (hb : BytesAt s (fetchPa pc) 2 w)
    (hbit0 : (Sail.BitVec.access pc 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access pc 1 != 0#1) = true)
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = false)
    (hmisaC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (hisRVC : isRVC w = true) :
    execEff (fetch ()) s = some (.F_RVC w, s, [.WEread WeakFetchEff.wakIfetch (fetchPa pc) 2]) :=
  WeakFetch2.execEffFetch2Rvc pc w s s _ hpcPC hbit0 hbit1 (execEffCurrentlyEnabledZca s hmisaC) hvalign
    (execEffFetchBytes2 pc pc region w s hpriv hpmp hmatch halign hexec hc hsig hh hdev hb) hisRVC

/-- Rocq `exec_eff_fetch_F_Base_2` (deviations 2, 3, 6): the halves at
`fetchPa pc` and `fetchPa (pc + 2)`. -/
theorem execEffFetchFBase2 (pc : BitVec 64) (regl regh : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (hpcPC : s.regs .PC = pc) (hpriv : s.regs .cur_privilege = .Machine)
    (hpmpl : execEff (pmpCheck (.Physaddr (fetchPa pc)) 2 (.InstructionFetch ()) .Machine) s =
      some (none, s, []))
    (hpmph : execEff (pmpCheck (.Physaddr (fetchPa (BitVec.addInt pc 2))) 2 (.InstructionFetch ()) .Machine) s =
      some (none, s, []))
    (hmatchl : matching_pma_region (s.regs .pma_regions) (.Physaddr (fetchPa pc)) 2 = some regl)
    (hmatchh : matching_pma_region (s.regs .pma_regions) (.Physaddr (fetchPa (BitVec.addInt pc 2))) 2 =
      some regh)
    (halignl : is_aligned_paddr (.Physaddr (fetchPa pc)) 2 = true)
    (halignh : is_aligned_paddr (.Physaddr (fetchPa (BitVec.addInt pc 2))) 2 = true)
    (hexecl : (override_PMA regl.attributes .PBMT_PMA).executable = true)
    (hexech : (override_PMA regh.attributes .PBMT_PMA).executable = true)
    (hcl : execEff (within_clint (.Physaddr (fetchPa pc)) 2) s = some (false, s, []))
    (hsigl : execEff (within_sig (.Physaddr (fetchPa pc)) 2) s = some (false, s, []))
    (hhl : execEff (within_htif_readable (.Physaddr (fetchPa pc)) 2) s = some (false, s, []))
    (hch : execEff (within_clint (.Physaddr (fetchPa (BitVec.addInt pc 2))) 2) s = some (false, s, []))
    (hsigh : execEff (within_sig (.Physaddr (fetchPa (BitVec.addInt pc 2))) 2) s = some (false, s, []))
    (hhh : execEff (within_htif_readable (.Physaddr (fetchPa (BitVec.addInt pc 2))) 2) s =
      some (false, s, []))
    (hdevl : devAddr (fetchPa pc) = false) (hdevh : devAddr (fetchPa (BitVec.addInt pc 2)) = false)
    (hbytesl : BytesAt s (fetchPa pc) 2 (Sail.BitVec.extractLsb w 15 0))
    (hbytesh : BytesAt s (fetchPa (BitVec.addInt pc 2)) 2 (Sail.BitVec.extractLsb w 31 16))
    (hbit0 : (Sail.BitVec.access pc 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access pc 1 != 0#1) = true)
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = false)
    (hmisaC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (hnotRVC : isRVC (Sail.BitVec.extractLsb w 15 0) = false) :
    execEff (fetch ()) s =
      some (.F_Base w, s, [.WEread WeakFetchEff.wakIfetch (fetchPa pc) 2,
        .WEread WeakFetchEff.wakIfetch (fetchPa (BitVec.addInt pc 2)) 2]) := by
  have hf := WeakFetch2.execEffFetch2Base pc _ _ s s s _ _ hpcPC hbit0 hbit1
    (execEffCurrentlyEnabledZca s hmisaC) hvalign
    (execEffFetchBytes2 pc pc regl _ s hpriv hpmpl hmatchl halignl hexecl hcl hsigl hhl hdevl hbytesl) hnotRVC
    hpcPC
    (execEffFetchBytes2 pc (BitVec.addInt pc 2) regh _ s hpriv hpmph hmatchh halignh hexech hch hsigh hhh
      hdevh hbytesh)
  rw [hf]
  congr
  simp only [Sail.BitVec.extractLsb]
  bv_decide

/-! ## 3. THE FUNNEL'S FETCH, AT `execEff` -- the two 2-aligned arms -/

/-- One 2-byte RAM chunk of an M-mode fetch, at `execEff`, with every side
condition discharged from `inRam` (Lean-only; deviation 4). -/
theorem WeakFetch2.execEffFetchBytes2Ram (pc pc2 : BitVec 64) (h : BitVec 16) (t : ExecSt)
    (hpriv : t.regs .cur_privilege = .Machine) (hpmp : pmpAllowsAll (t.regs .pmpcfg_n))
    (hpma : t.regs .pma_regions = bootPMA) (hhtif : t.regs .htif_tohost_base = none)
    (hram : inRam pc2 2) (hb : BytesAt t pc2 2 h) (hal : pc2.toNat % 2 = 0) :
    execEff (fetch_bytes pc pc2 2) t =
      some (.FetchBytes_Success h, t, [.WEread WeakFetchEff.wakIfetch pc2 2]) := by
  have hal' : is_aligned_paddr (.Physaddr (fetchPa pc2)) 2 = true := by
    rw [fetchPa_eq]; exact is_aligned_paddr_of pc2 2 (by decide) hal
  have hsig : execEff (within_sig (.Physaddr (fetchPa pc2)) 2) t = some (false, t, []) := by
    first
    | rfl
    | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)
  have hf := execEffFetchBytes2 pc pc2 ramRegion h t hpriv
    (execEffPmpCheckMachineUnlockedIfetch2 _ t hpmp hal')
    (by rw [hpma, fetchPa_eq]; exact matching_pma_ram pc2 2 hram (by decide) (by decide))
    hal' ramRegionExec
    (by rw [fetchPa_eq, within_clint_ram pc2 2 hram]; rfl)
    hsig (execEffWithinHtifFalse _ 2 t hhtif)
    (by rw [fetchPa_eq]; exact devAddrRam pc2 2 hram)
    (by rw [fetchPa_eq]; exact hb)
  rw [fetchPa_eq] at hf
  exact hf

/-- Rocq `exec_eff_fetch_flat_base2` (deviations 2, 4). -/
theorem execEffFetchFlatBase2 (t : ExecSt) (pc : BitVec 64) (w : BitVec 32) :
    pmpAllowsAll (t.regs .pmpcfg_n) →
    t.regs .pma_regions = bootPMA →
    (_get_Misa_C (t.regs .misa) == 1#1) = true →
    t.regs .PC = pc →
    t.regs .cur_privilege = .Machine →
    t.regs .htif_tohost_base = none →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    fetchFlatOk t pc (.F_Base w) →
    execEff (fetch ()) t =
      some (.F_Base w, t, [.WEread WeakFetchEff.wakIfetch pc 2,
        .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2]) := by
  rintro hpmp hpma hmisaC lpc lpriv lhtif hal ⟨h2, hram, w0, hr, hb⟩
  obtain ⟨rfl, hnotRVC⟩ := hr
  have hm2 : pc.toNat % 2 = 0 := isAlignedVaddrMod pc 2 (by decide) h2
  have hm4 : pc.toNat % 4 = 2 := by
    by_cases hm : pc.toNat % 4 = 0
    · rw [is_aligned_vaddr_of pc 4 hm] at hal; exact absurd hal (by decide)
    · omega
  have hramLo : inRam pc 2 := by unfold inRam at hram ⊢; omega
  have hbLo : BytesAt t pc 2 (Sail.BitVec.extractLsb w 15 0) := by
    intro j hj
    rw [nthByteLo w j hj]
    exact hb j (by omega)
  have hramHi : inRam (Sail.BitVec.addInt pc 2) 2 := by
    rw [addIntTwo]
    have := toNatAddOfRam pc 2 hram (by omega)
    unfold inRam at hram ⊢
    omega
  have hbHi : BytesAt t (Sail.BitVec.addInt pc 2) 2 (Sail.BitVec.extractLsb w 31 16) := by
    intro j hj
    have e : (BitVec.ofNat 64 2 + BitVec.ofNat 64 j) = BitVec.ofNat 64 (2 + j) := by
      rcases j with _ | _ | j
      · rfl
      · rfl
      · omega
    rw [nthByteHi w j hj, addIntTwo, BitVec.add_assoc, e]
    exact hb (2 + j) (by omega)
  have hmHi : (Sail.BitVec.addInt pc 2).toNat % 2 = 0 := by
    rw [addIntTwo, toNatAddOfRam pc 2 hram (by omega)]
    omega
  have hf := WeakFetch2.execEffFetch2Base pc _ _ t t t _ _ lpc (bit0_clear_of_even pc hm2)
    (bit1_set_of_mod4 pc hm4) (execEffCurrentlyEnabledZca t hmisaC) hal
    (WeakFetch2.execEffFetchBytes2Ram pc pc _ t lpriv hpmp hpma lhtif hramLo hbLo hm2) hnotRVC lpc
    (WeakFetch2.execEffFetchBytes2Ram pc _ _ t lpriv hpmp hpma lhtif hramHi hbHi hmHi)
  rw [hf]
  congr
  simp only [Sail.BitVec.extractLsb]
  bv_decide

/-- Rocq `exec_eff_fetch_flat_rvc2` (deviations 2, 4). -/
theorem execEffFetchFlatRvc2 (t : ExecSt) (pc : BitVec 64) (h : BitVec 16) :
    pmpAllowsAll (t.regs .pmpcfg_n) →
    t.regs .pma_regions = bootPMA →
    (_get_Misa_C (t.regs .misa) == 1#1) = true →
    t.regs .PC = pc →
    t.regs .cur_privilege = .Machine →
    t.regs .htif_tohost_base = none →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    fetchFlatOk t pc (.F_RVC h) →
    execEff (fetch ()) t = some (.F_RVC h, t, [.WEread WeakFetchEff.wakIfetch pc 2]) := by
  rintro hpmp hpma hmisaC lpc lpriv lhtif hal ⟨h2, hram, w, hr, hb⟩
  obtain ⟨rfl, hisRVC⟩ := hr
  have hm2 : pc.toNat % 2 = 0 := isAlignedVaddrMod pc 2 (by decide) h2
  have hm4 : pc.toNat % 4 = 2 := by
    by_cases hm : pc.toNat % 4 = 0
    · rw [is_aligned_vaddr_of pc 4 hm] at hal; exact absurd hal (by decide)
    · omega
  have hramLo : inRam pc 2 := by unfold inRam at hram ⊢; omega
  have hbLo : BytesAt t pc 2 (Sail.BitVec.extractLsb w 15 0) := by
    intro j hj
    rw [nthByteLo w j hj]
    exact hb j (by omega)
  exact WeakFetch2.execEffFetch2Rvc pc _ t t _ lpc (bit0_clear_of_even pc hm2) (bit1_set_of_mod4 pc hm4)
    (execEffCurrentlyEnabledZca t hmisaC) hal
    (WeakFetch2.execEffFetchBytes2Ram pc pc _ t lpriv hpmp hpma lhtif hramLo hbLo hm2) hisRVC

/-! ## 4. THE RECIPES -- `wPEffOfLeafBase` / `wPEffOfLeafRvc4` at a 2-aligned pc -/

/-- The `F_Base`-at-2 run-assembly half over an arbitrary state (Lean-only,
deviation 5). -/
theorem WeakFetch2.execEffStepOfLeafBase2St (s : ExecSt) (W : GSet PAddr)
    (pc : BitVec 64) (w : BitVec 32) (i : instruction) (es_x : List Weff)
    (D : Register → Bool) (dst : ExecSt) :
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
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
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
      execEff (riscvStep tick) s = some ((), t',
        [.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2] ++ es_x) ∧
      bmDomSub t'.mem W := by
  intro lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hnotRVC hagree hDmi
    hgood hdec hnlpad hexec tick
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
  -- the fetch (§3), at the post-write state: only the MEMORY matters
  have hfetch : execEff (fetch ()) (hartActiveSA s b) =
      some (.F_Base w, hartActiveSA s b,
        [.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2]) :=
    execEffFetchFlatBase2 _ pc w
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpmp)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpma)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaC)
      lpc_a lpriv_a
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhtif)
      hal4 ⟨hal2, hram, w, ⟨rfl, hnotRVC⟩, htext⟩
  have hdec_a : execEff (ext_decode w) (hartActiveSA s b) = some (i, hartActiveSA s b, []) := by
    refine execEffDecodeBridge D (ext_decode w) dst _ i ?_ hgood hdec
    intro r hD
    have hne : r ≠ .minstret_increment := by
      rintro rfl
      rw [hDmi] at hD
      exact absurd hD (by decide)
    rw [WeakFetchEff.saLookup r s b hne]
    exact hagree r hD
  have hstep := execEffRiscvStepBase s sExec w i pc b
    [.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2] es_x hsi
    lhart_a lpriv_a hdisp hfetch hdec_a lelp_a hnlpad lpc_a hex hhe hmie
  obtain ⟨t', ht', hmt'⟩ := execEffRiscvStepAllTicks s _ _ hstep tick
  refine ⟨t', ht', ?_⟩
  rw [hmt']
  cases b <;> exact hdom

/-- Rocq `wP_eff_of_leaf_base2` (deviation 5): `WeakFetchEff.wPEffOfLeafBase`
at a 2-but-not-4-aligned pc, with the misa.C bit and the fetch's two-element
trace. -/
theorem wPEffOfLeafBase2 (cid : Nat) (σ : Wmstate) (W : GSet PAddr)
    (pc : BitVec 64) (w : BitVec 32) (i : instruction) (es_x : List Weff)
    (D : Register → Bool) (dst : ExecSt) :
    -- the window
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ a, a ∈ W → pinnedRead σ (paZ a)) →
    fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2]
      ++ es_x) →
    -- the M-mode config tower
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
    -- (a) the text word, IN THE CONFINED MEMORY, at a 2-not-4-aligned pc
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    inRam pc 4 →
    (∀ j : Nat, j < 4 → wmemRestrict σ W (pc + BitVec.ofNat 64 j) = some (nthByte (n := 4) w j)) →
    isRVC (Sail.BitVec.extractLsb w 15 0) = false →
    -- (b) the DECODE
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
    -- the certificate's whole obligation
    wPEff (some cid)
      ([.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2] ++ es_x) σ := by
  intro hwf hW0 hWp hfp lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hnotRVC
    hagree hDmi hgood hdec hnlpad hexec
  exact wPEffOfWindow cid _ σ W hwf hW0 hWp hfp
    (WeakFetch2.execEffStepOfLeafBase2St ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ W pc w i es_x D dst
      lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hnotRVC hagree hDmi hgood
      hdec hnlpad hexec)

/-- The `F_RVC`-at-2 run-assembly half over an arbitrary state (Lean-only,
deviation 5). -/
theorem WeakFetch2.execEffStepOfLeafRvc2St (s : ExecSt) (W : GSet PAddr)
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
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
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
      execEff (riscvStep tick) s = some ((), t', [.WEread WeakFetchEff.wakIfetch pc 2] ++ es_x) ∧
      bmDomSub t'.mem W := by
  intro lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hsub hisRVC hagree hDmi
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
      some (.F_RVC h, hartActiveSA s b, [.WEread WeakFetchEff.wakIfetch pc 2]) :=
    execEffFetchFlatRvc2 _ pc h
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpmp)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpma)
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaC)
      lpc_a lpriv_a
      (by rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhtif)
      hal4 ⟨hal2, hram, w, ⟨hsub, hisRVC⟩, htext⟩
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
  have hstep := execEffRiscvStepRvc s sExec h i0 i pc b [.WEread WeakFetchEff.wakIfetch pc 2] es_x hsi
    lhart_a lpriv_a hdisp hfetch hdec_a lelp_a lpc_a hzca hexp_a hex hhe hmie
  obtain ⟨t', ht', hmt'⟩ := execEffRiscvStepAllTicks s _ _ hstep tick
  refine ⟨t', ht', ?_⟩
  rw [hmt']
  cases b <;> exact hdom

/-- Rocq `wP_eff_of_leaf_rvc2` (deviation 5): `WeakFetchRvc.wPEffOfLeafRvc4` at
a 2-but-not-4-aligned pc, with the fetch's one-element width-2 trace. -/
theorem wPEffOfLeafRvc2 (cid : Nat) (σ : Wmstate) (W : GSet PAddr)
    (pc : BitVec 64) (h : BitVec 16) (w : BitVec 32) (i0 i : instruction) (es_x : List Weff)
    (D D0 : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ a, a ∈ W → pinnedRead σ (paZ a)) →
    fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc 2] ++ es_x) →
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
    -- (a) the text word, IN THE CONFINED MEMORY, at a 2-not-4-aligned pc
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
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
    wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 2] ++ es_x) σ := by
  intro hwf hW0 hWp hfp lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hsub
    hisRVC hagree hDmi hgood hdec hgood0 hexp hexec
  exact wPEffOfWindow cid _ σ W hwf hW0 hWp hfp
    (WeakFetch2.execEffStepOfLeafRvc2St ⟨σ.wmRegs, wmemRestrict σ W, σ.wmDev⟩ W pc h w i0 i es_x D D0 dst
      lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hsub hisRVC hagree hDmi
      hgood hdec hgood0 hexp hexec)

/-! ## 5. THE CERTIFICATES AT THE 2-ALIGNED FETCH PREFIXES, and the join

The split `F_Base` fetch contributes TWO trace elements, so its certificates
are `WeakEff`'s `_gen` family at the 2-element write-free prefix (at `post :=
[]` the `_gen` conclusion IS `prefix ++ es_x` on the nose).  The `F_RVC`-at-2
fetch is ONE element, so `WeakCert`'s own certificates apply at `nf := 2`. -/

/-- Rocq `nowrite_nil`. -/
theorem nowriteNil : nowriteTrace [] := fun _ he => by cases he

/-- Rocq `nowrite_fetch2` (deviation 2). -/
theorem nowriteFetch2 (pc : BitVec 64) :
    nowriteTrace [.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2] := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> trivial

/-! ### 5a. The certificates over the TWO-element fetch prefix -/

/-- Rocq `wcert_load_base2` (deviation 2). -/
theorem wcertLoadBase2 (cid : Nat) (pc : BitVec 64) (akl : AkInfo) (ea : PAddr) :
    akl.akIfetch = false →
    wstepCert cid pc
      (wPEff (some cid)
        ([.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2]
          ++ [.WEread akl ea 4]))
      (wQLoad ea) :=
  fun hcoh => wcertLoadGen cid pc _ [] akl ea hcoh (nowriteFetch2 pc) nowriteNil

/-- Rocq `wcert_store_base2` (deviation 2). -/
theorem wcertStoreBase2 (cid : Nat) (pc : BitVec 64) (akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    wstepCert cid pc
      (wPEff (some cid)
        ([.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2]
          ++ [.WEwrite akw ea 4 v]))
      (wQStore (some cid) ea v) :=
  wcertStoreGen cid pc _ [] akw ea v (nowriteFetch2 pc) nowriteNil

/-- Rocq `wcert_amo_aq_base2` (deviation 2). -/
theorem wcertAmoAqBase2 (cid : Nat) (pc : BitVec 64) (aka akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    aka.akIfetch = false → aka.akSync = true → akw.akLatest = true →
    wstepCert cid pc
      (wPEff (some cid)
        ([.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2]
          ++ [.WEread aka ea 4, .WEwrite akw ea 4 v]))
      (wQAmoAq (some cid) ea v) :=
  fun hcoh hsync hlat =>
    wcertAmoAqGen cid pc _ [] aka akw ea v hcoh hsync hlat (nowriteFetch2 pc) nowriteNil

/-- Rocq `wcert_fence_base2` (deviation 2). -/
theorem wcertFenceBase2 (cid : Nat) (pc : BitVec 64) (b : barrier_kind) :
    wstepCert cid pc
      (wPEff (some cid)
        ([.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2]
          ++ [.WEbar b]))
      (wQFence b) :=
  wcertFenceGen cid pc _ [] b (nowriteFetch2 pc) nowriteNil

/-! ### 5b. The `F_RVC`-at-2 instances: `WeakCert`'s certificates at the
ONE-element width-2 fetch prefix (`nf := 2`) -/

/-- Rocq `wcert_load_rvc2` (deviation 2). -/
theorem wcertLoadRvc2 (cid : Nat) (pc : BitVec 64) (akl : AkInfo) (ea : PAddr) :
    akl.akIfetch = false →
    wstepCert cid pc
      (wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 2] ++ [.WEread akl ea 4])) (wQLoad ea) :=
  fun hcoh => wcertLoad cid pc WeakFetchEff.wakIfetch pc 2 akl ea hcoh

/-- Rocq `wcert_store_rvc2` (deviation 2). -/
theorem wcertStoreRvc2 (cid : Nat) (pc : BitVec 64) (akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    wstepCert cid pc
      (wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 2] ++ [.WEwrite akw ea 4 v]))
      (wQStore (some cid) ea v) :=
  wcertStore cid pc WeakFetchEff.wakIfetch pc 2 akw ea v

/-- Rocq `wcert_amo_aq_rvc2` (deviation 2). -/
theorem wcertAmoAqRvc2 (cid : Nat) (pc : BitVec 64) (aka akw : AkInfo) (ea : PAddr) (v : BitVec 32) :
    aka.akIfetch = false → aka.akSync = true → akw.akLatest = true →
    wstepCert cid pc
      (wPEff (some cid) ([.WEread WeakFetchEff.wakIfetch pc 2] ++ [.WEread aka ea 4, .WEwrite akw ea 4 v]))
      (wQAmoAq (some cid) ea v) :=
  fun hcoh hsync hlat => wcertAmoAq cid pc WeakFetchEff.wakIfetch pc 2 aka akw ea v hcoh hsync hlat

/-! ### 5c. The end-to-end join check: the 3-element trace of a load under a
split fetch is §4's recipe at `es_x := [.WEread akl ea 4]`, and its conclusion
is `wcertLoadBase2`'s `P` on the nose. -/

/-- Rocq `wP_load_of_leaf_base2` (deviation 5). -/
theorem wPLoadOfLeafBase2 (cid : Nat) (σ : Wmstate) (W : GSet PAddr)
    (pc : BitVec 64) (w : BitVec 32) (i : instruction) (akl : AkInfo) (ea : PAddr)
    (D : Register → Bool) (dst : ExecSt) :
    wlogWf σ.wmLog →
    (∀ a, a ∈ W → paZ a ≠ 0) →
    (∀ a, a ∈ W → pinnedRead σ (paZ a)) →
    fetchPin σ ([.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2]
      ++ [.WEread akl ea 4]) →
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
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
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
    wPEff (some cid)
      ([.WEread WeakFetchEff.wakIfetch pc 2, .WEread WeakFetchEff.wakIfetch (BitVec.addInt pc 2) 2]
        ++ [.WEread akl ea 4]) σ :=
  wPEffOfLeafBase2 cid σ W pc w i _ D dst

/-! ## 6. Q10 (Lean-only): THE RVC-AT-2 RECIPE'S RUN IS SFENCE-FREE

Owner ruling Q10, as `WeakFetchEff` §10: the `noSfAnn` twins of the width-2 fetch chain and of
`WeakFetch2.execEffStepOfLeafRvc2St`.  A compressed announce (width 16) is never an sfence
announce, so no word fact is needed; the decode and the expansion are sfence-free by `goodb0`. -/

theorem WeakFetch2.noSfAnnCurrentlyEnabledC (s : ExecSt) :
    WeakEvLang.noSfAnn (currentlyEnabled .Ext_C) s := by
  rw [currentlyEnabled]
  simp only [execEffHartSupportsC, ↓reduceIte]
  nosf_run

theorem WeakFetch2.noSfAnnCurrentlyEnabledZca (s : ExecSt) :
    WeakEvLang.noSfAnn (currentlyEnabled .Ext_Zca) s := by
  rw [currentlyEnabled]
  simp only [WeakFetchRvc.execEffHartSupportsZca, ↓reduceIte]
  nosf_run [execEffRecCECMisa, WeakFetch2.noSfAnnCurrentlyEnabledC]

/-- `WeakFetch2.execEffFetch2Rvc`'s twin. -/
theorem WeakFetch2.noSfAnnFetch2Rvc (pc : BitVec 64) (h : BitVec 16) (s s1 : ExecSt) (es : List Weff)
    (hpc : s.regs .PC = pc)
    (hbit0 : (Sail.BitVec.access pc 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access pc 1 != 0#1) = true)
    (hzca : execEff (currentlyEnabled .Ext_Zca) s = some (true, s, []))
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = false)
    (hfb : execEff (fetch_bytes pc pc 2) s = some (.FetchBytes_Success h, s1, es)) (hrvc : isRVC h = true)
    (sfb : WeakEvLang.noSfAnn (fetch_bytes pc pc 2) s) :
    WeakEvLang.noSfAnn (fetch ()) s := by
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [WeakEffSkel.noSfAnnCatchEarlyReturn]
  nosf_run [hpc, hbit0, hbit1, hzca, WeakFetch2.noSfAnnCurrentlyEnabledZca, hvalign, hfb, sfb, hrvc,
    Functions.not]

/-- `WeakFetch2.execEffFetchBytes2Ram`'s twin. -/
theorem WeakFetch2.noSfAnnFetchBytes2Ram (pc pc2 : BitVec 64) (h : BitVec 16) (t : ExecSt)
    (hpriv : t.regs .cur_privilege = .Machine) (hpmp : pmpAllowsAll (t.regs .pmpcfg_n))
    (hpma : t.regs .pma_regions = bootPMA) (hhtif : t.regs .htif_tohost_base = none)
    (hram : inRam pc2 2) (hb : BytesAt t pc2 2 h) (hal : pc2.toNat % 2 = 0) :
    WeakEvLang.noSfAnn (fetch_bytes pc pc2 2) t := by
  have hal' : is_aligned_paddr (.Physaddr (fetchPa pc2)) 2 = true := by
    rw [fetchPa_eq]; exact is_aligned_paddr_of pc2 2 (by decide) hal
  have hsig : execEff (within_sig (.Physaddr (fetchPa pc2)) 2) t = some (false, t, []) := by
    first
    | rfl
    | (simp only [within_sig, plat_have_sig, Functions.not]; rfl)
  have hpmp' := execEffPmpCheckMachineUnlockedIfetch2 _ t hpmp hal'
  have hmatch : matching_pma_region (t.regs .pma_regions) (.Physaddr (fetchPa pc2)) 2 = some ramRegion := by
    rw [hpma, fetchPa_eq]; exact matching_pma_ram pc2 2 hram (by decide) (by decide)
  have hc : execEff (within_clint (.Physaddr (fetchPa pc2)) 2) t = some (false, t, []) := by
    rw [fetchPa_eq, within_clint_ram pc2 2 hram]; rfl
  have hhtif' := execEffWithinHtifFalse (fetchPa pc2) 2 t hhtif
  have hdev : devAddr (fetchPa pc2) = false := by rw [fetchPa_eq]; exact devAddrRam pc2 2 hram
  have hb' : BytesAt t (fetchPa pc2) 2 h := by rw [fetchPa_eq]; exact hb
  have htr := execEffTranslateAddrIdentity pc2 t hpriv
  have hmr := execEffMemReadFetch2 .PBMT_PMA (fetchPa pc2) ramRegion h t hpmp' hmatch hal' ramRegionExec
    hc hsig hhtif' hdev hb' hpriv
  have smr := WeakFetchEff.noSfAnnMemReadFetch .PBMT_PMA (fetchPa pc2) 2 ramRegion h t hpmp' hmatch hal'
    ramRegionExec (execEffWithinMmioReadableFalse _ 2 t hc hsig hhtif') hdev
    (bmRead_of_bytes _ _ _ _ hb')
    ⟨_, _, execEffCheckedMemReadRam2 .PBMT_PMA (fetchPa pc2) ramRegion h t hpmp' hmatch hal'
      ramRegionExec hc hsig hhtif' hdev hb'⟩ hpriv
  have str := WeakFetchEff.noSfAnnTranslateAddrMachine (.Virtaddr pc2) (.InstructionFetch ()) t
    (by rw [hpriv]; exact execEffEffectivePrivilegeFetch _ _ t)
  exact WeakFetchEff.noSfAnnFetchBytesOk pc pc2 (fetchPa pc2) 2 .PBMT_PMA h t t _ htr hmr str smr

/-- `execEffFetchFlatRvc2`'s twin. -/
theorem WeakFetch2.noSfAnnFetchFlatRvc2 (t : ExecSt) (pc : BitVec 64) (h : BitVec 16) :
    pmpAllowsAll (t.regs .pmpcfg_n) →
    t.regs .pma_regions = bootPMA →
    (_get_Misa_C (t.regs .misa) == 1#1) = true →
    t.regs .PC = pc →
    t.regs .cur_privilege = .Machine →
    t.regs .htif_tohost_base = none →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
    fetchFlatOk t pc (.F_RVC h) →
    WeakEvLang.noSfAnn (fetch ()) t := by
  rintro hpmp hpma hmisaC lpc lpriv lhtif hal ⟨h2, hram, w, hr, hb⟩
  obtain ⟨rfl, hisRVC⟩ := hr
  have hm2 : pc.toNat % 2 = 0 := isAlignedVaddrMod pc 2 (by decide) h2
  have hm4 : pc.toNat % 4 = 2 := by
    by_cases hm : pc.toNat % 4 = 0
    · rw [is_aligned_vaddr_of pc 4 hm] at hal; exact absurd hal (by decide)
    · omega
  have hramLo : inRam pc 2 := by unfold inRam at hram ⊢; omega
  have hbLo : BytesAt t pc 2 (Sail.BitVec.extractLsb w 15 0) := by
    intro j hj
    rw [nthByteLo w j hj]
    exact hb j (by omega)
  exact WeakFetch2.noSfAnnFetch2Rvc pc _ t t _ lpc (bit0_clear_of_even pc hm2) (bit1_set_of_mod4 pc hm4)
    (execEffCurrentlyEnabledZca t hmisaC) hal
    (WeakFetch2.execEffFetchBytes2Ram pc pc _ t lpriv hpmp hpma lhtif hramLo hbLo hm2) hisRVC
    (WeakFetch2.noSfAnnFetchBytes2Ram pc pc _ t lpriv hpmp hpma lhtif hramLo hbLo hm2)

/-- `WeakFetch2.execEffStepOfLeafRvc2St`'s twin (Q10): the same premises and the expanded
`execute`'s own `noSfAnn` give `noSfAnn` of the whole step at BOTH ticks. -/
theorem WeakFetch2.noSfAnnStepOfLeafRvc2St (s : ExecSt) (W : GSet PAddr)
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
    is_aligned_vaddr (.Virtaddr pc) 2 = true →
    is_aligned_vaddr (.Virtaddr pc) 4 = false →
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
    (∀ b : Bool, WeakEvLang.noSfAnn (execute i)
      ((s.setReg .minstret_increment b).setReg .nextPC (BitVec.addInt pc 2))) →
    ∀ tick : Bool, WeakEvLang.noSfAnn (riscvStep tick) s := by
  intro lpc lpriv lpmp lpma lhtif lhart lmisaS lmisaC lmIE lelp hal2 hal4 hram htext hsub hisRVC hagree hDmi
    hgood hdec hgood0 hexp hexec hsx tick
  obtain ⟨b, hsi⟩ := execEffShouldIncMinstretSome (s.regs .cur_privilege) s
  obtain ⟨sExec, hex, hhe, -, -⟩ := hexec b
  have lpriv_a : (hartActiveSA s b).regs .cur_privilege = .Machine := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpriv
  have lpc_a : (hartActiveSA s b).regs .PC = pc := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpc
  have lhart_a : (hartActiveSA s b).regs .hart_state = .HART_ACTIVE () := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhart
  have lelp_a : ((hartActiveSA s b).regs .elp == landing_pad_bits_backwards .LP_EXPECTED) = false := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lelp
  have lmisaS_a : (_get_Misa_S ((hartActiveSA s b).regs .misa) == 1#1) = true := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaS
  have lmIE_a : (_get_Mstatus_MIE ((hartActiveSA s b).regs .mstatus) == 1#1) = false := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmIE
  have lmisaC_a : (_get_Misa_C ((hartActiveSA s b).regs .misa) == 1#1) = true := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lmisaC
  have lpmp_a : pmpAllowsAll ((hartActiveSA s b).regs .pmpcfg_n) := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpmp
  have lpma_a : (hartActiveSA s b).regs .pma_regions = bootPMA := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lpma
  have lhtif_a : (hartActiveSA s b).regs .htif_tohost_base = none := by
    rw [WeakFetchEff.saLookup _ _ _ (by decide)]; exact lhtif
  have hdisp : execEff (dispatchInterrupt .Machine) (hartActiveSA s b) =
      some (none, hartActiveSA s b, []) :=
    execEffDispatchInterruptMachineNone _ lmisaS_a lmIE_a
  have hzca : execEff (currentlyEnabled .Ext_Zca) (hartActiveSA s b) =
      some (true, hartActiveSA s b, []) :=
    execEffCurrentlyEnabledZca _ lmisaC_a
  have hflat : fetchFlatOk (hartActiveSA s b) pc (.F_RVC h) := ⟨hal2, hram, w, ⟨hsub, hisRVC⟩, htext⟩
  have hfetch : execEff (fetch ()) (hartActiveSA s b) =
      some (.F_RVC h, hartActiveSA s b, [.WEread WeakFetchEff.wakIfetch pc 2]) :=
    execEffFetchFlatRvc2 _ pc h lpmp_a lpma_a lmisaC_a lpc_a lpriv_a lhtif_a hal4 hflat
  have sfetch : WeakEvLang.noSfAnn (fetch ()) (hartActiveSA s b) :=
    WeakFetch2.noSfAnnFetchFlatRvc2 _ pc h lpmp_a lpma_a lmisaC_a lpc_a lpriv_a lhtif_a hal4 hflat
  have hag : ∀ r, D r = true → dst.regs r = (hartActiveSA s b).regs r := by
    intro r hD
    have hne : r ≠ .minstret_increment := by
      rintro rfl
      rw [hDmi] at hD
      exact absurd hD (by decide)
    rw [WeakFetchEff.saLookup r s b hne]
    exact (hagree r hD).symm
  have hdec_a : execEff (ext_decode_compressed h) (hartActiveSA s b) =
      some (i0, hartActiveSA s b, []) :=
    execEffDecodeBridge D (ext_decode_compressed h) dst _ i0 (fun r hD => (hag r hD).symm) hgood hdec
  have sdec : WeakEvLang.noSfAnn (ext_decode_compressed h) (hartActiveSA s b) :=
    WeakFetchEff.noSfAnnOfGoodb0 D (ext_decode_compressed h) dst _ hag hgood
  have hexp_a : execEff (execute i0) ((hartActiveSA s b).setReg .nextPC (BitVec.addInt pc 2)) =
      some (.ExecuteAs i, (hartActiveSA s b).setReg .nextPC (BitVec.addInt pc 2), []) :=
    execEffOfGoodb0Self D0 (execute i0) _ _ (hgood0 _) (hexp _)
  have sexp : WeakEvLang.noSfAnn (execute i0) ((hartActiveSA s b).setReg .nextPC (BitVec.addInt pc 2)) :=
    WeakFetchEff.noSfAnnOfGoodb0 D0 (execute i0) _ _ (fun _ _ => rfl) (hgood0 _)
  have hrun := execEffHartActiveProgressRVCGen .Machine (hartActiveSA s b) (hartActiveSA s b) sExec h i0 i
    pc (.Retire_Success ()) _ es_x lpriv_a hdisp hfetch hdec_a lelp_a lpc_a hzca hexp_a hex
  have srun := WeakEffSkel.noSfAnnHartActiveProgressRVCGen .Machine (hartActiveSA s b) (hartActiveSA s b)
    sExec h i0 i pc (.Retire_Success ()) _ es_x lpriv_a hdisp hfetch hdec_a lelp_a lpc_a hzca hexp_a hex
    (WeakFetchEff.noSfAnnDispatchInterruptMachine _ lmisaS_a lmIE_a) sfetch sdec
    (WeakFetch2.noSfAnnCurrentlyEnabledZca _) sexp (hsx b)
  exact WeakEffSkel.noSfAnnRiscvStepHartActive s sExec _ b _ hsi lhart_a hrun hhe
    (WeakFetchEff.noSfAnnShouldIncMinstret _ s) srun WeakFetchEff.noSfAnnTickClock tick

end Weak
