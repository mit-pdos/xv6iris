/-
Weak: `fetch_bytes` and `fetch` (M-mode over the identity translation, and
S-mode over an abstract translation).

Rocq: `iris/RiscvFetchExec.v` (sections `FetchExec`, `FetchRVC`, `FetchBytes2`,
`FetchRVC2`, `FetchFBase2`; `execR_untilMT_1`, `fetch_pa`), `iris/SmodeCore.v`
(`exec_fetch_*_S_gen`) @ xxvzwolszwmp.

**Conventions (all `Weak/ExecSC*.lean` files; the deviations every statement shares).**
Statements are about `Weak.exec` over the LEAN model (sail-riscv `070832a1`,
`-D SYMBOLIC`: announce events silent), not Rocq's `exec` over the Coq model.
* GPRs: Rocq `if uint i =? 0 then zero_reg else register_lookup (R_bitvector_64
  (gpr_of_Z (uint i))) s.(sregs)` ↦ `s.gpr i`; Rocq `if uint rd =? 0 then s else
  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)` ↦
  `s.setGpr rd v` (`Weak/ExecSC.lean`).  Where Rocq has a `uint rd ≠ 0` premise and a
  plain `set_reg`, the premise is kept and the result is `setGpr` (equal under it).
* Spelling: `register_lookup r s.(sregs)` ↦ `s.regs r`; `eq_vec x 'b"1" = b` ↦
  `(x == 1#1) = b`; `vec_access_dec v i` ↦ `v[i]!`; `vec_update_dec v i x` ↦
  `vectorUpdate v i x`; `uint x` ↦ `x.toNat`; `Z` widths/indices ↦ `Nat`;
  `mword n` ↦ `BitVec n`; `tt` ↦ `()`; `zeros' n` ↦ `zeros (n := n)`.
* Memory: `dev_addr pa = false` ↦ `devAddr pa = false`; Rocq's byte window
  `∀ j < n, s.(mem) !! pa_add pa j = Some (nth_byte w j)` ↦ `BytesAt s pa n w`;
  `MState s.(sregs) (write_bytes s.(mem) pa n v) s.(mdev)` ↦
  `s.setMem (bmWrite s.mem pa n v)`.  An ifetch is a RAM read in `exec`
  (`Weak/Exec.lean`), so the fetch facts read the byte map (`AK_ifetch` plays no role).
* `hartSupports` is pure in Lean: Rocq `exec (hartSupports X) s = Some (true, s)` ↦
  `hartSupports .X = true`; Rocq's fuelled `_rec_currentlyEnabled` facts are stated on
  `currentlyEnabled`.  Rocq loops (`foreach_ZM_up'`, `untilMT`) ↦ lean-sail's `IntRange`
  `forIn` and `untilFuelM`.
* Rocq section hypotheses become theorem premises; section `Let`s become `def`s or are
  inlined; premise bundles that several statements share are `structure`s
  (`FetchM4`, `FetchM2`, `FetchS`, `MemM8`, `AmoS4`), each field a Rocq hypothesis.

**Deviations from Rocq.**
1. The Lean fetch at `pc ≡ 2 mod 4` reads two halfword chunks (as Rocq's model); the
   generic `execFetch4`, `execFetch2Rvc`, `execFetch2Base` take the `fetch_bytes`
   results as premises and the Rocq-named facts are their instances.
2. Section premises are bundled: `FetchM4`/`FetchM2` (Rocq's M-mode section
   hypotheses at `fetch_pa pc`), `FetchS` (SmodeCore's S-mode read premises at one
   physical address and state).
3. `exec_fetch_F_Base_2`: Rocq's `concat_vec ihi ilo = w` premise holds outright
   (dropped); the halves are `extractLsb w 15 0` / `extractLsb w 31 16`.
4. `execR_untilMT_1` ↦ `execRUntilFuelM1` (lean-sail's `untilFuelM`, fuel 1).

**Name map (Rocq → Lean).**  RiscvFetchExec: `execR_untilMT_1` ↦ `execRUntilFuelM1`,
`fetch_pa` ↦ `fetchPa`, `exec_fetch_bytes_4` ↦ `execFetchBytes4`,
`exec_fetch_bytes_2` ↦ `execFetchBytes2`, `exec_fetch_done` ↦ `execFetchDone`,
`exec_fetch_RVC_4` ↦ `execFetchRVC4`, `exec_fetch_RVC_2` ↦ `execFetchRVC2`,
`exec_fetch_F_Base_2` ↦ `execFetchFBase2`.  SmodeCore: `exec_fetch_F_Base_4_S_gen` ↦
`execFetchFBase4SGen`, `exec_fetch_RVC_4_S_gen` ↦ `execFetchRVC4SGen`,
`exec_fetch_RVC_2_S_gen` ↦ `execFetchRVC2SGen`, `exec_fetch_F_Base_2_S_gen` ↦
`execFetchFBase2SGen`.  Lean-only: `fetchPa_eq`, `execFetchBytesOk`,
`bit0ClearOfAligned4`, `bit1ClearOfAligned4`, `execFetch4`, `execFetch2Rvc`,
`execFetch2Base`, `FetchM4`, `FetchM2`, `FetchS`, `execMemReadFetchOfChecked`,
`execFetchS4`, `execFetchS2`.

**Dropped**: none of the names the weak tier uses.
-/
import Weak.ExecSC4
import MachCSL.PlatformFacts

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. `untilFuelM` (Rocq `RiscvFetchExec.execR_untilMT_1`) -/

/-- Rocq `execR_untilMT_1` (Lean's split-access loops are `untilFuelM` with fuel, not
`untilMT` with a measure): one iteration whose condition then holds. -/
theorem execRUntilFuelM1 {R Vars : Type} (vars vars' : Vars) (cond : Vars → SailME R Bool)
    (body : Vars → SailME R Vars) (s s' : ExecSt)
    (hb : execR (body vars) s = some (.inr vars', s')) (hc : execR (cond vars') s' = some (.inr true, s')) :
    execR (untilFuelM 1 cond vars body) s = some (.inr vars', s') := by
  unfold untilFuelM untilFuelM.go
  rw [execRBind, hb]
  simp only []
  rw [execRBind, hc]
  rfl

/-! ## 2. `fetch_bytes` -/

/-- Rocq `RiscvFetchExec.fetch_pa`: the physical address of a machine-mode fetch. -/
def fetchPa (pc : BitVec 64) : BitVec 64 := zero_extend (m := 64) (bits_of_virtaddr (.Virtaddr pc))

theorem fetchPa_eq (pc : BitVec 64) : fetchPa pc = pc := by
  simp [fetchPa, bits_of_virtaddr, zero_extend, Sail.BitVec.zeroExtend]

/-- A chunk whose translation and read succeed (the core of Rocq `exec_fetch_bytes_4/_2`). -/
theorem execFetchBytesOk (fs gs pa : BitVec 64) (n : Nat) (pbmt : page_based_mem_type) (w : BitVec (8 * n))
    (s s1 : ExecSt)
    (htr : exec (translateAddr (.Virtaddr gs) (.InstructionFetch ())) s = some (.Ok (.Physaddr pa, pbmt, ()), s1))
    (hmr : exec (mem_read (.InstructionFetch ()) pbmt (.Physaddr pa) n false false false) s1 = some (.Ok w, s1)) :
    exec (fetch_bytes fs gs n) s = some (.FetchBytes_Success w, s1) := by
  unfold fetch_bytes ext_fetch_check_pc
  rw [execCatchEarlyReturn]
  exec_run [htr, hmr]

/-- Rocq `RiscvFetchExec.exec_fetch_bytes_4` (section hypotheses as premises). -/
theorem execFetchBytes4 (pc : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (hpriv : s.regs .cur_privilege = .Machine)
    (hpmp : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (fetchPa pc)) 4 = some region)
    (hx : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : exec (within_clint (.Physaddr (fetchPa pc)) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr (fetchPa pc)) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr (fetchPa pc)) 4) s = some (false, s))
    (hdev : devAddr (fetchPa pc) = false) (hb : BytesAt s (fetchPa pc) 4 w)
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = true) :
    exec (fetch_bytes pc pc 4) s = some (.FetchBytes_Success w, s) := by
  have hal : is_aligned_paddr (.Physaddr (fetchPa pc)) 4 = true := by rw [fetchPa_eq]; exact hvalign
  exact execFetchBytesOk pc pc (fetchPa pc) 4 .PBMT_PMA w s s (execTranslateAddrIdentity pc s hpriv)
    (execMemReadFetch .PBMT_PMA (fetchPa pc) region w s hpmp hmatch hal hx hc hsig hh hdev hb hpriv)

/-- Rocq `RiscvFetchExec.exec_fetch_bytes_2`. -/
theorem execFetchBytes2 (pc : BitVec 64) (region : PMA_Region) (w : BitVec 16) (s : ExecSt)
    (hpriv : s.regs .cur_privilege = .Machine)
    (hpmp : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (fetchPa pc)) 2 = some region)
    (hal : is_aligned_paddr (.Physaddr (fetchPa pc)) 2 = true)
    (hx : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : exec (within_clint (.Physaddr (fetchPa pc)) 2) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr (fetchPa pc)) 2) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr (fetchPa pc)) 2) s = some (false, s))
    (hdev : devAddr (fetchPa pc) = false) (hb : BytesAt s (fetchPa pc) 2 w) :
    exec (fetch_bytes pc pc 2) s = some (.FetchBytes_Success w, s) :=
  execFetchBytesOk pc pc (fetchPa pc) 2 .PBMT_PMA w s s (execTranslateAddrIdentity pc s hpriv)
    (execMemReadFetch2 .PBMT_PMA (fetchPa pc) region w s hpmp hmatch hal hx hc hsig hh hdev hb hpriv)

/-! ## 3. `fetch` -/

theorem bit0ClearOfAligned4 (pc : BitVec 64) (h : is_aligned_vaddr (.Virtaddr pc) 4 = true) :
    (Sail.BitVec.access pc 0 != 0#1) = false :=
  bit0_clear_of_even pc (by have := isAlignedVaddrMod pc 4 (by decide) h; omega)

theorem bit1ClearOfAligned4 (pc : BitVec 64) (h : is_aligned_vaddr (.Virtaddr pc) 4 = true) :
    (Sail.BitVec.access pc 1 != 0#1) = false :=
  bit1_clear_of_mod4 pc (isAlignedVaddrMod pc 4 (by decide) h)

/-- A 4-aligned fetch whose word read succeeds (the core of Rocq `exec_fetch_done`,
`exec_fetch_RVC_4`, `SmodeCore.exec_fetch_*_4_S_gen`). -/
theorem execFetch4 (pc : BitVec 64) (w : BitVec 32) (s s1 : ExecSt) (hpc : s.regs .PC = pc)
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = true)
    (hfb : exec (fetch_bytes pc pc 4) s = some (.FetchBytes_Success w, s1)) :
    exec (fetch ()) s = some (if isRVC (Sail.BitVec.extractLsb w 15 0) then .F_RVC (Sail.BitVec.extractLsb w 15 0)
      else .F_Base w, s1) := by
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execCatchEarlyReturn]
  cases hr : isRVC (Sail.BitVec.extractLsb w 15 0) <;>
  exec_run [hpc, bit0ClearOfAligned4 pc hvalign, bit1ClearOfAligned4 pc hvalign, hvalign,
    execCurrentlyEnabledZiccif, hfb, hr]

/-- A 2-mod-4 fetch whose halfword is compressed (the core of Rocq `exec_fetch_RVC_2`,
`SmodeCore.exec_fetch_RVC_2_S_gen`). -/
theorem execFetch2Rvc (pc : BitVec 64) (h : BitVec 16) (s s1 : ExecSt) (hpc : s.regs .PC = pc)
    (hbit0 : (Sail.BitVec.access pc 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access pc 1 != 0#1) = true)
    (hzca : exec (currentlyEnabled .Ext_Zca) s = some (true, s))
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = false)
    (hfb : exec (fetch_bytes pc pc 2) s = some (.FetchBytes_Success h, s1)) (hrvc : isRVC h = true) :
    exec (fetch ()) s = some (.F_RVC h, s1) := by
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execCatchEarlyReturn]
  exec_run [hpc, hbit0, hbit1, hzca, hvalign, hfb, hrvc, Functions.not]

/-- A 2-mod-4 fetch of a 32-bit instruction: two halfword chunks, the second from where the
first translation left the state (the core of Rocq `exec_fetch_F_Base_2`,
`SmodeCore.exec_fetch_F_Base_2_S_gen`). -/
theorem execFetch2Base (pc : BitVec 64) (lo hi : BitVec 16) (s s1 s2 : ExecSt) (hpc : s.regs .PC = pc)
    (hbit0 : (Sail.BitVec.access pc 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access pc 1 != 0#1) = true)
    (hzca : exec (currentlyEnabled .Ext_Zca) s = some (true, s))
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = false)
    (hfb1 : exec (fetch_bytes pc pc 2) s = some (.FetchBytes_Success lo, s1)) (hnr : isRVC lo = false)
    (hpc1 : s1.regs .PC = pc)
    (hfb2 : exec (fetch_bytes pc (BitVec.addInt pc 2) 2) s1 = some (.FetchBytes_Success hi, s2)) :
    exec (fetch ()) s = some (.F_Base (hi ++ lo), s2) := by
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execCatchEarlyReturn]
  exec_run [hpc, hbit0, hbit1, hzca, hvalign, hfb1, hnr, Functions.not, hpc1, hfb2]

/-- The Machine-mode section premises of Rocq `RiscvFetchExec`'s 4-byte fetch facts. -/
structure FetchM4 (pc : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s : ExecSt) : Prop where
  hpc : s.regs .PC = pc
  hpriv : s.regs .cur_privilege = .Machine
  hpmp : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false
  hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (fetchPa pc)) 4 = some region
  hx : (override_PMA region.attributes .PBMT_PMA).executable = true
  hc : exec (within_clint (.Physaddr (fetchPa pc)) 4) s = some (false, s)
  hsig : exec (within_sig (.Physaddr (fetchPa pc)) 4) s = some (false, s)
  hh : exec (within_htif_readable (.Physaddr (fetchPa pc)) 4) s = some (false, s)
  hdev : devAddr (fetchPa pc) = false
  hb : BytesAt s (fetchPa pc) 4 w
  hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = true

/-- Rocq `RiscvFetchExec.exec_fetch_done`: a 4-aligned M-mode fetch of a 32-bit word. -/
theorem execFetchDone (pc : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (H : FetchM4 pc region w s) (hnot : isRVC (Sail.BitVec.extractLsb w 15 0) = false) :
    exec (fetch ()) s = some (.F_Base w, s) := by
  rw [execFetch4 pc w s s H.hpc H.hvalign (execFetchBytes4 pc region w s H.hpriv H.hpmp H.hmatch H.hx H.hc H.hsig
    H.hh H.hdev H.hb H.hvalign), hnot]
  rfl

/-- Rocq `RiscvFetchExec.exec_fetch_RVC_4`. -/
theorem execFetchRVC4 (pc : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (H : FetchM4 pc region w s) (hrvc : isRVC (Sail.BitVec.extractLsb w 15 0) = true) :
    exec (fetch ()) s = some (.F_RVC (Sail.BitVec.extractLsb w 15 0), s) := by
  rw [execFetch4 pc w s s H.hpc H.hvalign (execFetchBytes4 pc region w s H.hpriv H.hpmp H.hmatch H.hx H.hc H.hsig
    H.hh H.hdev H.hb H.hvalign), hrvc]
  rfl

/-- The Machine-mode section premises of Rocq `RiscvFetchExec`'s 2-byte fetch facts at `pc`. -/
structure FetchM2 (pc : BitVec 64) (region : PMA_Region) (w : BitVec 16) (s : ExecSt) : Prop where
  hpriv : s.regs .cur_privilege = .Machine
  hpmp : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false
  hmatch : matching_pma_region (s.regs .pma_regions) (.Physaddr (fetchPa pc)) 2 = some region
  hal : is_aligned_paddr (.Physaddr (fetchPa pc)) 2 = true
  hx : (override_PMA region.attributes .PBMT_PMA).executable = true
  hc : exec (within_clint (.Physaddr (fetchPa pc)) 2) s = some (false, s)
  hsig : exec (within_sig (.Physaddr (fetchPa pc)) 2) s = some (false, s)
  hh : exec (within_htif_readable (.Physaddr (fetchPa pc)) 2) s = some (false, s)
  hdev : devAddr (fetchPa pc) = false
  hb : BytesAt s (fetchPa pc) 2 w

/-- Rocq `RiscvFetchExec.exec_fetch_RVC_2`. -/
theorem execFetchRVC2 (pc : BitVec 64) (region : PMA_Region) (w : BitVec 16) (s : ExecSt)
    (H : FetchM2 pc region w s) (hpc : s.regs .PC = pc)
    (hbit0 : (Sail.BitVec.access pc 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access pc 1 != 0#1) = true)
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = false)
    (hmisaC : (_get_Misa_C (s.regs .misa) == 1#1) = true) (hrvc : isRVC w = true) :
    exec (fetch ()) s = some (.F_RVC w, s) :=
  execFetch2Rvc pc w s s hpc hbit0 hbit1 (execCurrentlyEnabledZca s hmisaC) hvalign
    (execFetchBytes2 pc region w s H.hpriv H.hpmp H.hmatch H.hal H.hx H.hc H.hsig H.hh H.hdev H.hb) hrvc

/-- Rocq `RiscvFetchExec.exec_fetch_F_Base_2`: the halves at `pc` and `pc + 2`
(`addrh := fetch_pa (pc + 2)`); Rocq's `concat_vec ihi ilo = w` premise holds outright. -/
theorem execFetchFBase2 (pc : BitVec 64) (regl regh : PMA_Region) (w : BitVec 32) (s : ExecSt)
    (Hl : FetchM2 pc regl (Sail.BitVec.extractLsb w 15 0) s)
    (Hh : FetchM2 (BitVec.addInt pc 2) regh (Sail.BitVec.extractLsb w 31 16) s)
    (hpc : s.regs .PC = pc)
    (hbit0 : (Sail.BitVec.access pc 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access pc 1 != 0#1) = true)
    (hvalign : is_aligned_vaddr (.Virtaddr pc) 4 = false)
    (hmisaC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (hnot : isRVC (Sail.BitVec.extractLsb w 15 0) = false) :
    exec (fetch ()) s = some (.F_Base w, s) := by
  have h2 := execFetchBytesOk pc (BitVec.addInt pc 2) (fetchPa (BitVec.addInt pc 2)) 2 .PBMT_PMA _ s s
    (execTranslateAddrIdentity _ s Hh.hpriv)
    (execMemReadFetch2 .PBMT_PMA _ regh _ s Hh.hpmp Hh.hmatch Hh.hal Hh.hx Hh.hc Hh.hsig Hh.hh Hh.hdev Hh.hb
      Hh.hpriv)
  rw [execFetch2Base pc _ _ s s s hpc hbit0 hbit1 (execCurrentlyEnabledZca s hmisaC) hvalign
    (execFetchBytes2 pc regl _ s Hl.hpriv Hl.hpmp Hl.hmatch Hl.hal Hl.hx Hl.hc Hl.hsig Hl.hh Hl.hdev Hl.hb) hnot
    hpc h2]
  congr
  simp only [Sail.BitVec.extractLsb, Nat.reduceMul, BitVec.setWidth_eq]
  bv_decide

/-! ## 4. The S-mode fetch over an abstract translation (Rocq `SmodeCore`) -/

/-- The S-mode physical-read premises of Rocq `SmodeCore`'s fetch facts, for an `n`-byte
read of `pa` at state `s` (PMP entry 0 TOR granting X, PMA executable, RAM, the bytes). -/
structure FetchS (n : Nat) (pa : BitVec 64) (region : PMA_Region) (w : BitVec (8 * n)) (s : ExecSt) : Prop where
  hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR
  hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false
  hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
    (to_bits (l := 64) n).toNat = .PMP_Match
  hX : (_get_Pmpcfg_ent_X (s.regs .pmpcfg_n)[0]! == 1#1) = true
  hm : matching_pma_region (s.regs .pma_regions) (.Physaddr pa) n = some region
  hal : is_aligned_paddr (.Physaddr pa) n = true
  hx : (override_PMA region.attributes .PBMT_PMA).executable = true
  hc : exec (within_clint (.Physaddr pa) n) s = some (false, s)
  hsig : exec (within_sig (.Physaddr pa) n) s = some (false, s)
  hh : exec (within_htif_readable (.Physaddr pa) n) s = some (false, s)
  hdev : devAddr pa = false
  hb : BytesAt s pa n w
  hcp : s.regs .cur_privilege = .Supervisor

/-- `mem_read` of a fetch from `checked_mem_read` at the current privilege. -/
theorem execMemReadFetchOfChecked (pbmt : page_based_mem_type) (p : Privilege) (pa : BitVec 64) (n : Nat)
    (w : BitVec (8 * n)) (s : ExecSt) (hcp : s.regs .cur_privilege = p)
    (h : exec (checked_mem_read (.InstructionFetch ()) pbmt p (.Physaddr pa) n false false false false) s =
      some (.Ok (w, default_meta), s)) :
    exec (mem_read (.InstructionFetch ()) pbmt (.Physaddr pa) n false false false) s = some (.Ok w, s) := by
  unfold mem_read
  exec_run [hcp, execEffectivePrivilegeFetch, execMemReadPriv _ _ _ _ _ _ _ _ w s (by decide) h]

theorem execFetchS4 (pa : BitVec 64) (region : PMA_Region) (w : BitVec 32) (s : ExecSt) (H : FetchS 4 pa region w s) :
    exec (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 4 false false false) s = some (.Ok w, s) :=
  execMemReadFetchOfChecked _ _ pa 4 w s H.hcp
    (execCheckedMemReadRam4S _ pa region w s H.hA H.hlt H.hr H.hX H.hm H.hal H.hx H.hc H.hsig H.hh H.hdev H.hb)

theorem execFetchS2 (pa : BitVec 64) (region : PMA_Region) (w : BitVec 16) (s : ExecSt) (H : FetchS 2 pa region w s) :
    exec (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr pa) 2 false false false) s = some (.Ok w, s) :=
  execMemReadFetchOfChecked _ _ pa 2 w s H.hcp
    (execCheckedMemReadRam2S _ pa region w s H.hA H.hlt H.hr H.hX H.hm H.hal H.hx H.hc H.hsig H.hh H.hdev H.hb)

/-- Rocq `SmodeCore.exec_fetch_F_Base_4_S_gen`. -/
theorem execFetchFBase4SGen (va pa : BitVec 64) (w : BitVec 32) (s s1 : ExecSt) (region : PMA_Region)
    (hpc : s.regs .PC = va) (hvalign : is_aligned_vaddr (.Virtaddr va) 4 = true)
    (htr : exec (translateAddr (.Virtaddr va) (.InstructionFetch ())) s = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1))
    (H : FetchS 4 pa region w s1) (hnot : isRVC (Sail.BitVec.extractLsb w 15 0) = false) :
    exec (fetch ()) s = some (.F_Base w, s1) := by
  rw [execFetch4 va w s s1 hpc hvalign (execFetchBytesOk va va pa 4 _ w s s1 htr (execFetchS4 pa region w s1 H)),
    hnot]
  rfl

/-- Rocq `SmodeCore.exec_fetch_RVC_4_S_gen`. -/
theorem execFetchRVC4SGen (va pa : BitVec 64) (w : BitVec 32) (s s1 : ExecSt) (region : PMA_Region)
    (hpc : s.regs .PC = va) (hvalign : is_aligned_vaddr (.Virtaddr va) 4 = true)
    (htr : exec (translateAddr (.Virtaddr va) (.InstructionFetch ())) s = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1))
    (H : FetchS 4 pa region w s1) (hrvc : isRVC (Sail.BitVec.extractLsb w 15 0) = true) :
    exec (fetch ()) s = some (.F_RVC (Sail.BitVec.extractLsb w 15 0), s1) := by
  rw [execFetch4 va w s s1 hpc hvalign (execFetchBytesOk va va pa 4 _ w s s1 htr (execFetchS4 pa region w s1 H)),
    hrvc]
  rfl

/-- Rocq `SmodeCore.exec_fetch_RVC_2_S_gen`. -/
theorem execFetchRVC2SGen (va pa : BitVec 64) (h : BitVec 16) (s s1 : ExecSt) (region : PMA_Region)
    (hpc : s.regs .PC = va) (hmisaC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (hbit0 : (Sail.BitVec.access va 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access va 1 != 0#1) = true)
    (hvalign : is_aligned_vaddr (.Virtaddr va) 4 = false)
    (htr : exec (translateAddr (.Virtaddr va) (.InstructionFetch ())) s = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1))
    (H : FetchS 2 pa region h s1) (hrvc : isRVC h = true) :
    exec (fetch ()) s = some (.F_RVC h, s1) :=
  execFetch2Rvc va h s s1 hpc hbit0 hbit1 (execCurrentlyEnabledZca s hmisaC) hvalign
    (execFetchBytesOk va va pa 2 _ h s s1 htr (execFetchS2 pa region h s1 H)) hrvc

/-- Rocq `SmodeCore.exec_fetch_F_Base_2_S_gen`: the two halfword translations thread
`s → s1 → s2` (the halves may land in different pages). -/
theorem execFetchFBase2SGen (va pal pah : BitVec 64) (w : BitVec 32) (s s1 s2 : ExecSt) (regl regh : PMA_Region)
    (hpc : s.regs .PC = va) (hpc1 : s1.regs .PC = va) (hmisaC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (hbit0 : (Sail.BitVec.access va 0 != 0#1) = false) (hbit1 : (Sail.BitVec.access va 1 != 0#1) = true)
    (hvalign : is_aligned_vaddr (.Virtaddr va) 4 = false)
    (htr1 : exec (translateAddr (.Virtaddr va) (.InstructionFetch ())) s = some (.Ok (.Physaddr pal, .PBMT_PMA, ()), s1))
    (htr2 : exec (translateAddr (.Virtaddr (BitVec.addInt va 2)) (.InstructionFetch ())) s1 =
      some (.Ok (.Physaddr pah, .PBMT_PMA, ()), s2))
    (Hl : FetchS 2 pal regl (Sail.BitVec.extractLsb w 15 0) s1)
    (Hh : FetchS 2 pah regh (Sail.BitVec.extractLsb w 31 16) s2)
    (hnot : isRVC (Sail.BitVec.extractLsb w 15 0) = false) :
    exec (fetch ()) s = some (.F_Base w, s2) := by
  rw [execFetch2Base va _ _ s s1 s2 hpc hbit0 hbit1 (execCurrentlyEnabledZca s hmisaC) hvalign
    (execFetchBytesOk va va pal 2 _ _ s s1 htr1 (execFetchS2 pal regl _ s1 Hl)) hnot hpc1
    (execFetchBytesOk va _ pah 2 _ _ s1 s2 htr2 (execFetchS2 pah regh _ s2 Hh))]
  congr
  simp only [Sail.BitVec.extractLsb, Nat.reduceMul, BitVec.setWidth_eq]
  bv_decide

end Weak
