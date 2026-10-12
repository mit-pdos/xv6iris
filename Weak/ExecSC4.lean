/-
Weak: the physical accesses -- `checked_mem_read`, `mem_read`, `read_pte`,
`checked_mem_write`, `mem_write_ea`, `mem_write_value` -- of one aligned RAM piece.

Rocq: `iris/RiscvFetchExec.v` (`exec_checked_mem_read_ram*`, `exec_mem_read_fetch*`),
`iris/SmodeCore.v` (`exec_checked_mem_read_ram_{4,2}_S`), `iris/SmodePte.v`
(`exec_read_pte_S`, `exec_read_pte_exclusive_S`), `iris/WpAmo.v`,
`iris/WpMmodeLeafBase.v` (`exec_mem_write_ea`, `exec_checked_mem_write_ram_store`,
`exec_mem_write_value_8`) @ xxvzwolszwmp.

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
1. The Lean model splits a physical access by `split_misaligned` and loops with
   `untilFuelM`; for an aligned granted access the plan is one piece, and the facts are
   instances of the generic `execCheckedMemReadRam` / `execCheckedMemWriteRam` /
   `execMemWriteEaRam` (widths 1, 2, 4, 8; read and write kinds `ReadKindOk` /
   `WriteKindOk`), with the MMIO test as `within_mmio_readable/_writable` (derived
   from Rocq's three `within_*` premises by `execWithinMmio*False`).
2. `exec_mem_write_ea` (WpMmodeLeafBase) takes the all-`OFF` PMP premise, as in Rocq.

**Name map (Rocq → Lean).**  RiscvFetchExec: `exec_checked_mem_read_ram` ↦
`execCheckedMemReadRamFetch4`, `exec_checked_mem_read_ram_2` ↦
`execCheckedMemReadRamFetch2`, `exec_mem_read_fetch` ↦ `execMemReadFetch`,
`exec_mem_read_fetch_2` ↦ `execMemReadFetch2`.  SmodeCore:
`exec_checked_mem_read_ram_4_S` ↦ `execCheckedMemReadRam4S`,
`exec_checked_mem_read_ram_2_S` ↦ `execCheckedMemReadRam2S`.  SmodePte:
`exec_read_pte_S` ↦ `execReadPteS`, `exec_read_pte_exclusive_S` ↦
`execReadPteExclusiveS`.  WpAmo: `exec_checked_mem_read_ram_amo_4_S` ↦
`execCheckedMemReadRamAmo4S`, `exec_mem_write_ea_amo_4` ↦ `execMemWriteEaAmo4`.
WpMmodeLeafBase: `exec_mem_write_ea` ↦ `execMemWriteEa`,
`exec_checked_mem_write_ram_store` ↦ `execCheckedMemWriteRamStore`,
`exec_mem_write_value_8` ↦ `execMemWriteValue8`.  Lean-only: `addIntZero`,
`exec_mem` (tactic), `execWithinMmioReadableFalse`, `execWithinMmioWritableFalse`,
`ReadKindOk`, `execCheckedMemReadRam`, `execMemReadPriv`, `WriteKindOk`,
`execCheckedMemWriteRam`, `execMemWriteEaRam`, `execMemWriteValueRam`.

**Dropped**: none of the names the weak tier uses.

**Import hygiene.**  `bv_decide` adds the auxiliary definitions
`page_based_mem_type.enumToBitVec` / `mem_payload.enumToBitVec` for the enums it meets; two
modules that each add them cannot be imported together.  `MachCSL.UTlb` adds them first; this
file depends on it, so `bv_decide` reuses its copies (as `MachCSL.BvEnumSatp` does for `SATPMode`).
-/
import Weak.ExecSC3
import MachCSL.WpTrap
import MachCSL.UTlb

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

theorem addIntZero (a : BitVec 64) : Sail.BitVec.addInt a 0 = a := by simp [Sail.BitVec.addInt]

/-- The physical-access normaliser: `exec_run` plus the closed integer arithmetic
of the split-access loops. -/
syntax "exec_mem" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| exec_mem [$ls,*]) => `(tactic| exec_run [pmaOkAligned, execSplitMisalignedUnsplit, untilFuelM,
      untilFuelM.go, misaligned_order, bits_of_physaddr, Int.reduceToNat, Int.reduceMul, Int.reduceAdd,
      Int.reduceSub, Int.cast_ofNat_Int, Int.natCast_zero, Int.toNat_natCast, Int.zero_mul, addIntZero, $ls,*])

/-! ## 1. `within_mmio_*` from the three device-window facts -/

/-- Rocq's three premises `exec (within_clint …) = false`, `within_sig`, `within_htif_readable`
make the access a RAM access. -/
theorem execWithinMmioReadableFalse (addr : BitVec 64) (n : Nat) (s : ExecSt)
    (hc : exec (within_clint (.Physaddr addr) n) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) n) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) n) s = some (false, s)) :
    exec (within_mmio_readable (.Physaddr addr) n) s = some (false, s) := by
  unfold within_mmio_readable
  exec_run [hc, hsig, hh]

theorem execWithinMmioWritableFalse (addr : BitVec 64) (n : Nat) (s : ExecSt)
    (hc : exec (within_clint (.Physaddr addr) n) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) n) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr addr) n) s = some (false, s)) :
    exec (within_mmio_writable (.Physaddr addr) n) s = some (false, s) := by
  unfold within_mmio_writable
  exec_run [hc, hsig, hh]

/-! ## 2. `checked_mem_read` of RAM (the core of Rocq `exec_checked_mem_read_ram*`) -/

/-- The read kinds the RAM-read lemmas cover: a fetch, a page-table read, a
plain data load, an acquiring reserved AMO read. -/
def ReadKindOk (acc : MemoryAccessType mem_payload) (aq rl res : Bool) (rk : read_kind) : Prop :=
  (acc = .InstructionFetch () ∧ res = false ∧ rk = .Read_ifetch) ∨
  (acc = .Load .PageTableEntry ∧ res = false ∧ rk = .Read_ttw) ∨
  (acc = .Load .Data ∧ aq = false ∧ rl = false ∧ res = false ∧ rk = .Read_plain) ∨
  (∃ aq' rl', acc = .Atomic (.AMOSWAP, aq', rl', .Data, .Data) ∧ aq = true ∧ rl = false ∧ res = true ∧
    rk = .Read_RISCV_reserved_acquire) ∨
  (acc = .Load .PageTableEntry ∧ aq = false ∧ rl = false ∧ res = true ∧ rk = .Read_RISCV_reserved)

/-- **A one-piece RAM read** (any access kind of `ReadKindOk`, width 1, 2, 4 or 8):
PMA grants it aligned, PMP grants it, it is not MMIO, the bytes are there. -/
theorem execCheckedMemReadRam (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (priv : Privilege) (addr : BitVec 64) (n : Nat) (aq rl res : Bool) (rk : read_kind) (w : BitVec (8 * n))
    (s : ExecSt) (hn : vmemWidth n) (hk : ReadKindOk acc aq rl res rk)
    (hpma : exec (pmaCheck (.Physaddr addr) n acc pbmt res) s = some (.Ok pmaOkAligned, s))
    (hpmp : exec (pmpCheck (.Physaddr addr) n acc priv) s = some (none, s))
    (hmm : exec (within_mmio_readable (.Physaddr addr) n) s = some (false, s))
    (hrr : exec (read_ram rk (.Physaddr addr) n false) s = some ((w, default_meta), s)) :
    exec (checked_mem_read acc pbmt priv (.Physaddr addr) n aq rl res false) s =
      some (.Ok (w, default_meta), s) := by
  rcases hk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨aq', rl', rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
  rcases hn with rfl | rfl | rfl | rfl <;>
  · unfold checked_mem_read check_pma_with_pmp_priority
    rw [execCatchEarlyReturn]
    exec_mem [hpma]
    exec_mem [hpmp, hmm, hrr, read_kind_of_flags]
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
    congr
    simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
    bv_decide

/-- Rocq `RiscvFetchExec.exec_checked_mem_read_ram`: an M-mode 4-byte fetch of RAM. -/
theorem execCheckedMemReadRamFetch4 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (s : ExecSt) (hunl : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hx : (override_PMA region.attributes pbmt).executable = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    exec (checked_mem_read (.InstructionFetch ()) pbmt .Machine (.Physaddr addr) 4 false false false false) s =
      some (.Ok (w, default_meta), s) :=
  execCheckedMemReadRam _ pbmt _ addr 4 false false false .Read_ifetch w s (by simp [vmemWidth])
    (Or.inl ⟨rfl, rfl, rfl⟩) (execPmaCheckRam addr pbmt region s hm hal hx)
    (execPmpCheckMachineUnlockedIfetch4 addr s hunl hal) (execWithinMmioReadableFalse addr 4 s hc hsig hh)
    (execReadRam _ addr 4 w s (Or.inr (Or.inl rfl)) hdev hb)

/-- Rocq `RiscvFetchExec.exec_checked_mem_read_ram_2`. -/
theorem execCheckedMemReadRamFetch2 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 16) (s : ExecSt) (hunl : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 2 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 2 = true)
    (hx : (override_PMA region.attributes pbmt).executable = true)
    (hc : exec (within_clint (.Physaddr addr) 2) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 2) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 2) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 2 w) :
    exec (checked_mem_read (.InstructionFetch ()) pbmt .Machine (.Physaddr addr) 2 false false false false) s =
      some (.Ok (w, default_meta), s) :=
  execCheckedMemReadRam _ pbmt _ addr 2 false false false .Read_ifetch w s (by simp [vmemWidth])
    (Or.inl ⟨rfl, rfl, rfl⟩) (execPmaCheckRam2 addr pbmt region s hm hal hx)
    (execPmpCheckMachineUnlockedIfetch2 addr s hunl hal) (execWithinMmioReadableFalse addr 2 s hc hsig hh)
    (execReadRam _ addr 2 w s (Or.inr (Or.inl rfl)) hdev hb)

/-- Rocq `SmodeCore.exec_checked_mem_read_ram_4_S`: an S-mode 4-byte fetch under PMP entry 0. -/
theorem execCheckedMemReadRam4S (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 4).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hx : (override_PMA region.attributes pbmt).executable = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    exec (checked_mem_read (.InstructionFetch ()) pbmt .Supervisor (.Physaddr addr) 4 false false false false) s =
      some (.Ok (w, default_meta), s) :=
  execCheckedMemReadRam _ pbmt _ addr 4 false false false .Read_ifetch w s (by simp [vmemWidth])
    (Or.inl ⟨rfl, rfl, rfl⟩) (execPmaCheckRam addr pbmt region s hm hal hx)
    (execPmpCheckSupervisorGrant addr 4 s hA hlt hr hX) (execWithinMmioReadableFalse addr 4 s hc hsig hh)
    (execReadRam _ addr 4 w s (Or.inr (Or.inl rfl)) hdev hb)

/-- Rocq `SmodeCore.exec_checked_mem_read_ram_2_S`. -/
theorem execCheckedMemReadRam2S (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 16) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 2).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 2 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 2 = true)
    (hx : (override_PMA region.attributes pbmt).executable = true)
    (hc : exec (within_clint (.Physaddr addr) 2) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 2) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 2) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 2 w) :
    exec (checked_mem_read (.InstructionFetch ()) pbmt .Supervisor (.Physaddr addr) 2 false false false false) s =
      some (.Ok (w, default_meta), s) :=
  execCheckedMemReadRam _ pbmt _ addr 2 false false false .Read_ifetch w s (by simp [vmemWidth])
    (Or.inl ⟨rfl, rfl, rfl⟩) (execPmaCheckRam2 addr pbmt region s hm hal hx)
    (execPmpCheckSupervisorGrant addr 2 s hA hlt hr hX) (execWithinMmioReadableFalse addr 2 s hc hsig hh)
    (execReadRam _ addr 2 w s (Or.inr (Or.inl rfl)) hdev hb)

/-- Rocq `WpAmo.exec_checked_mem_read_ram_amo_4_S`: the acquiring reserved read of an S-mode
`amoswap.w.aq`. -/
theorem execCheckedMemReadRamAmo4S (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 4).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hW : (_get_Pmpcfg_ent_W (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w) :
    exec (checked_mem_read (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt .Supervisor (.Physaddr addr) 4
      true false true false) s = some (.Ok (w, default_meta), s) :=
  execCheckedMemReadRam _ pbmt _ addr 4 true false true .Read_RISCV_reserved_acquire w s (by simp [vmemWidth])
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨true, false, rfl, rfl, rfl, rfl, rfl⟩))))
    (execPmaCheckRamAmo4 addr pbmt region true false s hm hal hrd hwr ha)
    (execPmpCheckSupervisorGrantAmo addr 4 true false s hA hlt hr hR hW)
    (execWithinMmioReadableFalse addr 4 s hc hsig hh)
    (execReadRam _ addr 4 w s (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hdev hb)

/-! ## 3. `mem_read`, `read_pte` -/

/-- `mem_read_priv` of a one-piece RAM read. -/
theorem execMemReadPriv (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (priv : Privilege)
    (addr : BitVec 64) (n : Nat) (aq rl res : Bool) (w : BitVec (8 * n)) (s : ExecSt)
    (hnr : (aq, rl, res) ≠ (false, true, false) ∧ (aq, rl, res) ≠ (false, true, true))
    (h : exec (checked_mem_read acc pbmt priv (.Physaddr addr) n aq rl res false) s =
      some (.Ok (w, default_meta), s)) :
    exec (mem_read_priv acc pbmt priv (.Physaddr addr) n aq rl res) s = some (.Ok w, s) := by
  unfold mem_read_priv mem_read_priv_meta
  rcases aq <;> rcases rl <;> rcases res <;> simp at hnr <;> exec_run [h] <;> rfl

/-- Rocq `RiscvFetchExec.exec_mem_read_fetch`. -/
theorem execMemReadFetch (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 32) (s : ExecSt) (hunl : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hx : (override_PMA region.attributes pbmt).executable = true)
    (hc : exec (within_clint (.Physaddr addr) 4) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 4) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 4 w)
    (hcp : s.regs .cur_privilege = .Machine) :
    exec (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) 4 false false false) s = some (.Ok w, s) := by
  unfold mem_read
  exec_run [hcp, execEffectivePrivilegeFetch,
    execMemReadPriv _ _ _ _ _ _ _ _ w s (by decide)
      (execCheckedMemReadRamFetch4 pbmt addr region w s hunl hm hal hx hc hsig hh hdev hb)]
  simp only [Nat.reduceMul, BitVec.setWidth_eq]

/-- Rocq `RiscvFetchExec.exec_mem_read_fetch_2`. -/
theorem execMemReadFetch2 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (w : BitVec 16) (s : ExecSt) (hunl : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 2 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 2 = true)
    (hx : (override_PMA region.attributes pbmt).executable = true)
    (hc : exec (within_clint (.Physaddr addr) 2) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 2) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 2) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 2 w)
    (hcp : s.regs .cur_privilege = .Machine) :
    exec (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) 2 false false false) s = some (.Ok w, s) := by
  unfold mem_read
  exec_run [hcp, execEffectivePrivilegeFetch,
    execMemReadPriv _ _ _ _ _ _ _ _ w s (by decide)
      (execCheckedMemReadRamFetch2 pbmt addr region w s hunl hm hal hx hc hsig hh hdev hb)]
  simp only [Nat.reduceMul, BitVec.setWidth_eq]

/-- Rocq `SmodePte.exec_read_pte_S`: a page-table read under PMP entry 0. -/
theorem execReadPteS (addr : BitVec 64) (region : PMA_Region) (w : BitVec 64) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hpte : (override_PMA region.attributes .PBMT_PMA).supports_pte_read = true)
    (hc : exec (within_clint (.Physaddr addr) 8) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 8) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 8) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 8 w) :
    exec (read_pte (.Physaddr addr) 8) s = some (.Ok w, s) := by
  unfold read_pte
  exact execMemReadPriv _ _ _ _ _ _ _ _ w s (by decide)
    (execCheckedMemReadRam _ _ _ addr 8 false false false .Read_ttw w s (by simp [vmemWidth])
      (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (execPmaCheckRamPte addr _ region false s hm hal hpte)
      (execPmpCheckSupervisorGrantLoad addr 8 s hA hlt hr hR) (execWithinMmioReadableFalse addr 8 s hc hsig hh)
      (execReadRam _ addr 8 w s (Or.inr (Or.inr (Or.inl rfl))) hdev hb))

/-- Rocq `SmodePte.exec_read_pte_exclusive_S`. -/
theorem execReadPteExclusiveS (addr : BitVec 64) (region : PMA_Region) (w : BitVec 64) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 8).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hpte : (override_PMA region.attributes .PBMT_PMA).supports_pte_read = true)
    (hc : exec (within_clint (.Physaddr addr) 8) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 8) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) 8) s = some (false, s))
    (hdev : devAddr addr = false) (hb : BytesAt s addr 8 w) :
    exec (read_pte_exclusive (.Physaddr addr) 8) s = some (.Ok w, s) := by
  unfold read_pte_exclusive
  exact execMemReadPriv _ _ _ _ _ _ _ _ w s (by decide)
    (execCheckedMemReadRam _ _ _ addr 8 false false true .Read_RISCV_reserved w s (by simp [vmemWidth])
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩))))
      (execPmaCheckRamPte addr _ region true s hm hal hpte)
      (execPmpCheckSupervisorGrantLoad addr 8 s hA hlt hr hR) (execWithinMmioReadableFalse addr 8 s hc hsig hh)
      (execReadRam _ addr 8 w s (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hdev hb))

/-! ## 4. Writes: `checked_mem_write`, `mem_write_ea`, `mem_write_value` -/

/-- The write kinds the RAM-write lemmas cover (Lean's `write_ram` stores both). -/
def WriteKindOk (aq rl con : Bool) (wk : write_kind) : Prop :=
  (aq = false ∧ rl = false ∧ con = false ∧ wk = .Write_plain) ∨
  (aq = false ∧ rl = false ∧ con = true ∧ wk = .Write_RISCV_conditional)

/-- **A one-piece RAM write** (width 1, 2, 4 or 8): PMA grants it aligned, PMP grants it,
it is not MMIO, and the bytes land in the map. -/
theorem execCheckedMemWriteRam (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (priv : Privilege) (addr : BitVec 64) (n : Nat) (data : BitVec (8 * n)) (aq rl con : Bool) (wk : write_kind)
    (s : ExecSt) (hn : vmemWidth n) (hk : WriteKindOk aq rl con wk)
    (hpma : exec (pmaCheck (.Physaddr addr) n acc pbmt con) s = some (.Ok pmaOkAligned, s))
    (hpmp : exec (pmpCheck (.Physaddr addr) n acc priv) s = some (none, s))
    (hmm : exec (within_mmio_writable (.Physaddr addr) n) s = some (false, s))
    (hdev : devAddr addr = false) :
    exec (checked_mem_write (.Physaddr addr) n data acc pbmt priv () aq rl con) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr n data)) := by
  have hw1 : ∀ k (d : BitVec (8 * k)), exec (write_ram .Write_plain (.Physaddr addr) k d ()) s =
      some (true, s.setMem (bmWrite s.mem addr k d)) := fun k d => execWriteRam _ addr k d s (Or.inl rfl) hdev
  have hw2 : ∀ k (d : BitVec (8 * k)), exec (write_ram .Write_RISCV_conditional (.Physaddr addr) k d ()) s =
      some (true, s.setMem (bmWrite s.mem addr k d)) := fun k d => execWriteRam _ addr k d s (Or.inr rfl) hdev
  rcases hk with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  rcases hn with rfl | rfl | rfl | rfl <;>
  · unfold checked_mem_write check_pma_with_pmp_priority
    rw [execCatchEarlyReturn]
    exec_mem [hpma]
    exec_mem [hpmp, hmm, write_kind_of_flags, hw1, hw2]
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
    congr
    simp only [Sail.BitVec.extractLsb]
    bv_decide

/-- The effective-address announcement of a one-piece write: PMA and PMP grant it, nothing moves
(the core of Rocq `WpMmodeLeafBase.exec_mem_write_ea`, `WpAmo.exec_mem_write_ea_amo_4`). -/
theorem execMemWriteEaRam (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (priv : Privilege)
    (addr : BitVec 64) (n : Nat) (aq rl con : Bool) (s : ExecSt) (hn : vmemWidth n)
    (hwk : ∃ wk, exec (write_kind_of_flags aq rl con) s = some (wk, s))
    (hep : exec (effectivePrivilege acc (s.regs .mstatus) (s.regs .cur_privilege)) s = some (priv, s))
    (hpma : exec (pmaCheck (.Physaddr addr) n acc pbmt con) s = some (.Ok pmaOkAligned, s))
    (hpmp : exec (pmpCheck (.Physaddr addr) n acc priv) s = some (none, s)) :
    exec (mem_write_ea (.Physaddr addr) n acc pbmt aq rl con) s = some (.Ok (), s) := by
  obtain ⟨wk, hwk⟩ := hwk
  rcases hn with rfl | rfl | rfl | rfl <;>
  · unfold mem_write_ea check_pma_with_pmp_priority
    rw [execCatchEarlyReturn]
    exec_mem [hep, hpma]
    exec_mem [hwk, hpmp]

/-- Rocq `WpMmodeLeafBase.exec_mem_write_ea`: an M-mode 8-byte store announcement. -/
theorem execMemWriteEa (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region) (s : ExecSt)
    (hoff : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hcp : s.regs .cur_privilege = .Machine)
    (hmprv : (_get_Mstatus_MPRV (s.regs .mstatus) == 1#1) = false) :
    exec (mem_write_ea (.Physaddr addr) 8 (.Store .Data) pbmt false false false) s = some (.Ok (), s) :=
  execMemWriteEaRam _ pbmt .Machine addr 8 false false false s (by simp [vmemWidth]) ⟨_, rfl⟩
    (by rw [hcp]; exact execEffectivePrivilegeStore _ s hmprv)
    (execPmaCheckRamStore addr pbmt region s hm hal hw) (execPmpCheckMachineNone _ 8 _ s hoff)

/-- Rocq `WpAmo.exec_mem_write_ea_amo_4`: the S-mode `amoswap.w.aq` store announcement. -/
theorem execMemWriteEaAmo4 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region) (m : BitVec 64)
    (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) addr.toNat
      (to_bits (l := 64) 4).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hW : (_get_Pmpcfg_ent_W (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hrd : (override_PMA region.attributes pbmt).readable = true)
    (hwr : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true)
    (hms : s.regs .mstatus = m) (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Supervisor) :
    exec (mem_write_ea (.Physaddr addr) 4 (.Atomic (.AMOSWAP, true, false, .Data, .Data)) pbmt false false true) s =
      some (.Ok (), s) :=
  execMemWriteEaRam _ pbmt .Supervisor addr 4 false false true s (by simp [vmemWidth]) ⟨_, rfl⟩
    (by rw [hcp, hms]; exact execEffectivePrivilegeAmoS _ true false s hmprv)
    (execPmaCheckRamAmo4 addr pbmt region true false s hm hal hrd hwr ha)
    (execPmpCheckSupervisorGrantAmo addr 4 true false s hA hlt hr hR hW)

/-- Rocq `WpMmodeLeafBase.exec_checked_mem_write_ram_store`: an M-mode 8-byte store of RAM. -/
theorem execCheckedMemWriteRamStore (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (data : BitVec 64) (s : ExecSt)
    (hoff : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hc : exec (within_clint (.Physaddr addr) 8) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 8) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr addr) 8) s = some (false, s))
    (hdev : devAddr addr = false) :
    exec (checked_mem_write (.Physaddr addr) 8 data (.Store .Data) pbmt .Machine () false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr 8 data)) :=
  execCheckedMemWriteRam _ pbmt _ addr 8 data false false false .Write_plain s (by simp [vmemWidth])
    (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (execPmaCheckRamStore addr pbmt region s hm hal hw)
    (execPmpCheckMachineNone _ 8 _ s hoff) (execWithinMmioWritableFalse addr 8 s hc hsig hh) hdev

/-- `mem_write_value` of a one-piece RAM write, through the effective privilege. -/
theorem execMemWriteValueRam (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (priv : Privilege)
    (addr : BitVec 64) (n : Nat) (data : BitVec (8 * n)) (aq rl con : Bool) (s : ExecSt)
    (hep : exec (effectivePrivilege acc (s.regs .mstatus) (s.regs .cur_privilege)) s = some (priv, s))
    (h : exec (checked_mem_write (.Physaddr addr) n data acc pbmt priv () aq rl con) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr n data))) :
    exec (mem_write_value (.Physaddr addr) n data acc pbmt aq rl con) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr n data)) := by
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  exec_run [hep, h]

/-- Rocq `WpMmodeLeafBase.exec_mem_write_value_8`. -/
theorem execMemWriteValue8 (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
    (data : BitVec 64) (m : BitVec 64) (s : ExecSt)
    (hoff : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (hc : exec (within_clint (.Physaddr addr) 8) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) 8) s = some (false, s))
    (hh : exec (within_htif_writable (.Physaddr addr) 8) s = some (false, s))
    (hdev : devAddr addr = false) (hms : s.regs .mstatus = m) (hmprv : (_get_Mstatus_MPRV m == 1#1) = false)
    (hcp : s.regs .cur_privilege = .Machine) :
    exec (mem_write_value (.Physaddr addr) 8 data (.Store .Data) pbmt false false false) s =
      some (.Ok true, s.setMem (bmWrite s.mem addr 8 data)) :=
  execMemWriteValueRam _ pbmt .Machine addr 8 data false false false s
    (by rw [hcp, hms]; exact execEffectivePrivilegeStore _ s hmprv)
    (execCheckedMemWriteRamStore pbmt addr region data s hoff hm hal hw hc hsig hh hdev)

end Weak
