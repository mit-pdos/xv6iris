/-
Weak: **the MEMORY leaf of the S-mode fetch chain at `execA`** — `checked_mem_read` at widths
2/4/8 (access-class generic: the register-only PMA/PMP/MMIO facts are premises, discharged by the
SC lemmas through `to_a`), `read_pte`, and the fetch's `mem_read`; then the S-mode fetch itself
(translation abstract, a premise).  Replays of `ExecSC4.execCheckedMemReadRam2S` /
`execReadPteS` / `ExecSC5.execFetchRVC{4,2}SGen` at `execA`.

Rocq: `iris/AxSpineOk3.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. ONE GENERIC REPLAY: the three Rocq `cmr` sections (identical scripts at widths 2/4/8) are
   instances of the Lean-only `AxSpineOk3.execACheckedMemRead` (any `vmemWidth n`).  The Lean model's
   read kind is the `(acc, res)` dispatch (`InstructionFetch` ↦ `Read_ifetch`, PTE load ↦
   `Read_ttw`, else `read_kind_of_flags` ↦ `Read_plain`; Rocq: always `Read_plain`), so the proof
   cases on `acc` and reads RAM through the Lean-only `AxSpineOk3.execAReadRam` (the three
   non-latest kinds; O2 Stage C: the ifetch read is a RAM read at `execA`, `AxSpineOk` deviation 1).
2. SPELLING (as `ExecSC4`'s conventions): `mword n` ↦ `BitVec n`, `register_lookup r s.(sregs)` ↦
   `s.regs r`, `eq_vec x 'b"1"` ↦ `(x == 1#1)`, `vec_access_dec v 0` ↦ `v[0]!`, `uint` ↦ `toNat`,
   `zeros' 64` ↦ `zeros (n := 64)`, `pma_ok_aligned` ↦ `pmaOkAligned`, `init_ext_ptw`/`tt` ↦ `()`,
   `subrange_vec_dec w 15 0` ↦ `Sail.BitVec.extractLsb w 15 0`, `neq_vec (access_vec_dec va i) 'b"0"`
   ↦ `(Sail.BitVec.access va i != 0#1)`; the byte window ↦ `BytesAt s pa n w`; the no-wrap bound
   `uint addr + n ≤ 2^64` ↦ `paZ addr + n ≤ 2 ^ 64`; record fields (`PMA_executable`, …) ↦ Lean's
   (`executable`, `supports_pte_read`).
3. `read_pte`: lean-sail's `read_pte` is `mem_read_priv` directly (no `mem_read_priv_meta`
   callback layer to step); the `mem_read` steps go through the Lean-only
   `AxSpineOk3.execAMemReadPriv` / `AxSpineOk3.execAMemReadFetchOfChecked` (as SC
   `execMemReadPriv` / `execMemReadFetchOfChecked`).  The PMA premise is lean-sail's
   `execPmaCheckRamPte` (Rocq `pma_ok_peel`).
4. The fetch: the `fetch_bytes` step is the Lean-only `AxSpineOk3.execAFetchBytesOk` (as SC
   `execFetchBytesOk`); `fetch`'s guards are stepped by one `simp` (Rocq: explicit `or_boolM`/
   `and_boolM` steps — Lean's model has none); `align4_low_bits` ↦ `bit0ClearOfAligned4`/
   `bit1ClearOfAligned4`.
5. The Ltac `nseip` (a register is not the pin) is dropped: the pin test `AxRunClose.pinReg r` on
   a concrete register is decided by `simp (config := { decide := true })` / `simp [pinReg]`.

**Rocq → Lean name map.**  `execA_checked_mem_read_2/4/8` `execACheckedMemRead2/4/8`,
`execA_mmio_false` `execAMmioFalse`, `execA_read_pte_S` `execAReadPteS`, `execA_mem_read_fetch_2_S`
`execAMemReadFetch2S`, `execA_mem_read_fetch_4_S` `execAMemReadFetch4S`,
`execA_currentlyEnabled_Ziccif` `execACurrentlyEnabledZiccif`, `execA_currentlyEnabled_Zca`
`execACurrentlyEnabledZca`, `execA_fetch_RVC_4_S_gen` `execAFetchRVC4SGen`,
`execA_fetch_RVC_2_S_gen` `execAFetchRVC2SGen`.  None is in the duplicated-name table.
Lean-only (file-qualified): `AxSpineOk3.execAReadRam`, `AxSpineOk3.execACheckedMemRead`,
`AxSpineOk3.execAMemReadPriv`, `AxSpineOk3.execAMemReadFetchOfChecked`,
`AxSpineOk3.execAFetchBytesOk`.

**Dropped:** the Ltac `nseip` (deviation 5).  No lemma dropped.
-/
import Weak.AxSpineOk2
import Weak.ExecSC5

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- (Lean-only) A non-latest RAM read kind reads the window at `execA`. -/
theorem AxSpineOk3.execAReadRam (rk : read_kind) (addr : BitVec 64) (n : Nat) (w : BitVec (8 * n))
    (s : ExecSt) (hrk : rk = .Read_plain ∨ rk = .Read_ifetch ∨ rk = .Read_ttw)
    (hdev : devAddr addr = false) (hwf : paZ addr + n ≤ 2 ^ 64) (hb : BytesAt s addr n w) :
    execA (read_ram rk (.Physaddr addr) n false) s = some ((w, default_meta), s) := by
  refine execAOfRfM _ ?_ s _ (execReadRam rk addr n w s (by rcases hrk with h | h | h <;> simp [h]) hdev hb)
  rcases hrk with rfl | rfl | rfl <;>
  · simp only [read_ram, PreSail.sail_mem_read, PreSail.emit]
    refine ⟨?_, fun v => ?_⟩
    · simp only [ramOk, hdev, Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨rfl, hwf⟩
    · rcases v with ⟨x, y⟩ | a <;> trivial


/-- (Lean-only) The common core of Rocq `execA_checked_mem_read_{2,4,8}`: one aligned RAM piece of
width `n`, any access class (the read kind is the model's `(acc, false)` dispatch). -/
theorem AxSpineOk3.execACheckedMemRead (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (addr : BitVec 64) (n : Nat) (s : ExecSt) (hn : vmemWidth n)
    (hcp : execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr addr) n false) s
      = some (.Ok pmaOkAligned, s))
    (hpmp : execA (pmpCheck (.Physaddr addr) n acc .Supervisor) s = some (none, s))
    (hmm : execA (within_mmio_readable (.Physaddr addr) n) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + n ≤ 2 ^ 64)
    (w : BitVec (8 * n)) (hb : BytesAt s addr n w) :
    execA (checked_mem_read acc pbmt .Supervisor (.Physaddr addr) n false false false false) s
      = some (.Ok (w, default_meta), s) := by
  have hrr : ∀ rk, (rk = .Read_plain ∨ rk = .Read_ifetch ∨ rk = .Read_ttw) →
      execA (read_ram rk (.Physaddr addr) n false) s = some ((w, default_meta), s) :=
    fun rk hrk => AxSpineOk3.execAReadRam rk addr n w s hrk hdev hwf hb
  have hsp : ∀ g, execA (split_misaligned (.Physaddr addr) n g .CannotSplit) s
      = some (((1 : Int), (n : Int)), s) := fun _ => rfl
  have hrP := hrr _ (Or.inl rfl)
  have hrI := hrr _ (Or.inr (Or.inl rfl))
  have hrT := hrr _ (Or.inr (Or.inr rfl))
  rcases hn with rfl | rfl | rfl | rfl <;>
  · unfold checked_mem_read
    rw [execACatchEarlyReturn]
    simp only [execARBind, execARLiftR, hcp, execARReturnRFwd, pmaOkAligned, hsp, untilFuelM,
      untilFuelM.go, misaligned_order, bits_of_physaddr, Int.reduceToNat, Int.reduceMul,
      Int.reduceAdd, Int.reduceSub, Int.cast_ofNat_Int,
      Int.zero_mul, addIntZero, execAAssertExpTrue, Int.toNat_one,
      sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
      Int.mul_one, Int.zero_mul]
    cases acc <;> (try (rename_i p; cases p)) <;>
    simp only [execARBind, execARLiftR, execARReturnRFwd, read_kind_of_flags, execAReturnM, hpmp,
      hmm, hrP, hrI, hrT, ↓reduceIte, Bool.false_eq_true, beq_self_eq_true] <;>
    (simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.setWidth_eq]
     congr
     simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.updateSubrange]
     bv_decide)

/-- Rocq `execA_checked_mem_read_2`. -/
theorem execACheckedMemRead2 (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (addr : BitVec 64) (s : ExecSt)
    (hcp : execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr addr) 2 false) s
      = some (.Ok pmaOkAligned, s))
    (hpmp : execA (pmpCheck (.Physaddr addr) 2 acc .Supervisor) s = some (none, s))
    (hmm : execA (within_mmio_readable (.Physaddr addr) 2) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + 2 ≤ 2 ^ 64) (w : BitVec 16)
    (hb : BytesAt s addr 2 w) :
    execA (checked_mem_read acc pbmt .Supervisor (.Physaddr addr) 2 false false false false) s
      = some (.Ok (w, default_meta), s) :=
  AxSpineOk3.execACheckedMemRead acc pbmt addr 2 s (by simp [vmemWidth]) hcp hpmp hmm hdev hwf w hb

/-- Rocq `execA_checked_mem_read_4`. -/
theorem execACheckedMemRead4 (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (addr : BitVec 64) (s : ExecSt)
    (hcp : execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr addr) 4 false) s
      = some (.Ok pmaOkAligned, s))
    (hpmp : execA (pmpCheck (.Physaddr addr) 4 acc .Supervisor) s = some (none, s))
    (hmm : execA (within_mmio_readable (.Physaddr addr) 4) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + 4 ≤ 2 ^ 64) (w : BitVec 32)
    (hb : BytesAt s addr 4 w) :
    execA (checked_mem_read acc pbmt .Supervisor (.Physaddr addr) 4 false false false false) s
      = some (.Ok (w, default_meta), s) :=
  AxSpineOk3.execACheckedMemRead acc pbmt addr 4 s (by simp [vmemWidth]) hcp hpmp hmm hdev hwf w hb

/-- Rocq `execA_checked_mem_read_8`. -/
theorem execACheckedMemRead8 (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (addr : BitVec 64) (s : ExecSt)
    (hcp : execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr addr) 8 false) s
      = some (.Ok pmaOkAligned, s))
    (hpmp : execA (pmpCheck (.Physaddr addr) 8 acc .Supervisor) s = some (none, s))
    (hmm : execA (within_mmio_readable (.Physaddr addr) 8) s = some (false, s))
    (hdev : devAddr addr = false) (hwf : paZ addr + 8 ≤ 2 ^ 64) (w : BitVec 64)
    (hb : BytesAt s addr 8 w) :
    execA (checked_mem_read acc pbmt .Supervisor (.Physaddr addr) 8 false false false false) s
      = some (.Ok (w, default_meta), s) :=
  AxSpineOk3.execACheckedMemRead acc pbmt addr 8 s (by simp [vmemWidth]) hcp hpmp hmm hdev hwf w hb

/-! # 2. The PTE read and the fetch's `mem_read`, at `execA` -/

/-- Rocq `execA_mmio_false`. -/
theorem execAMmioFalse (addr : BitVec 64) (n : Nat) (s : ExecSt)
    (hc : exec (within_clint (.Physaddr addr) n) s = some (false, s))
    (hsig : exec (within_sig (.Physaddr addr) n) s = some (false, s))
    (hh : exec (within_htif_readable (.Physaddr addr) n) s = some (false, s)) :
    execA (within_mmio_readable (.Physaddr addr) n) s = some (false, s) := by
  have hmm := execWithinMmioReadableFalse addr n s hc hsig hh
  to_a hmm
  exact hmm

/-- (Lean-only) `mem_read_priv` of a plain one-piece read at `execA` (as `execMemReadPriv`). -/
theorem AxSpineOk3.execAMemReadPriv (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (priv : Privilege) (addr : BitVec 64) (n : Nat)
    (w : BitVec (8 * n)) (s : ExecSt)
    (h : execA (checked_mem_read acc pbmt priv (.Physaddr addr) n false false false false) s =
      some (.Ok (w, default_meta), s)) :
    execA (mem_read_priv acc pbmt priv (.Physaddr addr) n false false false) s = some (.Ok w, s) := by
  unfold mem_read_priv mem_read_priv_meta
  simp only [execABind, h, execAReturnM]
  rfl

/-- Rocq `execA_read_pte_S`. -/
theorem execAReadPteS (addr : BitVec 64) (region : PMA_Region) (w : BitVec 64) (s : ExecSt)
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
    (hdev : devAddr addr = false) (hwf : paZ addr + 8 ≤ 2 ^ 64) (hb : BytesAt s addr 8 w) :
    execA (read_pte (.Physaddr addr) 8) s = some (.Ok w, s) := by
  have hpma := execPmaCheckRamPte addr .PBMT_PMA region false s hm hal hpte
  have hcp : exec (check_pma_with_pmp_priority (.Load .PageTableEntry) .PBMT_PMA .Supervisor
      (.Physaddr addr) 8 false) s = some (.Ok pmaOkAligned, s) := by
    unfold check_pma_with_pmp_priority
    exec_run [hpma]
  to_a hcp
  have hpmp := execPmpCheckSupervisorGrantLoad addr 8 s hA hlt hr hR
  to_a hpmp
  have hchk := execACheckedMemRead8 _ _ addr s hcp hpmp (execAMmioFalse addr 8 s hc hsig hh) hdev
    hwf w hb
  unfold read_pte
  exact AxSpineOk3.execAMemReadPriv _ _ _ addr 8 w s hchk

/-- (Lean-only) The fetch's `mem_read` from its `checked_mem_read` at `execA`, in S-mode
(as `execMemReadFetchOfChecked`). -/
theorem AxSpineOk3.execAMemReadFetchOfChecked (pbmt : page_based_mem_type) (pa : BitVec 64)
    (n : Nat) (w : BitVec (8 * n)) (s : ExecSt) (hcp : s.regs .cur_privilege = .Supervisor)
    (h : execA (checked_mem_read (.InstructionFetch ()) pbmt .Supervisor (.Physaddr pa) n false false
      false false) s = some (.Ok (w, default_meta), s)) :
    execA (mem_read (.InstructionFetch ()) pbmt (.Physaddr pa) n false false false) s
      = some (.Ok w, s) := by
  have hep := execEffectivePrivilegeFetch (s.regs .mstatus) (s.regs .cur_privilege) s
  to_a hep
  have hm : ¬ AxRunClose.pinReg .mstatus := by simp [AxRunClose.pinReg]
  have hc : ¬ AxRunClose.pinReg .cur_privilege := by simp [AxRunClose.pinReg]
  unfold mem_read
  simp only [execABind, readReg, PreSail.readReg, PreSail.emit, execA, hm, hc, ↓reduceIte]
  rw [hep, hcp]
  exact AxSpineOk3.execAMemReadPriv _ _ _ pa n w s h

/-- Rocq `execA_mem_read_fetch_2_S`. -/
theorem execAMemReadFetch2S (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
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
    (hdev : devAddr addr = false) (hwf : paZ addr + 2 ≤ 2 ^ 64) (hb : BytesAt s addr 2 w)
    (hpriv : s.regs .cur_privilege = .Supervisor) :
    execA (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) 2 false false false) s
      = some (.Ok w, s) := by
  have hpma := execPmaCheckRam2 addr pbmt region s hm hal hx
  have hcp : exec (check_pma_with_pmp_priority (.InstructionFetch ()) pbmt .Supervisor
      (.Physaddr addr) 2 false) s = some (.Ok pmaOkAligned, s) := by
    unfold check_pma_with_pmp_priority
    exec_run [hpma]
  to_a hcp
  have hpmp := execPmpCheckSupervisorGrant addr 2 s hA hlt hr hX
  to_a hpmp
  exact AxSpineOk3.execAMemReadFetchOfChecked pbmt addr 2 w s hpriv
    (execACheckedMemRead2 _ _ addr s hcp hpmp (execAMmioFalse addr 2 s hc hsig hh) hdev hwf w hb)

/-- Rocq `execA_mem_read_fetch_4_S`. -/
theorem execAMemReadFetch4S (pbmt : page_based_mem_type) (addr : BitVec 64) (region : PMA_Region)
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
    (hdev : devAddr addr = false) (hwf : paZ addr + 4 ≤ 2 ^ 64) (hb : BytesAt s addr 4 w)
    (hpriv : s.regs .cur_privilege = .Supervisor) :
    execA (mem_read (.InstructionFetch ()) pbmt (.Physaddr addr) 4 false false false) s
      = some (.Ok w, s) := by
  have hpma := execPmaCheckRam addr pbmt region s hm hal hx
  have hcp : exec (check_pma_with_pmp_priority (.InstructionFetch ()) pbmt .Supervisor
      (.Physaddr addr) 4 false) s = some (.Ok pmaOkAligned, s) := by
    unfold check_pma_with_pmp_priority
    exec_run [hpma]
  to_a hcp
  have hpmp := execPmpCheckSupervisorGrant addr 4 s hA hlt hr hX
  to_a hpmp
  exact AxSpineOk3.execAMemReadFetchOfChecked pbmt addr 4 w s hpriv
    (execACheckedMemRead4 _ _ addr s hcp hpmp (execAMmioFalse addr 4 s hc hsig hh) hdev hwf w hb)

/-! # 3. The S-mode fetch at `execA`, translation abstract (a premise) -/

/-- Rocq `execA_currentlyEnabled_Ziccif`. -/
theorem execACurrentlyEnabledZiccif (s : ExecSt) :
    execA (currentlyEnabled .Ext_Ziccif) s = some (true, s) := by
  have h := execCurrentlyEnabledZiccif s
  to_a h
  exact h

/-- Rocq `execA_currentlyEnabled_Zca`. -/
theorem execACurrentlyEnabledZca (s : ExecSt) (hm : (_get_Misa_C (s.regs .misa) == 1#1) = true) :
    execA (currentlyEnabled .Ext_Zca) s = some (true, s) := by
  have h := execCurrentlyEnabledZca s hm
  to_a h
  exact h

/-- (Lean-only) `execA` twin of `execFetchBytesOk`. -/
theorem AxSpineOk3.execAFetchBytesOk (fs gs pa : BitVec 64) (n : Nat) (pbmt : page_based_mem_type)
    (w : BitVec (8 * n)) (s s1 : ExecSt)
    (htr : execA (translateAddr (.Virtaddr gs) (.InstructionFetch ())) s
      = some (.Ok (.Physaddr pa, pbmt, ()), s1))
    (hmr : execA (mem_read (.InstructionFetch ()) pbmt (.Physaddr pa) n false false false) s1
      = some (.Ok w, s1)) :
    execA (fetch_bytes fs gs n) s = some (.FetchBytes_Success w, s1) := by
  unfold fetch_bytes ext_fetch_check_pc
  rw [execACatchEarlyReturn]
  simp (config := { decide := true }) only [execARBind, execARLiftR, execARReturnRFwd, htr, hmr]

/-- Rocq `execA_fetch_RVC_4_S_gen`. -/
theorem execAFetchRVC4SGen (va pa : BitVec 64) (w : BitVec 32) (s s1 : ExecSt)
    (region : PMA_Region) (hpc : s.regs .PC = va)
    (hvalign : is_aligned_vaddr (.Virtaddr va) 4 = true)
    (htr : execA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1))
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s1.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s1.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s1.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
      (to_bits (l := 64) 4).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s1.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s1.regs .pma_regions) (.Physaddr pa) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr pa) 4 = true)
    (hx : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : exec (within_clint (.Physaddr pa) 4) s1 = some (false, s1))
    (hsig : exec (within_sig (.Physaddr pa) 4) s1 = some (false, s1))
    (hh : exec (within_htif_readable (.Physaddr pa) 4) s1 = some (false, s1))
    (hdev : devAddr pa = false) (hwf : paZ pa + 4 ≤ 2 ^ 64) (hb : BytesAt s1 pa 4 w)
    (hpriv : s1.regs .cur_privilege = .Supervisor)
    (hrvc : isRVC (Sail.BitVec.extractLsb w 15 0) = true) :
    execA (fetch ()) s = some (.F_RVC (Sail.BitVec.extractLsb w 15 0), s1) := by
  have hfb := AxSpineOk3.execAFetchBytesOk va va pa 4 .PBMT_PMA w s s1 htr
    (execAMemReadFetch4S .PBMT_PMA pa region w s1 hA hlt hr hX hm hal hx hc hsig hh hdev hwf hb hpriv)
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execACatchEarlyReturn]
  simp (config := { decide := true }) only [execARBind, execARLiftR, execARReturnRFwd,
    readReg, PreSail.readReg, PreSail.emit, execA, hpc, bit0ClearOfAligned4 va hvalign,
    bit1ClearOfAligned4 va hvalign, hvalign, execACurrentlyEnabledZiccif, hfb, hrvc, ↓reduceIte,
    Bool.false_eq_true, Functions.not, Nat.reduceMul, BitVec.setWidth_eq]

/-- Rocq `execA_fetch_RVC_2_S_gen`. -/
theorem execAFetchRVC2SGen (va pa : BitVec 64) (h : BitVec 16) (s s1 : ExecSt)
    (region : PMA_Region) (hpc : s.regs .PC = va)
    (hmisaC : (_get_Misa_C (s.regs .misa) == 1#1) = true)
    (hbit0 : (Sail.BitVec.access va 0 != 0#1) = false)
    (hbit1 : (Sail.BitVec.access va 1 != 0#1) = true)
    (hvalign4 : is_aligned_vaddr (.Virtaddr va) 4 = false)
    (htr : execA (translateAddr (.Virtaddr va) (.InstructionFetch ())) s
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1))
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s1.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s1.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s1.regs .pmpaddr_n)[0]!.toNat * 4) pa.toNat
      (to_bits (l := 64) 2).toNat = .PMP_Match)
    (hX : (_get_Pmpcfg_ent_X (s1.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hm : matching_pma_region (s1.regs .pma_regions) (.Physaddr pa) 2 = some region)
    (hal : is_aligned_paddr (.Physaddr pa) 2 = true)
    (hx : (override_PMA region.attributes .PBMT_PMA).executable = true)
    (hc : exec (within_clint (.Physaddr pa) 2) s1 = some (false, s1))
    (hsig : exec (within_sig (.Physaddr pa) 2) s1 = some (false, s1))
    (hh : exec (within_htif_readable (.Physaddr pa) 2) s1 = some (false, s1))
    (hdev : devAddr pa = false) (hwf : paZ pa + 2 ≤ 2 ^ 64) (hb : BytesAt s1 pa 2 h)
    (hpriv : s1.regs .cur_privilege = .Supervisor) (hrvc : isRVC h = true) :
    execA (fetch ()) s = some (.F_RVC h, s1) := by
  have hfb := AxSpineOk3.execAFetchBytesOk va va pa 2 .PBMT_PMA h s s1 htr
    (execAMemReadFetch2S .PBMT_PMA pa region h s1 hA hlt hr hX hm hal hx hc hsig hh hdev hwf hb hpriv)
  have hzca := execACurrentlyEnabledZca s hmisaC
  unfold fetch ext_fetch_check_pc get_config_rvfi
  rw [execACatchEarlyReturn]
  simp (config := { decide := true }) only [execARBind, execARLiftR, execARReturnRFwd,
    readReg, PreSail.readReg, PreSail.emit, execA, hpc, hbit0, hbit1, hvalign4, hzca, hfb, hrvc,
    ↓reduceIte, Bool.false_eq_true, Functions.not, Nat.reduceMul, BitVec.setWidth_eq]

end Weak
