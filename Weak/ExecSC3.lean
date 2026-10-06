/-
Weak: the PMP and PMA checks.

Rocq: `iris/RiscvTryStep.v` (PMP), `iris/WpMmodeLeafBase.v` (`pmp_tor0_grants`,
`exec_pmpReadAddrReg`, `exec_pmpMatchAddr_tor0_match`, `exec_pmaCheck_ram_store`),
`iris/SmodePte.v`, `iris/WpSmodeGpr.v`, `iris/PtTreeAdue.v`, `iris/WpAmo.v`,
`iris/RiscvFetchExec.v` (PMA/PMP fetch leaves), `iris/MemAccessGen.v`,
`iris/RiscvExtras.v` (`pma_ok_aligned`) @ xxvzwolszwmp.

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
1. The PMP loop is lean-sail's `IntRange` loop (`execRForIn*`); entry facts are stated
   at `Nat` indices (`(s.regs .pmpcfg_n)[0]!`), the range match as
   `pmpRangeMatch ((zeros).toNat * 4) (paddr0.toNat * 4) a.toNat (to_bits 64 width).toNat`.
2. The supervisor-grant facts are instances of one `execPmpCheckEnt0` (entry 0 matches
   and its R/W/X bits grant the access, any privilege).
3. `exec_pmpCheck_machine_unlocked`: the cell premise is
   `(bits_of_physaddr addr).toNat % 4 + (to_bits 64 width).toNat ≤ 4`.
4. `exec_pmaCheck_ram` / `_ram_2` are instances of `execPmaCheckRamFetch` (any width);
   `exec_pmaCheck_ram_wpte` is generalised to any reservation flag
   (`execPmaCheckRamWpteRoc`; `execPmaCheckRamWpte` is the Rocq instance).
5. `exec_pmpReadAddrReg` (WpMmodeLeafBase) and `exec_pmpReadAddrReg_val` (SmodePte) are
   the same Lean lemma `execPmpReadAddrReg` (grain 0).

**Name map (Rocq → Lean).**  RiscvTryStep: `exec_pmpCheck_machine_none` ↦
`execPmpCheckMachineNone`, `exec_pmpReadAddrReg_ex` ↦ `execPmpReadAddrRegEx`,
`exec_pmpMatchAddr_OFF` ↦ `execPmpMatchAddrOFF`, `exec_pmpMatchAddr_machine_cell` ↦
`execPmpMatchAddrMachineCell`, `exec_pmpCheck_machine_unlocked` ↦
`execPmpCheckMachineUnlocked`.  WpMmodeLeafBase: `exec_pmpReadAddrReg` ↦
`execPmpReadAddrReg`, `exec_pmpMatchAddr_tor0_match` ↦ `execPmpMatchAddrTor0Match`,
`pmp_tor0_grants` ↦ `pmpTor0Grants`, `exec_pmpCheck_machine_tor0` ↦
`execPmpCheckMachineTor0`, `exec_pmaCheck_ram_store` ↦ `execPmaCheckRamStore`.
SmodePte: `exec_pmpReadAddrReg_val` ↦ `execPmpReadAddrReg`,
`exec_pmpMatchAddr_TOR_match` ↦ `execPmpMatchAddrTORMatch`,
`exec_pmpCheck_supervisor_grant` ↦ `execPmpCheckSupervisorGrant`,
`exec_pmpCheck_supervisor_grant_load` ↦ `execPmpCheckSupervisorGrantLoad`.
WpSmodeGpr: `exec_pmpCheck_supervisor_grant_store` ↦
`execPmpCheckSupervisorGrantStore`, `exec_pmpCheck_supervisor_grant_load_data` ↦
`execPmpCheckSupervisorGrantLoadData`.  PtTreeAdue:
`exec_pmpCheck_supervisor_grant_wpte` ↦ `execPmpCheckSupervisorGrantWpte`,
`exec_pmaCheck_ram_wpte` ↦ `execPmaCheckRamWpte`.  WpAmo:
`exec_pmpCheck_supervisor_grant_amo` ↦ `execPmpCheckSupervisorGrantAmo`,
`exec_pmaCheck_ram_amo_4` ↦ `execPmaCheckRamAmo4`.  RiscvFetchExec:
`exec_pmpCheck_machine_unlocked_ifetch4/2` ↦ `execPmpCheckMachineUnlockedIfetch4/2`,
`exec_pmaCheck_ram` ↦ `execPmaCheckRam`, `exec_pmaCheck_ram_2` ↦ `execPmaCheckRam2`.
MemAccessGen: `exec_pmaCheck_ram_load_g` ↦ `execPmaCheckRamLoadG`,
`exec_pmaCheck_ram_store_g` ↦ `execPmaCheckRamStoreG`.  RiscvExtras:
`pma_ok_aligned` ↦ `pmaOkAligned`.  Lean-only: `toNatInt_mul4_toNat`,
`toNatInt_toNat`, `pmpRangeMatch_full`, `pmpRangeMatch_cell`, `execPureCell`,
`execPmpCheckEnt0`, `execPmaCheckRamFetch`, `execPmaCheckRamWpteRoc`,
`execPmaCheckRamPte` (the page-table read twin `exec_read_pte_S` needs).

**Dropped**: none of the names the weak tier uses.
-/
import Weak.ExecSC2

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. PMP (Rocq `RiscvTryStep`, `WpMmodeLeafBase`, `SmodePte`, ...) -/

/-- Rocq `WpMmodeLeafBase.exec_pmpReadAddrReg` (and `SmodePte.exec_pmpReadAddrReg_val`):
with grain 0 the address register reads as stored. -/
theorem execPmpReadAddrReg (n : Nat) (s : ExecSt) :
    exec (pmpReadAddrReg n) s = some ((s.regs .pmpaddr_n)[n]!, s) := by
  unfold pmpReadAddrReg
  exec_run
  split <;> rfl

/-- Rocq `RiscvTryStep.exec_pmpReadAddrReg_ex`. -/
theorem execPmpReadAddrRegEx (n : Nat) (s : ExecSt) : ∃ v, exec (pmpReadAddrReg n) s = some (v, s) :=
  ⟨_, execPmpReadAddrReg n s⟩

/-- Rocq `RiscvTryStep.exec_pmpMatchAddr_OFF`. -/
theorem execPmpMatchAddrOFF (pa : physaddr) (width : BitVec 64) (ent : BitVec 8) (pmpaddr prev : BitVec 64)
    (s : ExecSt) (h : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = .OFF) :
    exec (pmpMatchAddr pa width ent pmpaddr prev) s = some (.PMP_NoMatch, s) := by
  unfold pmpMatchAddr
  simp only [h]
  rfl

theorem toNatInt_mul4_toNat {w : Nat} (x : BitVec w) : (BitVec.toNatInt x * 4).toNat = x.toNat * 4 := by
  simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]; omega

theorem toNatInt_toNat {w : Nat} (x : BitVec w) : (BitVec.toNatInt x).toNat = x.toNat := by
  simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]; omega

/-- Rocq `SmodePte.exec_pmpMatchAddr_TOR_match`. -/
theorem execPmpMatchAddrTORMatch (addr width : BitVec 64) (ent : BitVec 8) (pmpaddr prev : BitVec 64)
    (s : ExecSt) (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = .TOR)
    (hlt : zopz0zKzJ_u prev pmpaddr = false)
    (hr : pmpRangeMatch (prev.toNat * 4) (pmpaddr.toNat * 4) addr.toNat width.toNat = .PMP_Match) :
    exec (pmpMatchAddr (.Physaddr addr) width ent pmpaddr prev) s = some (.PMP_Match, s) := by
  unfold pmpMatchAddr
  simp only [hA, hlt, Bool.false_eq_true, ↓reduceIte, toNatInt_mul4_toNat, toNatInt_toNat, hr]
  rfl

/-- `pmpRangeMatch` on a range covering the access. -/
theorem pmpRangeMatch_full (b e a w : Nat) (h1 : b ≤ a) (h2 : 0 < w) (h3 : a + w ≤ e) :
    pmpRangeMatch b e a w = .PMP_Match := by
  unfold pmpRangeMatch
  have c1 : ((a +i w ≤b b) || (e ≤b a)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have c2 : ((b ≤b a) && (a +i w ≤b e)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [c1, c2, Bool.false_eq_true, ↓reduceIte]

/-- Rocq `WpMmodeLeafBase.exec_pmpMatchAddr_tor0_match`. -/
theorem execPmpMatchAddrTor0Match (a wbv : BitVec 64) (ent : BitVec 8) (paddr : BitVec 64) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = .TOR) (hw : 0 < wbv.toNat)
    (hin : a.toNat + wbv.toNat ≤ paddr.toNat * 4) :
    exec (pmpMatchAddr (.Physaddr a) wbv ent paddr (zeros (n := 64))) s = some (.PMP_Match, s) := by
  apply execPmpMatchAddrTORMatch _ _ _ _ _ s hA
  · unfold zopz0zKzJ_u
    simp only [decide_eq_false_iff_not, BitVec.toNatInt, Int.ofNat_eq_natCast, zeros]
    have hz : (BitVec.zero 64).toNat = 0 := rfl
    omega
  · exact pmpRangeMatch_full _ _ _ _ (by simp [zeros]) hw (by simpa [zeros] using hin)

/-- Rocq `RiscvTryStep.exec_pmpCheck_machine_none`: every entry off, a machine-mode
access passes. -/
theorem execPmpCheckMachineNone (addr : physaddr) (width : Nat) (access : MemoryAccessType mem_payload)
    (s : ExecSt)
    (hoff : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF) :
    exec (pmpCheck addr width access .Machine) s = some (none, s) := by
  unfold pmpCheck
  rw [execCatchEarlyReturn]
  exec_run
  have hoff' : ∀ i : Int,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[i]!) = .OFF :=
    fun i => hoff i.toNat
  rw [execRForInConst _ rfl _ s]
  intro i _
  split
  all_goals
    exec_run [execPmpReadAddrReg, execPmpMatchAddrOFF _ _ _ _ _ s (hoff' i)]

/-- PMP entry 0 matches the access and its permission bits grant it: the check
passes at any privilege (the shared core of Rocq `SmodePte.exec_pmpCheck_supervisor_grant*`,
`WpSmodeGpr.exec_pmpCheck_supervisor_grant_*`, `PtTreeAdue.exec_pmpCheck_supervisor_grant_wpte`,
`WpAmo.exec_pmpCheck_supervisor_grant_amo`). -/
theorem execPmpCheckEnt0 (a : BitVec 64) (width : Nat) (acc : MemoryAccessType mem_payload) (priv : Privilege)
    (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match)
    (hrwx : exec (pmpCheckRWX (s.regs .pmpcfg_n)[0]! acc) s = some (true, s)) :
    exec (pmpCheck (.Physaddr a) width acc priv) s = some (none, s) := by
  have hA' : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[(0 : Int)]!) = .TOR := hA
  have hrwx' : exec (pmpCheckRWX (s.regs .pmpcfg_n)[(0 : Int)]! acc) s = some (true, s) := hrwx
  unfold pmpCheck
  rw [execCatchEarlyReturn]
  exec_run
  rw [execRForInFirstEarly _ _ s s none (by decide)]
  exec_run [execPmpReadAddrReg, Int.toNat_zero, execPmpMatchAddrTORMatch _ _ _ _ _ s hA' hlt hr, hrwx']

/-- Rocq `SmodePte.exec_pmpCheck_supervisor_grant` (fetch, X bit). -/
theorem execPmpCheckSupervisorGrant (a : BitVec 64) (width : Nat) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match)
    (hx : (_get_Pmpcfg_ent_X (s.regs .pmpcfg_n)[0]! == 1#1) = true) :
    exec (pmpCheck (.Physaddr a) width (.InstructionFetch ()) .Supervisor) s = some (none, s) :=
  execPmpCheckEnt0 a width _ _ s hA hlt hr (by unfold pmpCheckRWX; rw [hx]; rfl)

/-- Rocq `SmodePte.exec_pmpCheck_supervisor_grant_load` (page-table read, R bit). -/
theorem execPmpCheckSupervisorGrantLoad (a : BitVec 64) (width : Nat) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true) :
    exec (pmpCheck (.Physaddr a) width (.Load .PageTableEntry) .Supervisor) s = some (none, s) :=
  execPmpCheckEnt0 a width _ _ s hA hlt hr (by unfold pmpCheckRWX; rw [hR]; rfl)

/-- Rocq `WpSmodeGpr.exec_pmpCheck_supervisor_grant_load_data` (data read, R bit). -/
theorem execPmpCheckSupervisorGrantLoadData (a : BitVec 64) (width : Nat) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true) :
    exec (pmpCheck (.Physaddr a) width (.Load .Data) .Supervisor) s = some (none, s) :=
  execPmpCheckEnt0 a width _ _ s hA hlt hr (by unfold pmpCheckRWX; rw [hR]; rfl)

/-- Rocq `WpSmodeGpr.exec_pmpCheck_supervisor_grant_store` (data write, W bit). -/
theorem execPmpCheckSupervisorGrantStore (a : BitVec 64) (width : Nat) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match)
    (hW : (_get_Pmpcfg_ent_W (s.regs .pmpcfg_n)[0]! == 1#1) = true) :
    exec (pmpCheck (.Physaddr a) width (.Store .Data) .Supervisor) s = some (none, s) :=
  execPmpCheckEnt0 a width _ _ s hA hlt hr (by unfold pmpCheckRWX; rw [hW]; rfl)

/-- Rocq `PtTreeAdue.exec_pmpCheck_supervisor_grant_wpte` (page-table write, W bit). -/
theorem execPmpCheckSupervisorGrantWpte (a : BitVec 64) (width : Nat) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match)
    (hW : (_get_Pmpcfg_ent_W (s.regs .pmpcfg_n)[0]! == 1#1) = true) :
    exec (pmpCheck (.Physaddr a) width (.Store .PageTableEntry) .Supervisor) s = some (none, s) :=
  execPmpCheckEnt0 a width _ _ s hA hlt hr (by unfold pmpCheckRWX; rw [hW]; rfl)

/-- Rocq `WpAmo.exec_pmpCheck_supervisor_grant_amo` (AMO, R and W bits). -/
theorem execPmpCheckSupervisorGrantAmo (a : BitVec 64) (width : Nat) (aq rl : Bool) (s : ExecSt)
    (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[0]!) = .TOR)
    (hlt : zopz0zKzJ_u (zeros (n := 64)) (s.regs .pmpaddr_n)[0]! = false)
    (hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) ((s.regs .pmpaddr_n)[0]!.toNat * 4) a.toNat
      (to_bits (l := 64) width).toNat = .PMP_Match)
    (hR : (_get_Pmpcfg_ent_R (s.regs .pmpcfg_n)[0]! == 1#1) = true)
    (hW : (_get_Pmpcfg_ent_W (s.regs .pmpcfg_n)[0]! == 1#1) = true) :
    exec (pmpCheck (.Physaddr a) width (.Atomic (.AMOSWAP, aq, rl, .Data, .Data)) .Supervisor) s =
      some (none, s) :=
  execPmpCheckEnt0 a width _ _ s hA hlt hr (by unfold pmpCheckRWX; rw [hR, hW]; rfl)

/-- Rocq `WpMmodeLeafBase.pmp_tor0_grants`. -/
def pmpTor0Grants (cfg : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64) (ea : BitVec 64)
    (width : Nat) : Prop :=
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A cfg[0]!) = .TOR ∧ pmpLocked cfg[0]! = false ∧
    0 < width ∧ ea.toNat + width ≤ pmpaddrs[0]!.toNat * 4

/-- Rocq `WpMmodeLeafBase.exec_pmpCheck_machine_tor0`. -/
theorem execPmpCheckMachineTor0 (addr : BitVec 64) (width : Nat) (access : MemoryAccessType mem_payload)
    (s : ExecSt) (hg : pmpTor0Grants (s.regs .pmpcfg_n) (s.regs .pmpaddr_n) addr width)
    (hrwx : ∀ ent, ∃ b, exec (pmpCheckRWX ent access) s = some (b, s))
    (hwidth : (to_bits (l := 64) width).toNat = width) :
    exec (pmpCheck (.Physaddr addr) width access .Machine) s = some (none, s) := by
  obtain ⟨hA, hL, hw, hin⟩ := hg
  have hA' : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[(0 : Int)]!) = .TOR := hA
  have hL' : pmpLocked (s.regs .pmpcfg_n)[(0 : Int)]! = false := hL
  obtain ⟨b, hb⟩ := hrwx (s.regs .pmpcfg_n)[(0 : Int)]!
  have hm := execPmpMatchAddrTor0Match addr (to_bits (l := 64) width) _ (s.regs .pmpaddr_n)[0]! s hA'
    (by rw [hwidth]; exact hw) (by rw [hwidth]; exact hin)
  unfold pmpCheck
  rw [execCatchEarlyReturn]
  exec_run
  rw [execRForInFirstEarly _ _ s s none (by decide)]
  exec_run [execPmpReadAddrReg, Int.toNat_zero, hm, hb, hL', Functions.not]
  cases b <;> rfl

/-- `pmpRangeMatch` of a 4-byte cell access against 4-aligned bounds never
partially matches. -/
theorem pmpRangeMatch_cell (b e a w : Nat) (hb : b % 4 = 0) (he : e % 4 = 0) (h : a % 4 + w ≤ 4) :
    pmpRangeMatch b e a w = .PMP_NoMatch ∨ pmpRangeMatch b e a w = .PMP_Match := by
  unfold pmpRangeMatch
  by_cases c1 : ((a +i w ≤b b) || (e ≤b a)) = true
  · simp only [c1, ↓reduceIte, true_or]
  · have c2 : ((b ≤b a) && (a +i w ≤b e)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at c1
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    simp only [c1, c2, Bool.false_eq_true, ↓reduceIte, or_true]

theorem execPureCell (b e a w : Nat) (s : ExecSt) (hb : b % 4 = 0) (he : e % 4 = 0) (h : a % 4 + w ≤ 4) :
    exec (pure (pmpRangeMatch b e a w) : SailM pmpAddrMatch) s = some (.PMP_NoMatch, s) ∨
      exec (pure (pmpRangeMatch b e a w) : SailM pmpAddrMatch) s = some (.PMP_Match, s) := by
  rcases pmpRangeMatch_cell b e a w hb he h with r | r <;> simp [r]

/-- Rocq `RiscvTryStep.exec_pmpMatchAddr_machine_cell`: an access inside one
4-byte cell matches an entry fully or not at all. -/
theorem execPmpMatchAddrMachineCell (pa : physaddr) (wbv : BitVec 64) (ent : BitVec 8) (paddr prev : BitVec 64)
    (s : ExecSt) (h : (bits_of_physaddr pa).toNat % 4 + wbv.toNat ≤ 4) :
    exec (pmpMatchAddr pa wbv ent paddr prev) s = some (.PMP_NoMatch, s) ∨
      exec (pmpMatchAddr pa wbv ent paddr prev) s = some (.PMP_Match, s) := by
  obtain ⟨a⟩ := pa
  have h' : (BitVec.toNatInt a).toNat % 4 + (BitVec.toNatInt wbv).toNat ≤ 4 := by
    simp only [toNatInt_toNat]; exact h
  unfold pmpMatchAddr
  dsimp only
  have hb : ∀ x : BitVec 64, (BitVec.toNatInt x * 4).toNat % 4 = 0 := fun x => by
    simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]; omega
  have hb4 : ∀ x : BitVec 64, (BitVec.toNatInt x * 4 + 4).toNat % 4 = 0 := fun x => by
    simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]; omega
  have hb2 : ∀ x y : BitVec 64, ((BitVec.toNatInt x + BitVec.toNatInt y + 1) * 4).toNat % 4 = 0 :=
    fun x y => by simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]; omega
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact execPureCell _ _ _ _ s (hb _) (hb _) h'
  · exec_run
    exact execPureCell _ _ _ _ s (hb _) (hb4 _) h'
  · exact execPureCell _ _ _ _ s (hb _) (hb2 _ _) h'

/-- Rocq `RiscvTryStep.exec_pmpCheck_machine_unlocked`: every entry unlocked and
an access inside one 4-byte cell: a machine-mode access passes. -/
theorem execPmpCheckMachineUnlocked (addr : physaddr) (width : Nat) (access : MemoryAccessType mem_payload)
    (s : ExecSt) (hunl : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hrwx : ∀ ent, ∃ b, exec (pmpCheckRWX ent access) s = some (b, s))
    (hcell : (bits_of_physaddr addr).toNat % 4 + (to_bits (l := 64) width).toNat ≤ 4) :
    exec (pmpCheck addr width access .Machine) s = some (none, s) := by
  unfold pmpCheck
  rw [execCatchEarlyReturn]
  exec_run
  generalize hx : execR (R := Option ExceptionType)
    (forIn (m := SailME (Option ExceptionType)) (_ : IntRange) () _) s = x
  have hf : x = some (.inr (), s) ∨ x = some (.inl none, s) :=
    hx ▸ execRForInAllow _ rfl _ s none (fun i _ => by
      have hu : pmpLocked (s.regs .pmpcfg_n)[i]! = false := hunl i.toNat
      obtain ⟨b, hb⟩ := hrwx (s.regs .pmpcfg_n)[i]!
      have hmm : (Privilege.Machine == Privilege.Machine) = true := rfl
      split
      · exec_run [execPmpReadAddrReg]
        rcases execPmpMatchAddrMachineCell addr (to_bits (l := 64) width) (s.regs .pmpcfg_n)[i]!
          (s.regs .pmpaddr_n)[i.toNat]! (s.regs .pmpaddr_n)[(i - 1).toNat]! s hcell with e | e <;>
        simp only [e] <;> exec_run [hb, hu, Functions.not, hmm, Bool.not_false, Bool.and_true, Bool.or_true, true_or, or_true]
      · exec_run [execPmpReadAddrReg]
        rcases execPmpMatchAddrMachineCell addr (to_bits (l := 64) width) (s.regs .pmpcfg_n)[i]!
          (s.regs .pmpaddr_n)[i.toNat]! zeros s hcell with e | e <;>
        simp only [e] <;> exec_run [hb, hu, Functions.not, hmm, Bool.not_false, Bool.and_true, Bool.or_true, true_or, or_true])
  rcases hf with rfl | rfl <;> rfl

/-- Rocq `RiscvFetchExec.exec_pmpCheck_machine_unlocked_ifetch4`. -/
theorem execPmpCheckMachineUnlockedIfetch4 (addr : BitVec 64) (s : ExecSt)
    (hunl : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true) :
    exec (pmpCheck (.Physaddr addr) 4 (.InstructionFetch ()) .Machine) s = some (none, s) := by
  have h4 := isAlignedVaddrMod addr 4 (by decide) hal
  exact execPmpCheckMachineUnlocked _ 4 _ s hunl (fun ent => ⟨_, rfl⟩)
    (by show addr.toNat % 4 + (to_bits (l := 64) 4).toNat ≤ 4; rw [show (to_bits (l := 64) 4).toNat = 4 from rfl]; omega)

/-- Rocq `RiscvFetchExec.exec_pmpCheck_machine_unlocked_ifetch2`. -/
theorem execPmpCheckMachineUnlockedIfetch2 (addr : BitVec 64) (s : ExecSt)
    (hunl : ∀ i : Nat, pmpLocked (s.regs .pmpcfg_n)[i]! = false)
    (hal : is_aligned_paddr (.Physaddr addr) 2 = true) :
    exec (pmpCheck (.Physaddr addr) 2 (.InstructionFetch ()) .Machine) s = some (none, s) := by
  have h2 := isAlignedVaddrMod addr 2 (by decide) hal
  exact execPmpCheckMachineUnlocked _ 2 _ s hunl (fun ent => ⟨_, rfl⟩)
    (by show addr.toNat % 4 + (to_bits (l := 64) 2).toNat ≤ 4; rw [show (to_bits (l := 64) 2).toNat = 2 from rfl]; omega)

/-! ## 2. PMA (Rocq `RiscvFetchExec`, `WpMmodeLeafBase`, `MemAccessGen`, `WpAmo`, `PtTreeAdue`) -/

/-- Rocq `RiscvExtras.pma_ok_aligned`. -/
def pmaOkAligned : Phys_Mem_Access_Info := { splittable := .CannotSplit, granule_size_exp := 0 }

/-- Rocq `RiscvFetchExec.exec_pmaCheck_ram` / `_ram_2`, at any width (an aligned fetch from an
executable region). -/
theorem execPmaCheckRamFetch (addr : BitVec 64) (k : Nat) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) k = some region)
    (hal : is_aligned_paddr (.Physaddr addr) k = true)
    (hx : (override_PMA region.attributes pbmt).executable = true) :
    exec (pmaCheck (.Physaddr addr) k (.InstructionFetch ()) pbmt false) s = some (.Ok pmaOkAligned, s) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  unfold pmaCheck mag_pma_check
  rw [execCatchEarlyReturn]
  exec_run [hm, hx, hal, Functions.not, Bool.true_or]
  rfl

/-- Rocq `MemAccessGen.exec_pmaCheck_ram_load_g`. -/
theorem execPmaCheckRamLoadG (k : Nat) (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) k = some region)
    (hal : is_aligned_paddr (.Physaddr addr) k = true)
    (hr : (override_PMA region.attributes pbmt).readable = true) :
    exec (pmaCheck (.Physaddr addr) k (.Load .Data) pbmt false) s = some (.Ok pmaOkAligned, s) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  unfold pmaCheck mag_pma_check
  rw [execCatchEarlyReturn]
  exec_run [hm, hr, hal, Functions.not, Bool.true_or]
  rfl

/-- Rocq `MemAccessGen.exec_pmaCheck_ram_store_g`. -/
theorem execPmaCheckRamStoreG (k : Nat) (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) k = some region)
    (hal : is_aligned_paddr (.Physaddr addr) k = true)
    (hw : (override_PMA region.attributes pbmt).writable = true) :
    exec (pmaCheck (.Physaddr addr) k (.Store .Data) pbmt false) s = some (.Ok pmaOkAligned, s) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  unfold pmaCheck mag_pma_check
  rw [execCatchEarlyReturn]
  exec_run [hm, hw, hal, Functions.not, Bool.true_or]
  rfl

/-- Rocq `WpMmodeLeafBase.exec_pmaCheck_ram_store`. -/
theorem execPmaCheckRamStore (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region) (s : ExecSt)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).writable = true) :
    exec (pmaCheck (.Physaddr addr) 8 (.Store .Data) pbmt false) s = some (.Ok pmaOkAligned, s) :=
  execPmaCheckRamStoreG 8 addr pbmt region s hm hal hw

/-- Rocq `RiscvFetchExec.exec_pmaCheck_ram`. -/
theorem execPmaCheckRam (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region) (s : ExecSt)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hx : (override_PMA region.attributes pbmt).executable = true) :
    exec (pmaCheck (.Physaddr addr) 4 (.InstructionFetch ()) pbmt false) s = some (.Ok pmaOkAligned, s) :=
  execPmaCheckRamFetch addr 4 pbmt region s hm hal hx

/-- Rocq `RiscvFetchExec.exec_pmaCheck_ram_2`. -/
theorem execPmaCheckRam2 (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region) (s : ExecSt)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 2 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 2 = true)
    (hx : (override_PMA region.attributes pbmt).executable = true) :
    exec (pmaCheck (.Physaddr addr) 2 (.InstructionFetch ()) pbmt false) s = some (.Ok pmaOkAligned, s) :=
  execPmaCheckRamFetch addr 2 pbmt region s hm hal hx

/-- Rocq `PtTreeAdue.exec_pmaCheck_ram_wpte`. -/
theorem execPmaCheckRamWpteRoc (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region)
    (roc : Bool) (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).supports_pte_write = true) :
    exec (pmaCheck (.Physaddr addr) 8 (.Store .PageTableEntry) pbmt roc) s = some (.Ok pmaOkAligned, s) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  unfold pmaCheck mag_pma_check
  rw [execCatchEarlyReturn]
  exec_run [hm, hw, hal, Functions.not, Bool.true_or]
  rfl

theorem execPmaCheckRamWpte (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region) (s : ExecSt)
    (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hw : (override_PMA region.attributes pbmt).supports_pte_write = true) :
    exec (pmaCheck (.Physaddr addr) 8 (.Store .PageTableEntry) pbmt false) s = some (.Ok pmaOkAligned, s) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  unfold pmaCheck mag_pma_check
  rw [execCatchEarlyReturn]
  exec_run [hm, hw, hal, Functions.not, Bool.true_or]
  rfl

/-- The page-table read twin (used by Rocq `SmodePte.exec_read_pte_S`). -/
theorem execPmaCheckRamPte (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region) (roc : Bool)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 8 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 8 = true)
    (hr : (override_PMA region.attributes pbmt).supports_pte_read = true) :
    exec (pmaCheck (.Physaddr addr) 8 (.Load .PageTableEntry) pbmt roc) s = some (.Ok pmaOkAligned, s) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  unfold pmaCheck mag_pma_check
  rw [execCatchEarlyReturn]
  exec_run [hm, hr, hal, Functions.not, Bool.true_or]
  rfl

/-- Rocq `WpAmo.exec_pmaCheck_ram_amo_4`. -/
theorem execPmaCheckRamAmo4 (addr : BitVec 64) (pbmt : page_based_mem_type) (region : PMA_Region) (aq rl : Bool)
    (s : ExecSt) (hm : matching_pma_region (s.regs .pma_regions) (.Physaddr addr) 4 = some region)
    (hal : is_aligned_paddr (.Physaddr addr) 4 = true)
    (hr : (override_PMA region.attributes pbmt).readable = true)
    (hw : (override_PMA region.attributes pbmt).writable = true)
    (ha : pma_allows_atomic_op (override_PMA region.attributes pbmt).atomic_support .AMOSWAP 4 = true) :
    exec (pmaCheck (.Physaddr addr) 4 (.Atomic (.AMOSWAP, aq, rl, .Data, .Data)) pbmt true) s =
      some (.Ok pmaOkAligned, s) := by
  obtain ⟨attrs, sz, inc, base⟩ := region
  unfold pmaCheck mag_pma_check
  rw [execCatchEarlyReturn]
  exec_run [hm, hr, hw, ha, hal, Functions.not, Bool.true_or]
  rfl

end Weak
