/-
MachCSL: the CSR check at User over the user footprint's read set, the NAMED
numbers (lane U3-A; U1-X3's `UExecCsrTab` at the smaller pin `uxrPin`; Rocq
`UserCsr.v` §3b–§3f).

One kernel evaluation per access type and quarter of the 4096 numbers, at a
SYMBOLIC file `f` (only `mstatus` is read from it, as data): every number is
default (`uxrDflt`, skipped by `||`), one of the three `FS`-gated ones or an
eager one (`uxrExc`, `uclEager`), or its check at `uxrPin` answers
`CSR_Illegal`.  That the walk succeeds at `uxrPin` is the fact that its reads
stay inside `uclReads` (the user footprint).
-/
import MachCSL.UclCsrPin
import MachCSL.UExecCsrTab

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- The check at `uxrPin` answers `CSR_Illegal`. -/
def uclIll (f : RegFile) (acc : CSRAccessType) (n : Nat) : Bool :=
  match runRead (uxrPin f) (check_CSR_result (BitVec.ofNat 12 n) Privilege.User acc) with
  | some (.CSR_Illegal (), _) => true
  | _ => false

/-- The table's check of one number. -/
def uclChk (f : RegFile) (acc : CSRAccessType) (n : Nat) : Bool :=
  uxrDflt (BitVec.ofNat 12 n) || uxrExc n || uclEager n || uclIll f acc n

/-- The table over a quarter of the numbers. -/
def uclQuarter (f : RegFile) (acc : CSRAccessType) (q : Nat) : Bool :=
  (List.range 1024).all (fun n => uclChk f acc (n + 1024 * q))

theorem ucl_tab_R0 (f : RegFile) : uclQuarter f .CSRRead 0 = true := by kernel_rfl
theorem ucl_tab_R1 (f : RegFile) : uclQuarter f .CSRRead 1 = true := by kernel_rfl
theorem ucl_tab_R2 (f : RegFile) : uclQuarter f .CSRRead 2 = true := by kernel_rfl
theorem ucl_tab_R3 (f : RegFile) : uclQuarter f .CSRRead 3 = true := by kernel_rfl
theorem ucl_tab_W0 (f : RegFile) : uclQuarter f .CSRWrite 0 = true := by kernel_rfl
theorem ucl_tab_W1 (f : RegFile) : uclQuarter f .CSRWrite 1 = true := by kernel_rfl
theorem ucl_tab_W2 (f : RegFile) : uclQuarter f .CSRWrite 2 = true := by kernel_rfl
theorem ucl_tab_W3 (f : RegFile) : uclQuarter f .CSRWrite 3 = true := by kernel_rfl
theorem ucl_tab_RW0 (f : RegFile) : uclQuarter f .CSRReadWrite 0 = true := by kernel_rfl
theorem ucl_tab_RW1 (f : RegFile) : uclQuarter f .CSRReadWrite 1 = true := by kernel_rfl
theorem ucl_tab_RW2 (f : RegFile) : uclQuarter f .CSRReadWrite 2 = true := by kernel_rfl
theorem ucl_tab_RW3 (f : RegFile) : uclQuarter f .CSRReadWrite 3 = true := by kernel_rfl

/-- **The table**: every number is default, excepted, eager, or `CSR_Illegal`
at `uxrPin`. -/
theorem ucl_tab (f : RegFile) (acc : CSRAccessType) (n : Nat) (hn : n < 4096) :
    uclChk f acc n = true := by
  have hq : ∀ q, uclQuarter f acc q = true → ∀ k, k < 1024 → uclChk f acc (k + 1024 * q) = true :=
    fun q h k hk => List.all_eq_true.1 h k (List.mem_range.2 hk)
  have h4 : ∀ q, q < 4 → uclQuarter f acc q = true := by
    intro q hq4
    have hq' : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
    cases acc <;> rcases hq' with rfl | rfl | rfl | rfl
    · exact ucl_tab_R0 f
    · exact ucl_tab_R1 f
    · exact ucl_tab_R2 f
    · exact ucl_tab_R3 f
    · exact ucl_tab_W0 f
    · exact ucl_tab_W1 f
    · exact ucl_tab_W2 f
    · exact ucl_tab_W3 f
    · exact ucl_tab_RW0 f
    · exact ucl_tab_RW1 f
    · exact ucl_tab_RW2 f
    · exact ucl_tab_RW3 f
  have := hq (n / 1024) (h4 _ (by omega)) (n % 1024) (Nat.mod_lt _ (by decide))
  rwa [Nat.mod_add_div] at this

/-- A named number outside `uxrExc` and `uclEager`: the check at `uxrPin` is
`CSR_Illegal`. -/
theorem ucl_ccr_spec (f : RegFile) (c : BitVec 12) (acc : CSRAccessType)
    (hd : uxrDflt c = false) (he : uxrExc c.toNat = false) (hz : uclEager c.toNat = false) :
    ∃ b, runRead (uxrPin f) (check_CSR_result c Privilege.User acc) =
      some (CSRCheckResult.CSR_Illegal (), b) := by
  have ht : uclIll f acc c.toNat = true := by
    have := ucl_tab f acc c.toNat c.isLt
    simpa [uclChk, he, hd, hz] using this
  unfold uclIll at ht
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at ht
  split at ht
  · rename_i b hr; exact ⟨b, hr⟩
  · exact absurd ht Bool.false_ne_true

end MachCSL
