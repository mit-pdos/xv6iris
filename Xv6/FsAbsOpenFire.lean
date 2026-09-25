/-
**THE ROW READINGS OF AN ERA NODE (pure): what a fire reads off a loaded
record's type.**  A PARTIAL port of Rocq `FsAbsOpenFire.v`
(`/shared/xv6rocq/iris/FsAbsOpenFire.v`, 424 lines): its section 0 ("THE
ROW READINGS OF AN ERA NODE (pure, no binder)"), WHOLE.

WHY PARTIAL (brief fs7 §7.2 A5 / D10).  Wave 7's fileread/filewrite need
only this file's pure readings -- Rocq `ProofFilewrite.v` imports
FsAbsOpenFire for `opf_era_file_row` and `opf_era_file_typed` alone, and
`FsAbsWriteFire.wrf_write_row_dist` calls `opf_era_file_row`.  The rest of
Rocq's file is sys_open's: item 1 (`opf_start_of_open`, over
`SysOpenDefs.namei_walk_pre_era` and `FsAbsStart.ex_start`), item 2 (the
terminal fire `opf_open_fire`, over `SysOpenDefs.aopen_commit_at`) and
item 3 (the trunc fire `opf_atrunc_fire`, over `SysOpenDefs.atrunc_commit_at`
and `FsAbsDelta.delta_trunc`).  Those need `SysOpenDefs`, `FsAbsEra` and
`FsAbsMknodFire`, none of which is ported; they land with sys_open (wave
7b, D9) and are APPENDED to this file then, so the one-Lean-file-per-Rocq-
file rule holds.

Rocq's header for this section, kept:

> THE READING BRIDGE is `opf_trunc_row`: the truncated record reads `AFile
> []` because `SpecItrunc.di_trunc` zeroes `di_size` and `fn_file_bytes` is
> `file_bytes _ 0 = []`, while the TYPE and the COUNT ride untouched --
> which is what makes the trunc delta collapse to the one-row insert and
> what makes the receipt's nlink the OBSERVED one.

## Deviations from Rocq

1. The `` `{XI : CurCtx} `` binder every lemma of this section carries is
   dropped: no statement or proof reads it (a TSO-rebase append, Rocq
   `FsAbsDelta.v`'s header says the same of `delta_trunc`), and the Lean
   `eraNode` takes no context.
2. `bv_unsigned (di_type dn)` is `dn.diType.toNat`; `FsImg.T_FILE_z` is
   `Xv6.T_FILE`, `T_DIR_z` is `Xv6.T_DIR_z` (both `Nat`).
3. `FsAbsMknodFire.mkf_era_is_dir` (which `opf_era_dir_row` calls, and which
   lives in an unported file) is stated here as `opfEra_is_dir`.
4. Names: `opf_era_type` → `opfEra_type`, `opf_trunc_row` → `opfTrunc_row`,
   and so on (camel head, Rocq's snake tail).

## Dropped/simplified vs Rocq

Nothing from section 0.  Sections 1-3 are DEFERRED to sys_open (above), not
dropped.
-/
import Xv6.FsAbsDefs
import Xv6.FsStateEraPure
import Xv6.SpecItrunc

namespace Xv6

open Iris.Std MachCSL

/-! ## 0.  The row readings of an era node (pure) -/

/-- Rocq's `opf_era_type`. -/
theorem opfEra_type (dn : Dinode) (bm : Blkmap) (data : Nat → List (BitVec 8)) :
    fnType (eraNode dn bm data) = dn.diType.toNat := rfl

/-- Rocq's `opf_era_not_dir`. -/
theorem opfEra_not_dir (dn : Dinode) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (h : dn.diType.toNat ≠ T_DIR_z) : fnIsDir (eraNode dn bm data) = false := by
  unfold fnIsDir
  rw [opfEra_type]
  exact decide_eq_false h

/-- Rocq's `FsAbsMknodFire.mkf_era_is_dir` (deviation 3). -/
theorem opfEra_is_dir (dn : Dinode) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (h : dn.diType.toNat = T_DIR_z) : fnIsDir (eraNode dn bm data) = true := by
  unfold fnIsDir
  rw [opfEra_type]
  exact decide_eq_true h

/-- THE FILE ROW: the abstract node is the record's bytes at its own count
(Rocq's `opf_era_file_row`). -/
theorem opfEra_file_row (dn : Dinode) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (hty : dn.diType.toNat = T_FILE) :
    absRow (eraNode dn bm data) =
      ⟨.AFile (fnFileBytes (eraNode dn bm data)), fnNlink (eraNode dn bm data)⟩ := by
  have hnd : fnIsDir (eraNode dn bm data) = false :=
    opfEra_not_dir dn bm data (by rw [hty]; decide)
  have ht : fnType (eraNode dn bm data) = T_FILE := hty
  simp [absRow, absNode, hnd, ht]

/-- THE DEVICE ROW: the major/minor pair straight off the record (Rocq's
`opf_era_dev_row`). -/
theorem opfEra_dev_row (dn : Dinode) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (hnd : dn.diType.toNat ≠ T_DIR_z) (hnf : dn.diType.toNat ≠ T_FILE) :
    absRow (eraNode dn bm data) =
      ⟨.ADev dn.diMajor.toNat dn.diMinor.toNat, fnNlink (eraNode dn bm data)⟩ := by
  have hd : fnIsDir (eraNode dn bm data) = false := opfEra_not_dir dn bm data hnd
  have ht : fnType (eraNode dn bm data) ≠ T_FILE := hnf
  simp [absRow, absNode, hd, ht, fnMajor, fnMinor, eraNode_rec]

/-- THE DIRECTORY ROW, for symmetry (Rocq's `opf_era_dir_row`). -/
theorem opfEra_dir_row (dn : Dinode) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (hty : dn.diType.toNat = T_DIR_z) :
    absRow (eraNode dn bm data) =
      ⟨.ADir (dirEntries (eraNode dn bm data)), fnNlink (eraNode dn bm data)⟩ :=
  absRow_dir_eq _ (opfEra_is_dir dn bm data hty)

/-! ### The trunc reading bridge -/

/-- Rocq's `opf_trunc_size`. -/
theorem opfTrunc_size (dn : Dinode) (bm' : Blkmap) (data' : Nat → List (BitVec 8)) :
    fnSize (eraNode (diTrunc dn) bm' data') = 0 := rfl

/-- Rocq's `opf_trunc_bytes`. -/
theorem opfTrunc_bytes (dn : Dinode) (bm' : Blkmap) (data' : Nat → List (BitVec 8)) :
    fnFileBytes (eraNode (diTrunc dn) bm' data') = [] := by
  unfold fnFileBytes
  rw [opfTrunc_size]
  rfl

/-- Rocq's `opf_trunc_nlink`. -/
theorem opfTrunc_nlink (dn : Dinode) (bm bm' : Blkmap) (data data' : Nat → List (BitVec 8)) :
    fnNlink (eraNode (diTrunc dn) bm' data') = fnNlink (eraNode dn bm data) := rfl

/-- Rocq's `opf_trunc_row`: the truncated record reads `AFile []` at the
OBSERVED nlink. -/
theorem opfTrunc_row (dn : Dinode) (bm bm' : Blkmap) (data data' : Nat → List (BitVec 8))
    (hty : dn.diType.toNat = T_FILE) :
    absRow (eraNode (diTrunc dn) bm' data') = ⟨.AFile [], fnNlink (eraNode dn bm data)⟩ := by
  rw [opfEra_file_row (diTrunc dn) bm' data' hty, opfTrunc_bytes dn bm' data',
    opfTrunc_nlink dn bm bm' data data']

/-! ### The typed row, as `absOf` (E2-V) -/

/-- an era node whose record has a nonzero type has a row (Rocq's
`opf_era_typed`) -/
theorem opfEra_typed (dn : Dinode) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (h : dn.diType.toNat ≠ 0) : fnType (eraNode dn bm data) ≠ 0 := h

/-- ...which every `inodeOk` payload has: its fourth clause is the type
(Rocq's `opf_era_typed_ok`) -/
theorem opfEra_typed_ok (cov : Std.ExtTreeSet Nat compare) (logstart : Nat) (dn : Dinode)
    (bm : Blkmap) (data : Nat → List (BitVec 8)) (h : inodeOk cov logstart dn bm data) :
    fnType (eraNode dn bm data) ≠ 0 :=
  opfEra_typed dn bm data h.2.2.2.1

/-- a FILE record is typed (Rocq's `opf_era_file_typed`) -/
theorem opfEra_file_typed (dn : Dinode) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (hty : dn.diType.toNat = T_FILE) : fnType (eraNode dn bm data) ≠ 0 := by
  apply opfEra_typed
  rw [hty]; decide

/-- a record with a nonzero count is LIVE (Rocq's `opf_era_live`; E2-V2) -/
theorem opfEra_live (dn : Dinode) (bm : Blkmap) (data : Nat → List (BitVec 8))
    (hnz : dn.diNlink.toNat ≠ 0) : fnNlink (eraNode dn bm data) ≠ 0 := hnz

end Xv6
