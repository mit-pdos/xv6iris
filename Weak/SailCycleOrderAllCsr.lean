/-
Weak: **W-SCO (A) — footprints of the CSR machinery** (plan rev 36 §C W-SCO (A) (1)(a)):
`read_CSR`, `write_CSR` (the CSR tables, walked once each: their literal matches unfold to `if`
chains, the closed conditions of the model's duplicated fall-backs are decided), the access
checks and `doCSR`.  Lean-only.
-/
import Weak.SailCycleOrderAllMem

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderFp

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpReadCSR (merge_var : (BitVec 12)) :
    fpT (read_CSR merge_var) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpWriteCSR (arg0 : (BitVec 12)) (arg1 : (BitVec 64)) :
    fpT (write_CSR arg0 arg1) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpIsCSRAccessible (arg0 : (BitVec 12)) (arg1 : Privilege) (arg2 : CSRAccessType) :
    fpT (is_CSR_accessible arg0 arg1 arg2) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpCheckCSRResult (csr : (BitVec 12)) (p : Privilege) (access_type : CSRAccessType) :
    fpT (check_CSR_result csr p access_type) := by
  fp_walk

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8000 in
@[fp_reg] theorem fpDoCSR (csr : (BitVec 12)) (rs1_val : (BitVec 64)) (rd : regidx) (op : csrop) (access_type : CSRAccessType) :
    fpT (doCSR csr rs1_val rd op access_type) := by
  fp_walk


end SailCycleOrderFp
end Weak
