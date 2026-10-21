import LeanRV64D.LeanRV64D
import LeanRV64D.Arith
import LeanRV64D.Prelude

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ArchSem

noncomputable section
namespace LeanRV64D

open ArchSem

namespace Functions

open zicondop
open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vstart_class
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open vector_support
open uop
open trigger_addr_type
open tdata
open stateen_bit
open sopw
open sop
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfwvvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open page_based_mem_type
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open ntl_type
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open misaligned_exception
open mem_payload
open maskfunct3
open mask_type
open loop_chain_state
open landing_pad_expectation
open iop
open instruction
open indexed_mop
open hlvop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open float_class
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open event_csr
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cbie
open cacheop
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open breakpoint_cause
open bop
open biop_zbs
open barrier_kind
open amoop
open agtype
open access_kind
open XtvecModeReservedBehavior
open XipReadType
open XenvcfgCbieReservedBehavior
open WaitReason
open VectorHalf
open Trigger
open Trig_Type
open Trig_Match
open Trig_Action
open TrapVectorMode
open TrapCause
open TranslationStage
open Step
open Splittability
open Software_Check_Code
open Signedness
open Sdtrig_breakpoint_reentrancy
open SWCheckCodes
open SATPMode
open Reservability
open Register
open RV32ZdinxOddRegisterReservedBehavior
open Privileged_ISA_Version
open Privilege
open PointerMaskingMode
open PmpWriteOnlyReservedBehavior
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open PM_Ext
open OOBVstartReservedBehavior
open MemoryTriggerPayload
open MemoryRegionType
open MemoryAccessType
open InterruptType
open IllegalVtypeReservedBehavior
open ISA_Format
open Hit
open HartState
open HGATPMode
open FflagsDirtyPolicy
open FetchResult
open FetchBytes_Result
open FeatureEnabledResult
open FcsrRmReservedBehavior
open Ext_DataAddr_Check
open ExtStatus
open ExtContextPolicy
open ExecutionResult
open ExceptionType
open Event
open Compare_Selection
open CSRCheckResult
open CSRBitConfig
open CSRAccessType
open AtomicSupport
open Architecture
open AmocasOddRegisterReservedBehavior

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ≥ 0 ∧ (k_m % 8) = 0 -/
def brev8 (input : (BitVec k_m)) : (BitVec k_m) := Id.run do
  let output : (BitVec k_m) := (zeros (n := (Sail.BitVec.length input)))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length output) -i 8)
  let mut loop_vars := output
  for i in [loop_i_lower:loop_i_upper:8]i do
    let output := loop_vars
    loop_vars :=
      (Sail.BitVec.updateSubrange output (i +i 7) i
        (reverse_bits (Sail.BitVec.extractLsb input (i +i 7) i)))
  (pure loop_vars)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def carryless_mul (a : (BitVec k_n)) (b : (BitVec k_n)) : (BitVec (2 * k_n)) := Id.run do
  let result : (BitVec (2 * k_n)) := (zeros (n := (2 *i (Sail.BitVec.length b))))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length b) -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars :=
      if (((BitVec.access a i) == 1#1) : Bool)
      then (result ^^^ ((zero_extend (m := (2 *i (Sail.BitVec.length b))) b) <<< i))
      else result
  (pure loop_vars)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def carryless_mulr (a : (BitVec k_n)) (b : (BitVec k_n)) : (BitVec k_n) := Id.run do
  let result : (BitVec k_n) := (zeros (n := (Sail.BitVec.length b)))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length result) -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars :=
      if (((BitVec.access a i) == 1#1) : Bool)
      then (result ^^^ (b >>> (((Sail.BitVec.length result) -i i) -i 1)))
      else result
  (pure loop_vars)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n > 0 -/
def carryless_mul_reversed (a : (BitVec k_n)) (b : (BitVec k_n)) : (BitVec k_n) :=
  let prod := (carryless_mul (reverse_bits a) (reverse_bits b))
  (reverse_bits (Sail.BitVec.extractLsb prod ((Sail.BitVec.length b) -i 1) 0))

/-- Type quantifiers: l : Nat, l ≥ 0, l > 0 -/
def mult_to_bits_half {l : _} (sign1 : Signedness) (sign2 : Signedness) (rs1_bits : (BitVec l)) (rs2_bits : (BitVec l)) (result_part : VectorHalf) : (BitVec l) :=
  let rs1_int : Int :=
    match sign1 with
    | .Signed => (BitVec.toInt rs1_bits)
    | .Unsigned => (BitVec.toNatInt rs1_bits)
  let rs2_int : Int :=
    match sign2 with
    | .Signed => (BitVec.toInt rs2_bits)
    | .Unsigned => (BitVec.toNatInt rs2_bits)
  let result_wide := (to_bits_truncate (l := (2 *i l)) (rs1_int *i rs2_int))
  match result_part with
  | .High => (Sail.BitVec.extractLsb result_wide ((2 *i l) -i 1) l)
  | .Low => (Sail.BitVec.extractLsb result_wide (l -i 1) 0)

def cmulr_equivalence (a : (BitVec 16)) (b : (BitVec 16)) : Bool :=
  ((carryless_mul_reversed a b) == (carryless_mulr a b))

/-- Type quantifiers: k_m : Nat, k_m ≥ 0, k_m ≥ 0 ∧ (k_m % 8) = 0 -/
def rev8 (input : (BitVec k_m)) : (BitVec k_m) := Id.run do
  let output : (BitVec k_m) := (zeros (n := (Sail.BitVec.length input)))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length output) -i 8)
  let mut loop_vars := output
  for i in [loop_i_lower:loop_i_upper:8]i do
    let output := loop_vars
    loop_vars :=
      (Sail.BitVec.updateSubrange output (i +i 7) i
        (Sail.BitVec.extractLsb input (((Sail.BitVec.length output) -i i) -i 1)
          (((Sail.BitVec.length output) -i i) -i 8)))
  (pure loop_vars)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def count_ones (x : (BitVec k_n)) : SailM Nat := do
  let count : Nat := 0
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length x) -i 1)
  let mut loop_vars := count
  for i in [loop_i_lower:loop_i_upper:1]i do
    let count := loop_vars
    loop_vars ← do
      if (((BitVec.access x i) == 1#1) : Bool)
      then
        (do
          let new_count := (count +i 1)
          sail_assert (new_count ≤b (Sail.BitVec.length x)) "core/arithmetic.sail:85.28-85.29"
          (pure new_count))
      else (pure count)
  (pure loop_vars)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def lowest_index_of (x : (BitVec k_n)) (b : (BitVec 1)) : (Option Nat) := ExceptM.run do
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length x) -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if (((BitVec.access x i) == b) : Bool)
      then throw ((some i) : (Option Nat))
      else (pure ())
  (pure loop_vars)
  (pure none)

def test_lowest_index_of (_ : Unit) : SailM Unit := do
  sail_assert ((lowest_index_of 0x0#4 1#1) == none) "core/arithmetic.sail:102.44-102.45"
  sail_assert ((lowest_index_of 0x0#4 0#1) == (some 0)) "core/arithmetic.sail:103.45-103.46"
  sail_assert ((lowest_index_of 0x1#4 0#1) == (some 1)) "core/arithmetic.sail:104.45-104.46"
  sail_assert ((lowest_index_of 0x8#4 0#1) == (some 0)) "core/arithmetic.sail:105.45-105.46"
  sail_assert ((lowest_index_of 0xE#4 0#1) == (some 0)) "core/arithmetic.sail:106.45-106.46"
  sail_assert ((lowest_index_of 0x7#4 0#1) == (some 3)) "core/arithmetic.sail:107.45-107.46"

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def highest_index_of (x : (BitVec k_n)) (b : (BitVec 1)) : (Option Nat) := ExceptM.run do
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length x) -i 1)
  let mut loop_vars := ()
  for i in [loop_i_upper:loop_i_lower:-1]i do
    let () := loop_vars
    loop_vars ← do
      if (((BitVec.access x i) == b) : Bool)
      then throw ((some i) : (Option Nat))
      else (pure ())
  (pure loop_vars)
  (pure none)

def test_highest_index_of (_ : Unit) : SailM Unit := do
  sail_assert ((highest_index_of 0x0#4 1#1) == none) "core/arithmetic.sail:120.45-120.46"
  sail_assert ((highest_index_of 0x0#4 0#1) == (some 3)) "core/arithmetic.sail:121.46-121.47"
  sail_assert ((highest_index_of 0x1#4 0#1) == (some 3)) "core/arithmetic.sail:122.46-122.47"
  sail_assert ((highest_index_of 0x8#4 0#1) == (some 2)) "core/arithmetic.sail:123.46-123.47"
  sail_assert ((highest_index_of 0xE#4 0#1) == (some 0)) "core/arithmetic.sail:124.46-124.47"
  sail_assert ((highest_index_of 0x7#4 0#1) == (some 3)) "core/arithmetic.sail:125.46-125.47"

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def least_significant_zero (x : (BitVec k_n)) : (Option Nat) :=
  (lowest_index_of x 0#1)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def least_significant_one (x : (BitVec k_n)) : (Option Nat) :=
  (lowest_index_of x 1#1)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def most_significant_zero (x : (BitVec k_n)) : (Option Nat) :=
  (highest_index_of x 0#1)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ≥ 0 -/
def most_significant_one (x : (BitVec k_n)) : (Option Nat) :=
  (highest_index_of x 1#1)

