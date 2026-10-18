import LeanRV64D.Flow
import LeanRV64D.Arith
import LeanRV64D.Prelude
import LeanRV64D.Xlen
import LeanRV64D.MemAddrtype
import LeanRV64D.PlatformConfig
import LeanRV64D.Types
import LeanRV64D.VmemTypes
import LeanRV64D.AddrChecks
import LeanRV64D.SyncException
import LeanRV64D.SdtrigControl
import LeanRV64D.PmUtils
import LeanRV64D.SysControl
import LeanRV64D.SplitAccessUtils
import LeanRV64D.Pma
import LeanRV64D.Mem
import LeanRV64D.Vmem
import LeanRV64D.InstsBegin

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

/-- Type quantifiers: k_ex1173329_ : Bool -/
def plat_misaligned_exception (access : (MemoryAccessType mem_payload)) (res : Bool) : (Option misaligned_exception) :=
  if ((is_amo_access access) : Bool)
  then plat_misaligned_access.amo
  else
    (if (res : Bool)
    then plat_misaligned_access.lrsc
    else
      (if ((is_vector_access access) : Bool)
      then plat_misaligned_access.vector
      else plat_misaligned_access.load_store))

def is_vmem_active (eff_priv : Privilege) : SailM Bool := do
  if ((privLevel_is_virtual eff_priv) : Bool)
  then
    (do
      if ((bne (← (vsatp_mode ())) Bare) : Bool)
      then (pure true)
      else (pure (bne (← (hgatp_mode ())) HBare)))
  else (pure (bne (← (satp_mode eff_priv)) Bare))

def exception_vaddr (access_info : AccessInfo) (typ_1 : virtaddr) (typ_2 : physaddr) (typ_3 : physaddr) : SailM (BitVec 64) := do
  let .Virtaddr base_vaddr : virtaddr := typ_1
  let .Physaddr base_paddr : physaddr := typ_2
  let .Physaddr exc_paddr : physaddr := typ_3
  if ((← (is_vmem_active access_info.eff_privilege)) : Bool)
  then
    (let offset := (Sail.BitVec.extractLsb (exc_paddr - base_paddr) (xlen -i 1) 0)
    (pure (base_vaddr + offset)))
  else
    (do
      let exc_paddr_is_valid ← do
        (pure (is_valid_physaddr (← readReg pma_regions) (Physaddr exc_paddr)))
      let exc_paddr := (Sail.BitVec.extractLsb exc_paddr (xlen -i 1) 0)
      if (exc_paddr_is_valid : Bool)
      then (pure exc_paddr)
      else
        (do
          match plat_invalid_physical_address with
          | none => (pure exc_paddr)
          | .some inv_addr =>
            (do
              let trimmed_exc_paddr :=
                (exc_paddr &&& (zero_extend (m := (((64 -i 1) -i 0) +i 1))
                    (ones (n := physaddr_bits))))
              if ((not
                   (is_valid_physaddr (← readReg pma_regions)
                     (Physaddr (zero_extend (m := 64) trimmed_exc_paddr)))) : Bool)
              then (pure trimmed_exc_paddr)
              else (pure inv_addr))))

def default_access_info (access : (MemoryAccessType mem_payload)) : SailM AccessInfo := do
  let eff_priv ← do (effectivePrivilege access (← readReg mstatus) (← readReg cur_privilege))
  (pure { eff_privilege := eff_priv
          pmlen := ← (get_pmlen access eff_priv)
          as_guest := false })

def transform_effective_address (vaddr : virtaddr) (access_info : AccessInfo) : SailM virtaddr := do
  let eff_privilege := access_info.eff_privilege
  let pmlen := access_info.pmlen
  let mode ← do
    if (((eff_privilege == VirtualSupervisor) || (eff_privilege == VirtualUser)) : Bool)
    then (vsatp_mode ())
    else (satp_mode eff_privilege)
  if ((mode == Bare) : Bool)
  then (pure (pm_transform_PA vaddr pmlen))
  else (pure (pm_transform_VA vaddr pmlen))

def access_is_gva (access_info : AccessInfo) : Bool :=
  ((privLevel_is_virtual access_info.eff_privilege) || access_info.as_guest)

def mem_exception_context (e : ExceptionType) (excinfo : (BitVec 64)) (access_info : AccessInfo) : ExceptionContext :=
  (make_exception_context e excinfo (access_is_gva access_info) none)

def with_excinst_offset (e : ExecutionResult) (vaddr : virtaddr) : ExecutionResult :=
  match e with
  | .Trap (priv, ctx, pc) =>
    (Trap
      (priv, { ctx with excinst_offset := (Sail.BitVec.truncate
          (ctx.excinfo - (bits_of_virtaddr vaddr)) 5) }, pc))
  | _ => e

def memory_exception (e : ExceptionType) (excinfo : (BitVec 64)) (access_info : AccessInfo) : SailM ExecutionResult := do
  (trap (mem_exception_context e excinfo access_info))

/-- Type quantifiers: k_ex1173332_ : Bool, k_ex1173331_ : Bool, k_ex1173330_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def translate_and_read_value (vaddr : virtaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (physaddr × (BitVec (8 * width))) ExecutionResult) := do
  let eff_priv := access_info.eff_privilege
  match (← (translateAddr vaddr access eff_priv)) with
  | .Err (e, _) => (pure (Err (← (trap e))))
  | .Ok (paddr, pbmt, _) =>
    (do
      match (← (mem_read access pbmt eff_priv paddr width aq rl res)) with
      | .Err (exc_paddr, e) =>
        (do
          let exc_vaddr ← do (exception_vaddr access_info vaddr paddr exc_paddr)
          (pure (Err (← (memory_exception e exc_vaddr access_info)))))
      | .Ok v => (pure (Ok (paddr, v))))

/-- Type quantifiers: k_ex1173338_ : Bool, k_ex1173337_ : Bool, k_ex1173336_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_read_addr (vaddr : virtaddr) (width : Nat) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := SailME.run do
  sail_assert (res == (is_load_reserved access)) "sys/vmem_utils.sail:188.40-188.41"
  match (← (match_memory_trigger_before (← readReg cur_privilege)
      (TriggerAddress (TriggerAddress_Load, (bits_of_virtaddr vaddr), width)))) with
  | .some pti =>
    SailME.throw ((Err (PendingTrigger pti)) : (Result (BitVec (8 * width)) ExecutionResult))
  | none => (pure ())
  let eff_priv := access_info.eff_privilege
  if ((not (is_aligned_vaddr vaddr width)) : Bool)
  then
    (do
      match (plat_misaligned_exception access res) with
      | .some .AccessFault =>
        SailME.throw (← do
            (pure (Err
                (← (memory_exception (E_Load_Access_Fault ()) (bits_of_virtaddr vaddr) access_info)))))
      | .some .AlignmentException =>
        SailME.throw (← do
            (pure (Err
                (← (memory_exception (E_Load_Addr_Align ()) (bits_of_virtaddr vaddr) access_info)))))
      | none => (pure ()))
  else (pure ())
  let vaddr_bits := (bits_of_virtaddr vaddr)
  let (in_page_bytes, next_page_bytes) ← do (split_on_page_boundary vaddr_bits width)
  let data := (zeros (n := (8 *i width)))
  let do_split_access ← do
    (pure ((← (is_vmem_active eff_priv)) && ((next_page_bytes >b 0) && (not res))))
  let data ← (( do
    if ((sys_misaligned_order_decreasing && do_split_access) : Bool)
    then
      (do
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        match (← (translate_and_read_value access_addr next_page_bytes access access_info aq rl
            res)) with
        | .Err e => SailME.throw ((Err e) : (Result (BitVec (8 * width)) ExecutionResult))
        | .Ok (_, v) =>
          (pure (Sail.BitVec.updateSubrange data ((8 *i width) -i 1) (8 *i in_page_bytes) v)))
    else (pure data) ) : SailME (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * width)) )
  let access_width :=
    if (do_split_access : Bool)
    then in_page_bytes
    else width
  let data ← (( do
    match (← (translate_and_read_value vaddr access_width access access_info aq rl res)) with
    | .Err e => SailME.throw ((Err e) : (Result (BitVec (8 * width)) ExecutionResult))
    | .Ok (paddr, v) =>
      (do
        if (res : Bool)
        then
          (do
            sail_assert (width == access_width) "sys/vmem_utils.sail:243.36-243.37"
            (load_reservation (bits_of_physaddr paddr) width))
        else (pure ())
        (pure (Sail.BitVec.updateSubrange data ((8 *i access_width) -i 1) 0 v))) ) : SailME
    (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * width)) )
  let data ← (( do
    if (((not sys_misaligned_order_decreasing) && do_split_access) : Bool)
    then
      (do
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        match (← (translate_and_read_value access_addr next_page_bytes access access_info aq rl
            res)) with
        | .Err e => SailME.throw ((Err e) : (Result (BitVec (8 * width)) ExecutionResult))
        | .Ok (_, v) =>
          (pure (Sail.BitVec.updateSubrange data ((8 *i width) -i 1) (8 *i in_page_bytes) v)))
    else (pure data) ) : SailME (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * width)) )
  (match_memory_trigger_after (← readReg cur_privilege)
    (TriggerLoadData ((bits_of_virtaddr vaddr), (zero_extend (m := (8 *i 16)) data), width)))
  (pure (Ok data))

/-- Type quantifiers: k_ex1173343_ : Bool, k_ex1173342_ : Bool, k_ex1173341_ : Bool, width : Nat, width
  ≥ 0, 0 < width ∧ width ≤ max_mem_access -/
def translate_and_write_value (vaddr : virtaddr) (width : Nat) (value : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := do
  let eff_priv := access_info.eff_privilege
  match (← (translateAddr vaddr access eff_priv)) with
  | .Err (e, _) => (pure (Err (← (trap e))))
  | .Ok (paddr, pbmt, _) =>
    (do
      match (← (mem_write_ea paddr width eff_priv access pbmt aq rl res)) with
      | .Err (exc_paddr, e) =>
        (do
          let exc_vaddr ← do (exception_vaddr access_info vaddr paddr exc_paddr)
          (pure (Err (← (memory_exception e exc_vaddr access_info)))))
      | .Ok () =>
        (do
          match (← (mem_write_value paddr width value eff_priv access pbmt aq rl res)) with
          | .Err (exc_paddr, e) =>
            (do
              let exc_vaddr ← do (exception_vaddr access_info vaddr paddr exc_paddr)
              (pure (Err (← (memory_exception e exc_vaddr access_info)))))
          | .Ok s => (pure (Ok s))))

/-- Type quantifiers: k_ex1173349_ : Bool, k_ex1173348_ : Bool, k_ex1173347_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_write_addr (vaddr : virtaddr) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := SailME.run do
  sail_assert (res == (is_store_conditional access)) "sys/vmem_utils.sail:303.44-303.45"
  match (← (match_memory_trigger_before (← readReg cur_privilege)
      (TriggerStore ((bits_of_virtaddr vaddr), (zero_extend (m := (8 *i 16)) data), width)))) with
  | .some pti => SailME.throw ((Err (PendingTrigger pti)) : (Result Bool ExecutionResult))
  | none => (pure ())
  let eff_priv := access_info.eff_privilege
  if ((not (is_aligned_vaddr vaddr width)) : Bool)
  then
    (do
      match (plat_misaligned_exception access res) with
      | .some .AccessFault =>
        SailME.throw (← do
            (pure (Err
                (← (memory_exception (E_SAMO_Access_Fault ()) (bits_of_virtaddr vaddr) access_info)))))
      | .some .AlignmentException =>
        SailME.throw (← do
            (pure (Err
                (← (memory_exception (E_SAMO_Addr_Align ()) (bits_of_virtaddr vaddr) access_info)))))
      | none => (pure ()))
  else (pure ())
  let vaddr_bits := (bits_of_virtaddr vaddr)
  let write_success : Bool := true
  let (in_page_bytes, next_page_bytes) ← do (split_on_page_boundary vaddr_bits width)
  let do_split_access ← do
    (pure ((← (is_vmem_active eff_priv)) && ((next_page_bytes >b 0) && (not res))))
  let write_success ← (( do
    if ((sys_misaligned_order_decreasing && do_split_access) : Bool)
    then
      (do
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        let write_value := (Sail.BitVec.extractLsb data ((8 *i width) -i 1) (8 *i in_page_bytes))
        match (← (translate_and_write_value access_addr next_page_bytes write_value access
            access_info aq rl res)) with
        | .Err e => SailME.throw ((Err e) : (Result Bool ExecutionResult))
        | .Ok s => (pure (write_success && s)))
    else (pure write_success) ) : SailME (Result Bool ExecutionResult) Bool )
  let access_width :=
    if (do_split_access : Bool)
    then in_page_bytes
    else width
  let write_success ← (( do
    match (← (translateAddr vaddr access eff_priv)) with
    | .Err (e, _) =>
      SailME.throw (← do
          (pure (Err (← (trap e)))))
    | .Ok (paddr, pbmt, _) =>
      (do
        if ((res && (not (match_reservation (bits_of_physaddr paddr)))) : Bool)
        then
          (do
            match (← (phys_access_check access pbmt eff_priv paddr access_width true)) with
            | .Err e =>
              SailME.throw (← do
                  let exc_vaddr ← do (exception_vaddr access_info vaddr paddr paddr)
                  (pure (Err (← (memory_exception e exc_vaddr access_info)))))
            | .Ok _ => (pure false))
        else
          (do
            match (← (mem_write_ea paddr access_width eff_priv access pbmt aq rl res)) with
            | .Err (exc_paddr, e) =>
              SailME.throw (← do
                  let exc_vaddr ← do (exception_vaddr access_info vaddr paddr exc_paddr)
                  (pure (Err (← (memory_exception e exc_vaddr access_info)))))
            | .Ok () =>
              (do
                let write_value := (Sail.BitVec.extractLsb data ((8 *i access_width) -i 1) 0)
                match (← (mem_write_value paddr access_width write_value eff_priv access pbmt aq
                    rl res)) with
                | .Err (exc_paddr, e) =>
                  SailME.throw (← do
                      let exc_vaddr ← do (exception_vaddr access_info vaddr paddr exc_paddr)
                      (pure (Err (← (memory_exception e exc_vaddr access_info)))))
                | .Ok s => (pure (write_success && s))))) ) : SailME (Result Bool ExecutionResult)
    Bool )
  let write_success ← (( do
    if (((not sys_misaligned_order_decreasing) && do_split_access) : Bool)
    then
      (do
        let access_addr := (Virtaddr (BitVec.addInt vaddr_bits in_page_bytes))
        let write_value := (Sail.BitVec.extractLsb data ((8 *i width) -i 1) (8 *i in_page_bytes))
        match (← (translate_and_write_value access_addr next_page_bytes write_value access
            access_info aq rl res)) with
        | .Err e => SailME.throw ((Err e) : (Result Bool ExecutionResult))
        | .Ok s => (pure (write_success && s)))
    else (pure write_success) ) : SailME (Result Bool ExecutionResult) Bool )
  (pure (Ok write_success))

/-- Type quantifiers: width : Nat, 1 ≤ width ∧ width ≤ 4096 -/
def get_transformed_data_addr (base : regidx) (offset : (BitVec 64)) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (width : Nat) : SailM (Ext_DataAddr_Check Unit) := do
  let eff_priv := access_info.eff_privilege
  match (← (ext_data_get_addr base offset access width)) with
  | .Ext_DataAddr_Error e => (pure (Ext_DataAddr_Error e))
  | .Ext_DataAddr_OK vaddr =>
    (do
      let vaddr ← do (transform_effective_address vaddr access_info)
      (pure (Ext_DataAddr_OK vaddr)))

/-- Type quantifiers: k_ex1173358_ : Bool, k_ex1173357_ : Bool, k_ex1173356_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_read_explicit (rs : regidx) (offset : (BitVec 64)) (width : Nat) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (get_transformed_data_addr rs offset access access_info width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result (BitVec (8 * width)) ExecutionResult))
    ) : SailME (Result (BitVec (8 * width)) ExecutionResult) virtaddr )
  match (← (vmem_read_addr vaddr width access access_info aq rl res)) with
  | .Ok data => (pure (Ok data))
  | .Err e => (pure (Err (with_excinst_offset e vaddr)))

/-- Type quantifiers: k_ex1173366_ : Bool, k_ex1173365_ : Bool, k_ex1173364_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_read (rs : regidx) (offset : (BitVec 64)) (width : Nat) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := do
  (vmem_read_explicit rs offset width access (← (default_access_info access)) aq rl res)

/-- Type quantifiers: k_ex1173374_ : Bool, k_ex1173373_ : Bool, k_ex1173372_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_write_explicit (rs_addr : regidx) (offset : (BitVec 64)) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (access_info : AccessInfo) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (get_transformed_data_addr rs_addr offset access access_info width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result Bool ExecutionResult)) ) : SailME
    (Result Bool ExecutionResult) virtaddr )
  match (← (vmem_write_addr vaddr width data access access_info aq rl res)) with
  | .Ok s => (pure (Ok s))
  | .Err e => (pure (Err (with_excinst_offset e vaddr)))

/-- Type quantifiers: k_ex1173382_ : Bool, k_ex1173381_ : Bool, k_ex1173380_ : Bool, width : Nat, width
  ≥ 0, (is_mem_width width) -/
def vmem_write (rs_addr : regidx) (offset : (BitVec 64)) (width : Nat) (data : (BitVec (8 * width))) (access : (MemoryAccessType mem_payload)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result Bool ExecutionResult) := do
  (vmem_write_explicit rs_addr offset width data access (← (default_access_info access)) aq rl res)

