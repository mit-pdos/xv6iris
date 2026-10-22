import LeanRV64D.LeanRV64D
import LeanRV64D.Flow
import LeanRV64D.Arith
import LeanRV64D.Prelude
import LeanRV64D.Errors
import LeanRV64D.IsaVersion
import LeanRV64D.Xlen
import LeanRV64D.MemAddrtype
import LeanRV64D.PlatformConfig
import LeanRV64D.TypesExt
import LeanRV64D.Types
import LeanRV64D.VmemTypes
import LeanRV64D.SysRegs
import LeanRV64D.Events
import LeanRV64D.SyncException
import LeanRV64D.Mem
import LeanRV64D.VmemPte
import LeanRV64D.VmemPtw
import LeanRV64D.Callbacks0
import LeanRV64D.VmemTlb

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
open PTE_Update_Result
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

def pte_update_max_retries : Nat := 16

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, List.elem pte_size [4, 8] -/
def write_pte (paddr : physaddr) (pte_size : Nat) (pte : (BitVec (pte_size * 8))) : SailM (Result Bool (physaddr × ExceptionType)) := do
  (mem_write_value paddr pte_size pte Supervisor (Store PageTableEntry) PBMT_PMA false false false)

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, List.elem pte_size [4, 8] -/
def write_pte_conditional (paddr : physaddr) (pte_size : Nat) (pte : (BitVec (pte_size * 8))) : SailM (Result Bool (physaddr × ExceptionType)) := do
  (mem_write_value paddr pte_size pte Supervisor (Store PageTableEntry) PBMT_PMA false false true)

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, List.elem pte_size [4, 8] -/
def read_pte (paddr : physaddr) (pte_size : Nat) : SailM (Result (BitVec (8 * pte_size)) (physaddr × ExceptionType)) := do
  (mem_read (Load PageTableEntry) PBMT_PMA Supervisor paddr pte_size false false false)

/-- Type quantifiers: pte_size : Nat, pte_size ≥ 0, List.elem pte_size [4, 8] -/
def read_pte_exclusive (paddr : physaddr) (pte_size : Nat) : SailM (Result (BitVec (8 * pte_size)) (physaddr × ExceptionType)) := do
  (mem_read (Load PageTableEntry) PBMT_PMA Supervisor paddr pte_size false false true)

def hgatp_mode (_ : Unit) : SailM HGATPMode := do
  let arch ← do (architecture Supervisor)
  let mbits ← (( do
    match arch with
    | .RV64 =>
      (do
        sail_assert (xlen ≥b 64) "sys/vmem.sail:476.31-476.32"
        (pure (_get_Hgatp64_Mode (Mk_Hgatp64 (← readReg hgatp)))))
    | .RV32 =>
      (pure (0b000#3 +++ (_get_Hgatp32_Mode
            (Mk_Hgatp32 (Sail.BitVec.extractLsb (← readReg hgatp) 31 0)))))
    | .RV128 => (internal_error "sys/vmem.sail" 478 "RV128 not supported") ) : SailM
    LeanRV64D.hgatp_mode )
  match (← (hgatpMode_of_bits arch mbits)) with
  | .some m => (pure m)
  | none => (internal_error "sys/vmem.sail" 483 "invalid translation mode in hgatp")

def hgatp_mode_width_forwards (arg_ : HGATPMode) : SailM Int := do
  match arg_ with
  | .Sv32x4 => (pure 34)
  | .Sv39x4 => (pure 41)
  | .Sv48x4 => (pure 50)
  | .Sv57x4 => (pure 59)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def get_mxr (stage : TranslationStage) : SailM Bool := do
  if ((stage == VS_Stage) : Bool)
  then
    (do
      if (((_get_Mstatus_MXR (← readReg mstatus)) == 1#1) : Bool)
      then (pure true)
      else (pure ((_get_Mstatus_MXR (← readReg vsstatus)) == 1#1)))
  else (pure ((_get_Mstatus_MXR (← readReg mstatus)) == 1#1))

def get_sum (stage : TranslationStage) : SailM Bool := do
  if ((stage == VS_Stage) : Bool)
  then (pure ((_get_Mstatus_SUM (← readReg vsstatus)) == 1#1))
  else (pure ((_get_Mstatus_SUM (← readReg mstatus)) == 1#1))

/-- Type quantifiers: level : Nat, k_ex1173922_ : Bool, k_ex1173921_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width), 0 ≤ level ∧
  level ≤
  (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 1 else (if ( sv_width = 39 ∨ sv_width = 41  : Bool) then 2 else (if ( sv_width
  = 48 ∨ sv_width = 50  : Bool) then 3 else 4))) -/
def check_leaf_pte (sv_width : Nat) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pte : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 32 else 64))) (pte_addr : physaddr) (level : Nat) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := SailME.run do
  let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
  let pte_ext := (ext_bits_of_PTE pte)
  if ((← (pte_is_invalid pte_flags pte_ext stage)) : Bool)
  then
    (let _ : Unit :=
      (ptw_fail_callback stage level (PTW_Invalid_PTE ()) (bits_of_physaddr pte_addr))
    (pure (Err ((PTW_Invalid_PTE ()), ext_ptw))))
  else
    (do
      if ((pte_is_non_leaf pte_flags) : Bool)
      then
        (let _ : Unit :=
          (ptw_fail_callback stage level (PTW_Invalid_PTE ()) (bits_of_physaddr pte_addr))
        (pure (Err ((PTW_Invalid_PTE ()), ext_ptw))))
      else
        (do
          let ppn := (PPN_of_PTE pte)
          let vpn_i_size := (get_vpn_level_size sv_width)
          let low_bits := (vpn_i_size *i level)
          if ((level >b 0) : Bool)
          then
            (do
              if (((Sail.BitVec.extractLsb ppn (low_bits -i 1) 0) != (zeros
                     (n := ((((vpn_i_size *i level) -i 1) -i 0) +i 1)))) : Bool)
              then
                SailME.throw (let _ : Unit :=
                    (ptw_fail_callback stage level (PTW_Misaligned ()) (bits_of_physaddr pte_addr))
                  (Err ((PTW_Misaligned ()), ext_ptw)) : (Result ((BitVec (if ( sv_width = 32 ∨
                  sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)))
              else (pure ()))
          else (pure ())
          match (← (check_PTE_permission access priv stage mxr do_sum pte_flags pte_ext ext_ptw)) with
          | .PTE_Check_Failure (ext_ptw, pte_failure) =>
            (let _ : Unit :=
              (ptw_fail_callback stage level (ext_get_ptw_error pte_failure)
                (bits_of_physaddr pte_addr))
            (pure (Err ((ext_get_ptw_error pte_failure), ext_ptw))))
          | .PTE_Check_Success ext_ptw =>
            (do
              let ppn ← (( do
                if ((level >b 0) : Bool)
                then
                  (do
                    if ((((_get_PTE_Ext_N pte_ext) == 1#1) && pte_reserved_bits_must_be_zero) : Bool)
                    then
                      SailME.throw ((Err ((PTW_Invalid_PTE ()), ext_ptw)) : (Result ((BitVec (if ( sv_width
                        = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)))
                    else
                      (pure ((Sail.BitVec.extractLsb ppn ((Sail.BitVec.length ppn) -i 1) low_bits) +++ (Sail.BitVec.extractLsb
                            vpn (low_bits -i 1) 0))))
                else
                  (do
                    if (((← (currentlyEnabled Ext_Svnapot)) && ((_get_PTE_Ext_N pte_ext) == 1#1)) : Bool)
                    then
                      (do
                        let pte_napot_bits := 4
                        if (((Sail.BitVec.extractLsb ppn (pte_napot_bits -i 1) 0) != 0b1000#4) : Bool)
                        then
                          SailME.throw ((Err ((PTW_Invalid_PTE ()), ext_ptw)) : (Result ((BitVec (if ( sv_width
                            = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)))
                        else
                          (pure (Sail.BitVec.updateSubrange ppn (pte_napot_bits -i 1) 0
                              (Sail.BitVec.extractLsb vpn (pte_napot_bits -i 1) 0))))
                    else (pure ppn)) ) : SailME
                (Result ((BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit))
                (ppn_bits sv_width) )
              let pbmt ← do
                if ((← do
                     if (((_get_MEnvcfg_PBMTE (← readReg menvcfg)) == 0#1) : Bool)
                     then (pure true)
                     else
                       (do
                         if ((stage == VS_Stage) : Bool)
                         then (pure ((_get_HEnvcfg_PBMTE (← (read_henvcfg ()))) == 0#1))
                         else (pure false))) : Bool)
                then (pure PBMT_PMA)
                else (page_based_mem_type_forwards (_get_PTE_Ext_PBMT pte_ext))
              (pure (Ok (ppn, pbmt, ext_ptw))))))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, sv_width : Nat, sv_width ≥ 0, (is_sv_or_svx4_mode
  sv_width) ∧ k_n ≥ sv_width -/
def translate_validate_address (addr : (BitVec k_n)) (sv_width : Nat) (stage : TranslationStage) : (Result (BitVec sv_width) PTW_Error) :=
  let truncated := (Sail.BitVec.truncate addr sv_width)
  let extended : (BitVec k_n) :=
    if ((stage == G_Stage) : Bool)
    then (zero_extend (m := (Sail.BitVec.length addr)) truncated)
    else (sign_extend (m := (Sail.BitVec.length addr)) truncated)
  if ((addr == extended) : Bool)
  then (Ok truncated)
  else (Err (PTW_Invalid_Addr ()))

def xatp_to_ppn (stage : TranslationStage) : SailM (BitVec 44) := do
  match stage with
  | .S_Stage => (pure (_get_Satp64_PPN (Mk_Satp64 (← readReg satp))))
  | .VS_Stage => (pure (_get_Satp64_PPN (Mk_Satp64 (← readReg vsatp))))
  | .G_Stage => (pure (_get_Hgatp64_PPN (Mk_Hgatp64 (← readReg hgatp))))

def translate_PTE_addr_mutrec_vv_zG_Stagev (pte_addr : (BitVec 64)) (access : (MemoryAccessType mem_payload)) (ext_ptw : Unit) : (Result (physaddr × page_based_mem_type × Unit) (PTW_Error × Unit)) :=
  (Ok ((Physaddr pte_addr), PBMT_PMA, ext_ptw))

/-- Type quantifiers: k_ex555890_ : Bool, k_ex555891_ : Bool, level : Nat, k_ex555893_ : Bool, sv_width
  : Nat, (is_sv_or_svx4_mode sv_width), 0 ≤ level ∧
  level ≤
  (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 1 else (if ( sv_width = 39 ∨ sv_width = 41  : Bool) then 2 else (if ( sv_width
  = 48 ∨ sv_width = 50  : Bool) then 3 else 4))) -/
def pt_walk_mutrec_vvv_zUservvvvv_zG_Stagev (sv_width : Nat) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (pt_base : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (level : Nat) (global : Bool) (ext_ptw : Unit) : SailM (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)) := SailME.run do
  let _ : Unit := (ptw_start_callback G_Stage level (zero_extend (m := 64) vpn) access User)
  let log_pte_size_bytes :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 2
    else 3
  let vpn_i_size := (pagesize_bits -i log_pte_size_bytes)
  let is_svx4_root :=
    (((sv_width == 34) || ((sv_width == 41) || ((sv_width == 50) || (sv_width == 59)))) && (level == (get_root_level
          sv_width)))
  let vpn_lo := (level *i vpn_i_size)
  let vpn_hi :=
    if (is_svx4_root : Bool)
    then (((level +i 1) *i vpn_i_size) +i 1)
    else (((level +i 1) *i vpn_i_size) -i 1)
  let pte_addr :=
    ((pt_base +++ 0x000#12) + (zero_extend
        (m := ((if (((sv_width == 32) || (sv_width == 34)) : Bool)
          then 22
          else 44) +i 12))
        ((Sail.BitVec.extractLsb vpn vpn_hi vpn_lo) +++ (zeros (n := log_pte_size_bytes)))))
  sail_assert true "sys/vmem.sail:339.41-339.42"
  let pte_addr_original := (Physaddr (zero_extend (m := 64) pte_addr))
  let pte_addr ← do
    match (translate_PTE_addr_mutrec_vv_zG_Stagev (zero_extend (m := 64) pte_addr)
      (Load PageTableEntry) ext_ptw) with
    | .Ok (pa, _, _) => (pure pa)
    | .Err (e, _) =>
      SailME.throw (← do
          (pure (Err
              ((PTW_Implicit_Error
                ((← (translationException access e)), (zero_extend (m := 64) pte_addr), (Load
                  PageTableEntry))), ext_ptw))))
  match (← (read_pte pte_addr (2 ^i log_pte_size_bytes))) with
  | .Err _ =>
    (let _ : Unit :=
      (ptw_fail_callback G_Stage level (PTW_No_Access ()) (bits_of_physaddr pte_addr))
    (pure (Err ((PTW_No_Access ()), ext_ptw))))
  | .Ok pte =>
    (do
      let _ : Unit :=
        (ptw_step_callback G_Stage level (bits_of_physaddr pte_addr) (zero_extend (m := 64) pte))
      let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
      let global := (global || ((bne G_Stage G_Stage) && ((_get_PTE_Flags_G pte_flags) == 1#1)))
      if (((not (← (pte_is_invalid pte_flags (ext_bits_of_PTE pte) G_Stage))) && ((pte_is_non_leaf
               pte_flags) && (level >b 0))) : Bool)
      then
        (do
          let ppn := (PPN_of_PTE pte)
          (pt_walk_mutrec_vvv_zUservvvvv_zG_Stagev sv_width vpn access mxr do_sum ppn (level -i 1)
            global ext_ptw))
      else
        (do
          match (← (check_leaf_pte sv_width vpn access User mxr do_sum pte pte_addr level G_Stage
              ext_ptw)) with
          | .Err (e, ext_ptw) => (pure (Err (e, ext_ptw)))
          | .Ok (ppn, pbmt, ext_ptw) =>
            (let _ : Unit := (ptw_success_callback G_Stage level (zero_extend (m := 64) ppn))
            (pure (Ok
                ({ ppn := ppn
                   pte := pte
                   pteAddr := pte_addr_original
                   level := level
                   pbmt := pbmt
                   global := global }, ext_ptw))))))
termination_by (let (_, _, _, _, _, _, level, _, _) :=
  (sv_width, vpn, access, mxr, do_sum, pt_base, level, global, ext_ptw)
level).toNat

/-- Type quantifiers: k_ex555890_ : Bool, k_ex555891_ : Bool, level : Nat, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width), 0 ≤ level ∧
  level ≤
  (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 1 else (if ( sv_width = 39 ∨ sv_width = 41  : Bool) then 2 else (if ( sv_width
  = 48 ∨ sv_width = 50  : Bool) then 3 else 4))) -/
def pt_walk_mutrec_vvv_zUservvvvF_zG_Stagev (sv_width : Nat) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (pt_base : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (level : Nat) (ext_ptw : Unit) : SailM (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)) := SailME.run do
  let _ : Unit := (ptw_start_callback G_Stage level (zero_extend (m := 64) vpn) access User)
  let log_pte_size_bytes :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 2
    else 3
  let vpn_i_size := (pagesize_bits -i log_pte_size_bytes)
  let is_svx4_root :=
    (((sv_width == 34) || ((sv_width == 41) || ((sv_width == 50) || (sv_width == 59)))) && (level == (get_root_level
          sv_width)))
  let vpn_lo := (level *i vpn_i_size)
  let vpn_hi :=
    if (is_svx4_root : Bool)
    then (((level +i 1) *i vpn_i_size) +i 1)
    else (((level +i 1) *i vpn_i_size) -i 1)
  let pte_addr :=
    ((pt_base +++ 0x000#12) + (zero_extend
        (m := ((if (((sv_width == 32) || (sv_width == 34)) : Bool)
          then 22
          else 44) +i 12))
        ((Sail.BitVec.extractLsb vpn vpn_hi vpn_lo) +++ (zeros (n := log_pte_size_bytes)))))
  sail_assert true "sys/vmem.sail:339.41-339.42"
  let pte_addr_original := (Physaddr (zero_extend (m := 64) pte_addr))
  let pte_addr ← do
    match (translate_PTE_addr_mutrec_vv_zG_Stagev (zero_extend (m := 64) pte_addr)
      (Load PageTableEntry) ext_ptw) with
    | .Ok (pa, _, _) => (pure pa)
    | .Err (e, _) =>
      SailME.throw (← do
          (pure (Err
              ((PTW_Implicit_Error
                ((← (translationException access e)), (zero_extend (m := 64) pte_addr), (Load
                  PageTableEntry))), ext_ptw))))
  match (← (read_pte pte_addr (2 ^i log_pte_size_bytes))) with
  | .Err _ =>
    (let _ : Unit :=
      (ptw_fail_callback G_Stage level (PTW_No_Access ()) (bits_of_physaddr pte_addr))
    (pure (Err ((PTW_No_Access ()), ext_ptw))))
  | .Ok pte =>
    (do
      let _ : Unit :=
        (ptw_step_callback G_Stage level (bits_of_physaddr pte_addr) (zero_extend (m := 64) pte))
      let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
      let global := (false || ((bne G_Stage G_Stage) && ((_get_PTE_Flags_G pte_flags) == 1#1)))
      if (((not (← (pte_is_invalid pte_flags (ext_bits_of_PTE pte) G_Stage))) && ((pte_is_non_leaf
               pte_flags) && (level >b 0))) : Bool)
      then
        (do
          let ppn := (PPN_of_PTE pte)
          (pt_walk_mutrec_vvv_zUservvvvv_zG_Stagev sv_width vpn access mxr do_sum ppn (level -i 1)
            global ext_ptw))
      else
        (do
          match (← (check_leaf_pte sv_width vpn access User mxr do_sum pte pte_addr level G_Stage
              ext_ptw)) with
          | .Err (e, ext_ptw) => (pure (Err (e, ext_ptw)))
          | .Ok (ppn, pbmt, ext_ptw) =>
            (let _ : Unit := (ptw_success_callback G_Stage level (zero_extend (m := 64) ppn))
            (pure (Ok
                ({ ppn := ppn
                   pte := pte
                   pteAddr := pte_addr_original
                   level := level
                   pbmt := pbmt
                   global := global }, ext_ptw))))))

/-- Type quantifiers: sv_width : Nat, (is_sv_or_svx4_mode sv_width) -/
def update_and_write_pte_mutrec_vvvv_zG_Stagev (sv_width : Nat) (pteAddr : physaddr) (pte : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 32 else 64))) (access : (MemoryAccessType mem_payload)) (ext_ptw : Unit) : SailM (Result ((PTE_Update_Result sv_width) × Unit) (PTW_Error × Unit)) := SailME.run do
  match (← (update_PTE_Bits pte access G_Stage)) with
  | none => (pure (Ok ((PTE_Update_Done none), ext_ptw)))
  | .some pte_new =>
    (do
      if ((← (hw_updates_pte G_Stage)) : Bool)
      then
        (do
          let pte_width :=
            if (((sv_width == 32) || (sv_width == 34)) : Bool)
            then 4
            else 8
          let pte_paddr ← do
            match (translate_PTE_addr_mutrec_vv_zG_Stagev (bits_of_physaddr pteAddr)
              (Store PageTableEntry) ext_ptw) with
            | .Ok (pa, _, _) => (pure pa)
            | .Err (e, _) =>
              SailME.throw (← do
                  (pure (Err
                      ((PTW_Implicit_Error
                        ((← (translationException access e)), (bits_of_physaddr pteAddr), (Store
                          PageTableEntry))), ext_ptw))))
          match (← (read_pte_exclusive pte_paddr pte_width)) with
          | .Err _ => (pure (Err ((PTW_No_Access ()), ext_ptw)))
          | .Ok pte_fresh =>
            (do
              if ((pte_fresh != pte) : Bool)
              then (pure (Ok ((PTE_Update_Retry ()), ext_ptw)))
              else
                (do
                  match (← (write_pte_conditional pte_paddr pte_width pte_new)) with
                  | .Ok true => (pure (Ok ((PTE_Update_Done (some pte_new)), ext_ptw)))
                  | .Ok false => (internal_error "sys/vmem.sail" 281 "PTE conditional write failed")
                  | .Err _ => (pure (Err ((PTW_No_Access ()), ext_ptw))))))
      else (pure (Err ((PTW_PTE_Needs_Update ()), ext_ptw))))

/-- Type quantifiers: retries : Nat, k_ex555901_ : Bool, k_ex555902_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width), 0 ≤ retries -/
def translate_TLB_miss_retry_mutrec_vvvvvvv_zUservv_zG_Stagev (retries : Nat) (sv_width : Nat) (asid : (BitVec (if ( 64
  = 32  : Bool) then 9 else 16))) (vmid : (BitVec 14)) (base_ppn : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let initial_level := (get_root_level sv_width)
  let ptw_result ← do
    (pt_walk_mutrec_vvv_zUservvvvF_zG_Stagev sv_width vpn access mxr do_sum base_ppn initial_level
      ext_ptw)
  match ptw_result with
  | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw)))
  | .Ok ({ ppn := ppn, pte := pte, pteAddr := pteAddr, level := level, pbmt := pbmt, global := global }, ext_ptw) =>
    (do
      match (← (update_and_write_pte_mutrec_vvvv_zG_Stagev sv_width pteAddr pte access ext_ptw)) with
      | .Ok (.PTE_Update_Done (.some new_pte), ext_ptw) =>
        (do
          (add_to_TLB sv_width asid vmid vpn ppn new_pte pteAddr level global G_Stage)
          (pure (Ok (ppn, pbmt, ext_ptw))))
      | .Ok (.PTE_Update_Done none, ext_ptw) =>
        (do
          (add_to_TLB sv_width asid vmid vpn ppn pte pteAddr level global G_Stage)
          (pure (Ok (ppn, pbmt, ext_ptw))))
      | .Ok (.PTE_Update_Retry (), ext_ptw) =>
        (do
          if ((retries >b 0) : Bool)
          then
            (translate_TLB_miss_retry_mutrec_vvvvvvv_zUservv_zG_Stagev (retries -i 1) sv_width asid
              vmid base_ppn vpn access mxr do_sum ext_ptw)
          else (internal_error "sys/vmem.sail" 537 "PTE A/D update: retry bound exhausted"))
      | .Err (e, ext_ptw) => (pure (Err (e, ext_ptw))))
termination_by (let (retries, _, _, _, _, _, _, _, _, _) :=
  (retries, sv_width, asid, vmid, base_ppn, vpn, access, mxr, do_sum, ext_ptw)
retries).toNat

/-- Type quantifiers: k_ex555909_ : Bool, k_ex555910_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width) -/
def translate_TLB_miss_mutrec_vvvvvv_zUservv_zG_Stagev (sv_width : Nat) (asid : (BitVec (if ( 64 =
  32  : Bool) then 9 else 16))) (vmid : (BitVec 14)) (base_ppn : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  (translate_TLB_miss_retry_mutrec_vvvvvvv_zUservv_zG_Stagev pte_update_max_retries sv_width asid
    vmid base_ppn vpn access mxr do_sum ext_ptw)

/-- Type quantifiers: k_ex555916_ : Bool, k_ex555917_ : Bool, tlb_index : Nat, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width), 0 ≤ tlb_index ∧ tlb_index ≤ (2 ^ 6 - 1) -/
def translate_TLB_hit_mutrec_vvvvvv_zUservvvv_zG_Stagev (sv_width : Nat) (asid : (BitVec (if ( 64 =
  32  : Bool) then 9 else 16))) (vmid : (BitVec 14)) (base_ppn : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (tlb_index : Nat) (ent : TLB_Entry) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let pte_size :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 4
    else 8
  let pte := (tlb_get_pte pte_size ent)
  let ext_pte := (ext_bits_of_PTE pte)
  let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
  let pte_check ← do
    (check_PTE_permission access User G_Stage mxr do_sum pte_flags ext_pte ext_ptw)
  match pte_check with
  | .PTE_Check_Failure (ext_ptw, pte_failure) =>
    (pure (Err ((ext_get_ptw_error pte_failure), ext_ptw)))
  | .PTE_Check_Success ext_ptw =>
    (do
      match (← (update_and_write_pte_mutrec_vvvv_zG_Stagev sv_width ent.pteAddr pte access ext_ptw)) with
      | .Ok (.PTE_Update_Done (.some pte), ext_ptw) =>
        (do
          (write_TLB tlb_index (tlb_set_pte ent (pte : (BitVec (pte_size * 8)))))
          (pure (Ok ((tlb_get_ppn sv_width ent vpn), (← (tlb_get_pbmt ent)), ext_ptw))))
      | .Ok (.PTE_Update_Done none, ext_ptw) =>
        (pure (Ok ((tlb_get_ppn sv_width ent vpn), (← (tlb_get_pbmt ent)), ext_ptw)))
      | .Ok (.PTE_Update_Retry (), ext_ptw) =>
        (translate_TLB_miss_mutrec_vvvvvv_zUservv_zG_Stagev sv_width asid vmid base_ppn vpn access
          mxr do_sum ext_ptw)
      | .Err (e, ext_ptw) => (pure (Err (e, ext_ptw))))

/-- Type quantifiers: k_ex555928_ : Bool, k_ex555929_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width) -/
def translate_mutrec_vvvvvv_zUservv_zG_Stagev (sv_width : Nat) (asid : (BitVec 16)) (vmid : (BitVec (if ( 64
  = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (mxr : Bool) (do_sum : Bool) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (← (lookup_TLB sv_width asid vmid vpn G_Stage)) with
  | .some (index, ent) =>
    (translate_TLB_hit_mutrec_vvvvvv_zUservvvv_zG_Stagev sv_width asid vmid base_ppn vpn access mxr
      do_sum index ent ext_ptw)
  | none =>
    (do
      (generate_event EV_TLB_MISS)
      (translate_TLB_miss_mutrec_vvvvvv_zUservv_zG_Stagev sv_width asid vmid base_ppn vpn access mxr
        do_sum ext_ptw))

/-- Type quantifiers: k_n : Nat, sv_width : Nat, k_n ≥ 0, (is_sv_or_svx4_mode sv_width) ∧
  k_n ≥ sv_width -/
def translate_stage_mutrec_vvv_zUser_zG_Stage (sv_width : Nat) (addr : (BitVec k_n)) (access : (MemoryAccessType mem_payload)) : SailM (Result ((BitVec (if ( 64
  = 32  : Bool) then 34 else 64)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (translate_validate_address addr sv_width G_Stage) with
  | .Err e => (pure (Err (e, init_ext_ptw)))
  | .Ok valid_addr =>
    (do
      sail_assert (false || (true && ((sv_width != 32) && (sv_width != 34)))) "sys/vmem.sail:682.60-682.61"
      let vmid ← do (get_vmid G_Stage)
      let mxr ← do (get_mxr G_Stage)
      let do_sum ← do (get_sum G_Stage)
      let vpn := (Sail.BitVec.extractLsb valid_addr (sv_width -i 1) pagesize_bits)
      let base_ppn ← do (xatp_to_ppn G_Stage)
      let res ← do
        (translate_mutrec_vvvvvv_zUservv_zG_Stagev sv_width 0x0000#16 vmid base_ppn vpn access mxr
          do_sum init_ext_ptw)
      match res with
      | .Ok (ppn, pbmt, ext_ptw) =>
        (pure (Ok
            ((zero_extend (m := 64) (ppn +++ (Sail.BitVec.extractLsb valid_addr 11 0))), pbmt, ext_ptw)))
      | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw))))

def translate_g_stage (gpa : (BitVec 64)) (access : (MemoryAccessType mem_payload)) : SailM (Result ((BitVec (if ( 64
  = 32  : Bool) then 34 else 64)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let mode ← do (hgatp_mode ())
  if ((mode == HBare) : Bool)
  then (pure (Ok (gpa, PBMT_PMA, init_ext_ptw)))
  else
    (do
      let sv_width ← do (hgatp_mode_width_forwards mode)
      sail_assert (sv_width ≤b gpalen) "sys/vmem.sail:728.27-728.28"
      (translate_stage_mutrec_vvv_zUser_zG_Stage sv_width gpa access))

def translate_PTE_addr (pte_addr : (BitVec 64)) (access : (MemoryAccessType mem_payload)) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result (physaddr × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  if ((stage == VS_Stage) : Bool)
  then
    (do
      match (← (translate_g_stage pte_addr access)) with
      | .Ok (pa, pbmt, ext_ptw) => (pure (Ok ((Physaddr pa), pbmt, ext_ptw)))
      | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw))))
  else (pure (Ok ((Physaddr pte_addr), PBMT_PMA, ext_ptw)))

/-- Type quantifiers: k_ex1173987_ : Bool, level : Nat, k_ex1173985_ : Bool, k_ex1173984_ : Bool, sv_width
  : Nat, (is_sv_or_svx4_mode sv_width), 0 ≤ level ∧
  level ≤
  (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 1 else (if ( sv_width = 39 ∨ sv_width = 41  : Bool) then 2 else (if ( sv_width
  = 48 ∨ sv_width = 50  : Bool) then 3 else 4))) -/
def pt_walk (sv_width : Nat) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (pt_base : (BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (level : Nat) (global : Bool) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)) := SailME.run do
  let _ : Unit := (ptw_start_callback stage level (zero_extend (m := 64) vpn) access priv)
  let log_pte_size_bytes :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 2
    else 3
  let vpn_i_size := (pagesize_bits -i log_pte_size_bytes)
  let is_svx4_root :=
    (((sv_width == 34) || ((sv_width == 41) || ((sv_width == 50) || (sv_width == 59)))) && (level == (get_root_level
          sv_width)))
  let vpn_lo := (level *i vpn_i_size)
  let vpn_hi :=
    if (is_svx4_root : Bool)
    then (((level +i 1) *i vpn_i_size) +i 1)
    else (((level +i 1) *i vpn_i_size) -i 1)
  let pte_addr :=
    ((pt_base +++ (zeros (n := pagesize_bits))) + (zero_extend
        (m := ((if (((sv_width == 32) || (sv_width == 34)) : Bool)
          then 22
          else 44) +i 12))
        ((Sail.BitVec.extractLsb vpn vpn_hi vpn_lo) +++ (zeros (n := log_pte_size_bytes)))))
  sail_assert ((sv_width == 32) || ((sv_width == 34) || (xlen == 64))) "sys/vmem.sail:339.41-339.42"
  let pte_addr_original := (Physaddr (zero_extend (m := 64) pte_addr))
  let pte_addr ← (( do
    match (← (translate_PTE_addr (zero_extend (m := 64) pte_addr) (Load PageTableEntry) stage
        ext_ptw)) with
    | .Ok (pa, _, _) => (pure pa)
    | .Err (e, _) =>
      SailME.throw (← do
          (pure (Err
              ((PTW_Implicit_Error
                ((← (translationException access e)), (zero_extend (m := 64) pte_addr), (Load
                  PageTableEntry))), ext_ptw)))) ) : SailME
    (Result ((PTW_Output sv_width) × Unit) (PTW_Error × Unit)) physaddr )
  match (← (read_pte pte_addr (2 ^i log_pte_size_bytes))) with
  | .Err _ =>
    (let _ : Unit := (ptw_fail_callback stage level (PTW_No_Access ()) (bits_of_physaddr pte_addr))
    (pure (Err ((PTW_No_Access ()), ext_ptw))))
  | .Ok pte =>
    (do
      let _ : Unit :=
        (ptw_step_callback stage level (bits_of_physaddr pte_addr) (zero_extend (m := 64) pte))
      let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
      let global := (global || ((bne stage G_Stage) && ((_get_PTE_Flags_G pte_flags) == 1#1)))
      if (((not (← (pte_is_invalid pte_flags (ext_bits_of_PTE pte) stage))) && ((pte_is_non_leaf
               pte_flags) && (level >b 0))) : Bool)
      then
        (do
          let ppn := (PPN_of_PTE pte)
          (pt_walk sv_width vpn access priv mxr do_sum ppn (level -i 1) global stage ext_ptw))
      else
        (do
          match (← (check_leaf_pte sv_width vpn access priv mxr do_sum pte pte_addr level stage
              ext_ptw)) with
          | .Err (e, ext_ptw) => (pure (Err (e, ext_ptw)))
          | .Ok (ppn, pbmt, ext_ptw) =>
            (let _ : Unit := (ptw_success_callback stage level (zero_extend (m := 64) ppn))
            (pure (Ok
                ({ ppn := ppn
                   pte := pte
                   pteAddr := pte_addr_original
                   level := level
                   pbmt := pbmt
                   global := global }, ext_ptw))))))
termination_by (let (_, _, _, _, _, _, _, level, _, _, _) :=
  (sv_width, vpn, access, priv, mxr, do_sum, pt_base, level, global, stage, ext_ptw)
level).toNat

/-- Type quantifiers: sv_width : Nat, (is_sv_or_svx4_mode sv_width) -/
def update_and_write_pte (sv_width : Nat) (pteAddr : physaddr) (pte : (BitVec (if ( sv_width = 32
  ∨ sv_width = 34  : Bool) then 32 else 64))) (access : (MemoryAccessType mem_payload)) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((PTE_Update_Result sv_width) × Unit) (PTW_Error × Unit)) := SailME.run do
  match (← (update_PTE_Bits pte access stage)) with
  | none => (pure (Ok ((PTE_Update_Done none), ext_ptw)))
  | .some pte_new =>
    (do
      if ((← (hw_updates_pte stage)) : Bool)
      then
        (do
          let pte_width :=
            if (((sv_width == 32) || (sv_width == 34)) : Bool)
            then 4
            else 8
          let pte_paddr ← (( do
            match (← (translate_PTE_addr (bits_of_physaddr pteAddr) (Store PageTableEntry) stage
                ext_ptw)) with
            | .Ok (pa, _, _) => (pure pa)
            | .Err (e, _) =>
              SailME.throw (← do
                  (pure (Err
                      ((PTW_Implicit_Error
                        ((← (translationException access e)), (bits_of_physaddr pteAddr), (Store
                          PageTableEntry))), ext_ptw)))) ) : SailME
            (Result ((PTE_Update_Result sv_width) × Unit) (PTW_Error × Unit)) physaddr )
          match (← (read_pte_exclusive pte_paddr pte_width)) with
          | .Err _ => (pure (Err ((PTW_No_Access ()), ext_ptw)))
          | .Ok pte_fresh =>
            (do
              if ((pte_fresh != pte) : Bool)
              then (pure (Ok ((PTE_Update_Retry ()), ext_ptw)))
              else
                (do
                  match (← (write_pte_conditional pte_paddr pte_width pte_new)) with
                  | .Ok true => (pure (Ok ((PTE_Update_Done (some pte_new)), ext_ptw)))
                  | .Ok false => (internal_error "sys/vmem.sail" 281 "PTE conditional write failed")
                  | .Err _ => (pure (Err ((PTW_No_Access ()), ext_ptw))))))
      else (pure (Err ((PTW_PTE_Needs_Update ()), ext_ptw))))

/-- Type quantifiers: k_ex1174003_ : Bool, k_ex1174002_ : Bool, retries : Nat, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width), 0 ≤ retries -/
def translate_TLB_miss_retry (retries : Nat) (sv_width : Nat) (asid : (BitVec 16)) (vmid : (BitVec (if ( 64
  = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let initial_level := (get_root_level sv_width)
  let ptw_result ← do
    (pt_walk sv_width vpn access priv mxr do_sum base_ppn initial_level false stage ext_ptw)
  match ptw_result with
  | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw)))
  | .Ok ({ ppn := ppn, pte := pte, pteAddr := pteAddr, level := level, pbmt := pbmt, global := global }, ext_ptw) =>
    (do
      match (← (update_and_write_pte sv_width pteAddr pte access stage ext_ptw)) with
      | .Ok (.PTE_Update_Done (.some new_pte), ext_ptw) =>
        (do
          (add_to_TLB sv_width asid vmid vpn ppn new_pte pteAddr level global stage)
          (pure (Ok (ppn, pbmt, ext_ptw))))
      | .Ok (.PTE_Update_Done none, ext_ptw) =>
        (do
          (add_to_TLB sv_width asid vmid vpn ppn pte pteAddr level global stage)
          (pure (Ok (ppn, pbmt, ext_ptw))))
      | .Ok (.PTE_Update_Retry (), ext_ptw) =>
        (do
          if ((retries >b 0) : Bool)
          then
            (translate_TLB_miss_retry (retries -i 1) sv_width asid vmid base_ppn vpn access priv mxr
              do_sum stage ext_ptw)
          else (internal_error "sys/vmem.sail" 537 "PTE A/D update: retry bound exhausted"))
      | .Err (e, ext_ptw) => (pure (Err (e, ext_ptw))))
termination_by (let (retries, _, _, _, _, _, _, _, _, _, _, _) :=
  (retries, sv_width, asid, vmid, base_ppn, vpn, access, priv, mxr, do_sum, stage, ext_ptw)
retries).toNat

/-- Type quantifiers: k_ex1174011_ : Bool, k_ex1174010_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width) -/
def translate_TLB_miss (sv_width : Nat) (asid : (BitVec 16)) (vmid : (BitVec (if ( 64
  = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  (translate_TLB_miss_retry pte_update_max_retries sv_width asid vmid base_ppn vpn access priv mxr
    do_sum stage ext_ptw)

/-- Type quantifiers: tlb_index : Nat, k_ex1174018_ : Bool, k_ex1174017_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width), 0 ≤ tlb_index ∧ tlb_index ≤ (2 ^ 6 - 1) -/
def translate_TLB_hit (sv_width : Nat) (asid : (BitVec 16)) (vmid : (BitVec (if ( 64
  = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (tlb_index : Nat) (ent : TLB_Entry) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let pte_size :=
    if (((sv_width == 32) || (sv_width == 34)) : Bool)
    then 4
    else 8
  let pte := (tlb_get_pte pte_size ent)
  let ext_pte := (ext_bits_of_PTE pte)
  let pte_flags := (Mk_PTE_Flags (Sail.BitVec.extractLsb pte 7 0))
  let pte_check ← do (check_PTE_permission access priv stage mxr do_sum pte_flags ext_pte ext_ptw)
  match pte_check with
  | .PTE_Check_Failure (ext_ptw, pte_failure) =>
    (pure (Err ((ext_get_ptw_error pte_failure), ext_ptw)))
  | .PTE_Check_Success ext_ptw =>
    (do
      match (← (update_and_write_pte sv_width ent.pteAddr pte access stage ext_ptw)) with
      | .Ok (.PTE_Update_Done (.some pte), ext_ptw) =>
        (do
          (write_TLB tlb_index (tlb_set_pte ent (pte : (BitVec (pte_size * 8)))))
          (pure (Ok ((tlb_get_ppn sv_width ent vpn), (← (tlb_get_pbmt ent)), ext_ptw))))
      | .Ok (.PTE_Update_Done none, ext_ptw) =>
        (pure (Ok ((tlb_get_ppn sv_width ent vpn), (← (tlb_get_pbmt ent)), ext_ptw)))
      | .Ok (.PTE_Update_Retry (), ext_ptw) =>
        (translate_TLB_miss sv_width asid vmid base_ppn vpn access priv mxr do_sum stage ext_ptw)
      | .Err (e, ext_ptw) => (pure (Err (e, ext_ptw))))

/-- Type quantifiers: k_ex1174026_ : Bool, k_ex1174025_ : Bool, sv_width : Nat, (is_sv_or_svx4_mode
  sv_width) -/
def translate (sv_width : Nat) (asid : (BitVec 16)) (vmid : (BitVec (if ( 64
  = 32  : Bool) then 7 else 14))) (base_ppn : (BitVec (if ( sv_width = 32 ∨ sv_width = 34  : Bool) then 22 else 44))) (vpn : (BitVec (sv_width - 12))) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (mxr : Bool) (do_sum : Bool) (stage : TranslationStage) (ext_ptw : Unit) : SailM (Result ((BitVec (if ( sv_width
  = 32 ∨ sv_width = 34  : Bool) then 22 else 44)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (← (lookup_TLB sv_width asid vmid vpn stage)) with
  | .some (index, ent) =>
    (translate_TLB_hit sv_width asid vmid base_ppn vpn access priv mxr do_sum index ent stage
      ext_ptw)
  | none =>
    (do
      (generate_event EV_TLB_MISS)
      (translate_TLB_miss sv_width asid vmid base_ppn vpn access priv mxr do_sum stage ext_ptw))

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, sv_width : Nat, (is_sv_or_svx4_mode sv_width) ∧
  k_n ≥ sv_width -/
def translate_stage (sv_width : Nat) (addr : (BitVec k_n)) (access : (MemoryAccessType mem_payload)) (priv : Privilege) (stage : TranslationStage) : SailM (Result ((BitVec (if ( 64
  = 32  : Bool) then 34 else 64)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  match (translate_validate_address addr sv_width stage) with
  | .Err e => (pure (Err (e, init_ext_ptw)))
  | .Ok valid_addr =>
    (do
      sail_assert (((xlen == 32) && ((sv_width == 32) || (sv_width == 34))) || ((xlen == 64) && ((sv_width != 32) && (sv_width != 34)))) "sys/vmem.sail:682.60-682.61"
      let asid ← do (get_asid stage)
      let vmid ← do (get_vmid stage)
      let mxr ← do (get_mxr stage)
      let do_sum ← do (get_sum stage)
      let vpn := (Sail.BitVec.extractLsb valid_addr (sv_width -i 1) pagesize_bits)
      let base_ppn ← do (xatp_to_ppn stage)
      let eff_priv :=
        if ((stage == G_Stage) : Bool)
        then User
        else priv
      let res ← do
        (translate sv_width asid vmid base_ppn vpn access eff_priv mxr do_sum stage init_ext_ptw)
      match res with
      | .Ok (ppn, pbmt, ext_ptw) =>
        (pure (Ok
            ((zero_extend (m := 64)
              (ppn +++ (Sail.BitVec.extractLsb valid_addr (pagesize_bits -i 1) 0))), pbmt, ext_ptw)))
      | .Err (f, ext_ptw) => (pure (Err (f, ext_ptw))))

def satp_mode (priv : Privilege) : SailM SATPMode := do
  if ((← do
       if ((priv == Machine) : Bool)
       then (pure true)
       else (pure (not (← (currentlyEnabled Ext_S))))) : Bool)
  then (pure Bare)
  else
    (do
      let arch ← do (architecture Supervisor)
      let mbits ← (( do
        match arch with
        | .RV64 =>
          (do
            sail_assert (xlen ≥b 64) "sys/vmem.sail:441.33-441.34"
            (pure (_get_Satp64_Mode (Mk_Satp64 (← readReg satp)))))
        | .RV32 =>
          (pure (0b000#3 +++ (_get_Satp32_Mode
                (Mk_Satp32 (Sail.BitVec.extractLsb (← readReg satp) 31 0)))))
        | .RV128 => (internal_error "sys/vmem.sail" 443 "RV128 not supported") ) : SailM
        LeanRV64D.satp_mode )
      match (← (satpMode_of_bits arch mbits)) with
      | .some m => (pure m)
      | none => (internal_error "sys/vmem.sail" 448 "invalid translation mode in satp"))

def vsatp_mode (_ : Unit) : SailM SATPMode := do
  let arch ← do (architecture VirtualSupervisor)
  let mbits ← (( do
    match arch with
    | .RV64 =>
      (do
        sail_assert (xlen ≥b 64) "sys/vmem.sail:459.31-459.32"
        (pure (_get_Satp64_Mode (Mk_Satp64 (← readReg vsatp)))))
    | .RV32 =>
      (pure (0b000#3 +++ (_get_Satp32_Mode
            (Mk_Satp32 (Sail.BitVec.extractLsb (← readReg vsatp) 31 0)))))
    | .RV128 => (internal_error "sys/vmem.sail" 461 "RV128 not supported") ) : SailM
    LeanRV64D.satp_mode )
  match (← (satpMode_of_bits arch mbits)) with
  | .some m => (pure m)
  | none => (internal_error "sys/vmem.sail" 466 "invalid translation mode in vsatp")

def satp_mode_width_forwards (arg_ : SATPMode) : SailM Int := do
  match arg_ with
  | .Sv32 => (pure 32)
  | .Sv39 => (pure 39)
  | .Sv48 => (pure 48)
  | .Sv57 => (pure 57)
  | _ =>
    (do
      sail_assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [32, 39, 48, 57] -/
def satp_mode_width_backwards (arg_ : Nat) : SATPMode :=
  match arg_ with
  | 32 => Sv32
  | 39 => Sv39
  | 48 => Sv48
  | _ => Sv57

def satp_mode_width_forwards_matches (arg_ : SATPMode) : Bool :=
  match arg_ with
  | .Sv32 => true
  | .Sv39 => true
  | .Sv48 => true
  | .Sv57 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [32, 39, 48, 57] -/
def satp_mode_width_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 32 => true
  | 39 => true
  | 48 => true
  | 57 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [34, 41, 50, 59] -/
def hgatp_mode_width_backwards (arg_ : Nat) : HGATPMode :=
  match arg_ with
  | 34 => Sv32x4
  | 41 => Sv39x4
  | 50 => Sv48x4
  | _ => Sv57x4

def hgatp_mode_width_forwards_matches (arg_ : HGATPMode) : Bool :=
  match arg_ with
  | .Sv32x4 => true
  | .Sv39x4 => true
  | .Sv48x4 => true
  | .Sv57x4 => true
  | _ => false

/-- Type quantifiers: arg_ : Nat, List.elem arg_ [34, 41, 50, 59] -/
def hgatp_mode_width_backwards_matches (arg_ : Nat) : Bool :=
  match arg_ with
  | 34 => true
  | 41 => true
  | 50 => true
  | 59 => true
  | _ => false

def translate_vs_stage (vaddr : virtaddr) (access : (MemoryAccessType mem_payload)) (p : Privilege) : SailM (Result ((BitVec (if ( 64
  = 32  : Bool) then 34 else 64)) × page_based_mem_type × Unit) (PTW_Error × Unit)) := do
  let (stage, mode) ← do
    if (((p == VirtualSupervisor) || (p == VirtualUser)) : Bool)
    then (pure (VS_Stage, (← (vsatp_mode ()))))
    else (pure (S_Stage, (← (satp_mode p))))
  if ((mode == Bare) : Bool)
  then (pure (Ok ((zero_extend (m := 64) (bits_of_virtaddr vaddr)), PBMT_PMA, init_ext_ptw)))
  else
    (do
      let sv_width ← do (satp_mode_width_forwards mode)
      sail_assert (sv_width ≤b xlen) "sys/vmem.sail:715.25-715.26"
      (translate_stage sv_width (bits_of_virtaddr vaddr) access p stage))

def build_exception_context (gva : virtaddr) (gpa : (BitVec 64)) (access : (MemoryAccessType mem_payload)) (ptw_error : PTW_Error) (stage : TranslationStage) : SailM ExceptionContext := do
  match stage with
  | .S_Stage =>
    (pure { trap := ← (translationException access ptw_error)
            excinfo_is_gva := false
            excinfo := (zero_extend (m := 64) (bits_of_virtaddr gva))
            excinfo2 := none
            excinst := none
            excinst_offset := (zeros (n := 5))
            ext := none })
  | .VS_Stage =>
    (do
      match ptw_error with
      | .PTW_Implicit_Error (e, pte_addr, access) =>
        (do
          let is_write ← (( do
            match access with
            | .Store _ => (pure true)
            | .Load _ => (pure false)
            | _ => (internal_error "sys/vmem.sail" 776 "invalid memory access type") ) : SailM Bool
            )
          let trap := (convertToGuestException e)
          let tval2 := (g_stage_tval2_exception_value trap pte_addr)
          (pure { trap := trap
                  excinfo_is_gva := true
                  excinfo := (zero_extend (m := 64) (bits_of_virtaddr gva))
                  excinfo2 := (some tval2)
                  excinst := if ((tval2 != (zeros (n := 64))) : Bool)
                    then
                      (some
                        (if (is_write : Bool)
                        then (zero_extend (m := 64) 0x00003020#32)
                        else (zero_extend (m := 64) 0x00003000#32)))
                    else none
                  excinst_offset := (zeros (n := 5))
                  ext := none }))
      | _ =>
        (pure { trap := ← (translationException access ptw_error)
                excinfo_is_gva := true
                excinfo := (zero_extend (m := 64) (bits_of_virtaddr gva))
                excinfo2 := (some (zeros (n := 64)))
                excinst := none
                excinst_offset := (zeros (n := 5))
                ext := none }))
  | .G_Stage =>
    (do
      let trap ← do (pure (convertToGuestException (← (translationException access ptw_error))))
      (pure { trap := trap
              excinfo_is_gva := true
              excinfo := (zero_extend (m := 64) (bits_of_virtaddr gva))
              excinfo2 := (some (g_stage_tval2_exception_value trap gpa))
              excinst := none
              excinst_offset := (zeros (n := 5))
              ext := none }))

def is_svukte_qualified (access : (MemoryAccessType mem_payload)) (eff_priv : Privilege) (mode : SATPMode) : SailM Bool := do
  let qualified_access_type :=
    ((access == (InstructionFetch ())) || (not (is_implicit_access access)))
  let ukte_enable ← do
    if ((← do
         if ((eff_priv == VirtualUser) : Bool)
         then (pure ((← readReg cur_privilege) == User))
         else (pure false)) : Bool)
    then (pure (_get_Hstatus_HUKTE (← readReg hstatus)))
    else (pure (_get_SEnvcfg_UKTE (← (read_senvcfg ()))))
  (pure ((bne mode Bare) && (((eff_priv == User) || (eff_priv == VirtualUser)) && (qualified_access_type && (ukte_enable == 1#1)))))

def translateAddr (gva : virtaddr) (access : (MemoryAccessType mem_payload)) (p : Privilege) : SailM (Result (physaddr × page_based_mem_type × Unit) (ExceptionContext × Unit)) := SailME.run do
  let is_virtual_access := ((p == VirtualSupervisor) || (p == VirtualUser))
  let mode ← do
    if (is_virtual_access : Bool)
    then (vsatp_mode ())
    else (satp_mode p)
  if ((← (is_shadow_stack_access access)) : Bool)
  then
    (do
      if ((((mode == Bare) && (bne p Machine)) || (p == Machine)) : Bool)
      then
        SailME.throw ((Err
            ({ trap := (E_SAMO_Access_Fault ())
               excinfo_is_gva := is_virtual_access
               excinfo := (zero_extend (m := 64) (bits_of_virtaddr gva))
               excinfo2 := none
               excinst := none
               excinst_offset := (zeros (n := 5))
               ext := none }, init_ext_ptw)) : (Result (physaddr × page_based_mem_type × Unit) (ExceptionContext × Unit)))
      else (pure ()))
  else (pure ())
  if (((← (is_svukte_qualified access p mode)) && ((BitVec.access (bits_of_virtaddr gva)
           (xlen -i 1)) == 1#1)) : Bool)
  then
    (pure (Err
        ((make_exception_context (← (translationException access (PTW_Invalid_Addr ())))
          (zero_extend (m := 64) (bits_of_virtaddr gva)) is_virtual_access none), init_ext_ptw)))
  else
    (do
      match (← (translate_vs_stage gva access p)) with
      | .Ok (gpa, vs_pbmt, ext_ptw) =>
        (do
          if ((not is_virtual_access) : Bool)
          then (pure (Ok ((Physaddr gpa), vs_pbmt, ext_ptw)))
          else
            (do
              match (← (translate_g_stage gpa access)) with
              | .Ok (spa, g_pbmt, ext_ptw) =>
                (let pbmt :=
                  if ((bne vs_pbmt PBMT_PMA) : Bool)
                  then vs_pbmt
                  else g_pbmt
                (pure (Ok ((Physaddr spa), pbmt, ext_ptw))))
              | .Err (ptw_error, ext_ptw) =>
                (pure (Err
                    ((← (build_exception_context gva gpa access ptw_error G_Stage)), ext_ptw)))))
      | .Err (ptw_error, ext_ptw) =>
        (pure (Err
            ((← (build_exception_context gva (zeros (n := 64)) access ptw_error
                (if (is_virtual_access : Bool)
                then VS_Stage
                else S_Stage))), ext_ptw))))

def reset_vmem (_ : Unit) : SailM Unit := do
  writeReg vsatp (zeros (n := 64))
  writeReg hgatp (zeros (n := 64))
  (reset_TLB ())

