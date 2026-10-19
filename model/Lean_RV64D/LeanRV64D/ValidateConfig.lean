import LeanRV64D.Flow
import LeanRV64D.Arith
import LeanRV64D.Vector
import LeanRV64D.Prelude
import LeanRV64D.IsaVersion
import LeanRV64D.Xlen
import LeanRV64D.Vlen
import LeanRV64D.MemAddrtype
import LeanRV64D.PlatformConfig
import LeanRV64D.Types
import LeanRV64D.SysRegs
import LeanRV64D.InterruptInterface
import LeanRV64D.InterruptRegs
import LeanRV64D.PmpRegs
import LeanRV64D.SdtrigTypes
import LeanRV64D.PmUtils
import LeanRV64D.Pma

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

def check_privs (_ : Unit) : Bool :=
  if (((true : Bool) && (not (true : Bool))) : Bool)
  then
    (let _ : Unit :=
      (print_endline "User mode (U) should be enabled if supervisor mode (S) is enabled.")
    false)
  else true

def check_tvecs (_ : Unit) : Bool :=
  let valid : Bool := true
  let valid : Bool :=
    if (((not (true : Bool)) && (not (true : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "`mtvec` specifies neither `direct` or `vectored` is supported; one of the modes must be supported.")
      valid)
    else valid
  let valid : Bool :=
    if (((true : Bool) && ((not (true : Bool)) && (not (true : Bool)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "`stvec` specifies neither `direct` or `vectored` is supported; one of the modes must be supported.")
      valid)
    else valid
  if (((false : Bool) && ((not (true : Bool)) && (not (true : Bool)))) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit :=
      (print_endline
        "`vstvec` specifies neither `direct` or `vectored` is supported; one of the modes must be supported.")
    valid)
  else valid

def require_Sv32 (ext_name : String) : Bool :=
  if ((not (false : Bool)) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "The "
          (HAppend.hAppend ext_name
            (HAppend.hAppend " extension is enabled but Sv32 is disabled: "
              (HAppend.hAppend ext_name " depends on Sv32 on RV32.")))))
    false)
  else true

def check_mutable_misa (_ : Unit) : Bool :=
  let valid : Bool := true
  let valid : Bool :=
    if (((true : Bool) && (((hartSupports Ext_D) && (not (true : Bool))) || ((hartSupports Ext_V) && (not
               (true : Bool))))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "`extensions.F.mutable_misa` is true but `extensions.D.mutable_misa` and/or `extensions.V.mutable_misa` is false: mutable F requires mutable D and V when they are supported.")
      valid)
    else valid
  let valid : Bool :=
    if (((true : Bool) && ((hartSupports Ext_V) && (not (true : Bool)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "`extensions.D.mutable_misa` is true but `extensions.V.mutable_misa` is false: mutable D requires mutable V if V is supported.")
      valid)
    else valid
  let valid : Bool :=
    if (((true : Bool) && (((hartSupports Ext_S) && (not (true : Bool))) || ((hartSupports Ext_H) && (not
               (true : Bool))))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "`extensions.U.mutable_misa` is true but `extensions.S.mutable_misa` and/or `extensions.H.mutable_misa` is false: mutable U requires mutable S and H when they are supported.")
      valid)
    else valid
  if (((true : Bool) && ((hartSupports Ext_H) && (not (true : Bool)))) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit :=
      (print_endline
        "`extensions.S.mutable_misa` is true but `extensions.H.mutable_misa` is false: mutable S requires mutable H if H is supported.")
    valid)
  else valid

def require_Sv39 (ext_name : String) : Bool :=
  if ((not (true : Bool)) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "The "
          (HAppend.hAppend ext_name
            (HAppend.hAppend " extension is enabled but Sv39 is disabled: "
              (HAppend.hAppend ext_name " depends on Sv39 on RV64.")))))
    false)
  else true

/-- Type quantifiers: k_ex1173424_ : Bool -/
def check_sha_dependency (name : String) (supported : Bool) : Bool :=
  if ((not supported) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "The Sha extension is enabled but "
          (HAppend.hAppend name
            (HAppend.hAppend " is disabled: supporting Sha requires " (HAppend.hAppend name ".")))))
    false)
  else true

/-- Type quantifiers: k_ex1173426_ : Bool, k_ex1173425_ : Bool -/
def check_shgatpa_mode (sv_name : String) (satp_supported : Bool) (hgatp_supported : Bool) : Bool :=
  if ((satp_supported && (not hgatp_supported)) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "The Shgatpa extension is enabled and "
          (HAppend.hAppend sv_name
            (HAppend.hAppend " is supported in `satp`, but the matching "
              (HAppend.hAppend sv_name "x4 mode is disabled (under `extensions.H.hgatp_modes`).")))))
    false)
  else true

/-- Type quantifiers: k_ex1173428_ : Bool, k_ex1173427_ : Bool -/
def check_shvsatpa_mode (sv_name : String) (satp_supported : Bool) (vsatp_supported : Bool) : Bool :=
  if ((satp_supported && (not vsatp_supported)) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "The Shvsatpa extension is enabled and "
          (HAppend.hAppend sv_name
            (HAppend.hAppend " is supported in `satp`, but "
              (HAppend.hAppend sv_name " is disabled in `vsatp` (under `extensions.H.vsatp_modes`).")))))
    false)
  else true

def require_virtual_memory (ext_name : String) : SailM Bool := do
  sail_assert (xlen == 64) "postlude/validate_config.sail:113.19-113.20"
  (pure (require_Sv39 ext_name))

def check_mmu_config (_ : Unit) : SailM Bool := do
  let valid : Bool := true
  let _ : Unit :=
    let _ : Unit :=
      if (((not (true : Bool)) && ((true : Bool) || ((true : Bool) || (true : Bool)))) : Bool)
      then
        (let valid : Bool := false
        (print_endline
          "Supervisor mode (S) disabled but one of (Sv57, Sv48, Sv39) is enabled: cannot support address translation without supervisor mode."))
      else ()
    let _ : Unit :=
      if (((true : Bool) && (not
             ((true : Bool) || ((true : Bool) || ((true : Bool) || (true : Bool)))))) : Bool)
      then
        (let valid : Bool := false
        (print_endline
          "Supervisor mode (S) is enabled but no `satp` mode is supported for RV64: enable Svbare or one of (Sv39, Sv48, Sv57)."))
      else ()
    let _ : Unit :=
      if (((true : Bool) && (not (true : Bool))) : Bool)
      then
        (let valid : Bool := false
        (print_endline
          "Sv57 is enabled but Sv48 is disabled: supporting Sv57 requires supporting Sv48."))
      else ()
    let _ : Unit :=
      if (((true : Bool) && (not (true : Bool))) : Bool)
      then
        (let valid : Bool := false
        (print_endline
          "Sv48 is enabled but Sv39 is disabled: supporting Sv48 requires supporting Sv39."))
      else ()
    let _ : Unit :=
      if ((false : Bool) : Bool)
      then
        (let valid : Bool := false
        (print_endline "Sv32 is enabled: Sv32 is not supported on RV64."))
      else ()
    if ((false : Bool) : Bool)
    then
      (let _ : Unit :=
        if ((sys_vsatp_sv57_supported && (not sys_vsatp_sv48_supported)) : Bool)
        then
          (let valid : Bool := false
          (print_endline
            "Sv57 is enabled for `vsatp` but Sv48 is disabled: supporting Sv57 requires supporting Sv48."))
        else ()
      let _ : Unit :=
        if ((sys_vsatp_sv48_supported && (not sys_vsatp_sv39_supported)) : Bool)
        then
          (let valid : Bool := false
          (print_endline
            "Sv48 is enabled for `vsatp` but Sv39 is disabled: supporting Sv48 requires supporting Sv39."))
        else ()
      if (sys_vsatp_sv32_supported : Bool)
      then
        (let valid : Bool := false
        (print_endline "Sv32 is enabled for `vsatp`: Sv32 is not currently supported on RV64."))
      else ())
    else ()
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then (valid && (require_Sv39 "Svrsw60t59b"))
    else valid
  let valid ← (( do
    if ((true : Bool) : Bool)
    then
      (do
        if (valid : Bool)
        then (require_virtual_memory "Ssccptr")
        else (pure false))
    else (pure valid) ) : SailM Bool )
  let valid ← (( do
    if ((true : Bool) : Bool)
    then
      (do
        if (valid : Bool)
        then (require_virtual_memory "Svade")
        else (pure false))
    else (pure valid) ) : SailM Bool )
  let valid ← (( do
    if ((true : Bool) : Bool)
    then
      (do
        if (valid : Bool)
        then (require_virtual_memory "Svadu")
        else (pure false))
    else (pure valid) ) : SailM Bool )
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then (valid && (require_Sv39 "Svpbmt"))
    else valid
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then (valid && (require_Sv39 "Svnapot"))
    else valid
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then (valid && (require_Sv39 "Svukte"))
    else valid
  let valid ← (( do
    if ((true : Bool) : Bool)
    then
      (do
        if (valid : Bool)
        then (require_virtual_memory "Svvptc")
        else (pure false))
    else (pure valid) ) : SailM Bool )
  let asidlen_nat : Nat := asidlen
  let valid : Bool :=
    if (((true : Bool) && (asidlen_nat >b asidmax)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "`memory.asidlen` is "
            (HAppend.hAppend (Int.repr asidlen)
              (HAppend.hAppend " but cannot be greater than "
                (HAppend.hAppend (Int.repr asidmax) (HAppend.hAppend " on " "RV64."))))))
      valid)
    else valid
  let vmidlen_nat : Nat := vmidlen
  if (((false : Bool) && (vmidlen_nat >b vmidmax)) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit :=
      (print_endline
        (HAppend.hAppend "`memory.vmidlen` is "
          (HAppend.hAppend (Int.repr vmidlen)
            (HAppend.hAppend " but cannot be greater than "
              (HAppend.hAppend (Int.repr vmidmax) (HAppend.hAppend " on " "RV64."))))))
    (pure valid))
  else (pure valid)

def check_vlen_elen (_ : Unit) : Bool :=
  if (((vlen_exp : Nat) <b (elen_exp : Nat)) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "VLEN (set to 2^"
          (HAppend.hAppend (Int.repr vlen_exp)
            (HAppend.hAppend ") cannot be less than ELEN (set to 2^"
              (HAppend.hAppend (Int.repr elen_exp) ").")))))
    false)
  else
    (if ((((vlen_exp : Nat) <b 3) || (((vlen_exp : Nat) >b 16) : Bool)) : Bool)
    then
      (let _ : Unit :=
        (print_endline
          (HAppend.hAppend "VLEN set to 2^"
            (HAppend.hAppend (Int.repr vlen_exp) " but must be within [2^3, 2^16].")))
      false)
    else
      (if ((((elen_exp : Nat) <b 3) || (((elen_exp : Nat) >b 16) : Bool)) : Bool)
      then
        (let _ : Unit :=
          (print_endline
            (HAppend.hAppend "ELEN set to 2^"
              (HAppend.hAppend (Int.repr elen_exp) " but must be within [2^3, 2^16].")))
        false)
      else true))

def check_vext_config (_ : Unit) : Bool :=
  let valid : Bool := true
  let valid : Bool :=
    if (((vector_support_ge vector_support_level Integer) && (((elen_exp : Nat) <b 5) : Bool)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "Zve*x is enabled but ELEN is 2^"
            (HAppend.hAppend (Int.repr elen_exp) ": ELEN must be >= 2^5")))
      valid)
    else valid
  let max_index_eew := (6 : Nat)
  let valid : Bool :=
    if ((max_index_eew >b elen_exp) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "The maximum index EEW is 2^"
            (HAppend.hAppend (Int.repr max_index_eew)
              (HAppend.hAppend " but ELEN is 2^"
                (HAppend.hAppend (Int.repr elen_exp) ": the index EEW must not exceed ELEN.")))))
      valid)
    else
      (if ((max_index_eew <b 3) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            (HAppend.hAppend "The maximum index EEW is 2^"
              (HAppend.hAppend (Int.repr max_index_eew) " but it should be at least 2^3.")))
        valid)
      else valid)
  let valid : Bool :=
    if (((vector_support_ge vector_support_level Float_single) && (not (false : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zve*f is enabled but F is disabled: supporting Zve*f requires F.")
      valid)
    else valid
  let valid : Bool :=
    if ((vector_support_ge vector_support_level Float_double) : Bool)
    then
      (let valid : Bool :=
        if (((elen_exp : Nat) <b 6) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              (HAppend.hAppend "Zve*d is enabled but ELEN is 2^"
                (HAppend.hAppend (Int.repr elen_exp) ": ELEN must be >= 2^6")))
          valid)
        else valid
      if ((not (hartSupports Ext_D)) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline "Zve*d is enabled but D is disabled: supporting Zve*d requires D.")
        valid)
      else valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zve32x) && (not (true : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zve32x is enabled but Zicsr is disabled: supporting Zve32x requires Zicsr.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zve32x) && (not (hartSupports Ext_Zvl32b))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "VLEN (set to 2^"
            (HAppend.hAppend (Int.repr vlen_exp)
              ") is below the minimum required for Zve32x (need Zvl32b).")))
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zve64x) && (not (hartSupports Ext_Zvl64b))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "VLEN (set to 2^"
            (HAppend.hAppend (Int.repr vlen_exp)
              ") is below the minimum required for Zve64x (need Zvl64b).")))
      valid)
    else valid
  let valid : Bool :=
    if (((vector_support_ge vector_support_level Full) && (not (hartSupports Ext_Zvl128b))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "VLEN (set to 2^"
            (HAppend.hAppend (Int.repr vlen_exp)
              ") is below the minimum required for V (need Zvl128b).")))
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (hartSupports Ext_Zve32f))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvfhmin is enabled but Zve32f is disabled: Zvfhmin requires Zve32f.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && ((not (hartSupports Ext_Zve32f)) || (not (false : Bool)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "Zvfh is enabled but Zve32f and/or Zfhmin are disabled: Zvfh requires Zve32f and Zfhmin.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvbb is enabled but Zve32x is disabled: Zvbb requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not ((hartSupports Ext_Zve64x) || (hartSupports Ext_V)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvbc is enabled but Zve64x and V are disabled: Zvbc requires Zve64x or V.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvkb is enabled but Zve32x is disabled: Zvkb requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvkg is enabled but Zve32x is disabled: Zvkg requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvkned is enabled but Zve32x is disabled: Zvkned requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvknha is enabled but Zve32x is disabled: Zvknha requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not ((hartSupports Ext_Zve64x) || (hartSupports Ext_V)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "Zvknhb is enabled but Zve64x and V are disabled: Zvknhb requires Zve64x or V.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvksed is enabled but Zve32x is disabled: Zvksed requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvksh is enabled but Zve32x is disabled: Zvksh requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvkt is enabled but Zve32x is disabled: Zvkt requires Zve32x.")
      valid)
    else valid
  if (((false : Bool) && (not (hartSupports Ext_Zve32x))) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit :=
      (print_endline "Zvabd is enabled but Zve32x is disabled: Zvabd requires Zve32x.")
    valid)
  else valid

def check_pma_region (region : PMA_Region) : Bool := ExceptM.run do
  if (((Sail.BitVec.extractLsb region.base (pagesize_bits -i 1) 0) != (zeros
         (n := (((12 -i 1) -i 0) +i 1)))) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "Memory region starting at "
          (HAppend.hAppend (BitVec.toFormatted region.base)
            " does not start on a 4K (page) boundary.")))
    (pure false))
  else
    (do
      if (((Sail.BitVec.extractLsb region.size (pagesize_bits -i 1) 0) != (zeros
             (n := (((12 -i 1) -i 0) +i 1)))) : Bool)
      then
        (let _ : Unit :=
          (print_endline
            (HAppend.hAppend "Memory region starting at "
              (HAppend.hAppend (BitVec.toFormatted region.base)
                (HAppend.hAppend " with size "
                  (HAppend.hAppend (BitVec.toFormatted region.size)
                    " does not end on a 4K (page) boundary.")))))
        (pure false))
      else
        (do
          let pma := region.attributes
          match pma.mem_type with
          | .MainMemory =>
            (do
              if ((not
                   (pma.readable && (pma.writable && (pma.read_idempotent && pma.write_idempotent)))) : Bool)
              then
                throw (let _ : Unit :=
                    (print_endline
                      (HAppend.hAppend "Memory region starting at "
                        (HAppend.hAppend (BitVec.toFormatted region.base)
                          (HAppend.hAppend " is marked as "
                            (HAppend.hAppend (memory_region_type_str_forwards pma.mem_type)
                              " but is not readable, read-idempotent, writable, and write-idempotent.")))))
                  false : Bool)
              else (pure ()))
          | .IOMemory => (pure ())
          (pure true)))

def undefined_pma_check_opts (_ : Unit) : SailM pma_check_opts := do
  (pure { zama16b := ← (undefined_bool ())
          ziccamoa := ← (undefined_bool ())
          ziccamoc := ← (undefined_bool ())
          ziccif := ← (undefined_bool ())
          zicclsm := ← (undefined_bool ())
          ziccrse := ← (undefined_bool ())
          ssccptr := ← (undefined_bool ())
          svadu := ← (undefined_bool ()) })

/-- Type quantifiers: k_ex1173429_ : Bool -/
def check_pma_regions (regions : (List PMA_Region)) (prev_base : (BitVec 64)) (prev_size : (BitVec 64)) (check_opts : pma_check_opts) (found_valid_svadu_pma : Bool) : Bool := ExceptM.run do
  match regions with
  | [] =>
    (if ((check_opts.svadu && (not found_valid_svadu_pma)) : Bool)
    then
      (let _ : Unit :=
        (print_endline
          "The Svadu extension is enabled but no memory region supports hardware page-table writes: Svadu requires at least one region provide this support.")
      (pure false))
    else (pure true))
  | (region :: rest) =>
    (do
      if ((zopz0zI_u region.base (prev_base + prev_size)) : Bool)
      then
        (let _ : Unit :=
          (print_endline
            (HAppend.hAppend "Memory region starting at "
              (HAppend.hAppend (BitVec.toFormatted region.base)
                (HAppend.hAppend " is not above the end of the previous region starting at "
                  (HAppend.hAppend (BitVec.toFormatted prev_base)
                    (HAppend.hAppend " and ending at "
                      (HAppend.hAppend (BitVec.toFormatted (prev_base + prev_size)) ".")))))))
        (pure false))
      else
        (do
          if ((((BitVec.toNatInt region.base) +i (BitVec.toNatInt region.size)) >b (2 ^i physaddr_bits)) : Bool)
          then
            (let _ : Unit :=
              (print_endline
                (HAppend.hAppend "Memory region starting at "
                  (HAppend.hAppend (BitVec.toFormatted region.base)
                    (HAppend.hAppend " ends at "
                      (HAppend.hAppend (BitVec.toFormatted (region.base + region.size))
                        (HAppend.hAppend
                          " which is above the representable limit of the physical address bit size (i.e. "
                          (HAppend.hAppend (Int.repr physaddr_bits) " from `memory.physaddr_bits`).")))))))
            (pure false))
          else
            (do
              if ((not (check_pma_region region)) : Bool)
              then (pure false)
              else
                (do
                  let attributes := region.attributes
                  if (((attributes.mem_type == MainMemory) && (attributes.cacheable && attributes.coherent)) : Bool)
                  then
                    (do
                      let mag := attributes.misaligned_atomicity_granule_size_exp
                      if ((check_opts.zama16b && (mag <b 4)) : Bool)
                      then
                        throw (let _ : Unit :=
                            (print_endline
                              (HAppend.hAppend "Main memory region starting at "
                                (HAppend.hAppend (BitVec.toFormatted region.base)
                                  (HAppend.hAppend " is coherent and cacheable with "
                                    (HAppend.hAppend
                                      (if ((mag == 0) : Bool)
                                      then "no specified misaligned atomicity granule PMA"
                                      else
                                        (HAppend.hAppend "a misaligned atomicity granule size of 2^"
                                          (Int.repr mag)))
                                      ", but Zama16b is enabled which requires granule size of at least 2^4 bytes.")))))
                          false : Bool)
                      else
                        (do
                          if ((check_opts.ziccamoa && (pma_atomicity_support_lt
                                 attributes.atomic_support AMOArithmetic)) : Bool)
                          then
                            throw (let _ : Unit :=
                                (print_endline
                                  (HAppend.hAppend "Main memory region starting at "
                                    (HAppend.hAppend (BitVec.toFormatted region.base)
                                      (HAppend.hAppend " is coherent and cacheable with "
                                        (HAppend.hAppend
                                          (atomic_support_str_forwards attributes.atomic_support)
                                          " atomicity support, but Ziccamoa is enabled which requires AMOArithmetic support.")))))
                              false : Bool)
                          else
                            (do
                              if ((check_opts.ziccamoc && (bne attributes.atomic_support AMOCASQ)) : Bool)
                              then
                                throw (let _ : Unit :=
                                    (print_endline
                                      (HAppend.hAppend "Main memory region starting at "
                                        (HAppend.hAppend (BitVec.toFormatted region.base)
                                          (HAppend.hAppend " is coherent and cacheable with "
                                            (HAppend.hAppend
                                              (atomic_support_str_forwards attributes.atomic_support)
                                              " atomicity support, but Ziccamoc is enabled which requires AMOCASQ support.")))))
                                  false : Bool)
                              else
                                (do
                                  if ((check_opts.ziccif && (not attributes.executable)) : Bool)
                                  then
                                    throw (let _ : Unit :=
                                        (print_endline
                                          (HAppend.hAppend "Memory region starting at "
                                            (HAppend.hAppend (BitVec.toFormatted region.base)
                                              " is coherent and cacheable with no instruction fetch support, but Ziccif is enabled which requires this support.")))
                                      false : Bool)
                                  else
                                    (do
                                      if (check_opts.zicclsm : Bool)
                                      then
                                        (do
                                          if ((misaligned_exception_is_access_fault
                                               attributes.misaligned_exceptions.load_store) : Bool)
                                          then
                                            throw (let _ : Unit :=
                                                (print_endline
                                                  (HAppend.hAppend "Main memory region starting at "
                                                    (HAppend.hAppend
                                                      (BitVec.toFormatted region.base)
                                                      " is coherent and cacheable with access faults for misaligned scalar loads/stores, but Zicclsm is enabled which requires no exceptions or only misaligned exceptions for such accesses.")))
                                              false : Bool)
                                          else
                                            (do
                                              if ((misaligned_exception_is_access_fault
                                                   attributes.misaligned_exceptions.vector) : Bool)
                                              then
                                                throw (let _ : Unit :=
                                                    (print_endline
                                                      (HAppend.hAppend
                                                        "Main memory region starting at "
                                                        (HAppend.hAppend
                                                          (BitVec.toFormatted region.base)
                                                          " is coherent and cacheable with access faults for misaligned vector loads/stores, but Zicclsm is enabled which requires no exceptions or only misaligned exceptions for such accesses.")))
                                                  false : Bool)
                                              else (pure ())))
                                      else (pure ())
                                      if ((check_opts.ziccrse && (bne attributes.reservability
                                             RsrvEventual)) : Bool)
                                      then
                                        throw (let _ : Unit :=
                                            (print_endline
                                              (HAppend.hAppend "Main memory region starting at "
                                                (HAppend.hAppend (BitVec.toFormatted region.base)
                                                  (HAppend.hAppend
                                                    " is coherent and cacheable with "
                                                    (HAppend.hAppend
                                                      (reservability_str_forwards
                                                        attributes.reservability)
                                                      " reservability support, but Ziccrse is enabled which requires RsrvEventual support.")))))
                                          false : Bool)
                                      else
                                        (do
                                          if ((check_opts.ssccptr && (not
                                                 attributes.supports_pte_read)) : Bool)
                                          then
                                            throw (let _ : Unit :=
                                                (print_endline
                                                  (HAppend.hAppend "Main memory region starting at "
                                                    (HAppend.hAppend
                                                      (BitVec.toFormatted region.base)
                                                      " is coherent and cacheable without hardware page-table read support, but Ssccptr is enabled which requires this support.")))
                                              false : Bool)
                                          else (pure ())))))))
                  else (pure ())
                  let found_valid_svadu_pma :=
                    (found_valid_svadu_pma || (attributes.supports_pte_write && (attributes.reservability == RsrvEventual)))
                  (pure (check_pma_regions rest region.base region.size check_opts
                      found_valid_svadu_pma))))))

def within_configured_pma_memory (component : String) (mem_type_opt : (Option MemoryRegionType)) (addr : (BitVec 64)) (size : (BitVec 64)) : SailM Bool := do
  let valid : Bool := true
  match ((matching_pma_region_bits_range (← readReg pma_regions) addr size), mem_type_opt) with
  | (none, _) =>
    (let valid : Bool := false
    let _ : Unit :=
      (print_endline
        (HAppend.hAppend "The "
          (HAppend.hAppend component " for the platform is not in a defined memory region.")))
    (pure valid))
  | (.some region, .some mem_type) =>
    (if ((bne region.attributes.mem_type mem_type) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "The "
            (HAppend.hAppend component
              (HAppend.hAppend " for the platform is in a memory region starting at "
                (HAppend.hAppend (BitVec.toFormatted region.base)
                  (HAppend.hAppend " which is not a "
                    (HAppend.hAppend (memory_region_type_str_forwards mem_type) " region.")))))))
      (pure valid))
    else (pure valid))
  | (.some _, _) => (pure valid)

def dtb_within_configured_pma_memory (addr : (BitVec 64)) (size : (BitVec 64)) : SailM Bool := do
  (within_configured_pma_memory "DTB" none addr size)

def check_mem_layout (_ : Unit) : SailM Bool := do
  if (((← readReg pma_regions) == []) : Bool)
  then
    (let _ : Unit := (print_endline "No memory regions specified.")
    (pure false))
  else
    (do
      let check_opts : pma_check_opts :=
        { zama16b := true
          ziccamoa := true
          ziccamoc := true
          ziccif := true
          zicclsm := true
          ziccrse := true
          ssccptr := true
          svadu := true }
      let pmas_ok ← do
        (pure (check_pma_regions (← readReg pma_regions) (zeros (n := 64)) (zeros (n := 64))
            check_opts false))
      let clint_supported : Bool := true
      let clint_ok ← do
        if ((not clint_supported) : Bool)
        then (pure true)
        else
          (within_configured_pma_memory "CLINT (platform.clint)" (some IOMemory)
            (← (to_bits_checked (l := 64) (33554432 : Int)))
            (← (to_bits_checked (l := 64) (49152 : Int))))
      let sig_supported : Bool := false
      let sig_ok ← do
        if ((not sig_supported) : Bool)
        then (pure true)
        else
          (within_configured_pma_memory
            "simple interrupt generator (platform.simple_interrupt_generator)" (some IOMemory)
            (← (to_bits_checked (l := 64) (201326592 : Int)))
            (zero_extend (m := 64) plat_sig_size))
      if ((not (pmas_ok && (clint_ok && sig_ok))) : Bool)
      then (pure false)
      else
        (do
          let valid : Bool := true
          let physaddr_bits_nat : Nat := physaddr_bits
          if ((physaddr_bits_nat <b xlen) : Bool)
          then
            (do
              match (none : (Option xlenbits)) with
              | none => (pure valid)
              | .some paddr =>
                (do
                  if ((is_valid_physaddr (← readReg pma_regions)
                       (Physaddr (zero_extend (m := 64) paddr))) : Bool)
                  then
                    (let valid : Bool := false
                    let _ : Unit :=
                      (print_endline
                        (HAppend.hAppend "The configured `memory.invalid_physical_address` ("
                          (HAppend.hAppend (BitVec.toFormatted paddr)
                            ") lies within a configured PMA region, and hence is valid.")))
                    (pure valid))
                  else (pure valid)))
          else (pure valid)))

def check_pmp (_ : Unit) : Bool :=
  let valid : Bool := true
  let valid : Bool :=
    if (((true : Bool) && (sys_pmp_grain != 0)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit := (print_endline "NA4 is not supported if the PMP grain G is non-zero.")
      valid)
    else valid
  if ((sys_pmp_usable_count >b sys_pmp_count) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit :=
      (print_endline
        "The number of usable PMP entries cannot exceed the total number of PMP entries.")
    valid)
  else valid

/-- Type quantifiers: k_ex1173430_ : Bool -/
def check_required_xtval_option (ext_name : String) (name : String) (value : Bool) : Bool :=
  if ((not value) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "The "
          (HAppend.hAppend ext_name
            (HAppend.hAppend " extension is enabled but "
              (HAppend.hAppend name
                " have not been configured (under `base.xtval_nonzero`) to write xtval.")))))
    false)
  else true

def reserved_exception_mask (_ : Unit) : (BitVec 64) :=
  if ((false : Bool) : Bool)
  then (zero_extend (m := 64) 0x0FFFF00024000#52)
  else (zero_extend (m := 64) 0x0FFFF00F24400#52)

def check_misc_extension_dependencies (_ : Unit) : SailM Bool := do
  let valid : Bool := true
  let valid : Bool :=
    if (((false : Bool) && (xlen == 64)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit := (print_endline "The Zcf extension is enabled: Zcf is not supported on RV64.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (false : Bool)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The F and Zfinx extensions are mutually exclusive and cannot be supported simultaneously.")
      valid)
    else valid
  let valid : Bool :=
    if ((not (false : Bool)) : Bool)
    then
      (let valid : Bool :=
        if ((false : Bool) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Zfa extension is enabled but F is disabled: supporting Zfa requires F.")
          valid)
        else valid
      let valid : Bool :=
        if ((false : Bool) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Zfh extension is enabled but F is disabled: supporting Zfh requires F.")
          valid)
        else valid
      let valid : Bool :=
        if ((false : Bool) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Zfhmin extension is enabled but F is disabled: supporting Zfhmin requires F.")
          valid)
        else valid
      let valid : Bool :=
        if ((false : Bool) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Zfbfmin extension is enabled but F is disabled: supporting Zfbfmin requires F.")
          valid)
        else valid
      if ((false : Bool) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The Zcf extension is enabled but F is disabled: supporting Zcf requires F.")
        valid)
      else valid)
    else valid
  let valid : Bool :=
    if (((true : Bool) && (not ((false : Bool) || (true : Bool)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zabha extension is enabled but Zaamo and A are disabled: supporting Zabha requires Zaamo or A.")
      valid)
    else valid
  let valid : Bool :=
    if (((true : Bool) && (not ((false : Bool) || (true : Bool)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zacas extension is enabled but Zaamo and A are disabled: supporting Zacas requires Zaamo or A.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (true : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zfinx extensions is enabled but Zicsr is disabled: supporting Zfinx requires Zicsr.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (false : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zdinx extensions is enabled but Zfinx is disabled: supporting Zdinx requires Zfinx.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (false : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zhinx extensions is enabled but Zfinx is disabled: supporting Zhinx requires Zfinx.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (false : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zhinxmin extensions is enabled but Zfinx is disabled: supporting Zhinxmin requires Zfinx.")
      valid)
    else valid
  let valid : Bool :=
    if (((true : Bool) && (not (true : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zicfilp extension is enabled but Zicsr is disabled: supporting Zicfilp requires Zicsr.")
      valid)
    else valid
  let valid : Bool :=
    if (((true : Bool) && (not
           ((true : Bool) && ((true : Bool) && ((false : Bool) || (true : Bool)))))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zicfiss extension is enabled but one or more of Zicsr, Zimop and (Zaamo or A) are disabled: supporting Zicfiss requires Zicsr, Zimop and (Zaamo or A).")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (hartSupports Ext_Zve32f))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zvfbfmin extension is enabled but Zve32f is disabled: supporting Zvfbfmin requires Zve32f.")
      valid)
    else valid
  let valid : Bool :=
    if (((false : Bool) && ((not (false : Bool)) || (not (false : Bool)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zvfbfwma extension is enabled but either Zfbfmin or Zvfbfmin is disabled: supporting Zvfbfwma requires Zfbfmin and Zvfbfmin.")
      valid)
    else valid
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then
      (let valid : Bool :=
        if ((not (true : Bool)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Sstvala extension writes `stval` which requires supervisor mode (S) but supervisor mode is not enabled.")
          valid)
        else valid
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "load page-faults"
            load_page_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "load access-faults"
            load_access_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "misaligned load exceptions"
            misaligned_load_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "store/AMO page-faults"
            samo_page_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "store/AMO access-faults"
            samo_access_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "misaligned store/AMO exceptions"
            misaligned_samo_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "fetch page-faults"
            fetch_page_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "fetch access-faults"
            fetch_access_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "misaligned fetch exceptions"
            misaligned_fetch_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "hardware breakpoint exceptions"
            hardware_breakpoint_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Sstvala" "illegal instruction exceptions"
            illegal_instruction_writes_xtval))
      if ((false : Bool) : Bool)
      then
        (let valid : Bool :=
          (valid && (check_required_xtval_option "Sstvala" "load guest page-faults"
              load_guest_page_fault_writes_xtval))
        let valid : Bool :=
          (valid && (check_required_xtval_option "Sstvala" "store/AMO guest page-faults"
              samo_guest_page_fault_writes_xtval))
        let valid : Bool :=
          (valid && (check_required_xtval_option "Sstvala" "fetch guest page-faults"
              fetch_guest_page_fault_writes_xtval))
        (valid && (check_required_xtval_option "Sstvala" "virtual instruction exceptions"
            virtual_instruction_writes_xtval)))
      else valid)
    else valid
  let valid : Bool :=
    if ((false : Bool) : Bool)
    then
      (let valid : Bool :=
        if ((not (false : Bool)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Shvstvala extension writes `vstval` which requires the H extension but H is not enabled.")
          valid)
        else valid
      let valid : Bool :=
        (valid && (check_required_xtval_option "Shvstvala" "load page-faults"
            load_page_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Shvstvala" "load access-faults"
            load_access_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Shvstvala" "misaligned load exceptions"
            misaligned_load_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Shvstvala" "store/AMO page-faults"
            samo_page_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Shvstvala" "store/AMO access-faults"
            samo_access_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Shvstvala" "misaligned store/AMO exceptions"
            misaligned_samo_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Shvstvala" "fetch page-faults"
            fetch_page_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Shvstvala" "fetch access-faults"
            fetch_access_fault_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Shvstvala" "misaligned fetch exceptions"
            misaligned_fetch_writes_xtval))
      let valid : Bool :=
        (valid && (check_required_xtval_option "Shvstvala" "hardware breakpoint exceptions"
            hardware_breakpoint_writes_xtval))
      (valid && (check_required_xtval_option "Shvstvala" "illegal instruction exceptions"
          illegal_instruction_writes_xtval)))
    else valid
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then
      (let valid : Bool :=
        if ((not (true : Bool)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Sstvecd extension is enabled but supervisor mode (S) is disabled: supporting Sstvecd requires S.")
          valid)
        else valid
      if ((not (true : Bool)) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The Sstvecd extension is enabled but `stvec` does not support the `direct` mode (see `base.stvec.direct.supported`).")
        valid)
      else valid)
    else valid
  let valid : Bool :=
    if (((true : Bool) && (not (true : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Ssqosid extension is enabled but Zicsr is disabled: supporting Ssqosid requires Zicsr.")
      valid)
    else valid
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then
      (let valid : Bool :=
        if ((not (true : Bool)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Sscounterenw extension is enabled but supervisor mode (S) is disabled: supporting Sscounterenw requires S.")
          valid)
        else valid
      if ((((Sail.BitVec.extractLsb sys_writable_hpm_counters 31 3) &&& (Sail.BitVec.extractLsb
               sys_scounteren_writable_bits 31 3)) != (Sail.BitVec.extractLsb
             sys_writable_hpm_counters 31 3)) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The Sscounterenw extension is enabled but `scounteren` is not writable (via `base.scounteren_writable_bits`) for some supported HPM counters (specified in `base.writable_hpm_counters`).")
        valid)
      else valid)
    else valid
  let valid : Bool :=
    if ((false : Bool) : Bool)
    then
      (let valid : Bool :=
        if ((not (false : Bool)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Shcounterenw extension is enabled but the H extension is disabled: supporting Shcounterenw requires H.")
          valid)
        else valid
      if ((((Sail.BitVec.extractLsb sys_writable_hpm_counters 31 3) &&& (Sail.BitVec.extractLsb
               sys_hcounteren_writable_bits 31 3)) != (Sail.BitVec.extractLsb
             sys_writable_hpm_counters 31 3)) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The Shcounterenw extension is enabled but `hcounteren` is not writable (via `base.hcounteren_writable_bits`) for some supported HPM counters (specified in `base.writable_hpm_counters`).")
        valid)
      else valid)
    else valid
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then
      (let inhibitable_counters : (BitVec 32) := 0b11111111111111111111111111111101#32
      if (((BitVec.access inhibitable_counters 1) == 1#1) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "Bit 1 of `base.mcountinhibit.writable_bits` is set; `mcountinhibit[1]` is read-only zero.")
        valid)
      else valid)
    else valid
  let valid : Bool :=
    if (((true : Bool) || ((true : Bool) || (true : Bool))) : Bool)
    then
      (if (((true : Bool) && (not (true : Bool))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The Ssnpm extensions is enabled but supervisor mode (S) is disabled: supporting Ssnpm requires S.")
        valid)
      else
        (match (none : (Option xlenbits)) with
        | none => valid
        | .some inv_addr =>
          (let check_pmlen_7 : Bool :=
            (((true : Bool) && ((true : Bool) && (true : Bool))) || (((true : Bool) && (true : Bool)) || ((true : Bool) && (true : Bool))))
          let valid : Bool :=
            if (check_pmlen_7 : Bool)
            then
              (let .Virtaddr transformed_inv_addr := (pm_transform_PA (Virtaddr inv_addr) 7)
              if ((transformed_inv_addr != inv_addr) : Bool)
              then
                (let valid : Bool := false
                let _ : Unit :=
                  (print_endline
                    (HAppend.hAppend
                      "Pointer masking with PMLEN=7 is supported, but the specified `memory.invalid_physical_address` ("
                      (HAppend.hAppend (BitVec.toFormatted inv_addr)
                        (HAppend.hAppend
                          ") is not invariant under this pointer masking (pointer masked value is "
                          (HAppend.hAppend (BitVec.toFormatted transformed_inv_addr) ").")))))
                valid)
              else valid)
            else valid
          let check_pmlen_16 :=
            (((true : Bool) && ((true : Bool) && (true : Bool))) || (((true : Bool) && (true : Bool)) || ((true : Bool) && (true : Bool))))
          if (check_pmlen_16 : Bool)
          then
            (let .Virtaddr transformed_inv_addr := (pm_transform_PA (Virtaddr inv_addr) 16)
            if ((transformed_inv_addr != inv_addr) : Bool)
            then
              (let valid : Bool := false
              let _ : Unit :=
                (print_endline
                  (HAppend.hAppend
                    "Pointer masking with PMLEN=16 is supported, but the specified `memory.invalid_physical_address` ("
                    (HAppend.hAppend (BitVec.toFormatted inv_addr)
                      (HAppend.hAppend
                        ") is not invariant under this pointer masking (pointer masked value is "
                        (HAppend.hAppend (BitVec.toFormatted transformed_inv_addr) ").")))))
              valid)
            else valid)
          else valid)))
    else valid
  let valid : Bool :=
    if (((true : Bool) && (not (true : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Ssstrict extension is enabled but supervisor mode (S) is disabled: supporting Ssstrict requires S.")
      valid)
    else valid
  let valid : Bool :=
    if (((true : Bool) && (not (true : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Ssstateen extension is enabled but supervisor mode (S) is disabled: supporting Ssstateen requires S.")
      valid)
    else valid
  let valid ← (( do
    if ((false : Bool) : Bool)
    then
      (do
        let valid : Bool :=
          if ((not (true : Bool)) : Bool)
          then
            (let valid : Bool := false
            let _ : Unit :=
              (print_endline
                "The H extension is enabled but supervisor mode (S) is disabled: supporting H requires S.")
            valid)
          else valid
        if (valid : Bool)
        then (require_virtual_memory "H")
        else (pure false))
    else (pure valid) ) : SailM Bool )
  let valid : Bool :=
    if (sys_hgatp_sv32x4_supported : Bool)
    then
      (let valid : Bool := false
      let _ : Unit := (print_endline "Sv32x4 is enabled: Sv32x4 is not supported on RV64.")
      valid)
    else valid
  let valid : Bool :=
    if ((false : Bool) : Bool)
    then
      (let valid : Bool :=
        if ((not (false : Bool)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Shgatpa extension is enabled but the H extension is disabled: supporting Shgatpa requires H.")
          valid)
        else valid
      let valid : Bool :=
        (valid && (check_shgatpa_mode "Sv32" (false : Bool) sys_hgatp_sv32x4_supported))
      let valid : Bool :=
        (valid && (check_shgatpa_mode "Sv39" (true : Bool) sys_hgatp_sv39x4_supported))
      let valid : Bool :=
        (valid && (check_shgatpa_mode "Sv48" (true : Bool) sys_hgatp_sv48x4_supported))
      (valid && (check_shgatpa_mode "Sv57" (true : Bool) sys_hgatp_sv57x4_supported)))
    else valid
  let valid : Bool :=
    if ((false : Bool) : Bool)
    then
      (let valid : Bool :=
        if ((not (false : Bool)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Shtvala extension is enabled but the H extension is disabled: supporting Shtvala requires H.")
          valid)
        else valid
      if ((not sys_guest_page_fault_writes_htval) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The Shtvala extension is enabled but `extensions.H.guest_page_fault_writes_htval` is disabled: supporting Shtvala requires this option to be enabled.")
        valid)
      else valid)
    else valid
  let valid : Bool :=
    if ((false : Bool) : Bool)
    then
      (let valid : Bool :=
        if ((not (false : Bool)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Shvstvecd extension is enabled but the H extension is disabled: supporting Shvstvecd requires H.")
          valid)
        else valid
      if ((not (true : Bool)) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The Shvstvecd extension is enabled but `vstvec` does not support the `direct` mode (see `base.vstvec.direct.supported`).")
        valid)
      else valid)
    else valid
  let valid : Bool :=
    if ((false : Bool) : Bool)
    then
      (let valid : Bool :=
        if ((not (false : Bool)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Shvsatpa extension is enabled but the H extension is disabled: supporting Shvsatpa requires H.")
          valid)
        else valid
      let valid : Bool :=
        (valid && (check_shvsatpa_mode "Sv32" (false : Bool) sys_vsatp_sv32_supported))
      let valid : Bool :=
        (valid && (check_shvsatpa_mode "Sv39" (true : Bool) sys_vsatp_sv39_supported))
      let valid : Bool :=
        (valid && (check_shvsatpa_mode "Sv48" (true : Bool) sys_vsatp_sv48_supported))
      (valid && (check_shvsatpa_mode "Sv57" (true : Bool) sys_vsatp_sv57_supported)))
    else valid
  let valid : Bool :=
    if ((false : Bool) : Bool)
    then
      (let valid : Bool := (valid && (check_sha_dependency "H" (false : Bool)))
      let valid : Bool := (valid && (check_sha_dependency "Ssstateen" (true : Bool)))
      let valid : Bool := (valid && (check_sha_dependency "Shcounterenw" (false : Bool)))
      let valid : Bool := (valid && (check_sha_dependency "Shgatpa" (false : Bool)))
      let valid : Bool := (valid && (check_sha_dependency "Shtvala" (false : Bool)))
      let valid : Bool := (valid && (check_sha_dependency "Shvsatpa" (false : Bool)))
      let valid : Bool := (valid && (check_sha_dependency "Shvstvala" (false : Bool)))
      (valid && (check_sha_dependency "Shvstvecd" (false : Bool))))
    else valid
  let valid : Bool :=
    if (((false : Bool) && (not (true : Bool))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Ssdbltrp extension is enabled but S is disabled: supporting Ssdbltrp requires S.")
      valid)
    else valid
  if ((false : Bool) : Bool)
  then
    (let valid : Bool :=
      if (((true : Bool) && (not (false : Bool))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The `hcontext` CSR is supported but the H extension is not: `hcontext` requires H to be supported.")
        valid)
      else valid
    let valid : Bool :=
      if (((true : Bool) && (not (true : Bool))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The `hcontext` CSR is supported but the `mcontext` CSR is not: `hcontext` requires `mcontext` to be supported.")
        valid)
      else valid
    let valid : Bool :=
      if (((true : Bool) && ((((sail_mask 64
                 0b0000000000000000000000000000000000000000111111011011111111111111#64) : xlenbits) &&& (Sail.BitVec.extractLsb
                 (reserved_exception_mask ()) (xlen -i 1) 0)) != (zeros (n := 64)))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "Bits for reserved exceptions are set in `extensions.Sdtrig.etrigger.supported_exceptions`.")
        valid)
      else valid
    let reserved_interrupt_mask : xlenbits := (zero_extend (m := 64) 0xC111#16)
    let valid : Bool :=
      if (((true : Bool) && ((((sail_mask 64
                 0b0000000000000000000000000000000000000000000000000011111011101110#64) : xlenbits) &&& reserved_interrupt_mask) != (zeros
               (n := 64)))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "Bits for reserved interrupts are set in `extensions.Sdtrig.itrigger.supported_interrupts`.")
        valid)
      else valid
    let valid : Bool :=
      if (((Use_interrupt_enables : Sdtrig_breakpoint_reentrancy) == Use_tcontrol) : Bool)
      then
        (let medelegation :=
          (Mk_Medeleg 0b0000000000000000000000000000000000000000000011001011001111111111#64)
        if (((_get_Medeleg_Breakpoint medelegation) != 0#1) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "Bit 3 (Breakpoint) in `base.medeleg.delegatable_bits` is set, but `extensions.Sdtrig.breakpoint_reentrancy` is set to `Use_tcontrol`: `tcontrol`-based reentrancy control hardwires this bit to 0.")
          valid)
        else valid)
      else valid
    let valid : Bool :=
      if (((true : Bool) && (not (true : Bool))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "`extensions.Sdtrig.textra.mhselect.mcontext_match` is enabled but the `mcontext` CSR is not supported: mcontext matching requires `mcontext`.")
        valid)
      else valid
    let valid : Bool :=
      if (((true : Bool) && (not (false : Bool))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "`extensions.Sdtrig.textra.mhselect.vmid_match` is enabled but the H extension is not supported: VMID matching requires H.")
        valid)
      else valid
    let valid : Bool :=
      if (((true : Bool) && ((not (true : Bool)) || (not (true : Bool)))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "`extensions.Sdtrig.textra.sselect.scontext_match` is enabled but S or the `scontext` CSR is not supported: scontext matching requires both.")
        valid)
      else valid
    let valid : Bool :=
      if (((true : Bool) && (not (true : Bool))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "`extensions.Sdtrig.textra.sselect.asid_match` is enabled but the S extension is not supported: ASID matching requires S.")
        valid)
      else valid
    let mhvalue_max : Nat := 13
    let valid : Bool :=
      if ((sdtrig_mhvalue_len >b mhvalue_max) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            (HAppend.hAppend "`extensions.Sdtrig.textra.mhvalue_len` is "
              (HAppend.hAppend (Int.repr sdtrig_mhvalue_len)
                (HAppend.hAppend " but cannot be greater than "
                  (HAppend.hAppend (Int.repr mhvalue_max) (HAppend.hAppend " on " "RV64."))))))
        valid)
      else valid
    let svalue_max : Nat := 32
    let valid : Bool :=
      if ((sdtrig_svalue_len >b svalue_max) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            (HAppend.hAppend "`extensions.Sdtrig.textra.svalue_len` is "
              (HAppend.hAppend (Int.repr sdtrig_svalue_len)
                (HAppend.hAppend " but cannot be greater than "
                  (HAppend.hAppend (Int.repr svalue_max) (HAppend.hAppend " on " "RV64."))))))
        valid)
      else valid
    if ((true : Bool) : Bool)
    then
      (let maskmax : Nat := sdtrig_mcontrol6_maskmax
      let valid : Bool :=
        if (((maskmax ≤b 0) || (maskmax ≥b xlen)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              (HAppend.hAppend "`extensions.Sdtrig.mcontrol6.maskmax6` is set to "
                (HAppend.hAppend (Int.repr maskmax)
                  (HAppend.hAppend ", but needs to be between 1 and `xlen` - 1 ("
                    (HAppend.hAppend (Int.repr (xlen -i 1)) "), inclusive.")))))
          valid)
        else valid
      let max_chain_length := (4 : Nat)
      if ((max_chain_length >b num_triggers) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            (HAppend.hAppend "`extensions.Sdtrig.mcontrol6.max_chain_length` is set to "
              (HAppend.hAppend (Int.repr max_chain_length)
                (HAppend.hAppend " which exceeds the number of triggers ("
                  (HAppend.hAppend (Int.repr num_triggers) ".")))))
        (pure valid))
      else (pure valid))
    else (pure valid))
  else (pure valid)

def check_extension_param_constraints (_ : Unit) : Bool :=
  let valid : Bool := true
  let valid : Bool :=
    if (((true : Bool) && (plat_cache_block_size_exp != 6)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "The Zic64b extension is enabled but the cache block size is not 64 bytes.")
      valid)
    else valid
  let min_rss_exp := (log2_xlen -i 3)
  let valid : Bool :=
    if ((((true : Bool) || (false : Bool)) && (plat_reservation_set_size_exp <b min_rss_exp)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend
            "The A or Zalrsc extensions are enabled, but the reservation set size of 2^"
            (HAppend.hAppend (Int.repr plat_reservation_set_size_exp)
              (HAppend.hAppend " is too small; it should be at least 2^"
                (HAppend.hAppend (Int.repr min_rss_exp) " for the LR/SC operands on this platform.")))))
      valid)
    else valid
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then
      (let valid : Bool :=
        if ((misaligned_exception_is_access_fault
             ({ load_store := none
                vector := none
                amo := (some AccessFault)
                lrsc := (some AccessFault) } : GlobalMisalignedExceptions).load_store) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The Zicclsm extension is enabled, but misaligned scalar loads/stores raise access faults before address translation (as per `memory.misaligned.exceptions.load_store`); Zicclsm requires no exceptions or only misaligned exceptions for such accesses.")
          valid)
        else valid
      if ((misaligned_exception_is_access_fault
           ({ load_store := none
              vector := none
              amo := (some AccessFault)
              lrsc := (some AccessFault) } : GlobalMisalignedExceptions).vector) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The Zicclsm extension is enabled, but misaligned vector loads/stores raise access faults before address translation (as per `memory.misaligned.exceptions.vector`); Zicclsm requires no exceptions or only misaligned exceptions for such accesses.")
        valid)
      else valid)
    else valid
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then
      (let medelegation :=
        (Mk_Medeleg 0b0000000000000000000000000000000000000000000011001011001111111111#64)
      let valid : Bool :=
        if (((_get_Medeleg_Double_Trap medelegation) != 0#1) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "Bit 16 (Double Trap) in `base.medeleg.delegatable_bits` is set; Double Trap cannot be delegated.")
          valid)
        else valid
      let valid : Bool :=
        if (((_get_Medeleg_MEnvCall medelegation) != 0#1) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "Bit 11 (Environment call from M-mode) in `base.medeleg.delegatable_bits` is set; this environment call cannot be delegated.")
          valid)
        else valid
      let valid : Bool :=
        if ((((_get_Medeleg_Software_Check medelegation) != 0#1) && ((privileged_isa_version_lt
                 priv_isa_version Privileged_ISA_1_13) && ((not (true : Bool)) && (not (true : Bool))))) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "Bit 18 (Software Check) in `base.medeleg.delegatable_bits` is set, but the software-check exception requires privileged ISA version 1.13 or later, or Zicfilp or Zicfiss support.")
          valid)
        else valid
      let valid : Bool :=
        if ((((_get_Medeleg_Hardware_Error medelegation) != 0#1) && (privileged_isa_version_lt
               priv_isa_version Privileged_ISA_1_13)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "Bit 19 (Hardware Error) in `base.medeleg.delegatable_bits` is set, but the hardware-error exception requires privileged ISA version 1.13 or later.")
          valid)
        else valid
      let valid : Bool :=
        if (((medelegation &&& (reserved_exception_mask ())) != (zeros (n := 64))) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "Bits for reserved exceptions are set in `base.medeleg.delegatable_bits`.")
          valid)
        else valid
      let midelegation :=
        (Mk_Minterrupts
          (sail_mask 64 0b0000000000000000000000000000000000000000000000000010001000100010#64))
      let reserved_interrupt_mask : xlenbits := (zero_extend (m := 64) 0xD555#16)
      let valid : Bool :=
        if (((midelegation &&& reserved_interrupt_mask) != (zeros (n := 64))) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "Bits for reserved interrupts are set in `base.mideleg.delegatable_bits`.")
          valid)
        else valid
      if ((true : Bool) : Bool)
      then
        (if ((not (true : Bool)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "Supervisor timer interrupts are disabled in `extensions.S.interrupts.timer` but the Sstc extension is enabled: Sstc requires supervisor-mode timer interrupts to be supported.")
          valid)
        else valid)
      else valid)
    else valid
  let valid : Bool :=
    if ((false : Bool) : Bool)
    then
      (let geilen_nat : Nat := geilen
      let valid : Bool :=
        if ((geilen_nat >b (xlen -i 1)) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              (HAppend.hAppend "`extensions.H.geilen` is "
                (HAppend.hAppend (Int.repr geilen)
                  (HAppend.hAppend " but cannot be greater than "
                    (HAppend.hAppend (Int.repr (xlen -i 1))
                      (HAppend.hAppend " for RV" (HAppend.hAppend (Int.repr xlen) ".")))))))
          valid)
        else valid
      if ((mtval_is_readonly_zero ()) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The hypervisor extension (H) is enabled but `mtval` is read-only zero (`base.xtval_non_zero.*` are all false)): H requires that `mtval` cannot be read-only zero.")
        valid)
      else valid)
    else valid
  if ((not sys_enable_writable_fiom) : Bool)
  then
    (if (((xlen == 64) && (true : Bool)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "`base.writable_fiom` is false but Sv39 is supported: FIOM may only be read-only zero when satp.MODE is always Bare.")
      valid)
    else valid)
  else valid

/-- Type quantifiers: k_ex1173431_ : Bool -/
def check_stateen_bit_feature (name : String) (c : CSRBitConfig) (feature_supported : Bool) : Bool :=
  if (((bne c CSRBit_ReadOnlyZero) && (not feature_supported)) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "Stateen "
          (HAppend.hAppend name
            " is not read-only zero but the feature it controls is not supported: bits for unsupported features must be read-only zero.")))
    false)
  else true

def check_stateen_config (_ : Unit) : Bool :=
  if (((not (true : Bool)) && (not (true : Bool))) : Bool)
  then true
  else
    (let valid : Bool := true
    let valid : Bool :=
      if ((((mstateen0_se0 == CSRBit_ReadOnlyZero) || ((mstateen1_se1 == CSRBit_ReadOnlyZero) || ((mstateen2_se2 == CSRBit_ReadOnlyZero) || (mstateen3_se3 == CSRBit_ReadOnlyZero)))) && (hartSupports
             Ext_H)) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "Stateen bit 63 of mstateen0, mstateen1, mstateen2 or mstateen3 is read-only zero but H extension is supported: bit 63 must not be read-only zero when H is implemented.")
        valid)
      else valid
    let valid : Bool :=
      if (((mstateen0_se0 == CSRBit_ReadOnlyZero) && (((false : Bool) && ((bne sstateen0_fcsr
                   CSRBit_ReadOnlyZero) && (bne mstateen0_fcsr CSRBit_ReadOnlyZero))) || ((bne
                 sstateen0_c CSRBit_ReadOnlyZero) && (bne mstateen0_c CSRBit_ReadOnlyZero)))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "Stateen mstateen0.SE0 is read-only zero but sstateen0 is not all read-only zero: SE0 must not be read-only zero.")
        valid)
      else valid
    let valid : Bool :=
      if (((hartSupports Ext_Smstateen) && (((hstateen0_envcfg == CSRBit_ReadOnlyOne) && (bne
                 mstateen0_envcfg CSRBit_ReadOnlyOne)) || (((hstateen0_context == CSRBit_ReadOnlyOne) && (bne
                   mstateen0_context CSRBit_ReadOnlyOne)) || (((hstateen0_fcsr == CSRBit_ReadOnlyOne) && (bne
                     mstateen0_fcsr CSRBit_ReadOnlyOne)) || ((hstateen0_c == CSRBit_ReadOnlyOne) && (bne
                     mstateen0_c CSRBit_ReadOnlyOne)))))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "Stateen hstateen0 has a read-only one bit that is not read-only one in mstateen0.")
        valid)
      else valid
    let valid : Bool :=
      if ((((sstateen0_fcsr == CSRBit_ReadOnlyOne) && (((hartSupports Ext_Smstateen) && (bne
                   mstateen0_fcsr CSRBit_ReadOnlyOne)) || ((hartSupports Ext_H) && (bne
                   hstateen0_fcsr CSRBit_ReadOnlyOne)))) || ((sstateen0_c == CSRBit_ReadOnlyOne) && (((hartSupports
                   Ext_Smstateen) && (bne mstateen0_c CSRBit_ReadOnlyOne)) || ((hartSupports Ext_H) && (bne
                   hstateen0_c CSRBit_ReadOnlyOne))))) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "Stateen sstateen0 has a read-only one bit that is not read-only one in mstateen0 and hstateen0.")
        valid)
      else valid
    let valid : Bool :=
      if ((hartSupports Ext_Smstateen) : Bool)
      then
        (let valid : Bool :=
          ((check_stateen_bit_feature "mstateen0.ENVCFG" mstateen0_envcfg (hartSupports Ext_S)) && valid)
        let valid : Bool :=
          ((check_stateen_bit_feature "mstateen0.CONTEXT" mstateen0_context
              ((hartSupports Ext_Sdtrig) && (sdtrig_has_scontext || sdtrig_has_hcontext))) && valid)
        let valid : Bool :=
          ((check_stateen_bit_feature "mstateen0.P1P13" mstateen0_p1p13
              (delegh_csrs_are_defined && ((hartSupports Ext_H) && (xlen == 32)))) && valid)
        let valid : Bool :=
          ((check_stateen_bit_feature "mstateen0.SRMCFG" mstateen0_srmcfg (hartSupports Ext_Ssqosid)) && valid)
        ((check_stateen_bit_feature "mstateen0.FCSR" mstateen0_fcsr (hartSupports Ext_Zfinx)) && valid))
      else valid
    let valid : Bool :=
      if ((hartSupports Ext_H) : Bool)
      then
        (let valid : Bool :=
          ((check_stateen_bit_feature "hstateen0.CONTEXT" hstateen0_context
              ((hartSupports Ext_Sdtrig) && sdtrig_has_scontext)) && valid)
        ((check_stateen_bit_feature "hstateen0.FCSR" hstateen0_fcsr (hartSupports Ext_Zfinx)) && valid))
      else valid
    if ((hartSupports Ext_S) : Bool)
    then
      ((check_stateen_bit_feature "sstateen0.FCSR" sstateen0_fcsr (hartSupports Ext_Zfinx)) && valid)
    else valid)

def check_mmio_devices (_ : Unit) : SailM Bool := do
  let valid : Bool := true
  let valid : Bool :=
    if (((false : Bool) && ((Sail.BitVec.extractLsb plat_sig_base 1 0) != (zeros
             (n := ((1 -i 0) +i 1))))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "platform.simple_interrupt_generator.base is not 4-byte aligned.")
      valid)
    else valid
  let valid : Bool :=
    if ((true : Bool) : Bool)
    then
      (if ((not (true : Bool)) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "Zicntr is enabled but there is no source of time: a source of time (currently only `platform.clint.supported`) must be enabled.")
        valid)
      else valid)
    else valid
  let _ : Unit :=
    if ((true : Bool) : Bool)
    then
      (let hartid : Int := 0
      if ((hartid ≥b 4095) : Bool)
      then
        (print_endline
          (HAppend.hAppend "Warning: platform.hartid is "
            (HAppend.hAppend (Int.repr hartid)
              ", which is out-of-range for the CLINT, which serves harts 0 through 4094; the hart will not receive interrupts from the CLINT.")))
      else ())
    else ()
  (pure valid)

def check_mstatus_fields (_ : Unit) : Bool :=
  let valid : Bool := true
  let legal_fs : ExtContextPolicy := ExtContext_FourState
  let valid : Bool :=
    if ((false : Bool) : Bool)
    then
      (if ((bne legal_fs ExtContext_Off) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The Zfinx extension is enabled but `base.mstatus.fs_legal_states` is not set to `ExtContext_Off`: `mstatus.FS` needs to be read-only zero (i.e. `base.mstatus.fs_legal_states` should be set to `ExtContext_Off`).")
        valid)
      else valid)
    else
      (if ((false : Bool) : Bool)
      then
        (if ((legal_fs == ExtContext_Off) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              "The F extension is enabled but `base.mstatus.fs_legal_states` is set to `ExtContext_Off`, which makes `mstatus.FS` read-only zero: it cannot be read-only zero.")
          valid)
        else valid)
      else
        (if ((not (true : Bool)) : Bool)
        then
          (if ((bne legal_fs ExtContext_Off) : Bool)
          then
            (let valid : Bool := false
            let _ : Unit :=
              (print_endline
                "Both supervisor mode (S) and the F extension are not enabled, but `base.mstatus.fs_legal_states` is not set to `ExtContext_Off`; i.e. `mstatus.FS` is not read-only zero: it should be read-only zero.")
            valid)
          else valid)
        else valid))
  let legal_vs : ExtContextPolicy := ExtContext_FourState
  if ((vector_support_ge vector_support_level Integer) : Bool)
  then
    (if ((legal_vs == ExtContext_Off) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The vector registers are enabled but `base.mstatus.vs_legal_states` is set to `ExtContext_Off`, which makes `mstatus.VS` read-only zero: it cannot be read-only zero.")
      valid)
    else valid)
  else
    (if ((not (true : Bool)) : Bool)
    then
      (if ((bne legal_vs ExtContext_Off) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "Both supervisor mode (S) and the vector registers are not enabled, but `base.mstatus.vs_legal_states` is not set to `ExtContext_Off`; i.e. `mstatus.VS` is not read-only zero: it should be read-only zero.")
        valid)
      else valid)
    else valid)

def check_physaddr_bits (_ : Unit) : Bool :=
  let physaddr_bits_nat : Nat := physaddr_bits
  if ((physaddr_bits_nat >b 64) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "`memory.physaddr_bits` is "
          (HAppend.hAppend (Int.repr physaddr_bits) " but cannot be greater than 64.")))
    false)
  else
    (if ((physaddr_bits_nat <b 13) : Bool)
    then
      (let _ : Unit :=
        (print_endline
          (HAppend.hAppend "`memory.physaddr_bits` is "
            (HAppend.hAppend (Int.repr physaddr_bits)
              " but values smaller than 13 are not supported.")))
      false)
    else true)

def check_version_constraints (_ : Unit) : Bool :=
  let valid : Bool := true
  if (((sys_pmp_count >b 16) && (privileged_isa_version_lt priv_isa_version Privileged_ISA_1_12)) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit :=
      (print_endline
        (HAppend.hAppend
          "More than 16 PMP registers are specified, but the privileged ISA version is set to "
          (HAppend.hAppend (privileged_isa_version_name_forwards priv_isa_version)
            " which only allows 16 PMP registers.")))
    valid)
  else valid

def validate_event_selectors (_ : Unit) : Bool :=
  true

def check_platform_constraints (_ : Unit) : Bool :=
  (validate_event_selectors ())

def config_is_valid (_ : Unit) : SailM Bool := do
  if ((check_privs ()) : Bool)
  then
    (do
      if ((check_tvecs ()) : Bool)
      then
        (do
          if ((check_mutable_misa ()) : Bool)
          then
            (do
              if ((check_mstatus_fields ()) : Bool)
              then
                (do
                  if ((check_physaddr_bits ()) : Bool)
                  then
                    (do
                      if ((← (check_mmu_config ())) : Bool)
                      then
                        (do
                          if ((← (check_mem_layout ())) : Bool)
                          then
                            (do
                              if ((← (check_mmio_devices ())) : Bool)
                              then
                                (do
                                  if ((check_vlen_elen ()) : Bool)
                                  then
                                    (do
                                      if ((check_vext_config ()) : Bool)
                                      then
                                        (do
                                          if ((check_pmp ()) : Bool)
                                          then
                                            (pure ((← (check_misc_extension_dependencies ())) && ((check_extension_param_constraints
                                                    ()) && ((check_version_constraints ()) && ((check_platform_constraints
                                                        ()) && (check_stateen_config ()))))))
                                          else (pure false))
                                      else (pure false))
                                  else (pure false))
                              else (pure false))
                          else (pure false))
                      else (pure false))
                  else (pure false))
              else (pure false))
          else (pure false))
      else (pure false))
  else (pure false)

