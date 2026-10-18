import LeanRV64D.LeanRV64D
import LeanRV64D.Option
import LeanRV64D.Flow
import LeanRV64D.Prelude
import LeanRV64D.Errors
import LeanRV64D.Xlen
import LeanRV64D.Arithmetic
import LeanRV64D.PlatformConfig
import LeanRV64D.Callbacks
import LeanRV64D.SysRegs
import LeanRV64D.InterruptRegs
import LeanRV64D.SdtrigTypeUtils
import LeanRV64D.SdtrigTypes

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

def prevent_reentrance (act : Trig_Action) (priv : Privilege) : SailM Bool := do
  if ((bne act TA_Breakpoint) : Bool)
  then (pure false)
  else
    (do
      match sdtrig_breakpoint_reentrancy with
      | .Use_tcontrol =>
        (do
          if ((priv == Machine) : Bool)
          then (pure ((_get_TControl_mte (← readReg tcontrol)) == 0#1))
          else (pure false))
      | .Use_interrupt_enables =>
        (do
          match priv with
          | .Machine => (pure ((_get_Mstatus_MIE (← readReg mstatus)) == 0#1))
          | .Supervisor =>
            (do
              if (((_get_Medeleg_Breakpoint (← readReg medeleg)) == 1#1) : Bool)
              then (pure ((_get_Mstatus_SIE (← readReg mstatus)) == 0#1))
              else (pure false))
          | .VirtualSupervisor =>
            (do
              if (((_get_Medeleg_Breakpoint (← readReg medeleg)) == 1#1) : Bool)
              then
                (do
                  if (((_get_Medeleg_Breakpoint (← readReg hedeleg)) == 1#1) : Bool)
                  then (pure ((_get_Mstatus_SIE (← readReg vsstatus)) == 0#1))
                  else (pure false))
              else (pure false))
          | .VirtualUser => (pure false)
          | .User => (pure false))
      | .No_reentrancy_support => (pure false))

def sselect_match (t : TExtra) (priv : Privilege) : SailM Bool := do
  let ctx ← do (pure (_get_SContext_data (← readReg scontext)))
  match t.sselect with
  | 0b00 => (pure true)
  | 0b01 =>
    (pure ((((BitVec.access t.sbytemask 0) == 1#1) || ((Sail.BitVec.extractLsb ctx 7 0) == (Sail.BitVec.extractLsb
              t.svalue 7 0))) && ((((BitVec.access t.sbytemask 1) == 1#1) || ((Sail.BitVec.extractLsb
                ctx 15 8) == (Sail.BitVec.extractLsb t.svalue 15 8))) && (((xlen == 32) || (((BitVec.access
                    t.sbytemask 2) == 1#1) || ((Sail.BitVec.extractLsb ctx 23 16) == (Sail.BitVec.extractLsb
                    t.svalue 23 16)))) && ((xlen == 32) || (((BitVec.access t.sbytemask 3) == 1#1) || ((Sail.BitVec.extractLsb
                    ctx 31 24) == (Sail.BitVec.extractLsb t.svalue 31 24))))))))
  | 0b10 =>
    (pure ((← (get_asid
            (if ((privLevel_is_virtual priv) : Bool)
            then VS_Stage
            else S_Stage))) == (trunc (m := 16) t.svalue)))
  | _ => (pure true)

def mhselect_match (t : TExtra) : SailM Bool := do
  let ctx ← do (pure (_get_MContext_hcontext (← readReg mcontext)))
  let v := (t.mhvalue +++ (Sail.BitVec.extractLsb t.mhselect 2 2))
  match t.mhselect with
  | 0b000 => (pure true)
  | 0b001 => (pure (ctx == v))
  | 0b010 => (pure ((← (get_vmid VS_Stage)) == (trunc (m := 14) v)))
  | 0b100 => (pure ((Sail.BitVec.extractLsb ctx 12 0) == t.mhvalue))
  | 0b101 => (pure (ctx == v))
  | 0b110 => (pure ((← (get_vmid VS_Stage)) == (trunc (m := 14) v)))
  | _ => (pure true)

def textra_match (t : TExtra) (priv : Privilege) : SailM Bool := do
  if ((← (mhselect_match t)) : Bool)
  then (sselect_match t priv)
  else (pure false)

/-- Type quantifiers: k_ex1173082_ : Bool -/
def icount_match (t : ICount) (priv : Privilege) (reentrance : Bool) : SailM Bool := do
  if ((not ((t.action == TA_Breakpoint) && reentrance)) : Bool)
  then
    (pure ((← (textra_match t.textra priv)) && (match priv with
        | .Machine => t.m
        | .Supervisor => t.s
        | .User => t.u
        | .VirtualSupervisor => t.vs
        | .VirtualUser => t.vu : Bool)))
  else (pure false)

/-- Type quantifiers: k_ex1173083_ : Bool -/
def match_icount_triggers (priv : Privilege) (reentrance : Bool) : SailM Unit := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then (pure ())
  else
    (do
      let loop_i_lower := 0
      let loop_i_upper := (num_triggers -i 1)
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          match (GetElem?.getElem! (← readReg triggers) i) with
          | .T_icount t =>
            (do
              if ((← do
                   if (t.active : Bool)
                   then (icount_match t priv reentrance)
                   else (pure false)) : Bool)
              then
                (do
                  let set_pending ← (( do
                    match (← readReg written_trigger_index) with
                    | .some (idx, .TDATA1) => (pure ((idx != i) || icount_self_write_sets_pending))
                    | .some (_, _) => (pure true)
                    | none => (pure true) ) : SailM Bool )
                  let new_t : ICount :=
                    match (BitVec.toNatInt t.count) with
                    | 0 => t
                    | 1 =>
                      { t with count := if (icount_count_is_hardwired_one : Bool)
                        then t.count
                        else (zeros (n := 14)), pending := set_pending }
                    | _ => { t with count := (BitVec.subInt t.count 1) }
                  writeReg triggers (vectorUpdate (← readReg triggers) i (T_icount new_t))
                  let _ : Unit :=
                    if ((get_config_print_trigger ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "Matched icount trigger at index #"
                          (HAppend.hAppend (Int.repr i)
                            (HAppend.hAppend " with action " (trigger_action_name_forwards t.action)))))
                    else ()
                  (pure (trigger_match_callback i)))
              else (pure ()))
          | _ => (pure ())
      (pure loop_vars))

def itrigger_match (t : ITrigger) (intr : InterruptType) (from_priv : Privilege) (to_priv : Privilege) : SailM Bool := do
  let priv_match ← (( do
    if ((not (← (prevent_reentrance t.action to_priv))) : Bool)
    then
      (pure ((← (textra_match t.textra from_priv)) && (match from_priv with
          | .Machine => t.m
          | .Supervisor => t.s
          | .User => t.u
          | .VirtualSupervisor => t.vs
          | .VirtualUser => t.vu : Bool)))
    else (pure false) ) : SailM Bool )
  (pure (priv_match && ((t.tdata2 &&& (make_itrigger_flag intr)) != (zeros (n := 64)))))

def match_itrigger_triggers (intr : InterruptType) (from_priv : Privilege) (to_priv : Privilege) : SailM Unit := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then (pure ())
  else
    (do
      let loop_i_lower := 0
      let loop_i_upper := (num_triggers -i 1)
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          match (GetElem?.getElem! (← readReg triggers) i) with
          | .T_itrigger t =>
            (do
              if ((← (itrigger_match t intr from_priv to_priv)) : Bool)
              then
                (do
                  writeReg triggers (vectorUpdate (← readReg triggers) i
                    (T_itrigger { t with pending := true, hit := true }))
                  let _ : Unit :=
                    if ((get_config_print_trigger ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "Interrupt "
                          (HAppend.hAppend (interruptType_to_str intr)
                            (HAppend.hAppend " matched itrigger at index #"
                              (HAppend.hAppend (Int.repr i)
                                (HAppend.hAppend " with action "
                                  (trigger_action_name_forwards t.action)))))))
                    else ()
                  (pure (trigger_match_callback i)))
              else (pure ()))
          | _ => (pure ())
      (pure loop_vars))

def etrigger_match (t : ETrigger) (e : ExceptionType) (from_priv : Privilege) (to_priv : Privilege) : SailM Bool := do
  let priv_match ← (( do
    if ((not (← (prevent_reentrance t.action to_priv))) : Bool)
    then
      (pure ((← (textra_match t.textra from_priv)) && (match from_priv with
          | .Machine => t.m
          | .Supervisor => t.s
          | .User => t.u
          | .VirtualSupervisor => t.vs
          | .VirtualUser => t.vu : Bool)))
    else (pure false) ) : SailM Bool )
  (pure (priv_match && ((t.tdata2 &&& (make_etrigger_flag e)) != (zeros (n := 64)))))

def match_etrigger_triggers (exc : ExceptionType) (from_priv : Privilege) (to_priv : Privilege) : SailM Unit := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then (pure ())
  else
    (do
      let loop_i_lower := 0
      let loop_i_upper := (num_triggers -i 1)
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          match (GetElem?.getElem! (← readReg triggers) i) with
          | .T_etrigger t =>
            (do
              if ((← (etrigger_match t exc from_priv to_priv)) : Bool)
              then
                (do
                  writeReg triggers (vectorUpdate (← readReg triggers) i
                    (T_etrigger { t with pending := true, hit := true }))
                  let _ : Unit :=
                    if ((get_config_print_trigger ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "Exception "
                          (HAppend.hAppend (exceptionType_to_str exc)
                            (HAppend.hAppend " matched etrigger at index #"
                              (HAppend.hAppend (Int.repr i)
                                (HAppend.hAppend " with action "
                                  (trigger_action_name_forwards t.action)))))))
                    else ()
                  (pure (trigger_match_callback i)))
              else (pure ()))
          | _ => (pure ())
      (pure loop_vars))

/-- Type quantifiers: t_size : Nat, width : Nat, 0 < width ∧ width ≤ max_mem_access, List.elem
  t_size [0, 8, 16, 32, 48, 64, 128] -/
def compare_access_size (t_size : Nat) (width : Nat) : Bool :=
  ((t_size == 0) || (t_size == (8 *i width)))

def compare_value_napot (value : (BitVec 64)) (tdata2 : (BitVec 64)) : SailM Bool := do
  let lsz ← (( do
    match (least_significant_zero tdata2) with
    | none =>
      (internal_error "extensions/Sdtrig/sdtrig_control.sail" 192
        (HAppend.hAppend "Invalid tdata2 for NAPOT match: " (BitVec.toFormatted tdata2)))
    | .some i => (pure i) ) : SailM Nat )
  sail_assert (lsz <b sdtrig_mcontrol6_maskmax) "extensions/Sdtrig/sdtrig_control.sail:196.39-196.40"
  let M := ((xlen -i 1) -i lsz)
  sail_assert (M >b 0) "extensions/Sdtrig/sdtrig_control.sail:198.14-198.15"
  (pure ((Sail.BitVec.extractLsb value (xlen -i 1) (xlen -i M)) == (Sail.BitVec.extractLsb tdata2
        (xlen -i 1) (xlen -i M))))

def undefined_mask_type (_ : Unit) : SailM mask_type := do
  (internal_pick [MASK_LO, MASK_HI])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def mask_type_of_num (arg_ : Nat) : mask_type :=
  match arg_ with
  | 0 => MASK_LO
  | _ => MASK_HI

def num_of_mask_type (arg_ : mask_type) : Int :=
  match arg_ with
  | .MASK_LO => 0
  | .MASK_HI => 1

def compare_value_mask (value : (BitVec 64)) (tdata2 : (BitVec 64)) (mask_type : mask_type) : Bool :=
  let test_val :=
    if ((mask_type == MASK_LO) : Bool)
    then (Sail.BitVec.extractLsb value ((Int.tdiv xlen 2) -i 1) 0)
    else (Sail.BitVec.extractLsb value (xlen -i 1) (Int.tdiv xlen 2))
  let mask := (Sail.BitVec.extractLsb tdata2 (xlen -i 1) (Int.tdiv xlen 2))
  let check_val := (Sail.BitVec.extractLsb tdata2 ((Int.tdiv xlen 2) -i 1) 0)
  ((test_val &&& mask) == check_val)

def compare_value_xlen (t_match : Trig_Match) (value : (BitVec 64)) (tdata2 : (BitVec 64)) : SailM Bool := do
  match t_match with
  | .TM_EQ => (pure (value == tdata2))
  | .TM_NAPOT => (compare_value_napot value tdata2)
  | .TM_GE => (pure (zopz0zKzJ_u value tdata2))
  | .TM_LT => (pure (zopz0zI_u value tdata2))
  | .TM_MASK_LO => (pure (compare_value_mask value tdata2 MASK_LO))
  | .TM_MASK_HI => (pure (compare_value_mask value tdata2 MASK_HI))
  | .TM_NEQ => (pure (value != tdata2))
  | .TM_NOT_NAPOT => (pure (not (← (compare_value_napot value tdata2))))
  | .TM_NOT_MASK_LO => (pure (not (compare_value_mask value tdata2 MASK_LO)))
  | .TM_NOT_MASK_HI => (pure (not (compare_value_mask value tdata2 MASK_HI)))

def address_select_matches_all : Bool := true

/-- Type quantifiers: width : Nat, 0 < width ∧ width ≤ max_mem_access -/
def compare_address (t_match : Trig_Match) (addr : (BitVec 64)) (width : Nat) (tdata2 : (BitVec 64)) : SailM (Option (BitVec 64)) := SailME.run do
  let span :=
    if (address_select_matches_all : Bool)
    then (width -i 1)
    else 0
  let loop_i_lower := 0
  let loop_i_upper := span
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let match_addr := (BitVec.addInt addr i)
      if ((← (compare_value_xlen t_match match_addr tdata2)) : Bool)
      then SailME.throw ((some match_addr) : (Option (BitVec 64)))
      else (pure ())
  (pure loop_vars)
  (pure none)

/-- Type quantifiers: width : Nat, t_size : Nat, List.elem t_size [0, 8, 16, 32, 48, 64, 128], 1 ≤
  width ∧ width ≤ 16 -/
def compare_value (t_match : Trig_Match) (t_size : Nat) (value : (BitVec (8 * 16))) (width : Nat) (tdata2 : (BitVec 64)) : SailM Bool := do
  if (((width ≤b xlen_bytes) && (compare_access_size t_size width)) : Bool)
  then (compare_value_xlen t_match (Sail.BitVec.extractLsb value (xlen -i 1) 0) tdata2)
  else (pure false)

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ (16 - 1) -/
def match_mcontrol6 (idx : Nat) (t : MControl6) (priv : Privilege) (payload : MemoryTriggerPayload) : SailM (Option (BitVec 64)) := do
  let priv_match ← (( do
    if ((not (← (prevent_reentrance t.action priv))) : Bool)
    then
      (pure ((← (textra_match t.textra priv)) && (match priv with
          | .Machine => t.m
          | .Supervisor => t.s
          | .User => t.u
          | .VirtualSupervisor => t.vs
          | .VirtualUser => t.vu : Bool)))
    else (pure false) ) : SailM Bool )
  if ((not priv_match) : Bool)
  then (pure none)
  else
    (do
      let chain_info : String :=
        if (t.chain : Bool)
        then "in-chain"
        else "chain-terminating"
      match payload with
      | .TriggerFetchAddr addr =>
        (do
          if ((← do
               if (t.execute : Bool)
               then
                 (do
                   if ((t.select == Compare_Address) : Bool)
                   then
                     (do
                       if (((compare_access_size t.size 2) || (compare_access_size t.size 4)) : Bool)
                       then (compare_value_xlen t.t_match addr t.tdata2)
                       else (pure false))
                   else (pure false))
               else (pure false)) : Bool)
          then
            (let _ : Unit :=
              if ((get_config_print_trigger ()) : Bool)
              then
                (print_endline
                  (HAppend.hAppend "Matched "
                    (HAppend.hAppend chain_info
                      (HAppend.hAppend " memory execute address trigger at index #"
                        (HAppend.hAppend (Int.repr idx)
                          (HAppend.hAppend " with action " (trigger_action_name_forwards t.action)))))))
              else ()
            let _ : Unit := (trigger_match_callback idx)
            (pure (some addr)))
          else (pure none))
      | .TriggerFetchInstr (addr, inst, width) =>
        (do
          if ((← do
               if (t.execute : Bool)
               then
                 (do
                   if ((t.select == Compare_Data) : Bool)
                   then (compare_value t.t_match t.size inst width t.tdata2)
                   else (pure false))
               else (pure false)) : Bool)
          then
            (let _ : Unit :=
              if ((get_config_print_trigger ()) : Bool)
              then
                (print_endline
                  (HAppend.hAppend "Matched "
                    (HAppend.hAppend chain_info
                      (HAppend.hAppend " memory execute data trigger at index #"
                        (HAppend.hAppend (Int.repr idx)
                          (HAppend.hAppend " with action " (trigger_action_name_forwards t.action)))))))
              else ()
            let _ : Unit := (trigger_match_callback idx)
            (pure (some addr)))
          else (pure none))
      | .TriggerAddress (addr_type, addr, width) =>
        (do
          let addr_type_match : Bool :=
            match addr_type with
            | .TriggerAddress_Load => t.load
            | .TriggerAddress_Store => t.store
            | .TriggerAddress_AMO => (t.store || t.load)
          let size_match : Bool := (compare_access_size t.size width)
          if ((addr_type_match && (size_match && (t.select == Compare_Address))) : Bool)
          then
            (do
              let compare_result ← do (compare_address t.t_match addr width t.tdata2)
              let _ : Unit :=
                if ((is_some compare_result) : Bool)
                then
                  (let _ : Unit :=
                    if ((get_config_print_trigger ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "Matched "
                          (HAppend.hAppend chain_info
                            (HAppend.hAppend " memory address trigger at index #"
                              (HAppend.hAppend (Int.repr idx)
                                (HAppend.hAppend " with action "
                                  (trigger_action_name_forwards t.action)))))))
                    else ()
                  (trigger_match_callback idx))
                else ()
              (pure compare_result))
          else (pure none))
      | .TriggerStore (addr, data, width) =>
        (do
          if ((t.store && ((t.select == Compare_Address) && (compare_access_size t.size width))) : Bool)
          then
            (do
              let compare_result ← do (compare_address t.t_match addr width t.tdata2)
              let _ : Unit :=
                if ((is_some compare_result) : Bool)
                then
                  (let _ : Unit :=
                    if ((get_config_print_trigger ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "Matched "
                          (HAppend.hAppend chain_info
                            (HAppend.hAppend " memory store address trigger at index #"
                              (HAppend.hAppend (Int.repr idx)
                                (HAppend.hAppend " with action "
                                  (trigger_action_name_forwards t.action)))))))
                    else ()
                  (trigger_match_callback idx))
                else ()
              (pure compare_result))
          else
            (do
              if ((← do
                   if (t.store : Bool)
                   then
                     (do
                       if ((t.select == Compare_Data) : Bool)
                       then (compare_value t.t_match t.size data width t.tdata2)
                       else (pure false))
                   else (pure false)) : Bool)
              then
                (let _ : Unit :=
                  if ((get_config_print_trigger ()) : Bool)
                  then
                    (print_endline
                      (HAppend.hAppend "Matched "
                        (HAppend.hAppend chain_info
                          (HAppend.hAppend " memory store data trigger at index #"
                            (HAppend.hAppend (Int.repr idx)
                              (HAppend.hAppend " with action "
                                (trigger_action_name_forwards t.action)))))))
                  else ()
                let _ : Unit := (trigger_match_callback idx)
                (pure (some addr)))
              else (pure none)))
      | .TriggerLoadData (addr, data, width) =>
        (do
          if ((← do
               if (t.load : Bool)
               then
                 (do
                   if ((t.select == Compare_Data) : Bool)
                   then (compare_value t.t_match t.size data width t.tdata2)
                   else (pure false))
               else (pure false)) : Bool)
          then
            (let _ : Unit :=
              if ((get_config_print_trigger ()) : Bool)
              then
                (print_endline
                  (HAppend.hAppend "Matched "
                    (HAppend.hAppend chain_info
                      (HAppend.hAppend " memory load data trigger at index #"
                        (HAppend.hAppend (Int.repr idx)
                          (HAppend.hAppend " with action " (trigger_action_name_forwards t.action)))))))
              else ()
            let _ : Unit := (trigger_match_callback idx)
            (pure (some addr)))
          else (pure none))
      | .TriggerAMOData (addr, loaded, stored, width) =>
        (do
          if ((not ((t.load || t.store) && (t.select == Compare_Data))) : Bool)
          then (pure none)
          else
            (do
              let load_matched ← do
                if (t.load : Bool)
                then (compare_value t.t_match t.size loaded width t.tdata2)
                else (pure false)
              let store_matched ← do
                if (t.store : Bool)
                then (compare_value t.t_match t.size stored width t.tdata2)
                else (pure false)
              if ((load_matched || store_matched) : Bool)
              then
                (let _ : Unit :=
                  if ((get_config_print_trigger ()) : Bool)
                  then
                    (print_endline
                      (HAppend.hAppend "Matched "
                        (HAppend.hAppend chain_info
                          (HAppend.hAppend " memory data trigger at index #"
                            (HAppend.hAppend (Int.repr idx)
                              (HAppend.hAppend " with action "
                                (trigger_action_name_forwards t.action)))))))
                  else ()
                let _ : Unit := (trigger_match_callback idx)
                (pure (some addr)))
              else (pure none))))

def undefined_loop_chain_state (_ : Unit) : SailM loop_chain_state := do
  (internal_pick [NotInChain, InChainWithMatch, InChainWithoutMatch])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def loop_chain_state_of_num (arg_ : Nat) : loop_chain_state :=
  match arg_ with
  | 0 => NotInChain
  | 1 => InChainWithMatch
  | _ => InChainWithoutMatch

def num_of_loop_chain_state (arg_ : loop_chain_state) : Int :=
  match arg_ with
  | .NotInChain => 0
  | .InChainWithMatch => 1
  | .InChainWithoutMatch => 2

def loop_chain_state_name_forwards_matches (arg_ : loop_chain_state) : Bool :=
  match arg_ with
  | .NotInChain => true
  | .InChainWithMatch => true
  | .InChainWithoutMatch => true

def loop_chain_state_name_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "not-in-chain" => true
  | "in-chain-with-match" => true
  | "in-chain-without-match" => true
  | _ => false

def match_memory_triggers (priv : Privilege) (payload : MemoryTriggerPayload) (hit : Hit) : SailM (Option (Trig_Action × Nat × (BitVec 64))) := do
  sail_assert (num_triggers >b 0) "extensions/Sdtrig/sdtrig_control.sail:376.25-376.26"
  let chain_state ← (( do
    if ((trigger_is_in_chain (GetElem?.getElem! (← readReg triggers) 0)) : Bool)
    then (pure InChainWithMatch)
    else (pure NotInChain) ) : SailM loop_chain_state )
  let matched_info : (Option pending_trigger_info) := none
  let (chain_state, matched_info) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (num_triggers -i 1)
    let mut loop_vars := (chain_state, matched_info)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (chain_state, matched_info) := loop_vars
      loop_vars ← do
        let (chain_state, matched_info) ← (( do
          match (GetElem?.getElem! (← readReg triggers) i) with
          | .T_mcontrol6 t =>
            (do
              let match_result ← do
                if (((is_none t.match_info) && (bne chain_state InChainWithoutMatch)) : Bool)
                then
                  (do
                    match (← (match_mcontrol6 i t priv payload)) with
                    | none => (pure none)
                    | .some tval => (pure (some (tval, hit))))
                else (pure t.match_info)
              writeReg triggers (vectorUpdate (← readReg triggers) i
                (T_mcontrol6 { t with match_info := match_result }))
              let (chain_state, matched_info) ← (( do
                match chain_state with
                | .NotInChain =>
                  (let (chain_state, matched_info) : (loop_chain_state × (Option (Trig_Action × Nat × (BitVec 64)))) :=
                    if (t.chain : Bool)
                    then
                      (let chain_state : loop_chain_state :=
                        if ((is_some match_result) : Bool)
                        then InChainWithMatch
                        else InChainWithoutMatch
                      (chain_state, matched_info))
                    else
                      (let matched_info : (Option (Trig_Action × Nat × (BitVec 64))) :=
                        match match_result with
                        | none => matched_info
                        | .some (tval, _) => (some (t.action, i, tval))
                      (chain_state, matched_info))
                  (pure (chain_state, matched_info)))
                | .InChainWithoutMatch =>
                  (do
                    sail_assert (is_none match_result) "extensions/Sdtrig/sdtrig_control.sail:405.40-405.41"
                    let chain_state : loop_chain_state :=
                      if ((not t.chain) : Bool)
                      then NotInChain
                      else chain_state
                    (pure (chain_state, matched_info)))
                | .InChainWithMatch =>
                  (let (chain_state, matched_info) : (loop_chain_state × (Option (Trig_Action × Nat × (BitVec 64)))) :=
                    if (t.chain : Bool)
                    then
                      (let chain_state : loop_chain_state :=
                        if ((is_none match_result) : Bool)
                        then InChainWithoutMatch
                        else chain_state
                      (chain_state, matched_info))
                    else
                      (let chain_state : loop_chain_state := NotInChain
                      let matched_info : (Option (Trig_Action × Nat × (BitVec 64))) :=
                        match match_result with
                        | none => matched_info
                        | .some (tval, _) => (some (t.action, i, tval))
                      (chain_state, matched_info))
                  (pure (chain_state, matched_info))) ) : SailM
                (loop_chain_state × (Option (Trig_Action × Nat × (BitVec 64)))) )
              (pure (chain_state, matched_info)))
          | _ =>
            (let chain_state : loop_chain_state := NotInChain
            (pure (chain_state, matched_info))) ) : SailM
          (loop_chain_state × (Option (Trig_Action × Nat × (BitVec 64)))) )
        (pure (chain_state, matched_info))
    (pure loop_vars) ) : SailM (loop_chain_state × (Option (Trig_Action × Nat × (BitVec 64)))) )
  (pure matched_info)

def match_memory_trigger_before (priv : Privilege) (payload : MemoryTriggerPayload) : SailM (Option (Trig_Action × Nat × (BitVec 64))) := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then (pure none)
  else (match_memory_triggers priv payload Hit_before)

def match_memory_trigger_after (priv : Privilege) (payload : MemoryTriggerPayload) : SailM Unit := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then (pure ())
  else
    (do
      let _ ← do (match_memory_triggers priv payload Hit_imm_after)
      (pure ()))

def fire_pending_before_triggers (_pti : (Trig_Action × Nat × (BitVec 64))) : SailM Unit := do
  sail_assert (num_triggers >b 0) "extensions/Sdtrig/sdtrig_control.sail:454.25-454.26"
  let loop_i_lower := 0
  let loop_i_upper := (num_triggers -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let t ← do (pure (GetElem?.getElem! (← readReg triggers) i))
      match (GetElem?.getElem! (← readReg triggers) i) with
      | .T_mcontrol6 s =>
        (do
          match s.match_info with
          | none => (pure ())
          | .some (_, hit) =>
            (do
              let s :=
                if (((not s.chain) && (hit == Hit_before)) : Bool)
                then
                  (let _ : Unit :=
                    if ((get_config_print_trigger ()) : Bool)
                    then
                      (print_endline
                        (HAppend.hAppend "Fired "
                          (HAppend.hAppend (trigger_name t)
                            (HAppend.hAppend " at index #"
                              (HAppend.hAppend (Int.repr i)
                                (HAppend.hAppend " with action "
                                  (trigger_action_name_forwards s.action)))))))
                    else ()
                  let _ : Unit := (trigger_fire_callback i)
                  { s with hit := hit })
                else s
              writeReg triggers (vectorUpdate (← readReg triggers) i
                (T_mcontrol6 { s with match_info := none }))))
      | _ => (pure ())
  (pure loop_vars)

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ (16 - 1) -/
def fire_trigger_after (idx : Nat) : SailM Bool := do
  let (t, action, fired) ← (( do
    match (GetElem?.getElem! (← readReg triggers) idx) with
    | .T_icount t =>
      (let t :=
        if (icount_count_is_hardwired_one : Bool)
        then { t with m := false, s := false, u := false, vs := false, vu := false }
        else t
      (pure ((T_icount { t with pending := false, hit := true }), t.action, true)))
    | .T_itrigger t => (pure ((T_itrigger { t with pending := false }), t.action, true))
    | .T_etrigger t => (pure ((T_etrigger { t with pending := false }), t.action, true))
    | .T_mcontrol6 t =>
      (do
        match t.match_info with
        | .some (_, hit) =>
          (do
            sail_assert (t.chain || (hit == Hit_imm_after)) "extensions/Sdtrig/sdtrig_control.sail:498.45-498.46"
            let fire := (not t.chain)
            (pure ((T_mcontrol6
                { t with hit := if (fire : Bool)
                  then Hit_imm_after
                  else t.hit, match_info := none }), t.action, fire)))
        | none => (pure ((T_mcontrol6 t), t.action, false)))
    | .T_disabled _ =>
      (internal_error "extensions/Sdtrig/sdtrig_control.sail" 508 "Disabled triggers cannot fire.")
    ) : SailM (Trigger × Trig_Action × Bool) )
  writeReg triggers (vectorUpdate (← readReg triggers) idx t)
  let _ : Unit :=
    if (fired : Bool)
    then
      (let _ : Unit :=
        if ((get_config_print_trigger ()) : Bool)
        then
          (print_endline
            (HAppend.hAppend "Fired "
              (HAppend.hAppend (trigger_name t)
                (HAppend.hAppend " at index #"
                  (HAppend.hAppend (Int.repr idx)
                    (HAppend.hAppend " with action " (trigger_action_name_forwards action)))))))
        else ()
      (trigger_fire_callback idx))
    else ()
  (pure fired)

def find_highest_priority_pending_trigger (priv : Privilege) : SailM (Option (Trig_Action × Nat × (BitVec 64))) := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then (pure none)
  else
    (do
      sail_assert (num_triggers >b 0) "extensions/Sdtrig/sdtrig_control.sail:529.25-529.26"
      let found_pending : Bool := false
      let pending_index : trigger_index := 0
      let pending_action : Trig_Action := TA_Breakpoint
      let pending_tval : xlenbits := (zeros (n := 64))
      let (found_pending, pending_action, pending_index, pending_tval) ← (( do
        let loop_i_lower := 0
        let loop_i_upper := (num_triggers -i 1)
        let mut loop_vars := (found_pending, pending_action, pending_index, pending_tval)
        for i in [loop_i_lower:loop_i_upper:1]i do
          let (found_pending, pending_action, pending_index, pending_tval) := loop_vars
          loop_vars ← do
            let (found_pending, pending_action, pending_index, pending_tval) ← (( do
              match (GetElem?.getElem! (← readReg triggers) i) with
              | .T_disabled _ => (pure (found_pending, pending_action, pending_index, pending_tval))
              | .T_icount t =>
                (do
                  sail_assert (zopz0zJzJzK t.pending t.active) "extensions/Sdtrig/sdtrig_control.sail:551.37-551.38"
                  let (found_pending, pending_action, pending_index, pending_tval) ← (( do
                    if ((← do
                         if (t.pending : Bool)
                         then (icount_match t priv (← (prevent_reentrance TA_Breakpoint priv)))
                         else (pure false)) : Bool)
                    then
                      (do
                        let found_pending : Bool := true
                        let pending_index : trigger_index := i
                        let pending_action : Trig_Action := t.action
                        let pending_tval : (BitVec 64) :=
                          if ((pending_action == TA_Breakpoint) : Bool)
                          then (zeros (n := 64))
                          else pending_tval
                        let fired ← do (fire_trigger_after i)
                        sail_assert fired "extensions/Sdtrig/sdtrig_control.sail:559.22-559.23"
                        (pure (found_pending, pending_action, pending_index, pending_tval)))
                    else (pure (found_pending, pending_action, pending_index, pending_tval)) ) :
                    SailM (Bool × Trig_Action × Nat × (BitVec 64)) )
                  (pure (found_pending, pending_action, pending_index, pending_tval)))
              | .T_itrigger t =>
                (do
                  let (found_pending, pending_action, pending_index, pending_tval) ← (( do
                    if ((← do
                         if (t.pending : Bool)
                         then (pure (not (← (prevent_reentrance t.action priv))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let found_pending : Bool := true
                        let pending_index : trigger_index := i
                        let pending_action : Trig_Action := t.action
                        let pending_tval : (BitVec 64) :=
                          if ((pending_action == TA_Breakpoint) : Bool)
                          then (zeros (n := 64))
                          else pending_tval
                        let fired ← do (fire_trigger_after i)
                        sail_assert fired "extensions/Sdtrig/sdtrig_control.sail:569.22-569.23"
                        (pure (found_pending, pending_action, pending_index, pending_tval)))
                    else (pure (found_pending, pending_action, pending_index, pending_tval)) ) :
                    SailM (Bool × Trig_Action × Nat × (BitVec 64)) )
                  (pure (found_pending, pending_action, pending_index, pending_tval)))
              | .T_etrigger t =>
                (do
                  let (found_pending, pending_action, pending_index, pending_tval) ← (( do
                    if ((← do
                         if (t.pending : Bool)
                         then (pure (not (← (prevent_reentrance t.action priv))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let found_pending : Bool := true
                        let pending_index : trigger_index := i
                        let pending_action : Trig_Action := t.action
                        let pending_tval : (BitVec 64) :=
                          if ((pending_action == TA_Breakpoint) : Bool)
                          then (zeros (n := 64))
                          else pending_tval
                        let fired ← do (fire_trigger_after i)
                        sail_assert fired "extensions/Sdtrig/sdtrig_control.sail:578.22-578.23"
                        (pure (found_pending, pending_action, pending_index, pending_tval)))
                    else (pure (found_pending, pending_action, pending_index, pending_tval)) ) :
                    SailM (Bool × Trig_Action × Nat × (BitVec 64)) )
                  (pure (found_pending, pending_action, pending_index, pending_tval)))
              | .T_mcontrol6 t =>
                (do
                  let (found_pending, pending_action, pending_index, pending_tval) ← (( do
                    match t.match_info with
                    | .some (tval, _) =>
                      (do
                        sail_assert (not (← (prevent_reentrance t.action priv))) "extensions/Sdtrig/sdtrig_control.sail:589.58-589.59"
                        let fired ← do (fire_trigger_after i)
                        let (found_pending, pending_action, pending_index, pending_tval) : (Bool × Trig_Action × Nat × (BitVec 64)) :=
                          if (fired : Bool)
                          then
                            (let found_pending : Bool := true
                            let pending_index : trigger_index := i
                            let pending_action : Trig_Action := t.action
                            let pending_tval : (BitVec 64) :=
                              if ((pending_action == TA_Breakpoint) : Bool)
                              then tval
                              else pending_tval
                            (found_pending, pending_action, pending_index, pending_tval))
                          else (found_pending, pending_action, pending_index, pending_tval)
                        (pure (found_pending, pending_action, pending_index, pending_tval)))
                    | none => (pure (found_pending, pending_action, pending_index, pending_tval)) )
                    : SailM (Bool × Trig_Action × Nat × (BitVec 64)) )
                  (pure (found_pending, pending_action, pending_index, pending_tval))) ) : SailM
              (Bool × Trig_Action × Nat × (BitVec 64)) )
            (pure (found_pending, pending_action, pending_index, pending_tval))
        (pure loop_vars) ) : SailM (Bool × Trig_Action × Nat × (BitVec 64)) )
      if (found_pending : Bool)
      then (pure (some (pending_action, pending_index, pending_tval)))
      else (pure none))

def new_chain_state (s : MControl6) : SailM loop_chain_state := do
  sail_assert (not s.chain) "extensions/Sdtrig/sdtrig_control.sail:614.21-614.22"
  if ((is_some s.match_info) : Bool)
  then (pure InChainWithMatch)
  else (pure InChainWithoutMatch)

def update_triggers (_ : Unit) : SailM Unit := do
  if ((not (← (currentlyEnabled Ext_Sdtrig))) : Bool)
  then
    (do
      sail_assert (is_none (← readReg written_trigger_index)) "extensions/Sdtrig/sdtrig_control.sail:620.41-620.42")
  else
    (do
      match (← readReg written_trigger_index) with
      | none => (pure ())
      | .some (idx, .TDATA1) =>
        (do
          match (GetElem?.getElem! (← readReg triggers) idx) with
          | .T_icount t =>
            (do
              match t.new_count with
              | .some c =>
                writeReg triggers (vectorUpdate (← readReg triggers) idx
                  (T_icount { t with count := c, new_count := none, active := true }))
              | none => sail_assert t.active "extensions/Sdtrig/sdtrig_control.sail:630.36-630.37")
          | _ => (pure ())
          writeReg written_trigger_index none)
      | .some _ => writeReg written_trigger_index none
      sail_assert (num_triggers >b 0) "extensions/Sdtrig/sdtrig_control.sail:643.25-643.26"
      let chain_state ← (( do
        match (GetElem?.getElem! (← readReg triggers) (num_triggers -i 1)) with
        | .T_mcontrol6 s =>
          (do
            if (s.chain : Bool)
            then (pure InChainWithoutMatch)
            else (new_chain_state s))
        | _ => (pure NotInChain) ) : SailM loop_chain_state )
      let chain_state ← (( do
        let loop_i_lower := 0
        let loop_i_upper := (num_triggers -i 1)
        let mut loop_vars := chain_state
        for i in [loop_i_upper:loop_i_lower:-1]i do
          let chain_state := loop_vars
          loop_vars ← do
            match (GetElem?.getElem! (← readReg triggers) i) with
            | .T_mcontrol6 s =>
              (do
                match chain_state with
                | .InChainWithoutMatch =>
                  (do
                    if (s.chain : Bool)
                    then
                      (do
                        writeReg triggers (vectorUpdate (← readReg triggers) i
                          (T_mcontrol6 { s with match_info := none }))
                        (pure chain_state))
                    else
                      (do
                        (new_chain_state s)))
                | .InChainWithMatch =>
                  (do
                    if (s.chain : Bool)
                    then
                      (do
                        sail_assert (is_some s.match_info) "extensions/Sdtrig/sdtrig_control.sail:658.61-658.62"
                        (pure chain_state))
                    else
                      (do
                        (new_chain_state s)))
                | .NotInChain =>
                  (do
                    if (s.chain : Bool)
                    then
                      (do
                        writeReg triggers (vectorUpdate (← readReg triggers) i
                          (T_mcontrol6 { s with match_info := none }))
                        (pure InChainWithoutMatch))
                    else
                      (do
                        (new_chain_state s))))
            | _ => (pure NotInChain)
        (pure loop_vars) ) : SailM loop_chain_state )
      (pure ()))

