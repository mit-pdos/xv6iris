import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ArchSem

noncomputable section
namespace LeanRV64D

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

abbrev bit := (BitVec 1)

inductive AtomicSupport where | AMONone | AMOSwap | AMOLogical | AMOArithmetic | AMOCASW | AMOCASD | AMOCASQ
  deriving BEq, Inhabited, Repr
  open AtomicSupport

inductive Privileged_ISA_Version where | Privileged_ISA_1_11 | Privileged_ISA_1_12 | Privileged_ISA_1_13
  deriving BEq, Inhabited, Repr
  open Privileged_ISA_Version

inductive vector_support where | Disabled | Integer | Float_single | Float_double | Full
  deriving BEq, Inhabited, Repr
  open vector_support

abbrev bits k_n := (BitVec k_n)

inductive regidx where
  | Regidx (_ : (BitVec (if ( false  : Bool) then 4 else 5)))
  deriving Inhabited, BEq, Repr
  open regidx

abbrev base_E_enabled  : Bool := false

abbrev regidx_bit_width  : Int := (if ( base_E_enabled  : Bool) then 4 else 5)

inductive vregidx where
  | Vregidx (_ : (BitVec 5))
  deriving Inhabited, BEq, Repr
  open vregidx

abbrev physaddrbits := (BitVec 64)

inductive physaddr where
  | Physaddr (_ : physaddrbits)
  deriving Inhabited, BEq, Repr
  open physaddr

abbrev xlenbits := (BitVec 64)

inductive virtaddr where
  | Virtaddr (_ : xlenbits)
  deriving Inhabited, BEq, Repr
  open virtaddr

abbrev fp_exception_flags := (BitVec 5)

abbrev fp_rounding_modes := (BitVec 5)

abbrev is_fp_bits (k_n : Int) : Bool := List.elem k_n [16, 32, 64, 128]

-- Abbreviation fp_bits skipped

/-- Type quantifiers: k_n : Int -/
structure float_bits (k_n : Int) where
  sign : (BitVec 1)
  exp :
  (BitVec (if ( k_n = 16  : Bool) then 5 else (if ( k_n = 32  : Bool) then 8 else (if ( k_n = 64  : Bool) then 11 else 15))))
  mantissa :
  (BitVec (if ( k_n = 16  : Bool) then 10 else (if ( k_n = 32  : Bool) then 23 else (if ( k_n = 64  : Bool) then 52 else 112))))
  deriving BEq, Inhabited, Repr

inductive float_class where | float_class_negative_inf | float_class_negative_normal | float_class_negative_subnormal | float_class_negative_zero | float_class_positive_zero | float_class_positive_subnormal | float_class_positive_normal | float_class_positive_inf | float_class_snan | float_class_qnan
  deriving BEq, Inhabited, Repr
  open float_class

abbrev nat1 := Int

inductive Signedness where | Signed | Unsigned
  deriving BEq, Inhabited, Repr
  open Signedness

inductive VectorHalf where | High | Low
  deriving BEq, Inhabited, Repr
  open VectorHalf

abbrev max_mem_access  : Int := 4096

abbrev mem_access_width := Nat

inductive exception where
  | Error_not_implemented (_ : String)
  | Error_internal_error (_ : String)
  | Error_reserved_behavior (_ : String)
  deriving Inhabited, BEq, Repr
  open exception

inductive amoop where | AMOSWAP | AMOAND | AMOOR | AMOXOR | AMOADD | AMOMIN | AMOMAX | AMOMINU | AMOMAXU | AMOCAS
  deriving BEq, Inhabited, Repr
  open amoop

inductive cbop_zicbom where | CBO_CLEAN | CBO_FLUSH | CBO_INVAL
  deriving BEq, Inhabited, Repr
  open cbop_zicbom

inductive cbop_zicbop where | PREFETCH_I | PREFETCH_R | PREFETCH_W
  deriving BEq, Inhabited, Repr
  open cbop_zicbop

abbrev pm_len := Int

inductive PM_Ext where | PM_SSNPM | PM_SMNPM | PM_SMMPM
  deriving BEq, Inhabited, Repr
  open PM_Ext

inductive PointerMaskingMode where | PMM_Disabled | PMM_Reserved | PMM_PMLEN_7 | PMM_PMLEN_16
  deriving BEq, Inhabited, Repr
  open PointerMaskingMode

abbrev xlen  : Int := 64

abbrev sdtrig_mcontrol6_maskmax  : Int := 63

abbrev physaddr_bits  : Int := 56

abbrev geilen  : Int := 63

abbrev log2_xlen  : Int := (if ( xlen = 32  : Bool) then 5 else 6)

abbrev xlen_bytes  : Int := (if ( xlen = 32  : Bool) then 4 else 8)

abbrev physaddrbits_len  : Int := (if ( xlen = 32  : Bool) then 34 else 64)

abbrev gpalen  : Int := (if ( xlen = 32  : Bool) then 34 else 64)

abbrev asidmax  : Int := (if ( xlen = 32  : Bool) then 9 else 16)

abbrev asidlen  : Int := 16

abbrev vmidmax  : Int := (if ( xlen = 32  : Bool) then 7 else 14)

abbrev vmidlen  : Int := 14

abbrev gpabits := (BitVec 64)

abbrev asidbits := (BitVec 16)

abbrev vmidbits := (BitVec 14)

abbrev ext_d_supported  : Bool := true

abbrev flen_bytes  : Int := (if ( ext_d_supported  : Bool) then 8 else 4)

abbrev flen  : Int := ((if ( true  : Bool) then 8 else 4) * 8)

abbrev flenbits := (BitVec ((if ( true  : Bool) then 8 else 4) * 8))

abbrev vlen_exp  : Int := 8

abbrev elen_exp  : Int := 6

abbrev vlen  : Int := (2 ^ 8)

abbrev elen  : Int := (2 ^ 6)

abbrev mem_meta := Unit

abbrev RVFI_DII_Instruction_Packet := (BitVec 64)

abbrev RVFI_DII_Execution_Packet_InstMetaData := (BitVec 192)

abbrev RVFI_DII_Execution_Packet_PC := (BitVec 128)

abbrev RVFI_DII_Execution_Packet_Ext_Integer := (BitVec 320)

abbrev RVFI_DII_Execution_Packet_Ext_MemAccess := (BitVec 704)

abbrev RVFI_DII_Execution_Packet_V1 := (BitVec 704)

abbrev RVFI_DII_Execution_PacketV2 := (BitVec 512)

abbrev tvec_alignment := Nat

inductive misaligned_exception where | AccessFault | AlignmentException
  deriving BEq, Inhabited, Repr
  open misaligned_exception

inductive mem_payload where | Data | Vector | PageTableEntry | ShadowStack
  deriving BEq, Inhabited, Repr
  open mem_payload

inductive cacheop where
  | CB_manage (_ : cbop_zicbom)
  | CB_zero (_ : Unit)
  | CB_prefetch (_ : cbop_zicbop)
  deriving Inhabited, BEq, Repr
  open cacheop

/-- Type quantifiers: k_a : Type -/
inductive MemoryAccessType (k_a : Type) where
  | Load (_ : k_a)
  | Store (_ : k_a)
  | LoadReserved (_ : (Bool × Bool × k_a))
  | LoadExecute (_ : k_a)
  | StoreConditional (_ : (Bool × Bool × k_a))
  | Atomic (_ : (amoop × Bool × Bool × k_a × k_a))
  | InstructionFetch (_ : Unit)
  | CacheAccess (_ : cacheop)
  deriving Inhabited, BEq, Repr
  open MemoryAccessType

abbrev csreg := (BitVec 12)

abbrev ext_exc_type := Unit

inductive breakpoint_cause where | Brk_Software | Brk_Hardware
  deriving BEq, Inhabited, Repr
  open breakpoint_cause

inductive ExceptionType where
  | E_Fetch_Addr_Align (_ : Unit)
  | E_Fetch_Access_Fault (_ : Unit)
  | E_Illegal_Instr (_ : Unit)
  | E_Breakpoint (_ : breakpoint_cause)
  | E_Load_Addr_Align (_ : Unit)
  | E_Load_Access_Fault (_ : Unit)
  | E_SAMO_Addr_Align (_ : Unit)
  | E_SAMO_Access_Fault (_ : Unit)
  | E_U_EnvCall (_ : Unit)
  | E_S_EnvCall (_ : Unit)
  | E_VS_EnvCall (_ : Unit)
  | E_M_EnvCall (_ : Unit)
  | E_Fetch_Page_Fault (_ : Unit)
  | E_Load_Page_Fault (_ : Unit)
  | E_Reserved_14 (_ : Unit)
  | E_SAMO_Page_Fault (_ : Unit)
  | E_Double_Trap (_ : Unit)
  | E_Reserved_17 (_ : Unit)
  | E_Software_Check (_ : Unit)
  | E_Hardware_Error (_ : Unit)
  | E_Fetch_GPage_Fault (_ : Unit)
  | E_Load_GPage_Fault (_ : Unit)
  | E_Virtual_Instr (_ : Unit)
  | E_SAMO_GPage_Fault (_ : Unit)
  | E_Extension (_ : ext_exc_type)
  deriving Inhabited, BEq, Repr
  open ExceptionType

inductive bop where | BEQ | BNE | BLT | BGE | BLTU | BGEU
  deriving BEq, Inhabited, Repr
  open bop

inductive cregidx where
  | Cregidx (_ : (BitVec 3))
  deriving Inhabited, BEq, Repr
  open cregidx

inductive csrop where | CSRRW | CSRRS | CSRRC
  deriving BEq, Inhabited, Repr
  open csrop

inductive iop where | ADDI | SLTI | SLTIU | XORI | ORI | ANDI
  deriving BEq, Inhabited, Repr
  open iop

inductive hlvop where | HLV | HLVX
  deriving BEq, Inhabited, Repr
  open hlvop

structure mul_op where
  result_part : VectorHalf
  signed_rs1 : Signedness
  signed_rs2 : Signedness
  deriving BEq, Inhabited, Repr

inductive ntl_type where | NTL_P1 | NTL_PALL | NTL_S1 | NTL_ALL
  deriving BEq, Inhabited, Repr
  open ntl_type

inductive rop where | ADD | SUB | SLL | SLT | SLTU | XOR | SRL | SRA | OR | AND
  deriving BEq, Inhabited, Repr
  open rop

inductive ropw where | ADDW | SUBW | SLLW | SRLW | SRAW
  deriving BEq, Inhabited, Repr
  open ropw

inductive sop where | SLLI | SRLI | SRAI
  deriving BEq, Inhabited, Repr
  open sop

inductive sopw where | SLLIW | SRLIW | SRAIW
  deriving BEq, Inhabited, Repr
  open sopw

inductive uop where | LUI | AUIPC
  deriving BEq, Inhabited, Repr
  open uop

inductive extop_zbb where | SEXTB | SEXTH | ZEXTH
  deriving BEq, Inhabited, Repr
  open extop_zbb

inductive brop_zbb where | ANDN | ORN | XNOR | MAX | MAXU | MIN | MINU | ROL | ROR
  deriving BEq, Inhabited, Repr
  open brop_zbb

inductive bropw_zbb where | ROLW | RORW
  deriving BEq, Inhabited, Repr
  open bropw_zbb

inductive biop_zbs where | BCLRI | BEXTI | BINVI | BSETI
  deriving BEq, Inhabited, Repr
  open biop_zbs

inductive brop_zbs where | BCLR | BEXT | BINV | BSET
  deriving BEq, Inhabited, Repr
  open brop_zbs

inductive zicondop where | CZERO_EQZ | CZERO_NEZ
  deriving BEq, Inhabited, Repr
  open zicondop

abbrev half := (BitVec 16)

abbrev landing_pad_label := (BitVec 20)

abbrev shamt_zba := (BitVec 2)

abbrev word := (BitVec 32)

abbrev word_width := Int

abbrev word_width_wide := Int

inductive wrsop where | WRS_STO | WRS_NTO
  deriving BEq, Inhabited, Repr
  open wrsop

inductive instruction where
  | ILLEGAL (_ : word)
  | C_ILLEGAL (_ : half)
  | ZICBOP (_ : (cbop_zicbop × regidx × (BitVec 12)))
  | NTL (_ : ntl_type)
  | C_NTL (_ : ntl_type)
  | PAUSE (_ : Unit)
  | LPAD (_ : landing_pad_label)
  | UTYPE (_ : ((BitVec 20) × regidx × uop))
  | JAL (_ : ((BitVec 21) × regidx))
  | JALR (_ : ((BitVec 12) × regidx × regidx))
  | BTYPE (_ : ((BitVec 13) × regidx × regidx × bop))
  | ITYPE (_ : ((BitVec 12) × regidx × regidx × iop))
  | SHIFTIOP (_ : ((BitVec 6) × regidx × regidx × sop))
  | RTYPE (_ : (regidx × regidx × regidx × rop))
  | LOAD (_ : ((BitVec 12) × regidx × regidx × Bool × word_width))
  | STORE (_ : ((BitVec 12) × regidx × regidx × word_width))
  | ADDIW (_ : ((BitVec 12) × regidx × regidx))
  | RTYPEW (_ : (regidx × regidx × regidx × ropw))
  | SHIFTIWOP (_ : ((BitVec 5) × regidx × regidx × sopw))
  | FENCE_TSO (_ : Unit)
  | FENCE (_ : ((BitVec 4) × (BitVec 4) × (BitVec 4) × regidx × regidx))
  | ECALL (_ : Unit)
  | MRET (_ : Unit)
  | SRET (_ : Unit)
  | EBREAK (_ : Unit)
  | WFI (_ : Unit)
  | SFENCE_VMA (_ : (regidx × regidx))
  | AMO (_ : (amoop × Bool × Bool × regidx × regidx × word_width_wide × regidx))
  | LOADRES (_ : (Bool × Bool × regidx × word_width × regidx))
  | STORECON (_ : (Bool × Bool × regidx × regidx × word_width × regidx))
  | MUL (_ : (regidx × regidx × regidx × mul_op))
  | DIV (_ : (regidx × regidx × regidx × Bool))
  | REM (_ : (regidx × regidx × regidx × Bool))
  | MULW (_ : (regidx × regidx × regidx))
  | DIVW (_ : (regidx × regidx × regidx × Bool))
  | REMW (_ : (regidx × regidx × regidx × Bool))
  | SLLIUW (_ : ((BitVec 6) × regidx × regidx))
  | ZBA_RTYPEUW (_ : (regidx × regidx × regidx × shamt_zba))
  | ZBA_RTYPE (_ : (regidx × regidx × regidx × shamt_zba))
  | RORIW (_ : ((BitVec 5) × regidx × regidx))
  | RORI (_ : ((BitVec 6) × regidx × regidx))
  | ZBB_RTYPEW (_ : (regidx × regidx × regidx × bropw_zbb))
  | ZBB_RTYPE (_ : (regidx × regidx × regidx × brop_zbb))
  | ZBB_EXTOP (_ : (regidx × regidx × extop_zbb))
  | REV8 (_ : (regidx × regidx))
  | ORCB (_ : (regidx × regidx))
  | CPOP (_ : (regidx × regidx))
  | CPOPW (_ : (regidx × regidx))
  | CLZ (_ : (regidx × regidx))
  | CLZW (_ : (regidx × regidx))
  | CTZ (_ : (regidx × regidx))
  | CTZW (_ : (regidx × regidx))
  | CLMUL (_ : (regidx × regidx × regidx))
  | CLMULH (_ : (regidx × regidx × regidx))
  | CLMULR (_ : (regidx × regidx × regidx))
  | ZBS_IOP (_ : ((BitVec 6) × regidx × regidx × biop_zbs))
  | ZBS_RTYPE (_ : (regidx × regidx × regidx × brop_zbs))
  | C_NOP (_ : (BitVec 6))
  | C_ADDI4SPN (_ : (cregidx × (BitVec 8)))
  | C_LW (_ : ((BitVec 5) × cregidx × cregidx))
  | C_LD (_ : ((BitVec 5) × cregidx × cregidx))
  | C_SW (_ : ((BitVec 5) × cregidx × cregidx))
  | C_SD (_ : ((BitVec 5) × cregidx × cregidx))
  | C_ADDI (_ : ((BitVec 6) × regidx))
  | C_JAL (_ : (BitVec 11))
  | C_ADDIW (_ : ((BitVec 6) × regidx))
  | C_LI (_ : ((BitVec 6) × regidx))
  | C_ADDI16SP (_ : (BitVec 6))
  | C_LUI (_ : ((BitVec 6) × regidx))
  | C_SRLI (_ : ((BitVec 6) × cregidx))
  | C_SRAI (_ : ((BitVec 6) × cregidx))
  | C_ANDI (_ : ((BitVec 6) × cregidx))
  | C_SUB (_ : (cregidx × cregidx))
  | C_XOR (_ : (cregidx × cregidx))
  | C_OR (_ : (cregidx × cregidx))
  | C_AND (_ : (cregidx × cregidx))
  | C_SUBW (_ : (cregidx × cregidx))
  | C_ADDW (_ : (cregidx × cregidx))
  | C_J (_ : (BitVec 11))
  | C_BEQZ (_ : ((BitVec 8) × cregidx))
  | C_BNEZ (_ : ((BitVec 8) × cregidx))
  | C_SLLI (_ : ((BitVec 6) × regidx))
  | C_LWSP (_ : ((BitVec 6) × regidx))
  | C_LDSP (_ : ((BitVec 6) × regidx))
  | C_SWSP (_ : ((BitVec 6) × regidx))
  | C_SDSP (_ : ((BitVec 6) × regidx))
  | C_JR (_ : regidx)
  | C_JALR (_ : regidx)
  | C_MV (_ : (regidx × regidx))
  | C_EBREAK (_ : Unit)
  | C_ADD (_ : (regidx × regidx))
  | C_LBU (_ : ((BitVec 2) × cregidx × cregidx))
  | C_LHU (_ : ((BitVec 2) × cregidx × cregidx))
  | C_LH (_ : ((BitVec 2) × cregidx × cregidx))
  | C_SB (_ : ((BitVec 2) × cregidx × cregidx))
  | C_SH (_ : ((BitVec 2) × cregidx × cregidx))
  | C_ZEXT_B (_ : cregidx)
  | C_SEXT_B (_ : cregidx)
  | C_ZEXT_H (_ : cregidx)
  | C_SEXT_H (_ : cregidx)
  | C_ZEXT_W (_ : cregidx)
  | C_NOT (_ : cregidx)
  | C_MUL (_ : (cregidx × cregidx))
  | HLVTYPE (_ : (word_width × hlvop × Bool × regidx × regidx))
  | HSV (_ : (word_width × regidx × regidx))
  | HFENCE_VVMA (_ : (regidx × regidx))
  | HFENCE_GVMA (_ : (regidx × regidx))
  | CSRReg (_ : (csreg × regidx × regidx × csrop))
  | CSRImm (_ : (csreg × (BitVec 5) × regidx × csrop))
  | SINVAL_VMA (_ : (regidx × regidx))
  | SFENCE_W_INVAL (_ : Unit)
  | SFENCE_INVAL_IR (_ : Unit)
  | HINVAL_VVMA (_ : (regidx × regidx))
  | HINVAL_GVMA (_ : (regidx × regidx))
  | WRS (_ : wrsop)
  | SSPUSH (_ : regidx)
  | C_SSPUSH (_ : Unit)
  | SSPOPCHK (_ : regidx)
  | C_SSPOPCHK (_ : Unit)
  | SSRDP (_ : regidx)
  | SSAMOSWAP (_ : (Bool × Bool × regidx × regidx × word_width × regidx))
  | ZICOND_RTYPE (_ : (regidx × regidx × regidx × zicondop))
  | ZICBOM (_ : (cbop_zicbom × regidx))
  | ZICBOZ (_ : regidx)
  | FENCEI (_ : ((BitVec 12) × regidx × regidx))
  | ZIMOP_MOP_R (_ : ((BitVec 5) × regidx × regidx))
  | ZIMOP_MOP_RR (_ : ((BitVec 3) × regidx × regidx × regidx))
  | ZCMOP (_ : (BitVec 3))
  deriving Inhabited, Repr
  open instruction

inductive Privilege where | User | VirtualUser | Supervisor | VirtualSupervisor | Machine
  deriving BEq, Inhabited, Repr
  open Privilege

inductive extension where | Ext_M | Ext_A | Ext_F | Ext_D | Ext_B | Ext_V | Ext_S | Ext_U | Ext_H | Ext_Sha | Ext_Shcounterenw | Ext_Shgatpa | Ext_Shtvala | Ext_Shvsatpa | Ext_Shvstvala | Ext_Shvstvecd | Ext_Zibi | Ext_Zic64b | Ext_Zicbom | Ext_Zicbop | Ext_Zicboz | Ext_Zicfilp | Ext_Zicfiss | Ext_Zicntr | Ext_Zicond | Ext_Zicsr | Ext_Zifencei | Ext_Zihintntl | Ext_Zihintpause | Ext_Zihpm | Ext_Zilx | Ext_Zimop | Ext_Zmmul | Ext_Zaamo | Ext_Zabha | Ext_Zacas | Ext_Zalrsc | Ext_Zama16b | Ext_Zawrs | Ext_Za64rs | Ext_Za128rs | Ext_Zfa | Ext_Zfbfmin | Ext_Zfh | Ext_Zfhmin | Ext_Zfinx | Ext_Zdinx | Ext_Zca | Ext_Zcb | Ext_Zcd | Ext_Zcf | Ext_Zcmop | Ext_C | Ext_Zba | Ext_Zbb | Ext_Zbc | Ext_Zbkb | Ext_Zbkc | Ext_Zbkx | Ext_Zbs | Ext_Ziccamoa | Ext_Ziccamoc | Ext_Ziccif | Ext_Zicclsm | Ext_Ziccrse | Ext_Zknd | Ext_Zkne | Ext_Zknh | Ext_Zkr | Ext_Zksed | Ext_Zksh | Ext_Zkt | Ext_Zhinx | Ext_Zhinxmin | Ext_Zvl32b | Ext_Zvl64b | Ext_Zvl128b | Ext_Zvl256b | Ext_Zvl512b | Ext_Zvl1024b | Ext_Zve32f | Ext_Zve32x | Ext_Zve64d | Ext_Zve64f | Ext_Zve64x | Ext_Zvabd | Ext_Zvfbfmin | Ext_Zvfbfwma | Ext_Zvfh | Ext_Zvfhmin | Ext_Zvbb | Ext_Zvbc | Ext_Zvkb | Ext_Zvkg | Ext_Zvkned | Ext_Zvknha | Ext_Zvknhb | Ext_Zvksed | Ext_Zvksh | Ext_Zvkt | Ext_Zvkn | Ext_Zvknc | Ext_Zvkng | Ext_Zvks | Ext_Zvksc | Ext_Zvksg | Ext_Ssccptr | Ext_Sscofpmf | Ext_Sscounterenw | Ext_Ssdbltrp | Ext_Ssnpm | Ext_Ssstateen | Ext_Ssstrict | Ext_Sdtrig | Ext_Sstc | Ext_Sstvala | Ext_Sstvecd | Ext_Ssu64xl | Ext_Svbare | Ext_Sv32 | Ext_Sv39 | Ext_Sv48 | Ext_Sv57 | Ext_Svade | Ext_Svadu | Ext_Svinval | Ext_Svnapot | Ext_Svpbmt | Ext_Svrsw60t59b | Ext_Svukte | Ext_Svvptc | Ext_Smcntrpmf | Ext_Smdbltrp | Ext_Smmpm | Ext_Smnpm | Ext_Smstateen | Ext_Ssqosid | Ext_Sspm | Ext_Supm
  deriving BEq, Inhabited, Repr
  open extension

inductive XenvcfgCbieReservedBehavior where | Xenvcfg_Fatal | Xenvcfg_ClearPermissions | Xenvcfg_Ignore
  deriving BEq, Inhabited, Repr
  open XenvcfgCbieReservedBehavior

abbrev MEnvcfg := (BitVec 64)

inductive Architecture where | RV32 | RV64 | RV128
  deriving BEq, Inhabited, Repr
  open Architecture

abbrev Misa := (BitVec 64)

abbrev Mstatus := (BitVec 64)

abbrev Seccfg := (BitVec 64)

abbrev HEnvcfg := (BitVec 64)

abbrev SEnvcfg := (BitVec 64)

abbrev Hstateen0 := (BitVec 64)

abbrev Hstateen1 := (BitVec 64)

abbrev Hstateen2 := (BitVec 64)

abbrev Hstateen3 := (BitVec 64)

abbrev Mstateen1 := (BitVec 64)

abbrev Mstateen2 := (BitVec 64)

abbrev Mstateen3 := (BitVec 64)

abbrev Mstateen0 := (BitVec 64)

inductive CSRBitConfig where | CSRBit_Writable | CSRBit_ReadOnlyZero | CSRBit_ReadOnlyOne
  deriving BEq, Inhabited, Repr
  open CSRBitConfig

abbrev Sstateen0 := (BitVec 32)

abbrev Sstateen1 := (BitVec 32)

abbrev Sstateen2 := (BitVec 32)

abbrev Sstateen3 := (BitVec 32)

inductive stateen_bit where | STATEEN_FCSR | STATEEN_SRMCFG | STATEEN_P1P13 | STATEEN_CONTEXT | STATEEN_ENVCFG | STATEEN_SE
  deriving BEq, Inhabited, Repr
  open stateen_bit

inductive AmocasOddRegisterReservedBehavior where | AMOCAS_Fatal | AMOCAS_Illegal
  deriving BEq, Inhabited, Repr
  open AmocasOddRegisterReservedBehavior

inductive InterruptType where | I_Reserved_0 | I_S_Software | I_VS_Software | I_M_Software | I_Reserved_4 | I_S_Timer | I_VS_Timer | I_M_Timer | I_Reserved_8 | I_S_External | I_VS_External | I_M_External | I_SG_External | I_COF | I_Reserved_14 | I_Reserved_15
  deriving BEq, Inhabited, Repr
  open InterruptType

inductive loop_chain_state where | NotInChain | InChainWithMatch | InChainWithoutMatch
  deriving BEq, Inhabited, Repr
  open loop_chain_state

inductive MemoryRegionType where | MainMemory | IOMemory
  deriving BEq, Inhabited, Repr
  open MemoryRegionType

structure PMAMisalignedExceptions where
  load_store : (Option misaligned_exception)
  vector : (Option misaligned_exception)
  amo : misaligned_exception
  lrsc : misaligned_exception
  deriving BEq, Inhabited, Repr

inductive Reservability where | RsrvNone | RsrvNonEventual | RsrvEventual
  deriving BEq, Inhabited, Repr
  open Reservability

abbrev mag_size_exp := Nat

structure PMA where
  mem_type : MemoryRegionType
  cacheable : Bool
  coherent : Bool
  executable : Bool
  readable : Bool
  writable : Bool
  read_idempotent : Bool
  write_idempotent : Bool
  misaligned_exceptions : PMAMisalignedExceptions
  atomic_support : AtomicSupport
  reservability : Reservability
  supports_cbo_zero : Bool
  supports_pte_read : Bool
  supports_pte_write : Bool
  misaligned_atomicity_granule_size_exp : mag_size_exp
  vector_misaligned_atomicity_granule_size_exp : mag_size_exp
  deriving BEq, Inhabited, Repr

structure PMA_Region where
  base : (BitVec 64)
  size : (BitVec 64)
  attributes : PMA
  include_in_device_tree : Bool
  deriving BEq, Inhabited, Repr

abbrev ext_ptw_error := Unit

inductive PTW_Error where
  | PTW_Invalid_Addr (_ : Unit)
  | PTW_No_Access (_ : Unit)
  | PTW_Invalid_PTE (_ : Unit)
  | PTW_No_Permission (_ : Unit)
  | PTW_Misaligned (_ : Unit)
  | PTW_PTE_Needs_Update (_ : Unit)
  | PTW_Implicit_Error (_ : (ExceptionType × gpabits × (MemoryAccessType mem_payload)))
  | PTW_Ext_Error (_ : ext_ptw_error)
  deriving Inhabited, BEq, Repr
  open PTW_Error

inductive TranslationStage where | S_Stage | VS_Stage | G_Stage
  deriving BEq, Inhabited, Repr
  open TranslationStage

abbrev ext_exception := Unit

structure ExceptionContext where
  trap : ExceptionType
  excinfo_is_gva : Bool
  excinfo : xlenbits
  excinfo2 : (Option xlenbits)
  excinst : (Option xlenbits)
  excinst_offset : (BitVec 5)
  ext : (Option ext_exception)
  deriving BEq, Inhabited, Repr

inductive TrapCause where
  | Interrupt (_ : InterruptType)
  | Exception (_ : ExceptionContext)
  deriving Inhabited, BEq, Repr
  open TrapCause

inductive WaitReason where | WAIT_WFI | WAIT_WRS_STO | WAIT_WRS_NTO
  deriving BEq, Inhabited, Repr
  open WaitReason

structure GlobalMisalignedExceptions where
  load_store : (Option misaligned_exception)
  vector : (Option misaligned_exception)
  amo : (Option misaligned_exception)
  lrsc : (Option misaligned_exception)
  deriving BEq, Inhabited, Repr

inductive ExtContextPolicy where | ExtContext_Off | ExtContext_TwoState | ExtContext_FourState
  deriving BEq, Inhabited, Repr
  open ExtContextPolicy

abbrev plat_hpmcounter_width_bits  : Int := 64

abbrev plat_hpmevent_width_bits  : Int := 56

abbrev num_triggers  : Int := 16

inductive Sdtrig_breakpoint_reentrancy where | Use_tcontrol | Use_interrupt_enables | No_reentrancy_support
  deriving BEq, Inhabited, Repr
  open Sdtrig_breakpoint_reentrancy

inductive FcsrRmReservedBehavior where | Fcsr_RM_Fatal | Fcsr_RM_Illegal
  deriving BEq, Inhabited, Repr
  open FcsrRmReservedBehavior

inductive PmpWriteOnlyReservedBehavior where | PMP_Fatal | PMP_ClearPermissions | PMP_Ignore
  deriving BEq, Inhabited, Repr
  open PmpWriteOnlyReservedBehavior

inductive XtvecModeReservedBehavior where | Xtvec_Fatal | Xtvec_Ignore
  deriving BEq, Inhabited, Repr
  open XtvecModeReservedBehavior

inductive RV32ZdinxOddRegisterReservedBehavior where | Zdinx_Fatal | Zdinx_Illegal
  deriving BEq, Inhabited, Repr
  open RV32ZdinxOddRegisterReservedBehavior

inductive IllegalVtypeReservedBehavior where | IllegalVtype_SetVill | IllegalVtype_Illegal | IllegalVtype_Fatal
  deriving BEq, Inhabited, Repr
  open IllegalVtypeReservedBehavior

inductive OOBVstartReservedBehavior where | Vstart_Illegal | Vstart_Ignore
  deriving BEq, Inhabited, Repr
  open OOBVstartReservedBehavior

inductive FflagsDirtyPolicy where | Fflags_Dirty_Precise | Fflags_Dirty_Flag | Fflags_Dirty_Instruction
  deriving BEq, Inhabited, Repr
  open FflagsDirtyPolicy

abbrev exc_code := (BitVec 6)

abbrev ext_ptw := Unit

abbrev ext_ptw_fail := Unit

abbrev instbits := (BitVec 32)

abbrev pagesize_bits  : Int := 12

inductive regno where
  | Regno (_ : Nat)
  deriving Inhabited, BEq, Repr
  open regno

abbrev arch_xlen := (BitVec 2)

abbrev nom_priv_bits := (BitVec 2)

abbrev virt_mode_bit := (BitVec 1)

inductive CSRAccessType where | CSRRead | CSRWrite | CSRReadWrite
  deriving BEq, Inhabited, Repr
  open CSRAccessType

inductive CSRCheckResult where
  | CSR_Check_OK (_ : Unit)
  | CSR_Illegal (_ : Unit)
  | CSR_Virtual (_ : Unit)
  deriving Inhabited, BEq, Repr
  open CSRCheckResult

abbrev is_mem_width (k_w : Int) : Bool := List.elem k_w [1, 2, 4, 8]

abbrev max_mem_width_bytes_exp  : Int := 3

abbrev max_mem_width_bytes  : Int := (2 ^ 3)

abbrev is_mem_width_wide (k_w : Int) : Bool := List.elem k_w [1, 2, 4, 8, 16]

inductive SWCheckCodes where | LANDING_PAD_FAULT
  deriving BEq, Inhabited, Repr
  open SWCheckCodes

abbrev tv_mode := (BitVec 2)

inductive TrapVectorMode where | TV_Direct | TV_Vector | TV_Reserved
  deriving BEq, Inhabited, Repr
  open TrapVectorMode

inductive xRET_type where | mRET | sRET
  deriving BEq, Inhabited, Repr
  open xRET_type

abbrev ext_status := (BitVec 2)

inductive ExtStatus where | Off | Initial | Clean | Dirty
  deriving BEq, Inhabited, Repr
  open ExtStatus

abbrev hgatp_mode := (BitVec 4)

inductive HGATPMode where | HBare | Sv32x4 | Sv39x4 | Sv48x4 | Sv57x4
  deriving BEq, Inhabited, Repr
  open HGATPMode

abbrev satp_mode := (BitVec 4)

inductive SATPMode where | Bare | Sv32 | Sv39 | Sv48 | Sv57
  deriving BEq, Inhabited, Repr
  open SATPMode

abbrev csrRW := (BitVec 2)

abbrev is_sv_mode (k_v : Int) : Bool := List.elem k_v [32, 39, 48, 57]

abbrev is_svx4_mode (k_v : Int) : Bool := List.elem k_v [34, 41, 50, 59]

abbrev is_sv_or_svx4_mode (k_v : Int) : Bool := (is_sv_mode k_v) ∨ (is_svx4_mode k_v)

abbrev is_sv32_mode (k_v : Int) : Bool := k_v = 32 ∨ k_v = 34

abbrev root_level (k_v : Nat) : Int :=
  (if ( k_v = 32 ∨ k_v = 34  : Bool) then 1 else (if ( k_v = 39 ∨ k_v = 41  : Bool) then 2 else (if ( k_v
  = 48 ∨ k_v = 50  : Bool) then 3 else 4)))

abbrev level_range (k_v : Nat) := Nat

abbrev vpn_level_size (k_v : Nat) : Int := (12 - (if ( (is_sv32_mode k_v)  : Bool) then 2 else 3))

abbrev pte_bits k_v := (BitVec (if ( (is_sv32_mode k_v)  : Bool) then 32 else 64))

abbrev ppn_bits k_v := (BitVec (if ( (is_sv32_mode k_v)  : Bool) then 22 else 44))

abbrev vpn_bits k_v := (BitVec (k_v - 12))

inductive page_based_mem_type where | PBMT_PMA | PBMT_NC | PBMT_IO
  deriving BEq, Inhabited, Repr
  open page_based_mem_type

inductive write_kind where | Write_plain | Write_RISCV_release | Write_RISCV_strong_release | Write_RISCV_conditional | Write_RISCV_conditional_release | Write_RISCV_conditional_strong_release
  deriving BEq, Inhabited, Repr
  open write_kind

inductive read_kind where | Read_plain | Read_ifetch | Read_RISCV_acquire | Read_RISCV_strong_acquire | Read_RISCV_reserved | Read_RISCV_reserved_acquire | Read_RISCV_reserved_strong_acquire
  deriving BEq, Inhabited, Repr
  open read_kind

inductive access_kind where
  | AK_Write (_ : (write_kind × (MemoryAccessType mem_payload)))
  | AK_Read (_ : (read_kind × (MemoryAccessType mem_payload)))
  deriving Inhabited, BEq, Repr
  open access_kind

inductive barrier_kind where | Barrier_RISCV_rw_rw | Barrier_RISCV_r_rw | Barrier_RISCV_r_r | Barrier_RISCV_rw_w | Barrier_RISCV_w_w | Barrier_RISCV_w_rw | Barrier_RISCV_rw_r | Barrier_RISCV_r_w | Barrier_RISCV_w_r | Barrier_RISCV_tso | Barrier_RISCV_i
  deriving BEq, Inhabited, Repr
  open barrier_kind

abbrev regtype := xlenbits

abbrev Hstatus := (BitVec 64)

abbrev Mtvec := (BitVec 64)

abbrev Mcause := (BitVec 64)

abbrev Counteren := (BitVec 32)

abbrev Counterin := (BitVec 32)

abbrev Sstatus := (BitVec 64)

abbrev Hgatp64 := (BitVec 64)

abbrev Hgatp32 := (BitVec 32)

abbrev Satp64 := (BitVec 64)

abbrev Satp32 := (BitVec 32)

inductive FeatureEnabledResult where | FEATURE_ENABLED | FEATURE_ILLEGAL | FEATURE_VIRTUAL
  deriving BEq, Inhabited, Repr
  open FeatureEnabledResult

inductive Event where | EV_FENCE | EV_TLB_MISS | EV_MISALIGNED_LOAD_EXCEPTION | EV_MISALIGNED_STORE_EXCEPTION
  deriving BEq, Inhabited, Repr
  open Event

structure event_selector where
  event : Event
  selector : (BitVec 64)
  deriving BEq, Inhabited, Repr

abbrev Minterrupts := (BitVec 64)

abbrev Medeleg := (BitVec 64)

inductive XipReadType where | IncludePlatformInterrupts | ExcludePlatformInterrupts
  deriving BEq, Inhabited, Repr
  open XipReadType

abbrev Sinterrupts := (BitVec 64)

abbrev HpmEvent := (BitVec 64)

abbrev hpmidx := Nat

inductive event_csr where | EV_EVENT | EV_COUNTER
  deriving BEq, Inhabited, Repr
  open event_csr

/-- Type quantifiers: k_a : Type -/
inductive Ext_DataAddr_Check (k_a : Type) where
  | Ext_DataAddr_OK (_ : virtaddr)
  | Ext_DataAddr_Error (_ : k_a)
  deriving Inhabited, BEq, Repr
  open Ext_DataAddr_Check

abbrev ext_fetch_addr_error := Unit

abbrev ext_control_addr_error := Unit

abbrev ext_data_addr_error := Unit

abbrev bits_rm := (BitVec 3)

abbrev bits_fflags := (BitVec 5)

abbrev bits_BF16 := (BitVec 16)

abbrev bits_H := (BitVec 16)

abbrev bits_S := (BitVec 32)

abbrev bits_D := (BitVec 64)

abbrev bits_W := (BitVec 32)

abbrev bits_WU := (BitVec 32)

abbrev bits_L := (BitVec 64)

abbrev bits_LU := (BitVec 64)

inductive PmpAddrMatchType where | OFF | TOR | NA4 | NAPOT
  deriving BEq, Inhabited, Repr
  open PmpAddrMatchType

abbrev Pmpcfg_ent := (BitVec 8)

inductive pmpAddrMatch where | PMP_NoMatch | PMP_PartialMatch | PMP_Match
  deriving BEq, Inhabited, Repr
  open pmpAddrMatch

inductive brop_zbkb where | PACK | PACKH
  deriving BEq, Inhabited, Repr
  open brop_zbkb

abbrev fregtype := flenbits

inductive f_madd_op_H where | FMADD_H | FMSUB_H | FNMSUB_H | FNMADD_H
  deriving BEq, Inhabited, Repr
  open f_madd_op_H

inductive f_bin_rm_op_H where | FADD_H | FSUB_H | FMUL_H | FDIV_H
  deriving BEq, Inhabited, Repr
  open f_bin_rm_op_H

inductive f_un_rm_ff_op_H where | FSQRT_H | FCVT_H_S | FCVT_H_D | FCVT_S_H | FCVT_D_H
  deriving BEq, Inhabited, Repr
  open f_un_rm_ff_op_H

inductive f_un_rm_fx_op_H where | FCVT_W_H | FCVT_WU_H | FCVT_L_H | FCVT_LU_H
  deriving BEq, Inhabited, Repr
  open f_un_rm_fx_op_H

inductive f_un_rm_xf_op_H where | FCVT_H_W | FCVT_H_WU | FCVT_H_L | FCVT_H_LU
  deriving BEq, Inhabited, Repr
  open f_un_rm_xf_op_H

inductive f_un_x_op_H where | FCLASS_H | FMV_X_H
  deriving BEq, Inhabited, Repr
  open f_un_x_op_H

inductive f_un_f_op_H where | FMV_H_X
  deriving BEq, Inhabited, Repr
  open f_un_f_op_H

inductive f_bin_f_op_H where | FSGNJ_H | FSGNJN_H | FSGNJX_H | FMIN_H | FMAX_H
  deriving BEq, Inhabited, Repr
  open f_bin_f_op_H

inductive f_bin_x_op_H where | FEQ_H | FLT_H | FLE_H
  deriving BEq, Inhabited, Repr
  open f_bin_x_op_H

inductive rounding_mode where | RM_RNE | RM_RTZ | RM_RDN | RM_RUP | RM_RMM | RM_DYN
  deriving BEq, Inhabited, Repr
  open rounding_mode

inductive f_madd_op_S where | FMADD_S | FMSUB_S | FNMSUB_S | FNMADD_S
  deriving BEq, Inhabited, Repr
  open f_madd_op_S

inductive f_bin_rm_op_S where | FADD_S | FSUB_S | FMUL_S | FDIV_S
  deriving BEq, Inhabited, Repr
  open f_bin_rm_op_S

inductive f_un_rm_ff_op_S where | FSQRT_S
  deriving BEq, Inhabited, Repr
  open f_un_rm_ff_op_S

inductive f_un_rm_fx_op_S where | FCVT_W_S | FCVT_WU_S | FCVT_L_S | FCVT_LU_S
  deriving BEq, Inhabited, Repr
  open f_un_rm_fx_op_S

inductive f_un_rm_xf_op_S where | FCVT_S_W | FCVT_S_WU | FCVT_S_L | FCVT_S_LU
  deriving BEq, Inhabited, Repr
  open f_un_rm_xf_op_S

inductive f_un_op_f_S where | FMV_W_X
  deriving BEq, Inhabited, Repr
  open f_un_op_f_S

inductive f_un_op_x_S where | FCLASS_S | FMV_X_W
  deriving BEq, Inhabited, Repr
  open f_un_op_x_S

inductive f_bin_op_f_S where | FSGNJ_S | FSGNJN_S | FSGNJX_S | FMIN_S | FMAX_S
  deriving BEq, Inhabited, Repr
  open f_bin_op_f_S

inductive f_bin_op_x_S where | FEQ_S | FLT_S | FLE_S
  deriving BEq, Inhabited, Repr
  open f_bin_op_x_S

inductive f_madd_op_D where | FMADD_D | FMSUB_D | FNMSUB_D | FNMADD_D
  deriving BEq, Inhabited, Repr
  open f_madd_op_D

inductive f_bin_rm_op_D where | FADD_D | FSUB_D | FMUL_D | FDIV_D
  deriving BEq, Inhabited, Repr
  open f_bin_rm_op_D

inductive f_un_rm_ff_op_D where | FSQRT_D | FCVT_S_D | FCVT_D_S
  deriving BEq, Inhabited, Repr
  open f_un_rm_ff_op_D

inductive f_un_rm_fx_op_D where | FCVT_W_D | FCVT_WU_D | FCVT_L_D | FCVT_LU_D
  deriving BEq, Inhabited, Repr
  open f_un_rm_fx_op_D

inductive f_un_rm_xf_op_D where | FCVT_D_W | FCVT_D_WU | FCVT_D_L | FCVT_D_LU
  deriving BEq, Inhabited, Repr
  open f_un_rm_xf_op_D

inductive f_bin_f_op_D where | FSGNJ_D | FSGNJN_D | FSGNJX_D | FMIN_D | FMAX_D
  deriving BEq, Inhabited, Repr
  open f_bin_f_op_D

inductive f_bin_x_op_D where | FEQ_D | FLT_D | FLE_D
  deriving BEq, Inhabited, Repr
  open f_bin_x_op_D

inductive f_un_x_op_D where | FCLASS_D | FMV_X_D
  deriving BEq, Inhabited, Repr
  open f_un_x_op_D

inductive f_un_f_op_D where | FMV_D_X
  deriving BEq, Inhabited, Repr
  open f_un_f_op_D

inductive fregidx where
  | Fregidx (_ : (BitVec 5))
  deriving Inhabited, BEq, Repr
  open fregidx

inductive fregno where
  | Fregno (_ : Nat)
  deriving Inhabited, BEq, Repr
  open fregno

inductive cfregidx where
  | Cfregidx (_ : (BitVec 3))
  deriving Inhabited, BEq, Repr
  open cfregidx

abbrev Fcsr := (BitVec 32)

abbrev nfields_range (k_q : Int) : Bool := k_q > 0 ∧ k_q ≤ 8

abbrev nfields_range_pow2 (k_q : Int) : Bool := List.elem k_q [1, 2, 4, 8]

abbrev nfields := Int

abbrev nfields_pow2 := Int

abbrev vlenbits := (BitVec (2 ^ 8))

inductive vvfunct6 where | VV_VADD | VV_VSUB | VV_VMINU | VV_VMIN | VV_VMAXU | VV_VMAX | VV_VAND | VV_VOR | VV_VXOR | VV_VRGATHER | VV_VRGATHEREI16 | VV_VSADDU | VV_VSADD | VV_VSSUBU | VV_VSSUB | VV_VSLL | VV_VSMUL | VV_VSRL | VV_VSRA | VV_VSSRL | VV_VSSRA
  deriving BEq, Inhabited, Repr
  open vvfunct6

inductive vvcmpfunct6 where | VVCMP_VMSEQ | VVCMP_VMSNE | VVCMP_VMSLTU | VVCMP_VMSLT | VVCMP_VMSLEU | VVCMP_VMSLE
  deriving BEq, Inhabited, Repr
  open vvcmpfunct6

inductive vvmfunct6 where | VVM_VMADC | VVM_VMSBC
  deriving BEq, Inhabited, Repr
  open vvmfunct6

inductive vvmcfunct6 where | VVMC_VMADC | VVMC_VMSBC
  deriving BEq, Inhabited, Repr
  open vvmcfunct6

inductive vvmsfunct6 where | VVMS_VADC | VVMS_VSBC
  deriving BEq, Inhabited, Repr
  open vvmsfunct6

inductive vxmfunct6 where | VXM_VMADC | VXM_VMSBC
  deriving BEq, Inhabited, Repr
  open vxmfunct6

inductive vxmcfunct6 where | VXMC_VMADC | VXMC_VMSBC
  deriving BEq, Inhabited, Repr
  open vxmcfunct6

inductive vxmsfunct6 where | VXMS_VADC | VXMS_VSBC
  deriving BEq, Inhabited, Repr
  open vxmsfunct6

inductive vimfunct6 where | VIM_VMADC
  deriving BEq, Inhabited, Repr
  open vimfunct6

inductive vimcfunct6 where | VIMC_VMADC
  deriving BEq, Inhabited, Repr
  open vimcfunct6

inductive vimsfunct6 where | VIMS_VADC
  deriving BEq, Inhabited, Repr
  open vimsfunct6

inductive vxcmpfunct6 where | VXCMP_VMSEQ | VXCMP_VMSNE | VXCMP_VMSLTU | VXCMP_VMSLT | VXCMP_VMSLEU | VXCMP_VMSLE | VXCMP_VMSGTU | VXCMP_VMSGT
  deriving BEq, Inhabited, Repr
  open vxcmpfunct6

inductive vicmpfunct6 where | VICMP_VMSEQ | VICMP_VMSNE | VICMP_VMSLEU | VICMP_VMSLE | VICMP_VMSGTU | VICMP_VMSGT
  deriving BEq, Inhabited, Repr
  open vicmpfunct6

inductive nvfunct6 where | NV_VNCLIPU | NV_VNCLIP
  deriving BEq, Inhabited, Repr
  open nvfunct6

inductive nvsfunct6 where | NVS_VNSRL | NVS_VNSRA
  deriving BEq, Inhabited, Repr
  open nvsfunct6

inductive nxfunct6 where | NX_VNCLIPU | NX_VNCLIP
  deriving BEq, Inhabited, Repr
  open nxfunct6

inductive nxsfunct6 where | NXS_VNSRL | NXS_VNSRA
  deriving BEq, Inhabited, Repr
  open nxsfunct6

inductive mmfunct6 where | MM_VMAND | MM_VMNAND | MM_VMANDN | MM_VMXOR | MM_VMOR | MM_VMNOR | MM_VMORN | MM_VMXNOR
  deriving BEq, Inhabited, Repr
  open mmfunct6

inductive nifunct6 where | NI_VNCLIPU | NI_VNCLIP
  deriving BEq, Inhabited, Repr
  open nifunct6

inductive nisfunct6 where | NIS_VNSRL | NIS_VNSRA
  deriving BEq, Inhabited, Repr
  open nisfunct6

inductive wvvfunct6 where | WVV_VADD | WVV_VSUB | WVV_VADDU | WVV_VSUBU | WVV_VWMUL | WVV_VWMULU | WVV_VWMULSU
  deriving BEq, Inhabited, Repr
  open wvvfunct6

inductive wvfunct6 where | WV_VADD | WV_VSUB | WV_VADDU | WV_VSUBU
  deriving BEq, Inhabited, Repr
  open wvfunct6

inductive wvxfunct6 where | WVX_VADD | WVX_VSUB | WVX_VADDU | WVX_VSUBU | WVX_VWMUL | WVX_VWMULU | WVX_VWMULSU
  deriving BEq, Inhabited, Repr
  open wvxfunct6

inductive wxfunct6 where | WX_VADD | WX_VSUB | WX_VADDU | WX_VSUBU
  deriving BEq, Inhabited, Repr
  open wxfunct6

inductive vextfunct6 where | VEXT2_ZVF2 | VEXT2_SVF2 | VEXT4_ZVF4 | VEXT4_SVF4 | VEXT8_ZVF8 | VEXT8_SVF8
  deriving BEq, Inhabited, Repr
  open vextfunct6

inductive vxfunct6 where | VX_VADD | VX_VSUB | VX_VRSUB | VX_VMINU | VX_VMIN | VX_VMAXU | VX_VMAX | VX_VAND | VX_VOR | VX_VXOR | VX_VSADDU | VX_VSADD | VX_VSSUBU | VX_VSSUB | VX_VSLL | VX_VSMUL | VX_VSRL | VX_VSRA | VX_VSSRL | VX_VSSRA
  deriving BEq, Inhabited, Repr
  open vxfunct6

inductive vifunct6 where | VI_VADD | VI_VRSUB | VI_VAND | VI_VOR | VI_VXOR | VI_VSADDU | VI_VSADD | VI_VSLL | VI_VSRL | VI_VSRA | VI_VSSRL | VI_VSSRA
  deriving BEq, Inhabited, Repr
  open vifunct6

inductive vxsgfunct6 where | VX_VSLIDEUP | VX_VSLIDEDOWN | VX_VRGATHER
  deriving BEq, Inhabited, Repr
  open vxsgfunct6

inductive visgfunct6 where | VI_VSLIDEUP | VI_VSLIDEDOWN | VI_VRGATHER
  deriving BEq, Inhabited, Repr
  open visgfunct6

inductive mvvfunct6 where | MVV_VAADDU | MVV_VAADD | MVV_VASUBU | MVV_VASUB | MVV_VMUL | MVV_VMULH | MVV_VMULHU | MVV_VMULHSU | MVV_VDIVU | MVV_VDIV | MVV_VREMU | MVV_VREM
  deriving BEq, Inhabited, Repr
  open mvvfunct6

inductive mvvmafunct6 where | MVV_VMACC | MVV_VNMSAC | MVV_VMADD | MVV_VNMSUB
  deriving BEq, Inhabited, Repr
  open mvvmafunct6

inductive rmvvfunct6 where | MVV_VREDSUM | MVV_VREDAND | MVV_VREDOR | MVV_VREDXOR | MVV_VREDMINU | MVV_VREDMIN | MVV_VREDMAXU | MVV_VREDMAX
  deriving BEq, Inhabited, Repr
  open rmvvfunct6

inductive rivvfunct6 where | IVV_VWREDSUMU | IVV_VWREDSUM
  deriving BEq, Inhabited, Repr
  open rivvfunct6

inductive rfvvfunct6 where | FVV_VFREDOSUM | FVV_VFREDUSUM | FVV_VFREDMAX | FVV_VFREDMIN
  deriving BEq, Inhabited, Repr
  open rfvvfunct6

inductive rfwvvfunct6 where | FVV_VFWREDOSUM | FVV_VFWREDUSUM
  deriving BEq, Inhabited, Repr
  open rfwvvfunct6

inductive wmvvfunct6 where | WMVV_VWMACCU | WMVV_VWMACC | WMVV_VWMACCSU
  deriving BEq, Inhabited, Repr
  open wmvvfunct6

inductive mvxfunct6 where | MVX_VAADDU | MVX_VAADD | MVX_VASUBU | MVX_VASUB | MVX_VSLIDE1UP | MVX_VSLIDE1DOWN | MVX_VMUL | MVX_VMULH | MVX_VMULHU | MVX_VMULHSU | MVX_VDIVU | MVX_VDIV | MVX_VREMU | MVX_VREM
  deriving BEq, Inhabited, Repr
  open mvxfunct6

inductive mvxmafunct6 where | MVX_VMACC | MVX_VNMSAC | MVX_VMADD | MVX_VNMSUB
  deriving BEq, Inhabited, Repr
  open mvxmafunct6

inductive wmvxfunct6 where | WMVX_VWMACCU | WMVX_VWMACC | WMVX_VWMACCUS | WMVX_VWMACCSU
  deriving BEq, Inhabited, Repr
  open wmvxfunct6

inductive maskfunct3 where | VV_VMERGE | VI_VMERGE | VX_VMERGE
  deriving BEq, Inhabited, Repr
  open maskfunct3

inductive vlewidth where | VLE8 | VLE16 | VLE32 | VLE64
  deriving BEq, Inhabited, Repr
  open vlewidth

inductive fvvfunct6 where | FVV_VADD | FVV_VSUB | FVV_VMIN | FVV_VMAX | FVV_VSGNJ | FVV_VSGNJN | FVV_VSGNJX | FVV_VDIV | FVV_VMUL
  deriving BEq, Inhabited, Repr
  open fvvfunct6

inductive fvvmafunct6 where | FVV_VMADD | FVV_VNMADD | FVV_VMSUB | FVV_VNMSUB | FVV_VMACC | FVV_VNMACC | FVV_VMSAC | FVV_VNMSAC
  deriving BEq, Inhabited, Repr
  open fvvmafunct6

inductive fwvvfunct6 where | FWVV_VADD | FWVV_VSUB | FWVV_VMUL
  deriving BEq, Inhabited, Repr
  open fwvvfunct6

inductive fwvvmafunct6 where | FWVV_VMACC | FWVV_VNMACC | FWVV_VMSAC | FWVV_VNMSAC
  deriving BEq, Inhabited, Repr
  open fwvvmafunct6

inductive fwvfunct6 where | FWV_VADD | FWV_VSUB
  deriving BEq, Inhabited, Repr
  open fwvfunct6

inductive fvvmfunct6 where | FVVM_VMFEQ | FVVM_VMFLE | FVVM_VMFLT | FVVM_VMFNE
  deriving BEq, Inhabited, Repr
  open fvvmfunct6

inductive vfunary0 where | FV_CVT_XU_F | FV_CVT_X_F | FV_CVT_F_XU | FV_CVT_F_X | FV_CVT_RTZ_XU_F | FV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr
  open vfunary0

inductive vfwunary0 where | FWV_CVT_XU_F | FWV_CVT_X_F | FWV_CVT_F_XU | FWV_CVT_F_X | FWV_CVT_F_F | FWV_CVT_RTZ_XU_F | FWV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr
  open vfwunary0

inductive vfnunary0 where | FNV_CVT_XU_F | FNV_CVT_X_F | FNV_CVT_F_XU | FNV_CVT_F_X | FNV_CVT_F_F | FNV_CVT_ROD_F_F | FNV_CVT_RTZ_XU_F | FNV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr
  open vfnunary0

inductive vfunary1 where | FVV_VSQRT | FVV_VRSQRT7 | FVV_VREC7 | FVV_VCLASS
  deriving BEq, Inhabited, Repr
  open vfunary1

inductive fvffunct6 where | VF_VADD | VF_VSUB | VF_VMIN | VF_VMAX | VF_VSGNJ | VF_VSGNJN | VF_VSGNJX | VF_VDIV | VF_VRDIV | VF_VMUL | VF_VRSUB | VF_VSLIDE1UP | VF_VSLIDE1DOWN
  deriving BEq, Inhabited, Repr
  open fvffunct6

inductive fvfmafunct6 where | VF_VMADD | VF_VNMADD | VF_VMSUB | VF_VNMSUB | VF_VMACC | VF_VNMACC | VF_VMSAC | VF_VNMSAC
  deriving BEq, Inhabited, Repr
  open fvfmafunct6

inductive fwvffunct6 where | FWVF_VADD | FWVF_VSUB | FWVF_VMUL
  deriving BEq, Inhabited, Repr
  open fwvffunct6

inductive fwvfmafunct6 where | FWVF_VMACC | FWVF_VNMACC | FWVF_VMSAC | FWVF_VNMSAC
  deriving BEq, Inhabited, Repr
  open fwvfmafunct6

inductive fwffunct6 where | FWF_VADD | FWF_VSUB
  deriving BEq, Inhabited, Repr
  open fwffunct6

inductive fvfmfunct6 where | VFM_VMFEQ | VFM_VMFLE | VFM_VMFLT | VFM_VMFNE | VFM_VMFGT | VFM_VMFGE
  deriving BEq, Inhabited, Repr
  open fvfmfunct6

inductive vmlsop where | VLM | VSM
  deriving BEq, Inhabited, Repr
  open vmlsop

inductive indexed_mop where | INDEXED_UNORDERED | INDEXED_ORDERED
  deriving BEq, Inhabited, Repr
  open indexed_mop

inductive vstart_class where | VSTART_ARITH | VSTART_LOAD_STORE | VSTART_SCALAR_MOVE | VSTART_MANDATORY
  deriving BEq, Inhabited, Repr
  open vstart_class

inductive vregno where
  | Vregno (_ : Nat)
  deriving Inhabited, BEq, Repr
  open vregno

abbrev Vtype := (BitVec 64)

abbrev SEW_pow := Nat

abbrev LMUL_pow := Int

abbrev sew_bitsize := Int

abbrev is_sew_bitsize (k_n : Int) : Bool := List.elem k_n [8, 16, 32, 64]

inductive agtype where | UNDISTURBED | AGNOSTIC
  deriving BEq, Inhabited, Repr
  open agtype

abbrev Vcsr := (BitVec 3)

abbrev CountSmcntrpmf := (BitVec 64)

abbrev trigger_index := Nat

inductive Trig_Type where | TT_none | TT_legacy | TT_mcontrol | TT_icount | TT_itrigger | TT_etrigger | TT_mcontrol6 | TT_tmexttrigger | TT_custom | TT_disabled | TT_reserved
  deriving BEq, Inhabited, Repr
  open Trig_Type

inductive Trig_Action where | TA_Breakpoint | TA_Enter_Debug | TA_Trace_On | TA_Trace_Off | TA_Trace_Notify | TA_Ext_Trigger_0 | TA_Ext_Trigger_1
  deriving BEq, Inhabited, Repr
  open Trig_Action

inductive Hit where | Hit_false | Hit_before | Hit_after | Hit_imm_after
  deriving BEq, Inhabited, Repr
  open Hit

inductive Compare_Selection where | Compare_Address | Compare_Data
  deriving BEq, Inhabited, Repr
  open Compare_Selection

abbrev Trig_Match_Size := Int

inductive Trig_Match where | TM_EQ | TM_NAPOT | TM_GE | TM_LT | TM_MASK_LO | TM_MASK_HI | TM_NEQ | TM_NOT_NAPOT | TM_NOT_MASK_LO | TM_NOT_MASK_HI
  deriving BEq, Inhabited, Repr
  open Trig_Match

abbrev Trigger_Extra_RV32 := (BitVec 32)

abbrev Trigger_Extra_RV64 := (BitVec 64)

structure TExtra where
  mhvalue : (BitVec 13)
  mhselect : (BitVec 3)
  sbytemask : (BitVec 4)
  svalue : (BitVec 32)
  sselect : (BitVec 2)
  deriving BEq, Inhabited, Repr

inductive trigger_addr_type where | TriggerAddress_Load | TriggerAddress_Store | TriggerAddress_AMO
  deriving BEq, Inhabited, Repr
  open trigger_addr_type

abbrev trigger_data_bits  : Int := (8 * 16)

abbrev trigger_data := (BitVec (8 * 16))

inductive MemoryTriggerPayload where
  | TriggerFetchAddr (_ : xlenbits)
  | TriggerFetchInstr (_ : (xlenbits × trigger_data × Nat))
  | TriggerAddress (_ : (trigger_addr_type × xlenbits × Int))
  | TriggerStore (_ : (xlenbits × trigger_data × Nat))
  | TriggerLoadData (_ : (xlenbits × trigger_data × Nat))
  | TriggerAMOData (_ : (xlenbits × trigger_data × trigger_data × Nat))
  deriving Inhabited, BEq, Repr
  open MemoryTriggerPayload

abbrev pending_trigger_info := (Trig_Action × trigger_index × xlenbits)

structure TDisabled where
  dmode : Bool
  data : (BitVec (64 - 5))
  tdata2 : xlenbits
  textra : TExtra
  deriving BEq, Inhabited, Repr

abbrev TDisabled_bits := (BitVec 64)

structure MControl6 where
  dmode : Bool
  uncertain : Bool
  hit : Hit
  vs : Bool
  vu : Bool
  select : Compare_Selection
  size : Trig_Match_Size
  action : Trig_Action
  chain : Bool
  t_match : Trig_Match
  m : Bool
  uncertainen : Bool
  s : Bool
  u : Bool
  execute : Bool
  store : Bool
  load : Bool
  tdata2 : xlenbits
  textra : TExtra
  match_info : (Option (xlenbits × Hit))
  deriving BEq, Inhabited, Repr

abbrev MControl6_bits := (BitVec 64)

structure ICount where
  dmode : Bool
  vs : Bool
  vu : Bool
  hit : Bool
  count : (BitVec 14)
  m : Bool
  pending : Bool
  s : Bool
  u : Bool
  new_count : (Option (BitVec 14))
  action : Trig_Action
  active : Bool
  tdata2 : xlenbits
  textra : TExtra
  deriving BEq, Inhabited, Repr

abbrev ICount_bits := (BitVec 64)

structure ITrigger where
  dmode : Bool
  hit : Bool
  vs : Bool
  vu : Bool
  nmi : Bool
  m : Bool
  s : Bool
  u : Bool
  action : Trig_Action
  tdata2 : xlenbits
  textra : TExtra
  pending : Bool
  deriving BEq, Inhabited, Repr

structure ETrigger where
  dmode : Bool
  hit : Bool
  vs : Bool
  vu : Bool
  m : Bool
  s : Bool
  u : Bool
  action : Trig_Action
  tdata2 : xlenbits
  textra : TExtra
  pending : Bool
  deriving BEq, Inhabited, Repr

abbrev IETrigger_bits := (BitVec 64)

inductive Trigger where
  | T_disabled (_ : TDisabled)
  | T_icount (_ : ICount)
  | T_itrigger (_ : ITrigger)
  | T_etrigger (_ : ETrigger)
  | T_mcontrol6 (_ : MControl6)
  deriving Inhabited, BEq, Repr
  open Trigger

abbrev TInfo := (BitVec 64)

abbrev TData1 := (BitVec 64)

abbrev TControl := (BitVec 64)

abbrev SContext := (BitVec 64)

abbrev MContext := (BitVec 64)

abbrev External_Trigger := (BitVec 64)

inductive tdata where | TDATA1 | TDATA2 | TDATA3
  deriving BEq, Inhabited, Repr
  open tdata

inductive mask_type where | MASK_LO | MASK_HI
  deriving BEq, Inhabited, Repr
  open mask_type

inductive Software_Check_Code where | SWC_NO_INFO | SWC_LANDING_PAD_FAULT | SWC_SHADOW_STACK_FAULT
  deriving BEq, Inhabited, Repr
  open Software_Check_Code

inductive landing_pad_expectation where | NO_LP_EXPECTED | LP_EXPECTED
  deriving BEq, Inhabited, Repr
  open landing_pad_expectation

abbrev MemoryOpResult k_a := (Result k_a (physaddr × ExceptionType))

abbrev htif_cmd := (BitVec 64)

inductive Splittability where | CanSplit | CannotSplit
  deriving BEq, Inhabited, Repr
  open Splittability

abbrev valid_misaligned_order (k_n : Int) (k_first : Int) (k_last : Int) (k_step : Int) : Bool :=
  k_first = 0 ∧ k_last = (k_n - 1) ∧ k_step = 1 ∨
  k_first = (k_n - 1) ∧ k_last = 0 ∧ k_step = ((- 1))

structure Phys_Mem_Access_Info where
  splittable : Splittability
  granule_size_exp : mag_size_exp
  deriving BEq, Inhabited, Repr

abbrev pte_flags_bits := (BitVec 8)

abbrev pte_ext_bits := (BitVec 10)

abbrev PTE_Ext := (BitVec 10)

abbrev PTE_Flags := (BitVec 8)

inductive pte_check_failure where
  | PTE_No_Permission (_ : Unit)
  | PTE_No_Access (_ : Unit)
  | PTE_Ext_Failure (_ : ext_ptw_fail)
  deriving Inhabited, BEq, Repr
  open pte_check_failure

inductive PTE_Check where
  | PTE_Check_Success (_ : ext_ptw)
  | PTE_Check_Failure (_ : (ext_ptw × pte_check_failure))
  deriving Inhabited, BEq, Repr
  open PTE_Check

abbrev tlb_vpn_bits  : Int := (59 - 12)

abbrev tlb_ppn_bits  : Int := 44

structure TLB_Entry where
  asid : asidbits
  vmid : vmidbits
  stage : TranslationStage
  global : Bool
  vpn : (BitVec (59 - 12))
  levelMask : (BitVec (59 - 12))
  ppn : (BitVec 44)
  pte : (BitVec 64)
  pteAddr : physaddr
  deriving BEq, Inhabited, Repr

abbrev num_tlb_entries_exp  : Int := 6

abbrev num_tlb_entries  : Int := (2 ^ 6)

abbrev tlb_index_range := Nat

/-- Type quantifiers: k_v : Int, (is_sv_or_svx4_mode k_v) -/
structure PTW_Output (k_v : Nat) where
  ppn : (ppn_bits k_v)
  pte : (pte_bits k_v)
  pteAddr : physaddr
  level : (level_range k_v)
  pbmt : page_based_mem_type
  global : Bool
  deriving BEq, Inhabited, Repr

abbrev PTW_Result k_v := (Result ((PTW_Output k_v) × ext_ptw) (PTW_Error × ext_ptw))

abbrev TR_Result k_paddr k_failure :=
  (Result (k_paddr × page_based_mem_type × ext_ptw) (k_failure × ext_ptw))

inductive ExecutionResult where
  | Retire_Success (_ : Unit)
  | ExecuteAs (_ : instruction)
  | Enter_Wait (_ : WaitReason)
  | Illegal_Instruction (_ : Unit)
  | Virtual_Instruction (_ : Unit)
  | Trap (_ : (Privilege × ExceptionContext × xlenbits))
  | PendingTrigger (_ : pending_trigger_info)
  | Ext_CSR_Check_Failure (_ : Unit)
  | Ext_ControlAddr_Check_Failure (_ : ext_control_addr_error)
  | Ext_DataAddr_Check_Failure (_ : ext_data_addr_error)
  | Ext_XRET_Priv_Failure (_ : Unit)
  deriving Inhabited, Repr
  open ExecutionResult

structure AccessInfo where
  eff_privilege : Privilege
  pmlen : pm_len
  as_guest : Bool
  deriving BEq, Inhabited, Repr

abbrev Srmcfg := (BitVec 64)

inductive cbie where | CBIE_ILLEGAL | CBIE_EXEC_FLUSH | CBIE_EXEC_INVAL
  deriving BEq, Inhabited, Repr
  open cbie

inductive checked_cbop where | CBOP_ILLEGAL | CBOP_ILLEGAL_VIRTUAL | CBOP_INVAL_FLUSH | CBOP_INVAL_INVAL
  deriving BEq, Inhabited, Repr
  open checked_cbop

structure instr_info where
  fetch_privilege : Privilege
  fetch_trigger_reentrance : Bool
  fetched_instruction : instruction
  executed_instruction : (Option instruction)
  instbits : instbits
  compressed : Bool
  deriving Inhabited, Repr

inductive HartState where
  | HART_ACTIVE (_ : Unit)
  | HART_WAITING (_ : (WaitReason × instr_info))
  deriving Inhabited, Repr
  open HartState

inductive FetchResult where
  | F_Ext_Error (_ : ext_fetch_addr_error)
  | F_Base (_ : word)
  | F_RVC (_ : half)
  | F_Error (_ : ExceptionContext)
  deriving Inhabited, BEq, Repr
  open FetchResult

/-- Type quantifiers: k_width : Int, k_width ≥ 0 -/
inductive FetchBytes_Result (k_width : Nat) where
  | FetchBytes_Ext_Error (_ : ext_fetch_addr_error)
  | FetchBytes_Exception (_ : ExceptionContext)
  | FetchBytes_Success (_ : (BitVec (k_width * 8)))
  deriving Inhabited, BEq, Repr
  open FetchBytes_Result

inductive Step where
  | Step_Pending_Interrupt (_ : (InterruptType × Privilege))
  | Step_Pending_Trigger (_ : pending_trigger_info)
  | Step_Fetch_Trigger (_ : pending_trigger_info)
  | Step_Ext_Fetch_Failure (_ : ext_fetch_addr_error)
  | Step_Fetch_Failure (_ : ExceptionContext)
  | Step_Execute (_ : (ExecutionResult × instr_info))
  | Step_Waiting (_ : WaitReason)
  deriving Inhabited, Repr
  open Step

structure pma_check_opts where
  zama16b : Bool
  ziccamoa : Bool
  ziccamoc : Bool
  ziccif : Bool
  zicclsm : Bool
  ziccrse : Bool
  ssccptr : Bool
  svadu : Bool
  deriving BEq, Inhabited, Repr

inductive ISA_Format where | Canonical_Lowercase | DeviceTree_ISA_Extensions
  deriving BEq, Inhabited, Repr
  open ISA_Format

inductive Register : Type where
  | hart_state
  | ssp
  | srmcfg
  | tlb
  | pma_regions
  | htif_payload_writes
  | htif_cmd_write
  | htif_exit_code
  | htif_done
  | htif_tohost
  | htif_tohost_base
  | pc_reset_address
  | elp
  | mcontext
  | scontext
  | tcontrol
  | written_trigger_index
  | tselect
  | triggers
  | minstretcfg
  | mcyclecfg
  | vcsr
  | vtype
  | vl
  | vstart
  | vr31
  | vr30
  | vr29
  | vr28
  | vr27
  | vr26
  | vr25
  | vr24
  | vr23
  | vr22
  | vr21
  | vr20
  | vr19
  | vr18
  | vr17
  | vr16
  | vr15
  | vr14
  | vr13
  | vr12
  | vr11
  | vr10
  | vr9
  | vr8
  | vr7
  | vr6
  | vr5
  | vr4
  | vr3
  | vr2
  | vr1
  | vr0
  | fcsr
  | f31
  | f30
  | f29
  | f28
  | f27
  | f26
  | f25
  | f24
  | f23
  | f22
  | f21
  | f20
  | f19
  | f18
  | f17
  | f16
  | f15
  | f14
  | f13
  | f12
  | f11
  | f10
  | f9
  | f8
  | f7
  | f6
  | f5
  | f4
  | f3
  | f2
  | f1
  | f0
  | pmpaddr_n
  | pmpcfg_n
  | written_event_index
  | mhpmcounter
  | mhpmevent
  | vsip
  | vsie
  | hideleg
  | hedeleg
  | sig_msip
  | msip
  | mtime
  | mtimecmp
  | sig_ssip
  | sig_seip
  | sig_meip
  | mideleg
  | medeleg
  | mip
  | mie
  | hvip
  | sig_hgeip
  | hgeie
  | vstimecmp
  | stimecmp
  | vsatp
  | satp
  | hgatp
  | stval
  | scause
  | sepc
  | sscratch
  | stvec
  | vstval
  | vscause
  | vsepc
  | vsscratch
  | vstvec
  | htinst
  | htval
  | htimedelta
  | mtval2
  | mtinst
  | mconfigptr
  | mhartid
  | marchid
  | mimpid
  | mvendorid
  | minstret_increment
  | minstret
  | mcycle
  | mcountinhibit
  | mcounteren
  | hcounteren
  | scounteren
  | mscratch
  | mtval
  | mepc
  | mcause
  | mtvec
  | hstatus
  | cur_inst
  | x31
  | x30
  | x29
  | x28
  | x27
  | x26
  | x25
  | x24
  | x23
  | x22
  | x21
  | x20
  | x19
  | x18
  | x17
  | x16
  | x15
  | x14
  | x13
  | x12
  | x11
  | x10
  | x9
  | x8
  | x7
  | x6
  | x5
  | x4
  | x3
  | x2
  | x1
  | nextPC
  | PC
  | henvcfg
  | menvcfg
  | mseccfg
  | senvcfg
  | sstateen3
  | sstateen2
  | sstateen1
  | sstateen0
  | mstateen0
  | mstateen3
  | mstateen2
  | mstateen1
  | hstateen3
  | hstateen2
  | hstateen1
  | hstateen0
  | vsstatus
  | mstatus
  | misa
  | cur_privilege
  | rvfi_mem_data_present
  | rvfi_mem_data
  | rvfi_int_data_present
  | rvfi_int_data
  | rvfi_pc_data
  | rvfi_inst_data
  | rvfi_instruction
  | fp_rounding_global
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .hart_state => HartState
  | .ssp => (BitVec 64)
  | .srmcfg => (BitVec 64)
  | .tlb => (Vector (Option TLB_Entry) (2 ^ 6))
  | .pma_regions => (List PMA_Region)
  | .htif_payload_writes => (BitVec 4)
  | .htif_cmd_write => (BitVec 1)
  | .htif_exit_code => (BitVec 64)
  | .htif_done => Bool
  | .htif_tohost => (BitVec 64)
  | .htif_tohost_base => (Option (BitVec 64))
  | .pc_reset_address => (BitVec 64)
  | .elp => (BitVec 1)
  | .mcontext => (BitVec 64)
  | .scontext => (BitVec 64)
  | .tcontrol => (BitVec 64)
  | .written_trigger_index => (Option (Nat × tdata))
  | .tselect => (BitVec 64)
  | .triggers => (Vector Trigger 16)
  | .minstretcfg => (BitVec 64)
  | .mcyclecfg => (BitVec 64)
  | .vcsr => (BitVec 3)
  | .vtype => (BitVec 64)
  | .vl => (BitVec 64)
  | .vstart => (BitVec 64)
  | .vr31 => (BitVec (2 ^ 8))
  | .vr30 => (BitVec (2 ^ 8))
  | .vr29 => (BitVec (2 ^ 8))
  | .vr28 => (BitVec (2 ^ 8))
  | .vr27 => (BitVec (2 ^ 8))
  | .vr26 => (BitVec (2 ^ 8))
  | .vr25 => (BitVec (2 ^ 8))
  | .vr24 => (BitVec (2 ^ 8))
  | .vr23 => (BitVec (2 ^ 8))
  | .vr22 => (BitVec (2 ^ 8))
  | .vr21 => (BitVec (2 ^ 8))
  | .vr20 => (BitVec (2 ^ 8))
  | .vr19 => (BitVec (2 ^ 8))
  | .vr18 => (BitVec (2 ^ 8))
  | .vr17 => (BitVec (2 ^ 8))
  | .vr16 => (BitVec (2 ^ 8))
  | .vr15 => (BitVec (2 ^ 8))
  | .vr14 => (BitVec (2 ^ 8))
  | .vr13 => (BitVec (2 ^ 8))
  | .vr12 => (BitVec (2 ^ 8))
  | .vr11 => (BitVec (2 ^ 8))
  | .vr10 => (BitVec (2 ^ 8))
  | .vr9 => (BitVec (2 ^ 8))
  | .vr8 => (BitVec (2 ^ 8))
  | .vr7 => (BitVec (2 ^ 8))
  | .vr6 => (BitVec (2 ^ 8))
  | .vr5 => (BitVec (2 ^ 8))
  | .vr4 => (BitVec (2 ^ 8))
  | .vr3 => (BitVec (2 ^ 8))
  | .vr2 => (BitVec (2 ^ 8))
  | .vr1 => (BitVec (2 ^ 8))
  | .vr0 => (BitVec (2 ^ 8))
  | .fcsr => (BitVec 32)
  | .f31 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f30 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f29 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f28 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f27 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f26 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f25 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f24 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f23 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f22 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f21 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f20 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f19 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f18 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f17 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f16 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f15 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f14 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f13 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f12 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f11 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f10 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f9 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f8 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f7 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f6 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f5 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f4 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f3 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f2 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f1 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .f0 => (BitVec ((if ( true  : Bool) then 8 else 4) * 8))
  | .pmpaddr_n => (Vector (BitVec 64) 64)
  | .pmpcfg_n => (Vector (BitVec 8) 64)
  | .written_event_index => (Option (Nat × event_csr))
  | .mhpmcounter => (Vector (BitVec 64) 32)
  | .mhpmevent => (Vector (BitVec 64) 32)
  | .vsip => (BitVec 64)
  | .vsie => (BitVec 64)
  | .hideleg => (BitVec 64)
  | .hedeleg => (BitVec 64)
  | .sig_msip => (BitVec 1)
  | .msip => (BitVec 32)
  | .mtime => (BitVec 64)
  | .mtimecmp => (BitVec 64)
  | .sig_ssip => (BitVec 1)
  | .sig_seip => (BitVec 1)
  | .sig_meip => (BitVec 1)
  | .mideleg => (BitVec 64)
  | .medeleg => (BitVec 64)
  | .mip => (BitVec 64)
  | .mie => (BitVec 64)
  | .hvip => (BitVec 64)
  | .sig_hgeip => (BitVec 64)
  | .hgeie => (BitVec 64)
  | .vstimecmp => (BitVec 64)
  | .stimecmp => (BitVec 64)
  | .vsatp => (BitVec 64)
  | .satp => (BitVec 64)
  | .hgatp => (BitVec 64)
  | .stval => (BitVec 64)
  | .scause => (BitVec 64)
  | .sepc => (BitVec 64)
  | .sscratch => (BitVec 64)
  | .stvec => (BitVec 64)
  | .vstval => (BitVec 64)
  | .vscause => (BitVec 64)
  | .vsepc => (BitVec 64)
  | .vsscratch => (BitVec 64)
  | .vstvec => (BitVec 64)
  | .htinst => (BitVec 64)
  | .htval => (BitVec 64)
  | .htimedelta => (BitVec 64)
  | .mtval2 => (BitVec 64)
  | .mtinst => (BitVec 64)
  | .mconfigptr => (BitVec 64)
  | .mhartid => (BitVec 64)
  | .marchid => (BitVec 64)
  | .mimpid => (BitVec 64)
  | .mvendorid => (BitVec 32)
  | .minstret_increment => Bool
  | .minstret => (BitVec 64)
  | .mcycle => (BitVec 64)
  | .mcountinhibit => (BitVec 32)
  | .mcounteren => (BitVec 32)
  | .hcounteren => (BitVec 32)
  | .scounteren => (BitVec 32)
  | .mscratch => (BitVec 64)
  | .mtval => (BitVec 64)
  | .mepc => (BitVec 64)
  | .mcause => (BitVec 64)
  | .mtvec => (BitVec 64)
  | .hstatus => (BitVec 64)
  | .cur_inst => (BitVec 64)
  | .x31 => (BitVec 64)
  | .x30 => (BitVec 64)
  | .x29 => (BitVec 64)
  | .x28 => (BitVec 64)
  | .x27 => (BitVec 64)
  | .x26 => (BitVec 64)
  | .x25 => (BitVec 64)
  | .x24 => (BitVec 64)
  | .x23 => (BitVec 64)
  | .x22 => (BitVec 64)
  | .x21 => (BitVec 64)
  | .x20 => (BitVec 64)
  | .x19 => (BitVec 64)
  | .x18 => (BitVec 64)
  | .x17 => (BitVec 64)
  | .x16 => (BitVec 64)
  | .x15 => (BitVec 64)
  | .x14 => (BitVec 64)
  | .x13 => (BitVec 64)
  | .x12 => (BitVec 64)
  | .x11 => (BitVec 64)
  | .x10 => (BitVec 64)
  | .x9 => (BitVec 64)
  | .x8 => (BitVec 64)
  | .x7 => (BitVec 64)
  | .x6 => (BitVec 64)
  | .x5 => (BitVec 64)
  | .x4 => (BitVec 64)
  | .x3 => (BitVec 64)
  | .x2 => (BitVec 64)
  | .x1 => (BitVec 64)
  | .nextPC => (BitVec 64)
  | .PC => (BitVec 64)
  | .henvcfg => (BitVec 64)
  | .menvcfg => (BitVec 64)
  | .mseccfg => (BitVec 64)
  | .senvcfg => (BitVec 64)
  | .sstateen3 => (BitVec 32)
  | .sstateen2 => (BitVec 32)
  | .sstateen1 => (BitVec 32)
  | .sstateen0 => (BitVec 32)
  | .mstateen0 => (BitVec 64)
  | .mstateen3 => (BitVec 64)
  | .mstateen2 => (BitVec 64)
  | .mstateen1 => (BitVec 64)
  | .hstateen3 => (BitVec 64)
  | .hstateen2 => (BitVec 64)
  | .hstateen1 => (BitVec 64)
  | .hstateen0 => (BitVec 64)
  | .vsstatus => (BitVec 64)
  | .mstatus => (BitVec 64)
  | .misa => (BitVec 64)
  | .cur_privilege => Privilege
  | .rvfi_mem_data_present => Bool
  | .rvfi_mem_data => (BitVec 704)
  | .rvfi_int_data_present => Bool
  | .rvfi_int_data => (BitVec 320)
  | .rvfi_pc_data => (BitVec 128)
  | .rvfi_inst_data => (BitVec 192)
  | .rvfi_instruction => (BitVec 64)
  | .fp_rounding_global => (BitVec 5)

/-- Type quantifiers: k_p : Bool -/
def not (b : Bool) : Bool :=
  (! b)

def is_implicit_access (access : (MemoryAccessType mem_payload)) : Bool :=
  match access with
  | .InstructionFetch () => true
  | .Load .PageTableEntry => true
  | .Store .PageTableEntry => true
  | _ => false

def ak_memory_access (acc : access_kind) : (MemoryAccessType mem_payload) :=
  match acc with
  | .AK_Write (_, access) => access
  | .AK_Read (_, access) => access

def ak_is_explicit (acc : access_kind) : Bool :=
  (not (is_implicit_access (ak_memory_access acc)))

def ak_is_ifetch (acc : access_kind) : Bool :=
  ((ak_memory_access acc) == (InstructionFetch ()))

def ak_is_ttw (acc : access_kind) : Bool :=
  match (ak_memory_access acc) with
  | .Load .PageTableEntry => true
  | .Store .PageTableEntry => true
  | _ => false

def ak_is_relaxed (acc : access_kind) : Bool :=
  ((ak_is_explicit acc) && (match acc with
    | .AK_Write (.Write_plain, _) => true
    | .AK_Write (.Write_RISCV_conditional, _) => true
    | .AK_Read (.Read_plain, _) => true
    | .AK_Read (.Read_RISCV_reserved, _) => true
    | _ => false : Bool))

def ak_is_rel_acq_rcsc (acc : access_kind) : Bool :=
  ((ak_is_explicit acc) && (match acc with
    | .AK_Write (.Write_RISCV_strong_release, _) => true
    | .AK_Write (.Write_RISCV_conditional_strong_release, _) => true
    | .AK_Read (.Read_RISCV_strong_acquire, _) => true
    | .AK_Read (.Read_RISCV_reserved_strong_acquire, _) => true
    | _ => false : Bool))

def ak_is_rel_acq_rcpc (acc : access_kind) : Bool :=
  ((ak_is_explicit acc) && (match acc with
    | .AK_Write (.Write_RISCV_release, _) => true
    | .AK_Write (.Write_RISCV_conditional_release, _) => true
    | .AK_Read (.Read_RISCV_acquire, _) => true
    | .AK_Read (.Read_RISCV_reserved_acquire, _) => true
    | _ => false : Bool))

def ak_is_standalone (acc : access_kind) : Bool :=
  ((ak_is_explicit acc) && (match (ak_memory_access acc) with
    | .LoadReserved _ => false
    | .StoreConditional _ => false
    | .Atomic _ => false
    | _ => true : Bool))

def ak_is_exclusive (acc : access_kind) : Bool :=
  match (ak_memory_access acc) with
  | .LoadReserved _ => true
  | .StoreConditional _ => true
  | _ => false

def ak_is_atomic_rmw (acc : access_kind) : Bool :=
  match (ak_memory_access acc) with
  | .Atomic _ => true
  | _ => false

@[reducible]
instance : Arch where
  addr_size := physaddrbits_len
  addr_space := Unit
  CHERI := false
  cap_size_log := 0
  register := Register
  register_type := RegisterType
  mem_acc := access_kind
  mem_acc_is_explicit := ak_is_explicit
  mem_acc_is_ifetch := ak_is_ifetch
  mem_acc_is_ttw := ak_is_ttw
  mem_acc_is_relaxed := ak_is_relaxed
  mem_acc_is_rel_acq_rcpc := ak_is_rel_acq_rcpc
  mem_acc_is_rel_acq_rcsc := ak_is_rel_acq_rcsc
  mem_acc_is_standalone := ak_is_standalone
  mem_acc_is_exclusive := ak_is_exclusive
  mem_acc_is_atomic_rmw := ak_is_atomic_rmw
  trans_start := Unit
  trans_end := Unit
  abort := Unit
  barrier := barrier_kind
  cache_op := Unit
  tlbi := Unit
  exn := Unit
  sys_reg_id := Unit

abbrev SailM := PreSailM exception
abbrev SailME := PreSailME exception



instance : Inhabited (RegisterRef HartState) where
  default := .Reg hart_state
instance : Inhabited (RegisterRef Privilege) where
  default := .Reg cur_privilege
instance : Inhabited (RegisterRef (BitVec 1)) where
  default := .Reg sig_meip
instance : Inhabited (RegisterRef (BitVec 128)) where
  default := .Reg rvfi_pc_data
instance : Inhabited (RegisterRef (BitVec 192)) where
  default := .Reg rvfi_inst_data
instance : Inhabited (RegisterRef (BitVec 3)) where
  default := .Reg vcsr
instance : Inhabited (RegisterRef (BitVec 32)) where
  default := .Reg sstateen0
instance : Inhabited (RegisterRef (BitVec 320)) where
  default := .Reg rvfi_int_data
instance : Inhabited (RegisterRef (BitVec 4)) where
  default := .Reg htif_payload_writes
instance : Inhabited (RegisterRef (BitVec 5)) where
  default := .Reg fp_rounding_global
instance : Inhabited (RegisterRef (BitVec 64)) where
  default := .Reg rvfi_instruction
instance : Inhabited (RegisterRef (BitVec 704)) where
  default := .Reg rvfi_mem_data
instance : Inhabited (RegisterRef (BitVec (2 ^ 8))) where
  default := .Reg vr0
instance : Inhabited (RegisterRef Bool) where
  default := .Reg rvfi_int_data_present
instance : Inhabited (RegisterRef (List PMA_Region)) where
  default := .Reg pma_regions
instance : Inhabited (RegisterRef (Option (BitVec 64))) where
  default := .Reg htif_tohost_base
instance : Inhabited (RegisterRef (Option (Nat × tdata))) where
  default := .Reg written_trigger_index
instance : Inhabited (RegisterRef (Option (Nat × event_csr))) where
  default := .Reg written_event_index
instance : Inhabited (RegisterRef (Vector Trigger 16)) where
  default := .Reg triggers
instance : Inhabited (RegisterRef (Vector (BitVec 64) 32)) where
  default := .Reg mhpmevent
instance : Inhabited (RegisterRef (Vector (BitVec 64) 64)) where
  default := .Reg pmpaddr_n
instance : Inhabited (RegisterRef (Vector (BitVec 8) 64)) where
  default := .Reg pmpcfg_n
instance : Inhabited (RegisterRef (Vector (Option TLB_Entry) (2 ^ 6))) where
  default := .Reg tlb