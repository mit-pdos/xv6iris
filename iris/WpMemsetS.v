(* WpMemsetS.v -- executing [memset]'s entry in S-mode.

   [memset(void *dst, int c, uint n)] (kernel/string.c) begins, per the proof's
   [KernelInstrs] byte map, at [KernelSyms.memset = 0x80000ccc]:

     80000ccc:  1141    addi  sp,sp,-16     <- this instruction (frame alloc)
     80000cce:  e406    sd    ra,8(sp)
     80000cd0:  e022    sd    s0,0(sp)
     80000cd2:  0800    addi  s0,sp,16
     80000cd4:  ca19    beqz  a2,...        (loop-skip when n = 0)
     ...

   The entry instruction is the compressed [c.addi sp,sp,-16] (halfword 0x1141,
   funct3 = 000 -- an ordinary C.ADDI to x2, NOT c.addi16sp).  It is register-
   only (it writes just [sp]; no memory access), so it needs no data-page Sv39
   geometry -- only the FETCH side conditions of the S-mode step engine.  We
   run it on [wp_rvc_gpr_write_s_pt] (the generic S-mode RVC gpr-write engine, the
   same one [wp_caddi16sp_gpr_s_pt] is built on), specialising the ExecuteAs base
   to the [ITYPE ADDI] expansion.

   THE THEOREM ([wp_memset_s]): from [memset]'s entry PC in S-mode -- with the
   standard kernel Sv39 fetch setup (identity superpage TLB hit at slot 5, PMP
   TOR entry 0 granting S-mode fetch over the code page) -- [memset] executes
   its first instruction, allocating its 16-byte stack frame ([sp := sp - 16])
   and advancing to [memset+2], with every ambient S-mode cell handed back to
   the continuation unchanged. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import WpGpr.
Require Import RiscvExtras.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Export WpSmodeLeafBase.
Require Import RiscvExtras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

Section WpMemsetS.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the entry halfword [c.addi sp,sp,-16], and the 4-byte fetch window it sits
     in (its own 0x1141 in the low half, the next halfword 0xe406 in the high). *)
  (* C.ADDI's 6-bit signed immediate (== -16) and destination register (== sp),
     extracted exactly as the model's decoder does (mirror of [imm_caddi] /
     [rsd_caddi] in CodeEntry). *)


  (* ---- decode: 0x1141 decodes to [C_ADDI (imm_memset0, rsd_memset0)] ---- *)

  (* ---- the [instr] fact at [memset]'s entry ---- *)
  (* The RVC arm of [instr] carries the ExecuteAs-EXPANDED base instruction:
     the entry c.addi16sp expands to [addi sp,sp,-16]. *)


  (* =================================================================== *)
  (*  Branch execute-reductions (BTYPE), from scratch against the model's  *)
  (*  [execute_BTYPE]: read rs1/rs2, compare, and either fall through      *)
  (*  (RETIRE_SUCCESS, state unchanged) or jump to PC + sext(imm).         *)
  (* =================================================================== *)

  (* register value as [rX_bits] reads it (x0 -> zero_reg). *)

  (* the comparison prefix of [execute_BTYPE] for BNE / BEQ evaluates to the
     boolean [taken], leaving the state unchanged. *)



  (* jump_to variant allowing a 2-aligned (bit1 = 1) target under the C
     extension (Zca enabled) -- for the memset loop's back-edge, whose head
     [sb] sits at a 2-aligned (not 4-aligned) address in the relocated image.
     Mirrors ProofKernelvec.kv_exec_jump_to_zca, which lives downstream of this
     file and so is re-proved locally. *)

  (* [exec_execute_JALR_ret] variant for a 2-aligned (bit1 possibly set)
     return target under the C extension: the misalignment check reduces via
     [exec_jump_to_zca] instead of requiring bit1 = 0. *)


  (* ---- bne rs1,rs2  NOT taken (rs1 == rs2): fall through to pc+4 ---- *)

  (* ---- bne rs1,rs2  TAKEN (rs1 <> rs2): jump to pc + sext(imm) ---- *)

  (* ---- beqz rs (c.beqz) NOT taken (rs <> 0): fall through to pc+2 ---- *)

  (* =================================================================== *)
  (*  Base (4-byte) register-write S-mode engine -- the [is_rvc = false]   *)
  (*  analogue of [wp_rvc_gpr_write_s_pt]: any base instruction [i] that       *)
  (*  writes ONE gpr [rd := wval].  Used for memset's [add a4,a2,a0].       *)
  (*  Extra premise: the SECOND fetch half also has fetch geometry.         *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  c.ret  (= c.jr ra = jalr x0, 0(ra)): the RETURN.  Sets nextPC := ra  *)
  (*  (low bit cleared), no register write.  JALR's execute consults        *)
  (*  currentlyEnabled Ext_Zicfilp, which in Supervisor reads menvcfg.LPE;   *)
  (*  so this runs on [wp_instr_s_config] (menvcfg value exposed).          *)
  (* =================================================================== *)

  (* Supervisor mirror of exec_cE_zicfilp_false: get_xLPE reads
     menvcfg.LPE at Supervisor (vs mseccfg.MLPE at Machine). *)


  (* =================================================================== *)
  (*  Width-1 (store-byte) low-level data-path primitives -- ports of the  *)
  (*  width-8 store primitives in WpSmodeGpr Part A with width := 1.        *)
  (*  (within_clint/sig/htif are width-generic and reused directly.)       *)
  (* =================================================================== *)


  (* width-1 split_misaligned: a 1-byte access is always aligned -> 1 chunk. *)


  (* ---- width-1 vmem_write_addr: the aligned single-byte write path ---- *)
  Section SWS1.
  Variable a : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 1)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  End SWS1.

  (* ---- width-1 register-generic vmem_write: base from rs1, byte [data] ---- *)
  Section VWgS1.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable s : mstate.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  End VWgS1.

  (* ---- width-1 register-generic STORE execute (sb): store low byte of rs2 ---- *)
  Section ExecStoreGS1.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable s : mstate.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  End ExecStoreGS1.

  (* ---- width-1 WALK mirrors: the store's data translation FILLS the TLB
     (s -> s' = set_reg s tlb tlbf); ports of WpSmodeGpr's width-8
     SWSwalk / VWgSwalk / ExecStoreGSwalk with width := 1. ---- *)
  Section SWS1walk.
  Variable a : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let pa := zero_extend' 64 (add_vec_int a (0 * 1)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  End SWS1walk.

  Section VWgS1walk.
  Variable rs1 : mword 5.
  Variable offset : mword 64.
  Variable data : bv 8.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  End VWgS1walk.

  Section ExecStoreGS1walk.
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable satp0 : mword 64.
  Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
  Variable s : mstate.
  Let s' := set_reg s tlb tlbf.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
  Let pa := zero_extend' 64 (add_vec_int a8 (0 * 1)).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 1))) (Store Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
  Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
      (uint pa) (uint (to_bits 64 1)) = PMP_Match.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 1 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 1 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 1) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.

  End ExecStoreGS1walk.


  (* =================================================================== *)
  (*  sb rs2, imm(rs1)  in S-mode: store the low byte of rs2 to the byte  *)
  (*  address ea = rs1 + sext(imm) -- a TLB HIT at tlb_hash of its vpn.    *)
  (*  Base (4-byte) instruction (wp_instr_s_config, is_rvc=false), width-1 *)
  (*  store path, single-byte points-to updated from [vold] to rs2's byte. *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  sb rs2, imm(rs1) UNIFIED over the TLB/page-table consistency        *)
  (*  invariant: the fetch case-splits inside the engine; the DATA        *)
  (*  translation case-splits here (hit: state-preserving; miss: store    *)
  (*  page-walk + fill at tlb_hash svpn, preserving the invariant).       *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  UNBUNDLED register-write engine (RVC), on wp_instr_s_config: reads   *)
  (*  cur_privilege..tlb as separate cells (not the smode_config bundle),  *)
  (*  so it composes with wp_sb_s_pt without a bundle round-trip losing the   *)
  (*  MXR/PMM facts the store needs.  Payload mirrors wp_rvc_gpr_write_s_pt.   *)
  (* =================================================================== *)


  (* ---- unbundled c.addi rd,imm (on wp_gpr_write_s_config_pt) ---- *)


  (* ---- unbundled bne rs1,rs2 NOT taken (rs1=rs2): fall to pc+4 ---- *)


  (* ---- unbundled bne rs1,rs2 TAKEN (rs1<>rs2): jump to pc+sext(imm) ---- *)


  (* ===== BEQ leaves (clones of the BNE leaves above, for wakeup's beq) ===== *)


  (* ---- unbundled BASE (4-byte) register-write engine (for `add a4`) ---- *)


  (* ---- unbundled c.beqz rs NOT taken (rs<>0): fall to pc+2 ---- *)


  (* ---- unbundled c.beqz rs TAKEN (rs=0): jump to pc+sext(imm) ---- *)

  (* ============ unbundled RVC register-write wrappers ============ *)
  (* Shared config-fact block, abbreviated in each wrapper below via a copy. *)


  (* ------------------------------------------------------------------- *)
  (*  The memset fill loop, 0xce0..0xce6:                                  *)
  (*     ce0:  sb   a1, 0(a5)        (store the fill byte at a5)           *)
  (*     ce4:  c.addi a5, a5, 1      (a5 := a5 + 1)                        *)
  (*     ce6:  bne  a5, a4, ce0      (loop while a5 <> a4)                 *)
  (*  Runs [rem] iterations, filling the [rem] pending bytes at a5..a4-1   *)
  (*  with a1's low byte, ending (bne falls through) at 0xcea with a5=a4.  *)
  (*  Proved by induction on [rem]; the whole body runs on the unbundled   *)
  (*  cell interface (wp_sb_s_pt ; wp_caddi_gpr_s_config_pt ; wp_bne_*_s_config) *)
  (*  so no smode_config round-trip loses the store's MXR/PMM facts.       *)
  (*  The per-byte Sv39/PMP geometry and the pointer arithmetic (byte j's  *)
  (*  address, a5+1 vs a4) are provided as hypotheses quantified over the  *)
  (*  byte offset; the loop-INDUCTION structure is what is proved here.    *)
  (* ------------------------------------------------------------------- *)

  (* the store's translated (identity) byte address for a5-value [cur]. *)
  Definition ms_a8 (cur : mword 64) : mword 64 :=
    sign_extend' 64 (subrange_vec_dec (add_vec cur (sign_extend' 64 (mword_of_int 0 : mword 12)))
                       (xlen - 0 - 1) 0).
  Definition ms_pa (cur : mword 64) : mword 64 :=
    zero_extend' 64 (add_vec_int (ms_a8 cur) (0 * 1)).
  (* the j-th byte's a5-value, from base [p]. *)
  Definition ms_addr (p : mword 64) (j : nat) : mword 64 :=
    add_vec p (mword_of_int (Z.of_nat j)).
  (* c.addi a5,a5,1 increments a5 by exactly one. *)
  Definition ms_incr1 : mword 64 := sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)).



  Lemma ms_addr_pa_add (p : mword 64) (j : nat) : ms_addr p j = pa_add p j.
  Proof. unfold ms_addr, pa_add, add_vec_int. reflexivity. Qed.

  (* the c.addi increment [ms_incr1] is just [1]. *)
  Lemma ms_incr1_one : ms_incr1 = (mword_of_int 1 : mword 64).
  Proof. unfold ms_incr1. apply bv_eq; vm_compute; reflexivity. Qed.

  (* pointer arithmetic: the c.addi advances the byte offset by one (any j). *)
  Lemma ms_incr_step (p : mword 64) (j : nat) :
    add_vec (ms_addr p j) ms_incr1 = ms_addr p (S j).
  Proof.
    rewrite ms_incr1_one. rewrite !ms_addr_pa_add. unfold pa_add, add_vec_int.
    apply bv_eq. rewrite !add_vec64_unsigned. rewrite !moi64_unsigned.
    rewrite Nat2Z.inj_succ.
    rewrite !bv_wrap_add_idemp_r. rewrite !bv_wrap_add_idemp_l.
    f_equal. lia.
  Qed.

  Lemma seq_cons (a b : nat) : seq a (S b) = a :: seq (S a) b.
  Proof. reflexivity. Qed.

  (* ---- c.addi rd,rd,imm on the [smode_config] bundle: thin wrapper over the
     unbundled [wp_caddi_gpr_s_config_pt] (the add preserves every config cell). *)

  (* ---- c.mv rd,rs2 (== add rd,x0,rs2) on the [smode_config] bundle. *)

  (* ---- c.addi4spn rd,sp,nzimm on the [smode_config] bundle. *)

  (* ---- c.beqz rs,imm FALL (rs <> 0): fall to pc+2, on the [smode_config] bundle. *)

  (* ---- bne rs1,rs2 FALL / TAKEN on the [smode_config] bundle: thin wrappers
     over the unbundled [wp_bne_*_s_config], peeling the config once and
     re-bundling in the continuation (the branch preserves every config cell). *)


  (* =================================================================== *)
  (*  memset SUFFIX, 0xcea..0xcf0: restore ra/s0 from the frame, pop it,   *)
  (*  and return.                                                          *)
  (*     cea: c.ldsp ra,8(sp)   cec: c.ldsp s0,0(sp)                        *)
  (*     cee: c.addi sp,16      cf0: ret (c.jr ra)                          *)
  (*  Ends with PC at the saved return address ra0 (low bit cleared), with *)
  (*  ra=ra0 and s0=s00 restored from the two 8-byte frame slots (held at   *)
  (*  fraction dqm, returned to the caller unchanged).                     *)
  (* =================================================================== *)

  (* ===== smode_config leaf wrappers (local, for the memset sequencers) ===== *)


  (* =================================================================== *)
  (*  memset PREFIX, 0xccc..0xcdc: set up the frame and the loop bounds.   *)
  (*     ccc: c.addi sp,-16        cce: c.sdsp ra,8(sp)                     *)
  (*     cd0: c.sdsp s0,0(sp)      cd2: c.addi4spn s0,sp,16                 *)
  (*     cd4: c.beqz a2,cea (n<>0, fall through)                            *)
  (*     cd6: c.mv a5,a0           cd8: c.slli a2,32                        *)
  (*     cda: c.srli a2,32         cdc: add a4,a2,a0                        *)
  (*  Ends at the loop top 0xce0 with sp=sp', ra/s0 saved on the frame,     *)
  (*  s0=sp0, a5=a0 (dst), a2=zext32(count), a4=a2+a0 (end pointer).        *)
  (*  Registers: ra=x1 sp=x2 s0=x8 a0=x10 a1=x11 a2=x12 a4=x14 a5=x15.      *)
  (* =================================================================== *)


  (* =================================================================== *)
  (*  memset with a ZERO byte count (n = 0): prologue (0xccc..0xcd2) then  *)
  (*  the TAKEN c.beqz at 0xcd4 jumps straight to the epilogue at          *)
  (*  memset+0x1e, skipping the loop.  ra/s0 are saved on the frame (to    *)
  (*  be restored by the suffix); a2/a4/a5 are left untouched (m2).        *)
  (* =================================================================== *)


End WpMemsetS.
