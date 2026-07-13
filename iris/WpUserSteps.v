(* WpUserSteps.v -- the classification [ustep_case], its dispatch, and wp_user_exec_v1.
   Split from the monolithic WpUserExec.v; all lemmas close over the
   single parameter bundle [uctx] (see WpUserBase).                      *)
(* WpUserExec.v -- the user-execution theorem: the loop frames and the
   Löb skeleton.

   [user_frame] is the loop invariant P of [wp_user_loop]: an ARBITRARY
   user machine -- existential GPRs, pc, trap CSRs, TLB (consistent with
   the page-table spec) -- over the loop-constant configuration (the
   [user_cfg] cells, the page-table ownership [upt_inv], the persistent
   user code bytes, and the writable user data bytes).

   [user_trap_frame] is Tr: the same machine handed to the kernel
   re-entry continuation -- Supervisor privilege, pc at stvec's direct
   base, trap CSRs written (existential here; refined per-cause by the
   USTEP cases that produce it).

   [wp_user_exec] is the Löb capstone: one USTEP obligation -- a single
   machine step from [user_frame] re-establishes [user_frame] (retire)
   or produces [user_trap_frame] (trap), with both continuations under a
   later -- runs arbitrary user code forever.  The USTEP obligation is
   discharged case by case in the companion files (fetch trichotomy x
   decode totality x execute families); the proven instances so far are
   the wp_user_ecall / wp_user_fetch_pagefault vertical slices.        *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv WpGpr.
Require Import WpDecodeBridge.
Require Import UmodeFetch UmodeEcall.
Require Import UptInv WpUserEcall WpMemsetS WpGprStore.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase.
Require Import WpUserFetch.
Require Import WpUserCompute.
Require Import WpUserCtrl.
Require Import WpUserComputeC.
Require Import WpUserTrap.
Require Import WpUserMem.
Require Import WpUserMemC.
Require Import WpUserMem4.
Require Import WpUserMemC4.

Section WpUserSteps.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation stvec_v := (WpUserBase.stvec_v U).
  Local Notation mie_v := (WpUserBase.mie_v U).
  Local Notation midl_v := (WpUserBase.midl_v U).
  Local Notation medl_v := (WpUserBase.medl_v U).
  Local Notation mip_v := (WpUserBase.mip_v U).
  Local Notation meip := (WpUserBase.meip U).
  Local Notation seip := (WpUserBase.seip U).
  Local Notation satp0 := (WpUserBase.satp0 U).
  Local Notation root := (WpUserBase.root U).
  Local Notation slots := (WpUserBase.slots U).
  Local Notation spec := (WpUserBase.spec U).
  Local Notation pmpcfg0 := (WpUserBase.pmpcfg0 U).
  Local Notation pmpaddr00 := (WpUserBase.pmpaddr00 U).
  Local Notation code := (WpUserBase.code U).
  Local Notation data := (WpUserBase.data U).
  Local Notation dq := (WpUserBase.dq U).
  Local Notation dqc := (WpUserBase.dqc U).
  Local Notation Hmm := (WpUserBase.Hmm U).
  Local Notation Hs0 := (WpUserBase.Hs0 U).
  Local Notation Hsatpmode := (WpUserBase.Hsatpmode U).
  Local Notation Hasid := (WpUserBase.Hasid U).
  Local Notation Hroot := (WpUserBase.Hroot U).
  Local Notation Htvd := (WpUserBase.Htvd U).
  Local Notation Hdel_ecall := (WpUserBase.Hdel_ecall U).
  Local Notation Hdel_fetchpf := (WpUserBase.Hdel_fetchpf U).
  Local Notation Hdel_loadpf := (WpUserBase.Hdel_loadpf U).
  Local Notation Hdel_samopf := (WpUserBase.Hdel_samopf U).
  Local Notation Hdel_illegal := (WpUserBase.Hdel_illegal U).
  Local Notation Hdel_break := (WpUserBase.Hdel_break U).
  Local Notation HpmpA := (WpUserBase.HpmpA U).
  Local Notation Hpmp_ord := (WpUserBase.Hpmp_ord U).
  Local Notation HpmpX := (WpUserBase.HpmpX U).
  Local Notation HpmpR := (WpUserBase.HpmpR U).
  Local Notation HpmpW := (WpUserBase.HpmpW U).
  Local Notation Hpmp_cov := (WpUserBase.Hpmp_cov U).
  Local Notation Hpter := (WpUserBase.Hpter U).
  Local Notation Hspec := (WpUserBase.Hspec U).
  Local Notation user_frame := (WpUserBase.user_frame U).
  Local Notation user_trap_frame := (WpUserBase.user_trap_frame U).
  Local Notation user_step_obligation := (WpUserBase.user_step_obligation U).
  Local Notation wp_user_exec := (WpUserBase.wp_user_exec U).
  Local Notation ustep_branch_fall := (WpUserCtrl.ustep_branch_fall U).
  Local Notation ustep_branch_taken := (WpUserCtrl.ustep_branch_taken U).
  Local Notation ustep_c_branch_fall := (WpUserCtrl.ustep_c_branch_fall U).
  Local Notation ustep_c_branch_taken := (WpUserCtrl.ustep_c_branch_taken U).
  Local Notation ustep_c_compute1 := (WpUserComputeC.ustep_c_compute1 U).
  Local Notation ustep_c_compute1_direct := (WpUserComputeC.ustep_c_compute1_direct U).
  Local Notation ustep_c_ebreak := (WpUserTrap.ustep_c_ebreak U).
  Local Notation ustep_c_illegal := (WpUserTrap.ustep_c_illegal U).
  Local Notation ustep_c_ld_code := (WpUserMemC.ustep_c_ld_code U).
  Local Notation ustep_c_itype := (WpUserComputeC.ustep_c_itype U).
  Local Notation ustep_c_jal := (WpUserCtrl.ustep_c_jal U).
  Local Notation ustep_c_jalr := (WpUserCtrl.ustep_c_jalr U).
  Local Notation ustep_c_mul := (WpUserComputeC.ustep_c_mul U).
  Local Notation ustep_c_nop := (WpUserComputeC.ustep_c_nop U).
  Local Notation ustep_c_rtype := (WpUserComputeC.ustep_c_rtype U).
  Local Notation ustep_c_rtype2 := (WpUserComputeC.ustep_c_rtype2 U).
  Local Notation ustep_c_rtypew := (WpUserComputeC.ustep_c_rtypew U).
  Local Notation ustep_c_shiftiop := (WpUserComputeC.ustep_c_shiftiop U).
  Local Notation ustep_c_utype := (WpUserComputeC.ustep_c_utype U).
  Local Notation ustep_compute1 := (WpUserCompute.ustep_compute1 U).
  Local Notation ustep_ebreak := (WpUserTrap.ustep_ebreak U).
  Local Notation ustep_ecall := (WpUserTrap.ustep_ecall U).
  Local Notation ustep_fetch_adfault_hit := (WpUserFetch.ustep_fetch_adfault_hit U).
  Local Notation ustep_fetch_noncanonical := (WpUserFetch.ustep_fetch_noncanonical U).
  Local Notation ustep_fetch_unmapped := (WpUserFetch.ustep_fetch_unmapped U).
  Local Notation ustep_illegal := (WpUserTrap.ustep_illegal U).
  Local Notation ustep_illegal_st := (WpUserTrap.ustep_illegal_st U).
  Local Notation ustep_itype := (WpUserCompute.ustep_itype U).
  Local Notation ustep_jal := (WpUserCtrl.ustep_jal U).
  Local Notation ustep_jalr := (WpUserCtrl.ustep_jalr U).
  Local Notation ustep_ld_code := (WpUserMem.ustep_ld_code U).
  Local Notation ustep_lw_code := (WpUserMem4.ustep_lw_code U).
  Local Notation ustep_c_lw_code := (WpUserMemC4.ustep_c_lw_code U).
  Local Notation ustep_mul := (WpUserCompute.ustep_mul U).
  Local Notation ustep_nop := (WpUserCompute.ustep_nop U).
  Local Notation ustep_rtype := (WpUserCompute.ustep_rtype U).
  Local Notation ustep_rtype2 := (WpUserCompute.ustep_rtype2 U).
  Local Notation ustep_rtypew := (WpUserCompute.ustep_rtypew U).
  Local Notation ustep_shiftiop := (WpUserCompute.ustep_shiftiop U).
  Local Notation ustep_utype := (WpUserCompute.ustep_utype U).


  (* the two compressed fetch modes, as one pure predicate (definitionally
     transparent -- the ustep_c_* arms take the raw disjunction) *)
  Definition c_fetch_mode (va : mword 64) (vpn : mword 27) (i : uwalk_info)
      (h : mword 16) : Prop :=
    (exists w4 : mword 32,
        is_aligned_vaddr (Virtaddr va) 4 = true /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
        (forall j : nat, (j < 4)%nat ->
           code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w4 j)) /\
        h = subrange_vec_dec w4 15 0)
    \/ (neq_vec (access_vec_dec va 0) ('b"0") = false /\
        neq_vec (access_vec_dec va 1) ('b"0") = true /\
        is_aligned_vaddr (Virtaddr va) 4 = false /\
        is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 2 = true /\
        (forall j : nat, (j < 2)%nat ->
           code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte h j))).


  Definition ustep_case (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
    (* 1: non-canonical pc *)
    (is_aligned_vaddr (Virtaddr va) 4 = true /\
     neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true)
    \/
    (* 2: canonical, but the pc's vpn is unmapped / kernel-only *)
    (exists vpn,
       spec !! vpn = None /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn)
    \/
    (* 3: mapped, TLB hit, but the leaf needs an A update (ADUE = 0) *)
    (exists vpn i pte',
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = Some pte' /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn)
    \/
    (* 4: fetch succeeds via a hit and the word is ECALL *)
    (exists vpn i,
       spec !! vpn = Some i /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte ecall_w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true)
    \/
    (* 5: fetch succeeds via a hit and the word retires as an ITYPE op *)
    (exists vpn i (w : mword 32) (op : iop)
            (f : mword 64 -> mword 12 -> mword 64)
            (imm : mword 12) (rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (ITYPE (imm, Regidx rs1, Regidx rd, op), s0)) /\
       uint rd <> 0 /\
       (forall (rs1' rd' : mword 5) (imm' : mword 12) s,
          exec (execute (ITYPE (imm', Regidx rs1', Regidx rd', op))) s
          = Some (RETIRE_SUCCESS,
                  if Z.eqb (uint rd') 0 then s
                  else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                         (regval_into_reg
                            (f (if Z.eqb (uint rs1') 0 then zero_reg
                                else register_lookup
                                       (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                               imm')))))
    \/
    (* 6: fetch hit, retiring RTYPE (register-register) op *)
    (exists vpn i (w : mword 32) (op : rop)
            (f : mword 64 -> mword 64 -> mword 64)
            (rs2 rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) /\
       uint rd <> 0 /\
       (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
          exec (execute (RTYPE (Regidx rs2', Regidx rs1', Regidx rd', op))) s
          = Some (RETIRE_SUCCESS,
                  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                    (regval_into_reg
                       (f (if Z.eqb (uint rs1') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                          (if Z.eqb (uint rs2') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))))
    \/
    (* 7: fetch hit, retiring UTYPE (LUI/AUIPC) op *)
    (exists vpn i (w : mword 32) (op : uop)
            (V : mword 20 -> mstate -> mword 64) (v : mword 64)
            (imm : mword 20) (rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (UTYPE (imm, Regidx rd, op), s0)) /\
       uint rd <> 0 /\
       (forall s', register_lookup PC s'.(sregs) = va -> V imm s' = v) /\
       (forall (rd' : mword 5) (imm' : mword 20) s,
          exec (execute (UTYPE (imm', Regidx rd', op))) s
          = Some (RETIRE_SUCCESS,
                  if Z.eqb (uint rd') 0 then s
                  else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                         (regval_into_reg (V imm' s)))))
    \/
    (* 8: fetch hit, retiring SHIFTIOP (SLLI/SRLI/SRAI) op *)
    (exists vpn i (w : mword 32) (op : sop)
            (f : mword 64 -> mword 6 -> mword 64)
            (shamt : mword 6) (rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op), s0)) /\
       uint rd <> 0 /\
       (forall (rs1' rd' : mword 5) (shamt' : mword 6) s,
          exec (execute (SHIFTIOP (shamt', Regidx rs1', Regidx rd', op))) s
          = Some (RETIRE_SUCCESS,
                  if Z.eqb (uint rd') 0 then s
                  else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                         (regval_into_reg
                            (f (if Z.eqb (uint rs1') 0 then zero_reg
                                else register_lookup
                                       (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                               shamt')))))
    \/
    (* 9: fetch hit, retiring JAL (aligned target) *)
    (exists vpn i (w : mword 32) (imm : mword 21) (rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (JAL (imm, Regidx rd), s0)) /\
       uint rd <> 0 /\
       eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true /\
       bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false)
    \/
    (* 10: fetch hit, retiring JALR (aligned target from rs1) *)
    (exists vpn i (w : mword 32) (imm : mword 12) (rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (JALR (imm, Regidx rs1, Regidx rd), s0)) /\
       uint rd <> 0 /\
       eq_vec (access_vec_dec (jalr_target (g !!! Regidx rs1) imm) 0) ('b"0") = true /\
       bit_to_bool (access_vec_dec (jalr_target (g !!! Regidx rs1) imm) 1) = false)
    \/
    (* 11: fetch hit, a no-state-change retiring instruction (NOP-like) *)
    (exists vpn i (w : mword 32) (ii : instruction),
       (forall s, exec (execute ii) s = Some (RETIRE_SUCCESS, s)) /\
       is_lpad_instruction ii = false /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (ii, s0)))
    \/
    (* 12: fetch hit, the decoded instruction is ILLEGAL in this state -> trap *)
    (exists vpn i (w : mword 32) (ii : instruction),
       (forall s, exec (execute ii) s = Some (Illegal_Instruction tt, s)) /\
       is_lpad_instruction ii = false /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (ii, s0)))
    \/
    (* 13: fetch hit, BTYPE branch NOT taken (falls through to pc+4) *)
    (exists vpn i (w : mword 32) (op : bop) (c : mword 64 -> mword 64 -> bool)
            (imm : mword 13) (rs2 rs1 : mword 5),
       (forall (imm' : mword 13) (rs2' rs1' : mword 5) s,
          c (rvv rs1' s) (rvv rs2' s) = false ->
          exec (execute (BTYPE (imm', Regidx rs2', Regidx rs1', op))) s
            = Some (RETIRE_SUCCESS, s)) /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (BTYPE (imm, Regidx rs2, Regidx rs1, op), s0)) /\
       c (g !!! Regidx rs1) (g !!! Regidx rs2) = false)
    \/
    (* 14: fetch hit, BTYPE branch TAKEN (aligned target) *)
    (exists vpn i (w : mword 32) (op : bop) (c : mword 64 -> mword 64 -> bool)
            (imm : mword 13) (rs2 rs1 : mword 5),
       (forall (imm' : mword 13) (rs2' rs1' : mword 5) s,
          c (rvv rs1' s) (rvv rs2' s) = true ->
          eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs))
                    (sign_extend' 64 imm')) 0) ('b"0") = true ->
          bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs))
                    (sign_extend' 64 imm')) 1) = false ->
          exec (execute (BTYPE (imm', Regidx rs2', Regidx rs1', op))) s
            = Some (RETIRE_SUCCESS,
                    set_reg s nextPC (add_vec (register_lookup PC s.(sregs))
                                        (sign_extend' 64 imm')))) /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (BTYPE (imm, Regidx rs2, Regidx rs1, op), s0)) /\
       c (g !!! Regidx rs1) (g !!! Regidx rs2) = true /\
       eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true /\
       bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false)
    \/
    (* 15: fetch hit, single-source compute (ADDIW etc.) *)
    (exists vpn i (w : mword 32) (mk : mword 5 -> mword 5 -> instruction)
            (F : mword 64 -> mword 64) (rs1 rd : mword 5),
       (forall (rs1' rd' : mword 5) s,
          exec (execute (mk rs1' rd')) s
          = Some (RETIRE_SUCCESS,
                  if Z.eqb (uint rd') 0 then s
                  else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                         (regval_into_reg
                            (F (if Z.eqb (uint rs1') 0 then zero_reg
                                else register_lookup
                                       (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs)))))) /\
       is_lpad_instruction (mk rs1 rd) = false /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (mk rs1 rd, s0)) /\
       uint rd <> 0)
    \/
    (* 16: fetch hit, retiring 8-byte LOAD from a code page *)
    (exists vpn i vpnD ieD (w : mword 32) (imm : mword 12) (rs1 rd : mword 5) (v : mword 64),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), s0)) /\
       uint rd <> 0 /\
       spec !! vpnD = Some ieD /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) /\
       uw_check_ok (Load Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 8 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 8 = true /\
       (forall j : nat, (j < 8)%nat -> code !! pa_add paD j = Some (nth_byte v j)))
    \/
    (* 17: RVC fetch hit, compressed expanding to a retiring ITYPE op *)
    (exists vpn i (h : mword 16) (ii : instruction) (op : iop)
            (f : mword 64 -> mword 12 -> mword 64)
            (imm : mword 12) (rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (ITYPE (imm, Regidx rs1, Regidx rd, op)), s)) /\
       uint rd <> 0 /\
       (forall (rs1' rd' : mword 5) (imm' : mword 12) s,
          exec (execute (ITYPE (imm', Regidx rs1', Regidx rd', op))) s
          = Some (RETIRE_SUCCESS,
                  if Z.eqb (uint rd') 0 then s
                  else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                         (regval_into_reg
                            (f (if Z.eqb (uint rs1') 0 then zero_reg
                                else register_lookup
                                       (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                               imm')))))
    \/
    (* 18: RVC fetch hit, compressed expanding to a retiring RTYPE op *)
    (exists vpn i (h : mword 16) (ii : instruction) (op : rop)
            (f : mword 64 -> mword 64 -> mword 64)
            (rs2 rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, op)), s)) /\
       uint rd <> 0 /\
       (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
          exec (execute (RTYPE (Regidx rs2', Regidx rs1', Regidx rd', op))) s
          = Some (RETIRE_SUCCESS,
                  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                    (regval_into_reg
                       (f (if Z.eqb (uint rs1') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                          (if Z.eqb (uint rs2') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))))
    \/
    (* 19: RVC fetch hit, compressed expanding to a retiring UTYPE op *)
    (exists vpn i (h : mword 16) (ii : instruction) (op : uop)
            (V : mword 20 -> mstate -> mword 64) (v : mword 64)
            (imm : mword 20) (rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (UTYPE (imm, Regidx rd, op)), s)) /\
       uint rd <> 0 /\
       (forall s', register_lookup PC s'.(sregs) = va -> V imm s' = v) /\
       (forall (rd' : mword 5) (imm' : mword 20) s,
          exec (execute (UTYPE (imm', Regidx rd', op))) s
          = Some (RETIRE_SUCCESS,
                  if Z.eqb (uint rd') 0 then s
                  else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                         (regval_into_reg (V imm' s)))))
    \/
    (* 20: RVC fetch hit, compressed expanding to a retiring SHIFTIOP op *)
    (exists vpn i (h : mword 16) (ii : instruction) (op : sop)
            (f : mword 64 -> mword 6 -> mword 64)
            (shamt : mword 6) (rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (SHIFTIOP (shamt, Regidx rs1, Regidx rd, op)), s)) /\
       uint rd <> 0 /\
       (forall (rs1' rd' : mword 5) (shamt' : mword 6) s,
          exec (execute (SHIFTIOP (shamt', Regidx rs1', Regidx rd', op))) s
          = Some (RETIRE_SUCCESS,
                  if Z.eqb (uint rd') 0 then s
                  else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                         (regval_into_reg
                            (f (if Z.eqb (uint rs1') 0 then zero_reg
                                else register_lookup
                                       (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                               shamt')))))
    \/
    (* 21: RVC fetch hit, compressed expanding to a single-source compute *)
    (exists vpn i (h : mword 16) (ii : instruction)
            (mk : mword 5 -> mword 5 -> instruction)
            (F : mword 64 -> mword 64) (rs1 rd : mword 5),
       (forall (rs1' rd' : mword 5) s,
          exec (execute (mk rs1' rd')) s
          = Some (RETIRE_SUCCESS,
                  if Z.eqb (uint rd') 0 then s
                  else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                         (regval_into_reg
                            (F (if Z.eqb (uint rs1') 0 then zero_reg
                                else register_lookup
                                       (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs)))))) /\
       is_lpad_instruction (mk rs1 rd) = false /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (mk rs1 rd), s)) /\
       uint rd <> 0)
    \/
    (* 22: RVC fetch hit, compressed expanding to JAL (aligned target) *)
    (exists vpn i (h : mword 16) (ii : instruction) (imm : mword 21) (rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (JAL (imm, Regidx rd)), s)) /\
       uint rd <> 0 /\
       eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true /\
       bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false)
    \/
    (* 23: RVC fetch hit, compressed expanding to JALR (aligned target) *)
    (exists vpn i (h : mword 16) (ii : instruction) (imm : mword 12) (rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (JALR (imm, Regidx rs1, Regidx rd)), s)) /\
       uint rd <> 0 /\
       eq_vec (access_vec_dec (jalr_target (g !!! Regidx rs1) imm) 0) ('b"0") = true /\
       bit_to_bool (access_vec_dec (jalr_target (g !!! Regidx rs1) imm) 1) = false)
    \/
    (* 24: RVC fetch hit, compressed BTYPE expansion, branch NOT taken *)
    (exists vpn i (h : mword 16) (ii : instruction) (op : bop)
            (c : mword 64 -> mword 64 -> bool)
            (imm : mword 13) (rs2 rs1 : mword 5),
       (forall (imm' : mword 13) (rs2' rs1' : mword 5) s,
          c (rvv rs1' s) (rvv rs2' s) = false ->
          exec (execute (BTYPE (imm', Regidx rs2', Regidx rs1', op))) s
            = Some (RETIRE_SUCCESS, s)) /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (BTYPE (imm, Regidx rs2, Regidx rs1, op)), s)) /\
       c (g !!! Regidx rs1) (g !!! Regidx rs2) = false)
    \/
    (* 25: RVC fetch hit, compressed BTYPE expansion, branch TAKEN *)
    (exists vpn i (h : mword 16) (ii : instruction) (op : bop)
            (c : mword 64 -> mword 64 -> bool)
            (imm : mword 13) (rs2 rs1 : mword 5),
       (forall (imm' : mword 13) (rs2' rs1' : mword 5) s,
          c (rvv rs1' s) (rvv rs2' s) = true ->
          eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs))
                    (sign_extend' 64 imm')) 0) ('b"0") = true ->
          bit_to_bool (access_vec_dec (add_vec (register_lookup PC s.(sregs))
                    (sign_extend' 64 imm')) 1) = false ->
          exec (execute (BTYPE (imm', Regidx rs2', Regidx rs1', op))) s
            = Some (RETIRE_SUCCESS,
                    set_reg s nextPC (add_vec (register_lookup PC s.(sregs))
                                        (sign_extend' 64 imm')))) /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (BTYPE (imm, Regidx rs2, Regidx rs1, op)), s)) /\
       c (g !!! Regidx rs1) (g !!! Regidx rs2) = true /\
       eq_vec (access_vec_dec (add_vec va (sign_extend' 64 imm)) 0) ('b"0") = true /\
       bit_to_bool (access_vec_dec (add_vec va (sign_extend' 64 imm)) 1) = false)
    \/
    (* 26: RVC fetch hit, a no-state-change retiring compressed instruction *)
    (exists vpn i (h : mword 16) (ii : instruction),
       (forall s, exec (execute ii) s = Some (RETIRE_SUCCESS, s)) /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)))
    \/
    (* 27: RVC fetch hit, the compressed instruction is ILLEGAL -> trap *)
    (exists vpn i (h : mword 16) (ii : instruction),
       (forall s, exec (execute ii) s = Some (Illegal_Instruction tt, s)) /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)))
    \/
    (* 28: RVC fetch hit, DIRECT compressed single-source compute (C_NOT etc.) *)
    (exists vpn i (h : mword 16) (ii : instruction)
            (F : mword 64 -> mword 64) (rs1 rd : mword 5),
       (forall s,
          exec (execute ii) s
          = Some (RETIRE_SUCCESS,
                  if Z.eqb (uint rd) 0 then s
                  else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                         (regval_into_reg
                            (F (if Z.eqb (uint rs1) 0 then zero_reg
                                else register_lookup
                                       (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))))) /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       uint rd <> 0)
    \/
    (* 29: fetch hit, retiring RTYPEW (W-compute register-register) op *)
    (exists vpn i (w : mword 32) (op : ropw)
            (f : mword 64 -> mword 64 -> mword 64)
            (rs2 rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op), s0)) /\
       uint rd <> 0 /\
       (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
          exec (execute (RTYPEW (Regidx rs2', Regidx rs1', Regidx rd', op))) s
          = Some (RETIRE_SUCCESS,
                  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                    (regval_into_reg
                       (f (if Z.eqb (uint rs1') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                          (if Z.eqb (uint rs2') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))))
    \/
    (* 30: fetch hit, retiring MUL *)
    (exists vpn i (w : mword 32) (mulop : mul_op)
            (f : mword 64 -> mword 64 -> mword 64)
            (rs2 rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop), s0)) /\
       uint rd <> 0 /\
       (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
          exec (execute (MUL (Regidx rs2', Regidx rs1', Regidx rd', mulop))) s
          = Some (RETIRE_SUCCESS,
                  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                    (regval_into_reg
                       (f (if Z.eqb (uint rs1') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                          (if Z.eqb (uint rs2') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))))
    \/
    (* 31: RVC fetch hit, compressed expanding to a retiring RTYPEW op *)
    (exists vpn i (h : mword 16) (ii : instruction) (op : ropw)
            (f : mword 64 -> mword 64 -> mword 64)
            (rs2 rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, op)), s)) /\
       uint rd <> 0 /\
       (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
          exec (execute (RTYPEW (Regidx rs2', Regidx rs1', Regidx rd', op))) s
          = Some (RETIRE_SUCCESS,
                  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                    (regval_into_reg
                       (f (if Z.eqb (uint rs1') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                          (if Z.eqb (uint rs2') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))))
    \/
    (* 32: RVC fetch hit, compressed expanding to a retiring MUL *)
    (exists vpn i (h : mword 16) (ii : instruction) (mulop : mul_op)
            (f : mword 64 -> mword 64 -> mword 64)
            (rs2 rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop)), s)) /\
       uint rd <> 0 /\
       (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
          exec (execute (MUL (Regidx rs2', Regidx rs1', Regidx rd', mulop))) s
          = Some (RETIRE_SUCCESS,
                  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                    (regval_into_reg
                       (f (if Z.eqb (uint rs1') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                          (if Z.eqb (uint rs2') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))))
    \/
    (* 33: fetch hit, GENERIC retiring two-source compute (MULW/DIV/REM/...) *)
    (exists vpn i (w : mword 32) (mk2 : mword 5 -> mword 5 -> mword 5 -> instruction)
            (f : mword 64 -> mword 64 -> mword 64)
            (rs2 rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (mk2 rs2 rs1 rd, s0)) /\
       uint rd <> 0 /\
       (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
          exec (execute (mk2 rs2' rs1' rd')) s
          = Some (RETIRE_SUCCESS,
                  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                    (regval_into_reg
                       (f (if Z.eqb (uint rs1') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                          (if Z.eqb (uint rs2') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))) /\
       is_lpad_instruction (mk2 rs2 rs1 rd) = false)
    \/
    (* 34: RVC fetch hit, compressed expanding to a two-source compute *)
    (exists vpn i (h : mword 16) (ii : instruction) (mk2 : mword 5 -> mword 5 -> mword 5 -> instruction)
            (f : mword 64 -> mword 64 -> mword 64)
            (rs2 rs1 rd : mword 5),
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (mk2 rs2 rs1 rd), s)) /\
       uint rd <> 0 /\
       (forall (rs2' rs1' rd' : mword 5) s, uint rd' <> 0 ->
          exec (execute (mk2 rs2' rs1' rd')) s
          = Some (RETIRE_SUCCESS,
                  set_reg s (R_bitvector_64 (gpr_of_Z (uint rd')))
                    (regval_into_reg
                       (f (if Z.eqb (uint rs1') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs1'))) s.(sregs))
                          (if Z.eqb (uint rs2') 0 then zero_reg
                           else register_lookup
                                  (R_bitvector_64 (gpr_of_Z (uint rs2'))) s.(sregs)))))))
    \/
    (* 35: fetch hit, the instruction traps to a software BREAKPOINT *)
    (exists vpn i (w : mword 32) (ii : instruction),
       (forall s, register_lookup cur_privilege s.(sregs) = User ->
          register_lookup PC s.(sregs) = va ->
          exec (execute ii) s
            = Some (rv64d_types.Trap (User, make_sync_exception (E_Breakpoint Brk_Software) va, va), s)) /\
       is_lpad_instruction ii = false /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (ii, s0)))
    \/
    (* 36: RVC fetch hit, compressed expanding to a software BREAKPOINT trap *)
    (exists vpn i (h : mword 16) (ii : instruction),
       (forall s : mstate, exec (execute ii) s = Some (ExecuteAs (EBREAK tt), s)) /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)))
    \/
    (* 37: fetch hit, the instruction is illegal IN USER MODE (privileged family) *)
    (exists vpn i (w : mword 32) (ii : instruction),
       (forall s, register_lookup cur_privilege s.(sregs) = User ->
          exec (execute ii) s = Some (Illegal_Instruction tt, s)) /\
       is_lpad_instruction ii = false /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (ii, s0)))
    \/
    (* 38: RVC fetch hit, compressed expanding to an 8-byte LOAD from a code page *)
    (exists vpn i vpnD ieD (h : mword 16) (ii : instruction) (imm : mword 12) (rs1 rd : mword 5) (v : mword 64),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)), s)) /\
       uint rd <> 0 /\
       spec !! vpnD = Some ieD /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) /\
       uw_check_ok (Load Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 8 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 8 = true /\
       (forall j : nat, (j < 8)%nat -> code !! pa_add paD j = Some (nth_byte v j)))
    \/
    (* 39: fetch hit, retiring width-4 LW/LWU from a code page *)
    (exists vpn i vpnD ieD (w : mword 32) (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool) (v : mword 32),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn i) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn i) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) /\
       uint rd <> 0 /\
       spec !! vpnD = Some ieD /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) /\
       uw_check_ok (Load Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 4 = true /\
       (forall j : nat, (j < 4)%nat -> code !! pa_add paD j = Some (nth_byte v j)))
    \/
    (* 40: RVC fetch hit, compressed expanding to a width-4 C_LW from a code page *)
    (exists vpn i vpnD ieD (h : mword 16) (ii : instruction) (imm : mword 12) (rs1 rd : mword 5) (v : mword 32),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn i) /\
       uw_check_ok (InstructionFetch tt) i /\
       update_PTE_Bits (uw_pte0 i) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 i)) = ('b"00" : mword 2) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       c_fetch_mode va vpn i h /\
       isRVC h = true /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode_compressed h) s0 = Some (ii, s0)) /\
       (forall s : mstate, exec (execute ii) s
          = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 4)), s)) /\
       uint rd <> 0 /\
       spec !! vpnD = Some ieD /\
       vec_access_dec tlbvec (tlb_hash (__id 39) vpnD) = Some (upt_entry vpnD ieD) /\
       uw_check_ok (Load Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 4 = true /\
       (forall j : nat, (j < 4)%nat -> code !! pa_add paD j = Some (nth_byte v j))).

  (* the assembled Löb step obligation, v1 coverage *)
  Theorem user_step_holds E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_fault_wf root slots spec ->
    (forall (va ms_v : mword 64) (g : gmap regidx (mword 64))
            (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
        upt_tlb_ok spec tlbvec ->
        _get_Mstatus_SXL ms_v = 'b"10" ->
        ustep_case va ms_v g tlbvec) ->
    hw_config -∗ minstret_inv -∗ user_step_obligation E Φ.
  Proof.
    intros HN Hfwf Hclass.
    iIntros "#Hhw #Hinv".
    rewrite /user_step_obligation.
    iIntros "!> HP Hk".
    rewrite {1}/user_frame.
    iDestruct "HP" as (ms_v sc_v stval_v sepc_v va g tlbvec)
      "(%HSXL & %Hok & Hhs & Hpriv & Hms & Hsc & Hstv & Hsepc & Htlbc & Hpc &
        Hgpr & Hupt & #Hcode & Hdata & Hcfg)".
    destruct (Hclass va ms_v g tlbvec Hok HSXL) as
      [ (Hval & Hcanon)
      | [ (vpn & Hvpn & Hval & Hcanon & Hvpn_def)
        | [ (vpn & i & pte' & Hvec & Hchk & Hupd & Hval & Hcanon & Hvpn_def)
          | [ (vpn & i & Hsome & Hvec & Hchk & Hupd & Hcw & Hval & Hcanon & Hvpn_def & Hpaal)
            | [ (vpn & i & w & op & f & imm & rs1 & rd & Hvec & Hchk & Hupd & Hpbmt &
                 Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & Hexec_op)
              | [ (vpn & i & w & op & f & rs2 & rs1 & rd & Hvec & Hchk & Hupd & Hpbmt &
                   Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & Hexec_op)
                | [ (vpn & i & w & op & V & v & imm & rd & Hvec & Hchk & Hupd & Hpbmt &
                     Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & HVeq & Hexec_op)
                  | [ (vpn & i & w & op & f & shamt & rs1 & rd & Hvec & Hchk & Hupd & Hpbmt &
                       Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & Hexec_op)
                    | [ (vpn & i & w & imm & rd & Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval &
                         Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & Halign0 & Halign1)
                      | [ (vpn & i & w & imm & rs1 & rd & Hvec & Hchk & Hupd & Hpbmt & Hcw & Hval &
                           Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & Halign0 & Halign1)
                        | [ (vpn & i & w & ii & Hexec_op & Hlpad & Hvec & Hchk & Hupd & Hpbmt & Hcw &
                             Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec)
                          | [ (vpn & i & w & ii & Hexec_op & Hlpad & Hvec & Hchk & Hupd & Hpbmt & Hcw &
                               Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec)
                            | [ (vpn & i & w & op & c & imm & rs2 & rs1 & Hexec_op & Hvec & Hchk & Hupd &
                                 Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hcfalse)
                              | [ (vpn & i & w & op & c & imm & rs2 & rs1 & Hexec_op & Hvec & Hchk & Hupd &
                                   Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hctrue &
                                   Halign0 & Halign1)
                                | [ (vpn & i & w & mk & F & rs1 & rd & Hexec_op & Hlpad & Hvec & Hchk & Hupd &
                                     Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd)
                                  | [ (vpn & i & vpnD & ieD & w & imm & rs1 & rd & v & Hvec & Hchk & Hupd &
                                       Hpbmt & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC &
                                       Hdec & Hrd & HsomeD & HvecD & HchkD & HupdD & HpbmtD & HalignD & HcanonD &
                                       Hvpn_defD & HpaalD & Hcwd)
                                    | [ (vpn & i & h & ii & op & f & imm & rs1 & rd & Hvec & Hchk & Hupd & Hpbmt &
                                         Hcanon & Hvpn_def & Hmode & HisRVC & Hdec & Hexp & Hrd & Hexec_op)
                                      | [ (vpn & i & h & ii & op & f & rs2 & rs1 & rd & Hvec & Hchk & Hupd & Hpbmt &
                                           Hcanon & Hvpn_def & Hmode & HisRVC & Hdec & Hexp & Hrd & Hexec_op)
                                        | [ (vpn & i & h & ii & op & V & v & imm & rd & Hvec & Hchk & Hupd & Hpbmt &
                                             Hcanon & Hvpn_def & Hmode & HisRVC & Hdec & Hexp & Hrd & HVeq & Hexec_op)
                                          | [ (vpn & i & h & ii & op & f & shamt & rs1 & rd & Hvec & Hchk & Hupd &
                                               Hpbmt & Hcanon & Hvpn_def & Hmode & HisRVC & Hdec & Hexp & Hrd & Hexec_op)
                                            | [ (vpn & i & h & ii & mk & F & rs1 & rd & Hexec_op & Hlpad & Hvec & Hchk &
                                                 Hupd & Hpbmt & Hcanon & Hvpn_def & Hmode & HisRVC & Hdec & Hexp & Hrd)
                                              | [ (vpn & i & h & ii & imm & rd & Hvec & Hchk & Hupd & Hpbmt & Hcanon &
                                                   Hvpn_def & Hmode & HisRVC & Hdec & Hexp & Hrd & Halign0 & Halign1)
                                                | [ (vpn & i & h & ii & imm & rs1 & rd & Hvec & Hchk & Hupd & Hpbmt &
                                                     Hcanon & Hvpn_def & Hmode & HisRVC & Hdec & Hexp & Hrd & Halign0 &
                                                     Halign1)
                                                  | [ (vpn & i & h & ii & op & c & imm & rs2 & rs1 & Hexec_op & Hvec &
                                                       Hchk & Hupd & Hpbmt & Hcanon & Hvpn_def & Hmode & HisRVC & Hdec &
                                                       Hexp & Hcfalse)
                                                    | [ (vpn & i & h & ii & op & c & imm & rs2 & rs1 & Hexec_op & Hvec &
                                                         Hchk & Hupd & Hpbmt & Hcanon & Hvpn_def & Hmode & HisRVC & Hdec &
                                                         Hexp & Hctrue & Halign0 & Halign1)
                                                      | [ (vpn & i & h & ii & Hexec_op & Hvec & Hchk & Hupd & Hpbmt &
                                                           Hcanon & Hvpn_def & Hmode & HisRVC & Hdec)
                                                        | [ (vpn & i & h & ii & Hexec_op & Hvec & Hchk & Hupd & Hpbmt &
                                                             Hcanon & Hvpn_def & Hmode & HisRVC & Hdec)
                                                          | [ (vpn & i & h & ii & F & rs1 & rd & Hexec_op & Hvec & Hchk &
                                                               Hupd & Hpbmt & Hcanon & Hvpn_def & Hmode & HisRVC & Hdec &
                                                               Hrd)
                                                            | [ (vpn & i & w & op & f & rs2 & rs1 & rd & Hvec & Hchk & Hupd &
                                                                 Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC &
                                                                 Hdec & Hrd & Hexec_op)
                                                              | [ (vpn & i & w & mulop & f & rs2 & rs1 & rd & Hvec & Hchk &
                                                                   Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal &
                                                                   HnotRVC & Hdec & Hrd & Hexec_op)
                                                                | [ (vpn & i & h & ii & op & f & rs2 & rs1 & rd & Hvec & Hchk &
                                                                     Hupd & Hpbmt & Hcanon & Hvpn_def & Hmode & HisRVC & Hdec &
                                                                     Hexp & Hrd & Hexec_op)
                                                                  | [ (vpn & i & h & ii & mulop & f & rs2 & rs1 & rd & Hvec &
                                                                       Hchk & Hupd & Hpbmt & Hcanon & Hvpn_def & Hmode & HisRVC &
                                                                       Hdec & Hexp & Hrd & Hexec_op)
                                                                    | [ (vpn & i & w & mk2 & f & rs2 & rs1 & rd & Hvec & Hchk &
                                                                         Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def & Hpaal &
                                                                         HnotRVC & Hdec & Hrd & Hexec_op & Hnlpad)
                                                                      | [ (vpn & i & h & ii & mk2 & f & rs2 & rs1 & rd & Hvec &
                                                                           Hchk & Hupd & Hpbmt & Hcanon & Hvpn_def & Hmode &
                                                                           HisRVC & Hdec & Hexp & Hrd & Hexec_op)
                                                                        | [ (vpn & i & w & ii & Hexec_op & Hlpad & Hvec & Hchk &
                                                                             Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def &
                                                                             Hpaal & HnotRVC & Hdec)
                                                                          | [ (vpn & i & h & ii & Hexec_op & Hvec & Hchk & Hupd &
                                                                               Hpbmt & Hcanon & Hvpn_def & Hmode & HisRVC & Hdec)
                                                                            | [ (vpn & i & w & ii & Hexec_op & Hlpad & Hvec & Hchk &
                                                                                 Hupd & Hpbmt & Hcw & Hval & Hcanon & Hvpn_def &
                                                                                 Hpaal & HnotRVC & Hdec)
                                                                              | [ (vpn & i & vpnD & ieD & h & ii & imm & rs1 & rd & v &
                                                                                 Hvec & Hchk & Hupd & Hpbmt & HMPRV & HMXR & Hcanon &
                                                                                 Hvpn_def & Hmode & HisRVC & Hdec & Hexp & Hrd &
                                                                                 HsomeD & HvecD & HchkD & HupdD & HpbmtD & HalignD &
                                                                                 HcanonD & Hvpn_defD & HpaalD & Hcwd)
                                                                              | [ (vpn & i & vpnD & ieD & w & imm & rs1 & rd & is_unsigned & v & Hvec & Hchk & Hupd & Hpbmt & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & HsomeD & HvecD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hcwd)
                                                                                | (vpn & i & vpnD & ieD & h & ii & imm & rs1 & rd & v & Hvec & Hchk & Hupd & Hpbmt & HMPRV & HMXR & Hcanon & Hvpn_def & Hmode & HisRVC & Hdec & Hexp & Hrd & HsomeD & HvecD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hcwd) ] ]
                                                                              ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
                                  ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
    - (* non-canonical *)
      iDestruct "Hk" as "[_ HkT]".
      iApply (ustep_fetch_noncanonical va ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hok HSXL Hval Hcanon
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkT").
    - (* unmapped *)
      iDestruct "Hk" as "[_ HkT]".
      iApply (ustep_fetch_unmapped va vpn ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hvpn Hfwf Hok HSXL Hval Hcanon Hvpn_def
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkT").
    - (* A-bit fault on hit *)
      iDestruct "Hk" as "[_ HkT]".
      iApply (ustep_fetch_adfault_hit va vpn i pte' ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hok Hvec Hchk Hupd HSXL Hval Hcanon Hvpn_def
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkT").
    - (* ecall *)
      iDestruct "Hk" as "[_ HkT]".
      iApply (ustep_ecall va vpn i ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hsome Hok Hvec Hchk Hupd Hcw HSXL Hval Hcanon Hvpn_def Hpaal
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkT").
    - (* retiring ITYPE op *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_itype op f va vpn i w imm rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* retiring RTYPE op *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_rtype op f va vpn i w rs2 rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* retiring UTYPE op *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_utype op V v va vpn i w imm rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op HVeq Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* retiring SHIFTIOP op *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_shiftiop op f va vpn i w shamt rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* retiring JAL *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_jal va vpn i w imm rd ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval Hcanon Hvpn_def Hpaal
                HnotRVC Hdec Hrd Halign0 Halign1
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* retiring JALR *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_jalr va vpn i w imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval Hcanon Hvpn_def Hpaal
                HnotRVC Hdec Hrd Halign0 Halign1
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* retiring NOP-like (no state change) *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_nop ii va vpn i w ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hexec_op Hlpad Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval Hcanon
                Hvpn_def Hpaal HnotRVC Hdec
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* illegal instruction -> trap *)
      iDestruct "Hk" as "[_ HkT]".
      iApply (ustep_illegal ii va vpn i w ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hexec_op Hlpad Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval Hcanon
                Hvpn_def Hpaal HnotRVC Hdec
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkT").
    - (* BTYPE branch not taken *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_branch_fall op c va vpn i w imm rs2 rs1 ms_v sc_v stval_v sepc_v
                g tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hcfalse
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* BTYPE branch taken *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_branch_taken op c va vpn i w imm rs2 rs1 ms_v sc_v stval_v sepc_v
                g tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hctrue Halign0 Halign1
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* single-source compute (ADDIW etc.) *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_compute1 mk F va vpn i w rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hlpad Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* 8-byte LOAD from a code page *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_ld_code va vpn i w vpnD ieD imm rs1 rd v ms_v sc_v stval_v sepc_v
                g tlbvec E Φ HN Hok Hvec Hchk Hupd Hpbmt Hcw HSXL HMPRV HMXR Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HvecD HchkD HupdD HpbmtD
                HalignD HcanonD Hvpn_defD HpaalD Hcwd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> retiring ITYPE *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_itype op f va vpn i h ii imm rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> retiring RTYPE *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_rtype op f va vpn i h ii rs2 rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> retiring UTYPE *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_utype op V v va vpn i h ii imm rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op HVeq Hok Hvec Hchk Hupd Hpbmt HSXL
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> retiring SHIFTIOP *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_shiftiop op f va vpn i h ii shamt rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> single-source compute *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_compute1 mk F va vpn i h ii rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hlpad Hok Hvec Hchk Hupd Hpbmt HSXL
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> JAL *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_jal va vpn i h ii imm rd ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hok Hvec Hchk Hupd Hpbmt HSXL Hcanon Hvpn_def Hmode HisRVC
                Hdec Hexp Hrd Halign0 Halign1
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> JALR *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_jalr va vpn i h ii imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hok Hvec Hchk Hupd Hpbmt HSXL Hcanon Hvpn_def Hmode HisRVC
                Hdec Hexp Hrd Halign0 Halign1
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> BTYPE branch not taken *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_branch_fall op c va vpn i h ii imm rs2 rs1 ms_v sc_v stval_v sepc_v
                g tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hcfalse
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> BTYPE branch taken *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_branch_taken op c va vpn i h ii imm rs2 rs1 ms_v sc_v stval_v sepc_v
                g tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hctrue Halign0 Halign1
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> NOP-like retire *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_nop ii va vpn i h ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL Hcanon
                Hvpn_def Hmode HisRVC Hdec
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed illegal -> trap *)
      iDestruct "Hk" as "[_ HkT]".
      iApply (ustep_c_illegal ii va vpn i h ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL Hcanon Hvpn_def
                Hmode HisRVC Hdec
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkT").
    - (* compressed DIRECT single-source compute *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_compute1_direct F va vpn i h ii rs1 rd ms_v sc_v stval_v sepc_v
                g tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL Hcanon
                Hvpn_def Hmode HisRVC Hdec Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* retiring RTYPEW op *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_rtypew op f va vpn i w rs2 rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* retiring MUL *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_mul mulop f va vpn i w rs2 rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> retiring RTYPEW *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_rtypew op f va vpn i h ii rs2 rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> retiring MUL *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_mul mulop f va vpn i h ii rs2 rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* generic two-source compute (MULW/DIV/DIVW/REM/REMW/...) *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_rtype2 mk2 f va vpn i w rs2 rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hnlpad Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> generic two-source compute *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_rtype2 mk2 f va vpn i h ii rs2 rs1 rd ms_v sc_v stval_v sepc_v g
                tlbvec E Φ HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hrd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* breakpoint trap (EBREAK) *)
      iDestruct "Hk" as "[_ HkT]".
      iApply (ustep_ebreak ii va vpn i w ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hexec_op Hlpad Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval Hcanon
                Hvpn_def Hpaal HnotRVC Hdec
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkT").
    - (* compressed breakpoint trap (C_EBREAK) *)
      iDestruct "Hk" as "[_ HkT]".
      iApply (ustep_c_ebreak ii va vpn i h ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hexec_op Hok Hvec Hchk Hupd Hpbmt HSXL Hcanon Hvpn_def
                Hmode HisRVC Hdec
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkT").
    - (* privileged instruction, illegal in User mode -> trap *)
      iDestruct "Hk" as "[_ HkT]".
      iApply (ustep_illegal_st ii va vpn i w ms_v sc_v stval_v sepc_v g tlbvec E Φ
                HN Hexec_op Hlpad Hok Hvec Hchk Hupd Hpbmt Hcw HSXL Hval Hcanon
                Hvpn_def Hpaal HnotRVC Hdec
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkT").
    - (* compressed -> 8-byte LOAD from a code page *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_ld_code va vpn i h ii vpnD ieD imm rs1 rd v ms_v sc_v stval_v
                sepc_v g tlbvec E Φ HN Hok Hvec Hchk Hupd Hpbmt HSXL HMPRV HMXR
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hrd HsomeD HvecD HchkD
                HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hcwd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* width-4 LW/LWU from a code page *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_lw_code va vpn i w vpnD ieD imm rs1 rd is_unsigned v ms_v sc_v stval_v sepc_v
                g tlbvec E Φ HN Hok Hvec Hchk Hupd Hpbmt Hcw HSXL HMPRV HMXR Hval
                Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HvecD HchkD HupdD HpbmtD
                HalignD HcanonD Hvpn_defD HpaalD Hcwd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
    - (* compressed -> width-4 C_LW from a code page *)
      iDestruct "Hk" as "[HkP _]".
      iApply (ustep_c_lw_code va vpn i h ii vpnD ieD imm rs1 rd v ms_v sc_v stval_v
                sepc_v g tlbvec E Φ HN Hok Hvec Hchk Hupd Hpbmt HSXL HMPRV HMXR
                Hcanon Hvpn_def Hmode HisRVC Hdec Hexp Hrd HsomeD HvecD HchkD
                HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hcwd
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt
                      Hcode Hdata Hcfg HkP").
  Qed.


  (* the END-TO-END theorem at v1 coverage: the machine runs user code
     forever, from the frame, with only the kernel re-entry continuation *)
  Theorem wp_user_exec_v1 E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_fault_wf root slots spec ->
    (forall (va ms_v : mword 64) (g : gmap regidx (mword 64))
            (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
        upt_tlb_ok spec tlbvec ->
        _get_Mstatus_SXL ms_v = 'b"10" ->
        ustep_case va ms_v g tlbvec) ->
    hw_config -∗ minstret_inv -∗
    user_frame -∗
    (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hfwf Hclass.
    iIntros "#Hhw #Hinv HP Htr".
    iApply (wp_user_exec E Φ with "[] HP Htr").
    iApply (user_step_holds E Φ HN Hfwf Hclass with "Hhw Hinv").
  Qed.


End WpUserSteps.
