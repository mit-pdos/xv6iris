(* WpUserFull.v -- the spatial-composed user-mode step obligation.

   [user_step_holds_full] discharges [user_step_obligation] from a
   SUCCESS-PATH classification [∀ frame, ustep_case ∨ ustep_mem_case] --
   WITHOUT the pure universal [Hclass] of [user_step_holds] (which is
   unprovable: memory ops have no [ustep_case] home).  Non-memory words go
   to [ustep_case_sound]; memory words go to the frame-consuming
   dispatchers [wp_user_{l,s}*_frame] (WpUserMemStep.v), which pull the
   mutable [user_data] ownership internally so their premises stay PURE and
   fit in [ustep_mem_case] (8 arms: loads LD/LW/LH/LB + stores SD/SW/SH/SB).

   This is the memory SUCCESS path; faulting/misaligned/unmapped data
   addresses (-> [user_trap_frame]) still need the fault arms before the
   classification is TOTAL. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions list list_monad.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv.
Require Import WpDecodeBridge.
Require Import UmodeFetch UmodeEcall UptInv.
Local Open Scope Z_scope.
Import Defs.

Require Import WpUserBase WpUserSteps WpUserMemStep WpUserDataFault WpUserTrapish.

Section WpUserFull.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation spec := (WpUserBase.spec U).
  Local Notation root := (WpUserBase.root U).
  Local Notation slots := (WpUserBase.slots U).
  Local Notation code := (WpUserBase.code U).
  Local Notation data := (WpUserBase.data U).
  Local Notation dq := (WpUserBase.dq U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).
  Local Notation user_frame := (WpUserBase.user_frame U).
  Local Notation user_trap_frame := (WpUserBase.user_trap_frame U).
  Local Notation user_step_obligation := (WpUserBase.user_step_obligation U).
  Local Notation ustep_case := (WpUserSteps.ustep_case U).
  Local Notation ustep_case_sound := (WpUserSteps.ustep_case_sound U).
  Local Notation wp_user_ld_data_frame := (WpUserMemStep.wp_user_ld_data_frame U).
  Local Notation wp_user_lw_data_frame := (WpUserMemStep.wp_user_lw_data_frame U).
  Local Notation wp_user_lh_data_frame := (WpUserMemStep.wp_user_lh_data_frame U).
  Local Notation wp_user_lb_data_frame := (WpUserMemStep.wp_user_lb_data_frame U).
  Local Notation wp_user_sd_frame := (WpUserMemStep.wp_user_sd_frame U).
  Local Notation wp_user_sw_frame := (WpUserMemStep.wp_user_sw_frame U).
  Local Notation wp_user_sh_frame := (WpUserMemStep.wp_user_sh_frame U).
  Local Notation wp_user_sb_frame := (WpUserMemStep.wp_user_sb_frame U).
  Local Notation wp_user_ld_data_frame_u := (WpUserMemStep.wp_user_ld_data_frame_u U).
  Local Notation wp_user_lw_data_frame_u := (WpUserMemStep.wp_user_lw_data_frame_u U).
  Local Notation wp_user_lh_data_frame_u := (WpUserMemStep.wp_user_lh_data_frame_u U).
  Local Notation wp_user_lb_data_frame_u := (WpUserMemStep.wp_user_lb_data_frame_u U).
  Local Notation wp_user_sd_frame_u := (WpUserMemStep.wp_user_sd_frame_u U).
  Local Notation wp_user_sw_frame_u := (WpUserMemStep.wp_user_sw_frame_u U).
  Local Notation wp_user_sh_frame_u := (WpUserMemStep.wp_user_sh_frame_u U).
  Local Notation wp_user_sb_frame_u := (WpUserMemStep.wp_user_sb_frame_u U).
  Local Notation wp_user_amoswap_frame_u := (WpUserMemStep.wp_user_amoswap_frame_u U).
  Local Notation wp_user_split_lw_frame := (WpUserMemStep.wp_user_split_lw_frame U).
  Local Notation medl_v := (WpUserBase.medl_v U).
  Local Notation ustep_lr_fault_u := (WpUserTrapish.ustep_lr_fault_u U).
  Local Notation ustep_sc_fault_u := (WpUserTrapish.ustep_sc_fault_u U).
  Local Notation ustep_load_pf_4_u := (WpUserTrapish.ustep_load_pf_4_u U).
  Local Notation ustep_load_pf_8_u := (WpUserTrapish.ustep_load_pf_8_u U).
  Local Notation ustep_load_pf_2_u := (WpUserTrapish.ustep_load_pf_2_u U).
  Local Notation ustep_load_pf_1_u := (WpUserTrapish.ustep_load_pf_1_u U).
  Local Notation ustep_store_pf_4_u := (WpUserTrapish.ustep_store_pf_4_u U).
  Local Notation ustep_store_pf_8_u := (WpUserTrapish.ustep_store_pf_8_u U).
  Local Notation ustep_store_pf_2_u := (WpUserTrapish.ustep_store_pf_2_u U).
  Local Notation ustep_store_pf_1_u := (WpUserTrapish.ustep_store_pf_1_u U).
  Local Notation ustep_load_pf_4_noperm_u := (WpUserTrapish.ustep_load_pf_4_noperm_u U).
  Local Notation ustep_load_pf_8_noperm_u := (WpUserTrapish.ustep_load_pf_8_noperm_u U).
  Local Notation ustep_load_pf_2_noperm_u := (WpUserTrapish.ustep_load_pf_2_noperm_u U).
  Local Notation ustep_load_pf_1_noperm_u := (WpUserTrapish.ustep_load_pf_1_noperm_u U).
  Local Notation ustep_store_pf_8_noperm_u := (WpUserTrapish.ustep_store_pf_8_noperm_u U).
  Local Notation ustep_store_pf_4_noperm_u := (WpUserTrapish.ustep_store_pf_4_noperm_u U).
  Local Notation ustep_store_pf_2_noperm_u := (WpUserTrapish.ustep_store_pf_2_noperm_u U).
  Local Notation ustep_store_pf_1_noperm_u := (WpUserTrapish.ustep_store_pf_1_noperm_u U).
  Local Notation ustep_lr_fault_misalign_u := (WpUserTrapish.ustep_lr_fault_misalign_u U).
  Local Notation ustep_sc_fault_misalign_u := (WpUserTrapish.ustep_sc_fault_misalign_u U).
  Local Notation ustep_amoswap_fault_misalign_u := (WpUserTrapish.ustep_amoswap_fault_misalign_u U).
  Local Notation ustep_load_unmapped_fault := (WpUserDataFault.ustep_load_unmapped_fault U).
  Local Notation ustep_store_unmapped_fault := (WpUserDataFault.ustep_store_unmapped_fault U).
  Local Notation ustep_load_unmapped_fault_8 := (WpUserDataFault.ustep_load_unmapped_fault_8 U).
  Local Notation ustep_load_unmapped_fault_2 := (WpUserDataFault.ustep_load_unmapped_fault_2 U).
  Local Notation ustep_load_unmapped_fault_1 := (WpUserDataFault.ustep_load_unmapped_fault_1 U).
  Local Notation ustep_store_unmapped_fault_8 := (WpUserDataFault.ustep_store_unmapped_fault_8 U).
  Local Notation ustep_store_unmapped_fault_2 := (WpUserDataFault.ustep_store_unmapped_fault_2 U).
  Local Notation ustep_store_unmapped_fault_1 := (WpUserDataFault.ustep_store_unmapped_fault_1 U).

  Definition ustep_mem_case (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs1 rd : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, false, 8), s0)) /\
       uint rd <> 0 /\
       spec !! vpnD = Some ieD /\
       uw_check_ok (Load Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 8 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 8 = true /\
       (forall j : nat, (j < 8)%nat -> pa_add paD j ∈ data))
    \/
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) /\
       uint rd <> 0 /\
       spec !! vpnD = Some ieD /\
       uw_check_ok (Load Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 4 = true /\
       (forall j : nat, (j < 4)%nat -> pa_add paD j ∈ data))
    \/
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2), s0)) /\
       uint rd <> 0 /\
       spec !! vpnD = Some ieD /\
       uw_check_ok (Load Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 2 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 2 = true /\
       (forall j : nat, (j < 2)%nat -> pa_add paD j ∈ data))
    \/
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1), s0)) /\
       uint rd <> 0 /\
       spec !! vpnD = Some ieD /\
       uw_check_ok (Load Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 1 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 1 = true /\
       (forall j : nat, (j < 1)%nat -> pa_add paD j ∈ data))
    \/
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       (uint paD + 8 <= 18446744073709551616)%Z /\
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_ok (Store Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Store Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 8 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 8 = true /\
       (forall j : nat, (j < 8)%nat -> pa_add paD j ∈ data))
    \/
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       (uint paD + 4 <= 18446744073709551616)%Z /\
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_ok (Store Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Store Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 4 = true /\
       (forall j : nat, (j < 4)%nat -> pa_add paD j ∈ data))
    \/
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       (uint paD + 2 <= 18446744073709551616)%Z /\
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 2), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_ok (Store Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Store Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 2 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 2 = true /\
       (forall j : nat, (j < 2)%nat -> pa_add paD j ∈ data))
    \/
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       (uint paD + 1 <= 18446744073709551616)%Z /\
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 1), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_ok (Store Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Store Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 1 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 1 = true /\
       (forall j : nat, (j < 1)%nat -> pa_add paD j ∈ data))
    \/
    (* AMOSWAP.W success (width 4, no immediate) *)
    (exists vpn ie (w : mword 32) vpnD ieD (rs2 rs1 rd : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (zeros' 64) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       (uint paD + 4 <= 18446744073709551616)%Z /\
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (AMO (AMOSWAP, true, false, Regidx rs2, Regidx rs1, 4, Regidx rd), s0)) /\
       uint rd <> 0 /\
       spec !! vpnD = Some ieD /\
       uw_check_ok (Atomic (AMOSWAP, Data, Data)) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Atomic (AMOSWAP, Data, Data)) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 4 = true /\
       (forall j : nat, (j < 4)%nat -> pa_add paD j ∈ data))
    \/
    (* --- 2-aligned split-fetch twins (32-bit instr at odd halfword) --- *)
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       (forall j : nat, (j < 2)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j
            = Some (nth_byte (subrange_vec_dec w 15 0 : mword 16) j)) /\
       (forall j : nat, (j < 2)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn) j
            = Some (nth_byte (subrange_vec_dec w 31 16 : mword 16) j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       neq_vec (access_vec_dec va 0) ('b"0") = false /\
       neq_vec (access_vec_dec va 1) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = false /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 2 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr (add_vec_int va 2)))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr (add_vec_int va 2))) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) (add_vec_int va 2) vpn)) 2 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) /\
       uint rd <> 0 /\
       spec !! vpnD = Some ieD /\
       uw_check_ok (Load Data) ieD /\
       update_PTE_Bits (uw_pte0 ieD) (Load Data) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
       is_aligned_vaddr (Virtaddr eaF) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
       is_aligned_paddr (Physaddr paD) 4 = true /\
       (forall j : nat, (j < 4)%nat -> pa_add paD j ∈ data)).

  (* the DATA-FAULT classification: the fetched word is a width-4 LOAD/STORE
     whose effective address's vpn is UNMAPPED (spec!!vpnD=None), so the data
     access page-faults into [user_trap_frame].  Packages exactly the pure
     premises of [ustep_{load,store}_unmapped_fault] (the top-level
     [upt_fault_wf], [upt_tlb_ok], [SXL] hyps of [user_step_holds_full] are
     dropped -- they are already in scope). *)
  Definition ustep_fault_case (va ms_v : mword 64) (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) : Prop :=
    (exists vpn ie (w : mword 32) vpnD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 8), s0)) /\
       spec !! vpnD = None /\
       is_aligned_vaddr (Virtaddr eaF) 8 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (exists vpn ie (w : mword 32) vpnD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) /\
       spec !! vpnD = None /\
       is_aligned_vaddr (Virtaddr eaF) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (exists vpn ie (w : mword 32) vpnD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2), s0)) /\
       spec !! vpnD = None /\
       is_aligned_vaddr (Virtaddr eaF) 2 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (exists vpn ie (w : mword 32) vpnD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1), s0)) /\
       spec !! vpnD = None /\
       is_aligned_vaddr (Virtaddr eaF) 1 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (exists vpn ie (w : mword 32) vpnD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), s0)) /\
       spec !! vpnD = None /\
       is_aligned_vaddr (Virtaddr eaF) 8 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (exists vpn ie (w : mword 32) vpnD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), s0)) /\
       spec !! vpnD = None /\
       is_aligned_vaddr (Virtaddr eaF) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (exists vpn ie (w : mword 32) vpnD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 2), s0)) /\
       spec !! vpnD = None /\
       is_aligned_vaddr (Virtaddr eaF) 2 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (exists vpn ie (w : mword 32) vpnD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 1), s0)) /\
       spec !! vpnD = None /\
       is_aligned_vaddr (Virtaddr eaF) 1 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (exists vpn ie (w : mword 32) vpnD ieD (rs1 rd : mword 5) (aq rl : bool),
       let eaF := add_vec (g !!! Regidx rs1) (zeros' 64) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    spec !! vpn = Some ie /\
    uw_check_ok (InstructionFetch tt) ie /\
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
    is_aligned_vaddr (Virtaddr va) 4 = true /\
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
    isRVC (subrange_vec_dec w 15 0) = false /\
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd), s0)) /\
    spec !! vpnD = Some ieD /\
    uw_check_ok (LoadReserved Data) ieD /\
    update_PTE_Bits (uw_pte0 ieD) (LoadReserved Data) = None /\
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
    is_aligned_vaddr (Virtaddr eaF) 4 = true /\
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
    is_aligned_paddr (Physaddr paD) 4 = true /\
    addr_is_ram paD /\
    addr_is_ram (pa_add paD 3) /\
    (forall region s0, matching_pma_region (register_lookup pma_regions s0.(sregs)) (Physaddr paD) 4 = Some region ->
       (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone) /\
    bit_to_bool (access_vec_dec medl_v (uint (exceptionType_bits_forwards (E_Load_Access_Fault tt)))) = true)
    \/
    (exists vpn ie (w : mword 32) vpnD ieD (rs2 rs1 rd : mword 5) (aq rl : bool),
       let eaF := add_vec (g !!! Regidx rs1) (zeros' 64) in
       let paD := u_pa (upt_entry vpnD ieD) eaF vpnD in
    spec !! vpn = Some ie /\
    uw_check_ok (InstructionFetch tt) ie /\
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
    eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
    eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
    is_aligned_vaddr (Virtaddr va) 4 = true /\
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
    isRVC (subrange_vec_dec w 15 0) = false /\
    (forall s0, agree_on D_u s0 dstateU ->
       exec (ext_decode w) s0 = Some (STORECON (aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd), s0)) /\
    spec !! vpnD = Some ieD /\
    uw_check_ok (StoreConditional Data) ieD /\
    update_PTE_Bits (uw_pte0 ieD) (StoreConditional Data) = None /\
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ieD)) = ('b"00" : mword 2) /\
    is_aligned_vaddr (Virtaddr eaF) 4 = true /\
    neq_vec (bits_of_virtaddr (Virtaddr eaF))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD /\
    is_aligned_paddr (Physaddr paD) 4 = true /\
    addr_is_ram paD /\
    addr_is_ram (pa_add paD 3) /\
    (forall region s0, matching_pma_region (register_lookup pma_regions s0.(sregs)) (Physaddr paD) 4 = Some region ->
       (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_reservability) = RsrvNone) /\
    match_reservation (bits_of_physaddr (Physaddr paD)) = false /\
    bit_to_bool (access_vec_dec medl_v (uint (exceptionType_bits_forwards (E_SAMO_Access_Fault tt)))) = true)
    \/
    (* DATA-NO-PERM load page-fault (width 4): the eaF vpn is MAPPED but the
       data-side permission check DENIES the load. *)
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_denied (Load Data) ieD /\
       is_aligned_vaddr (Virtaddr eaF) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (* DATA-NO-PERM load page-fault (width 8) *)
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 8), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_denied (Load Data) ieD /\
       is_aligned_vaddr (Virtaddr eaF) 8 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (* DATA-NO-PERM load page-fault (width 2) *)
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_denied (Load Data) ieD /\
       is_aligned_vaddr (Virtaddr eaF) 2 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (* DATA-NO-PERM load page-fault (width 1) *)
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs1 rd : mword 5) (is_unsigned : bool),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_denied (Load Data) ieD /\
       is_aligned_vaddr (Virtaddr eaF) 1 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (* DATA-NO-PERM store page-fault (width 8) *)
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 8), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_denied (Store Data) ieD /\
       is_aligned_vaddr (Virtaddr eaF) 8 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (* DATA-NO-PERM store page-fault (width 4) *)
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 4), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_denied (Store Data) ieD /\
       is_aligned_vaddr (Virtaddr eaF) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (* DATA-NO-PERM store page-fault (width 2) *)
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 2), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_denied (Store Data) ieD /\
       is_aligned_vaddr (Virtaddr eaF) 2 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (* DATA-NO-PERM store page-fault (width 1) *)
    (exists vpn ie (w : mword 32) vpnD ieD (imm : mword 12) (rs2 rs1 : mword 5),
       let eaF := add_vec (g !!! Regidx rs1) (sign_extend' 64 imm) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORE (imm, Regidx rs2, Regidx rs1, 1), s0)) /\
       spec !! vpnD = Some ieD /\
       uw_check_denied (Store Data) ieD /\
       is_aligned_vaddr (Virtaddr eaF) 1 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr eaF))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr eaF)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpnD)
    \/
    (* MISALIGNED LR access-fault *)
    (exists vpn ie (w : mword 32) (rs1 rd : mword 5) (aq rl : bool),
       let eaF := add_vec (g !!! Regidx rs1) (zeros' 64) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (LOADRES (aq, rl, Regidx rs1, 4, Regidx rd), s0)) /\
       is_aligned_vaddr (Virtaddr eaF) 4 = false /\
       bit_to_bool (access_vec_dec medl_v (uint (exceptionType_bits_forwards (E_Load_Access_Fault tt)))) = true)
    \/
    (* MISALIGNED SC access-fault *)
    (exists vpn ie (w : mword 32) (rs2 rs1 rd : mword 5) (aq rl : bool),
       let eaF := add_vec (g !!! Regidx rs1) (zeros' 64) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (STORECON (aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd), s0)) /\
       is_aligned_vaddr (Virtaddr eaF) 4 = false /\
       bit_to_bool (access_vec_dec medl_v (uint (exceptionType_bits_forwards (E_SAMO_Access_Fault tt)))) = true)
    \/
    (* MISALIGNED AMOSWAP access-fault *)
    (exists vpn ie (w : mword 32) (rs2 rs1 rd : mword 5) (aq rl : bool),
       let eaF := add_vec (g !!! Regidx rs1) (zeros' 64) in
       spec !! vpn = Some ie /\
       uw_check_ok (InstructionFetch tt) ie /\
       update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None /\
       _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) /\
       (forall j : nat, (j < 4)%nat ->
          code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) /\
       eq_vec (_get_Mstatus_MPRV ms_v) ('b"1" : mword 1) = false /\
       eq_vec (_get_Mstatus_MXR ms_v) ('b"0") = true /\
       is_aligned_vaddr (Virtaddr va) 4 = true /\
       neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false /\
       autocast (T := mword) (subrange_vec_dec
         (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn /\
       is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true /\
       isRVC (subrange_vec_dec w 15 0) = false /\
       (forall s0, agree_on D_u s0 dstateU ->
          exec (ext_decode w) s0 = Some (AMO (AMOSWAP, aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd), s0)) /\
       is_aligned_vaddr (Virtaddr eaF) 4 = false /\
       bit_to_bool (access_vec_dec medl_v (uint (exceptionType_bits_forwards (E_SAMO_Access_Fault tt)))) = true).

  (* the spatial-composed obligation: reduce [user_step_obligation] to the
     success-or-fault classification, dispatching memory/fault words spatially *)
  Theorem user_step_holds_full E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_fault_wf root slots spec ->
    (forall (va ms_v : mword 64) (g : gmap regidx (mword 64))
            (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
        upt_tlb_ok spec tlbvec ->
        _get_Mstatus_SXL ms_v = 'b"10" ->
        ustep_case va ms_v g tlbvec \/ ustep_mem_case va ms_v g tlbvec
        \/ ustep_fault_case va ms_v g tlbvec) ->
    hw_config -∗ minstret_inv -∗ user_step_obligation E Φ.
  Proof.
    intros HN Hfwf Hfull.
    iIntros "#Hhw #Hinv".
    rewrite /user_step_obligation.
    iIntros "!> HP Hk".
    rewrite {1}/user_frame.
    iDestruct "HP" as (ms_v sc_v stval_v sepc_v va g tlbvec)
      "(%HSXL & %Hok & Hhs & Hpriv & Hms & Hsc & Hstv & Hsepc & Htlbc & Hpc &
        Hgpr & Hupt & #Hcode & Hdata & Hcfg)".
    destruct (Hfull va ms_v g tlbvec Hok HSXL) as [Hcase | [Hmem | Hfault]].
    - iApply (ustep_case_sound E Φ ms_v sc_v stval_v sepc_v va g tlbvec
                HN Hfwf Hok HSXL Hcase
                with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg Hk").
    - iAssert (▷ (user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}))%I
        with "[Hk]" as "HkP".
      { iNext. iDestruct "Hk" as "[$ _]". }
      destruct Hmem as [Hld | [Hlw | [Hlh | [Hlb | [Hsd | [Hsw | [Hsh | [Hsb | [Hamo | Hslw]]]]]]]]].
      + (* LD width 8 *)
        destruct Hld as (vpn & ie & w & vpnD & ieD & imm & rs1 & rd & Hsome & Hchk0 & HupdN & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hwin).
        iApply (wp_user_ld_data_frame_u va vpn ie w vpnD ieD imm rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkP").
      + (* LW width 4 *)
        destruct Hlw as (vpn & ie & w & vpnD & ieD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hwin).
        iApply (wp_user_lw_data_frame_u va vpn ie w vpnD ieD imm rs1 rd is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkP").
      + (* LH width 2 *)
        destruct Hlh as (vpn & ie & w & vpnD & ieD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hwin).
        iApply (wp_user_lh_data_frame_u va vpn ie w vpnD ieD imm rs1 rd is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkP").
      + (* LB width 1 *)
        destruct Hlb as (vpn & ie & w & vpnD & ieD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hwin).
        iApply (wp_user_lb_data_frame_u va vpn ie w vpnD ieD imm rs1 rd is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkP").
      + (* SD width 8 *)
        destruct Hsd as (vpn & ie & w & vpnD & ieD & imm & rs2 & rs1 & Hnowrap & Hsome & Hchk0 & HupdN & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hwin).
        iApply (wp_user_sd_frame_u va vpn ie w vpnD ieD imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hnowrap Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkP").
      + (* SW width 4 *)
        destruct Hsw as (vpn & ie & w & vpnD & ieD & imm & rs2 & rs1 & Hnowrap & Hsome & Hchk0 & HupdN & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hwin).
        iApply (wp_user_sw_frame_u va vpn ie w vpnD ieD imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hnowrap Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkP").
      + (* SH width 2 *)
        destruct Hsh as (vpn & ie & w & vpnD & ieD & imm & rs2 & rs1 & Hnowrap & Hsome & Hchk0 & HupdN & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hwin).
        iApply (wp_user_sh_frame_u va vpn ie w vpnD ieD imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hnowrap Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkP").
      + (* SB width 1 *)
        destruct Hsb as (vpn & ie & w & vpnD & ieD & imm & rs2 & rs1 & Hnowrap & Hsome & Hchk0 & HupdN & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hwin).
        iApply (wp_user_sb_frame_u va vpn ie w vpnD ieD imm rs2 rs1 ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hnowrap Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkP").
      + (* AMOSWAP.W width 4 *)
        destruct Hamo as (vpn & ie & w & vpnD & ieD & rs2 & rs1 & rd & Hnowrap & Hsome & Hchk0 & HupdN & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & Hrd & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hwin).
        iApply (wp_user_amoswap_frame_u va vpn ie w vpnD ieD rs2 rs1 rd ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hnowrap Hok Hsome Hchk0 HupdN Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkP").
      + (* LW split-fetch (2-aligned, width 4) *)
        destruct Hslw as (vpn & ie & w & vpnD & ieD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & HcwL & HcwH & HMPRV & HMXR & Hbit0 & Hbit1 & Hvalign4 & HcanonL & Hvpn_defL & HalignL & HcanonH & Hvpn_defH & HalignH & HnotRVC & Hdec & Hrd & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & Hwin).
        iApply (wp_user_split_lw_frame va vpn ie w vpnD ieD imm rs1 rd is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN HcwL HcwH HSXL HMPRV HMXR Hbit0 Hbit1 Hvalign4 HcanonL Hvpn_defL HalignL HcanonH Hvpn_defH HalignH HnotRVC Hdec Hrd HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD Hwin
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkP").
    - (* fault branch: the data address is UNMAPPED -> page-fault trap frame *)
      iAssert (▷ (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}))%I
        with "[Hk]" as "HkT".
      { iNext. iDestruct "Hk" as "[_ $]". }
      destruct Hfault as [Hl8 | [Hl4 | [Hl2 | [Hl1 | [Hs8 | [Hs4 | [Hs2 | [Hs1 | [Hlr | [Hsc | [Hln4 | [Hln8 | [Hln2 | [Hln1 | [Hsn8 | [Hsn4 | [Hsn2 | [Hsn1 | [Hlrm | [Hscm | Hamom]]]]]]]]]]]]]]]]]]]].
      + (* LOAD fault (width 8) *)
        destruct Hl8 as (vpn & ie & w & vpnD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD_none & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_load_pf_8_u va vpn ie w vpnD rs1 rd imm is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD_none Hfwf HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* LOAD fault (width 4) *)
        destruct Hl4 as (vpn & ie & w & vpnD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD_none & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_load_pf_4_u va vpn ie w vpnD rs1 rd imm is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD_none Hfwf HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* LOAD fault (width 2) *)
        destruct Hl2 as (vpn & ie & w & vpnD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD_none & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_load_pf_2_u va vpn ie w vpnD rs1 rd imm is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD_none Hfwf HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* LOAD fault (width 1) *)
        destruct Hl1 as (vpn & ie & w & vpnD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD_none & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_load_pf_1_u va vpn ie w vpnD rs1 rd imm is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD_none Hfwf HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* STORE fault (width 8) *)
        destruct Hs8 as (vpn & ie & w & vpnD & imm & rs2 & rs1 & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD_none & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_store_pf_8_u va vpn ie w vpnD rs2 rs1 imm ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD_none Hfwf HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* STORE fault (width 4) *)
        destruct Hs4 as (vpn & ie & w & vpnD & imm & rs2 & rs1 & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD_none & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_store_pf_4_u va vpn ie w vpnD rs2 rs1 imm ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD_none Hfwf HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* STORE fault (width 2) *)
        destruct Hs2 as (vpn & ie & w & vpnD & imm & rs2 & rs1 & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD_none & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_store_pf_2_u va vpn ie w vpnD rs2 rs1 imm ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD_none Hfwf HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* STORE fault (width 1) *)
        destruct Hs1 as (vpn & ie & w & vpnD & imm & rs2 & rs1 & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD_none & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_store_pf_1_u va vpn ie w vpnD rs2 rs1 imm ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD_none Hfwf HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* LR access fault (atomic on non-reservable region) *)
        destruct Hlr as (vpn & ie & w & vpnD & ieD & rs1 & rd & aq & rl & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & HramD & HramD3 & Hresv & Hdel_loadaf).
        iApply (ustep_lr_fault_u va vpn ie w vpnD ieD rs1 rd aq rl ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD HramD HramD3 Hresv Hdel_loadaf
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* SC access fault (atomic on non-reservable region) *)
        destruct Hsc as (vpn & ie & w & vpnD & ieD & rs2 & rs1 & rd & aq & rl & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & HchkD & HupdD & HpbmtD & HalignD & HcanonD & Hvpn_defD & HpaalD & HramD & HramD3 & Hresv & Hmatchrsv & Hdel_samoaf).
        iApply (ustep_sc_fault_u va vpn ie w vpnD ieD rs2 rs1 rd aq rl ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD HchkD HupdD HpbmtD HalignD HcanonD Hvpn_defD HpaalD HramD HramD3 Hresv Hmatchrsv Hdel_samoaf
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* LOAD data-no-perm fault (width 4) *)
        destruct Hln4 as (vpn & ie & w & vpnD & ieD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & Hden & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_load_pf_4_noperm_u va vpn ie w vpnD ieD rs1 rd imm is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD Hden HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* LOAD data-no-perm fault (width 8) *)
        destruct Hln8 as (vpn & ie & w & vpnD & ieD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & Hden & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_load_pf_8_noperm_u va vpn ie w vpnD ieD rs1 rd imm is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD Hden HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* LOAD data-no-perm fault (width 2) *)
        destruct Hln2 as (vpn & ie & w & vpnD & ieD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & Hden & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_load_pf_2_noperm_u va vpn ie w vpnD ieD rs1 rd imm is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD Hden HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* LOAD data-no-perm fault (width 1) *)
        destruct Hln1 as (vpn & ie & w & vpnD & ieD & imm & rs1 & rd & is_unsigned & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & Hden & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_load_pf_1_noperm_u va vpn ie w vpnD ieD rs1 rd imm is_unsigned ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD Hden HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* STORE data-no-perm fault (width 8) *)
        destruct Hsn8 as (vpn & ie & w & vpnD & ieD & imm & rs2 & rs1 & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & Hden & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_store_pf_8_noperm_u va vpn ie w vpnD ieD rs2 rs1 imm ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD Hden HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* STORE data-no-perm fault (width 4) *)
        destruct Hsn4 as (vpn & ie & w & vpnD & ieD & imm & rs2 & rs1 & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & Hden & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_store_pf_4_noperm_u va vpn ie w vpnD ieD rs2 rs1 imm ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD Hden HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* STORE data-no-perm fault (width 2) *)
        destruct Hsn2 as (vpn & ie & w & vpnD & ieD & imm & rs2 & rs1 & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & Hden & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_store_pf_2_noperm_u va vpn ie w vpnD ieD rs2 rs1 imm ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD Hden HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* STORE data-no-perm fault (width 1) *)
        destruct Hsn1 as (vpn & ie & w & vpnD & ieD & imm & rs2 & rs1 & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HsomeD & Hden & HalignD & HcanonD & Hvpn_defD).
        iApply (ustep_store_pf_1_noperm_u va vpn ie w vpnD ieD rs2 rs1 imm ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HsomeD Hden HalignD HcanonD Hvpn_defD
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* LR misaligned access-fault *)
        destruct Hlrm as (vpn & ie & w & rs1 & rd & aq & rl & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HmisD & Hdel_loadaf).
        iApply (ustep_lr_fault_misalign_u va vpn ie w rs1 rd aq rl ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HmisD Hdel_loadaf
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* SC misaligned access-fault *)
        destruct Hscm as (vpn & ie & w & rs2 & rs1 & rd & aq & rl & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HmisD & Hdel_samoaf).
        iApply (ustep_sc_fault_misalign_u va vpn ie w rs2 rs1 rd aq rl ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HmisD Hdel_samoaf
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
      + (* AMOSWAP misaligned access-fault *)
        destruct Hamom as (vpn & ie & w & rs2 & rs1 & rd & aq & rl & Hsome & Hchk0 & HupdN & Hpbmt0 & Hcw & HMPRV & HMXR & Hval & Hcanon & Hvpn_def & Hpaal & HnotRVC & Hdec & HmisD & Hdel_samoaf).
        iApply (ustep_amoswap_fault_misalign_u va vpn ie w rs2 rs1 rd aq rl ms_v sc_v stval_v sepc_v g tlbvec E Φ
                  HN Hok Hsome Hchk0 HupdN Hpbmt0 Hcw HSXL HMPRV HMXR Hval Hcanon Hvpn_def Hpaal HnotRVC Hdec HmisD Hdel_samoaf
                  with "Hhw Hinv Hhs Hpriv Hms Hsc Hstv Hsepc Htlbc Hpc Hgpr Hupt Hcode Hdata Hcfg HkT").
  Qed.


  (* the END-TO-END theorem at FULL coverage.  Identical to
     [wp_user_exec_v1] (WpUserSteps.v) except the classification hypothesis is
     the full three-way disjunction [ustep_case \/ ustep_mem_case \/
     ustep_fault_case], dispatched by [user_step_holds_full] above (rather than
     the [ustep_case]-only [user_step_holds]).  A total classifier
     [user_classify] proving that disjunction for every [va] plugs directly in
     here and yields the unconditional "runs user code forever" statement. *)
  Theorem wp_user_exec_full E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    upt_fault_wf root slots spec ->
    (forall (va ms_v : mword 64) (g : gmap regidx (mword 64))
            (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
        upt_tlb_ok spec tlbvec ->
        _get_Mstatus_SXL ms_v = 'b"10" ->
        ustep_case va ms_v g tlbvec \/ ustep_mem_case va ms_v g tlbvec
        \/ ustep_fault_case va ms_v g tlbvec) ->
    hw_config -∗ minstret_inv -∗
    user_frame -∗
    (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hfwf Hfull.
    iIntros "#Hhw #Hinv HP Htr".
    iApply (WpUserBase.wp_user_exec U E Φ with "[] HP Htr").
    iApply (user_step_holds_full E Φ HN Hfwf Hfull with "Hhw Hinv").
  Qed.

End WpUserFull.
