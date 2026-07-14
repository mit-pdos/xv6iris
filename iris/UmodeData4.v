(* UmodeData4.v -- U-mode width-4 DATA load/store execute lemmas.

   Thin U-mode instantiation of the mode-neutral width-4 tower in
   MemData4: we supply the User-privilege pmpCheck grant, the Sv39
   TLB-hit translation (pa = u_pa ent ea vpn, no A/D write-back), and the
   identity effective-address transform (pmlen 0), then discharge the
   generic exec_execute_LOAD_4_gpr / exec_execute_STORE_4_gpr.  The LOAD
   lemma is sign-generic (is_unsigned) so it covers both LW and LWU. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodeCore.
Require Import WpGpr.
Require Import UmodeFetch MemData4 UmodeData.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* U-mode width-4 register-generic LOAD (LW / LWU), rd <> x0.            *)
(* ===================================================================== *)
Section VRU4.
  Context (ent : TLB_Entry) (vpn : mword 27).
  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let pa := u_pa ent ea vpn.
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.

  (* stored-entry leaf facts at Load Data *)
  Hypothesis Hchk : forall (mxr do_sum : bool) s0,
    exec (check_PTE_permission (Load Data) User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
            (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
      = Some (PTE_Check_Success tt, s0).
  Hypothesis Hupd : update_PTE_Bits (tlb_get_pte 8 ent) (Load Data)
                    = (None : option (mword 64)).
  Hypothesis Hpbmt : forall s0, exec (tlb_get_pbmt ent) s0 = Some (PBMT_PMA, s0).
  Hypothesis Hmatch_tlb : match_TLB_Entry ent (mword_of_int 0 : mword 16)
                        (sign_extend' (57 - 12) vpn) = true.
  (* machine-state pins *)
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = User.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis HES : exec (currentlyEnabled Ext_S) s = Some (true, s).
  Hypothesis Hsenv : register_lookup senvcfg s.(sregs) = mword_of_int 0.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = MENVCFG_S.
  Hypothesis Hsatpmode : _get_Satp64_Mode (Mk_Satp64 (register_lookup satp s.(sregs))) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) (register_lookup satp s.(sregs)) : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Hvec : vec_access_dec (register_lookup tlb s.(sregs)) (tlb_hash (__id 39) vpn) = Some ent.
  (* va geometry at the effective address *)
  Hypothesis Halign : is_aligned_vaddr (Virtaddr ea) 4 = true.
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr ea))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn.
  (* physical-side facts at the translated pa *)
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HpmpR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hpmam : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
    s.(mem) !! (pa_add pa j) = Some (nth_byte v j).
  Hypothesis Hrd : uint rd <> 0.

  Lemma exec_execute_LOAD_4_U (is_unsigned : bool) :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))) s
      = Some (RETIRE_SUCCESS,
              set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value is_unsigned data2))).
  Proof.
    assert (Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s = Some (Virtaddr ea, s)).
    { apply exec_transform_effective_address_load_u; assumption. }
    assert (Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr ea)) (0 * 4))) (Load Data)) s
                  = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s)).
    { cbn [bits_of_virtaddr]. rewrite avi0_mul4.
      exact (exec_translateAddr_load_hit_u ent vpn ea
               (register_lookup satp s.(sregs)) (register_lookup tlb s.(sregs)) s
               Hchk Hupd Hpbmt Hmatch_tlb Hcp HSXL Hmprv eq_refl Hsatpmode Hasid
               eq_refl Hvec Hcanon Hvpn_def). }
    assert (Hpmp : exec (pmpCheck (Physaddr pa) 4 (Load Data) User) s = Some (None, s)).
    { exact (exec_pmpCheck_user_grant_load pa 4 s HpmpA Hpmp_ord Hrange HpmpR). }
    exact (exec_execute_LOAD_4_gpr User is_unsigned rs1 rd imm ea v region s pa
             Hrd Htea Halign Hcp Hmprv Htr Hpmp Hpmam Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  Qed.
End VRU4.

(* ===================================================================== *)
(* U-mode width-4 LOAD, DATA-TLB-MISS form.  The data translate walks and  *)
(* fills, so it moves the state s -> s'; the load body then runs at s'.     *)
(* The caller supplies the identity EA-transform [Htea] and the walk-fill   *)
(* translate [Htr] (via exec_translateAddr_load_walk_u); the physical-side  *)
(* facts are stated at the filled state s'.  Thin glue over the generic     *)
(* exec_execute_LOAD_4_gpr_walk + the U pmpCheck grant.                     *)
(* ===================================================================== *)
Section VRU4Miss.
  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Variable v : bv 32.
  Variable region : PMA_Region.
  Variable s s' : mstate.
  Variable pa : mword 64.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let data2 : mword (4*1*8) :=
    update_subrange_vec_dec (zeros' (4*1*8)) (4*(0+1)*8-1) (4*0*8) v.
  Hypothesis Hrd : uint rd <> 0.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s = Some (Virtaddr ea, s).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr ea) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr ea)) (0 * 4))) (Load Data)) s
                   = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = User.
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1" : mword 1) = false.
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HpmpR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hpmam : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 4) s' = Some (false, s').
  Hypothesis Hdev : dev_addr pa = false.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N ->
    s'.(mem) !! (pa_add pa j) = Some (nth_byte v j).

  Lemma exec_execute_LOAD_4_U_miss (is_unsigned : bool) :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))) s
      = Some (RETIRE_SUCCESS,
              set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (extend_value is_unsigned data2))).
  Proof.
    assert (Hpmp : exec (pmpCheck (Physaddr pa) 4 (Load Data) User) s' = Some (None, s')).
    { exact (exec_pmpCheck_user_grant_load pa 4 s' HpmpA Hpmp_ord Hrange HpmpR). }
    exact (exec_execute_LOAD_4_gpr_walk User is_unsigned rs1 rd imm ea v region s s' pa
             Hrd Htea Halign Htr Hcp Hmprv Hpmp Hpmam Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  Qed.
End VRU4Miss.

(* ===================================================================== *)
(* U-mode width-4 register-generic STORE (SW).                          *)
(* ===================================================================== *)
Section VWU4.
  Context (ent : TLB_Entry) (vpn : mword 27).
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Variable region : PMA_Region.
  Variable s : mstate.
  Let offset := sign_extend' 64 imm.
  Let vrs2 := if Z.eqb (uint rs2) 0 then zero_reg
              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs).
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Let pa := u_pa ent ea vpn.

  (* stored-entry leaf facts at Store Data *)
  Hypothesis Hchk : forall (mxr do_sum : bool) s0,
    exec (check_PTE_permission (Store Data) User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
            (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s0
      = Some (PTE_Check_Success tt, s0).
  Hypothesis Hupd : update_PTE_Bits (tlb_get_pte 8 ent) (Store Data)
                    = (None : option (mword 64)).
  Hypothesis Hpbmt : forall s0, exec (tlb_get_pbmt ent) s0 = Some (PBMT_PMA, s0).
  Hypothesis Hmatch_tlb : match_TLB_Entry ent (mword_of_int 0 : mword 16)
                        (sign_extend' (57 - 12) vpn) = true.
  (* machine-state pins *)
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = User.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false.
  Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
  Hypothesis HES : exec (currentlyEnabled Ext_S) s = Some (true, s).
  Hypothesis Hsenv : register_lookup senvcfg s.(sregs) = mword_of_int 0.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = MENVCFG_S.
  Hypothesis Hsatpmode : _get_Satp64_Mode (Mk_Satp64 (register_lookup satp s.(sregs))) = ('b"1000" : mword 4).
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) (register_lookup satp s.(sregs)) : mword 64)) = (mword_of_int 0 : mword 16).
  Hypothesis Hvec : vec_access_dec (register_lookup tlb s.(sregs)) (tlb_hash (__id 39) vpn) = Some ent.
  (* va geometry at the effective address *)
  Hypothesis Halign : is_aligned_vaddr (Virtaddr ea) 4 = true.
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr ea))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr ea)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn.
  (* physical-side facts at the translated pa *)
  Hypothesis HpmpA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hpmp_ord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HpmpW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hpmam : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 4 = Some region.
  Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 4 = true.
  Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 4) s = Some (false, s).
  Hypothesis Hdev : dev_addr pa = false.

  Lemma exec_execute_STORE_4_U :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s
      = Some (RETIRE_SUCCESS,
              MState s.(sregs) (write_bytes s.(mem) pa 4
                (autocast (T := mword) (subrange_vec_dec vrs2 (Z.sub (Z.mul 4 8) 1) 0) : mword 32)) s.(mdev)).
  Proof.
    assert (Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr ea, s)).
    { apply exec_transform_effective_address_store_u; assumption. }
    assert (Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr ea)) (0 * 4))) (Store Data)) s
                  = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s)).
    { cbn [bits_of_virtaddr]. rewrite avi0_mul4.
      exact (exec_translateAddr_store_hit_u ent vpn ea
               (register_lookup satp s.(sregs)) (register_lookup tlb s.(sregs)) s
               Hchk Hupd Hpbmt Hmatch_tlb Hcp HSXL Hmprv eq_refl Hsatpmode Hasid
               eq_refl Hvec Hcanon Hvpn_def). }
    assert (Hpmp : exec (pmpCheck (Physaddr pa) 4 (Store Data) User) s = Some (None, s)).
    { exact (exec_pmpCheck_user_grant_store pa 4 s HpmpA Hpmp_ord Hrange HpmpW). }
    exact (exec_execute_STORE_4_gpr User rs2 rs1 imm ea region s pa
             Htea Halign Hcp Hmprv Htr Hpmp Hpmam Hpalign Hwrite Hc Hsig Hh Hdev).
  Qed.
End VWU4.
