(* WpSmodeGpr.v -- K2: the S-mode per-instruction CLIENT WPs on the SmodeCore
   infrastructure, for exactly the kernelvec repertoire:
     - c.addi16sp   [wp_caddi16sp_gpr_s (TLB hit) + wp_caddi16sp_gpr_s_fill
                     (instr #1: the fetch page-WALKS and fills the TLB)];
     - c.sdsp       [wp_csdsp_gpr_s (data-address TLB hit) +
                     wp_csdsp_gpr_s_fill (FIRST store: the data address is a
                     DIFFERENT page than the code page, so its translation
                     page-walks and fills the TLB at tlb_hash svpn)];
     - c.ldsp       [wp_cldsp_gpr_s (data hit; the epilogue loads run after
                     the stores installed the stack-page entry)];
     - jal          [wp_jal_gpr_s];
     - sret         [wp_sret_gpr, in WpSmodeSret.v].

   DATA-TRANSLATION DESIGN (recovered from the archived WpStoreWalk/WpKvStore
   and the vmem model): lookup_TLB indexes the direct-mapped TLB by
   [tlb_hash 39 vpn], so the fetch-installed superpage entry (slot 5 =
   tlb_hash of the CODE page vpn 0x80005) serves a DATA access only when
   tlb_hash svpn = 5.  In general the first store to the kernel stack page
   MISSES and page-walks: it re-reads the SAME single leaf PTE
   [pte_super @ pte_paddr root_ppn] (W permitted: flags 0xCF), and installs
   the SAME entry VALUE [pw_tlb_entry root_ppn 0] at slot [tlb_hash svpn]
   (superpage entries are keyed by the MASKED vpn, so the installed entry is
   identical to the fetch one).  Later stores/loads to the page HIT that slot.

   Layer plan:
     - Part A: pure S-mode Store/Load-Data lemmas (PMP W/R grants, the
       checked write/read, transform_effective_address, translateAddr for
       (Store Data)/(Load Data) on both the HIT and the WALK path, and the
       execute reductions exec_execute_STORE_8_gpr_S{,_walk} /
       exec_execute_LOAD_8_gpr_S) -- ports of the archived
       WpStoreS/WpStoreWalk/WpKvLoad onto the in-build base.
     - Part B: [wp_instr_s_config] -- the S-mode mirror of InstrBytes'
       [wp_instr_config]: the [wp_instr_s] variant for instructions that READ
       or WRITE the very cells [smode_config] bundles (the stores/loads need
       the mstatus.MXR / menvcfg.PMM VALUES, which the opaque bundle hides;
       SRET writes mstatus/cur_privilege).  It takes the UNBUNDLED cells and
       passes them INTO the caller's fupd (so the caller can read them at σ
       via reg_valid and/or reg_update them alongside its other writes).
     - Part C: the client WPs. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpLoad.
Require Import WpGpr WpMmodeJal WpGprRvcTor.
Require Import SmodeCore.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Part A.1 -- S-mode STORE write path (PMP W grant, checked_mem_write,   *)
(* mem_write_value, transform_effective_address).  Ported from the        *)
(* archived WpStoreS.v.                                                   *)
(* ===================================================================== *)

(* Supervisor PMP grant for a STORE (W bit). *)
Lemma exec_pmpCheck_supervisor_grant_store (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Store Data) Supervisor) s = Some (None, s).
Proof.
  intros HA Hord Hrange HW.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (Store Data)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* checked_mem_write in Supervisor mode with the W grant. *)
Lemma exec_checked_mem_write_ram_store_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 8 data (Store Data) pbmt Supervisor tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_store addr 8 s HA Hord Hrange HW)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_8 addr data s Hdev)).
  apply exec_returnM.
Qed.

Lemma exec_effectivePrivilege_store_S (m : mword 64) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  exec (effectivePrivilege (Store Data) m Supervisor) s = Some (Supervisor, s).
Proof.
  intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
  rewrite H. cbn [andb]. apply exec_returnm.
Qed.

Lemma exec_mem_write_value_8_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 64) (m : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_write_value (Physaddr addr) 8 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev Hms Hmprv Hpriv.
  unfold mem_write_value, mem_write_value_meta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_S m s Hmprv)).
  unfold mem_write_value_priv_meta. cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_checked_mem_write_ram_store_S pbmt addr region data s HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

Lemma exec_is_pmm_applicable_store_S s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (is_pmm_applicable (Store Data) Supervisor) s = Some (true, s).
Proof.
  intro Hmxr. unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Store Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec orb s = Some (true, s))
  end.
  { rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
    replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). rewrite Hmxr. apply exec_returnm. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_get_pmlen_store_S s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled ->
  exec (get_pmlen (Store Data) Supervisor) s = Some (0, s).
Proof.
  intros Hmxr Hpmm. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_store_S s Hmxr)).
  cbn match.
  assert (Hgp : exec (get_pmm Supervisor) s
          = Some (pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))), s)).
  { unfold get_pmm. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hgp).
  rewrite Hpmm.
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_store_S (ea : mword 64) (satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled ->
  exec (transform_effective_address (Virtaddr ea) (Store Data)) s
    = Some (pm_transform_VA (Virtaddr ea) 0, s).
Proof.
  intros Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm. unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_store_S _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_store_S s Hmxr Hpmm)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity). cbn match.
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* Part A.2 -- Sv39 translation of a SYMBOLIC data address in the 1GB     *)
(* identity superpage, for (Store Data) and (Load Data): TLB HIT at        *)
(* tlb_hash vpn (state-preserving) and the one-PTE WALK (fills the TLB).   *)
(* Ported from the archived WpStoreWalk.v / WpKvLoad.v.                    *)
(* ===================================================================== *)

Section SDataTranslate.
  Context (root_ppn : mword 44).

  (* The (symbolic) Sv39 output ppn for a 1GB superpage leaf with PTE ppn
     0x80000: concat(0x80000[43:18], vpn[17:0]); identity in-region. *)
  Definition sdata_ppn_out (vpn : mword 27) : mword 44 :=
    concat_vec (subrange_vec_dec (mword_of_int 0x80000 : mword 44) 43 18) (subrange_vec_dec vpn 17 0).

  Lemma exec_pt_walk_store_super (vpn : mword 27) (mxr do_sum : bool)
        (region : PMA_Region) (menvcfg0 : mword 64) s :
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    dev_addr (pte_paddr root_ppn) = false ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (pt_walk 39 vpn (Store Data) Supervisor mxr do_sum
            root_ppn 2 false tt) s
      = Some (Ok (Build_PTW_Output 39 (sdata_ppn_out vpn) (autocast (T := mword) pte_super)
                    (Physaddr (pte_paddr root_ppn)) 2 PBMT_PMA false, tt), s).
  Proof.
    intros Hvpn2 HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE.
    unfold pt_walk, Zwf_guarded.
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    assert (Hae1 : exec (Defs.assert_exp' (2 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (pte_paddr root_ppn : mword 64) by
        (unfold pte_paddr; rewrite Hvpn2; reflexivity);
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_read_pte_S (pte_paddr root_ppn) region pte_super s
                  HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes)).
    assert (Hinv : exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte_super 7 0))
                           (ext_bits_of_PTE pte_super)) s = Some (false, s))
      by (vm_compute; reflexivity).
    rewrite (execR_liftR_seq _ _ _ _ _ Hinv).
    match goal with |- context[pte_is_non_leaf ?f] =>
      replace (pte_is_non_leaf f) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    match goal with |- context[neq_vec ?a ?b] =>
      replace (neq_vec a b) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    change (2 >? 0) with true. cbv iota beta.
    assert (Hchk : exec (check_PTE_permission (Store Data) Supervisor mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte_super 7 0)) (ext_bits_of_PTE pte_super) tt) s
                   = Some (PTE_Check_Success tt, s))
      by (destruct mxr, do_sum; vm_compute; reflexivity).
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR (Defs.bind0 A B) s = Some (inr (PTE_Check_Success tt), s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite Hchk. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ HAB).
    cbv iota beta. cbn match.
    change (2 >? 0) with true. cbv iota beta.
    match goal with |- context[eq_vec (_get_PTE_Ext_N ?e) ?b] =>
      replace (eq_vec (_get_PTE_Ext_N e) b) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg menvcfg s)).
    rewrite Hmenv. rewrite HPBMTE. cbv iota beta.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite execR_returnR. cbn match.
    unfold sdata_ppn_out.
    repeat f_equal; (try apply bv_eq); vm_compute; reflexivity.
  Qed.

  (* The masked superpage base for any in-region vpn equals 0x80000 -- taken
     as bitvector hypotheses.  With these the installed entry is exactly
     pw_tlb_entry (the same superpage entry the fetch installs), only at the
     symbolic index tlb_hash vpn. *)
  Lemma exec_add_to_TLB_store_super (vpn : mword 27) (asid : mword 16) s :
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    exec (add_to_TLB 39 asid vpn (sdata_ppn_out vpn) (autocast (T := mword) pte_super)
            (Physaddr (pte_paddr root_ppn)) 2 false) s
      = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                                   (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Hmvpn Hmppn.
    unfold add_to_TLB. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb _)).
    rewrite exec_returnm.
    do 5 f_equal. unfold pw_tlb_entry.
    f_equal; first [ exact Hmvpn | exact Hmppn | vm_compute; reflexivity ].
  Qed.

  Lemma exec_translate_TLB_miss_store (vpn : mword 27) (mxr do_sum : bool) (asid : mword 16)
        (region : PMA_Region) (menvcfg0 : mword 64) s :
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    dev_addr (pte_paddr root_ppn) = false ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate_TLB_miss 39 asid root_ppn vpn
            (Store Data) Supervisor mxr do_sum tt) s
      = Some (Ok (sdata_ppn_out vpn, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                               (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_store_super vpn mxr do_sum region menvcfg0 s
                  Hvpn2 HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE)).
    cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_add_to_TLB_store_super vpn asid s Hmvpn Hmppn)).
    apply exec_returnm.
  Qed.

  Lemma exec_lookup_TLB_miss_data (vpn : mword 27) (asid : mword 16)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    exec (lookup_TLB 39 asid vpn) s = Some (None, s).
  Proof.
    intros Htlb Hvec.
    unfold lookup_TLB.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec. apply exec_returnm.
  Qed.

  Lemma exec_translate_store_walk (vpn : mword 27) (mxr do_sum : bool) (asid : mword 16)
        (region : PMA_Region) (menvcfg0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    dev_addr (pte_paddr root_ppn) = false ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate 39 asid root_ppn vpn
            (Store Data) Supervisor mxr do_sum tt) s
      = Some (Ok (sdata_ppn_out vpn, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_miss_data vpn asid tlbvec s Htlb Hvec)).
    cbn match.
    rewrite <- Htlb.
    apply (exec_translate_TLB_miss_store vpn mxr do_sum asid region menvcfg0 s
             Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE).
  Qed.

  (* FULL Sv39 translation of a SYMBOLIC store data address `a` in the 1GB
     identity superpage, with the stack page NOT yet in the TLB: the walk
     re-reads the same PTE (pte_paddr root_ppn) and FILLS the TLB at
     tlb_hash vpn (state change). *)
  Lemma exec_translateAddr_store_walk (a : mword 64) (vpn : mword 27)
        (region : PMA_Region) (menvcfg0 satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    (* canonical (sign-extended) 39-bit address *)
    neq_vec (bits_of_virtaddr (Virtaddr a))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false ->
    (* the Sv39 vpn the model extracts from `a` *)
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    (* superpage output ppn is the identity for `a` *)
    zero_extend' 64 (concat_vec (sdata_ppn_out vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub pagesize_bits 1) 0)) = a ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    dev_addr (pte_paddr root_ppn) = false ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translateAddr (Virtaddr a) (Store Data)) s
      = Some (Ok (Physaddr a, PBMT_PMA, init_ext_ptw),
              set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn (mword_of_int 0))))).
  Proof.
    intros Hcp HSXL Hmprv Hsatp Hmode Hppn Hasid Hcanon Hvpn_def Hident
           Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_store_S (register_lookup mstatus s.(sregs)) s Hmprv)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_store s)).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace bppn with root_ppn by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_store_walk vpn _ _ (mword_of_int 0) region menvcfg0 tlbvec s
                  Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

  (* ---- Data-address TLB HIT (state-preserving): a store/load to a stack
     page whose (superpage) entry sits at tlb_hash vpn. ---- *)
  Lemma exec_translate_TLB_hit_store_super (vpn : mword 27) (mxr do_sum : bool) s :
    exec (translate_TLB_hit 39 (mword_of_int 0 : mword 16) vpn (Store Data) Supervisor mxr do_sum
            tt (tlb_hash (__id 39) vpn) (pw_tlb_entry root_ppn (mword_of_int 0))) s
      = Some (Ok (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn, PBMT_PMA, tt), s).
  Proof.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[check_PTE_permission ?ac ?pr ?mx ?ds ?fl ?ex ?ep] =>
      assert (Hchk : exec (check_PTE_permission ac pr mx ds fl ex ep) s = Some (PTE_Check_Success tt, s))
        by (destruct mxr, do_sum; vm_compute; reflexivity) end.
    rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    assert (Hpbmt : exec (tlb_get_pbmt (pw_tlb_entry root_ppn (mword_of_int 0))) s = Some (PBMT_PMA, s))
      by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ Hpbmt). apply exec_returnm.
  Qed.

  Lemma exec_lookup_TLB_hit_data (vpn : mword 27) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    exec (lookup_TLB 39 (mword_of_int 0 : mword 16) vpn) s
      = Some (Some (tlb_hash (__id 39) vpn, pw_tlb_entry root_ppn (mword_of_int 0)), s).
  Proof.
    intros Htlb Hvec Hmask.
    unfold lookup_TLB.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec.
    match goal with |- context[match_TLB_Entry ?e ?a ?v] =>
      replace (match_TLB_Entry e a v) with true end.
    2:{ unfold match_TLB_Entry, pw_tlb_entry; cbn.
        rewrite Hmask. vm_compute; reflexivity. }
    apply exec_returnm.
  Qed.

  Lemma exec_translate_store_hit (vpn : mword 27) (mxr do_sum : bool)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    exec (translate 39 (mword_of_int 0 : mword 16) base_ppn vpn (Store Data) Supervisor mxr do_sum tt) s
      = Some (Ok (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn, PBMT_PMA, tt), s).
  Proof.
    intros Htlb Hvec Hmask.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_hit_data vpn tlbvec s Htlb Hvec Hmask)).
    cbn match.
    apply exec_translate_TLB_hit_store_super.
  Qed.

  Lemma exec_translateAddr_store_hit (a : mword 64) (vpn : mword 27)
        (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr a))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub pagesize_bits 1) 0)) = a ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    exec (translateAddr (Virtaddr a) (Store Data)) s
      = Some (Ok (Physaddr a, PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hcp HSXL Hmprv Hsatp Hmode Hasid Hcanon Hvpn_def Hident Htlb Hvec Hmask.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_store_S (register_lookup mstatus s.(sregs)) s Hmprv)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_store s)).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translate_store_hit vpn _ _ _ tlbvec s Htlb Hvec Hmask)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

  (* ---- the LOAD (Read-Data) mirror of the HIT path. ---- *)
  Lemma exec_effectivePrivilege_load_S (m : mword 64) s :
    eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
    exec (effectivePrivilege (Load Data) m Supervisor) s = Some (Supervisor, s).
  Proof.
    intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
    rewrite H. cbn [andb]. apply exec_returnm.
  Qed.

  Lemma exec_translate_TLB_hit_load_super (vpn : mword 27) (mxr do_sum : bool) s :
    exec (translate_TLB_hit 39 (mword_of_int 0 : mword 16) vpn (Load Data) Supervisor mxr do_sum
            tt (tlb_hash (__id 39) vpn) (pw_tlb_entry root_ppn (mword_of_int 0))) s
      = Some (Ok (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn, PBMT_PMA, tt), s).
  Proof.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[check_PTE_permission ?ac ?pr ?mx ?ds ?fl ?ex ?ep] =>
      assert (Hchk : exec (check_PTE_permission ac pr mx ds fl ex ep) s = Some (PTE_Check_Success tt, s))
        by (destruct mxr, do_sum; vm_compute; reflexivity) end.
    rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    assert (Hpbmt : exec (tlb_get_pbmt (pw_tlb_entry root_ppn (mword_of_int 0))) s = Some (PBMT_PMA, s))
      by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ Hpbmt). apply exec_returnm.
  Qed.

  Lemma exec_translate_load_hit (vpn : mword 27) (mxr do_sum : bool)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    exec (translate 39 (mword_of_int 0 : mword 16) base_ppn vpn (Load Data) Supervisor mxr do_sum tt) s
      = Some (Ok (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn, PBMT_PMA, tt), s).
  Proof.
    intros Htlb Hvec Hmask.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_hit_data vpn tlbvec s Htlb Hvec Hmask)).
    cbn match.
    apply exec_translate_TLB_hit_load_super.
  Qed.

  Lemma exec_translateAddr_load_hit (a : mword 64) (vpn : mword 27)
        (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr a))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub pagesize_bits 1) 0)) = a ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (pw_tlb_entry root_ppn (mword_of_int 0)) ->
    and_vec (sign_extend' (57 - 12) vpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    exec (translateAddr (Virtaddr a) (Load Data)) s
      = Some (Ok (Physaddr a, PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hcp HSXL Hmprv Hsatp Hmode Hasid Hcanon Hvpn_def Hident Htlb Hvec Hmask.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_load_S (register_lookup mstatus s.(sregs)) s Hmprv)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_load s)).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translate_load_hit vpn _ _ _ tlbvec s Htlb Hvec Hmask)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

  (* ---- the LOAD (Read-Data) mirror of the WALK path: the data address
     MISSES the TLB, page-walks the same superpage PTE and FILLS the TLB
     at tlb_hash vpn.  Mechanical (Load Data) copies of the store-walk
     lemmas above. ---- *)
  Lemma exec_pt_walk_load_super (vpn : mword 27) (mxr do_sum : bool)
        (region : PMA_Region) (menvcfg0 : mword 64) s :
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    dev_addr (pte_paddr root_ppn) = false ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (pt_walk 39 vpn (Load Data) Supervisor mxr do_sum
            root_ppn 2 false tt) s
      = Some (Ok (Build_PTW_Output 39 (sdata_ppn_out vpn) (autocast (T := mword) pte_super)
                    (Physaddr (pte_paddr root_ppn)) 2 PBMT_PMA false, tt), s).
  Proof.
    intros Hvpn2 HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE.
    unfold pt_walk, Zwf_guarded.
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    assert (Hae1 : exec (Defs.assert_exp' (2 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (pte_paddr root_ppn : mword 64) by
        (unfold pte_paddr; rewrite Hvpn2; reflexivity);
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_read_pte_S (pte_paddr root_ppn) region pte_super s
                  HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes)).
    assert (Hinv : exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte_super 7 0))
                           (ext_bits_of_PTE pte_super)) s = Some (false, s))
      by (vm_compute; reflexivity).
    rewrite (execR_liftR_seq _ _ _ _ _ Hinv).
    match goal with |- context[pte_is_non_leaf ?f] =>
      replace (pte_is_non_leaf f) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    match goal with |- context[neq_vec ?a ?b] =>
      replace (neq_vec a b) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    change (2 >? 0) with true. cbv iota beta.
    assert (Hchk : exec (check_PTE_permission (Load Data) Supervisor mxr do_sum
                     (Mk_PTE_Flags (subrange_vec_dec pte_super 7 0)) (ext_bits_of_PTE pte_super) tt) s
                   = Some (PTE_Check_Success tt, s))
      by (destruct mxr, do_sum; vm_compute; reflexivity).
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR (Defs.bind0 A B) s = Some (inr (PTE_Check_Success tt), s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite Hchk. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ HAB).
    cbv iota beta. cbn match.
    change (2 >? 0) with true. cbv iota beta.
    match goal with |- context[eq_vec (_get_PTE_Ext_N ?e) ?b] =>
      replace (eq_vec (_get_PTE_Ext_N e) b) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg menvcfg s)).
    rewrite Hmenv. rewrite HPBMTE. cbv iota beta.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite execR_returnR. cbn match.
    unfold sdata_ppn_out.
    repeat f_equal; (try apply bv_eq); vm_compute; reflexivity.
  Qed.

  Lemma exec_translate_TLB_miss_load (vpn : mword 27) (mxr do_sum : bool) (asid : mword 16)
        (region : PMA_Region) (menvcfg0 : mword 64) s :
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    dev_addr (pte_paddr root_ppn) = false ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate_TLB_miss 39 asid root_ppn vpn
            (Load Data) Supervisor mxr do_sum tt) s
      = Some (Ok (sdata_ppn_out vpn, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                               (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_load_super vpn mxr do_sum region menvcfg0 s
                  Hvpn2 HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE)).
    cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_add_to_TLB_store_super vpn asid s Hmvpn Hmppn)).
    apply exec_returnm.
  Qed.

  Lemma exec_translate_load_walk (vpn : mword 27) (mxr do_sum : bool) (asid : mword 16)
        (region : PMA_Region) (menvcfg0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    dev_addr (pte_paddr root_ppn) = false ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate 39 asid root_ppn vpn
            (Load Data) Supervisor mxr do_sum tt) s
      = Some (Ok (sdata_ppn_out vpn, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn asid)))).
  Proof.
    intros Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_miss_data vpn asid tlbvec s Htlb Hvec)).
    cbn match.
    rewrite <- Htlb.
    apply (exec_translate_TLB_miss_load vpn mxr do_sum asid region menvcfg0 s
             Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE).
  Qed.

  Lemma exec_translateAddr_load_walk (a : mword 64) (vpn : mword 27)
        (region : PMA_Region) (menvcfg0 satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr a))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec (sdata_ppn_out vpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub pagesize_bits 1) 0)) = a ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
    subrange_vec_dec vpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec vpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out vpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (pte_paddr root_ppn : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (pte_paddr root_ppn)) 8 = Some region ->
    is_aligned_paddr (Physaddr (pte_paddr root_ppn)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (pte_paddr root_ppn)) 8) s = Some (false, s) ->
    dev_addr (pte_paddr root_ppn) = false ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (pte_paddr root_ppn) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translateAddr (Virtaddr a) (Load Data)) s
      = Some (Ok (Physaddr a, PBMT_PMA, init_ext_ptw),
              set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some (pw_tlb_entry root_ppn (mword_of_int 0))))).
  Proof.
    intros Hcp HSXL Hmprv Hsatp Hmode Hppn Hasid Hcanon Hvpn_def Hident
           Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_load_S (register_lookup mstatus s.(sregs)) s Hmprv)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_load s)).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace bppn with root_ppn by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_load_walk vpn _ _ (mword_of_int 0) region menvcfg0 tlbvec s
                  Htlb Hvec Hvpn2 Hmvpn Hmppn HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hdev Hbytes Hmenv HPBMTE)).
    cbn match.
    rewrite execR_returnR. cbn match.
    rewrite Hident.
    reflexivity.
  Qed.

End SDataTranslate.

(* ===================================================================== *)
(* The BRIDGE between the two data-identity phrasings: the ppn a TLB HIT *)
(* on the identity superpage entry computes [tlb_get_ppn] equals the ppn *)
(* the page WALK computes [sdata_ppn_out] -- both are                    *)
(* 0x80000 | (vpn & 0x3FFFF).  Lets the unified (tlb_inv) store/load     *)
(* clients carry ONE ident premise (the tlb_get_ppn form) and derive the *)
(* walk form.                                                            *)
(* ===================================================================== *)

(* bv_swrap agrees with the argument modulo the modulus. *)
Lemma bv_swrap_mod (n : N) (z : Z) :
  (bv_swrap n z) mod (bv_modulus n) = z mod (bv_modulus n).
Proof.
  unfold bv_swrap, bv_wrap.
  rewrite Zminus_mod_idemp_l.
  f_equal. ring.
Qed.

(* testbit of bv_signed below the width = testbit of bv_unsigned. *)
Lemma bv_signed_testbit_low (n : N) (b : bv n) (i : Z) :
  0 <= i < Z.of_N n ->
  Z.testbit (bv_signed b) i = Z.testbit (bv_unsigned b) i.
Proof.
  intros Hi.
  unfold bv_signed.
  rewrite <- (Z.mod_pow2_bits_low (bv_swrap n (bv_unsigned b)) (Z.of_N n) i) by lia.
  rewrite <- (Z.mod_pow2_bits_low (bv_unsigned b) (Z.of_N n) i) by lia.
  f_equal.
  pose proof (bv_swrap_mod n (bv_unsigned b)) as Hm.
  unfold bv_modulus in Hm. exact Hm.
Qed.

Lemma tlb_get_ppn_pw (root_ppn : mword 44) (vpn : mword 27) :
  tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) vpn = sdata_ppn_out vpn.
Proof.
  unfold tlb_get_ppn, pw_tlb_entry, sdata_ppn_out.
  cbn [TLB_Entry_levelMask TLB_Entry_ppn].
  cbv [trunc vector_truncate slice or_vec and_vec sign_extend' zero_extend'
       concat_vec subrange_vec_dec Operators_mwords.sign_extend Operators_mwords.zero_extend
       Operators_mwords.exts_vec Operators_mwords.extz_vec
       Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  change (43 - 18 + 1) with 26.
  change (17 - 0 + 1) with 18.
  cbn.
  change (Z.of_N (26 + 18)) with 44.
  change ((26 + 18)%N) with 44%N.
  cbn.
  change (26 + 18) with 44.
  cbn.
  cbv [MachineWord.slice MachineWord.or MachineWord.and MachineWord.zero_extend
       MachineWord.sign_extend MachineWord.concat MachineWord.Z_to_word mword_of_int
       Values.mword_of_int].
  apply bv_eq.
  rewrite bv_extract_unsigned.
  rewrite bv_or_unsigned.
  rewrite bv_and_unsigned.
  rewrite (@bv_zero_extend_unsigned 44 64 _ ltac:(lia)).
  rewrite (@bv_zero_extend_unsigned 45 64 _ ltac:(lia)).
  rewrite bv_sign_extend_unsigned.
  rewrite (@bv_concat_unsigned 26 44 18 _ _ eq_refl).
  rewrite !bv_extract_unsigned.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small (MachineWord.Z_idx 44) 524288
             ltac:(vm_compute; split; [discriminate | reflexivity])).
  rewrite (bv_wrap_small (MachineWord.Z_idx (57 - 12)) 262143
             ltac:(vm_compute; split; [discriminate | reflexivity])).
  rewrite !Z.shiftr_0_r.
  replace (bv_wrap 26 (Z.shiftr 524288 (Z.of_N 18))) with 2 by (vm_compute; reflexivity).
  apply Z.bits_inj'. intros i Hi.
  rewrite (bv_wrap_spec _ _ i Hi).
  rewrite !Z.lor_spec. rewrite Z.land_spec.
  rewrite (Z.shiftl_spec _ _ i Hi).
  rewrite (bv_wrap_spec 18 _ i Hi).
  (* both sides now carry the same constant-bit term testbit 2 (i - 18) *)
  change 2 with (Z.pow 2 1).
  rewrite (Z.pow2_bits_eqb 1 (i - Z.of_N 18) ltac:(lia)).
  change 262143 with (Z.ones 18).
  rewrite (Z.testbit_ones_nonneg 18 i ltac:(lia) Hi).
  change (MachineWord.Z_idx 44) with 44%N.
  destruct (Z.ltb_spec i 18) as [Hlt | Hge].
  - (* low bits: the vpn bits *)
    rewrite (bv_wrap_spec 64 _ i Hi).
    rewrite (bv_signed_testbit_low 27 _ i ltac:(lia)).
    rewrite !andb_true_r.
    destruct (Z.eqb_spec 1 (i - Z.of_N 18)); [lia |].
    cbn [orb].
    rewrite (bool_decide_true (i < Z.of_N 44) ltac:(lia)).
    rewrite (bool_decide_true (i < Z.of_N 18) ltac:(lia)).
    rewrite (bool_decide_true (i < Z.of_N 64) ltac:(lia)).
    cbn [andb orb]. reflexivity.
  - (* i >= 18: only the constant bit (i = 19) can be set *)
    rewrite !andb_false_r.
    rewrite (bool_decide_false (i < Z.of_N 18) ltac:(lia)).
    cbn [andb orb].
    rewrite !orb_false_r.
    destruct (Z.eqb_spec 1 (i - Z.of_N 18)) as [He | Hne].
    + rewrite (bool_decide_true (i < Z.of_N 44) ltac:(lia)). reflexivity.
    + rewrite andb_false_r. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* RAM-range geometry for the S-mode gigapage identity map: the remaining  *)
(* two per-address obligations that need [sdata_ppn_out]/[tlb_get_ppn_pw]  *)
(* (the others -- ram_canonical, ram_svpn2, ram_mask, ram_mvpn,            *)
(* svpn_of_unsigned -- live in RiscvExtras).  Together they let the S-mode *)
(* load/store WPs discharge the whole superpage-identity geometry from an  *)
(* owned points-to (addr_is_ram) instead of taking it as preconditions.    *)
(* ---------------------------------------------------------------------- *)

(* superpage mask fact, output-PPN side. *)
Lemma ram_mppn (a : mword 64) :
  addr_is_ram a ->
  zero_extend' 44 (and_vec (sdata_ppn_out (svpn_of a)) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44).
Proof.
  intros _.
  generalize (svpn_of a). intro vpn.
  unfold sdata_ppn_out.
  cbv [and_vec or_vec not_vec sign_extend' zero_extend' concat_vec subrange_vec_dec
       Operators_mwords.sign_extend Operators_mwords.zero_extend Operators_mwords.exts_vec
       Operators_mwords.extz_vec Operators_mwords.word_binop Operators_mwords.word_unop
       Operators_mwords.with_word' SailStdpp.Values.with_word to_word get_word autocast].
  cbn.
  change (43 - 18 + 1) with 26.
  change (17 - 0 + 1) with 18.
  cbn.
  change (Z.of_N (26 + 18)) with 44.
  change ((26 + 18)%N) with 44%N.
  cbn.
  change (26 + 18) with 44.
  cbn.
  cbv [MachineWord.slice MachineWord.or MachineWord.and MachineWord.not MachineWord.zero_extend
       MachineWord.sign_extend MachineWord.concat MachineWord.Z_to_word mword_of_int Values.mword_of_int].
  apply bv_eq.
  rewrite (@bv_zero_extend_unsigned 44 44 _ ltac:(lia)).
  rewrite bv_and_unsigned.
  rewrite (@bv_concat_unsigned 26 44 18 _ _ eq_refl).
  rewrite bv_not_unsigned.
  rewrite (@bv_zero_extend_unsigned 18 44 _ ltac:(lia)).
  rewrite !bv_extract_unsigned.
  rewrite !Z_to_bv_unsigned.
  assert (Hb1 : bv_wrap 26 (bv_wrap (MachineWord.MachineWord.Z_idx 44) 524288 ≫ Z.of_N 18) = 2)
    by (vm_compute; reflexivity).
  rewrite Hb1.
  assert (Hz : bv_wrap 18 (Z.lnot (bv_unsigned (zeros 18))) = 262143) by (vm_compute; reflexivity).
  rewrite Hz.
  rewrite Z.shiftr_0_r.
  assert (Hsh : (2 ≪ Z.of_N 18) = 524288) by (vm_compute; reflexivity).
  rewrite Hsh.
  assert (Hrhs : bv_wrap (MachineWord.MachineWord.Z_idx 44) 524288 = 524288) by (vm_compute; reflexivity).
  rewrite Hrhs.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec. rewrite Z.lor_spec.
  rewrite (bv_wrap_spec 44 (Z.lnot 262143) i Hi).
  rewrite (bv_wrap_spec 18 (bv_unsigned vpn) i Hi).
  rewrite (Z.lnot_spec 262143 i ltac:(lia)).
  change 262143 with (Z.ones 18).
  rewrite (Z.testbit_ones_nonneg 18 i ltac:(lia) Hi).
  change 524288 with (2 ^ 19).
  rewrite (Z.pow2_bits_eqb 19 i ltac:(lia)).
  destruct (Z.ltb_spec i 18) as [Hlt | Hge].
  - replace (i <? 18) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (19 =? i) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. rewrite !andb_false_r. reflexivity.
  - rewrite (bool_decide_false (i < Z.of_N 18) ltac:(lia)).
    replace (i <? 18) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [negb]. rewrite andb_false_l. rewrite orb_false_r. rewrite andb_true_r.
    destruct (Z.eqb_spec 19 i) as [He | Hne].
    + rewrite (bool_decide_true (i < Z.of_N 44) ltac:(lia)). reflexivity.
    + reflexivity.
Qed.

(* the gigapage identity translation: a RAM vaddr walks to itself. *)
Lemma ram_ident (root_ppn : mword 44) (a : mword 64) :
  addr_is_ram a ->
  zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) (svpn_of a))
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub pagesize_bits 1) 0)) = a.
Proof.
  intros Hram. pose proof Hram as [Hlo Hhi]. rewrite uint_unsigned in Hlo, Hhi. unfold ram_base, ram_size in *.
  rewrite tlb_get_ppn_pw. unfold sdata_ppn_out.
  cbn [bits_of_virtaddr]. unfold pagesize_bits.
  apply bv_eq. symmetry.
  cbv [trunc vector_truncate slice or_vec and_vec sign_extend' zero_extend'
       concat_vec subrange_vec_dec Operators_mwords.sign_extend Operators_mwords.zero_extend
       Operators_mwords.exts_vec Operators_mwords.extz_vec
       Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  change (12 - 1 - 0 + 1) with 12.
  change (43 - 18 + 1) with 26.
  change (17 - 0 + 1) with 18.
  cbn.
  change (Z.of_N (26 + 18)) with 44.
  change ((26 + 18)%N) with 44%N.
  change (Z.of_N (44 + 12)) with 56.
  change ((44 + 12)%N) with 56%N.
  cbn.
  change (26 + 18) with 44.
  change (44 + 12) with 56.
  cbn.
  cbv [MachineWord.slice MachineWord.or MachineWord.zero_extend MachineWord.concat
       MachineWord.Z_to_word mword_of_int Values.mword_of_int].
  rewrite (@bv_zero_extend_unsigned (44 + 12)%N 64 _ ltac:(lia)).
  rewrite (@bv_concat_unsigned 44 (44 + 12) 12 _ _ eq_refl).
  rewrite (@bv_concat_unsigned 26 (26 + 18) 18 _ _ eq_refl).
  rewrite !bv_extract_unsigned.
  rewrite !Z_to_bv_unsigned.
  change (bv_unsigned (get_word (bits_of_virtaddr (Virtaddr a)))) with (bv_unsigned a).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 12.
  change (Z.of_N 0) with 0.
  change (Z.of_N 18) with 18.
  change (Z.of_N 12) with 12.
  rewrite !Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (39 - 1 - 0 + 1)) with 39%N.
  assert (Hconst : bv_wrap 26 (bv_wrap 44 524288 ≫ 18) ≪ 18 = 524288) by (vm_compute; reflexivity).
  rewrite Hconst.
  assert (E39 : bv_wrap 39 (bv_unsigned a) = bv_unsigned a).
  { apply bv_wrap_small. assert (bv_modulus 39 = 549755813888) as -> by (vm_compute; reflexivity). lia. }
  rewrite E39.
  assert (E27 : bv_wrap 27 (bv_unsigned a ≫ 12) = bv_unsigned a ≫ 12).
  { apply bv_wrap_small.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned a) 12 ltac:(lia)). change (2 ^ 12) with 4096.
    assert (bv_modulus 27 = 134217728) as -> by (vm_compute; reflexivity).
    split. apply Z.div_pos. lia. lia. apply Z.div_lt_upper_bound. lia. lia. }
  rewrite E27.
  assert (Hd31 : bv_unsigned a / 2147483648 = 1).
  { assert (1 <= bv_unsigned a / 2147483648) by (apply Z.div_le_lower_bound; lia).
    assert (bv_unsigned a / 2147483648 < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hd30 : bv_unsigned a / 1073741824 = 2).
  { assert (2 <= bv_unsigned a / 1073741824) by (apply Z.div_le_lower_bound; lia).
    assert (bv_unsigned a / 1073741824 < 3) by (apply Z.div_lt_upper_bound; lia). lia. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec.
  rewrite (Z.shiftl_spec _ 12 i Hi).
  rewrite (bv_wrap_spec 12 (bv_unsigned a) i Hi).
  destruct (Z.ltb_spec i 12) as [Hi12 | Hi12].
  - rewrite (bool_decide_true (i < Z.of_N 12) ltac:(lia)). rewrite andb_true_l.
    rewrite (Z.testbit_neg_r _ (i - 12) ltac:(lia)). rewrite orb_false_l. reflexivity.
  - rewrite (bool_decide_false (i < Z.of_N 12) ltac:(lia)). rewrite andb_false_l. rewrite orb_false_r.
    rewrite Z.lor_spec.
    rewrite (bv_wrap_spec 18 (bv_unsigned a ≫ 12) (i - 12) ltac:(lia)).
    rewrite (Z.shiftr_spec (bv_unsigned a) 12 (i - 12) ltac:(lia)).
    replace (i - 12 + 12) with i by lia.
    change 524288 with (2 ^ 19).
    rewrite (Z.pow2_bits_eqb 19 (i - 12) ltac:(lia)).
    destruct (Z.ltb_spec (i - 12) 18) as [Hlt | Hge].
    + rewrite (bool_decide_true (i - 12 < Z.of_N 18) ltac:(lia)). rewrite andb_true_l.
      replace (19 =? i - 12) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite orb_false_l. reflexivity.
    + rewrite (bool_decide_false (i - 12 < Z.of_N 18) ltac:(lia)). rewrite andb_false_l. rewrite orb_false_r.
      destruct (Z.eqb_spec 19 (i - 12)) as [He | Hne].
      * assert (i = 31) as -> by lia.
        apply (proj2 (Z.testbit_true (bv_unsigned a) 31 ltac:(lia))).
        change (2 ^ 31) with 2147483648. rewrite Hd31. reflexivity.
      * assert (i = 30 \/ i >= 32) as [-> | Hge32] by lia.
        -- apply (proj2 (Z.testbit_false (bv_unsigned a) 30 ltac:(lia))).
           change (2 ^ 30) with 1073741824. rewrite Hd30. reflexivity.
        -- apply (proj1 (Z.bounded_iff_bits_nonneg 32 (bv_unsigned a) ltac:(lia) ltac:(lia))
                    ltac:(change (2 ^ 32) with 4294967296; lia) i ltac:(lia)).
Qed.

(* [uint] of a small offset from a base that does not wrap: used to turn the
   RAM-ness of an access's LAST byte into the fit bound [uint a + 8 <= ram top]
   that [ram_pmp_match] needs. *)
Lemma uint_pa_add (a : mword 64) (j : nat) :
  (uint a + Z.of_nat j < 18446744073709551616)%Z ->
  uint (pa_add a j) = uint a + Z.of_nat j.
Proof.
  intro Hlt. rewrite !uint_unsigned in Hlt |- *.
  unfold pa_add, add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hj : bv_unsigned (mword_of_int (Z.of_nat j) : mword 64) = Z.of_nat j).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    pose proof (bv_unsigned_in_range 64 a) as Har. destruct Har as [Har _].
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
    split.
    - apply Nat2Z.is_nonneg.
    - apply Z.le_lt_trans with (bv_unsigned a + Z.of_nat j).
      + rewrite <- (Z.add_0_l (Z.of_nat j)) at 1. apply Z.add_le_mono_r. exact Har.
      + exact Hlt. }
  rewrite Hj.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a) as Har. destruct Har as [Har _].
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  split.
  - apply Z.add_nonneg_nonneg. exact Har. apply Nat2Z.is_nonneg.
  - exact Hlt.
Qed.


(* ===================================================================== *)
(* Part A.3 -- S-mode LOAD read path (PMP R grant for (Load Data),        *)
(* checked_mem_read, mem_read, transform), ported from archived WpKvLoad. *)
(* ===================================================================== *)

(* Supervisor PMP grant for a LOAD of DATA (R bit).  (SmodeCore's
   exec_pmpCheck_supervisor_grant_load is the (Load PageTableEntry) flavour
   used by the page walk; this is the (Load Data) one.) *)
Lemma exec_pmpCheck_supervisor_grant_load_data (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Load Data) Supervisor) s = Some (None, s).
Proof.
  intros HA Hord Hrange HR.
  unfold pmpCheck. rewrite exec_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_bind0.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR (foreach_ZM_up F T S V B) s = Some (inl None, s)) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_bind.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_bind.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (Load Data)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* checked_mem_read in Supervisor mode with the R grant. *)
Lemma exec_checked_mem_read_ram_load_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt Supervisor (Physaddr addr) 8 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_supervisor_grant_load_data addr 8 s HA Hord Hrange HR)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_8 addr w s Hdev Hbytes)).
  apply exec_returnM.
Qed.

(* mem_read for Load Data in Supervisor mode, width 8 (needs MPRV=0). *)
Lemma exec_mem_read_load_S (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 64) (m : mword 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) 8 false false false)
       s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes Hms Hmprv Hpriv.
  unfold mem_read.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hms.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load_S m s Hmprv)).
  unfold mem_read_priv.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_load_S with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Lemma exec_is_pmm_applicable_load_S s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  exec (is_pmm_applicable (Load Data) Supervisor) s = Some (true, s).
Proof.
  intro Hmxr. unfold is_pmm_applicable.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (InstructionFetch tt)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (Load PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
  replace (generic_neq (Load Data) (Store PageTableEntry)) with true by (vm_compute; reflexivity). cbn match.
  match goal with
  | |- context [ and_boolM ?orb _ ] => assert (Hor : exec orb s = Some (true, s))
  end.
  { rewrite (exec_or_boolM_Some _ _ _ _ _ (exec_returnM _ s)).
    replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). rewrite Hmxr. apply exec_returnm. }
  rewrite (exec_and_boolM_Some _ _ _ _ _ Hor).
  cbn match.
  rewrite (exec_returnM _ s).
  replace (xlen =? 64) with true by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma exec_get_pmlen_load_S s :
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled ->
  exec (get_pmlen (Load Data) Supervisor) s = Some (0, s).
Proof.
  intros Hmxr Hpmm. unfold get_pmlen.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_pmm_applicable_load_S s Hmxr)).
  cbn match.
  assert (Hgp : exec (get_pmm Supervisor) s
          = Some (pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))), s)).
  { unfold get_pmm. rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hgp).
  rewrite Hpmm.
  apply exec_returnM.
Qed.

Lemma exec_transform_effective_address_load_S (ea : mword 64) (satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true ->
  pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled ->
  exec (transform_effective_address (Virtaddr ea) (Load Data)) s
    = Some (pm_transform_VA (Virtaddr ea) 0, s).
Proof.
  intros Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm. unfold transform_effective_address.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_load_S _ s Hmprv)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_get_pmlen_load_S s Hmxr Hpmm)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
  replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity). cbn match.
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* Part A.4 -- S-mode vmem write/read + execute reductions.               *)
(* HIT path: translation is state-preserving (taken as hypothesis Htr).   *)
(* WALK path: translation FILLS the TLB (s -> s' = set_reg s tlb tlbf).   *)
(* Ported from archived WpStoreS (SWS/VWgS/ExecStoreGS), WpStoreWalk      *)
(* (SWPATH), WpKvLoad (RWS/RWgS/ExecLoadGS).                              *)
(* ===================================================================== *)

Section SWS.
Variable a : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 8))) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_addr_8_S :
  exec (vmem_write_addr (Virtaddr a) 8 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)).
Proof.
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0%Z, true), MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr).
      cbn [bits_of_virtaddr] in *. cbn match.
      assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s
                    = Some (tt, s)) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s = Some (inr tt, s))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s
                           = Some (inr true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)))
      end.
      { match goal with
        | |- execR (Defs.bind0 _ ?Nbody) s = _ => set (NN := Nbody)
        end.
        rewrite (execR_bind0_Some _ _ _ _ Hscm).
        unfold NN; clear NN.
        match goal with
        | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
            change (execR B ss = R)
        end.
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea (zero_extend' 64 (add_vec_int a (0*8))) s)).
        cbn match.
        match goal with
        | |- context [ mem_write_value ?pp 8 ?D (Store Data) ?pb false false false ] =>
            replace D with data
        end.
        2: { symmetry.
             change (8*(0+1)*8-1) with 63. change (8*0*8) with 0. change (8*8) with 64.
             change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold subrange_vec_dec. change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold to_word_idx, to_word, get_word, MachineWord.slice.
             rewrite MachineWord.cast_idx_refl.
             apply bv_eq. rewrite bv_extract_unsigned.
             change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
             apply bv_wrap_bv_unsigned. }
        rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_write_value_8_S PBMT_PMA (zero_extend' 64 (add_vec_int a (0*8))) region data
             (register_lookup mstatus s.(sregs)) s HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp)).
        cbn match.
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
      cbn.
      apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.
End SWS.

(* register-generic 8-byte S-mode vmem_write: base from rs1, value [data]. *)
Section VWgS.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_8_gpr_S :
  exec (vmem_write (Regidx rs1) offset 8 data (Store Data) false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) pa 8 data) s.(mdev)).
Proof.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_write_addr_8_S a8 data region s Halign Hcp Hmprv Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
  reflexivity.
Qed.
End VWgS.

(* register-generic 8-byte S-mode STORE execute: base from rs1, value from rs2. *)
Section ExecStoreGS.
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
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_execute_STORE_8_gpr_S :
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s
    = Some (RETIRE_SUCCESS, MState s.(sregs) (write_bytes s.(mem) pa 8 vrs2) s.(mdev)).
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
  unfold execute_STORE.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_write_8_gpr_S rs1 offset _ region satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
  cbn match.
  rewrite (exec_returnM _ _).
  rewrite autocast_subrange_id.
  reflexivity.
Qed.
End ExecStoreGS.

(* ---- state-CHANGING store path: the store's data translation is a page
   walk that fills the TLB (s -> s' = set_reg s tlb tlbf). ---- *)
Section SWSwalk.
Variable a : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
Variable s : mstate.
Let s' := set_reg s tlb tlbf.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hcp : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 8))) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_addr_8_S_walk :
  exec (vmem_write_addr (Virtaddr a) 8 data (Store Data) false false false) s
    = Some (Ok true, MState s'.(sregs) (write_bytes s.(mem) pa 8 data) s'.(mdev)).
Proof.
  unfold vmem_write_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s
                 = Some (inr (true, 0%Z, true), MState s'.(sregs) (write_bytes s.(mem) pa 8 data) s'.(mdev)))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr).
      cbn [bits_of_virtaddr] in *. cbn match.
      assert (Hsc : exec (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51") s'
                    = Some (tt, s')) by reflexivity.
      assert (Hscm : execR (Defs.liftR (assert_exp (Bool.eqb false (is_store_conditional (Store Data))) "sys/vmem_utils.sail:197.50-197.51")
                            : Defs.monadR (result bool ExecutionResult) exception unit) s' = Some (inr tt, s'))
        by (rewrite execR_liftR; rewrite Hsc; reflexivity).
      match goal with
      | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
          assert (Hwrloop : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s'
                           = Some (inr true, MState s'.(sregs) (write_bytes s.(mem) pa 8 data) s'.(mdev)))
      end.
      { match goal with
        | |- execR (Defs.bind0 _ ?Nbody) s' = _ => set (NN := Nbody)
        end.
        rewrite (execR_bind0_Some _ _ _ _ Hscm).
        unfold NN; clear NN.
        match goal with
        | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
            change (execR B ss = R)
        end.
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_mem_write_ea (zero_extend' 64 (add_vec_int a (0*8))) s')).
        cbn match.
        match goal with
        | |- context [ mem_write_value ?pp 8 ?D (Store Data) ?pb false false false ] =>
            replace D with data
        end.
        2: { symmetry.
             change (8*(0+1)*8-1) with 63. change (8*0*8) with 0. change (8*8) with 64.
             change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold subrange_vec_dec. change (63 - 0 + 1) with 64. rewrite autocast_id.
             unfold to_word_idx, to_word, get_word, MachineWord.slice.
             rewrite MachineWord.cast_idx_refl.
             apply bv_eq. rewrite bv_extract_unsigned.
             change (Z.of_N (MachineWord.Z_idx 0)) with 0. rewrite Z.shiftr_0_r.
             apply bv_wrap_bv_unsigned. }
        assert (Hmem' : s'.(mem) = s.(mem)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_write_value_8_S PBMT_PMA (zero_extend' 64 (add_vec_int a (0*8))) region data
             (register_lookup mstatus s'.(sregs)) s' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev eq_refl Hmprv Hcp)).
        cbn match.
        rewrite Hmem'.
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrloop).
      cbn.
      apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. reflexivity.
Qed.
End SWSwalk.

(* register-generic 8-byte S-mode vmem_write whose translation WALKS (fills TLB). *)
Section VWgSwalk.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable data : bv 64.
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
Variable s : mstate.
Let s' := set_reg s tlb tlbf.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_vmem_write_8_gpr_S_walk :
  exec (vmem_write (Regidx rs1) offset 8 data (Store Data) false false false) s
    = Some (Ok true, MState s'.(sregs) (write_bytes s.(mem) pa 8 data) s'.(mdev)).
Proof.
  unfold vmem_write. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_store_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_write_addr_8_S_walk a8 data region tlbf s Halign Hcp' Hmprv' Htr HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev).
  reflexivity.
Qed.
End VWgSwalk.

(* register-generic 8-byte S-mode STORE execute whose translation WALKS. *)
Section ExecStoreGSwalk.
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
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Store Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hwrite : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_writable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_writable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.

Lemma exec_execute_STORE_8_gpr_S_walk :
  exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s
    = Some (RETIRE_SUCCESS, MState s'.(sregs) (write_bytes s.(mem) pa 8 vrs2) s'.(mdev)).
Proof.
  change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
    with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
  unfold execute_STORE.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:320.28-320.29" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_write_8_gpr_S_walk rs1 offset _ region satp0 tlbf s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr Hcp' Hmprv' HA Hord Hrange HW Hmatch Hpalign Hwrite Hc Hsig Hh Hdev)).
  cbn match.
  rewrite (exec_returnM _ _).
  rewrite autocast_subrange_id.
  reflexivity.
Qed.
End ExecStoreGSwalk.

(* 8-byte S-mode vmem_read at a translated address (translate via Htr). *)
Section RWS.
Variable a : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable s : mstate.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 8))) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_addr_8_S :
  exec (vmem_read_addr (Virtaddr a) 8 (Load Data) false false false) s
    = Some (Ok data2, s).
Proof.
  unfold vmem_read_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result (mword (8 * 8)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr).
      cbn [bits_of_virtaddr] in *. cbn match.
      match goal with
      | |- execR (Defs.bind ?mrm ?post) s = _ =>
        assert (Hmrm : execR mrm s = Some (inr data2, s))
      end.
      { rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_read_load_S PBMT_PMA pa region v (register_lookup mstatus s.(sregs)) s
             HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes eq_refl Hmprv Hcp)).
        cbn match.
        rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite autocast_id. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
      cbn. apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. rewrite autocast_id. reflexivity.
Qed.
End RWS.

(* register-generic 8-byte S-mode vmem_read: base address from ANY rs1. *)
Section RWgS.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable s : mstate.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_8_gpr_S :
  exec (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s = Some (Ok data2, s).
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_8_S a8 v region s Halign Hcp Hmprv Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End RWgS.

(* register-generic 8-byte S-mode LOAD execute: base from rs1, result to rd. *)
Section ExecLoadGS.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable v : bv 64.
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable s : mstate.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s).
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s = Some (false, s).
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_8_gpr_S :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_8_gpr_S rs1 offset v region satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) s
               = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false data2)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value false data2) s).
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadGS.

(* 8-byte S-mode vmem_read whose translation WALKS (fills the TLB): the
   translate transitions s -> s' = set_reg s tlb tlbf; the memory read runs
   at s' (same memory).  Mirror of [Section SWSwalk] for (Load Data). *)
Section RWSwalk.
Variable a : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
Variable s : mstate.
Let s' := set_reg s tlb tlbf.
Let pa := zero_extend' 64 (add_vec_int a (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 8))) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_addr_8_S_walk :
  exec (vmem_read_addr (Virtaddr a) 8 (Load Data) false false false) s
    = Some (Ok data2, s').
Proof.
  assert (Hbytes' : forall j : nat, (N.of_nat j < 8)%N ->
            s'.(mem) !! (pa_add pa j) = Some (nth_byte v j)) by exact Hbytes.
  unfold vmem_read_addr.
  rewrite exec_catch_early_return.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  assert (Hinner : execR (returnR (result (mword (8 * 8)) ExecutionResult) tt >>
                          liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
    rewrite execR_liftR. rewrite (exec_split_misaligned_aligned (Virtaddr a) s Halign). reflexivity. }
  rewrite (execR_bind_Some _ _ _ _ _ Hinner).
  rewrite misaligned_order_1.
  match goal with
  | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (data2, true, 0), s'))
  end.
  { eapply execR_untilMT_1.
    - reflexivity.
    - cbn match.
      assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
      rewrite (execR_liftR_seq _ _ _ _ _ Hass).
      rewrite (execR_liftR_seq _ _ _ _ _ Htr).
      cbn [bits_of_virtaddr] in *. cbn match.
      match goal with
      | |- execR (Defs.bind ?mrm ?post) s' = _ =>
        assert (Hmrm : execR mrm s' = Some (inr data2, s'))
      end.
      { rewrite (execR_liftR_seq _ _ _ _ _
          (exec_mem_read_load_S PBMT_PMA pa region v (register_lookup mstatus s'.(sregs)) s'
             HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes' eq_refl Hmprv' Hcp')).
        cbn match.
        rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s')).
        rewrite autocast_id. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hmrm).
      cbn. apply execR_returnR_fwd.
    - apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu).
  cbn. rewrite autocast_id. reflexivity.
Qed.
End RWSwalk.

(* register-generic 8-byte S-mode vmem_read whose translation WALKS. *)
Section RWgSwalk.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
Variable s : mstate.
Let s' := set_reg s tlb tlbf.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_vmem_read_8_gpr_S_walk :
  exec (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s = Some (Ok data2, s').
Proof.
  unfold vmem_read. rewrite exec_catch_early_return.
  assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                 = Some (Ext_DataAddr_OK (Virtaddr a8), s)).
  { unfold get_transformed_data_addr.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_load_S ea satp0 s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
  cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a8) s)).
  rewrite execR_liftR.
  rewrite (exec_vmem_read_addr_8_S_walk a8 v region tlbf s Halign Hcp' Hmprv' Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End RWgSwalk.

(* register-generic 8-byte S-mode LOAD execute whose translation WALKS. *)
Section ExecLoadGSwalk.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable v : bv 64.
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
Variable s : mstate.
Let s' := set_reg s tlb tlbf.
Let offset := sign_extend' 64 imm.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
Let pa := zero_extend' 64 (add_vec_int a8 (0 * 8)).
Let data2 : mword (8*1*8) :=
  update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v.
Hypothesis Hrd : uint rd <> 0.
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hmprv : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false.
Hypothesis Hmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"0") = true.
Hypothesis Hpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg s.(sregs))) = PMM_Disabled.
Hypothesis Halign : is_aligned_vaddr (Virtaddr a8) 8 = true.
Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a8)) (0 * 8))) (Load Data)) s
                 = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
Hypothesis Hcp' : register_lookup cur_privilege s'.(sregs) = Supervisor.
Hypothesis Hmprv' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s'.(sregs))) ('b"1") = false.
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0) = false.
Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s'.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 8)) = PMP_Match.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s'.(sregs)) 0)) ('b"1") = true.
Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s'.(sregs)) (Physaddr pa) 8 = Some region.
Hypothesis Hpalign : is_aligned_paddr (Physaddr pa) 8 = true.
Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_readable) = true.
Hypothesis Hc : exec (within_clint (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hsig : exec (within_sig (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hh : exec (within_htif_readable (Physaddr pa) 8) s' = Some (false, s').
Hypothesis Hdev : dev_addr pa = false.
Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add pa j) = Some (nth_byte v j).

Lemma exec_execute_LOAD_8_gpr_S_walk :
  exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s
    = Some (RETIRE_SUCCESS,
            set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (extend_value false data2))).
Proof.
  change (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8)))
    with (execute_LOAD imm (Regidx rs1) (Regidx rd) false 8).
  unfold execute_LOAD.
  replace (8 <=? xlen_bytes) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/I/base_insts.sail:289.28-289.29" : M (true = true)) s = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (exec_bind_Some _ _ _ _ _ Hass).
  rewrite (exec_bind_Some _ _ _ _ _
    (exec_vmem_read_8_gpr_S_walk rs1 offset v region satp0 tlbf s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr Hcp' Hmprv' HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) s'
               = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false data2)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value false data2) s').
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadGSwalk.

(* ===================================================================== *)
(* Part B -- wp_instr_s_config: the S-mode mirror of InstrBytes'          *)
(* [wp_instr_config].  The [wp_instr_s] variant for instructions that     *)
(* READ or WRITE the cells [smode_config] bundles: it takes the UNBUNDLED *)
(* cells (mstatus / menvcfg VALUES explicit -- the stores/loads need      *)
(* mstatus.MXR and menvcfg.PMM, which the opaque bundle hides; SRET       *)
(* writes mstatus / cur_privilege) and passes ALL of them INTO the        *)
(* caller's fupd, so the caller can reg_valid them at σ and/or reg_update *)
(* them alongside its other writes when exhibiting s_exec.  The tlb cell  *)
(* is threaded the same way (the FIRST store's data translation WALKS and *)
(* fills the TLB: the caller needs the cell at full ownership to mirror   *)
(* the fill).  Fraction-generic: read-only clients instantiate any dq.    *)
(* ===================================================================== *)
Section WpInstrSConfig.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.


  (* ------------------------------------------------------------------- *)
  (* wp_instr_s_config_tlbinv -- THE UNIFIED raw-cell S-mode engine over  *)
  (* the TLB/page-table consistency invariant: case-splits internally on  *)
  (* slot 5 (hit / walk+fill) and hands the caller's fupd the tlb cell    *)
  (* CONTENTS (post-fetch) together with its consistency fact, so the     *)
  (* caller can perform its own data-side lookup/fill and re-establish    *)
  (* [tlb_inv] in its continuation.                                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_instr_s_config_tlbinv (root_ppn : mword 44) E Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    ↑minstretN ⊆ E →
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (* the SATP cell + its three facts + the post-fetch tlb cell + its       *)
    (* consistency + the owned super-PTE bytes are all handed to the caller's *)
    (* fupd (opened out of [tlb_inv]); the caller does its data-side          *)
    (* lookup/fill and RE-SEALS [tlb_inv] in its final continuation.          *)
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc)
       (satp0 : mword 64) (tlbvec_f : vec (option TLB_Entry) (2 ^ 6))
       (Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4))
       (Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16))
       (Hppn : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn)
       (Hconsf : tlb_pt_consistent root_ppn tlbvec_f),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       satp ↦ᵣ satp0 -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       pmp_config root_ppn -∗
       tlb ↦ᵣ tlbvec_f -∗
       pte_super_bytes root_ppn (DfracOwn 1) -∗
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    (* Open [tlb_inv] ONCE, then drive the UNIFIED fetch (which translates each
       16-bit chunk through its own vpn and fills 0/1/2 slots as needed) -- no
       up-front hit/walk slot case-split, no same-page premise. *)
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0)
      "#Hhw #Hinv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Htlbinv Hpc Hinstr H".
    iDestruct (tlb_inv_open with "Htlbinv") as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hcons & Hpbytes & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (fetch_from_instr_bytes_s_consistent root_ppn σ pc r
                 satp0 mstatus0 misa0 menvcfg0 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HmisaS HSXL Hmode Hppn Hasid Hcons HPBMTE HX Hcov
                 HA0 Hord0 HR Hpma_pte
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %Hfetch.
    destruct Hfetch as (tlbvec2 & Hfetcheq & Hcons2).
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE
                 with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    (* the TLB fill(s): update the owned cell to the fetch's [tlbvec2] *)
    iMod (reg_update _ tlb _ tlbvec2 with "Hreg Htlb") as "[Hreg Htlb]".
    set (σf := set_reg σ tlb tlbvec2 : mstate).
    iAssert (mstate_interp σf) with "[Hreg Hmem]" as "Hsi".
    { unfold σf, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc).
    { unfold σf, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iDestruct (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                 HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa") as "Hpmp".
    iMod ("H" $! σf Lpc_σf satp0 tlbvec2 Hmode Hasid Hppn Hcons2
            with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hpmp Htlb Hpbytes [$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
    - (* F_Base w : direct decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
    - (* F_RVC h : indirect decode (i0 ExecuteAs-expands to the target i) *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* wp_instr_s_config_tlbinv_gen -- the generic raw-cell S-mode engine   *)
  (* over [tlb_inv_gen P].  Like [wp_instr_s_config_tlbinv] but the fetch  *)
  (* runs over a generic [tlb_consistent P] TLB, and the caller is handed  *)
  (* the post-fetch tlb cell + [tlb_consistent P] to do its data-side fill *)
  (* (which may install a foreign leaf, e.g. the UART leaf) and re-seal    *)
  (* [tlb_inv_gen P].  [HPsuper]/[Hdisc] are the fetch obligations.        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_instr_s_config_tlbinv_gen (P : TLB_Entry -> Prop) (root_ppn : mword 44) E Φ
      (pc : mword 64) (is_rvc : bool) (i : instruction)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    ↑minstretN ⊆ E →
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (forall a, addr_is_ram a -> P (kpt_tlb_ent root_ppn (svpn_of a))) ->
    (forall a e, addr_is_ram a -> P e ->
       e = kpt_tlb_ent root_ppn (svpn_of a) \/
       match_TLB_Entry e (mword_of_int 0 : mword 16) (sign_extend' (57 - 12) (svpn_of a)) = false) ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv_gen P root_ppn -∗
    PC ↦ᵣ pc -∗
    instr pc is_rvc i -∗
    (∀ σ (Hpceq : register_lookup PC σ.(sregs) = pc)
       (satp0 : mword 64) (tlbvec_f : vec (option TLB_Entry) (2 ^ 6))
       (Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4))
       (Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16))
       (Hppn : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn)
       (Hconsf : tlb_consistent P tlbvec_f),
       cur_privilege ↦ᵣ{ dq } Supervisor -∗
       satp ↦ᵣ satp0 -∗
       mstatus ↦ᵣ{ dq } mstatus0 -∗
       mie ↦ᵣ{ dq } mie_v -∗
       mideleg ↦ᵣ{ dq } mdv0 -∗
       menvcfg ↦ᵣ{ dq } menvcfg0 -∗
       pmp_config root_ppn -∗
       tlb ↦ᵣ tlbvec_f -∗
       pte_super_bytes root_ppn (DfracOwn 1) -∗
       mstate_interp σ ={E ∖ ↑minstretN}=∗
       ∃ (s_exec : mstate),
         ⌜ exec (execute i)
                (set_reg σ nextPC (add_vec_int (register_lookup PC σ.(sregs))
                                     (if is_rvc then 2 else 4)))
             = Some (RETIRE_SUCCESS, s_exec) ⌝ ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0 HPsuper Hdisc)
      "#Hhw #Hinv Hhs Hpriv Hmstatus Hmiec Hmdlc Hmenvc Htlbinv Hpc Hinstr H".
    iDestruct (tlb_inv_gen_open with "Htlbinv") as (satp0 tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hcons & Hpbytes & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iApply (wp_exec_step_decode_execute_inv_priv Supervisor E Φ HN with "Hinv Hhs").
    iIntros (σ) "Hsi".
    iDestruct (fetch_from_instr_bytes_s_consistent_gen root_ppn P σ pc r
                 satp0 mstatus0 misa0 menvcfg0 pmpcfg0 pmpaddr00 pmar0 tlbvec
                 Hpma_all HmisaC HmisaS HSXL Hmode Hppn Hasid Hcons HPsuper Hdisc HPBMTE HX Hcov
                 HA0 Hord0 HR Hpma_pte
                 with "Hsi Hpc Hpriv Hmstatus Hsatp Htlb Hmenvc Hpmpc Hpmpa Hpma Hhtif Hmisa Hpbytes Hbytes")
      as %Hfetch.
    destruct Hfetch as (tlbvec2 & Hfetcheq & Hcons2).
    iDestruct (dispatchInterrupt_none_S_from_regs σ misa0 mstatus0 mie_v mdv0
                 HmisaS Hmm HSIE
                 with "Hsi Hmisa Hmstatus Hmiec Hmdlc") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σ.
    iDestruct (reg_valid    with "Hreg Hpc")   as %Lpc.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iMod (reg_update _ tlb _ tlbvec2 with "Hreg Htlb") as "[Hreg Htlb]".
    set (σf := set_reg σ tlb tlbvec2 : mstate).
    iAssert (mstate_interp σf) with "[Hreg Hmem]" as "Hsi".
    { unfold σf, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Hpriv_σf.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_σf.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_σf.
    iDestruct (reg_valid_dq with "Hreg Hmenvc") as %Hmenv_σf.
    specialize (Hdec0 ltac:(rewrite Hpriv_σf; reflexivity)
                      ltac:(rewrite Hmisa_σf; exact HmisaC)
                      ltac:(rewrite Hmisa_σf; exact HmisaA)
                      ltac:(rewrite Hmisa_σf; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_σf | rewrite Hmenv_σf; exact Hmenvval0 ])).
    assert (Lpc_σf : register_lookup PC σf.(sregs) = pc).
    { unfold σf, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    iDestruct (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                 HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa") as "Hpmp".
    iMod ("H" $! σf Lpc_σf satp0 tlbvec2 Hmode Hasid Hppn Hcons2
            with "Hpriv Hsatp Hmstatus Hmiec Hmdlc Hmenvc Hpmp Htlb Hpbytes [$Hreg $Hmem]")
      as (s_exec) "(Hexec & [Hreg' Hmem'] & Hcont)".
    iDestruct (reg_valid with "Hreg' Hpc") as %Lpc_exec.
    iDestruct "Hexec" as %Hexec.
    destruct r as [e | w | h | erx].
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
    - (* F_Base w : direct decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      iModIntro. iExists (F_Base w), i, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec0 |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR; [iPureIntro; exact Hnlpad |]. iPureIntro; exact Hexec. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
    - (* F_RVC h : indirect decode *)
      cbn [fetch_is_rvc] in Hrvc, Hdec0. subst is_rvc.
      destruct Hdec0 as (i0 & Hdec & Hnlpad0 & Hexp).
      iModIntro. iExists (F_RVC h), i0, σf, s_exec.
      iSplitR; [iPureIntro; exact Hpriv_σ |].
      iSplitR; [iPureIntro; exact Hdisp |].
      iSplitR; [iPureIntro; exact Hfetcheq |].
      iSplitR; [iPureIntro; exact Hdec |].
      iSplitR; [iPureIntro; rewrite Help_σf; exact Help_np |].
      iSplitR.
      { iSplitR.
        { iPureIntro. apply exec_currentlyEnabled_Zca. rewrite Hmisa_σf. exact HmisaC. }
        iExists i. iSplit; iPureIntro; [apply Hexp | exact Hexec]. }
      rewrite Lpc_exec. iFrame "Hpc Hreg' Hmem'". iExact "Hcont".
    - iDestruct "Hbytes" as "[_ %Hbf]". done.
  Qed.

End WpInstrSConfig.

(* ===================================================================== *)
(* Part C -- the kernelvec client WPs.                                    *)
(* ===================================================================== *)
Section SmodeGprClients.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* C.1 GENERIC S-mode RVC gpr-write engine (TLB-hit fetch): mirror of   *)
  (* WpGprRvc's [wp_rvc_gpr_write], built on [wp_instr_s].                *)
  (* ------------------------------------------------------------------- *)

  (* ---- c.addi16sp imm6 (S-mode, fetch TLB hit) ---- *)

  (* ------------------------------------------------------------------- *)
  (* C.2 GENERIC S-mode RVC gpr-write engine on the WALK fetch            *)
  (* ([wp_instr_s_fill]): kernelvec's FIRST instruction, whose fetch page- *)
  (* walks and fills the TLB at slot 5.  The continuation receives the    *)
  (* FILLED tlb cell.                                                     *)
  (* ------------------------------------------------------------------- *)

  (* ---- c.addi16sp imm6 on the WALK fetch: kernelvec's FIRST instruction ---- *)

  (* ------------------------------------------------------------------- *)
  (* C.3 jal (S-mode, fetch TLB hit): mirror of [wp_jal_gpr] on           *)
  (* [wp_instr_s].  Control flow: continuation lands on pc_is TARGET.     *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* C.4 c.sdsp rs2, uimm*8(sp) -- the S-mode 8-byte stack store, with    *)
  (* the DATA-address translation a TLB HIT at slot [tlb_hash svpn]       *)
  (* (installed by the first store's walk, or = slot 5 if the stack page  *)
  (* hashes there).  Built on [wp_instr_s_config]: the client reads the   *)
  (* mstatus.MXR / menvcfg.PMM values off the threaded cells.  The data   *)
  (* premises are phrased at the model's address tower                    *)
  (* a8 = sext(ea[63:0]) / pa = zext(a8+0) (both = ea propositionally;    *)
  (* collapse with subrange_id / sign_extend'_id / avi0 /                 *)
  (* zero_extend'_id).                                                    *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* C.5 c.sdsp rs2, uimm*8(sp) -- the FIRST store: the data address      *)
  (* MISSES the TLB (slot tlb_hash svpn empty) and page-WALKS, re-reading *)
  (* the owned superpage PTE and FILLING the TLB at tlb_hash svpn (with   *)
  (* the same entry VALUE the fetch walk installs).  The tlb cell is held *)
  (* at FULL ownership; the continuation receives it FILLED.              *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* C.6 c.ldsp rd, uimm*8(sp) -- the S-mode 8-byte stack load (epilogue),*)
  (* data-address translation a TLB HIT at slot [tlb_hash svpn] (the      *)
  (* entry the prologue stores installed).  Loaded window read-only at    *)
  (* any fraction; rd := v inserted into the file.                        *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* UNIFIED (tlb_inv) clients.  Same statements as the hit/fill pairs    *)
  (* above, with (tlb cell + slot facts) replaced by [tlb_inv root_ppn] + *)
  (* [pte_super_bytes] (the page-table fact's resource).                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_rvc_gpr_write_s (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd rsa rsb : mword 5)
      (base : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64))
      (q : Qp) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    smode_config γ (DfracOwn q) -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true base -∗
    ( smode_config γ (DfracOwn q) -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Hbexec)
      "Hsm Htlbinv [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_tlbinv root_ppn γ E Φ pc true base
              HN
              with "Hsm Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rsa = Some (m !!! Regidx rsa))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rsb = Some (m !!! Regidx rsb))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* tick nextPC := pc+2 *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m !!! Regidx rsa) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m !!! Regidx rsb) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc.
      exact (Hbexec s_pc Lnpc0 Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hsm' Htlbinv' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 2).
    { tmig. exact Lnpc0. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hsm' Htlbinv' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- c.addi16sp imm6 (S-mode, unified) ---- *)
  Lemma wp_caddi16sp_gpr_s (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm6 : mword 6)
      (m : gmap regidx (mword 64))
      (q : Qp) :
    ↑minstretN ⊆ E ->
    smode_config γ (DfracOwn q) -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    ( smode_config γ (DfracOwn q) -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN)
      "Hsm Htlbinv Hpc Hfile Hinstr Hcont".
    assert (Hsp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    unshelve iApply (wp_rvc_gpr_write_s root_ppn γ E Φ pc csp_rs1 csp_rs1 csp_rs1
              (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))
              m q
              HN Hsp _
              with "Hsm Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change sp with (Regidx csp_rs1).
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (caddi16sp_imm imm6) s_pc).
    replace (Z.eqb (uint csp_rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hsp).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  (* ---- jal rd, imm (S-mode, unified; 2-aligned F_Base: the fetch may
     WALK -- the first halfword's translation fills slot 5, the second
     halfword hits it) ---- *)
  Lemma wp_jal_gpr_s (root_ppn : mword 44) (γ : gname) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 21)
      (m : gmap regidx (mword 64))
      (q : Qp) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr (add_vec pc (sign_extend' 64 imm))) 4 = true ->
    smode_config γ (DfracOwn q) -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc false (JAL (imm, Regidx rd)) -∗
    ( smode_config γ (DfracOwn q) -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec pc (sign_extend' 64 imm)) -∗
      gpr_file (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hrd Halign)
      "Hsm Htlbinv [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    destruct (aligned4_jump_bits _ Halign) as [Hal0 Hal1].
    iApply (wp_instr_s_tlbinv root_ppn γ E Φ pc false (JAL (imm, Regidx rd))
             
              HN
              with "Hsm Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    assert (Hpcv : register_lookup PC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = pc).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (Hlink : register_lookup nextPC
             (set_reg σ nextPC (add_vec_int pc 4)).(sregs) = add_vec_int pc 4).
    { unfold set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iMod (reg_update _ nextPC _ (add_vec pc (sign_extend' 64 imm))
            with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec_int pc 4))
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec_int pc 4))
                 with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                        nextPC (add_vec pc (sign_extend' 64 imm)))
               (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (add_vec_int pc 4))).
    iSplitR.
    { iPureIntro. rewrite Hpceq.
      change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
      rewrite (exec_execute_JAL_gpr imm rd (set_reg σ nextPC (add_vec_int pc 4))
                 Hrd).
      - rewrite Hpcv. rewrite Hlink. reflexivity.
      - rewrite Hpcv. exact Hal0.
      - rewrite Hpcv. exact Hal1. }
    iSplitL "Hreg Hmem".
    { unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem". }
    iIntros "Hsm' Htlbinv' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg (set_reg (set_reg σ nextPC (add_vec_int pc 4))
                         nextPC (add_vec pc (sign_extend' 64 imm)))
                (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (add_vec_int pc 4))).(sregs)
             = add_vec pc (sign_extend' 64 imm)).
    { unfold set_reg; cbn [sregs].
      tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hsm' Htlbinv' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.sdsp rs2, uimm*8(sp) -- UNIFIED: the fetch goes through the        *)
  (* invariant engine; the DATA translation case-splits on consistency at *)
  (* tlb_hash svpn (hit: state-preserving; miss: walk + fill, which       *)
  (* preserves the invariant).  ONE ident premise (the tlb_get_ppn form); *)
  (* the walk form is derived via [tlb_get_ppn_pw].                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_csdsp_gpr_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* store PMP: TOR entry 0 covers pa with W *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea a8 pa HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign8 & Hbytes)".
    assert (Halign8 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign8.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_st & Hmatch_st0 & _ & _ & Hwrite_st & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (STORE (imm, Regidx rs2, sp, 8))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx csp_rs1 = Some (m !!! Regidx csp_rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    pose proof (addr_is_ram_not_dev _ Hrampa) as Hdevea.
    (* per-access PMP: derive [pmpRangeMatch] for the store address from the
       folded RAM coverage + [pa]'s RAM-ness (no longer a caller premise). *)
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match a8 (vec_access_dec pmpaddr00 0) Hlo Hfit Hcov) as Hrange_st.
    (* the kernel PT's layout fact + memory image (for the data-side walk) *)
    iDestruct "Hpbytes" as "[%Hok Hpbytesb]".
    iDestruct (kpt_bytes_body_mem root_ppn (DfracOwn 1) σ with "Hmem Hpbytesb") as %Hmemσ.
    iAssert (kpt_bytes root_ppn (DfracOwn 1)) with "[Hpbytesb]" as "Hpbytes".
    { iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"]. }
    (* tick nextPC := pc+2 *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value csp_rs1 (m !!! Regidx csp_rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lv2.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* the data-address translate through the kernel PT (KptPt.v): packaged
       three-way -- a HIT at [a8]'s own 4KB leaf entry, or (empty slot /
       foreign resident entry) a 3-level WALK that fills the slot with
       [kpt_tlb_ent root_ppn (svpn_of a8)]. *)
    destruct (exec_translateAddr_kpt_ram (Store Data) root_ppn menvcfg0 satp0 a8 s_pc
                Hok (kpt_mem_eq σ s_pc root_ppn eq_refl Hmemσ) Hrampa
                (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                   ltac:(rewrite Lms_pc; exact HMPRV))
                (exec_is_shadow_stack_store s_pc)
                kpt_ram_check_store
                Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode Hppn Hasid
                ltac:(rewrite Lmisa_pc; exact HmisaS) Lmenv_pc HPBMTE Lhtif_pc
                ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                ltac:(rewrite Lpmpc_pc; exact HR) ltac:(rewrite Lpmpaddr_pc; exact Hcov)
                ltac:(rewrite Lpma_pc; exact Hpma_pte)
                tlbvec_f Ltlb_pc
                (kpt_slot_disj root_ppn a8 tlbvec_f Hrampa Hconsf))
      as (s_tr & Htr0 & [Hst | Hst]).
    - (* ---- data translate HIT: state-preserving ---- *)
      subst s_tr.
      pose proof (within_clint_false pa 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) pa 8 (m !!! Regidx rs2)) s_pc.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, sp, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { change sp with (Regidx csp_rs1).
        rewrite (exec_execute_STORE_8_gpr_S rs2 csp_rs1 imm region_st satp0 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id sext9_12_64; exact Halign8) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Htr_pc)
                   ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                   ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hrange_st) ltac:(rewrite Lpmpc_pc; exact HW)
                   ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hpalign8)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64. reflexivity. }
      iMod (upd_window_8 σ.(mem) pa (m !!! Regidx rs2) vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ (m !!! Regidx rs2))%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
    - (* ---- data translate WALK (empty or evicted foreign slot) ---- *)
      subst s_tr.
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) (svpn_of a8))
                      (Some (kpt_tlb_ent root_ppn (svpn_of a8)))) in *.
      set (s_f := set_reg s_pc tlb tlbf2) in *.
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 8 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_writable_false pa 8 s_f Lhtif_f) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Store Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      pose (s_x := MState s_f.(sregs) (write_bytes s_pc.(mem) pa 8 (m !!! Regidx rs2)) s_f.(mdev)).
      assert (Hstore : exec (execute (STORE (imm, Regidx rs2, sp, 8))) s_pc
                       = Some (RETIRE_SUCCESS, s_x)).
      { change sp with (Regidx csp_rs1).
        rewrite (exec_execute_STORE_8_gpr_S_walk rs2 csp_rs1 imm region_st satp0 tlbf2 s_pc
                   Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                   ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                   ltac:(rewrite Lmenv_pc; exact Hpmm)
                   ltac:(rewrite Lva subrange_id sign_extend'_id sext9_12_64; exact Halign8) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Htr_pc)
                   Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                   ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                   ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hrange_st) ltac:(rewrite Lpmpc_f; exact HW)
                   ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hmatch_st0)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hpalign8)
                   Hwrite_st ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwc)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hws)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwh)
                   ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hdevea)).
        subst s_x. do 3 f_equal. rewrite Lva Lv2 zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64. reflexivity. }
      (* the data fill, mirrored on the ghost cell *)
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iMod (upd_window_8 σ.(mem) pa (m !!! Regidx rs2) vold with "Hmem Hbytes") as "[Hmem Hbytes]".
      iModIntro.
      iExists s_x.
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hstore. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_x, s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
      { unfold s_x, s_f, s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈ (m !!! Regidx rs2))%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f a8 Hrampa Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.ldsp rd, uimm*8(sp) -- UNIFIED: like the store above, with the     *)
  (* data-address translation case-split on consistency at tlb_hash svpn  *)
  (* (hit: state-preserving; miss: LOAD page-walk + fill).                *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_cldsp_gpr_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5) (svpn : mword 27)
      (m : gmap regidx (mword 64)) (v : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    (* S-mode config facts *)
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    (* fetch *)
    (* data address: superpage-identity geometry at tlb_hash svpn *)
    neq_vec (bits_of_virtaddr (Virtaddr a8))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = svpn ->
    zero_extend' 64 (concat_vec (tlb_get_ppn 39 (pw_tlb_entry root_ppn (mword_of_int 0)) svpn)
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8 ->
    and_vec (sign_extend' (57 - 12) svpn) (not_vec (mword_of_int 0x3FFFF : mword 45)) = (mword_of_int 0x80000 : mword 45) ->
    subrange_vec_dec svpn 26 18 = (mword_of_int 2 : mword 9) ->
    sign_extend' 45 (and_vec svpn (not_vec (zero_extend' 27 (ones 18)))) = (mword_of_int 0x80000 : mword 45) ->
    zero_extend' 44 (and_vec (sdata_ppn_out svpn) (not_vec (zero_extend' 44 (ones 18)))) = (mword_of_int 0x80000 : mword 44) ->
    (* the walks' PTE read *)
    (* load PMP: TOR entry 0 covers pa with R *)
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (LOAD (imm, sp, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea a8 pa HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
      Hcanon Hvpn_def Hident Hmask Hvpn2 Hmvpn Hmppn.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct "Hbytes" as "(%Hpalign8 & Hbytes)".
    assert (Halign8 : is_aligned_vaddr (Virtaddr a8) 8 = true) by exact Hpalign8.
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    destruct (Hpma_all pa 8) as (region_ld & Hmatch_ld0 & _ & Hread_ld & _).
    assert (Hident_walk : zero_extend' 64 (concat_vec (sdata_ppn_out svpn)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub pagesize_bits 1) 0)) = a8).
    { rewrite <- (tlb_get_ppn_pw root_ppn svpn). exact Hident. }
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (LOAD (imm, sp, Regidx rd, false, 8))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpmpc & Hpmpa & %HA0 & %Hord0 & %Hpma_imp & %HX & %HW & %HR & %Hcov)".
    pose proof (Hpma_imp pmar0 Hpma_all) as Hpma_pte.
    iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpaddr.
    iDestruct (reg_valid    with "Hreg Htlb")  as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmsp : m !! Regidx csp_rs1 = Some (m !!! Regidx csp_rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              σ.(mem) !! (pa_add pa j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    pose proof (addr_is_ram_not_dev _ Hrampa) as Hdevea.
    (* per-access PMP: derive [pmpRangeMatch] for the load address from the
       folded RAM coverage + [pa]'s RAM-ness (no longer a caller premise). *)
    iAssert (⌜addr_is_ram (pa_add pa 7)⌝)%I as %Hrampa7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr. iPureIntro. exact Hr. }
    assert (Hlo : (ram_base <= uint pa)%Z) by (destruct Hrampa as [Hl _]; exact Hl).
    assert (Hfit : (uint pa + 8 <= ram_base + ram_size)%Z).
    { assert (Hnw : (uint pa + Z.of_nat 7 < 18446744073709551616)%Z).
      { destruct Hrampa as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
      pose proof (uint_pa_add pa 7 Hnw) as Heq.
      destruct Hrampa7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    pose proof (ram_pmp_match a8 (vec_access_dec pmpaddr00 0) Hlo Hfit Hcov) as Hrange_ld.
    (* the kernel PT's layout fact + memory image (for the data-side walk) *)
    iDestruct "Hpbytes" as "[%Hok Hpbytesb]".
    iDestruct (kpt_bytes_body_mem root_ppn (DfracOwn 1) σ with "Hmem Hpbytesb") as %Hmemσ.
    iAssert (kpt_bytes root_ppn (DfracOwn 1)) with "[Hpbytesb]" as "Hpbytes".
    { iSplitR; [iPureIntro; exact Hok | iExact "Hpbytesb"]. }
    (* tick nextPC := pc+2 *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmsp with "Hfmap") as "[Hspc Hfb1]".
    iDestruct (gpr_pt_value csp_rs1 (m !!! Regidx csp_rs1) s_pc with "Hreg Hspc") as %Lva.
    iDestruct ("Hfb1" with "Hspc") as "Hfmap".
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsatp_pc : register_lookup satp s_pc.(sregs) = satp0)
      by (unfold s_pc; tmig; exact Lsatp).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    assert (Lpmpc_pc : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmpaddr_pc : register_lookup pmpaddr_n s_pc.(sregs) = pmpaddr00)
      by (unfold s_pc; tmig; exact Lpmpaddr).
    assert (Ltlb_pc : register_lookup tlb s_pc.(sregs) = tlbvec_f)
      by (unfold s_pc; tmig; exact Ltlb).
    assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    assert (Hbytesf_pc : forall j : nat, (N.of_nat j < 8)%N ->
              s_pc.(mem) !! (pa_add pa j) = Some (nth_byte v j)) by exact Hbytesf.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    (* the data-address translate through the kernel PT (KptPt.v): packaged
       three-way -- a HIT at [a8]'s own 4KB leaf entry, or (empty slot /
       foreign resident entry) a 3-level WALK that fills the slot with
       [kpt_tlb_ent root_ppn (svpn_of a8)]. *)
    destruct (exec_translateAddr_kpt_ram (Load Data) root_ppn menvcfg0 satp0 a8 s_pc
                Hok (kpt_mem_eq σ s_pc root_ppn eq_refl Hmemσ) Hrampa
                (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                   ltac:(rewrite Lms_pc; exact HMPRV))
                (exec_is_shadow_stack_load s_pc)
                kpt_ram_check_load
                Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode Hppn Hasid
                ltac:(rewrite Lmisa_pc; exact HmisaS) Lmenv_pc HPBMTE Lhtif_pc
                ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                ltac:(rewrite Lpmpc_pc; exact HR) ltac:(rewrite Lpmpaddr_pc; exact Hcov)
                ltac:(rewrite Lpma_pc; exact Hpma_pte)
                tlbvec_f Ltlb_pc
                (kpt_slot_disj root_ppn a8 tlbvec_f Hrampa Hconsf))
      as (s_tr & Htr0 & [Hst | Hst]).
    - (* ---- data translate HIT: state-preserving ---- *)
      subst s_tr.
      pose proof (within_clint_false pa 8 s_pc (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_pc (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_false pa 8 s_pc Lhtif_pc) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_pc)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      assert (Hload : exec (execute (LOAD (imm, sp, Regidx rd, false, 8))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg v))).
      { change sp with (Regidx csp_rs1).
        rewrite <- Hev.
        apply (exec_execute_LOAD_8_gpr_S csp_rs1 rd imm v region_ld satp0 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id sext9_12_64; exact Halign8) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Htr_pc)
                 ltac:(rewrite Lpmpc_pc; exact HA0) ltac:(rewrite Lpmpaddr_pc; exact Hord0)
                 ltac:(rewrite Lpmpaddr_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hrange_ld) ltac:(rewrite Lpmpc_pc; exact HR)
                 ltac:(rewrite Lpma_pc Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hpalign8)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hdevea)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hbytesf_pc)). }
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
               = add_vec_int pc 2).
      { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈{ dqm } v)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
    - (* ---- data translate WALK (empty or evicted foreign slot) ---- *)
      subst s_tr.
      set (tlbf2 := vec_update_dec tlbvec_f (tlb_hash (__id 39) (svpn_of a8))
                      (Some (kpt_tlb_ent root_ppn (svpn_of a8)))) in *.
      set (s_f := set_reg s_pc tlb tlbf2) in *.
      assert (Lpriv_f : register_lookup cur_privilege s_f.(sregs) = Supervisor)
        by (unfold s_f; tmig; exact Lpriv_pc).
      assert (Lms_f : register_lookup mstatus s_f.(sregs) = mstatus0)
        by (unfold s_f; tmig; exact Lms_pc).
      assert (Lpmpc_f : register_lookup pmpcfg_n s_f.(sregs) = pmpcfg0)
        by (unfold s_f; tmig; exact Lpmpc_pc).
      assert (Lpmpaddr_f : register_lookup pmpaddr_n s_f.(sregs) = pmpaddr00)
        by (unfold s_f; tmig; exact Lpmpaddr_pc).
      assert (Lpma_f : register_lookup pma_regions s_f.(sregs) = pmar0)
        by (unfold s_f; tmig; exact Lpma_pc).
      assert (Lhtif_f : register_lookup htif_tohost_base s_f.(sregs) = None)
        by (unfold s_f; tmig; exact Lhtif_pc).
      pose proof (within_clint_false pa 8 s_f (addr_is_ram_not_in_clint _ Hrampa) ltac:(lia)) as Hwc.
      pose proof (within_sig_false pa 8 s_f (addr_is_ram_not_in_sig _ Hrampa) ltac:(lia)) as Hws.
      pose proof (within_htif_false pa 8 s_f Lhtif_f) as Hwh.
      assert (Htr_pc : exec (translateAddr (Virtaddr ((bits_of_virtaddr (Virtaddr a8)))) (Load Data)) s_pc
                       = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s_f)).
      { replace ((bits_of_virtaddr (Virtaddr a8))) with a8
          by (cbn [bits_of_virtaddr]; reflexivity).
        replace pa with a8 by (unfold pa; reflexivity).
        exact Htr0. }
      assert (Hload : exec (execute (LOAD (imm, sp, Regidx rd, false, 8))) s_pc
                      = Some (RETIRE_SUCCESS,
                              set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg v))).
      { change sp with (Regidx csp_rs1).
        rewrite <- Hev.
        apply (exec_execute_LOAD_8_gpr_S_walk csp_rs1 rd imm v region_ld satp0 tlbf2 s_pc Hrd
                 Lpriv_pc ltac:(rewrite Lms_pc; exact HSXL) Lsatp_pc Hmode
                 ltac:(rewrite Lms_pc; exact HMPRV) ltac:(rewrite Lms_pc; exact HMXR)
                 ltac:(rewrite Lmenv_pc; exact Hpmm)
                 ltac:(rewrite Lva subrange_id sign_extend'_id sext9_12_64; exact Halign8) ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Htr_pc)
                 Lpriv_f ltac:(rewrite Lms_f; exact HMPRV)
                 ltac:(rewrite Lpmpc_f; exact HA0) ltac:(rewrite Lpmpaddr_f; exact Hord0)
                 ltac:(rewrite Lpmpaddr_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hrange_ld) ltac:(rewrite Lpmpc_f; exact HR)
                 ltac:(rewrite Lpma_f Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hmatch_ld0)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hpalign8)
                 Hread_ld ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwc)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hws)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; apply Hwh)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hdevea)
                 ltac:(rewrite Lva zero_extend'_id avi0_mul8 subrange_id sign_extend'_id sext9_12_64; exact Hbytesf_pc)). }
      (* the data fill, mirrored on the ghost cell; then rd := v *)
      iMod (reg_update _ tlb _ tlbf2 with "Hreg Htlb") as "[Hreg Htlb]".
      iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
      rewrite (gpr_pt_nz rd _ Hrd).
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg v)
              with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]") as "Hfmap".
      { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
      iModIntro.
      iExists (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).
      iSplitR.
      { iPureIntro. rewrite Hpceq.
        change (if true then 2%Z else 4%Z) with 2%Z. fold s_pc. exact Hload. }
      iSplitL "Hreg Hmem Hdev".
      { unfold s_f, s_pc, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
      iIntros "Hhs' Hpc'".
      assert (Lnpc : register_lookup nextPC
               (set_reg s_f (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)).(sregs)
               = add_vec_int pc 2).
      { unfold s_f, s_pc; cbn [sregs]. tmig. tmig. rewrite register_lookup_set. reflexivity. }
      iEval (rewrite Lnpc) in "Hpc'".
      iAssert (pa ↦₈{ dqm } v)%I with "[Hbytes]" as "Hbw".
      { rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8. }
      iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmpc Hpmpa]
                            [$Hpc' $Hnpc] [Hfmap] Hbw").
      { iApply (tlb_inv_close root_ppn satp0 tlbf2 Hmode Hasid Hppn
                  (tlb_pt_consistent_fill root_ppn tlbvec_f a8 Hrampa Hconsf)
                  with "Hsatp Htlb Hpbytes [Hpmpc Hpmpa]").
        iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                  HA0 Hord0 Hpma_imp HX HW HR Hcov with "Hpmpc Hpmpa"). }
      iSplitR.
      { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
      iExact "Hfmap".
  Qed.

  (* ==================================================================== *)
  (* RAM wrappers: the whole S-mode superpage-identity geometry (Sv39      *)
  (* canonicality, VPN=svpn, identity translation, the gigapage masks) and *)
  (* the store/load PMP match are DISCHARGED from the owned points-to      *)
  (* (addr_is_ram, via [mem_ram] on bytes 0 and 7) using the ram_* lemmas. *)
  (* Callers need only own the frame bytes + one "PMP covers RAM" fact     *)
  (* ([pmpaddr00[0]*4 >= ram top]) and the sp-alignment; they no longer    *)
  (* carry the per-address translation preconditions.                      *)
  (* ==================================================================== *)

  Lemma wp_csdsp_gpr_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (m : gmap regidx (mword 64)) (vold : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (STORE (imm, Regidx rs2, sp, 8)) -∗
    pa ↦₈ vold -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      pa ↦₈ (m !!! Regidx rs2) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea a8 pa HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpcis Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iAssert (⌜addr_is_ram pa⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr. iPureIntro. exact Hr. }
    (* [pmpRangeMatch] and the PMP config are now discharged inside
       [wp_csdsp_gpr_s] from the folded [tlb_inv]; the wrapper only supplies
       the RAM-derived Sv39 geometry. *)
    iApply (wp_csdsp_gpr_s root_ppn E Φ pc uimm rs2 (svpn_of a8) m vold
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpcis Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

  Lemma wp_cldsp_gpr_s_ram (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (uimm : mword 6) (rd : mword 5)
      (m : gmap regidx (mword 64)) (v : bv 64)
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq dqm : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec uimm ('b"000"))) in
    let a8 := ea in
    let pa := a8 in
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗
    mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗
    mideleg ↦ᵣ{ dq } mdv0 -∗
    menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (LOAD (imm, sp, Regidx rd, false, 8)) -∗
    pa ↦₈{ dqm } v -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗
      mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗
      mideleg ↦ᵣ{ dq } mdv0 -∗
      menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      pa ↦₈{ dqm } v -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea a8 pa HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0.
    iIntros "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpcis Hfile Hinstr Hbw Hcont".
    iDestruct "Hbw" as "(%Hpalign8 & Hbytes)".
    iAssert (⌜addr_is_ram pa⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr. rewrite pa_add_0 in Hr. iPureIntro. exact Hr. }
    (* [pmpRangeMatch] and the PMP config are now discharged inside
       [wp_cldsp_gpr_s] from the folded [tlb_inv]; the wrapper only supplies
       the RAM-derived Sv39 geometry. *)
    iApply (wp_cldsp_gpr_s root_ppn E Φ pc uimm rd (svpn_of a8) m v
              mstatus0 mie_v mdv0 menvcfg0
              HN Hrd HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0
              (ram_canonical a8 Hr0) ltac:(reflexivity) (ram_ident root_ppn a8 Hr0)
              (ram_mask a8 Hr0) (ram_svpn2 a8 Hr0) (ram_mvpn a8 Hr0) (ram_mppn a8 Hr0)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpcis Hfile Hinstr [Hbytes] Hcont").
    rewrite /word_pointsto. iFrame "Hbytes". iPureIntro. exact Hpalign8.
  Qed.

End SmodeGprClients.
