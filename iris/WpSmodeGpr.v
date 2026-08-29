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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpLoad.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import SmodePte.
From Kernel Require Import KernelInstrs.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
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
  assert (Hcp : exec (check_pma_with_pmp_priority (Store Data) pbmt Supervisor
                        (Physaddr addr) 8 false) s = Some (Ok pma_ok_aligned, s)).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pmaCheck_ram_store addr pbmt region s Hmatch Halign Hwrite)).
    cbn match. apply exec_returnM. }
  assert (Hmmio : exec (within_mmio_writable (Physaddr addr) 8) s = Some (false, s)).
  { unfold within_mmio_writable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  set (sw := MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
  unfold checked_mem_write. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 8 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (_ : exec (write_kind_of_flags false false false) s
                  = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m0 c b) s = Some (inr (true, 0, true), sw)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    rewrite avi0_mul8.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_pmpCheck_supervisor_grant_store addr 8 s HA Hord Hrange HW)).
    cbn beta. cbn match.
    rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
    rewrite autocast_id.
    change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
    rewrite subrange_full_64.
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?pa ?wd ?dt ?mt)) ?k1) _] =>
      assert (Hwr : execR (Defs.bind (Defs.liftR (write_ram wk pa wd dt mt)) k1) s
                    = Some (inr true, sw)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ (exec_write_ram_plain_8 addr data s Hdev)).
      cbn beta. cbn [andb]. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hwr). cbn beta zeta.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite execR_returnR. reflexivity.
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


  (* The masked superpage base for any in-region vpn equals 0x80000 -- taken
     as bitvector hypotheses.  With these the installed entry is exactly
     pw_tlb_entry (the same superpage entry the fetch installs), only at the
     symbolic index tlb_hash vpn. *)




  (* FULL Sv39 translation of a SYMBOLIC store data address `a` in the 1GB
     identity superpage, with the stack page NOT yet in the TLB: the walk
     re-reads the same PTE (pte_paddr root_ppn) and FILLS the TLB at
     tlb_hash vpn (state change). *)

  (* ---- Data-address TLB HIT (state-preserving): a store/load to a stack
     page whose (superpage) entry sits at tlb_hash vpn. ---- *)




  (* ---- the LOAD (Read-Data) mirror of the HIT path. ---- *)
  Lemma exec_effectivePrivilege_load_S (m : mword 64) s :
    eq_vec (_get_Mstatus_MPRV m) ('b"1" : mword 1) = false ->
    exec (effectivePrivilege (Load Data) m Supervisor) s = Some (Supervisor, s).
  Proof.
    intro H. unfold effectivePrivilege. cbn [generic_neq generic_eq].
    rewrite H. cbn [andb]. apply exec_returnm.
  Qed.




  (* ---- the LOAD (Read-Data) mirror of the WALK path: the data address
     MISSES the TLB, page-walks the same superpage PTE and FILLS the TLB
     at tlb_hash vpn.  Mechanical (Load Data) copies of the store-walk
     lemmas above. ---- *)



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

(* testbit of bv_signed below the width = testbit of bv_unsigned. *)


(* ---------------------------------------------------------------------- *)
(* RAM-range geometry for the S-mode gigapage identity map: the remaining  *)
(* two per-address obligations that need [sdata_ppn_out]/[tlb_get_ppn_pw]  *)
(* (the others -- ram_canonical, ram_svpn2, ram_mask, ram_mvpn,            *)
(* svpn_of_unsigned -- live in RiscvExtras).  Together they let the S-mode *)
(* load/store WPs discharge the whole superpage-identity geometry from an  *)
(* owned points-to (addr_is_ram) instead of taking it as preconditions.    *)
(* ---------------------------------------------------------------------- *)

(* superpage mask fact, output-PPN side. *)

(* the gigapage identity translation: a RAM vaddr walks to itself. *)

(* [uint] of a small offset from a base that does not wrap: used to turn the
   RAM-ness of an access's LAST byte into the fit bound [uint a + 8 <= ram top]
   that [ram_pmp_match] needs. *)
(* [uint_pa_add] lives in RiscvExtras.v (one home): the offset-[j] byte of an
   access is at [uint a + j] whenever the sum does not wrap. *)


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
  assert (Hcp : exec (check_pma_with_pmp_priority (Load Data) pbmt Supervisor (Physaddr addr) 8 false) s = Some (Ok pma_ok_aligned, s)).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load addr pbmt region s Hmatch Halign Hread)).
    cbn match. apply exec_returnM. }
  assert (Hmmio : exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s)).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  unfold checked_mem_read. rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
  rewrite execR_bind. rewrite execR_returnR. cbn match beta.
  rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 8 0 s)). cbn beta.
  rewrite misaligned_order_1. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _
             (_ : exec (read_kind_of_flags _ _ false) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  cbn beta.
  match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
    assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s)) end.
  { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
    change (bits_of_physaddr (Physaddr addr)) with addr.
    rewrite avi0_mul8.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_pmpCheck_supervisor_grant_load_data addr 8 s HA Hord Hrange HR)). cbn beta.
    cbn match.
    match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
      assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite Hmmio. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
    match goal with
      |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pa ?wd ?mt)) ?k1) _] =>
      assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk pa wd mt)) k1) s
                    = Some (inr w, s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_ram_plain_8 addr w s Hdev Hbytes)).
      cbn beta match. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
    rewrite autocast_id. rewrite usvd_zeros_full_64.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
  rewrite autocast_id. rewrite execR_returnR. reflexivity.
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
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.


  (* ------------------------------------------------------------------- *)
  (* wp_instr_s_config_tlbinv -- THE UNIFIED raw-cell S-mode engine over  *)
  (* the TLB/page-table consistency invariant: case-splits internally on  *)
  (* slot 5 (hit / walk+fill) and hands the caller's fupd the tlb cell    *)
  (* CONTENTS (post-fetch) together with its consistency fact, so the     *)
  (* caller can perform its own data-side lookup/fill and re-establish    *)
  (* [tlb_inv] in its continuation.                                       *)
  (* ------------------------------------------------------------------- *)

  (* arbitrary-A/D raw-cell data engine *)

  (* ------------------------------------------------------------------- *)
  (* wp_instr_s_config_tlbinv_gen -- the generic raw-cell S-mode engine   *)
  (* over [tlb_inv_gen P].  Like [wp_instr_s_config_tlbinv] but the fetch  *)
  (* runs over a generic [tlb_consistent P] TLB, and the caller is handed  *)
  (* the post-fetch tlb cell + [tlb_consistent P] to do its data-side fill *)
  (* (which may install a foreign leaf, e.g. the UART leaf) and re-seal    *)
  (* [tlb_inv_gen P].  [HPsuper]/[Hdisc] are the fetch obligations.        *)
  (* ------------------------------------------------------------------- *)

  (* arbitrary-A/D raw-cell P-generic data engine *)

End WpInstrSConfig.

(* ===================================================================== *)
(* Part C -- the kernelvec client WPs.                                    *)
(* ===================================================================== *)
Section SmodeGprClients.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

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

  (* ---- c.addi16sp imm6 (S-mode, unified) ---- *)

  (* ---- jal rd, imm (S-mode, unified; 2-aligned F_Base: the fetch may
     WALK -- the first halfword's translation fills slot 5, the second
     halfword hits it) ---- *)

  (* ------------------------------------------------------------------- *)
  (* c.sdsp rs2, uimm*8(sp) -- UNIFIED: the fetch goes through the        *)
  (* invariant engine; the DATA translation case-splits on consistency at *)
  (* tlb_hash svpn (hit: state-preserving; miss: walk + fill, which       *)
  (* preserves the invariant).  ONE ident premise (the tlb_get_ppn form); *)
  (* the walk form is derived via [tlb_get_ppn_pw].                       *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* c.ldsp rd, uimm*8(sp) -- UNIFIED: like the store above, with the     *)
  (* data-address translation case-split on consistency at tlb_hash svpn  *)
  (* (hit: state-preserving; miss: LOAD page-walk + fill).                *)
  (* ------------------------------------------------------------------- *)

  (* ==================================================================== *)
  (* RAM wrappers: the whole S-mode superpage-identity geometry (Sv39      *)
  (* canonicality, VPN=svpn, identity translation, the gigapage masks) and *)
  (* the store/load PMP match are DISCHARGED from the owned points-to      *)
  (* (addr_is_ram, via [mem_ram] on bytes 0 and 7) using the ram_* lemmas. *)
  (* Callers need only own the frame bytes + one "PMP covers RAM" fact     *)
  (* ([pmpaddr00[0]*4 >= ram top]) and the sp-alignment; they no longer    *)
  (* carry the per-address translation preconditions.                      *)
  (* ==================================================================== *)


End SmodeGprClients.
