(* UmodeDataFault.v -- DATA-side translateAddr page-fault reductions.

   The data-access analogs of [exec_translateAddr_fetch_walk_u_pagefault]
   (UmodeWalk.v): when a U-mode LOAD/STORE effective address misses the TLB
   and the page walk returns [Err f] (unmapped / kernel-denied vpn), the
   [translateAddr] for [Load Data] / [Store Data] returns
   [Err (E_Load_Page_Fault)] / [Err (E_SAMO_Page_Fault)] with NO state
   change.  Clones of the fetch reduction with the access type swapped
   (and the extra MPRV=0 hypothesis the data effectivePrivilege needs).
   The walk-[Err] itself comes from [upt_unmapped_walk_fault] (access-
   generic) and the caller supplies the [translationException] fact. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodeCore.
Require Import WpDecodeBridge.
Require Import UmodeFetch UmodeFetchFault UmodeWalk.
Require Import UptInv.
Require Import UmodeData.
Require Import MemData4 MemData2 MemData1 WpGpr WpLoad UmodeLrsc.
Local Open Scope Z_scope.
Import Defs.

(* width-8 split helper (the width-4/2/1 analogs live in MemData4/2/1;
   there is no MemData8, so it is proved here for the LD/SD fault towers). *)
Lemma exec_split_misaligned_aligned_8 (vaddr : virtaddr) s :
  is_aligned_vaddr vaddr 8 = true ->
  exec (split_misaligned vaddr 8) s = Some ((1, 8), s).
Proof. intro H. unfold split_misaligned. rewrite H. cbn [orb]. apply exec_returnm. Qed.

(* LOAD: translateAddr faults through the walk with a load page fault *)
Lemma exec_translateAddr_load_walk_u_pagefault
    (vpn : mword 27) (root : mword 44) (f : PTW_Error)
    (va satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  exec (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s) ->
  exec (pt_walk 39 vpn (Load Data) User
          (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
          (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
          root 2 false tt) s
    = Some (Err (f, tt), s) ->
  exec (translationException (Load Data) f) s
    = Some (E_Load_Page_Fault tt, s) ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (Load Data)) s
    = Some (Err (E_Load_Page_Fault tt, tt), s).
Proof.
  intros Hcp HSXL HMPRV Hsatp Hmode Hasid Hppn Hlk Hwalk Hte Hcanon Hvpn_def.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_load_nm _ _ s HMPRV)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
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
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn) end.
  rewrite (execR_liftR_seq _ _ _ _ _
             (exec_translate_walk_user_err vpn (Load Data) User
                (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
                (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
                (mword_of_int 0) root f s Hlk
                (exec_translate_TLB_miss_user_walk_err vpn (Load Data) User
                   (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
                   (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
                   (mword_of_int 0) root f s Hwalk))).
  cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hte).
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

(* STORE: translateAddr faults through the walk with a store/amo page fault *)
Lemma exec_translateAddr_store_walk_u_pagefault
    (vpn : mword 27) (root : mword 44) (f : PTW_Error)
    (va satp0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = User ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1" : mword 1) = false ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
  exec (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s) ->
  exec (pt_walk 39 vpn (Store Data) User
          (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
          (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
          root 2 false tt) s
    = Some (Err (f, tt), s) ->
  exec (translationException (Store Data) f) s
    = Some (E_SAMO_Page_Fault tt, s) ->
  neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
  autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
  exec (translateAddr (Virtaddr va) (Store Data)) s
    = Some (Err (E_SAMO_Page_Fault tt, tt), s).
Proof.
  intros Hcp HSXL HMPRV Hsatp Hmode Hasid Hppn Hlk Hwalk Hte Hcanon Hvpn_def.
  unfold translateAddr.
  rewrite exec_catch_early_return.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_store_nm _ _ s HMPRV)).
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
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
    replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid);
    replace bppn with root by (symmetry; exact Hppn) end.
  rewrite (execR_liftR_seq _ _ _ _ _
             (exec_translate_walk_user_err vpn (Store Data) User
                (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
                (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
                (mword_of_int 0) root f s Hlk
                (exec_translate_TLB_miss_user_walk_err vpn (Store Data) User
                   (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
                   (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
                   (mword_of_int 0) root f s Hwalk))).
  cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hte).
  rewrite execR_returnR. cbn match.
  reflexivity.
Qed.

Section DataFaultFrame.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---- s_x transport: the page walk reads PT-slot MEMORY (dischargeable
     only at sigma, where mstate_interp sigma is held), but the model runs
     [execute] at the POST-FETCH state s' = [set_reg sigma nextPC v] (mem
     unchanged, only nextPC ticked).  These [_sx] clones extract the slot
     bytes at sigma and re-run the PURE read_pte/walk reductions at s' with
     s'-register lookups (= sigma's, via [tmig]/irrelevant_register_set) and
     the sigma-extracted bytes (s'.(mem) = sigma.(mem) definitionally). ---- *)

  (* one owned slot -> its [read_pte] fact AT s' = set_reg sigma nextPC v *)
  Lemma upt_slot_read_pte_sx (a : mword 64) (w : bv 64) (dq : dfrac)
      (σ : mstate) (v : mword 64) :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    (a ↦₈{dq} w) -∗
    ⌜exec (read_pte (Physaddr a) 8) (set_reg σ nextPC v)
       = Some (Ok w, set_reg σ nextPC v)⌝.
  Proof.
    iIntros (HA Hord HR Hcov Hpter) "Hhw [Hreg [Hmem Hdev]] Hw".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (word_pointsto_bytes with "Hw") as "Hbytes".
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
               σ.(mem) !! (pa_add a j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram a⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add a 7)⌝)%I as %Hram7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hbytes") as "Hb7".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb7") as %Hr7. iPureIntro. exact Hr7. }
    iPureIntro.
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    destruct (Hpter pmar0 Hpma_all a) as (region & Hpmam & Hptep).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n (set_reg σ nextPC v).(sregs)) 0)) = TOR).
    { unfold set_reg; cbn [sregs]. tmig. exact HA. }
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n (set_reg σ nextPC v).(sregs)) 0) = false).
    { unfold set_reg; cbn [sregs]. tmig. exact Hord. }
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n (set_reg σ nextPC v).(sregs)) 0)) ('b"1") = true).
    { unfold set_reg; cbn [sregs]. tmig. exact HR. }
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions (set_reg σ nextPC v).(sregs)) (Physaddr a) 8 = Some region).
    { unfold set_reg; cbn [sregs]. tmig. rewrite Lpma. exact Hpmam. }
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n (set_reg σ nextPC v).(sregs)) 0)) 4)
              (uint a) (uint (to_bits 64 8)) = PMP_Match).
    { unfold set_reg; cbn [sregs]. tmig.
      exact (ram_fetch_pmp a (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) 8 7
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram7 Hcov). }
    assert (Lhtif' : register_lookup htif_tohost_base (set_reg σ nextPC v).(sregs) = None).
    { unfold set_reg; cbn [sregs]. tmig. exact Lhtif. }
    assert (Hbf' : forall j : nat, (N.of_nat j < 8)%N ->
              (set_reg σ nextPC v).(mem) !! (pa_add a j) = Some (nth_byte w j)).
    { unfold set_reg; cbn [mem]. exact Hbf. }
    exact (exec_read_pte_S a region w (set_reg σ nextPC v)
             HA' Hord' Hrange' HR' Hpmam' Hal Hptep
             (within_clint_false a 8 (set_reg σ nextPC v) Hnc ltac:(lia))
             (within_sig_false a 8 (set_reg σ nextPC v) Hns ltac:(lia))
             (within_htif_false a 8 (set_reg σ nextPC v) Lhtif')
             (addr_is_ram_not_dev _ Hram)
             Hbf').
  Qed.

  (* the pt_walk-Err fact AT s' = set_reg sigma nextPC v (clone of
     [upt_unmapped_walk_fault], slot reads via [upt_slot_read_pte_sx]) *)
  Lemma upt_unmapped_walk_fault_sx (root : mword 44)
      (slots : gmap (mword 64) (mword 64))
      (spec : gmap (mword 27) uwalk_info)
      (vpn : mword 27) (acc : MemoryAccessType mem_payload)
      (mxr do_sum : bool) (σ : mstate) (v : mword 64) :
    spec !! vpn = None ->
    upt_fault_wf root slots spec ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_inv root slots spec -∗
    ⌜exists f : PTW_Error,
       exec (pt_walk 39 vpn acc User mxr do_sum root 2 false tt) (set_reg σ nextPC v)
         = Some (Err (f, tt), set_reg σ nextPC v) /\
       (f = PTW_Invalid_PTE tt \/ f = PTW_No_Permission tt)⌝.
  Proof.
    iIntros (Hvpn Hfwf HA Hord HR Hcov Hpter) "#Hhw Hint [Hslots %Hspec]".
    destruct (Hfwf vpn Hvpn) as
      [ (w2 & Hs2 & Hi2)
      | [ (w2 & w1 & Hs2 & Hv2 & Hn2 & Hs1 & Hi1)
        | (w2 & w1 & w0 & Hs2 & Hv2 & Hn2 & Hs1 & Hv1 & Hn1 & Hs0 & Hleaf) ] ].
    - iAssert (⌜exec (read_pte (Physaddr (uw_addr2 root vpn)) 8) (set_reg σ nextPC v)
                 = Some (Ok w2, set_reg σ nextPC v)⌝)%I as %Hr2.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs2 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte_sx _ _ _ _ v HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iPureIntro. exists (PTW_Invalid_PTE tt). split; [|by left].
      exact (exec_pt_walk_user_l2_invalid vpn acc User mxr do_sum root w2 (set_reg σ nextPC v) Hr2 Hi2).
    - iAssert (⌜exec (read_pte (Physaddr (uw_addr2 root vpn)) 8) (set_reg σ nextPC v)
                 = Some (Ok w2, set_reg σ nextPC v)⌝)%I as %Hr2.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs2 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte_sx _ _ _ _ v HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iAssert (⌜exec (read_pte (Physaddr (u_pte_addr (u_next_base w2)
                        (subrange_vec_dec vpn 17 9))) 8) (set_reg σ nextPC v)
                 = Some (Ok w1, set_reg σ nextPC v)⌝)%I as %Hr1.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs1 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte_sx _ _ _ _ v HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iPureIntro. exists (PTW_Invalid_PTE tt). split; [|by left].
      apply (exec_pt_walk_user_sub vpn acc User mxr do_sum root w2 _ (set_reg σ nextPC v) Hr2 Hv2 Hn2).
      intros g' a.
      exact (exec_rec_walk_l1_invalid vpn acc User mxr do_sum
               (u_next_base w2) w1 g' a (set_reg σ nextPC v) Hr1 Hi1).
    - iAssert (⌜exec (read_pte (Physaddr (uw_addr2 root vpn)) 8) (set_reg σ nextPC v)
                 = Some (Ok w2, set_reg σ nextPC v)⌝)%I as %Hr2.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs2 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte_sx _ _ _ _ v HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iAssert (⌜exec (read_pte (Physaddr (u_pte_addr (u_next_base w2)
                        (subrange_vec_dec vpn 17 9))) 8) (set_reg σ nextPC v)
                 = Some (Ok w1, set_reg σ nextPC v)⌝)%I as %Hr1.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs1 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte_sx _ _ _ _ v HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iAssert (⌜exec (read_pte (Physaddr (u_pte_addr (u_next_base w1)
                        (subrange_vec_dec vpn 8 0))) 8) (set_reg σ nextPC v)
                 = Some (Ok w0, set_reg σ nextPC v)⌝)%I as %Hr0.
      { iDestruct (big_sepM_lookup_acc _ _ _ _ Hs0 with "Hslots") as "[Hw _]".
        iApply (upt_slot_read_pte_sx _ _ _ _ v HA Hord HR Hcov Hpter
                  with "Hhw Hint Hw"). }
      iPureIntro.
      destruct Hleaf as [Hi0 | (Hv0 & Hl0 & Hden0)].
      + exists (PTW_Invalid_PTE tt). split; [|by left].
        apply (exec_pt_walk_user_sub vpn acc User mxr do_sum root w2 _ (set_reg σ nextPC v) Hr2 Hv2 Hn2).
        intros g' a.
        apply (exec_rec_walk_l1_sub vpn acc User mxr do_sum
                 (u_next_base w2) w1 g' _ a (set_reg σ nextPC v) Hr1 Hv1 Hn1).
        intros g'' a0.
        exact (exec_rec_walk_leaf_invalid vpn acc User mxr do_sum
                 (u_next_base w1) w0 g'' a0 (set_reg σ nextPC v) Hr0 Hi0).
      + exists (PTW_No_Permission tt). split; [|by right].
        apply (exec_pt_walk_user_sub vpn acc User mxr do_sum root w2 _ (set_reg σ nextPC v) Hr2 Hv2 Hn2).
        intros g' a.
        apply (exec_rec_walk_l1_sub vpn acc User mxr do_sum
                 (u_next_base w2) w1 g' _ a (set_reg σ nextPC v) Hr1 Hv1 Hn1).
        intros g'' a0.
        exact (exec_rec_walk_leaf_noperm vpn acc User mxr do_sum
                 (u_next_base w1) w0 g'' (PTE_No_Permission tt) a0 (set_reg σ nextPC v) Hr0 Hv0 Hl0
                 (fun s0 => Hden0 acc mxr do_sum s0)).
  Qed.

  (* frame-level: an UNMAPPED (or kernel-denied) data address page-faults,
     no state change -- the data analog of [upt_translateAddr_fetch_unmapped]. *)
  Lemma upt_translateAddr_load_unmapped (root : mword 44)
      (slots : gmap (mword 64) (mword 64))
      (spec : gmap (mword 27) uwalk_info)
      (vpn : mword 27) (va satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (σ : mstate) :
    spec !! vpn = None ->
    upt_fault_wf root slots spec ->
    upt_tlb_ok spec tlbvec ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp σ.(sregs) = satp0 ->
    register_lookup tlb σ.(sregs) = tlbvec ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_inv root slots spec -∗
    ⌜exec (translateAddr (Virtaddr va) (Load Data)) σ
       = Some (Err (E_Load_Page_Fault tt, tt), σ)⌝.
  Proof.
    iIntros (Hvpn Hfwf Hok Lpriv LSXL HMPRV Lsatp Ltlb Hmode Hasid Hroot Hcanon Hvpn_def
             HA Hord HR Hcov Hpter) "#Hhw Hint Hupt".
    iDestruct (upt_unmapped_walk_fault root slots spec vpn (Load Data)
                 (eq_vec (_get_Mstatus_MXR (register_lookup mstatus σ.(sregs))) ('b"1"))
                 (eq_vec (_get_Mstatus_SUM (register_lookup mstatus σ.(sregs))) ('b"1"))
                 σ Hvpn Hfwf HA Hord HR Hcov Hpter
                 with "Hhw Hint Hupt") as %(f & Hwalk & Hf).
    iPureIntro.
    assert (Hte : exec (translationException (Load Data) f) σ
                    = Some (E_Load_Page_Fault tt, σ)).
    { destruct Hf as [-> | ->];
        unfold translationException; cbn match; apply exec_returnm. }
    exact (exec_translateAddr_load_walk_u_pagefault vpn root f va satp0 σ
             Lpriv LSXL HMPRV Lsatp Hmode Hasid Hroot
             (upt_lookup_TLB_unmapped spec vpn tlbvec σ Hvpn Hok Ltlb)
             Hwalk Hte Hcanon Hvpn_def).
  Qed.

  (* frame-level: an UNMAPPED (or kernel-denied) data address page-faults,
     no state change -- the data analog of [upt_translateAddr_fetch_unmapped]. *)
  Lemma upt_translateAddr_store_unmapped (root : mword 44)
      (slots : gmap (mword 64) (mword 64))
      (spec : gmap (mword 27) uwalk_info)
      (vpn : mword 27) (va satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (σ : mstate) :
    spec !! vpn = None ->
    upt_fault_wf root slots spec ->
    upt_tlb_ok spec tlbvec ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp σ.(sregs) = satp0 ->
    register_lookup tlb σ.(sregs) = tlbvec ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_inv root slots spec -∗
    ⌜exec (translateAddr (Virtaddr va) (Store Data)) σ
       = Some (Err (E_SAMO_Page_Fault tt, tt), σ)⌝.
  Proof.
    iIntros (Hvpn Hfwf Hok Lpriv LSXL HMPRV Lsatp Ltlb Hmode Hasid Hroot Hcanon Hvpn_def
             HA Hord HR Hcov Hpter) "#Hhw Hint Hupt".
    iDestruct (upt_unmapped_walk_fault root slots spec vpn (Store Data)
                 (eq_vec (_get_Mstatus_MXR (register_lookup mstatus σ.(sregs))) ('b"1"))
                 (eq_vec (_get_Mstatus_SUM (register_lookup mstatus σ.(sregs))) ('b"1"))
                 σ Hvpn Hfwf HA Hord HR Hcov Hpter
                 with "Hhw Hint Hupt") as %(f & Hwalk & Hf).
    iPureIntro.
    assert (Hte : exec (translationException (Store Data) f) σ
                    = Some (E_SAMO_Page_Fault tt, σ)).
    { destruct Hf as [-> | ->];
        unfold translationException; cbn match; apply exec_returnm. }
    exact (exec_translateAddr_store_walk_u_pagefault vpn root f va satp0 σ
             Lpriv LSXL HMPRV Lsatp Hmode Hasid Hroot
             (upt_lookup_TLB_unmapped spec vpn tlbvec σ Hvpn Hok Ltlb)
             Hwalk Hte Hcanon Hvpn_def).
  Qed.

  (* ---- the s_x forms: the translate-Err fact AT the post-fetch state
     [set_reg sigma nextPC v], for the LOAD/STORE fault Iris arms. ---- *)
  Lemma upt_translateAddr_load_unmapped_sx (root : mword 44)
      (slots : gmap (mword 64) (mword 64))
      (spec : gmap (mword 27) uwalk_info)
      (vpn : mword 27) (va satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (σ : mstate) (v : mword 64) :
    spec !! vpn = None ->
    upt_fault_wf root slots spec ->
    upt_tlb_ok spec tlbvec ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp σ.(sregs) = satp0 ->
    register_lookup tlb σ.(sregs) = tlbvec ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_inv root slots spec -∗
    ⌜exec (translateAddr (Virtaddr va) (Load Data)) (set_reg σ nextPC v)
       = Some (Err (E_Load_Page_Fault tt, tt), set_reg σ nextPC v)⌝.
  Proof.
    iIntros (Hvpn Hfwf Hok Lpriv LSXL HMPRV Lsatp Ltlb Hmode Hasid Hroot Hcanon Hvpn_def
             HA Hord HR Hcov Hpter) "#Hhw Hint Hupt".
    iDestruct (upt_unmapped_walk_fault_sx root slots spec vpn (Load Data)
                 (eq_vec (_get_Mstatus_MXR (register_lookup mstatus (set_reg σ nextPC v).(sregs))) ('b"1"))
                 (eq_vec (_get_Mstatus_SUM (register_lookup mstatus (set_reg σ nextPC v).(sregs))) ('b"1"))
                 σ v Hvpn Hfwf HA Hord HR Hcov Hpter
                 with "Hhw Hint Hupt") as %(f & Hwalk & Hf).
    iPureIntro.
    assert (Hte : exec (translationException (Load Data) f) (set_reg σ nextPC v)
                    = Some (E_Load_Page_Fault tt, set_reg σ nextPC v)).
    { destruct Hf as [-> | ->];
        unfold translationException; cbn match; apply exec_returnm. }
    assert (Lpriv' : register_lookup cur_privilege (set_reg σ nextPC v).(sregs) = User)
      by (unfold set_reg; cbn [sregs]; tmig; exact Lpriv).
    assert (LSXL' : _get_Mstatus_SXL (register_lookup mstatus (set_reg σ nextPC v).(sregs)) = 'b"10")
      by (unfold set_reg; cbn [sregs]; tmig; exact LSXL).
    assert (HMPRV' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus (set_reg σ nextPC v).(sregs))) ('b"1" : mword 1) = false)
      by (unfold set_reg; cbn [sregs]; tmig; exact HMPRV).
    assert (Lsatp' : register_lookup satp (set_reg σ nextPC v).(sregs) = satp0)
      by (unfold set_reg; cbn [sregs]; tmig; exact Lsatp).
    assert (Ltlb' : register_lookup tlb (set_reg σ nextPC v).(sregs) = tlbvec)
      by (unfold set_reg; cbn [sregs]; tmig; exact Ltlb).
    exact (exec_translateAddr_load_walk_u_pagefault vpn root f va satp0 (set_reg σ nextPC v)
             Lpriv' LSXL' HMPRV' Lsatp' Hmode Hasid Hroot
             (upt_lookup_TLB_unmapped spec vpn tlbvec (set_reg σ nextPC v) Hvpn Hok Ltlb')
             Hwalk Hte Hcanon Hvpn_def).
  Qed.

  Lemma upt_translateAddr_store_unmapped_sx (root : mword 44)
      (slots : gmap (mword 64) (mword 64))
      (spec : gmap (mword 27) uwalk_info)
      (vpn : mword 27) (va satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (σ : mstate) (v : mword 64) :
    spec !! vpn = None ->
    upt_fault_wf root slots spec ->
    upt_tlb_ok spec tlbvec ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1" : mword 1) = false ->
    register_lookup satp σ.(sregs) = satp0 ->
    register_lookup tlb σ.(sregs) = tlbvec ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    (forall regions, pma_allows_all regions -> pma_allows_pte_read regions) ->
    hw_config -∗
    mstate_interp σ -∗
    upt_inv root slots spec -∗
    ⌜exec (translateAddr (Virtaddr va) (Store Data)) (set_reg σ nextPC v)
       = Some (Err (E_SAMO_Page_Fault tt, tt), set_reg σ nextPC v)⌝.
  Proof.
    iIntros (Hvpn Hfwf Hok Lpriv LSXL HMPRV Lsatp Ltlb Hmode Hasid Hroot Hcanon Hvpn_def
             HA Hord HR Hcov Hpter) "#Hhw Hint Hupt".
    iDestruct (upt_unmapped_walk_fault_sx root slots spec vpn (Store Data)
                 (eq_vec (_get_Mstatus_MXR (register_lookup mstatus (set_reg σ nextPC v).(sregs))) ('b"1"))
                 (eq_vec (_get_Mstatus_SUM (register_lookup mstatus (set_reg σ nextPC v).(sregs))) ('b"1"))
                 σ v Hvpn Hfwf HA Hord HR Hcov Hpter
                 with "Hhw Hint Hupt") as %(f & Hwalk & Hf).
    iPureIntro.
    assert (Hte : exec (translationException (Store Data) f) (set_reg σ nextPC v)
                    = Some (E_SAMO_Page_Fault tt, set_reg σ nextPC v)).
    { destruct Hf as [-> | ->];
        unfold translationException; cbn match; apply exec_returnm. }
    assert (Lpriv' : register_lookup cur_privilege (set_reg σ nextPC v).(sregs) = User)
      by (unfold set_reg; cbn [sregs]; tmig; exact Lpriv).
    assert (LSXL' : _get_Mstatus_SXL (register_lookup mstatus (set_reg σ nextPC v).(sregs)) = 'b"10")
      by (unfold set_reg; cbn [sregs]; tmig; exact LSXL).
    assert (HMPRV' : eq_vec (_get_Mstatus_MPRV (register_lookup mstatus (set_reg σ nextPC v).(sregs))) ('b"1" : mword 1) = false)
      by (unfold set_reg; cbn [sregs]; tmig; exact HMPRV).
    assert (Lsatp' : register_lookup satp (set_reg σ nextPC v).(sregs) = satp0)
      by (unfold set_reg; cbn [sregs]; tmig; exact Lsatp).
    assert (Ltlb' : register_lookup tlb (set_reg σ nextPC v).(sregs) = tlbvec)
      by (unfold set_reg; cbn [sregs]; tmig; exact Ltlb).
    exact (exec_translateAddr_store_walk_u_pagefault vpn root f va satp0 (set_reg σ nextPC v)
             Lpriv' LSXL' HMPRV' Lsatp' Hmode Hasid Hroot
             (upt_lookup_TLB_unmapped spec vpn tlbvec (set_reg σ nextPC v) Hvpn Hok Ltlb')
             Hwalk Hte Hcanon Hvpn_def).
  Qed.
End DataFaultFrame.

(* ===================================================================== *)
(* Piece C: width-4 LOAD/STORE fault-execute towers.                      *)
(*                                                                         *)
(* Mirrors MemData4's SUCCESS vmem_read/vmem_write chains, but the         *)
(* translate step returns [Err (E_Load_Page_Fault)] / [Err                 *)
(* (E_SAMO_Page_Fault)] directly: the untilMT loop body takes translate's  *)
(* Err arm -> memory_exception -> early_return the Trap.  Cause is         *)
(* width-independent, so a single width-4 tower suffices for LW/SW; the    *)
(* Iris arm reuses it after the fetch decodes a LOAD/STORE.                *)
(* ===================================================================== *)

Section GenLoadFault4.
  Variable a : mword 64.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_Load_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Load Data)) s
                   = Some (Err (E_Load_Page_Fault tt, tt), s).

  Lemma exec_vmem_read_addr_load_fault_4 :
    exec (vmem_read_addr (Virtaddr a) 4 (Load Data) false false false) s
      = Some (Err W, s).
  Proof.
    unfold vmem_read_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result (mword (4 * 8)) ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W), s))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?inner ?post) s = _ =>
          assert (Hbody : execR inner s = Some (inl (Err W), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 4))) (E_Load_Page_Fault tt) s)).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul4.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.

  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s = Some (Virtaddr a, s).

  Lemma exec_vmem_read_load_fault_4 :
    exec (vmem_read (Regidx rs1) offset 4 (Load Data) false false false) s = Some (Err W, s).
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite exec_vmem_read_addr_load_fault_4.
    reflexivity.
  Qed.

  Lemma exec_execute_LOAD_fault_4 (is_unsigned : bool) :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))) s = Some (W, s).
  Proof.
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 4).
    unfold execute_LOAD.
    assert (Hass : exec (assert_exp' (Z.leb 4 xlen_bytes) "extensions/I/base_insts.sail:289.28-289.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ exec_vmem_read_load_fault_4).
    cbn match. apply exec_returnM.
  Qed.
End GenLoadFault4.

Section GenStoreFault4.
  Variable a : mword 64.
  Variable data : bv 32.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_SAMO_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                   = Some (Err (E_SAMO_Page_Fault tt, tt), s).

  Lemma exec_vmem_write_addr_store_fault_4 :
    exec (vmem_write_addr (Virtaddr a) 4 data (Store Data) false false false) s
      = Some (Err W, s).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 4)) s = Some (inr (1, 4), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_4 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W), s))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?inner ?post) s = _ =>
          assert (Hbody : execR inner s = Some (inl (Err W), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 4))) (E_SAMO_Page_Fault tt) s)).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul4.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.

  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).

  Lemma exec_vmem_write_store_fault_4 :
    exec (vmem_write (Regidx rs1) offset 4 data (Store Data) false false false) s = Some (Err W, s).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 4) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 4 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite exec_vmem_write_addr_store_fault_4.
    reflexivity.
  Qed.
End GenStoreFault4.

Section GenExecStoreFault4.
  Variable a : mword 64.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_SAMO_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 4 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 4))) (Store Data)) s
                   = Some (Err (E_SAMO_Page_Fault tt, tt), s).
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).

  Lemma exec_execute_STORE_fault_4 :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s = Some (W, s).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
    unfold execute_STORE.
    assert (Hass : exec (assert_exp' (Z.leb 4 xlen_bytes) "extensions/I/base_insts.sail:320.28-320.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_vmem_write_store_fault_4 a _ s Halign Htr rs1 imm Htea)).
    cbn match. apply exec_returnM.
  Qed.
End GenExecStoreFault4.


Section GenLoadFault2.
  Variable a : mword 64.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_Load_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 2 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 2))) (Load Data)) s
                   = Some (Err (E_Load_Page_Fault tt, tt), s).

  Lemma exec_vmem_read_addr_load_fault_2 :
    exec (vmem_read_addr (Virtaddr a) 2 (Load Data) false false false) s
      = Some (Err W, s).
  Proof.
    unfold vmem_read_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result (mword (2 * 8)) ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 2)) s = Some (inr (1, 2), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_2 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W), s))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?inner ?post) s = _ =>
          assert (Hbody : execR inner s = Some (inl (Err W), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 2))) (E_Load_Page_Fault tt) s)).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul2.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.

  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s = Some (Virtaddr a, s).

  Lemma exec_vmem_read_load_fault_2 :
    exec (vmem_read (Regidx rs1) offset 2 (Load Data) false false false) s = Some (Err W, s).
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 2) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 2 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite exec_vmem_read_addr_load_fault_2.
    reflexivity.
  Qed.

  Lemma exec_execute_LOAD_fault_2 (is_unsigned : bool) :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2))) s = Some (W, s).
  Proof.
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 2)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 2).
    unfold execute_LOAD.
    assert (Hass : exec (assert_exp' (Z.leb 2 xlen_bytes) "extensions/I/base_insts.sail:289.28-289.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ exec_vmem_read_load_fault_2).
    cbn match. apply exec_returnM.
  Qed.
End GenLoadFault2.

Section GenStoreFault2.
  Variable a : mword 64.
  Variable data : bv 16.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_SAMO_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 2 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 2))) (Store Data)) s
                   = Some (Err (E_SAMO_Page_Fault tt, tt), s).

  Lemma exec_vmem_write_addr_store_fault_2 :
    exec (vmem_write_addr (Virtaddr a) 2 data (Store Data) false false false) s
      = Some (Err W, s).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 2)) s = Some (inr (1, 2), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_2 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W), s))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?inner ?post) s = _ =>
          assert (Hbody : execR inner s = Some (inl (Err W), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 2))) (E_SAMO_Page_Fault tt) s)).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul2.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.

  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).

  Lemma exec_vmem_write_store_fault_2 :
    exec (vmem_write (Regidx rs1) offset 2 data (Store Data) false false false) s = Some (Err W, s).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 2) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 2 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite exec_vmem_write_addr_store_fault_2.
    reflexivity.
  Qed.
End GenStoreFault2.

Section GenExecStoreFault2.
  Variable a : mword 64.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_SAMO_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 2 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 2))) (Store Data)) s
                   = Some (Err (E_SAMO_Page_Fault tt, tt), s).
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).

  Lemma exec_execute_STORE_fault_2 :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 2))) s = Some (W, s).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 2)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 2).
    unfold execute_STORE.
    assert (Hass : exec (assert_exp' (Z.leb 2 xlen_bytes) "extensions/I/base_insts.sail:320.28-320.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_vmem_write_store_fault_2 a _ s Halign Htr rs1 imm Htea)).
    cbn match. apply exec_returnM.
  Qed.
End GenExecStoreFault2.

Section GenLoadFault1.
  Variable a : mword 64.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_Load_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 1))) (Load Data)) s
                   = Some (Err (E_Load_Page_Fault tt, tt), s).

  Lemma exec_vmem_read_addr_load_fault_1 :
    exec (vmem_read_addr (Virtaddr a) 1 (Load Data) false false false) s
      = Some (Err W, s).
  Proof.
    unfold vmem_read_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result (mword (1 * 8)) ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 1)) s = Some (inr (1, 1), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_1 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W), s))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?inner ?post) s = _ =>
          assert (Hbody : execR inner s = Some (inl (Err W), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 1))) (E_Load_Page_Fault tt) s)).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul1.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.

  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s = Some (Virtaddr a, s).

  Lemma exec_vmem_read_load_fault_1 :
    exec (vmem_read (Regidx rs1) offset 1 (Load Data) false false false) s = Some (Err W, s).
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 1) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 1 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite exec_vmem_read_addr_load_fault_1.
    reflexivity.
  Qed.

  Lemma exec_execute_LOAD_fault_1 (is_unsigned : bool) :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1))) s = Some (W, s).
  Proof.
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 1)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 1).
    unfold execute_LOAD.
    assert (Hass : exec (assert_exp' (Z.leb 1 xlen_bytes) "extensions/I/base_insts.sail:289.28-289.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ exec_vmem_read_load_fault_1).
    cbn match. apply exec_returnM.
  Qed.
End GenLoadFault1.

Section GenStoreFault1.
  Variable a : mword 64.
  Variable data : bv 8.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_SAMO_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 1))) (Store Data)) s
                   = Some (Err (E_SAMO_Page_Fault tt, tt), s).

  Lemma exec_vmem_write_addr_store_fault_1 :
    exec (vmem_write_addr (Virtaddr a) 1 data (Store Data) false false false) s
      = Some (Err W, s).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 1)) s = Some (inr (1, 1), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_1 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W), s))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?inner ?post) s = _ =>
          assert (Hbody : execR inner s = Some (inl (Err W), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 1))) (E_SAMO_Page_Fault tt) s)).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul1.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.

  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).

  Lemma exec_vmem_write_store_fault_1 :
    exec (vmem_write (Regidx rs1) offset 1 data (Store Data) false false false) s = Some (Err W, s).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 1) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 1 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite exec_vmem_write_addr_store_fault_1.
    reflexivity.
  Qed.
End GenStoreFault1.

Section GenExecStoreFault1.
  Variable a : mword 64.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_SAMO_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 1 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 1))) (Store Data)) s
                   = Some (Err (E_SAMO_Page_Fault tt, tt), s).
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).

  Lemma exec_execute_STORE_fault_1 :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 1))) s = Some (W, s).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 1)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 1).
    unfold execute_STORE.
    assert (Hass : exec (assert_exp' (Z.leb 1 xlen_bytes) "extensions/I/base_insts.sail:320.28-320.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_vmem_write_store_fault_1 a _ s Halign Htr rs1 imm Htea)).
    cbn match. apply exec_returnM.
  Qed.
End GenExecStoreFault1.


Section GenLoadFault8.
  Variable a : mword 64.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_Load_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 8))) (Load Data)) s
                   = Some (Err (E_Load_Page_Fault tt, tt), s).

  Lemma exec_vmem_read_addr_load_fault_8 :
    exec (vmem_read_addr (Virtaddr a) 8 (Load Data) false false false) s
      = Some (Err W, s).
  Proof.
    unfold vmem_read_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result (mword (8 * 8)) ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_8 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W), s))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?inner ?post) s = _ =>
          assert (Hbody : execR inner s = Some (inl (Err W), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 8))) (E_Load_Page_Fault tt) s)).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul8.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.

  Variable rs1 rd : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Load Data)) s = Some (Virtaddr a, s).

  Lemma exec_vmem_read_load_fault_8 :
    exec (vmem_read (Regidx rs1) offset 8 (Load Data) false false false) s = Some (Err W, s).
  Proof.
    unfold vmem_read. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Load Data) 8) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Load Data) 8 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite exec_vmem_read_addr_load_fault_8.
    reflexivity.
  Qed.

  Lemma exec_execute_LOAD_fault_8 (is_unsigned : bool) :
    exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 8))) s = Some (W, s).
  Proof.
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 8)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 8).
    unfold execute_LOAD.
    assert (Hass : exec (assert_exp' (Z.leb 8 xlen_bytes) "extensions/I/base_insts.sail:289.28-289.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ exec_vmem_read_load_fault_8).
    cbn match. apply exec_returnM.
  Qed.
End GenLoadFault8.

Section GenStoreFault8.
  Variable a : mword 64.
  Variable data : bv 64.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_SAMO_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 8))) (Store Data)) s
                   = Some (Err (E_SAMO_Page_Fault tt, tt), s).

  Lemma exec_vmem_write_addr_store_fault_8 :
    exec (vmem_write_addr (Virtaddr a) 8 data (Store Data) false false false) s
      = Some (Err W, s).
  Proof.
    unfold vmem_write_addr.
    rewrite exec_catch_early_return.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    assert (Hinner : execR (returnR (result bool ExecutionResult) tt >>
                            liftR (split_misaligned (Virtaddr a) 8)) s = Some (inr (1, 8), s)).
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite (exec_split_misaligned_aligned_8 (Virtaddr a) s Halign). reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hinner).
    rewrite misaligned_order_1.
    match goal with
    | |- context [ Defs.bind (Defs.untilMT ?vs ?m ?c ?b) ?post ] =>
      assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inl (Err W), s))
    end.
    { eapply execR_untilMT_1_early.
      - reflexivity.
      - cbn match.
        assert (Hass : exec (assert_exp' true "loop dummy assert") s = Some (@eq_refl bool true, s)) by reflexivity.
        rewrite (execR_liftR_seq _ _ _ _ _ Hass).
        rewrite (execR_liftR_seq _ _ _ _ _ Htr).
        cbn [bits_of_virtaddr] in *. cbn match.
        match goal with
        | |- execR (Defs.bind ?inner ?post) s = _ =>
          assert (Hbody : execR inner s = Some (inl (Err W), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _
            (exec_memory_exception (Virtaddr (add_vec_int a (0 * 8))) (E_SAMO_Page_Fault tt) s)).
          cbn match. cbn [bits_of_virtaddr]. rewrite avi0_mul8.
          unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
        rewrite execR_bind. rewrite Hbody. reflexivity. }
    rewrite execR_bind. rewrite Hu. cbn match. reflexivity.
  Qed.

  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).

  Lemma exec_vmem_write_store_fault_8 :
    exec (vmem_write (Regidx rs1) offset 8 data (Store Data) false false false) s = Some (Err W, s).
  Proof.
    unfold vmem_write. rewrite exec_catch_early_return.
    assert (Hgta : exec (get_transformed_data_addr (Regidx rs1) offset (Store Data) 8) s
                   = Some (Ext_DataAddr_OK (Virtaddr a), s)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 offset (Store Data) 8 s)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ Htea).
      apply exec_returnM. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgta).
    cbn match.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Virtaddr a) s)).
    rewrite execR_liftR.
    rewrite exec_vmem_write_addr_store_fault_8.
    reflexivity.
  Qed.
End GenStoreFault8.

Section GenExecStoreFault8.
  Variable a : mword 64.
  Variable s : mstate.
  Let W : ExecutionResult :=
    Trap (register_lookup cur_privilege s.(sregs),
          make_sync_exception (E_SAMO_Page_Fault tt) a,
          register_lookup PC s.(sregs)).
  Variable rs2 rs1 : mword 5.
  Variable imm : mword 12.
  Let offset := sign_extend' 64 imm.
  Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
  Hypothesis Halign : is_aligned_vaddr (Virtaddr a) 8 = true.
  Hypothesis Htr : exec (translateAddr (Virtaddr (add_vec_int (bits_of_virtaddr (Virtaddr a)) (0 * 8))) (Store Data)) s
                   = Some (Err (E_SAMO_Page_Fault tt, tt), s).
  Hypothesis Htea : exec (transform_effective_address (Virtaddr ea) (Store Data)) s = Some (Virtaddr a, s).

  Lemma exec_execute_STORE_fault_8 :
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s = Some (W, s).
  Proof.
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 8)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 8).
    unfold execute_STORE.
    assert (Hass : exec (assert_exp' (Z.leb 8 xlen_bytes) "extensions/I/base_insts.sail:320.28-320.29" : M (_ = _)) s = Some (@eq_refl bool true, s)) by reflexivity.
    rewrite (exec_bind_Some _ _ _ _ _ Hass).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_vmem_write_store_fault_8 a _ s Halign Htr rs1 imm Htea)).
    cbn match. apply exec_returnM.
  Qed.
End GenExecStoreFault8.
