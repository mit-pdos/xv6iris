From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpSmode WpSmode2 WpKernelvec.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpPageWalk.v — address translation through an actual Sv39 PAGE TABLE when the
   TLB is empty (TLB miss → page walk reading PTEs from memory → TLB fill).
   A valid identity page table is represented by a single 1GB superpage leaf PTE
   (8 bytes) owned in memory at the root page-table; the walk reads it via
   read_pte (Supervisor Load PageTableEntry, PMP R-grant), fills the TLB, and
   returns the identity physical address.  Capstone: exec_translateAddr_walk. *)

Section PW.
  Context `{!riscvGS Σ}.

  (* ---- Load-permission Supervisor PMP grant (R bit instead of X) ---- *)
  Lemma exec_pmpCheck_supervisor_grant_load (a : mword 64) (width : Z) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a) (uint (to_bits 64 width)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    exec (pmpCheck (Physaddr a) width (Load PageTableEntry) Supervisor) s = Some (None, s).
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
                              (Load PageTableEntry)) s = Some (true, s))).
      2:{ unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm. }
      cbn match. rewrite execR_returnR. cbn beta.
      cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
      unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
    rewrite Hfe. cbn match. reflexivity.
  Qed.

  (* pmaCheck for a PTE load: the Load PageTableEntry arm returns PMA_supports_pte_read. *)
  Lemma exec_pmaCheck_ram_pte (addr : mword 64) (pbmt : page_based_mem_type)
      (region : PMA_Region) s :
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
    is_aligned_paddr (Physaddr addr) 8 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_supports_pte_read) = true ->
    exec (pmaCheck (Physaddr addr) 8 (Load PageTableEntry) pbmt false) s = Some (None, s).
  Proof.
    intros Hmatch Halign Hpte.
    unfold pmaCheck.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
    rewrite Hmatch.
    destruct region as [rbase rsize rattr rdtree].
    cbn [PMA_Region_attributes] in Hpte |- *.
    rewrite Halign. cbn [Riscv.rv64d.not negb].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
    cbn match beta.
    change (assert_exp' true "sys/mem.sail:105.61-105.62" >>=
            (fun _ : true = true => returnM (PMA_supports_pte_read (override_PMA rattr pbmt))))
      with (returnM (PMA_supports_pte_read (override_PMA rattr pbmt)) : M bool).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
    rewrite Hpte. cbn match.
    apply exec_returnM.
  Qed.

  Lemma exec_checked_mem_read_ram_pte_S (addr : mword 64) (region : PMA_Region) (w : bv 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
    is_aligned_paddr (Physaddr addr) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (checked_mem_read (Load PageTableEntry) PBMT_PMA Supervisor (Physaddr addr) 8 false false false false)
         s = Some (Ok (w, default_meta), s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hbytes.
    unfold checked_mem_read.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
    2:{ unfold phys_access_check.
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_pmpCheck_supervisor_grant_load addr 8 s HA Hord Hrange HR)).
        cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_pte addr PBMT_PMA region s Hmatch Halign Hread)).
        cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s))).
    2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
        rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
    2:{ unfold read_kind_of_flags. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_8 addr w s Hbytes)).
    apply exec_returnM.
  Qed.

  Lemma exec_read_pte_S (addr : mword 64) (region : PMA_Region) (w : bv 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
    is_aligned_paddr (Physaddr addr) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr addr) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (read_pte (Physaddr addr) 8) s = Some (Ok w, s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hbytes.
    unfold read_pte, mem_read_priv.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
    2:{ unfold mem_read_priv_meta. cbn [orb andb].
        rewrite (exec_bind_Some _ _ _ _ _
                  (_ : exec (checked_mem_read _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
        2:{ cbn match. apply exec_checked_mem_read_ram_pte_S with (region := region); assumption. }
        cbn match. unfold mem_read_callback. apply exec_returnM. }
    cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
  Qed.

  (* ---- Concrete identity page table for VA 0x800053e0 (single 1GB superpage) ----
     A valid Sv39 identity mapping: the root page-table at PPN 0x80100 has, at
     index VPN[2]=2, a LEAF PTE mapping the 1GB region [0x80000000,0xC0000000)
     identically (ppn field 0x80000 = 1GB-aligned, flags D A X W R V).
     Walk reads exactly one PTE → output ppn 0x80005 → pa 0x800053e0 (identity). *)
  Definition pw_root_ppn : Z := 0x80100.
  Definition pte_super : mword 64 := mword_of_int (Z.lor (Z.shiftl 0x80000 10) 0xCF).
  Definition a_super : mword 64 := mword_of_int 0x80100010.  (* root<<12 + VPN[2]*8 *)
  Definition pw_vpn : mword 27 := mword_of_int 0x80005.

  (* The single-level (1GB superpage) page walk: TLB miss reads ONE PTE from
     memory and returns the identity translation output ppn 0x80005. *)
  Lemma exec_pt_walk_super (mxr do_sum : bool) (region : PMA_Region) (menvcfg0 : mword 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (mword_of_int 0x80100010 : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (mword_of_int 0x80100010)) 8 = Some region ->
    is_aligned_paddr (Physaddr (mword_of_int 0x80100010)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (mword_of_int 0x80100010) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (pt_walk 39 pw_vpn (InstructionFetch tt) Supervisor mxr do_sum
            (mword_of_int pw_root_ppn : mword 44) 2 false tt) s
      = Some (Ok (Build_PTW_Output 39 (mword_of_int 0x80005) (autocast (T := mword) pte_super)
                    (Physaddr (mword_of_int 0x80100010)) 2 PBMT_PMA false, tt), s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold pt_walk, Zwf_guarded.
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    (* assert (2>=0) and (39=32||xlen=64), both true *)
    assert (Hae1 : exec (Defs.assert_exp' (2 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    (* read_pte: rewrite address to literal, width to 8 *)
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (mword_of_int 0x80100010 : mword 64) by (vm_compute; reflexivity);
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_read_pte_S (mword_of_int 0x80100010) region pte_super s
                  HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes)).
    (* pte_is_invalid pte_super = false (V=R=W=X=1, no reserved bits, no reg read) *)
    assert (Hinv : exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte_super 7 0))
                           (ext_bits_of_PTE pte_super)) s = Some (false, s))
      by (vm_compute; reflexivity).
    rewrite (execR_liftR_seq _ _ _ _ _ Hinv).
    match goal with |- context[pte_is_non_leaf ?f] =>
      replace (pte_is_non_leaf f) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    (* leaf branch: misalign check false (ppn 17:0 = 0), then >> check_PTE *)
    match goal with |- context[neq_vec ?a ?b] =>
      replace (neq_vec a b) with false by (vm_compute; reflexivity) end.
    cbv iota beta.
    change (2 >? 0) with true. cbv iota beta.
    assert (Hchk : exec (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
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
    (* bind the computed ppn (= 0x80005) *)
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    (* read menvcfg → menvcfg0, PBMTE=0 ⇒ PBMT_PMA *)
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg menvcfg s)).
    rewrite Hmenv. rewrite HPBMTE. cbv iota beta.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite execR_returnR. cbn match.
    repeat f_equal; (try apply bv_eq); vm_compute; reflexivity.
  Qed.

  (* The superpage TLB entry that the walk installs at hash index 5. *)
  Definition pw_tlb_entry (asid : mword 16) : TLB_Entry := {|
    TLB_Entry_asid     := asid;
    TLB_Entry_global   := false;
    TLB_Entry_vpn      := mword_of_int 0x80000;
    TLB_Entry_levelMask := mword_of_int 0x3FFFF;
    TLB_Entry_ppn      := mword_of_int 0x80000;
    TLB_Entry_pte      := pte_super;
    TLB_Entry_pteAddr  := Physaddr (mword_of_int 0x80100010);
  |}.

  (* add_to_TLB installs the entry at index 5 (= tlb_hash 39 pw_vpn), changing state. *)
  Lemma exec_add_to_TLB_super (asid : mword 16) s :
    exec (add_to_TLB 39 asid pw_vpn (mword_of_int 0x80005 : mword 44) (autocast (T := mword) pte_super)
            (Physaddr (mword_of_int 0x80100010)) 2 false) s
      = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs)) 5 (Some (pw_tlb_entry asid)))).
  Proof.
    unfold add_to_TLB. cbn zeta.
    replace (tlb_hash (__id 39) pw_vpn) with 5 by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb _)).
    rewrite exec_returnm.
    do 3 f_equal.
  Qed.

  (* translate_TLB_miss: walk one PTE from memory, no PTE writeback (A set),
     fill the TLB at index 5, return the identity output ppn. STATE CHANGES. *)
  Lemma exec_translate_TLB_miss_super (mxr do_sum : bool) (asid : mword 16) (region : PMA_Region) (menvcfg0 : mword 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (mword_of_int 0x80100010 : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (mword_of_int 0x80100010)) 8 = Some region ->
    is_aligned_paddr (Physaddr (mword_of_int 0x80100010)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (mword_of_int 0x80100010) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate_TLB_miss 39 asid (mword_of_int pw_root_ppn : mword 44) pw_vpn
            (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (mword_of_int 0x80005 : mword 44, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs)) 5 (Some (pw_tlb_entry asid)))).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_super mxr do_sum region menvcfg0 s
                  HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)).
    cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (vm_compute; reflexivity) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_add_to_TLB_super asid s)).
    apply exec_returnm.
  Qed.

  (* lookup_TLB on an empty slot at index 5 ⇒ miss. *)
  Lemma exec_lookup_TLB_miss (asid : mword 16) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = None ->
    exec (lookup_TLB 39 asid pw_vpn) s = Some (None, s).
  Proof.
    intros Htlb Hvec.
    unfold lookup_TLB.
    replace (tlb_hash (__id 39) pw_vpn) with 5 by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec. apply exec_returnm.
  Qed.

  Lemma exec_translate_walk (mxr do_sum : bool) (asid : mword 16) (region : PMA_Region)
        (menvcfg0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = None ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (mword_of_int 0x80100010 : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (mword_of_int 0x80100010)) 8 = Some region ->
    is_aligned_paddr (Physaddr (mword_of_int 0x80100010)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (mword_of_int 0x80100010) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translate 39 asid (mword_of_int pw_root_ppn : mword 44) pw_vpn
            (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (mword_of_int 0x80005 : mword 44, PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec tlbvec 5 (Some (pw_tlb_entry asid)))).
  Proof.
    intros Htlb Hvec HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_miss asid tlbvec s Htlb Hvec)).
    cbn match.
    rewrite <- Htlb.
    apply (exec_translate_TLB_miss_super mxr do_sum asid region menvcfg0 s
             HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE).
  Qed.

  (* FULL Sv39 translation of vaddr 0x800053e0 with an EMPTY TLB: the page walk
     reads the PTE from memory and fills the TLB (state change). satp encodes
     MODE=Sv39, ASID=0, root PPN 0x80100. *)
  Definition pw_satp : mword 64 := mword_of_int 0x8000000000080100.

  Lemma exec_translateAddr_walk (region : PMA_Region) (menvcfg0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = pw_satp ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = None ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (mword_of_int 0x80100010 : mword 64)) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (mword_of_int 0x80100010)) 8 = Some region ->
    is_aligned_paddr (Physaddr (mword_of_int 0x80100010)) 8 = true ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    exec (within_clint (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    exec (within_sig (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (mword_of_int 0x80100010) j) = Some (nth_byte pte_super j)) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec (translateAddr (Virtaddr (mword_of_int 0x800053e0)) (InstructionFetch tt)) s
      = Some (Ok (Physaddr (mword_of_int 0x800053e0), PBMT_PMA, init_ext_ptw),
              set_reg s tlb (vec_update_dec tlbvec 5 (Some (pw_tlb_entry (mword_of_int 0))))).
  Proof.
    intros Hcp HSXL Hsatp Htlb Hvec HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 pw_satp s HSXL Hsatp
               ltac:(vm_compute; reflexivity))).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) pw_satp, s)).
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
    replace (neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e0 : mword 64)))
               (sign_extend' 64
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e0 : mword 64)))
                     (Z.sub 39 1) 0))) with false by (vm_compute; reflexivity).
    cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    (* normalise vpn, base_ppn, asid arguments of translate to the concrete walk *)
    match goal with |- context[translate 39 ?asid ?bppn ?vpn _ _ _ _ _] =>
      replace vpn with pw_vpn by (apply bv_eq; vm_compute; reflexivity);
      replace bppn with (mword_of_int pw_root_ppn : mword 44) by (apply bv_eq; vm_compute; reflexivity);
      replace asid with (mword_of_int 0 : mword 16) by (apply bv_eq; vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_translate_walk _ _ (mword_of_int 0) region menvcfg0 tlbvec s
                  Htlb Hvec HA Hord Hrange HR Hmatch Halign Hpte Hc Hsig Hh Hbytes Hmenv HPBMTE)).
    cbn match.
    rewrite execR_returnR. cbn match.
    f_equal.
  Qed.

  (* The state after the fetch's page walk: TLB filled at index 5. *)
  Definition pw_filled (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate) : mstate :=
    set_reg s tlb (vec_update_dec tlbvec 5 (Some (pw_tlb_entry (mword_of_int 0)))).

Section FetchWalk.
  Context (region region_pte : PMA_Region) (w : mword 32) (menvcfg0 : mword 64)
          (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (s : mstate).
  Let a := mword_of_int 0x800053e0 : mword 64.    (* instruction vaddr = paddr *)
  Let sf := pw_filled tlbvec s.
  (* ---- page-walk hypotheses (evaluated at s) ---- *)
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = a.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = pw_satp.
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec 5 = None.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = menvcfg0.
  Hypothesis HPBMTE : eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true.
  (* PMP/PMA + PTE bytes for the page-table entry read (at s) *)
  Hypothesis pHA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis pHord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis pHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (mword_of_int 0x80100010 : mword 64)) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis pHR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis pHmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr (mword_of_int 0x80100010)) 8 = Some region_pte.
  Hypothesis pHalign : is_aligned_paddr (Physaddr (mword_of_int 0x80100010)) 8 = true.
  Hypothesis pHpte : (override_PMA (PMA_Region_attributes region_pte) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis pHc : exec (within_clint (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s).
  Hypothesis pHsig : exec (within_sig (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s).
  Hypothesis pHh : exec (within_htif_readable (Physaddr (mword_of_int 0x80100010)) 8) s = Some (false, s).
  Hypothesis pHbytes : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add (mword_of_int 0x80100010) j) = Some (nth_byte pte_super j).
  (* PMP/PMA + instruction bytes for the fetch read (evaluated at the FILLED state sf) *)
  Hypothesis iHA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sf.(sregs)) 0)) = TOR.
  Hypothesis iHord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0) = false.
  Hypothesis iHrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sf.(sregs)) 0)) 4)
      (uint a) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis iHX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n sf.(sregs)) 0)) ('b"1") = true.
  Hypothesis iHmatch : matching_pma_region (register_lookup pma_regions sf.(sregs)) (Physaddr a) 4 = Some region.
  Hypothesis iHalign : is_aligned_paddr (Physaddr a) 4 = true.
  Hypothesis iHexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis iHc : exec (within_clint (Physaddr a) 4) sf = Some (false, sf).
  Hypothesis iHsig : exec (within_sig (Physaddr a) 4) sf = Some (false, sf).
  Hypothesis iHh : exec (within_htif_readable (Physaddr a) 4) sf = Some (false, sf).
  Hypothesis iHbytes : forall j : nat, (N.of_nat j < 4)%N -> sf.(mem) !! (pa_add a j) = Some (nth_byte w j).
  Hypothesis iHpriv : register_lookup cur_privilege sf.(sregs) = Supervisor.
  Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.

  Lemma exec_fetch_bytes_4_walk : exec (fetch_bytes a a 4) s = Some (@FetchBytes_Success 4 w, sf).
  Proof using All.
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc a a) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr a) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr a, PBMT_PMA, init_ext_ptw)), sf))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR.
        rewrite (exec_translateAddr_walk region_pte menvcfg0 tlbvec s Hcp HSXL Hsatp Htlb Hvec
                   pHA pHord pHrange pHR pHmatch pHalign pHpte pHc pHsig pHh pHbytes Hmenv HPBMTE).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr a, PBMT_PMA) sf)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr a) 4 false false false)) sf
           = Some (inr (Ok w), sf))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_4_S PBMT_PMA a region w sf
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHbytes iHpriv).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  Lemma exec_fetch_RVC_4_walk : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), sf).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (a, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc a a) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            change (neq_vec (access_vec_dec a 0) ('b"0")) with false. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            change (neq_vec (access_vec_dec a 1) ('b"0")) with false. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            change (is_aligned_vaddr (Virtaddr a) 4) with true. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4_walk).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchWalk.

End PW.
