From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpSmode WpSmode2.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpKernelvec.v — WP for the first instruction of kernelvec (the xv6 S-mode
   trap vector at 0x800053e0).  Builds, with no admits:
   - Sv39 identity address translation via a valid identity TLB entry
     (exec_translateAddr_kv), the page-table-aware analogue of the Bare
     translation used for boot;
   - a 4-aligned 4-byte instruction fetch in Supervisor mode (exec_fetch_RVC_4_S);
   - the iris-level WP wp_smode_addi4 / capstone wp_kernelvec_caddi16sp for the
     c.addi16sp sp,imm entry instruction, under the kernelvec entry precondition
     (S-mode, interrupts disabled / SIE=0, a valid-looking Sv39 page table in satp). *)

Section KVT.
  Context `{!riscvGS Σ}.

  (* Identity-map PTE for the kernel page (VPN 0x80005 = the kernelvec page):
     PPN = 0x80005 (identity), flags D A _ _ X W R V = 0xCF (V R W X A D set, U=0). *)
  Definition kv_pte : mword 64 := mword_of_int (Z.lor (Z.shiftl 0x80005 10) 0xCF).

  (* update_PTE_Bits returns None for an InstructionFetch when A is already set:
     no dirty/accessed-bit write is needed, so the TLB hit does no memory write. *)
  Lemma update_PTE_Bits_kv_none :
    update_PTE_Bits (pte_size := 64) kv_pte (InstructionFetch tt) = None.
  Proof. vm_compute. reflexivity. Qed.


  Lemma exec_check_PTE_permission_kv (mxr do_sum : bool) s :
    exec (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
            (subrange_vec_dec kv_pte 7 0) (ext_bits_of_PTE kv_pte) tt) s
      = Some (PTE_Check_Success tt, s).
  Proof.
    destruct mxr, do_sum; vm_compute; reflexivity.
  Qed.

  (* The kernelvec page: identity-mapped TLB entry at hash index 5.
     vpn = ppn = 0x80005 (4KB leaf, levelMask = 0), global, pte = kv_pte. *)
  Definition kv_vpn : mword 27 := mword_of_int 0x80005.

  Definition kv_tlb_entry : TLB_Entry := {|
    TLB_Entry_asid     := mword_of_int 0;
    TLB_Entry_global   := true;
    TLB_Entry_vpn      := mword_of_int 0x80005;
    TLB_Entry_levelMask := mword_of_int 0;
    TLB_Entry_ppn      := mword_of_int 0x80005;
    TLB_Entry_pte      := kv_pte;
    TLB_Entry_pteAddr  := Physaddr (mword_of_int 0);
  |}.

  (* translate_TLB_hit is pure for our entry: check_PTE -> Success, update -> Ok None
     (A already set), so no memory write and no register read. *)
  Lemma exec_translate_TLB_hit_kv (mxr do_sum : bool) (asid : mword 16) s :
    exec (translate_TLB_hit 39 asid kv_vpn (InstructionFetch tt) Supervisor mxr do_sum
            tt 5 kv_tlb_entry) s
      = Some (Ok (mword_of_int 0x80005 : mword 44, PBMT_PMA, tt), s).
  Proof.
    destruct mxr, do_sum; vm_compute; reflexivity.
  Qed.

  (* lookup_TLB hits our entry at index 5 (tlb_hash 39 kv_vpn = 5; global ⇒ asid ignored). *)
  Lemma exec_lookup_TLB_kv (asid : mword 16) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = Some kv_tlb_entry ->
    exec (lookup_TLB 39 asid kv_vpn) s = Some (Some (5, kv_tlb_entry), s).
  Proof.
    intros Htlb Hvec.
    unfold lookup_TLB.
    replace (tlb_hash (__id 39) kv_vpn) with 5 by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec.
    replace (match_TLB_Entry kv_tlb_entry asid (sign_extend' (57 - 12) kv_vpn)) with true
      by (vm_compute; reflexivity).
    apply exec_returnm.
  Qed.

  (* translate: lookup hit → translate_TLB_hit. base_ppn unused on hit path. *)
  Lemma exec_translate_kv (mxr do_sum : bool) (asid : mword 16)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = Some kv_tlb_entry ->
    exec (translate 39 asid base_ppn kv_vpn (InstructionFetch tt) Supervisor mxr do_sum tt) s
      = Some (Ok (mword_of_int 0x80005 : mword 44, PBMT_PMA, tt), s).
  Proof.
    intros Htlb Hvec.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_kv asid tlbvec s Htlb Hvec)).
    cbn match.
    apply exec_translate_TLB_hit_kv.
  Qed.

  Lemma exec_translationMode_S_sv39 (satp0 : mword 64) s :
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    exec (translationMode Supervisor) s = Some (Sv39, s).
  Proof.
    intros HSXL Hsatp Hmode.
    unfold translationMode.
    replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_architecture_Supervisor s HSXL)).
    cbn match.
    change (xlen >=? 64) with true.
    match goal with |- exec (Defs.bind ?ARM _) s = _ =>
      assert (HARM : exec ARM s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s)) end.
    { assert (Hae : exec (Defs.assert_exp' true "sys/vmem.sail:254.25-254.26") s
                    = Some (eq_refl, s)).
      { unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ HARM).
    rewrite Hmode.
    replace (satpMode_of_bits RV64 ('b"1000" : mword 4)) with (Some Sv39)
      by (vm_compute; reflexivity).
    cbn match. apply exec_returnm.
  Qed.

  (* Full Sv39 translation of the kernelvec first-instr vaddr 0x800053e0 via the
     identity TLB entry. effPriv=Supervisor, mode=Sv39, canonical address ⇒ TLB hit. *)
  Lemma exec_translateAddr_kv (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec 5 = Some kv_tlb_entry ->
    exec (translateAddr (Virtaddr (mword_of_int 0x800053e0)) (InstructionFetch tt)) s
      = Some (Ok (Physaddr (mword_of_int 0x800053e0), PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hcp HSXL Hsatp Hmode Htlb Hvec.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    (* else branch: satp_mode_width_forwards Sv39 = 39 *)
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
    (* get_satp 39 reads satp; value discarded downstream (global TLB entry) *)
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
    (* assert_exp' (sv_width=32 || xlen=64) *)
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    (* canonical address: neq_vec check is false *)
    replace (neq_vec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e0 : mword 64)))
               (sign_extend' 64
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr (mword_of_int 0x800053e0 : mword 64)))
                     (Z.sub 39 1) 0))) with false by (vm_compute; reflexivity).
    cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    (* vpn argument equals kv_vpn *)
    match goal with |- context[translate 39 ?asid ?bppn ?vpn _ _ _ _ _] =>
      replace vpn with kv_vpn by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translate_kv _ _ _ _ _ s Htlb Hvec)).
    cbn match.
    rewrite execR_returnR. cbn match.
    f_equal.
  Qed.

  (* ---- 4-byte (4-aligned) instruction fetch in Supervisor mode with Sv39 ---- *)

  Lemma exec_checked_mem_read_ram_4_S (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : bv 32) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
    is_aligned_paddr (Physaddr addr) 4 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
    exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (checked_mem_read (InstructionFetch tt) pbmt Supervisor (Physaddr addr) 4 false false false false)
         s = Some (Ok (w, default_meta), s).
  Proof.
    intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes.
    unfold checked_mem_read.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
    2:{ unfold phys_access_check.
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_pmpCheck_supervisor_grant addr 4 s HA Hord Hrange HX)).
        cbn match.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram addr pbmt region s Hmatch Halign Hexec)).
        cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (within_mmio_readable (Physaddr addr) 4) s = Some (false, s))).
    2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
        rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
    2:{ unfold read_kind_of_flags. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hbytes)).
    apply exec_returnM.
  Qed.

  Lemma exec_mem_read_fetch_4_S (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : bv 32) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
    is_aligned_paddr (Physaddr addr) 4 = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
    exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
    (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false)
         s = Some (Ok w, s).
  Proof.
    intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hpriv.
    unfold mem_read.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
    rewrite Hpriv.
    unfold mem_read_priv.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
    2:{ unfold mem_read_priv_meta. cbn [orb andb].
        rewrite (exec_bind_Some _ _ _ _ _
                  (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
        2:{ cbn match. apply exec_checked_mem_read_ram_4_S with (region := region); assumption. }
        cbn match. unfold mem_read_callback. apply exec_returnM. }
    cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
  Qed.

Section FetchRVC4_S.
  Context (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
          (region : PMA_Region) (w : mword 32) (s : mstate).
  Let pc : mword 64 := mword_of_int 0x800053e0.
  Let addr : mword 64 := mword_of_int 0x800053e0.
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HpcPC : register_lookup PC s.(sregs) = pc.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Htlb : register_lookup tlb s.(sregs) = tlbvec.
  Hypothesis Hvec : vec_access_dec tlbvec 5 = Some kv_tlb_entry.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 4)) = PMP_Match.
  Hypothesis HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 4 = true.
  Hypothesis Hexec : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hh : exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s).
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j).
  Hypothesis HisRVC : isRVC (subrange_vec_dec w 15 0) = true.

  Lemma exec_fetch_bytes_4_S : exec (fetch_bytes pc pc 4) s = Some (@FetchBytes_Success 4 w, s).
  Proof using All.
    unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr pc) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr addr, PBMT_PMA, init_ext_ptw)), s))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR.
        rewrite (exec_translateAddr_kv satp0 tlbvec s Hcp HSXL Hsatp Hmode Htlb Hvec).
        cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr addr, PBMT_PMA) s)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr addr) 4 false false false)) s
           = Some (inr (Ok w), s))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_4_S PBMT_PMA addr region w s
                   HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hbytes Hcp).
        cbn match. reflexivity. }
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.

  Lemma exec_fetch_RVC_4_S : exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s).
  Proof using All.
    assert (HrdPC : exec (Defs.read_reg PC) s = Some (pc, s)).
    { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
    unfold fetch.
    rewrite exec_catch_early_return.
    change (get_config_rvfi tt) with false. cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    change (ext_fetch_check_pc pc pc) with (@None unit). cbv iota beta.
    rewrite (execR_bind_Some _ _ _ false s).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        unfold or_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            change (neq_vec (access_vec_dec pc 0) ('b"0")) with false. apply execR_returnR_fwd. }
        cbv iota beta.
        unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ false s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            change (neq_vec (access_vec_dec pc 1) ('b"0")) with false. apply execR_returnR_fwd. }
        cbv iota beta. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ true s).
    2:{ unfold and_boolM.
        rewrite (execR_bind_Some _ _ _ true s).
        2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
            change (is_aligned_vaddr (Virtaddr pc) 4) with true. apply execR_returnR_fwd. }
        cbv iota beta.
        rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
    rewrite (execR_liftR_seq _ _ _ _ _ exec_fetch_bytes_4_S).
    cbv iota beta. rewrite HisRVC. cbv iota beta.
    rewrite execR_returnR_fwd. cbn match. reflexivity.
  Qed.
End FetchRVC4_S.

  (* iris-level bridge: from owned PC/CSR/tlb/memory points-to to the pure fetch
     fact, for the concrete 4-aligned kernelvec address 0x800053e0. *)
  Lemma fetch_from_pts_minstret_RVC4_S
      (satp0 mstatus0 : mword 64) (w : mword 32) (region : PMA_Region)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (b : bool) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (s : mstate) {dq : dfrac} :
    matching_pma_region pmar0 (Physaddr (mword_of_int 0x800053e0)) 4 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    vec_access_dec tlbvec 5 = Some kv_tlb_entry ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e0 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e0)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    reg_interp s.(sregs) -∗ gen_heap_interp s.(mem) -∗
    PC ↦ᵣ (mword_of_int 0x800053e0 : mword 64) -∗ cur_privilege ↦ᵣ Supervisor -∗
    (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗
    pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e0) j) ↦ₘ{dq} nth_byte w j) -∗
    ⌜ exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_RVC (subrange_vec_dec w 15 0), set_reg s (R_bool minstret_increment) b) ⌝.
  Proof.
    iIntros (Hmatch0 Hexec HSXL0 Hsmode Hvec HA0 Hord0 Hrange0 HX0 Halign HisRVC)
            "Hreg Hmem Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpaddr Hpma Hhtif Hbytes".
    iDestruct (reg_valid with "Hreg Hpc")    as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")  as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms")    as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")  as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb")   as %Ltlb.
    iDestruct (reg_valid with "Hreg Hpmpc")  as %Lpmpc.
    iDestruct (reg_valid with "Hreg Hpmpaddr") as %Lpmpaddr.
    iDestruct (reg_valid with "Hreg Hpma")   as %Lpma.
    iDestruct (reg_valid with "Hreg Hhtif")  as %Lhtif.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               s.(mem) !! (pa_add (mword_of_int 0x800053e0) j) = Some (nth_byte w j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 4)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram (mword_of_int 0x800053e0)⌝)%I as %Hram.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0. iPureIntro. exact Hr0. }
    iPureIntro.
    unfold addr_is_ram in Hram. destruct Hram as [Hnc Hns].
    set (t := set_reg s (R_bool minstret_increment) b).
    assert (Ltpc : register_lookup PC t.(sregs) = mword_of_int 0x800053e0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpc | vm_compute; reflexivity]. }
    assert (Ltpriv : register_lookup cur_privilege t.(sregs) = Supervisor).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpriv | vm_compute; reflexivity]. }
    assert (Ltms : register_lookup mstatus t.(sregs) = mstatus0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity]. }
    assert (Ltsatp : register_lookup satp t.(sregs) = satp0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lsatp | vm_compute; reflexivity]. }
    assert (Lttlb : register_lookup tlb t.(sregs) = tlbvec).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Ltlb | vm_compute; reflexivity]. }
    assert (Ltpmpc : register_lookup pmpcfg_n t.(sregs) = pmpcfg0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpc | vm_compute; reflexivity]. }
    assert (Ltpmpaddr : register_lookup pmpaddr_n t.(sregs) = pmpaddr00).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpmpaddr | vm_compute; reflexivity]. }
    assert (Ltpma : register_lookup pma_regions t.(sregs) = pmar0).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lpma | vm_compute; reflexivity]. }
    assert (Lthtif : register_lookup htif_tohost_base t.(sregs) = None).
    { unfold t, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lhtif | vm_compute; reflexivity]. }
    assert (Ltmem : forall j : nat, (N.of_nat j < 4)%N ->
              t.(mem) !! (pa_add (mword_of_int 0x800053e0) j) = Some (nth_byte w j))
      by (unfold t, set_reg; cbn [mem]; exact Hbytesf).
    assert (HSXL : _get_Mstatus_SXL (register_lookup mstatus t.(sregs)) = 'b"10")
      by (rewrite Ltms; exact HSXL0).
    assert (HA : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n t.(sregs)) 0)) = TOR)
      by (rewrite Ltpmpc; exact HA0).
    assert (Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n t.(sregs)) 0) = false)
      by (rewrite Ltpmpaddr; exact Hord0).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n t.(sregs)) 0)) 4)
              (uint (mword_of_int 0x800053e0 : mword 64)) (uint (to_bits 64 4)) = PMP_Match)
      by (rewrite Ltpmpaddr; exact Hrange0).
    assert (HX : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n t.(sregs)) 0)) ('b"1") = true)
      by (rewrite Ltpmpc; exact HX0).
    assert (Hmatch : matching_pma_region (register_lookup pma_regions t.(sregs))
              (Physaddr (mword_of_int 0x800053e0)) 4 = Some region)
      by (rewrite Ltpma; exact Hmatch0).
    exact (exec_fetch_RVC_4_S satp0 tlbvec region w t Ltpriv Ltpc HSXL Ltsatp Hsmode Lttlb Hvec
             HA Hord Hrange HX Hmatch Halign Hexec
             (within_clint_false (mword_of_int 0x800053e0) 4 t Hnc ltac:(lia))
             (within_sig_false  (mword_of_int 0x800053e0) 4 t Hns ltac:(lia))
             (within_htif_false (mword_of_int 0x800053e0) 4 t Lthtif)
             Ltmem HisRVC).
  Qed.

  (* Generic S-mode WP for an RVC ADDI self-write (rs1=rd) at the 4-aligned
     kernelvec entry 0x800053e0 (e.g. c.addi16sp sp,-256), fetched as a 4-byte
     word via Sv39 identity translation.  w : mword 32 are the 4 fetched bytes;
     the decoded instruction is its low 16 bits. *)
  Lemma wp_smode_addi4 (w : mword 32)
      (cinstr : instruction) (rd : mword 5) (imm12 : mword 12)
      (m : gmap register_bitvector_64 (mword 64)) (vd misa0 mdv0 mstatus0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    uint rd <> 0 ->
    m !! gpr_of_Z (uint rd) = Some vd ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    vec_access_dec tlbvec 5 = Some kv_tlb_entry ->
    pma_allows_all pmar0 ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e0 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e0)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (cinstr, s0)) ->
    (forall s0, exec (execute cinstr) s0
       = Some (ExecuteAs (ITYPE (imm12, Regidx rd, Regidx rd, ADDI)), s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ (mword_of_int 0x800053e0 : mword 64) -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e0) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int (mword_of_int 0x800053e0 : mword 64) 2 -∗
        gpr_file (<[gpr_of_Z (uint rd) := regval_into_reg (add_vec vd (sign_extend' 64 imm12))]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int (mword_of_int 0x800053e0 : mword 64) 2 -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e0) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hrd Hmd HsatpM HSXL Hvec Hpmaall HA0 Hord0 Hrange0 HX0 Halignf
             HisRVC HmisaC HmisaS Hdec Hcexec1 Hb1 Hmie_mdl HSIE Help)
      "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes Hcont".
    destruct (Hpmaall (mword_of_int 0x800053e0) 4) as (region_f & Hmatchf & Hexecf & _ & _).
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) with "Hinv"); first done.
    iIntros (s ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct (reg_valid with "Hreg Hpc")      as %Lpc.
    iDestruct (reg_valid with "Hreg Hpriv")    as %Lpriv.
    iDestruct (reg_valid with "Hreg Hhs")      as %Lhs.
    iDestruct (reg_valid with "Hreg Hmdl")     as %Lmdl.
    iDestruct (reg_valid with "Hreg Hms")      as %Lms.
    iDestruct (reg_valid with "Hreg Hsatp")    as %Lsatp.
    iDestruct (reg_valid with "Hreg Htlb")     as %Ltlb.
    iDestruct (reg_valid with "Hreg Hmie")     as %Lmie.
    iDestruct (reg_valid with "Hreg Help'")    as %Lelp.
    iDestruct (reg_valid with "Hreg Hmcinh")   as %Lmc.
    iDestruct (reg_valid with "Hreg Hmcfg")    as %Lmcfg.
    iDestruct (reg_valid with "Hreg Hmisa'")   as %Lmisa.
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc1 Hfb]".
    iDestruct (reg_valid with "Hreg Hrdc1") as %Lrd.
    iDestruct ("Hfb" with "Hrdc1") as "Hfile".
    assert (Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b1, s)).
    { rewrite Hb1. apply (exec_should_inc_S mc mcfg Supervisor s Lmc Lmcfg). }
    iDestruct (fetch_from_pts_minstret_RVC4_S satp0 mstatus0 w region_f pmpcfg0 pmpaddr00 pmar0 b1 tlbvec s
                 Hmatchf Hexecf HSXL HsatpM Hvec HA0 Hord0 Hrange0 HX0 Halignf HisRVC
                 with "Hreg Hmem Hpc Hpriv Hms Hsatp Htlb Hpmpc Hpmpaddr Hpma Hhtif Hibytes") as %Hfetch_at.
    assert (Hdisp : exec (dispatchInterrupt Supervisor) (sAl s b1) = Some (None, sAl s b1)).
    { apply exec_dispatchInterrupt_none_S.
      apply (exec_getPendingSet_supervisor_none (sAl s b1) mie_v mdv0 mstatus0).
      - rewrite (exec_currentlyEnabled_S (sAl s b1)).
        replace (register_lookup misa (sAl s b1).(sregs)) with misa0.
        2:{ unfold sAl, set_reg; cbn [sregs].
            rewrite irrelevant_register_set; [symmetry; exact Lmisa | vm_compute; reflexivity]. }
        rewrite HmisaS. reflexivity.
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmie | vm_compute; reflexivity].
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lmdl | vm_compute; reflexivity].
      - unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [exact Lms | vm_compute; reflexivity].
      - exact Hmie_mdl.
      - exact HSIE. }
    assert (Hcexec2' : exec (execute (ITYPE (imm12, Regidx rd, Regidx rd, ADDI))) (s_pcl s (mword_of_int 0x800053e0) b1)
                       = Some (RETIRE_SUCCESS, set_reg (s_pcl s (mword_of_int 0x800053e0) b1)
                                 (R_bitvector_64 (gpr_of_Z (uint rd)))
                                 (regval_into_reg (add_vec vd (sign_extend' 64 imm12))))).
    { rewrite (exec_execute_ITYPE_ADDI_gpr rd rd imm12 (s_pcl s (mword_of_int 0x800053e0) b1)).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite (gpr_addi_val_self_file s (mword_of_int 0x800053e0) b1 rd imm12 vd Hrd Lrd). reflexivity. }
    iModIntro.
    iExists (WpRvc.sFcg s (mword_of_int 0x800053e0) b1 rd (add_vec vd (sign_extend' 64 imm12)) (register_lookup minstret s.(sregs))). iSplitR.
    { iPureIntro.
      rewrite <- (WpRvc.sFg_eq s (mword_of_int 0x800053e0) b1 rd (add_vec vd (sign_extend' 64 imm12)) (register_lookup minstret s.(sregs)) Lpc eq_refl).
      apply (forward_exec_rvc_gpr_write_gen Supervisor s (mword_of_int 0x800053e0) b1 (subrange_vec_dec w 15 0) cinstr
               (ITYPE (imm12, Regidx rd, Regidx rd, ADDI)) rd (add_vec vd (sign_extend' 64 imm12))
               Hfetch_at Hsi_s Hdec (Hcexec1 (s_pcl s (mword_of_int 0x800053e0) b1)) Hcexec2' Lpc Lpriv Hdisp Lhs).
      - rewrite Lmisa. exact HmisaS.
      - rewrite Lelp. exact Help.
      - rewrite Lmisa. exact HmisaC. }
    iNext.
    iDestruct "Hbody" as (mst mi) "[Hmst Hmi]".
    iMod (reg_update _ (R_bool minstret_increment) _ b1 with "Hreg Hmi") as "[Hreg Hmi]".
    iMod (reg_update _ nextPC _ (add_vec_int (mword_of_int 0x800053e0 : mword 64) 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfile") as "[Hrdc Hfins]".
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (add_vec vd (sign_extend' 64 imm12))) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iMod (reg_update _ PC _ (add_vec_int (mword_of_int 0x800053e0 : mword 64) 2) with "Hreg Hpc") as "[Hreg Hpc]".
    iDestruct ("Hfins" $! (regval_into_reg (add_vec vd (sign_extend' 64 imm12))) with "Hrdc") as "Hfile".
    unfold WpRvc.sFcg, WpRvc.base_upd_g. destruct b1.
    - iMod (reg_update _ minstret _ (add_vec_int (register_lookup minstret s.(sregs)) 1) with "Hreg Hmst") as "[Hreg Hmst]".
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists (add_vec_int (register_lookup minstret s.(sregs)) 1), true. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
    - iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
      iApply ("Hcont" with "Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes").
  Qed.

  (* CAPSTONE: WP for kernelvec's first instruction, the c.addi16sp sp,imm at
     0x800053e0 (kernel idx 7828, enc 0x7111).  Specialises wp_smode_addi4 to
     C_ADDI16SP, discharging the execute obligation via exec_execute_C_ADDI16SP;
     the decode of the low-16 word is the single instruction-identity hypothesis
     (the standard decode-as-hypothesis pattern of this development). *)
  Lemma wp_kernelvec_caddi16sp (w : mword 32) (imm6 : mword 6)
      (m : gmap register_bitvector_64 (mword 64)) (vsp misa0 mdv0 mstatus0 satp0 mie_v : mword 64)
      (b1 : bool) (npc0 mst0 : mword 64) (mc : mword 32) (mcfg : mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (pmar0 : list PMA_Region) (mi0 : bool) (elp0 : mword 1)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) E {dq : dfrac} (Phi : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    m !! gpr_of_Z 2 = Some vsp ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    vec_access_dec tlbvec 5 = Some kv_tlb_entry ->
    pma_allows_all pmar0 ->
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec pmpaddr00 0)) 4)
      (uint (mword_of_int 0x800053e0 : mword 64)) (uint (to_bits 64 4)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    is_aligned_paddr (Physaddr (mword_of_int 0x800053e0)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = true ->
    eq_vec (_get_Misa_C misa0) ('b"1") = true ->
    eq_vec (_get_Misa_S misa0) ('b"1") = true ->
    (forall s0, eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
       exec (ext_decode_compressed (subrange_vec_dec w 15 0)) s0 = Some (C_ADDI16SP imm6, s0)) ->
    b1 = andb (eq_vec (_get_Counterin_IR mc) ('b"0"))
              (eq_vec (counter_priv_filter_bit mcfg Supervisor) ('b"0")) ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    minstret_inv -∗
    PC ↦ᵣ (mword_of_int 0x800053e0 : mword 64) -∗ gpr_file m -∗ misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ npc0 -∗
    cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
    tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗
    elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
    ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e0) j) ↦ₘ{dq} nth_byte w j) -∗
    ▷ ( PC ↦ᵣ add_vec_int (mword_of_int 0x800053e0 : mword 64) 2 -∗
        gpr_file (<[gpr_of_Z 2 := regval_into_reg (add_vec vsp (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
        misa ↦ᵣ misa0 -∗ nextPC ↦ᵣ add_vec_int (mword_of_int 0x800053e0 : mword 64) 2 -∗
        cur_privilege ↦ᵣ Supervisor -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
        (R_bitvector_64 mideleg) ↦ᵣ mdv0 -∗ (R_bitvector_64 mstatus) ↦ᵣ mstatus0 -∗ satp ↦ᵣ satp0 -∗
        tlb ↦ᵣ tlbvec -∗ mie ↦ᵣ mie_v -∗
        elp ↦ᵣ elp0 -∗ mcountinhibit ↦ᵣ mc -∗ minstretcfg ↦ᵣ mcfg -∗
        pmpcfg_n ↦ᵣ pmpcfg0 -∗ pmpaddr_n ↦ᵣ pmpaddr00 -∗ pma_regions ↦ᵣ pmar0 -∗ htif_tohost_base ↦ᵣ None -∗
        ([∗ list] j ∈ seq 0 4, (pa_add (mword_of_int 0x800053e0) j) ↦ₘ{dq} nth_byte w j) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    iIntros (HN Hsp HsatpM HSXL Hvec Hpmaall HA0 Hord0 Hrange0 HX0 Halignf
             HisRVC HmisaC HmisaS Hdec Hb1 Hmie_mdl HSIE Help)
      "#Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes Hcont".
    iApply (wp_smode_addi4 w (C_ADDI16SP imm6) (zero_extend' 5 ('b"10")) (caddi16sp_imm imm6)
              m vsp misa0 mdv0 mstatus0 satp0 mie_v b1 npc0 mc mcfg pmpcfg0 pmpaddr00 pmar0 elp0 tlbvec E Phi
              HN
              ltac:(vm_compute; discriminate) Hsp HsatpM HSXL Hvec Hpmaall HA0 Hord0 Hrange0 HX0 Halignf
              HisRVC HmisaC HmisaS Hdec (fun s0 => exec_execute_C_ADDI16SP imm6 s0)
              Hb1 Hmie_mdl HSIE Help
             with "Hinv Hpc Hfile Hmisa' Hnpc Hpriv Hhs Hmdl Hms Hsatp Htlb Hmie Help' Hmcinh Hmcfg Hpmpc Hpmpaddr Hpma Hhtif Hibytes [Hcont]").
    iApply "Hcont".
  Qed.

End KVT.
