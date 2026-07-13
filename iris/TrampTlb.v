(* TrampTlb.v -- TLB lookup / translate / translateAddr through the 4K
   trampoline-style mapping (continuation of TrampPt.v), plus the SFENCE.VMA
   flush and the S-mode csrw satp execute reductions. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpGprCsrwCommon WpGprCsrwB.
Require Import WpLeafCommon WpGpr WpLoad WpSmodeGpr.
Require Import SmodeCore.
Require Import TrampPt.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.


(* The 4K TLB lookup/get/match lemmas and the access-generic three-way
   translate ([exec_translate_tramp] / [exec_translateAddr_tramp]) MOVED to
   Pt4kWalk.v (visible here via TrampPts re-export). *)


(* ===================================================================== *)
(* 8. flush_TLB None None clears every slot; the SFENCE.VMA x0,x0         *)
(*    execute reduction (S-mode, TVM=0).                                  *)
(* ===================================================================== *)

Lemma exec_flush_TLB_all (s : mstate) :
  exists tlbvec' : vec (option TLB_Entry) (2 ^ 6),
    exec (flush_TLB None None) s = Some (tt, set_reg s tlb tlbvec') /\
    (forall i, 0 <= i < 64 -> vec_access_dec tlbvec' i = None).
Proof.
  unfold flush_TLB.
  cbv zeta iota.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
  match goal with |- context[Defs.foreach_ZM_up ?f ?t ?st ?v ?b] =>
    change t with 63; set (B := b) end.
  unfold Defs.foreach_ZM_up.
  (* the loop invariant: after running from [from] with enough fuel, slots
     [from..63] are cleared and lower slots keep the START state's values. *)
  assert (Hloop : forall (n : nat) (from : Z) (s0 : mstate),
    0 <= from -> from + Z.of_nat n = 64 ->
    exists tv : vec (option TLB_Entry) (2 ^ 6),
      exec (Defs.foreach_ZM_up' from 63 1 n tt B) s0 = Some (tt, set_reg s0 tlb tv) /\
      (forall i, 0 <= i < 64 ->
         vec_access_dec tv i = (if from <=? i then None
                                else vec_access_dec (register_lookup tlb s0.(sregs)) i))).
  { induction n as [| n IHn]; intros from s0 Hfrom Hcover.
    - (* fuel exhausted exactly at from = 64 *)
      exists (register_lookup tlb s0.(sregs)).
      split.
      + cbn [Defs.foreach_ZM_up'].
        destruct (from <=? 63); rewrite set_reg_tlb_id; apply exec_returnm.
      + intros i Hi.
        replace (from <=? i) with false by (symmetry; apply Z.leb_gt; lia).
        reflexivity.
    - assert (Hle : from <= 63) by lia.
      rewrite (Defs.unroll_foreach_ZM_up' _ _ from 63 1 n tt B Hle).
      destruct (vec_access_dec (register_lookup tlb s0.(sregs)) from) as [e |] eqn:Hslot.
      + (* resident: cleared *)
        assert (HB : exec (B from tt) s0
                     = Some (tt, set_reg s0 tlb
                                   (vec_update_dec (register_lookup tlb s0.(sregs)) from None))).
        { unfold B. cbv beta.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s0)).
          rewrite Hslot.
          change (flush_TLB_Entry e None None) with true.
          cbv iota.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s0)).
          rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg tlb _ s0)).
          apply exec_returnM. }
        rewrite (exec_bind_Some _ _ _ _ _ HB).
        destruct (IHn (from + 1) (set_reg s0 tlb
                    (vec_update_dec (register_lookup tlb s0.(sregs)) from None))
                    ltac:(lia) ltac:(lia)) as (tv & Hex & Hprop).
        exists tv. split.
        * rewrite Hex. rewrite set_reg_tlb_overwrite. reflexivity.
        * intros i Hi.
          rewrite (Hprop i Hi).
          unfold set_reg; cbn [sregs]. rewrite register_lookup_set.
          rewrite (vec64_access_update _ from i None ltac:(lia)).
          destruct (Z.leb_spec from i) as [Hfi | Hfi];
            destruct (Z.leb_spec (from + 1) i) as [Hf1i | Hf1i];
            destruct (Z.eqb_spec i from) as [-> | Hne];
            try reflexivity; try lia.
      + (* empty: skip *)
        assert (HB : exec (B from tt) s0 = Some (tt, s0)).
        { unfold B. cbv beta.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s0)).
          rewrite Hslot. apply exec_returnM. }
        rewrite (exec_bind_Some _ _ _ _ _ HB).
        destruct (IHn (from + 1) s0 ltac:(lia) ltac:(lia)) as (tv & Hex & Hprop).
        exists tv. split; [exact Hex |].
        intros i Hi.
        rewrite (Hprop i Hi).
        destruct (Z.leb_spec from i) as [Hfi | Hfi];
          destruct (Z.leb_spec (from + 1) i) as [Hf1i | Hf1i];
          try reflexivity; try lia.
        (* i = from: the slot is already None *)
        assert (i = from) by lia. subst i. rewrite Hslot. reflexivity. }
  destruct (Hloop (S (Z.abs_nat (0 - 63))) 0 s ltac:(lia)
              ltac:(vm_compute (Z.of_nat _); reflexivity)) as (tv & Hex & Hprop).
  exists tv.
  split.
  - match goal with |- context[Defs.bind (Defs.bind0 ?L ?r) ?k] =>
      assert (HLr : exec (Defs.bind0 L r) s = Some (tv, set_reg s tlb tv)) end.
    { rewrite (exec_bind0_Some _ _ _ _ _ Hex).
      rewrite (exec_read_reg tlb _).
      unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ HLr).
    cbv beta. apply exec_returnM.
  - intros i Hi. rewrite (Hprop i Hi).
    replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
Qed.

(* the SFENCE.VMA x0,x0 execute reduction: S-mode, TVM=0 => full flush. *)
Lemma exec_execute_SFENCE_VMA_S (s : mstate) :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  exists tlbvec' : vec (option TLB_Entry) (2 ^ 6),
    exec (execute (SFENCE_VMA (zreg, zreg))) s
      = Some (RETIRE_SUCCESS, set_reg s tlb tlbvec') /\
    (forall i, 0 <= i < 64 -> vec_access_dec tlbvec' i = None).
Proof.
  intros Hpriv HTVM.
  destruct (exec_flush_TLB_all s) as (tv & Hfl & Hprop).
  exists tv. split; [| exact Hprop].
  change (execute (SFENCE_VMA (zreg, zreg))) with (execute_SFENCE_VMA zreg zreg).
  unfold execute_SFENCE_VMA.
  replace (generic_neq zreg zreg) with false by (vm_compute; reflexivity).
  cbv iota.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv. cbv iota beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  cbv zeta.
  rewrite HTVM. cbv iota.
  match goal with |- context[flush_TLB ?a ?b] =>
    change a with (@None (mword 16)) end.
  rewrite (exec_bind0_Some _ _ _ _ _ Hfl).
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* 9. csrw satp,rs1 in S-MODE (mstatus.TVM = 0).                          *)
(* ===================================================================== *)

Lemma exec_check_CSR_priv_satp_S s :
  exec (check_CSR_priv csr_satp Supervisor) s = Some (true, s).
Proof. vm_compute. reflexivity. Qed.

Lemma exec_is_CSR_accessible_satp_S s :
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  exec (is_CSR_accessible csr_satp Supervisor CSRWrite) s = Some (true, s).
Proof.
  intro HTVM.
  unfold is_CSR_accessible.
  skip_csr_false_clauses.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity) end. cbn match.
  unfold satp_accessible. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
  pose proof (mword1_zero_of_ne_one _ HTVM) as H0.
  rewrite H0.
  replace (eq_vec ('b"0" : mword 1) ('b"0")) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_check_CSR_result_csrw_satp_S s :
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  exec (check_CSR_result csr_satp Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s).
Proof.
  intro HTVM.
  unfold check_CSR_result.
  match goal with |- context[Defs.bind ?m ?f] =>
    assert (Hcc : exec m s = Some (true, s)) end.
  { unfold check_CSR.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_check_CSR_priv_satp_S s)). cbn match.
    match goal with |- context[and_boolM ?A ?B] =>
      assert (HB : exec A s = Some (true, s)) end.
    { vm_compute (check_CSR_access _ _). apply exec_returnM. }
    rewrite (exec_and_boolM_Some _ _ _ _ _ HB). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_is_CSR_accessible_satp_S s HTVM)). cbn match.
    vm_compute (stateen_allows_CSR_access csr_satp Supervisor CSRWrite).
    apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ Hcc). cbn match. apply exec_returnm.
Qed.

(* the S-mode doCSR / execute_CSRReg for a csrw (privilege-generic copies of
   WpGprCsrwCommon's Machine-pinned versions). *)
Lemma exec_doCSR_csrw_S (csr : mword 12) (v : mword 64) (s s' : mstate) (cfinal : mword 64) :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (check_CSR_result csr Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s) ->
  ext_check_CSR csr Supervisor CSRWrite = true ->
  eq_vec csr (Ox"344") = false ->
  eq_vec csr (Ox"144") = false ->
  exec (write_CSR csr v) s = Some (Ok cfinal, s') ->
  exec (csr_id_write_callback csr cfinal) s' = Some (tt, s') ->
  exec (doCSR csr v zreg CSRRW CSRWrite) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Hpriv Hchk Hext H344 H144 Hwr Hcb.
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hpriv.
  rewrite Hext.
  change (Riscv.rv64d.not true) with false. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (zeros' 64) s)).
  rewrite H344, H144. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (zeros' 64) s)).
  replace (generic_eq CSRWrite CSRRead) with false by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ Hwr). cbn match.
  match goal with |- context[Defs.bind0 (Defs.bind0 ?a ?b) ?c] =>
    assert (Hab : exec (Defs.bind0 a b) s' = Some (tt, s')) end.
  { rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_zreg (zeros' 64) s')).
    exact Hcb. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hab).
  apply exec_returnM.
Qed.

Lemma exec_execute_csrw_gpr_S (csr : mword 12) (rs1 : mword 5) (s s' : mstate) (cfinal : mword 64) :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  exec (check_CSR_result csr Supervisor CSRWrite) s = Some (CSR_Check_OK tt, s) ->
  ext_check_CSR csr Supervisor CSRWrite = true ->
  eq_vec csr (Ox"344") = false ->
  eq_vec csr (Ox"144") = false ->
  exec (write_CSR csr (if Z.eqb (uint rs1) 0 then zero_reg
                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))) s
    = Some (Ok cfinal, s') ->
  exec (csr_id_write_callback csr cfinal) s' = Some (tt, s') ->
  exec (execute_CSRReg csr (Regidx rs1) zreg CSRRW) s = Some (RETIRE_SUCCESS, s').
Proof.
  intros Hpriv Hchk Hext H344 H144 Hwr Hcb.
  unfold execute_CSRReg.
  replace (csr_access_type CSRRW (generic_eq zreg zreg) (generic_eq (Regidx rs1) zreg))
    with CSRWrite by (replace (generic_eq zreg zreg) with true by reflexivity; reflexivity).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  apply (exec_doCSR_csrw_S csr _ s s' cfinal); assumption.
Qed.

(* csrw satp,rs1 in S-mode: writes satp := legalized(rs1 value). *)
Lemma exec_execute_csrw_satp_S (rs1 : mword 5) s :
  uint rs1 <> 0 ->
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  eq_vec (_get_Mstatus_TVM (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec (execute (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW))) s
    = Some (RETIRE_SUCCESS,
            set_reg s satp
              (satp_legalized (register_lookup satp s.(sregs))
                 (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
Proof.
  intros Hrs1 Hpriv HTVM HS HSXL.
  change (execute (CSRReg (csr_satp, Regidx rs1, zreg, CSRRW)))
    with (execute_CSRReg csr_satp (Regidx rs1) zreg CSRRW).
  replace (register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    with (if Z.eqb (uint rs1) 0 then zero_reg
          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
    by (replace (Z.eqb (uint rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrs1); reflexivity).
  apply (exec_execute_csrw_gpr_S csr_satp rs1 s _
           (satp_legalized (register_lookup satp s.(sregs))
              (if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)))).
  - exact Hpriv.
  - apply exec_check_CSR_result_csrw_satp_S. exact HTVM.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply exec_write_CSR_satp; assumption.
  - apply exec_csr_id_write_callback_satp.
Qed.

(* a Sv39-mode value legalizes to itself. *)
Lemma satp_legalized_sv39 (prev v : mword 64) :
  _get_Satp64_Mode (Mk_Satp64 v) = ('b"1000" : mword 4) ->
  satp_legalized prev v = v.
Proof.
  intro Hmode. unfold satp_legalized.
  rewrite Hmode.
  vm_compute (satpMode_of_bits RV64 ('b"1000" : mword 4)).
  reflexivity.
Qed.

(* ===================================================================== *)
(* 10. Fetch compositions where the TRANSLATED page differs from the va's *)
(* page (pa != va): verbatim generalizations of SmodeCore's               *)
(* [exec_fetch_*_S_gen] with a separate [pa].                             *)
(* ===================================================================== *)

Lemma exec_fetch_F_Base_4_pa
      (va pa : mword 64) (w : mword 32) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 4 = Some region ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 4) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  exec (fetch tt) s = Some (F_Base w, s1).
Proof.
  intros HpcPC Hvalign Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv HnotRVC.
  destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (Hfb4 : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    match goal with |- context[Defs.bind (Defs.bind0 ?r ?t) ?k] =>
      assert (Hpre : execR (Defs.bind0 r t : Defs.monadR (FetchBytes_Result 4) exception _) s
                     = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1)) end.
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hpre). clear Hpre.
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    match goal with |- context[Defs.bind (Defs.liftR (mem_read ?a ?b ?c ?d ?e ?f ?g)) ?k] =>
      assert (Hmr : execR (Defs.liftR (mem_read a b c d e f g) : Defs.monadR (FetchBytes_Result 4) exception _) s1
                    = Some (inr (Ok w), s1)) end.
    { rewrite execR_liftR.
      rewrite (exec_mem_read_fetch_4_S PBMT_PMA pa region w s1
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv).
      cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmr). clear Hmr.
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  unfold fetch.
  rewrite exec_catch_early_return.
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold or_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ true s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb4).
  cbv iota beta.
  match goal with |- context[if isRVC ?h then _ else _] =>
    replace (isRVC h) with false by (symmetry; exact HnotRVC) end.
  cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

Lemma exec_fetch_RVC_4_pa
      (va pa : mword 64) (w : mword 32) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 4 = Some region ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 4) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 4) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC (subrange_vec_dec w 15 0) = true ->
  exec (fetch tt) s = Some (F_RVC (subrange_vec_dec w 15 0), s1).
Proof.
  intros HpcPC Hvalign Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv HisRVC.
  destruct (align4_low_bits va Hvalign) as [Hbit0 Hbit1].
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (Hfb4 : exec (fetch_bytes va va 4) s = Some (@FetchBytes_Success 4 w, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    match goal with |- context[Defs.bind (Defs.bind0 ?r ?t) ?k] =>
      assert (Hpre : execR (Defs.bind0 r t : Defs.monadR (FetchBytes_Result 4) exception _) s
                     = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1)) end.
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hpre). clear Hpre.
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    match goal with |- context[Defs.bind (Defs.liftR (mem_read ?a ?b ?c ?d ?e ?f ?g)) ?k] =>
      assert (Hmr : execR (Defs.liftR (mem_read a b c d e f g) : Defs.monadR (FetchBytes_Result 4) exception _) s1
                    = Some (inr (Ok w), s1)) end.
    { rewrite execR_liftR.
      rewrite (exec_mem_read_fetch_4_S PBMT_PMA pa region w s1
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv).
      cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmr). clear Hmr.
    cbv iota beta. rewrite autocast_mword_id.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  unfold fetch.
  rewrite exec_catch_early_return.
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold or_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ true s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite execR_liftR. rewrite exec_currentlyEnabled_Ziccif. cbn match. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb4).
  cbv iota beta.
  match goal with |- context[if isRVC ?h then _ else _] =>
    replace (isRVC h) with true by (symmetry; exact HisRVC) end.
  cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

Lemma exec_fetch_RVC_2_pa
      (va pa : mword 64) (h : mword 16) (s s1 : mstate) (region : PMA_Region) :
  register_lookup PC s.(sregs) = va ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 2 = Some region ->
  is_aligned_paddr (Physaddr pa) 2 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 2) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 2) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 2) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte h j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  isRVC h = true ->
  exec (fetch tt) s = Some (F_RVC h, s1).
Proof.
  intros HpcPC HmisaC Hbit0 Hbit1 Hvalign4 Htr iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv HisRVC.
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (Hfb2 : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 h, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    match goal with |- context[Defs.bind (Defs.bind0 ?r ?t) ?k] =>
      assert (Hpre : execR (Defs.bind0 r t : Defs.monadR (FetchBytes_Result 2) exception _) s
                     = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1)) end.
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hpre). clear Hpre.
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    match goal with |- context[Defs.bind (Defs.liftR (mem_read ?a ?b ?c ?d ?e ?f ?g)) ?k] =>
      assert (Hmr : execR (Defs.liftR (mem_read a b c d e f g) : Defs.monadR (FetchBytes_Result 2) exception _) s1
                    = Some (inr (Ok h), s1)) end.
    { rewrite execR_liftR.
      rewrite (exec_mem_read_fetch_2_S PBMT_PMA pa region h s1
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv).
      cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmr). clear Hmr.
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  unfold fetch.
  rewrite exec_catch_early_return.
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold or_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
          apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign4. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2).
  cbv iota beta.
  match goal with |- context[if isRVC ?h then _ else _] =>
    replace (isRVC h) with true by (symmetry; exact HisRVC) end.
  cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.

Lemma exec_fetch_F_Base_2_pa
      (va pa pah : mword 64) (w : mword 32) (s s1 s2 : mstate) (regl regh : PMA_Region) :
  let ilo : mword 16 := subrange_vec_dec w 15 0 in
  let ihi : mword 16 := subrange_vec_dec w 31 16 in
  let vah : mword 64 := add_vec_int va 2 in
  register_lookup PC s.(sregs) = va ->
  register_lookup PC s1.(sregs) = va ->
  eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  neq_vec (access_vec_dec va 0) ('b"0") = false ->
  neq_vec (access_vec_dec va 1) ('b"0") = true ->
  is_aligned_vaddr (Virtaddr va) 4 = false ->
  exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s1) ->
  exec (translateAddr (Virtaddr vah) (InstructionFetch tt)) s1
    = Some (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw), s2) ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s1.(sregs)) 0)) 4)
    (uint pa) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s1.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s1.(sregs)) (Physaddr pa) 2 = Some regl ->
  is_aligned_paddr (Physaddr pa) 2 = true ->
  (override_PMA (PMA_Region_attributes regl) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pa) 2) s1 = Some (false, s1) ->
  exec (within_sig (Physaddr pa) 2) s1 = Some (false, s1) ->
  exec (within_htif_readable (Physaddr pa) 2) s1 = Some (false, s1) ->
  dev_addr pa = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s1.(mem) !! (pa_add pa j) = Some (nth_byte ilo j)) ->
  register_lookup cur_privilege s1.(sregs) = Supervisor ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s2.(sregs)) 0)) 4)
    (uint pah) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s2.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s2.(sregs)) (Physaddr pah) 2 = Some regh ->
  is_aligned_paddr (Physaddr pah) 2 = true ->
  (override_PMA (PMA_Region_attributes regh) PBMT_PMA).(PMA_executable) = true ->
  exec (within_clint (Physaddr pah) 2) s2 = Some (false, s2) ->
  exec (within_sig (Physaddr pah) 2) s2 = Some (false, s2) ->
  exec (within_htif_readable (Physaddr pah) 2) s2 = Some (false, s2) ->
  dev_addr pah = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s2.(mem) !! (pa_add pah j) = Some (nth_byte ihi j)) ->
  register_lookup cur_privilege s2.(sregs) = Supervisor ->
  isRVC ilo = false ->
  concat_vec ihi ilo = w ->
  exec (fetch tt) s = Some (F_Base w, s2).
Proof.
  intros ilo ihi vah HpcPC HpcPC1 HmisaC Hbit0 Hbit1 Hvalign4 Htrl Htrh
         iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHdevL iHbytesL iHprivL
         iHAH iHordH iHrangeH iHXH iHmatchH iHalignH iHexecH iHcH iHsigH iHhH iHdevH iHbytesH iHprivH
         HnotRVC Hconcat.
  assert (HrdPC : exec (Defs.read_reg PC) s = Some (va, s)).
  { rewrite (exec_read_reg PC s). rewrite HpcPC. reflexivity. }
  assert (HrdPC1 : exec (Defs.read_reg PC) s1 = Some (va, s1)).
  { rewrite (exec_read_reg PC s1). rewrite HpcPC1. reflexivity. }
  assert (Hfb2l : exec (fetch_bytes va va 2) s = Some (@FetchBytes_Success 2 ilo, s1)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
    match goal with |- context[Defs.bind (Defs.bind0 ?r ?t) ?k] =>
      assert (Hpre : execR (Defs.bind0 r t : Defs.monadR (FetchBytes_Result 2) exception _) s
                     = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1)) end.
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      rewrite execR_liftR. rewrite Htrl. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hpre). clear Hpre.
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    match goal with |- context[Defs.bind (Defs.liftR (mem_read ?a ?b ?c ?d ?e ?f ?g)) ?k] =>
      assert (Hmr : execR (Defs.liftR (mem_read a b c d e f g) : Defs.monadR (FetchBytes_Result 2) exception _) s1
                    = Some (inr (Ok ilo), s1)) end.
    { rewrite execR_liftR.
      rewrite (exec_mem_read_fetch_2_S PBMT_PMA pa regl ilo s1
                   iHAL iHordL iHrangeL iHXL iHmatchL iHalignL iHexecL iHcL iHsigL iHhL iHdevL iHbytesL iHprivL).
      cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmr). clear Hmr.
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  assert (Hfb2h : exec (fetch_bytes va vah 2) s1 = Some (@FetchBytes_Success 2 ihi, s2)).
  { unfold fetch_bytes.
    rewrite exec_catch_early_return.
    change (ext_fetch_check_pc va vah) with (@None unit). cbv iota beta.
    match goal with |- context[Defs.bind (Defs.bind0 ?r ?t) ?k] =>
      assert (Hpre : execR (Defs.bind0 r t : Defs.monadR (FetchBytes_Result 2) exception _) s1
                     = Some (inr (Ok (Physaddr pah, PBMT_PMA, init_ext_ptw)), s2)) end.
    { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
      rewrite execR_liftR. rewrite Htrh. cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hpre). clear Hpre.
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pah, PBMT_PMA) s2)).
    cbv iota beta.
    match goal with |- context[Defs.bind (Defs.liftR (mem_read ?a ?b ?c ?d ?e ?f ?g)) ?k] =>
      assert (Hmr : execR (Defs.liftR (mem_read a b c d e f g) : Defs.monadR (FetchBytes_Result 2) exception _) s2
                    = Some (inr (Ok ihi), s2)) end.
    { rewrite execR_liftR.
      rewrite (exec_mem_read_fetch_2_S PBMT_PMA pah regh ihi s2
                   iHAH iHordH iHrangeH iHXH iHmatchH iHalignH iHexecH iHcH iHsigH iHhH iHdevH iHbytesH iHprivH).
      cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ Hmr). clear Hmr.
    cbv iota beta. rewrite autocast_mword_id_16.
    rewrite execR_returnR_fwd. cbn match. reflexivity. }
  unfold fetch.
  rewrite exec_catch_early_return.
  change (get_config_rvfi tt) with false. cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  change (ext_fetch_check_pc va va) with (@None unit). cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
      unfold or_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit0. apply execR_returnR_fwd. }
      cbv iota beta.
      unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hbit1. apply execR_returnR_fwd. }
      cbv iota beta.
      rewrite (execR_bind_Some _ _ _ true s).
      2:{ rewrite execR_liftR. rewrite (exec_currentlyEnabled_Zca s HmisaC). cbn match.
          apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_bind_Some _ _ _ false s).
  2:{ unfold and_boolM.
      rewrite (execR_bind_Some _ _ _ false s).
      2:{ rewrite (execR_liftR_seq _ _ _ _ _ HrdPC). rewrite Hvalign4. apply execR_returnR_fwd. }
      cbv iota beta. reflexivity. }
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2l).
  cbv iota beta.
  match goal with |- context[if isRVC ?h then _ else _] =>
    replace (isRVC h) with false by (symmetry; exact HnotRVC) end.
  cbv iota beta.
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite (execR_liftR_seq _ _ _ _ _ HrdPC1).
  rewrite (execR_liftR_seq _ _ _ _ _ Hfb2h).
  cbv iota beta. rewrite execR_returnR_fwd. cbn match.
  do 3 f_equal. exact Hconcat.
Qed.

(* ===================================================================== *)
(* 11. 8-byte S-mode LOADs through a NON-IDENTITY translation (pa != ea): *)
(* pa-generalized copies of WpSmodeGpr's RWS/RWgS/ExecLoadGS (+walk).     *)
(* ===================================================================== *)

Section RWSpa.
Variable a pa : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
Variable s : mstate.
Let s' := set_reg s tlb tlbf.
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

Lemma exec_vmem_read_addr_8_pa :
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
End RWSpa.

Section RWgSpa.
Variable rs1 : mword 5.
Variable offset : mword 64.
Variable pa : mword 64.
Variable v : bv 64.
Variable region : PMA_Region.
Variable satp0 : mword 64.
Variable tlbf : vec (option TLB_Entry) (2 ^ 6).
Variable s : mstate.
Let s' := set_reg s tlb tlbf.
Let ea := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) offset.
Let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0).
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

Lemma exec_vmem_read_8_gpr_pa :
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
  rewrite (exec_vmem_read_addr_8_pa a8 pa v region tlbf s Halign Hcp' Hmprv' Htr HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes).
  reflexivity.
Qed.
End RWgSpa.

Section ExecLoadGSpa.
Variable rs1 rd : mword 5.
Variable imm : mword 12.
Variable pa : mword 64.
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

Lemma exec_execute_LOAD_8_gpr_pa :
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
    (exec_vmem_read_8_gpr_pa rs1 offset pa v region satp0 tlbf s Hcp HSXL Hsatp Hmode Hmprv Hmxr Hpmm Halign Htr Hcp' Hmprv' HA Hord Hrange HR Hmatch Hpalign Hread Hc Hsig Hh Hdev Hbytes)).
  cbn match.
  assert (Hw : exec (wX_bits (Regidx rd) (extend_value false data2)) s'
               = Some (tt, set_reg s' (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (extend_value false data2)))).
  { rewrite (exec_wX_bits_gpr rd (extend_value false data2) s').
    rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd). reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hw).
  apply exec_returnM.
Qed.
End ExecLoadGSpa.

