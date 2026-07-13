(* UmodeFetch.v -- User-mode instruction fetch through the Sv39 TLB-hit path.

   U-mode twins of SmodeCore's S-mode fetch tower, in two flavours:
     - straight clones where only the privilege changes
       ([exec_translationMode_U_sv39],
        [exec_pmpCheck_user_grant], [exec_checked_mem_read_ram_4_U],
        [exec_mem_read_fetch_4_U], [exec_dispatchInterrupt_none_U]);
     - the TLB-hit translate chain GENERALIZED over an abstract TLB entry
       [ent] (SmodeCore's is specialized to the kernel identity superpage):
       the per-entry facts (permission check succeeds for a U/X/A leaf,
       A/D preset so no PTE write-back, PBMT_PMA, the entry matches the
       vpn) become SECTION HYPOTHESES in the conditioned-engine style --
       a concrete instantiation discharges them by vm_compute, the future
       user-page-table invariant by pt_wf.  The translated address is NOT
       the identity: the result is [u_pa ent va vpn], the entry's ppn
       glued to the page offset.                                          *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodeCore.
Require Import WpIntrCore.
Require Import WpGprCsrwB.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 dispatchInterrupt = None in User mode.  Unlike Supervisor (where     *)
(*    SIE = 0 masks delivery), S-destined interrupts are ALWAYS deliverable *)
(*    in User mode -- so None requires the pending SETS themselves to be    *)
(*    empty: mie & ~mideleg = 0 kills the M set, and the S set              *)
(*    (mip|sig) & mie & mideleg must be zero.                               *)
(* ===================================================================== *)

Lemma exec_getPendingSet_user_none (s : mstate)
    (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  and_vec (s_mip_bits mip_v meip seip) (and_vec mie_v mdv_v) = zeros' 64 ->
  exec (getPendingSet User) s = Some (None, s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hm0 Hs0.
  assert (Hguard : exec (or_boolM (currentlyEnabled Ext_S)
                     (bind (read_reg mideleg)
                        (fun w1 : mword 64 => returnM (eq_vec w1 (zeros' 64))))) s
                   = Some (true, s)).
  { rewrite (exec_or_boolM_Some _ _ _ _ _ HES). reflexivity. }
  assert (Hae : exec (Defs.assert_exp' true "sys/sys_control.sail:107.58-107.59") s
                = Some (eq_refl, s)).
  { unfold assert_exp'. cbn match. apply exec_returnm. }
  assert (Hmipr : exec (read_mip IncludePlatformInterrupts) s
                  = Some (s_mip_bits mip_v meip seip, s)).
  { apply (exec_read_mip_reduce s mip_v meip seip HES Hmip Hmeip Hseip). }
  assert (HmIEt : exec (or_boolM
            (and_boolM (returnM (generic_eq User Machine))
               (bind (read_reg mstatus)
                  (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
            (returnM (orb (generic_eq User Supervisor) (generic_eq User User)))) s
                = Some (true, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq User Machine))
                     (bind (read_reg mstatus)
                        (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq User Machine) s)).
      change (generic_eq User Machine) with false. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (orb (generic_eq User Supervisor) (generic_eq User User)) with true.
    apply exec_returnm. }
  assert (HsIEt : exec (or_boolM
            (and_boolM (returnM (generic_eq User Supervisor))
               (bind (read_reg mstatus)
                  (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq User User))) s
                = Some (true, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq User Supervisor))
                     (bind (read_reg mstatus)
                        (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq User Supervisor) s)).
      change (generic_eq User Supervisor) with false. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (generic_eq User User) with true. apply exec_returnm. }
  unfold getPendingSet.
  rewrite (exec_bind_Some _ _ _ _ _ Hguard).
  rewrite (exec_bind_Some _ _ _ _ _ Hae).
  rewrite (exec_bind_Some _ _ _ _ _ Hmipr).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ HmIEt).
  rewrite (exec_bind_Some _ _ _ _ _ HsIEt).
  rewrite Hmie. rewrite Hmdl.
  rewrite Hm0. rewrite and_vec_zeros64_r.
  rewrite Hs0.
  assert (Hnq : neq_vec (zeros' 64 : mword 64) (zeros' 64) = false).
  { vm_compute. reflexivity. }
  rewrite Hnq.
  cbn [andb].
  apply exec_returnm.
Qed.

Lemma exec_dispatchInterrupt_none_U (s : mstate) :
  exec (getPendingSet User) s = Some (None, s) ->
  exec (dispatchInterrupt User) s = Some (None, s).
Proof.
  intros Hgp. unfold dispatchInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _ Hgp). cbn match. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §2 translationMode User = Sv39 (reads mstatus.UXL, then satp.Mode).     *)
(* ===================================================================== *)

Lemma exec_translationMode_U_sv39 (satp0 : mword 64) s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
  exec (translationMode User) s = Some (Sv39, s).
Proof.
  intros HSXL Hsatp Hmode.
  unfold translationMode.
  replace (generic_eq User Machine) with false by (vm_compute; reflexivity).
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

(* ===================================================================== *)
(* §3 User-mode PMP grant + physical 4-byte fetch read (straight clones   *)
(*    of the Supervisor versions -- the per-entry PMP logic is identical   *)
(*    below Machine).                                                      *)
(* ===================================================================== *)

Lemma exec_pmpCheck_user_grant (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (InstructionFetch tt) User) s = Some (None, s).
Proof.
  intros HA Hord Hrange HX.
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
                            (InstructionFetch tt)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HX. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

Lemma exec_checked_mem_read_ram_4_U (pbmt : page_based_mem_type) (addr : mword 64)
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
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (InstructionFetch tt) pbmt User (Physaddr addr) 4 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant addr 4 s HA Hord Hrange HX)).
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
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_4 addr w s Hdev Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_fetch_4_U (pbmt : page_based_mem_type) (addr : mword 64)
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
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_read (InstructionFetch tt) pbmt (Physaddr addr) 4 false false false)
       s = Some (Ok w, s).
Proof.
  intros HA Hord Hrange HX Hmatch Halign Hexec Hc Hsig Hh Hdev Hbytes Hpriv.
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
      2:{ cbn match. apply exec_checked_mem_read_ram_4_U with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §4 The abstract-entry TLB-hit translate chain in User mode.  The       *)
(*    per-entry semantic facts are section hypotheses (quantified over    *)
(*    the state -- these operations are read-only there).                  *)
(* ===================================================================== *)

(* the physical address a hit on [ent] yields for [va] (ppn ++ page offset) *)
Definition u_pa (ent : TLB_Entry) (va : mword 64) (vpn : mword 27) : mword 64 :=
  zero_extend' 64 (concat_vec (tlb_get_ppn 39 ent vpn)
    (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)).

Section UTranslateHit.
  Context (ent : TLB_Entry) (vpn : mword 27).

  (* the fetch-permission check succeeds on this entry's PTE (a V/X/U/A
     leaf), for every mxr/do_sum *)
  Hypothesis Hchk : forall (mxr do_sum : bool) s,
    exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
            (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 ent) 7 0))
            (ext_bits_of_PTE (tlb_get_pte 8 ent)) tt) s
      = Some (PTE_Check_Success tt, s).
  (* A (and D as needed) preset: the hit performs NO PTE write-back *)
  Hypothesis Hupd : update_PTE_Bits (tlb_get_pte 8 ent) (InstructionFetch tt)
                    = (None : option (mword 64)).
  Hypothesis Hpbmt : forall s, exec (tlb_get_pbmt ent) s = Some (PBMT_PMA, s).
  Hypothesis Hmatch : match_TLB_Entry ent (mword_of_int 0 : mword 16)
                        (sign_extend' (57 - 12) vpn) = true.

  Lemma exec_translate_TLB_hit_u (mxr do_sum : bool) s :
    exec (translate_TLB_hit 39 (mword_of_int 0 : mword 16) vpn (InstructionFetch tt) User mxr do_sum
            tt (tlb_hash (__id 39) vpn) ent) s
      = Some (Ok (tlb_get_ppn 39 ent vpn, PBMT_PMA, tt), s).
  Proof.
    unfold translate_TLB_hit. cbn zeta.
    rewrite (exec_bind_Some _ _ _ _ _ (Hchk mxr do_sum s)). cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd' : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[update_PTE_Bits ?p ?ac] =>
        replace (update_PTE_Bits p ac) with (@None (mword 64)) by (symmetry; exact Hupd) end.
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd'). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (Hpbmt s)). apply exec_returnm.
  Qed.

  Lemma exec_lookup_TLB_hit_u (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    exec (lookup_TLB 39 (mword_of_int 0 : mword 16) vpn) s
      = Some (Some (tlb_hash (__id 39) vpn, ent), s).
  Proof.
    intros Htlb Hvec.
    unfold lookup_TLB.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
    rewrite Htlb. rewrite Hvec.
    rewrite Hmatch.
    apply exec_returnm.
  Qed.

  Lemma exec_translate_hit_u (mxr do_sum : bool)
        (base_ppn : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    exec (translate 39 (mword_of_int 0 : mword 16) base_ppn vpn (InstructionFetch tt) User mxr do_sum tt) s
      = Some (Ok (tlb_get_ppn 39 ent vpn, PBMT_PMA, tt), s).
  Proof.
    intros Htlb Hvec.
    unfold translate.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_hit_u tlbvec s Htlb Hvec)).
    cbn match.
    apply exec_translate_TLB_hit_u.
  Qed.

  Lemma exec_translateAddr_fetch_hit_u (va : mword 64) (satp0 : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    register_lookup cur_privilege s.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
    register_lookup satp s.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb s.(sregs) = tlbvec ->
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    exec (translateAddr (Virtaddr va) (InstructionFetch tt)) s
      = Some (Ok (Physaddr (u_pa ent va vpn), PBMT_PMA, init_ext_ptw), s).
  Proof.
    intros Hcp HSXL Hsatp Hmode Hasid Htlb Hvec Hcanon Hvpn_def.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_effectivePrivilege_fetch _ _ s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_U_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_is_shadow_stack_fetch s)).
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
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translate_hit_u _ _ _ tlbvec s Htlb Hvec)).
    cbn match.
    rewrite execR_returnR. cbn match.
    reflexivity.
  Qed.

End UTranslateHit.

(* ===================================================================== *)
(* §5 The U-mode 4-byte F_Base fetch, with the translated pa DISTINCT     *)
(*    from the va (user mappings are not the identity).                    *)
(* ===================================================================== *)

Lemma exec_fetch_F_Base_4_U_gen
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
  register_lookup cur_privilege s1.(sregs) = User ->
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
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.bind0 (Defs.returnR _ tt)
              (Defs.liftR (translateAddr (Virtaddr va) (InstructionFetch tt)))) s
           = Some (inr (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)), s1))).
    2:{ rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s)).
        rewrite execR_liftR. rewrite Htr. cbn match. reflexivity. }
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (Physaddr pa, PBMT_PMA) s1)).
    cbv iota beta.
    rewrite (execR_bind_Some _ _ _ _ _
      (_ : execR (Defs.liftR (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4 false false false)) s1
           = Some (inr (Ok w), s1))).
    2:{ rewrite execR_liftR.
        rewrite (exec_mem_read_fetch_4_U PBMT_PMA pa region w s1
                   iHA iHord iHrange iHX iHmatch iHalign iHexec iHc iHsig iHh iHdev iHbytes iHpriv).
        cbn match. reflexivity. }
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
  cbv iota beta. rewrite HnotRVC. cbv iota beta.
  rewrite execR_returnR_fwd. cbn match. reflexivity.
Qed.
