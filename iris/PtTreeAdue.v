(* PtTreeAdue.v -- the Svadu/ADUE WRITE-BACK arm of the page-table-tree
   translation (PtTree.v).  Under this build menvcfg.ADUE = 1, so an
   access whose leaf lacks the A bit (or D, for stores) does NOT fault:
   the walk WRITES the A/D-updated PTE back to the leaf slot and installs
   the updated word in the TLB.  Because the leaf slot is owned by the
   table invariant ([ptree_own]) and the updated word is an A/D VARIANT
   of the old one ([update_PTE_Bits_set_ad]), the invariant absorbs the
   write: [ptree_own_path_upd] reseals the ownership at
   [ptree_set_leaf], [tlb_ok_pt_fill]/[tlb_ok_pt_set_leaf] reseal the
   TLB consistency, and an instance spec like [kpt_tree_spec_gen]
   survives by [kpt_tree_spec_gen_set_leaf].  Clients of the invariant
   never see the memory change.

   Layers here (all exec-level):
     §1 the raw PTE write ([write_pte] = an 8-byte Supervisor
        [mem_write_value_priv] at access (Store PageTableEntry)):
        PMP store grant, PMA store check, checked write, [exec_write_pte_ram];
     §2 [update_and_write_pte] with [update_PTE_Bits = Some] (the Svadu
        gate is LIVE: menvcfg.ADUE = 1);
     §3 the level-0 [add_to_TLB] with arbitrary arguments
        ([pt_fill_ent]) and its identification with [u_walk_entry] of
        the UPDATED leaf ([pt_fill_ent_uwe] -- needs only that the new
        word is an A/D variant: PPN and G are stable);
     §4 the write-back translate: [exec_translate_TLB_miss_pt_upd] and
        the three-way [exec_translate_pt_upd] (miss arms), plus
        [exec_translate_TLB_hit_pt_upd] -- a HIT whose cached word lacks
        A/D writes back through the cached pteAddr and refreshes the
        entry in place.                                                  *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte.
Require Import PtAdBits.
Require Import CommonWalk.
(* the [swp] layer, for the footprinted twin of the front matter below *)
Require Import HartSwp HartLift HartRegNode HartSpan HartSpanChar HartGoodb
        WpDecodeBridge.
Require Import WpMmodeLeafBase HartMPmp HartMFetch HartMStore HartEvents.
Require Import PtTree.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The raw PTE write.                                                  *)
(* ===================================================================== *)

(* Supervisor PMP grant for the PTE store (clone of WpSmodeGpr's
   [exec_pmpCheck_supervisor_grant_store] at access (Store PageTableEntry)) *)
Lemma exec_pmpCheck_supervisor_grant_wpte (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Store PageTableEntry) Supervisor) s = Some (None, s).
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
                            (Store PageTableEntry)) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* PMA check for the PTE store (clone of WpMmodeLeafBase's
   [exec_pmaCheck_ram_store] at access (Store PageTableEntry)) *)
Lemma exec_pmaCheck_ram_wpte (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_supports_pte_write) = true ->
  exec (pmaCheck (Physaddr addr) 8 (Store PageTableEntry) pbmt false) s = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Halign Hwrite.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Hwrite (exec_is_mag_applicable_store_pte 8 s) Halign.
Qed.

Lemma exec_pmaCheck_ram_wpte_con (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8 = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_supports_pte_write) = true ->
  exec (pmaCheck (Physaddr addr) 8 (Store PageTableEntry) pbmt true) s = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Halign Hwrite.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_peel Hmatch Hwrite (exec_is_mag_applicable_store_pte 8 s) Halign.
Qed.

(* the full PTE write to a RAM slot: memory gains the 8 bytes, registers
   and the device are untouched *)
Lemma exec_write_pte_ram (a : mword 64) (w' : mword 64) (region : PMA_Region) s :
  addr_is_ram a -> addr_is_ram (pa_add a 7) ->
  is_aligned_paddr (Physaddr a) 8 = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) * 4)%Z ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a) 8 = Some region ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_write) = true ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec (write_pte (Physaddr a) 8 (w' : mword 64)) s
  = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) a 8 w') s.(mdev)).
Proof.
  intros Hram Hram7 Halign HA Hord HW Hcov Hmatch Hwr Hhtif.
  assert (Hnw : (uint a + Z.of_nat 7 < 18446744073709551616)%Z).
  { destruct Hram as [_ Hh]. unfold ram_base, ram_size in Hh.
    change (Z.of_nat 7) with 7. lia. }
  assert (Hfit : (uint a + 8 <= ram_base + ram_size)%Z).
  { pose proof (uint_pa_add a 7 Hnw) as Heq.
    destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7.
    change (Z.of_nat 7) with 7 in Hhi7.
    unfold ram_base, ram_size in *. lia. }
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
            (uint a) (uint (to_bits 64 8)) = PMP_Match).
  { apply (ram_pmp_match_w a _ 8); [lia | vm_compute; reflexivity | | exact Hfit | exact Hcov].
    destruct Hram as [Hlo _]. exact Hlo. }
  pose proof (within_clint_false a 8 s (addr_is_ram_not_in_clint _ Hram) ltac:(lia)) as Hc.
  pose proof (within_sig_false a 8 s (addr_is_ram_not_in_sig _ Hram) ltac:(lia)) as Hsig.
  pose proof (within_htif_writable_false a 8 s Hhtif) as Hh.
  pose proof (addr_is_ram_not_dev _ Hram) as Hdev.
  assert (Hchk : exec (checked_mem_write (Physaddr a) 8 (w' : mword 64) (Store PageTableEntry)
                        PBMT_PMA Supervisor tt false false false) s
                 = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) a 8 w') s.(mdev))).
  { assert (Hcp : exec (check_pma_with_pmp_priority (Store PageTableEntry) PBMT_PMA
                          Supervisor (Physaddr a) 8 false) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_wpte a PBMT_PMA region s Hmatch Halign Hwr)).
      cbn match. apply exec_returnM. }
    assert (Hmmio : exec (within_mmio_writable (Physaddr a) 8) s = Some (false, s)).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    set (sw := MState s.(sregs) (write_bytes s.(mem) a 8 w') s.(mdev)).
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit a 8 0 s)). cbn beta.
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
      change (bits_of_physaddr (Physaddr a)) with a.
      rewrite avi0_mul8.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_supervisor_grant_wpte a 8 s HA Hord Hrange HW)).
      cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
      rewrite autocast_id.
      change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
      rewrite subrange_full_64.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?pa ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwr2 : execR (Defs.bind (Defs.liftR (write_ram wk pa wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (exec_write_ram_plain_8 a w' s Hdev)).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwr2). cbn beta zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity. }
  unfold write_pte, mem_write_value_priv, mem_write_value_priv_meta.
  cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ Hchk).
  cbn match. unfold mem_write_callback. apply exec_returnM.
Qed.

(* The CONDITIONAL PTE write: the write half of the fork's atomic A/D update.
   Same memory effect as the plain one -- the interpreter routes by address and
   ignores the access kind -- but it goes through the [con = true] path, so
   [mem_write_value_priv_meta]'s (rl || con) alignment guard is live (and false
   here, the PTE being 8-aligned) and the PTE arm of [pmaCheck] must not assert
   against res_or_con, which is exactly the fork's mem.sail change. *)
Lemma exec_write_pte_conditional_ram (a : mword 64) (w' : mword 64) (region : PMA_Region) s :
  addr_is_ram a -> addr_is_ram (pa_add a 7) ->
  is_aligned_paddr (Physaddr a) 8 = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) * 4)%Z ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a) 8 = Some region ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_write) = true ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec (write_pte_conditional (Physaddr a) 8 (w' : mword 64)) s
  = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) a 8 w') s.(mdev)).
Proof.
  intros Hram Hram7 Halign HA Hord HW Hcov Hmatch Hwr Hhtif.
  assert (Hnw : (uint a + Z.of_nat 7 < 18446744073709551616)%Z).
  { destruct Hram as [_ Hh]. unfold ram_base, ram_size in Hh.
    change (Z.of_nat 7) with 7. lia. }
  assert (Hfit : (uint a + 8 <= ram_base + ram_size)%Z).
  { pose proof (uint_pa_add a 7 Hnw) as Heq.
    destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7.
    change (Z.of_nat 7) with 7 in Hhi7.
    unfold ram_base, ram_size in *. lia. }
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
            (uint a) (uint (to_bits 64 8)) = PMP_Match).
  { apply (ram_pmp_match_w a _ 8); [lia | vm_compute; reflexivity | | exact Hfit | exact Hcov].
    destruct Hram as [Hlo _]. exact Hlo. }
  pose proof (within_clint_false a 8 s (addr_is_ram_not_in_clint _ Hram) ltac:(lia)) as Hc.
  pose proof (within_sig_false a 8 s (addr_is_ram_not_in_sig _ Hram) ltac:(lia)) as Hsig.
  pose proof (within_htif_writable_false a 8 s Hhtif) as Hh.
  pose proof (addr_is_ram_not_dev _ Hram) as Hdev.
  assert (Hchk : exec (checked_mem_write (Physaddr a) 8 (w' : mword 64) (Store PageTableEntry)
                        PBMT_PMA Supervisor tt false false true) s
                 = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) a 8 w') s.(mdev))).
  { assert (Hcp : exec (check_pma_with_pmp_priority (Store PageTableEntry) PBMT_PMA
                          Supervisor (Physaddr a) 8 true) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_wpte_con a PBMT_PMA region s Hmatch Halign Hwr)).
      cbn match. apply exec_returnM. }
    assert (Hmmio : exec (within_mmio_writable (Physaddr a) 8) s = Some (false, s)).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    set (sw := MState s.(sregs) (write_bytes s.(mem) a 8 w') s.(mdev)).
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit a 8 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _
               (_ : exec (write_kind_of_flags false false true) s
                    = Some (rv64d_types.Write_RISCV_conditional, s))).
    2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
    cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?b) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c b) s = Some (inr (true, 0, true), sw)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr a)) with a.
      rewrite avi0_mul8.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_supervisor_grant_wpte a 8 s HA Hord Hrange HW)).
      cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
      rewrite autocast_id.
      change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
      rewrite subrange_full_64.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?pa ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwr2 : execR (Defs.bind (Defs.liftR (write_ram wk pa wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (exec_write_ram_cond_8 a w' s Hdev)).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwr2). cbn beta zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity. }
  unfold write_pte_conditional, mem_write_value_priv, mem_write_value_priv_meta.
  cbn [orb andb Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ Hchk).
  cbn match. unfold mem_write_callback. apply exec_returnM.
Qed.

(* --------------------------------------------------------------------- *)
(* §1b THE SAME PTE ACCESS AT THE [swp] LAYER.  Spliced beside the exec   *)
(*     lemmas above, the way [swp_translateAddr_pt_front] is spliced       *)
(*     beside [exec_translateAddr_pt_front] in §5: the walk's PMP grant,   *)
(*     PMA check and PTE read become footprinted nodes, and the A/D        *)
(*     write-back twins below are then assembled from them by FOLLOWING    *)
(*     the exec proofs rather than re-deriving what they settle.           *)
(* --------------------------------------------------------------------- *)

(* ====================================================================== *)
(* THE SUPERVISOR PMP CHECK, FOOTPRINTED.                                  *)
(*                                                                        *)
(* [HartMPmp.mpmp_hval] cannot serve here and the reason is not the        *)
(* privilege argument, it is the DEFAULT.  At Machine a walk that matches  *)
(* no entry falls through to ALLOW, so that proof is a 16-entry loop        *)
(* induction whose every exit is [Ret None].  At Supervisor the fall-      *)
(* through is DENY, so a granting walk must actually MATCH -- and the      *)
(* xv6 configuration grants through entry 0 (TOR, base 0, R/W/X set),      *)
(* which the exec side already states as                                  *)
(* [SmodePte.exec_pmpCheck_supervisor_grant_load].                        *)
(*                                                                        *)
(* That makes this the SHORTER proof of the two: entry 0 matches, so the   *)
(* walk early-returns on the FIRST iteration and no loop invariant is      *)
(* needed at all.  What it costs instead is that the walk cannot go        *)
(* through the [goodb] bridge -- [goodb] rejects [ExtraOutcome], which is  *)
(* exactly the node an early return is -- so the reads are peeled at the   *)
(* [hspan] level, the way the M-mode walk peels its own.                   *)
(* ====================================================================== *)

Local Ltac spmp_red H :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR Defs.read_reg
     pmpReadAddrReg Defs.early_return Defs.throw sys_pmp_grain Z.geb
     Z.compare andb not negb pmpCheckRWX Defs.or_boolM] in H.

Local Ltac spmp_peel_any reg H Hstop v rsN HagN :=
  apply hspan_peel in H; [ | reflexivity | exact Hstop ];
  let c := fresh "c" in
  let Hstep := fresh "Hstep" in
  destruct H as (c & Hstep & H);
  let Hat := fresh "Hat" in
  match type of Hstep with
  | hspani _ _ (?m, _) _ =>
      assert (Hat : hregread_at reg m = true)
        by (cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity)
  end;
  destruct (hspani_read_any_inv _ _ reg _ _ _ Hat Hstep) as (v & rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

Local Ltac spmp_peel_D reg H Hstop HD rsN HagN :=
  apply hspan_peel in H; [ | reflexivity | exact Hstop ];
  let c := fresh "c" in
  let Hstep := fresh "Hstep" in
  destruct H as (c & Hstep & H);
  let Hat := fresh "Hat" in
  match type of Hstep with
  | hspani _ _ (?m, _) _ =>
      assert (Hat : hregread_at reg m = true)
        by (cbn [hregread_at]; apply bool_decide_eq_true_2; reflexivity)
  end;
  destruct (hspani_read_D_inv _ _ reg _ _ _ Hat HD Hstep) as (rsN & HagN & ->);
  clear Hat Hstep;
  rewrite hregread_resume_red in H.

(* [SmodePte.exec_pmpMatchAddr_TOR_match] with the state dropped: its proof
   is three rewrites and never touches [s], so the PURE equation is what a
   footprint peel can actually rewrite with. *)

(* ---------------------------------------------------------------------- *)
(* THE PMA CHECK FOR AN 8-BYTE PTE READ.                                    *)
(*                                                                        *)
(* [HartMFetch.hfrun_check_pma_ifetch] is already width-generic, so what    *)
(* changes here is only WHICH grant conjunct the region has to supply:      *)
(* a fetch reads [PMA_executable], a page-table read reads                  *)
(* [PMA_supports_pte_read].  Both sit in the same [pma_allows_ram] bundle,  *)
(* so the caller's premise does not grow.                                   *)
(* ---------------------------------------------------------------------- *)

Local Ltac scmr_cbn :=
  cbn beta iota zeta delta
    [Defs.bind Defs.bind0 Interface.iMon_bind Defs.liftR Defs.try_catch
     Defs.catch_early_return Defs.returnm returnM returnR
     Defs.returnR Defs.read_reg Defs.early_return Defs.throw
     Defs.assert_exp Defs.assert_exp'
     Defs.and_boolM Defs.or_boolM andb orb negb not
     check_pma_with_pmp_priority pmaCheck mag_pma_check
     is_mag_applicable_access __id
     get_config_rvfi plat_have_clint plat_have_sig].

Local Ltac scmr_read :=
  rewrite hfrun_read;
  match goal with
  | |- context [ bool_decide ?P ] =>
      rewrite (bool_decide_eq_true_2 P ltac:(assumption))
  end.

Lemma hfrun_check_pma_pte (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) (n : Z)
    (con : bool) :
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_ram pmar0 ->
  pma_ram_access pa n ->
  is_aligned_paddr (Physaddr pa) n = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (Load PageTableEntry) PBMT_PMA Supervisor
       (Physaddr pa) n con)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros HD Hpma Hpallow Hacc Hpa.
  unfold check_pma_with_pmp_priority. scmr_cbn.
  scmr_read. rewrite Hpma. scmr_cbn.
  destruct (Hpallow pa n Hacc) as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (_ & _ & _ & _ & Hpte & _).
  cbn [PMA_Region_attributes] in Hpte.
  rewrite Hmatch. scmr_cbn.
  rewrite Hpte. scmr_cbn.
  rewrite Hpa. scmr_cbn.
  apply hfrun_ret.
Qed.

Lemma pmpMatchAddr_TOR_match_pure (addr width : mword 64) (ent : mword 8)
    (pmpaddr prev : mword 64) :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = TOR ->
  zopz0zKzJ_u prev pmpaddr = false ->
  pmpRangeMatch (Z.mul (uint prev) 4) (Z.mul (uint pmpaddr) 4)
    (uint addr) (uint width) = PMP_Match ->
  pmpMatchAddr (Physaddr addr) width ent pmpaddr prev = returnM PMP_Match.
Proof.
  intros HA Hord Hrange. unfold pmpMatchAddr. cbn zeta.
  rewrite HA. cbn match. rewrite Hord. rewrite Hrange. reflexivity.
Qed.

Lemma spmp_hval_grant (D Drw : gset register)
    (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n)
    (addr : SailStdpp.Values.mword 64) (rs : regstate) (wd : Z)
    (acc : MemoryAccessType mem_payload) :
  (pmpcfg_n : register) ∈ D ->
  (pmpaddr_n : register) ∈ D ->
  register_lookup pmpcfg_n rs = pcfg ->
  register_lookup pmpaddr_n rs = paddr ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec paddr 0)) 4)
    (uint addr) (uint (to_bits 64 wd)) = PMP_Match ->
  (* the entry GRANTS this access class.  Pure: [pmpCheckRWX] only reads the
     entry's permission bits, so the caller supplies it as an equation and no
     state reaches this premise. *)
  pmpCheckRWX (vec_access_dec pcfg 0) acc = returnM true ->
  hval D Drw rs (pmpCheck (Physaddr addr) wd acc Supervisor) None rs.
Proof.
  intros HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange Hrwx rs0 l Hag0 Hchain Hstop.
  unfold pmpCheck in Hchain.
  replace (Z.eqb sys_pmp_count 0) with false in Hchain
    by (vm_compute; reflexivity).
  replace (Z.sub sys_pmp_count 1) with 15 in Hchain
    by (vm_compute; reflexivity).
  unfold Defs.foreach_ZM_up in Hchain.
  replace (S (Z.abs_nat (Z.sub 0 15))) with 16%nat in Hchain
    by (vm_compute; reflexivity).
  spmp_red Hchain.
  (* ONE iteration: entry 0 matches, so the walk never reaches entry 1 *)
  cbn [Defs.foreach_ZM_up'] in Hchain.
  spmp_red Hchain.
  (* the entry's cfg byte, pinned *)
  spmp_peel_D pmpcfg_n Hchain Hstop HDcfg rs1 Hag1.
  rewrite (Hag0 _ HDcfg) Hpcfg in Hchain.
  spmp_red Hchain.
  (* [pmpReadAddrReg 0] reads cfg again (value-dead: the grain adjustment is
     [false] at [sys_pmp_grain = 0] whatever the entry says) then pmpaddr *)
  spmp_peel_any pmpcfg_n Hchain Hstop w2 rs2 Hag2. spmp_red Hchain.
  (* the peel substitutes the value read from the file it was AT, so the
     agreement that transports it is the one for the PRE-peel file *)
  assert (Hag12 : reg_agree_on D rs2 rs).
  { intros r Hr. rewrite (Hag2 r Hr) (Hag1 r Hr). exact (Hag0 r Hr). }
  spmp_peel_D pmpaddr_n Hchain Hstop HDaddr rs3 Hag3.
  rewrite (Hag12 _ HDaddr) Hpaddr in Hchain.
  assert (Hag13 : reg_agree_on D rs3 rs).
  { intros r Hr. rewrite (Hag3 r Hr). exact (Hag12 r Hr). }
  spmp_red Hchain.
  (* the address match is now on concrete values: TOR + in range = Match *)
  rewrite (pmpMatchAddr_TOR_match_pure addr (to_bits 64 wd)
             (vec_access_dec pcfg 0) (vec_access_dec paddr 0) (zeros' 64)
             HA Hord Hrange) in Hchain.
  spmp_red Hchain.
  (* granted by the entry's permission bit -- at Supervisor the second
     disjunct of [or_boolM] (Machine and unlocked) is unavailable, and this
     is the whole difference from the M-mode walk *)
  rewrite Hrwx in Hchain.
  spmp_red Hchain.
  assert (Hl : l = (Interface.Ret None, rs3))
    by (apply (hspan_stop_refl D Drw _ rs3 l); [reflexivity | exact Hchain]).
  rewrite Hl. cbn. split; [reflexivity | exact Hag13].
Qed.



(* THE PURE CONVERSE of [read_bytes_spec], which the tree does not have.
   [HartLift2.text_read_bytes] and [HartPilot.phys_read_bytes] both END here
   but each bundles the step with its own resource, so neither is reusable
   for a slot whose bytes arrive as a [pt_slot_mem] conjunct rather than as a
   points-to.  The proof is exactly their shared tail.  (Belongs with the
   [read_bytes] family in [RiscvFetchExec]; it is here because that file sits
   under most of the tree and this is its only consumer so far.) *)
Lemma read_bytes_of_bytes mm pa n (w : bv (8 * n)) :
  (forall j : nat, (N.of_nat j < n)%N -> mm !! pa_add pa j = Some (nth_byte w j)) ->
  read_bytes mm pa n = Some w.
Proof.
  intros Hbytes.
  destruct (read_bytes mm pa n) as [w'|] eqn:Hrb.
  - f_equal. apply bv_eq_of_bytes. intros j Hj.
    pose proof (read_bytes_spec _ _ _ _ Hrb j Hj) as H0.
    pose proof (Hbytes j Hj) as H1.
    rewrite H0 in H1. apply Some_inj in H1. exact H1.
  - exfalso. exact (read_bytes_ne mm pa n w Hbytes Hrb).
Qed.

Section SPmpSwp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload).

  (* the [swp] face of [spmp_hval_grant] -- one [swp_span], as with
     [HartMPmp]'s M-mode instances. *)
  Lemma swp_pmpCheck_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n)
      (addr : SailStdpp.Values.mword 64) (wd : Z) :
    Drw ## Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec paddr 0)) 4)
      (uint addr) (uint (to_bits 64 wd)) = PMP_Match ->
    pmpCheckRWX (vec_access_dec pcfg 0) acc = returnM true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (pmpCheck (Physaddr addr) wd acc Supervisor)
      (fun r => ⌜r = None⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange Hrwx.
    exact (swp_span Drw Dro Df rs rs _ None Hdisj
             (spmp_hval_grant (Drw ∪ Dro) Drw pcfg paddr addr rs wd acc
                HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange Hrwx)).
  Qed.

End SPmpSwp.

(* ====================================================================== *)
(* THE PTE READ, as a node.                                                *)
(*                                                                        *)
(* [HartMFetch.swp_checked_mem_read_ifetch4]'s shape at the page walk's     *)
(* access: [Load PageTableEntry] at [Supervisor], width 8.  The memory      *)
(* itself arrives the same way it does there -- as an ATOMIC-STEP fupd      *)
(* [∀ σ, mstate_interp σ ={⊤,∅}=∗ ⌜read_bytes …⌝ ∗ ▷ (|={∅,⊤}=> …)] -- and  *)
(* that is the shape that makes the shared kernel table usable here: the    *)
(* [kptN] invariant is opened INSIDE this one node and closed again before  *)
(* the next, which is the only way an invariant can be reached at all once  *)
(* a translation spans many nodes.                                         *)
(* ====================================================================== *)
Section pteread.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma swp_checked_mem_read_pte8 (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (bytes : bv 64) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec paddr 0)) 4)
      (uint pa) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    pma_allows_ram pmar0 ->
    pma_ram_access pa 8 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) pa 8 = Some bytes⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    swp (checked_mem_read (Load PageTableEntry) PBMT_PMA Supervisor
           (Physaddr pa) 8 false false false false)
      (fun r => ⌜r = Values.Ok (bytes, tt)⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HD HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
      HA Hord Hrange HR Hpallow Hacc Hram Hpa.
    iIntros "#Hcert Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_read.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Load PageTableEntry) PBMT_PMA
                 Supervisor (Physaddr pa) 8 false) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_pte (Drw ∪ Dro) Drw rs pa pmar0 8 false
                   HD Hpma Hpallow Hacc Hpa) with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind_ret. cbn beta iota zeta.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing read_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    cbn beta iota.
    rewrite /returnM mliftR_ret mbind_ret. cbn beta iota zeta.
    rewrite mliftR_ret mbind_ret. cbn beta iota zeta.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. cbn beta iota.
    change (0 * 8) with 0. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) 8 (Load PageTableEntry) Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S (Load PageTableEntry) Drw Dro Df rs pcfg paddr
                pa 8 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(unfold pmpCheckRWX; cbn match; rewrite HR; reflexivity)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_readable (Physaddr pa) 8)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_ram (Drw ∪ Dro) Drw rs pa 8
                   ltac:(lia) HDhtif Hhtif Hram)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota.
    iApply (swp_use_cer4 (read_ram Read_plain (Physaddr pa) 8 false)
              _ _ _ _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_hart_ram_read 8 (mread_req8 pa) _
                (fun r => (⌜r = (bytes, default_meta)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I)
                (hread_req_at_read_ram8 pa)
                (addr_is_ram_not_dev pa Hram) ltac:(reflexivity)
                with "Hcert [Hrw Hro Hmem]").
      iIntros (σ) "Hσ". iMod ("Hmem" $! σ with "Hσ") as "[%Hrb Hclose]".
      iModIntro. iExists bytes. iSplitR; [done|]. iNext.
      iMod "Hclose" as "Hσ". iModIntro. iFrame "Hσ".
      rewrite hread_resume_read_ram8. iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro)". cbn beta iota zeta.
    rewrite mbind_ret. cbn beta.
    change (0 =? 1 - 1) with true. cbn beta iota zeta.
    rewrite !autocast_id usvd_zeros_full_64 mcer_ret.
    iApply ("Hcont" $! (Values.Ok (bytes, tt))). by iFrame.
  Qed.

  (* [read_pte] on top of the node: [mem_read_priv] at [Load PageTableEntry]
     is [checked_mem_read] plus the callback and the meta drop, both pure.
     [SmodePte.exec_read_pte_S] reduces the same two steps on the exec side. *)
  (* THE EXCLUSIVE PTE RE-READ of the A/D write-back is an ordinary node
     (design §3a): [HartEvents.swp_hart_ram_read_excl], the plain read's
     twin, which also leaves the hart's reservation behind; the window is an
     ordinary silent stretch and [write_pte_conditional] an ordinary write
     ([swp_checked_mem_write_pte8_con] above).  Assembling the write-back
     from those three is item (e) of the worklist's reservation plan; the
     conditional-write rule that also learns the word is still the snapshot
     needs the [resv_frag]/[resv_ok] pair in [state_interp] first. *)

  Lemma swp_read_pte_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : SailStdpp.Values.mword 64) (w : bv 64) :
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_read (Load PageTableEntry) PBMT_PMA Supervisor
              (Physaddr pa) 8 false false false false)
         (fun r => ⌜r = Values.Ok (w, tt)⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)) -∗
    swp (read_pte (Physaddr pa) 8)
      (fun r => ⌜r = Values.Ok w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    iIntros "#Hcert Hrw Hro Hcmr".
    unfold read_pte, mem_read_priv, mem_read_priv_meta.
    cbn [orb andb].
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                         hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I) _
              with "[Hrw Hro Hcmr] [-]").
    { iApply (swp_bind_use _ _
                (fun r => (⌜r = Values.Ok (w, tt)⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro)%I) _
                with "[Hrw Hro Hcmr] [-]").
      - iApply ("Hcmr" with "Hrw Hro").
      - iIntros (v) "(-> & Hrw & Hro)". iApply swp_ret. by iFrame. }
    iIntros (v) "(-> & Hrw & Hro)". iApply swp_ret.
    cbn [MemoryOpResult_drop_meta]. by iFrame.
  Qed.

End pteread.


(* ---- the PMA check for an 8-byte PTE WRITE: [hfrun_check_pma_pte]'s twin
   taking the region's [PMA_supports_pte_write] conjunct instead of its
   [_read] one.  Same bundle, so no caller premise grows. ---- *)
Lemma hfrun_check_pma_wpte (D Drw : gset register) (rs : regstate)
    (pa : SailStdpp.Values.mword 64) (pmar0 : list PMA_Region) (n : Z)
    (con : bool) :
  (pma_regions : register) ∈ D ->
  register_lookup pma_regions rs = pmar0 ->
  pma_allows_ram pmar0 ->
  pma_ram_access pa n ->
  is_aligned_paddr (Physaddr pa) n = true ->
  hfrun 6 D Drw rs
    (check_pma_with_pmp_priority (Store PageTableEntry) PBMT_PMA Supervisor
       (Physaddr pa) n con)
  = Some (Values.Ok
            {| Phys_Mem_Access_Info_splittable := CannotSplit;
               Phys_Mem_Access_Info_granule_size_exp := 0 |}, rs).
Proof.
  intros HD Hpma Hpallow Hacc Hpa.
  unfold check_pma_with_pmp_priority. scmr_cbn.
  scmr_read. rewrite Hpma. scmr_cbn.
  destruct (Hpallow pa n Hacc) as (region & Hmatch & Hgrant).
  destruct region as [rbase rsize rattr rdtree].
  destruct Hgrant as (_ & _ & _ & _ & _ & Hptew & _).
  cbn [PMA_Region_attributes] in Hptew.
  rewrite Hmatch. scmr_cbn.
  rewrite Hptew. scmr_cbn.
  rewrite Hpa. scmr_cbn.
  apply hfrun_ret.
Qed.

(* the GLUE reducer, as [HartMStore]'s: pure combinators only, and it must
   NOT unfold the bind/liftR/cer spine [swp_use_cer] matches on. *)
Local Ltac spte_glue :=
  cbn beta iota zeta delta
    [Defs.returnm returnM returnR Defs.returnR andb orb negb not
     Instances.generic_eq Instances.generic_neq].

Section ptewrite.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE PTE WRITE, as a node -- [HartMStore.swp_checked_mem_write]'s shape at
     the walk's access.  [R] is the caller's carried resource, exactly as
     there: a write's memory obligation cannot hand back a pure fact, so what
     crosses the node is whatever the caller re-establishes. *)
  Lemma swp_checked_mem_write_pte8 (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) (v : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (R : iProp Σ) (rr : option resv) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec paddr 0)) 4)
      (uint pa) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    pma_allows_ram pmar0 ->
    pma_ram_access pa 8 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 8
                   (Interface.WriteReq.value (mwrite_req8 pa v)))
                σ.(mdev)) ∗ R)) -∗
    swp (checked_mem_write (Physaddr pa) 8 v (Store PageTableEntry) PBMT_PMA
           Supervisor tt false false false)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                resv_frag cpu_id None).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hpma Hpcfg Hpaddr Hhtif
      HA Hord Hrange HW Hpallow Hacc Hram Hpa.
    iIntros "#Hcert Hfrag Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_write.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Store PageTableEntry) PBMT_PMA
                 Supervisor (Physaddr pa) 8 false) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_wpte (Drw ∪ Dro) Drw rs pa pmar0 8 false
                   HDpma Hpma Hpallow Hacc Hpa) with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". spte_glue.
    rewrite mbind_ret. spte_glue.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing write_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    spte_glue.
    rewrite /returnM mliftR_ret mbind_ret. spte_glue.
    rewrite mliftR_ret mbind_ret. spte_glue.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. spte_glue.
    change (0 * 8) with 0. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) 8 (Store PageTableEntry) Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S (Store PageTableEntry) Drw Dro Df rs pcfg paddr
                pa 8 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(unfold pmpCheckRWX; cbn match; rewrite HW; reflexivity)
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". spte_glue.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_writable (Physaddr pa) 8)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_w_ram (Drw ∪ Dro) Drw rs pa 8
                   ltac:(lia) HDhtif Hhtif Hram) with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". spte_glue.
    change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
    rewrite subrange_full_64 autocast_id.
    iApply (swp_use_cer4 (write_ram Write_plain (Physaddr pa) 8 v tt)
              _ _ _ _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_hart_ram_write 8 (mwrite_req8 pa v) _
                (fun r => (⌜r = true⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗
                           R ∗ resv_frag cpu_id None)%I)
                rr (hwrite_req_at_write_ram8 pa v)
                (addr_is_ram_not_dev pa Hram) with "Hcert Hfrag [Hrw Hro Hmem]").
      iIntros (σ) "Hσ". iMod ("Hmem" $! σ with "Hσ") as "Hclose".
      iModIntro. iNext. iMod "Hclose" as "[Hσ HR]". iModIntro.
      iFrame "Hσ". iIntros "Hfrag".
      rewrite hwrite_resume_write_ram8. iApply swp_ret. by iFrame. }
    iIntros (v0) "(-> & Hrw & Hro & HR & Hfrag)". spte_glue.
    change (0 =? 1 - 1) with true. spte_glue.
    rewrite mbind_ret. spte_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok true)). by iFrame.
  Qed.

  (* THE CONDITIONAL PTE WRITE -- the write half of the fork's atomic A/D
     update, and the one the walk actually uses.  Same memory effect as the
     plain node (the interpreter routes by address and ignores the access
     kind); what differs is that [mem_write_value_priv_meta]'s (rl || con)
     alignment guard is LIVE.  The exec side splits into two lemmas for the
     same reason ([exec_write_pte_ram] / [_conditional_ram]), so this does
     too. *)
  Lemma swp_checked_mem_write_pte8_con (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64) (v : SailStdpp.Values.mword 64)
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (R : iProp Σ) (rr : option resv) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup htif_tohost_base rs = None ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec paddr 0)) 4)
      (uint pa) (uint (to_bits 64 8)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    pma_allows_ram pmar0 ->
    pma_ram_access pa 8 ->
    addr_is_ram pa ->
    is_aligned_paddr (Physaddr pa) 8 = true ->
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) pa 8
                   (Interface.WriteReq.value (mwrite_req8_con pa v)))
                σ.(mdev)) ∗ R)) -∗
    swp (checked_mem_write (Physaddr pa) 8 v (Store PageTableEntry) PBMT_PMA
           Supervisor tt false false true)
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R ∗
                resv_frag cpu_id None).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hpma Hpcfg Hpaddr Hhtif
      HA Hord Hrange HW Hpallow Hacc Hram Hpa.
    iIntros "#Hcert Hfrag Hrw Hro Hmem".
    rewrite /swp. iIntros (C) "%HC Hcont".
    unfold checked_mem_write.
    iApply (swp_use_cer
              (check_pma_with_pmp_priority (Store PageTableEntry) PBMT_PMA
                 Supervisor (Physaddr pa) 8 true) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 6 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_check_pma_wpte (Drw ∪ Dro) Drw rs pa pmar0 8 true
                   HDpma Hpma Hpallow Hacc Hpa) with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". spte_glue.
    rewrite mbind_ret. spte_glue.
    cbn [Phys_Mem_Access_Info_granule_size_exp Phys_Mem_Access_Info_splittable].
    cbn beta iota zeta delta [split_misaligned misaligned_order
      sys_misaligned_order_decreasing write_kind_of_flags].
    change (Instances.generic_eq CannotSplit CannotSplit) with true.
    spte_glue.
    rewrite /returnM mliftR_ret mbind_ret. spte_glue.
    rewrite mliftR_ret mbind_ret. spte_glue.
    cbn beta iota zeta delta [Defs.untilMT Defs.untilMT' Defs.Zwf_guarded
      Z_ge_dec Z_ge_lt_dec Zcompare_rec Z.compare].
    cbn beta iota zeta delta [Defs.assert_exp' bits_of_physaddr].
    rewrite mliftR_ret mbind_ret. spte_glue.
    change (0 * 8) with 0. rewrite avi0.
    iApply (swp_use_cer3
              (pmpCheck (Physaddr pa) 8 (Store PageTableEntry) Supervisor)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_pmpCheck_S (Store PageTableEntry) Drw Dro Df rs pcfg paddr
                pa 8 Hdisj HDcfg HDaddr Hpcfg Hpaddr HA Hord Hrange
                ltac:(unfold pmpCheckRWX; cbn match; rewrite HW; reflexivity)
                with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". spte_glue.
    rewrite mbind0_ret.
    iApply (swp_use_cer3 (within_mmio_writable (Physaddr pa) 8)
              _ _ _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 12 Drw Dro Df rs rs _ _ Hdisj
                (hfrun_within_mmio_w_ram (Drw ∪ Dro) Drw rs pa 8
                   ltac:(lia) HDhtif Hhtif Hram) with "Hcert Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro)". spte_glue.
    change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
    rewrite subrange_full_64 autocast_id.
    iApply (swp_use_cer4 (write_ram Write_RISCV_conditional (Physaddr pa) 8 v tt)
              _ _ _ _ _ C HC with "[Hrw Hro Hmem] [-]").
    { iApply (swp_hart_ram_write 8 (mwrite_req8_con pa v) _
                (fun r => (⌜r = true⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗
                           R ∗ resv_frag cpu_id None)%I)
                rr (hwrite_req_at_write_ram8_con pa v)
                (addr_is_ram_not_dev pa Hram) with "Hcert Hfrag [Hrw Hro Hmem]").
      iIntros (σ) "Hσ". iMod ("Hmem" $! σ with "Hσ") as "Hclose".
      iModIntro. iNext. iMod "Hclose" as "[Hσ HR]". iModIntro.
      iFrame "Hσ". iIntros "Hfrag".
      rewrite hwrite_resume_write_ram8_con. iApply swp_ret. by iFrame. }
    iIntros (v0) "(-> & Hrw & Hro & HR & Hfrag)". spte_glue.
    change (0 =? 1 - 1) with true. spte_glue.
    rewrite mbind_ret. spte_glue.
    rewrite mcer_ret.
    iApply ("Hcont" $! (Values.Ok true)). by iFrame.
  Qed.

  (* [write_pte] / [write_pte_conditional] on top of the nodes.
     [mem_write_value_priv]'s callback and meta drop are pure -- exactly the
     two steps [exec_write_pte_ram] / [_conditional_ram] reduce -- so each of
     these is that reduction with the checked write taken as an obligation. *)
  Lemma swp_write_pte_S (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (pa : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 64) (R : iProp Σ) :
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_write (Physaddr pa) 8 w (Store PageTableEntry) PBMT_PMA
              Supervisor tt false false false)
         (fun r => ⌜r = Values.Ok true⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)) -∗
    swp (write_pte (Physaddr pa) 8 (w : mword 64))
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    iIntros "#Hcert Hrw Hro Hcmw".
    unfold write_pte, mem_write_value_priv, mem_write_value_priv_meta.
    cbn [orb andb].
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok true⌝ ∗ hreg_frame rs Drw ∗
                         hreg_frame_ro Df rs Dro ∗ R)%I) _
              with "[Hrw Hro Hcmw] [-]").
    { iApply ("Hcmw" with "Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro & HR)". unfold mem_write_callback.
    iApply swp_ret. by iFrame.
  Qed.

  Lemma swp_write_pte_conditional_S (Drw Dro : gset register)
      (Df : register -> dfrac) (rs : regstate)
      (pa : SailStdpp.Values.mword 64)
      (w : SailStdpp.Values.mword 64) (R : iProp Σ) :
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (checked_mem_write (Physaddr pa) 8 w (Store PageTableEntry) PBMT_PMA
              Supervisor tt false false true)
         (fun r => ⌜r = Values.Ok true⌝ ∗
                   hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R)) -∗
    swp (write_pte_conditional (Physaddr pa) 8 (w : mword 64))
      (fun r => ⌜r = Values.Ok true⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro ∗ R).
  Proof.
    iIntros "#Hcert Hrw Hro Hcmw".
    unfold write_pte_conditional, mem_write_value_priv, mem_write_value_priv_meta.
    cbn [orb andb Riscv.rv64d.not negb].
    iApply (swp_bind_use _ _
              (fun r => (⌜r = Values.Ok true⌝ ∗ hreg_frame rs Drw ∗
                         hreg_frame_ro Df rs Dro ∗ R)%I) _
              with "[Hrw Hro Hcmw] [-]").
    { iApply ("Hcmw" with "Hrw Hro"). }
    iIntros (v0) "(-> & Hrw & Hro & HR)". unfold mem_write_callback.
    iApply swp_ret. by iFrame.
  Qed.

End ptewrite.

(* ===================================================================== *)
(* §2 The level-0 TLB fill with arbitrary arguments, and its              *)
(*    identification with [u_walk_entry] of the UPDATED leaf.             *)
(* ===================================================================== *)

(* the entry [add_to_TLB 39 asid vpn pp pte ptea 0 g] installs *)
Definition pt_fill_ent (asid : mword 16) (vpn : mword 27) (pp : mword 44)
    (pte : mword 64) (ptea : physaddr) (g : bool) : TLB_Entry :=
  {| TLB_Entry_asid := asid;
     TLB_Entry_global := g;
     TLB_Entry_pte := zero_extend' 64 pte;
     TLB_Entry_pteAddr := ptea;
     TLB_Entry_levelMask := zero_extend' (57 - 12) (ones 0 : mword 0);
     TLB_Entry_vpn := sign_extend' (57 - 12)
                        (and_vec vpn (not_vec (zero_extend' 27 (ones 0 : mword 0))));
     TLB_Entry_ppn := zero_extend' 44
                        (and_vec pp (not_vec (zero_extend' 44 (ones 0 : mword 0)))) |}.

Lemma exec_add_to_TLB_pt (asid : mword 16) (vpn : mword 27) (pp : mword 44)
    (pte : mword 64) (ptea : physaddr) (g : bool) s :
  exec (add_to_TLB 39 asid vpn pp pte ptea 0 g) s
  = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                               (tlb_hash (__id 39) vpn)
                               (Some (pt_fill_ent asid vpn pp pte ptea g)))).
Proof.
  unfold add_to_TLB. cbn zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb _)).
  rewrite exec_returnm.
  reflexivity.
Qed.

(* the fill built from the WALK's outputs (ppn/global of the OLD leaf)
   and the UPDATED pte word IS the walk entry of the updated leaf: an
   A/D variant has the same PPN and G bit *)
Lemma pt_fill_ent_uwe (vpn : mword 27) (p2 p1 p0 q : mword 64)
    (asid : mword 16) (a d : mword 1) :
  q = pte_set_ad p0 a d ->
  pt_fill_ent asid vpn
    (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44))
    (autocast (T := mword) q)
    (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)))
    (u_global p2 p1 p0)
  = u_walk_entry vpn p2 p1 q asid.
Proof.
  intros ->.
  unfold pt_fill_ent, u_walk_entry.
  f_equal;
    first
      [ rewrite pte_set_ad_ppn; reflexivity
      | unfold u_global, u_gbit; rewrite pte_set_ad_flag_G; reflexivity ].
Qed.

(* ===================================================================== *)
(* §3 The write-back translate.                                           *)
(* ===================================================================== *)

Section PtUpd.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  Lemma exec_translate_TLB_miss_pt_upd (vpn : mword 27) (root : mword 44)
        (p2 p1 p0 p0' : mword 64) (menvcfg0 : mword 64) (asid : mword 16)
        (sw : mstate) s :
    pte_valid p2 -> pte_ptr p2 ->
    pte_valid p1 -> pte_ptr p1 ->
    pte_valid p0 -> pte_leaf p0 -> pte_no_napot p0 ->
    pte_check_ok acc p mxr do_sum p0 ->
    update_PTE_Bits (p0 : mword 64) acc = Some p0' ->
    exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok p2, s) ->
    exec (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok p1, s) ->
    exec (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok p0, s) ->
    (* the fork's atomic update re-reads the PTE exclusively before writing *)
    exec (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok p0, s) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec (write_pte_conditional (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
            (p0' : mword 64)) s
      = Some (Ok true, sw) ->
    sw.(sregs) = s.(sregs) ->
    exec (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44), PBMT_PMA, tt),
            set_reg sw tlb (vec_update_dec (register_lookup tlb s.(sregs))
                              (tlb_hash (__id 39) vpn)
                              (Some (u_walk_entry vpn p2 p1 p0' asid)))).
  Proof.
    intros Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hchk Hupd
           Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv HPBMTE HADUE Hwrite Hswregs.
    unfold translate_TLB_miss. cbn zeta.
    match goal with |- context[pt_walk 39 _ _ _ _ _ _ ?l false ?e] =>
      change l with 2 end.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_user vpn root p2 p1 p0 acc p mxr do_sum
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk Hnap menvcfg0 s
                  Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
    cbn match. cbn zeta.
    (* THE FORK'S CHANGE, in full: the A/D update is an atomic read-check-write.
       After the Svadu/ADUE gate it re-reads the PTE with an EXCLUSIVE read,
       re-runs the tablewalk checks on the freshly read value ([check_leaf_pte],
       the same lemma the walk's leaf arm uses), recomputes the A/D bits on that
       value, and writes it back with a CONDITIONAL write.  Sequentially the
       re-read returns what the walk read, so every step agrees with the old
       single-write model -- which is exactly the observation that makes this
       change conservative for these proofs. *)
    match goal with |- context[update_and_write_pte ?w ?vp ?aa ?pv ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hu : exec (update_and_write_pte w vp aa pv lv ac pr mx ds e) s
                   = Some (Ok (Some p0', tt), sw)) end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
        assert (Hupd' : @update_PTE_Bits w pv ac = Some p0') by exact Hupd end.
      rewrite Hupd'.
      cbn match.
      match goal with |- context[Defs.bind (or_boolM ?A ?B) ?k] =>
        assert (Hgate : exec (or_boolM A B) s = Some (true, s)) end.
      { match goal with |- exec (or_boolM ?A ?B) s = _ =>
          assert (Hand : exec A s = Some (true, s)) end.
        { unfold and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)).
          cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
          cbn beta.
          rewrite Hmenv. rewrite HADUE.
          apply exec_returnm. }
        unfold or_boolM.
        rewrite (exec_bind_Some _ _ _ _ _ Hand).
        cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hgate).
      cbn match zeta.
      (* the exclusive re-read returns the value the walk read *)
      rewrite (exec_bind_Some _ _ _ _ _ Hrdx).
      cbn match beta.
      rewrite autocast_id.
      (* the re-check succeeds, on the same hypotheses the walk's leaf arm used *)
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_check_leaf_pte_leaf0 vpn p0 acc p mxr do_sum Hv0 Hl0 Hchk Hnap
                    (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)))
                    menvcfg0 s Hmisa Hmenv HPBMTE)).
      cbn match beta.
      rewrite Hupd'.
      cbn match.
      rewrite autocast_id.
      match goal with |- context[Defs.bind (write_pte_conditional ?aa' ?wd' ?pv') ?k] =>
        assert (Hwrite' : exec (write_pte_conditional aa' wd' pv') s = Some (Ok true, sw))
          by exact Hwrite end.
      rewrite (exec_bind_Some _ _ _ _ _ Hwrite').
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hu).
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_add_to_TLB_pt asid vpn _ _ _ _ sw)).
    rewrite exec_returnm.
    rewrite Hswregs.
    destruct (update_PTE_Bits_set_ad _ _ _ Hupd) as (a & d & Hq).
    match goal with |- context[pt_fill_ent ?asx ?vpx ?ppx ?ptx ?pax ?gx] =>
      assert (Hent : pt_fill_ent asx vpx ppx ptx pax gx
                     = u_walk_entry vpn p2 p1 p0' asid)
        by exact (pt_fill_ent_uwe vpn p2 p1 p0 p0' asid a d Hq) end.
    rewrite Hent.
    reflexivity.
  Qed.

End PtUpd.

(* ===================================================================== *)
(* §4 HIT + write-back: a cached entry whose word needs the A/D update    *)
(*    write-backs through its cached pteAddr and refreshes the entry in   *)
(*    place ([tlb_set_pte]).  The refreshed entry is the walk entry of    *)
(*    the updated word (PPN and G are A/D-stable).                        *)
(* ===================================================================== *)

Lemma tlb_set_pte_uwe (vpn : mword 27) (q2 q1 q0 q0' : mword 64)
    (asid : mword 16) (a d : mword 1) :
  q0' = pte_set_ad q0 a d ->
  tlb_set_pte (n := 8) (u_walk_entry vpn q2 q1 q0 asid) (q0' : mword 64)
  = u_walk_entry vpn q2 q1 q0' asid.
Proof.
  intros ->.
  unfold tlb_set_pte, u_walk_entry.
  cbn [TLB_Entry_asid TLB_Entry_global TLB_Entry_pte TLB_Entry_pteAddr
       TLB_Entry_levelMask TLB_Entry_vpn TLB_Entry_ppn].
  f_equal;
    first
      [ rewrite pte_set_ad_ppn; reflexivity
      | unfold u_global, u_gbit; rewrite pte_set_ad_flag_G; reflexivity
      | f_equal; symmetry; apply autocast_refl ].
Qed.

Section PtUpdHit.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (* THE FORK'S CHANGE ON THE HIT PATH, and it is not cosmetic here.  The
     cached word [q0] and the word in MEMORY [m0] agree only up to A/D (that is
     exactly what the TLB invariant promises).  The old model recomputed the
     A/D update on the CACHED word; the fork re-reads the PTE and recomputes on
     the MEMORY word, so the value written back -- and installed in the TLB --
     is derived from [m0], not from [q0].  The two lemmas below are the two
     ways that lands:

       [_upd]      [update_PTE_Bits m0] is [Some m0']: memory is written and
                   the entry is refreshed with [m0'];
       [_refresh]  [update_PTE_Bits m0] is [None] -- memory ALREADY has the
                   bits the cached copy lacks -- so nothing is written and the
                   entry is merely refreshed with [m0].

     The gate is still the cached word ([Hgate]): [update_and_write_pte] tests
     it before doing anything.  The returned PPN is the cached entry's either
     way, which is why both outcomes are invariant-absorbable. *)
  Lemma exec_translate_TLB_hit_pt_upd (vpn : mword 27) (q2 q1 q0 q0g m0 m0' : mword 64)
        (menvcfg0 : mword 64) (asid : mword 16) (idx : Z) (sw : mstate) s :
    pte_check_ok acc p mxr do_sum q0 ->
    update_PTE_Bits (q0 : mword 64) acc = Some q0g ->
    pte_pbmt0 q0 ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    (* the exclusive re-read, and the tablewalk checks re-run on ITS value *)
    exec (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok m0, s) ->
    pte_valid m0 -> pte_leaf m0 -> pte_no_napot m0 ->
    pte_check_ok acc p mxr do_sum m0 ->
    register_lookup misa s.(sregs) = MISA_C ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    (* the memory word is an A/D variant of the cached one: the TLB invariant *)
    (exists a2 d2 : mword 1, m0 = pte_set_ad q0 a2 d2) ->
    update_PTE_Bits (m0 : mword 64) acc = Some m0' ->
    exec (write_pte_conditional (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8
            (m0' : mword 64)) s
      = Some (Ok true, sw) ->
    sw.(sregs) = s.(sregs) ->
    exec (translate_TLB_hit 39 asid vpn acc p mxr do_sum tt idx
            (u_walk_entry vpn q2 q1 q0 asid)) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (q0 : mword 64))) : mword 44), PBMT_PMA, tt),
            set_reg sw tlb (vec_update_dec (register_lookup tlb s.(sregs)) idx
                              (Some (u_walk_entry vpn q2 q1 m0' asid)))).
  Proof.
    intros Hchk Hgate Hpb Hmenv HADUE Hrdx Hv0 Hl0 Hnap Hchkm Hmisa HPBMTE Hvar Hupd Hwrite Hswregs.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte.
    rewrite autocast_id.
    rewrite (exec_bind_Some _ _ _ _ _ (Hchk s)). cbn match.
    match goal with |- context[update_and_write_pte ?w ?vp ?aa ?pv ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hu : exec (update_and_write_pte w vp aa pv lv ac pr mx ds e) s
                   = Some (Ok (Some m0', tt), sw)) end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
        assert (Hgate' : @update_PTE_Bits w pv ac = Some q0g) by exact Hgate end.
      rewrite Hgate'.
      cbn match.
      match goal with |- context[Defs.bind (or_boolM ?A ?B) ?k] =>
        assert (Hgt : exec (or_boolM A B) s = Some (true, s)) end.
      { match goal with |- exec (or_boolM ?A ?B) s = _ =>
          assert (Hand : exec A s = Some (true, s)) end.
        { unfold and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)).
          cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
          cbn beta.
          rewrite Hmenv. rewrite HADUE.
          apply exec_returnm. }
        unfold or_boolM.
        rewrite (exec_bind_Some _ _ _ _ _ Hand).
        cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hgt).
      cbn match zeta.
      rewrite (exec_bind_Some _ _ _ _ _ Hrdx). cbn match beta.
      rewrite autocast_id.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_check_leaf_pte_leaf0 vpn m0 acc p mxr do_sum Hv0 Hl0 Hchkm Hnap
                    (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)))
                    menvcfg0 s Hmisa Hmenv HPBMTE)).
      cbn match beta.
      match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
        assert (Hupd' : @update_PTE_Bits w pv ac = Some m0') by exact Hupd end.
      rewrite Hupd'. cbn match. rewrite autocast_id.
      match goal with |- context[Defs.bind (write_pte_conditional ?aa' ?wd' ?pv') ?k] =>
        assert (Hwrite' : exec (write_pte_conditional aa' wd' pv') s = Some (Ok true, sw))
          by exact Hwrite end.
      rewrite (exec_bind_Some _ _ _ _ _ Hwrite').
      cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hu).
    cbn match.
    match goal with |- context[write_TLB ?ix ?en] =>
      assert (Hwt : exec (write_TLB ix en) sw
                    = Some (tt, set_reg sw tlb
                                  (vec_update_dec (register_lookup tlb sw.(sregs)) ix
                                     (Some en)))) end.
    { unfold write_TLB.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb sw)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ sw)).
      apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hwt).
    (* [m0'] is an A/D variant OF THE CACHED WORD, so the entry's PPN and G
       fields (which [tlb_set_pte] keeps) still agree with it *)
    destruct Hvar as (a2 & d2 & Hm0).
    destruct (update_PTE_Bits_set_ad _ _ _ Hupd) as (a & d & Hq).
    assert (Hqc : m0' = pte_set_ad q0 a d)
      by (rewrite Hq; rewrite Hm0; apply pte_set_ad_absorb).
    rewrite (exec_bind_Some _ _ _ _ _ (uwe_pbmt vpn q2 q1 q0 asid _ Hpb)).
    rewrite uwe_ppn.
    rewrite exec_returnm.
    rewrite Hswregs.
    match goal with |- context[tlb_set_pte ?en ?pv] =>
      assert (Hent : tlb_set_pte (n := 8) en pv = u_walk_entry vpn q2 q1 m0' asid)
        by exact (tlb_set_pte_uwe vpn q2 q1 q0 m0' asid a d Hqc) end.
    rewrite Hent.
    reflexivity.
  Qed.

  (* the re-read found the bits already set: no write, the entry is refreshed *)
  Lemma exec_translate_TLB_hit_pt_refresh (vpn : mword 27) (q2 q1 q0 q0g m0 : mword 64)
        (menvcfg0 : mword 64) (asid : mword 16) (idx : Z) s :
    pte_check_ok acc p mxr do_sum q0 ->
    update_PTE_Bits (q0 : mword 64) acc = Some q0g ->
    pte_pbmt0 q0 ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok m0, s) ->
    pte_valid m0 -> pte_leaf m0 -> pte_no_napot m0 ->
    pte_check_ok acc p mxr do_sum m0 ->
    register_lookup misa s.(sregs) = MISA_C ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    (exists a2 d2 : mword 1, m0 = pte_set_ad q0 a2 d2) ->
    update_PTE_Bits (m0 : mword 64) acc = None ->
    exec (translate_TLB_hit 39 asid vpn acc p mxr do_sum tt idx
            (u_walk_entry vpn q2 q1 q0 asid)) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (q0 : mword 64))) : mword 44), PBMT_PMA, tt),
            set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs)) idx
                             (Some (u_walk_entry vpn q2 q1 m0 asid)))).
  Proof.
    intros Hchk Hgate Hpb Hmenv HADUE Hrdx Hv0 Hl0 Hnap Hchkm Hmisa HPBMTE Hvar Hupd.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte.
    rewrite autocast_id.
    rewrite (exec_bind_Some _ _ _ _ _ (Hchk s)). cbn match.
    match goal with |- context[update_and_write_pte ?w ?vp ?aa ?pv ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hu : exec (update_and_write_pte w vp aa pv lv ac pr mx ds e) s
                   = Some (Ok (Some m0, tt), s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
        assert (Hgate' : @update_PTE_Bits w pv ac = Some q0g) by exact Hgate end.
      rewrite Hgate'.
      cbn match.
      match goal with |- context[Defs.bind (or_boolM ?A ?B) ?k] =>
        assert (Hgt : exec (or_boolM A B) s = Some (true, s)) end.
      { match goal with |- exec (or_boolM ?A ?B) s = _ =>
          assert (Hand : exec A s = Some (true, s)) end.
        { unfold and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)).
          cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
          cbn beta.
          rewrite Hmenv. rewrite HADUE.
          apply exec_returnm. }
        unfold or_boolM.
        rewrite (exec_bind_Some _ _ _ _ _ Hand).
        cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hgt).
      cbn match zeta.
      rewrite (exec_bind_Some _ _ _ _ _ Hrdx). cbn match beta.
      rewrite autocast_id.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_check_leaf_pte_leaf0 vpn m0 acc p mxr do_sum Hv0 Hl0 Hchkm Hnap
                    (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)))
                    menvcfg0 s Hmisa Hmenv HPBMTE)).
      cbn match beta.
      match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
        assert (Hupd' : @update_PTE_Bits w pv ac = None) by exact Hupd end.
      rewrite Hupd'. cbn match. rewrite ?autocast_id.
      apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hu).
    cbn match.
    match goal with |- context[write_TLB ?ix ?en] =>
      assert (Hwt : exec (write_TLB ix en) s
                    = Some (tt, set_reg s tlb
                                  (vec_update_dec (register_lookup tlb s.(sregs)) ix
                                     (Some en)))) end.
    { unfold write_TLB.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
      rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ s)).
      apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hwt).
    destruct Hvar as (a2 & d2 & Hm0).
    rewrite (exec_bind_Some _ _ _ _ _ (uwe_pbmt vpn q2 q1 q0 asid _ Hpb)).
    rewrite uwe_ppn.
    rewrite exec_returnm.
    match goal with |- context[tlb_set_pte ?en ?pv] =>
      assert (Hent : tlb_set_pte (n := 8) en pv = u_walk_entry vpn q2 q1 m0 asid)
        by exact (tlb_set_pte_uwe vpn q2 q1 q0 m0 asid a2 d2 Hm0) end.
    rewrite Hent.
    reflexivity.
  Qed.

End PtUpdHit.

(* ===================================================================== *)
(* §5 The translateAddr FRONT MATTER, factored once over an arbitrary     *)
(*    successful [translate] outcome: mstatus/priv reads, Sv39 dispatch,  *)
(*    canonicality, satp -> root/asid, and the pa concatenation.  Every   *)
(*    outcome arm (no-update / walk fill / write-back, PtTree §8e and     *)
(*    this file) composes with this head.  PRIVILEGE-GENERIC: the         *)
(*    privilege-specific ingredients (cur_privilege read, effective       *)
(*    privilege, the Sv39 mode dispatch) are premises -- Supervisor       *)
(*    callers discharge [Htm] with [exec_translationMode_S_sv39], User    *)
(*    callers with [exec_translationMode_U_sv39] (UserTranslate.v).       *)
(* ===================================================================== *)

Section PtFront.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  Lemma exec_translateAddr_pt_front (vpn : mword 27) (root : mword 44)
        (ppnv : mword 44) (satp0 va pa : mword 64) (s s' : mstate) :
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) p) s
      = Some (p, s) ->
    exec (is_shadow_stack_access acc) s = Some (false, s) ->
    register_lookup cur_privilege s.(sregs) = p ->
    exec (translationMode p) s = Some (Sv39, s) ->
    register_lookup satp s.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    (forall mxr do_sum,
       exec (translate 39 (mword_of_int 0 : mword 16) root vpn acc p mxr do_sum tt) s
       = Some (Ok (ppnv, PBMT_PMA, tt), s')) ->
    zero_extend' 64 (concat_vec ppnv
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s').
  Proof.
    intros Heff Hss Hcp Htm Hsatp Hppn Hasid Hcanon Hvpn_def Htr Hident.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ Heff).
    rewrite (execR_liftR_seq _ _ _ _ _ Htm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hss).
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
      replace bppn with root by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _ (Htr _ _)).
    cbn match.
    rewrite execR_returnR. cbn match.
    match goal with |- context[Physaddr ?e] =>
      replace e with pa by (symmetry; exact Hident) end.
    reflexivity.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* THE SAME HEAD AT THE SWP LAYER.  Nothing about the translation moves: *)
  (* the register reads become frame reads, the three monadic ingredients  *)
  (* (effective privilege, shadow-stack, mode) are carried across by the   *)
  (* [goodb] bridge -- so each arrives as ITS EXEC PREMISE PLUS a          *)
  (* certificate, discharged where the exec one already is -- and the      *)
  (* [translate] premise becomes the caller's OBLIGATION, which is the one  *)
  (* thing that has to change: the walk it stands for reads memory and      *)
  (* writes the TLB, so it may land on a DIFFERENT FILE.                    *)
  (* ------------------------------------------------------------------ *)
  Lemma swp_translateAddr_pt_front (Drw Dro : gset register)
      (Df : register -> dfrac) (rs rsf : regstate) (dst : mstate)
      (Db : register -> bool) (vpn : mword 27) (root : mword 44)
      (ppnv : mword 44) (satp0 va pa : mword 64) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    register_lookup cur_privilege rs = p ->
    register_lookup satp rs = satp0 ->
    register_lookup mstatus rs = register_lookup mstatus dst.(sregs) ->
    (* the three monadic ingredients: exec fact + footprint certificate *)
    exec (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) p) dst
      = Some (p, dst) ->
    goodb Db (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) p)
      dst = true ->
    exec (is_shadow_stack_access acc) dst = Some (false, dst) ->
    goodb Db (is_shadow_stack_access acc) dst = true ->
    exec (translationMode p) dst = Some (Sv39, dst) ->
    goodb Db (translationMode p) dst = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64))
      = root ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)
      (Z.sub 39 1) pagesize_bits) = vpn ->
    zero_extend' 64 (concat_vec ppnv
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
         (Z.sub pagesize_bits 1) 0)) = pa ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ mxr do_sum : bool,
       hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
       swp (translate 39 (mword_of_int 0 : mword 16) root vpn acc p mxr do_sum tt)
         (fun r => ⌜r = Values.Ok (ppnv, PBMT_PMA, tt)⌝ ∗
                   hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro)) -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro).
  Proof.
    intros Hdisj HDmst HDpriv HDsatp HDb Hag Hcp Hsatp Hmstag
      Heff Heffg Hss Hssg Htm Htmg Hppn Hasid Hcanon Hvpn_def Hident.
    iIntros "#Hcert Hrw Hro Htr".
    unfold translateAddr.
    rewrite /swp. iIntros (C) "%HC Hcont".
    (* mstatus, then cur_privilege *)
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg cur_privilege) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDpriv
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". rewrite Hcp.
    (* the three carried ingredients *)
    rewrite Hmstag.
    iApply (swp_use_cer
              (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) p)
              _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw _ dst rs _ HDb Hag Heffg Heff)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (translationMode p) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw _ dst rs _ HDb Hag Htmg Htm)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (is_shadow_stack_access acc) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_span Drw Dro Df rs rs _ _ Hdisj
                (hval_of_goodb Db (Drw ∪ Dro) Drw _ dst rs _ HDb Hag Hssg Hss)
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    (* not a shadow-stack access, and the mode is not Bare *)
    (* not a shadow-stack access, and the mode is not Bare: both tests are
       already decided by the values the peels returned *)
    cbn match. rewrite mbind0_ret.
    (* the width is a constant *)
    replace (satp_mode_width_forwards Sv39)
      with (Defs.returnm (E := exception) 39) by (cbn; reflexivity).
    rewrite mliftR_ret mbind_ret. cbn beta.
    (* satp, through [get_satp]'s assert.  Small closed stretch, so the
       narrow whitelist is enough -- the only node is the satp read. *)
    assert (Hgs : hfrun 3 (Drw ∪ Dro) Drw rs (get_satp 39)
                  = Some (autocast (T := mword) satp0, rs)).
    { unfold get_satp.
      replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true
        by (vm_compute; reflexivity).
      cbn beta iota zeta delta [Defs.assert_exp' Defs.bind
        Interface.iMon_bind Defs.read_reg Defs.returnm returnM autocast_m].
      rewrite hfrun_read (bool_decide_eq_true_2 _ HDsatp).
      rewrite Hsatp.
      cbn beta iota zeta delta [Defs.returnm returnM autocast].
      apply hfrun_ret. }
    iApply (swp_use_cer (get_satp 39) _ _ C HC with "[Hrw Hro] [-]").
    { iApply (swp_hfrun 3 Drw Dro Df rs rs _ _ Hdisj Hgs
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true
      by (vm_compute; reflexivity).
    unfold Defs.assert_exp'. cbn match. rewrite mliftR_ret.
    rewrite mbind_ret. cbn beta zeta.
    rewrite Hcanon. cbn match.
    (* mxr and do_sum, both off mstatus *)
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    iApply (swp_use_cer (Defs.read_reg mstatus) _ _ C HC
              with "[Hrw Hro] [-]").
    { iApply (swp_read_reg_pinned Drw Dro Df rs _ Hdisj HDmst
                with "Hcert Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)".
    (* THE WALK, as the caller's obligation *)
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace bppn with root by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16)
        by (symmetry; exact Hasid) end.
    iApply (swp_use_cer (translate 39 (mword_of_int 0 : mword 16) root vpn acc p
                           _ _ tt) _ _ C HC with "[Hrw Hro Htr] [-]").
    { iApply ("Htr" with "Hrw Hro"). }
    iIntros (v) "(-> & Hrw & Hro)". cbn match.
    rewrite mcer_ret.
    match goal with |- context[Physaddr ?e] =>
      replace e with pa by (symmetry; exact Hident) end.
    iApply ("Hcont" $! (Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw))).
    by iFrame.
  Qed.

  (* the same head over a FAILED [translate] outcome: the PTW error maps
     through [translationException] and surfaces as the page-fault
     exception, state unchanged (fault walks write nothing). *)
  Lemma exec_translateAddr_pt_front_err (vpn : mword 27) (root : mword 44)
        (f : PTW_Error) (e : ExceptionType) (satp0 va : mword 64) (s : mstate) :
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) p) s
      = Some (p, s) ->
    exec (is_shadow_stack_access acc) s = Some (false, s) ->
    register_lookup cur_privilege s.(sregs) = p ->
    exec (translationMode p) s = Some (Sv39, s) ->
    register_lookup satp s.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    (forall mxr do_sum,
       exec (translate 39 (mword_of_int 0 : mword 16) root vpn acc p mxr do_sum tt) s
       = Some (Err (f, tt), s)) ->
    exec (translationException acc f) s = Some (e, s) ->
    exec (translateAddr (Virtaddr va) acc) s
    = Some (Err (e, tt), s).
  Proof.
    intros Heff Hss Hcp Htm Hsatp Hppn Hasid Hcanon Hvpn_def Htr Hte.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ Heff).
    rewrite (execR_liftR_seq _ _ _ _ _ Htm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hss).
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
      replace bppn with root by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _ (Htr _ _)).
    cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ Hte).
    rewrite execR_returnR. cbn match.
    reflexivity.
  Qed.

  (* NON-CANONICAL va: the fault fires at the canonicality test, before
     the TLB or any memory read -- no satp geometry needed beyond the
     mode dispatch. *)
  Lemma exec_translateAddr_pt_front_noncanon (f := PTW_Invalid_Addr tt)
        (e : ExceptionType) (satp0 va : mword 64) (s : mstate) :
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) p) s
      = Some (p, s) ->
    exec (is_shadow_stack_access acc) s = Some (false, s) ->
    register_lookup cur_privilege s.(sregs) = p ->
    exec (translationMode p) s = Some (Sv39, s) ->
    register_lookup satp s.(sregs) = satp0 ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true ->
    exec (translationException acc (PTW_Invalid_Addr tt)) s = Some (e, s) ->
    exec (translateAddr (Virtaddr va) acc) s
    = Some (Err (e, tt), s).
  Proof.
    intros Heff Hss Hcp Htm Hsatp Hcanon Hte.
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ Heff).
    rewrite (execR_liftR_seq _ _ _ _ _ Htm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hss).
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
    rewrite (execR_liftR_seq _ _ _ _ _ Hte).
    rewrite execR_returnR. cbn match.
    reflexivity.
  Qed.

End PtFront.

(* ===================================================================== *)
(* §6 Iris: writing the leaf slot (the ghost side of the write-back).     *)
(* ===================================================================== *)

(* the PMA table serves 8-byte PTE writes everywhere (mirror of KptPt's
   [pma_allows_pte_read]; holds for the boot table, which allows all) *)
Definition pma_allows_pte_write (regions : list PMA_Region) : Prop :=
  forall (a : mword 64),
    pma_ram_access a 8 ->
    exists r,
    matching_pma_region regions (Physaddr a) 8 = Some r /\
    (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_supports_pte_write) = true.

(* the platform table serves 8-byte PTE writes AT A RAM ADDRESS: a direct
   projection now that [pma_allows_ram] pins [PMA_supports_pte_write].  See
   KptPt's read twin for why the RAM restriction is the honest statement. *)
Lemma pma_allows_all_pte_write (pmar0 : list PMA_Region) :
  pma_allows_all pmar0 -> pma_allows_pte_write pmar0.
Proof.
  intros H a Hram.
  destruct (pma_all_ram H a 8 Hram) as (r & Hm & _ & _ & _ & _ & _ & Hpw & _).
  exists r. split; [exact Hm | exact Hpw].
Qed.

Section PtWriteIris.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* update an owned 8-byte slot to a new word, in step with the model's
     [write_bytes] memory update *)
  Lemma phys_word_pointsto_write (mm : _) (a : Arch.pa)
      (vold vnew : mword 64) :
    gen_heap_interp (hG := riscv_memGS) mm -∗ a ↦ₚ₈ vold ==∗
    gen_heap_interp (hG := riscv_memGS) (write_bytes mm a 8 vnew) ∗ a ↦ₚ₈ vnew.
  Proof.
    iIntros "Hm Hw".
    iDestruct (phys_word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (phys_word_pointsto_bytes with "Hw") as "Hb".
    iMod (upd_window_8 mm a vnew vold with "Hm Hb") as "[Hm Hb]".
    iModIntro. iFrame "Hm".
    iApply phys_word_pointsto_intro; [exact Hal |].
    iExact "Hb".
  Qed.

End PtWriteIris.
