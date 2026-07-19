(* PtTreeAdue.v -- the Svadu/ADUE WRITE-BACK arm of the page-table-tree
   translation (PtTree.v).  Under this build menvcfg.ADUE = 1, so an
   access whose leaf lacks the A bit (or D, for stores) does NOT fault:
   the walk WRITES the A/D-updated PTE back to the leaf slot and installs
   the updated word in the TLB.  Because the leaf slot is owned by the
   table invariant ([ptree_own]) and the updated word is an A/D VARIANT
   of the old one ([update_PTE_Bits_set_ad]), the invariant absorbs the
   write: [ptree_own_path_upd] reseals the ownership at
   [ptree_set_leaf], [tlb_ok_pt_fill]/[tlb_ok_pt_set_leaf] reseal the
   TLB consistency, and an instance spec like [kpt_tree_spec] survives
   by [kpt_tree_spec_set_leaf].  Clients of the invariant never see the
   memory change.

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
        the three-way [exec_translate_pt_upd] (miss arms; a HIT that
        needs an update also write-backs and refreshes the entry --
        worklisted, see iris/CLAUDE.md).                                 *)
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
Require Import WpMmodeLeafBase.
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
  exec (pmaCheck (Physaddr addr) 8 (Store PageTableEntry) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hwrite.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hwrite |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:108.61-108.62" >>=
          (fun _ : true = true => returnM (PMA_supports_pte_write (override_PMA rattr pbmt))))
    with (returnM (PMA_supports_pte_write (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hwrite. cbn match.
  apply exec_returnM.
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
  { unfold checked_mem_write.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
    2:{ unfold phys_access_check.
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_pmpCheck_supervisor_grant_wpte a 8 s HA Hord Hrange HW)).
        cbn match.
        rewrite (exec_bind_Some _ _ _ _ _
                   (exec_pmaCheck_ram_wpte a PBMT_PMA region s Hmatch Halign Hwr)).
        cbn match. apply exec_returnM. }
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (within_mmio_writable (Physaddr a) 8) s = Some (false, s))).
    2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
        rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
        rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (write_kind_of_flags false false false) s
                   = Some (rv64d_types.Write_plain, s))).
    2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_8 a w' s Hdev)).
    apply exec_returnM. }
  unfold write_pte, mem_write_value_priv, mem_write_value_priv_meta.
  cbn [orb andb].
  rewrite (exec_bind_Some _ _ _ _ _ Hchk).
  cbn match. unfold mem_write_callback. apply exec_returnM.
Qed.

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
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec (write_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
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
           Hrd2 Hrd1 Hrd0 Hmisa Hmenv HPBMTE HADUE Hwrite Hswregs.
    unfold translate_TLB_miss. cbn zeta.
    match goal with |- context[pt_walk 39 _ _ _ _ _ _ ?l false ?e] =>
      change l with 2 end.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_user vpn root p2 p1 p0 acc p mxr do_sum
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk Hnap menvcfg0 s
                  Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
    cbn match. cbn zeta.
    match goal with |- context[update_and_write_pte ?aa ?wd ?pv ?ac] =>
      assert (Hu : exec (update_and_write_pte aa wd pv ac) s = Some (Ok (Some p0'), sw)) end.
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
      cbn match.
      match goal with |- context[Defs.bind (write_pte ?aa' ?wd' ?pv') ?k] =>
        assert (Hwrite' : exec (write_pte aa' wd' pv') s = Some (Ok true, sw))
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

  Lemma exec_translate_TLB_hit_pt_upd (vpn : mword 27) (q2 q1 q0 q0' : mword 64)
        (menvcfg0 : mword 64) (asid : mword 16) (idx : Z) (sw : mstate) s :
    pte_check_ok acc p mxr do_sum q0 ->
    update_PTE_Bits (q0 : mword 64) acc = Some q0' ->
    pte_pbmt0 q0 ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec (write_pte (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8
            (q0' : mword 64)) s
      = Some (Ok true, sw) ->
    sw.(sregs) = s.(sregs) ->
    exec (translate_TLB_hit 39 asid vpn acc p mxr do_sum tt idx
            (u_walk_entry vpn q2 q1 q0 asid)) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (q0 : mword 64))) : mword 44), PBMT_PMA, tt),
            set_reg sw tlb (vec_update_dec (register_lookup tlb s.(sregs)) idx
                              (Some (u_walk_entry vpn q2 q1 q0' asid)))).
  Proof.
    intros Hchk Hupd Hpb Hmenv HADUE Hwrite Hswregs.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte.
    rewrite autocast_id.
    rewrite (exec_bind_Some _ _ _ _ _ (Hchk s)). cbn match.
    match goal with |- context[update_and_write_pte ?aa ?wd ?pv ?ac] =>
      assert (Hu : exec (update_and_write_pte aa wd pv ac) s = Some (Ok (Some q0'), sw)) end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
        assert (Hupd' : @update_PTE_Bits w pv ac = Some q0') by exact Hupd end.
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
      cbn match.
      match goal with |- context[Defs.bind (write_pte ?aa' ?wd' ?pv') ?k] =>
        assert (Hwrite' : exec (write_pte aa' wd' pv') s = Some (Ok true, sw))
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
    destruct (update_PTE_Bits_set_ad _ _ _ Hupd) as (a & d & Hq).
    rewrite (exec_bind_Some _ _ _ _ _ (uwe_pbmt vpn q2 q1 q0 asid _ Hpb)).
    rewrite uwe_ppn.
    rewrite exec_returnm.
    rewrite Hswregs.
    match goal with |- context[tlb_set_pte ?en ?pv] =>
      assert (Hent : tlb_set_pte (n := 8) en pv = u_walk_entry vpn q2 q1 q0' asid)
        by exact (tlb_set_pte_uwe vpn q2 q1 q0 q0' asid a d Hq) end.
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
  forall (a : mword 64), exists r,
    matching_pma_region regions (Physaddr a) 8 = Some r /\
    (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_supports_pte_write) = true.

Section PtWriteIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* update an owned 8-byte slot to a new word, in step with the model's
     [write_bytes] memory update *)
  Lemma word_pointsto_write (mm : _) (a : Arch.pa)
      (vold vnew : mword 64) :
    gen_heap_interp (hG := riscv_memGS) mm -∗ a ↦₈ vold ==∗
    gen_heap_interp (hG := riscv_memGS) (write_bytes mm a 8 vnew) ∗ a ↦₈ vnew.
  Proof.
    iIntros "Hm Hw".
    iDestruct (word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (word_pointsto_bytes with "Hw") as "Hb".
    iMod (upd_window_8 mm a vnew vold with "Hm Hb") as "[Hm Hb]".
    iModIntro. iFrame "Hm".
    iApply word_pointsto_intro; [exact Hal |].
    iExact "Hb".
  Qed.

End PtWriteIris.
