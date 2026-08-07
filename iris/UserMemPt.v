(* UserMemPt.v -- the U-mode DATA-memory machinery over the ptree user
   table: physical loads and stores against the owned data pages
   ([udata_own]), composed with the U-mode translation absorption
   (UserPtTree.v).  This is the layer the LOAD/STORE step arms consume.

   The whole development is GENERIC in the access width [k] (a positive
   divisor of the page size, at most 8): §5's Section closes over [k]
   and the two width-TYPED plain-RAM bricks (the only places the
   dependent value type [mword (8*k)] resists abstraction -- the
   [cast_N] inside [sail_mem_read]); §6 instantiates the composers at
   the four RV64 access widths with the concrete bricks.

   Layers:
     §1 the width-generic page-window lemma;
     §2 the U-mode PMP TOR entry-0 grants (width-generic already);
     §3 the width-generic pma checks for data reads and writes;
     §4 the per-width plain-RAM bricks (read_1 and write_1/2/4 local;
        read_2/4 from RiscvFetchExec, read_8 from WpLoad, write_8 from
        WpMmodeLeafBase);
     §5 THE GENERIC SECTION: physical read/write chains at User, the
        ghost side (word out of the existential bytes; store update),
        and the invariant-level composers;
     §6 the width instances (the names the memory arms consume).        *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte.
Require Import CommonWalk.
Require Import SmodeCore.
Require Import UptTree.
Require Import UserPtTree.
Require Import UserBits.
Require Import WpMmodeLeafBase.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import MemAccessGen.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The width-generic page window (bounds in UserBits.v).                *)
(* ===================================================================== *)

Lemma u_walk_pa_window_div (k : Z) (pte0 : mword 64) (va : mword 64) (j : nat) :
  0 < k -> (k | 4096) ->
  is_aligned_vaddr (Virtaddr va) k = true ->
  (j < Z.to_nat k)%nat ->
  pa_add (u_walk_pa pte0 va) j = u_walk_pa pte0 (add_vec_int va (Z.of_nat j)).
Proof.
  intros Hk Hdvd Hal Hj.
  pose proof (off_bound_div va k Hk Hdvd Hal) as Hb.
  exact (pa_window _ va j ltac:(lia)).
Qed.

(* ===================================================================== *)
(* §2 The U-mode PMP TOR entry-0 grants for data accesses.                 *)
(* ===================================================================== *)

Lemma exec_pmpCheck_user_grant_load (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Load Data) User) s = Some (None, s).
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

Lemma exec_pmpCheck_user_grant_store (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (Store Data) User) s = Some (None, s).
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

(* ===================================================================== *)
(* §3 The width-generic pma checks (the width is never scrutinized).       *)
(* ===================================================================== *)



(* ===================================================================== *)
(* §4 The per-width plain-RAM bricks -- the only width-TYPED pieces.       *)
(* ===================================================================== *)

Lemma is_aligned_vaddr_1 (va : mword 64) :
  is_aligned_vaddr (Virtaddr va) 1 = true.
Proof.
  unfold is_aligned_vaddr. apply Z.eqb_eq. apply Z.rem_1_r.
Qed.

Lemma run_read_ram_plain_1_pin (addr : mword 64) (w : bv 8) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 1)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  run (read_ram Read_plain (Physaddr addr) 1 false) s (w, default_meta) s.
Proof.
  intros Hdev Hbytes.
  unfold read_ram. cbn match.
  apply (proj2 (run_bind _ _ _ _ _)).
  eexists _, s. split; [ apply run_returnM_fwd | ]. cbn beta zeta.
  apply (proj2 (run_bind _ _ _ _ _)).
  unfold Defs.sail_mem_read. cbn beta zeta.
  eexists _, s. split.
  - eapply run_MemRead_ram_intro.
    + exact Hdev.
    + intros j Hj. exact (Hbytes j Hj).
    + apply run_returnM_fwd.
  - cbn match beta. apply run_returnM_fwd.
Qed.

Lemma exec_read_ram_plain_1 (addr : mword 64) (w : bv 8) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 1)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram Read_plain (Physaddr addr) 1 false) s = Some ((w, default_meta), s).
Proof.
  intros Hdev Hbytes.
  apply (run_to_exec _ _ _ _ (run_read_ram_plain_1_pin addr w s Hdev Hbytes)).
  unfold read_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_read. cbn beta zeta.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  rewrite exec_MemRead; last exact Hdev.
  cbn [Interface.ReadReq.pa].
  case_match eqn:Hrb.
  - cbn [Interface.iMon_bind]. cbn match beta iota. discriminate.
  - exfalso.
    refine (read_bytes_ne (mem s) addr (Z.to_N 1) w _ Hrb).
    intros j Hj.
    change (RiscvModelBytes.pa_add addr j) with (pa_add addr j).
    change (RiscvModelBytes.nth_byte w j) with (nth_byte w j).
    exact (Hbytes j Hj).
Qed.




(* ===================================================================== *)
(* §4b The width-free ghost window update (a store re-picks the           *)
(*     existential byte map; dom unchanged -- every address covered).     *)
(* ===================================================================== *)

Section UserMemPtGhost.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma udata_own_upd (data : gset Arch.pa) (l : list nat) (pa : Arch.pa)
        {wd : N} (v : bv wd) (m : _) :
      (forall j, j ∈ l -> pa_add pa j ∈ data) ->
      gen_heap_interp (hG := riscv_memGS) m -∗ udata_own data ==∗
      gen_heap_interp (hG := riscv_memGS)
        (foldr (fun j acc => <[pa_add pa j := nth_byte v j]> acc) m l) ∗
      udata_own data.
    Proof.
      iIntros (Hin) "Hm Hdata".
      iInduction l as [|x xs] "IH" forall (m).
      - cbn [foldr]. iModIntro. iFrame.
      - iMod ("IH" with "[] Hm Hdata") as "[Hm Hdata]".
        { iPureIntro. intros j Hj. apply Hin. apply elem_of_cons. right. exact Hj. }
        iDestruct "Hdata" as (dm) "[%Hdom Hbytes]".
        assert (Hmem : pa_add pa x ∈ dom dm).
        { rewrite Hdom. apply Hin. apply elem_of_cons. left. reflexivity. }
        apply elem_of_dom in Hmem. destruct Hmem as [b Hb].
        iDestruct (big_sepM_insert_acc _ _ _ _ Hb with "Hbytes") as "[Hab Hrest]".
        iMod (phys_update _ (pa_add pa x) b (nth_byte v x) with "Hm Hab") as "[Hm Hab]".
        iDestruct ("Hrest" $! (nth_byte v x) with "Hab") as "Hbytes".
        iModIntro.
        cbn [foldr]. iFrame "Hm".
        iExists (<[pa_add pa x := nth_byte v x]> dm).
        iFrame "Hbytes". iPureIntro.
        rewrite dom_insert_L Hdom.
        apply subseteq_union_1_L.
        apply singleton_subseteq_l.
        rewrite <- Hdom. exact (elem_of_dom_2 _ _ _ Hb).
    Qed.

End UserMemPtGhost.

(* ===================================================================== *)
(* §5 THE GENERIC DEVELOPMENT: everything above the plain bricks, over an  *)
(*    abstract access width [k].                                           *)
(* ===================================================================== *)

Section UserMemPtGeneric.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)).
  Context (Huintk : uint (to_bits 64 k) = k).
  (* the two width-TYPED plain-RAM bricks *)
  Context (Hread_plain : forall (addr : mword 64) (w : mword (8 * k)) s,
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
      exec (read_ram Read_plain (Physaddr addr) k false) s = Some ((w, default_meta), s)).
  Context (Hwrite_plain : forall (addr : mword 64) (data : mword (8 * k)) s,
      dev_addr addr = false ->
      exec (write_ram rv64d_types.Write_plain (Physaddr addr) k data tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev))).

  Lemma exec_checked_mem_read_ram_U (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    exec (within_clint (Physaddr addr) k) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) k) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (checked_mem_read (Load Data) pbmt User (Physaddr addr) k false false false false)
         s = Some (Ok (w, default_meta), s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
    assert (Hcp : exec (check_pma_with_pmp_priority (Load Data) pbmt User
                          (Physaddr addr) k false) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_load_g k addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
    assert (Hmmio : exec (within_mmio_readable (Physaddr addr) k) s = Some (false, s)).
    { unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    unfold checked_mem_read. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr k 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    assert (Hrkf : exec (read_kind_of_flags false false false) s
                   = Some (rv64d_types.Read_plain, s))
      by (unfold read_kind_of_flags; apply exec_returnM).
    rewrite (execR_liftR_seq _ _ _ _ _ Hrkf). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (w, true, 0), s)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * k) = addr)
        by (assert (H0 : (0 * k)%Z = 0) by lia; rewrite H0; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_load addr k s HA Hord Hrange HR)).
      cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
        assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite Hmmio. reflexivity. }
      rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?ad ?wd ?mt)) ?k1) _] =>
        assert (Hrdr : execR (Defs.bind (Defs.liftR (read_ram rk ad wd mt)) k1) s
                       = Some (inr w, s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (Hread_plain addr w s Hdev Hbytes)).
        cbn beta match. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hrdr). cbn beta zeta.
      change (update_subrange_vec_dec (zeros' (8 * 1 * k))
                (8 * (0 + 1) * k - 1) (8 * 0 * k) (autocast w))
        with (update_subrange_vec_dec (zeros' (8 * k)) (8 * k - 1) 0
                (autocast (T := mword) w)).
      rewrite (usvd_zeros_full_gen (8 * k) w ltac:(lia)).
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. kill_autocast. reflexivity.
  Qed.

  Lemma exec_mem_read_data_U (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    exec (within_clint (Physaddr addr) k) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) k) s = Some (false, s) ->
    exec (within_htif_readable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (mem_read (Load Data) pbmt (Physaddr addr) k false false false)
         s = Some (Ok w, s).
  Proof.
    intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes Hmprv Hpriv.
    unfold mem_read.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_effectivePrivilege_mprv0 (Load Data) _ _ s Hmprv)).
    rewrite Hpriv.
    unfold mem_read_priv.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (mem_read_priv_meta _ _ _ _ k _ _ _ _) s = Some (Ok (w, default_meta), s))).
    2:{ unfold mem_read_priv_meta. cbn [orb andb].
        rewrite (exec_bind_Some _ _ _ _ _
                  (_ : exec (checked_mem_read _ _ _ _ k _ _ _ _) s = Some (Ok (w, default_meta), s))).
        2:{ cbn match. apply exec_checked_mem_read_ram_U with (region := region); assumption. }
        cbn match. unfold mem_read_callback. apply exec_returnM. }
    cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
  Qed.

  Lemma exec_checked_mem_write_ram_U (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (within_clint (Physaddr addr) k) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) k) s = Some (false, s) ->
    exec (within_htif_writable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    exec (checked_mem_write (Physaddr addr) k data (Store Data) pbmt User tt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev.
    assert (Hcp : exec (check_pma_with_pmp_priority (Store Data) pbmt User
                          (Physaddr addr) k false) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_store_g k addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
    assert (Hmmio : exec (within_mmio_writable (Physaddr addr) k) s = Some (false, s)).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
    set (sw := MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr k 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    assert (Hwkf : exec (write_kind_of_flags false false false) s
                   = Some (rv64d_types.Write_plain, s))
      by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwkf). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0, true), sw)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * k) = addr)
        by (assert (H0 : (0 * k)%Z = 0) by lia; rewrite H0; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_store addr k s HA Hord Hrange HW)).
      cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
      change (autocast (T := mword)
                (subrange_vec_dec data (8 * (0 + 1) * k - 1) (8 * 0 * k))
              : mword (8 * k))
        with (autocast (T := mword) (subrange_vec_dec data (8 * k - 1) 0)
              : mword (8 * k)).
      rewrite (subrange_full_gen_cast (8 * k) data ltac:(lia)).
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?ad ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk ad wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (Hwrite_plain addr data s Hdev)).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity.
  Qed.

  Lemma exec_mem_write_value_U (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    exec (within_clint (Physaddr addr) k) s = Some (false, s) ->
    exec (within_sig (Physaddr addr) k) s = Some (false, s) ->
    exec (within_htif_writable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (mem_write_value (Physaddr addr) k data (Store Data) pbmt false false false) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev Hmprv Hpriv.
    unfold mem_write_value, mem_write_value_meta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_effectivePrivilege_mprv0 (Store Data) _ _ s Hmprv)).
    rewrite Hpriv.
    unfold mem_write_value_priv_meta. cbn [orb andb].
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_checked_mem_write_ram_U pbmt addr region data s
                 HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
    cbn match. unfold mem_write_callback. apply exec_returnm.
  Qed.

  (* a k-window of a mapped page, out of the existential bytes *)
  Lemma udata_read_word_g (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ' : mstate) :
    um !! svpn_of va = Some w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    gen_heap_interp σ'.(mem) -∗ udata_own data -∗
    ⌜exists dv : mword (8 * k),
       (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
          σ'.(mem) !! pa_add (u_walk_pa w va) j = Some (nth_byte dv j))
       /\ addr_is_ram (u_walk_pa w va)
       /\ addr_is_ram (pa_add (u_walk_pa w va) (Z.to_nat k - 1))⌝.
  Proof.
    iIntros (Hl Hcov Hal) "Hmem Hdata".
    iDestruct "Hdata" as (dm) "[%Hdom Hbytes]".
    set (pa := u_walk_pa w va).
    assert (Hin : forall j : nat, (j < Z.to_nat k)%nat -> pa_add pa j ∈ dom dm).
    { intros j Hj. rewrite Hdom.
      unfold pa. rewrite (u_walk_pa_window_div k _ _ _ Hk Hkdvd Hal Hj).
      exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl). }
    assert (Hex : forall j : nat, (j < Z.to_nat k)%nat ->
              exists b, dm !! pa_add pa j = Some b).
    { intros j Hj. apply elem_of_dom. apply Hin. exact Hj. }
    destruct (bytes_list_of_lookups (fun j => dm !! pa_add pa j) (Z.to_nat k) Hex)
      as (bs & Hlen & Hbs).
    set (dv := (Z_to_bv _ (assemble_bytes bs) : mword (8 * k))).
    assert (Hnb : forall j : nat, (j < Z.to_nat k)%nat -> nth_byte dv j = bs !!! j).
    { intros j Hj. apply nth_byte_assemble_len; [ | lia ].
      rewrite Hlen.
      assert (HZN : Z.of_N (MachineWord.MachineWord.Z_idx (8 * k)) = 8 * k).
      { unfold MachineWord.MachineWord.Z_idx. apply Z2N.id. lia. }
      rewrite HZN. lia. }
    iAssert (⌜forall (a : Arch.pa) (b : bv 8), dm !! a = Some b ->
               σ'.(mem) !! a = Some b /\ addr_is_ram a⌝)%I as %Hmm.
    { iIntros (a b Hab).
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hab with "Hbytes") as "[Hab Hrest]".
      iDestruct (phys_valid with "Hmem Hab") as %Hv.
      iDestruct (phys_ram with "Hab") as %Hr.
      iPureIntro. exact (conj Hv Hr). }
    iPureIntro.
    exists dv.
    split; [ | split ].
    - intros j HjN.
      assert (Hj : (j < Z.to_nat k)%nat) by lia.
      rewrite (Hnb j Hj).
      exact (proj1 (Hmm _ _ (Hbs j Hj))).
    - rewrite <- (pa_add_0 pa).
      exact (proj2 (Hmm _ _ (Hbs 0%nat ltac:(lia)))).
    - exact (proj2 (Hmm _ _ (Hbs (Z.to_nat k - 1)%nat ltac:(lia)))).
  Qed.

  (* a k-window STORE into the existential bytes *)
  Lemma udata_own_store_g (data : gset Arch.pa) (pa : Arch.pa)
      (v : mword (8 * k)) (m : _) :
    (forall j : nat, (j < Z.to_nat k)%nat -> pa_add pa j ∈ data) ->
    gen_heap_interp (hG := riscv_memGS) m -∗ udata_own data ==∗
    gen_heap_interp (hG := riscv_memGS) (write_bytes m pa (Z.to_N k) v) ∗ udata_own data.
  Proof.
    intros Hin.
    unfold write_bytes.
    rewrite Z_N_nat.
    apply (udata_own_upd data (seq 0 (Z.to_nat k)) pa v m).
    intros j Hj. apply Hin.
    apply elem_of_seq in Hj. lia.
  Qed.


  Lemma user_pt_load_data_g (uroot tfp : mword 44)
        (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
        (w va : mword 64) (σ : mstate) :
      um !! svpn_of va = Some w ->
      uleaf_ok (Load Data) w ->
      udata_cov um data ->
      is_aligned_vaddr (Virtaddr va) k = true ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = User ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
      utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
      ∃ (dv : mword (8 * k)) (σ' : mstate),
        ⌜exec (translateAddr (Virtaddr va) (Load Data)) σ
          = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
        ⌜exec (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w va)) k false false false) σ'
          = Some (Ok dv, σ')⌝ ∗
        ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
        ⌜(σ'.(sregs) = σ.(sregs) \/
          exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
        utlb_inv_pt uroot tfp um ∗ udata_own data.
    Proof.
      intros Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
      iIntros "Hri Hgh Hinv Hdata".
      iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
        as %(HA & Hord & HX & HR & HW & Hcovp).
      iMod (utlb_inv_pt_translateAddr_u (Load Data) uroot tfp um w va
              (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
              Hmisa Hmenv Hhtif Hcp HSXL
              (exec_effectivePrivilege_mprv0 (Load Data)
                 (register_lookup mstatus σ.(sregs)) User σ Hmprv)
              (exec_is_shadow_stack_u_acc (Load Data) σ
                 (or_intror (or_introl eq_refl))) Hall
              with "Hri Hgh Hinv")
        as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
      { intros r Hne.
        destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      iDestruct (udata_read_word_g um data w va σ' Hl Hcov Hal with "Hgh Hdata")
        as %(dv & Hbytes & Hram0 & Hram7).
      iModIntro.
      iExists dv, σ'.
      iSplit; [ iPureIntro; exact Htr | ].
      iSplit; [ iPureIntro | ].
      { set (pa := u_walk_pa w va) in *.
        destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                   : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa k
                  (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                     Hram0 Hram7 (pma_width_le k 8 Hk Hk8 eq_refl)))
          as (region & Hpmam & _ & Hrd & _).
        pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
        assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                  (uint pa) (uint (to_bits 64 k)) = PMP_Match).
        { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
          exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk Hk8
                   Huintk ltac:(lia)
                   Hram0 Hram7 Hcovp). }
        exact (exec_mem_read_data_U PBMT_PMA pa region dv σ'
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 Hrange
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
                 Hpmam
                 (pa_aligned_div _ va k Hk Hkdvd Hal) Hrd
                 (within_clint_false pa k σ' Hnc Hk)
                 (within_sig_false pa k σ' Hns Hk)
                 (within_htif_false pa k σ'
                    (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
                 (addr_is_ram_not_dev _ Hram0)
                 Hbytes
                 (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                 (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
    Qed.

  Lemma user_pt_store_data_g (uroot tfp : mword 44)
        (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
        (w va : mword 64) (v : mword (8 * k)) (σ : mstate) :
      um !! svpn_of va = Some w ->
      uleaf_ok (Store Data) w ->
      udata_cov um data ->
      is_aligned_vaddr (Virtaddr va) k = true ->
      neq_vec (bits_of_virtaddr (Virtaddr va))
         (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
      register_lookup misa σ.(sregs) = MISA_C ->
      register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
      register_lookup htif_tohost_base σ.(sregs) = None ->
      register_lookup cur_privilege σ.(sregs) = User ->
      _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
      eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
      pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
      reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
      utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
      ∃ σ' : mstate,
        ⌜exec (translateAddr (Virtaddr va) (Store Data)) σ
          = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
        ⌜exec (mem_write_value (Physaddr (u_walk_pa w va)) k v (Store Data)
                 PBMT_PMA false false false) σ'
          = Some (Ok true,
                  MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k) v) σ'.(mdev))⌝ ∗
        ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
        ⌜(σ'.(sregs) = σ.(sregs) \/
          exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
        reg_interp σ'.(sregs) ∗
        gen_heap_interp (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k) v) ∗
        utlb_inv_pt uroot tfp um ∗ udata_own data.
    Proof.
      intros Hl Hchk Hcov Hal Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
      iIntros "Hri Hgh Hinv Hdata".
      iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
        as %(HA & Hord & HX & HR & HW & Hcovp).
      iMod (utlb_inv_pt_translateAddr_u (Store Data) uroot tfp um w va
              (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
              Hmisa Hmenv Hhtif Hcp HSXL
              (exec_effectivePrivilege_mprv0 (Store Data)
                 (register_lookup mstatus σ.(sregs)) User σ Hmprv)
              (exec_is_shadow_stack_u_acc (Store Data) σ
                 (or_intror (or_intror (or_introl eq_refl)))) Hall
              with "Hri Hgh Hinv")
        as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
      { intros r Hne.
        destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      (* RAM/window facts for the write, from the (pre-write) bytes *)
      iDestruct (udata_read_word_g um data w va σ' Hl Hcov Hal with "Hgh Hdata")
        as %(dv0 & _ & Hram0 & Hram7).
      set (pa := u_walk_pa w va) in *.
      (* the physical write fact at σ' *)
      assert (Hwr : exec (mem_write_value (Physaddr pa) k v (Store Data)
                            PBMT_PMA false false false) σ'
                    = Some (Ok true,
                            MState σ'.(sregs) (write_bytes σ'.(mem) pa (Z.to_N k) v) σ'.(mdev))).
      { destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                   : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa k
                  (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                     Hram0 Hram7 (pma_width_le k 8 Hk Hk8 eq_refl)))
          as (region & Hpmam & _ & _ & Hwrb).
        pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
        pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
        assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                  (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                  (uint pa) (uint (to_bits 64 k)) = PMP_Match).
        { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
          exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk Hk8
                   Huintk ltac:(lia)
                   Hram0 Hram7 Hcovp). }
        exact (exec_mem_write_value_U PBMT_PMA pa region v σ'
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                 (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                 Hrange
                 (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
                 Hpmam
                 (pa_aligned_div _ va k Hk Hkdvd Hal) (proj1 Hwrb)
                 (within_clint_false pa k σ' Hnc Hk)
                 (within_sig_false pa k σ' Hns Hk)
                 (within_htif_writable_false pa k σ'
                    (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
                 (addr_is_ram_not_dev _ Hram0)
                 (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                 (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
      (* ghost update of the written window *)
      iMod (udata_own_store_g data pa v σ'.(mem)
              (fun j Hj => ltac:(
                 rewrite (u_walk_pa_window_div k w va j Hk Hkdvd Hal Hj);
                 exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl)))
              with "Hgh Hdata") as "[Hgh Hdata]".
      iModIntro.
      iExists σ'.
      iSplit; [ iPureIntro; exact Htr | ].
      iSplit; [ iPureIntro; exact Hwr | ].
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
    Qed.

End UserMemPtGeneric.

(* ===================================================================== *)
(* §6 The width instances -- the names the memory arms consume.            *)
(* ===================================================================== *)

Section UserMemPtInstances.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.









End UserMemPtInstances.

(* ===================================================================== *)
(* §7 AMO (width 4, AMOSWAP -- MemAmo4's kernel scope): the U-mode PMP    *)
(*    grant and the bundle composer.  The AMO's single translation serves *)
(*    both the read and the write, so the composer returns the old value  *)
(*    plus a ∀-value PURE write fact at the moved state; the arm computes *)
(*    the stored value from the old one and absorbs the write into        *)
(*    [udata_own] with [udata_own_store_4].                               *)
(* ===================================================================== *)


Section UserMemPtAmo.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


End UserMemPtAmo.
