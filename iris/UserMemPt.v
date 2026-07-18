(* UserMemPt.v -- the U-mode DATA-memory machinery over the ptree user
   table: physical loads and stores against the owned data pages
   ([udata_own]), composed with the U-mode translation absorption
   (UserPtTree.v).  This is the layer the LOAD/STORE step arms consume.

   Width 8 (LD/SD) is built end-to-end here; the 4/2/1-byte clones are
   mechanical (same chain, the width-matched pma/read/write-plain
   bricks).

   Layers:
     §1 window arithmetic at width 8;
     §2 the U-mode PMP TOR entry-0 grants for data reads and writes;
     §3 the physical read chain at User (checked_mem_read / mem_read);
     §4 the physical write chain at User (checked_mem_write /
        mem_write_value);
     §5 the ghost side: reading a word out of [udata_own] (existential
        contents) and absorbing a store into it (the byte map is
        existential, so the update just re-picks it);
     §6 the invariant-level composers: translate (absorbed) + physical
        access + bundle re-established.                                  *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte.
Require Import PtAdBits.
Require Import Pt4kWalk.
Require Import CommonWalk.
Require Import PtTree.
Require Import PtTreeAdue.
Require Import KptPt.
Require Import TrampPt.
Require Import SmodeCore.
Require Import KptTree.
Require Import UptTree.
Require Import UserPtTree.
Require Import UserBits.
Require Import UserMem.
Require Import KallocInv.
Require Import WpLoad.
Require Import WpMmodeLeafBase.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* (the width-8 bounds -- off8_bound / pa8_aligned -- live in UserBits.v
   next to their width-4 twins) *)

(* bytes of an 8-aligned access stay on the translated page *)
Lemma u_walk_pa_window_8 (pte0 : mword 64) (va : mword 64) (j : nat) :
  is_aligned_vaddr (Virtaddr va) 8 = true ->
  (j < 8)%nat ->
  pa_add (u_walk_pa pte0 va) j = u_walk_pa pte0 (add_vec_int va (Z.of_nat j)).
Proof.
  intros Hal Hj.
  pose proof (off8_bound va Hal) as Hb.
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
(* §3 The physical READ chain at User (width 8).                           *)
(* ===================================================================== *)

Lemma exec_checked_mem_read_ram_8_U (pbmt : page_based_mem_type) (addr : mword 64)
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
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt User (Physaddr addr) 8 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_load addr 8 s HA Hord Hrange HR)).
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

Lemma exec_mem_read_data_8_U (pbmt : page_based_mem_type) (addr : mword 64)
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
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) 8 false false false)
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
            (_ : exec (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 8 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_8_U with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §4 The physical WRITE chain at User (width 8).                          *)
(* ===================================================================== *)

Lemma exec_checked_mem_write_ram_8_U (pbmt : page_based_mem_type) (addr : mword 64)
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
  exec (checked_mem_write (Physaddr addr) 8 data (Store Data) pbmt User tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_store addr 8 s HA Hord Hrange HW)).
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

Lemma exec_mem_write_value_8_U (pbmt : page_based_mem_type) (addr : mword 64)
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
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_write_value (Physaddr addr) 8 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev)).
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
            (exec_checked_mem_write_ram_8_U pbmt addr region data s
               HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §5 The ghost side of data accesses.                                     *)
(* ===================================================================== *)

Section UserMemPtGhost.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* an 8-aligned window of a mapped page, out of the existential bytes *)
  Lemma udata_read_word_8 (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ' : mstate) :
    um !! svpn_of va = Some w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    gen_heap_interp σ'.(mem) -∗ udata_own data -∗
    ⌜exists dv : bv 64,
       (forall j : nat, (N.of_nat j < 8)%N ->
          σ'.(mem) !! pa_add (u_walk_pa w va) j = Some (nth_byte dv j))
       /\ addr_is_ram (u_walk_pa w va)
       /\ addr_is_ram (pa_add (u_walk_pa w va) 7)⌝.
  Proof.
    iIntros (Hl Hcov Hal) "Hmem Hdata".
    iDestruct "Hdata" as (dm) "[%Hdom Hbytes]".
    set (pa := u_walk_pa w va).
    assert (Hin : forall j : nat, (j < 8)%nat -> pa_add pa j ∈ dom dm).
    { intros j Hj. rewrite Hdom.
      unfold pa. rewrite (u_walk_pa_window_8 _ _ _ Hal Hj).
      exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl). }
    assert (Hb : forall j : nat, (j < 8)%nat -> exists b, dm !! pa_add pa j = Some b).
    { intros j Hj. apply elem_of_dom. apply Hin. exact Hj. }
    destruct (Hb 0%nat ltac:(lia)) as [b0 Hb0].
    destruct (Hb 1%nat ltac:(lia)) as [b1 Hb1].
    destruct (Hb 2%nat ltac:(lia)) as [b2 Hb2].
    destruct (Hb 3%nat ltac:(lia)) as [b3 Hb3].
    destruct (Hb 4%nat ltac:(lia)) as [b4 Hb4].
    destruct (Hb 5%nat ltac:(lia)) as [b5 Hb5].
    destruct (Hb 6%nat ltac:(lia)) as [b6 Hb6].
    destruct (Hb 7%nat ltac:(lia)) as [b7 Hb7].
    set (dv := Z_to_bv 64 (assemble_bytes [b0; b1; b2; b3; b4; b5; b6; b7]) : bv 64).
    assert (Hw : forall j : nat, (j < 8)%nat ->
              nth_byte dv j = [b0; b1; b2; b3; b4; b5; b6; b7] !!! j).
    { intros j Hj. apply nth_byte_assemble8; [reflexivity | exact Hj]. }
    iAssert (⌜forall (a : Arch.pa) (b : bv 8), dm !! a = Some b ->
               σ'.(mem) !! a = Some b /\ addr_is_ram a⌝)%I as %Hmm.
    { iIntros (a b Hab).
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hab with "Hbytes") as "[Hab Hrest]".
      iDestruct (mem_valid with "Hmem Hab") as %Hv.
      iDestruct (mem_ram with "Hab") as %Hr.
      iPureIntro. exact (conj Hv Hr). }
    iPureIntro.
    exists dv.
    split; [ | split;
      [ rewrite <- (pa_add_0 pa); exact (proj2 (Hmm _ _ Hb0))
      | exact (proj2 (Hmm _ _ Hb7)) ] ].
    intros j HjN.
    assert (Hj : (j < 8)%nat) by lia.
    rewrite Hw; [ | exact Hj ].
    destruct j as [|[|[|[|[|[|[|[|]]]]]]]]; try lia;
      cbn [lookup_total list_lookup_total];
      [ exact (proj1 (Hmm _ _ Hb0)) | exact (proj1 (Hmm _ _ Hb1))
      | exact (proj1 (Hmm _ _ Hb2)) | exact (proj1 (Hmm _ _ Hb3))
      | exact (proj1 (Hmm _ _ Hb4)) | exact (proj1 (Hmm _ _ Hb5))
      | exact (proj1 (Hmm _ _ Hb6)) | exact (proj1 (Hmm _ _ Hb7)) ].
  Qed.

  (* a data-window STORE: update the model heap and the existential bytes
     in step.  The byte map is existential, so [udata_own] survives with
     the updated map (dom unchanged: every written address was covered). *)
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
      iMod (mem_update _ (pa_add pa x) b (nth_byte v x) with "Hm Hab") as "[Hm Hab]".
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

  Lemma udata_own_store_8 (data : gset Arch.pa) (pa : Arch.pa)
      (v : bv 64) (m : _) :
    (forall j : nat, (j < 8)%nat -> pa_add pa j ∈ data) ->
    gen_heap_interp (hG := riscv_memGS) m -∗ udata_own data ==∗
    gen_heap_interp (hG := riscv_memGS) (write_bytes m pa 8 v) ∗ udata_own data.
  Proof.
    intros Hin.
    apply (udata_own_upd data (seq 0 8) pa v m).
    intros j Hj. apply Hin.
    apply elem_of_seq in Hj. lia.
  Qed.

End UserMemPtGhost.

(* ===================================================================== *)
(* §6 The invariant-level composers: translate (absorbed) + physical      *)
(*    access, with the bundle re-established.                              *)
(* ===================================================================== *)

Section UserMemPtComposers.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* an 8-byte user LOAD: translation succeeds at the leaf page (the
     invariant absorbing whatever the walk did) and the owned pages
     provide SOME value readable at the moved state *)
  Lemma user_pt_load_data_8 (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (Load Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
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
    ∃ (dv : bv 64) (σ' : mstate),
      ⌜exec (translateAddr (Virtaddr va) (Load Data)) σ
        = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
      ⌜exec (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w va)) 8 false false false) σ'
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
    iDestruct (udata_read_word_8 um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv & Hbytes & Hram0 & Hram7).
    iModIntro.
    iExists dv, σ'.
    iSplit; [ iPureIntro; exact Htr | ].
    iSplit; [ iPureIntro | ].
    { set (pa := u_walk_pa w va) in *.
      destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                 : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 8)
        as (region & Hpmam & _ & Hrd & _).
      pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 8)) = PMP_Match).
      { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
        exact (ram_fetch_pmp pa _ 8 7 ltac:(lia) ltac:(lia)
                 ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram0 Hram7 Hcovp). }
      exact (exec_mem_read_data_8_U PBMT_PMA pa region dv σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
               Hpmam
               (pa8_aligned _ va Hal) Hrd
               (within_clint_false pa 8 σ' Hnc ltac:(lia))
               (within_sig_false pa 8 σ' Hns ltac:(lia))
               (within_htif_false pa 8 σ'
                  (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
               (addr_is_ram_not_dev _ Hram0)
               Hbytes
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iFrame "Hri Hgh Hinv Hdata".
  Qed.

  (* an 8-byte user STORE: translation succeeds (absorbed), the physical
     write lands on the owned pages, and the bundle re-establishes with
     the updated (still existential) contents *)
  Lemma user_pt_store_data_8 (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (v : bv 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (Store Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
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
      ⌜exec (mem_write_value (Physaddr (u_walk_pa w va)) 8 v (Store Data)
               PBMT_PMA false false false) σ'
        = Some (Ok true,
                MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w va) 8 v) σ'.(mdev))⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗
      gen_heap_interp (write_bytes σ'.(mem) (u_walk_pa w va) 8 v) ∗
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
    iDestruct (udata_read_word_8 um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv0 & _ & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    (* the physical write fact at σ' *)
    assert (Hwr : exec (mem_write_value (Physaddr pa) 8 v (Store Data)
                          PBMT_PMA false false false) σ'
                  = Some (Ok true,
                          MState σ'.(sregs) (write_bytes σ'.(mem) pa 8 v) σ'.(mdev))).
    { destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                 : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 8)
        as (region & Hpmam & _ & _ & Hwrb).
      pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 8)) = PMP_Match).
      { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
        exact (ram_fetch_pmp pa _ 8 7 ltac:(lia) ltac:(lia)
                 ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram0 Hram7 Hcovp). }
      exact (exec_mem_write_value_8_U PBMT_PMA pa region v σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
               Hpmam
               (pa8_aligned _ va Hal) (proj1 Hwrb)
               (within_clint_false pa 8 σ' Hnc ltac:(lia))
               (within_sig_false pa 8 σ' Hns ltac:(lia))
               (within_htif_writable_false pa 8 σ'
                  (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
               (addr_is_ram_not_dev _ Hram0)
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    (* ghost update of the written window *)
    iMod (udata_own_store_8 data pa v σ'.(mem)
            (fun j Hj => ltac:(
               rewrite (u_walk_pa_window_8 w va j Hal Hj);
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

End UserMemPtComposers.

(* ===================================================================== *)
(* §7 The width-4 clones (LW/SW).  Local bricks first: the width-4        *)
(*    pma checks and the width-4 plain write (their width-8 originals     *)
(*    live in WpLoad / WpMmodeLeafBase; the width-4 PLAIN READ is         *)
(*    RiscvFetchExec's [exec_read_ram_plain_4]).                          *)
(* ===================================================================== *)

Lemma exec_pmaCheck_ram_load_4 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4
    = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (pmaCheck (Physaddr addr) 4 (Load Data) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hread.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hread |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:103.61-103.62" >>=
          (fun _ : true = true => returnM (PMA_readable (override_PMA rattr pbmt))))
    with (returnM (PMA_readable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hread. cbn match.
  apply exec_returnM.
Qed.

Lemma exec_pmaCheck_ram_store_4 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) 4 (Store Data) pbmt false) s = Some (None, s).
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
  change (assert_exp' true "sys/mem.sail:106.61-106.62" >>=
          (fun _ : true = true => returnM (PMA_writable (override_PMA rattr pbmt))))
    with (returnM (PMA_writable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hwrite. cbn match.
  apply exec_returnM.
Qed.

Lemma exec_write_ram_plain_4 (addr : mword 64) (data : bv 32) s :
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_plain (Physaddr addr) 4 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite exec_MemWrite; last exact Hdev.
  reflexivity.
Qed.

Lemma exec_checked_mem_read_ram_4_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt User (Physaddr addr) 4 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_load addr 4 s HA Hord Hrange HR)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load_4 addr pbmt region s Hmatch Halign Hread)).
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

Lemma exec_mem_read_data_4_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 4)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) 4 false false false)
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
            (_ : exec (mem_read_priv_meta _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 4 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_4_U with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Lemma exec_checked_mem_write_ram_4_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 4 data (Store Data) pbmt User tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_store addr 4 s HA Hord Hrange HW)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store_4 addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr addr) 4) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_4 addr data s Hdev)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_4_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 32) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 4)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 4 = Some region ->
  is_aligned_paddr (Physaddr addr) 4 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 4) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 4) s = Some (false, s) ->
  dev_addr addr = false ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_write_value (Physaddr addr) 4 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 4 data) s.(mdev)).
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
            (exec_checked_mem_write_ram_4_U pbmt addr region data s
               HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

(* ---- the width-4 ghost side and composers ---------------------------- *)
Section UserMemPtGhost4.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma udata_read_word_4 (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ' : mstate) :
    um !! svpn_of va = Some w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    gen_heap_interp σ'.(mem) -∗ udata_own data -∗
    ⌜exists dv : bv 32,
       (forall j : nat, (N.of_nat j < 4)%N ->
          σ'.(mem) !! pa_add (u_walk_pa w va) j = Some (nth_byte dv j))
       /\ addr_is_ram (u_walk_pa w va)
       /\ addr_is_ram (pa_add (u_walk_pa w va) 3)⌝.
  Proof.
    iIntros (Hl Hcov Hal) "Hmem Hdata".
    iDestruct "Hdata" as (dm) "[%Hdom Hbytes]".
    set (pa := u_walk_pa w va).
    assert (Hin : forall j : nat, (j < 4)%nat -> pa_add pa j ∈ dom dm).
    { intros j Hj. rewrite Hdom.
      unfold pa. rewrite (u_walk_pa_window _ _ _ Hal Hj).
      exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl). }
    assert (Hb : forall j : nat, (j < 4)%nat -> exists b, dm !! pa_add pa j = Some b).
    { intros j Hj. apply elem_of_dom. apply Hin. exact Hj. }
    destruct (Hb 0%nat ltac:(lia)) as [b0 Hb0].
    destruct (Hb 1%nat ltac:(lia)) as [b1 Hb1].
    destruct (Hb 2%nat ltac:(lia)) as [b2 Hb2].
    destruct (Hb 3%nat ltac:(lia)) as [b3 Hb3].
    set (dv := Z_to_bv 32 (assemble_bytes [b0; b1; b2; b3]) : bv 32).
    assert (Hw : forall j : nat, (j < 4)%nat ->
              nth_byte dv j = [b0; b1; b2; b3] !!! j).
    { intros j Hj. apply nth_byte_assemble4; [reflexivity | exact Hj]. }
    iAssert (⌜forall (a : Arch.pa) (b : bv 8), dm !! a = Some b ->
               σ'.(mem) !! a = Some b /\ addr_is_ram a⌝)%I as %Hmm.
    { iIntros (a b Hab).
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hab with "Hbytes") as "[Hab Hrest]".
      iDestruct (mem_valid with "Hmem Hab") as %Hv.
      iDestruct (mem_ram with "Hab") as %Hr.
      iPureIntro. exact (conj Hv Hr). }
    iPureIntro.
    exists dv.
    split; [ | split;
      [ rewrite <- (pa_add_0 pa); exact (proj2 (Hmm _ _ Hb0))
      | exact (proj2 (Hmm _ _ Hb3)) ] ].
    intros j HjN.
    assert (Hj : (j < 4)%nat) by lia.
    rewrite Hw; [ | exact Hj ].
    destruct j as [|[|[|[|]]]]; try lia;
      cbn [lookup_total list_lookup_total];
      [ exact (proj1 (Hmm _ _ Hb0)) | exact (proj1 (Hmm _ _ Hb1))
      | exact (proj1 (Hmm _ _ Hb2)) | exact (proj1 (Hmm _ _ Hb3)) ].
  Qed.

Lemma udata_own_store_4 (data : gset Arch.pa) (pa : Arch.pa)
      (v : bv 32) (m : _) :
    (forall j : nat, (j < 4)%nat -> pa_add pa j ∈ data) ->
    gen_heap_interp (hG := riscv_memGS) m -∗ udata_own data ==∗
    gen_heap_interp (hG := riscv_memGS) (write_bytes m pa 4 v) ∗ udata_own data.
  Proof.
    intros Hin.
    apply (udata_own_upd data (seq 0 4) pa v m).
    intros j Hj. apply Hin.
    apply elem_of_seq in Hj. lia.
  Qed.

End UserMemPtGhost4.

Section UserMemPtComposers4.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

Lemma user_pt_load_data_4 (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (Load Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
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
    ∃ (dv : bv 32) (σ' : mstate),
      ⌜exec (translateAddr (Virtaddr va) (Load Data)) σ
        = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
      ⌜exec (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w va)) 4 false false false) σ'
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
    iDestruct (udata_read_word_4 um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv & Hbytes & Hram0 & Hram7).
    iModIntro.
    iExists dv, σ'.
    iSplit; [ iPureIntro; exact Htr | ].
    iSplit; [ iPureIntro | ].
    { set (pa := u_walk_pa w va) in *.
      destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                 : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 4)
        as (region & Hpmam & _ & Hrd & _).
      pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 4)) = PMP_Match).
      { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
        exact (ram_fetch_pmp pa _ 4 3 ltac:(lia) ltac:(lia)
                 ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram0 Hram7 Hcovp). }
      exact (exec_mem_read_data_4_U PBMT_PMA pa region dv σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
               Hpmam
               (pa4_aligned _ va Hal) Hrd
               (within_clint_false pa 4 σ' Hnc ltac:(lia))
               (within_sig_false pa 4 σ' Hns ltac:(lia))
               (within_htif_false pa 4 σ'
                  (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
               (addr_is_ram_not_dev _ Hram0)
               Hbytes
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iFrame "Hri Hgh Hinv Hdata".
  Qed.

Lemma user_pt_store_data_4 (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (v : bv 32) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (Store Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
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
      ⌜exec (mem_write_value (Physaddr (u_walk_pa w va)) 4 v (Store Data)
               PBMT_PMA false false false) σ'
        = Some (Ok true,
                MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w va) 4 v) σ'.(mdev))⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗
      gen_heap_interp (write_bytes σ'.(mem) (u_walk_pa w va) 4 v) ∗
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
    iDestruct (udata_read_word_4 um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv0 & _ & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    (* the physical write fact at σ' *)
    assert (Hwr : exec (mem_write_value (Physaddr pa) 4 v (Store Data)
                          PBMT_PMA false false false) σ'
                  = Some (Ok true,
                          MState σ'.(sregs) (write_bytes σ'.(mem) pa 4 v) σ'.(mdev))).
    { destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                 : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 4)
        as (region & Hpmam & _ & _ & Hwrb).
      pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 4)) = PMP_Match).
      { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
        exact (ram_fetch_pmp pa _ 4 3 ltac:(lia) ltac:(lia)
                 ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram0 Hram7 Hcovp). }
      exact (exec_mem_write_value_4_U PBMT_PMA pa region v σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
               Hpmam
               (pa4_aligned _ va Hal) (proj1 Hwrb)
               (within_clint_false pa 4 σ' Hnc ltac:(lia))
               (within_sig_false pa 4 σ' Hns ltac:(lia))
               (within_htif_writable_false pa 4 σ'
                  (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
               (addr_is_ram_not_dev _ Hram0)
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    (* ghost update of the written window *)
    iMod (udata_own_store_4 data pa v σ'.(mem)
            (fun j Hj => ltac:(
               rewrite (u_walk_pa_window w va j Hal Hj);
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

End UserMemPtComposers4.

(* ===================================================================== *)
(* §8 The width-2 clones (LH/SH).                                          *)
(* ===================================================================== *)

Lemma u_walk_pa_window_2 (pte0 : mword 64) (va : mword 64) (j : nat) :
  is_aligned_vaddr (Virtaddr va) 2 = true ->
  (j < 2)%nat ->
  pa_add (u_walk_pa pte0 va) j = u_walk_pa pte0 (add_vec_int va (Z.of_nat j)).
Proof.
  intros Hal Hj.
  pose proof (off2_bound va Hal) as Hb.
  exact (pa_window _ va j ltac:(lia)).
Qed.

Lemma exec_pmaCheck_ram_load_2 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2
    = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (pmaCheck (Physaddr addr) 2 (Load Data) pbmt false) s = Some (None, s).
Proof.
  intros Hmatch Halign Hread.
  unfold pmaCheck.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg pma_regions s)).
  rewrite Hmatch.
  destruct region as [rbase rsize rattr rdtree].
  cbn [PMA_Region_attributes] in Hread |- *.
  rewrite Halign. cbn [Riscv.rv64d.not negb].
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM None s)).
  cbn match beta.
  change (assert_exp' true "sys/mem.sail:103.61-103.62" >>=
          (fun _ : true = true => returnM (PMA_readable (override_PMA rattr pbmt))))
    with (returnM (PMA_readable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hread. cbn match.
  apply exec_returnM.
Qed.

Lemma exec_pmaCheck_ram_store_2 (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) 2 (Store Data) pbmt false) s = Some (None, s).
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
  change (assert_exp' true "sys/mem.sail:106.61-106.62" >>=
          (fun _ : true = true => returnM (PMA_writable (override_PMA rattr pbmt))))
    with (returnM (PMA_writable (override_PMA rattr pbmt)) : M bool).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)).
  rewrite Hwrite. cbn match.
  apply exec_returnM.
Qed.

Lemma exec_write_ram_plain_2 (addr : mword 64) (data : bv 16) s :
  dev_addr addr = false ->
  exec (write_ram rv64d_types.Write_plain (Physaddr addr) 2 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 2 data) s.(mdev)).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)). cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite exec_MemWrite; last exact Hdev.
  reflexivity.
Qed.

Lemma exec_checked_mem_read_ram_2_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (checked_mem_read (Load Data) pbmt User (Physaddr addr) 2 false false false false)
       s = Some (Ok (w, default_meta), s).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_load addr 2 s HA Hord Hrange HR)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_load_2 addr pbmt region s Hmatch Halign Hread)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr addr) 2) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (rv64d_types.Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_ram_plain_2 addr w s Hdev Hbytes)).
  apply exec_returnM.
Qed.

Lemma exec_mem_read_data_2_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (w : bv 16) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr addr) 2) s = Some (false, s) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 2)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_read (Load Data) pbmt (Physaddr addr) 2 false false false)
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
            (_ : exec (mem_read_priv_meta _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _
                (_ : exec (checked_mem_read _ _ _ _ 2 _ _ _ _) s = Some (Ok (w, default_meta), s))).
      2:{ cbn match. apply exec_checked_mem_read_ram_2_U with (region := region); assumption. }
      cbn match. unfold mem_read_callback. apply exec_returnM. }
  cbn [MemoryOpResult_drop_meta]. apply exec_returnM.
Qed.

Lemma exec_checked_mem_write_ram_2_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 16) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 2) s = Some (false, s) ->
  dev_addr addr = false ->
  exec (checked_mem_write (Physaddr addr) 2 data (Store Data) pbmt User tt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 2 data) s.(mdev)).
Proof.
  intros HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmpCheck_user_grant_store addr 2 s HA Hord Hrange HW)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_ram_store_2 addr pbmt region s Hmatch Halign Hwrite)).
      cbn match. apply exec_returnM. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr addr) 2) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (write_kind_of_flags false false false) s = Some (rv64d_types.Write_plain, s))).
  2:{ unfold write_kind_of_flags. cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_ram_plain_2 addr data s Hdev)).
  apply exec_returnM.
Qed.

Lemma exec_mem_write_value_2_U (pbmt : page_based_mem_type) (addr : mword 64)
    (region : PMA_Region) (data : bv 16) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 2)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 2 = Some region ->
  is_aligned_paddr (Physaddr addr) 2 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_sig (Physaddr addr) 2) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr addr) 2) s = Some (false, s) ->
  dev_addr addr = false ->
  eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
  register_lookup cur_privilege s.(sregs) = User ->
  exec (mem_write_value (Physaddr addr) 2 data (Store Data) pbmt false false false) s
    = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr 2 data) s.(mdev)).
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
            (exec_checked_mem_write_ram_2_U pbmt addr region data s
               HA Hord Hrange HW Hmatch Halign Hwrite Hc Hsig Hh Hdev)).
  cbn match. unfold mem_write_callback. apply exec_returnm.
Qed.

Section UserMemPtGhost2.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

Lemma udata_read_word_2 (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ' : mstate) :
    um !! svpn_of va = Some w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
    gen_heap_interp σ'.(mem) -∗ udata_own data -∗
    ⌜exists dv : bv 16,
       (forall j : nat, (N.of_nat j < 2)%N ->
          σ'.(mem) !! pa_add (u_walk_pa w va) j = Some (nth_byte dv j))
       /\ addr_is_ram (u_walk_pa w va)
       /\ addr_is_ram (pa_add (u_walk_pa w va) 1)⌝.
  Proof.
    iIntros (Hl Hcov Hal) "Hmem Hdata".
    iDestruct "Hdata" as (dm) "[%Hdom Hbytes]".
    set (pa := u_walk_pa w va).
    assert (Hin : forall j : nat, (j < 2)%nat -> pa_add pa j ∈ dom dm).
    { intros j Hj. rewrite Hdom.
      unfold pa. rewrite (u_walk_pa_window_2 _ _ _ Hal Hj).
      exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl). }
    assert (Hb : forall j : nat, (j < 2)%nat -> exists b, dm !! pa_add pa j = Some b).
    { intros j Hj. apply elem_of_dom. apply Hin. exact Hj. }
    destruct (Hb 0%nat ltac:(lia)) as [b0 Hb0].
    destruct (Hb 1%nat ltac:(lia)) as [b1 Hb1].
    set (dv := Z_to_bv 16 (assemble_bytes [b0; b1]) : bv 16).
    assert (Hw : forall j : nat, (j < 2)%nat ->
              nth_byte dv j = [b0; b1] !!! j).
    { intros j Hj. apply nth_byte_assemble2; [reflexivity | exact Hj]. }
    iAssert (⌜forall (a : Arch.pa) (b : bv 8), dm !! a = Some b ->
               σ'.(mem) !! a = Some b /\ addr_is_ram a⌝)%I as %Hmm.
    { iIntros (a b Hab).
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hab with "Hbytes") as "[Hab Hrest]".
      iDestruct (mem_valid with "Hmem Hab") as %Hv.
      iDestruct (mem_ram with "Hab") as %Hr.
      iPureIntro. exact (conj Hv Hr). }
    iPureIntro.
    exists dv.
    split; [ | split;
      [ rewrite <- (pa_add_0 pa); exact (proj2 (Hmm _ _ Hb0))
      | exact (proj2 (Hmm _ _ Hb1)) ] ].
    intros j HjN.
    assert (Hj : (j < 2)%nat) by lia.
    rewrite Hw; [ | exact Hj ].
    destruct j as [|[|]]; try lia;
      cbn [lookup_total list_lookup_total];
      [ exact (proj1 (Hmm _ _ Hb0)) | exact (proj1 (Hmm _ _ Hb1)) ].
  Qed.

Lemma udata_own_store_2 (data : gset Arch.pa) (pa : Arch.pa)
      (v : bv 16) (m : _) :
    (forall j : nat, (j < 2)%nat -> pa_add pa j ∈ data) ->
    gen_heap_interp (hG := riscv_memGS) m -∗ udata_own data ==∗
    gen_heap_interp (hG := riscv_memGS) (write_bytes m pa 2 v) ∗ udata_own data.
  Proof.
    intros Hin.
    apply (udata_own_upd data (seq 0 2) pa v m).
    intros j Hj. apply Hin.
    apply elem_of_seq in Hj. lia.
  Qed.

End UserMemPtGhost2.

Section UserMemPtComposers2.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

Lemma user_pt_load_data_2 (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (Load Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
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
    ∃ (dv : bv 16) (σ' : mstate),
      ⌜exec (translateAddr (Virtaddr va) (Load Data)) σ
        = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
      ⌜exec (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w va)) 2 false false false) σ'
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
    iDestruct (udata_read_word_2 um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv & Hbytes & Hram0 & Hram7).
    iModIntro.
    iExists dv, σ'.
    iSplit; [ iPureIntro; exact Htr | ].
    iSplit; [ iPureIntro | ].
    { set (pa := u_walk_pa w va) in *.
      destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                 : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 2)
        as (region & Hpmam & _ & Hrd & _).
      pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 2)) = PMP_Match).
      { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
        exact (ram_fetch_pmp pa _ 2 1 ltac:(lia) ltac:(lia)
                 ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram0 Hram7 Hcovp). }
      exact (exec_mem_read_data_2_U PBMT_PMA pa region dv σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
               Hpmam
               (pa2_aligned _ va Hal) Hrd
               (within_clint_false pa 2 σ' Hnc ltac:(lia))
               (within_sig_false pa 2 σ' Hns ltac:(lia))
               (within_htif_false pa 2 σ'
                  (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
               (addr_is_ram_not_dev _ Hram0)
               Hbytes
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iFrame "Hri Hgh Hinv Hdata".
  Qed.

Lemma user_pt_store_data_2 (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (v : bv 16) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (Store Data) w ->
    udata_cov um data ->
    is_aligned_vaddr (Virtaddr va) 2 = true ->
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
      ⌜exec (mem_write_value (Physaddr (u_walk_pa w va)) 2 v (Store Data)
               PBMT_PMA false false false) σ'
        = Some (Ok true,
                MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w va) 2 v) σ'.(mdev))⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗
      gen_heap_interp (write_bytes σ'.(mem) (u_walk_pa w va) 2 v) ∗
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
    iDestruct (udata_read_word_2 um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv0 & _ & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    (* the physical write fact at σ' *)
    assert (Hwr : exec (mem_write_value (Physaddr pa) 2 v (Store Data)
                          PBMT_PMA false false false) σ'
                  = Some (Ok true,
                          MState σ'.(sregs) (write_bytes σ'.(mem) pa 2 v) σ'.(mdev))).
    { destruct ((ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
                 : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa 2)
        as (region & Hpmam & _ & _ & Hwrb).
      pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
      pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 2)) = PMP_Match).
      { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
        exact (ram_fetch_pmp pa _ 2 1 ltac:(lia) ltac:(lia)
                 ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                 Hram0 Hram7 Hcovp). }
      exact (exec_mem_write_value_2_U PBMT_PMA pa region v σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
               Hpmam
               (pa2_aligned _ va Hal) (proj1 Hwrb)
               (within_clint_false pa 2 σ' Hnc ltac:(lia))
               (within_sig_false pa 2 σ' Hns ltac:(lia))
               (within_htif_writable_false pa 2 σ'
                  (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))
               (addr_is_ram_not_dev _ Hram0)
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    (* ghost update of the written window *)
    iMod (udata_own_store_2 data pa v σ'.(mem)
            (fun j Hj => ltac:(
               rewrite (u_walk_pa_window_2 w va j Hal Hj);
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

End UserMemPtComposers2.
