(* ===================================================================== *)
(* UserMemClassifyAmo.v -- the ATOMIC half of the U-mode memory-family     *)
(* execute totalities: the AMO leaves / composers / engines (widths        *)
(* {1,2,4,8} and the AMOCAS.Q width 16), and the ZICBOP prefetch arm.      *)
(*                                                                         *)
(* Split out of UserMemClassify.v, which carries everything below the      *)
(* atomics (the plain load/store pipeline, the misaligned pipeline and the *)
(* LR/SC stacks) and is this file's only project-local prerequisite.       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import RegFile PtAdBits.
Require Import WpGpr UserBits.
Require Import SmodeCore.
Require Import UptTree UserPtTree UserExec UserCompute.
Require Import UserMemArms WpMmodeLeafBase.
Require Import WpGprCsrwC.
Require Import UserMemAccess UserMemPt.
Require Import UserTotalU.
Require Import RiscvModelBytes CommonWalk MemAmo4.
Require Import UserMemClassify.
Local Open Scope Z_scope.
Import Defs.

(* A failing tactic at this altitude otherwise prints a goal that takes tens
   of minutes to format -- see claude-notes/durable-notes.md. *)
Set Printing Depth 40.

(* ===================================================================== *)
(* op/width/aq-rl-generic AMO memory leaves (Atomic acc, RAM).            *)
(* ===================================================================== *)
Section AmoGeneric.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk16 : k <= 16) (Hkdvd : (k | 4096)).
  Context (Huintk : uint (to_bits 64 k) = k).
  Context (Hkvw : vmem_width k).
  Context (Hread_resv : forall (rk : rv64d_types.read_kind) (addr : mword 64) (w : mword (8 * k)) s,
      (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
      exec (read_ram rk (Physaddr addr) k false) s = Some ((w, default_meta), s)).
  Context (Hwrite_cond : forall (wk : rv64d_types.write_kind) (addr : mword 64) (data : mword (8 * k)) s,
      (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
      dev_addr addr = false ->
      exec (write_ram wk (Physaddr addr) k data tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev))).

  (* op/aq/rl-generic pmpCheck user grant for Atomic (R&W).  Nothing in the
     PMP path inspects the instruction's aq/rl annotations, so the lemma is
     generic in them. *)
  Lemma exec_pmpCheck_user_grant_amo_g (op : amoop) (aq rl : bool) (a : mword 64) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    exec (pmpCheck (Physaddr a) k (Atomic (op, aq, rl, Data, Data)) User) s = Some (None, s).
  Proof.
    intros HA Hord Hrange HR HW.
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
                 (exec_pmpMatchAddr_TOR_match a (to_bits 64 k)
                    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                    (zeros' 64) s HA Hord Hrange)). cbn beta.
      cbn match.
      unfold or_boolM.
      rewrite execR_bind.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (_ : exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                              (Atomic (op, aq, rl, Data, Data))) s = Some (true, s))).
      2:{ unfold pmpCheckRWX. cbn match. rewrite HR HW. apply exec_returnm. }
      cbn match. rewrite execR_returnR. cbn beta.
      cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
      unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
    rewrite Hfe. cbn match. reflexivity.
  Qed.

  (* THE AMO PMA BRICK.  [pmaCheck] answers a PLAN now, and on an aligned AMO
     over a region that permits the op the plan is [pma_ok_aligned] -- the
     whole splitting axis is inert for an aligned access.  There is no per-op
     fault arm: the atomic premise is [pma_allows_atomic_op … op k = true],
     i.e. exactly what [canAccess] asks, and it is what
     [RiscvFetchExec.pma_allows_ram] grants at every op and every width up to
     16.  (It used to be the support LEVEL [= AMOSwap], which is what made
     this lemma conclude an [E_SAMO_Access_Fault] for a user-mode [amoadd] --
     an artifact of the idealized table, not a property of the machine.)

     The LR/SC twins live in [UserMemAccess]; this one stays here because the
     AMO stack is its only consumer. *)
  Lemma exec_pmaCheck_ram_amo_gk (op : amoop) (aq rl : bool) (addr : mword 64)
      (pbmt : page_based_mem_type) (region : PMA_Region) s :
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    pma_allows_atomic_op
      (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) op k = true ->
    exec (pmaCheck (Physaddr addr) k (Atomic (op, aq, rl, Data, Data)) pbmt true) s
      = Some (Ok pma_ok_aligned, s).
  Proof.
    intros Hmatch Halign Hread Hwrite Hsupp.
    assert (Hfield : andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable)
                       (andb (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable)
                          (pma_allows_atomic_op
                             (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support)
                             op k)) = true)
      by (rewrite Hread; rewrite Hwrite; rewrite Hsupp; reflexivity).
    clear Hread Hwrite Hsupp.
    destruct region as [rbase rsize rattr rdtree].
    (* [pmaCheck]'s Atomic arm compiles to a match ON THE OP whose ten branches
       are the same body (the ShadowStack arms below it force the split), so
       [cbn match] cannot reach the arm at a symbolic op and the peel has to be
       run ten times.  The [lazymatch] reads the branch's op back out of the
       goal -- passing [_] leaves an uninferable placeholder. *)
    destruct op;
      lazymatch goal with
      | |- exec (pmaCheck _ _ (Atomic (?o, _, _, _, _)) _ _) _ = _ =>
          pma_ok_peel Hmatch Hfield (exec_is_mag_applicable_amo o aq rl k s) Halign
      end.
  Qed.

  Lemma exec_checked_mem_read_amo_gk (op : amoop) (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    pma_allows_atomic_op
      (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) op k = true ->
    exec (within_mmio_readable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    exec (checked_mem_read (Atomic (op, aq, rl, Data, Data)) pbmt User (Physaddr addr) k aq (andb aq rl) true false) s
      = Some (Ok (w, default_meta), s).
  Proof.
    intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev Hbytes.
    assert (Hcp : exec (check_pma_with_pmp_priority (Atomic (op, aq, rl, Data, Data)) pbmt User
                          (Physaddr addr) k true) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_amo_gk op aq rl addr pbmt region s Hmatch Halign
                    Hread Hwrite Hsupp)).
      cbn match. apply exec_returnM. }
    assert (Hrk : exists rk, exec (read_kind_of_flags aq (andb aq rl) true) s = Some (rk, s) /\
                    (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire)).
    { destruct aq; [ destruct rl |]; unfold read_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hrk as (rk & Hrke & Hrkv).
    unfold checked_mem_read. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr k 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hrke). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (w, true, 0), s)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * k) = addr)
        by (assert (H0 : (0 * k)%Z = 0) by lia; rewrite H0; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_amo_g op aq rl addr s HA Hord Hrange HR HW)).
      cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?aa ?bb) _] =>
        assert (Hseq : execR (Defs.bind0 aa bb) s = Some (inr false, s)) end.
      { rewrite execR_bind0. rewrite execR_returnR. cbn match.
        rewrite execR_liftR. rewrite Hmmio. reflexivity. }
      rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?ad ?wd ?mt)) ?k1) _] =>
        assert (Hrdr : execR (Defs.bind (Defs.liftR (read_ram rk0 ad wd mt)) k1) s
                       = Some (inr w, s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (Hread_resv rk addr w s Hrkv Hdev Hbytes)).
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

  Lemma exec_mem_read_amo_gk (op : amoop) (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (w : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    pma_allows_atomic_op
      (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) op k = true ->
    exec (within_mmio_readable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    (forall j : nat, (N.of_nat j < Z.to_N k)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt (Physaddr addr) k aq (andb aq rl) true) s
      = Some (Ok w, s).
  Proof.
    intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev Hbytes Hmprv Hpriv.
    unfold mem_read.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_nm op aq rl _ _ s Hmprv)).
    unfold mem_read_priv.
    assert (Hcmr := exec_checked_mem_read_amo_gk op aq rl pbmt addr region w s HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev Hbytes).
    assert (Hmrpm : exec (mem_read_priv_meta (Atomic (op, aq, rl, Data, Data)) pbmt User (Physaddr addr) k aq (andb aq rl) true false) s
                   = Some (Ok (w, default_meta), s)).
    (* [mem_read_priv_meta] no longer guards on alignment: it only dispatches
       on the (aq, rl, res) triple, and none of the three the AMO flags can
       form is one of the two unimplemented ones. *)
    { unfold mem_read_priv_meta.
      destruct aq; [ destruct rl |]; cbn match;
        (rewrite (exec_bind_Some _ _ _ _ _ Hcmr);
         cbn match; apply exec_returnM). }
    rewrite (exec_bind_Some _ _ _ _ _ Hmrpm).
    cbn [MemoryOpResult_drop_meta]; apply exec_returnM.
  Qed.


  (* the write leaves, op-generic: [canAccess] passes for the op the region
     permits, and [execute_AMO] issues the store AT THAT OP. *)
  Lemma exec_checked_mem_write_amo_gk (op : amoop) (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    pma_allows_atomic_op
      (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) op k = true ->
    exec (within_mmio_writable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    exec (checked_mem_write (Physaddr addr) k data (Atomic (op, aq, rl, Data, Data)) pbmt User tt (andb aq rl) rl true) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev.
    assert (Hcp : exec (check_pma_with_pmp_priority (Atomic (op, aq, rl, Data, Data)) pbmt User
                          (Physaddr addr) k true) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_amo_gk op aq rl addr pbmt region s Hmatch Halign
                    Hread Hwrite Hsupp)).
      cbn match. apply exec_returnM. }
    assert (Hwk : exists wk, exec (write_kind_of_flags (andb aq rl) rl true) s = Some (wk, s) /\
                    (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release)).
    { destruct aq; destruct rl; unfold write_kind_of_flags; cbn match;
        eexists; (split; [ apply exec_returnM | tauto ]). }
    destruct Hwk as (wk & Hwke & Hwkv).
    set (sw := MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
    unfold checked_mem_write. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr k 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hwke). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0, true), sw)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * k) = addr)
        by (assert (H0 : (0 * k)%Z = 0) by lia; rewrite H0; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_amo_g op aq rl addr s HA Hord Hrange HR HW)).
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
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?ad ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwrr : execR (Defs.bind (Defs.liftR (write_ram wk0 ad wd dt mt)) k1) s
                       = Some (inr true, sw)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ (Hwrite_cond wk addr data s Hwkv Hdev)).
        cbn beta. cbn [andb]. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hwrr). cbn beta zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity.
  Qed.

  Lemma exec_mem_write_value_amo_gk (op : amoop) (aq rl : bool) (pbmt : page_based_mem_type) (addr : mword 64)
      (region : PMA_Region) (data : mword (8 * k)) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    pma_allows_atomic_op
      (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) op k = true ->
    exec (within_mmio_writable (Physaddr addr) k) s = Some (false, s) ->
    dev_addr addr = false ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (mem_write_value (Physaddr addr) k data (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s
      = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev)).
  Proof.
    intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev Hmprv Hpriv.
    unfold mem_write_value, mem_write_value_meta.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_effectivePrivilege_amo_nm op aq rl _ _ s Hmprv)).
    (* [mem_write_value_priv_meta] no longer guards on anything: it is the
       [checked_mem_write] and the callback. *)
    unfold mem_write_value_priv_meta.
    assert (Hcmw := exec_checked_mem_write_amo_gk op aq rl pbmt addr region data s HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmmio Hdev).
    rewrite (exec_bind_Some _ _ _ _ _ Hcmw). cbn match. apply exec_returnM.
  Qed.

  (* [mem_write_ea] at the Atomic access.  The AMO announces its store before
     the read; the announcement runs the same PMA/PMP check and the same
     one-iteration split loop, with no memory effect. *)
  Lemma exec_mem_write_ea_amo_gk (op : amoop) (aq rl : bool) (pbmt : page_based_mem_type)
      (addr : mword 64) (region : PMA_Region) s :
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint addr) (uint (to_bits 64 k)) = PMP_Match ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k = Some region ->
    is_aligned_paddr (Physaddr addr) k = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
    (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
    pma_allows_atomic_op
      (override_PMA (PMA_Region_attributes region) pbmt).(PMA_atomic_support) op k = true ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    exec (mem_write_ea (Physaddr addr) k (Atomic (op, aq, rl, Data, Data)) pbmt
            (andb aq rl) rl true) s = Some (Ok tt, s).
  Proof.
    intros HA Hord Hrange HR HW Hmatch Halign Hread Hwrite Hsupp Hmprv Hpriv.
    assert (Heff : exec (effectivePrivilege (Atomic (op, aq, rl, Data, Data))
                           (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (User, s))
      by (rewrite Hpriv; apply exec_effectivePrivilege_amo_nm; exact Hmprv).
    assert (Hcp : exec (check_pma_with_pmp_priority (Atomic (op, aq, rl, Data, Data)) pbmt User
                          (Physaddr addr) k true) s = Some (Ok pma_ok_aligned, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_amo_gk op aq rl addr pbmt region s Hmatch Halign
                    Hread Hwrite Hsupp)).
      cbn match. apply exec_returnM. }
    assert (Hwkf : exists wk, exec (write_kind_of_flags (andb aq rl) rl true) s = Some (wk, s)).
    { destruct aq; destruct rl; unfold write_kind_of_flags; cbn match;
        eexists; apply exec_returnM. }
    destruct Hwkf as (wk & Hwke).
    unfold mem_write_ea. rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_bind. rewrite execR_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable. rewrite pma_ok_aligned_granule.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr k 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hwke). cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
      assert (Hu : execR (Defs.untilMT vs m0 c bb) s = Some (inr (true, 0), s)) end.
    { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      assert (Havi : add_vec_int addr (0 * k) = addr)
        by (assert (H0 : (0 * k)%Z = 0) by lia; rewrite H0; apply avi0).
      rewrite Havi.
      rewrite (execR_liftR_seq _ _ _ _ _
                 (exec_pmpCheck_user_grant_amo_g op aq rl addr s HA Hord Hrange HR HW)).
      cbn beta. cbn match.
      rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_returnR. reflexivity.
  Qed.


  (* The Iris composer: at a mapped-ok page, the physical AMO facts. *)
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma user_pt_amo_data_k (op : amoop) (aq rl : bool) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (σ : mstate) :
    um !! svpn_of va = Some w ->
    uleaf_ok (Atomic (op, aq, rl, Data, Data)) w ->
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
      ⌜exec (translateAddr (Virtaddr va) (Atomic (op, aq, rl, Data, Data))) σ
        = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
      ⌜exec (mem_write_ea (Physaddr (u_walk_pa w va)) k (Atomic (op, aq, rl, Data, Data))
               PBMT_PMA (andb aq rl) rl true) σ'
        = Some (Ok tt, σ')⌝ ∗
      ⌜exec (mem_read (Atomic (op, aq, rl, Data, Data)) PBMT_PMA
               (Physaddr (u_walk_pa w va)) k aq (andb aq rl) true) σ'
        = Some (Ok dv, σ')⌝ ∗
      ⌜forall v : mword (8 * k),
         exec (mem_write_value (Physaddr (u_walk_pa w va)) k v
                 (Atomic (op, aq, rl, Data, Data)) PBMT_PMA (andb aq rl) rl true) σ'
         = Some (Ok true,
                 MState σ'.(sregs) (write_bytes σ'.(mem) (u_walk_pa w va) (Z.to_N k) v) σ'.(mdev))⌝ ∗
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
    iMod (utlb_inv_pt_translateAddr_u (Atomic (op, aq, rl, Data, Data)) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl
            Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_amo_nm op aq rl (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (Atomic (op, aq, rl, Data, Data)) σ
               (or_intror (or_intror (or_intror (or_intror (or_intror
                  (ex_intro _ op (ex_intro _ aq (ex_intro _ rl eq_refl))))))))) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne.
      destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_read_word_g k Hk Hkdvd um data w va σ' Hl Hcov Hal with "Hgh Hdata")
      as %(dv & Hbytes & Hram0 & Hram7).
    set (pa := u_walk_pa w va) in *.
    destruct (pma_all_ram (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall)
               : pma_allows_all (register_lookup pma_regions σ'.(sregs))) pa k
                  (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia) Hram0 Hram7
                     (pma_width_le k 16 Hk Hk16 eq_refl)))
      as (region & Hpmam & _ & Hrd & Hwr & Hatomic & _).
    pose proof (addr_is_ram_not_in_clint _ Hram0) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram0) as Hns.
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 k)) = PMP_Match).
    { rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)).
      exact (ram_fetch_pmp_g pa _ k (Z.to_nat k - 1) Hk Hk16 Huintk ltac:(lia)
               Hram0 Hram7 Hcovp). }
    assert (Halp : is_aligned_paddr (Physaddr pa) k = true)
      by (exact (pa_aligned_div _ va k Hk Hkdvd Hal)).
    assert (Hmmior : exec (within_mmio_readable (Physaddr pa) k) σ' = Some (false, σ')).
    { unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_clint_false pa k σ' Hnc ltac:(lia))). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_sig_false pa k σ' Hns ltac:(lia))). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false pa k σ'
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))).
      cbn match. reflexivity. }
    assert (Hmmiow : exec (within_mmio_writable (Physaddr pa) k) σ' = Some (false, σ')).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_clint_false pa k σ' Hnc ltac:(lia))). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (within_sig_false pa k σ' Hns ltac:(lia))). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_writable_false pa k σ'
                 (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif)))).
      cbn match. reflexivity. }
    iModIntro.
    iExists dv, σ'.
    iSplit; [ iPureIntro; exact Htr | ].
    iSplit; [ iPureIntro | ].
    { exact (exec_mem_write_ea_amo_gk op aq rl PBMT_PMA pa region σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
               Hpmam Halp Hrd Hwr (Hatomic op k (proj2 (Z.leb_le k 16) Hk16))
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    iSplit; [ iPureIntro | ].
    { exact (exec_mem_read_amo_gk op aq rl PBMT_PMA pa region dv σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
               Hpmam Halp Hrd Hwr (Hatomic op k (proj2 (Z.leb_le k 16) Hk16)) Hmmior (addr_is_ram_not_dev _ Hram0) Hbytes
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    iSplit; [ iPureIntro; intros v | ].
    { exact (exec_mem_write_value_amo_gk op aq rl PBMT_PMA pa region v σ'
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               Hrange
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR))
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW))
               Hpmam Halp Hrd Hwr (Hatomic op k (proj2 (Z.leb_le k 16) Hk16)) Hmmiow (addr_is_ram_not_dev _ Hram0)
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))). }
    iSplit; [ iPureIntro; exact Hmdev | ].
    iSplit; [ iPureIntro; exact Hsregs | ].
    iFrame "Hri Hgh Hinv Hdata".
  Qed.

End AmoGeneric.

(* ===================================================================== *)
(* Translate-fault composer at the Atomic acc (width-generic).            *)
(* ===================================================================== *)
Section AmoFault.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma user_pt_amo_translate_fault (op : amoop) (aq rl : bool) (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va : mword 64) (σ : mstate) :
    u_fault_flavor (Atomic (op, aq, rl, Data, Data)) tfp um va ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um -∗
    ⌜exec (translateAddr (Virtaddr va) (Atomic (op, aq, rl, Data, Data))) σ
      = Some (Err (E_SAMO_Page_Fault tt, tt), σ)⌝.
  Proof.
    intros Hflavor Lhtif Lcp LSXL Lmprv Lpma.
    iIntros "Hri Hgh Hinv".
    iDestruct (utlb_inv_pt_translateAddr_u_fault (Atomic (op, aq, rl, Data, Data)) uroot tfp um va
                 (E_SAMO_Page_Fault tt) σ Hflavor Lhtif Lcp LSXL
                 (exec_effectivePrivilege_amo_nm op aq rl (register_lookup mstatus σ.(sregs)) User σ Lmprv)
                 (exec_is_shadow_stack_u_acc (Atomic (op, aq, rl, Data, Data)) σ
                    (or_intror (or_intror (or_intror (or_intror (or_intror (ex_intro _ op (ex_intro _ aq (ex_intro _ rl eq_refl)))))))))
                 Lpma
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 ltac:(unfold translationException; cbn match; apply exec_returnm)
                 with "Hri Hgh Hinv") as %Htr.
    iPureIntro. exact Htr.
  Qed.

End AmoFault.

(* ===================================================================== *)
(* The width-generic AMO execute engine (k in {1,2,4,8}).                 *)
(* ===================================================================== *)
Section AmoEngine.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)) (Huintk : uint (to_bits 64 k) = k).
  Context (Hread_resv : forall (rk : rv64d_types.read_kind) (addr : mword 64) (w : mword (8 * k)) s,
      (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
      dev_addr addr = false ->
      (forall j : nat, (N.of_nat j < Z.to_N k)%N ->
         s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
      exec (read_ram rk (Physaddr addr) k false) s = Some ((w, default_meta), s)).
  Context (Hwrite_cond : forall (wk : rv64d_types.write_kind) (addr : mword 64) (data : mword (8 * k)) s,
      (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
      dev_addr addr = false ->
      exec (write_ram wk (Physaddr addr) k data tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev))).
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma mem_exec_amo_k (pt : uptd) (op : amoop) (aq rl : bool)
      (rs2 rs1 rd : mword 5) (g : regfile) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (g' : regfile) (s_x : mstate),
        ⌜exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g' ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (xv pcx : mword 64) (s_x : mstate),
        ⌜exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), s_x)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U pt.(ud_root) pt.(ud_tfp) pt.(ud_um) s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption;
        (destruct op; destruct aq; destruct rl; vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_amo_nm op aq rl (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (zeros' 64)).
    assert (Hxb : xlen_bytes = 8) by (vm_compute; reflexivity).
    assert (Hkle : (k <=? xlen_bytes) = true) by (apply Z.leb_le; rewrite Hxb; lia).
    assert (Hkle2 : (k <=? Z.mul xlen_bytes 2) = true) by (apply Z.leb_le; rewrite Hxb; lia).
    destruct (is_aligned_vaddr (Virtaddr va) k) eqn:Hal.
    2:{ (* misaligned -> E_SAMO_Access_Fault trap *)
      iModIntro. iRight.
      iExists (E_SAMO_Access_Fault tt),
        (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64)),
        (register_lookup PC s.(sregs)), s.
      iSplitR.
      { iPureIntro.
        exact (exec_execute_AMO_u_misaligned op aq rl rs2 rs1 rd k
                 (register_lookup PC s.(sregs)) Sv39 s Hkle2 Lcp Heff Hpml Htm eq_refl Hal). }
      iSplitR; [iPureIntro; vm_compute; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh Hdev". }
      iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption. }
    (* aligned *)
    destruct (data_classify (Atomic (op, aq, rl, Data, Data)) pt.(ud_tfp) pt.(ud_um) va
                (or_intror (or_intror (or_intror (or_intror (or_intror (ex_intro _ op (ex_intro _ aq (ex_intro _ rl eq_refl)))))))) Hwf)
      as [ (w & Hum & Huleaf & Hcanon) | Hfault ].
    - (* mapped-ok *)
      iMod (user_pt_amo_data_k k Hk ltac:(lia) Hkdvd Huintk Hread_resv Hwrite_cond op aq rl
              pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) w va s
              Hum Huleaf Hcov Hal Hcanon Hmisa Hmenv Hhtif Lcp HSXL HMPRV Hpma
              with "Hreg Hgh Hutlb Hudata")
        as (dv sig') "(%Htr & %Hea & %Hrdm & %Hwv & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r sig'.(sregs) = register_lookup r s.(sregs)).
      { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      (* THE ARM IS DECIDED BY THE CAS GUARD, NOT BY THE OP.  Every AMO the
         decoder can produce is permitted by the DRAM region, so the read
         succeeded for every op and there is no per-op fault arm left; the only
         question is whether an AMOCAS's comparand matched what memory holds.
         A MISMATCH is the one arm that does not store. *)
      pose proof (exec_rX_bits_gpr rd sig') as Hrdv.
      set (rdv := if Z.eqb (uint rd) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rd))) sig'.(sregs)).
      set (lc := autocast (T := mword) dv : bits (k * 8)).
      destruct (andb (generic_eq op AMOCAS)
                     (neq_vec lc (trunc (Z.mul (__id k) 8) rdv))) eqn:Hguard.
      + (* AMOCAS, comparand MISMATCH: rd := the loaded value, no store. *)
        assert (Hexec : exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s
                        = Some (RETIRE_SUCCESS, wgpr_state rd (sign_extend' 64 lc) sig')).
        { exact (exec_execute_AMO_u_cas_ne op aq rl rs2 rs1 rd k
                   (Physaddr (u_walk_pa w va)) PBMT_PMA dv rdv Sv39 s sig'
                   Hkle Hkle2 Hrdv Hguard Lcp Heff Hpml Htm Hal Htr Hea Hrdm). }
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0.
        * (* rd = x0: the register write is discarded too, so nothing moved *)
          assert (Hst : wgpr_state rd (sign_extend' 64 lc) sig' = sig')
            by (unfold wgpr_state; rewrite Hrd0; reflexivity).
          rewrite Hst in Hexec.
          iModIntro. iLeft. iExists g, sig'.
          iSplitR; [iPureIntro; exact Hexec |].
          iSplitR; [iPureIntro; apply Tr; vm_compute; reflexivity |].
          iSplitR; [iPureIntro; apply Tr; vm_compute; reflexivity |].
          iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
          iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
        * apply Z.eqb_neq in Hrd0.
          set (nv := regval_into_reg (sign_extend' 64 lc)).
          assert (Hst : wgpr_state rd (sign_extend' 64 lc) sig'
                        = set_reg sig' (R_bitvector_64 (gpr_of_Z (uint rd))) nv)
            by (unfold wgpr_state, nv; rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd0); reflexivity).
          rewrite Hst in Hexec.
          iDestruct (gpr_file_acc g rd Hrd0 with "Hgpr") as "[Hrdf Hins]".
          iDestruct "Hrdf" as (v0) "Hrdf".
          iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) v0 nv with "Hreg Hrdf") as "[Hreg Hrdf]".
          iDestruct ("Hins" $! nv with "Hrdf") as "Hgpr".
          iModIntro. iLeft. set (s_x := set_reg sig' (R_bitvector_64 (gpr_of_Z (uint rd))) nv).
          iExists (<[Regidx rd := nv]> g), s_x.
          iSplitR; [iPureIntro; unfold s_x; exact Hexec |].
          assert (Tr2 : forall r : register, register_beq r (R_bitvector_64 (gpr_of_Z (uint rd))) = false ->
                    register_lookup r s_x.(sregs) = register_lookup r sig'.(sregs)).
          { intros r Hne. unfold s_x; rewrite ?sregs_set_reg. apply irrelevant_register_set; exact Hne. }
          iSplitR. { iPureIntro. rewrite Tr2; [| reg_ne]. apply Tr; vm_compute; reflexivity. }
          iSplitR. { iPureIntro. rewrite Tr2; [| reg_ne]. apply Tr; vm_compute; reflexivity. }
          iSplitL "Hreg Hgh Hdev".
          { unfold s_x; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
          iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
      + (* THE STORE ARM: all nine RMW ops, and AMOCAS on a matching comparand.
           The stored value is the model's own per-op [result'] -- the write
           leaf is stated forall-v, so one arm covers every op. *)
        set (rs2v := trunc (Z.mul (__id k) 8)
                       (if Z.eqb (uint rs2) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) sig'.(sregs))
                     : bits (k * 8)).
        set (resv := match op with
                     | AMOSWAP => rs2v | AMOADD => add_vec rs2v lc | AMOXOR => xor_vec rs2v lc
                     | AMOAND => and_vec rs2v lc | AMOOR => or_vec rs2v lc
                     | AMOMIN => if zopz0zI_s rs2v lc then rs2v else lc
                     | AMOMAX => if zopz0zK_s rs2v lc then rs2v else lc
                     | AMOMINU => if zopz0zI_u rs2v lc then rs2v else lc
                     | AMOMAXU => if zopz0zK_u rs2v lc then rs2v else lc
                     | AMOCAS => rs2v end : bits (k * 8)).
        set (v := sign_extend' (Z.mul 8 (__id k)) resv : mword (8 * k)).
        assert (Hwv' := Hwv v).
        set (s2 := MState sig'.(sregs) (write_bytes sig'.(mem) (u_walk_pa w va) (Z.to_N k) v) sig'.(mdev)).
        (* absorb the memory write into udata_own *)
        iMod (udata_own_store_g k
                pt.(ud_data) (u_walk_pa w va) v sig'.(mem)
                (fun j Hj => ltac:(
                   rewrite (u_walk_pa_window_div k _ _ _ Hk Hkdvd Hal Hj);
                   exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hum)))
                with "Hgh Hudata") as "[Hgh Hudata]".
        assert (Hexec : exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, k, Regidx rd))) s
                        = Some (RETIRE_SUCCESS, wgpr_state rd (sign_extend' 64 lc) s2)).
        { exact (exec_execute_AMO_u_store op aq rl rs2 rs1 rd k
                   (Physaddr (u_walk_pa w va)) PBMT_PMA dv rdv Sv39 s sig' s2
                   Hkle Hkle2 Hrdv Hguard Lcp Heff Hpml Htm Hal Htr Hea Hrdm Hwv'). }
        destruct (Z.eqb (uint rd) 0) eqn:Hrd0.
        * (* rd = x0 *)
          assert (Hst : wgpr_state rd (sign_extend' 64 lc) s2 = s2)
            by (unfold wgpr_state; rewrite Hrd0; reflexivity).
          rewrite Hst in Hexec.
          iModIntro. iLeft. iExists g, s2.
          iSplitR; [iPureIntro; exact Hexec |].
          iSplitR; [iPureIntro; unfold s2; cbn [sregs]; apply Tr; vm_compute; reflexivity |].
          iSplitR; [iPureIntro; unfold s2; cbn [sregs]; apply Tr; vm_compute; reflexivity |].
          iSplitL "Hreg Hgh Hdev". { unfold s2; cbn [sregs mem mdev]. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
          iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
        * (* rd <> x0 *)
          apply Z.eqb_neq in Hrd0.
          set (nv := regval_into_reg (sign_extend' 64 lc)).
          assert (Hst : wgpr_state rd (sign_extend' 64 lc) s2
                        = set_reg s2 (R_bitvector_64 (gpr_of_Z (uint rd))) nv)
            by (unfold wgpr_state, nv; rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd0); reflexivity).
          rewrite Hst in Hexec.
          iDestruct (gpr_file_acc g rd Hrd0 with "Hgpr") as "[Hrdf Hins]".
          iDestruct "Hrdf" as (v0) "Hrdf".
          iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) v0 nv with "Hreg Hrdf") as "[Hreg Hrdf]".
          iDestruct ("Hins" $! nv with "Hrdf") as "Hgpr".
          iModIntro. iLeft. set (s_x := set_reg s2 (R_bitvector_64 (gpr_of_Z (uint rd))) nv).
          iExists (<[Regidx rd := nv]> g), s_x.
          iSplitR; [iPureIntro; unfold s_x; exact Hexec |].
          assert (Tr2 : forall r : register, register_beq r (R_bitvector_64 (gpr_of_Z (uint rd))) = false ->
                    register_lookup r s_x.(sregs) = register_lookup r s2.(sregs)).
          { intros r Hne. unfold s_x; rewrite ?sregs_set_reg. apply irrelevant_register_set; exact Hne. }
          iSplitR. { iPureIntro. rewrite Tr2; [| reg_ne]. unfold s2; cbn [sregs]. apply Tr; vm_compute; reflexivity. }
          iSplitR. { iPureIntro. rewrite Tr2; [| reg_ne]. unfold s2; cbn [sregs]. apply Tr; vm_compute; reflexivity. }
          iSplitL "Hreg Hgh Hdev".
          { unfold s_x, s2; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev". }
          iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
    - (* fault -> translate-fault trap *)
      iDestruct (user_pt_amo_translate_fault op aq rl pt.(ud_root) pt.(ud_tfp) pt.(ud_um) va s
                   Hfault Hhtif Lcp HSXL HMPRV Hpma with "Hreg Hgh Hutlb") as %Htr.
      iModIntro. iRight.
      iExists (E_SAMO_Page_Fault tt),
        (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64)),
        (register_lookup PC s.(sregs)), s.
      iSplitR.
      { iPureIntro.
        exact (exec_execute_AMO_u_translate_err op aq rl rs2 rs1 rd k
                 (E_SAMO_Page_Fault tt) (register_lookup PC s.(sregs)) Sv39 s s
                 Hkle2 Lcp Heff Hpml Htm Lcp eq_refl Hal Htr). }
      iSplitR; [iPureIntro; vm_compute; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh Hdev". }
      iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
  Qed.

End AmoEngine.

(* ===================================================================== *)
(* Width-16 (AMOCAS) read-deny trap: the width>xlen (rX_pair) branch.     *)
(* ===================================================================== *)
Lemma exec_rX_pair_bits_gpr (rs : mword 5) s :
  exists v : mword (64 * 2), exec (rX_pair_bits (Regidx rs)) s = Some (v, s).
Proof.
  unfold rX_pair_bits.
  destruct (generic_neq (Regidx rs) zreg) eqn:Hz.
  - eexists.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr (add_vec_int rs 1) s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs s)).
    apply exec_returnM.
  - eexists. apply exec_returnM.
Qed.

Lemma exec_execute_AMO_u_read_err_16
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5)
    (addr : physaddr) (pbmt : page_based_mem_type) (e : ExceptionType)
    (pc : mword 64) (md : SATPMode) (s s' : mstate) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, aq, rl, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  register_lookup cur_privilege s'.(sregs) = User ->
  register_lookup PC s'.(sregs) = pc ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) 16 = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (mem_write_ea addr 16 (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s'
    = Some (Ok tt, s') ->
  exec (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s'
    = Some (Err (addr, e), s') ->
  (* the fault is AT the access base, which is what the model asserts here *)
  generic_eq addr addr = true ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
    = Some (Trap (User, make_sync_exception e
                    (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                              else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                             (zeros' 64)), pc), s').
Proof.
  intros Hcp Heff Hpml Htm Hcp' Hpc' Hal Htr Hea Hrdm Hgeq.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) 16 (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return.
  replace (Z.leb 16 (Z.mul xlen_bytes 2)) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, aq, rl, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite execR_bind. rewrite execR_bind0. rewrite execR_returnR. cbn match.
  rewrite execR_liftR. rewrite Htr. cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  (* mem_read -> Err (addr, e): the model asserts the fault address is the
     access base, then early_returns the memory_exception trap *)
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  assert (Hae : execR (Defs.liftR (assert_exp (generic_eq addr addr)
                         "extensions/A/zaamo_insts.sail:110.31-110.32")
                       : Defs.monadR ExecutionResult exception unit) s'
                = Some (inr tt, s'))
    by (rewrite execR_liftR; unfold assert_exp; rewrite Hgeq; reflexivity).
  rewrite execR_bind. rewrite (execR_bind0_Some _ _ _ _ Hae).
  rewrite execR_liftR.
  rewrite (exec_memory_exception _ pc e User s' Hcp' Hpc'). cbn match.
  reflexivity.
Qed.

(* ===================================================================== *)
(* Width-generic AMO read DENY (op != AMOSWAP): mem_read = Err, no bytes.  *)
(* ===================================================================== *)

(* ===================================================================== *)
(* addr_is_ram at any data address (from udata_own), + width-16 deny.      *)
(* ===================================================================== *)
Section AmoDeny16.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.



End AmoDeny16.

(* ===================================================================== *)
(* Width-16 support (the AMOCAS.Q width): every op RETIRES, through the    *)
(* 128-bit register-pair path (rX_pair / wX_pair).  Same two arms as the    *)
(* narrow widths -- store, or AMOCAS-mismatch -- with the pair reads given  *)
(* as premises (the caller gets them from exec_rX_pair_bits_gpr).           *)
(* ===================================================================== *)

(* 128-bit RAM read/write leaves (clones of the width-8 versions). *)
Lemma exec_read_ram_resv_kinds_16 (rk : rv64d_types.read_kind) (addr : mword 64) (w : bv 128) s :
  (rk = rv64d_types.Read_RISCV_reserved \/ rk = rv64d_types.Read_RISCV_reserved_acquire \/ rk = rv64d_types.Read_RISCV_reserved_strong_acquire) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 16)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec (read_ram rk (Physaddr addr) 16 false) s = Some ((w, default_meta), s).
Proof.
  intros Hrk Hdev Hbytes.
  assert (Hrun : run (read_ram rk (Physaddr addr) 16 false) s (w, default_meta) s).
  { destruct Hrk as [ -> | [ -> | -> ] ];
      (unfold read_ram; cbn match;
       apply (proj2 (run_bind _ _ _ _ _));
       eexists _, s; split; [ apply run_returnM_fwd | ]; cbn beta zeta;
       apply (proj2 (run_bind _ _ _ _ _));
       unfold Defs.sail_mem_read; cbn beta zeta;
       eexists _, s; split;
       [ eapply run_MemRead_ram_intro;
         [ exact Hdev | intros j Hj; exact (Hbytes j Hj) | apply run_returnM_fwd ]
       | cbn match beta; apply run_returnM_fwd ]). }
  apply (run_to_exec _ _ _ _ Hrun).
  destruct Hrk as [ -> | [ -> | -> ] ];
    (unfold read_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_read; cbn beta zeta;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     rewrite exec_MemRead; [| exact Hdev];
     cbn [Interface.ReadReq.pa];
     case_match eqn:Hrb;
     [ cbn [Interface.iMon_bind]; cbn match beta iota; discriminate
     | exfalso;
       refine (read_bytes_ne (mem s) addr (Z.to_N 16) w _ Hrb);
       intros j Hj;
       change (RiscvModelBytes.pa_add addr j) with (pa_add addr j);
       change (RiscvModelBytes.nth_byte w j) with (nth_byte w j);
       exact (Hbytes j Hj) ]).
Qed.

Lemma exec_write_ram_cond_kinds_16 (wk : rv64d_types.write_kind) (addr : mword 64) (data : bv 128) s :
  (wk = rv64d_types.Write_RISCV_conditional \/ wk = rv64d_types.Write_RISCV_conditional_release \/ wk = rv64d_types.Write_RISCV_conditional_strong_release) ->
  dev_addr addr = false ->
  exec (write_ram wk (Physaddr addr) 16 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 16 data) s.(mdev)).
Proof.
  intros Hwk Hdev. destruct Hwk as [ -> | [ -> | -> ] ];
    (unfold write_ram; cbn match;
     rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)); cbn beta zeta;
     unfold Defs.sail_mem_write; cbn beta zeta iota match;
     unfold Defs.bind; cbn [Interface.iMon_bind];
     cbn [Mem_write_request_value]; cbn match; cbn [Interface.iMon_bind];
     rewrite exec_MemWrite; [ reflexivity | exact Hdev ]).
Qed.

(* rd = 0 bridge: relate the wX_pair zreg guard to the uint. *)
Lemma neq_rd_zreg_uint (rd : mword 5) :
  generic_neq (Regidx rd) zreg = true -> Z.eqb (uint rd) 0 = false.
Proof.
  intro Hz. apply generic_neq_true in Hz.
  apply Z.eqb_neq. intro E.
  apply Hz. unfold zreg. f_equal.
  apply bv_eq.
  replace (bv_unsigned (zero_extend' 5 ('b"00"))) with 0%Z by (vm_compute; reflexivity).
  rewrite <- (uint_unsigned_n 5 rd). exact E.
Qed.

(* wX_pair reduction: writes rd (low 64) and rd+1 (high 64) when rd<>0. *)
Definition wpair_state (rd : mword 5) (data : mword (64 * 2)) (s : mstate) : mstate :=
  if generic_neq (Regidx rd) zreg
  then
    let s1 := (if Z.eqb (uint rd) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg (subrange_vec_dec data (Z.sub xlen 1) 0))) in
    (if Z.eqb (uint (add_vec_int rd 1)) 0 then s1
     else set_reg s1 (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1))))
            (regval_into_reg (subrange_vec_dec data (Z.sub (Z.mul xlen 2) 1) xlen)))
  else s.

Lemma exec_wX_pair_bits_gpr (rd : mword 5) (data : mword (64 * 2)) s :
  exec (wX_pair_bits (Regidx rd) data) s = Some (tt, wpair_state rd data s).
Proof.
  unfold wX_pair_bits, wpair_state.
  destruct (generic_neq (Regidx rd) zreg) eqn:Hz.
  - rewrite (exec_bind0_Some _ _ _ _ _
               (exec_wX_bits_gpr rd (subrange_vec_dec data (Z.sub xlen 1) 0) s)).
    change (regidx_offset_range (Regidx rd) 1) with (Regidx (add_vec_int rd 1)).
    apply exec_wX_bits_gpr.
  - apply exec_returnM.
Qed.

(* THE STORE ARM AT WIDTH 16, op-generic: rs2 via rX_pair, rd written via
   wX_pair.  [result'] is the model's per-op value at the pair-read operand. *)
Lemma exec_execute_AMO_u_store_16
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5)
    (addr : physaddr) (pbmt : page_based_mem_type)
    (rp rpd : mword (64 * 2)) (loaded : mword (8 * 16)) (md : SATPMode) (s s' s'' : mstate) :
  let rs2_val : bits (16 * 8) := trunc (Z.mul (__id 16) 8) rp in
  let lc : bits (16 * 8) := autocast (T := mword) loaded in
  let result' : bits (16 * 8) :=
    match op with
    | AMOSWAP => rs2_val | AMOADD => add_vec rs2_val lc | AMOXOR => xor_vec rs2_val lc
    | AMOAND => and_vec rs2_val lc | AMOOR => or_vec rs2_val lc
    | AMOMIN => if zopz0zI_s rs2_val lc then rs2_val else lc
    | AMOMAX => if zopz0zK_s rs2_val lc then rs2_val else lc
    | AMOMINU => if zopz0zI_u rs2_val lc then rs2_val else lc
    | AMOMAXU => if zopz0zK_u rs2_val lc then rs2_val else lc
    | AMOCAS => rs2_val end in
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, aq, rl, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) 16 = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (rX_pair_bits (Regidx rs2)) s' = Some (rp, s') ->
  exec (rX_pair_bits (Regidx rd)) s' = Some (rpd, s') ->
  andb (generic_eq op AMOCAS) (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd)) = false ->
  exec (mem_write_ea addr 16 (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s'
    = Some (Ok tt, s') ->
  exec (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s' = Some (Ok loaded, s') ->
  exec (mem_write_value addr 16
          (sign_extend' (Z.mul 8 (__id 16)) result')
          (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s' = Some (Ok true, s'') ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            wpair_state rd (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))) s'').
Proof.
  intros rs2_val lc result'.
  intros Hcp Heff Hpml Htm Hal Htr Hrp Hrpd Hguard Hea Hrdm Hwv.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) 16 (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return.
  replace (Z.leb 16 (Z.mul xlen_bytes 2)) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, aq, rl, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite execR_bind. rewrite execR_bind0. rewrite execR_returnR. cbn match.
  rewrite execR_liftR. rewrite Htr. cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  (* upstream reordered the body: the effective-address announcement and the
     load now run BEFORE rs2 is read *)
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  rewrite execR_returnR_fwd. cbn match zeta.
  replace (Z.leb 16 xlen_bytes) with false by (vm_compute; reflexivity).
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rs2)))
                    (fun w7 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w7))) s'
               = Some (inr (trunc (Z.mul (__id 16) 8) rp), s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ Hrp). apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hrs2).
  (* THE CAS GUARD at the pair width -- see UserMemArms for the shape. *)
  match goal with |- context[and_boolM ?A ?B] =>
    assert (Hab : execR (and_boolM A B) s'
                  = Some (inr (andb (generic_eq op AMOCAS)
                                 (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd))), s')) end.
  { assert (Hrdt : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rd)))
                     (fun w16 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w16))) s'
                 = Some (inr (trunc (Z.mul (__id 16) 8) rpd), s')).
    { rewrite (execR_liftR_seq _ _ _ _ _ Hrpd). apply execR_returnR_fwd. }
    unfold and_boolM.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (generic_eq op AMOCAS) s')).
    destruct (generic_eq op AMOCAS); cbn match; cbn [andb].
    - rewrite (execR_bind_Some _ _ _ _ _ Hrdt). apply execR_returnR_fwd.
    - first [ apply execR_returnR_fwd | reflexivity ]. }
  rewrite (execR_bind_Some _ _ _ _ _ Hab). rewrite Hguard. cbn match.
  rewrite (execR_liftR_seq _ _ _ _ _ Hwv). cbn match.
  assert (Hwxpr : execR (R := ExecutionResult)
                    (Defs.liftR (wX_pair_bits (Regidx rd) (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))))) s''
                = Some (inr tt, wpair_state rd (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))) s'')).
  { rewrite execR_liftR. rewrite exec_wX_pair_bits_gpr. reflexivity. }
  rewrite (execR_bind0_Some _ _ _ _ Hwxpr).
  rewrite execR_returnR_fwd. reflexivity.
Qed.
(* AMOCAS.Q, COMPARE MISMATCH: rd (the pair) := the loaded value, no store. *)
Lemma exec_execute_AMO_u_cas_ne_16
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : mword 5)
    (addr : physaddr) (pbmt : page_based_mem_type)
    (rp rpd : mword (64 * 2)) (loaded : mword (8 * 16)) (md : SATPMode) (s s' : mstate) :
  let lc : bits (16 * 8) := autocast (T := mword) loaded in
  register_lookup cur_privilege s.(sregs) = User ->
  exec (effectivePrivilege (Atomic (op, aq, rl, Data, Data)) (register_lookup mstatus s.(sregs)) User) s = Some (User, s) ->
  exec (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s = Some (0, s) ->
  exec (translationMode User) s = Some (md, s) ->
  is_aligned_vaddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))) 16 = true ->
  exec (translateAddr (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                          else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                         (zeros' 64))) (Atomic (op, aq, rl, Data, Data))) s = Some (Ok (addr, pbmt, tt), s') ->
  exec (rX_pair_bits (Regidx rs2)) s' = Some (rp, s') ->
  exec (rX_pair_bits (Regidx rd)) s' = Some (rpd, s') ->
  andb (generic_eq op AMOCAS) (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd)) = true ->
  exec (mem_write_ea addr 16 (Atomic (op, aq, rl, Data, Data)) pbmt (andb aq rl) rl true) s'
    = Some (Ok tt, s') ->
  exec (mem_read (Atomic (op, aq, rl, Data, Data)) pbmt addr 16 aq (andb aq rl) true) s' = Some (Ok loaded, s') ->
  exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
    = Some (RETIRE_SUCCESS,
            wpair_state rd (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))) s').
Proof.
  intros lc.
  intros Hcp Heff Hpml Htm Hal Htr Hrp Hrpd Hguard Hea Hrdm.
  change (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)))
    with (execute_AMO op aq rl (Regidx rs2) (Regidx rs1) 16 (Regidx rd)).
  unfold execute_AMO. rewrite exec_catch_early_return.
  replace (Z.leb 16 (Z.mul xlen_bytes 2)) with true by (vm_compute; reflexivity).
  assert (Hass : exec (assert_exp' true "extensions/A/zaamo_insts.sail:73.32-73.33" : M (true = true)) s
                 = Some (@eq_refl bool true, s)) by reflexivity.
  rewrite (execR_liftR_seq _ _ _ _ _ Hass).
  assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
                  = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
  { unfold get_transformed_data_addr.
    assert (Hedga : exec (ext_data_get_addr (Regidx rs1) (zeros' 64) (Atomic (op, aq, rl, Data, Data)) 16) s
              = Some (Ext_DataAddr_OK (Virtaddr (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                                       else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                                      (zeros' 64))), s)).
    { unfold ext_data_get_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)). apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hedga). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_transform_effective_address_u (Atomic (op, aq, rl, Data, Data)) md _ s Hcp Heff Hpml Htm)).
    apply exec_returnM. }
  rewrite (execR_liftR_seq _ _ _ _ _ Hgtda). cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s)).
  rewrite Hal. cbn [Riscv.rv64d.not negb].
  rewrite execR_bind. rewrite execR_bind0. rewrite execR_returnR. cbn match.
  rewrite execR_liftR. rewrite Htr. cbn match.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd _ s')).
  (* upstream reordered the body: the effective-address announcement and the
     load now run BEFORE rs2 is read *)
  rewrite (execR_liftR_seq _ _ _ _ _ Hea). cbn match.
  rewrite execR_bind.
  rewrite (execR_liftR_seq _ _ _ _ _ Hrdm). cbn match.
  rewrite execR_returnR_fwd. cbn match zeta.
  replace (Z.leb 16 xlen_bytes) with false by (vm_compute; reflexivity).
  assert (Hrs2 : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rs2)))
                    (fun w7 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w7))) s'
               = Some (inr (trunc (Z.mul (__id 16) 8) rp), s')).
  { rewrite (execR_liftR_seq _ _ _ _ _ Hrp). apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hrs2).
  match goal with |- context[and_boolM ?A ?B] =>
    assert (Hab : execR (and_boolM A B) s'
                  = Some (inr (andb (generic_eq op AMOCAS)
                                 (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd))), s')) end.
  { assert (Hrdt : execR (Defs.bind (Defs.liftR (rX_pair_bits (Regidx rd)))
                     (fun w16 : mword (64 * 2) => returnR ExecutionResult (trunc (__id 16 * 8) w16))) s'
                 = Some (inr (trunc (Z.mul (__id 16) 8) rpd), s')).
    { rewrite (execR_liftR_seq _ _ _ _ _ Hrpd). apply execR_returnR_fwd. }
    unfold and_boolM.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (generic_eq op AMOCAS) s')).
    destruct (generic_eq op AMOCAS); cbn match; cbn [andb].
    - rewrite (execR_bind_Some _ _ _ _ _ Hrdt). apply execR_returnR_fwd.
    - first [ apply execR_returnR_fwd | reflexivity ]. }
  rewrite (execR_bind_Some _ _ _ _ _ Hab). rewrite Hguard. cbn match.
  assert (Hwxpr : execR (R := ExecutionResult)
                    (Defs.liftR (wX_pair_bits (Regidx rd) (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))))) s'
                = Some (inr tt, wpair_state rd (sign_extend' (Z.mul 64 2) (autocast (T := mword) loaded : mword (16 * 8))) s')).
  { rewrite execR_liftR. rewrite exec_wX_pair_bits_gpr. reflexivity. }
  rewrite (execR_bind0_Some _ _ _ _ Hwxpr).
  rewrite execR_returnR_fwd. reflexivity.
Qed.


(* ===================================================================== *)
(* Width-16 AMO execute engine: AMOSWAP retires (128-bit, register pair), *)
(* every other op denies (mem_read Err) -> trap; misalign / walk-fault    *)
(* -> trap.  Mirrors mem_exec_amo_k but at the fixed wide width 16.        *)
(* ===================================================================== *)
Section AmoEngine16.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma mem_exec_amo_16 (pt : uptd) (op : amoop) (aq rl : bool)
      (rs2 rs1 rd : mword 5) (g : regfile) (s : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    user_mstatus_ok (register_lookup mstatus s.(sregs)) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s.(sregs) = None ->
    pma_allows_all (register_lookup pma_regions s.(sregs)) ->
    mstate_interp s -∗ gpr_file g -∗ user_pt_inv pt ==∗
    ((∃ (g' : regfile) (s_x : mstate),
        ⌜exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s = Some (RETIRE_SUCCESS, s_x)⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g' ∗ user_pt_inv pt)
     ∨ (∃ (e : ExceptionType) (xv pcx : mword 64) (s_x : mstate),
        ⌜exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
           = Some (rv64d_types.Trap (User, make_sync_exception e xv, pcx), s_x)⌝ ∗
        ⌜user_exc e = true⌝ ∗
        ⌜register_lookup (R_bool minstret_increment) s_x.(sregs) = register_lookup (R_bool minstret_increment) s.(sregs)⌝ ∗
        ⌜register_lookup nextPC s_x.(sregs) = register_lookup nextPC s.(sregs)⌝ ∗
        mstate_interp s_x ∗ gpr_file g ∗ user_pt_inv pt)).
  Proof.
    intros Lcp Hmsok Hmisa Hmenv Hsenv Hhtif Hpma.
    iIntros "(Hreg & Hgh & Hdev) Hgpr Hupt".
    iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
    pose proof Hmsok as (HSXL & HMPRV & HMXR & HFS & HVS & HTVM & HTSR).
    iDestruct (utlb_inv_pt_translationMode_U pt.(ud_root) pt.(ud_tfp) pt.(ud_um) s HSXL with "Hreg Hutlb")
      as "(%Htm & Hreg & Hutlb)".
    assert (Hpml : exec (get_pmlen (Atomic (op, aq, rl, Data, Data)) User) s = Some (0, s)).
    { apply exec_get_pmlen_u; try assumption;
        (destruct op; destruct aq; destruct rl; vm_compute; reflexivity). }
    pose proof (exec_effectivePrivilege_amo_nm op aq rl (register_lookup mstatus s.(sregs)) User s HMPRV) as Heff.
    set (va := add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs))
                       (zeros' 64)).
    assert (Hkle2 : (16 <=? Z.mul xlen_bytes 2) = true) by (vm_compute; reflexivity).
    destruct (is_aligned_vaddr (Virtaddr va) 16) eqn:Hal.
    2:{ (* misaligned -> E_SAMO_Access_Fault trap *)
      iModIntro. iRight.
      iExists (E_SAMO_Access_Fault tt),
        (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64)),
        (register_lookup PC s.(sregs)), s.
      iSplitR.
      { iPureIntro.
        exact (exec_execute_AMO_u_misaligned op aq rl rs2 rs1 rd 16
                 (register_lookup PC s.(sregs)) Sv39 s Hkle2 Lcp Heff Hpml Htm eq_refl Hal). }
      iSplitR; [iPureIntro; vm_compute; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh Hdev". }
      iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption. }
    (* aligned *)
    destruct (data_classify (Atomic (op, aq, rl, Data, Data)) pt.(ud_tfp) pt.(ud_um) va
                (or_intror (or_intror (or_intror (or_intror (or_intror (ex_intro _ op (ex_intro _ aq (ex_intro _ rl eq_refl)))))))) Hwf)
      as [ (w & Hum & Huleaf & Hcanon) | Hfault ].
    - (* mapped-ok *)
      iMod (user_pt_amo_data_k 16 ltac:(lia) ltac:(lia) ltac:(exists 256; reflexivity)
              ltac:(vm_compute; reflexivity)
              exec_read_ram_resv_kinds_16 exec_write_ram_cond_kinds_16 op aq rl
              pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) w va s
              Hum Huleaf Hcov Hal Hcanon Hmisa Hmenv Hhtif Lcp HSXL HMPRV Hpma
              with "Hreg Hgh Hutlb Hudata")
        as (dv sig') "(%Htr & %Hea & %Hrdm & %Hwv & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r sig'.(sregs) = register_lookup r s.(sregs)).
      { intros r Hne. destruct Hsregs as [He | (tv & He)]; rewrite He;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      (* THE ARM IS DECIDED BY THE CAS GUARD (see [mem_exec_amo_k]); at this
         width the operands are register PAIRS.  Both arms RETIRE and both end
         with the same pair write over a post state whose sregs and mdev are
         the translate's -- so the arms differ only in whether memory moved,
         and that difference is all this [iAssert] holds. *)
      destruct (exec_rX_pair_bits_gpr rs2 sig') as (rp & Hrp).
      destruct (exec_rX_pair_bits_gpr rd sig') as (rpd & Hrpd).
      set (lc := autocast (T := mword) dv : bits (16 * 8)).
      iAssert (|==> ∃ sx : mstate,
                 ⌜exec (execute (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))) s
                    = Some (RETIRE_SUCCESS,
                            wpair_state rd (sign_extend' (Z.mul 64 2) lc) sx)⌝ ∗
                 ⌜sx.(sregs) = sig'.(sregs)⌝ ∗ ⌜sx.(mdev) = s.(mdev)⌝ ∗
                 gen_heap_interp sx.(mem) ∗ udata_own pt.(ud_data))%I
        with "[Hgh Hudata]" as ">Hstep".
      { destruct (andb (generic_eq op AMOCAS)
                       (neq_vec lc (trunc (Z.mul (__id 16) 8) rpd))) eqn:Hguard.
        - (* AMOCAS, comparand MISMATCH: rd := loaded, no store *)
          iModIntro. iExists sig'.
          iSplitR.
          { iPureIntro.
            exact (exec_execute_AMO_u_cas_ne_16 op aq rl rs2 rs1 rd
                     (Physaddr (u_walk_pa w va)) PBMT_PMA rp rpd dv Sv39 s sig'
                     Lcp Heff Hpml Htm Hal Htr Hrp Hrpd Hguard Hea Hrdm). }
          iSplitR; [iPureIntro; reflexivity |].
          iSplitR; [iPureIntro; exact Hmdev |].
          iFrame "Hgh Hudata".
        - (* THE STORE ARM: every RMW op, and AMOCAS on a match *)
          set (rs2v := trunc (Z.mul (__id 16) 8) rp : bits (16 * 8)).
          set (resv := match op with
                       | AMOSWAP => rs2v | AMOADD => add_vec rs2v lc | AMOXOR => xor_vec rs2v lc
                       | AMOAND => and_vec rs2v lc | AMOOR => or_vec rs2v lc
                       | AMOMIN => if zopz0zI_s rs2v lc then rs2v else lc
                       | AMOMAX => if zopz0zK_s rs2v lc then rs2v else lc
                       | AMOMINU => if zopz0zI_u rs2v lc then rs2v else lc
                       | AMOMAXU => if zopz0zK_u rs2v lc then rs2v else lc
                       | AMOCAS => rs2v end : bits (16 * 8)).
          set (v := sign_extend' (Z.mul 8 (__id 16)) resv : mword (8 * 16)).
          assert (Hwv' := Hwv v).
          iMod (udata_own_store_g 16
                  pt.(ud_data) (u_walk_pa w va) v sig'.(mem)
                  (fun j Hj => ltac:(
                     rewrite (u_walk_pa_window_div 16 _ _ _ ltac:(lia) ltac:(exists 256; reflexivity) Hal Hj);
                     exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hum)))
                  with "Hgh Hudata") as "[Hgh Hudata]".
          iModIntro.
          iExists (MState sig'.(sregs) (write_bytes sig'.(mem) (u_walk_pa w va) (Z.to_N 16) v) sig'.(mdev)).
          iSplitR.
          { iPureIntro.
            exact (exec_execute_AMO_u_store_16 op aq rl rs2 rs1 rd
                     (Physaddr (u_walk_pa w va)) PBMT_PMA rp rpd dv Sv39 s sig' _
                     Lcp Heff Hpml Htm Hal Htr Hrp Hrpd Hguard Hea Hrdm Hwv'). }
          iSplitR; [iPureIntro; reflexivity |].
          iSplitR; [iPureIntro; exact Hmdev |].
          iFrame "Hgh Hudata". }
      iDestruct "Hstep" as (sx) "(%Hexec & %Hsx & %Hsxd & Hgh & Hudata)".
      (* re-point the register interp at the abstract post state, ONCE: every
         framing step below is then syntactically at [sx] the way it used to be
         at the concrete post state. *)
      iEval (rewrite -Hsx) in "Hreg".
      set (D := sign_extend' (Z.mul 64 2) lc).
      (* minstret / nextPC are preserved through the wpair set_regs *)
      assert (Hpres : forall (r : register), register_beq r tlb = false ->
                register_beq r (R_bitvector_64 (gpr_of_Z (uint rd))) = false ->
                register_beq r (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) = false ->
                register_lookup r (wpair_state rd D sx).(sregs) = register_lookup r s.(sregs)).
      { intros r Hne1 Hne2 Hne3. unfold wpair_state.
        destruct (generic_neq (Regidx rd) zreg);
          [ destruct (Z.eqb (uint rd) 0); destruct (Z.eqb (uint (add_vec_int rd 1)) 0);
            rewrite ?sregs_set_reg;
            repeat (rewrite irrelevant_register_set; [| assumption]);
            rewrite Hsx; apply Tr; exact Hne1
          | rewrite Hsx; apply Tr; exact Hne1 ]. }
      (* the register file after the pair write *)
      destruct (generic_neq (Regidx rd) zreg) eqn:Hz.
      + (* rd <> 0: rd (and maybe rd+1) written *)
        assert (Hrd0 : uint rd <> 0) by (apply Z.eqb_neq; apply neq_rd_zreg_uint; exact Hz).
        set (nvlo := regval_into_reg (subrange_vec_dec D (Z.sub xlen 1) 0)).
        iDestruct (gpr_file_acc g rd Hrd0 with "Hgpr") as "[Hrdf Hins]".
        iDestruct "Hrdf" as (v0) "Hrdf".
        iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) v0 nvlo with "Hreg Hrdf") as "[Hreg Hrdf]".
        iDestruct ("Hins" $! nvlo with "Hrdf") as "Hgpr".
        set (s1 := set_reg sx (R_bitvector_64 (gpr_of_Z (uint rd))) nvlo).
        destruct (Z.eqb (uint (add_vec_int rd 1)) 0) eqn:Hrd1.
        * (* rd+1 = 0: only rd written; final state = s1 *)
          iModIntro. iLeft. iExists (<[Regidx rd := nvlo]> g), (wpair_state rd D sx).
          assert (Hst : wpair_state rd D sx = s1).
          { unfold wpair_state, s1. rewrite Hz. rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd0).
            rewrite Hrd1. reflexivity. }
          iSplitR; [iPureIntro; exact Hexec |].
          iSplitR. { iPureIntro. apply Hpres; [ vm_compute; reflexivity | reg_ne |
                     apply Z.eqb_eq in Hrd1; rewrite Hrd1 (* rd+1 = 0 -> R_bitvector_64 0 <> minstret *); reg_ne ]. }
          iSplitR. { iPureIntro. apply Hpres; [ vm_compute; reflexivity | reg_ne |
                     apply Z.eqb_eq in Hrd1; rewrite Hrd1; reg_ne ]. }
          iSplitL "Hreg Hgh Hdev".
          { rewrite Hst. unfold s1; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hgh".
            rewrite Hsxd. iFrame "Hdev". }
          iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
        * (* rd+1 <> 0: both rd and rd+1 written *)
          apply Z.eqb_neq in Hrd1.
          set (nvhi := regval_into_reg (subrange_vec_dec D (Z.sub (Z.mul xlen 2) 1) xlen)).
          iDestruct (gpr_file_acc (<[Regidx rd := nvlo]> g) (add_vec_int rd 1) Hrd1 with "Hgpr") as "[Hr1f Hins1]".
          iDestruct "Hr1f" as (v1) "Hr1f".
          iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) v1 nvhi with "Hreg Hr1f") as "[Hreg Hr1f]".
          iDestruct ("Hins1" $! nvhi with "Hr1f") as "Hgpr".
          iModIntro. iLeft.
          iExists (<[Regidx (add_vec_int rd 1) := nvhi]> (<[Regidx rd := nvlo]> g)), (wpair_state rd D sx).
          assert (Hst : wpair_state rd D sx
                    = set_reg s1 (R_bitvector_64 (gpr_of_Z (uint (add_vec_int rd 1)))) nvhi).
          { unfold wpair_state, s1, nvlo, nvhi. rewrite Hz.
            rewrite (proj2 (Z.eqb_neq (uint rd) 0) Hrd0).
            rewrite (proj2 (Z.eqb_neq (uint (add_vec_int rd 1)) 0) Hrd1). reflexivity. }
          iSplitR; [iPureIntro; exact Hexec |].
          iSplitR. { iPureIntro. apply Hpres; [ vm_compute; reflexivity | reg_ne | reg_ne ]. }
          iSplitR. { iPureIntro. apply Hpres; [ vm_compute; reflexivity | reg_ne | reg_ne ]. }
          iSplitL "Hreg Hgh Hdev".
          { rewrite Hst. unfold s1; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hgh".
            rewrite Hsxd. iFrame "Hdev". }
          iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
      + (* rd = 0: no gpr write, final state = sx *)
        iModIntro. iLeft. iExists g, (wpair_state rd D sx).
        assert (Hst : wpair_state rd D sx = sx) by (unfold wpair_state; rewrite Hz; reflexivity).
        iSplitR; [iPureIntro; exact Hexec |].
        iSplitR. { iPureIntro. rewrite Hst. rewrite Hsx. apply Tr; vm_compute; reflexivity. }
        iSplitR. { iPureIntro. rewrite Hst. rewrite Hsx. apply Tr; vm_compute; reflexivity. }
        iSplitL "Hreg Hgh Hdev".
        { rewrite Hst. iFrame "Hreg Hgh". rewrite Hsxd. iFrame "Hdev". }
        iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
    - (* fault -> translate-fault trap *)
      iDestruct (user_pt_amo_translate_fault op aq rl pt.(ud_root) pt.(ud_tfp) pt.(ud_um) va s
                   Hfault Hhtif Lcp HSXL HMPRV Hpma with "Hreg Hgh Hutlb") as %Htr.
      iModIntro. iRight.
      iExists (E_SAMO_Page_Fault tt),
        (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                  else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) (zeros' 64)),
        (register_lookup PC s.(sregs)), s.
      iSplitR.
      { iPureIntro.
        exact (exec_execute_AMO_u_translate_err op aq rl rs2 rs1 rd 16
                 (E_SAMO_Page_Fault tt) (register_lookup PC s.(sregs)) Sv39 s s
                 Hkle2 Lcp Heff Hpml Htm Lcp eq_refl Hal Htr). }
      iSplitR; [iPureIntro; vm_compute; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitR; [iPureIntro; reflexivity |].
      iSplitL "Hreg Hgh Hdev". { iFrame "Hreg Hgh Hdev". }
      iFrame "Hgpr". unfold user_pt_inv; iFrame "Hutlb Hudata". iPureIntro; split; assumption.
  Qed.

End AmoEngine16.

(* ===================================================================== *)
(* arm_AMO_u : the AMO memory arm.  Widths {1,2,4,8} via mem_exec_amo_k    *)
(* (AMOSWAP retires, all other ops trap); width 16 via mem_exec_amo_16     *)
(* (AMOSWAP retires with a register-pair write, all other ops trap).       *)
(* ===================================================================== *)
Lemma arm_AMO_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (w : mword 32)
    (op : amoop) (aq rl : bool) (rs2 rs1 rd : regidx) (width : word_width_wide) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  (width = 1 \/ width = 2 \/ width = 4 \/ width = 8 \/ width = 16) ->
  exec (ext_decode w) sigma_f = Some (AMO (op, aq, rl, rs2, rs1, width, rd), sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
  base_post C pt E sigma sigma_f va w g.
Proof.
  intros Hcfg Hwidth Hdec.
  destruct rs2 as [rs2]. destruct rs1 as [rs1]. destruct rd as [rd].
  iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
  set (s0 := set_reg sigma_f nextPC (add_vec_int va 4)).
  iDestruct (post_fetch_uconfig C 4 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
    as %((Lcp0 & Hmsok0 & Hmisa0 & Lmenv0 & Hsenv0 & Hhtif0 & Hpma0) & _ & _ & Lmi).
  destruct Hwidth as [Hw|[Hw|[Hw|[Hw|Hw]]]]; subst width.
  - (* width 1 *)
    iMod (mem_exec_amo_k 1 ltac:(lia) ltac:(lia) ltac:(exists 4096; reflexivity) ltac:(vm_compute; reflexivity)
            exec_read_ram_resv_kinds_1 exec_write_ram_cond_kinds_1
            pt op aq rl rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 1, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 1, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 2 *)
    iMod (mem_exec_amo_k 2 ltac:(lia) ltac:(lia) ltac:(exists 2048; reflexivity) ltac:(vm_compute; reflexivity)
            exec_read_ram_resv_kinds_2 exec_write_ram_cond_kinds_2
            pt op aq rl rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 2, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 2, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 4 *)
    iMod (mem_exec_amo_k 4 ltac:(lia) ltac:(lia) ltac:(exists 1024; reflexivity) ltac:(vm_compute; reflexivity)
            exec_read_ram_resv_kinds_4 exec_write_ram_cond_kinds_4
            pt op aq rl rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 4, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 8 *)
    iMod (mem_exec_amo_k 8 ltac:(lia) ltac:(lia) ltac:(exists 512; reflexivity) ltac:(vm_compute; reflexivity)
            exec_read_ram_resv_kinds_8 exec_write_ram_cond_kinds_8
            pt op aq rl rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 8, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 8, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
  - (* width 16 *)
    iMod (mem_exec_amo_16 pt op aq rl rs2 rs1 rd g s0 Lcp0 Hmsok0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 Hpma0
            with "Hint Hgpr Hupt") as "[HOk | HErr]".
    + iDestruct "HOk" as (g' s_x) "(%Hexec & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g'
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd)) RETIRE_SUCCESS s_x
                Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
    + iDestruct "HErr" as (e xv pcx s_x) "(%Hexec & %Hue & %Hmi & %Hnpceq & Hint & Hgpr & Hupt)".
      iApply (base_finish_mem C pt E sigma sigma_f va w g g
                (AMO (op, aq, rl, Regidx rs2, Regidx rs1, 16, Regidx rd))
                (rv64d_types.Trap (User, make_sync_exception e xv, pcx)) s_x
                Lmi Hdec ltac:(reflexivity) Hexec (u_result_ok_trap e xv pcx Hue) I Hmi Hnpceq
                with "Hint Hgpr Hnpc Hupt Hcfg").
Qed.

(* ===================================================================== *)
(*  arm_ZICBOP_u : the ZICBOP prefetch memory arm (19th memory arm).       *)
(*  execute_ZICBOP runs a CacheAccess(CB_prefetch) translateAddr and ALWAYS *)
(*  RETIRES (fault suppressed to nop-retire).  The CacheAccess leaf-check   *)
(*  equals the corresponding u_acc check (check_ca_eq), so upt_acc_wf       *)
(*  classifies it; the Ok branch's phys_access_check grants over the owned  *)
(*  RAM page; both outcomes reframe (finish-unchanged-shaped) to base_post. *)
(* ===================================================================== *)
Definition uacc_of (cbop : cbop_zicbop) : MemoryAccessType mem_payload :=
  match cbop with
  | PREFETCH_R => Load Data
  | PREFETCH_W => Store Data
  | PREFETCH_I => InstructionFetch tt
  end.

Lemma exec_is_shadow_stack_ca (cbop : cbop_zicbop) s :
  exec (is_shadow_stack_access (CacheAccess (CB_prefetch cbop))) s = Some (false, s).
Proof. unfold is_shadow_stack_access. cbn match. apply exec_returnM. Qed.

(* ===================================================================== *)
(* THE SHADOW-STACK PTE, and why the CacheAccess/u_acc leaf checks agree.  *)
(*                                                                         *)
(* [check_PTE_permission] gained a branch for the SHADOW-STACK PTE encoding *)
(* (W set, R and X clear), and it is the ONE place where a prefetch and its *)
(* corresponding plain access disagree: with menvcfg.SSE enabled, a         *)
(* [Load Data] on such a PTE succeeds while [CacheAccess] is denied.  The   *)
(* branch's guard used to be unreachable -- the leading assert was          *)
(* [W -> R] -- but it is now [W -> (R \/ ~X)], which such a PTE satisfies.   *)
(*                                                                         *)
(* It stays unreachable HERE for a different reason: a PTE that both        *)
(* carries U and is shadow-stack-encoded has NO state-independent check     *)
(* result at all, because at menvcfg.SSE = 0 the branch's assert fails and  *)
(* [exec] is [None].  [pte_check_ok] / [pte_check_denied] are [forall s],   *)
(* so either of them RULES THE ENCODING OUT -- which is exactly the side    *)
(* condition [check_ca_eq] needs.                                          *)
(* ===================================================================== *)
Definition sspte (flags : mword 8) : bool :=
  andb (Riscv.rv64d.not (bit_to_bool (_get_PTE_Flags_R flags)))
       (andb (bit_to_bool (_get_PTE_Flags_W flags))
             (Riscv.rv64d.not (bit_to_bool (_get_PTE_Flags_X flags)))).

(* the witness state: any state with menvcfg cleared has SSE = 0 *)
Definition sse0 (s : mstate) : mstate :=
  MState (register_set menvcfg (zeros' 64 : mword 64) s.(sregs)) s.(mem) s.(mdev).

Lemma pte_check_no_sspte (acc : MemoryAccessType mem_payload) (mxr ds : bool)
    (w : mword 64) (r : PTE_Check) (s : mstate) :
  (forall s0, exec (check_PTE_permission acc User mxr ds
                      (Mk_PTE_Flags (subrange_vec_dec w 7 0)) (ext_bits_of_PTE w) tt) s0
              = Some (r, s0)) ->
  andb (bit_to_bool (_get_PTE_Flags_U (Mk_PTE_Flags (subrange_vec_dec w 7 0))))
       (sspte (Mk_PTE_Flags (subrange_vec_dec w 7 0))) = false.
Proof.
  intros H.
  destruct (bit_to_bool (_get_PTE_Flags_U (Mk_PTE_Flags (subrange_vec_dec w 7 0)))) eqn:EU;
    [ cbn [andb] | reflexivity ].
  destruct (sspte (Mk_PTE_Flags (subrange_vec_dec w 7 0))) eqn:E; [ exfalso | reflexivity ].
  unfold sspte in E.
  apply andb_true_iff in E. destruct E as (ER & E2).
  apply andb_true_iff in E2. destruct E2 as (EW & EX).
  apply negb_true_iff in ER. apply negb_true_iff in EX.
  assert (Hcalc : exec (check_PTE_permission acc User mxr ds
                          (Mk_PTE_Flags (subrange_vec_dec w 7 0)) (ext_bits_of_PTE w) tt) (sse0 s)
                  = None).
  { unfold check_PTE_permission.
    rewrite ER. rewrite EW. rewrite EX.
    cbn [Riscv.rv64d.not negb orb andb].
    replace (zopz0zJzJzK true true) with true by (vm_compute; reflexivity).
    unfold Defs.assert_exp. cbn match.
    rewrite exec_bind.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_returnm tt (sse0 s))).
    rewrite exec_returnm. rewrite EU. cbn match.
    { cbn [Riscv.rv64d.not negb]. cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg (sse0 s))).
      unfold sse0. cbn [sregs].
      rewrite register_lookup_set.
      replace (bool_bit_backwards (_get_MEnvcfg_SSE (zeros' 64 : mword 64))) with false
        by (vm_compute; reflexivity).
      unfold Defs.assert_exp. cbn match.
      rewrite exec_bind. rewrite exec_bind0.
      unfold Defs.fail. cbn [exec]. reflexivity. } }
  rewrite (H (sse0 s)) in Hcalc. discriminate.
Qed.

(* the prefetch's leaf check IS its plain access's, away from the
   shadow-stack encoding *)
Lemma check_ca_eq (cbop : cbop_zicbop) (mxr ds : bool) (flags : mword 8) (ext : mword 10) s :
  andb (bit_to_bool (_get_PTE_Flags_U flags)) (sspte flags) = false ->
  exec (check_PTE_permission (CacheAccess (CB_prefetch cbop)) User mxr ds flags ext tt) s
  = exec (check_PTE_permission (uacc_of cbop) User mxr ds flags ext tt) s.
Proof.
  intros Hss.
  unfold check_PTE_permission, uacc_of.
  destruct cbop; cbn match; [ reflexivity | | ].
  all: destruct (zopz0zJzJzK (bit_to_bool (_get_PTE_Flags_W flags))
                   (orb (bit_to_bool (_get_PTE_Flags_R flags))
                        (Riscv.rv64d.not (bit_to_bool (_get_PTE_Flags_X flags))))) eqn:Hass.
  all: unfold Defs.assert_exp; cbn match.
  (* the leading assert fails: both sides are [None] *)
  2,4: rewrite !exec_bind; unfold Defs.fail; cbn [exec]; reflexivity.
  all: rewrite !exec_bind.
  all: rewrite !exec_returnm; cbn match.
  all: destruct (bit_to_bool (_get_PTE_Flags_U flags)) eqn:EU;
       [ change (Riscv.rv64d.not true) with false
       | change (Riscv.rv64d.not false) with true ];
       cbn match; [| reflexivity].
  all: cbn [andb] in Hss; unfold sspte in Hss.
  all: rewrite Hss; cbn match.
  all: rewrite !exec_bind.
  all: reflexivity.
Qed.

(* transfer the leaf classification from the u_acc access to the CacheAccess *)
Lemma uleaf_ok_ca (cbop : cbop_zicbop) (w : mword 64) :
  uleaf_ok (uacc_of cbop) w -> uleaf_ok (CacheAccess (CB_prefetch cbop)) w.
Proof.
  intros H a d mxr do_sum s.
  rewrite (check_ca_eq cbop mxr do_sum _ _ s
             (pte_check_no_sspte (uacc_of cbop) mxr do_sum (pte_set_ad w a d) _ s
                (H a d mxr do_sum))).
  apply H.
Qed.

Lemma uleaf_denied_ca (cbop : cbop_zicbop) (w : mword 64) :
  uleaf_denied (uacc_of cbop) w -> uleaf_denied (CacheAccess (CB_prefetch cbop)) w.
Proof.
  intros H a d mxr do_sum s.
  rewrite (check_ca_eq cbop mxr do_sum _ _ s
             (pte_check_no_sspte (uacc_of cbop) mxr do_sum (pte_set_ad w a d) _ s
                (H a d mxr do_sum))).
  apply H.
Qed.

(* ===== block alignment ===== *)
Lemma block_aligned (addr : mword 64) :
  is_aligned_vaddr (Virtaddr (and_vec addr (not_vec (zero_extend' 64 (ones (plat_cache_block_size_exp)))))) (pow2 (plat_cache_block_size_exp)) = true.
Proof.
  unfold is_aligned_vaddr. apply Z.eqb_eq.
  replace (pow2 plat_cache_block_size_exp) with 64 by (vm_compute; reflexivity).
  rewrite uint_unsigned. rewrite WpGprCsrwC.and_vec_unsigned.
  assert (HM : bv_unsigned (not_vec (zero_extend' 64 (ones plat_cache_block_size_exp)) : mword 64)
             = 18446744073709551552) by (vm_compute; reflexivity).
  rewrite HM.
  rewrite Z.rem_mod_nonneg; [ | apply Z.land_nonneg; left; apply (proj1 (bv_unsigned_in_range 64 addr)) | lia ].
  change 64 with (2 ^ 6).
  rewrite <- Z.land_ones by lia.
  replace (Z.ones 6) with 63 by (vm_compute; reflexivity).
  rewrite <- Z.land_assoc.
  replace (Z.land 18446744073709551552 63) with 0 by (vm_compute; reflexivity).
  apply Z.land_0_r.
Qed.

(* ===== pmpCheck CacheAccess grant (User) : entry-0 TOR RWX match -> None ===== *)
Lemma exec_pmpCheck_user_grant_ca (cbop : cbop_zicbop) (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec (pmpCheck (Physaddr a) width (CacheAccess (CB_prefetch cbop)) User) s = Some (None, s).
Proof.
  intros HA Hord Hrange HX HW HR.
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
                            (CacheAccess (CB_prefetch cbop))) s = Some (true, s))).
    2:{ unfold pmpCheckRWX. cbn match. destruct cbop; cbn match;
        [ rewrite HX | rewrite HR | rewrite HW ]; apply exec_returnm. }
    cbn match. rewrite execR_returnR. cbn beta.
    cbn match. rewrite execR_bind. rewrite execR_returnR. cbn match.
    unfold early_return, throw. cbn [execR]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* ===== pmaCheck CacheAccess : aligned RAM page -> Ok ===== *)
Lemma exec_pmaCheck_ca (cbop : cbop_zicbop) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) (width : Z) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) width = Some region ->
  is_aligned_paddr (Physaddr addr) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (pmaCheck (Physaddr addr) width (CacheAccess (CB_prefetch cbop)) pbmt false) s
    = Some (Ok pma_ok_aligned, s).
Proof.
  intros Hmatch Halign Hx Hr Hw.
  destruct region as [rbase rsize rattr rdtree].
  destruct cbop;
    [ pma_ok_peel Hmatch Hx (exec_is_mag_applicable_cache (CB_prefetch PREFETCH_I) width s) Halign
    | pma_ok_peel Hmatch Hr (exec_is_mag_applicable_cache (CB_prefetch PREFETCH_R) width s) Halign
    | pma_ok_peel Hmatch Hw (exec_is_mag_applicable_cache (CB_prefetch PREFETCH_W) width s) Halign ].
Qed.

(* ===== phys_access_check CacheAccess -> Ok ===== *)
Lemma exec_phys_access_check_ca (cbop : cbop_zicbop) (pbmt : page_based_mem_type)
    (a : mword 64) (region : PMA_Region) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a) width = Some region ->
  is_aligned_paddr (Physaddr a) width = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_executable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (phys_access_check (CacheAccess (CB_prefetch cbop)) pbmt User (Physaddr a) width false) s
    = Some (Ok pma_ok_aligned, s).
Proof.
  intros HA Hord Hrange HX HW HR Hmatch Halign Hx Hr Hw.
  unfold phys_access_check.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_user_grant_ca cbop a width s HA Hord Hrange HX HW HR)).
  cbn match.
  exact (exec_pmaCheck_ca cbop a pbmt region width s Hmatch Halign Hx Hr Hw).
Qed.

(* ===== small pure helpers ===== *)
Lemma add_sub_cancel (a b : mword 64) : add_vec a (sub_vec b a) = b.
Proof.
  apply bv_eq.
  unfold add_vec, sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word,
    MachineWord.MachineWord.add, MachineWord.MachineWord.sub.
  rewrite bv_add_unsigned. rewrite bv_sub_unsigned.
  rewrite bv_wrap_add_idemp_r.
  replace (bv_unsigned a + (bv_unsigned b - bv_unsigned a)) with (bv_unsigned b) by lia.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma uacc_of_u_acc (cbop : cbop_zicbop) : u_acc (uacc_of cbop).
Proof. destruct cbop; unfold u_acc, uacc_of; auto. Qed.

Lemma u_fault_flavor_ca (cbop : cbop_zicbop) (tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (va : mword 64) :
  u_fault_flavor (uacc_of cbop) tfp um va -> u_fault_flavor (CacheAccess (CB_prefetch cbop)) tfp um va.
Proof.
  unfold u_fault_flavor. intros [H|[H|H]].
  - left; exact H.
  - right; left; exact H.
  - right; right. destruct H as (Hc & w & Hleaf & Hden).
    split; [exact Hc|]. exists w. split; [exact Hleaf | apply uleaf_denied_ca; exact Hden].
Qed.

Lemma ca_classify (cbop : cbop_zicbop) (tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (va : mword 64) :
  upt_acc_wf um ->
  u_data_ok (CacheAccess (CB_prefetch cbop)) um va \/ u_fault_flavor (CacheAccess (CB_prefetch cbop)) tfp um va.
Proof.
  intro Hwf.
  destruct (data_classify (uacc_of cbop) tfp um va (uacc_of_u_acc cbop) Hwf) as [Hok|Hf].
  - left. destruct Hok as (w & Hm & Hok & Hc). exists w.
    split; [exact Hm | split; [ apply uleaf_ok_ca; exact Hok | exact Hc ]].
  - right. apply u_fault_flavor_ca; exact Hf.
Qed.

(* the CacheAccess translationException maps every non-No_Access PTW error to
   the same page-fault exception (result discarded by ZICBOP) *)
Lemma exec_translationException_ca_pf (cbop : cbop_zicbop) (f : PTW_Error) s :
  (f = PTW_Invalid_Addr tt \/ f = PTW_Invalid_PTE tt \/ f = PTW_No_Permission tt) ->
  exec (translationException (CacheAccess (CB_prefetch cbop)) f) s
    = Some (match cbop with
            | PREFETCH_R => E_Load_Page_Fault tt
            | PREFETCH_W => E_SAMO_Page_Fault tt
            | PREFETCH_I => E_Fetch_Page_Fault tt end, s).
Proof.
  intro Hf. unfold translationException.
  destruct Hf as [-> | [-> | ->]]; destruct cbop; cbn match; apply exec_returnM.
Qed.

Section ZicbopExec.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma exec_execute_ZICBOP_u (cbop : cbop_zicbop) (rs1 : mword 5) (offset : mword 12)
      (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (s0 : mstate) :
    register_lookup cur_privilege s0.(sregs) = User ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s0.(sregs))) ('b"1") = false ->
    eq_vec (_get_Mstatus_MXR (register_lookup mstatus s0.(sregs))) ('b"0") = true ->
    register_lookup misa s0.(sregs) = MISA_C ->
    register_lookup menvcfg s0.(sregs) = MENVCFG_S ->
    register_lookup senvcfg s0.(sregs) = (mword_of_int 0 : mword 64) ->
    register_lookup htif_tohost_base s0.(sregs) = None ->
    _get_Mstatus_SXL (register_lookup mstatus s0.(sregs)) = 'b"10" ->
    pma_allows_all (register_lookup pma_regions s0.(sregs)) ->
    upt_acc_wf um -> udata_cov um data ->
    reg_interp s0.(sregs) -∗ gen_heap_interp s0.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ s_x : mstate,
      ⌜exec (execute (ZICBOP (cbop, Regidx rs1, offset))) s0 = Some (RETIRE_SUCCESS, s_x)⌝ ∗
      ⌜s_x.(mdev) = s0.(mdev)⌝ ∗
      ⌜(s_x.(sregs) = s0.(sregs) \/ exists tv, s_x.(sregs) = register_set tlb tv s0.(sregs))%type⌝ ∗
      reg_interp s_x.(sregs) ∗ gen_heap_interp s_x.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros Lcp Hmprv Hmxr Hmisa Hmenv Hsenv Hhtif HSXL Hpma Hwf Hcov.
    iIntros "Hri Hgh Hinv Hdata".
    assert (Hpml : exec (get_pmlen (CacheAccess (CB_prefetch cbop)) User) s0 = Some (0, s0)).
    { apply exec_get_pmlen_u;
        first [ assumption | destruct cbop; vm_compute; reflexivity ]. }
    assert (Heff : exec (effectivePrivilege (CacheAccess (CB_prefetch cbop))
                          (register_lookup mstatus s0.(sregs)) User) s0 = Some (User, s0))
      by (apply exec_effectivePrivilege_mprv0; exact Hmprv).
    iDestruct (utlb_inv_pt_translationMode_U uroot tfp um s0 HSXL with "Hri Hinv")
      as "(%Htm & Hri & Hinv)".
    set (rv := if Z.eqb (uint rs1) 0 then zero_reg
               else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s0.(sregs)).
    set (cba := and_vec (add_vec rv (sign_extend' 64 offset))
                        (not_vec (zero_extend' 64 (ones (plat_cache_block_size_exp))))).
    (* get_transformed_data_addr -> OK (Virtaddr cba) *)
    assert (Hgtda : exec (get_transformed_data_addr (Regidx rs1) (sub_vec cba rv)
                           (CacheAccess (CB_prefetch cbop)) (pow2 (plat_cache_block_size_exp))) s0
                    = Some (Ext_DataAddr_OK (Virtaddr cba), s0)).
    { unfold get_transformed_data_addr.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_ext_data_get_addr_gpr rs1 (sub_vec cba rv)
                 (CacheAccess (CB_prefetch cbop)) (pow2 (plat_cache_block_size_exp)) s0)).
      cbn match. fold rv.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_transform_effective_address_u (CacheAccess (CB_prefetch cbop)) Sv39
                    (add_vec rv (sub_vec cba rv)) s0 Lcp Heff Hpml Htm)).
      rewrite add_sub_cancel. apply exec_returnm. }
    destruct (ca_classify cbop tfp um cba Hwf) as [Hok | Hfault].
    - (* Ok : mapped, check passes -> translate Ok, phys grants, retire *)
      destruct Hok as (w & Hm & Hchk & Hcanon).
      iDestruct (utlb_inv_pt_pmp_facts uroot tfp um s0
                   with "Hri Hinv") as %(HA & Hord & HX & HR & HW & Hcovp).
      iMod (utlb_inv_pt_translateAddr_u (CacheAccess (CB_prefetch cbop)) uroot tfp um w cba
              (u_walk_pa w cba) s0 Hm Hchk Hcanon eq_refl Hmisa Hmenv Hhtif Lcp HSXL Heff
              (exec_is_shadow_stack_ca cbop s0) Hpma with "Hri Hgh Hinv")
        as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
      assert (Tr : forall r : register, register_beq r tlb = false ->
                register_lookup r σ'.(sregs) = register_lookup r s0.(sregs)).
      { intros r Hne. destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
          [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
      assert (Halb : is_aligned_vaddr (Virtaddr cba) 64 = true).
      { replace 64 with (pow2 (plat_cache_block_size_exp)) by (vm_compute; reflexivity).
        apply block_aligned. }
      iDestruct (udata_read_word_g 64 ltac:(lia) ltac:(exists 64; reflexivity) um data w cba σ'
                   Hm Hcov Halb with "Hgh Hdata") as %(dv & Hbytes & Hram0 & Hram63).
      set (pa := u_walk_pa w cba) in *.
      assert (HA' : pmpAddrMatchType_encdec_backwards
        (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) = TOR)
        by (rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA).
      assert (Hord' : zopz0zKzJ_u (zeros' 64)
        (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) = false)
        by (rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord).
      assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true)
        by (rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HX).
      assert (HW' : eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true)
        by (rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HW).
      assert (HR' : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ'.(sregs)) 0)) ('b"1") = true)
        by (rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HR).
      assert (Hcovp' : (ram_base + ram_size
        <= uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0) * 4)%Z)
        by (rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp).
      assert (Hpma' : pma_allows_all (register_lookup pma_regions σ'.(sregs)))
        by (rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hpma).
      destruct (pma_all_ram Hpma' pa 64
                 (pma_access_ram _ _ _ Hram0 Hram63 (pma_width_ok 64 eq_refl eq_refl) eq_refl eq_refl)) as (region & Hpmam & Hxr & Hrr & Hwr & _).
      assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n σ'.(sregs)) 0)) 4)
                (uint pa) (uint (to_bits 64 64)) = PMP_Match).
      { pose proof Hram0 as [Halo Hahi]. pose proof Hram63 as [_ Hhilast].
        rewrite (uint_pa_add pa (Z.to_nat 64 - 1)
                   ltac:(unfold ram_base, ram_size in Hahi; rewrite uint_unsigned in Hahi |- *; lia))
          in Hhilast.
        apply (ram_pmp_match_w pa _ 64 ltac:(lia) ltac:(vm_compute; reflexivity)
                 Halo ltac:(unfold ram_base, ram_size in *; lia) Hcovp'). }
      assert (Hphys : exec (phys_access_check (CacheAccess (CB_prefetch cbop)) PBMT_PMA User
                (Physaddr pa) 64 false) σ' = Some (Ok pma_ok_aligned, σ')).
      { apply (exec_phys_access_check_ca cbop PBMT_PMA pa region 64 σ'
                 HA' Hord' Hrange HX' HW' HR' Hpmam
                 (pa_aligned_div _ cba 64 ltac:(lia) ltac:(exists 64; reflexivity) Halb)
                 Hxr Hrr Hwr). }
      assert (Hexec : exec (execute (ZICBOP (cbop, Regidx rs1, offset))) s0
                      = Some (RETIRE_SUCCESS, σ')).
      { change (execute (ZICBOP (cbop, Regidx rs1, offset)))
          with (execute_ZICBOP cbop (Regidx rs1) offset).
        unfold execute_ZICBOP.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s0)). fold rv. cbn zeta.
        rewrite (exec_bind_Some _ _ _ _ _ Hgtda). cbn match.
        match goal with |- exec (Defs.bind0 ?A _) s0 = _ =>
          assert (HAbody : exec A s0 = Some (tt, σ')) end.
        { rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus σ')).
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege σ')).
          rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)). rewrite Lcp.
          rewrite (exec_bind_Some _ _ _ _ _
                     (exec_effectivePrivilege_mprv0 (CacheAccess (CB_prefetch cbop))
                        (register_lookup mstatus σ'.(sregs)) User σ'
                        (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv)))).
          replace (pow2 (plat_cache_block_size_exp)) with 64 by (vm_compute; reflexivity).
          rewrite (exec_bind_Some _ _ _ _ _ Hphys). cbn match. apply exec_returnm. }
        unfold Defs.bind0. rewrite (exec_bind_Some _ _ _ _ _ HAbody). apply exec_returnm. }
      iModIntro. iExists σ'.
      iSplit; [ iPureIntro; exact Hexec | ].
      iSplit; [ iPureIntro; exact Hmdev | ].
      iSplit; [ iPureIntro; exact Hsregs | ].
      iFrame "Hri Hgh Hinv Hdata".
    - (* Fault : translate Err -> retire, state unchanged *)
      set (e := match cbop with
                | PREFETCH_R => E_Load_Page_Fault tt
                | PREFETCH_W => E_SAMO_Page_Fault tt
                | PREFETCH_I => E_Fetch_Page_Fault tt end).
      iDestruct (utlb_inv_pt_translateAddr_u_fault (CacheAccess (CB_prefetch cbop)) uroot tfp um
                   cba e s0 Hfault Hhtif Lcp HSXL Heff (exec_is_shadow_stack_ca cbop s0) Hpma
                   (exec_translationException_ca_pf cbop (PTW_Invalid_Addr tt) s0 (or_introl eq_refl))
                   (exec_translationException_ca_pf cbop (PTW_Invalid_PTE tt) s0 (or_intror (or_introl eq_refl)))
                   (exec_translationException_ca_pf cbop (PTW_No_Permission tt) s0 (or_intror (or_intror eq_refl)))
                   with "Hri Hgh Hinv") as %Htr.
      assert (Hexec : exec (execute (ZICBOP (cbop, Regidx rs1, offset))) s0
                      = Some (RETIRE_SUCCESS, s0)).
      { change (execute (ZICBOP (cbop, Regidx rs1, offset)))
          with (execute_ZICBOP cbop (Regidx rs1) offset).
        unfold execute_ZICBOP.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s0)). fold rv. cbn zeta.
        rewrite (exec_bind_Some _ _ _ _ _ Hgtda). cbn match.
        match goal with |- exec (Defs.bind0 ?A _) s0 = _ =>
          assert (HAbody : exec A s0 = Some (tt, s0)) end.
        { rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match. apply exec_returnm. }
        unfold Defs.bind0. rewrite (exec_bind_Some _ _ _ _ _ HAbody). apply exec_returnm. }
      iModIntro. iExists s0.
      iSplit; [ iPureIntro; exact Hexec | ].
      iSplit; [ iPureIntro; reflexivity | ].
      iSplit; [ iPureIntro; left; reflexivity | ].
      iFrame "Hri Hgh Hinv Hdata".
  Qed.

End ZicbopExec.

Lemma arm_ZICBOP_u `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (C : ucfg) (pt : uptd)
    (E : coPset) (sigma sigma_f : mstate) (va : mword 64)
    (g : regfile) (w : mword 32)
    (p : cbop_zicbop * regidx * bits 12) :
  post_fetch_cfg sigma_f va (register_lookup (R_bool minstret_increment) sigma.(sregs)) ->
  exec (ext_decode w) sigma_f = Some (ZICBOP p, sigma_f) ->
  hw_config -∗
  mstate_interp (set_reg sigma_f nextPC (add_vec_int va 4)) -∗
  gpr_file g -∗ nextPC ↦ᵣ add_vec_int va 4 -∗ user_pt_inv pt -∗ user_cfg C -∗
  base_post C pt E sigma sigma_f va w g.
Proof.
  intros Hcfg Hdec.
  destruct p as [[cbop rs1] offset]. destruct rs1 as [rs1].
  iIntros "#Hhw Hint Hgpr Hnpc Hupt Hcfg".
  set (s0 := set_reg sigma_f nextPC (add_vec_int va 4)).
  iDestruct (post_fetch_uconfig C 4 sigma_f va _ Hcfg with "Hint Hhw Hcfg")
    as %((Lcp0 & Hmsok0 & Hmisa0 & Lmenv0 & Hsenv0 & Hhtif0 & Hpma0) & _ & _ & Lmi).
  destruct Hmsok0 as (HSXL0 & HMPRV0 & HMXR0 & _ & _).
  iDestruct "Hint" as "(Hreg & Hgh & Hdev)".
  iDestruct "Hupt" as "(Hutlb & Hudata & %Hcov & %Hwf)".
  iMod (exec_execute_ZICBOP_u cbop rs1 offset pt.(ud_root) pt.(ud_tfp) pt.(ud_um) pt.(ud_data) s0
          Lcp0 HMPRV0 HMXR0 Hmisa0 Lmenv0 Hsenv0 Hhtif0 HSXL0 Hpma0 Hwf Hcov
          with "Hreg Hgh Hutlb Hudata")
    as (s_x) "(%Hexec & %Hmdev & %Hsregs & Hreg & Hgh & Hutlb & Hudata)".
  assert (Hmi : register_lookup (R_bool minstret_increment) s_x.(sregs)
                = register_lookup (R_bool minstret_increment) s0.(sregs)).
  { destruct Hsregs as [-> | (tv & ->)]; [reflexivity | apply irrelevant_register_set; vm_compute; reflexivity]. }
  assert (Hnpc : register_lookup nextPC s_x.(sregs) = register_lookup nextPC s0.(sregs)).
  { destruct Hsregs as [-> | (tv & ->)]; [reflexivity | apply irrelevant_register_set; vm_compute; reflexivity]. }
  iApply (base_finish_mem C pt E sigma sigma_f va w g g
            (ZICBOP (cbop, Regidx rs1, offset)) RETIRE_SUCCESS s_x
            Lmi Hdec ltac:(reflexivity) Hexec u_result_ok_retire I Hmi Hnpc
            with "[Hreg Hgh Hdev] Hgpr Hnpc [Hutlb Hudata] Hcfg").
  - unfold mstate_interp. iFrame "Hreg Hgh". rewrite Hmdev. iFrame "Hdev".
  - iFrame "Hutlb Hudata". iPureIntro; split; assumption.
Qed.
