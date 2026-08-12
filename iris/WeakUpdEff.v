(** * WeakUpdEff.v — M4 batch 6a (update): the PTE A/D WRITE-BACK cone at
    [exec_eff]

    THE MIRROR of the S-mode translation UPDATE path — the walker's atomic
    A/D compare-and-swap that the sail bump landed — at the instrumented
    interpreter [WeakCert.exec_eff].  The SC originals are [SmodePte.v]'s
    [exec_read_pte_exclusive_S], [WpMmodeLeafBase.v]'s width-8 conditional
    RAM write, [PtTree.v]'s [pt_read_pte_exclusive_slot], and the whole of
    [PtTreeAdue.v] §§1–4 (the PMP/PMA store gates for the PTE slot, the
    conditional write, the generic TLB fill, and the three write-back
    translate heads).  [WeakWalkEff.v] is the READ-cone mirror this file
    extends; everything there (the [wpte_*] eff predicate twins, the
    success/fault walks, the [translate] dispatchers, the [translateAddr]
    front heads) is consumed as-is.

    THE MODEL'S UPDATE PATH, as landed (rv64d.v [update_and_write_pte],
    10 arguments, both [translate_TLB_miss] and [translate_TLB_hit] funnel
    through it):

      match update_PTE_Bits stale acc with
      | None   => Ok (None, ·)                      (O-UNCHANGED: NO events —
                                                     not even a read)
      | Some _ =>
        if Svadu ∧ menvcfg.ADUE then
          fresh ← read_pte_exclusive pteAddr 8;     (the CAS read half)
          check_leaf_pte … fresh …;;                (the re-checked tablewalk)
          match update_PTE_Bits fresh acc with
          | None        => Ok (Some fresh, ·)       (O-FRESH: read only —
                                                     memory already has bits)
          | Some fresh' => write_pte_conditional pteAddr 8 fresh';;
                           Ok (Some fresh', ·)      (O-WRITTEN: read + write,
                                                     adjacent)
        else Err PTW_PTE_Needs_Update               (Svade — dead, ADUE = 1)

    plus the three Err funnels (the exclusive read failing PMP/PMA →
    [PTW_No_Access]; the re-check failing → its PTW error; the conditional
    write failing PMP/PMA → [PTW_No_Access]) — mirrored as result-generic
    composers whose failure is a PREMISE, since under the kernel invariant
    (slot in RAM, PMP TOR grant, PMA pte-write) they are unreachable and
    the SC tree accordingly has no reduction lemmas for them.

    THE TRACE, and the WeakInterp classifications each interface kind hits:

      - [read_pte_exclusive] goes through [read_kind_of_flags false false
        true = Read_RISCV_reserved] → the interface request's access kind is
        [AK_explicit {| AV_exclusive; AS_normal |}] → [WeakInterp.classify]
        gives [AkInfo false true false]: NOT coherent, LATEST (exclusive),
        NOT synchronising.  [ak_latest] ⇒ [ak_pins] ⇒ the read is PINNED BY
        KIND: [WeakCert.trace_pin] exempts it, and its admissibility at the
        bridge IS [WeakMem.latest] — no view hypothesis anywhere (the
        batch-6 design's "reduced form").
      - [write_pte_conditional] goes through [write_kind_of_flags false
        false true = Write_RISCV_conditional] → [AK_explicit
        {| AV_exclusive; AS_normal |}] → [classify] = [AkInfo false true
        false] as well.  (Compare the lock AMO's [.aq] pair in
        [WeakLeafAmo4.v]: read [AkInfo false true true] — the acquire makes
        it AS_rel_or_acq — write [AkInfo false true false].  The walker's
        CAS is the same exclusive variety WITHOUT the acquire.)

    So the O-WRITTEN trace is the adjacent pair

        [WEread (AkInfo false true false) pteAddr 8;
         WEwrite (AkInfo false true false) pteAddr 8 fresh']

    — exactly the [wcert_amo_aq_gen] shape minus the acquire, which is why
    §8's certificates conclude [wQ_store_w 8] (message identity + the
    store's view floor) and NOT [wQ_amo_aq_w] (no [ak_sync] on the read, so
    no acquire gain to certify — and none is needed: the walker's read
    feeds only the PTE re-check, never a register).

    WHAT THE MODEL DID TO THE OLD DESIGN NAMES (recorded because the batch
    worklist still uses them): there is no [PTE_AD_*] outcome union and no
    [read_pte_reserved] — the outcomes are encoded in
    [result (option pte * unit) (PTW_Error * unit)] as above, the reserved
    read is [read_pte_exclusive], and there is NO whole-value compare
    against the walked pte: the CAS's "compare" is [check_leaf_pte] re-run
    on the FRESH word plus [update_PTE_Bits fresh] deciding whether to
    write.  Consequently a TLB-HIT whose fresh word fails the re-check
    FAULTS ([Err] propagates out of [translate_TLB_hit]) — there is no
    fall-back to a re-walk.  And in a single [exec_eff] run the fresh word
    IS the walked word (same memory), so the miss-path O-FRESH arm is
    unreachable at this altitude — it exists only on the HIT path, where
    the cached word and memory genuinely differ ([_refresh]).

    Sections:
      §1  the two exclusive-kind RAM steps at width 8 (where the traces are
          born)
      §2  the PTE-STORE gates: PMA ([PMA_supports_pte_write],
          res_or_con-generic) and the S-mode PMP store grant
      §3  the exclusive PTE read chain + the [pt_slot_mem]-keyed slot fact
      §4  the conditional PTE write chain ([exec_eff_write_pte_conditional_ram])
      §5  [update_and_write_pte]'s outcome arms, level-generic
      §6  the TLB plumbing: the generic level-0 fill and [write_TLB]
      §7  the write-back translate heads: miss-upd, hit-upd, hit-refresh
      §8  the [translateAddr]-level composition (miss-upd through
          [WeakWalkEff]'s outcome-generic front head)
      §9  the certificates for the CAS pair ([wQ_store_w 8], gen + pin)
*)
From Stdlib Require Import ZArith Bool Zwf.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpDecodeBridge WpLoad.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakEffSkel WeakFetchEff WeakLeafEffCommon WeakLeafEff8.
Require Import SmodePte Pt4kWalk CommonWalk PtAdBits PtTree UserPtTree PtTreeAdue.
Require Import WeakWalkEff.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(** ** 1. The two exclusive-kind RAM steps at width 8

    [read_ram Read_RISCV_reserved] emits [WEread (AkInfo false true false)
    addr 8] and [write_ram Write_RISCV_conditional] emits [WEwrite (AkInfo
    false true false) addr 8 data] — see the header for the kind chase.
    The interpreter routes by address and ignores the kind (the reservation
    lives behind the platform axioms), so the memory effect is the plain
    one's; only the recorded [classify] differs.  Mirrors of
    [WpLoad.exec_read_ram_resv_8] / [WpMmodeLeafBase.exec_write_ram_cond_8],
    by the [WeakLeafEff8] lockstep-peel technique. *)

Lemma exec_eff_read_ram_resv_8 (addr : mword 64) (w : bv 64) s :
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (read_ram rv64d_types.Read_RISCV_reserved (Physaddr addr) 8 false) s
    = Some ((w, default_meta), s, [WEread (AkInfo false true false) addr 8]).
Proof.
  intros Hdev Hbytes.
  pose proof (exec_read_ram_resv_8 addr w s Hdev Hbytes) as Hsc.
  unfold read_ram in Hsc |- *. cbn match in Hsc |- *.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM _ s)) in Hsc.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  cbn beta zeta in Hsc |- *.
  unfold Defs.sail_mem_read in Hsc |- *. cbn beta zeta in Hsc |- *.
  unfold Defs.bind in Hsc |- *. cbn [Interface.iMon_bind] in Hsc |- *.
  rewrite exec_MemRead in Hsc; [| exact Hdev].
  rewrite exec_eff_MemRead; [| exact Hdev].
  cbn [Interface.ReadReq.pa Interface.ReadReq.access_kind
       ConcurrencyInterfaceTypes.Mem_read_request_pa
       ConcurrencyInterfaceTypes.Mem_read_request_access_kind] in Hsc |- *.
  match goal with
  | |- context [ read_bytes ?mm ?pp ?nn ] =>
      destruct (read_bytes mm pp nn) as [w0|] eqn:Hrb
  end; [| discriminate].
  cbn [Interface.iMon_bind] in Hsc |- *. cbn match beta iota in Hsc |- *.
  rewrite exec_returnM in Hsc. rewrite exec_eff_returnM.
  cbn match beta iota.
  match goal with
  | |- context [ classify ?a ] =>
      replace (classify a) with (AkInfo false true false)
        by (vm_compute; reflexivity)
  end.
  change (Z.to_N 8) with 8%N.
  injection Hsc; intros; subst; reflexivity.
Qed.

Lemma exec_eff_write_ram_cond_8 (addr : mword 64) (data : bv 64) s :
  dev_addr addr = false ->
  exec_eff (write_ram rv64d_types.Write_RISCV_conditional (Physaddr addr) 8 data tt) s
  = Some (true, MState s.(sregs) (write_bytes s.(mem) addr 8 data) s.(mdev),
          [WEwrite (AkInfo false true false) addr 8 data]).
Proof.
  intros Hdev.
  unfold write_ram. cbn match.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_returnM _ s)).
  cbn beta zeta.
  unfold Defs.sail_mem_write. cbn beta zeta iota match.
  unfold Defs.bind. cbn [Interface.iMon_bind].
  cbn match.
  rewrite exec_eff_MemWrite; last exact Hdev.
  reflexivity.
Qed.

(* ====================================================================== *)
(** ** 2. The PTE-STORE gates

    The PMA check of the PTE store gates on the DISTINCT field
    [PMA_supports_pte_write] (not [PMA_writable]), and — the fork's
    mem.sail change — the PTE arms carry NO [assert(not(res_or_con))], so
    ONE lemma serves the plain and the conditional write
    ([PtTreeAdue.exec_pmaCheck_ram_wpte]/[_con] collapsed, exactly as
    [WeakWalkEff.exec_eff_pmaCheck_ram_pte] did for the read).  Then the
    S-mode PMP grant at [Store PageTableEntry]
    ([PtTreeAdue.exec_pmpCheck_supervisor_grant_wpte]).  All register-only. *)

Lemma exec_eff_is_mag_applicable_store_pte (width : Z) s :
  exec_eff (is_mag_applicable_access (Store PageTableEntry) width) s
  = Some (false, s, []).
Proof. apply exec_eff_returnM. Qed.

Lemma exec_eff_pmaCheck_ram_wpte (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) (res_or_con : bool) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_supports_pte_write) = true ->
  exec_eff (pmaCheck (Physaddr addr) 8 (Store PageTableEntry) pbmt res_or_con) s
  = Some (Ok pma_ok_aligned, s, []).
Proof.
  intros Hmatch Halign Hwrite.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_eff_peel Hmatch Hwrite (exec_eff_is_mag_applicable_store_pte 8 s) Halign.
Qed.

Lemma exec_eff_pmpCheck_supervisor_grant_wpte (a : mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec_eff (pmpCheck (Physaddr a) width (Store PageTableEntry) Supervisor) s
  = Some (None, s, []).
Proof.
  intros HA Hord Hrange HW.
  unfold pmpCheck. rewrite exec_eff_catch_early_return.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  rewrite execR_eff_bind0_eq.
  match goal with |- context[foreach_ZM_up ?F ?T ?S ?V ?B] =>
    assert (Hfe : execR_eff (foreach_ZM_up F T S V B) s = Some (inl None, s, [])) end.
  { unfold foreach_ZM_up. cbn [foreach_ZM_up'].
    rewrite execR_eff_bind_eq.
    rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)). cbn beta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_pmpReadAddrReg_val 0 s)). cbn beta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _
               (exec_eff_pmpMatchAddr_TOR_match a (to_bits 64 width)
                  (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                  (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
                  (zeros' 64) s HA Hord Hrange)). cbn beta.
    cbn match.
    unfold or_boolM.
    rewrite execR_eff_bind_eq.
    rewrite (execR_eff_liftR_seq _ _ _ _ _
               (_ : exec_eff (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
                            (Store PageTableEntry)) s = Some (true, s, []))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_eff_returnm. }
    cbn match. rewrite execR_eff_returnR. cbn beta.
    cbn match. rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match.
    unfold early_return, throw. cbn [execR_eff]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 3. THE EXCLUSIVE PTE READ — the CAS's read half

    [SmodePte.exec_read_pte_exclusive_S] replayed; identical to
    [WeakWalkEff.exec_eff_read_pte_S] except for the [res_or_con] flag,
    which selects the reserved read kind — and which the PTE arm of
    [pmaCheck] no longer asserts against, precisely so this is legal.  The
    trace element is §1's [WEread (AkInfo false true false) addr 8]. *)

Lemma exec_eff_read_pte_exclusive_S (addr : mword 64)
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
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
  exec_eff (within_clint (Physaddr addr) 8) s = Some (false, s, []) ->
  exec_eff (within_sig (Physaddr addr) 8) s = Some (false, s, []) ->
  exec_eff (within_htif_readable (Physaddr addr) 8) s = Some (false, s, []) ->
  dev_addr addr = false ->
  (forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add addr j) = Some (nth_byte w j)) ->
  exec_eff (read_pte_exclusive (Physaddr addr) 8) s
  = Some (Ok w, s, [WEread (AkInfo false true false) addr 8]).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  assert (Hcp : exec_eff (check_pma_with_pmp_priority (Load PageTableEntry) PBMT_PMA Supervisor
                            (Physaddr addr) 8 true) s = Some (Ok pma_ok_aligned, s, [])).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_pmaCheck_ram_pte addr region true s Hmatch Halign Hread)).
    cbn match. apply exec_eff_returnM. }
  assert (Hmmio : exec_eff (within_mmio_readable (Physaddr addr) 8) s = Some (false, s, [])).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
  assert (Hchk : exec_eff (checked_mem_read (Load PageTableEntry) PBMT_PMA Supervisor
                             (Physaddr addr) 8 false false true false) s
                 = Some (Ok (w, default_meta), s, [WEread (AkInfo false true false) addr 8])).
  { unfold checked_mem_read. rewrite exec_eff_catch_early_return.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
    rewrite (execR_eff_liftR_seq _ _ _ _ _
               (exec_eff_split_misaligned_unsplit addr 8 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _
               (_ : exec_eff (read_kind_of_flags false false true) s
                    = Some (rv64d_types.Read_RISCV_reserved, s, []))).
    2:{ unfold read_kind_of_flags. apply exec_eff_returnM. }
    cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
      assert (Hu : execR_eff (Defs.untilMT vs m c b) s
                   = Some (inr (w, true, 0), s, [WEread (AkInfo false true false) addr 8])) end.
    { eapply execR_eff_untilMT_1; [ reflexivity | | apply execR_eff_returnR ].
      rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr addr)) with addr.
      rewrite avi0_mul8.
      rewrite (execR_eff_liftR_seq _ _ _ _ _
                 (exec_eff_pmpCheck_supervisor_grant_load addr 8 s HA Hord Hrange HR)).
      cbn beta. cbn match.
      match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
        assert (Hseq : execR_eff (Defs.bind0 a b) s = Some (inr false, s, [])) end.
      { rewrite execR_eff_bind0_eq. rewrite execR_eff_returnR. cbn match.
        rewrite execR_eff_liftR. rewrite Hmmio. reflexivity. }
      rewrite (execR_eff_bind_nil _ _ _ _ _ Hseq). cbn beta. cbn match.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk ?pp ?wd ?mt)) ?k1) _] =>
        assert (Hrd : execR_eff (Defs.bind (Defs.liftR (read_ram rk pp wd mt)) k1) s
                      = Some (inr w, s, [WEread (AkInfo false true false) addr 8])) end.
      { rewrite (execR_eff_liftR_cat _ _ _ _ _ _
                   (exec_eff_read_ram_resv_8 addr w s Hdev Hbytes)).
        cbn beta match. rewrite execR_eff_returnR. cbn [app]. reflexivity. }
      rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hrd). cbn beta zeta.
      rewrite autocast_id. rewrite usvd_zeros_full_64.
      rewrite execR_eff_returnR. cbn [app]. reflexivity. }
    rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hu). cbn beta zeta.
    rewrite autocast_id. rewrite execR_eff_returnR. cbn [app]. reflexivity. }
  unfold read_pte_exclusive, mem_read_priv.
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (_ : exec_eff (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s
                 = Some (Ok (w, default_meta), s, [WEread (AkInfo false true false) addr 8]))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hchk).
      cbn match. unfold mem_read_callback. rewrite exec_eff_returnM.
      cbn [app]. reflexivity. }
  cbn [MemoryOpResult_drop_meta]. rewrite exec_eff_returnM.
  cbn [app]. reflexivity.
Qed.

(** [PtTree.pt_read_pte_exclusive_slot] replayed — [WeakWalkEff.wpt_read_pte_slot]
    with the exclusive brick. *)
Lemma wpt_read_pte_exclusive_slot (sg : mstate) (a w : mword 64)
    (region : PMA_Region) :
  pt_slot_mem sg a w ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
  (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
  matching_pma_region (register_lookup pma_regions sg.(sregs)) (Physaddr a) 8 = Some region ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
  register_lookup htif_tohost_base sg.(sregs) = None ->
  exec_eff (read_pte_exclusive (Physaddr a) 8) sg
  = Some (Ok w, sg, [WEread (AkInfo false true false) a 8]).
Proof.
  intros (Hbytes & Hram & Hram7 & Halign) HA Hord HR Hcov Hmatch Hpma Hhtif.
  assert (Hnw : (uint a + Z.of_nat 7 < 18446744073709551616)%Z).
  { destruct Hram as [_ Hh]. unfold ram_base, ram_size in Hh.
    change (Z.of_nat 7) with 7. lia. }
  assert (Hfit : (uint a + 8 <= ram_base + ram_size)%Z).
  { pose proof (uint_pa_add a 7 Hnw) as Heq.
    destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7.
    change (Z.of_nat 7) with 7 in Hhi7.
    unfold ram_base, ram_size in *. lia. }
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0)) 4)
            (uint a) (uint (to_bits 64 8)) = PMP_Match).
  { apply (ram_pmp_match_w a _ 8); [lia | vm_compute; reflexivity | | exact Hfit | exact Hcov].
    destruct Hram as [Hlo _]. exact Hlo. }
  apply (exec_eff_read_pte_exclusive_S a region w sg HA Hord Hrange HR Hmatch Halign Hpma).
  - apply exec_eff_within_clint_false; [apply addr_is_ram_not_in_clint; exact Hram | lia].
  - apply exec_eff_within_sig_false; [apply addr_is_ram_not_in_sig; exact Hram | lia].
  - apply exec_eff_within_htif_false. exact Hhtif.
  - apply addr_is_ram_not_dev. exact Hram.
  - exact Hbytes.
Qed.

(* ====================================================================== *)
(** ** 4. THE CONDITIONAL PTE WRITE — the CAS's write half

    [PtTreeAdue.exec_write_pte_conditional_ram] replayed: memory gains the
    8 bytes, registers and the device untouched, and the trace is §1's
    [WEwrite (AkInfo false true false) a 8 w'].  The [con = true] path's
    (rl ∥ con) alignment guard is live and false (the PTE is 8-aligned),
    and the PTE arm of [pmaCheck] does not assert against res_or_con —
    the fork's mem.sail change, taken through §2's res_or_con-generic
    gate. *)

Lemma exec_eff_write_pte_conditional_ram (a : mword 64) (w' : mword 64)
    (region : PMA_Region) s :
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
  exec_eff (write_pte_conditional (Physaddr a) 8 (w' : mword 64)) s
  = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) a 8 w') s.(mdev),
          [WEwrite (AkInfo false true false) a 8 w']).
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
  pose proof (exec_eff_within_clint_false a 8 s (addr_is_ram_not_in_clint _ Hram) ltac:(lia)) as Hc.
  pose proof (exec_eff_within_sig_false a 8 s (addr_is_ram_not_in_sig _ Hram) ltac:(lia)) as Hsig.
  pose proof (exec_eff_within_htif_w_false a 8 s Hhtif) as Hh.
  pose proof (addr_is_ram_not_dev _ Hram) as Hdev.
  assert (Hchk : exec_eff (checked_mem_write (Physaddr a) 8 (w' : mword 64) (Store PageTableEntry)
                        PBMT_PMA Supervisor tt false false true) s
                 = Some (Ok true, MState s.(sregs) (write_bytes s.(mem) a 8 w') s.(mdev),
                         [WEwrite (AkInfo false true false) a 8 w'])).
  { assert (Hcp : exec_eff (check_pma_with_pmp_priority (Store PageTableEntry) PBMT_PMA
                          Supervisor (Physaddr a) 8 true) s = Some (Ok pma_ok_aligned, s, [])).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_eff_bind_nil _ _ _ _ _
                 (exec_eff_pmaCheck_ram_wpte a PBMT_PMA region true s Hmatch Halign Hwr)).
      cbn match. apply exec_eff_returnM. }
    assert (Hmmio : exec_eff (within_mmio_writable (Physaddr a) 8) s = Some (false, s, [])).
    { unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
      rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
    set (sw := MState s.(sregs) (write_bytes s.(mem) a 8 w') s.(mdev)).
    unfold checked_mem_write. rewrite exec_eff_catch_early_return.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_split_misaligned_unsplit a 8 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _
               (_ : exec_eff (write_kind_of_flags false false true) s
                    = Some (rv64d_types.Write_RISCV_conditional, s, []))).
    2:{ unfold write_kind_of_flags. cbn match. apply exec_eff_returnM. }
    cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?b) _] =>
      assert (Hu : execR_eff (Defs.untilMT vs m0 c b) s
                   = Some (inr (true, 0, true), sw,
                           [WEwrite (AkInfo false true false) a 8 w'])) end.
    { eapply execR_eff_untilMT_1; [ reflexivity | | apply execR_eff_returnR ].
      rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_assert_exp'_true _ s)). cbn beta.
      change (bits_of_physaddr (Physaddr a)) with a.
      rewrite avi0_mul8.
      rewrite (execR_eff_liftR_seq _ _ _ _ _
                 (exec_eff_pmpCheck_supervisor_grant_wpte a 8 s HA Hord Hrange HW)).
      cbn beta. cbn match.
      rewrite execR_eff_bind0_eq. rewrite execR_eff_returnR. cbn match zeta.
      rewrite (execR_eff_liftR_seq _ _ _ _ _ Hmmio). cbn beta. cbn match.
      rewrite autocast_id.
      change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
      rewrite subrange_full_64.
      match goal with
        |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk ?pa ?wd ?dt ?mt)) ?k1) _] =>
        assert (Hwr2 : execR_eff (Defs.bind (Defs.liftR (write_ram wk pa wd dt mt)) k1) s
                       = Some (inr true, sw,
                               [WEwrite (AkInfo false true false) a 8 w'])) end.
      { rewrite (execR_eff_liftR_cat _ _ _ _ _ _ (exec_eff_write_ram_cond_8 a w' s Hdev)).
        cbn beta. cbn [andb]. rewrite execR_eff_returnR. cbn [app]. reflexivity. }
      rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hwr2). cbn beta zeta.
      rewrite execR_eff_returnR. cbn [app]. reflexivity. }
    rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hu). cbn beta zeta.
    rewrite execR_eff_returnR. cbn [app]. reflexivity. }
  unfold write_pte_conditional, mem_write_value_priv, mem_write_value_priv_meta.
  cbn [orb andb Riscv.rv64d.not negb].
  rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hchk).
  cbn match. unfold mem_write_callback. rewrite exec_eff_returnM.
  cbn [app]. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 5. [update_and_write_pte]'s OUTCOME ARMS, level-generic

    The SC tree proves these inline (the [assert Hu] blocks of
    [PtTreeAdue] §3/§4); here each arm is its own lemma so the heads AND
    future 6c consumers share them.  Every memory step enters as an
    [exec_eff] PREMISE, so the arms are pure bind-spine plumbing — and the
    Err arms cover the "failed" outcomes without any PMP/PMA-failure
    machinery (the failure is the premise; under [wkpt_inv] they are
    unreachable, which is why SC has no reduction lemmas for them). *)

Section UpdArmsEff.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (** The Svadu/ADUE gate, factored (the SC scripts inline it three
      times).  Register-only, empty trace. *)
  Local Ltac uawp_gate Hmenv HADUE st :=
    match goal with |- context[Defs.bind (or_boolM ?A ?B) ?k] =>
      let Hgt := fresh "Hgt" in
      assert (Hgt : exec_eff (or_boolM A B) st = Some (true, st, []));
      [ match goal with |- exec_eff (or_boolM ?A' ?B') st = _ =>
          let Hand := fresh "Hand" in
          assert (Hand : exec_eff A' st = Some (true, st, []));
          [ unfold and_boolM;
            rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_currentlyEnabled_Svadu st));
            cbn match;
            rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg menvcfg st));
            cbn beta; rewrite Hmenv; rewrite HADUE; apply exec_eff_returnm
          | unfold or_boolM;
            rewrite (exec_eff_bind_nil _ _ _ _ _ Hand);
            cbn match; apply exec_eff_returnm ]
        end
      | rewrite (exec_eff_bind_nil _ _ _ _ _ Hgt); cbn match zeta ]
    end.

  (** O-UNCHANGED: [update_PTE_Bits stale = None].  The model returns
      IMMEDIATELY — no Svadu probe, no menvcfg read, and crucially NO
      MEMORY READ: the trace is empty on the nose (this is the answer the
      quiet certificates needed; the arm rides [wcert_nowrite] at whatever
      surrounding trace the instruction has). *)
  Lemma exec_eff_update_and_write_pte_none (vpn : mword 27) (a : physaddr)
        (stale : mword 64) (lvl : Z) s :
    update_PTE_Bits (stale : mword 64) acc = None ->
    exec_eff (update_and_write_pte 39 vpn a stale lvl acc p mxr do_sum tt) s
    = Some (Ok (None, tt), s, []).
  Proof.
    intros Hnoupd. unfold update_and_write_pte.
    match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
      assert (Hn : @update_PTE_Bits w pv ac = None) by exact Hnoupd end.
    rewrite Hn. cbn match. apply exec_eff_returnm.
  Qed.

  (** O-FRESH: the stale word gated the update ON, but the freshly read
      word already has the bits — read only, no write, state unchanged.
      (Reachable only on the TLB-HIT path: in one [exec_eff] run the
      miss-path fresh word IS the walked word.) *)
  Lemma exec_eff_update_and_write_pte_fresh (vpn : mword 27) (a : mword 64)
        (stale g fresh : mword 64) (lvl : Z) (ppn0 : mword 44)
        (pb : page_based_mem_type) (menvcfg0 : mword 64) (es_x : list weff) s :
    update_PTE_Bits (stale : mword 64) acc = Some g ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec_eff (read_pte_exclusive (Physaddr a) 8) s = Some (Ok fresh, s, es_x) ->
    exec_eff (check_leaf_pte 39 vpn acc p mxr do_sum fresh (Physaddr a) lvl tt) s
      = Some (Ok (ppn0, pb, tt), s, []) ->
    update_PTE_Bits (fresh : mword 64) acc = None ->
    exec_eff (update_and_write_pte 39 vpn (Physaddr a) stale lvl acc p mxr do_sum tt) s
    = Some (Ok (Some fresh, tt), s, es_x).
  Proof.
    intros Hgate Hmenv HADUE Hrdx Hchk Hupd.
    unfold update_and_write_pte.
    match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
      assert (Hg : @update_PTE_Bits w pv ac = Some g) by exact Hgate end.
    rewrite Hg. cbn match.
    uawp_gate Hmenv HADUE s.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hrdx). cbn match beta.
    rewrite autocast_id.
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hchk). cbn match beta.
    match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
      assert (Hf : @update_PTE_Bits w pv ac = None) by exact Hupd end.
    rewrite Hf. cbn match. rewrite ?autocast_id.
    rewrite exec_eff_returnm. by rewrite ?app_nil_r.
  Qed.

  (** O-WRITTEN: the fresh word still needs bits — the conditional write
      lands and the trace is THE ADJACENT CAS PAIR [es_x ++ es_w] (at the
      singleton premises: read then write, back to back, the
      [wcert_amo_aq_gen]-family shape §9 certifies). *)
  Lemma exec_eff_update_and_write_pte_written (vpn : mword 27) (a : mword 64)
        (stale g fresh fresh' : mword 64) (lvl : Z) (ppn0 : mword 44)
        (pb : page_based_mem_type) (menvcfg0 : mword 64)
        (es_x es_w : list weff) (sw : mstate) s :
    update_PTE_Bits (stale : mword 64) acc = Some g ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec_eff (read_pte_exclusive (Physaddr a) 8) s = Some (Ok fresh, s, es_x) ->
    exec_eff (check_leaf_pte 39 vpn acc p mxr do_sum fresh (Physaddr a) lvl tt) s
      = Some (Ok (ppn0, pb, tt), s, []) ->
    update_PTE_Bits (fresh : mword 64) acc = Some fresh' ->
    exec_eff (write_pte_conditional (Physaddr a) 8 (fresh' : mword 64)) s
      = Some (Ok true, sw, es_w) ->
    exec_eff (update_and_write_pte 39 vpn (Physaddr a) stale lvl acc p mxr do_sum tt) s
    = Some (Ok (Some fresh', tt), sw, (es_x ++ es_w)%list).
  Proof.
    intros Hgate Hmenv HADUE Hrdx Hchk Hupd Hwrite.
    unfold update_and_write_pte.
    match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
      assert (Hg : @update_PTE_Bits w pv ac = Some g) by exact Hgate end.
    rewrite Hg. cbn match.
    uawp_gate Hmenv HADUE s.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hrdx). cbn match beta.
    rewrite autocast_id.
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hchk). cbn match beta.
    match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
      assert (Hf : @update_PTE_Bits w pv ac = Some fresh') by exact Hupd end.
    rewrite Hf. cbn match. rewrite autocast_id.
    match goal with |- context[Defs.bind (write_pte_conditional ?aa' ?wd' ?pv') ?k] =>
      assert (Hwrite' : exec_eff (write_pte_conditional aa' wd' pv') s
                        = Some (Ok true, sw, es_w)) by exact Hwrite end.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hwrite').
    cbn match. rewrite ?autocast_id. rewrite exec_eff_returnm.
    by rewrite ?app_nil_r.
  Qed.

  (** The three FAILED funnels — result-generic; the failing memory step is
      a premise.  [Ok false] from the conditional write (a lost race) is an
      [internal_error] in the model and has no lemma: the machine has no
      other hart inside one [exec_eff] step, so the CAS cannot lose. *)

  (* the exclusive read faults (PMP/PMA on the PTE slot) *)
  Lemma exec_eff_update_and_write_pte_read_err (vpn : mword 27) (a : physaddr)
        (stale g : mword 64) (lvl : Z) (menvcfg0 : mword 64)
        (ex : physaddr * ExceptionType) (es_x : list weff) (s s' : mstate) :
    update_PTE_Bits (stale : mword 64) acc = Some g ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec_eff (read_pte_exclusive a 8) s = Some (Err ex, s', es_x) ->
    exec_eff (update_and_write_pte 39 vpn a stale lvl acc p mxr do_sum tt) s
    = Some (Err (PTW_No_Access tt, tt), s', es_x).
  Proof.
    intros Hgate Hmenv HADUE Hrdx.
    unfold update_and_write_pte.
    match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
      assert (Hg : @update_PTE_Bits w pv ac = Some g) by exact Hgate end.
    rewrite Hg. cbn match.
    uawp_gate Hmenv HADUE s.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hrdx). cbn match beta.
    rewrite exec_eff_returnm. by rewrite ?app_nil_r.
  Qed.

  (* the re-check fails on the fresh word (its PTW error propagates) *)
  Lemma exec_eff_update_and_write_pte_recheck_err (vpn : mword 27) (a : mword 64)
        (stale g fresh : mword 64) (lvl : Z) (menvcfg0 : mword 64)
        (e : PTW_Error) (es_x : list weff) s :
    update_PTE_Bits (stale : mword 64) acc = Some g ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec_eff (read_pte_exclusive (Physaddr a) 8) s = Some (Ok fresh, s, es_x) ->
    exec_eff (check_leaf_pte 39 vpn acc p mxr do_sum fresh (Physaddr a) lvl tt) s
      = Some (Err (e, tt), s, []) ->
    exec_eff (update_and_write_pte 39 vpn (Physaddr a) stale lvl acc p mxr do_sum tt) s
    = Some (Err (e, tt), s, es_x).
  Proof.
    intros Hgate Hmenv HADUE Hrdx Hchk.
    unfold update_and_write_pte.
    match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
      assert (Hg : @update_PTE_Bits w pv ac = Some g) by exact Hgate end.
    rewrite Hg. cbn match.
    uawp_gate Hmenv HADUE s.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hrdx). cbn match beta.
    rewrite autocast_id.
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hchk). cbn match beta.
    rewrite exec_eff_returnm. by rewrite ?app_nil_r.
  Qed.

  (* the conditional write faults (PMP/PMA on the PTE store) *)
  Lemma exec_eff_update_and_write_pte_write_err (vpn : mword 27) (a : mword 64)
        (stale g fresh fresh' : mword 64) (lvl : Z) (ppn0 : mword 44)
        (pb : page_based_mem_type) (menvcfg0 : mword 64)
        (ex : physaddr * ExceptionType) (es_x es_w : list weff) (sw : mstate) s :
    update_PTE_Bits (stale : mword 64) acc = Some g ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec_eff (read_pte_exclusive (Physaddr a) 8) s = Some (Ok fresh, s, es_x) ->
    exec_eff (check_leaf_pte 39 vpn acc p mxr do_sum fresh (Physaddr a) lvl tt) s
      = Some (Ok (ppn0, pb, tt), s, []) ->
    update_PTE_Bits (fresh : mword 64) acc = Some fresh' ->
    exec_eff (write_pte_conditional (Physaddr a) 8 (fresh' : mword 64)) s
      = Some (Err ex, sw, es_w) ->
    exec_eff (update_and_write_pte 39 vpn (Physaddr a) stale lvl acc p mxr do_sum tt) s
    = Some (Err (PTW_No_Access tt, tt), sw, (es_x ++ es_w)%list).
  Proof.
    intros Hgate Hmenv HADUE Hrdx Hchk Hupd Hwrite.
    unfold update_and_write_pte.
    match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
      assert (Hg : @update_PTE_Bits w pv ac = Some g) by exact Hgate end.
    rewrite Hg. cbn match.
    uawp_gate Hmenv HADUE s.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hrdx). cbn match beta.
    rewrite autocast_id.
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hchk). cbn match beta.
    match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
      assert (Hf : @update_PTE_Bits w pv ac = Some fresh') by exact Hupd end.
    rewrite Hf. cbn match. rewrite autocast_id.
    match goal with |- context[Defs.bind (write_pte_conditional ?aa' ?wd' ?pv') ?k] =>
      assert (Hwrite' : exec_eff (write_pte_conditional aa' wd' pv') s
                        = Some (Err ex, sw, es_w)) by exact Hwrite end.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hwrite').
    cbn match. rewrite exec_eff_returnm.
    by rewrite ?app_nil_r.
  Qed.

End UpdArmsEff.

(* ====================================================================== *)
(** ** 6. The TLB plumbing: the GENERIC level-0 fill and [write_TLB]

    [PtTreeAdue.exec_add_to_TLB_pt] replayed ([WeakWalkEff]'s
    [exec_eff_add_to_TLB_user] is its no-update specialization), and the
    hit path's in-place refresh.  Register-only, empty trace; the pure
    entry identifications ([pt_fill_ent_uwe], [tlb_set_pte_uwe]) are
    [PtTreeAdue]'s, reused. *)

Lemma exec_eff_add_to_TLB_pt (asid : mword 16) (vpn : mword 27) (pp : mword 44)
    (pte : mword 64) (ptea : physaddr) (g : bool) s :
  exec_eff (add_to_TLB 39 asid vpn pp pte ptea 0 g) s
  = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                               (tlb_hash (__id 39) vpn)
                               (Some (pt_fill_ent asid vpn pp pte ptea g))), []).
Proof.
  unfold add_to_TLB. cbn zeta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg tlb s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_write_reg tlb _ s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg tlb _)).
  rewrite exec_eff_returnm.
  reflexivity.
Qed.

Lemma exec_eff_write_TLB (ix : Z) (en : TLB_Entry) s :
  exec_eff (write_TLB ix en) s
  = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs)) ix
                               (Some en)), []).
Proof.
  unfold write_TLB.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg tlb s)).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_write_reg tlb _ s)).
  apply exec_eff_returnm.
Qed.

(* ====================================================================== *)
(** ** 7. THE WRITE-BACK TRANSLATE HEADS — [PtTreeAdue] §3/§4 replayed

    The O3 arms: a MISS whose walked leaf needs bits (write-back + TLB
    fill with the UPDATED word), a HIT whose cached word needs bits and
    whose fresh word still does (write-back + in-place refresh with the
    word DERIVED FROM MEMORY, not the cache), and a HIT whose fresh word
    already has them (no write, refresh only).  Premise shapes are
    [WeakWalkEff]'s ([wpte_*] eff twins, trace-generic reads); the update
    machinery is §5's arms.  The post-write state [sw] stays abstract with
    [sw.(sregs) = s.(sregs)], exactly as in SC. *)

Section PtUpdEff.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  Lemma exec_eff_translate_TLB_miss_user_upd (vpn : mword 27) (root : mword 44)
        (p2 p1 p0 p0' : mword 64) (menvcfg0 : mword 64) (asid : mword 16)
        (es2 es1 es0 es_x es_w : list weff) (sw : mstate) s :
    wpte_valid p2 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p2 7 0)) = true ->
    wpte_valid p1 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p1 7 0)) = true ->
    wpte_valid p0 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p0 7 0)) = false ->
    wpte_check_ok acc p mxr do_sum p0 ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE p0)) ('b"1") = false ->
    update_PTE_Bits (p0 : mword 64) acc = Some p0' ->
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok p2, s, es2) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok p1, s, es1) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok p0, s, es0) ->
    (* the CAS re-reads the leaf exclusively; same memory, same word *)
    exec_eff (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok p0, s, es_x) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec_eff (write_pte_conditional (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
            (p0' : mword 64)) s
      = Some (Ok true, sw, es_w) ->
    sw.(sregs) = s.(sregs) ->
    exec_eff (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44), PBMT_PMA, tt),
            set_reg sw tlb (vec_update_dec (register_lookup tlb s.(sregs))
                              (tlb_hash (__id 39) vpn)
                              (Some (u_walk_entry vpn p2 p1 p0' asid))),
            ((es2 ++ es1 ++ es0) ++ es_x ++ es_w)%list).
  Proof.
    intros Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk H0N Hupd
           Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv HPBMTE HADUE Hwrite Hswregs.
    unfold translate_TLB_miss. cbn zeta.
    match goal with |- context[pt_walk 39 _ _ _ _ _ _ ?l false ?e] =>
      change l with 2 end.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _
               (exec_eff_pt_walk_user vpn root p2 p1 p0 acc p mxr do_sum
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk H0N menvcfg0 es2 es1 es0 s
                  Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
    cbn match. cbn zeta.
    (* the CAS: exclusive re-read, re-check on the fresh word (= the walked
       word, same memory), recompute, conditional write — §5's written arm *)
    match goal with |- context[update_and_write_pte ?w ?vp ?aa ?pv ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hu : exec_eff (update_and_write_pte w vp aa pv lv ac pr mx ds e) s
                   = Some (Ok (Some p0', tt), sw, (es_x ++ es_w)%list)) end.
    { exact (exec_eff_update_and_write_pte_written acc p mxr do_sum vpn
               (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))
               p0 p0' p0 p0' 0
               (autocast (T := mword) (PPN_of_PTE p0)) PBMT_PMA menvcfg0
               es_x es_w sw s Hupd Hmenv HADUE Hrdx
               (exec_eff_check_leaf_pte_leaf0 vpn p0 acc p mxr do_sum
                  Hv0 Hl0 Hchk H0N
                  (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)))
                  menvcfg0 s Hmisa Hmenv HPBMTE)
               Hupd Hwrite). }
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hu).
    cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_add_to_TLB_pt asid vpn _ _ _ _ sw)).
    rewrite exec_eff_returnm.
    rewrite Hswregs.
    destruct (update_PTE_Bits_set_ad _ _ _ Hupd) as (a & d & Hq).
    match goal with |- context[pt_fill_ent ?asx ?vpx ?ppx ?ptx ?pax ?gx] =>
      assert (Hent : pt_fill_ent asx vpx ppx ptx pax gx
                     = u_walk_entry vpn p2 p1 p0' asid)
        by exact (pt_fill_ent_uwe vpn p2 p1 p0 p0' asid a d Hq) end.
    rewrite Hent.
    by rewrite ?app_nil_r.
  Qed.

  (** HIT + write-back.  The cached word [q0] and the MEMORY word [m0]
      agree only up to A/D (the TLB invariant); the CAS recomputes on
      [m0], so the value written back — and installed — derives from
      MEMORY, never the cache.  The gate is still the cached word. *)
  Lemma exec_eff_translate_TLB_hit_pt_upd (vpn : mword 27)
        (q2 q1 q0 q0g m0 m0' : mword 64) (menvcfg0 : mword 64)
        (asid : mword 16) (idx : Z) (es_x es_w : list weff) (sw : mstate) s :
    wpte_check_ok acc p mxr do_sum q0 ->
    update_PTE_Bits (q0 : mword 64) acc = Some q0g ->
    pte_pbmt0 q0 ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec_eff (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok m0, s, es_x) ->
    wpte_valid m0 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec m0 7 0)) = false ->
    wpte_check_ok acc p mxr do_sum m0 ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE m0)) ('b"1") = false ->
    register_lookup misa s.(sregs) = MISA_C ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    (* the memory word is an A/D variant of the cached one: the TLB invariant *)
    (exists a2 d2 : mword 1, m0 = pte_set_ad q0 a2 d2) ->
    update_PTE_Bits (m0 : mword 64) acc = Some m0' ->
    exec_eff (write_pte_conditional (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8
            (m0' : mword 64)) s
      = Some (Ok true, sw, es_w) ->
    sw.(sregs) = s.(sregs) ->
    exec_eff (translate_TLB_hit 39 asid vpn acc p mxr do_sum tt idx
                (u_walk_entry vpn q2 q1 q0 asid)) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (q0 : mword 64))) : mword 44), PBMT_PMA, tt),
            set_reg sw tlb (vec_update_dec (register_lookup tlb s.(sregs)) idx
                              (Some (u_walk_entry vpn q2 q1 m0' asid))),
            (es_x ++ es_w)%list).
  Proof.
    intros Hchk Hgate Hpb Hmenv HADUE Hrdx Hv0 Hl0 Hchkm HmN Hmisa HPBMTE Hvar Hupd Hwrite Hswregs.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte.
    rewrite autocast_id.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (Hchk s)). cbn match.
    match goal with |- context[update_and_write_pte ?w ?vp ?aa ?pv ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hu : exec_eff (update_and_write_pte w vp aa pv lv ac pr mx ds e) s
                   = Some (Ok (Some m0', tt), sw, (es_x ++ es_w)%list)) end.
    { exact (exec_eff_update_and_write_pte_written acc p mxr do_sum vpn
               (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))
               q0 q0g m0 m0' 0
               (autocast (T := mword) (PPN_of_PTE m0)) PBMT_PMA menvcfg0
               es_x es_w sw s Hgate Hmenv HADUE Hrdx
               (exec_eff_check_leaf_pte_leaf0 vpn m0 acc p mxr do_sum
                  Hv0 Hl0 Hchkm HmN
                  (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)))
                  menvcfg0 s Hmisa Hmenv HPBMTE)
               Hupd Hwrite). }
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hu).
    cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_write_TLB idx _ sw)).
    (* [m0'] is an A/D variant OF THE CACHED WORD, so the entry's PPN and G
       fields (which [tlb_set_pte] keeps) still agree with it *)
    destruct Hvar as (a2 & d2 & Hm0).
    destruct (update_PTE_Bits_set_ad _ _ _ Hupd) as (a & d & Hq).
    assert (Hqc : m0' = pte_set_ad q0 a d)
      by (rewrite Hq; rewrite Hm0; apply pte_set_ad_absorb).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_uwe_pbmt vpn q2 q1 q0 asid _ Hpb)).
    rewrite uwe_ppn.
    rewrite exec_eff_returnm.
    rewrite Hswregs.
    match goal with |- context[tlb_set_pte ?en ?pv] =>
      assert (Hent : tlb_set_pte (n := 8) en pv = u_walk_entry vpn q2 q1 m0' asid)
        by exact (tlb_set_pte_uwe vpn q2 q1 q0 m0' asid a d Hqc) end.
    rewrite Hent.
    by rewrite ?app_nil_r.
  Qed.

  (** HIT + refresh: the fresh word already has the bits — no write, the
      entry is refreshed in place with the MEMORY word; trace = the CAS
      read alone. *)
  Lemma exec_eff_translate_TLB_hit_pt_refresh (vpn : mword 27)
        (q2 q1 q0 q0g m0 : mword 64) (menvcfg0 : mword 64)
        (asid : mword 16) (idx : Z) (es_x : list weff) s :
    wpte_check_ok acc p mxr do_sum q0 ->
    update_PTE_Bits (q0 : mword 64) acc = Some q0g ->
    pte_pbmt0 q0 ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec_eff (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok m0, s, es_x) ->
    wpte_valid m0 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec m0 7 0)) = false ->
    wpte_check_ok acc p mxr do_sum m0 ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE m0)) ('b"1") = false ->
    register_lookup misa s.(sregs) = MISA_C ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    (exists a2 d2 : mword 1, m0 = pte_set_ad q0 a2 d2) ->
    update_PTE_Bits (m0 : mword 64) acc = None ->
    exec_eff (translate_TLB_hit 39 asid vpn acc p mxr do_sum tt idx
                (u_walk_entry vpn q2 q1 q0 asid)) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (q0 : mword 64))) : mword 44), PBMT_PMA, tt),
            set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs)) idx
                             (Some (u_walk_entry vpn q2 q1 m0 asid))),
            es_x).
  Proof.
    intros Hchk Hgate Hpb Hmenv HADUE Hrdx Hv0 Hl0 Hchkm HmN Hmisa HPBMTE Hvar Hupd.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte.
    rewrite autocast_id.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (Hchk s)). cbn match.
    match goal with |- context[update_and_write_pte ?w ?vp ?aa ?pv ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hu : exec_eff (update_and_write_pte w vp aa pv lv ac pr mx ds e) s
                   = Some (Ok (Some m0, tt), s, es_x)) end.
    { exact (exec_eff_update_and_write_pte_fresh acc p mxr do_sum vpn
               (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))
               q0 q0g m0 0
               (autocast (T := mword) (PPN_of_PTE m0)) PBMT_PMA menvcfg0
               es_x s Hgate Hmenv HADUE Hrdx
               (exec_eff_check_leaf_pte_leaf0 vpn m0 acc p mxr do_sum
                  Hv0 Hl0 Hchkm HmN
                  (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)))
                  menvcfg0 s Hmisa Hmenv HPBMTE)
               Hupd). }
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hu).
    cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_write_TLB idx _ s)).
    destruct Hvar as (a2 & d2 & Hm0).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_uwe_pbmt vpn q2 q1 q0 asid _ Hpb)).
    rewrite uwe_ppn.
    rewrite exec_eff_returnm.
    match goal with |- context[tlb_set_pte ?en ?pv] =>
      assert (Hent : tlb_set_pte (n := 8) en pv = u_walk_entry vpn q2 q1 m0 asid)
        by exact (tlb_set_pte_uwe vpn q2 q1 q0 m0 asid a2 d2 Hm0) end.
    rewrite Hent.
    by rewrite ?app_nil_r.
  Qed.

End PtUpdEff.

(* ====================================================================== *)
(** ** 8. THE [translateAddr]-LEVEL COMPOSITION

    [WeakWalkEff]'s front head is OUTCOME-GENERIC (its [translate] premise
    binds an arbitrary successor state [s']), so the update-cone outcomes
    plug straight in through the two dispatchers.  One composed corollary
    is stated for the reachable-on-the-kernel-table case — the MISS whose
    leaf needs bits (the first store to a page) — as the seam validation;
    the HIT arms compose identically through
    [WeakWalkEff.exec_eff_translate_hit_user].  The check premise is
    ∀-mxr/do_sum because the front quantifies its [translate] premise so
    (the mstatus MXR/SUM reads happen INSIDE [translateAddr]); nothing
    else in the update path depends on them. *)

Section PtUpdFrontEff.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  Lemma exec_eff_translateAddr_pt_miss_upd (vpn : mword 27) (root : mword 44)
        (p2 p1 p0 p0' : mword 64) (satp0 va pa menvcfg0 : mword 64)
        (es2 es1 es0 es_x es_w : list weff) (sw : mstate) (s : mstate) :
    exec_eff (effectivePrivilege acc (register_lookup mstatus s.(sregs)) p) s
      = Some (p, s, []) ->
    exec_eff (is_shadow_stack_access acc) s = Some (false, s, []) ->
    register_lookup cur_privilege s.(sregs) = p ->
    exec_eff (translationMode p) s = Some (Sv39, s, []) ->
    register_lookup satp s.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s, []) ->
    wpte_valid p2 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p2 7 0)) = true ->
    wpte_valid p1 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p1 7 0)) = true ->
    wpte_valid p0 ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec p0 7 0)) = false ->
    (forall mxr do_sum, wpte_check_ok acc p mxr do_sum p0) ->
    eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE p0)) ('b"1") = false ->
    update_PTE_Bits (p0 : mword 64) acc = Some p0' ->
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok p2, s, es2) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok p1, s, es1) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok p0, s, es0) ->
    exec_eff (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok p0, s, es_x) ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec_eff (write_pte_conditional (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
            (p0' : mword 64)) s
      = Some (Ok true, sw, es_w) ->
    sw.(sregs) = s.(sregs) ->
    zero_extend' 64 (concat_vec
      (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44)
       : mword 44)
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    exec_eff (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw),
            set_reg sw tlb (vec_update_dec (register_lookup tlb s.(sregs))
                              (tlb_hash (__id 39) vpn)
                              (Some (u_walk_entry vpn p2 p1 p0' (mword_of_int 0)))),
            ((es2 ++ es1 ++ es0) ++ es_x ++ es_w)%list).
  Proof.
    intros Heff Hss Hcp Htm Hsatp Hppn Hasid Hcanon Hvpn_def Hlk
           Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchkall H0N Hupd
           Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv HPBMTE HADUE Hwrite Hswregs Hident.
    apply (exec_eff_translateAddr_pt_front acc p vpn root
             (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44)
              : mword 44)
             satp0 va pa _ s _
             Heff Hss Hcp Htm Hsatp Hppn Hasid Hcanon Hvpn_def);
      [| exact Hident].
    intros mxr do_sum.
    apply (exec_eff_translate_miss_user vpn root (mword_of_int 0) acc p mxr do_sum _ s _ _ Hlk).
    exact (exec_eff_translate_TLB_miss_user_upd acc p mxr do_sum vpn root
             p2 p1 p0 p0' menvcfg0 (mword_of_int 0) es2 es1 es0 es_x es_w sw s
             Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 (Hchkall mxr do_sum) H0N Hupd
             Hrd2 Hrd1 Hrd0 Hrdx Hmisa Hmenv HPBMTE HADUE Hwrite Hswregs).
  Qed.

End PtUpdFrontEff.

(* ====================================================================== *)
(** ** 9. THE CERTIFICATES for the CAS pair

    The walker's read half is [ak_latest] — PINNED BY KIND, so it needs
    neither a [trace_pin] entry nor any view hypothesis: its bridge
    admissibility IS [WeakMem.latest].  What the CAS pair certifies is
    therefore exactly a STORE's effect at width 8 — the message identity
    (the appended [wwrite_msg], which the invariant's leaf element is
    retargeted at) plus the store's view floor — i.e. [wQ_store_w 8], NOT
    [wQ_amo_aq_w]: the read is not [ak_sync] (no [.aq]), so there is no
    acquire gain, and none is needed (the read feeds only the PTE
    re-check).  Shape mirrors [WeakEff.wcert_store_gen] with the read
    adjacent, in both the whole-window ([wP_eff]) and the trace-pinned
    ([wP_eff_pin]) forms — the pin form is the one batch-6 consumers use
    (walk reads get the variant treatment via [trace_pin]; the CAS pair is
    exempt by kind).

    The quiet outcomes need no new certificates: O-UNCHANGED contributes
    NO events and O-FRESH/hit-refresh contribute a lone READ — both ride
    [WeakEff.wcert_nowrite] at the instruction's surrounding trace. *)

Lemma wcert_ptw_upd_gen (cid : nat) (pc : mword 64)
    (pre post : list weff) (akx akw : akinfo) (ea : Arch.pa) (v : bv 64) :
  nowrite_trace pre -> nowrite_trace post ->
  wstep_cert cid pc
    (wP_eff (Some cid) (pre ++ WEread akx ea 8 :: WEwrite akw ea 8 v :: post))
    (wQ_store_w 8 (Some cid) ea v).
Proof.
  intros Hpre Hpost. apply wstep_cert_eff. intros s s' Hi Hl Hws.
  assert (Hle : ws_le (wm_ws s) (wm_ws s')) by (rewrite Hws; apply weffs_ws_le).
  set (s1 := weffs (Some cid) s pre).
  assert (Hl1 : wm_log s1 = wm_log s)
    by exact (weffs_nowrite_log (Some cid) s pre Hpre).
  set (s2 := weff_apply (Some cid) s1 (WEread akx ea 8)).
  assert (Hl2 : wm_log s2 = wm_log s)
    by (subst s2; rewrite weff_apply_read wread_post_log; exact Hl1).
  set (s3 := weff_apply (Some cid) s2 (WEwrite akw ea 8 v)).
  assert (Hl3 : wm_log s3
                = (wm_log s ++ [wwrite_msg (Some cid)
                     (wm_class_of akw (wm_ws s2)) ea 8 v])%list).
  { subst s3. rewrite weff_apply_write /wwrite_post /= Hl2. reflexivity. }
  assert (Hlpost : wm_log (weffs (Some cid) s3 post) = wm_log s3)
    by exact (weffs_nowrite_log (Some cid) s3 post Hpost).
  assert (Hls' : wm_log s'
                 = (wm_log s ++ [wwrite_msg (Some cid)
                      (wm_class_of akw (wm_ws s2)) ea 8 v])%list).
  { rewrite Hl !weffs_app !weffs_cons -/s1 -/s2 -/s3 Hlpost Hl3. reflexivity. }
  rewrite /wQ_store_w /wV_store_w.
  split_and!; [exact Hi| |exact Hle|].
  { eexists. split; [exact Hls'|]. intros Hr. apply wm_class_of_relp.
    subst s2. rewrite weff_apply_read wread_post_relp. subst s1.
    by apply weffs_nowrite_relp. }
  intros j Hj.
  (* the floor reached at the write's own step survives the write-free tail *)
  assert (Hstep : (S (length (wm_log s))
                   ≤ flr (ws_view (wm_ws s3)) (acc_addr ea j))%nat).
  { subst s3. rewrite weff_apply_write wwrite_post_ws Hl2 flr_ws_view /acc_addr.
    etrans; [|apply Nat.le_max_r].
    exact (store_post_run_coh (wm_ws s2) (ak_sync akw) (pa_z ea) (N.to_nat 8)
             (S (length (wm_log s))) j Hj). }
  etrans; [exact Hstep|].
  rewrite Hws !weffs_app !weffs_cons -/s1 -/s2 -/s3.
  apply flr_ws_le, weffs_ws_le.
Qed.

(** The PIN form — same arithmetic over [wstep_cert_eff_pin] (the [P] was
    never used).  This is the certificate a walk-carrying instruction
    discharges: the fetch and the three walk reads land in [pre]/[post]
    under [trace_pin]'s variant treatment, the CAS pair is exempt by kind. *)
Lemma wcert_ptw_upd_pin (cid : nat) (pc : mword 64)
    (pre post : list weff) (akx akw : akinfo) (ea : Arch.pa) (v : bv 64) :
  nowrite_trace pre -> nowrite_trace post ->
  wstep_cert cid pc
    (wP_eff_pin (Some cid) (pre ++ WEread akx ea 8 :: WEwrite akw ea 8 v :: post))
    (wQ_store_w 8 (Some cid) ea v).
Proof.
  intros Hpre Hpost. apply wstep_cert_eff_pin. intros s s' Hi Hl Hws.
  assert (Hle : ws_le (wm_ws s) (wm_ws s')) by (rewrite Hws; apply weffs_ws_le).
  set (s1 := weffs (Some cid) s pre).
  assert (Hl1 : wm_log s1 = wm_log s)
    by exact (weffs_nowrite_log (Some cid) s pre Hpre).
  set (s2 := weff_apply (Some cid) s1 (WEread akx ea 8)).
  assert (Hl2 : wm_log s2 = wm_log s)
    by (subst s2; rewrite weff_apply_read wread_post_log; exact Hl1).
  set (s3 := weff_apply (Some cid) s2 (WEwrite akw ea 8 v)).
  assert (Hl3 : wm_log s3
                = (wm_log s ++ [wwrite_msg (Some cid)
                     (wm_class_of akw (wm_ws s2)) ea 8 v])%list).
  { subst s3. rewrite weff_apply_write /wwrite_post /= Hl2. reflexivity. }
  assert (Hlpost : wm_log (weffs (Some cid) s3 post) = wm_log s3)
    by exact (weffs_nowrite_log (Some cid) s3 post Hpost).
  assert (Hls' : wm_log s'
                 = (wm_log s ++ [wwrite_msg (Some cid)
                      (wm_class_of akw (wm_ws s2)) ea 8 v])%list).
  { rewrite Hl !weffs_app !weffs_cons -/s1 -/s2 -/s3 Hlpost Hl3. reflexivity. }
  rewrite /wQ_store_w /wV_store_w.
  split_and!; [exact Hi| |exact Hle|].
  { eexists. split; [exact Hls'|]. intros Hr. apply wm_class_of_relp.
    subst s2. rewrite weff_apply_read wread_post_relp. subst s1.
    by apply weffs_nowrite_relp. }
  intros j Hj.
  assert (Hstep : (S (length (wm_log s))
                   ≤ flr (ws_view (wm_ws s3)) (acc_addr ea j))%nat).
  { subst s3. rewrite weff_apply_write wwrite_post_ws Hl2 flr_ws_view /acc_addr.
    etrans; [|apply Nat.le_max_r].
    exact (store_post_run_coh (wm_ws s2) (ak_sync akw) (pa_z ea) (N.to_nat 8)
             (S (length (wm_log s))) j Hj). }
  etrans; [exact Hstep|].
  rewrite Hws !weffs_app !weffs_cons -/s1 -/s2 -/s3.
  apply flr_ws_le, weffs_ws_le.
Qed.

Print Assumptions exec_eff_translate_TLB_miss_user_upd.
Print Assumptions exec_eff_translate_TLB_hit_pt_upd.
Print Assumptions exec_eff_translate_TLB_hit_pt_refresh.
Print Assumptions exec_eff_translateAddr_pt_miss_upd.
Print Assumptions wcert_ptw_upd_pin.
