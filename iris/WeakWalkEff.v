(** * WeakWalkEff.v — M4 batch 6a: the Sv39 page-table-walk READ cone at
    [exec_eff]

    THE MIRROR of the S-mode translation READ path — [CommonWalk.v]'s
    privilege/access-generic 3-level walk core, [SmodePte.v]'s checked
    8-byte PTE read, [PtTree.v] §8's abstract-word translate layer, and
    [PtTreeAdue.v] §5's [translateAddr] front heads — at the instrumented
    interpreter [WeakCert.exec_eff].  Every lemma is parametric over
    [acc : MemoryAccessType] and [p : Privilege] exactly as the SC
    originals are, and the leaf word is ABSTRACT throughout (the [_ad]
    discipline: A/D enter only through the hypotheses, never the
    statements), so the same cone serves fetch/load/store/AMO walks over
    any A/D variant.

    THE TRACE.  A walk's weak-memory effect is its PTE reads and nothing
    else: one [WEread wak_plain pteAddr 8] per level ([read_pte] goes
    through [read_kind_of_flags false false false = Read_plain], the same
    plain-normal kind as the fetch, so [classify] gives
    [AkInfo false false false]).  The three-level success walk's trace is
    [es2 ++ es1 ++ es0] over the per-level read premises; instantiated at
    [wpt_read_pte_slot]'s singletons that is the literal
    [[WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain a0 8]]
    by conversion.  The TLB-hit path and every register-only probe carry
    the EMPTY trace — mirrored, not detected, per the batch-0 rule (the
    empty-memory detector can only conclude [quiet_trace], which admits
    zero-width writes, and these runs sit inside bind spines whose exact
    trace the certificates need).

    SCOPE (batch 6a).  The [update_PTE_Bits = None] outcomes ONLY — the
    O1 (TLB hit, state unchanged) and O2 (walk + TLB fill) arms of the
    sconf/walk design — plus the fault walks (invalid / no-permission,
    state unchanged).  The A/D WRITE-BACK arm (O3: [update_and_write_pte]'s
    [Some] case, [write_pte], [exec_translate_TLB_{miss,hit}_pt_upd]) is
    deliberately NOT mirrored — the fork's atomic PTE A/D CAS has since
    landed ([read_pte_exclusive] + [write_pte_conditional] inside
    [update_and_write_pte]), and mirroring it is a separate batch.  Here
    [update_and_write_pte] is only ever entered at
    [update_PTE_Bits … = None], where it is one register-only step.

    THE HYPOTHESIS SHAPE.  The SC originals take the PTE-word probes as
    ∀-state [exec] facts ([PtTree.pte_valid] & co.).  Those cannot be
    transported to [exec_eff] generically (nothing about a ∀-state [exec]
    fact rules out a barrier or zero-width access in the run), so this
    file takes them in their [exec_eff] form — [wpte_valid] /
    [wpte_invalid] / [wpte_check_ok] / [wpte_check_denied], each the SC
    predicate with the EMPTY trace.  They discharge exactly as the SC
    predicates do (the probes are register-only; a semi-concrete flag
    byte reduces by the same [vm_compute]/bridge scripts), and each
    projects back to its SC twin ([wpte_valid_pte_valid] & co.), so a
    consumer holding the eff form never re-proves the pure one.

    Sections:
      §1  the eff predicate twins and their SC projections
      §2  the register-only probes, at the empty trace
      §3  the S-mode PMP grant + PMA gate for the PTE read
      §4  [exec_eff_read_pte_S] — where the walk's trace element is born —
          and [wpt_read_pte_slot], the [pt_slot_mem]-keyed slot fact
      §5  Section UserWalkEff — [exec_eff_check_leaf_pte_leaf0] (the leaf
          checks the fork factored out of [pt_walk]), the SUCCESS walk
          (leaf, l1, full) and the no-update [translate_TLB_miss] (O2)
      §6  Section UserWalkFaultEff — [check_leaf_pte]'s two failure
          outcomes and the fault walks, state unchanged
      §7  the [translate]-level dispatch + the PtTree §8 mirrors: TLB-hit
          (O1), hit-denied, blocked/denied translate, lookup-blocked
      §8  the [translateAddr] front heads (Ok / Err / non-canonical)
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
Require Import WpDecodeBridge.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakEffSkel WeakFetchEff WeakLeafEffCommon WeakLeafEff8.
Require Import SmodePte Pt4kWalk CommonWalk PtAdBits PtTree UserPtTree.
Local Open Scope Z_scope.
Import Defs.

(* ====================================================================== *)
(** ** 1. The eff predicate twins

    [PtTree.pte_valid] / [pte_invalid] / [pte_check_ok] / [pte_check_denied]
    with the interpreter swapped for [exec_eff] and the EMPTY trace pinned.
    The purely syntactic classifications ([pte_ptr] / [pte_leaf] /
    [pte_no_napot] / [pte_pbmt0]) are plain equations and are reused from
    [PtTree] as they are. *)

Definition wpte_valid (w : SailStdpp.Values.mword 64) : Prop :=
  forall s : mstate,
    exec_eff (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                (ext_bits_of_PTE w)) s = Some (false, s, []).

Definition wpte_invalid (w : SailStdpp.Values.mword 64) : Prop :=
  forall s : mstate,
    exec_eff (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                (ext_bits_of_PTE w)) s = Some (true, s, []).

Definition wpte_check_ok (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr do_sum : bool) (w : SailStdpp.Values.mword 64) : Prop :=
  forall s : mstate,
    exec_eff (check_PTE_permission acc p mxr do_sum
                (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                (ext_bits_of_PTE w) tt) s
    = Some (PTE_Check_Success tt, s, []).

Definition wpte_check_denied (acc : MemoryAccessType mem_payload) (p : Privilege)
    (mxr do_sum : bool) (f : pte_check_failure)
    (w : SailStdpp.Values.mword 64) : Prop :=
  forall s : mstate,
    exec_eff (check_PTE_permission acc p mxr do_sum
                (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                (ext_bits_of_PTE w) tt) s
    = Some (PTE_Check_Failure (tt, f), s, []).

(** The projections back to the SC predicates: an eff fact is strictly
    stronger, so a consumer holding one gets the pure cone ([pte_below],
    the §2c classifications, …) for free. *)
Lemma wpte_valid_pte_valid (w : SailStdpp.Values.mword 64) :
  wpte_valid w -> pte_valid w.
Proof. intros H s. exact (exec_eff_exec _ _ _ _ _ (H s)). Qed.

Lemma wpte_invalid_pte_invalid (w : SailStdpp.Values.mword 64) :
  wpte_invalid w -> pte_invalid w.
Proof. intros H s. exact (exec_eff_exec _ _ _ _ _ (H s)). Qed.

Lemma wpte_check_ok_pte_check_ok (acc : MemoryAccessType mem_payload)
    (p : Privilege) (mxr do_sum : bool) (w : SailStdpp.Values.mword 64) :
  wpte_check_ok acc p mxr do_sum w -> pte_check_ok acc p mxr do_sum w.
Proof. intros H s. exact (exec_eff_exec _ _ _ _ _ (H s)). Qed.

Lemma wpte_check_denied_pte_check_denied (acc : MemoryAccessType mem_payload)
    (p : Privilege) (mxr do_sum : bool) (f : pte_check_failure)
    (w : SailStdpp.Values.mword 64) :
  wpte_check_denied acc p mxr do_sum f w -> pte_check_denied acc p mxr do_sum f w.
Proof. intros H s. exact (exec_eff_exec _ _ _ _ _ (H s)). Qed.

(* ====================================================================== *)
(** ** 2. The register-only probes, at the empty trace

    [CommonWalk]'s extension probes, [ExecCommon]'s [architecture],
    [SmodePte]'s [translationMode]/TLB-lookup family and [UserPtTree]'s
    privilege bricks, each the SC script with the bind/lift lemmas renamed
    and [[]] appended.  Read them against their originals: nothing else
    changes. *)

(** [CommonWalk.exec_currentlyEnabled_Svnapot], through the decode
    bridge's [exec_eff] twin (the SC original goes through
    [decode_state_bridge] for the same reason: the probe recurses via the
    Zca gate, which reads misa, so an abstract-state [vm_compute]
    diverges). *)
Lemma exec_eff_currentlyEnabled_Svnapot s :
  register_lookup misa s.(sregs) = MISA_C ->
  exec_eff (currentlyEnabled Ext_Svnapot) s = Some (true, s, []).
Proof.
  intro Hmisa.
  apply (exec_eff_decode_bridge D_misa _ dstateM).
  - intros r Hr. unfold D_misa in Hr. apply register_beq_eq in Hr. subst r.
    rewrite Hmisa. vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

(** [CommonWalk.exec_currentlyEnabled_Svadu]: register-free, so the
    abstract-state [vm_compute] closes it just as at SC. *)
Lemma exec_eff_currentlyEnabled_Svadu s :
  exec_eff (currentlyEnabled Ext_Svadu) s = Some (true, s, []).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  vm_compute. reflexivity.
Qed.

(** [ExecCommon.exec_architecture_Supervisor]. *)
Lemma exec_eff_architecture_Supervisor s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  exec_eff (architecture Supervisor) s = Some (RV64, s, []).
Proof.
  intro HSXL. unfold architecture. cbn match.
  match goal with |- exec_eff (Defs.bind ?L _) s = _ =>
    assert (Hin : exec_eff L s
                  = Some (_get_Mstatus_SXL (register_lookup mstatus s.(sregs)), s, [])) end.
  { rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    apply exec_eff_returnM. }
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hin).
  unfold architecture_bits_backwards. rewrite HSXL.
  replace (eq_vec ('b"10") ('b"01")) with false by (vm_compute; reflexivity). cbn match.
  replace (eq_vec ('b"10") ('b"10")) with true by (vm_compute; reflexivity). cbn match.
  apply exec_eff_returnM.
Qed.

(** [SmodePte.exec_translationMode_S_sv39]. *)
Lemma exec_eff_translationMode_S_sv39 (satp0 : SailStdpp.Values.mword 64) s :
  _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10" ->
  register_lookup satp s.(sregs) = satp0 ->
  _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : SailStdpp.Values.mword 4) ->
  exec_eff (translationMode Supervisor) s = Some (Sv39, s, []).
Proof.
  intros HSXL Hsatp Hmode.
  unfold translationMode.
  replace (generic_eq Supervisor Machine) with false by (vm_compute; reflexivity).
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_architecture_Supervisor s HSXL)).
  cbn match.
  change (xlen >=? 64) with true.
  match goal with |- exec_eff (Defs.bind ?ARM _) s = _ =>
    assert (HARM : exec_eff ARM s = Some (_get_Satp64_Mode (Mk_Satp64 satp0), s, [])) end.
  { assert (Hae : exec_eff (Defs.assert_exp' true "sys/vmem.sail:254.25-254.26") s
                  = Some (eq_refl, s, [])).
    { unfold Defs.assert_exp'. cbn match. apply exec_eff_returnm. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hae).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg satp s)).
    rewrite Hsatp. apply exec_eff_returnm. }
  rewrite (exec_eff_bind_nil _ _ _ _ _ HARM).
  rewrite Hmode.
  replace (satpMode_of_bits RV64 ('b"1000" : SailStdpp.Values.mword 4)) with (Some Sv39)
    by (vm_compute; reflexivity).
  cbn match. apply exec_eff_returnm.
Qed.

(** [UserPtTree.exec_effectivePrivilege_mprv0] — access-type- and
    privilege-generic: with MPRV clear the effective privilege is the
    current one. *)
Lemma exec_eff_effectivePrivilege_mprv0 (acc : MemoryAccessType mem_payload)
    (m : SailStdpp.Values.mword 64) (pr : Privilege) s :
  eq_vec (_get_Mstatus_MPRV m) ('b"1") = false ->
  exec_eff (effectivePrivilege acc m pr) s = Some (pr, s, []).
Proof.
  intro H. unfold effectivePrivilege. rewrite H. rewrite andb_false_r.
  apply exec_eff_returnM.
Qed.

(** [UserPtTree.exec_is_shadow_stack_u_acc], over the same [u_acc] class. *)
Lemma exec_eff_is_shadow_stack_u_acc (acc : MemoryAccessType mem_payload) s :
  u_acc acc ->
  exec_eff (is_shadow_stack_access acc) s = Some (false, s, []).
Proof.
  intros [-> | [-> | [-> | [(aq & rl & ->) | [(aq & rl & ->) | (op & aq & rl & ->)]]]]];
    unfold is_shadow_stack_access; cbn match; apply exec_eff_returnM.
Qed.

(** The TLB lookup trio ([SmodePte.exec_lookup_TLB_miss] /
    [_nomatch_s], [Pt4kWalk.exec_lookup_TLB_hit_ent]). *)
Lemma exec_eff_lookup_TLB_miss (vpn : SailStdpp.Values.mword 27)
    (asid : SailStdpp.Values.mword 16)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None ->
  exec_eff (lookup_TLB 39 asid vpn) s = Some (None, s, []).
Proof.
  intros Htlb Hvec.
  unfold lookup_TLB.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg tlb s)).
  rewrite Htlb. rewrite Hvec. apply exec_eff_returnm.
Qed.

Lemma exec_eff_lookup_TLB_nomatch_s (vpn : SailStdpp.Values.mword 27)
    (asid : SailStdpp.Values.mword 16) (ent' : TLB_Entry)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent' ->
  match_TLB_Entry ent' asid (sign_extend' (57 - 12) vpn) = false ->
  exec_eff (lookup_TLB 39 asid vpn) s = Some (None, s, []).
Proof.
  intros Htlb Hvec Hnm.
  unfold lookup_TLB.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg tlb s)).
  rewrite Htlb. rewrite Hvec. rewrite Hnm. apply exec_eff_returnm.
Qed.

Lemma exec_eff_lookup_TLB_hit_ent (vpn : SailStdpp.Values.mword 27)
    (asid : SailStdpp.Values.mword 16)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (ent : TLB_Entry) s :
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
  match_TLB_Entry ent asid (sign_extend' (57 - 12) vpn) = true ->
  exec_eff (lookup_TLB 39 asid vpn) s
  = Some (Some (tlb_hash (__id 39) vpn, ent), s, []).
Proof.
  intros Htlb Hvec Hm.
  unfold lookup_TLB.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg tlb s)).
  rewrite Htlb. rewrite Hvec.
  match goal with |- context[match_TLB_Entry ?e ?a ?v] =>
    replace (match_TLB_Entry e a v) with true by (symmetry; exact Hm) end.
  apply exec_eff_returnm.
Qed.

(** [PtTree.uwe_pbmt]'s exec half at [exec_eff] (the pure [u_walk_entry]
    field bridges [uwe_pte] / [uwe_ppn] / [uwe_match_self] /
    [uwe_match_other] are interpreter-free and are reused from [PtTree]). *)
Lemma exec_eff_uwe_pbmt (vpn : SailStdpp.Values.mword 27)
    (p2 p1 q0 : SailStdpp.Values.mword 64) (asid : SailStdpp.Values.mword 16) s :
  pte_pbmt0 q0 ->
  exec_eff (tlb_get_pbmt (u_walk_entry vpn p2 p1 q0 asid)) s
  = Some (PBMT_PMA, s, []).
Proof.
  intros Hpb.
  unfold tlb_get_pbmt, u_walk_entry. cbn [TLB_Entry_pte]. cbn zeta.
  rewrite zero_extend64_id. rewrite autocast_id.
  unfold pte_pbmt0 in Hpb. rewrite Hpb.
  vm_compute (page_based_mem_type_forwards _). apply exec_eff_returnm.
Qed.

(* ====================================================================== *)
(** ** 3. The S-mode PMP grant and the PTE-read PMA gate

    [SmodePte.exec_pmpMatchAddr_TOR_match] / [exec_pmpReadAddrReg_val] /
    [exec_pmpCheck_supervisor_grant_load], and the [pmaCheck] arm of the
    PTE read (whose gate is the DISTINCT field [PMA_supports_pte_read],
    not [PMA_readable]).  All register-only. *)

Lemma exec_eff_pmpMatchAddr_TOR_match
    (addr width : SailStdpp.Values.mword 64) (ent : SailStdpp.Values.mword 8)
    (pmpaddr prev : SailStdpp.Values.mword 64) s :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = TOR ->
  zopz0zKzJ_u prev pmpaddr = false ->
  pmpRangeMatch (Z.mul (uint prev) 4) (Z.mul (uint pmpaddr) 4)
    (uint addr) (uint width) = PMP_Match ->
  exec_eff (pmpMatchAddr (Physaddr addr) width ent pmpaddr prev) s
  = Some (PMP_Match, s, []).
Proof.
  intros HA Hord Hrange. unfold pmpMatchAddr. cbn zeta.
  rewrite HA. cbn match. rewrite Hord. rewrite Hrange. apply exec_eff_returnm.
Qed.

Lemma exec_eff_pmpReadAddrReg_val (n : Z) s :
  exec_eff (pmpReadAddrReg n) s
  = Some (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) n, s, []).
Proof.
  unfold pmpReadAddrReg. cbn zeta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpcfg_n s)). cbn beta.
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg pmpaddr_n s)). cbn beta.
  replace (andb (Z.geb sys_pmp_grain 2)
             (eq_vec (access_vec_dec (_get_Pmpcfg_ent_A
                (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) n)) 1) ('b"1")))
    with false by (vm_compute; reflexivity).
  replace (andb (Z.geb sys_pmp_grain 1)
             (eq_vec (access_vec_dec (_get_Pmpcfg_ent_A
                (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) n)) 1) ('b"0")))
    with false by (vm_compute; reflexivity).
  cbn match. apply exec_eff_returnm.
Qed.

Lemma exec_eff_pmpCheck_supervisor_grant_load
    (a : SailStdpp.Values.mword 64) (width : Z) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : SailStdpp.Values.mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  exec_eff (pmpCheck (Physaddr a) width (Load PageTableEntry) Supervisor) s
  = Some (None, s, []).
Proof.
  intros HA Hord Hrange HR.
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
                            (Load PageTableEntry)) s = Some (true, s, []))).
    2:{ unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_eff_returnm. }
    cbn match. rewrite execR_eff_returnR. cbn beta.
    cbn match. rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match.
    unfold early_return, throw. cbn [execR_eff]. cbn match. reflexivity. }
  rewrite Hfe. cbn match. reflexivity.
Qed.

(** The [pmaCheck] of the PTE read: access [Load PageTableEntry], gate
    [PMA_supports_pte_read] (mirrors the inline block of
    [SmodePte.exec_read_pte_S]).  Since the bump [pmaCheck] answers a
    splitting PLAN in an early-return body; an aligned access's plan is
    [RiscvExtras.pma_ok_aligned].  The PTE arms carry NO [assert_exp']
    (the fork dropped [assert(not(res_or_con))] there — which is what
    makes the exclusive PTE read legal), so [pma_ok_eff_peel] takes its
    no-assert branch.  [Hmag] is the eff twin of
    [RiscvExtras.exec_is_mag_applicable_load_pte]. *)
Lemma exec_eff_is_mag_applicable_load_pte (width : Z) s :
  exec_eff (is_mag_applicable_access (Load PageTableEntry) width) s
  = Some (false, s, []).
Proof. apply exec_eff_returnM. Qed.

Lemma exec_eff_pmaCheck_ram_pte (addr : SailStdpp.Values.mword 64)
    (region : PMA_Region) (res_or_con : bool) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
  exec_eff (pmaCheck (Physaddr addr) 8 (Load PageTableEntry) PBMT_PMA res_or_con) s
  = Some (Ok pma_ok_aligned, s, []).
Proof.
  intros Hmatch Halign Hread.
  destruct region as [rbase rsize rattr rdtree].
  pma_ok_eff_peel Hmatch Hread (exec_eff_is_mag_applicable_load_pte 8 s) Halign.
Qed.

(* ====================================================================== *)
(** ** 4. THE PTE READ — where the walk's trace element is born

    [SmodePte.exec_read_pte_S] replayed; the one memory step is
    [WeakLeafEff8.exec_eff_read_ram_plain_8], whose trace element is
    [WEread wak_plain addr 8].  Then [PtTree.pt_read_pte_slot]'s
    [pt_slot_mem]-keyed wrapper on top of it — the fact the Iris engines
    extract per slot from [ptree_own_path_mem]. *)

Lemma exec_eff_read_pte_S (addr : SailStdpp.Values.mword 64)
    (region : PMA_Region) (w : bv 64) s :
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : SailStdpp.Values.mword 64)) 4)
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
  exec_eff (read_pte (Physaddr addr) 8) s
  = Some (Ok w, s, [WEread wak_plain addr 8]).
Proof.
  intros HA Hord Hrange HR Hmatch Halign Hread Hc Hsig Hh Hdev Hbytes.
  assert (Hcp : exec_eff (check_pma_with_pmp_priority (Load PageTableEntry) PBMT_PMA Supervisor
                            (Physaddr addr) 8 false) s = Some (Ok pma_ok_aligned, s, [])).
  { unfold check_pma_with_pmp_priority.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_pmaCheck_ram_pte addr region false s Hmatch Halign Hread)).
    cbn match. apply exec_eff_returnM. }
  assert (Hmmio : exec_eff (within_mmio_readable (Physaddr addr) 8) s = Some (false, s, [])).
  { unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hc). cbn match.
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_eff_and_boolM_nil _ _ _ _ _ Hh). cbn match. reflexivity. }
  assert (Hchk : exec_eff (checked_mem_read (Load PageTableEntry) PBMT_PMA Supervisor
                             (Physaddr addr) 8 false false false false) s
                 = Some (Ok (w, default_meta), s, [WEread wak_plain addr 8])).
  { unfold checked_mem_read. rewrite exec_eff_catch_early_return.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hcp). cbn beta. cbn match.
    rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match beta.
    rewrite pma_ok_aligned_splittable pma_ok_aligned_granule.
    rewrite (execR_eff_liftR_seq _ _ _ _ _
               (exec_eff_split_misaligned_unsplit addr 8 0 s)). cbn beta.
    rewrite misaligned_order_1. cbn zeta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _
               (_ : exec_eff (read_kind_of_flags false false false) s
                    = Some (rv64d_types.Read_plain, s, []))).
    2:{ unfold read_kind_of_flags. apply exec_eff_returnM. }
    cbn beta.
    match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
      assert (Hu : execR_eff (Defs.untilMT vs m c b) s
                   = Some (inr (w, true, 0), s, [WEread wak_plain addr 8])) end.
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
                      = Some (inr w, s, [WEread wak_plain addr 8])) end.
      { rewrite (execR_eff_liftR_cat _ _ _ _ _ _
                   (exec_eff_read_ram_plain_8 addr w s Hdev Hbytes)).
        cbn beta match. rewrite execR_eff_returnR. cbn [app]. reflexivity. }
      rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hrd). cbn beta zeta.
      rewrite autocast_id. rewrite usvd_zeros_full_64.
      rewrite execR_eff_returnR. cbn [app]. reflexivity. }
    rewrite (execR_eff_bind_cat _ _ _ _ _ _ Hu). cbn beta zeta.
    rewrite autocast_id. rewrite execR_eff_returnR. cbn [app]. reflexivity. }
  unfold read_pte, mem_read_priv.
  rewrite (exec_eff_bind_Some _ _ _ _ _ _
            (_ : exec_eff (mem_read_priv_meta _ _ _ _ 8 _ _ _ _) s
                 = Some (Ok (w, default_meta), s, [WEread wak_plain addr 8]))).
  2:{ unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hchk).
      cbn match. unfold mem_read_callback. rewrite exec_eff_returnM.
      cbn [app]. reflexivity. }
  cbn [MemoryOpResult_drop_meta]. rewrite exec_eff_returnM.
  cbn [app]. reflexivity.
Qed.

(** [PtTree.pt_read_pte_slot] replayed: the slot's [exec_eff] read fact
    from its [pt_slot_mem] + the [pmp_config]-stored PMP/PMA facts.  The
    pure geometry asserts are the SC's verbatim. *)
Lemma wpt_read_pte_slot (sg : mstate) (a w : SailStdpp.Values.mword 64)
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
  exec_eff (read_pte (Physaddr a) 8) sg
  = Some (Ok w, sg, [WEread wak_plain a 8]).
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
  assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : SailStdpp.Values.mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0)) 4)
            (uint a) (uint (to_bits 64 8)) = PMP_Match).
  { apply (ram_pmp_match_w a _ 8); [lia | vm_compute; reflexivity | | exact Hfit | exact Hcov].
    destruct Hram as [Hlo _]. exact Hlo. }
  apply (exec_eff_read_pte_S a region w sg HA Hord Hrange HR Hmatch Halign Hpma).
  - apply exec_eff_within_clint_false; [apply addr_is_ram_not_in_clint; exact Hram | lia].
  - apply exec_eff_within_sig_false; [apply addr_is_ram_not_in_sig; exact Hram | lia].
  - apply exec_eff_within_htif_false. exact Hhtif.
  - apply addr_is_ram_not_dev. exact Hram.
  - exact Hbytes.
Qed.

(* ====================================================================== *)
(** ** 5. THE SUCCESS WALK — [CommonWalk.Section UserWalk] replayed

    Per-level ∀-Acc lemmas, the Acc term destructed BEFORE
    [cbn [_rec_pt_walk]] so exactly one level unfolds (the durable-notes
    walk technique; a monolithic [cbn] explodes).  The per-level read
    premises carry ARBITRARY traces [es2]/[es1]/[es0]; at
    [wpt_read_pte_slot]'s singletons the concatenations below are the
    literal three-element list by conversion. *)

(** [CommonWalk]'s [walk_peel_asserts], mirrored: the walk body's shared
    head (the recursion-limit assert and the xlen assert) peels without
    ever spelling out the two Sail source positions — which is exactly
    what broke six copies of this head on the previous model bump.  The
    body is no longer an early-return block (the leaf arm's escapes moved
    into [check_leaf_pte]), so the head peels in the PLAIN monad. *)
Local Ltac walk_eff_peel_asserts lvl st :=
  cbn [_rec_pt_walk];
  change (lvl >=? 0) with true;
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_assert_exp'_true _ st)); cbn beta zeta;
  change ((39 =? 32) || (xlen =? 64)) with true;
  rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_assert_exp'_true _ st)); cbn beta zeta.

(** ... and the PTE read that follows, once the caller has named the slot
    address.  This is the ONE trace-carrying step of a walk level, so
    unlike its SC twin it goes through the concatenating bind. *)
Local Ltac walk_eff_peel_read Hrd :=
  rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hrd); cbn match beta zeta.

Section UserWalkEff.
  Context (vpn : SailStdpp.Values.mword 27) (root : SailStdpp.Values.mword 44).
  Context (pte2 pte1 pte0 : SailStdpp.Values.mword 64).
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (* the three slot addresses the walk reads *)
  Let addr2 : SailStdpp.Values.mword 64 := u_pte_addr root (subrange_vec_dec vpn 26 18).
  Let addr1 : SailStdpp.Values.mword 64 := u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9).
  Let addr0 : SailStdpp.Values.mword 64 := u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0).

  (* levels 2 and 1: valid non-leaf PTEs *)
  Hypothesis H2i : wpte_valid pte2.
  Hypothesis H2nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true.
  Hypothesis H1i : wpte_valid pte1.
  Hypothesis H1nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true.
  (* level 0: a valid leaf that passes the permission check, no NAPOT *)
  Hypothesis H0i : wpte_valid pte0.
  Hypothesis H0nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false.
  Hypothesis Hchk0 : wpte_check_ok acc p mxr do_sum pte0.
  Hypothesis H0N : eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false.

  (** [check_leaf_pte]: Steps 3 and 5–8 of the VATP, which the fork
      factored OUT of [pt_walk] so the atomic A/D update can re-run them
      on a freshly read PTE.  Mirrored as its own lemma for the same
      reason [CommonWalk.exec_check_leaf_pte_leaf0] is: one lemma serves
      the walk's leaf arm AND the re-check.  Register-only — the empty
      trace. *)
  Lemma exec_eff_check_leaf_pte_leaf0 (pa : physaddr)
        (menvcfg0 : SailStdpp.Values.mword 64) s :
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec_eff (check_leaf_pte 39 vpn acc p mxr do_sum pte0 pa 0 tt) s
      = Some (Ok (autocast (T := mword) (PPN_of_PTE pte0), PBMT_PMA, tt), s, []).
  Proof.
    intros Hmisa Hmenv HPBMTE.
    unfold check_leaf_pte. rewrite exec_eff_catch_early_return.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (H0i s)). cbv iota beta.
    rewrite H0nl. cbv iota beta.
    change (0 >? 0) with false. cbv iota beta.
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR_eff (Defs.bind0 A B) s = Some (inr (PTE_Check_Success tt), s, [])) end.
    { rewrite execR_eff_bind0_eq. rewrite execR_eff_returnR. cbn match.
      rewrite execR_eff_liftR. rewrite (Hchk0 s). cbn match. reflexivity. }
    rewrite (execR_eff_bind_nil _ _ _ _ _ HAB).
    cbv iota beta. cbn match.
    change (0 >? 0) with false. cbv iota beta.
    (* the Svnapot gate sits under two binds: decompose with the plain
       execR_eff_bind equations, resolve the probe, and let the N-bit kill it *)
    rewrite execR_eff_bind_eq.
    rewrite execR_eff_bind_eq.
    unfold Defs.and_boolM.
    rewrite execR_eff_bind_eq.
    rewrite execR_eff_liftR.
    rewrite (exec_eff_currentlyEnabled_Svnapot s Hmisa). cbn match beta.
    cbv iota beta.
    rewrite H0N. cbv iota beta.
    rewrite execR_eff_returnR. cbn match.
    rewrite execR_eff_returnR. cbn match beta.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg menvcfg s)).
    rewrite Hmenv. rewrite HPBMTE. cbv iota beta.
    cbn. by rewrite ?app_nil_r.
  Qed.

  (* level 0: the leaf, from any reclimit-0 Acc *)
  Lemma exec_eff_rec_walk_leaf (g : bool) (menvcfg0 : SailStdpp.Values.mword 64)
        (es0 : list weff) (wfacc : Acc (Zwf 0) 0) s :
    register_lookup misa s.(sregs) = MISA_C ->
    exec_eff (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s, es0) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec_eff (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte1) 0 g tt 0 wfacc) s
      = Some (Ok ({| PTW_Output_ppn := autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : SailStdpp.Values.mword 44);
                     PTW_Output_pte := autocast (T := mword) pte0;
                     PTW_Output_pteAddr := Physaddr addr0;
                     PTW_Output_level := 0;
                     PTW_Output_pbmt := PBMT_PMA;
                     PTW_Output_global := orb g (u_gbit pte0) |}, tt), s, es0).
  Proof.
    intros Hmisa Hrd0 Hmenv HPBMTE.
    destruct wfacc as [a0].
    walk_eff_peel_asserts 0 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr0 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_eff_peel_read Hrd0.
    (* the follow-a-pointer test: valid AND non-leaf AND level > 0.  A leaf
       fails the second conjunct, so the [check_leaf_pte] arm is taken. *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hnl : exec_eff (Defs.and_boolM A B) s = Some (false, s, [])) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec_eff (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s, [])) end.
      { rewrite (exec_eff_bind_nil _ _ _ _ _ (H0i s)). cbn match beta.
        apply exec_eff_returnM. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hv). cbn match beta.
      change (0 >? 0) with false. rewrite andb_false_r. apply exec_eff_returnM. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hnl). cbn match beta.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_check_leaf_pte_leaf0 (Physaddr addr0) menvcfg0 s Hmisa Hmenv HPBMTE)).
    cbn match beta zeta.
    rewrite exec_eff_returnM. cbn match. by rewrite ?app_nil_r.
  Qed.

  (* level 1: a valid non-leaf step into the leaf, from any reclimit-1 Acc *)
  Lemma exec_eff_rec_walk_l1 (g : bool) (menvcfg0 : SailStdpp.Values.mword 64)
        (es1 es0 : list weff) (wfacc : Acc (Zwf 0) 1) s :
    register_lookup misa s.(sregs) = MISA_C ->
    exec_eff (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s, es1) ->
    exec_eff (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s, es0) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec_eff (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte2) 1 g tt 1 wfacc) s
      = Some (Ok ({| PTW_Output_ppn := autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : SailStdpp.Values.mword 44);
                     PTW_Output_pte := autocast (T := mword) pte0;
                     PTW_Output_pteAddr := Physaddr addr0;
                     PTW_Output_level := 0;
                     PTW_Output_pbmt := PBMT_PMA;
                     PTW_Output_global := orb (orb g (u_gbit pte1)) (u_gbit pte0) |}, tt), s,
              (es1 ++ es0)%list).
  Proof.
    intros Hmisa Hrd1 Hrd0 Hmenv HPBMTE.
    destruct wfacc as [a1].
    walk_eff_peel_asserts 1 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr1 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_eff_peel_read Hrd1.
    (* valid AND non-leaf AND level > 0: follow the pointer *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hnl : exec_eff (Defs.and_boolM A B) s = Some (true, s, [])) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec_eff (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s, [])) end.
      { rewrite (exec_eff_bind_nil _ _ _ _ _ (H1i s)). cbn match beta.
        apply exec_eff_returnM. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hv). cbn match beta.
      rewrite H1nl. change (1 >? 0) with true. cbn [andb]. apply exec_eff_returnM. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hnl). cbn match beta.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (1 - 1)] =>
      change (1 - 1) with 0 end.
    rewrite (exec_eff_rec_walk_leaf _ menvcfg0 es0 _ s Hmisa Hrd0 Hmenv HPBMTE).
    cbn match. by rewrite ?app_nil_r.
  Qed.

  (* level 2 = the full walk: trace [es2 ++ es1 ++ es0] *)
  Lemma exec_eff_pt_walk_user (menvcfg0 : SailStdpp.Values.mword 64)
        (es2 es1 es0 : list weff) s :
    register_lookup misa s.(sregs) = MISA_C ->
    exec_eff (read_pte (Physaddr addr2) 8) s = Some (Ok pte2, s, es2) ->
    exec_eff (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s, es1) ->
    exec_eff (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s, es0) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec_eff (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s
      = Some (Ok ({| PTW_Output_ppn := autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : SailStdpp.Values.mword 44);
                     PTW_Output_pte := autocast (T := mword) pte0;
                     PTW_Output_pteAddr := Physaddr addr0;
                     PTW_Output_level := 0;
                     PTW_Output_pbmt := PBMT_PMA;
                     PTW_Output_global := u_global pte2 pte1 pte0 |}, tt), s,
              (es2 ++ es1 ++ es0)%list).
  Proof.
    intros Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE.
    unfold pt_walk.
    destruct (Defs.Zwf_guarded _) as [a2].
    walk_eff_peel_asserts 2 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr2 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_eff_peel_read Hrd2.
    (* valid AND non-leaf AND level > 0: follow the pointer *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hnl : exec_eff (Defs.and_boolM A B) s = Some (true, s, [])) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec_eff (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s, [])) end.
      { rewrite (exec_eff_bind_nil _ _ _ _ _ (H2i s)). cbn match beta.
        apply exec_eff_returnM. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hv). cbn match beta.
      rewrite H2nl. change (2 >? 0) with true. cbn [andb]. apply exec_eff_returnM. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hnl). cbn match beta.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (2 - 1)] =>
      change (2 - 1) with 1 end.
    rewrite (exec_eff_rec_walk_l1 _ menvcfg0 es1 es0 _ s Hmisa Hrd1 Hrd0 Hmenv HPBMTE).
    cbn match. by rewrite ?app_nil_r.
  Qed.

  (* the TLB fill: register-only, empty trace ([u_walk_entry] is
     CommonWalk's) *)
  Lemma exec_eff_add_to_TLB_user (asid : SailStdpp.Values.mword 16) s :
    exec_eff (add_to_TLB 39 asid vpn
                (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : SailStdpp.Values.mword 44))
                (autocast (T := mword) pte0) (Physaddr addr0) 0
                (u_global pte2 pte1 pte0)) s
      = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                                   (tlb_hash (__id 39) vpn)
                                   (Some (u_walk_entry vpn pte2 pte1 pte0 asid))), []).
  Proof.
    unfold add_to_TLB. cbn zeta.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg tlb s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_write_reg tlb _ s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg tlb _)).
    rewrite exec_eff_returnm.
    reflexivity.
  Qed.

  (* O2: the walk succeeds and the leaf's A (and D) bits need no update —
     the TLB fill is the ONLY state change and the trace is the three
     PTE reads *)
  Lemma exec_eff_translate_TLB_miss_user (asid : SailStdpp.Values.mword 16)
        (menvcfg0 : SailStdpp.Values.mword 64) (es2 es1 es0 : list weff) s :
    register_lookup misa s.(sregs) = MISA_C ->
    update_PTE_Bits (autocast (T := mword) pte0 : SailStdpp.Values.mword 64) acc = None ->
    exec_eff (read_pte (Physaddr addr2) 8) s = Some (Ok pte2, s, es2) ->
    exec_eff (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s, es1) ->
    exec_eff (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s, es0) ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    exec_eff (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
      = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : SailStdpp.Values.mword 44), PBMT_PMA, tt),
              set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                               (tlb_hash (__id 39) vpn)
                               (Some (u_walk_entry vpn pte2 pte1 pte0 asid))),
              (es2 ++ es1 ++ es0)%list).
  Proof.
    intros Hmisa Hnoupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _
               (exec_eff_pt_walk_user menvcfg0 es2 es1 es0 s Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE)).
    cbn match.
    (* [update_and_write_pte] takes the whole tablewalk context now (it
       re-runs the leaf checks on a freshly read PTE when it DOES write),
       and returns the ext_ptw alongside.  The no-write case is still one
       step, and still register-only. *)
    match goal with |- context[update_and_write_pte ?w ?vp ?a ?pv ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hupd : exec_eff (update_and_write_pte w vp a pv lv ac pr mx ds e) s
                     = Some (Ok (None, tt), s, [])) end.
    { unfold update_and_write_pte. rewrite Hnoupd. cbn match. apply exec_eff_returnm. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_add_to_TLB_user asid s)).
    rewrite exec_eff_returnm. cbn match. by rewrite ?app_nil_r.
  Qed.

End UserWalkEff.

(* ====================================================================== *)
(** ** 6. THE FAULT WALKS — [CommonWalk.Section UserWalkFault] replayed

    An invalid PTE at any level, a leaf permission failure, and the
    result-generic descend steps.  The fault paths stop before the
    Svnapot gate, so no misa premise; they perform NO writes — state
    preserved, trace = the reads performed up to the stop. *)

Section UserWalkFaultEff.
  Context (vpn : SailStdpp.Values.mword 27).
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (** [check_leaf_pte]'s two failure outcomes ([CommonWalk]'s
      [exec_check_leaf_pte_invalid] / [_noperm0]), at the empty trace:
      the leaf checks read no memory. *)
  Lemma exec_eff_check_leaf_pte_invalid (pte : SailStdpp.Values.mword 64)
        (pa : physaddr) (lvl : Z) s :
    wpte_invalid pte ->
    exec_eff (check_leaf_pte 39 vpn acc p mxr do_sum pte pa lvl tt) s
      = Some (Err (PTW_Invalid_PTE tt, tt), s, []).
  Proof.
    intro Hinv.
    unfold check_leaf_pte. rewrite exec_eff_catch_early_return.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (Hinv s)). cbv iota beta.
    cbn. by rewrite ?app_nil_r.
  Qed.

  Lemma exec_eff_check_leaf_pte_noperm0 (pte : SailStdpp.Values.mword 64)
        (pa : physaddr) (f : pte_check_failure) s :
    wpte_valid pte ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = false ->
    wpte_check_denied acc p mxr do_sum f pte ->
    exec_eff (check_leaf_pte 39 vpn acc p mxr do_sum pte pa 0 tt) s
      = Some (Err (ext_get_ptw_error f, tt), s, []).
  Proof.
    intros Hinv Hnl Hchk.
    unfold check_leaf_pte. rewrite exec_eff_catch_early_return.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (Hinv s)). cbv iota beta.
    rewrite Hnl. cbv iota beta.
    change (0 >? 0) with false. cbv iota beta.
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR_eff (Defs.bind0 A B) s
                    = Some (inr (PTE_Check_Failure (tt, f)), s, [])) end.
    { rewrite execR_eff_bind0_eq. rewrite execR_eff_returnR. cbn match.
      rewrite execR_eff_liftR. rewrite (Hchk s). cbn match. reflexivity. }
    rewrite (execR_eff_bind_nil _ _ _ _ _ HAB).
    cbv iota beta. cbn match.
    cbn. by rewrite ?app_nil_r.
  Qed.

  (* level 0: the leaf slot holds an INVALID pte *)
  Lemma exec_eff_rec_walk_leaf_invalid (base : SailStdpp.Values.mword 44)
        (pte : SailStdpp.Values.mword 64) (g : bool) (es0 : list weff)
        (wfacc : Acc (Zwf 0) 0) s :
    exec_eff (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok pte, s, es0) ->
    wpte_invalid pte ->
    exec_eff (_rec_pt_walk 39 vpn acc p mxr do_sum base 0 g tt 0 wfacc) s
      = Some (Err (PTW_Invalid_PTE tt, tt), s, es0).
  Proof.
    intros Hrd Hinv.
    destruct wfacc as [a0].
    walk_eff_peel_asserts 0 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 8 0)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_eff_peel_read Hrd.
    (* an INVALID pte fails the follow-a-pointer test's first conjunct *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec_eff (Defs.and_boolM A B) s = Some (false, s, [])) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec_eff (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s, [])) end.
      { rewrite (exec_eff_bind_nil _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_eff_returnM. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hv). cbn match beta. apply exec_eff_returnM. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hab). cbn match beta.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_check_leaf_pte_invalid pte
                  (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 0 s Hinv)).
    cbn match beta zeta.
    rewrite exec_eff_returnM. cbn match. by rewrite ?app_nil_r.
  Qed.

  (* level 0: a valid leaf that FAILS the permission check (e.g. U = 0) *)
  Lemma exec_eff_rec_walk_leaf_noperm (base : SailStdpp.Values.mword 44)
        (pte : SailStdpp.Values.mword 64) (g : bool) (f : pte_check_failure)
        (es0 : list weff) (wfacc : Acc (Zwf 0) 0) s :
    exec_eff (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok pte, s, es0) ->
    wpte_valid pte ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = false ->
    wpte_check_denied acc p mxr do_sum f pte ->
    exec_eff (_rec_pt_walk 39 vpn acc p mxr do_sum base 0 g tt 0 wfacc) s
      = Some (Err (ext_get_ptw_error f, tt), s, es0).
  Proof.
    intros Hrd Hinv Hnl Hchk.
    destruct wfacc as [a0].
    walk_eff_peel_asserts 0 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 8 0)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_eff_peel_read Hrd.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec_eff (Defs.and_boolM A B) s = Some (false, s, [])) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec_eff (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s, [])) end.
      { rewrite (exec_eff_bind_nil _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_eff_returnM. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hv). cbn match beta.
      rewrite Hnl. cbn [andb]. apply exec_eff_returnM. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hab). cbn match beta.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_check_leaf_pte_noperm0 pte
                  (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) f s Hinv Hnl Hchk)).
    cbn match beta zeta.
    rewrite exec_eff_returnM. cbn match. by rewrite ?app_nil_r.
  Qed.

  (* level 1: the mid slot holds an INVALID pte *)
  Lemma exec_eff_rec_walk_l1_invalid (base : SailStdpp.Values.mword 44)
        (pte : SailStdpp.Values.mword 64) (g : bool) (es1 : list weff)
        (wfacc : Acc (Zwf 0) 1) s :
    exec_eff (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok pte, s, es1) ->
    wpte_invalid pte ->
    exec_eff (_rec_pt_walk 39 vpn acc p mxr do_sum base 1 g tt 1 wfacc) s
      = Some (Err (PTW_Invalid_PTE tt, tt), s, es1).
  Proof.
    intros Hrd Hinv.
    destruct wfacc as [a1].
    walk_eff_peel_asserts 1 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 17 9)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_eff_peel_read Hrd.
    (* an INVALID pte fails the follow-a-pointer test's first conjunct *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec_eff (Defs.and_boolM A B) s = Some (false, s, [])) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec_eff (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s, [])) end.
      { rewrite (exec_eff_bind_nil _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_eff_returnM. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hv). cbn match beta. apply exec_eff_returnM. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hab). cbn match beta.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_check_leaf_pte_invalid pte
                  (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 1 s Hinv)).
    cbn match beta zeta.
    rewrite exec_eff_returnM. cbn match. by rewrite ?app_nil_r.
  Qed.

  (* level 1: a valid non-leaf step whose LEVEL-0 sub-walk returns [r]
     with trace [es_sub] (result-generic: instantiate with the
     invalid/noperm leaf faults; [r] and [es_sub] must not depend on the
     accumulated global bit, which fault results never do) *)
  Lemma exec_eff_rec_walk_l1_sub (base : SailStdpp.Values.mword 44)
        (pte : SailStdpp.Values.mword 64) (g : bool)
        (r : result (PTW_Output 39 * unit) (PTW_Error * unit))
        (es1 es_sub : list weff) (wfacc : Acc (Zwf 0) 1) s :
    exec_eff (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok pte, s, es1) ->
    wpte_valid pte ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = true ->
    (forall (g' : bool) (a : Acc (Zwf 0) 0),
       exec_eff (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte) 0 g' tt 0 a) s
         = Some (r, s, es_sub)) ->
    exec_eff (_rec_pt_walk 39 vpn acc p mxr do_sum base 1 g tt 1 wfacc) s
      = Some (r, s, (es1 ++ es_sub)%list).
  Proof.
    intros Hrd Hinv Hnl Hsub.
    destruct wfacc as [a1].
    walk_eff_peel_asserts 1 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 17 9)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_eff_peel_read Hrd.
    (* valid AND non-leaf AND level > 0: follow the pointer *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec_eff (Defs.and_boolM A B) s = Some (true, s, [])) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec_eff (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s, [])) end.
      { rewrite (exec_eff_bind_nil _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_eff_returnM. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hv). cbn match beta.
      rewrite Hnl. change (1 >? 0) with true. cbn [andb]. apply exec_eff_returnM. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hab). cbn match beta.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (1 - 1)] =>
      change (1 - 1) with 0 end.
    rewrite Hsub. cbn match. by rewrite ?app_nil_r.
  Qed.

  (* level 2 (= the full [pt_walk]): the root slot holds an INVALID pte *)
  Lemma exec_eff_pt_walk_user_l2_invalid (root : SailStdpp.Values.mword 44)
        (pte : SailStdpp.Values.mword 64) (es2 : list weff) s :
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok pte, s, es2) ->
    wpte_invalid pte ->
    exec_eff (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s
      = Some (Err (PTW_Invalid_PTE tt, tt), s, es2).
  Proof.
    intros Hrd Hinv.
    unfold pt_walk.
    destruct (Defs.Zwf_guarded _) as [a2].
    walk_eff_peel_asserts 2 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr root (subrange_vec_dec vpn 26 18)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_eff_peel_read Hrd.
    (* an INVALID pte fails the follow-a-pointer test's first conjunct *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec_eff (Defs.and_boolM A B) s = Some (false, s, [])) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec_eff (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s, [])) end.
      { rewrite (exec_eff_bind_nil _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_eff_returnM. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hv). cbn match beta. apply exec_eff_returnM. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hab). cbn match beta.
    rewrite (exec_eff_bind_nil _ _ _ _ _
               (exec_eff_check_leaf_pte_invalid pte
                  (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 2 s Hinv)).
    cbn match beta zeta.
    rewrite exec_eff_returnM. cbn match. by rewrite ?app_nil_r.
  Qed.

  (* level 2: a valid non-leaf step whose LEVEL-1 sub-walk returns [r] *)
  Lemma exec_eff_pt_walk_user_sub (root : SailStdpp.Values.mword 44)
        (pte : SailStdpp.Values.mword 64)
        (r : result (PTW_Output 39 * unit) (PTW_Error * unit))
        (es2 es_sub : list weff) s :
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok pte, s, es2) ->
    wpte_valid pte ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = true ->
    (forall (g' : bool) (a : Acc (Zwf 0) 1),
       exec_eff (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte) 1 g' tt 1 a) s
         = Some (r, s, es_sub)) ->
    exec_eff (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s
      = Some (r, s, (es2 ++ es_sub)%list).
  Proof.
    intros Hrd Hinv Hnl Hsub.
    unfold pt_walk.
    destruct (Defs.Zwf_guarded _) as [a2].
    walk_eff_peel_asserts 2 s.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr root (subrange_vec_dec vpn 26 18)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    walk_eff_peel_read Hrd.
    (* valid AND non-leaf AND level > 0: follow the pointer *)
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec_eff (Defs.and_boolM A B) s = Some (true, s, [])) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec_eff (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s, [])) end.
      { rewrite (exec_eff_bind_nil _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_eff_returnM. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hv). cbn match beta.
      rewrite Hnl. change (2 >? 0) with true. cbn [andb]. apply exec_eff_returnM. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hab). cbn match beta.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (2 - 1)] =>
      change (2 - 1) with 1 end.
    rewrite Hsub. cbn match. by rewrite ?app_nil_r.
  Qed.

  (* a faulting walk propagates through translate_TLB_miss unchanged
     (no TLB write on the fault path) *)
  Lemma exec_eff_translate_TLB_miss_user_walk_err
        (asid : SailStdpp.Values.mword 16) (root : SailStdpp.Values.mword 44)
        (f : PTW_Error) (es : list weff) s :
    exec_eff (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s
      = Some (Err (f, tt), s, es) ->
    exec_eff (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
      = Some (Err (f, tt), s, es).
  Proof.
    intros Hwalk.
    unfold translate_TLB_miss. cbn zeta.
    rewrite (exec_eff_bind_Some _ _ _ _ _ _ Hwalk).
    cbn match.
    rewrite exec_eff_returnm. cbn match. by rewrite ?app_nil_r.
  Qed.

End UserWalkFaultEff.

(* ====================================================================== *)
(** ** 7. THE [translate]-LEVEL DISPATCH, and the PtTree §8 mirrors

    [translate] is [lookup_TLB] followed by a hit/miss dispatch; the SC
    tree composes the dispatch inline at every use, so the two composers
    are named here once.  Then [PtTree] §8c/§8f replayed: the TLB-hit
    translate on a stored walk entry (O1 — state unchanged, EMPTY trace:
    every step of the hit path is register-only, which is also why the
    empty-memory detector would find it quiet; the syntactic replay is
    what sharpens quiet to the empty trace the bind spines need), the
    denied hit, and the blocked/denied fault translates. *)

(** Miss dispatch: result-generic, so it serves the success walk AND the
    fault walks (subsumes [CommonWalk.exec_translate_walk_user_err]). *)
Lemma exec_eff_translate_miss_user
    (vpn : SailStdpp.Values.mword 27) (root : SailStdpp.Values.mword 44)
    (asid : SailStdpp.Values.mword 16)
    (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool)
    (r : result (SailStdpp.Values.mword 44 * page_based_mem_type * unit) (PTW_Error * unit))
    (s s' : mstate) (es : list weff) :
  exec_eff (lookup_TLB 39 asid vpn) s = Some (None, s, []) ->
  exec_eff (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s
    = Some (r, s', es) ->
  exec_eff (translate 39 asid root vpn acc p mxr do_sum tt) s = Some (r, s', es).
Proof.
  intros Hlk Hmiss.
  unfold translate.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hlk).
  cbn match.
  exact Hmiss.
Qed.

(** Hit dispatch. *)
Lemma exec_eff_translate_hit_user
    (vpn : SailStdpp.Values.mword 27) (root : SailStdpp.Values.mword 44)
    (asid : SailStdpp.Values.mword 16) (idx : Z) (ent : TLB_Entry)
    (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool)
    (r : result (SailStdpp.Values.mword 44 * page_based_mem_type * unit) (PTW_Error * unit))
    (s s' : mstate) (es : list weff) :
  exec_eff (lookup_TLB 39 asid vpn) s = Some (Some (idx, ent), s, []) ->
  exec_eff (translate_TLB_hit 39 asid vpn acc p mxr do_sum tt idx ent) s
    = Some (r, s', es) ->
  exec_eff (translate 39 asid root vpn acc p mxr do_sum tt) s = Some (r, s', es).
Proof.
  intros Hlk Hhit.
  unfold translate.
  rewrite (exec_eff_bind_nil _ _ _ _ _ Hlk).
  cbn match.
  exact Hhit.
Qed.

Section PtHitEff.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (** O1: the TLB-HIT translate on a stored walk entry whose cached leaf
      word [q0] (an A/D variant of the current one) passes the check and
      needs no update — [PtTree.exec_translate_TLB_hit_pt] replayed.
      State unchanged, trace EMPTY. *)
  Lemma exec_eff_translate_TLB_hit_pt (vpn : SailStdpp.Values.mword 27)
        (p2 p1 q0 : SailStdpp.Values.mword 64)
        (asid : SailStdpp.Values.mword 16) (idx : Z) s :
    wpte_check_ok acc p mxr do_sum q0 ->
    update_PTE_Bits (autocast (T := mword) q0 : SailStdpp.Values.mword 64) acc = None ->
    pte_pbmt0 q0 ->
    exec_eff (translate_TLB_hit 39 asid vpn acc p mxr do_sum tt idx
                (u_walk_entry vpn p2 p1 q0 asid)) s
    = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE q0)) : SailStdpp.Values.mword 44), PBMT_PMA, tt), s, []).
  Proof.
    intros Hchk Hupd Hpb.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte.
    rewrite autocast_id.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (Hchk s)). cbn match.
    (* [update_and_write_pte] takes the whole tablewalk context now —
       including the entry's LEVEL, recovered from its levelMask by
       [tlb_get_level] — and returns the ext_ptw alongside. *)
    match goal with |- context[update_and_write_pte ?w ?vp ?a ?pv ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hu : exec_eff (update_and_write_pte w vp a pv lv ac pr mx ds e) s
                   = Some (Ok (None, tt), s, [])) end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] =>
        change w with 64 end.
      rewrite autocast_id in Hupd. rewrite Hupd.
      cbn match. apply exec_eff_returnM. }
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hu). cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_uwe_pbmt vpn p2 p1 q0 asid s Hpb)).
    rewrite uwe_ppn.
    apply exec_eff_returnm.
  Qed.

  (* the hit whose cached leaf word FAILS the check: the fault surfaces
     before any A/D update or pbmt read — state unchanged.  (The check
     runs FIRST on the hit path, so a denied hit never write-backs.) *)
  Lemma exec_eff_translate_TLB_hit_denied_pt (vpn : SailStdpp.Values.mword 27)
        (p2 p1 q0 : SailStdpp.Values.mword 64)
        (asid : SailStdpp.Values.mword 16) (idx : Z) s :
    wpte_check_denied acc p mxr do_sum (PTE_No_Permission tt) q0 ->
    exec_eff (translate_TLB_hit 39 asid vpn acc p mxr do_sum tt idx
                (u_walk_entry vpn p2 p1 q0 asid)) s
    = Some (Err (PTW_No_Permission tt, tt), s, []).
  Proof.
    intros Hden.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte.
    rewrite autocast_id.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (Hden s)). cbn match.
    apply exec_eff_returnm.
  Qed.

End PtHitEff.

(* ---- the FAULT translates over abstract path words ([PtTree] §8f).      *)
Section PtFaultEff.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  (* a blocked vpn: the walk stops at an INVALID word at level 2/1/0 —
     three lemmas with the EXACT per-arm trace, then the SC-shaped
     disjunctive wrapper with the trace existential *)
  Lemma exec_eff_translate_pt_blocks_l2 (vpn : SailStdpp.Values.mword 27)
        (root : SailStdpp.Values.mword 44) (w2 : SailStdpp.Values.mword 64)
        (es2 : list weff) s :
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok w2, s, es2) ->
    wpte_invalid w2 ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s, []) ->
    exec_eff (translate 39 (mword_of_int 0 : SailStdpp.Values.mword 16) root vpn acc p mxr do_sum tt) s
    = Some (Err (PTW_Invalid_PTE tt, tt), s, es2).
  Proof.
    intros Hrd2 Hi2 Hlk.
    apply (exec_eff_translate_miss_user vpn root (mword_of_int 0) acc p mxr do_sum _ s s _ Hlk).
    apply exec_eff_translate_TLB_miss_user_walk_err.
    exact (exec_eff_pt_walk_user_l2_invalid vpn acc p mxr do_sum root w2 es2 s Hrd2 Hi2).
  Qed.

  Lemma exec_eff_translate_pt_blocks_l1 (vpn : SailStdpp.Values.mword 27)
        (root : SailStdpp.Values.mword 44) (p2 w1 : SailStdpp.Values.mword 64)
        (es2 es1 : list weff) s :
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok p2, s, es2) ->
    wpte_valid p2 -> pte_ptr p2 ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok w1, s, es1) ->
    wpte_invalid w1 ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s, []) ->
    exec_eff (translate 39 (mword_of_int 0 : SailStdpp.Values.mword 16) root vpn acc p mxr do_sum tt) s
    = Some (Err (PTW_Invalid_PTE tt, tt), s, (es2 ++ es1)%list).
  Proof.
    intros Hrd2 Hv2 Hn2 Hrd1 Hi1 Hlk.
    apply (exec_eff_translate_miss_user vpn root (mword_of_int 0) acc p mxr do_sum _ s s _ Hlk).
    apply exec_eff_translate_TLB_miss_user_walk_err.
    apply (exec_eff_pt_walk_user_sub vpn acc p mxr do_sum root p2 _ es2 es1 s Hrd2 Hv2 Hn2).
    intros g' a.
    exact (exec_eff_rec_walk_l1_invalid vpn acc p mxr do_sum (u_next_base p2) w1 g' es1 a s Hrd1 Hi1).
  Qed.

  Lemma exec_eff_translate_pt_blocks_l0 (vpn : SailStdpp.Values.mword 27)
        (root : SailStdpp.Values.mword 44) (p2 p1 w0 : SailStdpp.Values.mword 64)
        (es2 es1 es0 : list weff) s :
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok p2, s, es2) ->
    wpte_valid p2 -> pte_ptr p2 ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok p1, s, es1) ->
    wpte_valid p1 -> pte_ptr p1 ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok w0, s, es0) ->
    wpte_invalid w0 ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s, []) ->
    exec_eff (translate 39 (mword_of_int 0 : SailStdpp.Values.mword 16) root vpn acc p mxr do_sum tt) s
    = Some (Err (PTW_Invalid_PTE tt, tt), s, (es2 ++ es1 ++ es0)%list).
  Proof.
    intros Hrd2 Hv2 Hn2 Hrd1 Hv1 Hn1 Hrd0 Hi0 Hlk.
    apply (exec_eff_translate_miss_user vpn root (mword_of_int 0) acc p mxr do_sum _ s s _ Hlk).
    apply exec_eff_translate_TLB_miss_user_walk_err.
    apply (exec_eff_pt_walk_user_sub vpn acc p mxr do_sum root p2 _ es2 (es1 ++ es0)%list s Hrd2 Hv2 Hn2).
    intros g' a.
    apply (exec_eff_rec_walk_l1_sub vpn acc p mxr do_sum (u_next_base p2) p1 g' _ es1 es0 a s Hrd1 Hv1 Hn1).
    intros g'' a'.
    exact (exec_eff_rec_walk_leaf_invalid vpn acc p mxr do_sum (u_next_base p1) w0 g'' es0 a' s Hrd0 Hi0).
  Qed.

  (** The [PtTree.exec_translate_pt_blocks]-shaped wrapper (drop-in for
      SC call sites that dispatch on the three-way stop disjunction; the
      per-arm trace is recovered from the arm by the lemmas above). *)
  Lemma exec_eff_translate_pt_blocks (vpn : SailStdpp.Values.mword 27)
        (root : SailStdpp.Values.mword 44) s :
    ((exists w2 es2,
        exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
          = Some (Ok w2, s, es2) /\ wpte_invalid w2)
     \/ (exists p2 w1 es2 es1,
        exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
          = Some (Ok p2, s, es2) /\ wpte_valid p2 /\ pte_ptr p2 /\
        exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
          = Some (Ok w1, s, es1) /\ wpte_invalid w1)
     \/ (exists p2 p1 w0 es2 es1 es0,
        exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
          = Some (Ok p2, s, es2) /\ wpte_valid p2 /\ pte_ptr p2 /\
        exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
          = Some (Ok p1, s, es1) /\ wpte_valid p1 /\ pte_ptr p1 /\
        exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
          = Some (Ok w0, s, es0) /\ wpte_invalid w0)) ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s, []) ->
    exists es,
      exec_eff (translate 39 (mword_of_int 0 : SailStdpp.Values.mword 16) root vpn acc p mxr do_sum tt) s
      = Some (Err (PTW_Invalid_PTE tt, tt), s, es).
  Proof.
    intros Hstop Hlk.
    destruct Hstop as [ (w2 & es2 & Hrd2 & Hi2)
                      | [ (p2 & w1 & es2 & es1 & Hrd2 & Hv2 & Hn2 & Hrd1 & Hi1)
                        | (p2 & p1 & w0 & es2 & es1 & es0 & Hrd2 & Hv2 & Hn2 & Hrd1 & Hv1 & Hn1 & Hrd0 & Hi0) ] ].
    - eexists. exact (exec_eff_translate_pt_blocks_l2 vpn root w2 es2 s Hrd2 Hi2 Hlk).
    - eexists. exact (exec_eff_translate_pt_blocks_l1 vpn root p2 w1 es2 es1 s
                        Hrd2 Hv2 Hn2 Hrd1 Hi1 Hlk).
    - eexists. exact (exec_eff_translate_pt_blocks_l0 vpn root p2 p1 w0 es2 es1 es0 s
                        Hrd2 Hv2 Hn2 Hrd1 Hv1 Hn1 Hrd0 Hi0 Hlk).
  Qed.

  (* mapped but DENIED: the walk reaches the leaf and the permission
     check fails — no fill, no write-back, state unchanged
     ([PtTree.exec_translate_pt_denied] replayed) *)
  Lemma exec_eff_translate_pt_denied (vpn : SailStdpp.Values.mword 27)
        (root : SailStdpp.Values.mword 44)
        (p2 p1 p0 : SailStdpp.Values.mword 64) (es2 es1 es0 : list weff) s :
    wpte_valid p2 -> pte_ptr p2 ->
    wpte_valid p1 -> pte_ptr p1 ->
    wpte_valid p0 -> pte_leaf p0 ->
    wpte_check_denied acc p mxr do_sum (PTE_No_Permission tt) p0 ->
    exec_eff (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok p2, s, es2) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok p1, s, es1) ->
    exec_eff (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok p0, s, es0) ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s, []) ->
    exec_eff (translate 39 (mword_of_int 0 : SailStdpp.Values.mword 16) root vpn acc p mxr do_sum tt) s
    = Some (Err (PTW_No_Permission tt, tt), s, (es2 ++ es1 ++ es0)%list).
  Proof.
    intros Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hden Hrd2 Hrd1 Hrd0 Hlk.
    apply (exec_eff_translate_miss_user vpn root (mword_of_int 0) acc p mxr do_sum _ s s _ Hlk).
    apply exec_eff_translate_TLB_miss_user_walk_err.
    apply (exec_eff_pt_walk_user_sub vpn acc p mxr do_sum root p2 _ es2 (es1 ++ es0)%list s Hrd2 Hv2 Hn2).
    intros g' a.
    apply (exec_eff_rec_walk_l1_sub vpn acc p mxr do_sum (u_next_base p2) p1 g' _ es1 es0 a s Hrd1 Hv1 Hn1).
    intros g'' a'.
    change (PTW_No_Permission tt) with (ext_get_ptw_error (PTE_No_Permission tt)).
    exact (exec_eff_rec_walk_leaf_noperm vpn acc p mxr do_sum (u_next_base p1) p0 g''
             (PTE_No_Permission tt) es0 a' s Hrd0 Hv0 Hl0 Hden).
  Qed.

  (* the soundness KEYSTONE, at [exec_eff]: under [tlb_ok_pt] a BLOCKED
     vpn is never TLB-resident ([PtTree.tlb_ok_pt_lookup_blocked]
     replayed on the eff lookup twins; the pure discrimination is
     [PtTree]'s verbatim) *)
  Lemma wtlb_ok_pt_lookup_blocked (t : ptree) (vpn : SailStdpp.Values.mword 27)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6)) s :
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    ptree_blocks t vpn ->
    register_lookup tlb s.(sregs) = tlbvec ->
    exec_eff (lookup_TLB 39 (mword_of_int 0) vpn) s = Some (None, s, []).
  Proof.
    intros Hok Hblk Htlb.
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - destruct (Hok vpn ent Hslot) as (vpn0 & q2 & q1 & q0 & a' & d' & Hm0 & Hh & ->).
      apply (exec_eff_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec s Htlb Hslot).
      apply (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad q0 a' d') (mword_of_int 0)).
      intros ->. exact (ptree_maps_blocks_excl t vpn q2 q1 q0 Hm0 Hblk).
    - exact (exec_eff_lookup_TLB_miss vpn (mword_of_int 0) tlbvec s Htlb Hslot).
  Qed.

End PtFaultEff.

(* ====================================================================== *)
(** ** 8. THE [translateAddr] FRONT HEADS — [PtTreeAdue] §5 replayed

    The S-mode front matter factored once over an arbitrary [translate]
    outcome: mstatus/priv reads, Sv39 dispatch, canonicality, satp →
    root/asid, and the pa concatenation.  PRIVILEGE-GENERIC exactly as
    the SC originals: Supervisor callers discharge [Htm] with
    [exec_eff_translationMode_S_sv39], the privilege bricks with
    [exec_eff_effectivePrivilege_mprv0] / [exec_eff_is_shadow_stack_u_acc].
    The [translate] premise carries the walk's trace [es_tr] (fixed
    across the ∀-mxr/do_sum quantification, as it is in every arm built
    above), and the head passes it through unchanged — the front matter
    is register-only.  Only the [update_PTE_Bits = None] outcomes (O1/O2)
    are ever fed in here in batch 6a; the head itself is outcome-generic
    like its SC original. *)

Section PtFrontEff.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  Lemma exec_eff_translateAddr_pt_front (vpn : SailStdpp.Values.mword 27)
        (root : SailStdpp.Values.mword 44) (ppnv : SailStdpp.Values.mword 44)
        (satp0 va pa : SailStdpp.Values.mword 64) (es_tr : list weff)
        (s s' : mstate) :
    exec_eff (effectivePrivilege acc (register_lookup mstatus s.(sregs)) p) s
      = Some (p, s, []) ->
    exec_eff (is_shadow_stack_access acc) s = Some (false, s, []) ->
    register_lookup cur_privilege s.(sregs) = p ->
    exec_eff (translationMode p) s = Some (Sv39, s, []) ->
    register_lookup satp s.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : SailStdpp.Values.mword 64)) = root ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : SailStdpp.Values.mword 64)) = (mword_of_int 0 : SailStdpp.Values.mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    (forall mxr do_sum,
       exec_eff (translate 39 (mword_of_int 0 : SailStdpp.Values.mword 16) root vpn acc p mxr do_sum tt) s
       = Some (Ok (ppnv, PBMT_PMA, tt), s', es_tr)) ->
    zero_extend' 64 (concat_vec ppnv
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    exec_eff (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s', es_tr).
  Proof.
    intros Heff Hss Hcp Htm Hsatp Hppn Hasid Hcanon Hvpn_def Htr Hident.
    unfold translateAddr.
    rewrite exec_eff_catch_early_return.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Heff).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Htm).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hss).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match.
    assert (Hwidth : exec_eff (satp_mode_width_forwards Sv39) s = Some (39, s, []))
      by (cbn; apply exec_eff_returnm).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec_eff (get_satp 39) s = Some (autocast (T := mword) satp0, s, [])).
    { unfold get_satp.
      assert (Hae : exec_eff (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s, [])).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_eff_returnm. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg satp s)).
      rewrite Hsatp. apply exec_eff_returnm. }
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec_eff (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s, [])).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_eff_returnm. }
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace bppn with root by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : SailStdpp.Values.mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_eff_liftR_cat _ _ _ _ _ _ (Htr _ _)).
    cbn match.
    rewrite execR_eff_returnR. cbn match.
    match goal with |- context[Physaddr ?e] =>
      replace e with pa by (symmetry; exact Hident) end.
    by rewrite ?app_nil_r.
  Qed.

  (* the same head over a FAILED [translate] outcome: the PTW error maps
     through [translationException] and surfaces as the page-fault
     exception, state unchanged (fault walks write nothing) *)
  Lemma exec_eff_translateAddr_pt_front_err (vpn : SailStdpp.Values.mword 27)
        (root : SailStdpp.Values.mword 44) (f : PTW_Error) (e : ExceptionType)
        (satp0 va : SailStdpp.Values.mword 64) (es_tr : list weff) (s : mstate) :
    exec_eff (effectivePrivilege acc (register_lookup mstatus s.(sregs)) p) s
      = Some (p, s, []) ->
    exec_eff (is_shadow_stack_access acc) s = Some (false, s, []) ->
    register_lookup cur_privilege s.(sregs) = p ->
    exec_eff (translationMode p) s = Some (Sv39, s, []) ->
    register_lookup satp s.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : SailStdpp.Values.mword 64)) = root ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : SailStdpp.Values.mword 64)) = (mword_of_int 0 : SailStdpp.Values.mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    (forall mxr do_sum,
       exec_eff (translate 39 (mword_of_int 0 : SailStdpp.Values.mword 16) root vpn acc p mxr do_sum tt) s
       = Some (Err (f, tt), s, es_tr)) ->
    exec_eff (translationException acc f) s = Some (e, s, []) ->
    exec_eff (translateAddr (Virtaddr va) acc) s
    = Some (Err (e, tt), s, es_tr).
  Proof.
    intros Heff Hss Hcp Htm Hsatp Hppn Hasid Hcanon Hvpn_def Htr Hte.
    unfold translateAddr.
    rewrite exec_eff_catch_early_return.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Heff).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Htm).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hss).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match.
    assert (Hwidth : exec_eff (satp_mode_width_forwards Sv39) s = Some (39, s, []))
      by (cbn; apply exec_eff_returnm).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec_eff (get_satp 39) s = Some (autocast (T := mword) satp0, s, [])).
    { unfold get_satp.
      assert (Hae : exec_eff (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s, [])).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_eff_returnm. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg satp s)).
      rewrite Hsatp. apply exec_eff_returnm. }
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec_eff (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s, [])).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_eff_returnm. }
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace bppn with root by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : SailStdpp.Values.mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_eff_liftR_cat _ _ _ _ _ _ (Htr _ _)).
    cbn match.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hte).
    rewrite execR_eff_returnR. cbn match.
    by rewrite ?app_nil_r.
  Qed.

  (* NON-CANONICAL va: the fault fires at the canonicality test, before
     the TLB or any memory read — no satp geometry needed beyond the
     mode dispatch, and the trace is EMPTY *)
  Lemma exec_eff_translateAddr_pt_front_noncanon (f := PTW_Invalid_Addr tt)
        (e : ExceptionType) (satp0 va : SailStdpp.Values.mword 64) (s : mstate) :
    exec_eff (effectivePrivilege acc (register_lookup mstatus s.(sregs)) p) s
      = Some (p, s, []) ->
    exec_eff (is_shadow_stack_access acc) s = Some (false, s, []) ->
    register_lookup cur_privilege s.(sregs) = p ->
    exec_eff (translationMode p) s = Some (Sv39, s, []) ->
    register_lookup satp s.(sregs) = satp0 ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = true ->
    exec_eff (translationException acc (PTW_Invalid_Addr tt)) s = Some (e, s, []) ->
    exec_eff (translateAddr (Virtaddr va) acc) s
    = Some (Err (e, tt), s, []).
  Proof.
    intros Heff Hss Hcp Htm Hsatp Hcanon Hte.
    unfold translateAddr.
    rewrite exec_eff_catch_early_return.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg mstatus s)).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ (exec_eff_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Heff).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Htm).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hss).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_eff_bind_eq. rewrite execR_eff_returnR. cbn match.
    assert (Hwidth : exec_eff (satp_mode_width_forwards Sv39) s = Some (39, s, []))
      by (cbn; apply exec_eff_returnm).
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec_eff (get_satp 39) s = Some (autocast (T := mword) satp0, s, [])).
    { unfold get_satp.
      assert (Hae : exec_eff (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s, [])).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_eff_returnm. }
      rewrite (exec_eff_bind_nil _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg satp s)).
      rewrite Hsatp. apply exec_eff_returnm. }
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec_eff (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s, [])).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_eff_returnm. }
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_eff_liftR_seq _ _ _ _ _ Hte).
    rewrite execR_eff_returnR. cbn match.
    reflexivity.
  Qed.

End PtFrontEff.

Print Assumptions exec_eff_translateAddr_pt_front.
Print Assumptions exec_eff_translate_TLB_miss_user.
Print Assumptions exec_eff_translate_pt_denied.
Print Assumptions wpt_read_pte_slot.
