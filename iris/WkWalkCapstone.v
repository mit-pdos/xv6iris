(** * WkWalkCapstone.v — THE WALK-BRIDGE VALIDATION CAPSTONE
      (walk-bridge §8, 6c: one whole WP leaf for a FETCH-WALKING S-mode
       instruction)

    Everything below [WkWalkRule] is pure; everything above it is resources.
    This file is the ONE place where the two meet: it threads
    [WkFetchPeel] §6's fupd ([wkpt_fetch_peel_at]) into a [wwalk_site]-shaped
    site predicate, drives [WkWalkRule.wp_wwalk_step], and re-establishes the
    successor's state interpretation — for the concrete instruction

      [addi rd, rs1, imm]   ([uint rd <> 0])

    executed at a KERNEL VIRTUAL ADDRESS [va] mapped executable by the kernel
    page table ([kmap_at (svpn_of va) ppn kpc]), where the fetch may TLB-miss,
    WALK the three levels, and CAS the leaf PTE's A-bit back.

    ------------------------------------------------------------------
    WHAT THE LEAF OWES ITS CALLER, and where each half comes from.

    (a) THE SITE.  [wwalk_site] (WkWalkRule §3) is σ-indexed, so it is
        established INSIDE the rule's σ-callback, out of
        [wkpt_fetch_peel_at]'s pure exports (the ∀bf [wwalk_exports] /
        [wfetch_gates] pair at [wmi σ bf]) plus this file's register-owned
        gates and [WkWalkTails]' four tail dischargers.  The rule fixes
        [(la, Φ)] BEFORE the callback while the fupd MINTS [p2 p1 lw] per σ,
        so the leaf takes [p2 p1 lw] as PARAMETERS and the caller's σ-callback
        pins them by the three [pt_slot_mem] facts; §6's [pt_slot_mem_inj]
        collapses the minted values onto the parameters (a [pt_slot_mem] is a
        flat-memory lookup, hence functional in the word).  The [region] is
        NOT pinned that way — nothing σ-local exports the [matching_pma_region]
        equation — so the site predicate quantifies it existentially and §6's
        certificate destructs it.

    (b) THE GHOST SIDE.  The fupd hands back [reg_interp (wm_regs σ)], a
        bf-indexed REGISTER WAND across the hidden [tlb] update, and the
        read-only / write-back disjunction carrying the log and latest-write
        authorities.  In the continuation the leaf REBUILDS the successor's
        mirror run concretely (§§5–6: the walk member, the text read, the ADDI
        [execute], the retire postlude, the clock tick) and pins
        [wflat_st σ'] against it by determinism of [exec_stale]; from there
        the register moves are ordinary [reg_update]s and the log is the
        arm's own authority.

    ------------------------------------------------------------------
    THE TWO RECORDED DEBTS, both flagged at their use sites:

      - the φ-mechanization's stand-in.  [wp_wwalk_step] carries no
        [sync_win]; what a caller owes instead is the clean/published state
        of the bytes the step touches (WkWalkRule's header).  Here that is
        the σ-callback conjunct ⌜∀ a, nv_free (wm_log σ) a⌝, which is what
        re-establishes [nv_hart] at σ' (§6, [nv_hart_of_free]).  The
        absorption theorem already exports the leaf window's half of it
        (⌜∀ j < 8, nv_free (wm_log σ) (acc_addr la j)⌝); the REST of the
        address space is the φ item that is not mechanized.

      - [wwalk_cert]'s [pinned_read] hypothesis at the PC — inherited from
        [WeakRacy.wracy_cert]'s shape, where the "pc" window was physical.
        [wp_wwalk_step_cert_of_peel] never uses it (the fetch's text
        pinnedness is [wwalk_site]'s, at [pa]), so it too is a σ-callback
        conjunct rather than a resource obligation. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import RiscvTryStep.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakGhost WeakExec.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakEffSkel WeakLeafEffCommon WeakFetchEff.
Require Import WeakRacy WeakVarCert WeakStale WeakWalkStale.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree.
Require Import SmodeCore.
Require Import WeakWalkEff.
Require Import WeakVariant WeakKpt WeakKptStale.
Require Import WkFetchPeel WkStepPeel WkWalkRule WkWalkTails.
Require Import WeakTickEff.
Require Import RegFile WpGpr WpMmodeLeafBase WpDecodeBridge.
Require Import WeakLeafWin WkEntryEff.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ====================================================================== *)
(** ** 1. THE S-MODE INTERRUPT GATE, AT [exec_eff]

    [WkStepPeel]'s step peel is gated by ⌜[dispatchInterrupt Supervisor]
    returns [None]⌝ at the post-flag-write states — the S-mode analogue of
    the M-mode [MIE = false] gate, and the one register-only fact of the
    wrapper that the weak tree did not yet have at [exec_eff].
    [SmodeCore.exec_getPendingSet_supervisor_none]'s script, mirrored the way
    [WeakFetchEff] §5 mirrors the Machine one: same lemma names with
    [exec_eff_] for [exec_], same three register facts.

    The register facts are xv6's: [misa.S] set, everything the kernel enables
    is delegated ([mie & ~mideleg = 0]) and S-level interrupts are globally
    off ([mstatus.SIE = 0]). *)

Section SIntrEff.
  Context (s : mstate).
  Hypothesis HmisaS :
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HSIE :
    eq_vec (_get_Mstatus_SIE (register_lookup mstatus s.(sregs))) ('b"1") = false.
  Hypothesis Hand0 :
    and_vec (register_lookup mie s.(sregs))
            (not_vec (register_lookup mideleg s.(sregs))) = zeros' 64.

  (** At [Supervisor] the M-destined gate is TRUE (the [or_boolM]'s right
      disjunct is [Supervisor = Supervisor]), which is why the S-mode proof
      needs [mie & ~mideleg = 0] where the Machine one needed nothing. *)
  Lemma exec_eff_mIE_S_true :
    exec_eff (Defs.or_boolM
            (Defs.and_boolM (returnM (generic_eq Supervisor Machine))
               (Defs.bind (Defs.read_reg mstatus)
                  (fun w7 : SailStdpp.Values.mword 64 =>
                     returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
            (returnM (orb (generic_eq Supervisor Supervisor)
                          (generic_eq Supervisor User)))) s
      = Some (true, s, []).
  Proof.
    assert (Hand : exec_eff (Defs.and_boolM (returnM (generic_eq Supervisor Machine))
                     (Defs.bind (Defs.read_reg mstatus)
                        (fun w7 : SailStdpp.Values.mword 64 =>
                           returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                   = Some (false, s, [])).
    { rewrite (exec_eff_and_boolM_nil _ _ _ _ _
                 (exec_eff_returnM (generic_eq Supervisor Machine) s)).
      change (generic_eq Supervisor Machine) with false. cbn match. reflexivity. }
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hand).
    change (orb (generic_eq Supervisor Supervisor) (generic_eq Supervisor User))
      with true.
    apply exec_eff_returnm.
  Qed.

  Lemma exec_eff_sIE_S_false :
    exec_eff (Defs.or_boolM
            (Defs.and_boolM (returnM (generic_eq Supervisor Supervisor))
               (Defs.bind (Defs.read_reg mstatus)
                  (fun w : SailStdpp.Values.mword 64 =>
                     returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq Supervisor User))) s
      = Some (false, s, []).
  Proof using HSIE.
    assert (Hand : exec_eff (Defs.and_boolM (returnM (generic_eq Supervisor Supervisor))
                     (Defs.bind (Defs.read_reg mstatus)
                        (fun w : SailStdpp.Values.mword 64 =>
                           returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (false, s, [])).
    { rewrite (exec_eff_and_boolM_nil _ _ _ _ _
                 (exec_eff_returnM (generic_eq Supervisor Supervisor) s)).
      change (generic_eq Supervisor Supervisor) with true. cbn match.
      rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mstatus s)).
      rewrite HSIE. apply exec_eff_returnm. }
    rewrite (exec_eff_or_boolM_nil _ _ _ _ _ Hand).
    change (generic_eq Supervisor User) with false. apply exec_eff_returnm.
  Qed.

  Lemma exec_eff_getPendingSet_supervisor_none :
    exec_eff (getPendingSet Supervisor) s = Some (None, s, []).
  Proof using HmisaS HSIE Hand0.
    destruct (exec_eff_read_mip_some s HmisaS) as [mipv Hmip].
    unfold getPendingSet.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_cE_S_true s HmisaS)).
    cbn match.
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mideleg s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ Hmip).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mie s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ (exec_eff_read_reg mie s)).
    rewrite (exec_eff_bind_nil _ _ _ _ _ exec_eff_mIE_S_true).
    rewrite (exec_eff_bind_nil _ _ _ _ _ exec_eff_sIE_S_false).
    rewrite Hand0.
    rewrite and_vec_zeros64_r.
    assert (Hnq : neq_vec (zeros' 64 : SailStdpp.Values.mword 64) (zeros' 64) = false)
      by (vm_compute; reflexivity).
    rewrite Hnq. cbn [andb]. apply exec_eff_returnm.
  Qed.

  Lemma exec_eff_dispatchInterrupt_supervisor_none :
    exec_eff (dispatchInterrupt Supervisor) s = Some (None, s, []).
  Proof using HmisaS HSIE Hand0.
    apply exec_eff_dispatchInterrupt_none.
    exact exec_eff_getPendingSet_supervisor_none.
  Qed.

End SIntrEff.

(* ====================================================================== *)
(** ** 2. THE MIRROR AT THE COHERENT WORD IS THE ORDINARY ONE

    The rule's reducibility witness is one ORDINARY [exec] run of
    [riscv_step false] at [wflat_st σ] — the SC side, at the COHERENT value
    of the window.  §4 builds the mirror run of every admissible word; this
    is what turns the member at the coherent word [lw] back into an
    [exec_eff] run.

    [WeakStale] §3's backward transfer ([exec_eff_of_exec_stale]) does not
    reach it: its side condition is [trace_off_win], and the walk's PLAIN
    leaf read is an unpinned read AT the window.  What is true instead is
    that at [w := lw] the PATCH IS THE IDENTITY ([write_bytes_id]), so every
    read — pinned or not — sees the same memory in both interpreters, and
    the only thing that can break the invariant is the walk's own write-back.
    [tstale_id] is exactly the residue: after a RAM write, the rest of the
    trace must be [trace_off_win] (for the walking step it is — the only
    later access is the TEXT read, which the site's [racc_disj la 8 pa 4]
    puts off the window), and from there the landed transfer finishes. *)

Fixpoint tstale_id (ra : Arch.pa) (rn : N) (es : list weff) : Prop :=
  match es with
  | [] => True
  | WEwrite _ _ _ _ :: es' => trace_off_win ra rn es'
  | _ :: es' => tstale_id ra rn es'
  end.

Lemma exec_eff_of_exec_stale_id (ra : Arch.pa) (rn : N) (w : bv (8 * rn))
    {X} (m : M X) :
  acc_wf ra rn ->
  forall s x t es,
    write_bytes s.(mem) ra rn w = s.(mem) ->
    exec_stale ra rn w m s = Some (x, t, es) ->
    tstale_id ra rn es ->
    exec_eff m s = Some (x, t, es).
Proof.
  intros Hracc.
  induction m as [y0 | T oc k IH]; intros s x tf es Hid Hex Hts.
  - simpl in Hex |- *. exact Hex.
  - destruct oc; simpl in Hex |- *; try discriminate;
      try (exact (IH _ _ _ _ _ Hid Hex Hts)).
    + (* RegWrite: the memory does not move *)
      exact (IH _ (set_reg s reg regval) _ _ _ Hid Hex Hts).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hdev.
      * destruct (dev_read _ _ _) as [[v0 d']|] eqn:Hdr; [|discriminate].
        exact (IH _ (MState s.(sregs) s.(mem) d') _ _ _ Hid Hex Hts).
      * (* the stale memory IS the memory: the patch is the identity *)
        assert (Hsm : stale_mem ra rn w
                        (classify (Interface.ReadReq.access_kind t)) s
                      = s.(mem)).
        { destruct (ak_pins (classify (Interface.ReadReq.access_kind t)))
            eqn:Hpin.
          - by rewrite (stale_mem_pins _ _ _ _ _ Hpin).
          - by rewrite (stale_mem_unpinned _ _ _ _ _ Hpin) Hid. }
        rewrite Hsm in Hex.
        destruct (read_bytes s.(mem) _ _) as [v0|] eqn:Hrb; [|discriminate].
        destruct (exec_stale ra rn w (k _) s) as [[[x0 t0] es0]|] eqn:Hee;
          [|discriminate].
        injection Hex as <- <- <-.
        rewrite (IH _ s _ _ _ Hid Hee Hts). reflexivity.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hdev.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|discriminate].
        exact (IH _ (MState s.(sregs) s.(mem) d') _ _ _ Hid Hex Hts).
      * (* the RAM write may break the identity — and from here the landed
           [trace_off_win] transfer takes over, which is what [tstale_id]
           records *)
        destruct (exec_stale ra rn w (k _) _) as [[[x0 t0] es0]|] eqn:Hee;
          [|discriminate].
        injection Hex as <- <- <-.
        rewrite (exec_eff_of_exec_stale ra rn w (k (inl None)) Hracc _ _ _ _
                   Hee Hts).
        reflexivity.
    + (* Barrier *)
      destruct (exec_stale ra rn w (k tt) s) as [[[x0 t0] es0]|] eqn:Hee;
        [|discriminate].
      injection Hex as <- <- <-.
      rewrite (IH tt s _ _ _ Hid Hee Hts). reflexivity.
Qed.

(** The two [tstale_id] facts the walking step's traces need: the walk's own
    events (six literal shapes, at most one write, always LAST) followed by
    the text read. *)
Lemma tstale_id_app_reads (ra : Arch.pa) (rn : N) (es1 es2 : list weff) :
  (forall (ak : akinfo) (pa : Arch.pa) (n : N) (v : bv (8 * n)),
     WEwrite ak pa n v ∈ es1 -> False) ->
  tstale_id ra rn es2 ->
  tstale_id ra rn (es1 ++ es2).
Proof.
  induction es1 as [|e es1 IH]; intros Hno H2; [exact H2|].
  destruct e as [ak pa n|ak pa n v|b]; simpl.
  - apply IH; [|exact H2]. intros ak' pa' n' v' Hin.
    apply (Hno ak' pa' n' v'), elem_of_cons. by right.
  - destruct (Hno ak pa n v). apply elem_of_cons. by left.
  - apply IH; [|exact H2]. intros ak' pa' n' v' Hin.
    apply (Hno ak' pa' n' v'), elem_of_cons. by right.
Qed.

(* ====================================================================== *)
(** ** 3. THE RETIRE POSTLUDE, WITH ITS STATE PINNED

    [WkWalkTails.exec_eff_ts_after_rha_retire] proves the postlude TOTAL on
    the retire arm, which is all the peel needs; the ghost side needs to know
    WHICH registers moved, so here is the same script with the post-state
    spelled out.  It is the PC tick ([nextPC] into [PC]) and, when the
    funnel's [minstret_increment] flag is set, the counter bump — and
    nothing else. *)

Definition ts_tick_pc (s : mstate) : mstate :=
  set_reg s PC (register_lookup nextPC s.(sregs)).

Definition ts_post (s : mstate) : mstate :=
  if register_lookup (R_bool minstret_increment) s.(sregs)
  then set_reg (ts_tick_pc s) minstret
         (add_vec_int (register_lookup minstret (ts_tick_pc s).(sregs)) 1)
  else ts_tick_pc s.

Lemma exec_eff_ts_after_rha_retire_at (s : mstate)
    (ib : SailStdpp.Values.mword 32) :
  register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
  exec_eff (ts_after_rha (Step_Execute (RETIRE_SUCCESS, ib))) s
    = Some (false, ts_post s, []).
Proof.
  intros Hhart.
  assert (Hmi : register_lookup (R_bool minstret_increment)
                  (ts_tick_pc s).(sregs)
                = register_lookup (R_bool minstret_increment) s.(sregs)).
  { unfold ts_tick_pc. rewrite sregs_set_reg.
    apply (irrelevant_register_set (R_bool minstret_increment) PC);
      vm_compute; reflexivity. }
  unfold ts_after_rha. cbv beta. unfold RETIRE_SUCCESS. cbn match beta iota.
  erewrite exec_eff_bind_nil.
  2:{ erewrite exec_eff_bind0_nil.
      2:{ erewrite exec_eff_bind_nil.
          2:{ apply exec_eff_read_reg. }
          rewrite Hhart. unfold Defs.assert_exp. cbn [hart_is_active].
          reflexivity. }
      apply exec_eff_read_reg. }
  rewrite Hhart. cbn beta iota.
  erewrite exec_eff_bind0_nil. 2:{ apply exec_eff_tick_pc. }
  erewrite exec_eff_bind_nil.
  2:{ unfold Defs.and_boolM. erewrite exec_eff_bind_nil. 2:{ reflexivity. }
      cbn beta iota. apply (exec_eff_read_reg minstret_increment). }
  change (get_config_rvfi tt) with false.
  change (set_reg s PC (register_lookup nextPC s.(sregs))) with (ts_tick_pc s).
  rewrite Hmi. unfold ts_post.
  destruct (register_lookup (R_bool minstret_increment) s.(sregs)).
  - erewrite exec_eff_bind0_nil.
    2:{ erewrite exec_eff_bind0_nil.
        2:{ erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg minstret). }
            apply exec_eff_write_reg. }
        cbn beta iota. reflexivity. }
    cbn beta iota. rewrite exec_eff_returnm. cbn match. reflexivity.
  - erewrite exec_eff_bind0_nil.
    2:{ erewrite exec_eff_bind0_nil.
        2:{ cbn beta iota. reflexivity. }
        cbn beta iota. reflexivity. }
    cbn beta iota. rewrite exec_eff_returnm. cbn match. reflexivity.
Qed.

(* ====================================================================== *)
(** ** 4. THE INSTRUCTION: [addi rd, rs1, imm]

    The two things [WkWalkTails]' interfaces ask of an instruction: that its
    [execute] retires everywhere, quietly, moving only registers the
    classifier [F] admits ([wexec_regonly]), and that [F] does not admit
    [hart_state] (the postlude's [assert_exp (hart_is_active …)] is where a
    wilder execute would break the step).  Both are read off
    [WkEntryEff.exec_eff_execute_ITYPE_ADDI_gpr] with
    [F := λ r, register_beq r rd's cell]. *)

Definition F_gpr (rd : mword 5) : register -> bool :=
  fun r => register_beq r (R_bitvector_64 (gpr_of_Z (uint rd))).

Lemma F_gpr_hart_state (rd : mword 5) : F_gpr rd hart_state = false.
Proof. reflexivity. Qed.

Lemma F_gpr_tlb (rd : mword 5) : F_gpr rd tlb = false.
Proof. reflexivity. Qed.

Lemma wexec_regonly_addi (rs1 rd : mword 5) (imm : mword 12) :
  uint rd <> 0 ->
  wexec_regonly (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) (F_gpr rd).
Proof.
  intros Hrd s.
  pose proof (exec_eff_execute_ITYPE_ADDI_gpr rs1 rd imm s) as He.
  replace (Z.eqb (uint rd) 0) with false in He
    by (symmetry; apply Z.eqb_neq; exact Hrd).
  eexists. split; [exact He|].
  intros r HF. cbn [sregs set_reg].
  exact (irrelevant_register_set r (R_bitvector_64 (gpr_of_Z (uint rd)))
           s.(sregs) _ HF).
Qed.

(** The ADDI's post-state, at a state whose registers agree with σ's off
    [tlb] and off the [minstret_increment] flag — which is where the walk
    leaves them.  The SOURCE operand is read from σ's own register file
    (x0-safe, [WpGpr.gpr_pt_value]'s shape), so the leaf's continuation can
    name the result. *)
Lemma gpr_addi_val_off (rs1 : mword 5) (imm : mword 12) (t : mstate)
    (npc : SailStdpp.Values.mword 64) (v : SailStdpp.Values.mword 64) :
  (if Z.eqb (uint rs1) 0 then zero_reg
   else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) t.(sregs)) = v ->
  gpr_addi_val rs1 imm (set_reg t nextPC npc) = add_vec v (sign_extend' 64 imm).
Proof.
  intros Hv. unfold gpr_addi_val.
  rewrite -Hv. destruct (Z.eqb (uint rs1) 0); [reflexivity|].
  by rewrite (set_lookup_ne (R_bitvector_64 (gpr_of_Z (uint rs1))) nextPC t npc
                ltac:(reg_ne)).
Qed.

(* ====================================================================== *)
(** ** 5. THE WHOLE STEP AT THE MIRROR, WITH ITS POST-STATE SPELLED OUT

    [WkStepPeel] §5g assembles a walking step's mirror run out of ONE walk
    member and leaves its post-state existential — enough for the family, and
    NOT enough for the ghost side, which has to know which registers moved.
    Here is the same assembly at the ADDI, with every intermediate state
    named: the walk's own post-state [sgx] (which the exports describe), then
    the [nextPC] pre-write and the destination write ([addi_sx]), the retire
    postlude (§3's [ts_post]: PC tick + the conditional [minstret] bump), and
    the clock tick's three cells.

    The leaf's continuation rewrites the RULE's [exec_stale] equation against
    this one — [exec_stale] is a function — and thereby learns [wm_regs σ']
    as a concrete [set_reg] chain. *)

Definition addi_sx (sg : mstate) (va : SailStdpp.Values.mword 64)
    (rs1 rd : mword 5) (imm : mword 12) : mstate :=
  set_reg (set_reg sg nextPC (add_vec_int va 4))
    (R_bitvector_64 (gpr_of_Z (uint rd)))
    (regval_into_reg
       (gpr_addi_val rs1 imm (set_reg sg nextPC (add_vec_int va 4)))).

Definition addi_fin (sg : mstate) (va : SailStdpp.Values.mword 64)
    (rs1 rd : mword 5) (imm : mword 12) (tick : bool)
    (c t p : SailStdpp.Values.mword 64) : mstate :=
  if tick
  then set_reg (set_reg (set_reg (ts_post (addi_sx sg va rs1 rd imm)) mcycle c)
                  mtime t) mip p
  else ts_post (addi_sx sg va rs1 rd imm).

(** The [wmi] register transport, at the FLAT state. *)
Lemma reg_at_wmi (σ : wmstate) (b : bool) (r : register) :
  register_beq r (R_bool minstret_increment) = false ->
  register_lookup r (sregs (wflat_st (wmi σ b))) = register_lookup r (wm_regs σ).
Proof.
  intros Hne. rewrite wflat_st_regs. exact (register_lookup_wmi σ b r Hne).
Qed.

Lemma exec_stale_step_addi
    (σ : wmstate) (la : Arch.pa) (va pa : SailStdpp.Values.mword 64)
    (w : SailStdpp.Values.mword 32) (rs1 rd : mword 5) (imm : mword 12)
    (bmi tick : bool) (u : bv (8 * 8)%N) (sgx : mstate) (esx : list weff) :
  acc_wf la 8 -> acc_wf pa 4 -> racc_disj la 8 pa 4 ->
  register_lookup cur_privilege (wm_regs σ) = Supervisor ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  register_lookup PC (wm_regs σ) = va ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  uint rd <> 0 ->
  exec_eff (should_inc_minstret Supervisor) (wflat_st σ)
    = Some (bmi, wflat_st σ, []) ->
  exec_eff (dispatchInterrupt Supervisor) (wflat_st (wmi σ bmi))
    = Some (None, wflat_st (wmi σ bmi), []) ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  (forall t : mstate,
     (forall r : register, register_beq r tlb = false ->
        register_lookup r t.(sregs) = register_lookup r (wm_regs (wmi σ bmi))) ->
     exec_eff (ext_decode w) t
       = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), t, [])) ->
  exec_stale la 8 u (translateAddr (Virtaddr va) (InstructionFetch tt))
    (wflat_st (wmi σ bmi))
    = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgx, esx) ->
  exec_eff (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
              false false false) sgx
    = Some (Ok w, sgx, [WEread wak_plain pa 4]) ->
  (forall r : register, register_beq r tlb = false ->
     register_lookup r sgx.(sregs) = register_lookup r (wm_regs (wmi σ bmi))) ->
  exists c t p : SailStdpp.Values.mword 64,
    exec_stale la 8 u (riscv_step tick) (wflat_st σ)
      = Some (tt, addi_fin sgx va rs1 rd imm tick c t p,
              (esx ++ [WEread wak_plain pa 4])%list).
Proof.
  intros Hacc Haccp Hdisj Hpriv Hhart Hpc Help Hrd Hsi Hdisp Hval HnotRVC
         Hdec Htr Hmr Hrg.
  assert (HpcA : register_lookup PC (sregs (wflat_st (wmi σ bmi))) = va)
    by (rewrite (reg_at_wmi σ bmi PC ltac:(vm_compute; reflexivity)); exact Hpc).
  assert (HprivA : register_lookup cur_privilege
            (sregs (wflat_st (wmi σ bmi))) = Supervisor)
    by (rewrite (reg_at_wmi σ bmi cur_privilege ltac:(vm_compute; reflexivity));
        exact Hpriv).
  assert (HhartA : register_lookup hart_state
            (sregs (wflat_st (wmi σ bmi))) = HART_ACTIVE tt)
    by (rewrite (reg_at_wmi σ bmi hart_state ltac:(vm_compute; reflexivity));
        exact Hhart).
  assert (Hpriv0 : register_lookup cur_privilege (sregs (wflat_st σ)) = Supervisor)
    by (rewrite wflat_st_regs; exact Hpriv).
  (* the fetch: the walk member, extended by the text read *)
  pose proof (exec_stale_fetch_S la u va pa w (wflat_st (wmi σ bmi)) sgx esx
                Hacc Haccp Hdisj HpcA Hval HnotRVC Htr Hmr) as Hf.
  (* the post-fetch remainder, at the walk's post-state *)
  assert (Helpx : eq_vec (register_lookup elp (sregs sgx))
                    (landing_pad_bits_backwards LP_EXPECTED) = false).
  { rewrite (Hrg elp ltac:(vm_compute; reflexivity))
            (register_lookup_wmi σ bmi elp ltac:(vm_compute; reflexivity)).
    exact Help. }
  assert (HpcX : register_lookup PC (sregs sgx) = va).
  { rewrite (Hrg PC ltac:(vm_compute; reflexivity))
            (register_lookup_wmi σ bmi PC ltac:(vm_compute; reflexivity)).
    exact Hpc. }
  pose proof (exec_eff_execute_ITYPE_ADDI_gpr rs1 rd imm
                (set_reg sgx nextPC (add_vec_int va 4))) as Hex.
  replace (Z.eqb (uint rd) 0) with false in Hex
    by (symmetry; apply Z.eqb_neq; exact Hrd).
  pose proof (exec_eff_rha_after_fetch_base sgx (addi_sx sgx va rs1 rd imm) w
                (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) va RETIRE_SUCCESS []
                (Hdec sgx Hrg) Helpx HpcX Hex I) as Hrha1.
  pose proof (exec_stale_run_hart_active la u (wflat_st (wmi σ bmi)) sgx
                (addi_sx sgx va rs1 rd imm) (F_Base w)
                (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w))
                (esx ++ [WEread wak_plain pa 4])%list []
                Hacc HprivA Hdisp Hf Hrha1 (trace_off_win_nil la 8)) as Hrha.
  rewrite app_nil_r in Hrha.
  (* the retire postlude *)
  assert (HhartX : register_lookup hart_state
            (sregs (addi_sx sgx va rs1 rd imm)) = HART_ACTIVE tt).
  { unfold addi_sx.
    rewrite (set_lookup_ne hart_state (R_bitvector_64 (gpr_of_Z (uint rd)))
               _ _ ltac:(reg_ne)).
    rewrite (set_lookup_ne hart_state nextPC _ _ ltac:(vm_compute; reflexivity)).
    rewrite (Hrg hart_state ltac:(vm_compute; reflexivity))
            (register_lookup_wmi σ bmi hart_state ltac:(vm_compute; reflexivity)).
    exact Hhart. }
  pose proof (exec_eff_ts_after_rha_retire_at (addi_sx sgx va rs1 rd imm)
                (zero_extend' 32 w) HhartX) as Hts.
  destruct tick.
  - destruct (exec_eff_tick_clock (ts_post (addi_sx sgx va rs1 rd imm)))
      as (c & t & p & Htk).
    exists c, t, p.
    pose proof (exec_stale_riscv_step la u true (wflat_st σ)
                  (addi_sx sgx va rs1 rd imm)
                  (ts_post (addi_sx sgx va rs1 rd imm))
                  (addi_fin sgx va rs1 rd imm true c t p) bmi false
                  (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w))
                  (esx ++ [WEread wak_plain pa 4])%list [] []
                  Hacc Hpriv0 Hsi HhartA Hrha Hts (trace_off_win_nil la 8)
                  Htk (trace_off_win_nil la 8)) as Hstep.
    rewrite !app_nil_r in Hstep. exact Hstep.
  - exists (zeros' 64), (zeros' 64), (zeros' 64).
    pose proof (exec_stale_riscv_step la u false (wflat_st σ)
                  (addi_sx sgx va rs1 rd imm)
                  (ts_post (addi_sx sgx va rs1 rd imm))
                  (ts_post (addi_sx sgx va rs1 rd imm)) bmi false
                  (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w))
                  (esx ++ [WEread wak_plain pa 4])%list [] []
                  Hacc Hpriv0 Hsi HhartA Hrha Hts (trace_off_win_nil la 8)
                  (exec_eff_returnm tt (ts_post (addi_sx sgx va rs1 rd imm)))
                  (trace_off_win_nil la 8)) as Hstep.
    rewrite !app_nil_r in Hstep. exact Hstep.
Qed.

(* ====================================================================== *)
(** ** 6. THE SITE PREDICATE AND ITS CERTIFICATE

    [wp_wwalk_step] fixes [(la, Φ, P)] BEFORE its σ-callback, so the leaf's
    site predicate is stated over the PARAMETERS [p2 p1 lw] — the callback
    pins the fupd's minted values onto them with [pt_slot_mem_inj].  The
    [region], by contrast, is minted and NOT σ-recoverable (nothing exports
    the [matching_pma_region] equation outside a [wrun] premise), so it is
    existentially quantified here and destructed by the certificate. *)

Lemma pt_slot_mem_inj (sg : mstate) (a : Arch.pa)
    (w1 w2 : SailStdpp.Values.mword 64) :
  pt_slot_mem sg a w1 -> pt_slot_mem sg a w2 -> w1 = w2.
Proof.
  intros [H1 _] [H2 _]. apply (bv_eq_of_bytes (n := 8%N)). intros j Hj.
  pose proof (H1 j Hj) as E1. pose proof (H2 j Hj) as E2.
  rewrite E1 in E2. apply bv_eq. injection E2 as E2. exact E2.
Qed.

Definition wsite_addi (tid : option nat) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : SailStdpp.Values.mword 64)
    (w : SailStdpp.Values.mword 32) (σ : wmstate) : Prop :=
  exists region : PMA_Region,
    forall tick : bool,
      wwalk_site tid root_ppn va pa p2 p1 w0 lw region w σ tick.

Lemma wwalk_cert_addi (cid : nat) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : SailStdpp.Values.mword 64)
    (w : SailStdpp.Values.mword 32) :
  wwalk_cert cid va
    (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0))
    (wwalk_filter w0 lw)
    (wsite_addi (Some cid) root_ppn va pa p2 p1 w0 lw w)
    (fun _ _ => True).
Proof.
  intros σ tick Hpc Hacc Hpin (region & Hsite).
  exact (wp_wwalk_step_cert_of_peel cid root_ppn va pa p2 p1 w0 lw region w
           (fun σ0 : wmstate =>
              forall t : bool,
                wwalk_site (Some cid) root_ppn va pa p2 p1 w0 lw region w σ0 t)
           (fun _ _ => True)
           (fun σ0 t H => H t)
           (fun _ _ _ _ _ _ _ => I)
           σ tick Hpc Hacc Hpin Hsite).
Qed.

(** The rule's fourth pure output, from the same bundle. *)
Lemma wsite_addi_adm_filter (cid : nat) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : SailStdpp.Values.mword 64)
    (w : SailStdpp.Values.mword 32) (σ : wmstate) :
  register_lookup PC (wm_regs σ) = va ->
  wsite_addi (Some cid) root_ppn va pa p2 p1 w0 lw w σ ->
  wadm_filter σ wak_plain
    (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0))
    8 (wwalk_filter w0 lw).
Proof.
  intros Hpc (region & Hsite).
  exact (wwalk_site_adm_filter cid root_ppn va pa p2 p1 w0 lw region w σ false
           Hpc (Hsite false)).
Qed.

(** *** The trace-shape corollaries the continuation and the reducibility
    witness need: [tstale_id] (§2) on the walk's six shapes, and the log
    projection ([WkWalkRule] §4) on the same six with the TEXT READ appended
    — the shape the whole step's trace really has. *)

Lemma tstale_id_walk_ro (la a2 a1 : Arch.pa) (pa : SailStdpp.Values.mword 64)
    (esx : list weff) :
  (esx = [] \/
   esx = [WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain la 8] \/
   esx = [WEread wak_excl la 8] \/
   esx = [WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain la 8;
          WEread wak_excl la 8]) ->
  tstale_id la 8 (esx ++ [WEread wak_plain pa 4]).
Proof. intros [->|[->|[-> | ->]]]; exact I. Qed.

Lemma tstale_id_walk_wb (la a2 a1 : Arch.pa) (pa : SailStdpp.Values.mword 64)
    (lw' : SailStdpp.Values.mword 64) (wtr : bool) (esx : list weff) :
  racc_disj la 8 pa 4 -> acc_wf pa 4 ->
  esx = (if wtr
         then [WEread wak_plain a2 8; WEread wak_plain a1 8;
               WEread wak_plain la 8; WEread wak_excl la 8;
               WEwrite wak_excl la 8 (lw' : SailStdpp.Values.mword 64)]
         else [WEread wak_excl la 8;
               WEwrite wak_excl la 8 (lw' : SailStdpp.Values.mword 64)]) ->
  tstale_id la 8 (esx ++ [WEread wak_plain pa 4]).
Proof.
  intros Hdisj Haccp ->.
  assert (Hoff : trace_off_win la 8 [WEread wak_plain pa 4]).
  { apply trace_off_win_of_all. intros ak pa0 n Hin.
    apply elem_of_list_singleton in Hin. by injection Hin as -> -> ->. }
  destruct wtr; simpl; exact Hoff.
Qed.

Lemma wtrace_msgs_walk_ro_app (tid : option nat) (rp : bool)
    (a2 a1 la : Arch.pa) (pa : SailStdpp.Values.mword 64) (esx : list weff) :
  (esx = [] \/
   esx = [WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain la 8] \/
   esx = [WEread wak_excl la 8] \/
   esx = [WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain la 8;
          WEread wak_excl la 8]) ->
  wtrace_msgs tid rp (esx ++ [WEread wak_plain pa 4]) = [].
Proof. intros [->|[->|[-> | ->]]]; reflexivity. Qed.

Lemma wtrace_msgs_walk_wb_app (tid : option nat) (rp : bool)
    (a2 a1 la : Arch.pa) (pa : SailStdpp.Values.mword 64)
    (lw' : SailStdpp.Values.mword 64) (wtr : bool) (esx : list weff) :
  esx = (if wtr
         then [WEread wak_plain a2 8; WEread wak_plain a1 8;
               WEread wak_plain la 8; WEread wak_excl la 8;
               WEwrite wak_excl la 8 (lw' : SailStdpp.Values.mword 64)]
         else [WEread wak_excl la 8;
               WEwrite wak_excl la 8 (lw' : SailStdpp.Values.mword 64)]) ->
  wtrace_msgs tid rp (esx ++ [WEread wak_plain pa 4])
  = [wwrite_msg tid WCexcl (la : Arch.pa) 8 (lw' : SailStdpp.Values.mword 64)].
Proof.
  intros ->. destruct wtr; simpl;
    by rewrite (wm_class_rp_latest wak_excl rp eq_refl).
Qed.

(** The φ-stand-in's payment: with every byte of the pre-log free of foreign
    unpublished plain stores, the successor's [nv_hart] is the append lemma
    for the hart's OWN messages ([WeakGhost] §2a). *)
Lemma nv_hart_of_free (log ms : list wmsg) (c : CPU) (ws : wstate) :
  (forall a : Z, nv_free log a) ->
  (forall m : wmsg, m ∈ ms -> wm_tid m = Some (fin_to_nat c)) ->
  nv_hart (log ++ ms) c ws.
Proof.
  intros Hfree Hown.
  apply nv_hart_app_own; [intros a; exact (Hfree a c (coh ws a))|exact Hown].
Qed.

(** *** The walk member, with EVERYTHING the leaf needs about it.

    [WkWalkTails] §9c's [wwalk_member_of_exports] keeps the run, the memory
    and the registers; the capstone also needs the DEVICE (to give
    [dev_interp] back at σ') and the TRACE SHAPE (to compute §2's
    [tstale_id] and the log projection).  Same two-line case split. *)
Definition wwalk_shape (a2 a1 la : Arch.pa) (esx : list weff) : Prop :=
  (esx = [] \/
   esx = [WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain la 8] \/
   esx = [WEread wak_excl la 8] \/
   esx = [WEread wak_plain a2 8; WEread wak_plain a1 8; WEread wak_plain la 8;
          WEread wak_excl la 8])
  \/
  (exists (lw' : SailStdpp.Values.mword 64) (wtr : bool),
     esx = (if wtr
            then [WEread wak_plain a2 8; WEread wak_plain a1 8;
                  WEread wak_plain la 8; WEread wak_excl la 8;
                  WEwrite wak_excl la 8 (lw' : SailStdpp.Values.mword 64)]
            else [WEread wak_excl la 8;
                  WEwrite wak_excl la 8 (lw' : SailStdpp.Values.mword 64)])).

Lemma wwalk_member_full (tid : option nat) (σ : wmstate) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : SailStdpp.Values.mword 64) (av dv : mword 1) :
  let vpn := svpn_of va in
  let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
  let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  wwalk_exports tid σ root_ppn va pa p2 p1 w0 lw ->
  pte_ad_le (pte_set_ad w0 av dv) lw ->
  exists (sgx : mstate) (esx : list weff),
    exec_stale la 8 (pte_set_ad w0 av dv)
      (translateAddr (Virtaddr va) (InstructionFetch tt)) (wflat_st σ)
      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgx, esx) /\
    (mem sgx = wflat (wm_img σ) (wm_log σ) \/
     exists lw' : SailStdpp.Values.mword 64,
       mem sgx = write_bytes (wflat (wm_img σ) (wm_log σ)) la 8 lw') /\
    mdev sgx = wm_dev σ /\
    (forall r : register, register_beq r tlb = false ->
       register_lookup r (sregs sgx) = register_lookup r (wm_regs σ)) /\
    wwalk_shape a2 a1 la esx.
Proof.
  intros vpn a2 a1 la Hexp Hle.
  pose proof Hexp as Hexp'.
  destruct Hexp' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Harm & Hregs).
  destruct Harm as [Hro | (lw' & wtr & Hupd & Hfam)].
  - destruct (Hro av dv Hle) as (sgx & esx & Hex & Hmem & Hmdev & Hes).
    exists sgx, esx. split_and!;
      [exact Hex|left; exact Hmem|exact Hmdev
      |exact (Hregs av dv sgx esx Hle Hex)|left; exact Hes].
  - destruct (Hfam av dv Hle) as (sgx & esx & Hex & Hmem & Hmdev & Hes).
    exists sgx, esx. split_and!;
      [exact Hex|right; exists lw'; exact Hmem|exact Hmdev
      |exact (Hregs av dv sgx esx Hle Hex)|right; exists lw', wtr; exact Hes].
Qed.

Lemma tstale_id_of_shape (a2 a1 la : Arch.pa) (pa : SailStdpp.Values.mword 64)
    (esx : list weff) :
  racc_disj la 8 pa 4 -> acc_wf pa 4 ->
  wwalk_shape a2 a1 la esx ->
  tstale_id la 8 (esx ++ [WEread wak_plain pa 4]).
Proof.
  intros Hdisj Haccp [Hro | (lw' & wtr & Hes)].
  - exact (tstale_id_walk_ro la a2 a1 pa esx Hro).
  - exact (tstale_id_walk_wb la a2 a1 pa lw' wtr esx Hdisj Haccp Hes).
Qed.

(** The device does not move along the ADDI's register chain. *)
Lemma mdev_addi_fin (sg : mstate) (va : SailStdpp.Values.mword 64)
    (rs1 rd : mword 5) (imm : mword 12) (tick : bool)
    (c t p : SailStdpp.Values.mword 64) :
  mdev (addi_fin sg va rs1 rd imm tick c t p) = mdev sg.
Proof.
  unfold addi_fin, ts_post, ts_tick_pc, addi_sx.
  destruct tick;
    match goal with |- context[if ?b then _ else _] => destruct b end;
    by rewrite !mdev_set_reg.
Qed.

(** The ADDI's post-execute state, with the destination value in the shape
    the leaf's continuation names it. *)
Definition addi_sx' (sg : mstate) (va : SailStdpp.Values.mword 64)
    (rd : mword 5) (x : SailStdpp.Values.mword 64) : mstate :=
  set_reg (set_reg sg nextPC (add_vec_int va 4))
    (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg x).

(* ====================================================================== *)
(** ** 7. THE LEAF: [addi rd, rs1, imm] AT A FETCH-WALKING S-MODE PC

    The capstone.  Read the statement as [WeakLeafItype.wwp_addi_leaf] with
    the M-mode funnel replaced by [WkWalkRule.wp_wwalk_step]: the leaf owns
    the register cells the step moves and the S-mode configuration cells it
    reads, plus the page-table resources the walk consumes
    ([kmap_at] / [wtlb_res_pt]) and the kernel-text fragments the fetch reads
    at [pa]; it returns them all, with [PC] / [nextPC] / [rd] moved and the
    hart's weak state grown.

    THE σ-CALLBACK is the caller's obligation record — the facts that are
    about the STATE and cannot be resources of this leaf: the three
    [pt_slot_mem] pins that collapse the fupd's minted [p2 p1 lw] onto the
    parameters, the φ stand-in (⌜∀ a, [nv_free] (wm_log σ) a⌝) and the rule's
    vestigial PC-window pinnedness.  See the file header. *)

Section leaf.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (** The S-mode configuration cells the leaf reads and hands back
      unchanged. *)
  Definition scfg_cells (dq : dfrac)
      (mstatus0 mie0 mideleg0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddr0 : type_of_register pmpaddr_n)
      (pmar0 : type_of_register pma_regions) (elp0 : type_of_register elp)
      : iProp Σ :=
    (cur_privilege ↦ᵣ{dq} Supervisor ∗
     hart_state ↦ᵣ{dq} HART_ACTIVE tt ∗
     misa ↦ᵣ{dq} MISA_C ∗
     menvcfg ↦ᵣ{dq} MENVCFG_S ∗
     mstatus ↦ᵣ{dq} mstatus0 ∗
     htif_tohost_base ↦ᵣ{dq} None ∗
     pma_regions ↦ᵣ{dq} pmar0 ∗
     pmpcfg_n ↦ᵣ{dq} pmpcfg0 ∗
     pmpaddr_n ↦ᵣ{dq} pmpaddr0 ∗
     elp ↦ᵣ{dq} elp0 ∗
     mie ↦ᵣ{dq} mie0 ∗
     mideleg ↦ᵣ{dq} mideleg0)%I.

  (** THE CALLER'S σ-OBLIGATION RECORD. *)
  Definition wwalk_scn (root_ppn : mword 44)
      (va p2 p1 lw : SailStdpp.Values.mword 64) (σ : wmstate) : Prop :=
    pt_slot_mem (wflat_st σ)
      (u_pte_addr root_ppn (subrange_vec_dec (svpn_of va) 26 18)) p2 /\
    pt_slot_mem (wflat_st σ)
      (u_pte_addr (u_next_base p2) (subrange_vec_dec (svpn_of va) 17 9)) p1 /\
    pt_slot_mem (wflat_st σ)
      (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0)) lw /\
    (forall a : Z, nv_free (wm_log σ) a) /\
    (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr va j)).

  Lemma wwp_walk_addi
      (root_ppn : mword 44) (T_kpt : nat)
      (va pa : SailStdpp.Values.mword 64) (ppn : mword 44) (kpc : kperm)
      (p2 p1 lw : SailStdpp.Values.mword 64)
      (imm : mword 12) (rs1 rd : mword 5) (w : SailStdpp.Values.mword 32)
      (m : regfile) (ws : wstate) (bs : _) (dq : dfrac)
      (npc0 : SailStdpp.Values.mword 64) (mi0 : bool)
      (mst0 mc0 mt0 mp0 : SailStdpp.Values.mword 64)
      (mstatus0 mie0 mideleg0 : SailStdpp.Values.mword 64)
      (pmpcfg0 : type_of_register pmpcfg_n)
      (pmpaddr0 : type_of_register pmpaddr_n)
      (pmar0 : type_of_register pma_regions) (elp0 : type_of_register elp) :
    gen_id = 0%nat ->
    uint rd <> 0 ->
    (* ---- the decode, in the σ-free reference-state form ---- *)
    goodb0 D_s (ext_decode w) dstateS = true ->
    exec (ext_decode w) dstateS
      = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), dstateS) ->
    (* ---- the page-table geometry ---- *)
    (forall (a d : mword 1) (mxr do_sum : bool),
       wpte_check_ok (InstructionFetch tt) Supervisor mxr do_sum
         (pte_set_ad (mk_pte ppn (kperm_flags kpc)) a d)) ->
    (forall a d : mword 1, wpte_valid (pte_set_ad (mk_pte ppn (kperm_flags kpc)) a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
         (Z.sub pagesize_bits 1) 0)) = pa ->
    acc_wf va 4 ->
    acc_wf (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0)) 8 ->
    acc_wf pa 4 ->
    racc_disj (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0))
      8 pa 4 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    is_aligned_paddr (Physaddr pa) 4 = true ->
    addr_is_ram pa ->
    addr_is_ram (pa_add pa 3) ->
    (forall j : nat, (j < 4)%nat -> pa_z (pa_add pa j) <> 0) ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* ---- the configuration values ---- *)
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    and_vec mie0 (not_vec mideleg0) = zeros' 64 ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    pma_allows_all pmar0 ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr0 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr0 0) * 4)%Z ->
    (T_kpt <= w_vrNew ws)%nat ->
    (* ---- the resources ---- *)
    kmap_at (svpn_of va) ppn kpc -∗
    wtlb_res_pt root_ppn T_kpt -∗
    PC ↦ᵣ va -∗
    nextPC ↦ᵣ npc0 -∗
    gpr_file m -∗
    (R_bool minstret_increment) ↦ᵣ mi0 -∗
    minstret ↦ᵣ mst0 -∗
    mcycle ↦ᵣ mc0 -∗
    mtime ↦ᵣ mt0 -∗
    mip ↦ᵣ mp0 -∗
    scfg_cells dq mstatus0 mie0 mideleg0 pmpcfg0 pmpaddr0 pmar0 elp0 -∗
    wkernel_text bs -∗
    ⌜forall j : nat, (j < 4)%nat -> bs !! pa_add pa j = Some (nth_byte w j)⌝ -∗
    hart_ws cpu_id ws -∗
    (∀ σ : wmstate,
       wmstate_interp σ ={⊤}=∗ ⌜wwalk_scn root_ppn va p2 p1 lw σ⌝ ∗
                               wmstate_interp σ) -∗
    (∀ ws' : wstate,
       ⌜ws_le ws ws'⌝ -∗
       (PC ↦ᵣ (add_vec_int va 4) ∗
        nextPC ↦ᵣ (add_vec_int va 4) ∗
        gpr_file (<[Regidx rd :=
                    regval_into_reg (add_vec (m !!! Regidx rs1)
                                       (sign_extend' 64 imm))]> m) ∗
        (∃ b : bool, (R_bool minstret_increment) ↦ᵣ b) ∗
        (∃ v : SailStdpp.Values.mword 64, minstret ↦ᵣ v) ∗
        (∃ v : SailStdpp.Values.mword 64, mcycle ↦ᵣ v) ∗
        (∃ v : SailStdpp.Values.mword 64, mtime ↦ᵣ v) ∗
        (∃ v : SailStdpp.Values.mword 64, mip ↦ᵣ v) ∗
        wtlb_res_pt root_ppn T_kpt ∗
        scfg_cells dq mstatus0 mie0 mideleg0 pmpcfg0 pmpaddr0 pmar0 elp0) -∗
       hart_ws cpu_id ws' -∗
       WWP Loop) -∗
    WWP Loop.
  Proof.
    intros Hgid Hrd Hgood Hdecd Hchk Hval Hcanon Hid4k Haccva Haccla
           Haccpa Hdisj Halv Halp Hram Hram3 HW0 HnotRVC HSXL HSIE Hand0 Help0
           Hall HA Hord HX Hcov HT.
    iIntros "Hkmap Hres Hpc Hnpc Hgf Hmi Hmst Hmc Hmt Hmip Hcfg #Htext %Hbs
             Hhws Hcb Hcont".
    iDestruct "Hcfg" as "(Hpriv & Hhart & Hmisa & Hmenv & Hmstatus & Hhtif &
                          Hpma & Hpmpc & Hpmpa & Help & Hmie & Hmdl)".
    iApply (wp_wwalk_step va
              (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0))
              (wwalk_filter (mk_pte ppn (kperm_flags kpc)) lw)
              (wsite_addi (Some (fin_to_nat cpu_id)) root_ppn va pa p2 p1
                 (mk_pte ppn (kperm_flags kpc)) lw w)
              (fun _ _ => True) Hgid Haccva Haccla
              (wwalk_cert_addi (fin_to_nat cpu_id) root_ppn va pa p2 p1
                 (mk_pte ppn (kperm_flags kpc)) lw w)).
    iIntros (σ) "Hσ".
    (* ---- the caller's scenario, at σ ---- *)
    iMod ("Hcb" $! σ with "Hσ") as "(%Hscn & Hσ)".
    destruct Hscn as (Hs2 & Hs1 & Hs0 & Hnvfree & Hpinva).
    iDestruct "Hσ" as "(%Hbnd & %Hnvh & %Hwf & Hreg & Hdev & Hlog & Hlat & Hwsa)".
    (* ---- every register the step reads ---- *)
    iDestruct (reg_valid    with "Hreg Hpc")       as %Lpc.
    iDestruct (reg_valid    with "Hreg Hmi")       as %Lmi.
    iDestruct (reg_valid_dq with "Hreg Hpriv")     as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hhart")     as %Lhart.
    iDestruct (reg_valid_dq with "Hreg Hmisa")     as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmenv")     as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hmstatus")  as %Lmstatus.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hpmpc")     as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa")     as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Help")      as %Lelp.
    iDestruct (reg_valid_dq with "Hreg Hmie")      as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl")      as %Lmdl.
    iDestruct (hart_ws_agree cpu_id (wm_ws σ) ws with "Hwsa Hhws") as %Hwseq.
    (* ---- the source operand, off the register file ---- *)
    iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hgf") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 _ (wflat_st σ) with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hgf".
    (* ---- the text window ---- *)
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               wflat (wm_img σ) (wm_log σ) !! (pa_add pa j)
               = Some (nth_byte w j)⌝)%I as %Hbytes.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (wkernel_text_flat σ bs (pa_add pa j) (nth_byte w j) Hwf
                   (Hbs j ltac:(lia)) with "Hlat Htext") as %[Hf _].
      by iPureIntro. }
    iAssert (⌜forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pa j)⌝)%I
      as %Hpinpa.
    { iApply (wkernel_text_pinned σ bs pa 4 Haccpa _ Hwf with "Hlat Htext").
      Unshelve. intros j Hj. exists (nth_byte w j). exact (Hbs j Hj). }
    (* ---- the fupd's register-shaped premises, at σ ---- *)
    assert (HE : (↑wkptN : coPset) ⊆ ⊤) by set_solver.
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus (wm_regs σ)) = 'b"10")
      by (rewrite Lmstatus; exact HSXL).
    assert (Lall : pma_allows_all (register_lookup pma_regions (wm_regs σ)))
      by (rewrite Lpma; exact Hall).
    assert (LA : pmpAddrMatchType_encdec_backwards
                   (_get_Pmpcfg_ent_A
                      (vec_access_dec (register_lookup pmpcfg_n (wm_regs σ)) 0)) = TOR)
      by (rewrite Lpmpc; exact HA).
    assert (Lord : zopz0zKzJ_u (zeros' 64)
                     (vec_access_dec (register_lookup pmpaddr_n (wm_regs σ)) 0) = false)
      by (rewrite Lpmpa; exact Hord).
    assert (LX : eq_vec (_get_Pmpcfg_ent_X
                   (vec_access_dec (register_lookup pmpcfg_n (wm_regs σ)) 0))
                   ('b"1") = true)
      by (rewrite Lpmpc; exact HX).
    assert (Lcov : (ram_base + ram_size
                    <= uint (vec_access_dec
                               (register_lookup pmpaddr_n (wm_regs σ)) 0) * 4)%Z)
      by (rewrite Lpmpa; exact Hcov).
    assert (LT : (T_kpt <= w_vrNew (wm_ws σ))%nat) by (rewrite -Hwseq; exact HT).
    assert (Heff : forall bf : bool,
              exec_eff (effectivePrivilege (InstructionFetch tt)
                          (register_lookup mstatus (wm_regs σ)) Supervisor)
                (set_reg (wflat_st σ) (R_bool minstret_increment) bf)
              = Some (Supervisor,
                      set_reg (wflat_st σ) (R_bool minstret_increment) bf, []))
      by (intros bf; apply exec_eff_effectivePrivilege_fetch).
    assert (Hss : forall bf : bool,
              exec_eff (is_shadow_stack_access (InstructionFetch tt))
                (set_reg (wflat_st σ) (R_bool minstret_increment) bf)
              = Some (false,
                      set_reg (wflat_st σ) (R_bool minstret_increment) bf, []))
      by (intros bf; apply exec_eff_is_shadow_stack_fetch).
    (* ---- THE FUPD ---- *)
    iMod (wkpt_fetch_peel_at root_ppn T_kpt (Some (fin_to_nat cpu_id)) va pa ppn
            kpc σ ⊤ w HE Hchk Hval Hcanon Hid4k Hwf Lmisa Lmenv Lhtif Lpriv
            LSXL Heff Hss Lall LT Lpc Halv Halp Hram Hram3 Haccpa HW0 Hpinpa
            Hbytes LA Lord LX Lcov with "Hkmap Hreg Hlog Hlat Hres")
      as (p2' p1' lw' region)
         "(%Hvar & %Hslots & %Hpins & %Hdj & %Hcoll & %Hnvf8 & %Hexpb &
           %Hgatesb & %Hexecp & Hreg & Hwand & Harm)".
    (* ---- the minted slot words collapse onto the parameters ---- *)
    destruct Hslots as (Hs2' & Hs1' & Hs0').
    assert (Hp2 : p2' = p2) by exact (pt_slot_mem_inj _ _ _ _ Hs2' Hs2).
    subst p2'.
    assert (Hp1 : p1' = p1) by exact (pt_slot_mem_inj _ _ _ _ Hs1' Hs1).
    subst p1'.
    assert (Hlw : lw' = lw) by exact (pt_slot_mem_inj _ _ _ _ Hs0' Hs0).
    subst lw'.
    (* ================= THE SITE ================= *)
    assert (Hgates : wfgate_regs (wm_regs σ) pa).
    { rewrite /wfgate_regs Lpmpc Lpmpa Lpma Lhtif Lpriv.
      split_and!; [exact Hram|exact Hram3|exact HA|exact Hord|exact HX
                  |exact Hcov|exact Hall|reflexivity|reflexivity]. }
    assert (Hdecbr : forall t : mstate,
              (forall r : register, register_beq r tlb = false ->
                 register_beq r (R_bool minstret_increment) = false ->
                 register_lookup r t.(sregs) = register_lookup r (wm_regs σ)) ->
              exec_eff (ext_decode w) t
                = Some (ITYPE (imm, Regidx rs1, Regidx rd, ADDI), t, [])).
    { intros t Hag.
      refine (exec_eff_decode_bridge D_s (ext_decode w) dstateS t _ _ Hgood Hdecd).
      apply agree_s.
      - rewrite (Hag cur_privilege ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)). exact Lpriv.
      - rewrite (Hag menvcfg ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)). exact Lmenv.
      - rewrite (Hag misa ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity)). exact Lmisa. }
    assert (Hinstr : forall b : bool,
              winstr_site (wmi σ b) w (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
                (F_gpr rd)).
    { intros b. apply (winstr_site_wmi σ b w _ (F_gpr rd) Hdecbr).
      - rewrite Lelp. exact Help0.
      - exact (wexec_regonly_addi rs1 rd imm Hrd).
      - exact (F_gpr_hart_state rd).
      - exact Lhart. }
    assert (Hfsite : forall b : bool,
              wfetch_site (Some (fin_to_nat cpu_id)) (wmi σ b) root_ppn va pa
                p2 p1 (mk_pte ppn (kperm_flags kpc)) lw w).
    { intros b.
      exact (wfetch_site_wmi (Some (fin_to_nat cpu_id)) σ root_ppn va pa p2 p1
               (mk_pte ppn (kperm_flags kpc)) lw w b (Hexpb b) Lpc Halv Halp
               HnotRVC Hgates Hdisj Haccpa HW0 Hpinpa Hbytes). }
    assert (Hdisp : forall b : bool,
              exec_eff (dispatchInterrupt Supervisor) (wflat_st (wmi σ b))
                = Some (None, wflat_st (wmi σ b), [])).
    { intros b. apply exec_eff_dispatchInterrupt_supervisor_none.
      - rewrite (reg_at_wmi σ b misa ltac:(vm_compute; reflexivity)) Lmisa.
        vm_compute; reflexivity.
      - rewrite (reg_at_wmi σ b mstatus ltac:(vm_compute; reflexivity)) Lmstatus.
        exact HSIE.
      - rewrite (reg_at_wmi σ b mie ltac:(vm_compute; reflexivity)) Lmie
                (reg_at_wmi σ b mideleg ltac:(vm_compute; reflexivity)) Lmdl.
        exact Hand0. }
    assert (Htot : forall s : mstate,
              exists t : mstate, exec_eff (tick_clock tt) s = Some (tt, t, [])).
    { intros s. destruct (exec_eff_tick_clock s) as (c & t & p & Heq).
      by eexists. }
    assert (HP : wsite_addi (Some (fin_to_nat cpu_id)) root_ppn va pa p2 p1
                   (mk_pte ppn (kperm_flags kpc)) lw w σ).
    { exists region. intros tick. rewrite /wwalk_site. split_and!.
      - exact Lpriv.
      - exact Lhart.
      - exact Hdisp.
      - intros b. split; [exact (Hexpb b)|exact (Hgatesb b)].
      - exact Halv.
      - exact HnotRVC.
      - exact Hdisj.
      - exact Haccpa.
      - exact HW0.
      - exact Hpinpa.
      - exact Hbytes.
      - exact Halp.
      - exact Hexecp.
      - exact (addr_is_ram_not_dev pa Hram).
      - intros b.
        exact (wexec_tail_of (Some (fin_to_nat cpu_id)) (wmi σ b) root_ppn va pa
                 p2 p1 (mk_pte ppn (kperm_flags kpc)) lw w _ (F_gpr rd)
                 (Hfsite b) (Hinstr b)).
      - intros b.
        exact (wstep_post_tail_of (Some (fin_to_nat cpu_id)) (wmi σ b) root_ppn
                 va pa p2 p1 (mk_pte ppn (kperm_flags kpc)) lw w _ (F_gpr rd)
                 (Hfsite b) (Hinstr b) (Hdisp b)).
      - exact (wstep_tick_tail_of_tick (Some (fin_to_nat cpu_id)) σ tick).
      - exact (wstep_family_ready_of (Some (fin_to_nat cpu_id)) σ root_ppn va pa
                 p2 p1 (mk_pte ppn (kperm_flags kpc)) lw w _ (F_gpr rd) tick
                 Hfsite Hinstr (fun _ => Htot)). }
    assert (Lelpv : eq_vec (register_lookup elp (wm_regs σ))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help0).
    (* ================= THE RULE'S σ-OUTPUTS ================= *)
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hclose".
    iSplitR; [iPureIntro; exact Lpc|].
    iSplitR; [iPureIntro; exact Hpinva|].
    iSplitR; [iPureIntro; exact HP|].
    iSplitR; [iPureIntro;
      exact (wsite_addi_adm_filter (fin_to_nat cpu_id) root_ppn va pa p2 p1
               (mk_pte ppn (kperm_flags kpc)) lw w σ Lpc HP)|].
    iSplitR.
    { iPureIntro. exists (lw : bv (8 * 8)%N). apply read_bytes_of_bytes.
      intros j Hj. rewrite -(wflat_st_mem σ). apply (proj1 Hs0). lia. }
    iSplitR.
    { (* REDUCIBILITY: the family member at the COHERENT word, transferred
         back to [exec_eff] by §2 (the patch is the identity there) and then
         to [exec]. *)
      iPureIntro.
      destruct (exec_eff_should_inc_minstret_Some Supervisor (wflat_st σ))
        as [bmi Hsi].
      destruct Hvar as (av0 & dv0 & Hlweq).
      assert (Hle0 : pte_ad_le
                (pte_set_ad (mk_pte ppn (kperm_flags kpc)) av0 dv0) lw)
        by (rewrite -Hlweq; apply pte_ad_le_refl).
      destruct (wwalk_member_full (Some (fin_to_nat cpu_id)) (wmi σ bmi)
                  root_ppn va pa p2 p1 (mk_pte ppn (kperm_flags kpc)) lw av0 dv0
                  (Hexpb bmi) Hle0)
        as (sgx & esx & Hexm & Hmemx & Hmdevx & Hrgx & Hshape).
      destruct (wstep_ready_at_member (Some (fin_to_nat cpu_id)) (wmi σ bmi)
                  root_ppn va pa p2 p1 (mk_pte ppn (kperm_flags kpc)) lw w
                  (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) (F_gpr rd) false
                  (Hfsite bmi) (Hinstr bmi) (fun _ => Htot)
                  (pte_set_ad (mk_pte ppn (kperm_flags kpc)) av0 dv0) sgx esx
                  Hexm Hmemx Hrgx) as [Hmr _].
      destruct (exec_stale_step_addi σ
                  (u_pte_addr (u_next_base p1)
                     (subrange_vec_dec (svpn_of va) 8 0)) va pa w rs1 rd imm
                  bmi false
                  (pte_set_ad (mk_pte ppn (kperm_flags kpc)) av0 dv0) sgx esx
                  Haccla Haccpa Hdisj Lpriv Lhart Lpc Lelpv Hrd Hsi (Hdisp bmi)
                  Halv HnotRVC (proj1 (Hinstr bmi)) Hexm Hmr Hrgx)
        as (c & t & p & Hstep).
      assert (Hid : write_bytes (mem (wflat_st σ))
                      (u_pte_addr (u_next_base p1)
                         (subrange_vec_dec (svpn_of va) 8 0)) 8
                      (pte_set_ad (mk_pte ppn (kperm_flags kpc)) av0 dv0
                       : bv (8 * 8)%N)
                    = mem (wflat_st σ)).
      { rewrite -Hlweq. apply write_bytes_id. intros j Hj.
        apply (proj1 Hs0). lia. }
      exists (addi_fin sgx va rs1 rd imm false c t p).
      apply (exec_eff_exec _ _ _ _ _
               (exec_eff_of_exec_stale_id _ 8 _ (riscv_step false) Haccla
                  (wflat_st σ) tt _ _ Hid Hstep
                  (tstale_id_of_shape _ _ _ pa esx Hdisj Haccpa Hshape))). }
    (* ================= THE CONTINUATION ================= *)
    iNext. iIntros (tick σ' u es)
      "%Hadm %HPhi %Hex %Hlatts %Hlogid %Hpost %HQ".
    destruct Hpost as (Himg' & _ & Hwsle & Hwf' & Hbnd').
    destruct (exec_eff_should_inc_minstret_Some Supervisor (wflat_st σ))
      as [bmi Hsi].
    destruct (wwalk_filter_inv (mk_pte ppn (kperm_flags kpc)) lw u HPhi)
      as (av & dv & Huw & Hle).
    (* the two ghost arms converge: one member, one message list *)
    iAssert (|==> ∃ (msgs : list wmsg) (sgx : mstate) (esx : list weff),
               ⌜exec_stale (u_pte_addr (u_next_base p1)
                              (subrange_vec_dec (svpn_of va) 8 0)) 8
                  (pte_set_ad (mk_pte ppn (kperm_flags kpc)) av dv)
                  (translateAddr (Virtaddr va) (InstructionFetch tt))
                  (wflat_st (wmi σ bmi))
                = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgx, esx)⌝ ∗
               ⌜mem sgx = wflat (wm_img σ) (wm_log σ) \/
                (exists lw' : SailStdpp.Values.mword 64,
                   mem sgx = write_bytes (wflat (wm_img σ) (wm_log σ))
                     (u_pte_addr (u_next_base p1)
                        (subrange_vec_dec (svpn_of va) 8 0)) 8 lw')⌝ ∗
               ⌜mdev sgx = wm_dev σ⌝ ∗
               ⌜forall r : register, register_beq r tlb = false ->
                  register_lookup r (sregs sgx)
                  = register_lookup r (wm_regs (wmi σ bmi))⌝ ∗
               ⌜wtrace_msgs (Some (fin_to_nat cpu_id)) (w_relp (wm_ws σ))
                  (esx ++ [WEread wak_plain pa 4])%list = msgs⌝ ∗
               ⌜forall mm : wmsg, mm ∈ msgs ->
                  wm_tid mm = Some (fin_to_nat cpu_id)⌝ ∗
               ⌜tstale_id (u_pte_addr (u_next_base p1)
                             (subrange_vec_dec (svpn_of va) 8 0)) 8
                  (esx ++ [WEread wak_plain pa 4])%list⌝ ∗
               wlog_auth (wm_log σ ++ msgs) ∗
               wlat_interp (wm_img σ) (wm_log σ ++ msgs))%I
      with "[Harm]" as ">Hbdl".
    { iDestruct "Harm" as "[(%Hro & Hlogr & Hlatr)|Hw]".
      - destruct (Hro av dv Hle bmi)
          as (sgx & esx & Hexm & Hmemx & Hmdevx & Hrgx & Hesx).
        iModIntro. iExists [], sgx, esx. rewrite app_nil_r.
        iFrame "Hlogr Hlatr". iPureIntro. split_and!.
        + exact Hexm.
        + left; exact Hmemx.
        + exact Hmdevx.
        + exact Hrgx.
        + exact (wtrace_msgs_walk_ro_app _ _ _ _ _ pa esx Hesx).
        + intros mm Hin. by apply elem_of_nil in Hin.
        + exact (tstale_id_of_shape _ _ _ pa esx Hdisj Haccpa (or_introl Hesx)).
      - iDestruct "Hw" as (lw') "(%Hupd & %Hfam & Hlogr & Hlatr)".
        destruct Hfam as (wtr & Hfam).
        destruct (Hfam av dv Hle bmi)
          as (sgx & esx & Hexm & Hmemx & Hmdevx & Hrgx & Hesx).
        iModIntro.
        iExists [wwrite_msg (Some (fin_to_nat cpu_id)) WCexcl
                   (u_pte_addr (u_next_base p1)
                      (subrange_vec_dec (svpn_of va) 8 0)) 8 lw'], sgx, esx.
        iFrame "Hlogr Hlatr". iPureIntro. split_and!.
        + exact Hexm.
        + right; exists lw'; exact Hmemx.
        + exact Hmdevx.
        + exact Hrgx.
        + exact (wtrace_msgs_walk_wb_app _ _ _ _ _ pa lw' wtr esx Hesx).
        + intros mm Hin. apply elem_of_list_singleton in Hin. by subst mm.
        + exact (tstale_id_of_shape _ _ _ pa esx Hdisj Haccpa
                   (or_intror (ex_intro _ lw' (ex_intro _ wtr Hesx)))). }
    iDestruct "Hbdl" as (msgs sgx esx)
      "(%Hexm & %Hmemx & %Hmdevx & %Hrgx & %Hmsgs & %Hown & %Htsid & Hlog & Hlat)".
    (* the text read at the member, and the whole step, concretely *)
    destruct (wstep_ready_at_member (Some (fin_to_nat cpu_id)) (wmi σ bmi)
                root_ppn va pa p2 p1 (mk_pte ppn (kperm_flags kpc)) lw w
                (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) (F_gpr rd) tick
                (Hfsite bmi) (Hinstr bmi) (fun _ => Htot)
                (pte_set_ad (mk_pte ppn (kperm_flags kpc)) av dv) sgx esx
                Hexm Hmemx Hrgx) as [Hmr _].
    destruct (exec_stale_step_addi σ
                (u_pte_addr (u_next_base p1)
                   (subrange_vec_dec (svpn_of va) 8 0)) va pa w rs1 rd imm
                bmi tick (pte_set_ad (mk_pte ppn (kperm_flags kpc)) av dv)
                sgx esx Haccla Haccpa Hdisj Lpriv Lhart Lpc Lelpv Hrd Hsi
                (Hdisp bmi) Halv HnotRVC (proj1 (Hinstr bmi)) Hexm Hmr Hrgx)
      as (c & t & p & Hstep).
    (* [exec_stale] is a function: the successor is that state *)
    rewrite Huw in Hex. rewrite Hstep in Hex.
    assert (Hfin : addi_fin sgx va rs1 rd imm tick c t p = wflat_st σ')
      by congruence.
    assert (Hes : (esx ++ [WEread wak_plain pa 4])%list = es) by congruence.
    assert (Hregs' : wm_regs σ' = sregs (addi_fin sgx va rs1 rd imm tick c t p))
      by (rewrite -(wflat_st_regs σ') -Hfin; reflexivity).
    assert (Hdev' : wm_dev σ' = wm_dev σ)
      by (rewrite -(wflat_st_dev σ') -Hfin mdev_addi_fin; exact Hmdevx).
    assert (Hlog' : wm_log σ' = (wm_log σ ++ msgs)%list)
      by (rewrite Hlogid -Hes Hmsgs; reflexivity).
    (* ---- the destination value, at the member's registers ---- *)
    assert (Hav : gpr_addi_val rs1 imm (set_reg sgx nextPC (add_vec_int va 4))
                  = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)).
    { apply gpr_addi_val_off. etransitivity; [|exact Hrv].
      destruct (Z.eqb (uint rs1) 0); [reflexivity|].
      rewrite (Hrgx (R_bitvector_64 (gpr_of_Z (uint rs1))) eq_refl).
      exact (register_lookup_wmi σ bmi (R_bitvector_64 (gpr_of_Z (uint rs1)))
               ltac:(reg_ne)). }
    assert (Hsx : addi_sx sgx va rs1 rd imm
                  = addi_sx' sgx va rd
                      (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
      by (unfold addi_sx, addi_sx'; by rewrite Hav).
    assert (Hmi_x : register_lookup (R_bool minstret_increment)
                      (sregs (addi_sx sgx va rs1 rd imm)) = bmi).
    { unfold addi_sx.
      rewrite (set_lookup_ne (R_bool minstret_increment)
                 (R_bitvector_64 (gpr_of_Z (uint rd))) _ _ ltac:(reg_ne)).
      rewrite (set_lookup_ne (R_bool minstret_increment) nextPC _ _
                 ltac:(vm_compute; reflexivity)).
      rewrite (Hrgx (R_bool minstret_increment)
                 ltac:(vm_compute; reflexivity)).
      apply register_lookup_set. }
    assert (Hnpc_x : register_lookup nextPC
                       (sregs (addi_sx sgx va rs1 rd imm)) = add_vec_int va 4).
    { unfold addi_sx.
      rewrite (set_lookup_ne nextPC (R_bitvector_64 (gpr_of_Z (uint rd)))
                 _ _ ltac:(reg_ne)).
      rewrite sregs_set_reg. apply register_lookup_set. }
    assert (Hfin_eq : addi_fin sgx va rs1 rd imm tick c t p
      = (let sx := addi_sx' sgx va rd
                     (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) in
         let s1 := set_reg sx PC (add_vec_int va 4) in
         let s2 := if bmi
                   then set_reg s1 minstret
                          (add_vec_int (register_lookup minstret (sregs s1)) 1)
                   else s1 in
         if tick
         then set_reg (set_reg (set_reg s2 mcycle c) mtime t) mip p
         else s2)).
    { unfold addi_fin, ts_post, ts_tick_pc. rewrite Hmi_x Hnpc_x Hsx.
      reflexivity. }
    (* ---- THE REGISTER MOVES ---- *)
    iMod (reg_update _ (R_bool minstret_increment) _ bmi with "Hreg Hmi")
      as "[Hreg Hmi]".
    iMod ("Hwand" $! bmi av dv sgx esx with "[%] [%] Hreg") as "[Hreg Hres]";
      [exact Hle|exact Hexm|].
    iAssert (|==> reg_interp (sregs (addi_fin sgx va rs1 rd imm tick c t p)) ∗
                  PC ↦ᵣ (add_vec_int va 4) ∗
                  nextPC ↦ᵣ (add_vec_int va 4) ∗
                  gpr_file (<[Regidx rd :=
                              regval_into_reg (add_vec (m !!! Regidx rs1)
                                                 (sign_extend' 64 imm))]> m) ∗
                  (∃ b : bool, (R_bool minstret_increment) ↦ᵣ b) ∗
                  (∃ v : SailStdpp.Values.mword 64, minstret ↦ᵣ v) ∗
                  (∃ v : SailStdpp.Values.mword 64, mcycle ↦ᵣ v) ∗
                  (∃ v : SailStdpp.Values.mword 64, mtime ↦ᵣ v) ∗
                  (∃ v : SailStdpp.Values.mword 64, mip ↦ᵣ v))%I
      with "[Hreg Hpc Hnpc Hgf Hmi Hmst Hmc Hmt Hmip]"
      as ">(Hreg & Hpc & Hnpc & Hgf & Hmi & Hmst & Hmc & Hmt & Hmip)".
    { rewrite Hfin_eq. cbv zeta.
      iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc")
        as "[Hreg Hnpc]".
      iDestruct (gpr_file_insert_acc m (Regidx rd)
                   (regval_into_reg (add_vec (m !!! Regidx rs1)
                      (sign_extend' 64 imm))) with "Hgf") as "[Hrdc Hfins]".
      iEval (rewrite (gpr_pt_nz rd _ Hrd)) in "Hrdc".
      iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
              (regval_into_reg (add_vec (m !!! Regidx rs1)
                 (sign_extend' 64 imm))) with "Hreg Hrdc") as "[Hreg Hrdc]".
      iDestruct ("Hfins" with "[Hrdc]") as "Hgf".
      { iEval (rewrite (gpr_pt_nz rd _ Hrd)). iExact "Hrdc". }
      iMod (reg_update _ PC _ (add_vec_int va 4) with "Hreg Hpc")
        as "[Hreg Hpc]".
      destruct bmi.
      - iMod (reg_update _ minstret _
                (add_vec_int (register_lookup minstret
                   (sregs (set_reg (addi_sx' sgx va rd
                             (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)))
                             PC (add_vec_int va 4)))) 1)
                with "Hreg Hmst") as "[Hreg Hmst]".
        destruct tick.
        + iMod (reg_update _ mcycle _ c with "Hreg Hmc") as "[Hreg Hmc]".
          iMod (reg_update _ mtime _ t with "Hreg Hmt") as "[Hreg Hmt]".
          iMod (reg_update _ mip _ p with "Hreg Hmip") as "[Hreg Hmip]".
          iModIntro. iFrame "Hreg Hpc Hnpc Hgf". iSplitL "Hmi"; [by iExists true|].
          iSplitL "Hmst"; [by iExists _|]. iSplitL "Hmc"; [by iExists c|].
          iSplitL "Hmt"; [by iExists t|]. by iExists p.
        + iModIntro. iFrame "Hreg Hpc Hnpc Hgf". iSplitL "Hmi"; [by iExists true|].
          iSplitL "Hmst"; [by iExists _|]. iSplitL "Hmc"; [by iExists mc0|].
          iSplitL "Hmt"; [by iExists mt0|]. by iExists mp0.
      - destruct tick.
        + iMod (reg_update _ mcycle _ c with "Hreg Hmc") as "[Hreg Hmc]".
          iMod (reg_update _ mtime _ t with "Hreg Hmt") as "[Hreg Hmt]".
          iMod (reg_update _ mip _ p with "Hreg Hmip") as "[Hreg Hmip]".
          iModIntro. iFrame "Hreg Hpc Hnpc Hgf". iSplitL "Hmi"; [by iExists false|].
          iSplitL "Hmst"; [by iExists mst0|]. iSplitL "Hmc"; [by iExists c|].
          iSplitL "Hmt"; [by iExists t|]. by iExists p.
        + iModIntro. iFrame "Hreg Hpc Hnpc Hgf". iSplitL "Hmi"; [by iExists false|].
          iSplitL "Hmst"; [by iExists mst0|]. iSplitL "Hmc"; [by iExists mc0|].
          iSplitL "Hmt"; [by iExists mt0|]. by iExists mp0. }
    (* ---- the hart's weak state, and the interpretation at σ' ---- *)
    iMod (hart_ws_update cpu_id (wm_ws σ) ws (wm_ws σ') with "Hwsa Hhws")
      as "[Hwsa Hhws]".
    iMod "Hclose" as "_". iModIntro.
    iAssert (scfg_cells dq mstatus0 mie0 mideleg0 pmpcfg0 pmpaddr0 pmar0 elp0)
      with "[Hpriv Hhart Hmisa Hmenv Hmstatus Hhtif Hpma Hpmpc Hpmpa Help Hmie
             Hmdl]" as "Hcfg"; [rewrite /scfg_cells; iFrame|].
    iSplitR "Hcont Hpc Hnpc Hgf Hmi Hmst Hmc Hmt Hmip Hres Hcfg Hhws".
    { rewrite /wmstate_interp.
      iSplitR; [iPureIntro; exact Hbnd'|].
      iSplitR; [iPureIntro; rewrite Hlog';
                exact (nv_hart_of_free (wm_log σ) msgs cpu_id (wm_ws σ')
                         Hnvfree Hown)|].
      iSplitR; [iPureIntro; exact Hwf'|].
      rewrite Hregs'. iFrame "Hreg".
      rewrite Hdev'. iFrame "Hdev".
      rewrite Hlog' Himg'. iFrame "Hlog Hlat Hwsa". }
    iApply ("Hcont" $! (wm_ws σ') with "[%] [$Hpc $Hnpc $Hgf $Hmi $Hmst $Hmc
                                          $Hmt $Hmip $Hres $Hcfg] Hhws").
    rewrite Hwseq. exact Hwsle.
  Qed.
End leaf.

(* ====================================================================== *)
(** ** 8. Soundness checks

    The capstone's axiom set is [rv64d.plat_term_write] +
    [functional_extensionality_dep] + the reservation quartet — i.e.
    [WkWalkRule]'s set (which any statement naming [riscv_step] carries) plus
    the funext that [WeakTickEff.exec_eff_tick_clock] brings in through the
    tick-totality premise of [WkWalkTails.wstep_tick_tail_of_tick].  Nothing
    else: no [Admitted], no decode axiom (the decode is a hypothesis), no
    [wlog_wf]-style [Parameter]. *)

Print Assumptions exec_eff_dispatchInterrupt_supervisor_none.
Print Assumptions exec_eff_of_exec_stale_id.
Print Assumptions exec_eff_ts_after_rha_retire_at.
Print Assumptions wexec_regonly_addi.
Print Assumptions exec_stale_step_addi.
Print Assumptions wwalk_cert_addi.
Print Assumptions wwalk_member_full.
Print Assumptions wwp_walk_addi.
