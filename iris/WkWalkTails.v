(** * WkWalkTails.v — THE TAIL OBLIGATIONS OF A FETCH-WALKING STEP
      (walk-bridge §8, 6c: the pure half of the capstone leaf)

    [WkStepPeel] assembles the peel, the family and the Q-half of a whole
    [riscv_step tick] whose FETCH walks the page table, and leaves FOUR
    obligations open — the ones that mention the INSTRUCTION rather than the
    walk:

      [wexec_tail]         (weak side, at [wmi σ bmi]) — the post-fetch
                           remainder is an ordinary certificate;
      [wstep_post_tail]    (weak side) — [run_hart_active]'s continuation
                           inside [try_step] is one too;
      [wstep_tick_tail]    (weak side) — and so is the clock tick;
      [wstep_family_ready] (mirror side) — the text read and the whole
                           window-free tail, at a family member's post-state.

    This file discharges all four for an instruction whose EXECUTE phase is
    REGISTER-ONLY, generically in the instruction ([wexec_regonly] below), so
    that a concrete leaf — a fetch-walking [ADDI], say — instantiates rather
    than re-proves.  Everything is pure [Prop]: no Iris, no [Σ].

    ------------------------------------------------------------------
    THE THREE ROUTES, and why each one is what it is.

    (a) THE FETCH'S OUTCOME (§3, [wfetch_run_outcome]).  [WkFetchPeel] §4a's
        [wwalk_run_outcome] ONE LEVEL UP: peel ([wfetch_peel_selfcontained])
        + a family of [exec_stale] runs of the WHOLE [fetch tt] (§2's
        [exec_stale_fetch_S] at each walk member, with the text read supplied
        at the member's own post-state) + [WeakStale] §10's ⇐-bridge.  Out
        comes: the fetch returned [F_Base w], and every register but [tlb],
        every byte off the leaf window and the device are where σ left them.
        That is exactly what transports the instruction's REGISTER-shaped
        premises (decode, [elp], [PC], [hart_state]) from σ to the
        post-fetch states, which is what [wexec_tail] needs.

    (b) THE POSTLUDE (§6, [wstep_post_tail_of]).  A TOTALITY route was tried
        first and does NOT work: [ts_after_rha sv] is total and quiet only on
        the RETIRE arm — the trap arms run [handle_exception] /
        [exception_handler], the [ExecuteAs] arm is an [internal_error], and
        the retire arm's own [assert_exp (hart_is_active …)] fails at a state
        whose [hart_state] is not [HART_ACTIVE].  So [sv] has to be PINNED,
        and it is pinned the same way (a) pins the fetch's result, one level
        up again: [WkStepPeel]'s [wrha_peel] + a family of
        [exec_stale_run_hart_active] runs + the same ⇐-bridge.  The family is
        (a)'s family with §4's remainder appended, so the marginal cost is
        one [exec_stale_run_hart_active] application per member.

    (c) THE TICK (§6, [wstep_tick_tail_of]).  Here totality DOES work:
        [step_tick false] is [returnm], for which [wstep_ok] is [True], and
        [tick_clock] is total, register-only and quiet at EVERY state
        ([WeakTickEff.exec_eff_tick_clock]).  No run inversion at all.  The
        tick-[true] arm's totality is taken as an explicit premise so that
        this file's exports stay inside [WkStepPeel]'s axiom set:
        [exec_eff_tick_clock] carries [functional_extensionality_dep] and
        [WkStepPeel] does not.  [wstep_tick_tail_of_tick] discharges the
        premise for a caller that accepts it.

    ------------------------------------------------------------------
    ONE INTERFACE CHANGE THIS FILE FORCED, recorded because it is the kind
    of over-strength that is invisible until something has to discharge it:
    [WkStepPeel]'s [wstep_family_ready] used to quantify its leaf word [u]
    over ALL of [bv 64].  The landed walk layer describes a stale walk only
    at an A/D VARIANT of the invariant's word, so a run at a wild [u] that
    still returns [Ok] has nothing pinning its post-registers or its
    post-memory — while [wstep_family_fetchwalk] only ever USES the
    interface at a filter-accepted word.  The definition now carries [w0 lw]
    and guards its [∀ u] with [wwalk_filter w0 lw (λ j, nth_byte u j)]; §9d
    is the discharger, with no frame premise left.

    Design: claude-notes/design/weak-memory-walk-bridge.md §8. *)
From Stdlib Require Import ZArith Bool Lia Wf_nat.
From stdpp Require Import gmap list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import RiscvTryStep.
Require Import WeakMem WeakInterp WeakLang WeakBridge.
Require Import WeakView WeakVProp WeakFence WeakInstr WeakCert WeakEff.
Require Import WeakEffSkel WeakLeafEffCommon WeakFetchEff.
Require Import WeakRacy WeakVarCert WeakStale WeakWalkStale.
Require Import SmodePte PtAdBits Pt4kWalk CommonWalk PtTree.
Require Import SmodeCore.
Require Import WeakWalkEff.
Require Import WeakVariant WeakKpt WeakKptStale.
Require Import WkFetchPeel WkStepPeel.
Require Import WeakTickEff.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ====================================================================== *)
(** ** 1. THE TRANSPORT THIS FILE RESTS ON: an empty-trace [exec_eff] run IS
        an ordinary certificate

    [WkStepPeel] §1a proves this for the CPS PEEL; the three tails owe a
    [WeakBridge.wstep_ok], and the induction is the same one.  A run whose
    trace is EMPTY touches no RAM at all (every RAM access emits an event),
    so it moves only registers and the device fabric, and both interpreters
    move those the same way — the certificate's memory arms are never
    reached. *)

Lemma wstep_ok_of_eff_nil (tid : option nat) {X} (m : M X) :
  forall (s : wmstate) (mm : gmap Arch.pa (bv 8)) (x : X) (t : mstate),
    exec_eff m (MState (wm_regs s) mm (wm_dev s)) = Some (x, t, []) ->
    wstep_ok tid m s.
Proof.
  induction m as [y|T oc k IH]; intros s mm x t Hex; [exact I|].
  destruct oc; simpl in Hex |- *; try discriminate; try exact I;
    try (exact (IH _ s mm x t Hex)).
  - (* RegWrite *)
    exact (IH tt (wset_reg s reg regval) mm x t Hex).
  - (* MemRead: the RAM arm emits an event, so only the device arm survives *)
    destruct (dev_addr _) eqn:Hdev.
    + intros w d' Hdr. rewrite Hdr in Hex.
      exact (IH _ (wset_dev s d') mm x t Hex).
    + destruct (read_bytes _ _ _) as [w0|]; [|discriminate].
      destruct (exec_eff (k _) _) as [[[ya ta] esa]|]; discriminate.
  - (* MemWrite: likewise *)
    destruct (dev_addr _) eqn:Hdev.
    + intros d' Hdw. rewrite Hdw in Hex.
      exact (IH _ (wset_dev s d') mm x t Hex).
    + destruct (exec_eff (k _) _) as [[[ya ta] esa]|]; discriminate.
  - (* Barrier: emits an event *)
    destruct (exec_eff (k tt) _) as [[[ya ta] esa]|]; discriminate.
Qed.

(** The instance every tail below uses: the run is stated at the weak state's
    own FLAT projection, which is where the [exec_eff] library's facts about
    a register-only program live. *)
Lemma wstep_ok_of_eff_nil_flat (tid : option nat) {X} (m : M X)
    (s : wmstate) (x : X) (t : mstate) :
  exec_eff m (wflat_st s) = Some (x, t, []) -> wstep_ok tid m s.
Proof.
  intros Hex.
  exact (wstep_ok_of_eff_nil tid m s (wflat (wm_img s) (wm_log s)) x t Hex).
Qed.

(** Two list-level facts the trace assembly needs and [WkStepPeel] §5a's
    twins do not cover: a READ contributes no write, so appending one is
    invisible to [WeakStale] §10-0's write-footprint predicate. *)
Lemma wtrace_wonly_app (A : Arch.pa -> N -> Prop) (es1 es2 : list weff) :
  wtrace_wonly A es1 -> wtrace_wonly A es2 -> wtrace_wonly A (es1 ++ es2).
Proof.
  intros H1 H2 ak pa n v Hin.
  apply elem_of_app in Hin as [Hin|Hin];
    [exact (H1 ak pa n v Hin)|exact (H2 ak pa n v Hin)].
Qed.

Lemma wtrace_wonly_reads (A : Arch.pa -> N -> Prop) (ak : akinfo)
    (pa : Arch.pa) (n : N) :
  wtrace_wonly A [WEread ak pa n].
Proof.
  intros ak0 pa0 n0 v Hin. apply elem_of_list_singleton in Hin. discriminate.
Qed.

(* ====================================================================== *)
(** ** 2. THE TEXT READ, AT AN ARBITRARY STATE WITH σ's GATE REGISTERS

    [WkFetchPeel] §5's [wfetch_gates_of_regs] discharges the fetch's
    register-only gates at the states the WEAK translation run can reach.
    The FAMILY needs the same gates at the states a MIRROR run reaches — the
    [sg'] of an [exec_stale] walk member — and those are not [wrun]
    post-states, so §5's statement does not reach them.

    Both sides read the SAME five registers ([pmpcfg_n], [pmpaddr_n],
    [pma_regions], [htif_tohost_base], [cur_privilege]), none of which is
    [tlb], so the honest common premise is a fact about a REGISTER MAP —
    [wfgate_regs] — from which §2b produces the gates at ANY state carrying
    those registers, weak-side or mirror-side.  §2c then reads the text word
    there. *)

(** *** 2a. The gate registers, as a σ-level bundle. *)
Definition wfgate_regs (regs : regstate) (pa : mword 64) : Prop :=
  addr_is_ram pa /\
  addr_is_ram (pa_add pa 3) /\
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n regs) 0)) = TOR /\
  zopz0zKzJ_u (zeros' 64)
    (vec_access_dec (register_lookup pmpaddr_n regs) 0) = false /\
  eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n regs) 0))
    ('b"1") = true /\
  (ram_base + ram_size
   <= uint (vec_access_dec (register_lookup pmpaddr_n regs) 0) * 4)%Z /\
  pma_allows_all (register_lookup pma_regions regs) /\
  register_lookup htif_tohost_base regs = None /\
  register_lookup cur_privilege regs = Supervisor.

(** It is a fact about FIVE registers, so it travels along any register
    agreement that covers them — which is what the walk's [tlb]-only
    footprint gives on both sides of the bridge. *)
Lemma wfgate_regs_transport (regs regs' : regstate) (pa : mword 64) :
  wfgate_regs regs pa ->
  register_lookup pmpcfg_n regs' = register_lookup pmpcfg_n regs ->
  register_lookup pmpaddr_n regs' = register_lookup pmpaddr_n regs ->
  register_lookup pma_regions regs' = register_lookup pma_regions regs ->
  register_lookup htif_tohost_base regs' = register_lookup htif_tohost_base regs ->
  register_lookup cur_privilege regs' = register_lookup cur_privilege regs ->
  wfgate_regs regs' pa.
Proof.
  intros (Hram & Hram3 & HA & Hord & HX & Hcov & Hall & Hhtif & Hpriv)
    Hc Ha Hm Hh Hp.
  rewrite /wfgate_regs Hc Ha Hm Hh Hp.
  split_and!; assumption.
Qed.

(** The one-line transporter for a state whose registers differ from σ's
    only at [tlb] — the shape both the exports' hoisted [sregs] field and
    [wwalk_run_outcome]'s last conclusion have. *)
Lemma wfgate_regs_off_tlb (regs regs' : regstate) (pa : mword 64) :
  wfgate_regs regs pa ->
  (forall r : register, register_beq r tlb = false ->
     register_lookup r regs' = register_lookup r regs) ->
  wfgate_regs regs' pa.
Proof.
  intros Hg Hoff.
  apply (wfgate_regs_transport regs regs' pa Hg);
    [ exact (Hoff pmpcfg_n ltac:(vm_compute; reflexivity))
    | exact (Hoff pmpaddr_n ltac:(vm_compute; reflexivity))
    | exact (Hoff pma_regions ltac:(vm_compute; reflexivity))
    | exact (Hoff htif_tohost_base ltac:(vm_compute; reflexivity))
    | exact (Hoff cur_privilege ltac:(vm_compute; reflexivity)) ].
Qed.

(** *** 2b. The gates themselves, at an arbitrary state.

    [WkFetchPeel] §5b's script with the [wwalk_run_outcome] transport
    removed: what is left is exactly the register-to-gate derivation, which
    is what both sides share. *)
Lemma wfgates_at_of_regs (t : mstate) (pa : mword 64) :
  wfgate_regs (sregs t) pa ->
  exists region : PMA_Region,
    exec_eff (pmpCheck (Physaddr pa) 4 (InstructionFetch tt) Supervisor) t
      = Some (None, t, []) /\
    matching_pma_region (register_lookup pma_regions (sregs t)) (Physaddr pa) 4
      = Some region /\
    exec_eff (within_clint (Physaddr pa) 4) t = Some (false, t, []) /\
    exec_eff (within_sig (Physaddr pa) 4) t = Some (false, t, []) /\
    exec_eff (within_htif_readable (Physaddr pa) 4) t = Some (false, t, []) /\
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_executable) = true.
Proof.
  intros (Hram & Hram3 & HA & Hord & HX & Hcov & Hall & Hhtif & Hpriv).
  assert (Hacc : pma_ram_access pa 4).
  { exact (pma_access_ram pa 4 3%nat Hram Hram3
             (pma_width_ok 4 eq_refl eq_refl) eq_refl eq_refl). }
  destruct (pma_all_ram Hall pa 4 Hacc) as (region & Hmatch & Hexec & _).
  assert (Hnw : (uint pa + Z.of_nat 3 < 18446744073709551616)%Z).
  { destruct Hram as [_ Hh]. unfold ram_base, ram_size in Hh.
    change (Z.of_nat 3) with 3%Z. lia. }
  assert (Hfit : (uint pa + 4 <= ram_base + ram_size)%Z).
  { pose proof (uint_pa_add pa 3%nat Hnw) as Heq.
    destruct Hram3 as [_ Hhi3]. rewrite Heq in Hhi3.
    change (Z.of_nat 3) with 3%Z in Hhi3.
    unfold ram_base, ram_size in *. lia. }
  assert (Hrange : pmpRangeMatch
            (Z.mul (uint (zeros' 64 : SailStdpp.Values.mword 64)) 4)
            (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n (sregs t)) 0)) 4)
            (uint pa) (uint (to_bits 64 4)) = PMP_Match).
  { apply (ram_pmp_match_w pa _ 4);
      [lia | vm_compute; reflexivity | | exact Hfit | exact Hcov].
    destruct Hram as [Hlo _]. exact Hlo. }
  exists region. split_and!; [| exact Hmatch | | | | exact Hexec].
  - apply exec_eff_pmpCheck_supervisor_grant_fetch;
      [exact HA | exact Hord | exact Hrange | exact HX].
  - apply exec_eff_within_clint_false;
      [apply addr_is_ram_not_in_clint; exact Hram | lia].
  - apply exec_eff_within_sig_false;
      [apply addr_is_ram_not_in_sig; exact Hram | lia].
  - apply exec_eff_within_htif_false. exact Hhtif.
Qed.

(** *** 2c. THE TEXT READ.  [WkFetchPeel] §2b's [exec_eff_mem_read_fetch_gen]
    with its gate premises discharged by 2b — the mirror-side twin of
    [wfetch_tail_read], and the one fact a family member owes about the
    instruction word. *)
Lemma exec_eff_text_read_at (t : mstate) (pa : mword 64) (w : bv 32) :
  wfgate_regs (sregs t) pa ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     (mem t) !! (pa_add pa j) = Some (nth_byte w j)) ->
  exec_eff (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
              false false false) t
    = Some (Ok w, t, [WEread wak_plain pa 4]).
Proof.
  intros Hg Halign Hbytes.
  pose proof Hg as Hg'.
  destruct Hg' as (Hram & _ & _ & _ & _ & _ & _ & _ & Hpriv).
  destruct (wfgates_at_of_regs t pa Hg)
    as (region & Hpmp & Hmatch & Hc & Hsig & Hh & Hexec).
  exact (exec_eff_mem_read_fetch_gen Supervisor PBMT_PMA pa region w t
           Hpmp Hmatch Halign Hexec Hc Hsig Hh (addr_is_ram_not_dev pa Hram)
           Hbytes Hpriv).
Qed.

(* ====================================================================== *)
(** ** 3. THE FETCH, AT ONE FAMILY MEMBER, AND THE FETCH'S RUN OUTCOME

    §3a is the piece BOTH ⇐-bridge applications below and §7's mirror-side
    interface share: one walk member's [exec_stale] run, extended by the text
    read into a run of the whole [fetch tt].  The member's own description —
    its memory (unchanged, or the leaf slot rewritten) and its registers
    (everything but [tlb] as at [s]) — is what makes the text read available
    THERE, which is the only thing the extension needs.

    §3b then runs [WkFetchPeel] §4a's script one level up. *)

(** *** 3a. One member, extended to the whole fetch. *)
Lemma wfetch_member_run (s : wmstate) (la : Arch.pa) (va pa : mword 64)
    (w : mword 32) (u : bv (8 * 8)%N) (sgm : mstate) (esm : list weff) :
  acc_wf la 8 ->
  acc_wf pa 4 ->
  racc_disj la 8 pa 4 ->
  register_lookup PC (wm_regs s) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  wfgate_regs (wm_regs s) pa ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     wflat (wm_img s) (wm_log s) !! (pa_add pa j) = Some (nth_byte w j)) ->
  exec_stale la 8 u (translateAddr (Virtaddr va) (InstructionFetch tt))
    (wflat_st s) = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgm, esm) ->
  (mem sgm = wflat (wm_img s) (wm_log s) \/
   exists lw' : mword 64,
     mem sgm = write_bytes (wflat (wm_img s) (wm_log s)) la 8 lw') ->
  (forall r : register, register_beq r tlb = false ->
     register_lookup r (sregs sgm) = register_lookup r (wm_regs s)) ->
  exec_eff (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
              false false false) sgm
    = Some (Ok w, sgm, [WEread wak_plain pa 4]) /\
  exec_stale la 8 u (fetch tt) (wflat_st s)
    = Some (F_Base w, sgm, (esm ++ [WEread wak_plain pa 4])%list).
Proof.
  intros Hacc Haccp Hdisj Hpc Halv Halp HnotRVC Hgates Hbytes Htr Hmem Hregs.
  (* the leaf window and the text window are byte-wise apart *)
  assert (Hne : forall i j : nat, (i < 8)%nat -> (j < 4)%nat ->
            pa_add la i <> pa_add pa j).
  { intros i j Hi Hj Heq.
    apply (pa_add_neq pa la 4 8 j i Haccp Hacc Hdisj
             ltac:(change (N.to_nat 4) with 4%nat; lia)
             ltac:(change (N.to_nat 8) with 8%nat; lia)).
    by rewrite Heq. }
  (* the member holds the text word ... *)
  assert (Hbm : forall j : nat, (N.of_nat j < 4)%N ->
            (mem sgm) !! (pa_add pa j) = Some (nth_byte w j)).
  { intros j Hj.
    destruct Hmem as [Hmem | (lw' & Hmem)]; rewrite Hmem; [apply Hbytes; exact Hj|].
    rewrite write_bytes_lookup_ne; [apply Hbytes; exact Hj|].
    intros i Hi Heq. apply (Hne i j ltac:(change (N.to_nat 8) with 8%nat in Hi; lia)
                              ltac:(lia)). by rewrite Heq. }
  (* ... and σ's gate registers *)
  assert (Hgm : wfgate_regs (sregs sgm) pa)
    by exact (wfgate_regs_off_tlb (wm_regs s) (sregs sgm) pa Hgates Hregs).
  pose proof (exec_eff_text_read_at sgm pa w Hgm Halp Hbm) as Hmr.
  split; [exact Hmr|].
  exact (exec_stale_fetch_S la u va pa w (wflat_st s) sgm esm
           Hacc Haccp Hdisj Hpc Halv HnotRVC Htr Hmr).
Qed.

(* ====================================================================== *)
(** ** 4. THE TWO SITE BUNDLES

    Every remaining deliverable takes the same two premise sets, so they are
    named once.  Both are stated AT the state the fetch starts from — which
    for the capstone is [wmi σ bmi] — and travel to the post-fetch and
    mirror-member states through the [tlb]-only register footprint of the
    walk. *)

Definition wfetch_site (tid : option nat) (σ : wmstate) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (w : SailStdpp.Values.mword 32) : Prop :=
  let vpn := svpn_of va in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  register_lookup PC (wm_regs σ) = va /\
  is_aligned_vaddr (Virtaddr va) 4 = true /\
  is_aligned_paddr (Physaddr pa) 4 = true /\
  isRVC (subrange_vec_dec w 15 0) = false /\
  wwalk_exports tid σ root_ppn va pa p2 p1 w0 lw /\
  wfgate_regs (wm_regs σ) pa /\
  racc_disj la 8 pa 4 /\
  acc_wf pa 4 /\
  (forall j : nat, (j < 4)%nat -> pa_z (pa_add pa j) <> 0) /\
  (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pa j)) /\
  (forall j : nat, (N.of_nat j < 4)%N ->
     wflat (wm_img σ) (wm_log σ) !! (pa_add pa j) = Some (nth_byte w j)).

(** THE REGISTER-ONLY EXECUTE INTERFACE: "[execute i] retires successfully at
    EVERY state, touches no memory — an [exec_eff] trace is empty exactly
    when no RAM is accessed — and moves only registers [F] admits."  [F] is a
    parameter rather than a fixed 'is-a-GPR' test so the interface is not
    tied to one instruction class: an ADDI takes
    [F := λ r, register_beq r (R_bitvector_64 (gpr_of_Z (uint rd)))]. *)
Definition wexec_regonly (i : instruction) (F : register -> bool) : Prop :=
  forall s : mstate,
    exists s' : mstate,
      exec_eff (execute i) s = Some (RETIRE_SUCCESS, s', []) /\
      (forall r : register, F r = false ->
         register_lookup r s'.(sregs) = register_lookup r s.(sregs)).

(** The instruction side.  The DECODE is owed at every state whose registers
    agree with σ's off [tlb] — the weakest form that survives both the fetch
    and the mirror walk (each moves only [tlb]), and exactly what
    [WeakFetchEff] §6's [exec_eff_decode_bridge] produces from a register
    agreement.  [F hart_state = false] is the ONE thing the ladder asks of
    the execute's register footprint: the postlude's
    [assert_exp (hart_is_active …)] is where a wilder execute would break the
    step. *)
Definition winstr_site (σ : wmstate) (w : SailStdpp.Values.mword 32)
    (i : instruction) (F : register -> bool) : Prop :=
  (forall t : mstate,
     (forall r : register, register_beq r tlb = false ->
        register_lookup r t.(sregs) = register_lookup r (wm_regs σ)) ->
     exec_eff (ext_decode w) t = Some (i, t, [])) /\
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false /\
  wexec_regonly i F /\
  F hart_state = false /\
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt.

(* ====================================================================== *)
(** ** 5. THE FETCH FAMILY, AND THE FETCH'S RUN OUTCOME

    §5a packages what §3a produces at EVERY admissible leaf word: one
    [exec_stale] run of the whole [fetch tt], its trace condition [T]
    (arm-uniform: [trace_stale] on the five stale-friendly walk shapes,
    [trace_off_win] on the TLB-hit write-back), and the member's own
    description.  Both ⇐-bridge applications in this file — the fetch's (§5c)
    and [run_hart_active]'s (§6) — consume exactly this, which is why the
    three-arm case split over the absorption theorem's ghost arms is paid for
    ONCE. *)

(** *** 5a. The family, as a predicate on the trace condition. *)
Definition wfetch_fam (σ : wmstate) (la : Arch.pa) (pa : mword 64)
    (w : SailStdpp.Values.mword 32) (Φ : (nat -> bv 8) -> Prop)
    (T : list weff -> Prop) : Prop :=
  forall u : bv (8 * 8)%N, Φ (fun j : nat => nth_byte u j) ->
    exists (sgm : mstate) (esm : list weff),
      exec_stale la 8 u (fetch tt) (wflat_st σ) = Some (F_Base w, sgm, esm) /\
      T esm /\
      mdev sgm = wm_dev σ /\
      (mem sgm = wflat (wm_img σ) (wm_log σ) \/
       exists lw' : mword 64,
         mem sgm = write_bytes (wflat (wm_img σ) (wm_log σ)) la 8 lw') /\
      (forall r : register, register_beq r tlb = false ->
         register_lookup r sgm.(sregs) = register_lookup r (wm_regs σ)) /\
      (forall a : Arch.pa,
         (forall j : nat, (j < 8)%nat -> pa_add la j <> a) ->
         wtrace_wonly (fun (pa0 : Arch.pa) (n : N) =>
            forall j : nat, (j < N.to_nat n)%nat -> pa_add pa0 j <> a) esm).

(** *** 5b. THE FAMILY ITSELF — the absorption theorem's three ghost arms,
    each extended by §3a's text read.  The trace side is [WkStepPeel] §5i's:
    the read-only and MISS write-back shapes are [trace_stale], the HIT
    write-back's only read is EXCLUSIVE so its family is constant and
    [trace_off_win] holds vacuously.  The appended text read is off the
    window ([racc_disj]) and is not a WRITE, so it disturbs neither. *)
Lemma wfetch_family (tid : option nat) (σ : wmstate) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (w : SailStdpp.Values.mword 32) :
  let vpn := svpn_of va in
  let a2 := u_pte_addr root_ppn (subrange_vec_dec vpn 26 18) in
  let a1 := u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9) in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  wfetch_site tid σ root_ppn va pa p2 p1 w0 lw w ->
  wfetch_fam σ la pa w (wwalk_filter w0 lw) (trace_stale wak_plain la 8) \/
  wfetch_fam σ la pa w (wwalk_filter w0 lw) (trace_off_win la 8).
Proof.
  intros vpn a2 a1 la
    (Hpc & Halv & Halp & HnotRVC & Hexp & Hgates & Hdisj & Haccp & HW0 & Hpin
     & Hbytes).
  pose proof Hexp as Hexp'.
  destruct Hexp' as (Hvar & Hwf & Hs2 & Hs1 & Hs0 & Hpins & Hd2 & Hd1 & Hcoll
                     & Harm & Hregs).
  pose proof (pt_slot_mem_acc_wf _ _ _ Hs0) as Hacc.
  (* the one-read trace fact, shared by all three arms *)
  assert (Hrdoff : trace_off_win la 8 [WEread wak_plain pa 4]).
  { apply trace_off_win_of_all. intros ak pa0 n Hin.
    apply elem_of_list_singleton in Hin. by injection Hin as -> -> ->. }
  assert (Hwoff : forall a : Arch.pa,
            wtrace_wonly (fun (pa0 : Arch.pa) (n : N) =>
               forall j : nat, (j < N.to_nat n)%nat -> pa_add pa0 j <> a)
              [WEread wak_plain pa 4])
    by (intros a; apply wtrace_wonly_reads).
  destruct Harm as [Hro | (lw' & wtr & Hupd & Hfam)].
  - (* ---------- READ-ONLY: four stale-friendly shapes ---------- *)
    left. intros u Hu.
    destruct (wwalk_filter_inv w0 lw u Hu) as (av & dv & Hw & Hle).
    destruct (Hro av dv Hle) as (sgm & esm & Hex & Hmem & Hmdev & Hes).
    destruct (wfetch_member_run σ la va pa w (pte_set_ad w0 av dv) sgm esm
                Hacc Haccp Hdisj Hpc Halv Halp HnotRVC Hgates Hbytes Hex
                (or_introl Hmem) (Hregs av dv sgm esm Hle Hex)) as [_ Hf].
    assert (Hev : Forall (wwalk_ev_ok a2 a1 la) esm)
      by (destruct Hes as [->|[->|[-> | ->]]]; walk_evs).
    exists sgm, (esm ++ [WEread wak_plain pa 4])%list.
    rewrite Hw. split_and!.
    + exact Hf.
    + apply trace_stale_app; [| |exact Hrdoff].
      * apply (trace_stale_walk_shapes a2 a1 la lw esm Hd2 Hd1).
        destruct Hes as [->|[->|[-> | ->]]];
          [by left|by right; left|by right; right; left
          |by right; right; right; left].
      * simpl. right; left. split_and!; [reflexivity|exact Hdisj|exact I].
    + exact Hmdev.
    + left. exact Hmem.
    + exact (Hregs av dv sgm esm Hle Hex).
    + intros a Hoff. apply wtrace_wonly_app;
        [exact (wtrace_wonly_of_evs a2 a1 la esm a Hev Hoff)|apply Hwoff].
  - destruct wtr.
    + (* ---------- MISS write-back: the five-event walk ---------- *)
      left. intros u Hu.
      destruct (wwalk_filter_inv w0 lw u Hu) as (av & dv & Hw & Hle).
      destruct (Hfam av dv Hle) as (sgm & esm & Hex & Hmem & Hmdev & Hes).
      destruct (wfetch_member_run σ la va pa w (pte_set_ad w0 av dv) sgm esm
                  Hacc Haccp Hdisj Hpc Halv Halp HnotRVC Hgates Hbytes Hex
                  (or_intror (ex_intro _ lw' Hmem))
                  (Hregs av dv sgm esm Hle Hex)) as [_ Hf].
      assert (Hev : Forall (wwalk_ev_ok a2 a1 la) esm)
        by (rewrite Hes; walk_evs).
      exists sgm, (esm ++ [WEread wak_plain pa 4])%list.
      rewrite Hw. split_and!.
      * exact Hf.
      * apply trace_stale_app; [| |exact Hrdoff].
        -- apply (trace_stale_walk_shapes a2 a1 la lw' esm Hd2 Hd1).
           rewrite Hes. by right; right; right; right.
        -- simpl. right; left. split_and!; [reflexivity|exact Hdisj|exact I].
      * exact Hmdev.
      * right. exists lw'. exact Hmem.
      * exact (Hregs av dv sgm esm Hle Hex).
      * intros a Hoff. apply wtrace_wonly_app;
          [exact (wtrace_wonly_of_evs a2 a1 la esm a Hev Hoff)|apply Hwoff].
    + (* ---------- HIT write-back: the CONSTANT family ---------- *)
      right. intros u Hu.
      destruct (wwalk_filter_inv w0 lw u Hu) as (av & dv & Hw & Hle).
      destruct (Hfam av dv Hle) as (sgm & esm & Hex & Hmem & Hmdev & Hes).
      destruct (wfetch_member_run σ la va pa w (pte_set_ad w0 av dv) sgm esm
                  Hacc Haccp Hdisj Hpc Halv Halp HnotRVC Hgates Hbytes Hex
                  (or_intror (ex_intro _ lw' Hmem))
                  (Hregs av dv sgm esm Hle Hex)) as [_ Hf].
      assert (Hev : Forall (wwalk_ev_ok a2 a1 la) esm)
        by (rewrite Hes; walk_evs).
      exists sgm, (esm ++ [WEread wak_plain pa 4])%list.
      rewrite Hw. split_and!.
      * exact Hf.
      * apply trace_off_win_app; [|exact Hrdoff].
        rewrite Hes. apply trace_off_win_pinned. pinned_trace.
      * exact Hmdev.
      * right. exists lw'. exact Hmem.
      * exact (Hregs av dv sgm esm Hle Hex).
      * intros a Hoff. apply wtrace_wonly_app;
          [exact (wtrace_wonly_of_evs a2 a1 la esm a Hev Hoff)|apply Hwoff].
Qed.

(** *** 5c. THE OUTCOME OF THE WEAK FETCH RUN — DELIVERABLE (1).

    [WkFetchPeel] §4d's [wwalk_run_outcome] one level up.  The glue below is
    the part that does not depend on which of the two ⇐-bridge eliminations
    delivered the witness: [exec_stale] is a FUNCTION, so the family's own
    equation pins the result, the post-memory, the post-device, the
    post-registers and the trace, and the elimination's [latest_ts] conjunct
    then reads off at every byte the trace does not write. *)
Lemma wfetch_outcome_glue (tid : option nat) (σ s' : wmstate) (la : Arch.pa)
    (pa : mword 64) (w : SailStdpp.Values.mword 32)
    (Φ : (nat -> bv 8) -> Prop) (T : list weff -> Prop)
    (u : bv (8 * 8)%N) (r : FetchResult) (es : list weff) :
  wfetch_fam σ la pa w Φ T ->
  Φ (fun j : nat => nth_byte u j) ->
  exec_stale la 8 u (fetch tt) (wflat_st σ) = Some (r, wflat_st s', es) ->
  wlog_wf (wm_log s') ->
  (forall a : Arch.pa,
     wtrace_wonly (fun (pa0 : Arch.pa) (n : N) =>
        forall j : nat, (j < N.to_nat n)%nat -> pa_add pa0 j <> a) es ->
     latest_ts (wm_log s') (pa_z a) = latest_ts (wm_log σ) (pa_z a)) ->
  ws_le (wm_ws σ) (wm_ws s') ->
  r = F_Base w /\
  wlog_wf (wm_log s') /\
  ws_le (wm_ws σ) (wm_ws s') /\
  wm_dev s' = wm_dev σ /\
  (forall a : Arch.pa,
     (forall j : nat, (j < 8)%nat -> pa_add la j <> a) ->
     latest_ts (wm_log s') (pa_z a) = latest_ts (wm_log σ) (pa_z a)) /\
  (forall a : Arch.pa,
     (forall j : nat, (j < 8)%nat -> pa_add la j <> a) ->
     wflat (wm_img s') (wm_log s') !! a = wflat (wm_img σ) (wm_log σ) !! a) /\
  (forall r0 : register, register_beq r0 tlb = false ->
     register_lookup r0 (wm_regs s') = register_lookup r0 (wm_regs σ)).
Proof.
  intros Hfam HΦu Hexu Hwf' Hlt Hle.
  destruct (Hfam u HΦu) as (sgm & esm & Hex & _ & Hmdev & Hmem & Hrg & Hwo).
  rewrite Hex in Hexu. injection Hexu as Hx Hsg Hes.
  split_and!.
  - by rewrite -Hx.
  - exact Hwf'.
  - exact Hle.
  - rewrite -(wflat_st_dev s') -Hsg. exact Hmdev.
  - intros a Hoff. apply Hlt. rewrite -Hes. exact (Hwo a Hoff).
  - intros a Hoff. rewrite -(wflat_st_mem s') -Hsg.
    destruct Hmem as [Hmem | (lw' & Hmem)]; rewrite Hmem; [reflexivity|].
    apply write_bytes_lookup_ne. intros j Hj Heq.
    apply (Hoff j ltac:(change (N.to_nat 8) with 8%nat in Hj; lia)).
    by rewrite Heq.
  - rewrite -(wflat_st_regs s') -Hsg. exact Hrg.
Qed.

(** The peel of the whole fetch, in the CPS form [WkStepPeel]'s
    [wfetch_peel_k_at] interface asks for, from the site bundle — the gates
    come from §2's register bundle through [WkFetchPeel] §5b. *)
Lemma wfetch_peel_k_of_site (tid : option nat) (σ : wmstate)
    (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64)
    (w : SailStdpp.Values.mword 32) :
  let vpn := svpn_of va in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  wfetch_site tid σ root_ppn va pa p2 p1 w0 lw w ->
  wfetch_peel_k_at tid la (wwalk_filter w0 lw) σ /\
  wstep_ok_racy tid la 8 wak_plain (wwalk_filter w0 lw) wD_any True true
    (fetch tt) σ /\
  wadm_filter σ wak_plain la 8 (wwalk_filter w0 lw).
Proof.
  intros vpn la
    (Hpc & Halv & Halp & HnotRVC & Hexp & Hgates & Hdisj & Haccp & HW0 & Hpin
     & Hbytes).
  pose proof Hgates as Hgates'.
  destruct Hgates' as (Hram & Hram3 & HA & Hord & HX & Hcov & Hall & Hhtif
                       & Hpriv).
  destruct (wfetch_gates_of_regs tid σ root_ppn va pa p2 p1 w0 lw
              Hexp Hram Hram3 HA Hord HX Hcov Hall Hhtif Hpriv)
    as (region & Hgt & Hexecp).
  split.
  - intros K HK.
    exact (proj1 (wfetch_peel_k_selfcontained tid σ root_ppn va pa p2 p1 w0 lw
                    region w K Hpc Halv Hexp Hdisj Haccp HW0 Hpin Hbytes Hgt
                    Halp Hexecp (addr_is_ram_not_dev pa Hram) HK)).
  - exact (wfetch_peel_selfcontained tid σ root_ppn va pa p2 p1 w0 lw region w
             Hpc Halv Hexp Hdisj Haccp HW0 Hpin Hbytes Hgt Halp Hexecp
             (addr_is_ram_not_dev pa Hram)).
Qed.

Lemma wfetch_run_outcome (tid : option nat) (σ : wmstate) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (w : SailStdpp.Values.mword 32) :
  let vpn := svpn_of va in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  wfetch_site tid σ root_ppn va pa p2 p1 w0 lw w ->
  forall (r : FetchResult) (s' : wmstate),
    wrun tid (fetch tt) σ r s' ->
    r = F_Base w /\
    wlog_wf (wm_log s') /\
    ws_le (wm_ws σ) (wm_ws s') /\
    wm_dev s' = wm_dev σ /\
    (forall a : Arch.pa,
       (forall j : nat, (j < 8)%nat -> pa_add la j <> a) ->
       latest_ts (wm_log s') (pa_z a) = latest_ts (wm_log σ) (pa_z a)) /\
    (forall a : Arch.pa,
       (forall j : nat, (j < 8)%nat -> pa_add la j <> a) ->
       wflat (wm_img s') (wm_log s') !! a = wflat (wm_img σ) (wm_log σ) !! a) /\
    (forall r0 : register, register_beq r0 tlb = false ->
       register_lookup r0 (wm_regs s') = register_lookup r0 (wm_regs σ)).
Proof.
  intros vpn la Hsite r s' Hrun.
  pose proof Hsite as Hsite'.
  destruct Hsite' as (Hpc & Halv & Halp & HnotRVC & Hexp & Hgates & Hdisj
                      & Haccp & HW0 & Hpin & Hbytes).
  pose proof Hexp as Hexp'.
  destruct Hexp' as (Hvar & Hwf & Hs2 & Hs1 & Hs0 & Hpins & Hd2 & Hd1 & Hcoll
                     & Harm & Hregs).
  pose proof (pt_slot_mem_acc_wf _ _ _ Hs0) as Hacc.
  destruct (wfetch_peel_k_of_site tid σ root_ppn va pa p2 p1 w0 lw w Hsite)
    as (_ & Hpeel & Hfilt).
  assert (Hrd : is_Some (read_bytes (wflat (wm_img σ) (wm_log σ)) la 8)).
  { exists (lw : bv (8 * 8)%N). apply read_bytes_of_bytes. intros j Hj.
    rewrite -(wflat_st_mem σ). apply (proj1 Hs0). lia. }
  pose proof (wrun_ws_le tid _ σ r s' Hrun) as Hle.
  destruct (wfetch_family tid σ root_ppn va pa p2 p1 w0 lw w Hsite)
    as [Hfam|Hfam].
  - assert (Hst : forall u : bv (8 * 8)%N,
              wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
              exists (y : FetchResult) (t' : mstate) (es : list weff),
                exec_stale la 8 u (fetch tt) (wflat_st σ) = Some (y, t', es) /\
                trace_stale wak_plain la 8 es).
    { intros u Hu. destruct (Hfam u Hu) as (sgm & esm & Hex & Ht & _).
      by exists (F_Base w), sgm, esm. }
    destruct (wrun_exec_stale_elim tid la 8 wak_plain (wwalk_filter w0 lw)
                True (fetch tt) Hacc ltac:(lia) ak_pins_plain σ Hpeel Hwf
                Hfilt Hrd Hst r s' Hrun)
      as (u & es & _ & HΦu & Hexu & Hwf' & Hlt).
    exact (wfetch_outcome_glue tid σ s' la pa w (wwalk_filter w0 lw)
             (trace_stale wak_plain la 8) u r es Hfam HΦu Hexu Hwf' Hlt Hle).
  - assert (Hst : forall u : bv (8 * 8)%N,
              wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
              exists (y : FetchResult) (t' : mstate) (es : list weff),
                exec_stale la 8 u (fetch tt) (wflat_st σ) = Some (y, t', es) /\
                trace_off_win la 8 es).
    { intros u Hu. destruct (Hfam u Hu) as (sgm & esm & Hex & Ht & _).
      by exists (F_Base w), sgm, esm. }
    destruct (wrun_exec_stale_elim_const tid la 8 wak_plain
                (wwalk_filter w0 lw) True true (fetch tt) Hacc ltac:(lia)
                ak_pins_plain σ Hpeel Hwf Hfilt Hrd Hst r s' Hrun)
      as (u & es & _ & HΦu & Hexu & Hwf' & Hlt).
    exact (wfetch_outcome_glue tid σ s' la pa w (wwalk_filter w0 lw)
             (trace_off_win la 8) u r es Hfam HΦu Hexu Hwf' Hlt Hle).
Qed.

(* ====================================================================== *)
(** ** 6. THE POST-FETCH REMAINDER, AND [wexec_tail]

    §6a is the second half of
    [WeakEffSkel.exec_eff_hart_active_progress_base_gen]'s script, replayed
    over [WkStepPeel] §0's extracted [rha_after_fetch]: the decode, the
    landing-pad gate, the [nextPC] write and the [execute].  It is the ONE
    fact that mentions the instruction, and BOTH sides of the bridge consume
    it — the weak side through §1 (an empty trace makes it a certificate),
    the mirror side verbatim (§7, §8).

    Note what is NOT a premise: [is_lpad_instruction i = false].  The gate is
    [and_boolM (is_landing_pad_expected …) (returnR …)], which SHORT-CIRCUITS
    on a clear [elp], so the instruction's landing-pad status is never
    probed. *)

(** *** 6a. The remainder at [exec_eff], at an arbitrary state. *)
Lemma exec_eff_rha_after_fetch_base (s s_x : mstate)
    (w : SailStdpp.Values.mword 32) (i : instruction)
    (pc : SailStdpp.Values.mword 64) (resf : ExecutionResult) (es_x : list weff) :
  exec_eff (ext_decode w) s = Some (i, s, []) ->
  eq_vec (register_lookup elp s.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  register_lookup PC s.(sregs) = pc ->
  exec_eff (execute i) (set_reg s nextPC (add_vec_int pc 4))
    = Some (resf, s_x, es_x) ->
  (match resf with ExecuteAs _ => False | _ => True end) ->
  exec_eff (Defs.catch_early_return (rha_after_fetch (F_Base w))) s
    = Some (Step_Execute (resf, zero_extend' 32 w), s_x, es_x).
Proof.
  intros Hdec Hlpad HpcF Hexec Hnotexec.
  unfold rha_after_fetch. cbv beta.
  rewrite exec_eff_catch_early_return.
  unfold ext_fetch_hook. cbn match. cbn beta iota.
  (* the SYMBOLIC model's instruction announcement: silent, empty trace *)
  rewrite execR_eff_bind0_eq execR_eff_liftR exec_eff_instr_announce.
  cbn match. rewrite ?app_nil_l.
  rewrite execR_eff_bind_eq execR_eff_liftR Hdec. cbn match.
  unfold get_config_print_instr. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_bind0_eq execR_eff_returnR.
  cbn match.
  unfold Defs.and_boolM.
  rewrite execR_eff_bind_eq execR_eff_liftR exec_eff_is_landing_pad Hlpad.
  cbn match. cbn match.
  rewrite execR_eff_returnR. cbn match. cbn match.
  rewrite execR_eff_bind_eq execR_eff_liftR (exec_eff_read_reg PC) HpcF. cbn match.
  rewrite execR_eff_bind_eq. rewrite execR_eff_bind0_eq execR_eff_liftR
    exec_eff_write_reg. cbn match.
  rewrite execR_eff_liftR Hexec. cbn match. cbn match.
  rewrite execR_eff_bind_eq.
  destruct resf; cbn in Hnotexec; try contradiction;
    cbn match; rewrite execR_eff_returnR; cbn match;
    rewrite execR_eff_returnR; cbn [app]; by rewrite ?app_nil_r.
Qed.

(** *** 6b. …for a REGISTER-ONLY execute: the post-state exists, the trace is
    EMPTY, and every register outside [F ∪ {nextPC}] is where the fetch left
    it. *)
Lemma exec_eff_rha_after_fetch_regonly (s : mstate)
    (w : SailStdpp.Values.mword 32) (i : instruction) (F : register -> bool) :
  exec_eff (ext_decode w) s = Some (i, s, []) ->
  eq_vec (register_lookup elp s.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  wexec_regonly i F ->
  exists s_x : mstate,
    exec_eff (Defs.catch_early_return (rha_after_fetch (F_Base w))) s
      = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), s_x, []) /\
    (forall r : register, F r = false -> register_beq r nextPC = false ->
       register_lookup r s_x.(sregs) = register_lookup r s.(sregs)).
Proof.
  intros Hdec Hlpad Hex.
  destruct (Hex (set_reg s nextPC
                   (add_vec_int (register_lookup PC s.(sregs)) 4)))
    as (s_x & Hxeq & Hxreg).
  exists s_x. split.
  - exact (exec_eff_rha_after_fetch_base s s_x w i
             (register_lookup PC s.(sregs)) RETIRE_SUCCESS []
             Hdec Hlpad eq_refl Hxeq I).
  - intros r HF Hne. rewrite (Hxreg r HF). cbn [sregs set_reg].
    exact (irrelevant_register_set r nextPC s.(sregs) _ Hne).
Qed.

(** *** 6c. …and the ordinary CERTIFICATE it is on the weak side (§1). *)
Lemma wstep_ok_rha_after_fetch (tid : option nat) (s : wmstate)
    (w : SailStdpp.Values.mword 32) (i : instruction) (F : register -> bool) :
  exec_eff (ext_decode w) (wflat_st s) = Some (i, wflat_st s, []) ->
  eq_vec (register_lookup elp (wm_regs s))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  wexec_regonly i F ->
  wstep_ok tid (Defs.catch_early_return (rha_after_fetch (F_Base w))) s.
Proof.
  intros Hdec Hlpad Hex.
  destruct (exec_eff_rha_after_fetch_regonly (wflat_st s) w i F Hdec Hlpad Hex)
    as (s_x & Hxeq & _).
  exact (wstep_ok_of_eff_nil_flat tid _ s _ s_x Hxeq).
Qed.

(** *** 6d. [wexec_tail] — DELIVERABLE (3).

    §5c says the fetch returned [F_Base w] and moved no register but [tlb];
    the instruction site's decode and [elp] facts therefore hold at the
    post-fetch state, and §6c turns them into the certificate. *)
Lemma wexec_tail_of (tid : option nat) (σ : wmstate) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (w : SailStdpp.Values.mword 32)
    (i : instruction) (F : register -> bool) :
  wfetch_site tid σ root_ppn va pa p2 p1 w0 lw w ->
  winstr_site σ w i F ->
  wexec_tail tid σ.
Proof.
  intros Hsite (Hdec & Hlpad & Hex & _ & _) r s' Hrun.
  destruct (wfetch_run_outcome tid σ root_ppn va pa p2 p1 w0 lw w Hsite
              r s' Hrun) as (-> & _ & _ & _ & _ & _ & Hrg).
  apply (wstep_ok_rha_after_fetch tid s' w i F).
  - exact (Hdec (wflat_st s') Hrg).
  - rewrite (Hrg elp ltac:(vm_compute; reflexivity)). exact Hlpad.
  - exact Hex.
Qed.

(* ====================================================================== *)
(** ** 7. THE POSTLUDE AND THE TICK

    [ts_after_rha sv] is [try_step]'s trap/retire dispatch followed by the PC
    tick and the [minstret] bump.  On the RETIRE arm — the only one a
    successfully-retiring instruction reaches — it is TOTAL, register-only
    and quiet, PROVIDED the hart is still active; off that arm it is neither
    (the trap arms run [handle_exception] / [exception_handler], and the
    [ExecuteAs] arm is an [internal_error]).  That is why §8 has to pin [sv]
    rather than discharge [wstep_post_tail] by totality. *)

Lemma exec_eff_ts_after_rha_retire (s : mstate)
    (ib : SailStdpp.Values.mword 32) :
  register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
  exists (bb : bool) (t : mstate),
    exec_eff (ts_after_rha (Step_Execute (RETIRE_SUCCESS, ib))) s
      = Some (bb, t, []).
Proof.
  intros Hhart.
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
  match goal with |- context [if ?c then _ else _] => destruct c end.
  - erewrite exec_eff_bind0_nil.
    2:{ erewrite exec_eff_bind0_nil.
        2:{ erewrite exec_eff_bind_nil. 2:{ apply (exec_eff_read_reg minstret). }
            apply exec_eff_write_reg. }
        cbn beta iota. reflexivity. }
    cbn beta iota. rewrite exec_eff_returnm. cbn match.
    do 2 eexists. reflexivity.
  - erewrite exec_eff_bind0_nil.
    2:{ erewrite exec_eff_bind0_nil.
        2:{ cbn beta iota. reflexivity. }
        cbn beta iota. reflexivity. }
    cbn beta iota. rewrite exec_eff_returnm. cbn match.
    do 2 eexists. reflexivity.
Qed.

(** The two empty-trace facts the concatenations need. *)
Lemma trace_off_win_nil (ra : Arch.pa) (rn : N) : trace_off_win ra rn [].
Proof. intros ak pa n Hin. by apply elem_of_nil in Hin. Qed.

Lemma trace_stale_nil (rak : akinfo) (ra : Arch.pa) (rn : N) :
  trace_stale rak ra rn [].
Proof. exact I. Qed.

(** *** 7b. [wstep_tick_tail] — DELIVERABLE (4), THE TOTALITY ROUTE.

    [step_tick false] is [returnm], for which [wstep_ok] is [True]; the clock
    tick is total, register-only and quiet at EVERY state, so no run
    inversion is needed on either branch.  The tick-[true] totality is an
    explicit premise so that this lemma's own axiom footprint is empty:
    [WeakTickEff.exec_eff_tick_clock] carries
    [functional_extensionality_dep], which [WkStepPeel] does not.  The
    corollary below discharges it for a caller that accepts that axiom. *)
Lemma wstep_tick_tail_of (tid : option nat) (σ : wmstate) (tick : bool) :
  (tick = true -> forall s : mstate,
     exists t : mstate, exec_eff (tick_clock tt) s = Some (tt, t, [])) ->
  wstep_tick_tail tid σ tick.
Proof.
  intros Htot x s' _. unfold step_tick. destruct tick.
  - destruct (Htot eq_refl (wflat_st s')) as (t & Heq).
    exact (wstep_ok_of_eff_nil_flat tid _ s' tt t Heq).
  - exact I.
Qed.

Lemma wstep_tick_tail_of_tick (tid : option nat) (σ : wmstate) (tick : bool) :
  wstep_tick_tail tid σ tick.
Proof.
  apply wstep_tick_tail_of. intros _ s.
  destruct (exec_eff_tick_clock s) as (c & t0 & p & Heq).
  by eexists.
Qed.

(* ====================================================================== *)
(** ** 8. [run_hart_active]'s OUTCOME, AND [wstep_post_tail]

    §5's family with §6a's remainder appended: [WkStepPeel] §5c's
    [exec_stale_run_hart_active] takes exactly that pair, and the remainder's
    trace is EMPTY, so the whole [run_hart_active] run has the fetch's trace
    and therefore the fetch family's trace condition, unchanged.  The peel is
    [WkStepPeel] §3a's [wrha_peel], whose two interface premises are the
    fetch peel (§5c) and [wexec_tail] (§6d).  The ⇐-bridge then pins the
    STEP VALUE — and that is the whole point: [ts_after_rha] is only well
    behaved on the retire arm. *)

Lemma wrha_fam_of_fetch_fam (σ : wmstate) (la : Arch.pa) (pa : mword 64)
    (w : SailStdpp.Values.mword 32) (i : instruction) (F : register -> bool)
    (Φ : (nat -> bv 8) -> Prop) (T : list weff -> Prop) :
  acc_wf la 8 ->
  register_lookup cur_privilege (wm_regs σ) = Supervisor ->
  exec_eff (dispatchInterrupt Supervisor) (wflat_st σ)
    = Some (None, wflat_st σ, []) ->
  winstr_site σ w i F ->
  wfetch_fam σ la pa w Φ T ->
  forall u : bv (8 * 8)%N, Φ (fun j : nat => nth_byte u j) ->
    exists (sx : mstate) (es : list weff),
      exec_stale la 8 u (run_hart_active 0) (wflat_st σ)
        = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sx, es) /\
      T es /\
      register_lookup hart_state sx.(sregs) = HART_ACTIVE tt.
Proof.
  intros Hacc Hpriv Hdisp (Hdec & Hlpad & Hex & HF & Hhart) Hfam u Hu.
  destruct (Hfam u Hu) as (sgm & esm & Hexf & Ht & _ & _ & Hrg & _).
  assert (Hlpadm : eq_vec (register_lookup elp sgm.(sregs))
                     (landing_pad_bits_backwards LP_EXPECTED) = false).
  { rewrite (Hrg elp ltac:(vm_compute; reflexivity)). exact Hlpad. }
  destruct (exec_eff_rha_after_fetch_regonly sgm w i F
              (Hdec sgm Hrg) Hlpadm Hex) as (sx & Hxeq & Hxreg).
  exists sx, esm. split_and!.
  - pose proof (exec_stale_run_hart_active la u (wflat_st σ) sgm sx (F_Base w)
                  (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w)) esm []
                  Hacc Hpriv Hdisp Hexf Hxeq (trace_off_win_nil la 8)) as Hr.
    by rewrite app_nil_r in Hr.
  - exact Ht.
  - rewrite (Hxreg hart_state HF ltac:(vm_compute; reflexivity)).
    rewrite (Hrg hart_state ltac:(vm_compute; reflexivity)). exact Hhart.
Qed.

Lemma wrha_run_outcome (tid : option nat) (σ : wmstate) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (w : SailStdpp.Values.mword 32)
    (i : instruction) (F : register -> bool) :
  wfetch_site tid σ root_ppn va pa p2 p1 w0 lw w ->
  winstr_site σ w i F ->
  exec_eff (dispatchInterrupt Supervisor) (wflat_st σ)
    = Some (None, wflat_st σ, []) ->
  forall (sv : Step) (s' : wmstate),
    wrun tid (run_hart_active 0) σ sv s' ->
    sv = Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w) /\
    register_lookup hart_state (wm_regs s') = HART_ACTIVE tt.
Proof.
  intros Hsite Hinstr Hdisp sv s' Hrun.
  pose proof Hsite as Hsite'.
  destruct Hsite' as (Hpc & Halv & Halp & HnotRVC & Hexp & Hgates & Hdisj
                      & Haccp & HW0 & Hpin & Hbytes).
  pose proof Hexp as Hexp'.
  destruct Hexp' as (Hvar & Hwf & Hs2 & Hs1 & Hs0 & Hpins & Hd2 & Hd1 & Hcoll
                     & Harm & Hregs).
  pose proof (pt_slot_mem_acc_wf _ _ _ Hs0) as Hacc.
  set (la := u_pte_addr (u_next_base p1)
               (subrange_vec_dec (svpn_of va) 8 0)) in *.
  assert (Hpriv : register_lookup cur_privilege (wm_regs σ) = Supervisor)
    by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hgates)))))))).
  destruct (wfetch_peel_k_of_site tid σ root_ppn va pa p2 p1 w0 lw w Hsite)
    as (Hfk & _ & Hfilt).
  pose proof (wrha_peel tid σ _ (wwalk_filter w0 lw) Hpriv Hdisp Hfk
                (wexec_tail_of tid σ root_ppn va pa p2 p1 w0 lw w i F
                   Hsite Hinstr)) as Hpeel.
  assert (Hrd : is_Some (read_bytes (wflat (wm_img σ) (wm_log σ)) la 8)).
  { exists (lw : bv (8 * 8)%N). apply read_bytes_of_bytes. intros j Hj.
    rewrite -(wflat_st_mem σ). apply (proj1 Hs0). lia. }
  destruct (wfetch_family tid σ root_ppn va pa p2 p1 w0 lw w Hsite)
    as [Hfam|Hfam];
    pose proof (wrha_fam_of_fetch_fam σ la pa w i F _ _ Hacc Hpriv Hdisp
                  Hinstr Hfam) as Hrfam.
  - assert (Hst : forall u : bv (8 * 8)%N,
              wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
              exists (y : Step) (t' : mstate) (es : list weff),
                exec_stale la 8 u (run_hart_active 0) (wflat_st σ)
                  = Some (y, t', es) /\ trace_stale wak_plain la 8 es).
    { intros u Hu. destruct (Hrfam u Hu) as (sx & es & Hex & Ht & _).
      by exists (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w)), sx, es. }
    destruct (wrun_exec_stale_elim tid la 8 wak_plain (wwalk_filter w0 lw)
                True (run_hart_active 0) Hacc ltac:(lia) ak_pins_plain σ
                Hpeel Hwf Hfilt Hrd Hst sv s' Hrun)
      as (u & es & _ & HΦu & Hexu & _ & _).
    destruct (Hrfam u HΦu) as (sx & es' & Hex & _ & Hhart).
    rewrite Hex in Hexu. injection Hexu as Hx Hsg _.
    split; [by rewrite -Hx|].
    rewrite -(wflat_st_regs s') -Hsg. exact Hhart.
  - assert (Hst : forall u : bv (8 * 8)%N,
              wwalk_filter w0 lw (fun j : nat => nth_byte u j) ->
              exists (y : Step) (t' : mstate) (es : list weff),
                exec_stale la 8 u (run_hart_active 0) (wflat_st σ)
                  = Some (y, t', es) /\ trace_off_win la 8 es).
    { intros u Hu. destruct (Hrfam u Hu) as (sx & es & Hex & Ht & _).
      by exists (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w)), sx, es. }
    destruct (wrun_exec_stale_elim_const tid la 8 wak_plain
                (wwalk_filter w0 lw) True true (run_hart_active 0) Hacc
                ltac:(lia) ak_pins_plain σ Hpeel Hwf Hfilt Hrd Hst sv s' Hrun)
      as (u & es & _ & HΦu & Hexu & _ & _).
    destruct (Hrfam u HΦu) as (sx & es' & Hex & _ & Hhart).
    rewrite Hex in Hexu. injection Hexu as Hx Hsg _.
    split; [by rewrite -Hx|].
    rewrite -(wflat_st_regs s') -Hsg. exact Hhart.
Qed.

(** *** [wstep_post_tail] — DELIVERABLE (4), the run-inversion route. *)
Lemma wstep_post_tail_of (tid : option nat) (σ : wmstate) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (w : SailStdpp.Values.mword 32)
    (i : instruction) (F : register -> bool) :
  wfetch_site tid σ root_ppn va pa p2 p1 w0 lw w ->
  winstr_site σ w i F ->
  exec_eff (dispatchInterrupt Supervisor) (wflat_st σ)
    = Some (None, wflat_st σ, []) ->
  wstep_post_tail tid σ.
Proof.
  intros Hsite Hinstr Hdisp sv s' Hrun.
  destruct (wrha_run_outcome tid σ root_ppn va pa p2 p1 w0 lw w i F
              Hsite Hinstr Hdisp sv s' Hrun) as (-> & Hhart).
  destruct (exec_eff_ts_after_rha_retire (wflat_st s') (zero_extend' 32 w)
              Hhart) as (bb & t & Heq).
  exact (wstep_ok_of_eff_nil_flat tid _ s' bb t Heq).
Qed.

(* ====================================================================== *)
(** ** 9. THE MIRROR SIDE: [wstep_tail_eff] AND [wstep_family_ready]

    [WkStepPeel] §5f's [wstep_tail_eff] is the whole window-free tail as
    three [exec_eff] equations with their traces; for a register-only execute
    all three traces are EMPTY, so both trace conditions are the empty-list
    ones and §9a is just §6b + §7 + §7b assembled.

    §§9c–9d then discharge [wstep_family_ready] outright.  What makes that
    possible is the interface's WALK-FILTER GUARD (see the file header): the
    landed walk layer describes a stale walk only at an A/D variant of the
    invariant's word — the absorption theorem's family is indexed by [av dv]
    with [pte_ad_le] — and a run at a wild [u] that still returned [Ok]
    would leave §9b with nothing to go on.  The guard is exactly the
    filter's own acceptance predicate, so [wwalk_filter_inv] recovers the
    index and the member is in hand. *)

(** *** 9a. The window-free tail at a mirror state. *)
Lemma wstep_tail_eff_at (la : Arch.pa) (tick : bool) (sf : mstate)
    (w : SailStdpp.Values.mword 32) (i : instruction) (F : register -> bool) :
  exec_eff (ext_decode w) sf = Some (i, sf, []) ->
  eq_vec (register_lookup elp sf.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  wexec_regonly i F ->
  F hart_state = false ->
  register_lookup hart_state sf.(sregs) = HART_ACTIVE tt ->
  (tick = true -> forall s : mstate,
     exists t : mstate, exec_eff (tick_clock tt) s = Some (tt, t, [])) ->
  wstep_tail_eff la tick sf (F_Base w).
Proof.
  intros Hdec Hlpad Hex HF Hhart Htot.
  destruct (exec_eff_rha_after_fetch_regonly sf w i F Hdec Hlpad Hex)
    as (sx & Hxeq & Hxreg).
  assert (Hhx : register_lookup hart_state sx.(sregs) = HART_ACTIVE tt).
  { rewrite (Hxreg hart_state HF ltac:(vm_compute; reflexivity)). exact Hhart. }
  destruct (exec_eff_ts_after_rha_retire sx (zero_extend' 32 w) Hhx)
    as (bb & sy & Hpost).
  assert (Htk : exists sfin : mstate,
            exec_eff (step_tick tick) sy = Some (tt, sfin, [])).
  { unfold step_tick. destruct tick.
    - destruct (Htot eq_refl sy) as (t & Heq). by exists t.
    - by exists sy. }
  destruct Htk as (sfin & Htick).
  exists (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w)), sx, sy, sfin, bb,
    [], [], [].
  split_and!; [> exact Hxeq | exact Hpost | exact Htick
             | exact (trace_off_win_nil la 8)
             | exact (trace_stale_nil wak_plain la 8) ].
Qed.

(** *** 9b. THE CORE: one member's post-state, described, is everything.

    Given a member's [exec_stale] equation together with what its memory and
    its registers look like, the text read and the whole window-free tail are
    available THERE.  §9c and §9d differ only in where that description comes
    from. *)
Lemma wstep_ready_at_member (tid : option nat) (σ : wmstate)
    (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64)
    (w : SailStdpp.Values.mword 32) (i : instruction) (F : register -> bool)
    (tick : bool) :
  let vpn := svpn_of va in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  wfetch_site tid σ root_ppn va pa p2 p1 w0 lw w ->
  winstr_site σ w i F ->
  (tick = true -> forall s : mstate,
     exists t : mstate, exec_eff (tick_clock tt) s = Some (tt, t, [])) ->
  forall (u : bv (8 * 8)%N) (sg' : mstate) (esw : list weff),
    exec_stale la 8 u (translateAddr (Virtaddr va) (InstructionFetch tt))
      (wflat_st σ)
      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sg', esw) ->
    (mem sg' = wflat (wm_img σ) (wm_log σ) \/
     exists lw' : mword 64,
       mem sg' = write_bytes (wflat (wm_img σ) (wm_log σ)) la 8 lw') ->
    (forall r : register, register_beq r tlb = false ->
       register_lookup r sg'.(sregs) = register_lookup r (wm_regs σ)) ->
    exec_eff (mem_read (InstructionFetch tt) PBMT_PMA (Physaddr pa) 4
                false false false) sg'
      = Some (Ok w, sg', [WEread wak_plain pa 4]) /\
    wstep_tail_eff la tick sg' (F_Base w).
Proof.
  intros vpn la Hsite Hinstr Htot u sg' esw Heq Hmem Hrg.
  pose proof Hsite as Hsite'.
  destruct Hsite' as (Hpc & Halv & Halp & HnotRVC & Hexp & Hgates & Hdisj
                      & Haccp & HW0 & Hpin & Hbytes).
  pose proof Hinstr as Hinstr'.
  destruct Hinstr' as (Hdec & Hlpad & Hex & HF & Hhart).
  pose proof Hexp as Hexp'.
  destruct Hexp' as (_ & _ & _ & _ & Hs0 & _).
  pose proof (pt_slot_mem_acc_wf _ _ _ Hs0) as Hacc.
  destruct (wfetch_member_run σ la va pa w u sg' esw
              Hacc Haccp Hdisj Hpc Halv Halp HnotRVC Hgates Hbytes Heq Hmem Hrg)
    as [Hmr _].
  split; [exact Hmr|].
  apply (wstep_tail_eff_at la tick sg' w i F).
  - exact (Hdec sg' Hrg).
  - rewrite (Hrg elp ltac:(vm_compute; reflexivity)). exact Hlpad.
  - exact Hex.
  - exact HF.
  - rewrite (Hrg hart_state ltac:(vm_compute; reflexivity)). exact Hhart.
  - exact Htot.
Qed.

(** *** 9c. The member description, from the exports.  The walk filter
    accepts exactly the A/D variants of the invariant's word
    ([WkFetchPeel] §4b's [wwalk_filter_inv]), which is precisely the index
    of the absorption theorem's family — so the guarded interface's
    hypothesis lands on a member, and [exec_stale] being a FUNCTION pins
    that member's post-state against the one the caller names. *)
Lemma wwalk_member_of_exports (tid : option nat) (σ : wmstate)
    (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64) (av dv : mword 1) :
  let vpn := svpn_of va in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  wwalk_exports tid σ root_ppn va pa p2 p1 w0 lw ->
  pte_ad_le (pte_set_ad w0 av dv) lw ->
  exists (sgx : mstate) (esx : list weff),
    exec_stale la 8 (pte_set_ad w0 av dv)
      (translateAddr (Virtaddr va) (InstructionFetch tt)) (wflat_st σ)
      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), sgx, esx) /\
    (mem sgx = wflat (wm_img σ) (wm_log σ) \/
     exists lw' : mword 64,
       mem sgx = write_bytes (wflat (wm_img σ) (wm_log σ)) la 8 lw') /\
    (forall r : register, register_beq r tlb = false ->
       register_lookup r sgx.(sregs) = register_lookup r (wm_regs σ)).
Proof.
  intros vpn la Hexp Hle.
  pose proof Hexp as Hexp'.
  destruct Hexp' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Harm & Hregs).
  destruct Harm as [Hro | (lw' & wtr & Hupd & Hfam)].
  - destruct (Hro av dv Hle) as (sgx & esx & Hex & Hmem & _ & _).
    exists sgx, esx. split_and!;
      [exact Hex|left; exact Hmem|exact (Hregs av dv sgx esx Hle Hex)].
  - destruct (Hfam av dv Hle) as (sgx & esx & Hex & Hmem & _ & _).
    exists sgx, esx. split_and!;
      [exact Hex|right; exists lw'; exact Hmem
      |exact (Hregs av dv sgx esx Hle Hex)].
Qed.

(** *** 9d. THE DISCHARGER — DELIVERABLE (5).

    The guard is what makes it possible: [wwalk_filter_inv] turns the
    accepted word into [pte_set_ad w0 av dv] with [pte_ad_le … lw], 9c
    produces the family member at that index, and the caller's own equation
    identifies its post-state with the one it named.  From there §9b's core
    reads the text word and assembles the whole window-free tail. *)
Lemma wstep_family_ready_of (tid : option nat) (σ : wmstate)
    (root_ppn : mword 44) (va pa p2 p1 w0 lw : mword 64)
    (w : SailStdpp.Values.mword 32) (i : instruction) (F : register -> bool)
    (tick : bool) :
  let vpn := svpn_of va in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  (forall bmi : bool,
     wfetch_site tid (wmi σ bmi) root_ppn va pa p2 p1 w0 lw w) ->
  (forall bmi : bool, winstr_site (wmi σ bmi) w i F) ->
  (tick = true -> forall s : mstate,
     exists t : mstate, exec_eff (tick_clock tt) s = Some (tt, t, [])) ->
  wstep_family_ready tid σ la va pa w0 lw w tick.
Proof.
  intros vpn la Hsites Hinstrs Htot bmi u sg' esw Hu Heq.
  destruct (wwalk_filter_inv w0 lw u Hu) as (av & dv & Hw & Hle).
  rewrite Hw in Heq.
  pose proof (Hsites bmi) as Hsite.
  pose proof Hsite as Hsite'.
  destruct Hsite' as (_ & _ & _ & _ & Hexp & _).
  destruct (wwalk_member_of_exports tid (wmi σ bmi) root_ppn va pa p2 p1 w0 lw
              av dv Hexp Hle) as (sgx & esx & Hex & Hmem & Hrg).
  rewrite Hex in Heq. injection Heq as Hsg Hes.
  rewrite -Hsg.
  exact (wstep_ready_at_member tid (wmi σ bmi) root_ppn va pa p2 p1 w0 lw w i F
           tick Hsite (Hinstrs bmi) Htot (pte_set_ad w0 av dv) sgx esx Hex
           Hmem Hrg).
Qed.

(* ====================================================================== *)
(** ** 10. THE [wmi] TRANSPORTS THE CAPSTONE WANTS

    [WkStepPeel] §3b owes its fetch-side premises at [wmi σ bmi] for BOTH
    values of the [minstret_increment] flag (the funnel's own choice of the
    flag is not visible to the caller).  Everything in §4's two bundles
    except the walk exports themselves is either a fact about the log, the
    image or the views — which a register write does not move, so it
    transports by conversion — or a [register_lookup] at a register that is
    not [minstret_increment]. *)

Lemma register_lookup_wmi (σ : wmstate) (b : bool) (r : register) :
  register_beq r (R_bool minstret_increment) = false ->
  register_lookup r (wm_regs (wmi σ b)) = register_lookup r (wm_regs σ).
Proof.
  intros Hne. unfold wmi. cbn [wm_regs wset_reg].
  exact (irrelevant_register_set r (R_bool minstret_increment)
           (wm_regs σ) b Hne).
Qed.

Lemma wfgate_regs_wmi (σ : wmstate) (b : bool) (pa : mword 64) :
  wfgate_regs (wm_regs σ) pa -> wfgate_regs (wm_regs (wmi σ b)) pa.
Proof.
  intros Hg.
  apply (wfgate_regs_transport (wm_regs σ) (wm_regs (wmi σ b)) pa Hg);
    [ exact (register_lookup_wmi σ b pmpcfg_n ltac:(vm_compute; reflexivity))
    | exact (register_lookup_wmi σ b pmpaddr_n ltac:(vm_compute; reflexivity))
    | exact (register_lookup_wmi σ b pma_regions ltac:(vm_compute; reflexivity))
    | exact (register_lookup_wmi σ b htif_tohost_base
               ltac:(vm_compute; reflexivity))
    | exact (register_lookup_wmi σ b cur_privilege
               ltac:(vm_compute; reflexivity)) ].
Qed.

Lemma wfetch_site_wmi (tid : option nat) (σ : wmstate) (root_ppn : mword 44)
    (va pa p2 p1 w0 lw : mword 64) (w : SailStdpp.Values.mword 32) (b : bool) :
  let vpn := svpn_of va in
  let la := u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0) in
  wwalk_exports tid (wmi σ b) root_ppn va pa p2 p1 w0 lw ->
  register_lookup PC (wm_regs σ) = va ->
  is_aligned_vaddr (Virtaddr va) 4 = true ->
  is_aligned_paddr (Physaddr pa) 4 = true ->
  isRVC (subrange_vec_dec w 15 0) = false ->
  wfgate_regs (wm_regs σ) pa ->
  racc_disj la 8 pa 4 ->
  acc_wf pa 4 ->
  (forall j : nat, (j < 4)%nat -> pa_z (pa_add pa j) <> 0) ->
  (forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr pa j)) ->
  (forall j : nat, (N.of_nat j < 4)%N ->
     wflat (wm_img σ) (wm_log σ) !! (pa_add pa j) = Some (nth_byte w j)) ->
  wfetch_site tid (wmi σ b) root_ppn va pa p2 p1 w0 lw w.
Proof.
  intros vpn la Hexp Hpc Halv Halp HnotRVC Hgates Hdisj Haccp HW0 Hpin Hbytes.
  rewrite /wfetch_site. split_and!;
    [ | exact Halv | exact Halp | exact HnotRVC | exact Hexp
    | exact (wfgate_regs_wmi σ b pa Hgates) | exact Hdisj | exact Haccp
    | exact HW0 | exact Hpin | exact Hbytes ].
  rewrite (register_lookup_wmi σ b PC ltac:(vm_compute; reflexivity)).
  exact Hpc.
Qed.

(** The instruction side.  The DECODE premise is the one that genuinely
    changes shape: at [wmi σ b] the agreeing states carry [b] in
    [minstret_increment], so what the caller must own is the decode at every
    state agreeing with σ off [tlb] AND off [minstret_increment] — which is
    exactly what [WeakFetchEff] §6's [exec_eff_decode_bridge] gives (the
    decode's read set contains neither: [WkEntryEff.D_m_mi]). *)
Lemma winstr_site_wmi (σ : wmstate) (b : bool)
    (w : SailStdpp.Values.mword 32) (i : instruction) (F : register -> bool) :
  (forall t : mstate,
     (forall r : register, register_beq r tlb = false ->
        register_beq r (R_bool minstret_increment) = false ->
        register_lookup r t.(sregs) = register_lookup r (wm_regs σ)) ->
     exec_eff (ext_decode w) t = Some (i, t, [])) ->
  eq_vec (register_lookup elp (wm_regs σ))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  wexec_regonly i F ->
  F hart_state = false ->
  register_lookup hart_state (wm_regs σ) = HART_ACTIVE tt ->
  winstr_site (wmi σ b) w i F.
Proof.
  intros Hdec Hlpad Hex HF Hhart. rewrite /winstr_site. split_and!.
  - intros t Hagree. apply Hdec. intros r Hr Hmi.
    rewrite (Hagree r Hr). exact (register_lookup_wmi σ b r Hmi).
  - rewrite (register_lookup_wmi σ b elp ltac:(vm_compute; reflexivity)).
    exact Hlpad.
  - exact Hex.
  - exact HF.
  - rewrite (register_lookup_wmi σ b hart_state ltac:(vm_compute; reflexivity)).
    exact Hhart.
Qed.

(* ====================================================================== *)
(** ** 11. Soundness checks *)

Print Assumptions wstep_ok_of_eff_nil.
Print Assumptions wfgates_at_of_regs.
Print Assumptions exec_eff_text_read_at.
Print Assumptions wfetch_member_run.
Print Assumptions wfetch_family.
Print Assumptions wfetch_run_outcome.
Print Assumptions exec_eff_rha_after_fetch_base.
Print Assumptions exec_eff_rha_after_fetch_regonly.
Print Assumptions wstep_ok_rha_after_fetch.
Print Assumptions wexec_tail_of.
Print Assumptions exec_eff_ts_after_rha_retire.
Print Assumptions wstep_tick_tail_of.
Print Assumptions wstep_tick_tail_of_tick.
Print Assumptions wrha_run_outcome.
Print Assumptions wstep_post_tail_of.
Print Assumptions wstep_tail_eff_at.
Print Assumptions wstep_family_ready_of.
Print Assumptions wfetch_site_wmi.
Print Assumptions winstr_site_wmi.
