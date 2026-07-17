(* MinstretInv.v -- put the retired-instruction counter [minstret] and its
   per-cycle increment flag [minstret_increment] into ONE Iris invariant, and
   provide the leaf-WP step rule [wp_exec_step_minstret] that OPENS that
   invariant across the single instruction step in order to read/bump them.

   Motivation: every instruction step writes both registers
   (minstret_increment := b; minstret += b), so today every leaf WP must take
   the two points-to in its precondition and hand them back (bumped) in its
   postcondition -- they are threaded linearly through the entire boot proof.
   Their *values* are never actually inspected by callers (minstret is just a
   counter), so we move them into an invariant whose body pins NEITHER value.
   The invariant is then persistent (duplicable): a leaf only needs [minstret_inv]
   (shareable) instead of the two owned cells, and obtains the cells transiently
   by opening the invariant for the duration of the step.

   CLOCK TICK.  [prim_step] nondeterministically runs [tick_clock] after the
   instruction ([riscv_step true]), which writes exactly {mcycle, mtime, mip}
   (mtime += 1 always; mip.MTIP := mtimecmp <=u mtime, and -- STCE is menvcfg
   bit 63, which MENVCFG_S pins to 1, so the Sstc branch is LIVE -- mip.STIP
   := stimecmp <=u mtime; mcycle += 1 unless filtered by mcountinhibit.CY /
   mcyclecfg).  Those three cells live in a SECOND value-agnostic invariant
   [clock_inv], and the step rule [wp_exec_step_clock] (layered BELOW the
   minstret rule) handles the tick branch entirely internally: the caller
   supplies only the no-tick witness [exec (riscv_step false) σ = Some (tt, σ')]
   and reasons at the FULL mask ⊤ ([WP Loop] is the top level, so masks are
   pinned to ⊤ throughout -- no [↑N ⊆ E] premises) -- the clock invariant is
   opened only inside the tick branch, strictly AFTER the caller's
   continuation, so an instruction whose own execution touches mtime/mip may
   open [clock_inv] itself. *)
From Stdlib Require Import FunctionalExtensionality.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* Pure exec layer for the clock tick: [tick_clock] is register-only and   *)
(* TOTAL -- at any state it succeeds, writing exactly mcycle               *)
(* (conditionally), mtime and mip.  The successor is stated as the three-  *)
(* register set_reg tower so the Iris layer can update the three           *)
(* invariant-owned cells by [reg_update].                                  *)
(* ====================================================================== *)

(* ---- regstate helpers: set-to-current-value identity, set-set collapse ---- *)
(* (register_set updates a FUNCTION field, so these need funext; clones of the
   WpPushOffCsr.v / SmodePte.v patterns -- those files are downstream.) *)

Lemma register_set_bv64_id (r : register_bitvector_64) (rs : regstate) :
  register_set (R_bitvector_64 r) (register_lookup (R_bitvector_64 r) rs) rs = rs.
Proof.
  destruct rs. unfold register_set, register_lookup. cbn.
  f_equal. apply functional_extensionality. intro r'.
  destruct (register_bitvector_64_beq r' r) eqn:E.
  - apply register_bitvector_64_beq_iff in E. subst r'. reflexivity.
  - reflexivity.
Qed.

Lemma register_set_bv64_overwrite (r : register_bitvector_64) (rs : regstate)
    (a b : mword 64) :
  register_set (R_bitvector_64 r) b (register_set (R_bitvector_64 r) a rs)
    = register_set (R_bitvector_64 r) b rs.
Proof.
  destruct rs. unfold register_set. cbn.
  f_equal. apply functional_extensionality. intro r'.
  destruct (register_bitvector_64_beq r' r); reflexivity.
Qed.

Lemma set_reg_mcycle_id (s : mstate) :
  set_reg s mcycle (register_lookup mcycle s.(sregs)) = s.
Proof.
  destruct s. unfold set_reg. cbn. rewrite register_set_bv64_id. reflexivity.
Qed.

Lemma set_reg_mip_mip (s : mstate) (v1 v2 : mword 64) :
  set_reg (set_reg s mip v1) mip v2 = set_reg s mip v2.
Proof.
  destruct s. unfold set_reg. cbn. rewrite register_set_bv64_overwrite. reflexivity.
Qed.

(* ---- clones of the Sstc gate reductions (primed: the unprimed originals
   live in WpGprCsrwCommon.v, which is DOWNSTREAM of this file) ---- *)

Lemma exec_hartSupports_Sstc' s : exec (hartSupports Ext_Sstc) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Sstc' s : exec (currentlyEnabled Ext_Sstc) s = Some (true, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Sstc) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Sstc'.
Qed.

(* ---- should_inc_mcycle is total (mirror of exec_should_inc_minstret_Some) ---- *)

Lemma exec_should_inc_mcycle_Some (priv : Privilege) s :
  ∃ b : bool, exec (should_inc_mcycle priv) s = Some (b, s).
Proof.
  unfold should_inc_mcycle, Defs.and_boolM.
  erewrite exec_bind_Some.
  2:{ erewrite exec_bind_Some.
      2:{ apply (exec_read_reg mcountinhibit s). }
      apply exec_returnm. }
  cbn beta.
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - erewrite exec_bind_Some.
    2:{ apply (exec_read_reg mcyclecfg s). }
    eexists. apply exec_returnm.
  - eexists. apply exec_returnm.
Qed.

(* ---- the "mip changed" callback branch: reads only, state no-op ---- *)

Lemma exec_csr_name_write_callback_mip (V : mword 64) s :
  exec (csr_name_write_callback "mip" V) s = Some (tt, s).
Proof.
  unfold csr_name_write_callback.
  rewrite (exec_bind_Some _ _ _ _ _
    (_ : exec (csr_name_map_backwards "mip") s = Some (mword_of_int 0x344, s))).
  2:{ vm_compute; reflexivity. }
  match goal with |- exec (returnM ?t) _ = _ => destruct t end.
  apply exec_returnm.
Qed.

Lemma exec_external_interrupts_pending_Some (s : mstate) :
  ∃ v : mword 64, exec (external_interrupts_pending tt) s = Some (v, s).
Proof.
  unfold external_interrupts_pending.
  erewrite exec_bind_Some.
  2:{ apply (exec_read_reg sig_meip s). }
  cbn beta.
  erewrite exec_bind_Some.
  2:{ apply exec_currentlyEnabled_S. }
  cbn beta.
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - erewrite exec_bind_Some.
    2:{ apply (exec_read_reg sig_seip s). }
    cbn beta. eexists. apply exec_returnM.
  - erewrite exec_bind_Some.
    2:{ apply exec_returnM. }
    cbn beta. eexists. apply exec_returnM.
Qed.

Lemma exec_read_mip_include_Some (s : mstate) :
  ∃ v : mword 64, exec (read_mip IncludePlatformInterrupts) s = Some (v, s).
Proof.
  unfold read_mip.
  erewrite exec_bind_Some.
  2:{ apply (exec_read_reg mip s). }
  cbn beta.
  destruct (exec_external_interrupts_pending_Some s) as [w He].
  erewrite exec_bind_Some.
  2:{ exact He. }
  cbn beta. eexists. apply exec_returnM.
Qed.

(* ---- clint_dispatch false: total, writes exactly mip ---- *)

(* [or_boolM (read mip -> neq ..) (returnM false)] reduces to an if over a
   neutral bool with the SAME state either way; fold it into [Some (c, st)]
   so the erewrite evars stay branch-independent. *)
Lemma if_some_bool {A} (c : bool) (x : A) :
  (if c then Some (true, x) else Some (false, x)) = Some (c, x).
Proof. destruct c; reflexivity. Qed.

Lemma exec_clint_dispatch_false (s : mstate) :
  ∃ p : mword 64,
    exec (clint_dispatch false) s = Some (tt, set_reg s mip p).
Proof.
  unfold clint_dispatch.
  erewrite exec_bind_Some. 2:{ apply (exec_read_reg mip s). }
  cbn beta.
  erewrite exec_bind_Some. 2:{ apply (exec_read_reg mip s). }
  cbn beta.
  erewrite exec_bind_Some. 2:{ apply (exec_read_reg mtimecmp s). }
  cbn beta.
  erewrite exec_bind_Some. 2:{ apply (exec_read_reg mtime s). }
  cbn beta.
  (* head = (write mip MTIP) >> (Sstc && menvcfg.STCE gate) *)
  erewrite exec_bind_Some.
  2:{ erewrite exec_bind0_Some. 2:{ apply exec_write_reg. }
      erewrite exec_and_boolM_Some. 2:{ apply exec_currentlyEnabled_Sstc'. }
      cbn match.
      erewrite exec_bind_Some. 2:{ apply (exec_read_reg menvcfg _). }
      cbn beta. apply exec_returnM. }
  cbn beta.
  match goal with |- context [ if ?c then _ else _ ] => destruct c end.
  - (* STCE live: mip.STIP write *)
    (* head = ((STIP-write >> print-nop) >> or_boolM (mip changed?)) *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind0_Some.
            2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg mip _). }
                cbn beta.
                erewrite exec_bind_Some. 2:{ apply (exec_read_reg stimecmp _). }
                cbn beta.
                erewrite exec_bind_Some. 2:{ apply (exec_read_reg mtime _). }
                cbn beta. apply exec_write_reg. }
            apply exec_returnm. }
        erewrite exec_or_boolM_Some.
        2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg mip _). }
            cbn beta. apply exec_returnM. }
        rewrite exec_returnM. apply if_some_bool. }
    cbn beta.
    match goal with |- context [ if ?c then _ else _ ] => destruct c end.
    + (* changed: read_mip + callback, state no-op *)
      match goal with
      |- context [ exec (Defs.bind (read_mip _) _) ?st = _ ] =>
        destruct (exec_read_mip_include_Some st) as [v Hrm]
      end.
      erewrite exec_bind_Some. 2:{ exact Hrm. }
      cbn beta.
      rewrite exec_csr_name_write_callback_mip.
      rewrite set_reg_mip_mip. eexists. reflexivity.
    + rewrite exec_returnM.
      rewrite set_reg_mip_mip. eexists. reflexivity.
  - (* STCE dead: single mip write *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind0_Some.
            2:{ apply exec_returnM. }
            apply exec_returnm. }
        erewrite exec_or_boolM_Some.
        2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg mip _). }
            cbn beta. apply exec_returnM. }
        rewrite exec_returnM. apply if_some_bool. }
    cbn beta.
    match goal with |- context [ if ?c then _ else _ ] => destruct c end.
    + match goal with
      |- context [ exec (Defs.bind (read_mip _) _) ?st = _ ] =>
        destruct (exec_read_mip_include_Some st) as [v Hrm]
      end.
      erewrite exec_bind_Some. 2:{ exact Hrm. }
      cbn beta.
      rewrite exec_csr_name_write_callback_mip.
      eexists. reflexivity.
    + rewrite exec_returnM.
      eexists. reflexivity.
Qed.

(* ---- tick_clock: total, writes exactly {mcycle, mtime, mip} ---- *)

Lemma exec_tick_clock (s : mstate) :
  ∃ (c t p : mword 64),
    exec (tick_clock tt) s
      = Some (tt, set_reg (set_reg (set_reg s mcycle c) mtime t) mip p).
Proof.
  unfold tick_clock.
  erewrite exec_bind_Some. 2:{ apply (exec_read_reg cur_privilege s). }
  cbn beta.
  destruct (exec_should_inc_mcycle_Some
              (register_lookup cur_privilege s.(sregs)) s) as [bc Hsic].
  erewrite exec_bind_Some. 2:{ exact Hsic. }
  cbn beta.
  destruct bc.
  - (* mcycle += 1; head = (mcycle-inc >> read mtime) *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg mcycle s). }
            cbn beta. apply exec_write_reg. }
        apply (exec_read_reg mtime _). }
    cbn beta.
    (* write mtime >> clint_dispatch false *)
    erewrite exec_bind0_Some. 2:{ apply exec_write_reg. }
    match goal with
    |- context [ exec (clint_dispatch false) ?st = _ ] =>
      destruct (exec_clint_dispatch_false st) as [p Hcd]
    end.
    rewrite Hcd. do 3 eexists. reflexivity.
  - (* mcycle untouched: insert the identity set *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ apply exec_returnM. }
        apply (exec_read_reg mtime _). }
    cbn beta.
    erewrite exec_bind0_Some. 2:{ apply exec_write_reg. }
    match goal with
    |- context [ exec (clint_dispatch false) ?st = _ ] =>
      destruct (exec_clint_dispatch_false st) as [p Hcd]
    end.
    rewrite Hcd.
    exists (register_lookup mcycle s.(sregs)).
    rewrite (set_reg_mcycle_id s). do 2 eexists. reflexivity.
Qed.

Section MinstretInv.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---------------------------------------------------------------------- *)
  (* The clock invariant: value-agnostic ownership of the three registers    *)
  (* [tick_clock] writes.  Same duplicability argument as the minstret one.  *)
  (* ---------------------------------------------------------------------- *)

  Definition clockN : namespace := nroot .@ "clock".

  Definition clock_inv_body : iProp Σ :=
    (∃ (c t p : mword 64), mcycle ↦ᵣ c ∗ mtime ↦ᵣ t ∗ mip ↦ᵣ p)%I.

  Definition clock_inv : iProp Σ := inv clockN clock_inv_body.

  Global Instance clock_inv_persistent : Persistent clock_inv.
  Proof. apply _. Qed.

  Definition minstretN : namespace := nroot .@ "minstret".

  (* Value-agnostic ownership of the two counter cells.  Because it quantifies
     [mst]/[mi] existentially, re-establishing it after a step (with the bumped
     values) is trivial, which is precisely what makes the invariant duplicable. *)
  Definition minstret_inv_body : iProp Σ :=
    (∃ (mst : mword 64) (mi : bool),
       minstret ↦ᵣ mst ∗ (R_bool minstret_increment) ↦ᵣ mi)%I.

  (* [minstret_inv] BUNDLES the clock invariant, so the (many) existing
     callers keep threading a single persistent proposition. *)
  Definition minstret_inv : iProp Σ :=
    (inv minstretN minstret_inv_body ∗ clock_inv)%I.

  Global Instance minstret_inv_persistent : Persistent minstret_inv.
  Proof. apply _. Qed.

  (* ---------------------------------------------------------------------- *)
  (* wp_exec_step_clock -- the tick-absorbing step rule, layered BELOW the   *)
  (* minstret rule.  It presents the caller the PRE-TICK interface: one      *)
  (* successor, one witness ([riscv_step false]), at the FULL mask [⊤] --    *)
  (* so an instruction whose own execution reads/writes mtime or mip can     *)
  (* [iInv clock_inv] inside its obligation.  ([WP Loop] is the top level,   *)
  (* so the mask is pinned to [⊤] rather than an arbitrary [E]; that makes   *)
  (* the [↑clockN ⊆ E]-style premises vacuous.)  The tick branch is handled  *)
  (* entirely here: [exec_tick_clock] is total, so the tick witness needs    *)
  (* no resources, and the post-tick [mstate_interp] is re-established by    *)
  (* [reg_update]-ing the three invariant-owned cells -- the invariant is    *)
  (* opened only in the tick branch, strictly AFTER the caller's             *)
  (* continuation has produced [mstate_interp σ'] and closed its own         *)
  (* invariants (we are back at mask [⊤]).                                   *)
  (* ---------------------------------------------------------------------- *)

  Lemma wp_exec_step_clock Φ :
    clock_inv -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
       ∃ σ', ⌜exec (riscv_step false) σ = Some (tt, σ')⌝ ∗
          ▷ (|={∅,⊤}=> mstate_interp σ' ∗ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "#Hcinv H".
    iApply wp_exec_step.
    iIntros (σ) "Hsi".
    iMod ("H" $! σ with "Hsi") as (σ') "[%Hexec Hk]".
    destruct (exec_tick_clock σ') as (c' & t' & p' & Htick).
    iModIntro.
    iExists σ', (set_reg (set_reg (set_reg σ' mcycle c') mtime t') mip p').
    iSplit; first done.
    iSplit.
    { iPureIntro. exact (exec_riscv_step_tick _ _ _ Hexec Htick). }
    iNext. iIntros (tick).
    iMod "Hk" as "[Hsi' HWP]".
    destruct tick.
    - (* tick: scribble the three clock cells under the invariant *)
      iInv "Hcinv" as ">Hcb" "Hclose".
      iDestruct "Hcb" as (c0 t0 p0) "(Hc & Ht & Hp)".
      iDestruct "Hsi'" as "(Hreg & Hmem & Hdev)".
      iMod (reg_update _ mcycle _ c' with "Hreg Hc") as "[Hreg Hc]".
      iMod (reg_update _ mtime _ t' with "Hreg Ht") as "[Hreg Ht]".
      iMod (reg_update _ mip _ p' with "Hreg Hp") as "[Hreg Hp]".
      iMod ("Hclose" with "[Hc Ht Hp]") as "_".
      { iNext. iExists c', t', p'. iFrame. }
      iModIntro. cbn iota. rewrite /mstate_interp. unfold set_reg; cbn [sregs mem mdev].
      iFrame "Hreg Hmem Hdev HWP".
    - iModIntro. cbn iota. iFrame "Hsi' HWP".
  Qed.

  (* The step rule for leaves that need the two counter cells: it [iInv]s
     [minstret_inv] on top of [wp_exec_step_clock], so a leaf gets
     [minstret_inv_body] for the step and hands a fresh body back -- without
     repeating the invariant-opening boilerplate.  The clock tick is fully
     absorbed one layer down, so the caller supplies only the no-tick witness
     [riscv_step false]; [clockN] is NOT removed from the caller's mask (an
     instruction may open [clock_inv] during its own execution).  Unlike the
     minstret cells, the clock cells are NEVER loaned to the caller.

     Crucially this is itself a FUPD spec: the caller picks the inner mask [Ei],
     so it can ALSO open its OWN invariants on top of the minstret one.  After the
     minstret invariant is opened (moving [⊤] -> [⊤∖↑minstretN]) the obligation
     hands the caller a [={⊤∖↑minstretN, Ei}] fupd; to open a further [inv N P],
     take [Ei := ⊤ ∖ ↑minstretN ∖ ↑N] and [iInv N] on that fupd, closing it in the
     [={Ei, ⊤∖↑minstretN}] continuation.  Leaves that need no further invariant just
     take [Ei := ⊤ ∖ ↑minstretN] (then both fupds are reflexive, discharged by
     [iModIntro]).  [wp_exec_step_clock] hands us a [={E,∅}] obligation; the
     [Ei→∅→Ei] detour is a single [fupd_mask_intro].

     The obligation must:
       - produce the next state [σ'] and the exec witness (state [σ'] via
         [register_lookup minstret σ.(sregs)], a function of σ -- so the cells are
         NOT needed for the witness, only for the post-step [state_interp] update);
       - fold the minstret bump into [state_interp σ'] and return a fresh
         [minstret_inv_body] to close the invariant. *)
  Lemma wp_exec_step_minstret Ei Φ :
    minstret_inv -∗
    (∀ σ, mstate_interp σ -∗ minstret_inv_body
         ={⊤ ∖ ↑minstretN, Ei}=∗
       ∃ σ', ⌜exec (riscv_step false) σ = Some (tt, σ')⌝ ∗
          ▷ (|={Ei, ⊤ ∖ ↑minstretN}=>
               mstate_interp σ' ∗ minstret_inv_body ∗
               WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "#[Hinv Hcinv] H".
    iApply (wp_exec_step_clock Φ with "Hcinv").
    iIntros (σ) "Hsi".
    (* open the minstret invariant ([={E, E∖↑minstretN}]); the caller's fupd
       supplies [={E∖↑minstretN, Ei}], and a [fupd_mask_intro] bridges [Ei→∅] to
       meet [wp_exec_step_clock]'s [={E,∅}] obligation. *)
    iInv "Hinv" as ">Hbody" "Hclose".
    iMod ("H" $! σ with "Hsi Hbody") as (σ') "[%Hexec Hk]".
    iApply fupd_mask_intro; [apply empty_subseteq|]. iIntros "Hcl".
    iExists σ'. iSplit; first done.
    iNext.
    iMod "Hcl" as "_".
    iMod "Hk" as "(Hsi' & Hbody' & HWP)".
    iMod ("Hclose" with "[$Hbody']") as "_".
    iModIntro. iFrame.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* wp_exec_step_hart_active_inv -- the [minstret_inv] flavour of the       *)
  (* run_hart_active leaf rule.  The caller reasons ONLY about the inner     *)
  (* instruction [run_hart_active]; this rule discharges the whole           *)
  (* [riscv_step] wrapper (read cur_privilege -> should_inc -> write         *)
  (* minstret_increment -> run_hart_active -> tick PC -> bump minstret) by    *)
  (* OPENING [minstret_inv] for the step (via [wp_exec_step_minstret]) and    *)
  (* the pure [exec_riscv_step_hart_active].  Because the two counter cells   *)
  (* live in the duplicable invariant, the caller passes only the shareable   *)
  (* [minstret_inv] and gets NOTHING counter-related back -- it keeps just    *)
  (* [hart_state] and [PC].  [cur_privilege] stays with the caller (it is     *)
  (* read by run_hart_active); [should_inc] is total                          *)
  (* ([exec_should_inc_minstret_Some]), so no privilege / increment premise   *)
  (* is required.  The caller hands back [state_interp s_exec] directly (not   *)
  (* behind a later), which lets this rule [reg_valid] the still-invariant-    *)
  (* owned counter cells to recover the wrapper's post-step reads. *)
  (* [hart_state] is held at a FRACTION [dq]: the wrapper only ever READS it
     (hart is still active at the end -- reg_valid_dq off any fraction), never
     writes it, so the caller may retain the complementary fraction throughout
     the instruction to keep reasoning about hart_state.  Returned to the
     continuation unchanged. *)
  (* The continuation lands on [▷ WP Loop], not [WP Loop]: this rule hands the
     step's OWN later back to the caller rather than consuming it internally.  A
     straight-line client doesn't care -- it [iNext]s the [▷] away and keeps its
     (timeless) resources -- but a client that closes a LOOP back onto the SAME
     [WP Loop] (the [spin] self-jump, proved by iLöb) needs exactly this later to
     strip its induction hypothesis.  To thread it, we tick PC / bump minstret
     UNDER the outer (reflexive) fupd and apply [Hcont] there -- yielding a
     [▷ WP Loop] hypothesis -- BEFORE the single [iNext] that discharges
     [wp_exec_step_minstret]'s [▷]; that [iNext] then strips the [Hcont]-produced
     later in lock-step with the step's, so no second later is needed. *)
  Lemma wp_exec_step_hart_active_inv Φ {dq : dfrac} :
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ,
       mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
       ∃ (retval : mword 32) (s_exec : mstate),
         ⌜ exec (run_hart_active 0) σ
             = Some (Step_Execute (RETIRE_SUCCESS, retval), s_exec) ⌝ ∗
         PC ↦ᵣ (register_lookup PC s_exec.(sregs)) ∗
         mstate_interp s_exec ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "#Hinv Hhs H".
    iApply (wp_exec_step_minstret (⊤ ∖ ↑minstretN) Φ with "Hinv").
    iIntros (σ) "[Hreg Hmem] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    (* should_inc returns SOME [b]; we neither know nor care which *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    (* PRE: minstret_increment := b (cell borrowed from the invariant) *)
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    iMod ("H" $! (set_reg σ (R_bool minstret_increment) b) with "[Hreg Hmem]")
      as (retval s_exec) "(%Hha & Hpc & [Hreg Hmem] & Hcont)".
    { rewrite /mstate_interp. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    (* wrapper's post-step reads, off the still-owned counter cells *)
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Hhart_exec.
    iDestruct (reg_valid with "Hreg Hmi") as %Hmi_exec.
    assert (Hhart_a :
      register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
        = HART_ACTIVE tt).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
    (* POST: tick PC and (if b) bump minstret UNDER the outer fupd, then apply the
       caller's continuation to obtain [HWP : ▷ WP Loop] -- BEFORE the [iNext]. *)
    iDestruct (reg_valid with "Hreg Hmst") as %Lmst_e.
    iMod (reg_update _ PC _ (register_lookup nextPC s_exec.(sregs)) with "Hreg Hpc")
      as "[Hreg Hpc]".
    assert (Hmst_tick :
      register_lookup minstret
        (set_reg s_exec PC (register_lookup nextPC s_exec.(sregs))).(sregs) = mst).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lmst_e | reflexivity]. }
    iDestruct ("Hcont" with "Hhs Hpc") as "HWP".
    destruct b.
    - iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst")
        as "[Hreg Hmst]".
      iModIntro. iExists _. iSplitR.
      { iPureIntro.
        exact (exec_riscv_step_hart_active σ s_exec retval true
                 Hsi Hhart_a Hha Hhart_exec Hmi_exec). }
      iNext.  (* strips HWP's later in lock-step with the step's later *)
      iModIntro. rewrite /mstate_interp. cbn [sregs mem]. rewrite Hmst_tick.
      unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi".
      { iExists (add_vec_int mst 1), true. iFrame. }
      iExact "HWP".
    - iModIntro. iExists _. iSplitR.
      { iPureIntro.
        exact (exec_riscv_step_hart_active σ s_exec retval false
                 Hsi Hhart_a Hha Hhart_exec Hmi_exec). }
      iNext.
      iModIntro. rewrite /mstate_interp. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi".
      { iExists mst, false. iFrame. }
      iExact "HWP".
  Qed.

End MinstretInv.
