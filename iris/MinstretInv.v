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
   by opening the invariant for the duration of the step. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec.
Local Open Scope Z_scope.

Section MinstretInv.
  Context `{!riscvGS Σ}.

  Definition minstretN : namespace := nroot .@ "minstret".

  (* Value-agnostic ownership of the two counter cells.  Because it quantifies
     [mst]/[mi] existentially, re-establishing it after a step (with the bumped
     values) is trivial, which is precisely what makes the invariant duplicable. *)
  Definition minstret_inv_body : iProp Σ :=
    (∃ (mst : mword 64) (mi : bool),
       minstret ↦ᵣ mst ∗ (R_bool minstret_increment) ↦ᵣ mi)%I.

  Definition minstret_inv : iProp Σ := inv minstretN minstret_inv_body.

  Global Instance minstret_inv_persistent : Persistent minstret_inv.
  Proof. apply _. Qed.

  (* Allocate the invariant once (e.g. during boot setup) from the owned cells. *)
  Lemma minstret_inv_alloc (mst : mword 64) (mi : bool) E :
    minstret ↦ᵣ mst -∗ (R_bool minstret_increment) ↦ᵣ mi ={E}=∗ minstret_inv.
  Proof.
    iIntros "Hmst Hmi". iApply inv_alloc. iNext.
    iExists mst, mi. iFrame.
  Qed.

  (* The step rule for leaves that need the two counter cells: it [iInv]s
     [minstret_inv] on top of [wp_exec_step], so a leaf gets [minstret_inv_body]
     for the step and hands a fresh body back -- without repeating the
     invariant-opening boilerplate.

     Crucially this is itself a FUPD spec: the caller picks the inner mask [Ei],
     so it can ALSO open its OWN invariants on top of the minstret one.  After the
     minstret invariant is opened (moving [E] -> [E∖↑minstretN]) the obligation
     hands the caller a [={E∖↑minstretN, Ei}] fupd; to open a further [inv N P],
     take [Ei := E ∖ ↑minstretN ∖ ↑N] and [iInv N] on that fupd, closing it in the
     [={Ei, E∖↑minstretN}] continuation.  Leaves that need no further invariant just
     take [Ei := E ∖ ↑minstretN] (then both fupds are reflexive, discharged by
     [iModIntro]).  [wp_exec_step] hands us a [={E,∅}] obligation; the [Ei→∅→Ei]
     detour is a single [fupd_mask_intro].

     The obligation must:
       - produce the next state [σ'] and the exec witness (state [σ'] via
         [register_lookup minstret σ.(sregs)], a function of σ -- so the cells are
         NOT needed for the witness, only for the post-step [state_interp] update);
       - fold the minstret bump into [state_interp σ'] and return a fresh
         [minstret_inv_body] to close the invariant. *)
  Lemma wp_exec_step_minstret E Ei Φ :
    ↑minstretN ⊆ E →
    minstret_inv -∗
    (∀ σ ns κs nt, state_interp σ ns κs nt -∗ minstret_inv_body
         ={E ∖ ↑minstretN, Ei}=∗
       ∃ σ', ⌜exec riscv_step σ = Some (tt, σ')⌝ ∗
          ▷ (|={Ei, E ∖ ↑minstretN}=>
               state_interp σ' (S ns) κs nt ∗ minstret_inv_body ∗
               WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN) "#Hinv H".
    iApply wp_exec_step.
    iIntros (σ ns κs nt) "Hsi".
    (* open the minstret invariant ([={E, E∖↑minstretN}]); the caller's fupd
       supplies [={E∖↑minstretN, Ei}], and a [fupd_mask_intro] bridges [Ei→∅] to
       meet [wp_exec_step]'s [={E,∅}] obligation. *)
    iInv "Hinv" as ">Hbody" "Hclose".
    iMod ("H" $! σ ns κs nt with "Hsi Hbody") as (σ') "[%Hexec Hk]".
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
  Lemma wp_exec_step_hart_active_inv E Φ {dq : dfrac} :
    ↑minstretN ⊆ E →
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    (∀ σ ns κs nt,
       state_interp σ ns κs nt ={E ∖ ↑minstretN}=∗
       ∃ (retval : mword 32) (s_exec : mstate),
         ⌜ exec (run_hart_active 0) σ
             = Some (Step_Execute (RETIRE_SUCCESS, retval), s_exec) ⌝ ∗
         PC ↦ᵣ (register_lookup PC s_exec.(sregs)) ∗
         state_interp s_exec ns κs nt ∗
         (hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
          PC ↦ᵣ (register_lookup nextPC s_exec.(sregs)) -∗
          ▷ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN) "#Hinv Hhs H".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) Φ HN with "Hinv").
    iIntros (σ ns κs nt) "[Hreg Hmem] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    (* should_inc returns SOME [b]; we neither know nor care which *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    (* PRE: minstret_increment := b (cell borrowed from the invariant) *)
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    iMod ("H" $! (set_reg σ (R_bool minstret_increment) b) ns κs nt with "[Hreg Hmem]")
      as (retval s_exec) "(%Hha & Hpc & [Hreg Hmem] & Hcont)".
    { unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
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
      iModIntro. cbn [sregs mem]. rewrite Hmst_tick.
      unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi".
      { iExists (add_vec_int mst 1), true. iFrame. }
      iExact "HWP".
    - iModIntro. iExists _. iSplitR.
      { iPureIntro.
        exact (exec_riscv_step_hart_active σ s_exec retval false
                 Hsi Hhart_a Hha Hhart_exec Hmi_exec). }
      iNext.
      iModIntro. unfold set_reg; cbn [sregs mem]. iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi".
      { iExists mst, false. iFrame. }
      iExact "HWP".
  Qed.

End MinstretInv.
