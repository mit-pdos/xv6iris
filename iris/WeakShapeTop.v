(** * WeakShapeTop.v — the top of the shape tower, and what is still owed

    The plan for this file was
        [Theorem riscv_step_shaped : ∀ b, sail_shaped (riscv_step b)]
        [Theorem riscv_step_live   : ∀ b, sail_live   (riscv_step b)]
    at the top of the generated tower ([WeakShapeGen01..07.v]), closing
    [WeakCompose] §6's seam (6) and deleting both premises from
    [WeakComposeLang.xv6_weak_robust_lifted]/[_adequate].  Stage C3 found
    both FALSE/blocked for two reasons; stage C4 fixed the first by changing
    the specification (§1) and the second is irreducible (§2).  What this
    file therefore holds is: the history of (O4) as the shape of a recurring
    finding (§1), the RECORD OF ASSUMPTIONS about the model's own monadic
    axioms (§2 — a [Record], not [Axiom]s, so that nothing here enters
    [Print Assumptions]), the sweep's coverage (§3), and §4, the
    [riscv_step] wrapper reduced to the tower's remaining obligations —
    which is exactly the list stage C5 owes.

    ------------------------------------------------------------------------
    §1  (O4) — WAS THE REFUTATION; FIXED IN STAGE C4 BY A SPECIFICATION
        CHANGE, so this section is now history plus the shape of the fix.

    [rv64d.execute_STORECON] (an [sc.w]/[sc.d]) issues

        vmem_write … (con := true)
          → mem_write_value … (con := true)
          → mem_write_value_priv_meta … (con := true)
          → checked_mem_write … (con := true)
          → write_kind_of_flags aq rl true = Write_RISCV_conditional[_release]
          → write_ram Write_RISCV_conditional (Physaddr paddr) split_width …

    i.e. a [MemWrite] whose access kind is [AV_exclusive] — [ak_latest =
    true] — and NO exclusive [MemRead] occurs anywhere in that instruction:
    the lr/sc reservation lives in the model's PURE axioms
    ([load_reservation]/[match_reservation]/[valid_reservation]), not in a
    memory event, and the matching [lr] is a different [riscv_step].  Through
    stage C3 [sail_shaped]'s window-closed [MemWrite] arm demanded
    [ak_latest (classify …) = false] off device addresses, so the fact was
    false at every [sc] to normal memory.

    STAGE C4 TOOK THE MIRROR OF C2's (O2) FIX ([WeakSailLTS] delta (e'')):
    the window-closed [MemWrite] arms of [sail_shaped], [sail_mstep] and the
    kit's [gwalk]/[gwalkx] accept ANY RAM write of nonzero width, so a
    standalone conditional write is shaped and steps as a plain
    [WeakPromise.LStore] — one step, no bracket, since there is no open
    window to abandon.  The two refutations that stood in
    [WeakShapeOverrides] §5 are false now and are replaced by the positive
    leaves [WeakShape.gwalk_write_ram_con] /
    [WeakShapeOverrides.gwalkx_write_ram_con].  The ⇐ cost went into the
    predicate that already pays for (O2): [WeakSailLTS2.pf_solo_f] also
    forbids stepping from a conditional-write node, so [fused_blk] reads
    "every exclusive access of the block is part of a fused rmw" — no new
    premise anywhere.

    ------------------------------------------------------------------------
    §2  (O5) — three of [rv64d]'s [Axiom]s are MONADIC.

    [load_reservation], [cancel_reservation] and [plat_term_write] are
    declared [Axiom … : M unit] and all three are reachable from [try_step]
    ([vmem_read_addr], [execute_STORECON], [htif_store] respectively).  An
    opaque constant of monad type has no shape: nothing about it is provable
    OR refutable.  So even with §1 fixed, the two [∀ b] facts cannot be
    closed from the model as generated.

    [rv64d_axiom_shapes] below is the honest statement of what must be
    assumed instead.  It is a [Record], NOT a set of [Axiom]s, precisely so
    that the capstones' [Print Assumptions] stays at the five rv64d axioms
    it already reports; the intended end state is that
    [xv6_weak_robust_lifted]/[_adequate] take this record IN PLACE OF the two
    [∀ b] premises, which is a strictly smaller and locally checkable
    obligation (three one-line facts about three extern functions, versus a
    property of the whole decoder).  The alternative is to give the three
    axioms definitions in [model-xv6iris/riscv_extras.v], which moves the
    same assumption into the model.

    ------------------------------------------------------------------------
    §3  WHAT *IS* ASSEMBLED.  [tools/gen_shape.py] can generate
    [gwalk None] — [WeakSailLTS.sail_shaped] generalised to an arbitrary
    monad type, by [WeakShape.gwalk_shaped] — for 294 of the 341 monadic
    definitions [rv64d.try_step] reaches; the 47-function residue is exactly
    the up-cone of the two memory leaves and of the three axioms above, plus
    [_rec_pt_walk].  [WeakShapeGen01..02.v] are the first 96 of that
    topological order, machine-checked here.  THE CUT IS A COMPILE-TIME
    BUDGET, NOT A DIFFICULTY BOUNDARY: the shards form a [Require] chain
    (the hint database is the dependency mechanism), so they cannot be built
    in parallel, and a 48-lemma shard costs ~10 minutes of [coqc] on this
    tree — the extension-enum dispatches ([currentlyEnabled] and its
    callers) dominate.  Raise [gen_shape.py]'s [--limit] and regenerate when
    there is a build budget for it; [make gen-shape] lists exactly which
    functions are below the cut.

    Even capped, that is what turns seam (6) from an estimate ("a syntactic
    analysis of thousands of generated branches") into a bounded, named list
    of remaining obligations.

    ------------------------------------------------------------------------
    §4  [riscv_step_shaped_cone]: THE WRAPPER, AND EXACTLY WHAT IS LEFT.

    [RiscvLang.riscv_step tick = try_step 0 false >>= λ _, if tick then
    tick_clock tt else returnm tt], so the [∀ b] premise reduces to
    [gwalk None] of TWO model functions — and those two are precisely where
    the residue starts.  §4 proves that reduction; the two hypotheses are the
    honest statement of what stage C5 owes, and neither is a ∀-path premise
    about anything but the model's own code.

    WHY THEY ARE NOT DISCHARGED HERE, in the order a C5 must attack them:

      (a) THE GENERATED TOWER IS CAPPED AT 96 OF 294 (§3), and every function
          between [try_step] and the memory leaves calls into the capped part
          ([try_step] alone needs [should_inc_minstret], [run_hart_waiting],
          [handle_interrupt], [handle_exception], [exception_handler],
          [set_next_pc]).  So no bridge lemma above the memory cone can be
          stated, let alone proved, before the remaining ~198 generated
          lemmas exist.  That is a serial multi-hour [coqc] chain, not a
          difficulty.
      (b) THE 47-FUNCTION RESIDUE then needs hand proofs, and three of its
          obligations are SEMANTIC rather than syntactic: [0 < split_width]
          in [checked_mem_write] (the nonzero-width conjunct — [split_width]
          comes from [split_misaligned], which returns [width] itself on the
          unsplit path, so it is the Sail precondition [0 < width ≤ 4096]
          travelling down); the fuel recursion [_rec_pt_walk]; and the
          EXCLUSIVE WINDOW carried from [checked_mem_read]'s [read_ram] to
          [checked_mem_write]'s [write_ram] through
          [catch_early_return]/[liftR]/[untilMT], which is what
          [WeakShapeOverrides] §3's escape index ([gwalkx]/[gsilent]) was
          built to compose.  Stage C4's (O4) fix removed one obligation from
          this list outright: a standalone conditional write no longer needs
          a window at all.
      (c) THE THREE AXIOMS of §2, via [gw_load_reservation] /
          [gw_cancel_reservation] / [gw_plat_term_write] — i.e. the record is
          consumed inside (b)'s proofs, at [vmem_read_addr],
          [execute_STORECON] and [htif_store], not at §4's statement. *)

From stdpp Require Import gmap finite list relations.
From Stdlib.ssr Require Import ssreflect.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
From xv6iris Require Import WeakSailLTS WeakSailComplete WeakShape.
From xv6iris Require Import WeakShapeOverrides.
From xv6iris Require Import WeakShapeGen01 WeakShapeGen02.
Require Import Riscv.rv64d.

Set Default Proof Using "Type".

(** The three shape facts the model does not state about its own monadic
    axioms.  [gquiet] (not merely [gwalk None]) is the right strength: these
    are extern hooks that touch no memory and raise nothing, so they must
    also be crossable by an open exclusive window — [cancel_reservation] is
    called by [execute_STORECON] AFTER its conditional write, i.e. inside the
    instruction's tail. *)
Record rv64d_axiom_shapes : Prop := {
  ax_load_reservation :
    ∀ (a : Values.mword (if 64 =? 32 then 34 else 64)%Z) (n : Z),
      gquiet (load_reservation a n);
  ax_cancel_reservation : ∀ u, gquiet (cancel_reservation u);
  ax_plat_term_write : ∀ (b : Values.mword 8), gquiet (plat_term_write b);
}.

(** …and what they buy at the leaves, in the sweep's own vocabulary. *)
Lemma gw_load_reservation (H : rv64d_axiom_shapes) a n :
  gwalk None (load_reservation a n).
Proof. by apply gwalk_quiet, (ax_load_reservation H). Qed.

Lemma gw_cancel_reservation (H : rv64d_axiom_shapes) u :
  gwalk None (cancel_reservation u).
Proof. by apply gwalk_quiet, (ax_cancel_reservation H). Qed.

Lemma gw_plat_term_write (H : rv64d_axiom_shapes) b :
  gwalk None (plat_term_write b).
Proof. by apply gwalk_quiet, (ax_plat_term_write H). Qed.

(** The window-crossing form, which is what [execute_STORECON]'s tail needs
    (it calls [cancel_reservation] AFTER the conditional write). *)
Lemma gsilent_cancel_reservation (H : rv64d_axiom_shapes) u :
  gsilent (cancel_reservation u).
Proof. by apply gquiet_gsilent, (ax_cancel_reservation H). Qed.

Lemma gsilent_load_reservation (H : rv64d_axiom_shapes) a n :
  gsilent (load_reservation a n).
Proof. by apply gquiet_gsilent, (ax_load_reservation H). Qed.

Lemma gsilent_plat_term_write (H : rv64d_axiom_shapes) b :
  gsilent (plat_term_write b).
Proof. by apply gquiet_gsilent, (ax_plat_term_write H). Qed.

(* ====================================================================== *)
(** ** 4. The [riscv_step] wrapper, over the tower's remaining obligations

    [WeakSailLTS.sail_shaped] is [gwalk None] at [M unit]
    ([WeakShape.gwalk_shaped]), so the whole [∀ b] premise of
    [WeakComposeLang]'s capstones is the shape of [try_step] plus the shape
    of [tick_clock] — the two functions §4's header names as C5's frontier.
    Nothing else about the decoder is involved: the wrapper contributes only
    a [bind] and a [bool] test. *)

Require Import RiscvLang.

Theorem riscv_step_shaped_cone :
  (∀ (n : Z) (b : bool), gwalk None (try_step n b)) →
  gwalk None (tick_clock tt) →
  ∀ b : bool, sail_shaped (riscv_step b).
Proof.
  intros Htry Htick b. apply gwalk_shaped.
  rewrite /riscv_step. apply gwalk_bind; [apply Htry|].
  intros _. destruct b; [exact Htick|by apply gwalk_quiet, gquiet_returnm].
Qed.

(** The same reduction in the [gok] mode, for the liveness half: [glive] has
    no [Ret]-mode subtlety, so the two halves reduce in lockstep and a C5
    that closes [gok] of the two frontier functions closes both premises of
    [WeakComposeLang.xv6_weak_robust_lifted] at once. *)
Theorem riscv_step_ok_cone :
  (∀ (n : Z) (b : bool), gok (try_step n b)) →
  gok (tick_clock tt) →
  ∀ b : bool, sail_shaped (riscv_step b) ∧ sail_live (riscv_step b).
Proof.
  intros Htry Htick b. apply gok_stageC.
  rewrite /riscv_step. apply gok_bind; [apply Htry|].
  intros _. destruct b; [exact Htick|apply gok_returnm].
Qed.
