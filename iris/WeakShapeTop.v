(** * WeakShapeTop.v — the top of the shape tower, and what is still owed

    The plan for this file was
        [Theorem riscv_step_shaped : ∀ b, sail_shaped (riscv_step b)]
        [Theorem riscv_step_live   : ∀ b, sail_live   (riscv_step b)]
    at the top of the generated tower ([WeakShapeGen01..15.v]), closing
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
    §3  WHAT *IS* ASSEMBLED — SINCE STAGE C5, THE WHOLE GENERATED TOWER.
    [tools/gen_shape.py] emits [gwalk None] — [WeakSailLTS.sail_shaped]
    generalised to an arbitrary monad type, by [WeakShape.gwalk_shaped] — for
    all 294 generatable monadic definitions [rv64d.try_step] reaches
    ([WeakShapeGen01..15.v], machine-checked here); the 51-function residue is
    exactly the up-cone of the two memory leaves and of the three axioms
    above, plus [_rec_pt_walk] and [check_leaf_pte].  The shards form a
    [Require] chain (the hint database is the dependency mechanism), so they
    cannot be built in parallel; a 48-lemma shard costs 7–30 minutes of
    [coqc] on this tree, the cost rising up the topological order, and the
    extension-enum dispatches ([currentlyEnabled] and its callers) dominate.

    THE TOWER HAS EXACTLY ONE MODE, and that is the C5 scheduling lesson
    (finding (O7)): every shard proves [gwalk None], which does NOT imply
    [gsilent]/[WeakShapeOverrides2.gpost] (it permits memory events) and says
    nothing about [glive].  Neither the postcondition sweep §4 (b) needs nor
    the liveness half can reuse it — each would have to regenerate the whole
    serial chain in its own mode.  A GENERATED SWEEP MUST EMIT EVERY MODE IT
    WILL EVER NEED IN ONE PASS.

    ------------------------------------------------------------------------
    §4  THE WRAPPER, AND EXACTLY WHAT IS LEFT — NOW A LIST OF TWELVE.

    [RiscvLang.riscv_step tick = try_step 0 false >>= λ _, if tick then
    tick_clock tt else returnm tt].  [tick_clock] is discharged outright
    ([WeakShapePeel.gw_tick_clock]), and with the tower complete the three
    functions between [try_step] and the memory cone ([try_step],
    [run_hart_active], [execute]) are ordinary [cbv] + [gw_solve] modulo their
    residue callees ([WeakShapePeel]).  So [riscv_step_shaped_residue] below
    reduces the whole [∀ b] premise of [WeakComposeLang]'s capstones to TWELVE
    one-line facts: [fetch] and the eleven memory [execute_*] clauses.

    WHY THOSE TWELVE ARE NOT DISCHARGED, in the order a C6 must attack them:

      (a) ONE OF THEM IS FALSE AS STATED — finding (O6).  Sail's
          [(0 <? width) && (width <=? 4096)] precondition is a COMMENT and
          [word_width] is [Z], so [execute_STORE imm rs2 rs1 0] is a
          well-typed instance and the model issues a ZERO-WIDTH [MemWrite] on
          it, which no shape predicate admits
          ([WeakShapeOverrides2.gwalk_write_ram_zero_False]).  The [∀ ast]
          form is unavoidable — [run_hart_active] applies [execute] to
          [ext_decode]'s output and to the [ExecuteAs] redirection VALUE, and
          neither is syntax — so what closes it is a DECODER POSTCONDITION,
          [gpost] of [encdec_backwards] with "every width field is in
          [[1;2;4;8]]".  [sail_shaped (riscv_step b)] itself is not refuted;
          the compositional ROUTE is.
      (b) THE MEMORY CONE then needs the same [gpost] machinery twice more:
          [0 < split_width] (DISCHARGED in [WeakShapeOverrides2] §2, given
          [0 < width] — which is (a)), and the EXCLUSIVE WINDOW, which needs
          [gpost] of [pmaCheck] ([LoadReserved]/[StoreConditional]/[Atomic]
          answer [CannotSplit], so [split_misaligned] returns [N = 1] and the
          window is opened at most once — otherwise the loop's second
          [read_ram] falls into [gwalk (Some _)]'s [MemRead] arm, which is
          [False]).  The fuel recursion [_rec_pt_walk] is DISCHARGED
          ([WeakShapeOverrides2] §3).
      (c) THE THREE AXIOMS of §2, via [gw_load_reservation] /
          [gw_cancel_reservation] / [gw_plat_term_write] — the record is
          consumed inside (b)'s proofs, at [vmem_read_addr],
          [execute_STORECON] and [htif_store], not at §4's statement. *)

From stdpp Require Import gmap finite list relations.
From Stdlib.ssr Require Import ssreflect.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
From xv6iris Require Import WeakSailLTS WeakSailComplete WeakShape.
From xv6iris Require Import WeakShapeOverrides WeakShapeOverrides2.
From xv6iris Require Import WeakShapeGen01 WeakShapeGen02 WeakShapeGen03
  WeakShapeGen04 WeakShapeGen05 WeakShapeGen06 WeakShapeGen07 WeakShapeGen08
  WeakShapeGen09 WeakShapeGen10 WeakShapeGen11 WeakShapeGen12 WeakShapeGen13
  WeakShapeGen14 WeakShapeGen15.
From xv6iris Require Import WeakShapePeel.
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

(** TWO OF THE RESIDUE'S FIFTY-ONE, CLOSED HERE, because they are exactly
    the functions whose only obstacle was [plat_term_write]: the HTIF store
    path.  [htif_store] is the axiom's single call site and [mmio_write] is
    its only caller, so the record above is the whole of what they needed —
    every other leaf is in the generated tower. *)
Lemma gw_htif_store (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2, gwalk None (@htif_store a0 a1 a2).
Proof.
  pose proof (gw_plat_term_write H) as Hterm.
  intros; destruct a0; cbv [htif_store]; gw_solve.
Qed.

Lemma gw_mmio_write (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2, gwalk None (@mmio_write a0 a1 a2).
Proof.
  pose proof (gw_htif_store H) as Hh.
  intros; cbv [mmio_write]; gw_solve.
Qed.

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
  ∀ b : bool, sail_shaped (riscv_step b).
Proof.
  intros Htry b. apply gwalk_shaped.
  rewrite /riscv_step. apply gwalk_bind; [apply Htry|].
  intros _. destruct b; [apply gw_tick_clock|by apply gwalk_quiet, gquiet_returnm].
Qed.

(** …AND THE SAME PREMISE PEELED TO THE RESIDUE.  This is the honest
    statement of what stage C5 leaves owed: not "a property of the decoder"
    but twelve named model functions, each of which is one line.  Eleven of
    them are the memory [execute_*] clauses and one is [fetch]; §4's header
    (a) says which of the eleven is FALSE as stated and what replaces it. *)
Theorem riscv_step_shaped_residue
    (Hfetch : ∀ a0, gwalk None (@fetch a0))
    (Hexecute_LOAD : ∀ a0 a1 a2 a3 a4, gwalk None (@execute_LOAD a0 a1 a2 a3 a4))
    (Hexecute_STORE : ∀ a0 a1 a2 a3, gwalk None (@execute_STORE a0 a1 a2 a3))
    (Hexecute_LOADRES : ∀ a0 a1 a2 a3 a4, gwalk None (@execute_LOADRES a0 a1 a2 a3 a4))
    (Hexecute_STORECON : ∀ a0 a1 a2 a3 a4 a5,
        gwalk None (@execute_STORECON a0 a1 a2 a3 a4 a5))
    (Hexecute_AMO : ∀ a0 a1 a2 a3 a4 a5 a6,
        gwalk None (@execute_AMO a0 a1 a2 a3 a4 a5 a6))
    (Hexecute_SSAMOSWAP : ∀ a0 a1 a2 a3 a4 a5,
        gwalk None (@execute_SSAMOSWAP a0 a1 a2 a3 a4 a5))
    (Hexecute_SSPUSH : ∀ a0, gwalk None (@execute_SSPUSH a0))
    (Hexecute_SSPOPCHK : ∀ a0, gwalk None (@execute_SSPOPCHK a0))
    (Hexecute_ZICBOM : ∀ a0 a1, gwalk None (@execute_ZICBOM a0 a1))
    (Hexecute_ZICBOP : ∀ a0 a1 a2, gwalk None (@execute_ZICBOP a0 a1 a2))
    (Hexecute_ZICBOZ : ∀ a0, gwalk None (@execute_ZICBOZ a0)) :
  ∀ b : bool, sail_shaped (riscv_step b).
Proof.
  apply riscv_step_shaped_cone, gw_try_step, gw_run_hart_active; [done|].
  by apply gw_execute.
Qed.

(** The same reduction in the [gok] mode, for the liveness half: [glive] has
    no [Ret]-mode subtlety, so the two halves reduce in lockstep at the
    wrapper.  BELOW the wrapper they do NOT: the generated tower is
    [gwalk None]-only (§3), so this premise cannot be peeled to the residue
    the way [riscv_step_shaped_residue] is — a liveness half needs its own
    294-lemma [gok] tower FIRST, and only then the ~100 reachability sites of
    (O3).  That ordering is finding (O7), and it is why the [gok] statement
    still names both frontier functions. *)
Theorem riscv_step_ok_cone :
  (∀ (n : Z) (b : bool), gok (try_step n b)) →
  gok (tick_clock tt) →
  ∀ b : bool, sail_shaped (riscv_step b) ∧ sail_live (riscv_step b).
Proof.
  intros Htry Htick b. apply gok_stageC.
  rewrite /riscv_step. apply gok_bind; [apply Htry|].
  intros _. destruct b; [exact Htick|apply gok_returnm].
Qed.
