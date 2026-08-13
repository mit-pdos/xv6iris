(** * WeakShapeTop.v — what stage C3 can and cannot assemble

    The plan for this file was
        [Theorem riscv_step_shaped : ∀ b, sail_shaped (riscv_step b)]
        [Theorem riscv_step_live   : ∀ b, sail_live   (riscv_step b)]
    at the top of the generated tower ([WeakShapeGen01..07.v]), closing
    [WeakCompose] §6's seam (6) and deleting both premises from
    [WeakComposeLang.xv6_weak_robust_lifted]/[_adequate].  NEITHER IS
    PROVABLE, and this file records the two reasons in the form the next
    stage needs them: a REFUTATION (§1, machine-checked in
    [WeakShapeOverrides] §5) and a RECORD OF ASSUMPTIONS (§2, a [Record]
    rather than [Axiom]s, so that nothing here enters
    [Print Assumptions]).

    ------------------------------------------------------------------------
    §1  (O4) — [∀ b, sail_shaped (riscv_step b)] IS FALSE.

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
    memory event, and the matching [lr] is a different [riscv_step].
    [sail_shaped]'s window-closed [MemWrite] arm demands
    [ak_latest (classify …) = false] off device addresses, so it is false at
    every [sc] to normal memory.  Machine-checked at the leaf:
    [WeakShapeOverrides.gwalk_write_ram_con_False] and
    [WeakShapeOverrides.sail_shaped_write_ram_con_False].

    This is the MIRROR of stage C1's (O2) — which found the read side (an
    exclusive read with no conditional write) and which C2 fixed by
    weakening [amo_tail]'s [Interface.Ret] arm and adding [sail_mstep]'s
    BARE EXCLUSIVE-READ arm.  The write side needs the symmetric fix, and it
    is a specification change of the same size, not a sweep change; the
    ordered plan is in [claude-notes/projects/weak-memory-premises.md].

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
    of remaining obligations. *)

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
    once (O4)'s LTS fix lands. *)
Lemma gsilent_cancel_reservation (H : rv64d_axiom_shapes) u :
  gsilent (cancel_reservation u).
Proof. by apply gquiet_gsilent, (ax_cancel_reservation H). Qed.
