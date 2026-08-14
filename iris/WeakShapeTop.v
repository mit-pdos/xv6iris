(** * WeakShapeTop.v — THE TOP OF THE SHAPE TOWER

        [Theorem riscv_step_shaped_ax :
           rv64d_axiom_shapes → ∀ b, sail_shaped (riscv_step b)]

    That is stage C8's deliverable and the whole point of the tower: the
    SHAPE half of [WeakCompose] §6's seam (6) is no longer a premise of
    [WeakComposeLang]'s capstones but a theorem, over the one assumption the
    model genuinely does not state about itself (§1).  The LIVENESS half
    stays a premise, and §3 says why it cannot be stated as [∀ b] at all.

    ------------------------------------------------------------------------
    §1  WHAT IS ASSUMED, AND IT IS ONE RECORD OF THREE LINES.

    [WeakShapeMem.rv64d_axiom_shapes] — [gquiet] of [load_reservation],
    [cancel_reservation] and [plat_term_write], the three [Axiom]s of MONAD
    TYPE that [rv64d] declares and that are reachable from [try_step]
    ([vmem_read_addr], [execute_STORECON], [htif_store]).  Nothing about an
    opaque constant's shape is provable OR refutable, so this is irreducible
    at the Coq level; the alternative is to give the three definitions in
    [model-xv6iris/riscv_extras.v], which moves the same assumption into the
    model.  It is a [Record], NOT a set of [Axiom]s, precisely so that the
    capstones' [Print Assumptions] stays at the five rv64d axioms it already
    reports.  (Finding (O5), stage C3.)

    ------------------------------------------------------------------------
    §2  WHAT IS PROVED, AND WHERE — THE WHOLE ASSEMBLY IN ONE LIST.

      [WeakShape] / [WeakShapeOverrides] / [WeakShapeOverrides2]
          the compositional kit: [gwalk] (= [sail_shaped] generalised to any
          monad type, [gwalk_shaped]), [gquiet], [gsilent], [gpost], the
          combinator lemmas and the sweep tactics.
      [WeakShapeGen01..15]   the GENERATED tower: [gwalk] for all 294 monadic
          definitions [try_step] reaches whose cone touches neither memory
          leaf nor an opaque axiom ([tools/gen_shape.py], [make gen-shape];
          ~5 min of [coqc], a serial [Require] chain).
      [WeakShapeAst] / [WeakShapeDec]   the DECODER POSTCONDITION: [ast_wf]
          ("every width field the decoder builds is positive") for
          [ext_decode] and [ext_decode_compressed], state-generic.
      [WeakShapeWin]   [gwp], the value mode, and [gwx] = [gwp] at [exres_wf].
      [WeakShapeExecGen01..03]   the GENERATED value sweep (116 lemmas).
      [WeakShapeMem]   THE MEMORY CONE: the 51-function residue, from
          [read_ram]/[write_ram] up to [fetch], plus the axiom record itself.
      [WeakShapeExec]  [execute] and [run_hart_active], where the decoder
          postcondition crosses into [execute]'s obligation and the
          [ExecuteAs] redirection is discharged.
      [WeakShapePeel]  [try_step] and [tick_clock].

    ------------------------------------------------------------------------
    §3  WHY THE LIVENESS HALF IS NOT HERE.

    [∀ b, sail_live (riscv_step b)] is REFUTABLE as stated — finding (O9):
    [glive] forbids a raised Sail exception outright, and
    [rv64d.zicfiss_xSSE] raises one at [VirtualSupervisor], a value the
    [RegRead] arm quantifies over.  Its honest form is STATE-CONDITIONED
    ([sail_live] under a register-state precondition: xv6 runs with the H
    extension off, so [cur_privilege] is never [VirtualSupervisor]), which is
    exactly why it cannot be a [∀ b] fact, and settling that precondition
    comes BEFORE generating a [gok] tower — the mode question is finding
    (O7): a generated sweep must emit every mode it will ever need in one
    pass, and [gwalk] implies neither [gpost] nor [glive].  Behind it sit the
    ~100 [exit]/[internal_error]/[assert_exp] reachability sites of (O3).
    [riscv_step_ok_cone] below is the reduction that a liveness half would
    plug into, kept for that purpose.

    ------------------------------------------------------------------------
    §4  THE FIVE FINDINGS IT TOOK, in one paragraph each, because the SHAPE
    of them recurs and four of the five were REFUTATIONS OF THE PREMISE THIS
    FILE NOW PROVES.  All five are written up at their sites and in
    [claude-notes/projects/weak-memory-premises.md].

      (O2)  an exclusive read with NO conditional write (a bare [lr], a
            failing [sc], a faulting AMO).  C2 legalised it by BRACKETING the
            abandoned window in [sail_mstep].
      (O4)  the mirror: a conditional write with NO exclusive read (a
            standalone [sc]; the lr/sc reservation lives in the model's pure
            axioms, so the matching [lr] is a different [riscv_step]).  C4
            dropped the [ak_latest = false] conjunct from the window-closed
            [MemWrite] arms — the write became an ordinary [LStore].
      (O6)  the decoder's ZERO WIDTH: Sail's [0 < width ≤ 4096] precondition
            is emitted as a COMMENT and [word_width] is [Z], so
            [execute_STORE imm rs2 rs1 0] is a well-typed instruction on
            which the model issues a zero-width [MemWrite].  C6 answered it
            with the decoder postcondition ([WeakShapeAst]/[WeakShapeDec]),
            C7 CONSUMED it at [run_hart_active] ([WeakShapeExec]).
      (O9)  a RAISED SAIL EXCEPTION is a dead end, not a continuation:
            [ExtraOutcome] is indexed by the monad's own return type, so the
            old [∀ r, …] arm walked the rest of the instruction at every
            value of the thrown-at type.  Arm := [True].
      (O10) THE ONE THAT DELETED THE WINDOW.  [update_and_write_pte] — on the
            path of every memory instruction and of the fetch, since every
            one of them translates — abandons an exclusive PTE reservation
            DEEP INSIDE [translate], so C2's "the abandoned tail is silent"
            bracket did not apply and the instruction's own data access fell
            inside an open window.  C8 took the same narrowing (O4) had
            taken, on the read side: [sail_shaped]'s [MemRead] arm dropped
            the window, [amo_tail] was deleted, and the bare arm became the
            ORDINARY load arm.  THE KIT COLLAPSED WITH IT — the window index
            left [gwalk], [gwalkx] disappeared, and the memory cone lost its
            hardest obligation (the read/write address-and-width agreement,
            which had needed [pmaCheck]'s [CannotSplit] postcondition and an
            [untilMT] unfolding at [N = 1]).  Which is why [WeakShapeMem] is
            a 700-line file and not a stage of its own.

    THE GENERAL RULE THE FIVE SHARE: an arm of a shape predicate that
    demands more than the machine enforces is a silent, unbounded
    strengthening, and the repair is always to NARROW THE ARM — never to add
    an index, and never to have the predicate describe a multi-step protocol
    the run's own evidence already pins down. *)

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
From xv6iris Require Import WeakShapeAst WeakShapeWin WeakShapeDec.
From xv6iris Require Import WeakShapeMem WeakShapeExec.
From xv6iris Require Import WeakShapePeel.
Require Import Riscv.rv64d.

Set Default Proof Using "Type".

(* ====================================================================== *)
(** ** 5. The [riscv_step] wrapper

    [RiscvLang.riscv_step tick = try_step 0 false >>= λ _, if tick then
    tick_clock tt else returnm tt], and [WeakSailLTS.sail_shaped] is [gwalk]
    at [M unit] ([WeakShape.gwalk_shaped]), so the wrapper contributes only a
    [bind] and a [bool] test. *)

Require Import RiscvLang.

Theorem riscv_step_shaped_cone :
  (∀ (n : Z) (b : bool), gwalk (try_step n b)) →
  ∀ b : bool, sail_shaped (riscv_step b).
Proof.
  intros Htry b. apply gwalk_shaped.
  rewrite /riscv_step. apply gwalk_bind; [apply Htry|].
  intros _. destruct b; [apply gw_tick_clock|by apply gwalk_quiet, gquiet_returnm].
Qed.

(** THE THEOREM.  Everything between [riscv_step] and the two memory leaves
    is machine-checked; the record is what is left. *)
Theorem riscv_step_shaped_ax (H : rv64d_axiom_shapes) :
  ∀ b : bool, sail_shaped (riscv_step b).
Proof.
  apply riscv_step_shaped_cone, gw_try_step, (gw_run_hart_active_ax H).
Qed.

(** The reduction the LIVENESS half would plug into (§3): [glive] has no
    [Ret]-mode subtlety, so the two halves reduce in lockstep AT THE WRAPPER.
    Below it they do not — the generated tower is [gwalk]-only (finding
    (O7)) — which is why this statement still names both frontier
    functions. *)
Theorem riscv_step_ok_cone :
  (∀ (n : Z) (b : bool), gok (try_step n b)) →
  gok (tick_clock tt) →
  ∀ b : bool, sail_shaped (riscv_step b) ∧ sail_live (riscv_step b).
Proof.
  intros Htry Htick b. apply gok_stageC.
  rewrite /riscv_step. apply gok_bind; [apply Htry|].
  intros _. destruct b; [exact Htick|apply gok_returnm].
Qed.
