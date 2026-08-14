(** * WeakShapePeel.v — the tower's TOP THREE FUNCTIONS, and the frontier

    [WeakShapeGen01..15.v] cover all 294 generatable monadic definitions
    [rv64d.try_step] reaches.  What sits between them and
    [WeakShapeTop.riscv_step_shaped_cone] is a short PEEL: the three
    functions on the path from [try_step] down to the memory cone
    ([try_step], [run_hart_active], [execute]) plus the clock tick, each
    stated MODULO its residue callees.  Every one of them is an ordinary
    [cbv] + [gw_solve], because the generated tower supplies every other
    leaf — that is exactly what the tower bought.

    The peel is what turns "the two [∀ b] premises" into a NAMED, MINIMAL
    frontier:

      [gwalk (tick_clock tt)]        — DISCHARGED here, outright.
      [gwalk (try_step n b)]         — reduced to [run_hart_active],
      [gwalk (run_hart_active n)]    — reduced to [fetch] + [execute],
      [∀ ast, gwalk (execute ast)]   — reduced to the ELEVEN memory
                                            execute clauses.

    and those eleven, plus [fetch], are precisely the residue.  Stage C5's
    finding (O6) — see [WeakShapeOverrides2] §4 — is about the LAST of these
    four: [execute]'s argument is an arbitrary [instruction] (both
    [ext_decode]'s output and the [ExecuteAs] redirection are values, not
    syntax), the AST's width fields are plain [Z] (Sail's
    [member_Z_list width [1;2;4;8]] is a COMMENT), and a zero width makes the
    model issue a zero-width [MemWrite], which no shape predicate admits.  So
    [Hexecute_STORE] below — [∀ a0 a1 a2 a3, gwalk (execute_STORE …)] —
    is FALSE as stated, and what C6 owes is the decoder postcondition that
    replaces it.  The peel is stated with the hypothesis anyway, because that
    is what makes the obligation a one-line, checkable statement instead of a
    property of the whole model.

    COVERAGE NOTE (a C5 finding): [tools/gen_shape.py]'s call graph is rooted
    at [try_step] ALONE, but [RiscvLang.riscv_step] also calls
    [rv64d.tick_clock], whose cone contributes two monadic definitions
    ([tick_clock], [should_inc_mcycle]) that no shard therefore covers.  They
    are proved here.  Rooting the generator at both would fix it at the cost
    of renumbering — hence rebuilding — every shard. *)

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
Require Import Riscv.rv64d.

Set Default Proof Using "Type".

(* ====================================================================== *)
(** ** 1. The clock tick — outright, no residue below it *)

Lemma gw_should_inc_mcycle : ∀ a0, gwalk (@should_inc_mcycle a0).
Proof. intros; cbv [should_inc_mcycle]; gw_solve. Qed.
#[export] Hint Resolve gw_should_inc_mcycle : gshape.

Lemma gw_tick_clock : ∀ a0, gwalk (@tick_clock a0).
Proof. intros; destruct a0; cbv [tick_clock]; gw_solve. Qed.
#[export] Hint Resolve gw_tick_clock : gshape.

(* ====================================================================== *)
(** ** 2. [execute], modulo its eleven memory clauses *)

Lemma gw_execute
    (Hexecute_LOAD : ∀ a0 a1 a2 a3 a4, gwalk (@execute_LOAD a0 a1 a2 a3 a4))
    (Hexecute_STORE : ∀ a0 a1 a2 a3, gwalk (@execute_STORE a0 a1 a2 a3))
    (Hexecute_LOADRES : ∀ a0 a1 a2 a3 a4, gwalk (@execute_LOADRES a0 a1 a2 a3 a4))
    (Hexecute_STORECON : ∀ a0 a1 a2 a3 a4 a5,
        gwalk (@execute_STORECON a0 a1 a2 a3 a4 a5))
    (Hexecute_AMO : ∀ a0 a1 a2 a3 a4 a5 a6,
        gwalk (@execute_AMO a0 a1 a2 a3 a4 a5 a6))
    (Hexecute_SSAMOSWAP : ∀ a0 a1 a2 a3 a4 a5,
        gwalk (@execute_SSAMOSWAP a0 a1 a2 a3 a4 a5))
    (Hexecute_SSPUSH : ∀ a0, gwalk (@execute_SSPUSH a0))
    (Hexecute_SSPOPCHK : ∀ a0, gwalk (@execute_SSPOPCHK a0))
    (Hexecute_ZICBOM : ∀ a0 a1, gwalk (@execute_ZICBOM a0 a1))
    (Hexecute_ZICBOP : ∀ a0 a1 a2, gwalk (@execute_ZICBOP a0 a1 a2))
    (Hexecute_ZICBOZ : ∀ a0, gwalk (@execute_ZICBOZ a0)) :
  ∀ ast, gwalk (execute ast).
Proof. intros ast; cbv [execute]; gw_solve. Qed.

(* ====================================================================== *)
(** ** 3. [run_hart_active] and [try_step] *)

Lemma gw_run_hart_active
    (Hfetch : ∀ a0, gwalk (@fetch a0))
    (Hexecute : ∀ ast, gwalk (execute ast)) :
  ∀ a0, gwalk (@run_hart_active a0).
Proof. intros; cbv [run_hart_active]; gw_solve. Qed.

Lemma gw_try_step
    (Hrun : ∀ a0, gwalk (@run_hart_active a0)) :
  ∀ a0 a1, gwalk (@try_step a0 a1).
Proof. intros; cbv [try_step]; gw_solve. Qed.
