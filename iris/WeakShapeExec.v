(** * WeakShapeExec.v — the peel, in the value-carrying mode

    This is stage C6's "what C7 owes" item 1: CONSUME the decoder
    postcondition at [rv64d.run_hart_active].  Two things had to come
    together for it, and both are here:

      §1  [execute] in [WeakShapeWin]'s [gwx] mode, over the 116-lemma value
          sweep ([WeakShapeExecGen01..03]) and the ELEVEN memory clauses as
          named hypotheses — stated WITH their [ast_wf] width premise, which
          is what makes them true-as-stated where [WeakShapePeel]'s were not
          (stage C5's (O6): [execute_STORE imm rs2 rs1 0] issues a
          zero-width [MemWrite], so [WeakShapePeel]'s premise-free
          [Hexecute_STORE] is FALSE).
      §2  [run_hart_active], where the decoder postcondition
          ([WeakShapeDec.gpureP_ext_decode] / [_compressed]) crosses the bind
          into [execute]'s obligation, and where the [ExecuteAs] REDIRECTION
          is discharged: [execute]'s postcondition says a redirection carries
          an [ast_wf] instruction, so the arm may call [execute] a second
          time.

    ONE READING, NOT TWO — WHAT STAGE C8 COLLAPSED.  Through C7 every
    theorem below came in a WEAK (abandoning) and a CLOSED copy, because
    [execute]'s memory clauses could leave an exclusive window open
    ([execute_LOADRES] never closes one) while [WeakShapePeel.gw_try_step]
    needed a window-free walk; the postcondition therefore carried a window
    ([exres_wf_win] vs. [exres_ok]) and the conclusion came in [gwalkx] and
    [gwalk] flavours.  Finding (O10) ([WeakShapeWin] §1) killed the index
    itself: an exclusive read is now shaped exactly like a plain one, so the
    two readings are literally the same statement and the two eleven-clause
    hypothesis lists are the same list.  The eleven clauses are proved in
    [WeakShapeMem.v]; here they stay hypotheses. *)

From stdpp Require Import gmap finite list relations.
From Stdlib.ssr Require Import ssreflect.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
From xv6iris Require Import WeakSailLTS WeakSailComplete WeakShape.
From xv6iris Require Import WeakShapeOverrides WeakShapeOverrides2.
From xv6iris Require Import WeakShapeAst WeakShapeWin WeakShapeDec.
From xv6iris Require Import WeakShapeGen01 WeakShapeGen02 WeakShapeGen03
  WeakShapeGen04 WeakShapeGen05 WeakShapeGen06 WeakShapeGen07 WeakShapeGen08
  WeakShapeGen09 WeakShapeGen10 WeakShapeGen11 WeakShapeGen12 WeakShapeGen13
  WeakShapeGen14 WeakShapeGen15.
From xv6iris Require Import WeakShapeExecGen01 WeakShapeExecGen02
  WeakShapeExecGen03.
From xv6iris Require Import WeakShapeMem.
Require Import Riscv.rv64d.

Set Default Proof Using "Type".

(* ====================================================================== *)
(** ** 1. [execute], modulo its eleven memory clauses *)

Section Execute.

(** THE DISPATCH IS BY HEAD CONSTANT, NOT BY [apply] — finding (O8) again,
    in a place that is not a hint database.  A chain of
    [try (by apply Hexecute_LOAD); try (by apply Hexecute_STORE); …] over
    [execute]'s ~130 arms unifies each hypothesis's conclusion against each
    arm's body, and the model's [execute_*] constants are TRANSPARENT, so
    every failing attempt delta-unfolds two large terms.  Measured: the
    [lazymatch] below is ~20 s; the [apply] chain did not finish in two
    minutes. *)
Ltac exec_arm HL HS HLR HSC HA HSA HP HK HM HO HZ :=
  lazymatch goal with
  | |- gwp _ _ (execute_LOAD _ _ _ _ _) => by apply HL
  | |- gwp _ _ (execute_STORE _ _ _ _) => by apply HS
  | |- gwp _ _ (execute_LOADRES _ _ _ _ _) => by apply HLR
  | |- gwp _ _ (execute_STORECON _ _ _ _ _ _) => by apply HSC
  | |- gwp _ _ (execute_AMO _ _ _ _ _ _ _) => by apply HA
  | |- gwp _ _ (execute_SSAMOSWAP _ _ _ _ _ _) => by apply HSA
  | |- gwp _ _ (execute_SSPUSH _) => by apply HP
  | |- gwp _ _ (execute_SSPOPCHK _) => by apply HK
  | |- gwp _ _ (execute_ZICBOM _ _) => by apply HM
  | |- gwp _ _ (execute_ZICBOP _ _ _) => by apply HO
  | |- gwp _ _ (execute_ZICBOZ _) => by apply HZ
  | _ => gwx_solve
  end.

Lemma gx_execute
    (HL : ∀ a0 a1 a2 a3 width, (0 < width)%Z → gwx (@execute_LOAD a0 a1 a2 a3 width))
    (HS : ∀ a0 a1 a2 width, (0 < width)%Z → gwx (@execute_STORE a0 a1 a2 width))
    (HLR : ∀ a0 a1 a2 width a4,
        (0 < width)%Z → gwx (@execute_LOADRES a0 a1 a2 width a4))
    (HSC : ∀ a0 a1 a2 a3 width a5,
        (0 < width)%Z → gwx (@execute_STORECON a0 a1 a2 a3 width a5))
    (HA : ∀ a0 a1 a2 a3 a4 width a6,
        (0 < width)%Z → gwx (@execute_AMO a0 a1 a2 a3 a4 width a6))
    (HSA : ∀ a0 a1 a2 a3 width a5,
        (0 < width)%Z → gwx (@execute_SSAMOSWAP a0 a1 a2 a3 width a5))
    (HP : ∀ a0, gwx (@execute_SSPUSH a0))
    (HK : ∀ a0, gwx (@execute_SSPOPCHK a0))
    (HM : ∀ a0 a1, gwx (@execute_ZICBOM a0 a1))
    (HO : ∀ a0 a1 a2, gwx (@execute_ZICBOP a0 a1 a2))
    (HZ : ∀ a0, gwx (@execute_ZICBOZ a0)) :
  ∀ ast, ast_wf ast → gwx (execute ast).
Proof.
  intros ast Hwf. cbv [execute]. destruct ast; cbn [ast_wf] in Hwf;
    exec_arm HL HS HLR HSC HA HSA HP HK HM HO HZ.
Qed.

End Execute.

(* ====================================================================== *)
(** ** 2. [run_hart_active]: the decoder postcondition, consumed

    THE TWO PLACES [execute] IS APPLIED, and neither is syntax:

      liftR (ext_decode w) >>= λ instruction, … execute instruction …
      match … with ExecuteAs other_inst => liftR (execute other_inst) | … end

    The first is closed by [WeakShapeDec.gpureP_ext_decode] through
    [WeakShapeWin.gwp_bind_pure] — the generic solver would take the
    [gwalk] route there instead and DROP the postcondition, which is why
    the decoder binds are named explicitly below.  The second is closed by
    [execute]'s own postcondition. *)

Section RunHart.

Context (Hfetch : ∀ a0, gwalk (@fetch a0)).

(** The driver.  Four model-specific cases in front of [gwx_solve]: the two
    decoder binds (where the postcondition must NOT be forgotten — the
    generic solver would take the [gwalk] route there and DROP it), the
    [ExecutionResult]-valued binds (where [execute]'s postcondition has to
    TRAVEL, since the redirection arm reads it), and [fetch], the twelfth
    residual fact. *)
Ltac rha_step Hex :=
  lazymatch goal with
  | |- gwp _ _ (Defs.bind (Defs.liftR (ext_decode _)) _) =>
      apply (gwp_bind_pure _ ast_wf);
        [ qtriv | by apply gpureP_liftR, gpureP_ext_decode | ]
  | |- gwp _ _ (Defs.bind (Defs.liftR (ext_decode_compressed _)) _) =>
      apply (gwp_bind_pure _ ast_wf);
        [ qtriv | by apply gpureP_liftR, gpureP_ext_decode_compressed | ]
  | |- gwp _ _ (@Defs.bind ExecutionResult _ _ _ _) =>
      apply (gwp_bind _ exres_wf)
  | |- gwp _ _ (execute _) => by apply Hex
  | |- gwp _ _ (fetch _) => apply gwalk_gwp; [qtriv | ptriv | by apply Hfetch]
  end.

(** UNPACK THE POSTCONDITION ONLY ONCE THE RESULT IS A CONSTRUCTOR.  An
    earlier version also had a [clear H] arm for a not-yet-destructed
    [exres_wf x], and that arm fired FIRST — throwing away the very fact the
    redirection arm needs, two steps before it became usable. *)
Ltac rha_clean :=
  match goal with
  | H : exres_wf (ExecuteAs _) |- _ => cbv [exres_wf] in H; cbn beta iota in H
  end.

Ltac rha_solve Hex :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | progress rha_clean
    | rha_step Hex
    | solve [gwx_leaf]
    | gwx_step ].

(** [run_hart_active] walks, given [execute]'s value postcondition — and
    [gwalk_gwp]/[gwp_gwalk] make [gwalk] literally the instance of [gwp] at
    the trivial postconditions, so the conclusion is the plain shape
    predicate [WeakShapePeel.gw_try_step] takes.  (C7 proved this twice, once
    per reading of the exclusive window; see the header.) *)
Lemma gw_run_hart_active_wf
    (Hex : ∀ ast, ast_wf ast → gwx (execute ast)) :
  ∀ n, gwalk (run_hart_active n).
Proof using Hfetch.
  intros n. apply (gwp_gwalk (λ _ : exception, True) (λ _, True)).
  cbv [run_hart_active]. rha_solve Hex.
Qed.

End RunHart.

(* ====================================================================== *)
(** ** 3. THE ELEVEN MEMORY CLAUSES

    §1's hypotheses, discharged.  Each clause is one bind over the access
    layer of [WeakShapeMem] plus register/trace code the `gshape` tower
    already covers, so the whole section is a page — which is the point of
    (O10)'s fix: through stage C7 every one of these owed, on top of its own
    shape, the exclusive-window agreement between a read's [(pa, n)] and the
    conditional write that closes it.

    WHICH FACT EACH CLAUSE NEEDS, and it is always one of two kinds:

      - a VALUE fact, [WeakShapeMem]'s [gxr] ([gwp] at "the [Err] payload is
        [exres_wf]"), wherever the clause's own result is the fault the
        access layer returned — [execute_LOAD]/[_LOADRES] and
        [execute_SSPOPCHK] take it from [vmem_read]/[vmem_read_addr],
        [execute_STORE]/[_STORECON] and [execute_SSPUSH] from
        [vmem_write]/[vmem_write_addr], [execute_ZICBOM] from
        [process_clean_inval].  The generic [gwx_solve] cannot carry it (its
        value-carrying bind rule keys on the prefix's type being literally
        [ExecutionResult], and these have type [result _ ExecutionResult]),
        so those six run [WeakShapeMem.gxm_solve] instead;
      - a plain SHAPE fact for the clauses that build their own
        [ExecutionResult] out of [memory_exception] and call the memory
        layer only in value-irrelevant prefix position — [execute_AMO],
        [execute_SSAMOSWAP], [execute_ZICBOP], [execute_ZICBOZ].  Those are
        [gwx_solve] over [WeakShapeMem]'s [gwalk] lemmas.

    THE WIDTHS.  Six clauses carry [ast_wf]'s [0 < width] and pass it
    straight down.  The other five write at a MODEL CONSTANT and need no
    premise: [execute_SSPUSH]/[_SSPOPCHK] at [xlen_bytes], [execute_ZICBOZ]
    at [pow2 plat_cache_block_size_exp] — both closed by [vm_compute]. *)

Section MemClauses.

Lemma gx_execute_LOAD (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 width, (0 < width)%Z → gwx (@execute_LOAD a0 a1 a2 a3 width).
Proof.
  intros a0 a1 a2 a3 width Hw.
  pose proof (gw_vmem_read H) as Hv. pose proof (gx_vmem_read H) as Hvx.
  cbv [execute_LOAD]; gxm_solve Hvx.
Qed.

Lemma gx_execute_LOADRES (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 width a4, (0 < width)%Z → gwx (@execute_LOADRES a0 a1 a2 width a4).
Proof.
  intros a0 a1 a2 width a4 Hw.
  pose proof (gw_vmem_read H) as Hv. pose proof (gx_vmem_read H) as Hvx.
  cbv [execute_LOADRES]; gxm_solve Hvx.
Qed.

Lemma gx_execute_STORE (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 width, (0 < width)%Z → gwx (@execute_STORE a0 a1 a2 width).
Proof.
  intros a0 a1 a2 width Hw.
  pose proof (fun a b c d e f g =>
                gw_vmem_write H a b width c d e f g Hw) as Hv.
  pose proof (fun a b c d e f g =>
                gx_vmem_write H a b width c d e f g Hw) as Hvx.
  cbv [execute_STORE]; gxm_solve Hvx.
Qed.

Lemma gx_execute_STORECON (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 width a5,
    (0 < width)%Z → gwx (@execute_STORECON a0 a1 a2 a3 width a5).
Proof.
  intros a0 a1 a2 a3 width a5 Hw.
  pose proof (fun a b c d e f g =>
                gw_vmem_write H a b width c d e f g Hw) as Hv.
  pose proof (fun a b c d e f g =>
                gx_vmem_write H a b width c d e f g Hw) as Hvx.
  pose proof (gw_cancel_reservation H) as Hcr.
  cbv [execute_STORECON]; gxm_solve Hvx.
Qed.

Lemma gx_execute_SSPUSH (H : rv64d_axiom_shapes) :
  ∀ a0, gwx (@execute_SSPUSH a0).
Proof.
  intros a0.
  assert (Hx : (0 < xlen_bytes)%Z) by (by vm_compute).
  pose proof (fun a b c d e f =>
                gw_vmem_write_addr H a xlen_bytes b c d e f Hx) as Hv.
  pose proof (fun a b c d e f =>
                gx_vmem_write_addr H a xlen_bytes b c d e f Hx) as Hvx.
  cbv [execute_SSPUSH]; gxm_solve Hvx.
Qed.

Lemma gx_execute_SSPOPCHK (H : rv64d_axiom_shapes) :
  ∀ a0, gwx (@execute_SSPOPCHK a0).
Proof.
  intros a0.
  pose proof (gw_vmem_read_addr H) as Hv.
  pose proof (gx_vmem_read_addr H) as Hvx.
  cbv [execute_SSPOPCHK]; gxm_solve Hvx.
Qed.

Lemma gx_execute_ZICBOM (H : rv64d_axiom_shapes) :
  ∀ a0 a1, gwx (@execute_ZICBOM a0 a1).
Proof.
  intros a0 a1.
  pose proof (gw_process_clean_inval H) as Hp.
  pose proof (gx_process_clean_inval H) as Hpx.
  cbv [execute_ZICBOM]; gwx_solve.
Qed.

Lemma gx_execute_AMO (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 a4 width a6,
    (0 < width)%Z → gwx (@execute_AMO a0 a1 a2 a3 a4 width a6).
Proof.
  intros a0 a1 a2 a3 a4 width a6 Hw.
  pose proof (gw_translateAddr H) as Ht.
  pose proof (fun a b c d e f g =>
                gw_mem_write_value H a width b c d e f g Hw) as Hmv.
  cbv [execute_AMO]; gwx_solve.
Qed.

Lemma gx_execute_SSAMOSWAP (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2 a3 width a5,
    (0 < width)%Z → gwx (@execute_SSAMOSWAP a0 a1 a2 a3 width a5).
Proof.
  intros a0 a1 a2 a3 width a5 Hw.
  pose proof (gw_translateAddr H) as Ht.
  pose proof (fun a b c d e f g =>
                gw_mem_write_value H a width b c d e f g Hw) as Hmv.
  cbv [execute_SSAMOSWAP]; gwx_solve.
Qed.

Lemma gx_execute_ZICBOP (H : rv64d_axiom_shapes) :
  ∀ a0 a1 a2, gwx (@execute_ZICBOP a0 a1 a2).
Proof.
  intros a0 a1 a2. pose proof (gw_translateAddr H) as Ht.
  cbv [execute_ZICBOP]; gwx_solve.
Qed.

Lemma gx_execute_ZICBOZ (H : rv64d_axiom_shapes) :
  ∀ a0, gwx (@execute_ZICBOZ a0).
Proof.
  intros a0. pose proof (gw_translateAddr H) as Ht.
  assert (Hcb : (0 < Values.pow2 plat_cache_block_size_exp)%Z) by (by vm_compute).
  pose proof (fun a b c d e f g =>
                gw_mem_write_value H a (Values.pow2 plat_cache_block_size_exp)
                  b c d e f g Hcb) as Hmv.
  cbv [execute_ZICBOZ]; gwx_solve.
Qed.

End MemClauses.

(** …and [execute] itself, with §1's eleven hypotheses discharged. *)
Lemma gx_execute_ax (H : rv64d_axiom_shapes) :
  ∀ ast, ast_wf ast → gwx (execute ast).
Proof.
  apply gx_execute;
    solve [ apply (gx_execute_LOAD H) | apply (gx_execute_STORE H)
          | apply (gx_execute_LOADRES H) | apply (gx_execute_STORECON H)
          | apply (gx_execute_AMO H) | apply (gx_execute_SSAMOSWAP H)
          | apply (gx_execute_SSPUSH H) | apply (gx_execute_SSPOPCHK H)
          | apply (gx_execute_ZICBOM H) | apply (gx_execute_ZICBOP H)
          | apply (gx_execute_ZICBOZ H) ].
Qed.

(** THE TOP OF THIS FILE'S CHAIN: [run_hart_active] over the record alone. *)
Lemma gw_run_hart_active_ax (H : rv64d_axiom_shapes) :
  ∀ n, gwalk (run_hart_active n).
Proof.
  apply (gw_run_hart_active_wf (gw_fetch H)), (gx_execute_ax H).
Qed.
