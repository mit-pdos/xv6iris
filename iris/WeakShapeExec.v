(** * WeakShapeExec.v — the peel, in the value-carrying mode

    This is stage C6's "what C7 owes" item 1: CONSUME the decoder
    postcondition at [rv64d.run_hart_active].  Three things had to come
    together for it, and all three are here:

      §1  [execute] in [WeakShapeWin]'s mode, over the 116-lemma value sweep
          ([WeakShapeExecGen01..03]) and the ELEVEN memory clauses as named
          hypotheses — now stated WITH their [ast_wf] width premise, which is
          what makes them true-as-stated where [WeakShapePeel]'s were not
          (stage C5's (O6): [execute_STORE imm rs2 rs1 0] issues a
          zero-width [MemWrite], so [WeakShapePeel]'s premise-free
          [Hexecute_STORE] is FALSE).
      §2  [run_hart_active], where the decoder postcondition
          ([WeakShapeDec.gpureP_ext_decode] / [_compressed]) crosses the bind
          into [execute]'s obligation, and where the [ExecuteAs] REDIRECTION
          is discharged.  THE REDIRECTION IS WHY THE MODE CARRIES A WINDOW:
          [execute]'s postcondition says a redirection arrives with [ast_wf]
          AND with no window open, so the arm may call [execute] a second
          time; a value-only postcondition cannot say that, and the
          [gwalkx]/[gsilent] split cannot either (the redirection arm is not
          silent).
      §3  the two readings side by side.  [gx_execute] is the WEAK
          (abandoning) one — honest for [execute_LOADRES], whose window
          escapes — and gives [gwalkx]; [gx_execute_closed] is the CLOSED one
          and is what [WeakShapePeel.gw_try_step] composes with.

    WHAT IS STILL FALSE, AND WHY C7 STOPS HERE.  Both readings' eleven
    hypotheses are refuted by finding (O10) ([WeakShapeWin] §1): every one of
    them translates, and [translate → update_and_write_pte] issues an
    exclusive PTE read whose window is ABANDONED on the "re-read needs no
    update" arm, after which the clause performs its own data access —
    a [MemRead] inside an open window, which [amo_tail] forbids.  That is a
    SPECIFICATION bug of the same family as (O2) and (O4), it is specified in
    [WeakShapeWin] §1, and it is not fixed here.  So this file reduces the
    premise honestly and does not pretend to discharge it. *)

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
Require Import Riscv.rv64d.

Set Default Proof Using "Type".

(** The WEAK mode [execute] exports: [WeakShapeWin.exres_wf_win] — "a
    redirection carries a well-formed instruction and arrives with no window
    open"; anything else is unconstrained, so an abandoning clause passes. *)
Notation gwxw m := (gwpx (λ _ : exception, True) exres_wf_win None m).

(** …and the trivial one, for the [Step]-valued functions above [execute]. *)
Notation gwxt m := (gwpx (λ _ : exception, True) (λ _ _, True) None m).

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
  | |- gwpx _ _ _ (execute_LOAD _ _ _ _ _) => by apply HL
  | |- gwpx _ _ _ (execute_STORE _ _ _ _) => by apply HS
  | |- gwpx _ _ _ (execute_LOADRES _ _ _ _ _) => by apply HLR
  | |- gwpx _ _ _ (execute_STORECON _ _ _ _ _ _) => by apply HSC
  | |- gwpx _ _ _ (execute_AMO _ _ _ _ _ _ _) => by apply HA
  | |- gwpx _ _ _ (execute_SSAMOSWAP _ _ _ _ _ _) => by apply HSA
  | |- gwpx _ _ _ (execute_SSPUSH _) => by apply HP
  | |- gwpx _ _ _ (execute_SSPOPCHK _) => by apply HK
  | |- gwpx _ _ _ (execute_ZICBOM _ _) => by apply HM
  | |- gwpx _ _ _ (execute_ZICBOP _ _ _) => by apply HO
  | |- gwpx _ _ _ (execute_ZICBOZ _) => by apply HZ
  | _ => gwx_solve
  end.

(** THE WEAK READING. *)
Lemma gx_execute
    (HL : ∀ a0 a1 a2 a3 width, (0 < width)%Z → gwxw (@execute_LOAD a0 a1 a2 a3 width))
    (HS : ∀ a0 a1 a2 width, (0 < width)%Z → gwxw (@execute_STORE a0 a1 a2 width))
    (HLR : ∀ a0 a1 a2 width a4,
        (0 < width)%Z → gwxw (@execute_LOADRES a0 a1 a2 width a4))
    (HSC : ∀ a0 a1 a2 a3 width a5,
        (0 < width)%Z → gwxw (@execute_STORECON a0 a1 a2 a3 width a5))
    (HA : ∀ a0 a1 a2 a3 a4 width a6,
        (0 < width)%Z → gwxw (@execute_AMO a0 a1 a2 a3 a4 width a6))
    (HSA : ∀ a0 a1 a2 a3 width a5,
        (0 < width)%Z → gwxw (@execute_SSAMOSWAP a0 a1 a2 a3 width a5))
    (HP : ∀ a0, gwxw (@execute_SSPUSH a0))
    (HK : ∀ a0, gwxw (@execute_SSPOPCHK a0))
    (HM : ∀ a0 a1, gwxw (@execute_ZICBOM a0 a1))
    (HO : ∀ a0 a1 a2, gwxw (@execute_ZICBOP a0 a1 a2))
    (HZ : ∀ a0, gwxw (@execute_ZICBOZ a0)) :
  ∀ ast, ast_wf ast → gwxw (execute ast).
Proof.
  intros ast Hwf. cbv [execute]. destruct ast; cbn [ast_wf] in Hwf;
    exec_arm HL HS HLR HSC HA HSA HP HK HM HO HZ.
Qed.

(** THE CLOSED READING — the same proof, at the stronger postcondition
    [exres_ok] ([exres_wf] AND no window open).  It is what the [gwalk]-mode
    peel ([WeakShapePeel]) composes with, and the eleven hypotheses are
    correspondingly stronger: they say the clause CLOSES every exclusive
    window it opens, which is (O2)'s and (O10)'s content. *)
Lemma gx_execute_closed
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
    [WeakShapeWin.gwpx_bind_pure] — the generic solver would take the
    [gwalk] route there instead and DROP the postcondition, which is why
    the decoder binds are named explicitly below.  The second is closed by
    [execute]'s own postcondition. *)

Section RunHart.

Context (Hfetch : ∀ a0, gwalk None (@fetch a0)).

(** The driver.  Four model-specific cases in front of [gwx_solve]: the two
    decoder binds (where the postcondition must NOT be forgotten), the
    [execute] bind (where it must be CONSUMED), and [fetch] (the twelfth
    residual fact). *)
(** The driver.  Four model-specific cases in front of [gwx_solve]: the two
    decoder binds (where the postcondition must NOT be forgotten — the
    generic solver would take the [gwalk] route there and DROP it), the
    [ExecutionResult]-valued binds (where [execute]'s postcondition has to
    TRAVEL, since the redirection arm reads it), and [fetch], the twelfth
    residual fact.  [Pex] is [execute]'s postcondition, which is the only
    thing that differs between the weak and the closed reading. *)
Ltac rha_step Pex Hex :=
  lazymatch goal with
  | |- gwpx _ _ _ (Defs.bind (Defs.liftR (ext_decode _)) _) =>
      apply (gwpx_bind_pure _ ast_wf);
        [ qtriv | by apply gpureP_liftR, gpureP_ext_decode | ]
  | |- gwpx _ _ _ (Defs.bind (Defs.liftR (ext_decode_compressed _)) _) =>
      apply (gwpx_bind_pure _ ast_wf);
        [ qtriv | by apply gpureP_liftR, gpureP_ext_decode_compressed | ]
  | |- gwpx _ _ _ (@Defs.bind ExecutionResult _ _ _ _) =>
      apply (gwpx_bind _ Pex)
  | |- gwpx _ _ _ (execute _) => by apply Hex
  | |- gwpx _ _ _ (fetch _) => apply gwalk_gwpx; [qtriv | by apply Hfetch]
  end.

(** UNPACK THE POSTCONDITION ONLY ONCE THE RESULT IS A CONSTRUCTOR.  An
    earlier version also had a [clear H] arm for a not-yet-destructed
    [exres_wf_win x w], and that arm fired FIRST — throwing away the very
    fact the redirection arm needs, two steps before it became usable. *)
Ltac rha_clean :=
  match goal with
  | H : exres_wf_win (ExecuteAs _) _ |- _ => destruct H as [? ?]
  | H : exres_ok _ _ |- _ => destruct H as [? ?]
  | H : exres_wf (ExecuteAs _) |- _ => cbv [exres_wf] in H; cbn beta iota in H
  | H : ?w = None |- _ => is_var w; subst w
  end.

Ltac rha_solve Pex Hex :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | progress rha_clean
    | rha_step Pex Hex
    | solve [gwx_leaf]
    | gwx_step ].

Lemma gwx_run_hart_active
    (Hex : ∀ ast, ast_wf ast → gwxw (execute ast)) :
  ∀ n, gwalkx None (run_hart_active n).
Proof using Hfetch.
  intros n.
  apply (gwpx_gwalkx (λ _ : exception, True) (λ _ _, True)).
  cbv [run_hart_active]. rha_solve exres_wf_win Hex.
Qed.

(** …and the CLOSED reading, which is what [WeakShapePeel.gw_try_step] takes.
    Same script; the only difference is the strength of [execute]'s
    postcondition, and [gwalk_gwpx]/[gwpx_gwalk] make [gwalk] literally the
    instance of [gwpx] at [P := λ _ w, w = None]. *)
Lemma gw_run_hart_active_wf
    (Hex : ∀ ast, ast_wf ast → gwx (execute ast)) :
  ∀ n, gwalk None (run_hart_active n).
Proof using Hfetch.
  intros n. apply (gwpx_gwalk (λ _ : exception, True)).
  cbv [run_hart_active]. rha_solve exres_ok Hex.
Qed.

End RunHart.
