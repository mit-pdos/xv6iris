(** * WeakShapeLive.v — THE STATE-THREADING LIVENESS KIT, AND THE
      PER-BOUNDARY LIVENESS FACT (stage C9)

    The SHAPE half of [WeakCompose] §6's seam (6) is a theorem
    ([WeakShapeTop.riscv_step_shaped_ax]).  This file is the LIVENESS half's
    specification-and-kit, and the first thing to say about it is what it is
    NOT: it is not [∀ b, sail_live (riscv_step b)].  That statement was
    REFUTED (finding (O9)) and has been DELETED from the tree along with the
    predicate it was stated over; its honest replacement is

        [priv_ok rs → sail_live_st rs (riscv_step b)]

    — liveness of the instruction monad RUN FROM A CONCRETE REGISTER FILE,
    under the one register-state side condition the model's failure sites
    need.  [WeakSailComplete] §2 notes (f)/(g) carry the argument for the
    predicate; this file carries the kit and the reduction.

    ------------------------------------------------------------------------
    §1  [gliveP Q P rs m] — THE MODE.  It is [WeakShapeOverrides2.gpost] with
        the memory and barrier arms OPENED UP (a live computation may access
        memory; the answers are the ones [WeakSailLTS.sail_mstep] supplies,
        as everywhere since stage C2) and a REGISTER STATE THREADED THROUGH:

          [Ret x]        ↦  [P x rs]        — the postcondition sees the
                                              FINAL state, which is what
                                              makes [bind] compositional;
          [RegRead r]    ↦  answered [register_lookup r rs] (except the pin,
                            note (g) of [WeakSailComplete] §2);
          [RegWrite r v] ↦  the continuation is measured at
                            [register_set r v rs];
          [ExtraOutcome] ↦  [Q e rs] — the exception postcondition, at the
                            state the throw was raised in;
          [GenericFail]/[Discard]/[ChooseReal] ↦ [False].

        WHY A POSTCONDITION AND NOT A PLAIN PREDICATE.  [glive]'s bind rule
        ([WeakShape.glive_bind]) can hypothesise [∀ x, glive (k x)] because
        it is state-blind.  Here the state at which [k] starts is
        PATH-DEPENDENT — it is whatever the prefix's [RegWrite]s left — so
        the only compositional formulation is the CPS one: the prefix's
        postcondition IS the continuation's hypothesis ([gliveP_bind]).
        That is the same shape [iris/DecodeSetU.v]'s [goodbP] driver has,
        and the porting recipe recorded in [claude-notes/durable-notes.md]
        ("a state-pinned boolean traversal and a ∀-quantified one are the
        same traversal") applies in the other direction here: this is the
        state-pinned traversal, and the ∀-quantified one ([WeakShape.glive])
        is its register-free specialisation, reusable at every prefix that
        does not branch on a register ([glive_glive_st]).

    §2  the combinator kit: [gliveP_bind]/[_bind0], the failure leaves, the
        register leaves, [gliveP_try_catch] and its two instances
        ([liftR], [catch_early_return]).

    §3  [priv_ok] (defined in [WeakSailComplete] §2, so that the residual
        invariant can name it) and the RESIDUE RECORD.

    §4  the reduction [riscv_step_live_ax].

    ------------------------------------------------------------------------
    WHAT IS ASSUMED, AND WHY IT IS A [Record] AND NOT AN [Axiom].

    [rv64d_live_residue] is the LIVENESS SWEEP, un-run.  Its two fields are
    the two model functions [RiscvLang.riscv_step] is built from, in this
    mode.  It is in exactly the epistemic slot [WeakShapeMem]'s
    [rv64d_axiom_shapes] is in — a named hypothesis a caller must supply, so
    that [Print Assumptions] on the capstones stays at the five rv64d axioms
    — but its status is DIFFERENT and the difference must not be blurred:
    [rv64d_axiom_shapes] is IRREDUCIBLE (three opaque model [Axiom]s of
    monad type, about which nothing is provable), whereas
    [rv64d_live_residue] is a WORK ITEM.  Discharging it is the (O3) sweep:
    a [gliveP] tower over the [try_step] cone plus a reachability argument
    at each [exit] / [internal_error] / [assert_exp] site, and the three
    opaque axioms then need [gliveP] facts of their own (an extension of
    [rv64d_axiom_shapes], deliberately NOT added here: with the cone
    hypothesised the axioms' liveness sits INSIDE the residue, and adding
    unusable fields to the shape record would misreport what is assumed).
    The site table and the sweep's shape are in
    [claude-notes/projects/weak-memory-premises.md].

    DEPENDENCIES: [WeakSailComplete] (the specification [sail_live_st] and
    [priv_ok]) and [WeakShape] (the register-free [glive], reused at
    register-insensitive prefixes).  Deliberately NOT the generated tower:
    that tower is [gwalk]-mode and, by finding (O7), implies nothing here. *)

From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From Stdlib.ssr Require Import ssreflect.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge.
From xv6iris Require Import WeakInterp WeakInterpProj WeakSailLTS WeakSailLTS2.
From xv6iris Require Import WeakSailComplete WeakShape.
Require Import Riscv.rv64d.
Require Import RiscvLang.

Set Default Proof Using "Type".

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. [gliveP]: liveness with the register state threaded *)

Section Live.
Context {E A : Type}.
Local Notation mon := (Defs.monad E A).

Fixpoint gliveP (Q : E → regstate → Prop) (P : A → regstate → Prop)
    (rs : regstate) (m : mon) {struct m} : Prop :=
  match m with
  | Interface.Ret x => P x rs
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → mon) → Prop with
       | Interface.RegRead r _ => λ k,
           if register_beq r (sig_seip : register)
           then ∀ v, gliveP Q P rs (k v)
           else gliveP Q P rs (k (register_lookup r rs))
       | Interface.RegWrite r _ v => λ k,
           gliveP Q P (register_set r v rs) (k tt)
       | Interface.MemRead n req => λ k,
           ∀ w : bv (8 * n), gliveP Q P rs (k (inl (w, None)))
       | Interface.MemWrite _ _ => λ k, gliveP Q P rs (k (inl None))
       | Interface.ExtraOutcome e => λ _, Q e rs
       | Interface.GenericFail _ => λ _, False
       | Interface.Discard => λ _, False
       | Interface.Choose ty =>
           match ty as t return (Values.choose_type t → mon) → Prop with
           | Values.ChooseReal => λ _, False
           | _ => λ k, ∀ r, gliveP Q P rs (k r)
           end
       | _ => λ k, ∀ r, gliveP Q P rs (k r)
       end) k
  end.

End Live.

Arguments gliveP {E A} Q P rs m.

(** THE INFORMATION-FREE INSTANCE, and the one the LTS asks for: a raised
    Sail exception is FATAL (the machine is stuck at an [ExtraOutcome] node
    — finding (O9)) and nothing is claimed about the value. *)
Definition glive_st {E A} (rs : regstate) (m : Defs.monad E A) : Prop :=
  gliveP (λ _ _, False) (λ _ _, True) rs m.

(** …and it IS the specification, at [M unit]. *)
Lemma glive_st_sail_live_st (rs : regstate) (m : M unit) :
  glive_st rs m ↔ sail_live_st rs m.
Proof.
  rewrite /glive_st. revert rs.
  induction m as [x|T oc k IH]; intros rs; [done|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|Ax eo|msg| | |ty| |msg2]; simpl;
    try done;
    (* RegRead: the pin's ∀ arm and the concrete arm, in lockstep *)
    try (destruct (register_beq rg (sig_seip : register));
         [split; intros H v; by apply IH|split; intros H; by apply IH]);
    try (destruct ty; simpl; try done; split; intros H r; by apply IH);
    try (split; intros H r; by apply IH);
    try (split; intros H; by apply IH).
Qed.

(** THE REGISTER-FREE REUSE ([WeakShape.glive]).  A fragment that never
    branches on a register is live at every state, and that is exactly what
    the state-threading bind rule needs of such a prefix. *)
Lemma glive_glive_st {E A} (rs : regstate) (m : Defs.monad E A) :
  glive true m → glive_st rs m.
Proof.
  rewrite /glive_st. revert rs. induction m as [x|T oc k IH]; intros rs; [done|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|Ax eo|msg| | |ty| |msg2]; simpl; try done;
    try (destruct (register_beq rg (sig_seip : register)); intros H;
         [intros v|]; by apply IH);
    try (destruct ty; simpl; try done; intros H r; by apply IH);
    try (intros H r; by apply IH);
    try (intros H; by apply IH).
Qed.

(* ====================================================================== *)
(** ** 2. The combinator kit *)

Lemma gliveP_mono {E A} (Q Q' : E → regstate → Prop)
    (P P' : A → regstate → Prop) (rs : regstate) (m : Defs.monad E A) :
  (∀ e s, Q e s → Q' e s) → (∀ x s, P x s → P' x s) →
  gliveP Q P rs m → gliveP Q' P' rs m.
Proof.
  intros HQ HP. revert rs.
  induction m as [x|T oc k IH]; intros rs; [by apply HP|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|Ax eo|msg| | |ty| |msg2]; simpl; try done;
    try (destruct (register_beq rg (sig_seip : register)); intros H;
         [intros v|]; by apply IH);
    try (destruct ty; simpl; try done; intros H r; by apply IH);
    try (intros H r; by apply IH);
    try (intros H; by apply IH);
    try (by apply HQ).
Qed.

Lemma gliveP_ret {E A} (Q : E → regstate → Prop) (P : A → regstate → Prop)
    rs (x : A) : P x rs → gliveP Q P rs (Interface.Ret x).
Proof. done. Qed.

Lemma gliveP_returnm {E A} (Q : E → regstate → Prop) (P : A → regstate → Prop)
    rs (x : A) : P x rs → gliveP Q P rs (Defs.returnm (E := E) x).
Proof. done. Qed.

(** THE BIND, and the whole reason for the postcondition: the prefix's
    postcondition — value AND state — is the continuation's hypothesis. *)
Lemma gliveP_bind {E A B} (Q : E → regstate → Prop)
    (Pm : A → regstate → Prop) (P : B → regstate → Prop)
    rs (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gliveP Q Pm rs m → (∀ x s, Pm x s → gliveP Q P s (k x)) →
  gliveP Q P rs (Defs.bind m k).
Proof.
  revert rs. induction m as [x|T oc k0 IH]; intros rs Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=.
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|Ax eo|msg| | |ty| |msg2]; simpl in Hm |- *;
    try done;
    try (destruct (register_beq rg (sig_seip : register));
         [intros v; exact (IH v rs (Hm v) Hk)|exact (IH _ rs Hm Hk)]);
    try (destruct ty; simpl in Hm |- *; try done;
         intros r; exact (IH r rs (Hm r) Hk));
    try (by intros r; exact (IH r rs (Hm r) Hk));
    try (by intros w; exact (IH _ rs (Hm w) Hk));
    (* RegWrite: the continuation starts at the WRITTEN state *)
    try (exact (IH tt _ Hm Hk));
    try (exact (IH _ rs Hm Hk)).
Qed.

Lemma gliveP_bind0 {E A} (Q : E → regstate → Prop) (P : A → regstate → Prop)
    rs (m : Defs.monad E unit) (n : Defs.monad E A) :
  gliveP Q (λ _ _, True) rs m → (∀ s, gliveP Q P s n) →
  gliveP Q P rs (Defs.bind0 m n).
Proof.
  intros H1 H2. rewrite /Defs.bind0.
  apply (gliveP_bind Q (λ _ _, True)); [exact H1|by intros x s _].
Qed.

(** THE FAILURE LEAVES.  [fail]/[exit] are NEVER live — that is the whole
    content of the (O3) sweep, and every one of the ~100 sites in the model
    is discharged by showing the site UNREACHABLE from [rs], not by a shape
    lemma. *)
Lemma gliveP_fail_False {E A} (Q : E → regstate → Prop)
    (P : A → regstate → Prop) rs (msg : String.string) :
  gliveP Q P rs (Defs.fail (A := A) (E := E) msg) → False.
Proof. done. Qed.

Lemma gliveP_exit_False {E A} (Q : E → regstate → Prop)
    (P : A → regstate → Prop) rs :
  gliveP Q P rs (Defs.exit (A := A) (E := E) tt) → False.
Proof. done. Qed.

Lemma gliveP_throw {E A} (Q : E → regstate → Prop) (P : A → regstate → Prop)
    rs (e : E) : Q e rs → gliveP Q P rs (Defs.throw (A := A) e).
Proof. done. Qed.

Lemma gliveP_assert_exp {E} (Q : E → regstate → Prop) rs (b : bool) msg :
  b = true → gliveP Q (λ _ _, True) rs (Defs.assert_exp b msg).
Proof. intros ->. done. Qed.

Lemma gliveP_assert_exp' {E} (Q : E → regstate → Prop) rs (b : bool) msg :
  b = true →
  gliveP Q (λ _ _, True) rs (Defs.assert_exp' (E := E) b msg).
Proof. rewrite /Defs.assert_exp'. by intros ->. Qed.

(** THE REGISTER LEAVES — where the concrete answer enters, and the one
    place the interrupt pin's ∀ arm is visible to a consumer. *)
Lemma gliveP_read_reg {E} (Q : E → regstate → Prop) (r : Arch.reg)
    (P : Arch.reg_type r → regstate → Prop) rs :
  (r ≠ (sig_seip : register) → P (register_lookup r rs) rs) →
  (r = (sig_seip : register) → ∀ v, P v rs) →
  gliveP Q P rs (Defs.read_reg (e := E) r).
Proof.
  intros H1 H2. rewrite /Defs.read_reg /=.
  destruct (register_beq r (sig_seip : register)) eqn:Hb.
  - intros v. apply H2. exact (register_beq_true _ _ Hb).
  - apply H1. intros ->. by rewrite register_beq_refl in Hb.
Qed.

(** The common case: any register but the pin. *)
Lemma gliveP_read_reg_ne {E} (Q : E → regstate → Prop) (r : Arch.reg)
    (P : Arch.reg_type r → regstate → Prop) rs :
  r ≠ (sig_seip : register) → P (register_lookup r rs) rs →
  gliveP Q P rs (Defs.read_reg (e := E) r).
Proof. intros Hne HP. apply gliveP_read_reg; [done|by intros ->]. Qed.

Lemma gliveP_write_reg {E} (Q : E → regstate → Prop) (r : Arch.reg)
    (P : unit → regstate → Prop) rs (v : Arch.reg_type r) :
  P tt (register_set r v rs) → gliveP Q P rs (Defs.write_reg (e := E) r v).
Proof. by rewrite /Defs.write_reg /=. Qed.

(** THE HANDLER RULE, and where the exception postcondition is consumed —
    at the state the throw was raised in, which is what a state-threading
    kit has to say and a state-blind one cannot. *)
Lemma gliveP_try_catch {A E1 E2} (Q1 : E1 → regstate → Prop)
    (Q2 : E2 → regstate → Prop) (P : A → regstate → Prop)
    rs (m : Defs.monad E1 A) (h : E1 → Defs.monad E2 A) :
  (∀ e s, Q1 e s → gliveP Q2 P s (h e)) →
  gliveP Q1 P rs m → gliveP Q2 P rs (Defs.try_catch m h).
Proof.
  intros Hh. revert rs. induction m as [x|T oc k IH]; intros rs Hm; [done|].
  destruct oc as [rg akk|rg akk rv|nn req|nn req|op|szb bpa|bk|co|to|flt
                 |epa|tst|tnd|Ax eo|msg| | |ty| |msg2]; simpl in Hm |- *;
    try done;
    try (destruct (register_beq rg (sig_seip : register));
         [intros v; exact (IH v rs (Hm v))|exact (IH _ rs Hm)]);
    try (destruct ty; simpl in Hm |- *; try done;
         intros r; exact (IH r rs (Hm r)));
    try (by intros r; exact (IH r rs (Hm r)));
    try (by intros w; exact (IH _ rs (Hm w)));
    try (exact (IH tt _ Hm));
    try (exact (IH _ rs Hm));
    (* ExtraOutcome: the handler takes over, at the state of the throw *)
    try (exact (Hh _ rs Hm)).
Qed.

Lemma gliveP_liftR {A R E} (Q1 : E → regstate → Prop)
    (Q2 : R + E → regstate → Prop) (P : A → regstate → Prop)
    rs (m : Defs.monad E A) :
  (∀ e s, Q1 e s → Q2 (inr e) s) →
  gliveP Q1 P rs m → gliveP Q2 P rs (Defs.liftR (R := R) m).
Proof.
  intros HQ Hm. apply (gliveP_try_catch Q1); [|exact Hm].
  intros e s He. by apply gliveP_throw, HQ.
Qed.

Lemma gliveP_catch_early_return {A E} (Q : E → regstate → Prop)
    (P : A → regstate → Prop) rs (m : Defs.monadR A E A) :
  gliveP (λ (re : A + E) s, match re with inl a => P a s | inr e => Q e s end)
         P rs m →
  gliveP Q P rs (Defs.catch_early_return m).
Proof.
  intros Hm.
  apply (gliveP_try_catch
           (λ (re : A + E) s, match re with inl a => P a s | inr e => Q e s end)
           Q P); [|exact Hm].
  intros [a|e] s H; [by apply gliveP_returnm|by apply gliveP_throw].
Qed.

(* ====================================================================== *)
(** ** 3. THE RESIDUE, AS A NAMED RECORD

    Two fields, one per model function [RiscvLang.riscv_step] is built from.
    Read the file header for what this is and what it is not: it is the
    (O3) liveness sweep un-run, not an irreducible fact.

    THE PRIVILEGE CONDITION TRAVELS.  [rlr_try_step]'s POSTCONDITION is
    [priv_ok] again — an instruction may change [cur_privilege] (a trap
    entry does, mid-monad), and what the model guarantees is that it lands
    in one of the three privileges an H-less machine has.  Carrying it is
    what lets the [tick_clock] tail be discharged at the state [try_step]
    left, rather than at every state; and it is the same statement
    [WeakComposeLang]'s [Hpriv] makes per trace record, so a proof of one is
    most of a proof of the other. *)

Record rv64d_live_residue := {
  rlr_try_step : ∀ (n : Z) (b : bool) (rs : regstate),
      priv_ok rs →
      gliveP (λ _ _, False) (λ _ rs', priv_ok rs') rs (try_step n b);
  rlr_tick_clock : ∀ rs : regstate, priv_ok rs → glive_st rs (tick_clock tt);
}.

(* ====================================================================== *)
(** ** 4. THE PER-BOUNDARY LIVENESS FACT

    The twin of [WeakShapeTop.riscv_step_shaped_ax], and the statement the
    residual invariant ([WeakSailCone.res_ok_step]'s boundary arm) consumes.
    Note what it is quantified over: the REGISTER FILE OF THE BOUNDARY
    RECORD, under [priv_ok] of that file — there is no [∀ b] form of this
    fact and there cannot be (finding (O9)). *)
Theorem riscv_step_live_ax (H : rv64d_live_residue) :
  ∀ (rs : regstate) (b : bool), priv_ok rs → sail_live_st rs (riscv_step b).
Proof.
  intros rs b Hp. apply glive_st_sail_live_st.
  rewrite /riscv_step /glive_st.
  apply (gliveP_bind _ (λ _ rs', priv_ok rs'));
    [exact (rlr_try_step H 0%Z false rs Hp)|].
  intros x s Hs. destruct b; [exact (rlr_tick_clock H s Hs)|].
  by apply gliveP_returnm.
Qed.
