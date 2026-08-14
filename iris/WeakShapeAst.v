(** * WeakShapeAst.v — the DECODER POSTCONDITION, and stage C6's finding (O9)

    Stage C5 left [∀ ast, gwalk None (rv64d.execute ast)] REFUTED (finding
    (O6)): Sail's [(0 <? width) && (width <=? 4096)] precondition is emitted
    as a COMMENT and [word_width] is [Z], so [STORE (imm, rs2, rs1, 0)] is a
    well-typed [instruction] on which the model issues a zero-width
    [MemWrite].  C5's prescription was a DECODER POSTCONDITION: every
    [instruction] the decoder can produce has positive memory widths, carried
    across [run_hart_active]'s bind into [execute]'s shape obligation.

    THIS FILE HOLDS THE THREE THINGS THAT PRESCRIPTION NEEDS, and the finding
    that had to be settled before any of them could be true:

      §1  (O9) — the LTS's [Interface.ExtraOutcome] arm OVER-QUANTIFIED, and
          the consequence was that [∀ b, sail_shaped (riscv_step b)] was
          FALSE AS STATED, not merely unreachable by the compositional route.
          The arm is fixed in [WeakSailLTS] (delta (e''')); this section
          records the structural fact the finding rests on, machine-checked,
          and the reachability path in the model.
      §2  [ast_wf] — the postcondition itself, and it is EXACTLY as strong as
          the residue needs: positive widths, nothing else.
      §3  the CONSUMERS — [gpost]-with-a-permissive-exception-postcondition
          ([gpureP]) and the two bind rules that carry a value fact from the
          decoder into a [gwalk]/[gwalkx] obligation.  [WeakShapeOverrides2]'s
          [gwalk_bind_post] cannot serve: it takes [gpost0], i.e. it forbids
          the prefix to raise ANY Sail exception, and the decoder does raise
          one (§1's path).

    ------------------------------------------------------------------------
    §1  (O9): A RAISED SAIL EXCEPTION IS A DEAD END, AND THE OLD ARM WALKED
        THE REST OF THE INSTRUCTION AT EVERY VALUE OF THE THROWN-AT TYPE.

    The structural fact ([throw_bind_node] below, machine-checked):

        Interface.ExtraOutcome {A} : eOutcome A → outcome A          (Sail)
        Defs.throw e             = Interface.Next (ExtraOutcome e) mret
        Defs.bind (Defs.throw e) k = Interface.Next (ExtraOutcome e) k

    — the outcome is indexed by the MONAD'S OWN RETURN TYPE, so the "answer"
    a throw node takes is a value of the type the throw pretends to produce,
    and [bind] pushes the whole rest of the computation into that position.
    Through stage C5 [sail_shaped] (and [gwalk], and [glive]) handled the
    node by their DEFAULT arm, [∀ r, sail_shaped (k r)].

    [WeakSailComplete]'s header (a) already said what the node means — "[
    sail_mstep] has no arm for them at all — the agent is stuck" — and
    justified the default arm by "their result types are empty (or
    abstract)".  That is true of [Interface.GenericFail] and
    [Interface.Discard], whose result type is [False].  It is FALSE of
    [ExtraOutcome].

    THE PATH THAT MAKES IT BITE (read off the sources; the leaf is
    machine-checked, the reachability is a source argument of the same kind
    as (O4)'s and (O6)'s):

      rv64d.run_hart_active
        → liftR (ext_decode w) >>= λ instruction, … execute instruction …
      rv64d.ext_decode = encdec_backwards
        → and_boolM (currentlyEnabled Ext_Zicfiss)
                    (read_reg cur_privilege >>= zicfiss_xSSE)   (SSPUSH arm)
      rv64d.currentlyEnabled Ext_Zicfiss
        = hartSupports Zicfiss (= true) ∧ currentlyEnabled Zicsr
          ∧ currentlyEnabled Zimop ∧ currentlyEnabled Zaamo,
        and currentlyEnabled Zaamo = hartSupports Zaamo (= false)
                                     ∨ currentlyEnabled Ext_A = misa.A
        — a REGISTER, so the gate is TRUE at ordinary states;
      rv64d.zicfiss_xSSE VirtualSupervisor
        = internal_error "Hypervisor extension not supported"
        = Defs.throw (Error_internal_error …)                  : M bool

    and [cur_privilege]'s answer is universally quantified by every shape
    predicate's [Interface.RegRead] arm.  So the old arm demanded
    [sail_shaped] of [run_hart_active]'s continuation at EVERY [instruction],
    i.e. exactly the [∀ ast] that (O6) refutes at
    [STORE (imm, rs2, rs1, 0)] ([WeakShapeOverrides2.gwalk_write_ram_zero_False]).

    [rv64d._rec_get_xLPE] throws at [VirtualSupervisor]/[VirtualUser] the
    same way and is reachable from the same gate, so the path is not a
    singleton; and [rv64d.amo_encoding_valid]'s [reserved_behavior] arm is
    dead only because [amocas_odd_register_reserved_behavior] is
    [AMOCAS_Illegal] in this configuration.

    THE FIX is (O1)'s, applied to a third arm: quantify over the answers
    [sail_mstep] SUPPLIES, and here it supplies none.  [WeakSailLTS] delta
    (e''') sets [sail_shaped]'s and [amo_tail]'s [ExtraOutcome] arm to
    [True].  [WeakShape.gwalk] follows in the window-CLOSED mode only — the
    window-open [False] is a kit-side strengthening that [gwalk_try_catch]
    needs (see the arm) — and [WeakShapeOverrides.gwalkx] follows in both.

    NOTE FOR THE LIVENESS HALF: [glive]'s arm is [if xf then False else True],
    i.e. [sail_live] FORBIDS a raised exception outright, and the path above
    is reachable in the same ∀-quantified sense.  So
    [∀ b, sail_live (riscv_step b)] is refuted by the SAME witness, and what
    it needs is not a shape fix but the per-image reachability narrowing of
    (O3): xv6 runs with the H extension off, so [cur_privilege] is never
    [VirtualSupervisor]/[VirtualUser].  That is a register-state side
    condition, and it is the reason the liveness half cannot be stated as
    [∀ b] at all. *)

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
From xv6iris Require Import WeakSailComplete WeakShape WeakShapeOverrides.
From xv6iris Require Import WeakShapeOverrides2.
Require Import Riscv.rv64d.

Set Default Proof Using "Type".

(* ====================================================================== *)
(** ** 1. (O9) at its leaf: what a [throw] node's continuation IS *)

(** THE WHOLE OF THE FINDING, IN ONE EQUATION.  [Defs.throw e]'s continuation
    is [mret], so binding anything onto a throw puts that thing in the
    outcome's answer position — at the type the throw pretends to produce.
    A predicate arm of the form [∀ r, P (k r)] therefore walks [k] at every
    value of that type, which for [rv64d.ext_decode] is every [instruction]. *)
Lemma throw_bind_node {E A B} (e : E) (k : A → Defs.monad E B) :
  Defs.bind (Defs.throw (A := A) e) k
  = Interface.Next (Interface.ExtraOutcome e) k.
Proof. reflexivity. Qed.

(** …and the same for the form the model actually builds, where the throw is
    wrapped by [liftR]: [Defs.try_catch] REPLACES the node by the handler,
    and the handler is itself a throw, so the continuation survives. *)
Lemma liftR_throw_bind_node {A R E B} (e : E) (k : A → Defs.monadR R E B) :
  Defs.bind (Defs.liftR (R := R) (Defs.throw (A := A) e)) k
  = Interface.Next (Interface.ExtraOutcome (inr e : R + E)) k.
Proof. reflexivity. Qed.

(** The arm as it now stands: nothing is asked.  (Before delta (e''') the
    two goals below were [∀ r, sail_shaped (k r)] and
    [∀ r, gwalk None (k r)].) *)
Lemma sail_shaped_throw_bind {A} (e : exception) (k : A → M unit) :
  sail_shaped (Defs.bind (Defs.throw (A := A) e) k).
Proof. by rewrite throw_bind_node. Qed.

Lemma gwalk_throw_bind {E A B} (e : E) (k : A → Defs.monad E B) :
  gwalk None (Defs.bind (Defs.throw (A := A) e) k).
Proof. by rewrite throw_bind_node. Qed.

(* ====================================================================== *)
(** ** 2. [ast_wf]: the decoder postcondition, no stronger than needed

    The residue's twelve facts ask ONE thing of the AST that the [instruction]
    type does not already guarantee: that a memory access has POSITIVE width.
    [WeakShapeOverrides2.gpost_split_misaligned] turns [0 < width] into
    [0 < split_width], and [gwalk_write_ram_any] / [WeakShape]'s read leaves
    need nothing else — since stage C4's (O4) fix the window-closed
    [MemWrite] arm constrains only the width, and the [MemRead] arms
    constrain only the access kind.

    So [ast_wf] is exactly "every [word_width]/[word_width_wide] field is
    positive", and NOT the [[1;2;4;8]] membership [DecodeSetU.width_ok1248]
    records: the extra strength would have to be carried through six more
    functions for no consumer.  ([DecodeSetU]'s sets are pinned at the U-mode
    reference state [dstateU]; this predicate has to hold at EVERY register
    state a fetch can run at, which is why it is stated over the ∀-quantified
    walk rather than over [goodbP].  The width fields themselves are
    gate-independent — they come from [width_enc_backwards] /
    [width_enc_wide_backwards] on a funct3/funct2 slice — so the two agree
    where they overlap.) *)

Definition ast_wf (i : instruction) : Prop :=
  match i with
  | LOAD (_, _, _, _, width) => (0 < width)%Z
  | STORE (_, _, _, width) => (0 < width)%Z
  | AMO (_, _, _, _, _, width, _) => (0 < width)%Z
  | LOADRES (_, _, _, width, _) => (0 < width)%Z
  | STORECON (_, _, _, _, width, _) => (0 < width)%Z
  | SSAMOSWAP (_, _, _, _, width, _) => (0 < width)%Z
  | _ => True
  end.

(** The two width mappings the decoder builds those fields with.  Both are
    total onto a positive literal set, and that is the whole arithmetic
    content of the postcondition. *)
Lemma width_enc_backwards_pos (x : Values.mword 2) :
  (0 < width_enc_backwards x)%Z.
Proof.
  rewrite /width_enc_backwards.
  destruct (eq_vec _ _); [lia|]. destruct (eq_vec _ _); [lia|].
  destruct (eq_vec _ _); lia.
Qed.

Lemma gpost_width_enc_wide_backwards (x : Values.mword 3) :
  gpost (λ _ : exception, True) (λ w, (0 < w)%Z) (width_enc_wide_backwards x).
Proof.
  rewrite /width_enc_wide_backwards.
  repeat (destruct (eq_vec _ _); [by apply gpost_returnm; lia|]).
  apply (gpost_bind _ (λ _, True)); [apply gpost_assert_exp'|].
  intros _ _. apply gpost_exit.
Qed.

(* ====================================================================== *)
(** ** 3. The consumers: a decoder fact crossing into a shape obligation

    [WeakShapeOverrides2.gwalk_bind_post] takes [gpost0], whose exception
    postcondition is [False] — i.e. it requires the prefix to raise NOTHING.
    §1 shows the decoder DOES raise, so the postcondition it can satisfy is
    the permissive one: no memory event, no barrier, every RETURNED value
    well-formed, and a raised exception simply unconstrained.  That is enough
    for [gwalk] since delta (e''') — the throw node asks nothing. *)

Notation gpureP P m := (gpost (λ _, True) P m).

Lemma gwalk_bind_pure {E A B} (P : A → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gpureP P m → (∀ x, P x → gwalk None (k x)) → gwalk None (Defs.bind m k).
Proof.
  revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

Lemma gwalkx_bind_pure {E A B} (P : A → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gpureP P m → (∀ x, P x → gwalkx None (k x)) → gwalkx None (Defs.bind m k).
Proof.
  revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

(** [gpure] is [gsilent] with the throw arm opened up, so every [gsilent]
    fact of the sweep is available at a [gpure] leaf. *)
Lemma gpureP_mono {E A} (P P' : A → Prop) (m : Defs.monad E A) :
  (∀ x, P x → P' x) → gpureP P m → gpureP P' m.
Proof. intros HP. by apply gpost_mono. Qed.

(** [liftR] at the permissive postcondition — the shape [run_hart_active]
    uses the decoder in.  ([WeakShapeOverrides2.gpost_liftR] is the [gpost0]
    instance and does not apply.) *)
Lemma gpureP_liftR {A R E} (P : A → Prop) (m : Defs.monad E A) :
  gpureP P m → gpost (λ _ : R + E, True) P (Defs.liftR (R := R) m).
Proof. apply gpost_try_catch. intros e _. by apply gpost_throw. Qed.

(** …and the clause-spine rule the decoder's ~250 arms are chained by, in
    the [gpost] mode.  This is [DecodeSetU.goodbP_spine] transposed from the
    boolean, state-pinned traversal to the ∀-quantified one: the head's leaf
    predicate becomes a hypothesis for the continuation, so
    "every clause leaf satisfies [optP P]" becomes "the decoder's leaves
    satisfy [P]". *)
Definition optW {X} (P : X → Prop) (o : option X) : Prop :=
  match o with Some x => P x | None => True end.

Lemma gpureP_spine {E X} (P : X → Prop) (c : Defs.monad E (option X))
    (rest : Defs.monad E X) :
  gpureP (optW P) c → gpureP P rest →
  gpureP P (Defs.bind c (λ o, match o with
                              | Some r => Defs.returnm r
                              | None => rest
                              end)).
Proof.
  intros Hc Hrest. apply (gpost_bind _ (optW P)); [done|].
  by intros [i|] HQ; [apply gpost_returnm|].
Qed.

Lemma gpureP_spine_pure {E X} (P : X → Prop) (c : Defs.monad E (option X))
    (dflt : X) :
  gpureP (optW P) c → P dflt →
  gpureP P (Defs.bind c (λ o, Defs.returnm (match o with
                                            | Some r => r
                                            | None => dflt
                                            end))).
Proof.
  intros Hc Hd. apply (gpost_bind _ (optW P)); [done|].
  by intros [i|] HQ; apply gpost_returnm.
Qed.

(* ====================================================================== *)
(** ** 4. [gpure]: the mode the decoder's own cone is proved in

    THE TOWER HAS ONE MODE AND IT IS THE WRONG ONE HERE (finding (O7)).
    [WeakShapeGen01..15] prove [gwalk None], which permits memory events and
    therefore does NOT imply [gpost]/[gpureP]; §3's bind rules need the
    decoder's 35 monadic callees in the value-carrying mode.  [gpure] is that
    mode at the trivial postcondition — "no memory event, no barrier, no
    [Discard]" — i.e. [gsilent] with the throw arm opened up, which is what
    the three throwing functions of the decoder cone
    ([zicfiss_xSSE], [_rec_virtual_memory_supported] via [_rec_get_xLPE],
    [amo_encoding_valid]) need.  Every [gsilent] fact of the existing sweep
    transfers by [gsilent_gpure]. *)

Definition gpure {E A} (m : Defs.monad E A) : Prop :=
  gpost (λ _ : E, True) (λ _ : A, True) m.

Lemma gpure_gpost {E A} (Q : E → Prop) (m : Defs.monad E A) :
  (∀ e, Q e) → gpure m → gpost Q (λ _, True) m.
Proof. intros HQ. apply gpost_mono; [done|done]. Qed.

Lemma gpureP_gpure {E A} (P : A → Prop) (m : Defs.monad E A) :
  gpureP P m → gpure m.
Proof. rewrite /gpure. by apply gpost_mono. Qed.

Lemma gsilent_gpure {E A} (m : Defs.monad E A) : gsilent m → gpure m.
Proof. apply gsilent_gpost. Qed.

Lemma gpure_ret {E A} (x : A) : gpure (Interface.Ret x : Defs.monad E A).
Proof. done. Qed.
Lemma gpure_returnm {E A} (x : A) : gpure (Defs.returnm (E := E) x).
Proof. done. Qed.
Lemma gpure_throw {E A} (e : E) : gpure (Defs.throw (A := A) e).
Proof. done. Qed.
Lemma gpure_early_return {A R E} (r : R) :
  gpure (Defs.early_return (A := A) (E := E) r).
Proof. done. Qed.
Lemma gpure_fail {E A} msg : gpure (Defs.fail (A := A) (E := E) msg).
Proof. apply gpost_fail. Qed.
Lemma gpure_exit {E A} : gpure (Defs.exit (A := A) (E := E) tt).
Proof. apply gpost_exit. Qed.
Lemma gpure_assert_exp' {E} (b : bool) msg :
  gpure (Defs.assert_exp' (E := E) b msg).
Proof. apply gpost_assert_exp'. Qed.
Lemma gpure_assert_exp {E} (b : bool) msg :
  gpure (Defs.assert_exp (E := E) b msg).
Proof. rewrite /Defs.assert_exp. destruct b; [done|apply gpure_fail]. Qed.

Lemma gpure_bind {E A B} (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gpure m → (∀ x, gpure (k x)) → gpure (Defs.bind m k).
Proof.
  intros Hm Hk. rewrite /gpure. apply (gpost_bind _ (λ _, True)); [exact Hm|].
  intros x _. apply Hk.
Qed.

Lemma gpure_bind0 {E A} (m : Defs.monad E unit) (n : Defs.monad E A) :
  gpure m → gpure n → gpure (Defs.bind0 m n).
Proof. intros ??. by apply gpost_bind0. Qed.

Lemma gpureP_bind {E A B} (P : B → Prop) (m : Defs.monad E A)
    (k : A → Defs.monad E B) :
  gpure m → (∀ x, gpureP P (k x)) → gpureP P (Defs.bind m k).
Proof.
  intros Hm Hk. apply (gpost_bind _ (λ _, True)); [exact Hm|].
  intros x _. apply Hk.
Qed.

Lemma gpure_try_catch {A E1 E2} (m : Defs.monad E1 A) (h : E1 → Defs.monad E2 A) :
  gpure m → (∀ e, gpure (h e)) → gpure (Defs.try_catch m h).
Proof.
  intros Hm Hh. apply (gpost_try_catch (λ _, True)); [|exact Hm].
  intros e _. apply Hh.
Qed.

Lemma gpure_liftR {A R E} (m : Defs.monad E A) :
  gpure m → gpure (Defs.liftR (R := R) m).
Proof. apply gpureP_liftR. Qed.

Lemma gpure_catch_early_return {A E} (m : Defs.monadR A E A) :
  gpure m → gpure (Defs.catch_early_return m).
Proof.
  intros Hm. apply (gpost_try_catch (λ _, True)); [by intros [a|e] _|exact Hm].
Qed.

Lemma gpure_and_boolM {E} (l r : Defs.monad E bool) :
  gpure l → gpure r → gpure (Defs.and_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.and_boolM. apply gpure_bind; [done|by intros []].
Qed.

Lemma gpure_or_boolM {E} (l r : Defs.monad E bool) :
  gpure l → gpure r → gpure (Defs.or_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.or_boolM. apply gpure_bind; [done|by intros []].
Qed.

Lemma gpure_foreachM {E a Vars} (l : list a) (vars : Vars)
    (body : a → Vars → Defs.monad E Vars) :
  (∀ x v, gpure (body x v)) → gpure (Defs.foreachM l vars body).
Proof.
  intros Hb. revert vars. induction l as [|x l IHl]; intros vars; [done|].
  simpl. apply gpure_bind; [apply Hb|intros v; apply IHl].
Qed.

Lemma gpure_foreach_ZM_up' {E Vars} (from to step : Z) (n : nat) (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gpure (body z v)) →
  gpure (Defs.foreach_ZM_up' from to step n vars body).
Proof.
  intros Hb. revert from vars. induction n as [|n IH]; intros from vars.
  - rewrite /Defs.foreach_ZM_up'. by destruct (from <=? to)%Z.
  - simpl. destruct (from <=? to)%Z; [|done].
    apply gpure_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma gpure_foreach_ZM_down' {E Vars} (from to step : Z) (n : nat) (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gpure (body z v)) →
  gpure (Defs.foreach_ZM_down' from to step n vars body).
Proof.
  intros Hb. revert from vars. induction n as [|n IH]; intros from vars.
  - rewrite /Defs.foreach_ZM_down'. by destruct (to <=? from)%Z.
  - simpl. destruct (to <=? from)%Z; [|done].
    apply gpure_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma gpure_genlistM {E A} (f : nat → Defs.monad E A) (n : nat) :
  (∀ i, gpure (f i)) → gpure (Defs.genlistM f n).
Proof.
  intros Hf. rewrite /Defs.genlistM. apply gpure_foreachM.
  intros i xs. apply gpure_bind; [apply Hf|by intros].
Qed.

Lemma gpure_autocast_m {E m n} {T : Z → Type} `{H : Inhabited (T n)}
    (x : Defs.monad E (T m)) :
  gpure x → gpure (Defs.autocast_m (n := n) x).
Proof.
  intros Hx. rewrite /Defs.autocast_m. apply gpure_bind; [done|by intros].
Qed.

(** The sweep tactic for this mode.  Same discipline as [gw_solve]: the leaf
    is GATED on the goal being atomic (finding (O8)), the hint lookup goes
    first, and the model's constants stay opaque to it. *)
Create HintDb gpure discriminated.
#[export] Hint Constants Opaque : gpure.
#[export] Hint Resolve gpure_ret gpure_returnm gpure_throw gpure_early_return
  gpure_fail gpure_exit gpure_assert_exp gpure_assert_exp' : gpure.

Ltac gpu_step :=
  match goal with
  | |- gpure (Defs.bind _ _) => apply gpure_bind
  | |- gpure (Defs.bind0 _ _) => apply gpure_bind0
  | |- gpure (Defs.try_catch _ _) => apply gpure_try_catch
  | |- gpure (Defs.liftR _) => apply gpure_liftR
  | |- gpure (Defs.catch_early_return _) => apply gpure_catch_early_return
  | |- gpure (Defs.and_boolM _ _) => apply gpure_and_boolM
  | |- gpure (Defs.or_boolM _ _) => apply gpure_or_boolM
  | |- gpure (Defs.foreachM _ _ _) => apply gpure_foreachM
  | |- gpure (Defs.foreach_ZM_up _ _ _ _ _) => apply gpure_foreach_ZM_up'
  | |- gpure (Defs.foreach_ZM_down _ _ _ _ _) => apply gpure_foreach_ZM_down'
  | |- gpure (Defs.genlistM _ _) => apply gpure_genlistM
  | |- gpure (Defs.autocast_m _) => apply gpure_autocast_m
  | |- gpure (if ?b then _ else _) => destruct b
  | |- gpure (match ?x with _ => _ end) => destruct x
  | |- gpure (match ?x with _ => _ end _) => destruct x
  | |- gpure (match ?x with _ => _ end _ _) => destruct x
  end.

Ltac gpu_atomic :=
  lazymatch goal with
  | |- gpure (Defs.bind _ _) => fail
  | |- gpure (Defs.bind0 _ _) => fail
  | |- gpure (Defs.try_catch _ _) => fail
  | |- gpure (Defs.liftR _) => fail
  | |- gpure (Defs.catch_early_return _) => fail
  | |- gpure (Defs.and_boolM _ _) => fail
  | |- gpure (Defs.or_boolM _ _) => fail
  | |- gpure (Defs.foreachM _ _ _) => fail
  | |- gpure (Defs.foreach_ZM_up _ _ _ _ _) => fail
  | |- gpure (Defs.foreach_ZM_down _ _ _ _ _) => fail
  | |- gpure (Defs.genlistM _ _) => fail
  | |- gpure (Defs.autocast_m _) => fail
  | |- gpure (if _ then _ else _) => fail
  | |- gpure (match _ with _ => _ end) => fail
  | |- gpure (match _ with _ => _ end _) => fail
  | |- gpure (match _ with _ => _ end _ _) => fail
  | _ => idtac
  end.

Ltac gpu_leaf :=
  first
    [ exact I | assumption
    | gpu_atomic;
      first
        [ solve [eauto 1 with gpure nocore]
        | apply gsilent_gpure; solve [gsl_leaf] ] ].

Ltac gpu_solve :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | solve [gpu_leaf]
    | gpu_step ].
