(** * WeakShapeOverrides2.v — the VALUE side of the shape sweep (stage C5)

    [WeakShapeOverrides.v] gives the sweep its SHAPE vocabulary: predicates
    over the monad's event structure ([gwalk]/[gsilent]) and the
    tactics the generated shards run.  Every one of those predicates is blind
    to VALUES — and stage C5 found that the 47-function memory residue cannot
    be closed without them.  This file adds the missing piece and records the
    two obligations it exposes.

    §1  [gpost] — quiet-up-to-failure WITH a Ret-postcondition and a
        throw-postcondition.  It is [gsilent] with the [Interface.Ret] arm
        strengthened from [True] to [P x] and the [ExtraOutcome] arm weakened
        from [False] to [Q e], and it is what carries a value fact ACROSS a
        [bind] into the shape obligation of the continuation
        ([gwalk_bind_post]).
    §2  the first of the three semantic obligations stage C4 handed C5:
        [0 < split_width] out of [split_misaligned], i.e. the Sail
        precondition [0 < width] travelling down to the width of the
        [MemWrite] node — plus the write leaf it feeds, generalised over the
        access kind ([gwalk_write_ram_any]/[_solo], which replace
        [WeakShape] §6b's kind-specific instances: since C4's (O4) fix the
        window-closed write arm constrains only the width).
    §3  the second: [_rec_pt_walk], the model's [Acc]-fuelled page-table
        walker, by the same [fix]-on-the-accessibility-argument recipe
        [tools/gen_shape.py]'s [OVERRIDE_PROOFS] uses for [_rec_hartSupports]
        and the nine-way [stateen] block.
    §4  (O6), the stage-C5 FINDING, at its leaf: a ZERO-WIDTH memory write is
        not [gwalk]-able, so [∀ ast, gwalk (rv64d.execute ast)] — the
        shape of the whole instruction set, which is how [run_hart_active]
        uses [execute] — is FALSE, and seam (6) needs a DECODER postcondition
        (every width the decoder puts in an [instruction] is in [1;2;4;8]),
        not just the memory cone's hand lemmas.  See the file's §4 for the
        path and for what it means for C6. *)

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
Require Import Riscv.rv64d.

Set Default Proof Using "Type".

(* ====================================================================== *)
(** ** 1. [gpost]: the value-carrying companion of [gsilent]

    THE SHAPE PREDICATES ARE VALUE-BLIND, AND THE MEMORY CONE IS NOT.  Two of
    the residue's obligations are facts about the VALUE a prefix computes:

      - [checked_mem_write]'s [MemWrite] node must have nonzero width, and
        the width is [split_width], the second component of what
        [split_misaligned] RETURNED;
      - [checked_mem_read]'s exclusive read may open at most one window per
        instruction, i.e. the loop count [N] that [split_misaligned] RETURNED
        must be 1 — which holds because [pmaCheck] answers [CannotSplit] for
        every exclusive access kind.

    Neither can be stated with [gwalk]/[gsilent], which say nothing about
    [Interface.Ret]'s payload.  [gpost Q P m] says: [m] issues no memory
    event and no barrier; every value it RETURNS satisfies [P]; and every
    Sail exception it RAISES satisfies [Q].

    TWO DESIGN POINTS, both forced:

    (a) THE [ExtraOutcome] ARM IGNORES ITS CONTINUATION.  A [throw] is
        [Interface.Next (ExtraOutcome e) mret], and [bind] pushes the rest of
        the computation INTO that continuation — so an arm of the form
        [Q e ∧ ∀ r, gpost Q P (k r)] would demand [P] of every value at the
        throw of [Defs.throw] itself ([k = mret]), i.e. [∀ r, P r].  Ignoring
        the continuation is also exactly right for the consumer:
        [Defs.try_catch] — hence [catch_early_return] and [liftR], the only
        way this model ever observes an exception — DISCARDS it.

    (b) The [GenericFail] arm recurses (vacuously: [Interface.GenericFail]'s
        continuation is indexed by [False]), which is what makes [gpost]
        usable at all — ~100 of the model's functions contain an [exit] or an
        [internal_error], exactly as [gsilent] records. *)

Section Post.
Context {E A : Type}.
Local Notation mon := (Defs.monad E A).

Fixpoint gpost (Q : E → Prop) (P : A → Prop) (m : mon) {struct m} : Prop :=
  match m with
  | Interface.Ret x => P x
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → mon) → Prop with
       | Interface.MemRead _ _ => λ _, False
       | Interface.MemWrite _ _ => λ _, False
       | Interface.Barrier _ => λ _, False
       | Interface.ExtraOutcome e => λ _, Q e
       | Interface.Discard => λ _, False
       | Interface.GenericFail _ => λ k, ∀ r, gpost Q P (k r)
       | Interface.Choose ty =>
           match ty as t return (Values.choose_type t → mon) → Prop with
           | Values.ChooseReal => λ k, ∀ r, gpost Q P (k r)
           | _ => λ k, ∀ r, gpost Q P (k r)
           end
       | _ => λ k, ∀ r, gpost Q P (k r)
       end) k
  end.

End Post.

Arguments gpost {E A} Q P m.

(** The throw-free instance — the one the [bind] consumers below take. *)
Notation gpost0 P m := (gpost (λ _, False) P m).

(** [gsilent] is [gpost] with no information: same arms, [True] at [Ret],
    [False] at a throw. *)
Lemma gsilent_gpost {E A} (Q : E → Prop) (m : Defs.monad E A) :
  gsilent m → gpost Q (λ _, True) m.
Proof.
  induction m as [x|T oc k IH]; [done|].
  destruct oc; simpl; try done; try (intros H r; by apply IH).
  destruct ty; simpl; try done; intros H r; by apply IH.
Qed.

Lemma gpost_gsilent {E A} (P : A → Prop) (m : Defs.monad E A) :
  gpost0 P m → gsilent (E := E) m.
Proof.
  induction m as [x|T oc k IH]; [done|].
  destruct oc; simpl; try done; try (intros H r; by apply IH).
  destruct ty; simpl; try done; intros H r; by apply IH.
Qed.

Lemma gpost_mono {E A} (Q Q' : E → Prop) (P P' : A → Prop) (m : Defs.monad E A) :
  (∀ e, Q e → Q' e) → (∀ x, P x → P' x) → gpost Q P m → gpost Q' P' m.
Proof.
  intros HQ HP. induction m as [x|T oc k IH]; [by apply HP|].
  destruct oc; simpl; try done; try (intros H r; by apply IH);
    try (by apply HQ).
  destruct ty; simpl; try done; intros H r; by apply IH.
Qed.

Lemma gpost_ret {E A} (Q : E → Prop) (P : A → Prop) (x : A) :
  P x → gpost (E := E) Q P (Interface.Ret x).
Proof. done. Qed.

Lemma gpost_returnm {E A} (Q : E → Prop) (P : A → Prop) (x : A) :
  P x → gpost Q P (Defs.returnm (E := E) x).
Proof. done. Qed.

Lemma gpost_throw {E A} (Q : E → Prop) (P : A → Prop) (e : E) :
  Q e → gpost Q P (Defs.throw (A := A) e).
Proof. done. Qed.

Lemma gpost_early_return {A R E} (Q : R + E → Prop) (P : A → Prop) (r : R) :
  Q (inl r) → gpost Q P (Defs.early_return (A := A) (E := E) r).
Proof. done. Qed.

Lemma gpost_fail {E A} (Q : E → Prop) (P : A → Prop) (msg : String.string) :
  gpost Q P (Defs.fail (A := A) (E := E) msg).
Proof. rewrite /Defs.fail /=. by intros []. Qed.

Lemma gpost_exit {E A} (Q : E → Prop) (P : A → Prop) :
  gpost Q P (Defs.exit (A := A) (E := E) tt).
Proof. apply gpost_fail. Qed.

Lemma gpost_assert_exp' {E} (Q : E → Prop) (b : bool) msg :
  gpost Q (λ _, True) (Defs.assert_exp' b msg).
Proof. rewrite /Defs.assert_exp'. destruct b; [done|apply gpost_fail]. Qed.

(** THE BIND.  The postcondition of [m] is the hypothesis of [k]'s. *)
Lemma gpost_bind {E A B} (Q : E → Prop) (P : A → Prop) (P' : B → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gpost Q P m → (∀ x, P x → gpost Q P' (k x)) → gpost Q P' (Defs.bind m k).
Proof.
  revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

Lemma gpost_bind0 {E A} (Q : E → Prop) (P : A → Prop)
    (m : Defs.monad E unit) (n : Defs.monad E A) :
  gpost Q (λ _, True) m → gpost Q P n → gpost Q P (Defs.bind0 m n).
Proof.
  intros H1 H2. rewrite /Defs.bind0.
  apply (gpost_bind Q (λ _, True)); [done|by intros].
Qed.

(** THE HANDLER RULE, and the reason the exception postcondition is carried
    at all: [Defs.try_catch] is where [Q] is CONSUMED — and where it becomes
    part of the value postcondition, since the handler returns a value.  Its
    two instances below ([liftR], [catch_early_return]) are the only two the
    model uses. *)
Lemma gpost_try_catch {A E1 E2} (Q1 : E1 → Prop) (Q2 : E2 → Prop) (P : A → Prop)
    (m : Defs.monad E1 A) (h : E1 → Defs.monad E2 A) :
  (∀ e, Q1 e → gpost Q2 P (h e)) →
  gpost Q1 P m → gpost Q2 P (Defs.try_catch m h).
Proof.
  intros Hh. induction m as [x|T oc k IH]; intros Hm; [done|].
  destruct oc; simpl in Hm |- *; try (intros r; by apply IH); try done;
    try (by apply Hh).
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

(** [liftR] wraps a throw-FREE computation into the early-return monad; the
    value postcondition survives and the exception postcondition is
    vacuous. *)
Lemma gpost_liftR {A R E} (Q : R + E → Prop) (P : A → Prop) (m : Defs.monad E A) :
  gpost0 P m → gpost Q P (Defs.liftR (R := R) m).
Proof. apply gpost_try_catch. by intros e []. Qed.

(** [catch_early_return] TURNS THE EXCEPTION POSTCONDITION INTO PART OF THE
    VALUE POSTCONDITION — which is why the two must be carried together: an
    early return is how the memory cone's prefix reports a fault, and the
    fault arms are exactly the ones the shape obligation does not care
    about. *)
Lemma gpost_catch_early_return {A E} (P : A → Prop) (m : Defs.monadR A E A) :
  gpost (λ e, match e with inl a => P a | inr _ => False end) P m →
  gpost0 P (Defs.catch_early_return m).
Proof.
  apply gpost_try_catch. by intros [a|e] He.
Qed.

(** THE CONSUMERS: a value fact crossing into a SHAPE obligation. *)
Lemma gwalk_bind_post {E A B} (P : A → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gpost0 P m → (∀ x, P x → gwalk (k x)) → gwalk (Defs.bind m k).
Proof.
  revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

Lemma gsilent_bind_post {E A B} (P : A → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gpost0 P m → (∀ x, P x → gsilent (k x)) → gsilent (Defs.bind m k).
Proof.
  revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

(** The sweep tactic, in the same shape as [gsl_solve]/[gw_solve]: descend
    through the combinators, split every branch, close a value-free leaf out
    of the [gsilent] machinery and a value leaf by the postcondition. *)
Ltac gp_step :=
  match goal with
  | |- gpost _ _ (Defs.bind _ _) => eapply gpost_bind
  | |- gpost _ _ (Defs.bind0 _ _) => eapply gpost_bind0
  | |- gpost _ _ (Defs.liftR _) => apply gpost_liftR
  | |- gpost _ _ (Defs.catch_early_return _) => apply gpost_catch_early_return
  | |- gpost _ _ (if ?b then _ else _) => destruct b
  | |- gpost _ _ (match ?x with _ => _ end) => destruct x
  | |- gpost _ _ (match ?x with _ => _ end _) => destruct x
  end.

Ltac gp_leaf :=
  first
    [ assumption
    | apply gpost_fail | apply gpost_exit | apply gpost_assert_exp'
    | apply gpost_ret | apply gpost_returnm
    | apply gsilent_gpost; solve [gsl_leaf] ].

Ltac gp_solve :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | solve [gp_leaf]
    | gp_step ].

(* ====================================================================== *)
(** ** 2. [0 < split_width]: the first of the three semantic obligations

    Stage C4 left C5 three obligations that are semantic rather than
    syntactic.  This is the first: [checked_mem_write]'s [MemWrite] node has
    width [split_width], the second component of what [split_misaligned]
    returned, and [WeakSailLTS.sail_shaped]'s write arm demands a NONZERO
    width.  [split_misaligned] returns [(1, width)] on the unsplit path, so
    the obligation is the Sail precondition [0 < width] travelling down —
    plus, on the split path, [0 < pow2 (min (ctz addr) (ctz width))], which
    needs only that a count of trailing zeros is nonnegative.

    THE OBLIGATION DOES NOT STOP HERE: [0 < width] has to come from
    somewhere, and §4 records where the chain breaks. *)

Lemma foreach_Z_down'_inv {Vars} (I : Vars → Prop) from to step off n vars
    (body : ∀ (z : Z), Vars → Vars) :
  I vars → (∀ z v, (to <= z)%Z → I v → I (body z v)) →
  I (Values.foreach_Z_down' from to step off n vars body).
Proof.
  revert off vars. induction n as [|n IHn]; intros off vars Hv Hb; simpl;
    destruct (sumbool_of_bool (to <=? from + off)%Z) as [Hle|Hle]; try done.
  apply IHn; [|done]. apply Hb; [by apply Z.leb_le|done].
Qed.

Lemma count_trailing_zeros_nonneg {N} (x : Values.mword N) :
  (0 <= N)%Z → (0 <= count_trailing_zeros x)%Z.
Proof.
  intros HN. rewrite /count_trailing_zeros /Values.foreach_Z_down.
  apply (foreach_Z_down'_inv (λ r : Z, (0 <= r)%Z)); [done|].
  intros z v Hz Hv. by destruct (eq_vec _ _).
Qed.

Lemma pow2_pos (e : Z) : (0 <= e)%Z → (0 < Values.pow2 e)%Z.
Proof. intros He. rewrite /Values.pow2 /Values.pow. by apply Z.pow_pos_nonneg. Qed.

Lemma gpost_split_access {n} (addr : Values.mword n) (width : Z) :
  (0 <= n)%Z →
  gpost0 (λ p, (0 < snd p)%Z) (split_access addr width).
Proof.
  intros Hn. cbv [split_access].
  apply (gpost_bind _ (λ _, True)); [apply gpost_assert_exp'|].
  intros _ _. apply gpost_returnm. simpl. apply pow2_pos.
  apply Z.min_glb; by apply count_trailing_zeros_nonneg.
Qed.

(** THE LEMMA THE MEMORY CONE NEEDS.  [split_misaligned] is where the Sail
    precondition [0 < width ≤ 4096] becomes the width of an actual memory
    event — and it is the only place in the model where it does, since both
    [checked_mem_read] and [checked_mem_write] take their per-access width
    from here. *)
Lemma gpost_split_misaligned (pa : physaddr) (width awe : Z) (spl : Splittability) :
  (0 < width)%Z →
  gpost0 (λ p, (0 < snd p)%Z) (split_misaligned pa width awe spl).
Proof.
  intros Hw. destruct pa as [addr]. cbv [split_misaligned].
  destruct (orb _ _); [by apply gpost_returnm|].
  cbv [sys_misaligned_byte_by_byte]. by apply gpost_split_access.
Qed.

(** …and the same fact in the form the two [checked_mem_*] proofs consume it:
    through the [liftR] that wraps every call in their early-return
    bodies. *)
Lemma gpost_liftR_split_misaligned {R} (pa : physaddr) (width awe : Z)
    (spl : Splittability) (Q : R + exception → Prop) :
  (0 < width)%Z →
  gpost Q (λ p, (0 < snd p)%Z)
        (Defs.liftR (R := R) (split_misaligned pa width awe spl)).
Proof. intros Hw. by apply gpost_liftR, gpost_split_misaligned. Qed.

(** THE WRITE LEAF, GENERALISED OVER THE ACCESS KIND.  Since stage C4's (O4)
    fix the window-CLOSED [MemWrite] arm constrains only the WIDTH, so
    [WeakShape] §6b's three kind-specific leaves ([gwalk_write_ram_plain] /
    [_con] / and the [Write_RISCV_conditional_release] instance of the latter)
    collapse into ONE lemma that holds for EVERY [write_kind] — including the
    three the model marks unused, whose arms are [internal_error]s, i.e.
    [ExtraOutcome] nodes that the walk crosses with the same obligation on the
    continuation.  This is the shape the memory cone actually needs, because
    the kind there is a BOUND VARIABLE ([write_kind_of_flags aq rl con]'s
    result), never a literal. *)
Local Ltac mred :=
  cbn [Defs.bind Defs.bind0 Defs.returnm returnM Interface.iMon_bind].

Lemma gwalk_write_ram_any {B} wk addr width data meta (k : _ → M B) :
  (0 < width)%Z →
  (∀ r, gwalk (k r)) →
  gwalk (Defs.bind (write_ram wk (Physaddr addr) width data meta) k).
Proof.
  intros Hw Hk.
  have Hn : Z.to_N width ≠ 0%N by apply to_N_nonzero.
  cbv [write_ram]. destruct wk; mred; cbv [Defs.sail_mem_write]; mred;
    (* the three "unused" kinds are [internal_error] nodes, i.e.
       [Interface.ExtraOutcome]s, which delta (e''') admits outright *)
    first [ apply gwalk_MemWrite_plain; [by right|mred; apply Hk] | done ].
Qed.

Lemma gwalk_write_ram_solo wk addr width data meta :
  (0 < width)%Z → gwalk (write_ram wk (Physaddr addr) width data meta).
Proof.
  intros Hw.
  have Hn : Z.to_N width ≠ 0%N by apply to_N_nonzero.
  cbv [write_ram]. destruct wk; mred; cbv [Defs.sail_mem_write]; mred;
    first [ apply gwalk_MemWrite_plain; [by right|mred; apply gwalk_ret] | done ].
Qed.

(* ====================================================================== *)
(** ** 3. [_rec_pt_walk]: the second semantic obligation

    The model's page-table walker is a [Fixpoint] on an [Acc (Zwf 0)]
    argument, so [cbv] + [gw_solve] cannot do it: like [_rec_hartSupports]
    and the nine-way [stateen] block in [tools/gen_shape.py]'s
    [OVERRIDE_PROOFS], it needs a [fix] on the ACCESSIBILITY argument, with
    the induction hypothesis asserted at the accessibility SUBTERM (applying
    it anywhere else breaks the guard condition, and [eauto] will not invent
    the instance).

    The lemma is stated MODULO ITS THREE MONADIC CALLEES.  Two of them
    ([pte_is_invalid], [check_leaf_pte]) are ordinary sweep material; the
    third, [read_pte], is the memory leaf the whole walk exists to issue, and
    it is what §4 says is still owed.  Stating them as hypotheses is what
    makes this file independent of the generated tower — [WeakShapeTop] can
    discharge the first two out of `gshape` the moment the shards are
    loaded.

    COVERAGE HOLE FOUND HERE, and fixed in the generator:
    [check_leaf_pte] was in NEITHER the generated set NOR the recorded
    residue.  [gen_shape.py]'s [is_monadic] tested the definition's head for
    [' M ('], and Sail had wrapped this one signature so that its [: M (...)]
    starts a line — so the function was silently classified non-monadic.  The
    test now normalises whitespace first; [check_leaf_pte] itself is in the
    generator's [SKIP] set (and hence in the reported residue), because
    proving it here beside [_rec_pt_walk] keeps the built shards
    byte-identical. *)

Section PtWalk.

Hypothesis Hread_pte :
  ∀ pa sz, gwalk (read_pte pa sz).
Hypothesis Hpte_is_invalid :
  ∀ fl ext, gwalk (pte_is_invalid fl ext).
Hypothesis Hcheck_leaf_pte :
  ∀ sv vpn access priv mxr ds pte pte_addr level ext,
    gwalk (check_leaf_pte sv vpn access priv mxr ds pte pte_addr level ext).

Lemma gw__rec_pt_walk :
  ∀ sv vpn access priv mxr ds base level global ext rl acc,
    gwalk (_rec_pt_walk sv vpn access priv mxr ds base level global ext rl acc).
Proof using Hread_pte Hpte_is_invalid Hcheck_leaf_pte.
  fix IH 12. intros sv vpn access priv mxr ds base level global ext rl acc.
  destruct acc as [acc].
  assert (K : ∀ y H sv' vpn' access' priv' mxr' ds' base' level' global' ext',
                gwalk (_rec_pt_walk sv' vpn' access' priv' mxr' ds' base' level'
                                    global' ext' y (acc y H)))
    by (intros; apply IH).
  clear IH.
  cbv [_rec_pt_walk]. gw_solve.
Qed.

Lemma gw_pt_walk :
  ∀ a0 a1 a2 a3 a4 a5 a6 level a8 a9,
    gwalk (pt_walk a0 a1 a2 a3 a4 a5 a6 level a8 a9).
Proof using Hread_pte Hpte_is_invalid Hcheck_leaf_pte.
  intros. cbv [pt_walk]. apply gw__rec_pt_walk.
Qed.

End PtWalk.

(* ====================================================================== *)
(** ** 4. (O6) — THE STAGE-C5 FINDING: the memory cone's width obligation
    does NOT stop at the memory cone, and [∀ ast, gwalk (execute ast)]
    is FALSE

    §2 discharges [0 < split_width] FROM [0 < width].  The question C5 then
    had to answer is where [0 < width] itself comes from, and the answer is:
    nowhere in the Coq model.  Sail's [(0 <? width) && (width <=? 4096)]
    precondition is emitted as a COMMENT — [execute_STORE]'s [width] is a
    plain [Z], as is the [width] field the [instruction] AST carries — so

        execute (STORE (imm, rs2, rs1, 0))

    is a well-typed instance of the [∀ ast] fact any compositional route to
    [try_step] needs, and on it the model issues a ZERO-WIDTH [MemWrite]:
    [split_misaligned] returns [(1, width)] on its unsplit path, so
    [split_width = 0], and [WeakSailLTS.sail_shaped]'s write arm (like
    [gwalk]'s and [sail_mstep]'s [LStore] arm) demands a nonzero
    width.  The leaf fact is [gwalk_write_ram_zero_False] below.

    WHY THE ∀ IS UNAVOIDABLE ON THE COMPOSITIONAL ROUTE, and why this is a
    real obligation rather than a refutation of [sail_shaped (riscv_step b)]:

      - [rv64d.run_hart_active] applies [execute] TWICE — once to
        [ext_decode w]'s output and once, in the [ExecuteAs other_inst] arm,
        to an [instruction] VALUE the first [execute] returned.  Neither is a
        syntactic instruction, so the sweep's per-function lemma for
        [execute] can only be the [∀ ast] one;
      - but the widths the DECODER actually builds are [word_width]-derived,
        i.e. always in [[1;2;4;8]], so [sail_shaped (riscv_step b)] itself is
        NOT refuted.  What is refuted is the route: the tower cannot climb
        past [execute] without a DECODER POSTCONDITION — [gpost] of
        [encdec_backwards] with [P] = "every width field of the resulting
        [instruction] is in [1;2;4;8]" (and the same for the [ExecuteAs]
        values, which is a postcondition of [execute] itself).

    THAT IS A SECOND GENERATOR-SCALE ITEM, and the honest scope note for C6:
    [encdec_backwards] is ~4000 lines of right-nested [bind]/[match] with
    ~250 arms, and the postcondition sweep needs [gpost] lemmas — NOT the
    [gwalk] ones the shards prove — for the whole prefix cone it
    walks.  [gwalk] does not imply [gpost]/[gsilent] (it permits memory
    events), so those lemmas cannot be recovered from the tower that exists;
    they have to be EMITTED IN THE SAME PASS.  The scheduling lesson, which
    is the expensive half of this finding: A GENERATED SWEEP MUST EMIT EVERY
    MODE IT WILL EVER NEED IN ONE PASS, because the shards form a serial
    [Require] chain and a second mode costs the whole chain again.

    The same [gpost] machinery is what the residue's THIRD semantic
    obligation needs: [checked_mem_read]'s exclusive read must be the only
    memory event of its instruction, which holds because [pmaCheck] returns
    [CannotSplit] for [LoadReserved]/[StoreConditional]/[Atomic] (their
    [is_mag_applicable_access] is [false] and their [pma_misaligned_exception]
    is an [internal_error]/[Some], so a misaligned exclusive access faults
    before any [read_ram]), hence [split_misaligned] returns [N = 1].  It is
    a [gpost] of [pmaCheck] — again over a prefix cone whose [gpost] lemmas
    do not exist yet. *)

Lemma gwalk_write_ram_zero_False {B} addr data meta (k : _ → M B) :
  dev_addr addr = false →
  gwalk (Defs.bind (write_ram Write_plain (Physaddr addr) 0 data meta) k) →
  False.
Proof.
  intros Hd. cbv [write_ram].
  cbn [Defs.bind Defs.bind0 Defs.returnm returnM Interface.iMon_bind].
  cbv [Defs.sail_mem_write].
  cbn [Defs.bind Defs.bind0 Defs.returnm returnM Interface.iMon_bind].
  simpl. rewrite Hd. by intros [Hn _].
Qed.

(** The same node is fine at a nonzero width — [WeakShape.gwalk_write_ram_plain]
    — so this is a WIDTH obligation, not a shape defect: exactly one
    hypothesis, [0 < width], separates the two, and §2 shows it is enough to
    reach the [MemWrite] node.  What is missing is a supplier for it. *)
