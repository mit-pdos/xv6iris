(** * WeakShapeOverrides.v — the HAND-WRITTEN half of the stage-C3 sweep

    [WeakShape.v] is the compositional kit; [WeakShapeGen*.v] are the
    machine-generated per-function lemmas over [Riscv.rv64d].  THIS file is
    what sits between them:

      §1  the [gwalk]-mode combinator lemmas the generated sweep needs and
          [WeakShape] did not have (it proved most combinators only in the
          [gok]/[gquiet] modes, which do not cover a function whose cone
          contains a failure node);
      §2  [gsilent] — quiet-UP-TO-FAILURE, the predicate the ~100
          [exit]/[internal_error]/[assert_exp] functions actually satisfy
          ([gquiet] refutes a [GenericFail]; [gwalk]/[amo_tail] do not, since
          a [GenericFail] continuation is [False → _]);
      §3  the ESCAPE INDEX that stage C2 asked C3 for: [gwalkx], the WEAK
          (abandonment-permitting) reading of the window, with the two bind
          lemmas it splits into;
      §4  [gw_solve] / [gq_solve], the tactics the generated shards run;
      §5  the stage-C3 findings (O4)/(O5) at their sites: (O4) is FIXED in
          C4 and its two refutations are replaced by the positive leaves;
          (O5) is what [WeakShapeTop]'s record assumes.

    §5 is written up in
    [claude-notes/projects/weak-memory-premises.md]; the short form:

    (O4) A STANDALONE STORE-CONDITIONAL — FIXED IN C4.
         [rv64d.execute_STORECON] issues a [Write_RISCV_conditional] RAM
         write with NO exclusive read anywhere in the instruction (the
         reservation lives in the model's pure
         [match_reservation]/[valid_reservation] axioms, not in a memory
         event).  Through C3 [sail_shaped]'s [MemWrite] arm demanded
         [ak_latest (classify …) = false] off device addresses, and a
         conditional write classifies as [AV_exclusive], i.e. [ak_latest =
         true], so [∀ b, sail_shaped (riscv_step b)] was FALSE — the exact
         mirror image of C1's (O2), which found the READ side (an exclusive
         read with no conditional write) and fixed it at the LTS.  C4 took
         the symmetric fix ([WeakSailLTS] delta (e'')): the window-closed
         [MemWrite] arms accept ANY RAM write and a standalone conditional
         write steps as a plain [LStore].  See [gwalkx_write_ram_con] here
         and [WeakShape.gwalk_write_ram_con].

    (O5) THREE OPAQUE MONADIC AXIOMS.  [rv64d] declares
         [load_reservation], [cancel_reservation] and [plat_term_write] as
         [Axiom]s of monad type, and all three are reachable from
         [try_step] ([vmem_read_addr], [execute_STORECON], [htif_store]).
         No shape fact about them is provable OR refutable, so neither
         [∀ b, sail_shaped (riscv_step b)] nor [∀ b, sail_live (riscv_step b)]
         can be closed without three assumptions about them — see
         [WeakShapeTop.v], which states them as an explicit record rather
         than as axioms.
*)

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

Set Default Proof Using "Type".

(* ====================================================================== *)
(** ** 1. The [gwalk]-mode combinators

    [WeakShape] proves most of the vocabulary in the [gok] mode (shape AND
    liveness together) or the [gquiet] mode.  The generated sweep needs the
    SHAPE mode on its own, because a function whose cone contains an
    [exit]/[internal_error] is shaped but not live and not quiet. *)

Lemma gwalk_and_boolM {E} w (l r : Defs.monad E bool) :
  gwalk w l → gwalk None r → gwalk w (Defs.and_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.and_boolM.
  apply gwalk_bind; [done|]. by intros [|].
Qed.

Lemma gwalk_or_boolM {E} w (l r : Defs.monad E bool) :
  gwalk w l → gwalk None r → gwalk w (Defs.or_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.or_boolM.
  apply gwalk_bind; [done|]. by intros [|].
Qed.

Lemma gwalk_genlistM {E A} (f : nat → Defs.monad E A) (n : nat) :
  (∀ i, gwalk None (f i)) → gwalk None (Defs.genlistM f n).
Proof.
  intros Hf. rewrite /Defs.genlistM. apply gwalk_foreachM; [|done].
  intros i xs. apply gwalk_bind; [apply Hf|intros x; apply gwalk_ret].
Qed.

Lemma gwalk_autocast_m {E m n} {T : Z → Type} `{H : Inhabited (T n)}
    (x : Defs.monad E (T m)) :
  gwalk None x → gwalk None (Defs.autocast_m (n := n) x).
Proof.
  intros Hx. rewrite /Defs.autocast_m.
  apply gwalk_bind; [done|intros v; apply gwalk_ret].
Qed.

Lemma gwalk_foreach_ZM_up {E Vars} from to step (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gwalk None (body z v)) →
  gwalk None (Defs.foreach_ZM_up from to step vars body).
Proof. intros Hb. by apply gwalk_foreach_ZM_up'. Qed.

Lemma gwalk_foreach_ZM_down {E Vars} from to step (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gwalk None (body z v)) →
  gwalk None (Defs.foreach_ZM_down from to step vars body).
Proof. intros Hb. by apply gwalk_foreach_ZM_down'. Qed.

(* ====================================================================== *)
(** ** 2. [gsilent]: quiet UP TO FAILURE

    [WeakShape.gquiet] refutes a [GenericFail] node, which makes it unusable
    as the sweep's default predicate: ~100 of the 346 monadic functions
    reachable from [try_step] contain an [exit tt] / [internal_error] /
    [reserved_behavior] / a non-constant [assert_exp].  All of those are
    still SHAPED (a [GenericFail] continuation is [False → _]) and still
    WINDOW-CROSSING (ditto for [amo_tail]), which is exactly what [gsilent]
    records.  [gquiet → gsilent → gwalk None], and [gsilent] is what §3's
    escaping bind lemma consumes. *)

Section Silent.
Context {E A : Type}.
Local Notation mon := (Defs.monad E A).

Fixpoint gsilent (m : mon) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → mon) → Prop with
       | Interface.MemRead _ _ => λ _, False
       | Interface.MemWrite _ _ => λ _, False
       | Interface.Barrier _ => λ _, False
       | Interface.ExtraOutcome _ => λ _, False
       | Interface.Discard => λ _, False
       | Interface.GenericFail _ => λ k, ∀ r, gsilent (k r)
       | Interface.Choose ty =>
           match ty as t return (Values.choose_type t → mon) → Prop with
           | Values.ChooseReal => λ k, ∀ r, gsilent (k r)
           | _ => λ k, ∀ r, gsilent (k r)
           end
       | _ => λ k, ∀ r, gsilent (k r)
       end) k
  end.

End Silent.

Arguments gsilent {E A} m.

Lemma gquiet_gsilent {E A} (m : Defs.monad E A) : gquiet m → gsilent m.
Proof.
  induction m as [x|T oc k IH]; [done|].
  destruct oc; simpl; try done; try (intros H r; by apply IH).
  destruct ty; simpl; try done; intros H r; by apply IH.
Qed.

Lemma gsilent_gwalk {E A} (m : Defs.monad E A) : gsilent m → gwalk None m.
Proof.
  induction m as [x|T oc k IH]; [done|].
  destruct oc; simpl; try done; try (intros H r; by apply IH).
  destruct ty; simpl; try done; intros H r; by apply IH.
Qed.

Lemma gsilent_amo_tail pa n (m : M unit) : gsilent m → amo_tail pa n m.
Proof.
  induction m as [x|T oc k IH]; [done|].
  destruct oc; simpl; try done; try (intros H r; by apply IH).
  destruct ty; simpl; try done; intros H r; by apply IH.
Qed.

Lemma gsilent_bind {E A B} (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gsilent m → (∀ x, gsilent (k x)) → gsilent (Defs.bind m k).
Proof.
  induction m as [x|T oc k0 IH]; intros Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

Lemma gsilent_bind0 {E A} (m : Defs.monad E unit) (n : Defs.monad E A) :
  gsilent m → gsilent n → gsilent (Defs.bind0 m n).
Proof. intros ??. by apply gsilent_bind. Qed.

Lemma gsilent_fail {E A} (msg : String.string) :
  gsilent (Defs.fail (A := A) (E := E) msg).
Proof. rewrite /Defs.fail /=. by intros []. Qed.

Lemma gsilent_exit {E A} : gsilent (Defs.exit (A := A) (E := E) tt).
Proof. apply gsilent_fail. Qed.

Lemma gsilent_assert_exp {E} (b : bool) msg :
  gsilent (E := E) (Defs.assert_exp b msg).
Proof. rewrite /Defs.assert_exp. destruct b; [done|apply gsilent_fail]. Qed.

Lemma gsilent_assert_exp' {E} (b : bool) msg :
  gsilent (E := E) (Defs.assert_exp' b msg).
Proof. rewrite /Defs.assert_exp'. destruct b; [done|apply gsilent_fail]. Qed.

Lemma gsilent_try_catch {A E1 E2} (m : Defs.monad E1 A) (h : E1 → Defs.monad E2 A) :
  gsilent m → gsilent (Defs.try_catch m h).
Proof.
  induction m as [x|T oc k IH]; intros Hm; [done|].
  destruct oc; simpl in Hm |- *; try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

Lemma gsilent_liftR {A R E} (m : Defs.monad E A) :
  gsilent m → gsilent (Defs.liftR (R := R) m).
Proof. apply gsilent_try_catch. Qed.

Lemma gsilent_catch_early_return {A E} (m : Defs.monadR A E A) :
  gsilent m → gsilent (Defs.catch_early_return m).
Proof. apply gsilent_try_catch. Qed.

Lemma gsilent_and_boolM {E} (l r : Defs.monad E bool) :
  gsilent l → gsilent r → gsilent (Defs.and_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.and_boolM.
  apply gsilent_bind; [done|]. by intros [|].
Qed.

Lemma gsilent_or_boolM {E} (l r : Defs.monad E bool) :
  gsilent l → gsilent r → gsilent (Defs.or_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.or_boolM.
  apply gsilent_bind; [done|]. by intros [|].
Qed.

Lemma gsilent_foreachM {E a Vars} (l : list a) (vars : Vars)
    (body : a → Vars → Defs.monad E Vars) :
  (∀ x v, gsilent (body x v)) → gsilent (Defs.foreachM l vars body).
Proof.
  intros Hb. revert vars. induction l as [|x xs IH]; intros vars; [done|].
  simpl. apply gsilent_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma gsilent_foreach_ZM_up' {E Vars} (from to step : Z) (n : nat) (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gsilent (body z v)) →
  gsilent (Defs.foreach_ZM_up' from to step n vars body).
Proof.
  intros Hb. revert from vars. induction n as [|n IH]; intros from vars.
  - rewrite /Defs.foreach_ZM_up'. by destruct (from <=? to)%Z.
  - simpl. destruct (from <=? to)%Z; [|done].
    apply gsilent_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma gsilent_foreach_ZM_down' {E Vars} (from to step : Z) (n : nat) (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gsilent (body z v)) →
  gsilent (Defs.foreach_ZM_down' from to step n vars body).
Proof.
  intros Hb. revert from vars. induction n as [|n IH]; intros from vars.
  - rewrite /Defs.foreach_ZM_down'. by destruct (to <=? from)%Z.
  - simpl. destruct (to <=? from)%Z; [|done].
    apply gsilent_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma gsilent_genlistM {E A} (f : nat → Defs.monad E A) (n : nat) :
  (∀ i, gsilent (f i)) → gsilent (Defs.genlistM f n).
Proof.
  intros Hf. rewrite /Defs.genlistM. apply gsilent_foreachM.
  intros i xs. apply gsilent_bind; [apply Hf|done].
Qed.

Lemma gsilent_autocast_m {E m n} {T : Z → Type} `{H : Inhabited (T n)}
    (x : Defs.monad E (T m)) :
  gsilent x → gsilent (Defs.autocast_m (n := n) x).
Proof.
  intros Hx. rewrite /Defs.autocast_m. apply gsilent_bind; [done|done].
Qed.

Lemma gsilent_choose_from_list {A E} (descr : String.string) (xs : list A) :
  gsilent (E := E) (Defs.choose_from_list descr xs).
Proof.
  rewrite /Defs.choose_from_list. apply gsilent_bind; [done|].
  intros idx. destruct (List.nth_error xs (Z.to_nat idx)); [done|apply gsilent_fail].
Qed.

(** The window-crossing bind, in the [gsilent] mode: a silent prefix carries
    an OPEN window into its continuation.  This is [WeakShape.gwalk_bind_quiet]
    with the failure nodes allowed. *)
Lemma gwalk_bind_silent {E A B} w (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gsilent m → (∀ x, gwalk w (k x)) → gwalk w (Defs.bind m k).
Proof.
  induction m as [x|T oc k0 IH]; intros Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

(* ====================================================================== *)
(** ** 3. THE ESCAPE INDEX (stage C2's C3 item)

    [WeakShape.gwalk (Some _)] is the CLOSED reading of an open window: the
    conditional write MUST arrive before the monad returns.  C2 weakened
    [WeakSailLTS.amo_tail]'s [Interface.Ret] arm to [True] — a window may be
    ABANDONED — but the kit could not follow, because weakening
    [gwalk (Some _) (Ret _)] refutes [gwalk_bind]: an abandoned window
    ESCAPES a bind into the continuation.

    [gwalkx] is the weak reading, added HERE rather than by editing [gwalk],
    so that every closed-reading lemma of [WeakShape] stays literally
    unchanged and transfers by [gwalk_gwalkx].  The bind splits in two:

      - [gwalkx_bind]        — [m] escape-FREE (the [gwalk] hypothesis), the
                               continuation arbitrary.  This is the case for
                               the ~330 functions that issue no exclusive
                               read.
      - [gwalkx_bind_silent] — [m] MAY escape, and then the continuation must
                               be crossable under an arbitrary window, i.e.
                               [gsilent].  This is the case at
                               [execute_LOADRES] and the abandoning arms of
                               [execute_AMO] / [update_and_write_pte].

    [gwalkx None] still implies [sail_shaped] and [gwalkx (Some _)] still
    implies [amo_tail], so the escape index costs the consumers nothing. *)

Section WalkX.
Context {E A : Type}.
Local Notation mon := (Defs.monad E A).

Fixpoint gwalkx (w : win) (m : mon) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → mon) → Prop with
       | Interface.MemRead n req => λ k,
           match w with
           | Some _ => False
           | None =>
               if dev_addr (Interface.ReadReq.pa req)
               then ∀ v : bv (8 * n), gwalkx None (k (inl (v, None)))
               else
                 ak_coh (classify (Interface.ReadReq.access_kind req)) = false ∧
                 (if ak_latest (classify (Interface.ReadReq.access_kind req))
                  then ∀ v : bv (8 * n),
                         gwalkx (Some (Interface.ReadReq.pa req, n))
                                (k (inl (v, None)))
                  else ∀ v : bv (8 * n), gwalkx None (k (inl (v, None))))
           end
       | Interface.MemWrite n' req' => λ k,
           match w with
           | Some (pa, n) =>
               dev_addr (Interface.WriteReq.pa req') = false ∧
               Interface.WriteReq.pa req' = pa ∧ n' = n ∧ n' ≠ 0%N ∧
               ak_latest (classify (Interface.WriteReq.access_kind req')) = true ∧
               gwalkx None (k (inl None))
           | None =>
               (* any RAM write of nonzero width — [WeakShape.gwalk]'s C4
                  arm, mirrored ([WeakSailLTS] delta (e'')) *)
               (if dev_addr (Interface.WriteReq.pa req') then True
                else n' ≠ 0%N) ∧
               gwalkx None (k (inl None))
           end
       | Interface.Barrier _ => λ k,
           match w with
           | Some _ => False
           | None => ∀ r, gwalkx None (k r)
           end
       | Interface.ExtraOutcome _ => λ k,
           match w with
           | Some _ => False
           | None => ∀ r, gwalkx None (k r)
           end
       | _ => λ k, ∀ r, gwalkx w (k r)
       end) k
  end.

End WalkX.

Arguments gwalkx {E A} w m.

Lemma gwalk_gwalkx {E A} w (m : Defs.monad E A) : gwalk w m → gwalkx w m.
Proof.
  revert w. induction m as [x|T oc k IH]; intros w Hm; [done|].
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
Qed.

Lemma gsilent_gwalkx {E A} w (m : Defs.monad E A) : gsilent m → gwalkx w m.
Proof.
  revert w. induction m as [x|T oc k IH]; intros w Hm; [done|].
  destruct oc; simpl in Hm |- *; try done; try (intros r; by apply IH).
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

(** The two halves of [sail_shaped]/[amo_tail], from the WEAK reading. *)
Lemma gwalkx_unit (m : M unit) :
  (gwalkx None m → sail_shaped m) ∧
  (∀ pa n, gwalkx (Some (pa, n)) m → amo_tail pa n m).
Proof.
  induction m as [x|T oc k IH]; [by split|].
  destruct oc; simpl.
  all: try (split; [intros H r; by apply IH, H
                   |intros pa1 n1 H r; by apply IH, H]).
  - split; [|by intros pa1 n1].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros H v; by apply IH, H. }
    intros [Hc H]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH, H.
  - split.
    + destruct (dev_addr (Interface.WriteReq.pa t)).
      * intros [_ H]. split; [done|by apply IH, H].
      * intros [Hn H]. split; [done|by apply IH, H].
    + intros pa1 n1 (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH, H6.
  - split; [intros H r; by apply IH, H|by intros pa1 n1].
  - split; [intros H r; by apply IH, H|by intros pa1 n1].
Qed.

Lemma gwalkx_shaped (m : M unit) : gwalkx None m → sail_shaped m.
Proof. apply gwalkx_unit. Qed.

Lemma gwalkx_amo_tail pa n (m : M unit) :
  gwalkx (Some (pa, n)) m → amo_tail pa n m.
Proof. apply gwalkx_unit. Qed.

(** THE ESCAPE-FREE BIND: [m] closes every window it opens (the [gwalk]
    hypothesis), so the continuation is entered with NO window. *)
Lemma gwalkx_bind {E A B} w (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gwalk w m → (∀ x, gwalkx None (k x)) → gwalkx w (Defs.bind m k).
Proof.
  revert w. induction m as [x|T oc k0 IH]; intros w Hm Hk.
  { destruct w; [done|apply Hk]. }
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
Qed.

(** THE ESCAPING BIND: [m] may leave a window open at its [Interface.Ret], so
    the continuation is entered under an ARBITRARY window and must be
    crossable under one — that is [gsilent].  This is the lemma the
    abandoning exclusive sites compose through. *)
Lemma gwalkx_bind_silent {E A B} w (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gwalkx w m → (∀ x, gsilent (k x)) → gwalkx w (Defs.bind m k).
Proof.
  revert w. induction m as [x|T oc k0 IH]; intros w Hm Hk.
  { apply gsilent_gwalkx. apply Hk. }
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _); intros v; by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
Qed.

(** The abandoning exclusive READ, in the weak reading: the continuation may
    end without a conditional write, provided it is silent from there on.
    This is the shape of [rv64d.execute_LOADRES]. *)
Lemma gwalkx_read_ram_abandon {B} rk addr width meta (k : _ → M B) :
  rk = Read_RISCV_reserved ∨ rk = Read_RISCV_reserved_acquire →
  dev_addr addr = false →
  (∀ r, gsilent (k r)) →
  gwalkx None (Defs.bind (read_ram rk (Physaddr addr) width meta) k).
Proof.
  intros Hrk Hd Hk. destruct Hrk as [->| ->];
    cbv [read_ram]; cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                         Interface.iMon_bind];
    cbv [Defs.sail_mem_read];
    cbn [Defs.bind Defs.bind0 Defs.returnm returnM Interface.iMon_bind];
    (simpl; rewrite Hd; split; [done|]);
    intros v;
    cbn [Defs.bind Defs.bind0 Defs.returnm returnM Interface.iMon_bind];
    by apply gsilent_gwalkx.
Qed.

(* ====================================================================== *)
(** ** 4. The sweep tactics

    [WeakShape.shape_solve] is the [gquiet]-mode tactic the C1 calibration
    measured.  [gsl_solve] is its [gsilent] twin and [gw_solve] its [gwalk]
    twin; the generated shards pick one per function from the call graph
    (silent if the function's cone touches no memory and no barrier, walk
    otherwise). *)

(** The [gwalk]-mode LEAVES.  Every one of these is [gwalk_quiet] applied to
    a [WeakShape] §3a leaf; they exist as named lemmas so the sweep's tactic
    can close a leaf with ONE hint-database lookup instead of the
    [apply gwalk_quiet; solve [shape_leaf]] chain, which is the difference
    between a 1-second and a 100-second per-function proof at this scale. *)
Lemma gwalk_read_reg {E} (r : Arch.reg) : gwalk (E := E) None (Defs.read_reg r).
Proof. by apply gwalk_quiet, gquiet_read_reg. Qed.
Lemma gwalk_write_reg {E} (r : Arch.reg) v :
  gwalk (E := E) None (Defs.write_reg r v).
Proof. by apply gwalk_quiet, gquiet_write_reg. Qed.
Lemma gwalk_read_reg_ref {E a}
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) :
  gwalk (E := E) None (Defs.read_reg_ref rf).
Proof. by apply gwalk_quiet, gquiet_read_reg_ref. Qed.
Lemma gwalk_reg_deref {E a}
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) :
  gwalk (E := E) None (Defs.reg_deref rf).
Proof. by apply gwalk_quiet, gquiet_reg_deref. Qed.
Lemma gwalk_write_reg_ref {E a}
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) v :
  gwalk (E := E) None (Defs.write_reg_ref rf v).
Proof. by apply gwalk_quiet, gquiet_write_reg_ref. Qed.
Lemma gwalk_sys_reg_read {E a} id
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) :
  gwalk (E := E) None (Defs.sail_sys_reg_read id rf).
Proof. by apply gwalk_quiet, gquiet_sys_reg_read. Qed.
Lemma gwalk_sys_reg_write {E a} id
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) v :
  gwalk (E := E) None (Defs.sail_sys_reg_write id rf v).
Proof. by apply gwalk_quiet, gquiet_sys_reg_write. Qed.
Lemma gwalk_instr_announce {E sz} (op : Values.mword sz) :
  gwalk (E := E) None (Defs.instr_announce op).
Proof. by apply gwalk_quiet, gquiet_instr_announce. Qed.
Lemma gwalk_branch_announce {E} sz (a : Values.mword sz) :
  gwalk (E := E) None (Defs.branch_announce sz a).
Proof. by apply gwalk_quiet, gquiet_branch_announce. Qed.
Lemma gwalk_sail_take_exception {E} f :
  gwalk (E := E) None (Defs.sail_take_exception f).
Proof. by apply gwalk_quiet, gquiet_sail_take_exception. Qed.
Lemma gwalk_sail_return_exception {E} pa :
  gwalk (E := E) None (Defs.sail_return_exception pa).
Proof. by apply gwalk_quiet, gquiet_sail_return_exception. Qed.
Lemma gwalk_sail_cache_op {E} o : gwalk (E := E) None (Defs.sail_cache_op o).
Proof. by apply gwalk_quiet, gquiet_sail_cache_op. Qed.
Lemma gwalk_sail_tlbi {E} o : gwalk (E := E) None (Defs.sail_tlbi o).
Proof. by apply gwalk_quiet, gquiet_sail_tlbi. Qed.
Lemma gwalk_translation_start {E} ts :
  gwalk (E := E) None (Defs.sail_translation_start ts).
Proof. by apply gwalk_quiet, gquiet_translation_start. Qed.
Lemma gwalk_translation_end {E} te :
  gwalk (E := E) None (Defs.sail_translation_end te).
Proof. by apply gwalk_quiet, gquiet_translation_end. Qed.
Lemma gwalk_cycle_count {E} u : gwalk (E := E) None (Defs.cycle_count u).
Proof. by apply gwalk_quiet, gquiet_cycle_count. Qed.
Lemma gwalk_get_cycle_count {E} u :
  gwalk (E := E) None (Defs.get_cycle_count u).
Proof. by apply gwalk_quiet, gquiet_get_cycle_count. Qed.
Lemma gwalk_print_effect {E} s : gwalk (E := E) None (Defs.print_effect s).
Proof. by apply gwalk_quiet, gquiet_print_effect. Qed.
Lemma gwalk_choose_bool {E} d : gwalk (E := E) None (Defs.choose_bool d).
Proof. by apply gwalk_quiet, gquiet_choose_bool. Qed.
Lemma gwalk_choose_int {E} d : gwalk (E := E) None (Defs.choose_int d).
Proof. by apply gwalk_quiet, gquiet_choose_int. Qed.
Lemma gwalk_choose_nat {E} d : gwalk (E := E) None (Defs.choose_nat d).
Proof. by apply gwalk_quiet, gquiet_choose_nat. Qed.
Lemma gwalk_choose_string {E} d : gwalk (E := E) None (Defs.choose_string d).
Proof. by apply gwalk_quiet, gquiet_choose_string. Qed.
Lemma gwalk_choose_range {E} d lo hi :
  gwalk (E := E) None (Defs.choose_range d lo hi).
Proof. by apply gwalk_quiet, gquiet_choose_range. Qed.
Lemma gwalk_choose_bitvector {E} d n :
  gwalk (E := E) None (Defs.choose_bitvector d n).
Proof. by apply gwalk_quiet, gquiet_choose_bitvector. Qed.
Lemma gwalk_undefined_unit {E} u : gwalk (E := E) None (Defs.undefined_unit u).
Proof. by apply gwalk_quiet, gquiet_undefined_unit. Qed.
Lemma gwalk_undefined_bool {E} u : gwalk (E := E) None (Defs.undefined_bool u).
Proof. by apply gwalk_quiet, gquiet_undefined_bool. Qed.
Lemma gwalk_undefined_int {E} u : gwalk (E := E) None (Defs.undefined_int u).
Proof. by apply gwalk_quiet, gquiet_undefined_int. Qed.
Lemma gwalk_undefined_nat {E} u : gwalk (E := E) None (Defs.undefined_nat u).
Proof. by apply gwalk_quiet, gquiet_undefined_nat. Qed.
Lemma gwalk_undefined_string {E} u :
  gwalk (E := E) None (Defs.undefined_string u).
Proof. by apply gwalk_quiet, gquiet_undefined_string. Qed.
Lemma gwalk_undefined_range {E} i j :
  gwalk (E := E) None (Defs.undefined_range i j).
Proof. by apply gwalk_quiet, gquiet_undefined_range. Qed.
Lemma gwalk_undefined_bitvector {E} n :
  gwalk (E := E) None (Defs.undefined_bitvector n).
Proof. by apply gwalk_quiet, gquiet_undefined_bitvector. Qed.
Lemma gwalk_undefined_vector {E T} n `{Inhabited T} (a : T) :
  gwalk (E := E) None (Defs.undefined_vector n a).
Proof. by apply gwalk_quiet, gquiet_undefined_vector. Qed.
Lemma gwalk_sail_barrier {E} (b : Arch.barrier) :
  gwalk (E := E) None (Defs.sail_barrier b).
Proof. apply gok_sail_barrier. Qed.

Create HintDb gshape discriminated.

#[export] Hint Resolve
  gsilent_fail gsilent_exit gsilent_assert_exp gsilent_assert_exp'
  gsilent_choose_from_list
  gwalk_ret gwalk_throw gwalk_fail gwalk_exit
  gwalk_assert_exp gwalk_assert_exp' gwalk_early_return
  gwalk_choose_from_list gwalk_sail_barrier
  gwalk_instr_announce gwalk_branch_announce
  gwalk_sail_take_exception gwalk_sail_return_exception
  gwalk_sail_cache_op gwalk_sail_tlbi
  gwalk_translation_start gwalk_translation_end
  gwalk_cycle_count gwalk_get_cycle_count gwalk_print_effect
  gwalk_choose_bool gwalk_choose_int gwalk_choose_nat
  gwalk_choose_string gwalk_choose_range gwalk_choose_bitvector
  gwalk_undefined_unit gwalk_undefined_bool gwalk_undefined_int
  gwalk_undefined_nat gwalk_undefined_string gwalk_undefined_range
  gwalk_undefined_bitvector gwalk_undefined_vector
  : gshape.

Ltac gsl_step :=
  match goal with
  | |- gsilent (Defs.bind _ _) => apply gsilent_bind
  | |- gsilent (Defs.bind0 _ _) => apply gsilent_bind0
  | |- gsilent (Defs.try_catch _ _) => apply gsilent_try_catch
  | |- gsilent (Defs.liftR _) => apply gsilent_liftR
  | |- gsilent (Defs.catch_early_return _) => apply gsilent_catch_early_return
  | |- gsilent (Defs.and_boolM _ _) => apply gsilent_and_boolM
  | |- gsilent (Defs.or_boolM _ _) => apply gsilent_or_boolM
  | |- gsilent (Defs.foreachM _ _ _) => apply gsilent_foreachM
  | |- gsilent (Defs.foreach_ZM_up _ _ _ _ _) => apply gsilent_foreach_ZM_up'
  | |- gsilent (Defs.foreach_ZM_down _ _ _ _ _) => apply gsilent_foreach_ZM_down'
  | |- gsilent (Defs.genlistM _ _) => apply gsilent_genlistM
  | |- gsilent (Defs.autocast_m _) => apply gsilent_autocast_m
  | |- gsilent (if ?b then _ else _) => destruct b
  | |- gsilent (match ?x with _ => _ end) => destruct x
  | |- gsilent (match ?x with _ => _ end _) => destruct x
  | |- gsilent (match ?x with _ => _ end _ _) => destruct x
  end.

Ltac gsl_leaf :=
  first
    [ exact I | assumption
    | apply gquiet_gsilent; solve [shape_leaf]
    | eauto with gshape nocore ].

Ltac gsl_solve :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | solve [gsl_leaf]
    | gsl_step ].

Ltac gw_step :=
  match goal with
  | |- gwalk _ (Defs.bind _ _) => apply gwalk_bind
  | |- gwalk _ (Defs.bind0 _ _) => apply gwalk_bind0
  | |- gwalk None (Defs.try_catch _ _) => apply gwalk_try_catch
  | |- gwalk None (Defs.liftR _) => apply gwalk_liftR
  | |- gwalk None (Defs.catch_early_return _) => apply gwalk_catch_early_return
  | |- gwalk None (Defs.try_catchR _ _) => apply gwalk_try_catchR
  | |- gwalk _ (Defs.and_boolM _ _) => apply gwalk_and_boolM
  | |- gwalk _ (Defs.or_boolM _ _) => apply gwalk_or_boolM
  | |- gwalk None (Defs.foreachM _ _ _) => apply gwalk_foreachM
  | |- gwalk None (Defs.foreach_ZM_up _ _ _ _ _) => apply gwalk_foreach_ZM_up'
  | |- gwalk None (Defs.foreach_ZM_down _ _ _ _ _) => apply gwalk_foreach_ZM_down'
  | |- gwalk None (Defs.genlistM _ _) => apply gwalk_genlistM
  | |- gwalk None (Defs.autocast_m _) => apply gwalk_autocast_m
  | |- gwalk None (Defs.untilMT _ _ _ _) => apply gwalk_untilMT
  | |- gwalk None (Defs.whileMT _ _ _ _) => apply gwalk_whileMT
  | |- gwalk _ (if ?b then _ else _) => destruct b
  | |- gwalk _ (match ?x with _ => _ end) => destruct x
  (* a function with SEVERAL pattern binders elaborates to a match APPLIED to
     the remaining arguments -- the generated proof destructs those arguments
     up front, but the applied form still shows up inside a body. *)
  | |- gwalk _ (match ?x with _ => _ end _) => destruct x
  | |- gwalk _ (match ?x with _ => _ end _ _) => destruct x
  end.

(** ORDER IS LOAD-BEARING AT THIS SCALE.  The common leaf is a call to an
    already-proven generated function, so the hint-database lookup goes
    FIRST, at depth 1 (every hint in `gshape` is premise-free, so no search
    is needed and none is paid for).  The register leaves come after it by
    NAME rather than as hints, because [eauto]'s unification does not see
    through [Arch.reg_type] — the C1 finding, still true. *)
Ltac gw_leaf :=
  first
    [ exact I | assumption
    | solve [eauto 1 with gshape nocore]
    | apply gwalk_read_reg | apply gwalk_write_reg
    | apply gwalk_read_reg_ref | apply gwalk_write_reg_ref
    | apply gwalk_reg_deref
    | apply gwalk_sys_reg_read | apply gwalk_sys_reg_write
    | apply gsilent_gwalk; solve [gsl_leaf]
    | apply gwalk_quiet; solve [shape_leaf] ].

Ltac gw_solve :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | solve [gw_leaf]
    | gw_step ].

(* ====================================================================== *)
(** ** 5. THE STAGE-C3 FINDINGS: (O4) FIXED IN C4, (O5) STILL OPEN

    ------------------------------------------------------------------------
    (O4) A STANDALONE STORE-CONDITIONAL — FIXED IN STAGE C4 BY WIDENING THE
         SPECIFICATION; the two refutations that stood here are FALSE now and
         are replaced by the positive leaves [gwalk_write_ram_con]
         ([WeakShape] §6b) and [gwalkx_write_ram_con] below.  The history,
         because the SHAPE of the finding recurs:

    The path, from the sources:

      rv64d.execute_STORECON aq rl rs2 rs1 width rd
        → vmem_write rs1 0 width data (StoreConditional (aq,rl,Data))
                     (aq && rl) rl (con := TRUE)
        → … → mem_write_value_priv_meta … (con := true)
        → checked_mem_write … (con := true)
        → write_kind_of_flags aq' rl' true  =  Write_RISCV_conditional[_release]
        → write_ram Write_RISCV_conditional (Physaddr paddr) split_width …

    and NOWHERE on that path is an exclusive [MemRead] issued — the lr/sc
    reservation lives in the model's PURE axioms [load_reservation] /
    [match_reservation] / [valid_reservation], not in a memory event, and the
    matching [lr] is a DIFFERENT INSTRUCTION, i.e. a different [riscv_step].
    So the conditional write reaches [sail_shaped]'s window-CLOSED [MemWrite]
    arm, which demands [ak_latest (classify …) = false] at a non-device
    address — and [write_ram] classifies a conditional write as
    [AV_exclusive], i.e. [ak_latest = true].

    This is the exact MIRROR of stage C1's (O2), which found the read side
    (an exclusive read with no conditional write, at [execute_LOADRES]) and
    which C2 fixed by weakening [amo_tail]'s [Interface.Ret] arm and adding
    [sail_mstep]'s BARE exclusive-read arm.  C4 took the symmetric fix:
    [sail_mstep]'s and [sail_shaped]'s window-CLOSED [MemWrite] arms lost the
    [ak_latest = false] conjunct (the [n ≠ 0] one stays), so a standalone
    conditional write steps as a plain [WeakPromise.LStore] — the machine
    only GAINS behaviors, the safe direction, and one step suffices because
    there is no window to abandon.  Its cost is on the ⇐ side, in the SAME
    predicate that pays for (O2): [WeakSailLTS2.pf_solo_f] now also forbids
    stepping from a conditional-write node ([at_con_write]), so
    [fused_blk] reads "every exclusive access of the block is part of a fused
    rmw".  A side condition is needed even though [WeakInterp.wrun]'s write
    arm takes a conditional write unchanged (it never inspects [ak_latest]),
    because the interpreter stamps the message [WCexcl] where the pf step
    carries [WeakSailLTS2.lbl_class] — one inert field, but the logs must
    agree syntactically for the reconstruction.

    The finding was definitional and needed no reachability reasoning beyond
    "some fetched word decodes to [STORECON]" (it does — [rv64d]'s decoder
    builds [STORECON] whenever [Ext_Zalrsc] is enabled and the width is
    valid, and [sail_shaped] quantifies over every register value and every
    fetched word). *)

(** THE POSITIVE LEAF, in the WEAK reading ([WeakShape.gwalk_write_ram_con]
    is the closed-reading twin).  A conditional RAM write with the window
    CLOSED is walkable exactly like a plain one; the [0 < width] side
    condition is the zero-width-write conjunct, the same one
    [gwalk_write_ram_plain] carries. *)
Lemma gwalkx_write_ram_con {B} wk addr width data meta (k : _ → M B) :
  wk = Write_RISCV_conditional ∨ wk = Write_RISCV_conditional_release →
  (0 < width)%Z →
  (∀ r, gwalkx None (k r)) →
  gwalkx None (Defs.bind (write_ram wk (Physaddr addr) width data meta) k).
Proof.
  intros Hwk Hw Hk.
  have Hn : Z.to_N width ≠ 0%N by apply to_N_nonzero.
  destruct Hwk as [->| ->];
    cbv [write_ram]; cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                          Interface.iMon_bind];
    cbv [Defs.sail_mem_write];
    cbn [Defs.bind Defs.bind0 Defs.returnm returnM Interface.iMon_bind];
    (simpl; split; [by destruct (dev_addr addr)|]);
    cbn [Defs.bind Defs.bind0 Defs.returnm returnM Interface.iMon_bind];
    apply Hk.
Qed.

(** …and the SAME node under an OPEN window must be the window's CLOSING
    write ([WeakShape.gwalk_write_ram_close]): same address, same width.
    That asymmetry is the whole content of the exclusive-window discipline —
    an AMO (read-modify-write in ONE instruction) fuses, a lone [sc] does
    not, and since C4 both are steppable. *)
