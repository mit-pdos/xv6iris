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
      §3  (was the ESCAPE INDEX [gwalkx] — DELETED in stage C8: with the
          window gone from [WeakShape.gwalk] the weak and closed readings
          coincide, and every [gwalkx] lemma is a [gwalk] one);
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
         write steps as a plain [LStore].  See
         [WeakShape.gwalk_write_ram_con].

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

Lemma gwalk_and_boolM {E} (l r : Defs.monad E bool) :
  gwalk l → gwalk r → gwalk (Defs.and_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.and_boolM.
  apply gwalk_bind; [done|]. by intros [|].
Qed.

Lemma gwalk_or_boolM {E} (l r : Defs.monad E bool) :
  gwalk l → gwalk r → gwalk (Defs.or_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.or_boolM.
  apply gwalk_bind; [done|]. by intros [|].
Qed.

Lemma gwalk_genlistM {E A} (f : nat → Defs.monad E A) (n : nat) :
  (∀ i, gwalk (f i)) → gwalk (Defs.genlistM f n).
Proof.
  intros Hf. rewrite /Defs.genlistM. apply gwalk_foreachM.
  intros i xs. apply gwalk_bind; [apply Hf|intros x; apply gwalk_ret].
Qed.

Lemma gwalk_autocast_m {E m n} {T : Z → Type} `{H : Inhabited (T n)}
    (x : Defs.monad E (T m)) :
  gwalk x → gwalk (Defs.autocast_m (n := n) x).
Proof.
  intros Hx. rewrite /Defs.autocast_m.
  apply gwalk_bind; [done|intros v; apply gwalk_ret].
Qed.

Lemma gwalk_foreach_ZM_up {E Vars} from to step (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gwalk (body z v)) →
  gwalk (Defs.foreach_ZM_up from to step vars body).
Proof. intros Hb. by apply gwalk_foreach_ZM_up'. Qed.

Lemma gwalk_foreach_ZM_down {E Vars} from to step (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gwalk (body z v)) →
  gwalk (Defs.foreach_ZM_down from to step vars body).
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

Lemma gsilent_gwalk {E A} (m : Defs.monad E A) : gsilent m → gwalk m.
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

(** The [gsilent]-prefix bind.  (Since stage C8 this is just
    [WeakShape.gwalk_bind] after [gsilent_gwalk]; it is kept because the
    sweep tactics dispatch on the PREFIX's mode.) *)
Lemma gwalk_bind_silent {E A B} (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gsilent m → (∀ x, gwalk (k x)) → gwalk (Defs.bind m k).
Proof. intros Hm Hk. apply gwalk_bind; [by apply gsilent_gwalk|exact Hk]. Qed.

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
Lemma gwalk_read_reg {E} (r : Arch.reg) : gwalk (E := E) (Defs.read_reg r).
Proof. by apply gwalk_quiet, gquiet_read_reg. Qed.
Lemma gwalk_write_reg {E} (r : Arch.reg) v :
  gwalk (E := E) (Defs.write_reg r v).
Proof. by apply gwalk_quiet, gquiet_write_reg. Qed.
Lemma gwalk_read_reg_ref {E a}
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) :
  gwalk (E := E) (Defs.read_reg_ref rf).
Proof. by apply gwalk_quiet, gquiet_read_reg_ref. Qed.
Lemma gwalk_reg_deref {E a}
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) :
  gwalk (E := E) (Defs.reg_deref rf).
Proof. by apply gwalk_quiet, gquiet_reg_deref. Qed.
Lemma gwalk_write_reg_ref {E a}
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) v :
  gwalk (E := E) (Defs.write_reg_ref rf v).
Proof. by apply gwalk_quiet, gquiet_write_reg_ref. Qed.
Lemma gwalk_sys_reg_read {E a} id
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) :
  gwalk (E := E) (Defs.sail_sys_reg_read id rf).
Proof. by apply gwalk_quiet, gquiet_sys_reg_read. Qed.
Lemma gwalk_sys_reg_write {E a} id
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) v :
  gwalk (E := E) (Defs.sail_sys_reg_write id rf v).
Proof. by apply gwalk_quiet, gquiet_sys_reg_write. Qed.
Lemma gwalk_instr_announce {E sz} (op : Values.mword sz) :
  gwalk (E := E) (Defs.instr_announce op).
Proof. by apply gwalk_quiet, gquiet_instr_announce. Qed.
Lemma gwalk_branch_announce {E} sz (a : Values.mword sz) :
  gwalk (E := E) (Defs.branch_announce sz a).
Proof. by apply gwalk_quiet, gquiet_branch_announce. Qed.
Lemma gwalk_sail_take_exception {E} f :
  gwalk (E := E) (Defs.sail_take_exception f).
Proof. by apply gwalk_quiet, gquiet_sail_take_exception. Qed.
Lemma gwalk_sail_return_exception {E} pa :
  gwalk (E := E) (Defs.sail_return_exception pa).
Proof. by apply gwalk_quiet, gquiet_sail_return_exception. Qed.
Lemma gwalk_sail_cache_op {E} o : gwalk (E := E) (Defs.sail_cache_op o).
Proof. by apply gwalk_quiet, gquiet_sail_cache_op. Qed.
Lemma gwalk_sail_tlbi {E} o : gwalk (E := E) (Defs.sail_tlbi o).
Proof. by apply gwalk_quiet, gquiet_sail_tlbi. Qed.
Lemma gwalk_translation_start {E} ts :
  gwalk (E := E) (Defs.sail_translation_start ts).
Proof. by apply gwalk_quiet, gquiet_translation_start. Qed.
Lemma gwalk_translation_end {E} te :
  gwalk (E := E) (Defs.sail_translation_end te).
Proof. by apply gwalk_quiet, gquiet_translation_end. Qed.
Lemma gwalk_cycle_count {E} u : gwalk (E := E) (Defs.cycle_count u).
Proof. by apply gwalk_quiet, gquiet_cycle_count. Qed.
Lemma gwalk_get_cycle_count {E} u :
  gwalk (E := E) (Defs.get_cycle_count u).
Proof. by apply gwalk_quiet, gquiet_get_cycle_count. Qed.
Lemma gwalk_print_effect {E} s : gwalk (E := E) (Defs.print_effect s).
Proof. by apply gwalk_quiet, gquiet_print_effect. Qed.
Lemma gwalk_choose_bool {E} d : gwalk (E := E) (Defs.choose_bool d).
Proof. by apply gwalk_quiet, gquiet_choose_bool. Qed.
Lemma gwalk_choose_int {E} d : gwalk (E := E) (Defs.choose_int d).
Proof. by apply gwalk_quiet, gquiet_choose_int. Qed.
Lemma gwalk_choose_nat {E} d : gwalk (E := E) (Defs.choose_nat d).
Proof. by apply gwalk_quiet, gquiet_choose_nat. Qed.
Lemma gwalk_choose_string {E} d : gwalk (E := E) (Defs.choose_string d).
Proof. by apply gwalk_quiet, gquiet_choose_string. Qed.
Lemma gwalk_choose_range {E} d lo hi :
  gwalk (E := E) (Defs.choose_range d lo hi).
Proof. by apply gwalk_quiet, gquiet_choose_range. Qed.
Lemma gwalk_choose_bitvector {E} d n :
  gwalk (E := E) (Defs.choose_bitvector d n).
Proof. by apply gwalk_quiet, gquiet_choose_bitvector. Qed.
Lemma gwalk_undefined_unit {E} u : gwalk (E := E) (Defs.undefined_unit u).
Proof. by apply gwalk_quiet, gquiet_undefined_unit. Qed.
Lemma gwalk_undefined_bool {E} u : gwalk (E := E) (Defs.undefined_bool u).
Proof. by apply gwalk_quiet, gquiet_undefined_bool. Qed.
Lemma gwalk_undefined_int {E} u : gwalk (E := E) (Defs.undefined_int u).
Proof. by apply gwalk_quiet, gquiet_undefined_int. Qed.
Lemma gwalk_undefined_nat {E} u : gwalk (E := E) (Defs.undefined_nat u).
Proof. by apply gwalk_quiet, gquiet_undefined_nat. Qed.
Lemma gwalk_undefined_string {E} u :
  gwalk (E := E) (Defs.undefined_string u).
Proof. by apply gwalk_quiet, gquiet_undefined_string. Qed.
Lemma gwalk_undefined_range {E} i j :
  gwalk (E := E) (Defs.undefined_range i j).
Proof. by apply gwalk_quiet, gquiet_undefined_range. Qed.
Lemma gwalk_undefined_bitvector {E} n :
  gwalk (E := E) (Defs.undefined_bitvector n).
Proof. by apply gwalk_quiet, gquiet_undefined_bitvector. Qed.
Lemma gwalk_undefined_vector {E T} n `{Inhabited T} (a : T) :
  gwalk (E := E) (Defs.undefined_vector n a).
Proof. by apply gwalk_quiet, gquiet_undefined_vector. Qed.
Lemma gwalk_sail_barrier {E} (b : Arch.barrier) :
  gwalk (E := E) (Defs.sail_barrier b).
Proof. apply gok_sail_barrier. Qed.

Create HintDb gshape discriminated.

(** A `discriminated` DB PRUNES BY HEAD CONSTANT ONLY IF THE CONSTANTS ARE
    OPAQUE TO IT.  Every hint here concludes [gwalk (<model function> ?a
    …)], and the generated model's definitions are TRANSPARENT, so without
    this line [eauto] delta-unfolds them while matching and compares BODIES:
    at a goal about one CSR [legalize_*] it walks into every sibling
    [legalize_*] in the database, and the siblings share a long prefix, so
    each failed match descends through two huge terms.  Measured on
    [rv64d.write_CSR] (a ~200-arm dispatch that calls most of that band):
    **>18 minutes transparent, 23 s opaque.**  It is sound here for the same
    reason it is cheap: the sweep emits a lemma for EVERY monadic definition,
    so a leaf never needs a constant unfolded to find its hint. *)
#[export] Hint Constants Opaque : gshape.

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
  | |- gwalk (Defs.bind _ _) => apply gwalk_bind
  | |- gwalk (Defs.bind0 _ _) => apply gwalk_bind0
  | |- gwalk (Defs.try_catch _ _) => apply gwalk_try_catch
  | |- gwalk (Defs.liftR _) => apply gwalk_liftR
  | |- gwalk (Defs.catch_early_return _) => apply gwalk_catch_early_return
  | |- gwalk (Defs.try_catchR _ _) => apply gwalk_try_catchR
  | |- gwalk (Defs.and_boolM _ _) => apply gwalk_and_boolM
  | |- gwalk (Defs.or_boolM _ _) => apply gwalk_or_boolM
  | |- gwalk (Defs.foreachM _ _ _) => apply gwalk_foreachM
  | |- gwalk (Defs.foreach_ZM_up _ _ _ _ _) => apply gwalk_foreach_ZM_up'
  | |- gwalk (Defs.foreach_ZM_down _ _ _ _ _) => apply gwalk_foreach_ZM_down'
  | |- gwalk (Defs.genlistM _ _) => apply gwalk_genlistM
  | |- gwalk (Defs.autocast_m _) => apply gwalk_autocast_m
  | |- gwalk (Defs.untilMT _ _ _ _) => apply gwalk_untilMT
  | |- gwalk (Defs.whileMT _ _ _ _) => apply gwalk_whileMT
  | |- gwalk (if ?b then _ else _) => destruct b
  | |- gwalk (match ?x with _ => _ end) => destruct x
  (* a function with SEVERAL pattern binders elaborates to a match APPLIED to
     the remaining arguments -- the generated proof destructs those arguments
     up front, but the applied form still shows up inside a body. *)
  | |- gwalk (match ?x with _ => _ end _) => destruct x
  | |- gwalk (match ?x with _ => _ end _ _) => destruct x
  end.

(** A LEAF TACTIC IS RUN AT EVERY *NODE*, NOT ONLY AT LEAVES — so any
    alternative in it that cannot succeed on a combinator node must not be
    REACHABLE from one.  [gw_atomic] is that gate.

    THIS IS THE SINGLE BIGGEST COST IN THE WHOLE SWEEP, and it does not look
    like a cost at all until a big term turns up (stage C5).  [gw_solve] tries
    [solve [gw_leaf]] before every structural step, so at a [bind] — where no
    leaf alternative CAN succeed — every one of them still ran, on the whole
    subterm.  Two ways that is superlinear:

      - [apply gwalk_quiet] / [apply gsilent_gwalk] succeed on ANY
        [gwalk ?m] goal and then hand the subterm to [eauto];
      - worse, THE HINT-DATABASE LOOKUP ITSELF.  Every hint's conclusion is
        [gwalk (<some model function> ?a …)] and the model's functions
        are TRANSPARENT, so unification delta-unfolds them and compares
        bodies.  Sibling functions in the same band share a long prefix
        ([legalize_mie] and [legalize_mideleg] are both four
        [currentlyEnabled] binds around a deeply nested returned bitvector),
        so the comparison descends deep into two huge terms before failing —
        once per hint, per node.

    Measured on [rv64d.legalize_mie], in the shard's own context: **>40
    minutes ungated, 0.9 s gated** — the shard containing it simply looked
    like a hung build.  Ordinary functions gain too ([legalize_mideleg]:
    7.7 s → 0.9 s; [WeakShapeGen01]: 7 min → 2 min).  GATE THE WHOLE LEAF,
    not just its expensive tail: the hint lookup is the bigger half.

    ORDER IS ALSO LOAD-BEARING.  The common leaf is a call to an
    already-proven generated function, so the hint-database lookup goes
    FIRST, at depth 1 (every hint in `gshape` is premise-free, so no search
    is needed and none is paid for).  The register leaves come after it by
    NAME rather than as hints, because [eauto]'s unification does not see
    through [Arch.reg_type] — the C1 finding, still true. *)
Ltac gw_atomic :=
  lazymatch goal with
  | |- gwalk (Defs.bind _ _) => fail
  | |- gwalk (Defs.bind0 _ _) => fail
  | |- gwalk (Defs.try_catch _ _) => fail
  | |- gwalk (Defs.liftR _) => fail
  | |- gwalk (Defs.catch_early_return _) => fail
  | |- gwalk (Defs.try_catchR _ _) => fail
  | |- gwalk (Defs.and_boolM _ _) => fail
  | |- gwalk (Defs.or_boolM _ _) => fail
  | |- gwalk (Defs.foreachM _ _ _) => fail
  | |- gwalk (Defs.foreach_ZM_up _ _ _ _ _) => fail
  | |- gwalk (Defs.foreach_ZM_down _ _ _ _ _) => fail
  | |- gwalk (Defs.genlistM _ _) => fail
  | |- gwalk (Defs.autocast_m _) => fail
  | |- gwalk (Defs.untilMT _ _ _ _) => fail
  | |- gwalk (Defs.whileMT _ _ _ _) => fail
  | |- gwalk (if _ then _ else _) => fail
  | |- gwalk (match _ with _ => _ end) => fail
  | |- gwalk (match _ with _ => _ end _) => fail
  | |- gwalk (match _ with _ => _ end _ _) => fail
  | _ => idtac
  end.

Ltac gw_leaf :=
  first
    [ exact I | assumption
    | gw_atomic;
      first
        [ solve [eauto 1 with gshape nocore]
        | apply gwalk_read_reg | apply gwalk_write_reg
        | apply gwalk_read_reg_ref | apply gwalk_write_reg_ref
        | apply gwalk_reg_deref
        | apply gwalk_sys_reg_read | apply gwalk_sys_reg_write
        | apply gsilent_gwalk; solve [gsl_leaf]
        | apply gwalk_quiet; solve [shape_leaf] ] ].

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
         are replaced by the positive leaf [gwalk_write_ram_con]
         ([WeakShape] §6b).  The history, because the SHAPE of the finding
         recurs — and it recurred once more, as (O10), which is what removed
         the window index from this kit altogether (stage C8):

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

(** The positive leaf itself is [WeakShape.gwalk_write_ram_con]; since
    stage C8 (finding (O10)) there is only one reading of the walk, so the
    weak twin that stood here is gone with the window index. *)
