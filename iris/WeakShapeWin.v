(** * WeakShapeWin.v — [gwp], the VALUE mode of the shape walk

    Stage C8.  Two things live here.

    §1  (O10) — THE FINDING, AND ITS FIX, kept as a record: it is the third
        member of the (O2)/(O4) family, it is what took the exclusive-window
        index out of the whole shape kit, and this file is where the index
        used to be.  Nothing in it is machine-checked any more, because the
        predicate the refutations were about ([WeakSailLTS.amo_tail], and the
        window argument of [WeakShape.gwalk]) NO LONGER EXISTS.

    §2  [gwp Q P m] — [WeakShape.gwalk] with two postconditions hung on its
        leaves:

          [Q : E → Prop]   the EXCEPTION postcondition, at
                           [Interface.ExtraOutcome];
          [P : A → Prop]   the RETURN postcondition, at [Interface.Ret].

        This is the mode stage C6 asked for ("[gwalk] WITH A RET
        POSTCONDITION") and the one [rv64d.run_hart_active] consumes: "if
        [execute] returns an [ExecuteAs] redirection then its payload is
        [ast_wf]", which is what lets the redirection arm call [execute] a
        second time.  Through C7 [P] took a SECOND argument, the exclusive
        window open at the return, because [execute]'s memory clauses could
        abandon a window and the redirection arm had to know they had not.
        Stage C8 deleted the window (§1), and with it that argument: the
        weak (abandoning) and closed readings of every lemma below coincide,
        which is why the file has one of each where C7 had two.

        The [Interface.ExtraOutcome] arm is a KIT-SIDE STRENGTHENING, not a
        claim of the specification: [gwalk] has [True] there (a raised Sail
        exception is a dead end — finding (O9)), and [gwp] has [Q e].  That
        is what makes [gwp_try_catch] able to hand the raised value to the
        handler, and every handler the model builds ([liftR],
        [catch_early_return]) needs it.  As the durable note says: a kit may
        be strictly stronger than the specification where that buys
        compositionality — but say so at the arm.

        §2 also holds the transfers ([gwalk] in, [gwalk]/[sail_shaped] out).

    §3  the combinator kit, including the two bind rules that make the
        EXISTING 294-lemma tower reusable for every prefix:
        [gwp_bind_closed] (a value-irrelevant prefix, which `gshape` supplies
        through [gwalk_gwp]) and [gwp_bind_pure] (a prefix from
        [WeakShapeAst]'s [gpureP], i.e. the decoder postcondition).

    §4  the solver [gwx_solve].

    ------------------------------------------------------------------------
    §1  (O10): AN ABANDONED EXCLUSIVE WINDOW IS NOT THE END OF THE
        INSTRUCTION — WHAT IT WAS, AND WHAT C8 DID ABOUT IT

    THE PATH, read off [model-xv6iris/rv64d.v] (it is still there; it is the
    predicate that changed):

      rv64d.update_and_write_pte sv vpn pteAddr pte level access …
        match update_PTE_Bits pte access with
        | None   => returnM (Ok (None, ext_ptw))          (* no read at all *)
        | Some _ =>
            (Svadu ∧ menvcfg.ADUE = 1) ∨ (¬Svadu ∧ ¬Svade) ⇒
              read_pte_exclusive pteAddr pte_width >>= λ w,
              match w with
              | Err _ => returnM (Err (PTW_No_Access, ext_ptw))
              | Ok pte' =>                       (* pte' is ∀-QUANTIFIED *)
                  check_leaf_pte … pte' … >>= λ c,
                  match c with
                  | Err (e, x) => returnM (Err (e, x))
                  | Ok (_, _, x) =>
                      match update_PTE_Bits pte' access with
                      | None      => returnM (Ok (Some pte', x))   (* ←—— *)
                      | Some pte'' => write_pte_conditional …

    [read_pte_exclusive] is [mem_read_priv (Load PageTableEntry) … (res :=
    true)], i.e. [read_kind_of_flags false false true = Read_RISCV_reserved],
    which [WeakInterp.classify] maps to [AV_exclusive] ([ak_latest = true]).
    Through C7 such a read OPENED a window in [sail_shaped]/[gwalk], and the
    marked arm RETURNS [Ok (Some pte', …)] — a successful A/D update with NO
    conditional write, which [translate]/[translateAddr] pass on as success,
    after which the [execute_*] clause performs the instruction's OWN data
    access.  That access is a [MemRead] (or a [MemWrite] at the DATA address)
    inside the window, and [amo_tail]'s arms were [MemRead ↦ False] and "any
    [MemWrite] must be at the window's own [pa]/[n]" — so
    [∀ b, sail_shaped (riscv_step b)] was FALSE, and it was false at EVERY
    memory instruction and at the fetch, since all of them translate.  The
    arm is reached in the ∀-quantified sense every shape predicate is stated
    in: [pte'] is the value of a [MemRead], universally quantified, so the
    walk must hold at a [pte'] whose A/D bits are already set and whose
    permissions pass [check_leaf_pte].

    THE GENRE, AND THE FIX (see [WeakSailLTS] delta (e) for the LTS side).
    (O2) found an exclusive READ with no conditional write and C2 fixed it by
    BRACKETING the abandoned window in [sail_mstep] — [silent_run … (Ret y,
    rs1)] — i.e. by assuming the abandoned tail is SILENT.  (O10) is the case
    where it is not: the tail of an abandoned PTE reservation is the whole
    rest of the instruction.  A "the tail is quiet from here" bracket is only
    as good as the CALL DEPTH at which the window is abandoned, so C8 took
    the fix the other deltas already had — NARROW THE PREDICATE TO WHAT THE
    MACHINE DOES:

      (i)   [WeakSailLTS.sail_shaped]'s [MemRead] arm DROPS the window: an
            exclusive read is shaped exactly like a plain one.  [amo_tail] is
            DELETED.
      (ii)  [sail_mstep]'s bare exclusive-read arm becomes ONE STEP instead
            of a bracket (the plain [LLoad] arm stops requiring
            [ak_latest = false]), exactly as C4's standalone conditional
            write did.  With no window mode there is no residual to preserve
            it in, so [WeakSailComplete.sail_shaped_res_step] and
            [tail_complete] go through unchanged; the machine only GAINS
            behaviours — the safe direction.
      (iii) the ⇐ cost goes where (O2)'s and (O4)'s went: into
            [WeakSailLTS2.fused_blk], the target-indexed run-local side
            condition.  Per-image discharge: xv6 runs with
            [menvcfg.ADUE = 0], so the A/D update path is never taken, and it
            uses [amoswap] rather than [lr]/[sc].

    THE FUSED rmw ARM STAYS — it is how an rmw appends a single [LRmw]
    message — but its evidence is now the RUN's ([silent_run] to a
    [wr_node]), not a claim [sail_shaped] makes, so the read/write
    address-and-width agreement that [amo_tail] used to state is supplied by
    the LTS arm itself.  That is what removed the memory cone's hardest
    semantic obligation, and what collapsed this file: the window index left
    [gwalk], [gwalkx] became [gwalk] and was deleted, and [gwp]'s [P] lost
    its window argument. *)

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
From xv6iris Require Import WeakShapeOverrides2 WeakShapeAst.
Require Import Riscv.rv64d.

Set Default Proof Using "Type".

(* ====================================================================== *)
(** ** 2. [gwp]: the value mode

    Arm for arm [WeakShape.gwalk], except at the two leaves: [Interface.Ret]
    carries [P] and [Interface.ExtraOutcome] carries [Q] (where [gwalk] has
    [True] on both).  [gwalk m] is therefore LITERALLY the instance
    [gwp (λ _, True) (λ _, True) m] — see [gwalk_gwp] / [gwp_gwalk]. *)

Section Wp.
Context {E A : Type}.
Local Notation mon := (Defs.monad E A).

Fixpoint gwp (Q : E → Prop) (P : A → Prop) (m : mon) {struct m} : Prop :=
  match m with
  | Interface.Ret x => P x
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → mon) → Prop with
       | Interface.MemRead n req => λ k,
           (if dev_addr (Interface.ReadReq.pa req) then True
            else ak_coh (classify (Interface.ReadReq.access_kind req)) = false) ∧
           ∀ v : bv (8 * n), gwp Q P (k (inl (v, None)))
       | Interface.MemWrite n' req' => λ k,
           (if dev_addr (Interface.WriteReq.pa req') then True
            else n' ≠ 0%N) ∧
           gwp Q P (k (inl None))
       | Interface.ExtraOutcome e => λ _,
           (* the KIT-SIDE strengthening: [gwalk] has [True] here (a raised
              Sail exception is a dead end, finding (O9)); [gwp] constrains
              the raised value, which is what [gwp_try_catch] hands to the
              handler. *)
           Q e
       | _ => λ k, ∀ r, gwp Q P (k r)
       end) k
  end.

End Wp.

Arguments gwp {E A} Q P m.

(** [gwalk] is the trivial instance, in both directions.  ([gwp_gwalk] holds
    at ANY [Q] and [P]: forgetting the postconditions is always sound.) *)
Lemma gwalk_gwp {E A} (Q : E → Prop) (P : A → Prop) (m : Defs.monad E A) :
  (∀ e, Q e) → (∀ x, P x) → gwalk m → gwp Q P m.
Proof.
  intros HQ HP. induction m as [x|T oc k IH]; intros Hm; [by apply HP|].
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct Hm as [Hc Hm]. split; [done|]. intros v; by apply IH.
  - destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - apply HQ.
Qed.

Lemma gwp_gwalk {E A} (Q : E → Prop) (P : A → Prop) (m : Defs.monad E A) :
  gwp Q P m → gwalk m.
Proof.
  induction m as [x|T oc k IH]; intros Hm; [done|].
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct Hm as [Hc Hm]. split; [done|]. intros v; by apply IH.
  - destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - done.
Qed.

(** …hence the specification, for the [M unit] instance. *)
Lemma gwp_shaped (Q : exception → Prop) (P : unit → Prop) (m : M unit) :
  gwp Q P m → sail_shaped m.
Proof. intros H. by apply gwalk_shaped, (gwp_gwalk Q P). Qed.

Lemma gwp_mono {E A} (Q Q' : E → Prop) (P P' : A → Prop)
    (m : Defs.monad E A) :
  (∀ e, Q e → Q' e) → (∀ x, P x → P' x) → gwp Q P m → gwp Q' P' m.
Proof.
  intros HQ HP. induction m as [x|T oc k IH]; intros Hm; [by apply HP|].
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct Hm as [Hc Hm]. split; [done|]. intros v; by apply IH.
  - destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - by apply HQ.
Qed.

(** A silent prefix satisfies every mode whose [P] is trivial — the leaf the
    solver falls back on. *)
Lemma gsilent_gwp {E A} (Q : E → Prop) (P : A → Prop) (m : Defs.monad E A) :
  (∀ x, P x) → gsilent m → gwp Q P m.
Proof.
  intros HP. induction m as [x|T oc k IH]; intros Hm; [by apply HP|].
  destruct oc; simpl in Hm |- *; try done; try (intros r; by apply IH).
  destruct ty; simpl in Hm |- *; intros r; by apply IH.
Qed.

(* ====================================================================== *)
(** [exres_wf]: the postcondition [rv64d.run_hart_active] consumes.  It is
    the ONE thing the redirection arm needs — "if [execute] hands back an
    [ExecuteAs], its payload is a well-formed instruction" — and nothing
    else about an [ExecutionResult] is ever asked.

    Through C7 there were THREE of these: [exres_wf], the sweep's
    "[exres_wf] and no window open" ([exres_ok]) and [execute]'s weaker
    "a REDIRECTION arrives with no window open" ([exres_wf_win]), because
    the memory clauses ([execute_LOADRES], the abandoning arms of
    [execute_AMO]) really did leave a window open while every function
    outside the memory cone did not.  With the window gone (§1) all three
    are [exres_wf]. *)
Definition exres_wf (r : ExecutionResult) : Prop :=
  match r with ExecuteAs i => ast_wf i | _ => True end.

(** The sweep's mode, in one notation. *)
Notation gwx m := (gwp (λ _ : exception, True) exres_wf m).

(** ** 3. The combinator kit *)

(** THE BIND, in its general form: the return postcondition of [m] is the
    hypothesis of [k]'s obligation.  Every other bind rule of this file, and
    [WeakShape.gwalk_bind], is this lemma with a particular [P]. *)
Lemma gwp_bind {E A B} (Q : E → Prop) (P : A → Prop) (P' : B → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gwp Q P m → (∀ x, P x → gwp Q P' (k x)) → gwp Q P' (Defs.bind m k).
Proof.
  induction m as [x|T oc k0 IH]; intros Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct Hm as [Hc Hm]. split; [done|]. intros v; by apply IH.
  - destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - done.
Qed.

(** THE FORM THE SOLVER RUNS ON — and the form that makes the EXISTING
    294-lemma tower reusable for every prefix.  "Closed" is the C7 name and
    it now means VALUE-IRRELEVANT: the prefix obligation is [gwp] at the
    TRIVIAL return postcondition, which an atomic call discharges out of
    `gshape` in one step ([gwalk_gwp]) and a compound prefix (an [if], a
    [match] with an [early_return] arm, a [liftR]) is walked into.  Stating
    it with a bare [gwalk] prefix instead would be WRONG inside a
    [catch_early_return]: there an [early_return r] node carries a value the
    postcondition constrains, and [gwalk] says nothing about it. *)
Lemma gwp_bind_closed {E A B} (Q : E → Prop) (P' : B → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gwp Q (λ _, True) m → (∀ x, gwp Q P' (k x)) →
  gwp Q P' (Defs.bind m k).
Proof. intros Hm Hk. apply (gwp_bind Q (λ _, True)); [done|]. by intros x _. Qed.

Lemma gwp_bind0_closed {E A} (Q : E → Prop) (P' : A → Prop)
    (m : Defs.monad E unit) (n : Defs.monad E A) :
  gwp Q (λ _, True) m → gwp Q P' n → gwp Q P' (Defs.bind0 m n).
Proof. intros ??. rewrite /Defs.bind0. by apply gwp_bind_closed. Qed.

(** …and the ONE value-carrying prefix rule the sweep needs, for the
    [ExecutionResult]-valued calls whose result the continuation matches on. *)
Lemma gwp_bind_exres {E B} (Q : E → Prop) (P' : B → Prop)
    (m : Defs.monad E ExecutionResult) (k : ExecutionResult → Defs.monad E B) :
  gwp Q exres_wf m → (∀ x, exres_wf x → gwp Q P' (k x)) →
  gwp Q P' (Defs.bind m k).
Proof. intros Hm Hk. by apply (gwp_bind Q exres_wf). Qed.

(** …and the form the DECODER POSTCONDITION feeds ([WeakShapeAst.gpureP]):
    a prefix that issues no memory event, raises whatever it likes, and
    whose returned values satisfy [Pm]. *)
Lemma gwp_bind_pure {E A B} (Q : E → Prop) (Pm : A → Prop) (P' : B → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  (∀ e, Q e) → gpureP Pm m → (∀ x, Pm x → gwp Q P' (k x)) →
  gwp Q P' (Defs.bind m k).
Proof.
  intros HQ. revert m. fix IH 1. intros [x|T oc k0] Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done; try (by apply HQ);
    try (destruct ty; simpl in Hm |- *; intros r; by apply IH).
Qed.

(** THE CONSUMER: a [gwp] fact crossing back into an ordinary shape
    obligation.  (C7 had two of these, one per reading of the window; with
    the window gone [gwalkx] is [gwalk] and so are they.) *)
Lemma gwalk_bind_wp {E A B} (Q : E → Prop) (P : A → Prop)
    (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gwp Q P m → (∀ x, P x → gwalk (k x)) → gwalk (Defs.bind m k).
Proof.
  induction m as [x|T oc k0 IH]; intros Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct Hm as [Hc Hm]. split; [done|]. intros v; by apply IH.
  - destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - done.
Qed.

(** THE HANDLER RULE — the whole reason the [ExtraOutcome] arm carries [Q]. *)
Lemma gwp_try_catch {A E1 E2} (Q1 : E1 → Prop) (Q2 : E2 → Prop)
    (P : A → Prop) (m : Defs.monad E1 A) (h : E1 → Defs.monad E2 A) :
  (∀ e, Q1 e → gwp Q2 P (h e)) →
  gwp Q1 P m → gwp Q2 P (Defs.try_catch m h).
Proof.
  intros Hh. induction m as [x|T oc k IH]; intros Hm; [done|].
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - destruct Hm as [Hc Hm]. split; [done|]. intros v; by apply IH.
  - destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - by apply Hh.
Qed.

(** The leaves. *)
Lemma gwp_ret {E A} (Q : E → Prop) (P : A → Prop) (x : A) :
  P x → gwp Q P (Interface.Ret x).
Proof. done. Qed.

Lemma gwp_returnm {E A} (Q : E → Prop) (P : A → Prop) (x : A) :
  P x → gwp Q P (Defs.returnm (E := E) x).
Proof. done. Qed.

Lemma gwp_throw {E A} (Q : E → Prop) (P : A → Prop) (e : E) :
  Q e → gwp Q P (Defs.throw (A := A) e).
Proof. done. Qed.

Lemma gwp_early_return {A R E} (Q : R + E → Prop) (P : A → Prop) (r : R) :
  Q (inl r) → gwp Q P (Defs.early_return (A := A) (E := E) r).
Proof. done. Qed.

Lemma gwp_fail {E A} (Q : E → Prop) (P : A → Prop) msg :
  gwp Q P (Defs.fail (A := A) (E := E) msg).
Proof. rewrite /Defs.fail /=. by intros []. Qed.

Lemma gwp_exit {E A} (Q : E → Prop) (P : A → Prop) :
  gwp Q P (Defs.exit (A := A) (E := E) tt).
Proof. apply gwp_fail. Qed.

Lemma gwp_assert_exp' {E} (Q : E → Prop) (b : bool)
    (P : (b = true) → Prop) msg :
  (∀ h, P h) → gwp Q P (Defs.assert_exp' (E := E) b msg).
Proof.
  intros HP. rewrite /Defs.assert_exp'. destruct b; [apply HP|apply gwp_fail].
Qed.

Lemma gwp_assert_exp {E} (Q : E → Prop) (P : unit → Prop) b msg :
  P tt → gwp Q P (Defs.assert_exp (E := E) b msg).
Proof.
  intros HP. rewrite /Defs.assert_exp. destruct b; [apply HP|apply gwp_fail].
Qed.

(** [liftR] and [catch_early_return], the model's only two handlers. *)
Lemma gwp_liftR {A R E} (Q : R + E → Prop) (P : A → Prop)
    (m : Defs.monad E A) :
  (∀ e, Q (inr e)) → gwp (λ _ : E, True) P m →
  gwp Q P (Defs.liftR (R := R) m).
Proof.
  intros HQ Hm. rewrite /Defs.liftR. apply (gwp_try_catch (λ _, True)); [|done].
  intros e _. by apply gwp_throw.
Qed.

Lemma gwp_catch_early_return {A E} (Q : E → Prop) (P : A → Prop)
    (m : Defs.monadR A E A) :
  gwp (λ ea, match ea with inl a => P a | inr e => Q e end) P m →
  gwp Q P (Defs.catch_early_return m).
Proof.
  intros Hm. rewrite /Defs.catch_early_return.
  apply (gwp_try_catch
           (λ ea, match ea with inl a => P a | inr e => Q e end) Q P);
    [|done].
  intros [a|e] He; [by apply gwp_returnm|by apply gwp_throw].
Qed.

Lemma gwp_try_catchR {A R E} (Q : R + E → Prop) (P : A → Prop)
    (m : Defs.monadR R E A) (h : E → Defs.monadR R E A) :
  (∀ e, gwp Q P (h e)) →
  gwp (λ ea, match ea with inl r => Q (inl r) | inr _ => True end) P m →
  gwp Q P (Defs.try_catchR m h).
Proof.
  intros Hh Hm. rewrite /Defs.try_catchR.
  apply (gwp_try_catch
           (λ ea, match ea with inl r => Q (inl r) | inr _ => True end) Q P);
    [|done].
  intros [r|e] He; [by apply gwp_throw|by apply Hh].
Qed.

(** The boolean short-circuits and the structural loops: the LEFT operand /
    the loop body is value-irrelevant, so its obligation is the tower's
    [gwalk], reached through the trivial postcondition. *)
Lemma gwp_and_boolM {E} (Q : E → Prop) (P : bool → Prop)
    (l r : Defs.monad E bool) :
  gwp Q (λ _, True) l → gwp Q P r → P false →
  gwp Q P (Defs.and_boolM l r).
Proof.
  intros Hl Hr HP. rewrite /Defs.and_boolM.
  apply gwp_bind_closed; [done|]. by intros [|].
Qed.

Lemma gwp_or_boolM {E} (Q : E → Prop) (P : bool → Prop)
    (l r : Defs.monad E bool) :
  gwp Q (λ _, True) l → gwp Q P r → P true →
  gwp Q P (Defs.or_boolM l r).
Proof.
  intros Hl Hr HP. rewrite /Defs.or_boolM.
  apply gwp_bind_closed; [done|]. by intros [|].
Qed.

Lemma gwp_autocast_m {E m n} {T : Z → Type} `{H : Inhabited (T n)}
    (Q : E → Prop) (P : T n → Prop) (x : Defs.monad E (T m)) :
  gwp Q (λ _, True) x → (∀ v, P v) →
  gwp Q P (Defs.autocast_m (n := n) x).
Proof.
  intros Hx HP. rewrite /Defs.autocast_m.
  apply gwp_bind_closed; [done|]. intros v. by apply gwp_returnm.
Qed.

(** The structural loops appear only as bind PREFIXES in the [execute_*]
    clauses, where the TRIVIAL postcondition is all that is needed and
    `gshape` supplies it through [gwalk_gwp].  A tail-position loop would
    need a loop invariant in the [P] position; no site asks for one. *)
Lemma gwp_foreachM_closed {E a Vars} (Q : E → Prop)
    (l : list a) (vars : Vars) (body : a → Vars → Defs.monad E Vars) :
  (∀ e, Q e) → (∀ x v, gwalk (body x v)) →
  gwp Q (λ _, True) (Defs.foreachM l vars body).
Proof.
  intros HQ Hb. apply gwalk_gwp; [done|done|]. by apply gwalk_foreachM.
Qed.

(* ====================================================================== *)
(** ** 4. [gwx_solve] — the solver, under the (O8) discipline

    Same three rules as [gw_solve]: the LEAF IS GATED on the goal being
    atomic (a leaf tactic runs at every node, not only at leaves), the
    hint-database lookup goes first and is premise-free, and the model's
    constants stay OPAQUE to the database (a `discriminated` DB prunes by
    head constant only if it cannot delta-unfold them).

    ONE THING IS DIFFERENT, and it is the point of the mode: at a [bind] the
    PREFIX obligation is value-irrelevant, i.e. [gwalk] modulo [gwalk_gwp],
    which is exactly what the 294-lemma tower proves — so the prefix is
    discharged by [gw_solve] and only the CONTINUATION is walked in this
    mode.  That is what keeps a [gwp] sweep the size of the clause bodies
    rather than the size of their cones.

    The postcondition side-goals ([P x] / [Q e]) are left to `gwpost`, which
    the consumer populates ([WeakShapeExec]'s [exres_wf]). *)


Create HintDb gwpost discriminated.
#[export] Hint Constants Opaque : gwpost.

(** …and the database of the sweep's own conclusions, so that a TAIL call to
    an already-proven [ExecutionResult]-returning function is one
    premise-free lookup ([doCSR] in [execute_CSRReg], [trap] in
    [execute_ECALL], …).  Prefix calls do not go here: they are
    value-irrelevant and the 294-lemma `gshape` tower already covers them. *)
Create HintDb gwexec discriminated.
#[export] Hint Constants Opaque : gwexec.

(** The PURE [ExecutionResult] producers — the ~54 compressed expansions —
    are closed by computation: every [ExecuteAs] payload they build has a
    LITERAL width. *)
(** ONE STEP OF THE PURE DRIVER.  A [match] on a VARIABLE is destructed
    first (Sail's pure clauses dispatch on their own arguments); only if no
    occurrence has a variable scrutinee is a computed one taken (an [if] over
    a [generic_eq]).  Taking them in the other order would [destruct] the
    [ExecutionResult] a clause returns and leave an [ExecuteAs ?i] goal with
    nothing known about [?i]. *)
Ltac ew_dstep :=
  cbn beta iota;
  match goal with
  | |- context [match ?x with _ => _ end] => is_var x; destruct x
  | |- context [match ?x with _ => _ end] => destruct x
  end.

Ltac ew_solve :=
  first
    [ exact I
    | solve [ simpl; first [ exact I | lia ] ]
    | solve [ repeat ew_dstep; simpl; first [ exact I | lia ] ] ].

(** [∀ e, Q e] where [Q] is the SUM postcondition a [catch_early_return]
    installs does NOT reduce until the sum is destructed, so [by intros]
    leaves a stuck [match] and every rule carrying that premise silently
    falls through.  (It cost an hour: the decoder rule in [WeakShapeExec]
    fell through to the [gwalk] route, which walks the decoder happily and
    DROPS its postcondition.) *)
Ltac qtriv :=
  first [ solve [by intros]
        | solve [intros e; destruct e; first [exact I | reflexivity | done]] ].

(** …and the same for the RETURN postcondition, which is what gates the
    [gwalk] route now that [P] is a plain value predicate: it must fail on
    [exres_wf] (an [ExecuteAs] payload is NOT well-formed for free) and
    succeed on the trivial one. *)
Ltac ptriv := first [ solve [by intros] | solve [intros; exact I] ].

Ltac gwx_wf :=
  first [ exact I | assumption | solve [eauto 3 with gwpost]
        | solve [ simpl; first [ exact I | lia ] ]
        | solve [ repeat ew_dstep; simpl;
                  first [ exact I | lia | solve [eauto 2 with gwpost] ] ] ].

Ltac gwx_val :=
  first [ exact I | reflexivity | assumption
        | solve [gwx_wf]
        | cbv [exres_wf]; solve [gwx_wf] ].

Ltac gwx_step :=
  match goal with
  (* THE PREFIX'S TYPE DECIDES THE RULE, and it is the only place the sweep
     needs to look at a type: an [ExecutionResult]-valued prefix is a call
     whose VALUE the continuation matches on ([jump_to] in [execute_JALR],
     [doCSR] in [execute_CSRReg]), so its postcondition has to travel; every
     other prefix is value-irrelevant and the `gshape` tower covers it. *)
  | |- gwp _ _ (@Defs.bind ExecutionResult _ _ _ _) => apply gwp_bind_exres
  | |- gwp _ _ (Defs.bind _ _) => apply gwp_bind_closed
  | |- gwp _ _ (Defs.bind0 _ _) => apply gwp_bind0_closed
  | |- gwp _ _ (Defs.try_catch _ _) => eapply gwp_try_catch
  | |- gwp _ _ (Defs.liftR _) => apply gwp_liftR; [qtriv|]
  | |- gwp _ _ (Defs.catch_early_return _) => apply gwp_catch_early_return
  | |- gwp _ _ (Defs.try_catchR _ _) => apply gwp_try_catchR
  | |- gwp _ _ (Defs.and_boolM _ _) =>
      apply gwp_and_boolM; [| |solve [gwx_val]]
  | |- gwp _ _ (Defs.or_boolM _ _) =>
      apply gwp_or_boolM; [| |solve [gwx_val]]
  | |- gwp _ _ (Defs.autocast_m _) =>
      apply gwp_autocast_m; [|solve [gwx_val]]
  | |- gwp _ _ (if ?b then _ else _) => destruct b
  | |- gwp _ _ (match ?x with _ => _ end) => destruct x
  | |- gwp _ _ (match ?x with _ => _ end _) => destruct x
  | |- gwp _ _ (match ?x with _ => _ end _ _) => destruct x
  end.

Ltac gwx_atomic :=
  lazymatch goal with
  | |- gwp _ _ (Defs.bind _ _) => fail
  | |- gwp _ _ (Defs.bind0 _ _) => fail
  | |- gwp _ _ (Defs.try_catch _ _) => fail
  | |- gwp _ _ (Defs.liftR _) => fail
  | |- gwp _ _ (Defs.catch_early_return _) => fail
  | |- gwp _ _ (Defs.try_catchR _ _) => fail
  | |- gwp _ _ (Defs.and_boolM _ _) => fail
  | |- gwp _ _ (Defs.or_boolM _ _) => fail
  | |- gwp _ _ (Defs.autocast_m _) => fail
  | |- gwp _ _ (if _ then _ else _) => fail
  | |- gwp _ _ (match _ with _ => _ end) => fail
  | |- gwp _ _ (match _ with _ => _ end _) => fail
  | |- gwp _ _ (match _ with _ => _ end _ _) => fail
  | _ => idtac
  end.

(** A goal whose postconditions are both trivial is just a [gwalk] goal, and
    the 294-lemma tower is what proves those — so try that route first, at
    every node.  It costs nothing where it does not apply: the [∀ x, P x]
    premise fails immediately at [exres_wf], and the [∀ e, Q e] premise fails
    immediately inside a [catch_early_return] (where an [early_return] node
    DOES carry a constrained value), both before [gw_solve] is ever
    entered. *)
Ltac gwx_closed :=
  apply gwalk_gwp; [qtriv | ptriv | solve [gw_solve]].

Ltac gwx_leaf :=
  first
    [ exact I | assumption
    (* THE COMMON LEAF, AND IT GOES THROUGH THE TOWER: an atomic call in
       bind-prefix position, at the trivial postcondition, out of `gshape`
       in one premise-free lookup.  It is UNGATED on purpose (see
       [gwx_closed]): a whole compound prefix can go this way too. *)
    | gwx_closed
    | gwx_atomic;
      first
        [ solve [eauto 1 with gwexec nocore]
        | apply gwp_fail | apply gwp_exit
        | apply gwp_ret; solve [gwx_val]
        | apply gwp_returnm; solve [gwx_val]
        | apply gwp_throw; solve [gwx_val]
        | apply gwp_early_return; solve [gwx_val]
        | apply gwp_assert_exp'; solve [gwx_val]
        | apply gwp_assert_exp; solve [gwx_val]
        | apply gsilent_gwp; [solve [gwx_val] | solve [gsl_leaf]]
        | solve [gwx_val] ] ].

Ltac gwx_solve :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | solve [gwx_leaf]
    | gwx_step ].
