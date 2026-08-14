(** * WeakShape.v — the COMPOSITIONAL SHAPE KIT for the Sail model (stage C)

    Stage C of [claude-notes/projects/weak-memory-premises.md] has to discharge

        ∀ b, sail_shaped (riscv_step b)   and   ∀ b, sail_live (riscv_step b)

    ([WeakSailLTS.sail_shaped] / [WeakSailComplete.sail_live]).  This file is
    the KIT that a sweep over the generated model would run on, plus a
    measured calibration.  It adds no axioms.

    ------------------------------------------------------------------------
    (1) THE ONE ABSTRACTION: [gwalk].

    [sail_shaped] and its mutual twin [amo_tail] are the SAME walk over the
    monad, indexed by whether an exclusive window is OPEN:

        [gwalk None m]              →  [sail_shaped m]     ([gwalk_shaped])
        [gwalk (Some (pa, n)) m]    →  [amo_tail pa n m]   ([gwalk_amo_tail])

    The implications are one-way by ONE deliberate strengthening — an
    [ExtraOutcome] (a raised Sail exception) is refused while a window is
    open, where [amo_tail] admits it.  That single line is what makes
    [try_catch]/[liftR]/[catch_early_return] window-compositional at all (see
    §4); it costs nothing real, since a throw inside a window ends the
    instruction with the window open, which [amo_tail] refutes one step
    later.  Since stage C has to PROVE [sail_shaped], proving the stronger
    predicate is exactly what is wanted.  Collapsing the mutual pair
    into one window-indexed predicate is what makes the kit affordable: every
    combinator needs ONE lemma instead of two, and the exclusive-window sites
    (lr/sc, AMO, [update_and_write_pte]) are the SAME lemmas at [w = Some _].
    [gwalk] is also polymorphic in the monad's exception and result types
    ([Defs.monad E A], not just [M unit]) — mandatory, since [bind] runs
    through [M A] and [try_catch]/[liftR] through [monadR R E].

    [glive] is likewise indexed by a bool [xf] = "an uncaught [ExtraOutcome]
    (i.e. a Sail exception) is fatal".  [glive true] is [sail_live]
    ([glive_live]); [glive false] is what a [try_catch] argument needs.

    ------------------------------------------------------------------------
    (2) WHAT THE KIT COVERS (151 lemmas).  All of SailStdpp's [Defs]
    vocabulary that the generated model uses: [bind]/[bind0]/[returnm],
    [throw]/[fail]/[exit]/[assert_exp]/[assert_exp'],
    [try_catch]/[catch_early_return]/[liftR]/[early_return]/[try_catchR],
    the [choose_*] and [undefined_*] families, the register combinators, the
    announce/barrier/cache/tlb/exception silent nodes,
    [foreachM]/[foreach_ZM_up']/[foreach_ZM_down']/[genlistM],
    [and_boolM]/[or_boolM], [whileMT]/[untilMT], [autocast_m],
    [choose_from_list], and the model's two memory leaves
    [rv64d.read_ram]/[rv64d.write_ram] (over [Defs.sail_mem_read] /
    [Defs.sail_mem_write]) — plus a THIRD predicate, [gquiet], which is what
    carries an open exclusive window across the register/trace code between
    an exclusive read and its conditional write ([gwalk_bind_quiet]).

    ------------------------------------------------------------------------
    (3) THE THREE STRUCTURAL OBSTACLES FOUND (details in each section, and in
    the stage-C report).  None is a defect of this kit; all three are facts
    about the pair (model, shape predicates):

    (O1) [sail_live] WAS REFUTABLE AS STATED — FIXED IN C2.  Its memory arms
         quantified over EVERY answer, including the ABORT answer [inr ab],
         and [rv64d.read_ram]'s abort arm is [exit tt] = [GenericFail].
         Since [Arch.abort = unit] that branch is inhabited, so
         [sail_live (read_ram rk pa width meta)] was FALSE
         ([read_ram_not_live], the machine-checked refutation that stood in
         §6b and is DELETED with the fix), and every load path of
         [riscv_step] goes through it.  The LTS never SUPPLIES an abort (see
         [WeakSailLTS.sail_mstep]: the [MemRead] arms hand the continuation
         [inl (w, None)] and only that), so the memory arms of
         [sail_live]/[sail_shaped] — and of [glive]/[gwalk] here — now
         quantify over exactly the LTS-supplied answers:
             | MemRead n req  => λ k, ∀ w : bv (8 * n), P (k (inl (w, None)))
             | MemWrite n req => λ k, P (k (inl None))
         What was a refutation is now [glive_read_ram], the positive leaf.

    (O2) AN ABANDONED EXCLUSIVE WINDOW (bare lr, failing sc, faulting AMO)
         HAD NO SHAPE AND NO STEP — FIXED IN C2 AT THE LTS, AND ONLY
         PARTLY HERE.  [rv64d.execute_LOADRES] issues an [ak_latest] read
         ([read_kind_of_flags _ _ true = Read_RISCV_reserved]) with no
         conditional write on ANY continuation; [execute_AMO] and
         [update_and_write_pte] do so on SOME paths (§7c).  C2's fix is in
         [WeakSailLTS]: [amo_tail]'s [Interface.Ret] arm becomes [True] and
         [sail_mstep] gains the BARE exclusive-read arm (delta (e) there).

         THIS KIT DELIBERATELY DID NOT FOLLOW THE WEAKENING, and the reason
         is a C2 finding worth keeping: WEAKENING [gwalk (Some _)
         (Interface.Ret _)] TO [True] REFUTES [gwalk_bind] AND EVERY LOOP
         LEMMA OF §5.  An abandoned window ESCAPES a [bind] — in
         [Defs.bind m k] the [Interface.Ret] of [m] is where [k] begins, so a
         window [m] leaves open runs on into [k] — and the honest bind lemma
         would have to hypothesise [k] walkable under an ARBITRARY window,
         i.e. essentially [gquiet]; that is true at the abandoning sites and
         false for ordinary continuations, so it cannot be the sweep's bind.
         [gwalk (Some _)] therefore keeps the CLOSED reading, which is
         STRICTLY STRONGER than [amo_tail] (as the [ExtraOutcome] arm of (1)
         already was) — so [gwalk_amo_tail]/[gwalk_shaped] stay sound — and
         the abandoning sites are served instead by [gquiet_amo_tail] (§3:
         quiet code abandons a window), which is the positive replacement for
         the two refutations [gwalk_some_quiet_False] / [amo_tail_quiet_False]
         that stood in §1b through C1 and are now FALSE and deleted.
         WHAT C3 MUST ADD to cover the abandoning sites compositionally: one
         more index — "no window escapes [m]" — under which the bind lemma
         splits into the escape-free case (the present one, for the ~330
         functions that issue no exclusive read) and the escaping case (with
         a quiet continuation).  It is a sweep-side addition, not a spec
         change: the SPECIFICATION is settled and lives in [WeakSailLTS].

    (O3) [whileMT]/[untilMT] ARE NOT LIVENESS-COMPOSITIONAL.  Their
         termination guard ends in [fail "Termination limit reached"], so
         [glive] of a loop needs a SEMANTIC argument (the measure really
         bounds the iterations), not a shape argument.  [checked_mem_read] /
         [checked_mem_write] — i.e. EVERY memory access — go through
         [untilMT] over the misaligned-split count, so this is on the
         critical path.  [gwalk] is fine (a [GenericFail] continuation is
         [False → _], so the walk is vacuous there): the obstacle is
         liveness-only.  There are FOUR such sites in the whole reachable
         model ([checked_mem_read], [checked_mem_write], [mem_write_ea],
         [loop]), and the same family covers the ~100 [exit tt] /
         [internal_error] / [reserved_behavior] / failing-[assert_exp]
         sites: each needs a REACHABILITY argument, not a shape lemma.

    ------------------------------------------------------------------------
    (4) WHAT IS MEASURED HERE.  §7 proves [gquiet]/[gok] for a bottom-up
    sample of generated functions with a semi-automated [shape_solve]; §8 is
    the assembly-strategy report (per-proof times, call-graph size, why one
    monolithic [shape_solve] on [try_step] is not the route, what a
    [tools/gen_shape.py] should emit, and the order in which the three
    obstacles must be settled).  The whole file compiles in ~12 s.
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
From xv6iris Require Import WeakSailComplete.

Set Default Proof Using "Type".

(* ====================================================================== *)
(** ** 1. The window-indexed walk *)

(** An OPEN exclusive window: the address and width the conditional write
    must have.  [None] = no window = [sail_shaped].

    THE WINDOW MODE IS THE *CLOSED* READING, and since C2 that is STRICTLY
    STRONGER than [WeakSailLTS.amo_tail] (whose [Interface.Ret] arm is now
    [True] — a window may be abandoned).  The implication [gwalk_amo_tail]
    is therefore still sound, and the strengthening is deliberate; see the
    header's (O2) entry for WHY the weak reading cannot be the kit's:
    weakening this arm REFUTES [gwalk_bind] and every loop lemma, because an
    abandoned window ESCAPES a [bind] into the continuation. *)
Definition win : Type := option (Arch.pa * N).

Section Walk.
Context {E A : Type}.

Local Notation mon := (Defs.monad E A).

Fixpoint gwalk (w : win) (m : mon) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => match w with Some _ => False | None => True end
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → mon) → Prop with
       | Interface.MemRead n req => λ k,
           match w with
           | Some _ => False
           | None =>
               if dev_addr (Interface.ReadReq.pa req)
               then ∀ v : bv (8 * n), gwalk None (k (inl (v, None)))
               else
                 ak_coh (classify (Interface.ReadReq.access_kind req)) = false ∧
                 (if ak_latest (classify (Interface.ReadReq.access_kind req))
                  then ∀ v : bv (8 * n),
                         gwalk (Some (Interface.ReadReq.pa req, n))
                               (k (inl (v, None)))
                  else ∀ v : bv (8 * n), gwalk None (k (inl (v, None))))
           end
       | Interface.MemWrite n' req' => λ k,
           match w with
           | Some (pa, n) =>
               dev_addr (Interface.WriteReq.pa req') = false ∧
               Interface.WriteReq.pa req' = pa ∧ n' = n ∧ n' ≠ 0%N ∧
               ak_latest (classify (Interface.WriteReq.access_kind req')) = true ∧
               gwalk None (k (inl None))
           | None =>
               (* ANY RAM write of nonzero width, conditional or not
                  ([WeakSailLTS] delta (e''), stage C4) *)
               (if dev_addr (Interface.WriteReq.pa req') then True
                else n' ≠ 0%N) ∧
               gwalk None (k (inl None))
           end
       | Interface.Barrier _ => λ k,
           match w with
           | Some _ => False
           | None => ∀ r, gwalk None (k r)
           end
       | Interface.ExtraOutcome _ => λ _,
           (* (e''') SINCE STAGE C6 THE WINDOW-CLOSED MODE IS [True], matching
              [WeakSailLTS]'s narrowed arm: [Interface.ExtraOutcome] is
              indexed by the MONAD'S OWN RETURN TYPE and [sail_mstep] has no
              arm for it, so a raised Sail exception is a DEAD END and
              nothing may be asked of its continuation — asking [∀ r, …]
              there walks the rest of the instruction at every value of that
              type, which is finding (O9).

              THE WINDOW-OPEN MODE KEEPS [False], and that is a KIT-SIDE
              strengthening, not a specification claim ([WeakSailLTS]'s
              [amo_tail] admits the node): [Defs.try_catch] REPLACES an
              [ExtraOutcome] node by the handler AT THE WINDOW THAT NODE WAS
              REACHED UNDER, and every handler the model builds
              ([catch_early_return], [liftR]) ends in [returnm]/[throw], i.e.
              closes nothing — so admitting a throw inside a window here
              would make [gwalk_try_catch] demand [gwalk (Some _) (h e)] and
              refute it at [catch_early_return].  The abandoning reading is
              [WeakShapeOverrides.gwalkx], whose arm IS [True] in both
              modes. *)
           match w with Some _ => False | None => True end
       | _ => λ k, ∀ r, gwalk w (k r)
       end) k
  end.

(** [xf]: an [ExtraOutcome] (a raised Sail exception) is FATAL.  [true] is
    [sail_live]; [false] is the hypothesis a [try_catch] argument satisfies. *)
Fixpoint glive (xf : bool) (m : mon) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → mon) → Prop with
       | Interface.MemRead n req => λ k,
           ∀ v : bv (8 * n), glive xf (k (inl (v, None)))
       | Interface.MemWrite _ _ => λ k, glive xf (k (inl None))
       | Interface.ExtraOutcome _ => λ _, if xf then False else True
       | Interface.GenericFail _ => λ _, False
       | Interface.Discard => λ _, False
       | Interface.Choose ty =>
           match ty as t return (Values.choose_type t → mon) → Prop with
           | Values.ChooseReal => λ _, False
           | _ => λ k, ∀ r, glive xf (k r)
           end
       | _ => λ k, ∀ r, glive xf (k r)
       end) k
  end.

(** [gquiet]: the polymorphic twin of [WeakSailComplete.quiet_tail], with
    BARRIERS ALSO EXCLUDED.  This is exactly "register / trace / choice code"
    — the class of prefixes an OPEN EXCLUSIVE WINDOW may cross (the wording
    of [WeakSailLTS]'s delta (e)).  It is what makes [bind] usable inside a
    window: [gwalk w (Defs.bind m k)] does NOT follow from [gwalk w m] when
    [m] returns (a [Ret] under an open window is [False]); it follows from
    [gquiet m] — see [gwalk_bind_quiet]. *)
Fixpoint gquiet (m : mon) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T → mon) → Prop with
       | Interface.MemRead _ _ => λ _, False
       | Interface.MemWrite _ _ => λ _, False
       | Interface.Barrier _ => λ _, False
       | Interface.ExtraOutcome _ => λ _, False
       | Interface.GenericFail _ => λ _, False
       | Interface.Discard => λ _, False
       | Interface.Choose ty =>
           match ty as t return (Values.choose_type t → mon) → Prop with
           | Values.ChooseReal => λ _, False
           | _ => λ k, ∀ r, gquiet (k r)
           end
       | _ => λ k, ∀ r, gquiet (k r)
       end) k
  end.

End Walk.

Arguments gwalk {E A} w m.
Arguments gquiet {E A} m.
Arguments glive {E A} xf m.

(** A monad is OK when it is shaped AND live. *)
Definition gok {E A} (m : Defs.monad E A) : Prop := gwalk None m ∧ glive true m.

(* ---------------------------------------------------------------------- *)
(** *** 1a. The two predicates of the LTS are instances *)

Lemma gwalk_unit (m : M unit) :
  (gwalk None m → sail_shaped m) ∧
  (∀ pa n, gwalk (Some (pa, n)) m → amo_tail pa n m).
Proof.
  induction m as [x|T oc k IH]; [by split; [done|intros ??]|].
  destruct oc; simpl.
  (* the generic silent arms *)
  all: try (split; [intros H r; by apply IH, H
                   |intros pa1 n1 H r; by apply IH, H]).
  - (* MemRead *)
    split; [|by intros pa1 n1].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros H v; by apply IH, H. }
    intros [Hc H]. split; [done|].
    destruct (ak_latest _).
    + intros v. by apply IH, H.
    + intros v. by apply IH, H.
  - (* MemWrite *)
    split.
    + destruct (dev_addr (Interface.WriteReq.pa t)).
      * intros [_ H]. split; [done|by apply IH, H].
      * intros [Hn H]. split; [done|by apply IH, H].
    + intros pa1 n1 (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH, H6.
  - (* Barrier *)
    split; [intros H r; by apply IH, H|by intros pa1 n1].
  - (* ExtraOutcome: (e''') — a dead end on both sides *)
    by split.
Qed.

Lemma gwalk_shaped (m : M unit) : gwalk None m → sail_shaped m.
Proof. apply gwalk_unit. Qed.

Lemma gwalk_amo_tail pa n (m : M unit) :
  gwalk (Some (pa, n)) m → amo_tail pa n m.
Proof. apply gwalk_unit. Qed.

Lemma glive_live (m : M unit) : glive true m ↔ sail_live m.
Proof.
  induction m as [x|T oc k IH]; [done|].
  destruct oc; simpl; try (split; intros H r; by apply IH, H); try done.
  - destruct ty; simpl; (split; [done|done]) ||
      (split; intros H r; by apply IH, H).
Qed.

(** The definitive form: [gok] on the instruction monad is exactly the two
    stage-C premises. *)
Lemma gok_stageC (m : M unit) : gok m → sail_shaped m ∧ sail_live m.
Proof.
  intros [H1 H2]. split; [by apply gwalk_shaped|by apply glive_live].
Qed.

(* ---------------------------------------------------------------------- *)
(** *** 1b. Elementary structure of the two predicates *)

Lemma glive_weaken {E A} (m : Defs.monad E A) : glive true m → glive false m.
Proof.
  induction m as [x|T oc k IH]; [done|].
  destruct oc; simpl; try (intros H r; by apply IH); try done.
  - (* MemWrite *) intros H; by apply IH.
  - destruct ty; simpl; try done; intros H r; by apply IH.
Qed.

(** A QUIET TAIL ABANDONS THE WINDOW, and that is now legal.  This replaces
    the two refutations [gwalk_some_quiet_False] / [amo_tail_quiet_False]
    that stood here through stage C1 and were the machine-checked half of
    obstacle (O2): they said a window can never close on quiet code, which
    was fatal only because [amo_tail]'s [Interface.Ret] arm was [False].  It
    is [True] since C2, so the same fact is now the POSITIVE lemma the
    abandoning sites ([execute_LOADRES] and friends) discharge: it is
    [gwalk_quiet] (§3) at an open window, and [gquiet_amo_tail] beside it. *)

(* ====================================================================== *)
(** ** 2. [bind] — the core of the kit

    The window-indexed statement is what makes [bind] compositional in BOTH
    modes at once: a window that is open in [m] must CLOSE inside [m]
    (because [gwalk (Some _) (Ret _)] is [False]), after which the
    continuation is walked with no window — so the hypothesis on [k] is the
    same [gwalk None] in both modes. *)

(** THE WINDOW-INDEXED BIND, and why it is the CLOSED reading that makes it
    work.  A window open in [m] must CLOSE inside [m] — [gwalk (Some _)
    (Interface.Ret _)] is [False] — after which the continuation is walked
    with no window; so the hypothesis on [k] is the same [gwalk None] in both
    modes.

    UNDER THE WEAK ([amo_tail]) READING THIS LEMMA IS FALSE, and that is the
    C2 finding recorded in the header: take [m] a bare exclusive read whose
    continuation returns (a window abandoned at [m]'s [Interface.Ret], which
    the weak reading admits) and [k] a plain store — then [bind m k] has the
    exclusive read followed by a NON-closing write, which no reading admits.
    The window ESCAPES the bind, so a weak-reading bind lemma would have to
    hypothesise [k] walkable under an arbitrary window, i.e. essentially
    quiet — which every ordinary continuation in the model is not.  The same
    argument refutes the loop lemmas of §5.  Hence the kit stays on the
    closed reading (sound for [sail_shaped] by [gwalk_amo_tail]), and
    covering the ABANDONING exclusive sites needs one more index — "no
    window escapes [m]" — which is a C3 item, not a C2 one. *)
Lemma gwalk_bind {E A B} (w : win) (m : Defs.monad E A)
    (k : A → Defs.monad E B) :
  gwalk w m → (∀ x, gwalk None (k x)) → gwalk w (Defs.bind m k).
Proof.
  revert w. induction m as [x|T oc k0 IH]; intros w Hm Hk.
  { destruct w; [done|apply Hk]. }
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - (* MemRead *)
    destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _).
    + intros v. by apply IH.
    + intros v. by apply IH.
  - (* MemWrite *)
    destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - (* Barrier *)
    destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - (* ExtraOutcome: (e''') — nothing is asked of the continuation *)
    done.
Qed.

Lemma glive_bind {E A B} xf (m : Defs.monad E A) (k : A → Defs.monad E B) :
  glive xf m → (∀ x, glive xf (k x)) → glive xf (Defs.bind m k).
Proof.
  induction m as [x|T oc k0 IH]; intros Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  - (* MemWrite *) by apply IH.
  - destruct ty; simpl in Hm |- *; try done; intros r; by apply IH.
Qed.

Lemma gok_bind {E A B} (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gok m → (∀ x, gok (k x)) → gok (Defs.bind m k).
Proof.
  intros [H1 H2] Hk. split.
  - apply gwalk_bind; [done|intros x; apply Hk].
  - apply glive_bind; [done|intros x; apply Hk].
Qed.

(** [>>] *)
Lemma gok_bind0 {E A} (m : Defs.monad E unit) (n : Defs.monad E A) :
  gok m → gok n → gok (Defs.bind0 m n).
Proof. intros ??. by apply gok_bind. Qed.

Lemma gwalk_bind0 {E A} w (m : Defs.monad E unit) (n : Defs.monad E A) :
  gwalk w m → gwalk None n → gwalk w (Defs.bind0 m n).
Proof. intros ??. by apply gwalk_bind. Qed.

Lemma glive_bind0 {E A} xf (m : Defs.monad E unit) (n : Defs.monad E A) :
  glive xf m → glive xf n → glive xf (Defs.bind0 m n).
Proof. intros ??. by apply glive_bind. Qed.

(* ====================================================================== *)
(** ** 3. Quiet code, and the leaves

    Every leaf of the generated vocabulary except the two memory outcomes,
    the barrier and the failure family is QUIET, and quietness is the single
    hypothesis that gives all three predicates at once — including the
    WINDOW-CROSSING form [gwalk_bind_quiet], which is what an exclusive
    window needs to travel from its [MemRead] to its conditional
    [MemWrite]. *)

(** The FAILURE FAMILY first: [fail]/[exit] are SHAPED (their continuation
    type is [False], so every walk over them is vacuous) and NEVER LIVE;
    [throw] is shaped with the window closed, and live only in the "caught"
    mode [xf = false]. *)
Lemma gwalk_fail {E A} w (msg : String.string) :
  gwalk w (Defs.fail (A := A) (E := E) msg).
Proof. rewrite /Defs.fail /=. by intros []. Qed.

Lemma gwalk_exit {E A} w : gwalk w (Defs.exit (A := A) (E := E) tt).
Proof. apply gwalk_fail. Qed.

Lemma fail_not_live {E A} xf (msg : String.string) :
  glive xf (Defs.fail (A := A) (E := E) msg) → False.
Proof. done. Qed.

Lemma exit_not_live {E A} xf : glive xf (Defs.exit (A := A) (E := E) tt) → False.
Proof. done. Qed.

(** The [bind]-consumed forms, which is how they occur in the generated
    code ([… >>= fun x => …] with a failing left operand). *)
Lemma gwalk_bind_fail {E A B} w (msg : String.string) (k : A → Defs.monad E B) :
  gwalk w (Defs.bind (Defs.fail msg) k).
Proof. rewrite /Defs.fail /Defs.bind /=. by intros []. Qed.

Lemma gwalk_bind_exit {E A B} w (k : A → Defs.monad E B) :
  gwalk w (Defs.bind (Defs.exit tt) k).
Proof. apply gwalk_bind_fail. Qed.

Lemma bind_exit_not_live {E A B} xf (k : A → Defs.monad E B) :
  glive xf (Defs.bind (Defs.exit tt) k) → False.
Proof. done. Qed.

Lemma gwalk_throw {E A} (e : E) : gwalk None (Defs.throw (A := A) e).
Proof. done. Qed.

(** THE KIT-SIDE STRENGTHENING, STILL A REFUTATION AFTER (e'''): the
    specification ([WeakSailLTS.amo_tail]) admits a throw inside a window,
    but [gwalk] does not — see the [ExtraOutcome] arm for why
    ([gwalk_try_catch] would otherwise need its handler at an open window,
    which [catch_early_return]'s [returnm] arm refutes).  The abandoning
    reading [WeakShapeOverrides.gwalkx] is where such a site is walked. *)
Lemma gwalk_throw_some {E A} pa n (e : E) :
  gwalk (Some (pa, n)) (Defs.throw (A := A) e) → False.
Proof. done. Qed.

Lemma glive_throw {E A} (e : E) : glive false (Defs.throw (A := A) e).
Proof. done. Qed.

Lemma throw_not_live {E A} (e : E) : glive true (Defs.throw (A := A) e) → False.
Proof. done. Qed.

Lemma gwalk_quiet {E A} (m : Defs.monad E A) : gquiet m → gwalk None m.
Proof.
  induction m as [x|T oc k IH]; [done|].
  destruct oc; simpl; try done; try (intros H r; by apply IH).
  destruct ty; simpl; try done; intros H r; by apply IH.
Qed.

Lemma glive_quiet {E A} xf (m : Defs.monad E A) : gquiet m → glive xf m.
Proof.
  induction m as [x|T oc k IH]; [done|].
  destruct oc; simpl; try done; try (intros H r; by apply IH).
  destruct ty; simpl; try done; intros H r; by apply IH.
Qed.

Lemma gok_quiet {E A} (m : Defs.monad E A) : gquiet m → gok m.
Proof. intros H. split; [by apply gwalk_quiet|by apply glive_quiet]. Qed.

Lemma gquiet_bind {E A B} (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gquiet m → (∀ x, gquiet (k x)) → gquiet (Defs.bind m k).
Proof.
  induction m as [x|T oc k0 IH]; intros Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; try done; intros r; by apply IH.
Qed.

(** THE WINDOW-CROSSING BIND.  [gwalk_bind] cannot carry an open window into
    the continuation ([gwalk (Some _) (Interface.Ret _)] is [False] — by
    design: the window must close before the instruction ends).  A QUIET
    prefix carries it: this is the lemma every exclusive call site uses to
    walk from the reserved read to the conditional write. *)
Lemma gwalk_bind_quiet {E A B} w (m : Defs.monad E A) (k : A → Defs.monad E B) :
  gquiet m → (∀ x, gwalk w (k x)) → gwalk w (Defs.bind m k).
Proof.
  induction m as [x|T oc k0 IH]; intros Hm Hk; [by apply Hk|].
  rewrite /Defs.bind /=. destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; try done; intros r; by apply IH.
Qed.

(** THE ABANDONMENT FACT, which is what the sites that open a window and
    never close it ([execute_LOADRES] and the fault arms of §7c) discharge.
    It is stated at [WeakSailLTS.amo_tail] — NOT at [gwalk (Some _)], which
    is the closed reading and refutes it — and it is the positive replacement
    for the two refutations ([gwalk_some_quiet_False], [amo_tail_quiet_False])
    that stood in §1b through stage C1. *)
Lemma gquiet_amo_tail pa n (m : M unit) : gquiet m → amo_tail pa n m.
Proof.
  induction m as [x|T oc k IH]; [done|].
  destruct oc; simpl; try done; try (intros H r; by apply IH).
  destruct ty; simpl; try done; intros H r; by apply IH.
Qed.

Lemma gquiet_bind0 {E A} (m : Defs.monad E unit) (n : Defs.monad E A) :
  gquiet m → gquiet n → gquiet (Defs.bind0 m n).
Proof. intros ??. by apply gquiet_bind. Qed.

(* ---------------------------------------------------------------------- *)
(** *** 3a. The quiet leaves *)

Lemma gquiet_ret {E A} (x : A) : gquiet (Interface.Ret x : Defs.monad E A).
Proof. done. Qed.

Lemma gquiet_returnm {E A} (x : A) : gquiet (Defs.returnm (E := E) x).
Proof. done. Qed.

Lemma gok_ret {E A} (x : A) : gok (Interface.Ret x : Defs.monad E A).
Proof. by split. Qed.

Lemma gok_returnm {E A} (x : A) : gok (Defs.returnm (E := E) x).
Proof. by split. Qed.

Lemma gwalk_ret {E A} (x : A) : gwalk (E := E) None (Interface.Ret x).
Proof. done. Qed.

Lemma glive_ret {E A} xf (x : A) : glive (E := E) xf (Interface.Ret x).
Proof. done. Qed.

Lemma gquiet_read_reg {E} (r : Arch.reg) : gquiet (Defs.read_reg (e := E) r).
Proof. rewrite /Defs.read_reg /=. by intros v. Qed.

Lemma gquiet_write_reg {E} (r : Arch.reg) v : gquiet (Defs.write_reg (e := E) r v).
Proof. rewrite /Defs.write_reg /=. by intros u. Qed.

Lemma gquiet_read_reg_ref {E a}
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) :
  gquiet (Defs.read_reg_ref (e := E) rf).
Proof. rewrite /Defs.read_reg_ref /=. by intros v. Qed.

Lemma gquiet_reg_deref {E a}
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) :
  gquiet (Defs.reg_deref (e := E) rf).
Proof. apply gquiet_read_reg_ref. Qed.

Lemma gquiet_write_reg_ref {E a}
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) v :
  gquiet (Defs.write_reg_ref (e := E) rf v).
Proof. rewrite /Defs.write_reg_ref /=. by intros u. Qed.

Lemma gquiet_sys_reg_read {E a} id
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) :
  gquiet (Defs.sail_sys_reg_read (e := E) id rf).
Proof. rewrite /Defs.sail_sys_reg_read /=. by intros v. Qed.

Lemma gquiet_sys_reg_write {E a} id
    (rf : @Values.register_ref Arch.reg Arch.reg_type a) v :
  gquiet (Defs.sail_sys_reg_write (e := E) id rf v).
Proof. rewrite /Defs.sail_sys_reg_write /=. by intros u. Qed.

Lemma gquiet_instr_announce {E sz} (op : Values.mword sz) :
  gquiet (Defs.instr_announce (e := E) op).
Proof. rewrite /Defs.instr_announce /=. by intros u. Qed.

Lemma gquiet_branch_announce {E} sz (a : Values.mword sz) :
  gquiet (Defs.branch_announce (e := E) sz a).
Proof. rewrite /Defs.branch_announce /=. by intros u. Qed.

Lemma gquiet_sail_take_exception {E} f :
  gquiet (Defs.sail_take_exception (e := E) f).
Proof. rewrite /Defs.sail_take_exception /=. by intros u. Qed.

Lemma gquiet_sail_return_exception {E} pa :
  gquiet (Defs.sail_return_exception (e := E) pa).
Proof. rewrite /Defs.sail_return_exception /=. by intros u. Qed.

Lemma gquiet_sail_cache_op {E} o : gquiet (Defs.sail_cache_op (e := E) o).
Proof. rewrite /Defs.sail_cache_op /=. by intros u. Qed.

Lemma gquiet_sail_tlbi {E} o : gquiet (Defs.sail_tlbi (e := E) o).
Proof. rewrite /Defs.sail_tlbi /=. by intros u. Qed.

Lemma gquiet_translation_start {E} ts :
  gquiet (Defs.sail_translation_start (e := E) ts).
Proof. rewrite /Defs.sail_translation_start /=. by intros u. Qed.

Lemma gquiet_translation_end {E} te :
  gquiet (Defs.sail_translation_end (e := E) te).
Proof. rewrite /Defs.sail_translation_end /=. by intros u. Qed.

Lemma gquiet_cycle_count {E} u : gquiet (Defs.cycle_count (e := E) u).
Proof. rewrite /Defs.cycle_count /=. by intros x. Qed.

Lemma gquiet_get_cycle_count {E} u : gquiet (Defs.get_cycle_count (e := E) u).
Proof. rewrite /Defs.get_cycle_count /=. by intros x. Qed.

Lemma gquiet_print_effect {E} s : gquiet (Defs.print_effect (e := E) s).
Proof. rewrite /Defs.print_effect /=. by intros x. Qed.

(** The [Choose] family: single [Choose] nodes with [Ret] continuations.
    [choose_real] is the ONE exclusion — it builds [Values.ChooseReal], which
    [glive] (and [quiet_tail]) refute.  Checked below: no [choose_real] and
    no [undefined_real] occurs anywhere in the reachable model. *)
Lemma gquiet_choose {E A} (ty : Values.ChooseType)
    (k : Values.choose_type ty → Defs.monad E A) :
  ty ≠ Values.ChooseReal → (∀ r, gquiet (k r)) →
  gquiet (Interface.Next (Interface.Choose ty) k).
Proof. by destruct ty. Qed.

Lemma gquiet_choose_bool {E} d : gquiet (Defs.choose_bool (E := E) d).
Proof. done. Qed.
Lemma gquiet_choose_int {E} d : gquiet (Defs.choose_int (E := E) d).
Proof. done. Qed.
Lemma gquiet_choose_nat {E} d : gquiet (Defs.choose_nat (E := E) d).
Proof. done. Qed.
Lemma gquiet_choose_string {E} d : gquiet (Defs.choose_string (E := E) d).
Proof. done. Qed.
Lemma gquiet_choose_range {E} d lo hi : gquiet (Defs.choose_range (E := E) d lo hi).
Proof. done. Qed.
Lemma gquiet_choose_bitvector {E} d n : gquiet (Defs.choose_bitvector (E := E) d n).
Proof. done. Qed.

(** [choose_real] / [undefined_real]: NOT live, NOT quiet. *)
Lemma choose_real_not_live {E} d :
  glive (E := E) true (Defs.choose_real d) → False.
Proof. done. Qed.

Lemma gquiet_undefined_unit {E} u : gquiet (Defs.undefined_unit (E := E) u).
Proof. done. Qed.
Lemma gquiet_undefined_bool {E} u : gquiet (Defs.undefined_bool (E := E) u).
Proof. done. Qed.
Lemma gquiet_undefined_int {E} u : gquiet (Defs.undefined_int (E := E) u).
Proof. done. Qed.
Lemma gquiet_undefined_nat {E} u : gquiet (Defs.undefined_nat (E := E) u).
Proof. done. Qed.
Lemma gquiet_undefined_string {E} u : gquiet (Defs.undefined_string (E := E) u).
Proof. done. Qed.
Lemma gquiet_undefined_range {E} i j : gquiet (Defs.undefined_range (E := E) i j).
Proof. done. Qed.
Lemma gquiet_undefined_bitvector {E} n : gquiet (Defs.undefined_bitvector (E := E) n).
Proof. done. Qed.
Lemma gquiet_undefined_vector {E T} n `{Inhabited T} (a : T) :
  gquiet (Defs.undefined_vector (E := E) n a).
Proof. done. Qed.

(** [assert_exp] / [assert_exp']: quiet exactly when the assertion holds;
    SHAPED unconditionally (a [GenericFail] continuation is [False → _], so
    the walk is vacuous), never live when it fails. *)
Lemma gquiet_assert_exp {E} msg : gquiet (Defs.assert_exp (E := E) true msg).
Proof. done. Qed.

Lemma gquiet_assert_exp' {E} msg : gquiet (Defs.assert_exp' (E := E) true msg).
Proof. done. Qed.

Lemma gok_assert_exp {E} msg : gok (Defs.assert_exp (E := E) true msg).
Proof. by apply gok_quiet, gquiet_assert_exp. Qed.

Lemma gok_assert_exp' {E} msg : gok (Defs.assert_exp' (E := E) true msg).
Proof. by apply gok_quiet, gquiet_assert_exp'. Qed.

Lemma gwalk_assert_exp {E} (b : bool) msg :
  gwalk (E := E) None (Defs.assert_exp b msg).
Proof. rewrite /Defs.assert_exp. destruct b; [done|apply gwalk_fail]. Qed.

Lemma gwalk_assert_exp' {E} (b : bool) msg :
  gwalk (E := E) None (Defs.assert_exp' b msg).
Proof. rewrite /Defs.assert_exp'. destruct b; [done|apply gwalk_fail]. Qed.

Lemma assert_exp_false_not_live {E} msg :
  glive (E := E) true (Defs.assert_exp false msg) → False.
Proof. done. Qed.

(** The BARRIER: shaped and live, but it CLOSES no window and may not occur
    inside one (the LTS's fused [LRmw] label has no room for a fence). *)
Lemma gok_sail_barrier {E} (b : Arch.barrier) : gok (Defs.sail_barrier (e := E) b).
Proof. split; [by intros u|by intros u]. Qed.

Lemma gwalk_sail_barrier_some {E} pa n (b : Arch.barrier) :
  gwalk (E := E) (Some (pa, n)) (Defs.sail_barrier b) → False.
Proof. done. Qed.

(* ====================================================================== *)
(** ** 4. The exception / early-return combinators

    [try_catch] traverses [m] replacing every [ExtraOutcome] node by [h e]
    and DISCARDING that node's continuation.  So the argument's hypothesis is
    the "caught" liveness [glive false] and the handler carries the rest.

    For the WINDOW the same shape holds, and it says something sharp: a
    window open at a throw must be closed BY THE HANDLER.  Every handler the
    model builds ([catch_early_return], [liftR]) ends in [returnm]/[throw],
    i.e. closes nothing — so an exclusive window can cross such a boundary
    only when the enclosed code provably raises NOTHING.  That is
    [gwalk_try_catch_live], and it is the shape all three exclusive call
    sites need.  It is also why [gwalk]'s [ExtraOutcome] arm keeps [False]
    in the window-open mode after (e''') — see the arm's own comment. *)

Lemma gwalk_try_catch {A E1 E2} w (m : Defs.monad E1 A) (h : E1 → Defs.monad E2 A) :
  gwalk w m → (∀ e, gwalk None (h e)) → gwalk w (Defs.try_catch m h).
Proof.
  revert w. induction m as [x|T oc k IH]; intros w Hm Hh; [by destruct w|].
  destruct oc; simpl in Hm |- *.
  all: try (intros r; by apply IH).
  - (* MemRead *)
    destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _).
    + intros v. by apply IH.
    + intros v. by apply IH.
  - (* MemWrite *)
    destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - (* Barrier *)
    destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - (* ExtraOutcome: under an open window the hypothesis is [False] (the
       kit-side strengthening the arm keeps); with the window closed, the
       handler. *)
    destruct w as [[pa0 n0]|]; [done|]. apply Hh.
Qed.

(** If [m] raises nothing, [try_catch] is TRANSPARENT to both predicates and
    the handler is irrelevant. *)
Lemma gwalk_try_catch_live {A E1 E2} w (m : Defs.monad E1 A)
    (h : E1 → Defs.monad E2 A) :
  gwalk w m → glive true m → gwalk w (Defs.try_catch m h).
Proof.
  revert w. induction m as [x|T oc k IH]; intros w Hm Hl; [by destruct w|].
  destruct oc; simpl in Hm, Hl |- *.
  all: try (intros r; by apply IH).
  all: try done.
  - destruct w as [[pa0 n0]|]; [done|].
    destruct (dev_addr (Interface.ReadReq.pa t)).
    { intros v. by apply IH. }
    destruct Hm as [Hc Hm]. split; [done|].
    destruct (ak_latest _).
    + intros v. by apply IH.
    + intros v. by apply IH.
  - destruct w as [[pa0 n0]|].
    + destruct Hm as (H1 & H2 & H3 & H4 & H5 & H6).
      split_and!; try done. by apply IH.
    + destruct Hm as [H1 H2]. split; [done|]. by apply IH.
  - destruct w as [[pa0 n0]|]; [done|]. intros r. by apply IH.
  - destruct ty; simpl in Hl |- *; try done; intros r; by apply IH.
Qed.

Lemma glive_try_catch_live {A E1 E2} xf (m : Defs.monad E1 A)
    (h : E1 → Defs.monad E2 A) :
  glive true m → glive xf (Defs.try_catch m h).
Proof.
  induction m as [x|T oc k IH]; intros Hl; [done|].
  destruct oc; simpl in Hl |- *; try (intros r; by apply IH); try done.
  - (* MemWrite *) by apply IH.
  - destruct ty; simpl in Hl |- *; try done; intros r; by apply IH.
Qed.

Lemma glive_try_catch {A E1 E2} xf (m : Defs.monad E1 A) (h : E1 → Defs.monad E2 A) :
  glive false m → (∀ e, glive xf (h e)) → glive xf (Defs.try_catch m h).
Proof.
  induction m as [x|T oc k IH]; intros Hm Hh; [done|].
  destruct oc; simpl in Hm |- *;
    try (intros r; by apply IH); try done; try (by apply Hh).
  - (* MemWrite *) by apply IH.
  - destruct ty; simpl in Hm |- *; try done; intros r; by apply IH.
Qed.

Lemma gquiet_try_catch {A E1 E2} (m : Defs.monad E1 A) (h : E1 → Defs.monad E2 A) :
  gquiet m → gquiet (Defs.try_catch m h).
Proof.
  induction m as [x|T oc k IH]; intros Hm; [done|].
  destruct oc; simpl in Hm |- *; try (intros r; by apply IH); try done.
  destruct ty; simpl in Hm |- *; try done; intros r; by apply IH.
Qed.

Lemma gok_try_catch {A E1 E2} (m : Defs.monad E1 A) (h : E1 → Defs.monad E2 A) :
  gwalk None m → glive false m → (∀ e, gok (h e)) → gok (Defs.try_catch m h).
Proof.
  intros Hw Hl Hh. split.
  - apply gwalk_try_catch; [done|intros e; apply Hh].
  - apply glive_try_catch; [done|intros e; apply Hh].
Qed.

(* ---------------------------------------------------------------------- *)
(** *** 4a. [early_return] / [liftR] / [catch_early_return] / [try_catchR] *)

Lemma gwalk_early_return {A R E} (r : R) :
  gwalk None (Defs.early_return (A := A) (E := E) r).
Proof. apply gwalk_throw. Qed.

Lemma glive_early_return {A R E} (r : R) :
  glive false (Defs.early_return (A := A) (E := E) r).
Proof. apply glive_throw. Qed.

Lemma gwalk_liftR {A R E} (m : Defs.monad E A) :
  gwalk None m → gwalk None (Defs.liftR (R := R) m).
Proof.
  intros H. rewrite /Defs.liftR.
  apply gwalk_try_catch; [done|intros e; apply gwalk_throw].
Qed.

Lemma gwalk_liftR_win {A R E} w (m : Defs.monad E A) :
  gwalk w m → glive true m → gwalk w (Defs.liftR (R := R) m).
Proof. intros ??. by apply gwalk_try_catch_live. Qed.

Lemma glive_liftR {A R E} xf (m : Defs.monad E A) :
  glive true m → glive xf (Defs.liftR (R := R) m).
Proof. intros H. by apply glive_try_catch_live. Qed.

Lemma glive_liftR_x {A R E} (m : Defs.monad E A) :
  glive false m → glive false (Defs.liftR (R := R) m).
Proof.
  intros H. apply glive_try_catch; [done|intros e; apply glive_throw].
Qed.

Lemma gquiet_liftR {A R E} (m : Defs.monad E A) :
  gquiet m → gquiet (Defs.liftR (R := R) m).
Proof. apply gquiet_try_catch. Qed.

Lemma gwalk_catch_early_return {A E} (m : Defs.monadR A E A) :
  gwalk None m → gwalk None (Defs.catch_early_return m).
Proof.
  intros H. rewrite /Defs.catch_early_return.
  apply gwalk_try_catch; [done|]. intros [a|e]; [done|apply gwalk_throw].
Qed.

Lemma gwalk_catch_early_return_win {A E} w (m : Defs.monadR A E A) :
  gwalk w m → glive true m → gwalk w (Defs.catch_early_return m).
Proof. intros ??. by apply gwalk_try_catch_live. Qed.

(** NOTE the hypothesis: [catch_early_return]'s handler RE-THROWS a genuine
    exception ([inr e]), which is not live.  So full liveness of the result
    needs the argument to raise NOTHING — [glive true m], not
    [glive false m].  Splitting the two roles of [monadR]'s [R + E] (early
    returns are fine, exceptions are not) would need a third index on
    [glive]; the model never relies on it, so it is left undone. *)
Lemma glive_catch_early_return {A E} xf (m : Defs.monadR A E A) :
  glive true m → glive xf (Defs.catch_early_return m).
Proof. intros H. by apply glive_try_catch_live. Qed.

Lemma gquiet_catch_early_return {A E} (m : Defs.monadR A E A) :
  gquiet m → gquiet (Defs.catch_early_return m).
Proof. apply gquiet_try_catch. Qed.

Lemma gwalk_try_catchR {A R E} (m : Defs.monadR R E A) (h : E → Defs.monadR R E A) :
  gwalk None m → (∀ e, gwalk None (h e)) → gwalk None (Defs.try_catchR m h).
Proof.
  intros Hm Hh. rewrite /Defs.try_catchR.
  apply gwalk_try_catch; [done|]. intros [r|e]; [apply gwalk_throw|apply Hh].
Qed.

(** [try_catchR] RE-THROWS the early return, so its result is live only in
    the "caught" mode — the [catch_early_return] above it is what closes it. *)
Lemma glive_try_catchR {A R E} (m : Defs.monadR R E A)
    (h : E → Defs.monadR R E A) :
  glive false m → (∀ e, glive false (h e)) → glive false (Defs.try_catchR m h).
Proof.
  intros Hm Hh. rewrite /Defs.try_catchR.
  apply glive_try_catch; [done|]. intros [r|e]; [apply glive_throw|apply Hh].
Qed.

Lemma gok_pure_early_return_embed {A R E} (v : R + A) :
  gwalk None (Defs.pure_early_return_embed (E := E) v) ∧
  glive false (Defs.pure_early_return_embed (E := E) v).
Proof.
  by destruct v as [r|a]; split.
Qed.

(* ====================================================================== *)
(** ** 5. The loop combinators

    [foreachM] and the four [foreach_Z*] variants are STRUCTURAL, hence fully
    compositional in all three predicates.  [whileMT]/[untilMT] are NOT:
    their guard ends in [fail "Termination limit reached"], so [glive] of a
    loop is a SEMANTIC fact (the measure really bounds the iterations) and
    must be discharged per site.  [gwalk] is fine for them, because a
    [GenericFail] continuation is [False → _] and the walk over it is
    vacuous — obstacle (O3) is liveness-only. *)

Lemma gwalk_foreachM {E a Vars} w (l : list a) (vars : Vars)
    (body : a → Vars → Defs.monad E Vars) :
  (∀ x v, gwalk None (body x v)) → w = None →
  gwalk w (Defs.foreachM l vars body).
Proof.
  intros Hb ->. revert vars. induction l as [|x xs IH]; intros vars; [done|].
  simpl. apply gwalk_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma glive_foreachM {E a Vars} xf (l : list a) (vars : Vars)
    (body : a → Vars → Defs.monad E Vars) :
  (∀ x v, glive xf (body x v)) → glive xf (Defs.foreachM l vars body).
Proof.
  intros Hb. revert vars. induction l as [|x xs IH]; intros vars; [done|].
  simpl. apply glive_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma gquiet_foreachM {E a Vars} (l : list a) (vars : Vars)
    (body : a → Vars → Defs.monad E Vars) :
  (∀ x v, gquiet (body x v)) → gquiet (Defs.foreachM l vars body).
Proof.
  intros Hb. revert vars. induction l as [|x xs IH]; intros vars; [done|].
  simpl. apply gquiet_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma gok_foreachM {E a Vars} (l : list a) (vars : Vars)
    (body : a → Vars → Defs.monad E Vars) :
  (∀ x v, gok (body x v)) → gok (Defs.foreachM l vars body).
Proof.
  intros Hb. split.
  - apply gwalk_foreachM; [intros x v; apply Hb|done].
  - apply glive_foreachM. intros x v; apply Hb.
Qed.

Lemma gwalk_foreach_ZM_up' {E Vars} (from to step : Z) (n : nat) (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gwalk None (body z v)) →
  gwalk None (Defs.foreach_ZM_up' from to step n vars body).
Proof.
  intros Hb. revert from vars. induction n as [|n IH]; intros from vars.
  - rewrite /Defs.foreach_ZM_up'. by destruct (from <=? to)%Z.
  - simpl. destruct (from <=? to)%Z; [|done].
    apply gwalk_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma glive_foreach_ZM_up' {E Vars} xf (from to step : Z) (n : nat) (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, glive xf (body z v)) →
  glive xf (Defs.foreach_ZM_up' from to step n vars body).
Proof.
  intros Hb. revert from vars. induction n as [|n IH]; intros from vars.
  - rewrite /Defs.foreach_ZM_up'. by destruct (from <=? to)%Z.
  - simpl. destruct (from <=? to)%Z; [|done].
    apply glive_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma gquiet_foreach_ZM_up' {E Vars} (from to step : Z) (n : nat) (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gquiet (body z v)) →
  gquiet (Defs.foreach_ZM_up' from to step n vars body).
Proof.
  intros Hb. revert from vars. induction n as [|n IH]; intros from vars.
  - rewrite /Defs.foreach_ZM_up'. by destruct (from <=? to)%Z.
  - simpl. destruct (from <=? to)%Z; [|done].
    apply gquiet_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma gwalk_foreach_ZM_down' {E Vars} (from to step : Z) (n : nat) (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gwalk None (body z v)) →
  gwalk None (Defs.foreach_ZM_down' from to step n vars body).
Proof.
  intros Hb. revert from vars. induction n as [|n IH]; intros from vars.
  - rewrite /Defs.foreach_ZM_down'. by destruct (to <=? from)%Z.
  - simpl. destruct (to <=? from)%Z; [|done].
    apply gwalk_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma glive_foreach_ZM_down' {E Vars} xf (from to step : Z) (n : nat) (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, glive xf (body z v)) →
  glive xf (Defs.foreach_ZM_down' from to step n vars body).
Proof.
  intros Hb. revert from vars. induction n as [|n IH]; intros from vars.
  - rewrite /Defs.foreach_ZM_down'. by destruct (to <=? from)%Z.
  - simpl. destruct (to <=? from)%Z; [|done].
    apply glive_bind; [apply Hb|intros v; apply IH].
Qed.

Lemma gok_foreach_ZM_up {E Vars} from to step (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gok (body z v)) → gok (Defs.foreach_ZM_up from to step vars body).
Proof.
  intros Hb. split.
  - apply gwalk_foreach_ZM_up'. intros z v; apply Hb.
  - apply glive_foreach_ZM_up'. intros z v; apply Hb.
Qed.

Lemma gok_foreach_ZM_down {E Vars} from to step (vars : Vars)
    (body : Z → Vars → Defs.monad E Vars) :
  (∀ z v, gok (body z v)) → gok (Defs.foreach_ZM_down from to step vars body).
Proof.
  intros Hb. split.
  - apply gwalk_foreach_ZM_down'. intros z v; apply Hb.
  - apply glive_foreach_ZM_down'. intros z v; apply Hb.
Qed.

Lemma gok_genlistM {E A} (f : nat → Defs.monad E A) (n : nat) :
  (∀ i, gok (f i)) → gok (Defs.genlistM f n).
Proof.
  intros Hf. rewrite /Defs.genlistM. apply gok_foreachM.
  intros i xs. apply gok_bind; [apply Hf|intros x; apply gok_ret].
Qed.

Lemma gok_and_boolM {E} (l r : Defs.monad E bool) :
  gok l → gok r → gok (Defs.and_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.and_boolM.
  apply gok_bind; [done|]. intros [|]; [done|apply gok_ret].
Qed.

Lemma gok_or_boolM {E} (l r : Defs.monad E bool) :
  gok l → gok r → gok (Defs.or_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.or_boolM.
  apply gok_bind; [done|]. intros [|]; [apply gok_ret|done].
Qed.

Lemma gquiet_and_boolM {E} (l r : Defs.monad E bool) :
  gquiet l → gquiet r → gquiet (Defs.and_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.and_boolM.
  apply gquiet_bind; [done|]. by intros [|].
Qed.

Lemma gquiet_or_boolM {E} (l r : Defs.monad E bool) :
  gquiet l → gquiet r → gquiet (Defs.or_boolM l r).
Proof.
  intros Hl Hr. rewrite /Defs.or_boolM.
  apply gquiet_bind; [done|]. by intros [|].
Qed.

Lemma gok_autocast_m {E m n} {T : Z → Type} `{H : Inhabited (T n)}
    (x : Defs.monad E (T m)) :
  gok x → gok (Defs.autocast_m (n := n) x).
Proof.
  intros Hx. rewrite /Defs.autocast_m.
  apply gok_bind; [done|intros v; apply gok_ret].
Qed.

Lemma gwalk_choose_from_list {A E} (descr : String.string) (xs : list A) :
  gwalk (E := E) None (Defs.choose_from_list descr xs).
Proof.
  rewrite /Defs.choose_from_list. apply gwalk_bind; [done|].
  intros idx. destruct (List.nth_error xs (Z.to_nat idx)); [done|apply gwalk_fail].
Qed.

(** [internal_pick] on a NON-EMPTY list is live only if the chosen index is
    in range — which the adversarial [Choose] does not guarantee.  So
    [choose_from_list] is SHAPED but not unconditionally LIVE: another
    (small) liveness residue, of the same family as (O3). *)
Lemma choose_from_list_not_live_nil {A E} (descr : String.string) :
  glive (E := E) true (Defs.choose_from_list descr (@nil A)) → False.
Proof.
  rewrite /Defs.choose_from_list /=. intros H.
  exact (H 0%Z).
Qed.

(** THE MEASURE-BOUNDED LOOPS.  Shape composes ([gwalk]); LIVENESS DOES NOT
    — the [limit < 0] arm is [fail "Termination limit reached"], and no
    hypothesis on [cond]/[body] can rule it out.  Discharging it is a
    semantic argument about the measure, per site; obstacle (O3). *)
Lemma gwalk_untilMT_acc {E Vars} (limit : Z) (vars : Vars)
    (cond : Vars → Defs.monad E bool) (body : Vars → Defs.monad E Vars)
    (acc : Acc (Zwf.Zwf 0%Z) limit) :
  (∀ v, gwalk None (cond v)) → (∀ v, gwalk None (body v)) →
  gwalk None (Defs.untilMT' limit vars cond body acc).
Proof.
  revert limit vars acc. fix IH 3. intros limit vars acc Hc Hb.
  destruct acc as [acc]. cbv [Defs.untilMT'].
  destruct (ZArith_dec.Z_ge_dec limit 0%Z); [|apply gwalk_fail].
  cbn [Defs.bind Interface.iMon_bind].
  apply gwalk_bind; [apply Hb|]. intros v.
  apply gwalk_bind; [apply Hc|]. intros [|]; [done|].
  apply IH; done.
Qed.

Lemma gwalk_untilMT {E Vars} (vars : Vars) (measure : Vars → Z)
    (cond : Vars → Defs.monad E bool) (body : Vars → Defs.monad E Vars) :
  (∀ v, gwalk None (cond v)) → (∀ v, gwalk None (body v)) →
  gwalk None (Defs.untilMT vars measure cond body).
Proof. intros ??. by apply gwalk_untilMT_acc. Qed.

Lemma gwalk_whileMT_acc {E Vars} (limit : Z) (vars : Vars)
    (cond : Vars → Defs.monad E bool) (body : Vars → Defs.monad E Vars)
    (acc : Acc (Zwf.Zwf 0%Z) limit) :
  (∀ v, gwalk None (cond v)) → (∀ v, gwalk None (body v)) →
  gwalk None (Defs.whileMT' limit vars cond body acc).
Proof.
  revert limit vars acc. fix IH 3. intros limit vars acc Hc Hb.
  destruct acc as [acc]. cbv [Defs.whileMT'].
  destruct (ZArith_dec.Z_ge_dec limit 0%Z); [|apply gwalk_fail].
  cbn [Defs.bind Interface.iMon_bind].
  apply gwalk_bind; [apply Hc|]. intros [|]; [|done].
  apply gwalk_bind; [apply Hb|]. intros v. apply IH; done.
Qed.

Lemma gwalk_whileMT {E Vars} (vars : Vars) (measure : Vars → Z)
    (cond : Vars → Defs.monad E bool) (body : Vars → Defs.monad E Vars) :
  (∀ v, gwalk None (cond v)) → (∀ v, gwalk None (body v)) →
  gwalk None (Defs.whileMT vars measure cond body).
Proof. intros ??. by apply gwalk_whileMT_acc. Qed.

(** …and the reason liveness cannot follow: the exhausted loop IS the
    failure. *)
Lemma untilMT_exhausted_not_live {E Vars} xf (limit : Z) (vars : Vars)
    (cond : Vars → Defs.monad E bool) (body : Vars → Defs.monad E Vars)
    (acc : Acc (Zwf.Zwf 0%Z) limit) :
  ¬ (limit >= 0)%Z →
  glive xf (Defs.untilMT' limit vars cond body acc) → False.
Proof.
  intros Hlt. destruct acc as [acc]. cbv [Defs.untilMT'].
  destruct (ZArith_dec.Z_ge_dec limit 0%Z); [done|]. done.
Qed.

(* ====================================================================== *)
(** ** 6. THE MEMORY LEAVES

    The only nodes the shape predicates actually constrain.  In this model
    every memory event is built in exactly two places — [rv64d.read_ram] and
    [rv64d.write_ram] — each of which wraps SailStdpp's
    [Defs.sail_mem_read]/[Defs.sail_mem_write] with an access-kind
    computation driven by the [read_kind]/[write_kind] argument.  So the
    per-wrapper lemmas below, keyed on that argument, are the WHOLE
    memory-side obligation of the sweep. *)

Require Import Riscv.rv64d.

(** The access-kind classification of every kind the model can produce.  All
    are computations, all are [ak_coh = false]: [read_kind_of_flags] /
    [write_kind_of_flags] pick the kind from the (aq, rl, res/con) FLAGS, and
    [Read_ifetch] — the one kind with [ak_coh = true] — is NEVER produced
    (confirmed by grep: it occurs only in [read_ram]'s dead match arm and in
    the [undefined_read_kind] enumeration). *)
Lemma classify_read_plain :
  classify (ConcurrencyInterfaceTypes.AK_explicit
              {| ConcurrencyInterfaceTypes.Explicit_access_kind_variety :=
                   ConcurrencyInterfaceTypes.AV_plain;
                 ConcurrencyInterfaceTypes.Explicit_access_kind_strength :=
                   ConcurrencyInterfaceTypes.AS_normal |})
  = AkInfo false false false.
Proof. reflexivity. Qed.

Lemma classify_excl_normal :
  classify (ConcurrencyInterfaceTypes.AK_explicit
              {| ConcurrencyInterfaceTypes.Explicit_access_kind_variety :=
                   ConcurrencyInterfaceTypes.AV_exclusive;
                 ConcurrencyInterfaceTypes.Explicit_access_kind_strength :=
                   ConcurrencyInterfaceTypes.AS_normal |})
  = AkInfo false true false.
Proof. reflexivity. Qed.

Lemma classify_excl_acq :
  classify (ConcurrencyInterfaceTypes.AK_explicit
              {| ConcurrencyInterfaceTypes.Explicit_access_kind_variety :=
                   ConcurrencyInterfaceTypes.AV_exclusive;
                 ConcurrencyInterfaceTypes.Explicit_access_kind_strength :=
                   ConcurrencyInterfaceTypes.AS_rel_or_acq |})
  = AkInfo false true true.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(** *** 6a. The raw nodes *)

Lemma gwalk_MemRead_plain {E A} n req (k : _ → Defs.monad E A) :
  ak_coh (classify (Interface.ReadReq.access_kind req)) = false →
  ak_latest (classify (Interface.ReadReq.access_kind req)) = false →
  (∀ v : bv (8 * n), gwalk None (k (inl (v, None)))) →
  gwalk None (Interface.Next (Interface.MemRead n req) k).
Proof.
  intros H1 H2 Hk. simpl. destruct (dev_addr (Interface.ReadReq.pa req)); [done|].
  rewrite H1 H2. by split.
Qed.

(** THE EXCLUSIVE READ.  The obligation handed to the continuation is the
    OPEN WINDOW — this is the lemma the three exclusive call sites (lr/sc,
    AMO, [update_and_write_pte]) discharge by exhibiting their conditional
    write. *)
Lemma gwalk_MemRead_excl {E A} n req (k : _ → Defs.monad E A) :
  dev_addr (Interface.ReadReq.pa req) = false →
  ak_coh (classify (Interface.ReadReq.access_kind req)) = false →
  ak_latest (classify (Interface.ReadReq.access_kind req)) = true →
  (∀ v : bv (8 * n),
     gwalk (Some (Interface.ReadReq.pa req, n)) (k (inl (v, None)))) →
  gwalk None (Interface.Next (Interface.MemRead n req) k).
Proof. intros H0 H1 H2 Hk. simpl. rewrite H0 H1 H2. by split. Qed.

(** ANY RAM WRITE with a nonzero width, with the window CLOSED — including a
    STANDALONE CONDITIONAL one, which is what a lone [sc] issues
    ([WeakSailLTS] delta (e''), stage C4's (O4) fix).  Through stage C3 this
    lemma also demanded [ak_latest = false], which is what made
    [∀ b, sail_shaped (riscv_step b)] false. *)
Lemma gwalk_MemWrite_plain {E A} n req (k : _ → Defs.monad E A) :
  (dev_addr (Interface.WriteReq.pa req) = true ∨ n ≠ 0%N) →
  gwalk None (k (inl None)) →
  gwalk None (Interface.Next (Interface.MemWrite n req) k).
Proof.
  intros [Hd|Hn] Hk; simpl.
  - rewrite Hd. by split.
  - destruct (dev_addr (Interface.WriteReq.pa req)); by split.
Qed.

(** THE WINDOW-CLOSING WRITE. *)
Lemma gwalk_MemWrite_close {E A} pa0 n0 n req (k : _ → Defs.monad E A) :
  dev_addr (Interface.WriteReq.pa req) = false →
  Interface.WriteReq.pa req = pa0 → n = n0 → n ≠ 0%N →
  ak_latest (classify (Interface.WriteReq.access_kind req)) = true →
  gwalk None (k (inl None)) →
  gwalk (Some (pa0, n0)) (Interface.Next (Interface.MemWrite n req) k).
Proof. intros. simpl. by split_and!. Qed.

(** (O1), FIXED.  Through stage C1 these two arms quantified over EVERY
    answer, including the ABORT answer [inr ab] that the model answers with
    [exit tt] — so [glive]/[sail_live] were refutable at every memory access
    ([read_ram_not_live], deleted with this change).  They now quantify over
    exactly what [WeakSailLTS.sail_mstep] supplies, and the memory leaves of
    §6b go through. *)
Lemma glive_MemRead {E A} xf n req (k : _ → Defs.monad E A) :
  (∀ v : bv (8 * n), glive xf (k (inl (v, None)))) →
  glive xf (Interface.Next (Interface.MemRead n req) k).
Proof. done. Qed.

Lemma glive_MemWrite {E A} xf n req (k : _ → Defs.monad E A) :
  glive xf (k (inl None)) →
  glive xf (Interface.Next (Interface.MemWrite n req) k).
Proof. done. Qed.

(* ---------------------------------------------------------------------- *)
(** *** 6b. [read_ram] / [write_ram]

    These are the model's two memory leaves.  Note the ARGUMENT-DRIVEN
    shape: the [read_kind] decides plain vs. exclusive, hence which of the
    two lemmas above applies, hence whether the caller owes a conditional
    write. *)

Local Ltac mred :=
  cbn [Defs.bind Defs.bind0 Defs.returnm returnM Interface.iMon_bind].

Lemma gwalk_read_ram_plain {B} addr width meta (k : _ → M B) :
  (∀ r, gwalk None (k r)) →
  gwalk None (Defs.bind (read_ram Read_plain (Physaddr addr) width meta) k).
Proof.
  intros Hk. cbv [read_ram]. mred. cbv [Defs.sail_mem_read]. mred.
  apply gwalk_MemRead_plain; [done|done|].
  intros v; mred; apply Hk.
Qed.

Lemma gwalk_read_ram_excl {B} rk addr width meta (k : _ → M B) :
  rk = Read_RISCV_reserved ∨ rk = Read_RISCV_reserved_acquire →
  dev_addr addr = false →
  (∀ r, gwalk (Some (addr, Z.to_N width)) (k r)) →
  gwalk None (Defs.bind (read_ram rk (Physaddr addr) width meta) k).
Proof.
  intros Hrk Hd Hk. destruct Hrk as [->| ->]; cbv [read_ram]; mred;
    cbv [Defs.sail_mem_read]; mred;
    (apply gwalk_MemRead_excl; [done|done|done|]);
    intros v; mred; apply Hk.
Qed.

(** (O1), FIXED — and this is where it shows.  Through stage C1 the leaf's
    LIVENESS was a REFUTATION ([read_ram_not_live], deleted with this
    change): [sail_live]/[glive]'s memory arms quantified over EVERY answer,
    including the abort [Values.Err tt], which the model answers with
    [exit tt] ([GenericFail]) — so [∀ b, sail_live (riscv_step b)] was FALSE
    at every load.  With the arms narrowed to the answers
    [WeakSailLTS.sail_mstep] supplies ([inl (w, None)]), the leaf is live
    outright, for each of the three read kinds the model can produce (the
    others are [internal_error], hence dead AND not live — the same
    reachability residue as (O3)). *)
Lemma glive_read_ram {B} xf rk addr width meta (k : _ → M B) :
  rk = Read_plain ∨ rk = Read_RISCV_reserved ∨ rk = Read_RISCV_reserved_acquire →
  (∀ r, glive xf (k r)) →
  glive xf (Defs.bind (read_ram rk (Physaddr addr) width meta) k).
Proof.
  intros Hrk Hk. destruct Hrk as [->|[->| ->]]; cbv [read_ram]; mred;
    cbv [Defs.sail_mem_read]; mred; intros v; mred; apply Hk.
Qed.

Lemma to_N_nonzero (w : Z) : (0 < w)%Z → Z.to_N w ≠ 0%N.
Proof. intros Hw Hz. apply (f_equal Z.of_N) in Hz. rewrite Z2N.id in Hz; lia. Qed.

Lemma gwalk_write_ram_plain {B} addr width data meta (k : _ → M B) :
  (0 < width)%Z →
  (∀ r, gwalk None (k r)) →
  gwalk None (Defs.bind (write_ram Write_plain (Physaddr addr) width data meta) k).
Proof.
  intros Hw Hk. cbv [write_ram]. mred. cbv [Defs.sail_mem_write]. mred.
  apply gwalk_MemWrite_plain; [right; by apply to_N_nonzero|].
  mred. apply Hk.
Qed.

(** THE STANDALONE CONDITIONAL WRITE — what [rv64d.execute_STORECON] issues
    with no exclusive read in the same instruction.  Since stage C4 this is
    the POSITIVE lemma at the leaf where C3 recorded a refutation
    ([WeakShapeOverrides] §5, (O4)): the write is walkable with the window
    closed, exactly like a plain one, and the LTS steps it as a plain
    [WeakPromise.LStore] ([WeakSailLTS] delta (e'')). *)
Lemma gwalk_write_ram_con {B} wk addr width data meta (k : _ → M B) :
  wk = Write_RISCV_conditional ∨ wk = Write_RISCV_conditional_release →
  (0 < width)%Z →
  (∀ r, gwalk None (k r)) →
  gwalk None (Defs.bind (write_ram wk (Physaddr addr) width data meta) k).
Proof.
  intros Hwk Hw Hk. destruct Hwk as [->| ->];
    cbv [write_ram]; mred; cbv [Defs.sail_mem_write]; mred;
    (apply gwalk_MemWrite_plain; [right; by apply to_N_nonzero|]);
    mred; apply Hk.
Qed.

(** THE CONDITIONAL WRITE — the window closer. *)
Lemma gwalk_write_ram_close {B} wk addr width data meta pa0 n0 (k : _ → M B) :
  wk = Write_RISCV_conditional ∨ wk = Write_RISCV_conditional_release →
  dev_addr addr = false → addr = pa0 → Z.to_N width = n0 → (0 < width)%Z →
  (∀ r, gwalk None (k r)) →
  gwalk (Some (pa0, n0))
    (Defs.bind (write_ram wk (Physaddr addr) width data meta) k).
Proof.
  intros Hwk Hd -> <- Hw Hk.
  have Hn : Z.to_N width ≠ 0%N by apply to_N_nonzero.
  destruct Hwk as [->| ->]; cbv [write_ram]; mred;
    cbv [Defs.sail_mem_write]; mred;
    (eapply gwalk_MemWrite_close; [done|done|done|done|done|]);
    mred; apply Hk.
Qed.

(* ====================================================================== *)
(** ** 7. CALIBRATION: the semi-automated sweep, measured

    [shape_solve] is the tactic a generated sweep would run.  It is a
    fixpoint over the kit: descend through [bind]/[bind0], split every [if]
    and [match] the generated code branches on, and close the leaves from the
    hint database.  The per-function lemmas below are proved bottom-up in
    dependency order and their wall times are recorded in the file header. *)

Create HintDb shape discriminated.

#[local] Hint Resolve
  gquiet_ret gquiet_returnm gquiet_read_reg gquiet_write_reg
  gquiet_read_reg_ref gquiet_write_reg_ref gquiet_reg_deref
  gquiet_sys_reg_read gquiet_sys_reg_write
  gquiet_instr_announce gquiet_branch_announce
  gquiet_sail_take_exception gquiet_sail_return_exception
  gquiet_sail_cache_op gquiet_sail_tlbi
  gquiet_translation_start gquiet_translation_end
  gquiet_cycle_count gquiet_get_cycle_count gquiet_print_effect
  gquiet_choose_bool gquiet_choose_int gquiet_choose_nat
  gquiet_choose_string gquiet_choose_range gquiet_choose_bitvector
  gquiet_undefined_unit gquiet_undefined_bool gquiet_undefined_int
  gquiet_undefined_nat gquiet_undefined_string gquiet_undefined_range
  gquiet_undefined_bitvector gquiet_undefined_vector
  gquiet_assert_exp gquiet_assert_exp'
  : shape.

Ltac shape_step :=
  match goal with
  | |- gquiet (Defs.bind _ _) => apply gquiet_bind
  | |- gquiet (Defs.bind0 _ _) => apply gquiet_bind0
  | |- gquiet (Defs.try_catch _ _) => apply gquiet_try_catch
  | |- gquiet (Defs.liftR _) => apply gquiet_liftR
  | |- gquiet (Defs.catch_early_return _) => apply gquiet_catch_early_return
  | |- gquiet (Defs.and_boolM _ _) => apply gquiet_and_boolM
  | |- gquiet (Defs.or_boolM _ _) => apply gquiet_or_boolM
  | |- gquiet (Defs.foreachM _ _ _) => apply gquiet_foreachM
  | |- gquiet (Defs.foreach_ZM_up _ _ _ _ _) => apply gquiet_foreach_ZM_up'
  | |- gquiet (if ?b then _ else _) => destruct b
  | |- gquiet (match ?x with _ => _ end) => destruct x
  | |- gok (Defs.bind _ _) => apply gok_bind
  | |- gok (Defs.bind0 _ _) => apply gok_bind0
  | |- gok (if ?b then _ else _) => destruct b
  | |- gok (match ?x with _ => _ end) => destruct x
  | |- gwalk _ (Defs.bind _ _) => apply gwalk_bind
  | |- gwalk _ (if ?b then _ else _) => destruct b
  | |- gwalk _ (match ?x with _ => _ end) => destruct x
  end.

(** [eauto]'s unification does NOT see through [Arch.reg_type] (a
    [Definition] inside the [Arch] module), so the register leaves must be
    applied by name rather than left to the hint database — a small but
    load-bearing detail for a generated sweep. *)
Ltac shape_leaf :=
  first
    [ exact I | assumption
    | apply gquiet_returnm | apply gquiet_ret
    | apply gquiet_read_reg | apply gquiet_write_reg
    | apply gquiet_read_reg_ref | apply gquiet_write_reg_ref
    | apply gquiet_sys_reg_read | apply gquiet_sys_reg_write
    | apply gquiet_instr_announce | apply gquiet_branch_announce
    | apply gquiet_cycle_count | apply gquiet_get_cycle_count
    | apply gquiet_print_effect
    | apply gquiet_sail_take_exception | apply gquiet_sail_return_exception
    | apply gquiet_sail_cache_op | apply gquiet_sail_tlbi
    | apply gquiet_translation_start | apply gquiet_translation_end
    | apply gquiet_choose_bool | apply gquiet_choose_int
    | apply gquiet_choose_nat | apply gquiet_choose_string
    | apply gquiet_choose_range | apply gquiet_choose_bitvector
    | apply gquiet_undefined_unit | apply gquiet_undefined_bool
    | apply gquiet_undefined_int | apply gquiet_undefined_nat
    | apply gquiet_undefined_string | apply gquiet_undefined_range
    | apply gquiet_undefined_bitvector | apply gquiet_undefined_vector
    | apply gquiet_assert_exp | apply gquiet_assert_exp'
    | apply gok_ret | apply gok_returnm
    | apply gwalk_ret
    | eauto with shape nocore ].

Ltac shape_solve :=
  repeat first
    [ progress intros
    | progress cbn [Defs.bind Defs.bind0 Defs.returnm returnM
                    Interface.iMon_bind]
    | solve [shape_leaf]
    | shape_step ].

(* ---------------------------------------------------------------------- *)
(** *** 7a. (a) a register-only leaf and a pure execute clause *)

(** NOTE (a sweep-design finding): the generated code branches on PURE
    CONFIGURATION FUNCTIONS ([get_config_use_abi_names], the
    [encdec_*_matches] predicates).  A blind [destruct] on those lands in the
    model's [exit tt] "pattern match failure" arm, which is shaped but NOT
    live — so the sweep must REDUCE them rather than split them.  That is a
    per-model [cbv] list, and it is the only manual ingredient this proof
    needed. *)
Ltac cfg_red :=
  cbv [get_config_use_abi_names encdec_reg_forwards_matches not].

Lemma gquiet_reg_name_forwards (r : regidx) : gquiet (reg_name_forwards r).
Proof. destruct r. cbv [reg_name_forwards]. cfg_red. cbn. shape_solve. Qed.

Lemma gquiet_xreg_write_callback r v : gquiet (xreg_write_callback r v).
Proof.
  cbv [xreg_write_callback]. apply gquiet_bind;
    [apply gquiet_reg_name_forwards|shape_solve].
Qed.

#[local] Hint Resolve gquiet_reg_name_forwards gquiet_xreg_write_callback : shape.

Lemma gquiet_rX (r : regno) : gquiet (rX r).
Proof. destruct r. cbv [rX]. shape_solve. Qed.

Lemma gquiet_wX (r : regno) v : gquiet (wX r v).
Proof. destruct r. cbv [wX]. shape_solve. Qed.

Lemma gquiet_rX_bits (i : regidx) : gquiet (rX_bits i).
Proof. destruct i. cbv [rX_bits]. apply gquiet_rX. Qed.

Lemma gquiet_wX_bits (i : regidx) v : gquiet (wX_bits i v).
Proof. destruct i. cbv [wX_bits]. apply gquiet_wX. Qed.

#[local] Hint Resolve gquiet_rX gquiet_wX gquiet_rX_bits gquiet_wX_bits : shape.

(** (a) THE PURE EXECUTE CLAUSE.  Quiet, hence shaped AND live. *)
Lemma gquiet_execute_ITYPE imm rs1 rd op : gquiet (execute_ITYPE imm rs1 rd op).
Proof. cbv [execute_ITYPE]. shape_solve. Qed.

Lemma gok_execute_ITYPE imm rs1 rd op : gok (execute_ITYPE imm rs1 rd op).
Proof. apply gok_quiet, gquiet_execute_ITYPE. Qed.

Lemma gquiet_execute_RTYPE rs2 rs1 rd op : gquiet (execute_RTYPE rs2 rs1 rd op).
Proof. cbv [execute_RTYPE]. shape_solve. Qed.

(** The two fence clauses: shaped and live, but NOT quiet (a barrier is a
    log-visible event) — so they go through [gok] directly. *)
Lemma gok_execute_FENCE_TSO u : gok (execute_FENCE_TSO u).
Proof. destruct u. cbv [execute_FENCE_TSO]. by split; intros []. Qed.

Lemma gquiet_execute_UTYPE imm rd op : gquiet (execute_UTYPE imm rd op).
Proof. cbv [execute_UTYPE]. shape_solve. Qed.

(* ---------------------------------------------------------------------- *)
(** *** 7b. (b) the plain load path — the TOP of the chain, and its two
    side conditions

    [execute_LOAD] decomposes by the kit into (i) an ASSERTION whose
    liveness needs a DECODER INVARIANT ([width ≤ xlen_bytes] — true of every
    width the decoder emits, but not of the Coq argument), and (ii) the
    [vmem_read] chain.  Both are recorded as hypotheses: the first is the
    per-instruction side condition a generated sweep must supply from the
    decode side; the second is the rest of the load path
    ([vmem_read → vmem_read_addr → mem_read → … → checked_mem_read →
    read_ram]), whose leaf is §6 and whose middle is blocked on (O1)/(O3).
    Measured: the decomposition itself is instant; it is the 12-deep callee
    chain, not the combinator algebra, that costs. *)
Lemma gok_execute_LOAD imm rs1 rd is_unsigned width :
  Z.leb width xlen_bytes = true →
  gok (vmem_read rs1 (sign_extend' 64 imm) width (Load Data) false false false) →
  gok (execute_LOAD imm rs1 rd is_unsigned width).
Proof.
  intros Hw Hv. cbv [execute_LOAD]. apply gok_bind.
  - rewrite Hw. apply gok_assert_exp'.
  - intros _. apply gok_bind; [exact Hv|]. intros [data|e]; [|apply gok_ret].
    apply gok_bind0; [apply gok_quiet, gquiet_wX_bits|apply gok_ret].
Qed.

(* ---------------------------------------------------------------------- *)
(** *** 7c. (c)/(d) THE EXCLUSIVE SITES — and why they do not close

    The three sites the worklist names ([execute_LOADRES] / [execute_AMO] /
    [update_and_write_pte]) each issue [mem_read … (res := true)], i.e. an
    [ak_latest] read, and each has PATHS ON WHICH NO CONDITIONAL WRITE
    FOLLOWS:

      - [execute_LOADRES]: an lr is a read with NO write at all.
      - [execute_AMO]: the AMOCAS comparison arm ([w__19 = false]) skips the
        write, and every post-read [early_return] (PMP/alignment/translation
        faults raised after [mem_write_ea]) leaves the window open.
      - [update_and_write_pte]: three arms return without writing — the
        [read_pte_exclusive] error arm, the [check_leaf_pte] error arm, and
        [update_PTE_Bits pte access = None].

    Through stage C1 [amo_tail] refuted all of them
    ([amo_tail (Interface.Ret _)] was [False]), so
    [∀ b, sail_shaped (riscv_step b)] was FALSE for this model.  C2 settled
    that in [WeakSailLTS] — the window may be abandoned, and the LTS's bare
    exclusive-read arm steps such a tail — so these sites are now WITHIN the
    specification.  The kit delivers the CLOSING half outright: the pair
    [gwalk_MemRead_excl] (opens the window) / [gwalk_write_ram_close]
    (closes it) with [gwalk_bind_quiet] carrying it across the
    register/trace code in between; and the ABANDONING half at the leaf,
    [gquiet_amo_tail].  What is still missing is neither an arm nor a lemma
    but the sweep-side ESCAPE INDEX of (O2), which is what would let an
    abandoned window travel out through the twelve binds between
    [read_ram] and [execute_LOADRES]. *)

(* ====================================================================== *)
(** ** 8. THE ASSEMBLY-STRATEGY REPORT (stage C, first slice)

    ------------------------------------------------------------------------
    8.1 MEASURED CALIBRATION (this file, [coqc -time], one process)

      whole file (151 lemmas, kit + calibration)        12.6 s
      the kit alone (§§1-6, 143 lemmas)                  2.6 s
      [gquiet_reg_name_forwards]  cfg-reduce + solve     0.03 s
      [gquiet_rX]      (32-way register dispatch)        3.06 s
      [gquiet_wX]      (32-way + callback)               2.50 s
      [gquiet_execute_ITYPE]                             1.04 s
      [gquiet_execute_RTYPE]                             3.03 s
      [gquiet_execute_UTYPE]                             0.39 s
      [gok_execute_LOAD] (decomposition, callees assumed)  0 s

    [Print Assumptions] on the kit: CLOSED UNDER THE GLOBAL CONTEXT for
    every lemma of §§1-6 (including the two memory-leaf lemmas and the
    [read_ram] refutation).  The only axioms that appear anywhere are two
    PRE-EXISTING ones of the generated model ([rv64d.plat_term_write],
    [rv64d.load_reservation], out of the 81 [Axiom]s [rv64d.v] declares),
    and only via [gok_execute_LOAD]'s mention of [vmem_read].

    MANUAL INTERVENTIONS NEEDED, and they are few and systematic:
      (i)   a [cbv] list for the PURE CONFIGURATION functions the generated
            code branches on ([get_config_use_abi_names],
            [encdec_*_matches], …).  A blind [destruct] on those lands in
            the model's [exit tt] "pattern match failure" arm, which is
            shaped but NOT live.  Per-model, written once.
      (ii)  [eauto] does not see through [Arch.reg_type] (a [Definition]
            inside a module), so the register leaves are applied by name in
            [shape_leaf] rather than left to the hint database.
      (iii) per-instruction DECODER INVARIANTS as hypotheses (e.g.
            [width ≤ xlen_bytes] in [execute_LOAD]) — needed for LIVENESS
            only, since a failed [assert_exp'] is shaped but not live.
      Everything else was [shape_solve] with no help.

    The dominant cost is the 32-way register dispatch (≈2.5 s each, and
    [rX]/[wX] are called by nearly every execute clause — but as LEMMAS,
    once).  A per-clause proof is then ~1-3 s.

    ------------------------------------------------------------------------
    8.2 SIZE OF THE JOB.  Call graph of [rv64d.v] from [try_step]
    (identifier-occurrence closure, tools/-style script):

      definitions in rv64d.v                3103
      reachable from [try_step]             1056
      of which MONADIC (need a lemma)        358
      touching memory                          2   ([read_ram], [write_ram])
      using [untilMT]/[whileMT]                4   ([checked_mem_read],
                                                   [checked_mem_write],
                                                   [mem_write_ea], [loop])
      using [catch_early_return]              20
      using [throw] directly                   3
      containing [exit tt]                    47
      containing [internal_error]              48
      containing [reserved_behavior]           9
      containing [choose_real]/[undefined_real] 0   ← the ChooseReal
                                                    exclusion is SATISFIED

    So: ~358 per-function lemmas at ~1-3 s each ≈ 10-20 min of proof time,
    which is affordable; but ~100 of them carry a LIVENESS obligation that
    is NOT shape-structural (see 8.4).

    ------------------------------------------------------------------------
    8.3 IS ONE MONOLITHIC [shape_solve] ON [try_step] FEASIBLE?
    MEASURED (twice, agreeing): a variant of the tactic with a
    head-unfolding step ([uh] = [eval red in m]) run on
    [gwalk None (riscv_step true)] runs **347 s, peak RSS 777 MB**, and then
    STOPS with **one goal left** — it does not fail, which is the trap: such
    a sweep looks like it is working right up to the [Qed].  So the search
    itself is not the wall (the machine handles it) and the wall is a SINGLE
    STUCK LEAF; but the route is still wrong for three reasons: the proof
    term would be the entire 1056-node model inlined (a [Qed] this file
    never had to pay); a stuck leaf gives no localisation — 347 s to learn
    one fact; and every re-run after any model change pays it again.  A
    per-function sweep gets the same coverage in ~10-20 min TOTAL with each
    failure named.  RECOMMENDATION:
    GENERATE the lemmas.  A [tools/gen_shape.py] in the style of
    [tools/gen_code.py] should

      - parse [rv64d.v]'s top-level definitions (the same regex the numbers
        above came from), build the call graph, topologically sort the 358
        monadic nodes reachable from [try_step];
      - emit, for each, either
            Lemma gquiet_<f> <args> : gquiet (<f> <args>).
            Proof. cbv [<f>]. shape_solve. Qed.
        (for the ~330 that touch no memory and no barrier) or a [gok]/[gwalk]
        variant for the rest, and a [#[local] Hint Resolve gquiet_<f> : shape]
        line after each — the hint database IS the dependency mechanism, so
        emitting in topological order is all the ordering that is needed;
      - leave a hand-written OVERRIDE list (the memory wrappers of §6, the
        four loop sites, and the exclusive sites) that the generator skips.

    The generator is worth writing only AFTER 8.4 is settled, because it is
    the shape predicates, not the sweep, that are currently wrong.

    ------------------------------------------------------------------------
    8.4 THE THREE STRUCTURAL OBSTACLES, and what to change

    (O1) FIXED IN C2: the [MemRead]/[MemWrite] arms of [sail_live],
         [sail_shaped], [glive] and [gwalk] quantify over the answers the LTS
         supplies ([inl (w, None)] / [inl None]) rather than over the full
         answer type with its abort branch.  Two lines each; nothing
         downstream weakened, since every consumer instantiated the arm at
         exactly those values already.  [read_ram_not_live] (the refutation)
         is gone; [glive_read_ram] (the leaf) is in its place.

    (O2) SETTLED IN C2, IN [WeakSailLTS].  [amo_tail]'s [Interface.Ret] arm
         is [True] (a window may be ABANDONED, keeping "no read, no barrier,
         and any write closes the window") and [sail_mstep] has the BARE
         exclusive-read arm, which brackets an abandoned window to the
         instruction's end exactly as the fused arm brackets to its
         conditional write.  What remains for the SWEEP is the escape index
         described in (O2) of the header: this kit still walks windows in the
         CLOSED reading, because the weak one refutes [gwalk_bind].

    (O3) [untilMT]/[whileMT] ARE NOT LIVENESS-COMPOSITIONAL: the guard ends
         in [fail "Termination limit reached"].  Four sites, three of them
         on EVERY memory access ([checked_mem_read], [checked_mem_write],
         [mem_write_ea] — the misaligned-split loop).  Each needs a semantic
         invariant ("the [finished] flag is set within [N] iterations"),
         i.e. four hand proofs.  Same family: the ~100 [exit tt] /
         [internal_error] / [reserved_behavior] / [assert_exp] sites, each
         of which needs a reachability argument (usually a computation on
         concrete flags, e.g. [mem_read_priv_meta]'s [throw] arms are the
         flag combination [(aq, rl) = (false, true)] which no [vmem_read]
         call site can produce).  [gwalk] is unaffected by all of these — a
         [GenericFail] continuation is [False → _] — so the SHAPE half of
         stage C is genuinely compositional and the LIVENESS half is not.

    ------------------------------------------------------------------------
    8.5 RECOMMENDED ORDER

      1. DONE (C2): (O1) fixed and (O2) decided, in
         [WeakSailLTS]/[WeakSailComplete].  The remaining sweep-side item is
         the ESCAPE INDEX of (O2) above, without which the abandoning
         exclusive sites cannot be composed through [bind].
      2. Discharge (O3)'s four loop sites and the ~100 unreachable-failure
         sites by hand / by a computation tactic; these are independent of
         1 and can start now.
      3. Then generate the 358 per-function lemmas (8.3) and close
         [riscv_step] with [gok_stageC].
*)
