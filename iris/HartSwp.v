(* HartSwp.v -- THE MONADIC WP LAYER, [swp]: the interface leaves compose in.

   Design: claude-notes/design/main-cycle-port.md §5 item 6.  Sail code is
   written with [bind]; the proof interface should decompose along THAT
   structure and let the value a continuation receives appear in a
   postcondition.  [swp] is DERIVED from the real WP -- no language change --
   so it inherits adequacy, laters and masks with no second soundness
   argument.

   THE CONTEXT-GENERIC FORM (a correction to the design doc's CPS shape,
   which quantified only over [K : X -> M unit] and concluded at
   [WP (HartE (bind m K))]).  Three things go wrong with the bind-only form,
   and one definition fixes all three:

     - ASSOCIATIVITY.  [swp_bind] against a bind-only [swp] needs
       [bind (bind m f) K = bind m (fun x => bind (f x) K)], an equation
       between monad terms whose [Next] case is provable only with
       [functional_extensionality_dep].  With contexts, "re-associating" is
       composing two context functions, which is [reflexivity].

     - THE EARLY-RETURN REGION.  [run_hart_active] -- which is where the
       fetch, the decode and the execute live -- is
       [catch_early_return (... liftR sub >>= K ...)], at [MR Step], not at
       [M].  A bind-only [swp] fact about [fetch] cannot be applied there
       without pushing [catch_early_return] inward, and that push-through is
       FALSE on the nose: at an [ExtraOutcome] node [try_catch] DISCARDS the
       continuation while [bind] re-attaches one, so the two sides differ
       (harmlessly -- under a node the machine cannot step -- but they are
       not equal, and no amount of throw-freeness fixes it, since the
       equation is about syntax and the model's [throw]s sit in unreached
       branches of [execute]).  As a CONTEXT, [fun h => catch_early_return
       (bind (liftR h) K)] is admissible, and the [ExtraOutcome] node is
       simply outside what [mctx] demands.

     - THE STUCK CLASSES.  [GenericFail]/[Discard]/[Choose] need no mirroring
       either: the machine cannot step them, so a proof never reaches one.

   Hence [mctx]: a context is a function that COMMUTES WITH THE HEAD NODE at
   every node the machine can actually step.  Everything downstream --
   [swp_bind] included -- is then definitional.

   THE LAYERING (design doc §5, unchanged): wp_hart_step (per node) ->
   span / batch (multi-node, where the expensive proofs live, once per
   stretch) -> [swp] (bridge lemmas export each stretch as one [swp] fact)
   -> leaves (compose by [swp_bind] along the model's own structure).
   UNFOLDING [swp] TO PER-NODE STEPS AT A LEAF IS THE ONE THING THIS FILE
   EXISTS TO PREVENT: it re-incurs the ~1 ms/node cost the batching exists
   to avoid. *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec.
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. MONADIC CONTEXTS (pure).                                             *)
(* ====================================================================== *)

(* The nodes a context must mirror.  [ExtraOutcome] is the only class a
   context former in this tree actually treats differently
   ([try_catch] handles it and passes everything else through), so the
   condition is stated against it rather than against the full stuck set --
   that makes [mctx] as weak as possible while still being provable by
   [reflexivity] for every former below. *)
Definition is_extra {T : Type} (oc : Interface.outcome (fun _ => exception) T)
    : bool :=
  match oc with
  | Interface.ExtraOutcome _ => true
  | _ => false
  end.

(* A CONTEXT: a function from a sub-monad to a whole hart expression's monad
   that commutes with the head node.  Note what is NOT required: nothing at
   all about [C (Ret x)] -- that is the continuation, and it is exactly what
   [swp]'s postcondition hands back. *)
Definition mctx {X : Type} (C : M X -> M unit) : Prop :=
  forall (T : Type) (oc : Interface.outcome (fun _ => exception) T)
         (k : T -> M X),
    is_extra oc = false ->
    C (Interface.Next oc k) = Interface.Next oc (fun v => C (k v)).

(* the identity context: a sub-monad at [M unit] IS a hart expression *)
Lemma mctx_id : mctx (fun m : M unit => m).
Proof. intros T oc k _. reflexivity. Qed.

(* the bind context, [_ >>= f] -- the one the design doc's [swp] baked in *)
Lemma mctx_bind {X Y : Type} (f : X -> M Y) (C : M Y -> M unit) :
  mctx C -> mctx (fun m : M X => C (Defs.bind m f)).
Proof. intros HC T oc k Hx. rewrite /Defs.bind /=. by apply HC. Qed.

(* contexts compose (the general form of [mctx_bind]) *)
Lemma mctx_comp {X Y : Type} (F : M X -> M Y) (C : M Y -> M unit) :
  mctx C ->
  (forall T (oc : Interface.outcome (fun _ => exception) T) (k : T -> M X),
     is_extra oc = false ->
     F (Interface.Next oc k) = Interface.Next oc (fun v => F (k v))) ->
  mctx (fun m : M X => C (F m)).
Proof. intros HC HF T oc k Hx. rewrite (HF _ oc k Hx). by apply HC. Qed.

(* THE EARLY-RETURN CONTEXT: a plain-[M] sub-monad lifted into an
   early-return region and bound to a continuation there -- which is how
   [run_hart_active] presents the fetch, the decode and the execute.

   Stated for the COMPOSITE, not for [liftR] and [catch_early_return]
   separately, and that is forced rather than stylistic: each half alone
   CHANGES THE OUTCOME'S ERROR FAMILY ([exception] vs [R + exception]), so
   "[C] mirrors the head node" does not even typecheck for it.  Round trip,
   the family comes back, and every non-[ExtraOutcome] node is the same
   constructor on both sides -- so the whole thing is [destruct oc;
   reflexivity], one line, and no cast machinery is needed anywhere. *)
Lemma mctx_cer_liftR {X R : Type} (K : X -> MR R R) (C : M R -> M unit) :
  mctx C ->
  mctx (fun m : M X =>
          C (Defs.catch_early_return (Defs.bind (Defs.liftR (R := R) m) K))).
Proof.
  intros HC T oc k Hx.
  assert (Heq :
    Defs.catch_early_return
      (Defs.bind (Defs.liftR (R := R) (Interface.Next oc k)) K)
    = Interface.Next oc
        (fun v => Defs.catch_early_return
                    (Defs.bind (Defs.liftR (R := R) (k v)) K))).
  { destruct oc; try discriminate Hx; reflexivity. }
  rewrite Heq. by apply HC.
Qed.

(* ====================================================================== *)
(* 2. [swp].                                                               *)
(* ====================================================================== *)

Section swp.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition swp {X : Type} (m : M X) (Φ : X -> iProp Σ) : iProp Σ :=
    (∀ C : M X -> M unit,
       ⌜mctx C⌝ -∗
       (∀ v : X, Φ v -∗ WP (HartE gen_id cpu_id (C (Interface.Ret v))
                            : expr riscv_lang)) -∗
       WP (HartE gen_id cpu_id (C m) : expr riscv_lang))%I.

  Global Instance swp_ne {X} (m : M X) n :
    Proper (pointwise_relation X (dist n) ==> dist n) (swp m).
  Proof. rewrite /swp. solve_proper. Qed.
  Global Instance swp_proper {X} (m : M X) :
    Proper (pointwise_relation X (≡) ==> (≡)) (swp m).
  Proof. rewrite /swp. solve_proper. Qed.

  (* ---- the laws ---- *)

  (* left unit: definitional, since [C (Ret x)] is literally the goal *)
  Lemma swp_ret {X} (x : X) (Φ : X -> iProp Σ) : Φ x -∗ swp (Interface.Ret x) Φ.
  Proof. iIntros "HΦ" (C) "_ H". by iApply "H". Qed.

  (* THE ELIMINATION FORM.  Every consumer goes through this rather than
     through [swp]'s ∀ directly, so no proof outside this file has to know
     that [swp] is a CPS definition at all. *)
  Lemma swp_use {X} (m : M X) (Φ : X -> iProp Σ) (C : M X -> M unit) :
    mctx C ->
    swp m Φ -∗
    (∀ v : X, Φ v -∗ WP (HartE gen_id cpu_id (C (Interface.Ret v))
                         : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id (C m) : expr riscv_lang).
  Proof. iIntros (HC) "Hswp H". by iApply ("Hswp" $! C with "[%//]"). Qed.

  Lemma swp_mono {X} (m : M X) (Φ Ψ : X -> iProp Σ) :
    (∀ v, Φ v -∗ Ψ v) -∗ swp m Φ -∗ swp m Ψ.
  Proof.
    iIntros "HΦΨ Hswp" (C) "%HC H". iApply ("Hswp" $! C with "[%//] [-]").
    iIntros (v) "HΦ". iApply "H". by iApply "HΦΨ".
  Qed.

  Lemma swp_frame_l {X} (m : M X) (Φ : X -> iProp Σ) (R : iProp Σ) :
    R -∗ swp m Φ -∗ swp m (fun v => R ∗ Φ v).
  Proof.
    iIntros "HR Hswp". iApply (swp_mono with "[HR] Hswp").
    iIntros (v) "HΦ". iFrame.
  Qed.

  (* THE BIND LAW -- the reason the file exists.  No associativity equation:
     [bind]'s context is [C o (_ >>= f)], and at the point [m] returns [v]
     the goal is [C (bind (Ret v) f)], which IS [C (f v)]. *)
  Lemma swp_bind {X Y} (m : M X) (f : X -> M Y) (Φ : Y -> iProp Σ) :
    swp m (fun v => swp (f v) Φ) -∗ swp (Defs.bind m f) Φ.
  Proof.
    iIntros "Hswp" (C) "%HC H".
    iApply ("Hswp" $! (fun m' => C (Defs.bind m' f))
              with "[%] [H]"); [by apply mctx_bind|].
    iIntros (v) "Hinner". iApply ("Hinner" $! C with "[%//] H").
  Qed.

  (* the [>>] form, so a call site need not unfold [bind0] *)
  Lemma swp_bind0 {Y} (m : M unit) (n : M Y) (Φ : Y -> iProp Σ) :
    swp m (fun _ => swp n Φ) -∗ swp (Defs.bind0 m n) Φ.
  Proof. rewrite /Defs.bind0. iApply swp_bind. Qed.

  (* RIGHT UNIT / the close into a real WP.  [LoopE] IS [HartE _ _ (Ret tt)],
     so the boundary side is definitional: a whole cycle's [swp] whose
     postcondition is the next boundary's WP is the leaf statement. *)
  Lemma swp_wp (m : M unit) (Φ : unit -> iProp Σ) :
    swp m Φ -∗
    (∀ v : unit, Φ v -∗ WP (Loop : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof.
    iIntros "Hswp H".
    iApply ("Hswp" $! (fun m' : M unit => m') with "[%] [H]");
      [exact mctx_id|].
    iIntros (v) "HΦ". rewrite /LoopE. destruct v. by iApply "H".
  Qed.

  (* the same, specialised to the shape every leaf ends in *)
  Lemma swp_wp_loop (m : M unit) :
    swp m (fun _ => WP (Loop : expr riscv_lang)) -∗
    WP (HartE gen_id cpu_id m : expr riscv_lang).
  Proof. iIntros "Hswp". iApply (swp_wp with "Hswp"). by iIntros (v) "H". Qed.

  (* ---- modalities: [swp] is closed under everything WP is ---- *)

  Lemma swp_fupd {X} (m : M X) (Φ : X -> iProp Σ) :
    (|={⊤}=> swp m Φ) -∗ swp m Φ.
  Proof.
    iIntros "Hswp" (C) "%HC H". iApply fupd_wp. iMod "Hswp".
    iModIntro. by iApply ("Hswp" $! C with "[%//]").
  Qed.

  Lemma swp_fupd_post {X} (m : M X) (Φ : X -> iProp Σ) :
    swp m (fun v => |={⊤}=> Φ v) -∗ swp m Φ.
  Proof.
    iIntros "Hswp" (C) "%HC H". iApply ("Hswp" $! C with "[%//] [H]").
    iIntros (v) "HΦ". iApply fupd_wp. iMod "HΦ". iModIntro. by iApply "H".
  Qed.

  (* [swp] IS PERSISTENTLY USABLE UNDER A CONTEXT: the definition is a ∀ of
     wands, so the usual [iApply] discipline applies with no extra lemma. *)

End swp.

Global Arguments swp {Σ _ _ _ X} m Φ.

(* the notation leaves read in: the value binder is the point of the layer *)
Notation "'SWP' m {{ v , Q } }" := (swp m (fun v => Q))
  (at level 20, m at level 200, v pattern, Q at level 200,
   format "'[hv' 'SWP'  m  '/' {{  '[' v ,  '/' Q  ']' } } ']'").
Notation "'SWP' m {{ Q } }" := (swp m Q)
  (at level 20, m at level 200, Q at level 200,
   format "'[hv' 'SWP'  m  '/' {{  '[' Q  ']' } } ']'").
