(* TsoCtx.v -- THE CONTEXT SURFACE, SC-degenerate instance (leg M skeleton).

   The TSO port's ownership interface Sigma
   ([claude-notes/projects/tso-port.md], legs M and C): every memory
   points-to fact is indexed by a CONTEXT -- a ghost identity for a thread
   of control -- and the ONLY ways a fact changes context are the exported
   transport laws.  Under today's SC semantics the index is inert (the
   definitions below ignore it, UNDER THE SEAL); under the TSO
   instantiation the context carries the view ledger tying the thread's
   facts to what its current hart has observed ([iris/TsoMem.v], and the
   `weak-memory` branch's `WeakCtx.v`/`WeakCtxPt.v` -- the validated
   design this file is the degenerate image of).

   THE THREE RULINGS THIS FILE ENCODES (owner-ratified):

   1. [CurCtx] IS AMBIENT, LIKE [CpuId] AND [CurKtier]: a file binds its
      context once ([Context `{XI : CurCtx}]) and its spec text does not
      change.  There is deliberately NO default instance -- a global
      default context would be one ghost shared by every thread, and
      [own_context] is exclusive.  ([CpuId] is the precedent: ambient,
      no default, swept through every WP statement once --
      [claude-notes/completed/explicit-cpuid.md].)

   2. THE CONTEXT RIDES IN [sie_cap_gpr] (owner's simplification): the
      ambient kernel-execution bundle gains an [own_context cur_ctx]
      conjunct (the M2 sweep edits [IntrDefs.v] in place), so no proof
      threads a NEW separation-logic resource -- the bundle already moves
      everywhere the context info is needed, and [wp_next]'s continuation
      re-anchors [CpuId] while cur_ctx STAYS, which is the whole point:
      the thread's points-to facts do not change proposition at a
      migration.  [own_context] is what ties the context to the current
      CPU's view state; at SC that tie is vacuous and the token is a
      plain exclusive ghost.

   3. NO CONTEXT-IRRELEVANCE ESCAPES: [ctx_pointsto xi = mem_pointsto]
      holds definitionally HERE, but no exported law states it -- a
      lemma of the shape [ctx_pointsto xi ⊣⊢ ctx_pointsto xi'] would be
      false under TSO and must never exist above the seal.  The one-time
      conversion shim for the M1 sweep lives in [TsoCtxShim.v] (a
      separate file, deleted at cutover), never here.

   The ghost is a [ghost_var] over [CPU] through the tree's existing
   [riscv_parkGS] functor, so this file adds NOTHING to [riscvGS] and
   touches no adequacy wiring.  The TSO twin will replace the ghost with
   the view ledger; the exported statements below are the contract both
   instances satisfy, and the tso-branch mirror recompile is what keeps
   this file honest (tso-port.md, T4). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.Base SailStdpp.Values.
Require Import Riscv.rv64d_types.
Require Import RiscvLang RiscvPtsto Ktier.

(* ------------------------------------------------------------------ *)
(* The context identity and the ambient class                          *)
(* ------------------------------------------------------------------ *)

Record CtxId := MkCtxId { ctx_name : gname }.
Add Printing Constructor CtxId.

Global Instance ctx_id_eq_dec : EqDecision CtxId.
Proof. solve_decision. Defined.
Global Instance ctx_id_countable : Countable CtxId.
Proof. apply (inj_countable' ctx_name MkCtxId). by intros []. Qed.

(* Ambient, and -- unlike [CurKtier] -- WITHOUT a default instance; see
   ruling 1 above. *)
Class CurCtx := cur_ctx : CtxId.

Section ctx.
  Context `{!riscvGS Σ}.

  (* ---------------------------------------------------------------- *)
  (* own_context: the running-thread token                             *)
  (* ---------------------------------------------------------------- *)

  (* At SC: an exclusive token, nothing more.  At TSO: the context's view
     authority paired with the running hart's view (the tie that makes a
     load rule at [cur_ctx] sound on the hart it happens on).  It lives
     inside [sie_cap_gpr] (ruling 2) and is minted once per thread of
     control (boot per hart; forkret for a parked child). *)
  Definition own_context (ξ : CtxId) : iProp Σ :=
    (∃ c : CPU, ghost_var (ctx_name ξ) 1 c)%I.

  Lemma own_context_alloc : ⊢ |==> ∃ ξ : CtxId, own_context ξ.
  Proof.
    iMod (ghost_var_alloc (0%fin : CPU)) as (γ) "Hv".
    iModIntro. iExists (MkCtxId γ), (0%fin : CPU). simpl. iExact "Hv".
  Qed.

  Lemma own_context_excl (ξ : CtxId) :
    own_context ξ -∗ own_context ξ -∗ False.
  Proof.
    iIntros "[%c1 H1] [%c2 H2]".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
    exfalso. by apply (Qp.not_add_le_l 1 1).
  Qed.

  Global Instance own_context_timeless ξ : Timeless (own_context ξ).
  Proof. rewrite /own_context. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (* The context-indexed points-to                                     *)
  (* ---------------------------------------------------------------- *)

  (* [ctx_pointsto ξ a dq v]: the byte fact, registered to context ξ.
     SC: the index is phantom.  TSO: [∃ t, lattice cell at t ∗ ξ's ledger
     covers t] -- the `weak-memory` branch's [wptsto_cl], with the ledger
     being what survives a change of hart.  The M1 sweep points the
     [↦ₘ]-notation tower here at [cur_ctx]; until then the tree's
     spellings are untouched. *)
  Definition ctx_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    mem_pointsto (KTR := KTR) va dq v.

  (* The law surface, mirroring [mem_pointsto]'s (RiscvPtsto.v).  Each is
     proved by unfolding HERE and must hold of the TSO twin; a law that
     could not is a law that must not be added. *)

  Global Instance ctx_pointsto_timeless (KTR : CurKtier) ξ a dq v :
    Timeless (ctx_pointsto (KTR := KTR) ξ a dq v).
  Proof. rewrite /ctx_pointsto. apply _. Qed.

  Global Instance ctx_pointsto_discarded_persistent (KTR : CurKtier) ξ a v :
    Persistent (ctx_pointsto (KTR := KTR) ξ a DfracDiscarded v).
  Proof. rewrite /ctx_pointsto. apply _. Qed.

  (* agreement is CROSS-context (two registered facts about one byte name
     one lattice cell): sound at TSO, and the form invariants need. *)
  Lemma ctx_pointsto_agree {kt1 kt2 : ktier} ξ1 ξ2 a dq1 b1 dq2 b2 :
    ctx_pointsto (KTR := kt1) ξ1 a dq1 b1 -∗
    ctx_pointsto (KTR := kt2) ξ2 a dq2 b2 -∗ ⌜b1 = b2⌝.
  Proof. rewrite /ctx_pointsto. apply mem_pointsto_agree. Qed.

  Lemma ctx_pointsto_ne {kt1 kt2 : ktier} ξ1 ξ2 a1 a2 dq b1 b2 :
    ctx_pointsto (KTR := kt1) ξ1 a1 (DfracOwn 1) b1 -∗
    ctx_pointsto (KTR := kt2) ξ2 a2 dq b2 -∗ ⌜a1 ≠ a2⌝.
  Proof. rewrite /ctx_pointsto. apply mem_pointsto_ne. Qed.

  Lemma ctx_pointsto_frac_split `{KTR : !CurKtier} ξ a q1 q2 b :
    ctx_pointsto ξ a (DfracOwn (q1 + q2)) b ⊣⊢
    ctx_pointsto ξ a (DfracOwn q1) b ∗ ctx_pointsto ξ a (DfracOwn q2) b.
  Proof. rewrite /ctx_pointsto. apply mem_pointsto_frac_split. Qed.

  Lemma ctx_pointsto_persist `{KTR : !CurKtier} ξ a dq b :
    ctx_pointsto ξ a dq b ==∗ ctx_pointsto ξ a DfracDiscarded b.
  Proof. rewrite /ctx_pointsto. apply mem_pointsto_persist. Qed.

  (* ---------------------------------------------------------------- *)
  (* Transport: the ONLY ways a fact changes context                   *)
  (* ---------------------------------------------------------------- *)

  (* [ctx_dom ξ ξ']: ξ's facts may be re-registered to ξ'.  At TSO this
     is ledger domination (ξ''s ledger is raised past ξ's at the transfer
     point) and it is minted ONLY inside the lock release/acquire and
     scheduler park/resume proofs -- which are below Sigma and get it from
     the machine's release/acquire evidence.  It is deliberately NOT
     persistent there (a persistent domination would license registering
     later facts -- the unsound step the `weak-memory` branch's notes call
     out), so nothing here may mark it persistent either. *)
  Definition ctx_dom (ξ ξ' : CtxId) : iProp Σ := True%I.

  (* A context-indexed payload that transports along domination.  This is
     the obligation lock payloads pick up in the M3 sweep: any payload
     failing it at SC is a payload the TSO flip would break -- found
     early, which is the point of the sweeps. *)
  Class CtxMorph (R : CtxId → iProp Σ) :=
    ctx_morph : ∀ ξ ξ', ctx_dom ξ ξ' -∗ R ξ ==∗ ctx_dom ξ ξ' ∗ R ξ'.

  (* The structural instances.  NOTE what is absent: no instance for
     [own_context] (the running-thread token never transfers by
     domination), and no blanket instance for persistent-but-ξ-dependent
     propositions (the TSO ledger lower bound is persistent AND pinned to
     its context).  ξ-CONSTANT propositions -- pure facts, ghost state,
     invariant handles, whole lock handles -- are covered by
     [ctx_morph_const]. *)

  Global Instance ctx_morph_const (P : iProp Σ) : CtxMorph (λ _, P).
  Proof. iIntros (ξ ξ') "Hd HP !>". iFrame. Qed.

  Global Instance ctx_morph_pointsto (kt : ktier) a dq v :
    CtxMorph (λ ξ, ctx_pointsto (KTR := kt) ξ a dq v).
  Proof. iIntros (ξ ξ') "Hd HP !>". rewrite /ctx_pointsto. iFrame. Qed.

  Global Instance ctx_morph_sep (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, R1 ξ ∗ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ ξ') "Hd [HR1 HR2]".
    iMod (ctx_morph with "Hd HR1") as "[Hd HR1]".
    iMod (ctx_morph with "Hd HR2") as "[Hd HR2]".
    iModIntro. iFrame.
  Qed.

  Global Instance ctx_morph_exist {A} (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMorph (Φ x)) → CtxMorph (λ ξ, ∃ x, Φ x ξ)%I.
  Proof.
    iIntros (HΦ ξ ξ') "Hd [%x HR]".
    iMod (ctx_morph with "Hd HR") as "[Hd HR]".
    iModIntro. iFrame "Hd". iExists x. iExact "HR".
  Qed.

  Global Instance ctx_morph_big_sepL {A} (l : list A)
      (Φ : nat → A → CtxId → iProp Σ) :
    (∀ i x, CtxMorph (Φ i x)) →
    CtxMorph (λ ξ, [∗ list] i ↦ x ∈ l, Φ i x ξ)%I.
  Proof.
    revert Φ. induction l as [|x l IH] => Φ HΦ.
    - iIntros (ξ ξ') "Hd _ !>". by iFrame.
    - iIntros (ξ ξ') "Hd [HR HRs]".
      iMod (ctx_morph with "Hd HR") as "[Hd HR]".
      iMod (IH (λ i y, Φ (S i) y) _ ξ ξ' with "Hd HRs") as "[Hd HRs]".
      iModIntro. iFrame.
  Qed.

  (* The composition acid test: a lock-payload-shaped assertion is
     morphable by typeclass search alone.  If this ever needs a manual
     proof, an instance regressed. *)
  Lemma ctx_morph_demo (kt : ktier) a1 a2 v1 (P : iProp Σ) :
    CtxMorph (λ ξ, ctx_pointsto (KTR := kt) ξ a1 (DfracOwn 1) v1 ∗
                   (∃ v2 : bv 8, ⌜v2 ≠ v1⌝ ∗
                      ctx_pointsto (KTR := kt) ξ a2 (DfracOwn 1) v2) ∗
                   P)%I.
  Proof. apply _. Qed.

End ctx.

(* The notation family, mirroring [mem_pointsto]'s ([RiscvPtsto.v]) with
   [↦c] in place of [↦ₘ]: the context index is AMBIENT ([cur_ctx], like
   the tier), so converted spec text reads as before --
   [a ↦c[ktb] v], [a ↦c v], [a ↦c{dq} v], [a ↦c□ v].  A statement that
   needs an EXPLICIT context (lock internals, the shim) spells
   [ctx_pointsto] directly.  At the M1 notation flip these become the
   [↦ₘ] spellings and [↦c] is retired.  The tier-bracket form goes
   through Iris's custom [dfrac] entry for the same lexer reason as
   [↦ₘ[kt]]'s (see the note there: a fused "]{" token would break
   ghost_map's [↪[γ]] tree-wide). *)
Notation "a ↦c{ dq } v" := (ctx_pointsto cur_ctx a dq v)
  (at level 20, format "a  ↦c{ dq }  v") : bi_scope.
Notation "a ↦c□ v" := (ctx_pointsto cur_ctx a DfracDiscarded v)
  (at level 20, format "a  ↦c□  v") : bi_scope.
Notation "a ↦c v" := (ctx_pointsto cur_ctx a (DfracOwn 1) v)
  (at level 20, format "a  ↦c  v") : bi_scope.
Notation "a ↦c[ kt ] dq v" := (ctx_pointsto (KTR := kt) cur_ctx a dq v)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦c[ kt ] dq  v") : bi_scope.

(* The seal.  [ctx_dom] stays opaque too: nothing above this file may
   learn it is [True] at SC. *)
Global Typeclasses Opaque own_context ctx_pointsto ctx_dom.
Global Opaque own_context ctx_pointsto ctx_dom.
