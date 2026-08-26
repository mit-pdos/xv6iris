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

   THE CONSTRUCTION THIS SURFACE IS THE DEGENERATE IMAGE OF is the
   corrected one, validated end to end in [TsoCtxTwin2.v] (which
   supersedes [TsoCtxTwin.v]'s global-map prototype): per-context state
   is ONE MONOTONE NAT (the context's bound), the clean/dirty bit rides
   inside [ctx_pointsto], and the authorities travel WITH THE TOKENS --
   which is what makes [CtxMorph]'s bare shape below true as written,
   the parked mint pure, and park/resume/exchange/deposit interp-free.
   Every law exported here has a proven twin image; the twin lemma is
   named beside each.

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
Require Import Riscv.rv64d_types Riscv.rv64d.   (* [is_aligned_paddr]/[Physaddr]: the word tower's alignment vocabulary *)
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.

(* ------------------------------------------------------------------ *)
(* The context identity and the ambient class                          *)
(* ------------------------------------------------------------------ *)

(* TWO GNAMES, BOTH THE CONTEXT'S OWN ([TsoCtxTwin2.CtxId] is the same
   record): the BOUND authority (the one monotone nat) and the DIRTY-SET
   authority.  The identity carrying its own ghost names is what lets a
   token -- and hence every authority -- be minted wherever the identity
   can, with no global roster: the corrected construction's cornerstone.
   At SC only the bound name is used (a plain exclusive ghost_var). *)
Record CtxId := MkCtxId { ctx_bound_name : gname; ctx_dirty_name : gname }.
Add Printing Constructor CtxId.

Global Instance ctx_id_eq_dec : EqDecision CtxId.
Proof. solve_decision. Defined.
(* INHABITED IS LOAD-BEARING, not decoration: a [CtxId] existentially bound
   inside a ▷-guarded record (the parked context, SwtchCtx.valid_context_pre)
   can only have its later pushed inward by [bi.later_exist], which HOLDS
   ONLY OVER AN INHABITED DOMAIN.  Without this instance the resumer cannot
   open the record it is about to run. *)
Global Instance ctx_id_inhabited : Inhabited CtxId :=
  populate (MkCtxId inhabitant inhabitant).

Global Instance ctx_id_countable : Countable CtxId.
Proof.
  apply (inj_countable' (λ ξ, (ctx_bound_name ξ, ctx_dirty_name ξ))
           (λ p, MkCtxId p.1 p.2)).
  by intros [].
Qed.

(* Ambient, and -- unlike [CurKtier] -- WITHOUT a default instance; see
   ruling 1 above. *)
Class CurCtx := cur_ctx : CtxId.

Section ctx.
  Context `{!riscvGS Σ}.

  (* ---------------------------------------------------------------- *)
  (* own_context: the running-thread token                             *)
  (* ---------------------------------------------------------------- *)

  (* THE RUNNING TOKEN: "this hart is running as ξ".  At SC: an exclusive
     token, nothing more.  At TSO ([TsoCtxTwin2.own_context]): BOTH of ξ's
     authorities (its bound and its dirty set) plus the stable receipt
     tying the bound to THIS hart's view -- which is why the token carries
     the ambient [CpuId]: the tie is to the hart the thread runs on, and
     re-hosting it is [ctx_resume]/[ctx_exchange], never a frame.  It
     lives inside [sie_cap_gpr] (ruling 2) and is born at boot
     ([own_context_boot], one per hart), exchanged at swtch, and dropped
     at a zombie park. *)
  (* CUTOVER REHEARSAL (2026-08-26): the five surface facts are sealed
     HERMETICALLY -- Qed-opaque via the sig-projection idiom -- so that
     NOTHING can convert them to their SC bodies except the named
     [_unseal] equations (used by this file's law proofs and by
     TsoCtxShim).  Under the ordinary [Global Opaque] seal, unification
     falls back to delta as a last resort, and the tree grew SILENT
     ctx/mem crossings that no grep can list; every such crossing is now
     a compile error, which is exactly the failure set the real
     TsoCtxTwin2 swap would produce at the statement level.  Revert this
     block (plain definitions again) to go back to the permeable SC
     seal. *)
  Definition own_context_def `{CID : CpuId} (ξ : CtxId) : iProp Σ :=
    (∃ c : CPU, ghost_var (ctx_bound_name ξ) 1 c)%I.
  Lemma own_context_aux : { f | f = @own_context_def }.
  Proof. by eexists. Qed.
  Definition own_context `{CID : CpuId} (ξ : CtxId) : iProp Σ :=
    proj1_sig own_context_aux CID ξ.
  Lemma own_context_unseal `{CID : CpuId} (ξ : CtxId) :
    own_context ξ = own_context_def ξ.
  Proof. unfold own_context. by rewrite (proj2_sig own_context_aux). Qed.

  (* THE PARKED TOKEN: a thread of control not running anywhere -- ξ's
     authorities with no hart tie, stamped at [T] (at TSO: the bound the
     resumer's view must dominate; here phantom).  It is what a swtch
     record and a fresh fork child hold ([SwtchCtx.valid_context_pre],
     [ProofForkretPark]).  Deliberately NOT hart-ambient: a parked record
     is migratable, and this token is why that is type-correct. *)
  Definition ctx_parked_def (ξ : CtxId) (T : nat) : iProp Σ :=
    (∃ c : CPU, ghost_var (ctx_bound_name ξ) 1 c)%I.
  Lemma ctx_parked_aux : { f | f = ctx_parked_def }.
  Proof. by eexists. Qed.
  Definition ctx_parked (ξ : CtxId) (T : nat) : iProp Σ :=
    proj1_sig ctx_parked_aux ξ T.
  Lemma ctx_parked_unseal (ξ : CtxId) (T : nat) :
    ctx_parked ξ T = ctx_parked_def ξ T.
  Proof. unfold ctx_parked. by rewrite (proj2_sig ctx_parked_aux). Qed.

  (* THE STABLE HART-VIEW LOWER BOUND (tso-port checkpoint 0.4 item 3;
     [TsoCtxTwin2.view_lb]): "this hart's view has passed K".  Persistent
     and monotone -- the honest, never-falsified form of the resume
     premise "the hart is at least as fresh as the parked stamp".  Minted
     below the seam (the AMO-acquire leaf, [TsoCtxTwin2.twin_passed_get]);
     at SC it is trivial and the shim provides it, which is the licensed
     stopgap until the M2 sweep threads it out of [SpecAcquire]. *)
  Definition hart_view_lb_def `{CID : CpuId} (K : nat) : iProp Σ := True%I.
  Lemma hart_view_lb_aux : { f | f = @hart_view_lb_def }.
  Proof. by eexists. Qed.
  Definition hart_view_lb `{CID : CpuId} (K : nat) : iProp Σ :=
    proj1_sig hart_view_lb_aux CID K.
  Lemma hart_view_lb_unseal `{CID : CpuId} (K : nat) :
    hart_view_lb K = hart_view_lb_def K.
  Proof. unfold hart_view_lb. by rewrite (proj2_sig hart_view_lb_aux). Qed.

  Global Instance hart_view_lb_persistent `{CID : CpuId} K :
    Persistent (hart_view_lb K).
  Proof. rewrite hart_view_lb_unseal /hart_view_lb_def. apply _. Qed.
  Global Instance hart_view_lb_timeless `{CID : CpuId} K :
    Timeless (hart_view_lb K).
  Proof. rewrite hart_view_lb_unseal /hart_view_lb_def. apply _. Qed.

  Lemma hart_view_lb_le `{CID : CpuId} (K K' : nat) :
    (K' ≤ K)%nat → hart_view_lb K -∗ hart_view_lb K'.
  Proof. rewrite !hart_view_lb_unseal /hart_view_lb_def. auto. Qed.

  (* Exclusivity, in all three pairings: one bound authority per context,
     one token.  ([TsoCtxTwin2.own_context_excl] / [ctx_parked_excl] /
     [own_context_parked_excl]; the running form holds across DIFFERENT
     ambient harts too, which is the statement here.) *)
  Lemma own_context_excl {CID1 CID2 : CpuId} (ξ : CtxId) :
    own_context (CID := CID1) ξ -∗ own_context (CID := CID2) ξ -∗ False.
  Proof.
    rewrite !own_context_unseal /own_context_def.
    iIntros "[%c1 H1] [%c2 H2]".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
    exfalso. by apply (Qp.not_add_le_l 1 1).
  Qed.

  Lemma ctx_parked_excl (ξ : CtxId) (T1 T2 : nat) :
    ctx_parked ξ T1 -∗ ctx_parked ξ T2 -∗ False.
  Proof.
    rewrite !ctx_parked_unseal /ctx_parked_def.
    iIntros "[%c1 H1] [%c2 H2]".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
    exfalso. by apply (Qp.not_add_le_l 1 1).
  Qed.

  Lemma own_context_parked_excl `{CID : CpuId} (ξ : CtxId) (T : nat) :
    own_context ξ -∗ ctx_parked ξ T -∗ False.
  Proof.
    rewrite own_context_unseal /own_context_def ctx_parked_unseal /ctx_parked_def.
    iIntros "[%c1 H1] [%c2 H2]".
    iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
    exfalso. by apply (Qp.not_add_le_l 1 1).
  Qed.

  Global Instance own_context_timeless `{CID : CpuId} ξ :
    Timeless (own_context ξ).
  Proof. rewrite own_context_unseal /own_context_def. apply _. Qed.
  Global Instance ctx_parked_timeless ξ T : Timeless (ctx_parked ξ T).
  Proof. rewrite ctx_parked_unseal /ctx_parked_def. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (* The token lifecycle (ruling 4's three primitives, plus deposit)    *)
  (* ---------------------------------------------------------------- *)

  (* FRESH ALLOCATION YIELDS A PARKED CONTEXT, and the mint is PURE (no
     interp, no premise): a context that has never run claims no hart and
     no visibility.  Stamp 0 suffices because [ctx_deposit] raises the
     stamp per deposited fact.  ([TsoCtxTwin2.twin_parked_alloc]; the
     rehearsal's [no_ctx_parked_alloc] refuted this only under the old
     global-map twin.)  This is [ProofForkretPark]'s mint. *)
  Lemma ctx_parked_alloc : ⊢ |==> ∃ ξc : CtxId, ctx_parked ξc 0.
  Proof.
    iMod (ghost_var_alloc (0%fin : CPU)) as (γ) "Hv".
    iModIntro. iExists (MkCtxId γ inhabitant).
    rewrite ctx_parked_unseal /ctx_parked_def.
    iExists (0%fin : CPU). iExact "Hv".
  Qed.

  (* BOOT'S MINT: a hart's FIRST running token.  One per hart, at
     [SystemAdequacy.xv6_boot_era], and nowhere else (the sweep-era
     throwaway mints live in [TsoCtxShim.own_context_alloc] and die with
     it).  Satisfiable at TSO unconditionally ([TsoCtxTwin2.twin_run_alloc]:
     a context born at bound 0 with an empty dirty set claims nothing any
     hart could not honour), so this is licensing by NAME, not a lie. *)
  Lemma own_context_boot `{CID : CpuId} : ⊢ |==> ∃ ξ : CtxId, own_context ξ.
  Proof.
    iMod (ghost_var_alloc (0%fin : CPU)) as (γ) "Hv".
    iModIntro. iExists (MkCtxId γ inhabitant).
    rewrite own_context_unseal /own_context_def.
    iExists (0%fin : CPU). iExact "Hv".
  Qed.

  (* PARK: publish and let go of the hart.  One ghost step, no machine
     evidence needed -- the stamp is read off the token's own receipts.
     ([TsoCtxTwin2.twin_park], interp-free.) *)
  Lemma ctx_park `{CID : CpuId} (ξ : CtxId) :
    own_context ξ ==∗ ∃ T, ctx_parked ξ T.
  Proof.
    rewrite own_context_unseal /own_context_def.
    iIntros "[%c H]". iModIntro. iExists 0%nat.
    rewrite ctx_parked_unseal /ctx_parked_def.
    iExists c. iExact "H".
  Qed.

  (* RESUME: re-host a parked context on THIS hart.  The premise is the
     stable pair -- a persistent view receipt dominating the parked stamp.
     ([TsoCtxTwin2.twin_resume]; the receipt/stamp comparison is minted at
     the resuming hart's lock acquire, [TsoCtxTwin2.twin_passed_get].) *)
  Lemma ctx_resume `{CID : CpuId} (ξ : CtxId) (T K : nat) :
    (T ≤ K)%nat →
    hart_view_lb K -∗ ctx_parked ξ T ==∗ own_context ξ.
  Proof.
    rewrite ctx_parked_unseal /ctx_parked_def own_context_unseal /own_context_def.
    iIntros (HTK) "_ [%c H]". iModIntro. iExists c. iExact "H".
  Qed.

  (* THE SWTCH EXCHANGE: a hart always runs exactly one thread, so the
     primitive crossing swaps the running token against a parked one --
     the parker's identity parks, the target's runs, on this hart.
     ([TsoCtxTwin2.twin_exchange], derived there from park + resume.) *)
  Lemma ctx_exchange `{CID : CpuId} (ξ1 ξ2 : CtxId) (T K : nat) :
    (T ≤ K)%nat →
    hart_view_lb K -∗ own_context ξ1 -∗ ctx_parked ξ2 T ==∗
    own_context ξ2 ∗ ∃ T1, ctx_parked ξ1 T1.
  Proof.
    iIntros (HTK) "#HK Hrun Hpk".
    iMod (ctx_park with "Hrun") as (T1) "Hpk1".
    iMod (ctx_resume ξ2 T K HTK with "HK Hpk") as "Hrun".
    iModIntro. iFrame "Hrun". iExists T1. iExact "Hpk1".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The context-indexed points-to                                     *)
  (* ---------------------------------------------------------------- *)

  (* [ctx_pointsto ξ a dq v]: the byte fact, registered to context ξ.
     SC: the index is phantom.  TSO: [∃ t, lattice cell at t ∗ ξ's ledger
     covers t] -- the `weak-memory` branch's [wptsto_cl], with the ledger
     being what survives a change of hart.  The M1 sweep points the
     [↦ₘ]-notation tower here at [cur_ctx]; until then the tree's
     spellings are untouched. *)
  Definition ctx_pointsto_def `{KTR : !CurKtier} (ξ : CtxId)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    mem_pointsto (KTR := KTR) va dq v.
  Lemma ctx_pointsto_aux : { f | f = @ctx_pointsto_def }.
  Proof. by eexists. Qed.
  Definition ctx_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    proj1_sig ctx_pointsto_aux KTR ξ va dq v.
  Lemma ctx_pointsto_unseal `{KTR : !CurKtier} (ξ : CtxId)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) :
    ctx_pointsto ξ va dq v = mem_pointsto (KTR := KTR) va dq v.
  Proof. unfold ctx_pointsto. by rewrite (proj2_sig ctx_pointsto_aux). Qed.

  (* The law surface, mirroring [mem_pointsto]'s (RiscvPtsto.v).  Each is
     proved by unfolding HERE and must hold of the TSO twin; a law that
     could not is a law that must not be added. *)

  Global Instance ctx_pointsto_timeless (KTR : CurKtier) ξ a dq v :
    Timeless (ctx_pointsto (KTR := KTR) ξ a dq v).
  Proof. rewrite ctx_pointsto_unseal. apply _. Qed.

  Global Instance ctx_pointsto_discarded_persistent (KTR : CurKtier) ξ a v :
    Persistent (ctx_pointsto (KTR := KTR) ξ a DfracDiscarded v).
  Proof. rewrite ctx_pointsto_unseal. apply _. Qed.

  (* agreement is CROSS-context (two registered facts about one byte name
     one lattice cell): sound at TSO, and the form invariants need. *)
  Lemma ctx_pointsto_agree {kt1 kt2 : ktier} ξ1 ξ2 a dq1 b1 dq2 b2 :
    ctx_pointsto (KTR := kt1) ξ1 a dq1 b1 -∗
    ctx_pointsto (KTR := kt2) ξ2 a dq2 b2 -∗ ⌜b1 = b2⌝.
  Proof. rewrite !ctx_pointsto_unseal. apply mem_pointsto_agree. Qed.

  Lemma ctx_pointsto_ne {kt1 kt2 : ktier} ξ1 ξ2 a1 a2 dq b1 b2 :
    ctx_pointsto (KTR := kt1) ξ1 a1 (DfracOwn 1) b1 -∗
    ctx_pointsto (KTR := kt2) ξ2 a2 dq b2 -∗ ⌜a1 ≠ a2⌝.
  Proof. rewrite !ctx_pointsto_unseal. apply mem_pointsto_ne. Qed.

  Lemma ctx_pointsto_frac_split `{KTR : !CurKtier} ξ a q1 q2 b :
    ctx_pointsto ξ a (DfracOwn (q1 + q2)) b ⊣⊢
    ctx_pointsto ξ a (DfracOwn q1) b ∗ ctx_pointsto ξ a (DfracOwn q2) b.
  Proof. rewrite !ctx_pointsto_unseal. apply mem_pointsto_frac_split. Qed.

  Lemma ctx_pointsto_persist `{KTR : !CurKtier} ξ a dq b :
    ctx_pointsto ξ a dq b ==∗ ctx_pointsto ξ a DfracDiscarded b.
  Proof. rewrite !ctx_pointsto_unseal. apply mem_pointsto_persist. Qed.

  (* ---------------------------------------------------------------- *)
  (* The context-indexed WORD tower (the M1 notation flip's carrier)    *)
  (* ---------------------------------------------------------------- *)

  (* [RiscvPtsto.word_pointsto]'s shape over the context fact: an 8-byte
     little-endian doubleword owned by thread-of-control ξ, alignment
     bundled.  This is what the [↦₈] spellings mean above the seam after
     the flip; the raw [word_pointsto] stays the kit's (below-Σ) fact.
     Every law is derived from [ctx_pointsto]'s exported surface alone,
     so the tower is honest at both instantiations with no shim. *)

  (* byte-window agreement and splitting, the two engine lemmas *)
  Lemma ctx_bytes_agree {m : N} {kt1 kt2 : ktier} (ξ1 ξ2 : CtxId)
      (a : Arch.pa) (k n : nat) (dq1 dq2 : dfrac) (w1 w2 : bv m) :
    ([∗ list] j ∈ seq k n,
       ctx_pointsto (KTR := kt1) ξ1 (pa_add a j) dq1 (nth_byte w1 j)) -∗
    ([∗ list] j ∈ seq k n,
       ctx_pointsto (KTR := kt2) ξ2 (pa_add a j) dq2 (nth_byte w2 j)) -∗
    ⌜forall j, (k <= j < k + n)%nat -> nth_byte w1 j = nth_byte w2 j⌝.
  Proof.
    revert k. induction n as [|n IH]; intros k; simpl.
    - iIntros "_ _". iPureIntro. intros j Hj. lia.
    - iIntros "[Hh1 Ht1] [Hh2 Ht2]".
      iDestruct (ctx_pointsto_agree with "Hh1 Hh2") as %Heq.
      iDestruct (IH (S k) with "Ht1 Ht2") as %Hrest.
      iPureIntro. intros j Hj.
      destruct (decide (j = k)) as [->|Hne]; [exact Heq|].
      apply Hrest. lia.
  Qed.

  Lemma ctx_bytes_frac_split `{KTR : !CurKtier} {m : N} (ξ : CtxId)
      (a : Arch.pa) (k n : nat) (q1 q2 : Qp) (w : bv m) :
    ([∗ list] j ∈ seq k n,
       ctx_pointsto ξ (pa_add a j) (DfracOwn (q1 + q2)) (nth_byte w j)) ⊣⊢
    ([∗ list] j ∈ seq k n,
       ctx_pointsto ξ (pa_add a j) (DfracOwn q1) (nth_byte w j)) ∗
    ([∗ list] j ∈ seq k n,
       ctx_pointsto ξ (pa_add a j) (DfracOwn q2) (nth_byte w j)).
  Proof.
    rewrite -big_sepL_sep. apply big_opL_proper. intros ? j ?.
    apply ctx_pointsto_frac_split.
  Qed.

  Definition ctx_word_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (w : bv 64) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
     [∗ list] j ∈ seq 0 8, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))%I.

  Section ctx_word.
    Context `{KTR : !CurKtier}.

    Lemma ctx_word_pointsto_unfold ξ a dq w :
      ctx_word_pointsto ξ a dq w ⊣⊢
      ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
      ([∗ list] j ∈ seq 0 8, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j)).
    Proof. reflexivity. Qed.

    Lemma ctx_word_pointsto_aligned_p ξ a dq w :
      ctx_word_pointsto ξ a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
    Proof. iIntros "[$ _]". Qed.

    Lemma ctx_word_pointsto_bytes ξ a dq w :
      ctx_word_pointsto ξ a dq w ⊢
      [∗ list] j ∈ seq 0 8, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j).
    Proof. iIntros "[_ $]". Qed.

    Lemma ctx_word_pointsto_intro ξ a dq w :
      is_aligned_paddr (Physaddr a) 8 = true ->
      ([∗ list] j ∈ seq 0 8, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))
      ⊢ ctx_word_pointsto ξ a dq w.
    Proof. iIntros (Hal) "H". by iFrame. Qed.

    Global Instance ctx_word_pointsto_timeless ξ a dq w :
      Timeless (ctx_word_pointsto ξ a dq w).
    Proof. rewrite /ctx_word_pointsto. apply _. Qed.

    Global Instance ctx_word_pointsto_discarded_persistent ξ a w :
      Persistent (ctx_word_pointsto ξ a DfracDiscarded w).
    Proof. rewrite /ctx_word_pointsto. apply _. Qed.

    Lemma ctx_word_pointsto_frac_split ξ a q1 q2 w :
      ctx_word_pointsto ξ a (DfracOwn (q1 + q2)) w ⊣⊢
      ctx_word_pointsto ξ a (DfracOwn q1) w ∗
      ctx_word_pointsto ξ a (DfracOwn q2) w.
    Proof.
      rewrite /ctx_word_pointsto (ctx_bytes_frac_split ξ a 0 8 q1 q2 w).
      iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
    Qed.

    Lemma ctx_word_pointsto_persist ξ a dq w :
      ctx_word_pointsto ξ a dq w ==∗ ctx_word_pointsto ξ a DfracDiscarded w.
    Proof.
      iIntros "[#Hal H]".
      iAssert (|==> [∗ list] j ∈ seq 0 8,
        ctx_pointsto ξ (pa_add a j) DfracDiscarded (nth_byte w j))%I
        with "[H]" as ">H".
      { iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
        iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_persist. }
      iModIntro. by iFrame "Hal H".
    Qed.
  End ctx_word.

  Lemma ctx_word_pointsto_agree {kt1 kt2 : ktier} (ξ1 ξ2 : CtxId) a dq1 w1 dq2 w2 :
    ctx_word_pointsto (KTR := kt1) ξ1 a dq1 w1 -∗
    ctx_word_pointsto (KTR := kt2) ξ2 a dq2 w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (ctx_bytes_agree ξ1 ξ2 a 0 8 with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=8)). intros j Hj. apply Hb. lia.
  Qed.

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
  Definition ctx_dom_def (ξ ξ' : CtxId) : iProp Σ := True%I.
  Lemma ctx_dom_aux : { f | f = ctx_dom_def }.
  Proof. by eexists. Qed.
  Definition ctx_dom (ξ ξ' : CtxId) : iProp Σ := proj1_sig ctx_dom_aux ξ ξ'.
  Lemma ctx_dom_unseal (ξ ξ' : CtxId) : ctx_dom ξ ξ' = ctx_dom_def ξ ξ'.
  Proof. unfold ctx_dom. by rewrite (proj2_sig ctx_dom_aux). Qed.

  (* A context-indexed payload that transports along domination.  This is
     the obligation lock payloads pick up in the M3 sweep: any payload
     failing it at SC is a payload the TSO flip would break -- found
     early, which is the point of the sweeps. *)
  (* IT IS A PLAIN ENTAILMENT, NOT AN UPDATE (transport memo ruling 3,
     2026-08-26).  The bare [==∗] this class carried until then was never
     used: [TsoCtxTwin2.ctx_morph_pointsto] and the REAL kit's
     [TsoCtx.ctx_morph_pointsto] both derive the timestamp bound by
     [mono_nat_lb_own_valid] / [ghost_map_lookup] -- entailments -- and
     rebuild the clean arm from [ctx_dom]'s persistent lower bound, with no
     [iMod] anywhere.  Stating it as [-∗] is therefore a STRENGTHENING that
     is provable at both instantiations, and it is what lets a payload
     under a [▷] be transported by [bi.later_mono] rather than needing a
     step.  ([ctx_deposit] below stays [==∗]: ITS update is
     [ctx_dom_to_parked], not the morph.) *)
  Class CtxMorph (R : CtxId → iProp Σ) :=
    ctx_morph : ∀ ξ ξ', ctx_dom ξ ξ' -∗ R ξ -∗ ctx_dom ξ ξ' ∗ R ξ'.

  (* The structural instances.  NOTE what is absent: no instance for
     [own_context] (the running-thread token never transfers by
     domination), and no blanket instance for persistent-but-ξ-dependent
     propositions (the TSO ledger lower bound is persistent AND pinned to
     its context).  ξ-CONSTANT propositions -- pure facts, ghost state,
     invariant handles, whole lock handles -- are covered by
     [ctx_morph_const]. *)

  (* LOW PRIORITY, and it is a guard, not a tuning: [ctx_morph_const]
     unifies with ANY payload whose context argument is still an evar
     ([?R := λ _, ?P]), so an eager resolution while a call site's payload
     is not yet pinned would silently commit it to a CONSTANT embedding.
     With the priority, the pointsto/structural instances win whenever the
     payload is known, and an evar payload stays pending until the framed
     [is_lock]/[R cur_ctx] hypothesis pins it -- which is what makes
     passing [_] for the payload at acquire/release call sites safe. *)
  Global Instance ctx_morph_const (P : iProp Σ) : CtxMorph (λ _, P) | 100.
  Proof. iIntros (ξ ξ') "Hd HP". iFrame. Qed.

  Global Instance ctx_morph_pointsto (kt : ktier) a dq v :
    CtxMorph (λ ξ, ctx_pointsto (KTR := kt) ξ a dq v).
  Proof.
    iIntros (ξ ξ') "Hd HP". iFrame "Hd".
    iEval (rewrite ctx_pointsto_unseal) in "HP".
    rewrite ctx_pointsto_unseal. iExact "HP".
  Qed.

  Global Instance ctx_morph_sep (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, R1 ξ ∗ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ ξ') "Hd [HR1 HR2]".
    iDestruct (ctx_morph with "Hd HR1") as "[Hd HR1]".
    iDestruct (ctx_morph with "Hd HR2") as "[Hd HR2]".
    iFrame.
  Qed.

  Global Instance ctx_morph_exist {A} (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMorph (Φ x)) → CtxMorph (λ ξ, ∃ x, Φ x ξ)%I.
  Proof.
    iIntros (HΦ ξ ξ') "Hd [%x HR]".
    iDestruct (ctx_morph with "Hd HR") as "[Hd HR]".
    iFrame "Hd". iExists x. iExact "HR".
  Qed.

  Global Instance ctx_morph_big_sepL {A} (l : list A)
      (Φ : nat → A → CtxId → iProp Σ) :
    (∀ i x, CtxMorph (Φ i x)) →
    CtxMorph (λ ξ, [∗ list] i ↦ x ∈ l, Φ i x ξ)%I.
  Proof.
    revert Φ. induction l as [|x l IH] => Φ HΦ.
    - iIntros (ξ ξ') "Hd _". by iFrame.
    - iIntros (ξ ξ') "Hd [HR HRs]".
      iDestruct (ctx_morph with "Hd HR") as "[Hd HR]".
      iDestruct (IH (λ i y, Φ (S i) y) _ ξ ξ' with "Hd HRs") as "[Hd HRs]".
      iFrame.
  Qed.

  (* the map form.  [disk_res]'s in-flight and parked windows are
     [big_sepM]s over ξ-indexed members, so the list instance above does
     not reach them; the proof is the same induction, over [map_ind].
     (Kit obligation: the twin's [CtxMorph] block needs the same
     instance -- it is derivable from [ctx_morph] alone, exactly as
     [ctx_morph_big_sepL] is.) *)
  Global Instance ctx_morph_big_sepM `{Countable K} {A} (m : gmap K A)
      (Φ : K → A → CtxId → iProp Σ) :
    (∀ k x, CtxMorph (Φ k x)) →
    CtxMorph (λ ξ, [∗ map] k ↦ x ∈ m, Φ k x ξ)%I.
  Proof.
    intros HΦ. induction m as [|k x m Hk IH] using map_ind.
    - iIntros (ξ ξ') "Hd _". rewrite !big_sepM_empty. by iFrame.
    - iIntros (ξ ξ') "Hd H". rewrite !big_sepM_insert //.
      iDestruct "H" as "[HR HRs]".
      iDestruct (ctx_morph with "Hd HR") as "[Hd HR]".
      iDestruct (IH ξ ξ' with "Hd HRs") as "[Hd HRs]".
      iFrame.
  Qed.

  (* THE GUARDED SLOT.  A payload that is present on some states and [emp]
     on the others -- [SchedCtx.proc_slots]' five arms, every [if ... then
     ... else emp] in a lock invariant -- transports arm by arm.  Stated as
     two instances rather than one over an [option] because the tree writes
     the guard as a plain [bool] and the [emp] side varies.
     (Kit obligation: both are derivable from [ctx_morph] alone, exactly as
     [ctx_morph_big_sepL] is, so the twin's block needs them at the swap.) *)
  Global Instance ctx_morph_if_then (b : bool) (R : CtxId → iProp Σ) :
    CtxMorph R → CtxMorph (λ ξ, if b then R ξ else emp)%I.
  Proof.
    intros HR. destruct b; [| iIntros (ξ ξ') "Hd _"; by iFrame ].
    iIntros (ξ ξ') "Hd H". by iApply (ctx_morph with "Hd H").
  Qed.

  Global Instance ctx_morph_if_else (b : bool) (R : CtxId → iProp Σ) :
    CtxMorph R → CtxMorph (λ ξ, if b then emp else R ξ)%I.
  Proof.
    intros HR. destruct b; [ iIntros (ξ ξ') "Hd _"; by iFrame |].
    iIntros (ξ ξ') "Hd H". by iApply (ctx_morph with "Hd H").
  Qed.

  (* the word cell's transport obligation, once for every payload *)
  Global Instance ctx_morph_word (kt : ktier) a dq w :
    CtxMorph (λ ξ, ctx_word_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ ξ') "Hd [%Hal H]".
    iDestruct (ctx_morph_big_sepL (seq 0 8)
            (λ _ j ξ0, ctx_pointsto (KTR := kt) ξ0 (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_morph_pointsto _ _ _ _)
            ξ ξ' with "Hd H") as "[Hd H]".
    iFrame "Hd". iSplit; [done|]. iExact "H".
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

  (* THE DEPOSIT: a running context hands ANY morphable payload to a
     PARKED one, the parked stamp raised to cover it -- so a fork's
     hand-me-downs (including bytes the parent wrote after the child's
     mint: uvmcopy) have NOTHING TO PROVE at the deposit site; the
     resumer's lock acquire pays the raised stamp.
     ([TsoCtxTwin2.twin_deposit], interp-free.  This subsumes the
     stamp-at-the-parent's-counter mechanism of tso-port ruling 2d.4.1:
     the stamp follows the deposits instead of being fixed at birth.) *)
  Lemma ctx_deposit `{CID : CpuId} (R : CtxId → iProp Σ) `{!CtxMorph R}
      (ξ ξc : CtxId) (T : nat) :
    own_context ξ -∗ ctx_parked ξc T -∗ R ξ ==∗
    own_context ξ ∗ ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_parked ξc T' ∗ R ξc.
  Proof.
    iIntros "Hrun Hpk HR".
    iDestruct (ctx_morph ξ ξc with "[] HR") as "[_ HR]".
    { rewrite ctx_dom_unseal /ctx_dom_def. done. }
    iModIntro. iFrame "Hrun". iExists T. iFrame "Hpk HR". done.
  Qed.

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

(* THE PAYLOAD WRAPPER (the M3 sweep's client spelling; the `weak-memory`
   branch's `<{ }>`, adopted with ONE deliberate change).  A lock client
   writes its payload as a plain [iProp] with the ambient spellings; this
   turns it into the [CtxId → iProp] the lock surface needs as a CONSTANT
   embedding.

   THE BINDER IS ANONYMOUS, unlike the branch's [λ XLK : CurCtx, P].  A
   NAMED [CurCtx] binder is a typeclass instance candidate inside [P], so
   an ambient-spelled fact in [P] re-indexes under it -- or not, depending
   on elaboration order at each mention site (the silent-drop hazard the
   kmem conversion recorded as recipe rule 1, observed live again when
   [proc_lock_res] picked up context-indexed conjuncts at the M1 flip and
   its ~40 wrapped mention sites stopped unifying with each other).  With
   [_] the wrapper can NEVER capture: everything inside [P] elaborates at
   the OUTER ambient, identically at every site, and [ctx_morph_const]
   applies.  A payload that should genuinely re-index is CONVERTED, not
   wrapped: it is passed as [(λ ξ : CtxId, pay (XI := ξ) ...)] and brings
   its own [CtxMorph] (rule 1's spelling; kmem_res is the reference).
   THE SPELLING IS [<{ P }>] AND NOT [<[ P ]>]: stdpp's insert notation
   shares the [<[] prefix and Coq reports the two as incompatible
   (measured on the branch; the brace form is free).

   IT IS A COMBINATOR, NOT A λ.  Even an ANONYMOUS [λ _ : CurCtx, P]
   captures: Coq auto-names the binder (H) and -- [CurCtx] being a
   transparent definitional class -- typeclass search inside [P] can still
   pick it up, at some sites and not others (observed live: two
   elaborations of the same wrapped [proc_lock_res] payload that refuse to
   unify).  With [const_pay], [P] is elaborated as the combinator's
   ARGUMENT -- outside any [CurCtx]-typed binder -- so its ambient facts
   always bind the caller's context, identically at every site. *)
Definition const_pay {Σ : gFunctors} (P : iProp Σ) : CtxId → iProp Σ :=
  λ _, P.
Notation "<{ P }>" := (const_pay P%I)
  (at level 0, P at level 200, format "<{  P  }>").

(* the combinator's transport obligation: same guard role and priority
   story as [ctx_morph_const] (which still serves bare λ-spellings). *)
Global Instance ctx_morph_const_pay `{!riscvGS Σ} (P : iProp Σ) :
  CtxMorph (const_pay P) | 99.
Proof. iIntros (ξ ξ') "Hd HP". iFrame. Qed.

(* The class TYPE is transparent to typeclass unification: [CurCtx] is
   definitionally [CtxId], and instance search must see through the
   wrapper's binder type or every [Persistent (is_lock … <{P}>)] /
   [CtxMorph <{P}>] resolution dies at the (CurCtx → iProp) vs
   (CtxId → iProp) seam.  This transparency is about the TYPE only; which
   ambient [CurCtx] INSTANCE a term picks up is unaffected (the
   silent-drop hazard in tso-port.md §2d concerns instance selection, not
   type unfolding). *)
Global Typeclasses Transparent CurCtx.

(* ================================================================== *)
(* THE M1 NOTATION FLIP (stage 1: the byte and 8-byte-word families).
   The [↦ₘ] and [↦₈] spellings are REBOUND here to the context-indexed
   facts; this declaration OVERRIDES [RiscvPtsto]'s in every file that
   imports this one after [RiscvPtsto] (the tree-wide import-order audit
   is [tools/lock_ctx_sweep.py] check mode's job).  Files below this one
   -- the kit -- never import it and keep the raw meanings; that split
   IS the seam.  The spellings are character-identical, which is the
   whole point: statement text above the seam does not change, its
   MEANING does.  [↦c] becomes a synonym and is retired by attrition.
   Stage 2 flips [↦₄]/[↦₂]/[↦ₛ]/[↦ₚ]; [↦ₓ] (text) and [↦ᵣ] (registers)
   NEVER flip -- text is timestamp-0 context-free by the port's ruling,
   and registers are per-hart machine state. *)
Notation "a ↦ₘ{ dq } v" := (ctx_pointsto cur_ctx a dq v)
  (at level 20, format "a  ↦ₘ{ dq }  v") : bi_scope.
Notation "a ↦ₘ□ v" := (ctx_pointsto cur_ctx a DfracDiscarded v)
  (at level 20, format "a  ↦ₘ□  v") : bi_scope.
Notation "a ↦ₘ v" := (ctx_pointsto cur_ctx a (DfracOwn 1) v)
  (at level 20, format "a  ↦ₘ  v") : bi_scope.
Notation "a ↦ₘ[ kt ] dq v" := (ctx_pointsto (KTR := kt) cur_ctx a dq v)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦ₘ[ kt ] dq  v") : bi_scope.

Notation "a ↦₈{ dq } w" := (ctx_word_pointsto cur_ctx a dq w)
  (at level 20, format "a  ↦₈{ dq }  w") : bi_scope.
Notation "a ↦₈ w" := (ctx_word_pointsto cur_ctx a (DfracOwn 1) w)
  (at level 20, format "a  ↦₈  w") : bi_scope.
Notation "a ↦₈□ w" := (ctx_word_pointsto cur_ctx a DfracDiscarded w)
  (at level 20, format "a  ↦₈□  w") : bi_scope.
Notation "a ↦₈[ kt ] dq w" := (ctx_word_pointsto (KTR := kt) cur_ctx a dq w)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦₈[ kt ] dq  w") : bi_scope.

(* The seal.  [ctx_dom] and [hart_view_lb] stay opaque too: nothing above
   this file may learn they are [True] at SC, and nothing may learn
   [ctx_parked] ignores its stamp. *)
Global Typeclasses Opaque own_context ctx_parked hart_view_lb
  ctx_pointsto ctx_dom.
Global Opaque own_context ctx_parked hart_view_lb ctx_pointsto ctx_dom.
(* [ctx_word_pointsto] is NOT sealed at all: it is a tower OVER the sealed
   byte fact, so exposing its ⌜aligned⌝ ∗ big-op shape leaks nothing about
   SC-degeneracy -- and the tree's pre-flip proofs destruct/frame the word
   shape structurally (that worked when [word_pointsto] was transparent, and
   keeps working now).  The BYTE seal below it is the one that matters. *)
