(* TsoCtxMove.v -- THE SAME-HART HAND-OFF (tso-port.md §0.43′; tso-machine-flip.md
   A6.128): moving a context-indexed fact between two RUNNING contexts on one
   hart, with both running tokens in hand.  On main: the STATEMENTS verbatim,
   the bodies SC-trivial.

   WHERE IT IS NEEDED.  swtch hands cells from the caller's thread to the
   target's with no fence between: the scheduler's [p->state = RUNNING] /
   [c->proc = p] stores are still in the hart's store buffer when the proc's
   [forkret]/[release] read them, and the parker's save-area stores are
   buffered when the scheduler resumes.  Store forwarding makes those reads
   correct on the hardware; in the logic that is the AUTHOR arm of
   [visibleb], which is what a context's DIRTY registration records.  So:

     - a CLEAN cell at ξ0 ([t ≤ B0 ≤ view]) is clean at ξ1 once ξ1's bound is
       raised to [max B1 B0] -- legal, both are under this hart's view
       ([TsoCtx.ctx_bound_raise]'s argument, paid with ξ0's own receipt);
     - a DIRTY cell at ξ0 (its key registered at ξ0, the message this hart's
       own) is REGISTERED at ξ1 with the same justification.  Registration is
       total because the dirty set is a monotone set authority whose
       membership is re-mintable (A6.128, [TsoGhost.dset_insert]): whether or
       not ξ1 already has the key, it gets the witness.

   The class [CtxMove R] is [TsoCtx.CtxMorph]'s twin for this crossing; its
   structural instances mirror [CtxMorph]'s.  Nothing here consults the
   interpretation: both premises are running tokens.

   WHAT IS TRIVIAL HERE, AND WHY.  Main is SC: [own_context] is sealed with
   the body [True ∨ …], [ctx_floor] with [True], and [ctx_pointsto]'s index
   is PHANTOM (its body is [RiscvPtsto.mem_pointsto]), so both leaf laws
   discharge by the unseal lemmas -- there is no bound to raise, no dirty set
   to register in and no [TsoGhost] below the seal to do it with.  The
   STATEMENTS are the T-leg's exactly, which is the seal principle: at the
   TSO cutover the bodies are replaced and no consumer above this file moves.
   [TsoCtxPark.v] / [TsoCtxAbsorbLb.v] are the precedent for exactly this
   arrangement.  The T-leg's [view_lb_max'] is below the seal and not
   stated; so are the two physical-tier leaves ([ctx_phys_pointsto] /
   [ctx_phys_word_pointsto] do not exist on main), and their two rows of the
   solver go with them.

   WHY ITS OWN FILE: [TsoCtx.v] is under the whole tree; this is a derivation
   off its public unseal lemmas ([TsoCtxAbsorbLb] / [TsoCtxPark] precedent). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var invariants.
Require Import SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoCtx.

Section Move.
  Context `{!riscvGS Σ}.

  (* THE CLEAN HALF: a bound ξ0 has passed, ξ1 passes too -- ξ1's bound
     rises to ξ0's.  Both are under the hart's view, so the raised bound
     keeps [B ≤ K] with the joined receipt; ξ1's dirty justifications are
     monotone in the bound.  (SC: the floor is [True] and the two tokens
     pass straight through.) *)
  Lemma ctx_move_floor `{CID : CpuId} (ξ0 ξ1 : CtxId) (lo : nat) :
    own_context ξ0 -∗ own_context ξ1 -∗ ctx_floor ξ0 lo ==∗
    own_context ξ0 ∗ own_context ξ1 ∗ ctx_floor ξ1 lo.
  Proof.
    rewrite !ctx_floor_unseal /ctx_floor_def.
    iIntros "H0 H1 _". iModIntro. iFrame "H0 H1".
  Qed.

  (* THE CELL MOVES, EITHER ARM.  (SC: the index is phantom -- the cell's
     clean/dirty bit and the whole case split live under the seal.) *)
  Lemma ctx_move_pointsto `{CID : CpuId} `{KTR : !CurKtier} (ξ0 ξ1 : CtxId)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    own_context ξ0 -∗ own_context ξ1 -∗ ctx_pointsto (KTR := KTR) ξ0 a dq v ==∗
    own_context ξ0 ∗ own_context ξ1 ∗ ctx_pointsto (KTR := KTR) ξ1 a dq v.
  Proof.
    iIntros "H0 H1 HP". iModIntro. iFrame "H0 H1".
    iEval (rewrite ctx_pointsto_unseal) in "HP".
    rewrite ctx_pointsto_unseal. iExact "HP".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The class and its structural instances -- [CtxMorph]'s mirror.    *)
  (* ---------------------------------------------------------------- *)
  Class CtxMove `{CID : CpuId} (R : CtxId → iProp Σ) :=
    ctx_move : ∀ ξ0 ξ1, own_context ξ0 -∗ own_context ξ1 -∗ R ξ0 ==∗
                        own_context ξ0 ∗ own_context ξ1 ∗ R ξ1.

  Global Instance ctx_move_const `{CID : CpuId} (P : iProp Σ) : CtxMove (λ _, P) | 100.
  Proof. iIntros (ξ0 ξ1) "H0 H1 HP !>". iFrame. Qed.

  Global Instance ctx_move_sep `{CID : CpuId} (R1 R2 : CtxId → iProp Σ) :
    CtxMove R1 → CtxMove R2 → CtxMove (λ ξ, R1 ξ ∗ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ0 ξ1) "H0 H1 [HR1 HR2]".
    iMod (ctx_move with "H0 H1 HR1") as "(H0 & H1 & HR1)".
    iMod (ctx_move with "H0 H1 HR2") as "(H0 & H1 & HR2)".
    iModIntro. iFrame.
  Qed.

  Global Instance ctx_move_exist `{CID : CpuId} {A} (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMove (Φ x)) → CtxMove (λ ξ, ∃ x, Φ x ξ)%I.
  Proof.
    iIntros (HΦ ξ0 ξ1) "H0 H1 (%x & HR)".
    iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)".
    iModIntro. iFrame "H0 H1". iExists x. iExact "HR".
  Qed.

  Global Instance ctx_move_big_sepL `{CID : CpuId} {A} (l : list A)
      (Φ : nat → A → CtxId → iProp Σ) :
    (∀ i x, CtxMove (Φ i x)) → CtxMove (λ ξ, [∗ list] i ↦ x ∈ l, Φ i x ξ)%I.
  Proof.
    revert Φ. induction l as [|x l IH] => Φ HΦ.
    - iIntros (ξ0 ξ1) "H0 H1 _ !>". by iFrame.
    - iIntros (ξ0 ξ1) "H0 H1 [HR HRs]".
      iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)".
      iMod (IH (λ i y, Φ (S i) y) _ ξ0 ξ1 with "H0 H1 HRs") as "(H0 & H1 & HRs)".
      iModIntro. iFrame.
  Qed.

  Global Instance ctx_move_big_sepM `{CID : CpuId} `{Countable K} {A} (m : gmap K A)
      (Φ : K → A → CtxId → iProp Σ) :
    (∀ k x, CtxMove (Φ k x)) → CtxMove (λ ξ, [∗ map] k ↦ x ∈ m, Φ k x ξ)%I.
  Proof.
    intros HΦ. induction m as [|k x m Hk IH] using map_ind.
    - iIntros (ξ0 ξ1) "H0 H1 _ !>". rewrite big_sepM_empty. by iFrame.
    - iIntros (ξ0 ξ1) "H0 H1 HR".
      iDestruct (big_sepM_insert _ _ _ _ Hk with "HR") as "[HR HRs]".
      iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)".
      iMod (IH ξ0 ξ1 with "H0 H1 HRs") as "(H0 & H1 & HRs)".
      iModIntro. iFrame "H0 H1". rewrite (big_sepM_insert _ _ _ _ Hk). iFrame.
  Qed.

  Global Instance ctx_move_big_sepS `{CID : CpuId} `{Countable A} (X : gset A)
      (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMove (Φ x)) → CtxMove (λ ξ, [∗ set] x ∈ X, Φ x ξ)%I.
  Proof.
    intros HΦ. induction X as [|x X Hx IH] using set_ind_L.
    - iIntros (ξ0 ξ1) "H0 H1 _ !>". rewrite big_sepS_empty. by iFrame.
    - iIntros (ξ0 ξ1) "H0 H1 HR".
      iDestruct (big_sepS_insert _ _ _ Hx with "HR") as "[HR HRs]".
      iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)".
      iMod (IH ξ0 ξ1 with "H0 H1 HRs") as "(H0 & H1 & HRs)".
      iModIntro. iFrame "H0 H1". rewrite (big_sepS_insert _ _ _ Hx). iFrame.
  Qed.

  Global Instance ctx_move_or `{CID : CpuId} (R1 R2 : CtxId → iProp Σ) :
    CtxMove R1 → CtxMove R2 → CtxMove (λ ξ, R1 ξ ∨ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ0 ξ1) "H0 H1 [HR | HR]".
    - iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)". iModIntro. iFrame "H0 H1". by iLeft.
    - iMod (ctx_move with "H0 H1 HR") as "(H0 & H1 & HR)". iModIntro. iFrame "H0 H1". by iRight.
  Qed.

  Global Instance ctx_move_if `{CID : CpuId} (b : bool) (R1 R2 : CtxId → iProp Σ) :
    CtxMove R1 → CtxMove R2 → CtxMove (λ ξ, if b then R1 ξ else R2 ξ)%I.
  Proof. intros H1 H2. destruct b; [exact H1 | exact H2]. Qed.

  Global Instance ctx_move_pointsto_inst `{CID : CpuId} (kt : ktier) a dq v :
    CtxMove (λ ξ, ctx_pointsto (KTR := kt) ξ a dq v).
  Proof. iIntros (ξ0 ξ1) "H0 H1 HP". iApply (ctx_move_pointsto with "H0 H1 HP"). Qed.

  Global Instance ctx_move_floor_inst `{CID : CpuId} (lo : nat) :
    CtxMove (λ ξ, ctx_floor ξ lo).
  Proof. iIntros (ξ0 ξ1) "H0 H1 #Hfl". iApply (ctx_move_floor with "H0 H1 Hfl"). Qed.

  Global Instance ctx_move_word `{CID : CpuId} (kt : ktier) a dq w :
    CtxMove (λ ξ, ctx_word_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 [%Hal H]".
    iMod (ctx_move_big_sepL (seq 0 8)
            (λ _ j ξ, ctx_pointsto (KTR := kt) ξ (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_move_pointsto_inst _ _ _ _) ξ0 ξ1 with "H0 H1 H") as "(H0 & H1 & H)".
    iModIntro. iFrame "H0 H1". iSplit; [done|]. iExact "H".
  Qed.

  Global Instance ctx_move_word2 `{CID : CpuId} (kt : ktier) a dq w :
    CtxMove (λ ξ, ctx_word2_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 [%Hal H]".
    iMod (ctx_move_big_sepL (seq 0 2)
            (λ _ j ξ, ctx_pointsto (KTR := kt) ξ (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_move_pointsto_inst _ _ _ _) ξ0 ξ1 with "H0 H1 H") as "(H0 & H1 & H)".
    iModIntro. iFrame "H0 H1". iSplit; [done|]. iExact "H".
  Qed.

  Global Instance ctx_move_word4 `{CID : CpuId} (kt : ktier) a dq w :
    CtxMove (λ ξ, ctx_word4_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ0 ξ1) "H0 H1 [%Hal H]".
    iMod (ctx_move_big_sepL (seq 0 4)
            (λ _ j ξ, ctx_pointsto (KTR := kt) ξ (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_move_pointsto_inst _ _ _ _) ξ0 ξ1 with "H0 H1 H") as "(H0 & H1 & H)".
    iModIntro. iFrame "H0 H1". iSplit; [done|]. iExact "H".
  Qed.

End Move.

(* THE DRIVER ([CtxMorphTac.ctx_morph_solve]'s mirror): [cur_ctx] unfolded
   first (a payload spelled with the ambient notations elaborates its cells
   at [@cur_ctx XI]), then the structural instances BY NAME down to the
   leaves; what it cannot decompose is left for the caller's own instances. *)
(* THE SOLVER IS SYNTACTIC.  Both the structural steps and the leaves are
   dispatched on the head symbol of the body: an [apply ctx_move_sep] (or
   [apply ctx_move_pointsto_inst]) against a NAMED predicate (say
   [proc_dormant_noctx (XI := ξ) pa st], or a ghost [own]) makes the
   unifier δ-unfold the name and search its [∗]/[∃] spine against the
   lemma's pattern -- measured: SchedCtx's payload instance hung for 20
   minutes.  A named ξ-dependent leaf goes to instance search ([apply _])
   instead, where the consumer registers one [CtxMove] instance per named
   piece (SchedCtx, CpuOwnMove, SwtchCtx); a ξ-free body is a constant.
   [cur_ctx] is unfolded at every step: the notations ([↦ₘ], [↦₈]) hide it,
   and a name unfolded by the consumer's [rewrite /...] exposes fresh
   occurrences. *)
Ltac ctx_move_step :=
  try rewrite /cur_ctx; cbv beta;
  lazymatch goal with
  | |- CtxMove (λ _, ?body) => apply ctx_move_const
  | |- CtxMove (λ ξ, bi_exist _) => apply ctx_move_exist; intros ?
  | |- CtxMove (λ ξ, bi_sep _ _) => apply ctx_move_sep
  | |- CtxMove (λ ξ, bi_or _ _) => apply ctx_move_or
  | |- CtxMove (λ ξ, big_opL bi_sep _ _) => apply ctx_move_big_sepL; intros ? ?
  | |- CtxMove (λ ξ, big_opM bi_sep _ _) => apply ctx_move_big_sepM; intros ? ?
  | |- CtxMove (λ ξ, big_opS bi_sep _ _) => apply ctx_move_big_sepS; intros ?
  | |- CtxMove (λ ξ, if _ then _ else _) => apply ctx_move_if
  | |- CtxMove (λ ξ, ctx_pointsto ξ _ _ _) => apply ctx_move_pointsto_inst
  | |- CtxMove (λ ξ, ctx_floor ξ _) => apply ctx_move_floor_inst
  | |- CtxMove (λ ξ, ctx_word_pointsto ξ _ _ _) => apply ctx_move_word
  | |- CtxMove (λ ξ, ctx_word2_pointsto ξ _ _ _) => apply ctx_move_word2
  | |- CtxMove (λ ξ, ctx_word4_pointsto ξ _ _ _) => apply ctx_move_word4
  | |- _ => apply _
  end.
Ltac ctx_move_solve := repeat ctx_move_step.
