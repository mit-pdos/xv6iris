(* CtxMorphTac.v -- THE TRANSPORT-OBLIGATION DRIVER (A6.121, the M3
   λ-conversion).

   A λ-converted lock payload owes [TsoCtx.CtxMorph] for real, and its proof
   is entirely structural: exists / sep / big-ops / boolean branches down to
   the leaves, which are the context cells ([ctx_pointsto] and the three
   word widths) and ξ-constant parts (pure facts, ghost state, ledger cells,
   invariant handles).  Typeclass search resolves these composites in some
   files and not in others -- measured on identical goals, the difference
   being only the file the goal is stated in -- so nothing here relies on
   it: the tactic applies the structural instances BY NAME and stops at
   whatever it cannot decompose, which a caller then closes with the
   payload's own component instances (see DiskInv.v's [DiskResAt]).

   [cur_ctx] is unfolded first: a payload spelled with the ambient
   notations elaborates its cells at [@cur_ctx XI], and once [XI] is
   instantiated at the λ's binder the projection has to go before the leaf
   lemmas can see the binder.  A separate file so that the tactic can grow
   without re-certifying [TsoCtx]'s cone. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import mono_nat.
Require Import SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.

(* A6.129: THE LEAVES THE p->lock PAYLOAD NEEDS -- [or], [big_sepS], the
   FULL physical-tier byte and word (the trapframe/page-table pages of a
   dormant slot).  Structural proofs mirror TsoCtx's; the physical byte's
   proof is [ctx_morph_phys_pointsto_h]'s with the full seal. *)
Section MorphMore.
  Context `{!riscvGS Σ}.

  (* TsoCtx's [llb_valid_q], which is Local there *)
  Lemma cmt_llb_valid_q (γ : gname) (q : Qp) (n K : nat) :
    mono_nat_auth_own γ q n -∗ llb γ K -∗ ⌜(K ≤ n)%nat⌝.
  Proof.
    iIntros "Ha [Hlb|%Hz]".
    - by iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ ?].
    - iPureIntro. lia.
  Qed.

  Global Instance ctx_morph_or (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, R1 ξ ∨ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ ξ') "Hd [HR | HR]".
    - iMod (ctx_morph with "Hd HR") as "[Hd HR]". iModIntro. iFrame "Hd". by iLeft.
    - iMod (ctx_morph with "Hd HR") as "[Hd HR]". iModIntro. iFrame "Hd". by iRight.
  Qed.

  Global Instance ctx_morph_big_sepS `{Countable A} (X : gset A)
      (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMorph (Φ x)) → CtxMorph (λ ξ, [∗ set] x ∈ X, Φ x ξ)%I.
  Proof.
    intros HΦ. induction X as [|x X Hx IH] using set_ind_L.
    - iIntros (ξ ξ') "Hd _ !>". rewrite big_sepS_empty. by iFrame.
    - iIntros (ξ ξ') "Hd HR".
      iDestruct (big_sepS_insert _ _ _ Hx with "HR") as "[HR HRs]".
      iMod (ctx_morph with "Hd HR") as "[Hd HR]".
      iMod (IH ξ ξ' with "Hd HRs") as "[Hd HRs]".
      iModIntro. iFrame "Hd". rewrite (big_sepS_insert _ _ _ Hx). iFrame.
  Qed.

  Global Instance ctx_morph_phys_pointsto (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    CtxMorph (λ ξ, ctx_phys_pointsto ξ a dq v).
  Proof.
    iIntros (ξ ξ') "Hd HP".
    rewrite ctx_dom_unseal /ctx_dom_def !ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iDestruct "Hd" as
      "(%B & %W & %B' & %D & [Hb Hdm] & %HDW & %HBB' & %HWB' & #Hlb')".
    iDestruct "HP" as "(%t & Hpt & Hts & Hbit)".
    iAssert (⌜(t ≤ B')%nat⌝)%I as %HtB'.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - iDestruct (cmt_llb_valid_q with "Hb Hcl") as %HtB.
        iPureIntro. lia.
      - iDestruct (dset_lookup with "Hdm Hdt") as %HDt.
        have HtW : ((t, a).1 ≤ W)%nat by apply HDW.
        simpl in HtW. iPureIntro. lia. }
    iClear "Hbit". iModIntro.
    iSplitL "Hb Hdm".
    { iExists B, W, B', D. iFrame "Hb Hdm Hlb'". by iPureIntro. }
    iExists t. iFrame "Hpt Hts".
    iLeft. rewrite /llb. iLeft.
    iApply (mono_nat_lb_own_le with "Hlb'"). lia.
  Qed.

  Global Instance ctx_morph_phys_word (a : Arch.pa) (dq : dfrac) (w : bv 64) :
    CtxMorph (λ ξ, ctx_phys_word_pointsto ξ a dq w).
  Proof.
    iIntros (ξ ξ') "Hd [%Hal H]".
    iMod (ctx_morph_big_sepL (seq 0 8)
            (λ _ j ξ, ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_morph_phys_pointsto _ _ _) ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame "Hd". iSplit; [done|]. iExact "H".
  Qed.
End MorphMore.

(* THE SOLVER IS SYNTACTIC (A6.129; TsoCtxMove.ctx_move_step's twin, and
   for the same measured reason: an [apply ctx_morph_sep] or a leaf [apply]
   against a NAMED piece δ-unfolds it and hangs).  Head-symbol dispatch;
   a named ξ-dependent leaf goes to instance search, where the consumer's
   per-piece instances live; [cur_ctx] is unfolded at every step. *)
Ltac ctx_morph_step :=
  try rewrite /cur_ctx; cbv beta;
  lazymatch goal with
  | |- CtxMorph (λ _, ?body) => apply ctx_morph_const
  | |- CtxMorph (λ ξ, ctx_phys_pointsto_h ξ _ _) => apply ctx_morph_phys_pointsto_h
  | |- CtxMorph (λ ξ, ctx_cell_keep ξ _) => apply ctx_morph_cell_keep
  | |- CtxMorph (λ ξ, bi_exist _) => apply ctx_morph_exist; intros ?
  | |- CtxMorph (λ ξ, bi_sep _ _) => apply ctx_morph_sep
  | |- CtxMorph (λ ξ, bi_or _ _) => apply ctx_morph_or
  | |- CtxMorph (λ ξ, big_opL bi_sep _ _) => apply ctx_morph_big_sepL; intros ? ?
  | |- CtxMorph (λ ξ, big_opM bi_sep _ _) => apply ctx_morph_big_sepM; intros ? ?
  | |- CtxMorph (λ ξ, big_opS bi_sep _ _) => apply ctx_morph_big_sepS; intros ?
  | |- CtxMorph (λ ξ, if _ then _ else _) => apply ctx_morph_if
  | |- CtxMorph (λ ξ, ctx_pointsto ξ _ _ _) => apply ctx_morph_pointsto
  | |- CtxMorph (λ ξ, ctx_floor ξ _) => apply _
  | |- CtxMorph (λ ξ, ctx_word_pointsto ξ _ _ _) => apply ctx_morph_word
  | |- CtxMorph (λ ξ, ctx_word2_pointsto ξ _ _ _) => apply ctx_morph_word2
  | |- CtxMorph (λ ξ, ctx_word4_pointsto ξ _ _ _) => apply ctx_morph_word4
  | |- CtxMorph (λ ξ, ctx_phys_pointsto ξ _ _ _) => apply ctx_morph_phys_pointsto
  | |- CtxMorph (λ ξ, ctx_phys_word_pointsto ξ _ _ _) => apply ctx_morph_phys_word
  | |- _ => apply _
  end.
Ltac ctx_morph_solve := repeat ctx_morph_step.
