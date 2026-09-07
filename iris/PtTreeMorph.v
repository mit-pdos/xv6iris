(* PtTreeMorph: the user-tier page-table tree moves between contexts.

   A6.128.  [PtTree.ptree_own_at (UTier ξ)] owns a process's page-table
   pages as [ctx_phys_word_pointsto ξ] slots; the zombie park's payload
   ([ProcDefs.proc_dormant_noctx] → [ProcPtOwn.proc_pt] → [pt_frame])
   carries one, and transport along domination ([TsoCtx.CtxMorph], the
   one transport class) has to carry it from the parker's context to the
   target's.  The tree is recursive in the level, so its instance is an
   induction rather than a [ctx_morph_solve] run; everything under it is
   structural. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import TsoCtx CtxMorphTac PtTree.

(* The tree along DOMINATION ([CtxMorph], the one transport class): a
   dormant slot's page table rides p->lock's payload, and rides the
   same-hart move ([TsoCtx.ctx_move]) at swtch. *)
Section PtTreeMorph.
  Context `{!riscvGS Σ}.

  Global Instance pt_slot_own_morph a dq w :
    CtxMorph (λ ξ, pt_slot_own (UTier ξ) a dq w).
  Proof. rewrite /pt_slot_own; cbn. ctx_morph_solve. Qed.

  Global Instance pt_page_own_at_morph dq t :
    CtxMorph (λ ξ, pt_page_own_at (UTier ξ) dq t).
  Proof. rewrite /pt_page_own_at. ctx_morph_solve. Qed.

  Lemma ptree_own_at_morph_l (lvl : nat) :
    ∀ dq t, CtxMorph (λ ξ, ptree_own_at (UTier ξ) lvl dq t).
  Proof.
    induction lvl as [|lvl IH]; intros dq t; cbn [ptree_own_at].
    - ctx_morph_solve.
    - apply ctx_morph_sep; [apply _ |].
      apply ctx_morph_big_sepL; intros i x; cbv beta.
      destruct (pt_kids t (mword_of_int x)) as [c |]; [apply IH | apply ctx_morph_const].
  Qed.
  Global Instance ptree_own_at_morph lvl dq t :
    CtxMorph (λ ξ, ptree_own_at (UTier ξ) lvl dq t) := ptree_own_at_morph_l lvl dq t.

  Global Instance pt_kids_own_at_morph lvl dq t :
    CtxMorph (λ ξ, pt_kids_own_at (UTier ξ) lvl dq t).
  Proof.
    rewrite /pt_kids_own_at. apply ctx_morph_big_sepL; intros i x; cbv beta.
    destruct (pt_kids t (mword_of_int x)) as [c |]; [apply _ | apply ctx_morph_const].
  Qed.

  Global Instance pt_frame_at_morph (S : ptree -> Prop) :
    CtxMorph (λ ξ, pt_frame_at (UTier ξ) S).
  Proof. rewrite /pt_frame_at. ctx_morph_solve. Qed.
End PtTreeMorph.
