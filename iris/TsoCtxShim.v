(* TsoCtxShim.v -- THE ONE-TIME MIGRATION SHIM.  BURNED AT CUTOVER.

   The ONLY place in the tree allowed to state that a context-indexed
   fact and a plain fact are the same thing.  At SC they are
   (`TsoCtx.ctx_pointsto` ignores its index UNDER THE SEAL), and the M
   sweeps convert the tree one file at a time, so every
   converted/unconverted boundary needs the conversion stated somewhere.
   It is stated HERE and nowhere else, so that at cutover -- when
   `ctx_pointsto` becomes the TSO ledger fact and these equivalences
   become FALSE -- deleting this one file finds every remaining
   unconverted boundary as a compile error, which is the honest worklist
   of what is left.

   Consequently: a converted file may import this shim ONLY to talk to a
   not-yet-converted neighbour.  A converted file whose callers and
   callees are all converted must not import it; import of this file IS
   the tree's list of open seams (grep for TsoCtxShim).

   See claude-notes/projects/tso-port.md ("no context-irrelevance
   escapes" -- this file is the sanctioned, quarantined exception). *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.Base SailStdpp.Values.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoCtx.

Section shim.
  Context `{!riscvGS Σ}.
  (* CUTOVER REHEARSAL: the surface is now HERMETICALLY sealed
     (TsoCtx's [_unseal] equations are the only way through); this file
     unseals BY NAME, which is its whole charter. *)

  (* THE SWEEP-ERA THROWAWAY MINT.  A converted callee demands a context
     token its unconverted caller does not have, so the call site conjures
     one ([ProofBalloc.v] is the reference diff).  Under the corrected TSO
     construction this mint is actually satisfiable
     ([TsoCtxTwin2.twin_run_alloc]) -- but it stays HERE, not in the
     surface, because a conjured context is useless once [ctx_pointsto]
     is real (its facts arrive through this file's [ctx_buf_of_mem], the
     genuinely SC-only step): when the shim burns, each such site is a
     caller whose own conversion is the remaining work. *)
  Lemma own_context_alloc `{CID : CpuId} : ⊢ |==> ∃ ξ : CtxId, own_context ξ.
  Proof.
    iMod (ghost_var_alloc (0%fin : CPU)) as (γ) "Hv".
    iModIntro. iExists (MkCtxId γ inhabitant).
    rewrite own_context_unseal /own_context_def.
    iExists (0%fin : CPU). iExact "Hv".
  Qed.

  (* THE RESUME-EVIDENCE STOPGAP.  [ctx_resume]/[ctx_exchange] want the
     stable pair "view receipt K, parked stamp ≤ K"; the honest producer
     is the resuming hart's p->lock ACQUIRE ([TsoCtxTwin2.twin_passed_get])
     and the M2 sweep threads it from [SpecAcquire] to [ProofSwtch].
     Until then this SC-only intro discharges it -- FALSE at TSO (a view
     receipt cannot be conjured), hence quarantined here: at cutover the
     compile errors it leaves ARE the M2 worklist. *)
  Lemma hart_view_lb_any `{CID : CpuId} (K : nat) :
    ⊢@{iPropI Σ} hart_view_lb K.
  Proof. rewrite hart_view_lb_unseal /hart_view_lb_def. done. Qed.

  (* THE TRANSPORT-EVIDENCE STOPGAP.  [ctx_dom ξ ξ'] licenses moving facts
     from ξ to ξ'; at TSO it is minted only against real synchronization
     evidence (the lock lemmas' AMO-at-the-top, [TsoCtxTwin2]'s two mints)
     and carries ξ's own authorities -- it can never be conjured.  Until
     the cutover kit proves the lock internals against the TSO machine,
     the SC lock proofs ([ProofAcquire]'s context tier) mint it here.
     FALSE at TSO; dies with the shim; each leftover use is a lock-kit
     worklist entry. *)
  Lemma ctx_dom_sc (ξ ξ' : CtxId) : ⊢@{iPropI Σ} ctx_dom ξ ξ'.
  Proof. rewrite ctx_dom_unseal /ctx_dom_def. done. Qed.

  Lemma ctx_pointsto_shim (KTR : CurKtier) (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    ctx_pointsto (KTR := KTR) ξ a dq v ⊣⊢ mem_pointsto (KTR := KTR) a dq v.
  Proof. rewrite ctx_pointsto_unseal. reflexivity. Qed.

  (* the two wand directions, for plain proofmode plumbing *)
  Lemma ctx_pointsto_of_mem (KTR : CurKtier) (ξ : CtxId) a dq v :
    mem_pointsto (KTR := KTR) a dq v -∗ ctx_pointsto (KTR := KTR) ξ a dq v.
  Proof. rewrite ctx_pointsto_shim. auto. Qed.

  Lemma ctx_pointsto_to_mem (KTR : CurKtier) (ξ : CtxId) a dq v :
    ctx_pointsto (KTR := KTR) ξ a dq v -∗ mem_pointsto (KTR := KTR) a dq v.
  Proof. rewrite ctx_pointsto_shim. auto. Qed.

  (* THE WORD BRIDGE (M1 flip stage 1): the flipped [↦₈] against the
     kit's raw word fact.  The leaf proofs' one-line conversion; dies at
     cutover with the file. *)
  Lemma ctx_word_shim (KTR : CurKtier) (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (w : bv 64) :
    ctx_word_pointsto (KTR := KTR) ξ a dq w
    ⊣⊢ word_pointsto (KTR := KTR) a dq w.
  Proof.
    rewrite /ctx_word_pointsto word_pointsto_unfold.
    apply bi.sep_proper; [done|].
    apply big_opL_proper. intros ? j ?. apply ctx_pointsto_shim.
  Qed.

  Lemma ctx_word_of_mem (KTR : CurKtier) (ξ : CtxId) a dq w :
    word_pointsto (KTR := KTR) a dq w -∗
    ctx_word_pointsto (KTR := KTR) ξ a dq w.
  Proof. rewrite ctx_word_shim. auto. Qed.

  Lemma ctx_word_to_mem (KTR : CurKtier) (ξ : CtxId) a dq w :
    ctx_word_pointsto (KTR := KTR) ξ a dq w -∗
    word_pointsto (KTR := KTR) a dq w.
  Proof. rewrite ctx_word_shim. auto. Qed.

  (* the ∃-slot forms the stack-frame hand-offs trade in (a frame slot
     whose value nobody names) *)
  Lemma ctx_eslot_of_mem (KTR : CurKtier) (ξ : CtxId) (a : Arch.pa) :
    (∃ w : bv 64, word_pointsto (KTR := KTR) a (DfracOwn 1) w) -∗
    ∃ w : mword 64, ctx_word_pointsto (KTR := KTR) ξ a (DfracOwn 1) w.
  Proof.
    iIntros "[%w Hw]". iExists w. iApply (ctx_word_of_mem with "Hw").
  Qed.

  Lemma ctx_eslot_to_mem (KTR : CurKtier) (ξ : CtxId) (a : Arch.pa) :
    (∃ w : mword 64, ctx_word_pointsto (KTR := KTR) ξ a (DfracOwn 1) w) -∗
    ∃ w : bv 64, word_pointsto (KTR := KTR) a (DfracOwn 1) w.
  Proof.
    iIntros "[%w Hw]". iExists w. iApply (ctx_word_to_mem with "Hw").
  Qed.

  (* the [∗ list] window form the buffer specs trade in *)
  Lemma ctx_buf_of_mem (KTR : CurKtier) (ξ : CtxId)
      (p : Arch.pa) (len : nat) (f : nat -> bv 8) (dq : dfrac) :
    ([∗ list] j ∈ seq 0 len, mem_pointsto (KTR := KTR) (pa_add p j) dq (f j))
    -∗
    ([∗ list] j ∈ seq 0 len,
       ctx_pointsto (KTR := KTR) ξ (pa_add p j) dq (f j)).
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_of_mem.
  Qed.

  Lemma ctx_buf_to_mem (KTR : CurKtier) (ξ : CtxId)
      (p : Arch.pa) (len : nat) (f : nat -> bv 8) (dq : dfrac) :
    ([∗ list] j ∈ seq 0 len,
       ctx_pointsto (KTR := KTR) ξ (pa_add p j) dq (f j))
    -∗
    ([∗ list] j ∈ seq 0 len, mem_pointsto (KTR := KTR) (pa_add p j) dq (f j)).
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_to_mem.
  Qed.
End shim.
