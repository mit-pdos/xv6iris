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
    iModIntro. iExists inhabitant. rewrite own_context_unseal /own_context_def. by iLeft.
  Qed.

  (* THE TOKENS AT A NAMED CONTEXT -- main's SC stub only (main-tso-readiness
     Amendment 6; FALSE at TSO, where each context has ONE token).  Two
     consumers, both structural: a forked child's record is stated at its
     PARKER's context ([ProofForkretPark], the record's [ctx_parked]), and
     the seven secondary harts run at the boot carve's context
     ([SystemAdequacy]).  Both exist because main's T-leg trap tier cannot
     restate [procs_inv] at a fresh context; at cutover these two sites ARE
     the fork/boot items of the M2 worklist. *)
  Lemma own_context_any `{CID : CpuId} (ξ : CtxId) : ⊢@{iPropI Σ} own_context ξ.
  Proof. rewrite own_context_unseal /own_context_def. by iLeft. Qed.
  Lemma ctx_parked_any (ξ : CtxId) (T : nat) : ⊢@{iPropI Σ} ctx_parked ξ T.
  Proof. rewrite ctx_parked_unseal /ctx_parked_def. by iLeft. Qed.

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

  (* THE CREATOR'S WITNESS AT ANY POSITION -- SC ONLY (main-tso-readiness
     Amendment 8, §5.1).  Under TSO a lock creator's floor is the dirty-write
     witness its own mint store registered ([TsoCtx.ctx_wrote_register] at
     the store leaf, tso-flip WpSconfMem.v's [wp_sd_zero_wpay_s_sconf]); at
     SC the registration is a ghost step with a trivial body, and this lemma
     is that step with the leaf left out.  FALSE at TSO.  Its clients are the
     lock creators' floors; when the shim burns, each is a compile error
     naming a creator whose witness must then come from its own store. *)
  Lemma ctx_wrote_any (ξ : CtxId) (t : nat) (a : Arch.pa) :
    ⊢@{iPropI Σ} ctx_wrote ξ t a.
  Proof. rewrite ctx_wrote_unseal /ctx_wrote_def. done. Qed.

  (* THE ACQUIRER'S FLOOR AT THE RECORD'S STAMP -- SC ONLY.  Under TSO the
     AMO leaf mints it: the winning AMO takes the hart's view to the log top
     and [TsoCtx.hart_view_lb_get] + [ctx_bound_raise] floor the running
     token at the parked record's stamp (tso-flip WpSconfLock.v's winner
     arm, A6.120).  At SC the floor is trivial and this lemma is that mint
     with the interp left out; FALSE at TSO.  Its one client is the AMO leaf's
     [WpLock.lock_pay_won] (WpSconfLock). *)
  Lemma ctx_floor_any (ξ : CtxId) (lo : nat) : ⊢@{iPropI Σ} ctx_floor ξ lo.
  Proof. rewrite ctx_floor_unseal /ctx_floor_def. done. Qed.

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

  (* THE PHYSICAL-TIER BRIDGES (the U-mode threading): the registered
     physical byte/word against the raw [↦ₚ]/[↦ₚ₈].  Same charter as
     [ctx_word_shim] -- at TSO the registered cell carries a stamp and a
     justification a raw cell cannot conjure, so these die with the file
     and each surviving import is an unconverted construction site
     (page-table build/free, the process image's carve). *)
  Lemma ctx_phys_shim (ξ : CtxId) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    ctx_phys_pointsto ξ a dq v ⊣⊢ phys_pointsto a dq v.
  Proof. rewrite ctx_phys_pointsto_unseal. done. Qed.

  Lemma ctx_phys_of_mem (ξ : CtxId) a dq v :
    phys_pointsto a dq v -∗ ctx_phys_pointsto ξ a dq v.
  Proof. rewrite ctx_phys_shim. auto. Qed.

  Lemma ctx_phys_to_mem (ξ : CtxId) a dq v :
    ctx_phys_pointsto ξ a dq v -∗ phys_pointsto a dq v.
  Proof. rewrite ctx_phys_shim. auto. Qed.

  Lemma ctx_phys_word_shim (ξ : CtxId) (a : Arch.pa) (dq : dfrac) (w : bv 64) :
    ctx_phys_word_pointsto ξ a dq w ⊣⊢ phys_word_pointsto a dq w.
  Proof.
    rewrite /ctx_phys_word_pointsto /phys_word_pointsto.
    apply bi.sep_proper; [done|].
    apply big_opL_proper. intros ? j ?. apply ctx_phys_shim.
  Qed.

  Lemma ctx_phys_word_of_mem (ξ : CtxId) a dq w :
    phys_word_pointsto a dq w -∗ ctx_phys_word_pointsto ξ a dq w.
  Proof. rewrite ctx_phys_word_shim. auto. Qed.

  Lemma ctx_phys_word_to_mem (ξ : CtxId) a dq w :
    ctx_phys_word_pointsto ξ a dq w -∗ phys_word_pointsto a dq w.
  Proof. rewrite ctx_phys_word_shim. auto. Qed.

  (* the byte-RUN form of the physical bridge: what a page build hands
     over (kalloc's zeroed page becoming a PT node or a process page) *)
  Lemma ctx_phys_run_of_mem (ξ : CtxId) (f : nat -> Arch.pa)
      (g : nat -> bv 8) (n : nat) (dq : dfrac) :
    ([∗ list] j ∈ seq 0 n, phys_pointsto (f j) dq (g j)) -∗
    ([∗ list] j ∈ seq 0 n, ctx_phys_pointsto ξ (f j) dq (g j)).
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k j _) "Hj". iApply (ctx_phys_of_mem with "Hj").
  Qed.

  Lemma ctx_phys_run_to_mem (ξ : CtxId) (f : nat -> Arch.pa)
      (g : nat -> bv 8) (n : nat) (dq : dfrac) :
    ([∗ list] j ∈ seq 0 n, ctx_phys_pointsto ξ (f j) dq (g j)) -∗
    ([∗ list] j ∈ seq 0 n, phys_pointsto (f j) dq (g j)).
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (k j _) "Hj". iApply (ctx_phys_to_mem with "Hj").
  Qed.

  (* THE 2- AND 4-BYTE WORD BRIDGES (M1 flip stage 2): the flipped
     [↦₂]/[↦₄] against the kit's raw word facts.  Same charter as
     [ctx_word_shim] above -- the leaf/gen_heap conversion, one line, dead
     at cutover with the file. *)
  Lemma ctx_word2_shim (KTR : CurKtier) (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (w : bv 16) :
    ctx_word2_pointsto (KTR := KTR) ξ a dq w
    ⊣⊢ word2_pointsto (KTR := KTR) a dq w.
  Proof.
    (* main has no [word2_pointsto_unfold] -- the M-leg's spelling.  Its
       word2 is a plain transparent Definition (RiscvPtsto.v:1527) and only
       the word4 tier ever needed the named unfolding, so delta does here
       what the lemma does there.  Slice 1 stays purely ADDITIVE: adding the
       missing lemma to RiscvPtsto would edit an existing file for nothing. *)
    rewrite /ctx_word2_pointsto /word2_pointsto.
    apply bi.sep_proper; [done|].
    apply big_opL_proper. intros ? j ?. apply ctx_pointsto_shim.
  Qed.

  Lemma ctx_word2_of_mem (KTR : CurKtier) (ξ : CtxId) a dq w :
    word2_pointsto (KTR := KTR) a dq w -∗
    ctx_word2_pointsto (KTR := KTR) ξ a dq w.
  Proof. rewrite ctx_word2_shim. auto. Qed.

  Lemma ctx_word2_to_mem (KTR : CurKtier) (ξ : CtxId) a dq w :
    ctx_word2_pointsto (KTR := KTR) ξ a dq w -∗
    word2_pointsto (KTR := KTR) a dq w.
  Proof. rewrite ctx_word2_shim. auto. Qed.

  Lemma ctx_word4_shim (KTR : CurKtier) (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (w : bv 32) :
    ctx_word4_pointsto (KTR := KTR) ξ a dq w
    ⊣⊢ word4_pointsto (KTR := KTR) a dq w.
  Proof.
    rewrite /ctx_word4_pointsto word4_pointsto_unfold.
    apply bi.sep_proper; [done|].
    apply big_opL_proper. intros ? j ?. apply ctx_pointsto_shim.
  Qed.

  Lemma ctx_word4_of_mem (KTR : CurKtier) (ξ : CtxId) a dq w :
    word4_pointsto (KTR := KTR) a dq w -∗
    ctx_word4_pointsto (KTR := KTR) ξ a dq w.
  Proof. rewrite ctx_word4_shim. auto. Qed.

  Lemma ctx_word4_to_mem (KTR : CurKtier) (ξ : CtxId) a dq w :
    ctx_word4_pointsto (KTR := KTR) ξ a dq w -∗
    word4_pointsto (KTR := KTR) a dq w.
  Proof. rewrite ctx_word4_shim. auto. Qed.

  (* THE 4-BYTE CELL RE-INDEX (M1 flip stage 2; the sibling of
     [SwtchCtx.ctx_cells_reindex] and [StackOwn.stack_own_reindex]).

     WHY IT EXISTS, and it is a NEW worklist entry that stage 2 creates.  An
     escrow-backed cell comes out of the record at the RECORD's ξ, and the
     store leaf's atomic update wants it at the ACTING thread's.  The honest
     transport is [TsoCtx.ctx_absorb], but §0.17′'s measured rule forbids it
     here: no absorb and no deposit can run inside a [wp_..._au_...], because
     the bundle carrying [own_context] has already gone to the leaf, and the
     escrow at a recycler store must be opened INSIDE the update (the store
     and the swap are one atomic step).  So the SC-only re-index stands in,
     quarantined here; at cutover each use is a racy-kit entry, and the fix
     is the state-indexed held arm §0.18′ prices. *)
  Lemma ctx_word4_reindex (KTR : CurKtier) (ξ ξ' : CtxId) a dq w :
    ctx_word4_pointsto (KTR := KTR) ξ a dq w -∗
    ctx_word4_pointsto (KTR := KTR) ξ' a dq w.
  Proof. rewrite !ctx_word4_shim. auto. Qed.

  Lemma ctx_word_reindex (KTR : CurKtier) (ξ ξ' : CtxId) a dq w :
    ctx_word_pointsto (KTR := KTR) ξ a dq w -∗
    ctx_word_pointsto (KTR := KTR) ξ' a dq w.
  Proof. rewrite !ctx_word_shim. auto. Qed.

  Lemma ctx_word2_reindex (KTR : CurKtier) (ξ ξ' : CtxId) a dq w :
    ctx_word2_pointsto (KTR := KTR) ξ a dq w -∗
    ctx_word2_pointsto (KTR := KTR) ξ' a dq w.
  Proof. rewrite !ctx_word2_shim. auto. Qed.

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

  (* ------------------------------------------------------------------- *)
  (* THE FREE RUNNING TOKEN (SC-only).  The M-leg [own_context] body is    *)
  (* [True ∨ …], so the token is mintable at ANY context on this leg.      *)
  (* Every use of these two marks a seam where the T-leg needs a REAL       *)
  (* token source (the thread's own, borrowed from the residue it parked   *)
  (* -- UsertrapRes.ut_trap_parked's conjunct -- or threaded down from the  *)
  (* caller): the grep for them is the cutover worklist for the U-mode     *)
  (* funnel, exactly like this file's other bridges.                        *)
  (* ------------------------------------------------------------------- *)
  Lemma own_context_sc `{CID : CpuId} (ξ : CtxId) : ⊢ own_context ξ.
  Proof. rewrite own_context_unseal /own_context_def. by iLeft. Qed.

  (* the [UserActiveClass.Rut_ctx]-shaped borrow accessor, for a residue    *)
  (* nobody can open (a quantified [Rut]): mint the token, drop the one     *)
  (* handed back.  T-leg: the accessor must come from the concrete residue. *)
  Lemma rut_ctx_sc `{CID : CpuId} (ξ : CtxId) (P : iProp Σ) :
    ⊢ P -∗ own_context ξ ∗ (own_context ξ -∗ P).
  Proof.
    iIntros "HP". iSplitR; [ iApply own_context_sc |]. iIntros "_". iExact "HP".
  Qed.
End shim.
