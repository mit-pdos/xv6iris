(* THREE FILES, ONE SECTION -- CUT FOR THE BUILD'S CRITICAL PATH.  This
   file is the VOCABULARY every context-indexed proof needs: the identity,
   the surface facts and their seal, the word towers, [CtxMorph], the
   pristine/physical/ledger DEFINITIONS with their cheap laws, and the
   notations.  It is imported by ~1000 files and sits at the root of both
   routes through the build, so every sentence here is on the critical path.
   The gate PROOFS -- each a multi-second induction -- live in two siblings
   that re-open the same [Section ctx]:

     - [TsoCtxStore.v]  the store gates ([ctx_store_ok], [ctx_store_win_*],
                        [ledger_store_*]) that the M-mode store leaf, the
                        S-mode page-table core and the sconf memory leaf
                        consume;
     - [TsoCtxLedger.v] the pin / wpay / rpay / pinw mints and drops, the
                        relaxed and racy reads, the x-stamp lemmas -- the
                        device drivers' and the boot carve's gates.

   A new lemma goes in the LAST of the three whose imports it needs, and a
   cheap law over a definition here stays here.  A file needs the sibling
   only if it names one of the sibling's lemmas; [Require Import TsoCtx]
   alone is the common case.  The cut was chosen by dependency closure over
   the build's .glob files (claude-notes/optimization.md, "Build shape"). *)
(* TsoCtx.v -- THE CONTEXT SURFACE, REAL (TSO) INSTANTIATION.

   The TSO port's ownership interface Sigma
   ([claude-notes/projects/tso-port.md], legs M and C): every memory
   points-to fact is indexed by a CONTEXT -- a ghost identity for a thread
   of control -- and the ONLY ways a fact changes context are the exported
   transport laws.  UNTIL THE MACHINE FLIP the definitions below ignored
   the index under the seal; NOW ([claude-notes/projects/
   tso-machine-flip.md] §5) they are the TsoCtxTwin2 construction wired
   to the live machine ghosts ([TsoGhost.v] at [riscvEraGS]'s era names,
   over the Ztso semantics of [RiscvLang.mnode_step]):

     - [ctx_pointsto ξ a dq v] is mem_pointsto's body PLUS the byte's
       latest-write TIMESTAMP (a [ts_name] fragment at the fact's own
       dq) PLUS the clean/dirty BIT: clean = a persistent lower bound of
       ξ's own bound covering the timestamp; dirty = a fragment of ξ's
       own dirty set at (t, pa).
     - [own_context ξ] is THE TIE between the CPU's view and the context
       object: both of ξ's authorities (its bound, its dirty set), a
       stable view receipt of the AMBIENT hart dominating the bound
       ([view_lb (hart_agent cpu_id) K] with [B ≤ K] -- every clean fact
       of mine is visible on the hart I am running on), and the per-entry
       justification of the dirty set (mine-on-this-hart, or under the
       bound).
     - [ctx_parked ξ T]: the authorities with no hart tie; the bound IS
       the stamp (park raised it past every dirty entry).
     - [hart_view_lb K] = [view_lb] at the ambient hart: the persistent,
       monotone acquire receipt.
     - [ctx_dom ξ ξ'] carries HALF of ξ's authorities plus a bound-lb of
       ξ' dominating ξ's bound and dirty watermark -- statable with no
       machine state, which is what makes [CtxMorph]'s bare shape true
       as written.

   Every law below was first proven of the self-contained twin
   ([TsoCtxTwin2.v], kept as the discovery record); the twin lemma is
   named beside each.  The kit-facing gates at the bottom (the load
   gate, the view-receipt mint, the acquire-side domination mint) are
   what the leaf re-proofs against the Ztso machine consume.

   THE THREE RULINGS THIS FILE ENCODES (owner-ratified) are unchanged:

   1. [CurCtx] IS AMBIENT, LIKE [CpuId] AND [CurKtier]: a file binds its
      context once ([Context `{XI : CurCtx}]) and its spec text does not
      change.  There is deliberately NO default instance.

   2. THE CONTEXT RIDES IN [sie_cap_gpr]: the ambient kernel-execution
      bundle carries [own_context cur_ctx], so no proof threads a NEW
      separation-logic resource, and [wp_next]'s continuation re-anchors
      [CpuId] while cur_ctx STAYS.  [own_context] is what ties the
      context to the current CPU's view state -- now for real.

   3. NO CONTEXT-IRRELEVANCE ESCAPES: a lemma of the shape
      [ctx_pointsto ξ ⊣⊢ ctx_pointsto ξ'] is FALSE here and must never
      exist above the seal.  (The SC-era shim equivalences died with the
      SC bodies; TsoCtxShim.v is a TOMBSTONE since A6.86.)

   THE SEAL IS STILL HERMETIC (the cutover-rehearsal sig-projection
   idiom): the five surface facts are Qed-opaque, each with a named
   [_unseal] equation.  The licensed unseal set grows from {this file's
   law proofs, TsoCtxShim} to include the BELOW-Σ kit re-proofs (the
   load/store leaves, the lock internals) -- they are the instantiation,
   not clients. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_var ghost_map mono_nat gen_heap.
(* SailStdpp.Base is deliberately ABSENT (the SC file imported it): it
   exports [Countable_mword]/[Decidable_eq_mword], which would make every
   [gmap]/[ghost_map] over [Arch.pa] in THIS file elaborate at the Sail
   key instances while [TsoGhost]'s classes carry stdpp's -- the
   riscvF_kmapGS trap, live.  [Values] alone does not export them. *)
Require Import SailStdpp.Values.
Require Import SailStdpp.Operators_mwords.  (* [uint]; exports no mword key instances *)
Require Import Riscv.rv64d_types Riscv.rv64d.   (* [is_aligned_paddr]/[Physaddr]: the word tower's alignment vocabulary *)
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoMemPa TsoGhost.

(* ------------------------------------------------------------------ *)
(* The context identity and the ambient class                          *)
(* ------------------------------------------------------------------ *)

(* TWO GNAMES, BOTH THE CONTEXT'S OWN ([TsoCtxTwin2.CtxId] is the same
   record): the BOUND authority (one monotone nat -- clean facts'
   justification) and the DIRTY-SET authority (a ghost map keyed by
   (timestamp, byte)).  The identity carrying its own ghost names is
   what lets a token -- and hence every authority -- be minted wherever
   the identity can, with no global roster: the corrected construction's
   cornerstone. *)
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

(* ---------------------------------------------------------------------- *)
(* [pa_add] IS INJECTIVE IN ITS INDEX -- the kit needs it for exactly one   *)
(* thing (A6.16): a store's window has DISTINCT addresses, so the byte LIST *)
(* a leaf holds and the message's byte MAP the log records are one and the  *)
(* same resource.  [VirtioQueue.pa_add_inj] is this fact, but that file     *)
(* sits far above the kit; these are LOCAL so the names cannot collide      *)
(* there.                                                                  *)
(* ---------------------------------------------------------------------- *)
Local Lemma tso_add_vec_unsigned (x y : SailStdpp.Values.mword 64) :
  bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, SailStdpp.Values.to_word,
    SailStdpp.Values.get_word, MachineWord.MachineWord.add.
  rewrite bv_add_unsigned. reflexivity.
Qed.

Local Lemma tso_moi_unsigned (k : Z) :
  bv_unsigned (SailStdpp.Values.mword_of_int k : SailStdpp.Values.mword 64)
  = bv_wrap 64 k.
Proof.
  unfold SailStdpp.Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* the [: mword 64] ascription is load-bearing: [pa_add] lands in [Arch.pa],
   whose width is an unreduced [Z_idx] match, and [bv_unsigned] would
   elaborate at THAT width (they print identically and then fail to
   rewrite) -- VirtioQueue.v's own note, kept. *)
Local Lemma tso_pa_add_unsigned (a : Arch.pa) (j : nat) :
  bv_unsigned (pa_add a j : SailStdpp.Values.mword 64)
  = bv_wrap 64 (bv_unsigned (a : SailStdpp.Values.mword 64) + Z.of_nat j).
Proof.
  unfold pa_add, add_vec_int.
  rewrite tso_add_vec_unsigned tso_moi_unsigned bv_wrap_add_idemp_r.
  reflexivity.
Qed.

Local Lemma tso_mod64 : bv_modulus 64 = 18446744073709551616%Z.
Proof. vm_compute. reflexivity. Qed.

Local Lemma tso_wrap_cancel (u i j : Z) :
  (0 <= i < 18446744073709551616)%Z -> (0 <= j < 18446744073709551616)%Z ->
  ((u + i) `mod` 18446744073709551616 = (u + j) `mod` 18446744073709551616)%Z ->
  i = j.
Proof.
  intros Hi Hj Heq.
  assert (Hd : ((i - j) `mod` 18446744073709551616 = 0)%Z).
  { replace (i - j)%Z with ((u + i) - (u + j))%Z by lia.
    rewrite Zminus_mod Heq Z.sub_diag. reflexivity. }
  apply Z.mod_divide in Hd; [| lia ].
  destruct Hd as [k Hk]. nia.
Qed.

Lemma tso_pa_add_inj (a : Arch.pa) (i j : nat) :
  (Z.of_nat i < 18446744073709551616)%Z ->
  (Z.of_nat j < 18446744073709551616)%Z ->
  pa_add a i = pa_add a j -> i = j.
Proof.
  intros Hi Hj Heq.
  assert (Hu : bv_unsigned (pa_add a i : SailStdpp.Values.mword 64)
               = bv_unsigned (pa_add a j : SailStdpp.Values.mword 64))
    by (by rewrite Heq).
  rewrite !tso_pa_add_unsigned in Hu. unfold bv_wrap in Hu.
  rewrite tso_mod64 in Hu.
  assert (Hz : Z.of_nat i = Z.of_nat j)
    by (apply (tso_wrap_cancel (bv_unsigned (a : SailStdpp.Values.mword 64)));
        [ lia | lia | exact Hu ]).
  lia.
Qed.

(* THE WINDOW'S OFFSET, RECOVERED FROM THE ADDRESS.  A window payload is
   held as a LIST indexed by offset and stored through a MAP keyed by
   address ([wpay_map_own]), so the two spellings have to be bridged --
   and [pa_add] is injective on the window ([tso_pa_add_inj]) but not
   computably invertible.  The residue mod 2^64 IS the inverse, and it
   needs no no-wrap side condition because the outer [mod] absorbs the
   wrap the window's own addition may have done. *)
(* A6.119: EXPORTED, not duplicated.  The lock word's value-set pin is the
   first client of the pinned-window store gate, and that gate's [Sg] premise
   is exactly this bridge -- offset-keyed sets re-keyed by address.  The law
   was here; only [Local] stood between it and its first caller. *)
Definition tso_pa_off (base a : Arch.pa) : nat :=
  Z.to_nat ((bv_unsigned (a : SailStdpp.Values.mword 64)
             - bv_unsigned (base : SailStdpp.Values.mword 64))
            `mod` 18446744073709551616)%Z.

Lemma tso_pa_off_add (base : Arch.pa) (j : nat) :
  (Z.of_nat j < 18446744073709551616)%Z ->
  tso_pa_off base (pa_add base j) = j.
Proof.
  intros Hj.
  rewrite /tso_pa_off tso_pa_add_unsigned /bv_wrap tso_mod64.
  rewrite Zminus_mod_idemp_l.
  replace (bv_unsigned (base : SailStdpp.Values.mword 64) + Z.of_nat j
           - bv_unsigned (base : SailStdpp.Values.mword 64))%Z
    with (Z.of_nat j) by lia.
  rewrite Z.mod_small; [ apply Nat2Z.id | lia ].
Qed.

Lemma tso_foldr_ins_dom {A} (l : list nat) (pa : Arch.pa)
    (f : nat -> A) (mm : gmap Arch.pa A) :
  dom (foldr (fun j acc => <[pa_add pa j := f j]> acc) mm l)
  = list_to_set (pa_add pa <$> l) ∪ dom mm.
Proof.
  induction l as [|j l IH].
  - cbn [foldr fmap list_fmap list_to_set]. set_solver.
  - cbn [foldr fmap list_fmap list_to_set]. rewrite dom_insert_L IH. set_solver + mm.
Qed.

Lemma tso_nodup_win (pa : Arch.pa) (k : nat) :
  (Z.of_nat k <= 18446744073709551616)%Z ->
  base.NoDup (pa_add pa <$> seq 0 k).
Proof.
  intros Hk. apply NoDup_fmap_2_strong; [| apply NoDup_seq].
  intros i j Hi Hj Heq. apply elem_of_seq in Hi. apply elem_of_seq in Hj.
  apply (tso_pa_add_inj pa i j); [ lia | lia | exact Heq ].
Qed.

Section ctx.
  Context `{!riscvGS Σ}.

  (* ---------------------------------------------------------------- *)
  (* The per-context authorities                                       *)
  (* ---------------------------------------------------------------- *)

  (* Both authorities at a fraction ([TsoCtxTwin2.ctx_at]): the halves
     are what [ctx_dom] borrows; agreement across halves is what pins
     the borrow. *)
  Definition ctx_at (ξ : CtxId) (q : Qp) (B : nat)
      (D : gset (nat * Arch.pa)) : iProp Σ :=
    (mono_nat_auth_own (ctx_bound_name ξ) q B ∗
     dset_auth (ctx_dirty_name ξ) q D)%I.

  Lemma ctx_at_halves ξ B D :
    ctx_at ξ 1 B D ⊣⊢ ctx_at ξ (1/2) B D ∗ ctx_at ξ (1/2) B D.
  Proof.
    rewrite /ctx_at.
    rewrite (fractional_half (mono_nat_auth_own (ctx_bound_name ξ) 1 B)).
    rewrite (dset_halves (ctx_dirty_name ξ) D).
    iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"].
  Qed.

  Lemma ctx_at_agree ξ q1 q2 B1 D1 B2 D2 :
    ctx_at ξ q1 B1 D1 -∗ ctx_at ξ q2 B2 D2 -∗ ⌜B1 = B2 ∧ D1 = D2⌝.
  Proof.
    iIntros "[Hb1 Hd1] [Hb2 Hd2]".
    iDestruct (mono_nat_auth_own_agree with "Hb1 Hb2") as %[_ ?].
    iDestruct (dset_agree with "Hd1 Hd2") as %?.
    by iPureIntro.
  Qed.

  (* [TsoGhost.llb_valid] at a FRACTION of the authority.  [ctx_dom] holds
     half of the bound authority ([ctx_at ξ (1/2) …]) and still has to read
     the clean arm off a fact, so the whole-authority form does not serve.
     Same proof; [mono_nat_lb_own_valid] is fraction-generic already. *)
  Local Lemma llb_valid_q (γ : gname) (q : Qp) (n K : nat) :
    mono_nat_auth_own γ q n -∗ llb γ K -∗ ⌜(K ≤ n)%nat⌝.
  Proof.
    iIntros "Ha [Hlb|%Hz]".
    - by iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ ?].
    - iPureIntro. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* own_context: the running-thread token -- THE TIE                  *)
  (* ---------------------------------------------------------------- *)

  (* THE RUNNING TOKEN: "this hart is running as ξ"
     ([TsoCtxTwin2.own_context] at the ambient hart).  Both of ξ's
     authorities; the stable view receipt tying the bound to THIS
     hart's view ([B ≤ K] and [view_lb (hart_agent cpu_id) K] --
     forever, since views only grow: every clean fact of mine is
     visible here); the dirty watermark [W] (every dirty timestamp is a
     legal log position at most W -- what lets park and fork stamp
     without the interp); and the per-entry justification (my own
     message on THIS hart, or under the bound).  It lives inside
     [sie_cap_gpr] (ruling 2), is born at boot ([own_context_boot], one
     per hart), exchanged at swtch, and dropped at a zombie park. *)
  Definition own_context_def `{CID : CpuId} (ξ : CtxId) : iProp Σ :=
    (∃ (B K W : nat) (D : gset (nat * Arch.pa)),
      ctx_at ξ 1 B D ∗
      view_lb view_name loglen_name (hart_agent cpu_id) K ∗ ⌜(B ≤ K)%nat⌝ ∗
      llb loglen_name W ∗ ⌜∀ k, k ∈ D → (k.1 ≤ W)%nat⌝ ∗
      [∗ set] k ∈ D, dirty_ok logm_name (hart_agent cpu_id) B k)%I.
  Lemma own_context_aux : { f | f = @own_context_def }.
  Proof. by eexists. Qed.
  Definition own_context `{CID : CpuId} (ξ : CtxId) : iProp Σ :=
    proj1_sig own_context_aux CID ξ.
  Lemma own_context_unseal `{CID : CpuId} (ξ : CtxId) :
    own_context ξ = own_context_def ξ.
  Proof. unfold own_context. by rewrite (proj2_sig own_context_aux). Qed.

  (* ================================================================== *)
  (* §0.35′(i): THE CONTEXT FLOOR -- "my context's bound has passed [lo]". *)
  (*                                                                      *)
  (* This is the whole of the bound-relation the owner's ruling adds, and  *)
  (* it is one line: [llb] on the context's OWN bound name.  PERSISTENT    *)
  (* and MONOTONE, so a handle may carry it, a crossing may copy it, and   *)
  (* nothing has to give it back.                                         *)
  (*                                                                      *)
  (* WHAT IT IS NOT, and this is the point A6.89/A6.92 paid for: it names  *)
  (* NO HART.  [llb (ctx_bound_name ξ) lo] is a fact about the THREAD OF   *)
  (* CONTROL ξ, and a thread carries its context across every migration,   *)
  (* so a floor claimed here survives a [wp_next] crossing, a park and a   *)
  (* resume.  That is exactly what the two refuted spellings could not do  *)
  (* -- the strengthened [locked] token (A6.89 §(5)) and the lock word's   *)
  (* author receipt (A6.92 §(3)) were both HART-relative and both died on  *)
  (* a crossing.  §0.35′'s answer is to move the fact one axis over.      *)
  (* ================================================================== *)
  Definition ctx_floor (ξ : CtxId) (lo : nat) : iProp Σ :=
    llb (ctx_bound_name ξ) lo.

  Global Instance ctx_floor_persistent ξ lo : Persistent (ctx_floor ξ lo).
  Proof. rewrite /ctx_floor. apply _. Qed.
  Global Instance ctx_floor_timeless ξ lo : Timeless (ctx_floor ξ lo).
  Proof. rewrite /ctx_floor. apply _. Qed.

  Lemma ctx_floor_0 ξ : ⊢ ctx_floor ξ 0.
  Proof. rewrite /ctx_floor. apply llb_0. Qed.

  Lemma ctx_floor_le ξ lo lo' : (lo' ≤ lo)%nat -> ctx_floor ξ lo -∗ ctx_floor ξ lo'.
  Proof. rewrite /ctx_floor. apply llb_le. Qed.

  (* >>> THE READ-SIDE CASH-IN, AND IT IS THE OBJECT FOUR SITES WANTED.
     A6.89 §(7) (the [notheld] owner-cell read), A6.92 §(3) (the lock
     word), A6.95 §(3) (the virtio queue words) and §0.27′ (the park
     stamp) all stopped at the same two missing premises: a view receipt
     [view_lb … K] and the relation [⌜lo ≤ K⌝] against a floor that was
     existential inside an invariant.  With the floor carried on the
     HANDLE and the running token in hand, both fall out in four lines --
     the token's own [B ≤ K] chained with [llb_valid]'s [lo ≤ B].
     The token is THREADED, not consumed: the conclusion's view receipt is
     persistent and the token comes straight back. <<< *)
  Lemma own_context_floor_view `{CID : CpuId} (ξ : CtxId) (lo : nat) :
    own_context ξ -∗ ctx_floor ξ lo -∗
    own_context ξ ∗ ∃ K : nat,
      view_lb view_name loglen_name (hart_agent cpu_id) K ∗ ⌜(lo ≤ K)%nat⌝.
  Proof.
    iIntros "Hrun #Hfl".
    iEval (rewrite own_context_unseal /own_context_def) in "Hrun".
    iDestruct "Hrun" as (B K W D) "(Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hat" as "[Hb Hd]".
    iDestruct (llb_valid with "Hb Hfl") as %HloB.
    iSplitL.
    { iEval (rewrite own_context_unseal /own_context_def).
      iExists B, K, W, D. iFrame "Hb Hd HK HW Hoks". by iPureIntro. }
    iExists K. iFrame "HK". iPureIntro. lia.
  Qed.

  (* THE PARKED TOKEN ([TsoCtxTwin2.ctx_parked]): a thread of control
     not running anywhere -- ξ's authorities with no hart tie.  The
     bound IS the stamp: park raised it past every dirty entry (the
     dirty→clean conversion), so a parked context's facts are all clean
     at [T] and the resumer needs exactly [T ≤ its view].  [llb T]
     keeps the stamp a legal log position.  Deliberately NOT
     hart-ambient: a parked record is migratable, and this token is why
     that is type-correct. *)
  Definition ctx_parked_def (ξ : CtxId) (T : nat) : iProp Σ :=
    (∃ D : gset (nat * Arch.pa),
      ctx_at ξ 1 T D ∗ llb loglen_name T ∗
      ⌜∀ k, k ∈ D → (k.1 ≤ T)%nat⌝)%I.
  Lemma ctx_parked_aux : { f | f = ctx_parked_def }.
  Proof. by eexists. Qed.
  Definition ctx_parked (ξ : CtxId) (T : nat) : iProp Σ :=
    proj1_sig ctx_parked_aux ξ T.
  Lemma ctx_parked_unseal (ξ : CtxId) (T : nat) :
    ctx_parked ξ T = ctx_parked_def ξ T.
  Proof. unfold ctx_parked. by rewrite (proj2_sig ctx_parked_aux). Qed.

  (* THE STABLE HART-VIEW LOWER BOUND ([TsoCtxTwin2.view_lb] at the
     ambient hart): "this hart's view has passed K".  Persistent and
     monotone -- the honest, never-falsified form of the resume premise
     "the hart is at least as fresh as the parked stamp".  Minted below
     the seam at the AMO-acquire leaf ([hart_view_lb_get] at the
     bottom of this file, the [twin_passed_get] image). *)
  Definition hart_view_lb_def `{CID : CpuId} (K : nat) : iProp Σ :=
    view_lb view_name loglen_name (hart_agent cpu_id) K.
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


  (* ================================================================== *)
  (* §0.35′(iii): THE ABSORB OF THE CONTEXT BOUND -- "B_ξ rises to K".    *)
  (*                                                                      *)
  (* The ruling's third clause, as a law.  A thread that holds a view      *)
  (* receipt may RAISE ITS OWN CONTEXT'S BOUND to it, and what it gets     *)
  (* back is the floor claim a lock handle carries ([ctx_floor]).  This is *)
  (* the primitive A6.96 §(3) found missing: [TsoCtxAbsorbLb.ctx_absorb_lb]*)
  (* transports a PAYLOAD between contexts and never touches the bound.    *)
  (*                                                                      *)
  (* WHY IT IS SOUND, and the argument is by inspection of the token:      *)
  (*   - the CLEAN facts are [llb _ t] with [t ≤ B ≤ K], so raising B      *)
  (*     past them changes nothing they claim;                             *)
  (*   - the DIRTY entries' justification [dirty_ok _ _ B k] is MONOTONE   *)
  (*     in [B] -- its two arms are "[k.1 ≤ B]" and "my own message", and  *)
  (*     the first only gets easier;                                       *)
  (*   - the token's own invariant [B ≤ K] is re-established at the new    *)
  (*     pair [(max B K', max K K')].                                      *)
  (* One [mono_nat_own_update]; nothing is invented and no fact is         *)
  (* strengthened -- the bound is bookkeeping about which facts are        *)
  (* already justified, and the receipt is what pays for moving it.        *)
  (*                                                                      *)
  (* THE AUTHOR'S FLOOR IS NOT FREE, IT IS BOUGHT WITH A RECEIPT, and that *)
  (* is the point of the creator-side use: [initlock]'s store-then-mint    *)
  (* leaves the lock's window floored at its own append, which the writer's*)
  (* bound has NOT passed (a plain store is buffered).  Hart 0 buys it at  *)
  (* its next acquire, whose AMO takes the view to the log top -- the same *)
  (* receipt every other hart pays with.                                   *)
  (* ================================================================== *)
  Lemma ctx_bound_raise `{CID : CpuId} (ξ : CtxId) (K' : nat) :
    own_context ξ -∗ hart_view_lb K' ==∗ own_context ξ ∗ ctx_floor ξ K'.
  Proof.
    iIntros "Hrun #HK'".
    iEval (rewrite own_context_unseal /own_context_def) in "Hrun".
    iDestruct "Hrun" as (B K W D) "([Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iMod (mono_nat_own_update (Nat.max B K') with "Hb") as "[Hb #Hlb]"; first lia.
    (* the receipt at the joined view: whichever of the two is larger *)
    iAssert (view_lb view_name loglen_name (hart_agent cpu_id) (Nat.max K K'))%I
      as "#HKm".
    { destruct (decide (K' <= K)%nat) as [Hle|Hgt].
      - replace (Nat.max K K') with K by lia. iExact "HK".
      - replace (Nat.max K K') with K' by lia.
        iEval (rewrite hart_view_lb_unseal /hart_view_lb_def) in "HK'".
        iExact "HK'". }
    (* the dirty justifications, at the raised bound *)
    iAssert ([∗ set] k ∈ D,
               dirty_ok logm_name (hart_agent cpu_id) (Nat.max B K') k)%I
      as "#Hoks'".
    { iApply (big_sepS_impl with "Hoks"). iIntros "!>" (k _) "Hok".
      iDestruct "Hok" as "[%Hle | Hown]"; [ iLeft; iPureIntro; lia | by iRight ]. }
    iModIntro.
    iSplitL "Hb Hd".
    - iEval (rewrite own_context_unseal /own_context_def).
      iExists (Nat.max B K'), (Nat.max K K'), W, D.
      iFrame "Hb Hd HKm HW Hoks'". iPureIntro. split; [ lia | exact HDW ].
    - rewrite /ctx_floor /llb. iLeft.
      iApply (mono_nat_lb_own_le with "Hlb"). lia.
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
     stamp per deposited fact.  ([TsoCtxTwin2.twin_parked_alloc].)
     This is [ProofForkretPark]'s mint. *)
  Lemma ctx_parked_alloc : ⊢ |==> ∃ ξc : CtxId, ctx_parked ξc 0.
  Proof.
    iMod (mono_nat_own_alloc 0) as (γb) "[Hb _]".
    iMod dset_alloc as (γd) "Hd".
    iModIntro. iExists (MkCtxId γb γd).
    rewrite ctx_parked_unseal /ctx_parked_def.
    iExists ∅. iFrame "Hb Hd".
    iSplitR; first by iApply llb_0.
    iPureIntro. intros k Hk. set_solver.
  Qed.

  (* BOOT'S MINT: a hart's FIRST running token.  One per hart, at
     [SystemAdequacy.xv6_boot_era], and nowhere else (the sweep-era
     throwaway mints live in [TsoCtxShim.own_context_alloc] and die with
     it).  Sound unconditionally ([TsoCtxTwin2.twin_run_alloc]: a
     context born at bound 0 with an empty dirty set claims nothing any
     hart could not honour), so this is licensing by NAME, not a lie. *)
  Lemma own_context_boot `{CID : CpuId} : ⊢ |==> ∃ ξ : CtxId, own_context ξ.
  Proof.
    iMod (mono_nat_own_alloc 0) as (γb) "[Hb _]".
    iMod dset_alloc as (γd) "Hd".
    iModIntro. iExists (MkCtxId γb γd).
    rewrite own_context_unseal /own_context_def.
    iExists 0%nat, 0%nat, 0%nat, ∅. iFrame "Hb Hd".
    iSplitR; first by iApply view_lb_0.
    iSplitR; first done.
    iSplitR; first by iApply llb_0.
    iSplitR; first (iPureIntro; intros k Hk; set_solver).
    by iApply big_sepS_empty.
  Qed.

  (* PARK: publish and let go of the hart.  ONE BOUND-RAISE converts
     every dirty entry to clean; the stamp is K ⊔ W -- the token's own
     receipts -- so the scheduler needs nothing from the machine.
     ([TsoCtxTwin2.twin_park], interp-free.) *)
  Lemma ctx_park `{CID : CpuId} (ξ : CtxId) :
    own_context ξ ==∗ ∃ T, ctx_parked ξ T.
  Proof.
    rewrite own_context_unseal /own_context_def.
    iIntros "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & _)".
    set (T := Nat.max K W).
    iMod (mono_nat_own_update T with "Hb") as "[Hb _]"; first lia.
    iModIntro. iExists T.
    rewrite ctx_parked_unseal /ctx_parked_def.
    iExists D. iFrame "Hb Hd".
    iSplitR.
    { iApply (llb_max with "[] HW"). by iApply view_lb_llb. }
    iPureIntro. intros k Hk. have := HDW _ Hk. lia.
  Qed.

  (* RESUME: re-host a parked context on THIS hart.  The premise is the
     stable pair -- a persistent view receipt dominating the parked stamp
     -- and NOTHING relates the parking and resuming harts.  The bundle
     is re-founded with every dirty entry on its clean arm.
     ([TsoCtxTwin2.twin_resume]; the receipt/stamp comparison is minted
     at the resuming hart's lock acquire, [hart_view_lb_get] below.) *)
  Lemma ctx_resume `{CID : CpuId} (ξ : CtxId) (T K : nat) :
    (T ≤ K)%nat →
    hart_view_lb K -∗ ctx_parked ξ T ==∗ own_context ξ.
  Proof.
    rewrite hart_view_lb_unseal /hart_view_lb_def
            ctx_parked_unseal /ctx_parked_def
            own_context_unseal /own_context_def.
    iIntros (HTK) "#HK (%D & Hat & #HT & %HDT)".
    iModIntro. iExists T, K, T, D. iFrame "Hat HK HT".
    iSplitR; first done.
    iSplitR; first done.
    iApply big_sepS_intro. iIntros "!>" (k Hk).
    iLeft. iPureIntro. by apply HDT.
  Qed.


  (* ---------------------------------------------------------------- *)
  (* The context-indexed points-to                                     *)
  (* ---------------------------------------------------------------- *)

  (* [ctx_pointsto ξ a dq v]: the byte fact, registered to context ξ --
     [mem_pointsto]'s body (the kmap claim, the canonicality/RAM/tier
     pins, the FLAT byte at the fact's dq) PLUS the byte's latest-write
     timestamp (a [ts_name] fragment, dq-mirrored so fractions and
     discards move all three together) PLUS the twin's clean/dirty bit.
     The disjunction is never client-visible (the seal).
     ([TsoCtxTwin2.ctx_pointsto], with the VA plumbing riding along.)

     THE CLEAN ARM IS [llb]-SHAPED, NOT A BARE [mono_nat_lb_own]
     (tso-machine-flip.md §6 amendment A6.10): [llb γ t] is
     [mono_nat_lb_own γ t ∨ ⌜t = 0⌝], and the second arm is not a
     convenience -- it is the TIMESTAMP-0 FACT.  A byte whose latest write
     is the era image is visible to every agent at every view
     ([TsoMemPa.read_down_0]), so its justification needs NO context at
     all; with the bare lower bound it would need one bupd PER CONTEXT
     ([mono_nat_lb_own_0] is an update), which is exactly what makes the
     ∀-context image facts ([KernelDataInv.kernel_data], kernel text)
     unmintable.  Everything downstream is unaffected: [llb_valid] gives
     [t ≤ B] on the [t ≠ 0] arm and [t = 0 ≤ B] on the other, which is all
     [ctx_load_ok] and [ctx_morph_pointsto] ever ask of it.  [TsoGhost.llb]
     carries the same trick at the log length for the same reason. *)
  Definition ctx_pointsto_def `{KTR : !CurKtier} (ξ : CtxId)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ (ppn : mword 44) (t : nat),
       kmap_at (svpn_of va) ppn KP_rw ∗
       ⌜(uint va < 274877906944)%Z⌝ ∗
       ⌜addr_is_ram (pa_of ppn va)⌝ ∗
       ⌜ktier_pin cur_ktier ppn va⌝ ∗
       pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn va) dq v ∗
       (pa_of ppn va) ↪[ts_name]{dq} (t, ts_pay_none) ∗
       (llb (ctx_bound_name ξ) t                             (* CLEAN *)
        ∨ dset_in (ctx_dirty_name ξ) (t, pa_of ppn va)))%I.  (* DIRTY *)
  Lemma ctx_pointsto_aux : { f | f = @ctx_pointsto_def }.
  Proof. by eexists. Qed.
  Definition ctx_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    proj1_sig ctx_pointsto_aux KTR ξ va dq v.
  Lemma ctx_pointsto_unseal `{KTR : !CurKtier} (ξ : CtxId)
      (va : Arch.pa) (dq : dfrac) (v : bv 8) :
    ctx_pointsto ξ va dq v = ctx_pointsto_def ξ va dq v.
  Proof. unfold ctx_pointsto. by rewrite (proj2_sig ctx_pointsto_aux). Qed.

  (* the ctx fact FORGETS to the raw flat fact (sound: gen_heap tracks
     the flat cache, and the pointsto inside IS the flat byte at the
     fact's dq).  Used INTERNALLY to derive the pure laws, and exported
     ONCE, under a name that says what it costs ([ctx_pointsto_forget]
     below). *)
  Local Lemma ctx_pointsto_mem_proj {KTR : CurKtier} ξ a dq v :
    ctx_pointsto_def (KTR := KTR) ξ a dq v ⊢ mem_pointsto (KTR := KTR) a dq v.
  Proof.
    iIntros "(%ppn & %t & #Hk & % & % & % & Hp & _ & _)".
    rewrite /mem_pointsto. iExists ppn. by iFrame "Hk Hp".
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE FORGETFUL PROJECTION (tso-machine-flip.md §6 amendment A6.8). *)
  (*                                                                   *)
  (* The ONE direction of the dead shim's [ctx_*_of/to_mem] pair that   *)
  (* survives the machine flip, and the ONLY sanctioned way a ctx fact  *)
  (* leaves the ledger.  Its price is stated once here so no call site  *)
  (* has to re-derive it:                                              *)
  (*                                                                   *)
  (*   IT IS ONE-WAY AND LOSSY.  It drops the byte's latest-write       *)
  (*   TIMESTAMP fragment and the clean/dirty BIT.  Neither can be      *)
  (*   recovered: the timestamp element is a [ghost_map] fragment that  *)
  (*   was handed out once, so nothing above the interp can mint it     *)
  (*   again ([TsoCtxShim]'s header: the [_of_mem] directions are FALSE *)
  (*   at TSO, and this is why).                                       *)
  (*                                                                   *)
  (*   THE RESULT LICENSES NO PLAIN LOAD.  [ctx_load_ok] -- the gate    *)
  (*   that discharges §6's [Mobl_ram_plain] -- needs exactly the two   *)
  (*   conjuncts this drops.  A [mem_pointsto] is still good for value  *)
  (*   agreement, canonicality, the tier pin, the RAM claim, and for    *)
  (*   the strongly-ordered arms (fetch / page walk / exclusive), which *)
  (*   read the flat cache.                                            *)
  (*                                                                   *)
  (* So [grep ctx_pointsto_forget] is the honest inventory of the       *)
  (* places where the tree still parks a byte OUTSIDE the ledger: the   *)
  (* raw towers the kit still speaks, the deliberately-raw lock         *)
  (* metadata (tso-port.md §0.8' ruling 2) and the phys tier (ruling    *)
  (* 6).  Each is an M4 worklist entry, not a leak.  [↦ₛ] left this     *)
  (* list at M1 stage 3.                                                *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_pointsto_forget {KTR : CurKtier} ξ a dq v :
    ctx_pointsto (KTR := KTR) ξ a dq v ⊢ mem_pointsto (KTR := KTR) a dq v.
  Proof. rewrite ctx_pointsto_unseal. apply ctx_pointsto_mem_proj. Qed.

  (* The law surface, mirroring [mem_pointsto]'s (RiscvPtsto.v).  Each is
     the twin lemma with the VA plumbing riding along; a law that could
     not be proven here is a law that must not be added. *)

  Global Instance ctx_pointsto_timeless (KTR : CurKtier) ξ a dq v :
    Timeless (ctx_pointsto (KTR := KTR) ξ a dq v).
  Proof. rewrite ctx_pointsto_unseal /ctx_pointsto_def. apply _. Qed.

  Global Instance ctx_pointsto_discarded_persistent (KTR : CurKtier) ξ a v :
    Persistent (ctx_pointsto (KTR := KTR) ξ a DfracDiscarded v).
  Proof. rewrite ctx_pointsto_unseal /ctx_pointsto_def. apply _. Qed.

  (* agreement is CROSS-context (two registered facts about one byte name
     one flat cell): sound at TSO, and the form invariants need. *)
  Lemma ctx_pointsto_agree {kt1 kt2 : ktier} ξ1 ξ2 a dq1 b1 dq2 b2 :
    ctx_pointsto (KTR := kt1) ξ1 a dq1 b1 -∗
    ctx_pointsto (KTR := kt2) ξ2 a dq2 b2 -∗ ⌜b1 = b2⌝.
  Proof.
    rewrite !ctx_pointsto_unseal.
    iIntros "H1 H2".
    iDestruct (ctx_pointsto_mem_proj with "H1") as "H1".
    iDestruct (ctx_pointsto_mem_proj with "H2") as "H2".
    iApply (mem_pointsto_agree with "H1 H2").
  Qed.

  Lemma ctx_pointsto_ne {kt1 kt2 : ktier} ξ1 ξ2 a1 a2 dq b1 b2 :
    ctx_pointsto (KTR := kt1) ξ1 a1 (DfracOwn 1) b1 -∗
    ctx_pointsto (KTR := kt2) ξ2 a2 dq b2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    rewrite !ctx_pointsto_unseal.
    iIntros "H1 H2".
    iDestruct (ctx_pointsto_mem_proj with "H1") as "H1".
    iDestruct (ctx_pointsto_mem_proj with "H2") as "H2".
    iApply (mem_pointsto_ne with "H1 H2").
  Qed.

  Lemma ctx_pointsto_frac_split `{KTR : !CurKtier} ξ a q1 q2 b :
    ctx_pointsto ξ a (DfracOwn (q1 + q2)) b ⊣⊢
    ctx_pointsto ξ a (DfracOwn q1) b ∗ ctx_pointsto ξ a (DfracOwn q2) b.
  Proof.
    rewrite !ctx_pointsto_unseal /ctx_pointsto_def.
    iSplit.
    - iIntros "(%ppn & %t & #Hk & %Hc & %Hr & %Hp & Hpt & Hts & Hbit)".
      iDestruct "Hpt" as "[Hpt1 Hpt2]".
      iDestruct "Hts" as "[Hts1 Hts2]".
      iDestruct "Hbit" as "[#Hcl | Hdt]".
      + iSplitL "Hpt1 Hts1".
        * iExists ppn, t. iFrame "Hk Hpt1 Hts1".
          iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. by iLeft.
        * iExists ppn, t. iFrame "Hk Hpt2 Hts2".
          iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. by iLeft.
      + iDestruct "Hdt" as "#Hdt1". iPoseProof "Hdt1" as "Hdt2".
        iSplitL "Hpt1 Hts1".
        * iExists ppn, t. iFrame "Hk Hpt1 Hts1 Hdt1".
          iSplit; [done|]. iSplit; [done|]. done.
        * iExists ppn, t. iFrame "Hk Hpt2 Hts2 Hdt2".
          iSplit; [done|]. iSplit; [done|]. done.
    - iIntros "[(%ppn1 & %t1 & #Hk1 & %Hc & %Hr1 & %Hp1 & Hpt1 & Hts1 & Hbit1)
                (%ppn2 & %t2 & #Hk2 & %  & %Hr2 & %Hp2 & Hpt2 & Hts2 & Hbit2)]".
      iDestruct (kmap_at_agree with "Hk1 Hk2") as %[<- _].
      iDestruct (ghost_map_elem_combine with "Hts1 Hts2") as "[Hts %Heq]".
      injection Heq as Heq. subst t2.
      iCombine "Hpt1 Hpt2" as "Hpt".
      rewrite !dfrac_op_own.
      iExists ppn1, t1. iFrame "Hk1 Hpt Hts".
      iSplit; first done. iSplit; first done. iSplit; first done.
      iDestruct "Hbit1" as "[#Hcl | Hdt1]"; first by iLeft.
      iDestruct "Hbit2" as "[#Hcl | Hdt2]"; first by iLeft.
      iRight. iExact "Hdt1".
  Qed.

  Lemma ctx_pointsto_persist `{KTR : !CurKtier} ξ a dq b :
    ctx_pointsto ξ a dq b ==∗ ctx_pointsto ξ a DfracDiscarded b.
  Proof.
    rewrite !ctx_pointsto_unseal /ctx_pointsto_def.
    iIntros "(%ppn & %t & #Hk & % & % & % & Hpt & Hts & Hbit)".
    iMod (pointsto_persist with "Hpt") as "Hpt".
    iMod (ghost_map_elem_persist with "Hts") as "Hts".
    iDestruct "Hbit" as "[#Hcl | Hdt]".
    - iModIntro. iExists ppn, t. iFrame "Hk Hpt Hts".
      iSplit; first done. iSplit; first done. iSplit; first done. by iLeft.
    - iModIntro. iExists ppn, t. iFrame "Hk Hpt Hts".
      iSplit; first done. iSplit; first done. iSplit; first done. by iRight.
  Qed.

  (* THE PURE CONJUNCTS, read off the fact ([mem_canonical]'s and
     [mem_pointsto_ram]'s images).  Stated here rather than left to
     [ctx_pointsto_forget] + the raw law because they cost the holder
     NOTHING: a pure fact is not a place where the ledger can leak. *)
  Lemma ctx_pointsto_canonical `{KTR : !CurKtier} ξ a dq v :
    ctx_pointsto ξ a dq v -∗ ⌜(uint a < 274877906944)%Z⌝.
  Proof.
    rewrite ctx_pointsto_unseal /ctx_pointsto_def.
    iIntros "(%ppn & %t & _ & %Hc & _)". iPureIntro. exact Hc.
  Qed.

  (* THE TIER WEAKENING ([mem_ktier_mono]'s image).  The pin is the only
     tier-dependent conjunct of the body and it weakens ([ktier_pin_mono]),
     exactly as at the raw fact -- so this law needs no crossing at all,
     which is what retires the rehearsal-era "mem_ktier_mono rides the raw
     law between two shims" seam (tso-port.md §0.9'). *)
  Lemma ctx_ktier_mono (kt kt' : ktier) `{!KtierLe kt kt'} ξ a dq v :
    ctx_pointsto (KTR := kt) ξ a dq v ⊢ ctx_pointsto (KTR := kt') ξ a dq v.
  Proof.
    rewrite !ctx_pointsto_unseal /ctx_pointsto_def.
    iIntros "(%ppn & %t & #Hk & %Hc & %Hd & %Hp & Hpt & Hts & Hbit)".
    iExists ppn, t. iFrame "Hk Hpt Hts Hbit".
    iSplit; [iPureIntro; exact Hc|]. iSplit; [iPureIntro; exact Hd|].
    iPureIntro. exact (ktier_pin_mono kt kt' ppn a Hp).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The context-indexed WORD tower (the M1 notation flip's carrier)    *)
  (* ---------------------------------------------------------------- *)

  (* Derived from [ctx_pointsto]'s exported surface alone, so the tower
     is honest with no extra proof obligations.  Text unchanged from the
     SC-era file. *)

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

  (* the tower's forgetful projection and tier weakening: [ctx_word_pointsto]
     is [word_pointsto]'s body over the sealed byte, so both are the byte law
     under the big-op.  The [_forget] form carries the same warning its byte
     original does -- it is what the raw lock metadata (tso-port.md §0.8'
     ruling 2) and the [↦₂]/[↦₄] towers cross on. *)
  Lemma ctx_word_pointsto_forget `{KTR : !CurKtier} ξ a dq w :
    ctx_word_pointsto ξ a dq w ⊢ word_pointsto a dq w.
  Proof.
    rewrite /ctx_word_pointsto /word_pointsto.
    iIntros "[$ H]". iApply (big_sepL_mono with "H").
    iIntros (k j _) "H". iApply (ctx_pointsto_forget with "H").
  Qed.

  Lemma ctx_word_ktier_mono (kt kt' : ktier) `{!KtierLe kt kt'} ξ a dq w :
    ctx_word_pointsto (KTR := kt) ξ a dq w ⊢
    ctx_word_pointsto (KTR := kt') ξ a dq w.
  Proof.
    rewrite /ctx_word_pointsto. iIntros "[$ H]".
    iApply (big_sepL_mono with "H").
    iIntros (k j _) "H". iApply (ctx_ktier_mono kt kt' with "H").
  Qed.

  Lemma ctx_word_pointsto_agree {kt1 kt2 : ktier} (ξ1 ξ2 : CtxId) a dq1 w1 dq2 w2 :
    ctx_word_pointsto (KTR := kt1) ξ1 a dq1 w1 -∗
    ctx_word_pointsto (KTR := kt2) ξ2 a dq2 w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (ctx_bytes_agree ξ1 ξ2 a 0 8 with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=8)). intros j Hj. apply Hb. lia.
  Qed.


  (* ---- the 2-BYTE tower ([↦₂]), M1 STAGE 2 ---------------------
     Character-for-character the 8-byte tower above at width 2; the two
     differ only in the alignment constant and the byte count, which is why
     stage 2 costs nothing beyond re-declaring the notations.  NOT SEALED,
     for the reason [ctx_word_pointsto] is not: a tower OVER the sealed byte
     leaks nothing, and the tree's proofs destruct and frame the word shape
     structurally. *)
  Definition ctx_word2_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (w : bv 16) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 2 = true⌝ ∗
     [∗ list] j ∈ seq 0 2, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))%I.

  Section ctx_word2.
    Context `{KTR : !CurKtier}.


    Lemma ctx_word2_pointsto_bytes ξ a dq w :
      ctx_word2_pointsto ξ a dq w ⊢
      [∗ list] j ∈ seq 0 2, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j).
    Proof. iIntros "[_ $]". Qed.

    Lemma ctx_word2_pointsto_intro ξ a dq w :
      is_aligned_paddr (Physaddr a) 2 = true ->
      ([∗ list] j ∈ seq 0 2, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))
      ⊢ ctx_word2_pointsto ξ a dq w.
    Proof. iIntros (Hal) "H". by iFrame. Qed.

    Global Instance ctx_word2_pointsto_timeless ξ a dq w :
      Timeless (ctx_word2_pointsto ξ a dq w).
    Proof. rewrite /ctx_word2_pointsto. apply _. Qed.

    Global Instance ctx_word2_pointsto_discarded_persistent ξ a w :
      Persistent (ctx_word2_pointsto ξ a DfracDiscarded w).
    Proof. rewrite /ctx_word2_pointsto. apply _. Qed.

    Lemma ctx_word2_pointsto_frac_split ξ a q1 q2 w :
      ctx_word2_pointsto ξ a (DfracOwn (q1 + q2)) w ⊣⊢
      ctx_word2_pointsto ξ a (DfracOwn q1) w ∗
      ctx_word2_pointsto ξ a (DfracOwn q2) w.
    Proof.
      rewrite /ctx_word2_pointsto (ctx_bytes_frac_split ξ a 0 2 q1 q2 w).
      iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
    Qed.


    (* the HALF split/join, the form the escrow and fraction protocols
       use ([word2_pointsto_half*]'s images) *)
    Lemma ctx_word2_pointsto_half ξ a w :
      ctx_word2_pointsto ξ a (DfracOwn 1) w ⊣⊢
      ctx_word2_pointsto ξ a (DfracOwn (1/2)) w ∗
      ctx_word2_pointsto ξ a (DfracOwn (1/2)) w.
    Proof. rewrite -ctx_word2_pointsto_frac_split Qp.div_2. reflexivity. Qed.


  End ctx_word2.

  Lemma ctx_word2_pointsto_agree {kt1 kt2 : ktier} (ξ1 ξ2 : CtxId)
      a dq1 w1 dq2 w2 :
    ctx_word2_pointsto (KTR := kt1) ξ1 a dq1 w1 -∗
    ctx_word2_pointsto (KTR := kt2) ξ2 a dq2 w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (ctx_bytes_agree ξ1 ξ2 a 0 2 with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=2)). intros j Hj. apply Hb. lia.
  Qed.


  (* ---- the 4-BYTE tower ([↦₄]), M1 STAGE 2 ---------------------
     Character-for-character the 8-byte tower above at width 4; the two
     differ only in the alignment constant and the byte count, which is why
     stage 2 costs nothing beyond re-declaring the notations.  NOT SEALED,
     for the reason [ctx_word_pointsto] is not: a tower OVER the sealed byte
     leaks nothing, and the tree's proofs destruct and frame the word shape
     structurally. *)
  Definition ctx_word4_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (w : bv 32) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
     [∗ list] j ∈ seq 0 4, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))%I.

  Section ctx_word4.
    Context `{KTR : !CurKtier}.

    Lemma ctx_word4_pointsto_unfold ξ a dq w :
      ctx_word4_pointsto ξ a dq w ⊣⊢
      ⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
      ([∗ list] j ∈ seq 0 4, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j)).
    Proof. reflexivity. Qed.

    Lemma ctx_word4_pointsto_aligned_p ξ a dq w :
      ctx_word4_pointsto ξ a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 4 = true⌝.
    Proof. iIntros "[$ _]". Qed.

    Lemma ctx_word4_pointsto_bytes ξ a dq w :
      ctx_word4_pointsto ξ a dq w ⊢
      [∗ list] j ∈ seq 0 4, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j).
    Proof. iIntros "[_ $]". Qed.

    Lemma ctx_word4_pointsto_intro ξ a dq w :
      is_aligned_paddr (Physaddr a) 4 = true ->
      ([∗ list] j ∈ seq 0 4, ctx_pointsto ξ (pa_add a j) dq (nth_byte w j))
      ⊢ ctx_word4_pointsto ξ a dq w.
    Proof. iIntros (Hal) "H". by iFrame. Qed.

    Global Instance ctx_word4_pointsto_timeless ξ a dq w :
      Timeless (ctx_word4_pointsto ξ a dq w).
    Proof. rewrite /ctx_word4_pointsto. apply _. Qed.

    Global Instance ctx_word4_pointsto_discarded_persistent ξ a w :
      Persistent (ctx_word4_pointsto ξ a DfracDiscarded w).
    Proof. rewrite /ctx_word4_pointsto. apply _. Qed.

    Lemma ctx_word4_pointsto_frac_split ξ a q1 q2 w :
      ctx_word4_pointsto ξ a (DfracOwn (q1 + q2)) w ⊣⊢
      ctx_word4_pointsto ξ a (DfracOwn q1) w ∗
      ctx_word4_pointsto ξ a (DfracOwn q2) w.
    Proof.
      rewrite /ctx_word4_pointsto (ctx_bytes_frac_split ξ a 0 4 q1 q2 w).
      iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
    Qed.

    Lemma ctx_word4_pointsto_persist ξ a dq w :
      ctx_word4_pointsto ξ a dq w ==∗
      ctx_word4_pointsto ξ a DfracDiscarded w.
    Proof.
      iIntros "[#Hal H]".
      iAssert (|==> [∗ list] j ∈ seq 0 4,
        ctx_pointsto ξ (pa_add a j) DfracDiscarded (nth_byte w j))%I
        with "[H]" as ">H".
      { iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
        iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_persist. }
      iModIntro. by iFrame "Hal H".
    Qed.

    (* the HALF split/join, the form the escrow and fraction protocols
       use ([word4_pointsto_half*]'s images) *)
    Lemma ctx_word4_pointsto_half ξ a w :
      ctx_word4_pointsto ξ a (DfracOwn 1) w ⊣⊢
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w ∗
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w.
    Proof. rewrite -ctx_word4_pointsto_frac_split Qp.div_2. reflexivity. Qed.

    Lemma ctx_word4_pointsto_half_split ξ a w :
      ctx_word4_pointsto ξ a (DfracOwn 1) w -∗
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w ∗
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w.
    Proof. rewrite ctx_word4_pointsto_half. iIntros "$". Qed.

    Lemma ctx_word4_pointsto_half_join ξ a w :
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w -∗
      ctx_word4_pointsto ξ a (DfracOwn (1/2)) w -∗
      ctx_word4_pointsto ξ a (DfracOwn 1) w.
    Proof. iIntros "H1 H2". rewrite ctx_word4_pointsto_half. iFrame "H1 H2". Qed.

  End ctx_word4.

  Lemma ctx_word4_pointsto_agree {kt1 kt2 : ktier} (ξ1 ξ2 : CtxId)
      a dq1 w1 dq2 w2 :
    ctx_word4_pointsto (KTR := kt1) ξ1 a dq1 w1 -∗
    ctx_word4_pointsto (KTR := kt2) ξ2 a dq2 w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (ctx_bytes_agree ξ1 ξ2 a 0 4 with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=4)). intros j Hj. apply Hb. lia.
  Qed.


  (* ---- the STRING tower ([↦ₛ]) ---------------------------------------
     [RiscvPtsto.string_pointsto]'s shape over the context fact: a
     NUL-terminated C string resident byte-by-byte from [a], no alignment
     side condition (a C string is byte-addressed).

     WHY IT IS CONTEXT-RELATIVE AT ALL (tso-port.md §0.21′/§0.22′, the
     ruling that retired the "↦ₛ stays raw" assessment that used to sit
     beside the notations below, and which this workspace's A6.15 had
     recorded).  The earlier assessment read every string in the tree as a
     DISCARDED read-only image literal, whose load obligation the pristine
     (timestamp-0) gate discharges with no context.  That is false of the
     kernel's DYNAMIC strings: [p->name] is written by [safestrcpy] at
     proc.c:290 and exec.c:132, so its bytes carry ordinary ledger residue
     and its readers owe an ordinary load obligation at the reading
     thread's context.  A tier that covers only the pristine case is not
     the string tier, it is a special case of it -- so [↦ₛ] denotes the
     context-relative fact at ARBITRARY timestamps, and the pristine story
     comes back as the DERIVED [ctx_string_all] below (the [kernel_data]
     precedent: one ∀-quantified fact minted once, usable at every
     context), which is what the persistent lock handles carry.

     THE STRUCTURE RULE, since this is the third tier to flip: a tier flip
     never RELOCATES the raw definition.  [RiscvPtsto]'s tower stays put as
     the below-Σ fact and this is a SECOND tower with the same spelling;
     import order decides.  Nothing moved. *)
  Definition ctx_string_pointsto `{KTR : !CurKtier} (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (s : string) : iProp Σ :=
    ([∗ list] j ↦ b ∈ cstring_bytes s, ctx_pointsto ξ (pa_add a j) dq b)%I.

  Section ctx_string.
    Context `{KTR : !CurKtier}.

    Lemma ctx_string_pointsto_unfold ξ a dq s :
      ctx_string_pointsto ξ a dq s ⊣⊢
      [∗ list] j ↦ b ∈ cstring_bytes s, ctx_pointsto ξ (pa_add a j) dq b.
    Proof. reflexivity. Qed.


    Global Instance ctx_string_pointsto_timeless ξ a dq s :
      Timeless (ctx_string_pointsto ξ a dq s).
    Proof. rewrite /ctx_string_pointsto. apply _. Qed.

    Global Instance ctx_string_pointsto_discarded_persistent ξ a s :
      Persistent (ctx_string_pointsto ξ a DfracDiscarded s).
    Proof. rewrite /ctx_string_pointsto. apply _. Qed.

    Lemma ctx_string_pointsto_frac_split ξ a q1 q2 s :
      ctx_string_pointsto ξ a (DfracOwn (q1 + q2)) s ⊣⊢
      ctx_string_pointsto ξ a (DfracOwn q1) s ∗
      ctx_string_pointsto ξ a (DfracOwn q2) s.
    Proof.
      rewrite /ctx_string_pointsto -big_sepL_sep.
      apply big_opL_proper. intros ? b ?. apply ctx_pointsto_frac_split.
    Qed.


  End ctx_string.


  (* >>> A6.91: THE BYTE'S AND THE 4-BYTE WORD'S [ktier]-TYPED TWINS, and
     they were the two the family was missing.  [Class CurKtier :=
     cur_ktier : ktier] is NOT declared transparent to typeclass
     unification (unlike [CurCtx], which is -- see the note at
     [Typeclasses Transparent CurCtx]), so an instance stated at
     [(KTR : CurKtier)] does not fire on a goal whose tier argument is
     [ktier]-typed.  Every OTHER tower in this file and in [RiscvPtsto]
     already carries the twin ([ctx_string_pointsto_discarded_persistent'],
     [word4_pointsto_discarded_persistent']); the byte and the word4 did
     not, and the symptom is remote and unhelpful --
     [iMod … as "#H"] on a freshly discarded cell failing with
     "not persistent" at a file that has the instance in scope
     (ProofForkret's [first_done] seal). <<< *)
  Global Instance ctx_pointsto_discarded_persistent' (ktr : ktier) (ξ : CtxId)
      (a : Arch.pa) (v : bv 8) :
    Persistent (ctx_pointsto (KTR := ktr) ξ a DfracDiscarded v).
  Proof. exact (ctx_pointsto_discarded_persistent ktr ξ a v). Qed.

  Global Instance ctx_word4_pointsto_discarded_persistent' (ktr : ktier)
      (ξ : CtxId) (a : Arch.pa) (w : mword 32) :
    Persistent (ctx_word4_pointsto (KTR := ktr) ξ a DfracDiscarded w).
  Proof. exact (ctx_word4_pointsto_discarded_persistent (KTR := ktr) ξ a w). Qed.

  (* the [ktier]-typed twins, for the same reason as the word towers' *)
  Global Instance ctx_string_pointsto_timeless' (ktr : ktier) (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (s : string) :
    Timeless (ctx_string_pointsto (KTR := ktr) ξ a dq s).
  Proof. exact (ctx_string_pointsto_timeless (KTR := ktr) ξ a dq s). Qed.

  Global Instance ctx_string_pointsto_discarded_persistent' (ktr : ktier)
      (ξ : CtxId) (a : Arch.pa) (s : string) :
    Persistent (ctx_string_pointsto (KTR := ktr) ξ a DfracDiscarded s).
  Proof. exact (ctx_string_pointsto_discarded_persistent (KTR := ktr) ξ a s). Qed.

  (* ---- the DERIVED context-free form -----------------------------------
     [ctx_string_all a dq s]: the string holds at EVERY context.  This is
     the pristine/timestamp-0 story, and it is a DERIVED special case of the
     tower above -- never its definition (tso-port.md §0.21′).

     It exists because the persistent lock handles carry a string.
     [WpLock.lock_name] / [SleepLock.sl_name] are half of [is_lock] /
     [is_sleeplock], which are CLOSED TERMS that ride in park records and
     are minted at boot for consumers that run at their own contexts; a
     handle whose statement mentions an ambient ξ is unstatable elsewhere
     (§0.8′ ruling 2, the root both design problems were routed around).
     The ∀ keeps the handle context-free IN SHAPE while its content is an
     ordinary string fact.

     WHERE IT COMES FROM, honestly, AND WHERE THE ⌜t = 0⌝ ARM IS PAID.
     [KernelDataInv.kernel_data] is itself ∀-context, so
     [kernel_data_string_all] mints this form with no seam; and
     [kernel_data]'s own ∀ is minted by the boot carve out of
     [ctx_pointsto_of_pristine_va_all] above -- a discarded image byte plus
     its pristine receipt, justified by [llb]'s [t = 0] arm, which mentions
     no context.  So the chain rodata -> [kernel_data_string_all] ->
     [lock_name_intro] -> [is_lock] bottoms out in the clean-arm disjunct
     and has no crossing anywhere in it. *)
  Definition ctx_string_all `{KTR : !CurKtier}
      (a : Arch.pa) (dq : dfrac) (s : string) : iProp Σ :=
    (∀ ξ : CtxId, ctx_string_pointsto ξ a dq s)%I.

  Section ctx_string_all.
    Context `{KTR : !CurKtier}.


    (* USE IT AT YOUR OWN CONTEXT: the only elimination, and the one every
       consumer of a handle's string runs. *)
    Lemma ctx_string_all_elim (ξ : CtxId) a dq s :
      ctx_string_all a dq s ⊢ ctx_string_pointsto ξ a dq s.
    Proof. iIntros "H". iApply "H". Qed.


    Global Instance ctx_string_all_persistent a s :
      Persistent (ctx_string_all a DfracDiscarded s).
    Proof. rewrite /ctx_string_all. apply _. Qed.
  End ctx_string_all.

  Global Instance ctx_string_all_persistent' (ktr : ktier) a s :
    Persistent (ctx_string_all (KTR := ktr) a DfracDiscarded s).
  Proof. exact (ctx_string_all_persistent (KTR := ktr) a s). Qed.


  (* ---------------------------------------------------------------- *)
  (* Transport: the ONLY ways a fact changes context                   *)
  (* ---------------------------------------------------------------- *)

  (* [ctx_dom ξ ξ']: ξ's facts may be re-registered to ξ'
     ([TsoCtxTwin2.ctx_dom] -- the checkpoint's "one correction, three
     problems" in one definition).  It carries HALF of ξ's own
     authorities (borrowed out of ξ's token, value-pinned by agreement
     with the half left behind) plus a bound-lb of ξ' dominating both
     ξ's bound and ξ's dirty watermark.  Nothing about the machine: Σ's
     constraint that [ctx_dom] be statable without the state
     interpretation holds BY CONSTRUCTION.  Minted ONLY inside the lock
     release/acquire and scheduler park/resume proofs
     ([ctx_dom_to_parked] / [ctx_dom_of_parked] below).  It is
     deliberately NOT persistent (a persistent domination would license
     registering later facts -- the unsound step the `weak-memory`
     branch's notes call out). *)
  Definition ctx_dom_def (ξ ξ' : CtxId) : iProp Σ :=
    (∃ (B W B' : nat) (D : gset (nat * Arch.pa)),
      ctx_at ξ (1/2) B D ∗
      ⌜∀ k, k ∈ D → (k.1 ≤ W)%nat⌝ ∗
      ⌜(B ≤ B')%nat⌝ ∗ ⌜(W ≤ B')%nat⌝ ∗
      mono_nat_lb_own (ctx_bound_name ξ') B')%I.
  Lemma ctx_dom_aux : { f | f = ctx_dom_def }.
  Proof. by eexists. Qed.
  Definition ctx_dom (ξ ξ' : CtxId) : iProp Σ := proj1_sig ctx_dom_aux ξ ξ'.
  Lemma ctx_dom_unseal (ξ ξ' : CtxId) : ctx_dom ξ ξ' = ctx_dom_def ξ ξ'.
  Proof. unfold ctx_dom. by rewrite (proj2_sig ctx_dom_aux). Qed.

  (* >>> A6.116 §3(2): THE FLOOR TRANSPORTS ALONG DOMINATION, FOR FREE.
     [ctx_dom]'s body already carries everything: the sender's authority at
     [B], the relation [B ≤ B'], and the receiver's lower bound at [B'].  So a
     floor the SENDER could discharge is one the RECEIVER can discharge, and
     the ξ-indexed half of §0.35′(i) is not an obstacle to payload transport
     at all -- what a crossing cannot do is CREATE the floor, only carry it.

     This is what makes the lock handle's left arm propagate once anyone
     has it; A6.116 §3 is then only about where the FIRST one comes from. <<< *)
  Lemma ctx_floor_dom (ξ ξ' : CtxId) (lo : nat) :
    ctx_dom ξ ξ' -∗ ctx_floor ξ lo -∗ ctx_dom ξ ξ' ∗ ctx_floor ξ' lo.
  Proof.
    rewrite ctx_dom_unseal /ctx_dom_def /ctx_floor.
    iIntros "(%B & %W & %B' & %D & [Hb Hd] & %HDW & %HBB' & %HWB' & #Hlb') Hfl".
    iDestruct (llb_valid_q with "Hb Hfl") as %HloB.
    iSplitR "".
    - iExists B, W, B', D. iFrame "Hb Hd Hlb'". by iPureIntro.
    - iApply (llb_le _ B'); [lia|]. by iLeft.
  Qed.

  (* A context-indexed payload that transports along domination.  This is
     the obligation lock payloads pick up in the M3 sweep: any payload
     failing it at SC is a payload the TSO flip would break -- found
     early, which is the point of the sweeps. *)
  Class CtxMorph (R : CtxId → iProp Σ) :=
    ctx_morph : ∀ ξ ξ', ctx_dom ξ ξ' -∗ R ξ ==∗ ctx_dom ξ ξ' ∗ R ξ'.

  (* The structural instances.  NOTE what is absent: no instance for
     [own_context] (the running-thread token never transfers by
     domination), and no blanket instance for persistent-but-ξ-dependent
     propositions (the clean lower bound is persistent AND pinned to its
     context).  ξ-CONSTANT propositions -- pure facts, ghost state,
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
  Proof. iIntros (ξ ξ') "Hd HP !>". iFrame. Qed.

  (* THE TRANSPORT OF A FACT ([TsoCtxTwin2.ctx_morph_pointsto]): a clean
     fact re-indexes by COPYING its justification (t ≤ B ≤ B', and ξ''s
     lb is persistent); a dirty one's timestamp sits under the watermark
     (t ≤ W ≤ B'), and its fragment is dropped -- the pinned key is a
     timestamp, never reused, so the leftover entry is inert. *)
  Global Instance ctx_morph_pointsto (kt : ktier) a dq v :
    CtxMorph (λ ξ, ctx_pointsto (KTR := kt) ξ a dq v).
  Proof.
    iIntros (ξ ξ') "Hd HP".
    rewrite ctx_dom_unseal /ctx_dom_def !ctx_pointsto_unseal /ctx_pointsto_def.
    iDestruct "Hd" as
      "(%B & %W & %B' & %D & [Hb Hdm] & %HDW & %HBB' & %HWB' & #Hlb')".
    iDestruct "HP" as "(%ppn & %t & #Hk & % & % & % & Hpt & Hts & Hbit)".
    iAssert (⌜(t ≤ B')%nat⌝)%I as %HtB'.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - iDestruct (llb_valid_q with "Hb Hcl") as %HtB.
        iPureIntro. lia.
      - iDestruct (dset_lookup with "Hdm Hdt") as %HDt.
        have HtW : ((t, pa_of ppn a).1 ≤ W)%nat by apply HDW.
        simpl in HtW. iPureIntro. lia. }
    iClear "Hbit". iModIntro.
    iSplitL "Hb Hdm".
    { iExists B, W, B', D. iFrame "Hb Hdm Hlb'". by iPureIntro. }
    iExists ppn, t. iFrame "Hk Hpt Hts".
    iSplit; first done. iSplit; first done. iSplit; first done.
    iLeft. rewrite /llb. iLeft.
    iApply (mono_nat_lb_own_le with "Hlb'"). lia.
  Qed.

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

  (* A6.121 (the M3 λ-conversion): two more structural instances the
     straggler payloads need -- a finite map of transportable parts, and a
     boolean branch between two transportable parts (the payloads' state-
     indexed [if]s and [bool_decide]s). *)
  Global Instance ctx_morph_big_sepM `{Countable K} {A} (m : gmap K A)
      (Φ : K → A → CtxId → iProp Σ) :
    (∀ k x, CtxMorph (Φ k x)) →
    CtxMorph (λ ξ, [∗ map] k ↦ x ∈ m, Φ k x ξ)%I.
  Proof.
    intros HΦ. induction m as [|k x m Hk IH] using map_ind.
    - iIntros (ξ ξ') "Hd _ !>". rewrite big_sepM_empty. by iFrame.
    - iIntros (ξ ξ') "Hd HR".
      iDestruct (big_sepM_insert _ _ _ _ Hk with "HR") as "[HR HRs]".
      iMod (ctx_morph with "Hd HR") as "[Hd HR]".
      iMod (IH ξ ξ' with "Hd HRs") as "[Hd HRs]".
      iModIntro. iFrame "Hd". rewrite (big_sepM_insert _ _ _ _ Hk). iFrame.
  Qed.

  Global Instance ctx_morph_if (b : bool) (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, if b then R1 ξ else R2 ξ)%I.
  Proof. intros H1 H2. destruct b; [exact H1 | exact H2]. Qed.

  (* the word cell's transport obligation, once for every payload *)
  Global Instance ctx_morph_word (kt : ktier) a dq w :
    CtxMorph (λ ξ, ctx_word_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ ξ') "Hd [%Hal H]".
    iMod (ctx_morph_big_sepL (seq 0 8)
            (λ _ j ξ0, ctx_pointsto (KTR := kt) ξ0 (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_morph_pointsto _ _ _ _)
            ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame "Hd". iSplit; [done|]. iExact "H".
  Qed.

  (* … and the same for the stage-2 towers. *)
  Global Instance ctx_morph_word2 (kt : ktier) a dq w :
    CtxMorph (λ ξ, ctx_word2_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ ξ') "Hd [%Hal H]".
    iMod (ctx_morph_big_sepL (seq 0 2)
            (λ _ j ξ0, ctx_pointsto (KTR := kt) ξ0 (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_morph_pointsto _ _ _ _)
            ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame "Hd". iSplit; [done|]. iExact "H".
  Qed.

  Global Instance ctx_morph_word4 (kt : ktier) a dq w :
    CtxMorph (λ ξ, ctx_word4_pointsto (KTR := kt) ξ a dq w).
  Proof.
    iIntros (ξ ξ') "Hd [%Hal H]".
    iMod (ctx_morph_big_sepL (seq 0 4)
            (λ _ j ξ0, ctx_pointsto (KTR := kt) ξ0 (pa_add a j) dq (nth_byte w j))
            (λ i x, ctx_morph_pointsto _ _ _ _)
            ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame "Hd". iSplit; [done|]. iExact "H".
  Qed.


  (* ---------------------------------------------------------------- *)
  (* The ctx_dom mints -- borrow accessors on the tokens               *)
  (* ---------------------------------------------------------------- *)

  (* RELEASE-SIDE / FORK-SIDE MINT, INTERP-FREE
     ([TsoCtxTwin2.ctx_dom_to_parked]): domination into a PARKED target.
     The target's stamp is raised to cover everything the source could
     deposit (its bound receipt K and its dirty watermark W -- both
     legal log positions by their [llb]s, so no interp is consulted).
     The give-back wand re-agrees the halves, so the source token comes
     back exactly as it went in. *)
  Lemma ctx_dom_to_parked `{CID : CpuId} (ξ ξ' : CtxId) (T : nat) :
    own_context ξ -∗ ctx_parked ξ' T ==∗
    ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_parked ξ' T' ∗ ctx_dom ξ ξ' ∗
          (ctx_dom ξ ξ' -∗ own_context ξ).
  Proof.
    iIntros "Hrun Hpk".
    iEval (rewrite own_context_unseal /own_context_def) in "Hrun".
    iEval (rewrite ctx_parked_unseal /ctx_parked_def) in "Hpk".
    iDestruct "Hrun" as "(%B & %K & %W & %D & Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hpk" as "(%D' & [Hb' Hd'] & #HT & %HD'T)".
    set (T' := Nat.max T (Nat.max K W)).
    iMod (mono_nat_own_update T' with "Hb'") as "[Hb' #Hlb']"; first lia.
    iModIntro. iExists T'.
    rewrite ctx_parked_unseal /ctx_parked_def ctx_dom_unseal /ctx_dom_def
            own_context_unseal /own_context_def.
    iDestruct (ctx_at_halves with "Hat") as "[Hat1 Hat2]".
    iSplitR; first (iPureIntro; lia).
    iSplitL "Hb' Hd'".
    { iExists D'. iFrame "Hb' Hd'".
      iSplitR.
      { iApply (llb_max with "HT").
        iApply (llb_max with "[] HW"). by iApply view_lb_llb. }
      iPureIntro. intros k Hk. have := HD'T _ Hk. lia. }
    iSplitL "Hat1".
    { iExists B, W, T', D. iFrame "Hat1 Hlb'". iPureIntro.
      split_and!; [done | lia | lia]. }
    (* the give-back *)
    iIntros "(%B0 & %W0 & %B0' & %D0 & Hat0 & _ & _ & _ & _)".
    iDestruct (ctx_at_agree with "Hat0 Hat2") as %[-> ->].
    iCombine "Hat0 Hat2" as "Hat".
    rewrite -ctx_at_halves.
    iExists B, K, W, D. iFrame "Hat HK HW Hoks". by iPureIntro.
  Qed.

  (* THE DEPOSIT: a running context hands ANY morphable payload to a
     PARKED one, the parked stamp raised to cover it -- so a fork's
     hand-me-downs (including bytes the parent wrote after the child's
     mint: uvmcopy) have NOTHING TO PROVE at the deposit site; the
     resumer's lock acquire pays the raised stamp.
     ([TsoCtxTwin2.twin_deposit], interp-free.) *)
  Lemma ctx_deposit `{CID : CpuId} (R : CtxId → iProp Σ) `{!CtxMorph R}
      (ξ ξc : CtxId) (T : nat) :
    own_context ξ -∗ ctx_parked ξc T -∗ R ξ ==∗
    own_context ξ ∗ ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_parked ξc T' ∗ R ξc.
  Proof.
    iIntros "Hrun Hpk HR".
    iMod (ctx_dom_to_parked ξ ξc T with "Hrun Hpk")
      as (T') "(%HTT' & Hpk & Hdom & Hback)".
    iMod (ctx_morph with "Hdom HR") as "[Hdom HR]".
    iModIntro. iSplitL "Hback Hdom"; first by iApply "Hback".
    iExists T'. by iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE KIT-FACING GATES: where the surface meets the machine's        *)
  (* interpretation.  Consumed by the below-Σ leaf re-proofs against    *)
  (* the Ztso arms (tso-machine-flip.md §6); each is the image of a     *)
  (* TsoCtxTwin2 gate lemma at the live interp [tso_interp_at].         *)
  (* ---------------------------------------------------------------- *)

  (* the parked stamp's own log-length receipt, exported off the token
     ([TsoCtxTwin2.ctx_parked_llb]) -- what the proc-lock payload carries
     to the acquire leaf *)
  (* A6.105: the log-length receipt straight off the interpretation -- the
     one resource a store leaf can hand out beside a freshly minted window,
     and the right half of [WpLock.lk_floor]. *)
  Lemma tso_interp_loglen_llb (g : gstate) :
    tso_interp_at riscv_eraGS g -∗
    tso_interp_at riscv_eraGS g ∗ llb loglen_name (length g.(glog)).
  Proof.
    iIntros "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (llb_get with "Hlen") as "[Hlen #Hlb]".
    iFrame "Hlb". iExists TM, LM. iFrame "Hts Hm Hlen Hv". by iPureIntro.
  Qed.

  Lemma ctx_parked_llb ξ T :
    ctx_parked ξ T -∗ ctx_parked ξ T ∗ llb loglen_name T.
  Proof.
    rewrite ctx_parked_unseal /ctx_parked_def.
    iIntros "(%D & Hat & #HT & %HDT)".
    iSplitL "Hat"; last iExact "HT".
    iExists D. iFrame "Hat HT". by iPureIntro.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE PRISTINE BYTE, and the load gate that needs NO context         *)
  (* (tso-machine-flip.md §6 amendment A6.10).                          *)
  (*                                                                   *)
  (* [ctx_load_ok] above is the general gate and it costs a ledger fact *)
  (* plus a running token.  There is a second, much cheaper one, and it *)
  (* is the RAW tiers' only honest way to discharge §6's                 *)
  (* [Mobl_ram_plain]: a byte whose LATEST WRITE IS THE ERA IMAGE --     *)
  (* timestamp 0 -- is visible to EVERY agent at EVERY view             *)
  (* ([TsoMemPa.read_down_0]: [visibleb h tv log 0] is unconditionally   *)
  (* true), so its value is the same no matter where the loading hart's  *)
  (* view sits and no matter who else is running.  This is the standing  *)
  (* text-is-timestamp-0 ruling, stated as a RESOURCE and extended from  *)
  (* text to every never-written image byte.                             *)
  (*                                                                   *)
  (* THE RESOURCE IS THE TIMESTAMP ELEMENT AT 0, DISCARDED.  Persistent  *)
  (* and duplicable, so it costs a holder nothing and can be handed to   *)
  (* every consumer of an image byte at once; and DISCARDED is exactly   *)
  (* the right strength, because it also says the byte can never be      *)
  (* STORED to again (a store must UPDATE the element, which a discarded *)
  (* one forbids).  Read-only-forever and readable-from-anywhere are the *)
  (* same fact here, which is why one resource says both.                *)
  (*                                                                   *)
  (* WHO MINTS IT: the era's initial-state ghosts (step 6 / adequacy),   *)
  (* beside [kernel_text]/[kernel_data]'s own mints -- the image is      *)
  (* where timestamp 0 comes from.  WHO CONSUMES IT: every raw-tier load *)
  (* of an image byte, [WpMmodeLoad]'s [phys_word_pointsto] leaf first   *)
  (* (see the amendment for the exact statement it wants).              *)
  (* ---------------------------------------------------------------- *)
  (* A6.63 / carve Q3: THE ALIAS.  This was a character-for-character
     duplicate of [RiscvPtsto.pristine_elem] under a second name, which is
     how the two drift apart.  DIRECTION IS FIXED BY IMPORT ORDER: TsoCtx
     imports RiscvPtsto, so [pristine_elem] is the definition and this is
     the alias -- never the other way round.  Kept as a [Definition] (not a
     [Notation]) so the two persistence/timeless instances below and every
     existing [rewrite /pristine_byte] keep working; the bodies are
     convertible, so no proof in the tree changes. *)
  Definition pristine_byte (a : Arch.pa) : iProp Σ := pristine_elem a.

  Global Instance pristine_byte_persistent a : Persistent (pristine_byte a).
  Proof. rewrite /pristine_byte. apply _. Qed.
  Global Instance pristine_byte_timeless a : Timeless (pristine_byte a).
  Proof. rewrite /pristine_byte. apply _. Qed.

  Definition pristine_win (a : Arch.pa) (n : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 n, pristine_byte (pa_add a j))%I.

  Global Instance pristine_win_persistent a n : Persistent (pristine_win a n).
  Proof. rewrite /pristine_win. apply _. Qed.

  (* THE GATE.  Note what is NOT quantified away: the conclusion holds at
     EVERY agent and EVERY view, so a caller does not have to know its own
     hart's view, its context's bound, or the log's length.  That is the
     whole point -- it is the one load fact a raw byte can carry. *)
  Lemma pristine_read_ok (g : gstate) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    phys_pointsto a dq v -∗ pristine_byte a -∗
    ⌜∀ (h : agent) (tv : nat), tso_read g.(gimg) g.(glog) h tv a = Some v⌝.
  Proof.
    iIntros "Hgh Hint Hpt #Hpr".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (ghost_map_lookup with "Hts Hpr") as %HTM.
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iPureIntro. intros h tv.
    apply (tso_read_of_latest _ _ _ _ _ 0%nat); [exact Hlat|].
    apply visibleb_below. lia.
  Qed.

  (* the window form, in the shape [HartMLoad.robl_ram] is stated at --
     [∀ tv'] with no lower bound at all, so the caller's [tv <= tv'] and
     [tv' <= length log] premises are simply not needed *)
  Lemma pristine_read_bytes_ok (g : gstate) (a : Arch.pa) (n : N) {m : N}
      (w : bv m) (dq : dfrac) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       phys_pointsto (pa_add a j) dq (nth_byte w j)) -∗
    pristine_win a (N.to_nat n) -∗
    ⌜∀ (h : agent) (tv : nat),
       tso_read_bytes g.(gimg) g.(glog) h tv a n w⌝.
  Proof.
    iIntros "Hgh Hint Hb #Hpr".
    iAssert (⌜∀ j : nat, (N.of_nat j < n)%N →
               ∀ (h : agent) (tv : nat),
                 tso_read g.(gimg) g.(glog) h tv (pa_add a j)
                 = Some (nth_byte w j)⌝)%I with "[Hgh Hint Hb]" as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hb")
        as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hpr")
        as "Hprj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (pristine_read_ok g (pa_add a j) dq (nth_byte w j)
                with "Hgh Hint Hbj Hprj"). }
    iPureIntro. intros h tv j Hj. exact (HH j Hj h tv).
  Qed.

  (* THE IMAGE MINT -- and the reason the clean arm is [llb]-shaped.  A
     DISCARDED byte plus its pristine receipt IS a ledger fact, at EVERY
     context, with NO ghost step and NO update modality: the timestamp
     element is the pristine one (discarded, so the fractions line up
     exactly) and the justification is [llb]'s [t = 0] arm, which mentions
     no context.  This is what makes the ∀-context image resources
     ([KernelDataInv.kernel_data]'s [∀ ξ, …], kernel text) MINTABLE: with a
     bare [mono_nat_lb_own] the mint would need one bupd per context, i.e.
     infinitely many under the ∀, and the boot carve could not build the
     fact it hands the whole tree.

     [ppn] is passed explicitly and pinned by the caller's own [kmap_at]
     ([kmap_at_agree]), because the mem fact's page number is existential
     and the pristine receipt lives at the PHYSICAL address. *)
  Lemma ctx_pointsto_of_pristine `{KTR : !CurKtier} (ξ : CtxId)
      (ppn : mword 44) (a : Arch.pa) (v : bv 8) :
    kmap_at (svpn_of a) ppn KP_rw -∗
    mem_pointsto a DfracDiscarded v -∗
    pristine_byte (pa_of ppn a) -∗
    ctx_pointsto ξ a DfracDiscarded v.
  Proof.
    rewrite ctx_pointsto_unseal /ctx_pointsto_def /mem_pointsto.
    iIntros "#Hk (%ppn' & #Hk' & %Hc & %Hr & %Hp & Hpt) #Hpr".
    iDestruct (kmap_at_agree with "Hk Hk'") as %[<- _].
    iExists ppn, 0%nat. iFrame "Hk Hpt Hpr".
    iSplit; first done. iSplit; first done. iSplit; first done.
    iLeft. iApply llb_0.
  Qed.


  (* THE VA-SIDE RECEIPT, which is the one a caller can actually hold.
     [pristine_byte] lives at a PHYSICAL address (the interpretation is keyed
     there), while every consumer of an image byte names it by its VA and
     does not know the page number -- so the receipt carries its own page
     claim, and [kmap_at_agree] is what lets it meet the [mem_pointsto]'s
     existential.  Persistent, like both of its conjuncts. *)
  Definition pristine_va `{KTR : !CurKtier} (a : Arch.pa) : iProp Σ :=
    (∃ ppn : mword 44,
       kmap_at (svpn_of a) ppn KP_rw ∗ pristine_byte (pa_of ppn a))%I.

  Global Instance pristine_va_persistent `{KTR : !CurKtier} a :
    Persistent (pristine_va a).
  Proof. rewrite /pristine_va. apply _. Qed.

  Lemma ctx_pointsto_of_pristine_va `{KTR : !CurKtier} (ξ : CtxId)
      (a : Arch.pa) (v : bv 8) :
    mem_pointsto a DfracDiscarded v -∗ pristine_va a -∗
    ctx_pointsto ξ a DfracDiscarded v.
  Proof.
    iIntros "Hm (%ppn & #Hk & #Hpr)".
    iApply (ctx_pointsto_of_pristine ξ ppn a v with "Hk Hm Hpr").
  Qed.


  (* ================================================================== *)
  (* THE PHYSICAL LEDGER BYTE, AND THE STORE GATE                       *)
  (* (tso-machine-flip.md §6 amendment A6.16)                           *)
  (*                                                                   *)
  (* WHY A SECOND BYTE FAMILY AT ALL.  [ctx_pointsto] is keyed by VA and *)
  (* carries [mem_pointsto]'s kernel-mapping plumbing; the MACHINE, and  *)
  (* every one of A6.14's four members, works at PHYSICAL addresses --   *)
  (* [HartMemRun.bytes_own] is a [gmap Arch.pa], [WpMmodeStore] and      *)
  (* [KptTree] hold [↦ₚ₈], the DMA lease is a [phys_map].  So the ledger *)
  (* fact those tiers need is [phys_pointsto] PLUS the timestamp element *)
  (* PLUS the clean/dirty bit -- [ctx_pointsto]'s body with the VA       *)
  (* plumbing stripped off, which is exactly what the era interp and the *)
  (* twin's gates are stated over ([pristine_byte] is already keyed      *)
  (* physically, for the same reason).                                   *)
  (*                                                                   *)
  (* IT IS NOT A NEW TIER: [ctx_pointsto_phys] below is a [⊣⊢], so the   *)
  (* VA family IS the kmap claim over this one.  The gates are stated    *)
  (* here, once, and the VA forms are corollaries.                       *)
  (* ================================================================== *)
  Definition ctx_phys_pointsto_def (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) : iProp Σ :=
    (∃ t : nat,
       phys_pointsto a dq v ∗
       a ↪[ts_name]{dq} (t, ts_pay_none) ∗
       (llb (ctx_bound_name ξ) t                          (* CLEAN *)
        ∨ dset_in (ctx_dirty_name ξ) (t, a)))%I.          (* DIRTY *)
  Lemma ctx_phys_pointsto_aux : { f | f = ctx_phys_pointsto_def }.
  Proof. by eexists. Qed.
  Definition ctx_phys_pointsto (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) : iProp Σ := proj1_sig ctx_phys_pointsto_aux ξ a dq v.
  Lemma ctx_phys_pointsto_unseal (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) :
    ctx_phys_pointsto ξ a dq v = ctx_phys_pointsto_def ξ a dq v.
  Proof.
    unfold ctx_phys_pointsto. by rewrite (proj2_sig ctx_phys_pointsto_aux).
  Qed.

  Global Instance ctx_phys_pointsto_timeless ξ a dq v :
    Timeless (ctx_phys_pointsto ξ a dq v).
  Proof. rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def. apply _. Qed.
  Global Instance ctx_phys_pointsto_discarded_persistent ξ a v :
    Persistent (ctx_phys_pointsto ξ a DfracDiscarded v).
  Proof. rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def. apply _. Qed.

  (* the forgetful projection at this tier (A6.8's price, same words) *)
  Lemma ctx_phys_pointsto_forget ξ a dq v :
    ctx_phys_pointsto ξ a dq v ⊢ phys_pointsto a dq v.
  Proof.
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    by iIntros "(% & $ & _)".
  Qed.

  Lemma ctx_phys_pointsto_ram ξ a dq v :
    ctx_phys_pointsto ξ a dq v ⊢ ⌜addr_is_ram a⌝.
  Proof.
    rewrite ctx_phys_pointsto_forget /phys_pointsto. by iIntros "[_ $]".
  Qed.


  (* THE VA FAMILY IS THIS ONE UNDER THE KMAP CLAIM.  Both directions:
     the ledger residue never moves, only the mapping plumbing does. *)
  Lemma ctx_pointsto_phys `{KTR : !CurKtier} (ξ : CtxId) (va : Arch.pa)
      (dq : dfrac) (v : bv 8) :
    ctx_pointsto ξ va dq v ⊣⊢
    ∃ ppn : mword 44,
      kmap_at (svpn_of va) ppn KP_rw ∗
      ⌜(uint va < 274877906944)%Z⌝ ∗
      ⌜ktier_pin cur_ktier ppn va⌝ ∗
      ctx_phys_pointsto ξ (pa_of ppn va) dq v.
  Proof.
    iSplit.
    - rewrite ctx_pointsto_unseal /ctx_pointsto_def.
      iIntros "(%ppn & %t & #Hk & %Hc & %Hr & %Hp & Hpt & Hts & Hbit)".
      iExists ppn. iFrame "Hk". iSplit; [done|]. iSplit; [done|].
      rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def /phys_pointsto.
      iExists t. iFrame "Hpt Hts Hbit". by iPureIntro.
    - iIntros "(%ppn & #Hk & %Hc & %Hp & Hb)".
      rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def /phys_pointsto
              ctx_pointsto_unseal /ctx_pointsto_def.
      iDestruct "Hb" as "(%t & [Hpt %Hr] & Hts & Hbit)".
      iExists ppn, t. iFrame "Hk Hpt Hts Hbit". by iPureIntro.
  Qed.

  (* ================================================================== *)
  (* THE VISIBILITY-FREE BYTE (tso-port.md §0.26′, A6.85).              *)
  (*                                                                   *)
  (* WHAT IT IS: the FUTURE half of ownership and nothing else -- the   *)
  (* physical fraction plus the byte's timestamp ELEMENT, at WHATEVER   *)
  (* history payload the element currently carries.  It licenses a      *)
  (* STORE (the store gate needs the element and nothing else -- see    *)
  (* [ctx_store_bytes], which destructs the ctx byte and [iClear]s the  *)
  (* bit) and it licenses NO LOAD (no clean/dirty justification, so     *)
  (* [ctx_load_ok] cannot fire).                                       *)
  (*                                                                   *)
  (* WHY IT IS THE FREE PAGE'S TIER.  §0.26′: [kfree]'s classical       *)
  (* precondition [∃ x, a ↦ x] asserts a value DETERMINATE AT THE       *)
  (* FREER'S OWN VIEW, and under TSO that is surplus -- a page whose    *)
  (* lock another CPU just released has no value well-known to the      *)
  (* freer, and freeing must not require one.  Determinacy re-mints     *)
  (* itself at the next write with NO evidence (a store does not read;  *)
  (* one's own write is visible by forwarding), and xv6's kfree/kalloc  *)
  (* memset immediately, so the allocator path never reads before       *)
  (* writing.                                                         *)
  (*                                                                   *)
  (* AND THE ∃ OVER THE PAYLOAD IS THE RECLAMATION (§0.26′ (ii)).  A    *)
  (* history claim -- a canon pin, a lock window -- is an OBLIGATION on *)
  (* the log recorded IN the element; at FULL element ownership,        *)
  (* forgetting it is a pure weakening of the interpretation, so the    *)
  (* "ghost reset" the ruling names needs no evidence AND, here, no     *)
  (* ghost step at all: [phys_ledger_wpay_free] below is an ⊢.  The     *)
  (* auth-side reset happens LAZILY, at the next store, which is the    *)
  (* only place the interp is in hand ([A6.68]'s rule: [own_context]    *)
  (* outside a leaf, [tso_interp_at] inside one) -- and the next store  *)
  (* is exactly [kfree]'s own memset.                                  *)
  (* ================================================================== *)
  (* THE VALUE IS HIDDEN TOO, and that is not tidiness: the byte's value
     is ghost bookkeeping for the interp's flat-memory tie -- it promises
     nothing, licenses nothing, and is re-established by the very store
     this resource exists to license.  Leaving it in the spelling would
     let a reader mistake it for a stability claim, which is precisely
     the claim §0.26′ says the freer does not have.  So it sits beside
     the element, existentially, and is invisible at every tier above. *)
  Definition phys_free (a : Arch.pa) (dq : dfrac) : iProp Σ :=
    (∃ (v : bv 8) (e : ts_elem),
       phys_pointsto a dq v ∗ a ↪[ts_name]{dq} e)%I.

  Global Instance phys_free_timeless a dq : Timeless (phys_free a dq).
  Proof. rewrite /phys_free. apply _. Qed.

  Lemma phys_free_ram a dq : phys_free a dq ⊢ ⌜addr_is_ram a⌝.
  Proof.
    rewrite /phys_free /phys_pointsto. by iIntros "(% & % & [_ $] & _)".
  Qed.


  (* the REGISTERED byte forgets to the visibility-free one: the bit is
     dropped, and with it the load license, nothing else.  (The
     [phys_ledger*] family's own weakenings are stated below, beside
     their definitions.) *)
  Lemma ctx_phys_pointsto_free ξ a dq v :
    ctx_phys_pointsto ξ a dq v ⊢ phys_free a dq.
  Proof.
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def /phys_free.
    iIntros "(%t & Hpt & Hts & _)". iExists v, (t, ts_pay_none). iFrame.
  Qed.


  (* ---------------------------------------------------------------- *)
  (* THE VA-KEYED VISIBILITY-FREE BYTE.  [ctx_pointsto]'s body with the *)
  (* justification stripped and the kmap plumbing kept -- so a free     *)
  (* page's bytes still know WHERE they are (which is what the store    *)
  (* leaf's translation needs) and no longer claim WHAT they are.       *)
  (* ---------------------------------------------------------------- *)
  Definition mem_free `{KTR : !CurKtier} (a : Arch.pa) (dq : dfrac)
      : iProp Σ :=
    (∃ ppn : mword 44,
       kmap_at (svpn_of a) ppn KP_rw ∗
       ⌜(uint a < 274877906944)%Z⌝ ∗
       ⌜ktier_pin cur_ktier ppn a⌝ ∗
       phys_free (pa_of ppn a) dq)%I.

  Global Instance mem_free_timeless `{KTR : !CurKtier} a dq :
    Timeless (mem_free a dq).
  Proof. rewrite /mem_free. apply _. Qed.

  Lemma ctx_pointsto_free `{KTR : !CurKtier} (ξ : CtxId) (a : Arch.pa)
      (dq : dfrac) (v : bv 8) :
    ctx_pointsto ξ a dq v ⊢ mem_free a dq.
  Proof.
    rewrite ctx_pointsto_phys /mem_free.
    iIntros "(%ppn & #Hk & %Hc & %Hp & Hb)".
    iExists ppn. iFrame "Hk". iSplit; [done|]. iSplit; [done|].
    by iApply ctx_phys_pointsto_free.
  Qed.


  (* ---------------------------------------------------------------- *)
  (* A6.61: THE TIER WEAKENING, the ctx twin of                        *)
  (* [RiscvPtsto.mem_ktier_mono].  It is the one kit item the owners'   *)
  (* mechanical residue needed and the tree did not have: four sites    *)
  (* ([ProofCreateParts] x2, [ProofForkretParts], [ProofKexecTail])     *)
  (* reached KT1 from a KT0 datum by dropping to the raw tower, using   *)
  (* [mem_ktier_mono] there and crossing back -- and the return leg is  *)
  (* the direction the flip makes FALSE.                                *)
  (*                                                                    *)
  (* It is sound for EXACTLY the raw lemma's reason and no new one: of  *)
  (* the seven conjuncts of [ctx_pointsto_def] only [ktier_pin] mentions*)
  (* the tier, and it weakens ([ktier_pin_mono]; at KT1 there is nothing*)
  (* to prove).  The timestamp, the ledger element and the clean/dirty  *)
  (* bit are tier-BLIND -- which is why this is a weakening and not a   *)
  (* re-mint, and why A6.9's prohibition is not in play.                *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_pointsto_ktier_mono (kt kt' : ktier) `{!KtierLe kt kt'}
      (ξ : CtxId) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    ctx_pointsto (KTR := kt) ξ a dq v ⊢ ctx_pointsto (KTR := kt') ξ a dq v.
  Proof.
    rewrite !ctx_pointsto_unseal /ctx_pointsto_def.
    iIntros "(%ppn & %t & #Hk & %Hc & %Hr & %Hp & Hpt & Hts & Hbit)".
    iExists ppn, t. iFrame "Hk Hpt Hts Hbit".
    iPureIntro. split_and!.
    - exact Hc.
    - exact Hr.
    - exact (ktier_pin_mono kt kt' ppn a Hp).
  Qed.

  (* ================================================================== *)
  (* THE WRITE-ONLY LEDGER BYTE, AND THE CONTEXT-FREE STORE GATE        *)
  (* (tso-machine-flip.md §6 amendment A6.20)                           *)
  (*                                                                   *)
  (* A store's four ghost steps need the TIMESTAMP ELEMENTS.  They do    *)
  (* NOT need a context: the clean/dirty BIT is what licenses a later    *)
  (* plain LOAD, and a byte nobody loads through the ledger does not     *)
  (* need one.  Dropping it gives a resource that                        *)
  (*   - can be stored to for ever (it holds the element), and           *)
  (*   - licenses no plain load (it holds no bit),                       *)
  (* which is exactly right for memory that is WRITTEN by one tier and   *)
  (* READ through a strongly-ordered arm.                                *)
  (*                                                                   *)
  (* ITS CONSUMER IS THE PAGE TABLE, and that is why it exists.  The     *)
  (* kernel page table's slots live inside a BARE [inv] shared by every  *)
  (* S-mode thread ([KptShare.kpt_inv]), so its body cannot name a       *)
  (* context (tso-port.md §0.8' ruling 2) -- and it does not have to:    *)
  (* a PTE is read at [Read_ttw], RULING 1's FLAT arm, so no load        *)
  (* license is ever wanted, while the Svadu A/D write-back is a real    *)
  (* store and owes the append.  Context-free ledger is the ONLY sound   *)
  (* shape there and it is also the cheapest.                            *)
  (*                                                                   *)
  (* (A6.17 measured this shape at [WpMmodeStore] and rejected it there, *)
  (* because [own_context] already arrives at the M-mode bracket and a   *)
  (* loadable byte is strictly stronger.  Here the judgement reverses:   *)
  (* [own_context] CANNOT be used, because the owner is an invariant.)   *)
  (* ================================================================== *)
  Definition phys_ledger_def (a : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ t : nat, phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, ts_pay_none))%I.
  Lemma phys_ledger_aux : { f | f = phys_ledger_def }.
  Proof. by eexists. Qed.
  Definition phys_ledger (a : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
    proj1_sig phys_ledger_aux a dq v.
  Lemma phys_ledger_unseal (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    phys_ledger a dq v = phys_ledger_def a dq v.
  Proof. unfold phys_ledger. by rewrite (proj2_sig phys_ledger_aux). Qed.

  Global Instance phys_ledger_timeless a dq v : Timeless (phys_ledger a dq v).
  Proof. rewrite phys_ledger_unseal /phys_ledger_def. apply _. Qed.

  Lemma phys_ledger_forget a dq v : phys_ledger a dq v ⊢ phys_pointsto a dq v.
  Proof.
    rewrite phys_ledger_unseal /phys_ledger_def. by iIntros "(% & $ & _)".
  Qed.

  (* two ledger bytes, one of them fully owned, cannot name the same address
     -- the DMA lease's disjointness argument, at the sealed tier (A6.48) *)
  Lemma phys_ledger_ne (a1 a2 : Arch.pa) (dq2 : dfrac) (v1 v2 : bv 8) :
    phys_ledger a1 (DfracOwn 1) v1 -∗ phys_ledger a2 dq2 v2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (phys_ledger_forget with "H1") as "Hp1".
    iDestruct (phys_ledger_forget with "H2") as "Hp2".
    iEval (rewrite /phys_pointsto) in "Hp1". iDestruct "Hp1" as "[Hp1 _]".
    iEval (rewrite /phys_pointsto) in "Hp2". iDestruct "Hp2" as "[Hp2 _]".
    by iDestruct (pointsto_ne with "Hp1 Hp2") as %?.
  Qed.

  Lemma phys_ledger_ram a dq v : phys_ledger a dq v ⊢ ⌜addr_is_ram a⌝.
  Proof.
    iIntros "H". iDestruct (phys_ledger_forget with "H") as "Hp".
    iEval (rewrite /phys_pointsto) in "Hp". by iDestruct "Hp" as "[_ $]".
  Qed.

  (* [phys_ledger] with its timestamp EXPOSED -- the sealed form hides  *)
  (* [t] existentially and every discharge below has to compare it      *)
  (* against a receipt.                                                 *)
  Definition phys_ledger_at (a : Arch.pa) (dq : dfrac) (v : bv 8)
      (t : nat) : iProp Σ :=
    (phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, ts_pay_none))%I.

  Global Instance phys_ledger_at_timeless a dq v t :
    Timeless (phys_ledger_at a dq v t).
  Proof. rewrite /phys_ledger_at. apply _. Qed.


  (* ---------------------------------------------------------------- *)
  (* THE CANON-PINNED LEDGER BYTE (tso-pin-memo.md §5.2; ruling 2).     *)
  (*                                                                   *)
  (* The SAME two authorities as [phys_ledger_at], with the element's   *)
  (* option arm SET.  What the pin buys is stated by the interp, not    *)
  (* here: [(t, Some (Sv, B))] ties the address to [TsoMemPa.pin_ok]    *)
  (* -- "from view [B] on, EVERY agent's read of [a] lands in [Sv]" --  *)
  (* which IS the kernel-PT walk's discharge conclusion.  Carrying the  *)
  (* bound in the ELEMENT is what keeps [kpt_inv]'s arity fixed (142    *)
  (* mention sites across 36 files) and what leaves every existing      *)
  (* store gate sound with no new premise: [phys_ledger] /              *)
  (* [ctx_pointsto] / [ctx_phys_pointsto] all pin the option to [None]  *)
  (* by DEFINITION, so the tie's frame arm applies definitionally.      *)
  (* ---------------------------------------------------------------- *)
  Definition phys_ledger_pin (a : Arch.pa) (dq : dfrac) (v : bv 8)
      (t B : nat) (Sv : gset (bv 8)) : iProp Σ :=
    (phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, ts_pay_pin Sv B))%I.

  Global Instance phys_ledger_pin_timeless a dq v t B Sv :
    Timeless (phys_ledger_pin a dq v t B Sv).
  Proof. rewrite /phys_ledger_pin. apply _. Qed.


  Lemma phys_ledger_pin_forget a dq v t B Sv :
    phys_ledger_pin a dq v t B Sv ⊢ phys_pointsto a dq v.
  Proof. by iIntros "[$ _]". Qed.

  (* the reader's per-byte fragment: the ledger byte with the WINDOW arm
     of its element set.  A window is held as [n] of these, all naming the
     same [(base, n, z, cp, own)] and differing only in the offset. *)
  Definition phys_ledger_wpay (a : Arch.pa) (dq : dfrac) (v : bv 8) (t : nat)
      (W : ts_win) : iProp Σ :=
    (phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, ts_pay_win W))%I.

  Global Instance phys_ledger_wpay_timeless a dq v t W :
    Timeless (phys_ledger_wpay a dq v t W).
  Proof. rewrite /phys_ledger_wpay. apply _. Qed.


  Lemma phys_ledger_at_ledger a dq v t :
    phys_ledger_at a dq v t ⊢ phys_ledger a dq v.
  Proof.
    rewrite /phys_ledger_at phys_ledger_unseal /phys_ledger_def.
    iIntros "[Hp He]". iExists t. iFrame.
  Qed.

  Lemma phys_ledger_of_at a dq v :
    phys_ledger a dq v ⊢ ∃ t, phys_ledger_at a dq v t.
  Proof.
    rewrite phys_ledger_unseal /phys_ledger_def /phys_ledger_at.
    iIntros "(%t & Hp & He)". iExists t. iFrame.
  Qed.

  Lemma phys_ledger_at_forget a dq v t :
    phys_ledger_at a dq v t ⊢ phys_pointsto a dq v.
  Proof. by iIntros "[$ _]". Qed.

  (* ---------------------------------------------------------------- *)
  (* §0.26′ (ii): THE EVIDENCE-FREE RECLAMATION.  Every history-shaped  *)
  (* claim this port carries lives in the byte's ELEMENT -- the canon   *)
  (* pin's [(Sv, B)], the lock window's [W] -- and at FULL element      *)
  (* ownership dropping it is an ⊢, not a ghost step: the ∃ over the    *)
  (* element in [phys_free] IS the reset, and the interpretation's      *)
  (* obligation disappears with the claim rather than being discharged. *)
  (* The auth side catches up at the next store ([ledger_store_bytes] / *)
  (* [ctx_store_bytes] below both re-key the element to                 *)
  (* [(S i, ts_pay_none)] from WHATEVER it was).                        *)
  (*                                                                   *)
  (* THIS IS WHAT UNBLOCKS [ProofPipeclose:749] (A6.84 §(2)): a lock on *)
  (* a [kalloc]'d page must be able to DIE, and its owner word is a     *)
  (* [phys_ledger_wpay] cell.  It cannot re-enter the ctx tower (that   *)
  (* needs a drain) -- but it does not have to: the page it is being    *)
  (* handed back into is VISIBILITY-FREE.                               *)
  (* ---------------------------------------------------------------- *)
  Lemma phys_ledger_free a dq v : phys_ledger a dq v ⊢ phys_free a dq.
  Proof.
    rewrite phys_ledger_unseal /phys_ledger_def /phys_free.
    iIntros "(%t & Hp & He)". iExists v, (t, ts_pay_none). iFrame.
  Qed.


  Lemma phys_ledger_wpay_free a dq v t W :
    phys_ledger_wpay a dq v t W ⊢ phys_free a dq.
  Proof.
    rewrite /phys_ledger_wpay /phys_free.
    iIntros "[Hp He]". iExists v, (t, ts_pay_win W). iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE AUTHOR TIE (A6.47 ruling 1 -- the ratified replacement for the *)
  (* withdrawn [sfence.vma] drain).  The log's entries are PERSISTED at *)
  (* append (§4), so naming one costs nothing and is duplicable; what   *)
  (* it buys is [TsoMemPa.visibleb]'s OWN-AUTHOR arm, i.e. STORE        *)
  (* FORWARDING: a hart always sees its own writes, at any view, with   *)
  (* no receipt and no fence.  That is hart 0's whole read story for    *)
  (* the page table it built between [kvminit] and [kvminithart] -- the *)
  (* boot path never migrates, so naming the AGENT is honest there.     *)
  (* ---------------------------------------------------------------- *)
  Definition ledger_msg_at (i : nat) (m : pwmsg) : iProp Σ :=
    (i ↪[logm_name]□ m)%I.

  Global Instance ledger_msg_at_persistent i m :
    Persistent (ledger_msg_at i m).
  Proof. rewrite /ledger_msg_at. apply _. Qed.
  Global Instance ledger_msg_at_timeless i m :
    Timeless (ledger_msg_at i m).
  Proof. rewrite /ledger_msg_at. apply _. Qed.

  (* THE READ LICENCE AT ONE TIMESTAMP, and the reason hart 0 and the
     secondaries end up using the SAME gate (which is what the withdrawn
     ruling wanted and this one delivers): "[t] is visible to [h] at every
     view at or above [B]" -- either because [t] is under the bound, or
     because [h] wrote it.  Structurally [TsoGhost.dirty_ok]'s disjunction,
     lifted off the dirty set and stated about a bare timestamp. *)
  Definition ledger_vis (h : agent) (B t : nat) : iProp Σ :=
    (⌜(t ≤ B)%nat⌝ ∨
     ∃ i m, ⌜t = S i⌝ ∗ ledger_msg_at i m ∗ ⌜pm_tid m = h⌝)%I.

  Global Instance ledger_vis_persistent h B t : Persistent (ledger_vis h B t).
  Proof. rewrite /ledger_vis. apply _. Qed.

  Lemma ledger_vis_below (h : agent) (B t : nat) :
    (t ≤ B)%nat -> ⊢ ledger_vis h B t.
  Proof. iIntros (Hle). iLeft. by iPureIntro. Qed.

  (* ================================================================== *)
  (* A6.120: THE CREATOR'S ARM IS THE CTX TOWER'S OWN DIRTY WITNESS.     *)
  (*                                                                      *)
  (* §0.38′ reads [WpLock.lk_floor] as "you received this handle, or you  *)
  (* wrote this lock" -- [ctx_pointsto]'s clean-vs-own-write disjunction *)
  (* surfacing in the handle.  Its right arm was spelled as a bare        *)
  (* [llb loglen_name lo], which says the floor is a LOG POSITION and     *)
  (* nothing about who wrote it; A6.113 measured that this cannot be     *)
  (* cashed at the read (the reader's view and a log position are         *)
  (* comparable only at an AMO), so every read needed the crossing        *)
  (* upgrade -- and the creator's own first acquire (kinit's kfree,       *)
  (* printfinit's printf: no AMO between initlock and holding()) had no   *)
  (* route at all.                                                        *)
  (*                                                                      *)
  (* The tower already records own writes: [ctx_at]'s dirty map [D] is a  *)
  (* ghost_map keyed by (timestamp, address), every entry justified by    *)
  (* [dirty_ok] -- "below my bound, or the message is MINE" -- which is   *)
  (* [ledger_vis] verbatim.  Entries are never deleted (a park stamps the *)
  (* record above all of them, [ctx_parked_def]; a resume raises the      *)
  (* bound past the stamp), so a PERSISTENT element fragment is a sound   *)
  (* witness for the lifetime of the context.  So the creator's arm is    *)
  (* [ctx_wrote ξ lo a]: ξ-indexed, hart-free, and cashed against the     *)
  (* running token in BOTH arms ([own_context_wrote_vis]).  Across a      *)
  (* crossing it travels as the LEFT arm for free ([ctx_dom_wrote_floor]: *)
  (* [ctx_dom] already carries [W ≤ B'] over the dirty watermark).        *)
  (*                                                                      *)
  (* The registration wants the key ABSENT, and [W]'s only semantics is   *)
  (* "a legal log position above every dirty key", so the bound          *)
  (* [W ≤ length log] must be taken BEFORE the store appends:            *)
  (* [own_context_expose_w] hands the watermark out, the store runs, and  *)
  (* [ctx_wrote_register] rebuilds the token with the new key -- the two  *)
  (* halves of one atomic step, split only so the append can sit between. *)
  (* ================================================================== *)
  Definition ctx_wrote (ξ : CtxId) (t : nat) (a : Arch.pa) : iProp Σ :=
    dset_in (ctx_dirty_name ξ) (t, a).

  Global Instance ctx_wrote_persistent ξ t a : Persistent (ctx_wrote ξ t a).
  Proof. rewrite /ctx_wrote. apply _. Qed.
  Global Instance ctx_wrote_timeless ξ t a : Timeless (ctx_wrote ξ t a).
  Proof. rewrite /ctx_wrote. apply _. Qed.

  (* the token with its dirty watermark exposed (and its [llb] peeled off) *)
  Definition own_context_w `{CID : CpuId} (ξ : CtxId) (W : nat) : iProp Σ :=
    (∃ (B K : nat) (D : gset (nat * Arch.pa)),
      ctx_at ξ 1 B D ∗
      view_lb view_name loglen_name (hart_agent cpu_id) K ∗ ⌜(B ≤ K)%nat⌝ ∗
      ⌜∀ k, k ∈ D → (k.1 ≤ W)%nat⌝ ∗
      [∗ set] k ∈ D, dirty_ok logm_name (hart_agent cpu_id) B k)%I.

  Lemma own_context_expose_w `{CID : CpuId} (ξ : CtxId) :
    own_context ξ -∗ ∃ W : nat, llb loglen_name W ∗ own_context_w ξ W.
  Proof.
    rewrite own_context_unseal /own_context_def.
    iIntros "(%B & %K & %W & %D & Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
    iExists W. iFrame "HW". iExists B, K, D. iFrame "Hat HK Hoks".
    iSplit; by iPureIntro.
  Qed.


  (* the store's own message, registered as a dirty key of its context *)
  Lemma ctx_wrote_register `{CID : CpuId} (ξ : CtxId) (W i : nat)
      (a : Arch.pa) (m : pwmsg) :
    (W ≤ i)%nat ->
    pm_tid m = hart_agent cpu_id ->
    own_context_w ξ W -∗ llb loglen_name (S i) -∗ ledger_msg_at i m ==∗
    own_context ξ ∗ ctx_wrote ξ (S i) a.
  Proof.
    iIntros (HWi Htid) "(%B & %K & %D & Hat & #HK & %HBK & %HDW & #Hoks) #HSi #Hm".
    iDestruct "Hat" as "[Hb Hd]".
    assert (Hnone : (S i, a) ∉ D).
    { intros Hin. specialize (HDW _ Hin). simpl in HDW. lia. }
    iMod (dset_insert _ D (S i, a) with "Hd") as "[Hd #Hfrag]".
    iModIntro. iSplitL.
    - rewrite own_context_unseal /own_context_def.
      iExists B, K, (S i), (D ∪ {[(S i, a)]}).
      iSplitL "Hb Hd"; [ rewrite /ctx_at; iFrame "Hb Hd" | ].
      iSplitR; [ iExact "HK" | ].
      iSplitR; [ iPureIntro; exact HBK | ].
      iSplitR; [ iExact "HSi" | ].
      iSplitR.
      { iPureIntro. intros k Hk.
        apply elem_of_union in Hk as [Hk | Hk].
        - specialize (HDW _ Hk). lia.
        - apply elem_of_singleton in Hk. subst k. simpl. lia. }
      rewrite (union_comm_L D) big_sepS_insert; last exact Hnone.
      iSplitR; [ | iExact "Hoks" ].
      rewrite /dirty_ok. iRight. iExists i, m. simpl.
      iSplitR; [ iPureIntro; reflexivity | ].
      iSplitR; [ rewrite /ledger_msg_at; iExact "Hm" | ].
      iPureIntro. exact Htid.
    - rewrite /ctx_wrote. iExact "Hfrag".
  Qed.

  (* THE CASH-IN: the witness against the running token is [ledger_vis] at
     the token's own view receipt -- the two-armed floor premise the racy
     read wants ([ledger_read_racy_ok]), on the creator's arm. *)
  Lemma own_context_wrote_vis `{CID : CpuId} (ξ : CtxId) (t : nat) (a : Arch.pa) :
    own_context ξ -∗ ctx_wrote ξ t a -∗
    own_context ξ ∗ ∃ K : nat,
      view_lb view_name loglen_name (hart_agent cpu_id) K ∗
      ledger_vis (hart_agent cpu_id) K t.
  Proof.
    iIntros "Hrun #Hw".
    iEval (rewrite own_context_unseal /own_context_def) in "Hrun".
    iDestruct "Hrun" as (B K W D) "(Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hat" as "[Hb Hd]".
    iEval (rewrite /ctx_wrote) in "Hw".
    iDestruct (dset_lookup with "Hd Hw") as %HD.
    iDestruct (big_sepS_elem_of _ _ (t, a) HD with "Hoks") as "#Hok".
    iSplitL.
    { iEval (rewrite own_context_unseal /own_context_def).
      iExists B, K, W, D. iFrame "Hb Hd HK HW Hoks". by iPureIntro. }
    iExists K. iFrame "HK".
    iEval (rewrite /dirty_ok) in "Hok". rewrite /ledger_vis.
    iDestruct "Hok" as "[%Hle | (%i & %m & %Ht & #Hm & %Htid)]".
    - iLeft. iPureIntro. simpl in Hle. lia.
    - iRight. iExists i, m. simpl in Ht.
      iSplitR; [ iPureIntro; exact Ht | ].
      iSplitR; [ rewrite /ledger_msg_at; iExact "Hm" | ].
      iPureIntro. exact Htid.
  Qed.

  (* THE TRANSPORT: a crossing turns the creator's arm into the receiver's
     LEFT arm for free -- [ctx_dom] already says the sender's dirty
     watermark is below the receiver's bound. *)
  Lemma ctx_dom_wrote_floor (ξ ξ' : CtxId) (t : nat) (a : Arch.pa) :
    ctx_dom ξ ξ' -∗ ctx_wrote ξ t a -∗ ctx_dom ξ ξ' ∗ ctx_floor ξ' t.
  Proof.
    rewrite ctx_dom_unseal /ctx_dom_def /ctx_floor /ctx_wrote.
    iIntros "(%B & %W & %B' & %D & [Hb Hd] & %HDW & %HBB' & %HWB' & #Hlb') #Hw".
    iDestruct (dset_lookup with "Hd Hw") as %HD.
    pose proof (HDW _ HD) as HtW. simpl in HtW.
    iSplitR "".
    - iExists B, W, B', D. iFrame "Hb Hd Hlb'". by iPureIntro.
    - iApply (llb_le _ B'); [lia|]. by iLeft.
  Qed.

  (* a log-length receipt, validated against the interpretation *)
  Lemma tso_interp_llb_valid (g : gstate) (K : nat) :
    tso_interp_at riscv_eraGS g -∗ llb loglen_name K -∗
    tso_interp_at riscv_eraGS g ∗ ⌜(K ≤ length g.(glog))%nat⌝.
  Proof.
    iIntros "Hint #HK".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (llb_valid with "Hlen HK") as %HKlen.
    iSplitL; [ | by iPureIntro ].
    iExists TM, LM. iFrame. iPureIntro. split_and!; done.
  Qed.

  (* A6.111: the projection to the machine's own predicate, BOTH ARMS.  It
     is the shape [TsoMemPa]'s window lemmas now take, and it is why the
     creator of a lock needs no receipt: its arm is [visibleb_own], which
     holds at every view. *)
  (* A6.126 §6: a view lower bound is under the interp's view -- what turns
     a reader's floor into [K ≤ tv] at every view the machine may choose *)
  Lemma view_lb_le_view `{CID : CpuId} (g : gstate) (K : nat) :
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) K -∗
    ⌜(K <= g.(gtv) cpu_id)%nat⌝.
  Proof.
    iIntros "Hint #HK".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    iDestruct (view_auth_valid with "Hvw HK") as %HK.
    rewrite avf_hart in HK. by iPureIntro.
  Qed.

  Lemma ledger_vis_visibleb `{CID : CpuId} (g : gstate) (B t : nat) :
    tso_interp_at riscv_eraGS g -∗
    ledger_vis (hart_agent cpu_id) B t -∗
    ⌜forall tv : nat, (B ≤ tv)%nat ->
       visibleb (hart_agent cpu_id) tv g.(glog) t = true⌝.
  Proof.
    iIntros "Hint Hvis".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct "Hvis" as "[%HtB | (%i & %mg & %Hti & Hi & %Htid)]".
    - iPureIntro. intros tv Htv. apply visibleb_below. lia.
    - iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
      iPureIntro. intros tv _. rewrite Hti.
      apply (visibleb_own _ _ _ _ mg); [by rewrite -HLM | done].
  Qed.

  (* A6.115: the ANCHOR projection.  [ledger_vis h B t] read the other way:
     either [t] is at or below [B], or the write at [t] is mine and visible at
     EVERY view.  This is the form the window's reassembly consumes, and it is
     why the owner cell's per-agent invariant ([ledger_vis h lo t], A6.114 §2)
     discharges the anchor for every hart rather than only the creator. *)
  Lemma ledger_vis_anchor `{CID : CpuId} (g : gstate) (B t : nat) :
    tso_interp_at riscv_eraGS g -∗
    ledger_vis (hart_agent cpu_id) B t -∗
    ⌜(t ≤ B)%nat \/
     forall tv : nat, visibleb (hart_agent cpu_id) tv g.(glog) t = true⌝.
  Proof.
    iIntros "Hint Hvis".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct "Hvis" as "[%HtB | (%i & %mg & %Hti & Hi & %Htid)]".
    - iPureIntro. by left.
    - iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
      iPureIntro. right. intros tv. rewrite Hti.
      apply (visibleb_own _ _ _ _ mg); [by rewrite -HLM | done].
  Qed.

  Lemma ledger_vis_mono (h : agent) (B B' t : nat) :
    (B ≤ B')%nat -> ledger_vis h B t -∗ ledger_vis h B' t.
  Proof.
    iIntros (Hle) "[%Hb|H]"; [iLeft; iPureIntro; lia | by iRight].
  Qed.


  (* ---------------------------------------------------------------- *)
  (* THE ERA-INITIAL ELEMENT, AND THE ONE BRIDGE OFF IT (A6.28's far end). *)
  (*                                                                      *)
  (* [pristine_byte] is the DISCARDED element and says "image byte, never  *)
  (* stored to again".  A region that IS stored to -- the M-mode boot      *)
  (* stack -- needs the same element at FULL ownership, and the boot carve *)
  (* has to be able to turn its raw bytes into ledger ones.  A6.9 is not   *)
  (* weakened by this: nothing here MINTS an element.  [ledger_elem0] is   *)
  (* handed out exactly once, by the era's initial-state ghost allocation  *)
  (* (the same place [BootCarve]'s image bytes and [pristine_va] receipts  *)
  (* come from), and these two laws only let the carve pair it back up     *)
  (* with the byte it belongs to.  The timestamp is 0 because at era       *)
  (* allocation the log is empty, which is also what makes the CLEAN arm   *)
  (* free ([TsoGhost.llb]'s [⌜K = 0⌝] disjunct -- no bupd, no context).    *)
  (* ---------------------------------------------------------------- *)
  Definition ledger_elem0 (a : Arch.pa) (dq : dfrac) : iProp Σ :=
    (a ↪[ts_name]{dq} (0%nat, ts_pay_none))%I.


  (* ...AND THE TIMESTAMP-EXPOSED TWIN, WHICH IS THE SAME TERM (A6.80).
     [ledger_wpay_mint] asks for [phys_ledger_at … 0] -- "this byte is
     unwritten in this era" -- and [ledger_elem0] IS that element, so the
     carve's cells reach the mint with no conversion at all.  What has to
     be arranged on the path is only that the timestamp is not SEALED
     away: [phys_ledger_of_elem] above is the sealing one, and every cell
     that will carry the racy payload must take THIS one instead.
     Both directions, because the carve builds and the mint consumes. *)
  Lemma phys_ledger_at0_of_elem (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    phys_pointsto a dq v -∗ ledger_elem0 a dq -∗ phys_ledger_at a dq v 0%nat.
  Proof. iIntros "Hp He". rewrite /phys_ledger_at /ledger_elem0. iFrame. Qed.


  Lemma ctx_phys_pointsto_of_elem (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) :
    phys_pointsto a dq v -∗ ledger_elem0 a dq -∗ ctx_phys_pointsto ξ a dq v.
  Proof.
    iIntros "Hp He".
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iExists 0%nat. iFrame "Hp He". iLeft. iApply llb_0.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* A6.63 THE READ-ONLY MINT, and it is what unblocks the last of the   *)
  (* shim tail.  A rodata byte lives at the RAW tower ([↦ₘ□],            *)
  (* KernelDataInv's image bytes) but the load leaves now demand a CTX   *)
  (* byte, and that direction is the one the flip makes false -- A6.62's *)
  (* four residual sites ([ProofPrintk] x2, [ProofSyscall],              *)
  (* [WpSconfLock]) are all this.                                        *)
  (*                                                                     *)
  (* It is payable, and for one reason: AT TIMESTAMP 0 THE CLEAN ARM IS  *)
  (* FREE ([TsoGhost.llb_0]).  So a byte needs no new authority to enter *)
  (* the tier -- it needs its LEDGER ELEMENT, and A6.9 says the era's    *)
  (* initial allocation is the only supplier of those.  That allocation  *)
  (* is the element carve, which is why this lemma could not be written  *)
  (* before it and why the carve unblocks step 5's tail as well as       *)
  (* step 6's (A6.62).                                                   *)
  (*                                                                     *)
  (* The caller supplies [ppn] with its [kmap_at] witness -- every leaf   *)
  (* site already holds one -- so the element is indexed at the PHYSICAL  *)
  (* address, exactly as [ctx_pointsto_def] holds it.                     *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_pointsto_of_ro `{KTR : !CurKtier} (ξ : CtxId) (a : Arch.pa)
      (ppn : mword 44) (dq : dfrac) (v : bv 8) :
    kmap_at (svpn_of a) ppn KP_rw -∗
    mem_pointsto a dq v -∗
    ledger_elem0 (pa_of ppn a) dq -∗
    ctx_pointsto ξ a dq v.
  Proof.
    iIntros "#Hk Hm He".
    rewrite /mem_pointsto.
    iDestruct "Hm" as (ppn') "(#Hk' & %Hc & %Hr & %Hp & Hpt)".
    iDestruct (kmap_at_agree with "Hk Hk'") as %[-> _].
    rewrite ctx_pointsto_unseal /ctx_pointsto_def.
    iExists ppn', 0%nat.
    iSplitR; [iExact "Hk'" |].
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iFrame "Hpt He". iLeft. iApply llb_0.
  Qed.


  (* ---------------------------------------------------------------- *)
  (* THE PINNED WORD TOWER (tso-pin-memo.md §5.4; A6.53's ruling 1).     *)
  (*                                                                    *)
  (* [phys_ledger_word]'s twin at the pinned byte, with the allowed sets *)
  (* indexed by BYTE OFFSET: for a kernel PT slot, byte 0's set is the   *)
  (* four-element A/D class of the slot's own word and bytes 1..7's are  *)
  (* singletons (§2's measurement).  The set FAMILY is a parameter here  *)
  (* on purpose -- naming [pte_canon] at this layer is the layering      *)
  (* violation candidate (iv) was rejected for; [PtTree.pte_slot_set]    *)
  (* supplies it.                                                       *)
  (* ---------------------------------------------------------------- *)
  Definition phys_ledger_word_pin (a : Arch.pa) (dq : dfrac) (w : bv 64)
      (B : nat) (Sf : nat -> TsoMemPa.byteset) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
     [∗ list] j ∈ seq 0 8, ∃ t : nat,
       phys_ledger_pin (pa_add a j) dq (nth_byte w j) t B (Sf j))%I.


  Lemma phys_ledger_word_pin_intro a dq w B Sf :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, ∃ t : nat,
       phys_ledger_pin (pa_add a j) dq (nth_byte w j) t B (Sf j))
    ⊢ phys_ledger_word_pin a dq w B Sf.
  Proof. iIntros (Hal) "H". by iFrame. Qed.

  Global Instance phys_ledger_word_pin_timeless a dq w B Sf :
    Timeless (phys_ledger_word_pin a dq w B Sf).
  Proof. rewrite /phys_ledger_word_pin. apply _. Qed.


  (* the REGISTERED byte forgets to the unregistered one -- the bit is what
     is dropped, and with it the load license, nothing else *)
  Lemma ctx_phys_pointsto_ledger ξ a dq v :
    ctx_phys_pointsto ξ a dq v ⊢ phys_ledger a dq v.
  Proof.
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def
            phys_ledger_unseal /phys_ledger_def.
    iIntros "(%t & Hpt & Hts & _)". iExists t. iFrame.
  Qed.

  (* A6.123: FORGETTING A CELL HANDS OUT ITS FLOOR.  A ctx cell leaving the
     tower for the ledger (a DMA lease, a lock's own words) carries its
     clean/dirty bit out with it as exactly [WpLock.lk_floor]'s two arms:
     clean is the context's bound past the stamp, dirty is the context's own
     write -- whose dirty element, no longer needed by a cell, can be
     PERSISTED into the witness A6.120 reads.  This is what lets the creator
     of a lease-held word (the boot's [virtio_disk_init]) hand the lock
     payload the floor its readers will cash. *)
  Lemma ctx_phys_pointsto_forget_floor (ξ : CtxId) (a : Arch.pa) (v : bv 8) :
    ctx_phys_pointsto ξ a (DfracOwn 1) v ==∗
    ∃ t : nat, phys_ledger_at a (DfracOwn 1) v t ∗
               (ctx_floor ξ t ∨ ctx_wrote ξ t a).
  Proof.
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def /phys_ledger_at
            /ctx_floor /ctx_wrote.
    iIntros "(%t & Hpt & Hts & [#Hcl | Hd])".
    - iModIntro. iExists t. iFrame "Hpt Hts". by iLeft.
    - iDestruct "Hd" as "#Hd".
      iModIntro. iExists t. iFrame "Hpt Hts". by iRight.
  Qed.

  (* >>> A6.125: THE HALF CTX CELL -- the pin-return crossing's instrument.
     A hart-written cell that a DEVICE must read while the hart keeps the
     right to get its ctx cell BACK splits in two: the lease takes a sealed
     half ([phys_ledger a ½ v], A6.124's shape), the ctx side keeps the
     other half WITH ITS ARM -- clean bound or the FULL dirty element.  The
     join is exact and rebuilds the full ctx cell; and the half transports
     along domination exactly as the full cell does
     ([ctx_morph_pointsto]'s proof: either arm becomes the receiver's clean
     one, the dirty fragment is dropped), so it can ride a lock payload.
     What CANNOT be done instead: rebuilding a ctx cell from a sealed
     ledger cell plus a persistent [ctx_wrote] -- the dirty arm of a full
     cell is the full element. <<< *)
  Definition ctx_phys_pointsto_h (ξ : CtxId) (a : Arch.pa) (v : bv 8) : iProp Σ :=
    (∃ t : nat,
       phys_pointsto a (DfracOwn (1/2)) v ∗
       a ↪[ts_name]{DfracOwn (1/2)} (t, TsoMemPa.ts_pay_none) ∗
       (llb (ctx_bound_name ξ) t ∨ dset_in (ctx_dirty_name ξ) (t, a)))%I.


  Lemma ctx_phys_pointsto_join (ξ : CtxId) (a : Arch.pa) (v v' : bv 8) :
    ctx_phys_pointsto_h ξ a v -∗ phys_ledger a (DfracOwn (1/2)) v' -∗
    ⌜v' = v⌝ ∗ ctx_phys_pointsto ξ a (DfracOwn 1) v.
  Proof.
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def /ctx_phys_pointsto_h
            phys_ledger_unseal /phys_ledger_def /phys_pointsto.
    iIntros "(%t & [Hp1 %Hr] & Ht1 & Harm) (%t' & [Hp2 _] & Ht2)".
    iDestruct (pointsto_agree with "Hp1 Hp2") as %Heqv. subst v'.
    iDestruct (ghost_map_elem_agree with "Ht1 Ht2") as %Heq.
    injection Heq as Ht. subst t'.
    iSplitR; [done|]. iExists t.
    rewrite (fractional_half (pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn 1) v))
            (fractional_half (a ↪[ts_name] (t, TsoMemPa.ts_pay_none))).
    iFrame "Hp1 Hp2 Ht1 Ht2 Harm". by iPureIntro.
  Qed.

  Global Instance ctx_morph_phys_pointsto_h (a : Arch.pa) (v : bv 8) :
    CtxMorph (λ ξ, ctx_phys_pointsto_h ξ a v).
  Proof.
    iIntros (ξ ξ') "Hd HP".
    rewrite ctx_dom_unseal /ctx_dom_def /ctx_phys_pointsto_h.
    iDestruct "Hd" as
      "(%B & %W & %B' & %D & [Hb Hdm] & %HDW & %HBB' & %HWB' & #Hlb')".
    iDestruct "HP" as "(%t & Hpt & Hts & Hbit)".
    iAssert (⌜(t ≤ B')%nat⌝)%I as %HtB'.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - iDestruct (llb_valid_q with "Hb Hcl") as %HtB.
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

  (* >>> A6.125 step 4: THE OFFER/KEEP SPLIT of a ctx cell (VirtioProto's
     PIN OFFER, A6.125's step-2 entry).  What goes out is the cell's memory
     at 1 with HALF its stamp: a raw ½ points-to plus a sealed ½ ledger cell
     -- enough for the lease to prove the new pin exclusive against its own
     ½ cells.  What stays is the other half of the stamp with the ARM
     ([ctx_cell_keep]); it transports like a ctx cell, and with the memory
     half the lease hands back ([pin_back]) it is exactly
     [ctx_phys_pointsto_h] again. <<< *)
  Definition ctx_cell_keep (ξ : CtxId) (a : Arch.pa) : iProp Σ :=
    (∃ t : nat,
       a ↪[ts_name]{DfracOwn (1/2)} (t, TsoMemPa.ts_pay_none) ∗
       (llb (ctx_bound_name ξ) t ∨ dset_in (ctx_dirty_name ξ) (t, a)))%I.

  Lemma ctx_phys_pointsto_offer_split (ξ : CtxId) (a : Arch.pa) (v : bv 8) :
    ctx_phys_pointsto ξ a (DfracOwn 1) v ⊢
    (phys_pointsto a (DfracOwn (1/2)) v ∗ phys_ledger a (DfracOwn (1/2)) v) ∗
    ctx_cell_keep ξ a.
  Proof.
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def /ctx_cell_keep
            phys_ledger_unseal /phys_ledger_def /phys_pointsto.
    iIntros "(%t & [Hp %Hr] & Hts & Harm)".
    iEval (rewrite (fractional_half (pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn 1) v)))
      in "Hp".
    iEval (rewrite (fractional_half (a ↪[ts_name] (t, TsoMemPa.ts_pay_none)))) in "Hts".
    iDestruct "Hp" as "[Hp1 Hp2]". iDestruct "Hts" as "[Ht1 Ht2]".
    iSplitR "Ht2 Harm".
    { iSplitL "Hp1"; [ iFrame "Hp1"; by iPureIntro |].
      iExists t. iFrame "Ht1 Hp2". by iPureIntro. }
    iExists t. iFrame "Ht2 Harm".
  Qed.

  Lemma ctx_cell_keep_back (ξ : CtxId) (a : Arch.pa) (v : bv 8) :
    ctx_cell_keep ξ a -∗ phys_pointsto a (DfracOwn (1/2)) v -∗
    ctx_phys_pointsto_h ξ a v.
  Proof.
    rewrite /ctx_cell_keep /ctx_phys_pointsto_h.
    iIntros "(%t & Ht & Harm) Hp". iExists t. iFrame.
  Qed.

  Global Instance ctx_morph_cell_keep (a : Arch.pa) :
    CtxMorph (λ ξ, ctx_cell_keep ξ a).
  Proof.
    iIntros (ξ ξ') "Hd HP".
    rewrite ctx_dom_unseal /ctx_dom_def /ctx_cell_keep.
    iDestruct "Hd" as
      "(%B & %W & %B' & %D & [Hb Hdm] & %HDW & %HBB' & %HWB' & #Hlb')".
    iDestruct "HP" as "(%t & Hts & Hbit)".
    iAssert (⌜(t ≤ B')%nat⌝)%I as %HtB'.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - iDestruct (llb_valid_q with "Hb Hcl") as %HtB.
        iPureIntro. lia.
      - iDestruct (dset_lookup with "Hdm Hdt") as %HDt.
        have HtW : ((t, a).1 ≤ W)%nat by apply HDW.
        simpl in HtW. iPureIntro. lia. }
    iClear "Hbit". iModIntro.
    iSplitL "Hb Hdm".
    { iExists B, W, B', D. iFrame "Hb Hdm Hlb'". by iPureIntro. }
    iExists t. iFrame "Hts".
    iLeft. rewrite /llb. iLeft.
    iApply (mono_nat_lb_own_le with "Hlb'"). lia.
  Qed.

  (* exclusivity at the REGISTERED physical tier, the companion of
     [phys_ledger_ne] one tier up: two owned bytes cannot name the same
     address.  A6.49's user-memory flip needs it -- [UmodeMem.umem_inj]
     derives the va -> pa injectivity from the ownership alone, and the
     sealed tier wants a law rather than an unfolding (A6.48's
     [phys_map_disj] precedent). *)
  Lemma ctx_phys_pointsto_ne (ξ1 ξ2 : CtxId) (a1 a2 : Arch.pa) (dq2 : dfrac)
      (v1 v2 : bv 8) :
    ctx_phys_pointsto ξ1 a1 (DfracOwn 1) v1 -∗
    ctx_phys_pointsto ξ2 a2 dq2 v2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ctx_phys_pointsto_ledger with "H1") as "H1".
    iDestruct (ctx_phys_pointsto_ledger with "H2") as "H2".
    by iApply (phys_ledger_ne with "H1 H2").
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE LOAD GATE AT THE PHYSICAL TIER ([ctx_load_ok] without the VA   *)
  (* plumbing): a running context's ledger byte predicts the machine's  *)
  (* plain load at EVERY admissible view advance of its hart.  Nothing  *)
  (* is consumed and the conclusion is PURE, so a caller keeps its      *)
  (* fact and its token.                                               *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_phys_load_ok `{CID : CpuId} (g : gstate) (ξ : CtxId)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ctx_phys_pointsto ξ a dq v -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝.
  Proof.
    rewrite own_context_unseal /own_context_def
            ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iIntros "Hgh Hint Hrun Hfact".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as ((Hflat & Htv & Hcov) & Hera).
    iDestruct "Hrun"
      as "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hfact" as "(%t & Hpt & Htse & Hbit)".
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iDestruct (view_auth_valid with "Hv HK") as %HKtvs.
    rewrite avf_hart in HKtvs.
    iAssert (⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
               visibleb (hart_agent cpu_id) tv' g.(glog) t = true⌝)%I
      as %Hvis.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - iDestruct (llb_valid with "Hb Hcl") as %HtB.
        iPureIntro. intros tv' Htv'. apply visibleb_below. lia.
      - iDestruct (dset_lookup with "Hd Hdt") as %HDt.
        iDestruct (big_sepS_elem_of _ _ _ HDt with "Hoks") as "[%HtB | Hown]".
        + iPureIntro. intros tv' Htv'. apply visibleb_below.
          simpl in HtB. lia.
        + iDestruct "Hown" as (i mg) "(%Hti & Hi & %Htid)".
          iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
          iPureIntro. intros tv' _. simpl in Hti. rewrite Hti.
          apply (visibleb_own _ _ _ _ mg); [by rewrite -HLM | done]. }
    iPureIntro. intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|by apply Hvis].
  Qed.

  (* the window form, in the shape [HartEvents.wp_hart_ram_read_plain]'s
     obligation is stated at ([Mobl_ram_plain]). *)
  Lemma ctx_phys_load_bytes_ok `{CID : CpuId} (g : gstate) (ξ : CtxId)
      (a : Arch.pa) (n : N) {m : N} (w : bv m) (dq : dfrac) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ([∗ list] j ∈ seq 0 (N.to_nat n),
       ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j)) -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv' a n w⌝.
  Proof.
    iIntros "Hgh Hint Hrun Hb".
    iAssert (⌜forall j : nat, (N.of_nat j < n)%N ->
               forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
                 tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' (pa_add a j)
                 = Some (nth_byte w j)⌝)%I as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 (N.to_nat n)) j j with "Hb")
        as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ctx_phys_load_ok g ξ (pa_add a j) dq (nth_byte w j)
                with "Hgh Hint Hrun Hbj"). }
    iPureIntro. intros tv' Htv' j Hj. exact (HH j Hj tv' Htv').
  Qed.

  (* ================================================================== *)
  (* THE PHYSICAL STAMPED BYTE (claude-notes/projects/icache.md):        *)
  (* [ctx_phys_pointsto]'s body plus the pure stamp "latest write at or  *)
  (* below [IK]", an instruction-view position.  [ctx_xpointsto]'s twin  *)
  (* at the tier [HartMemRun.bytes_own] is stated over.  The gates: a    *)
  (* data load reads it like any context byte ([ctx_phys_xload_ok]), a   *)
  (* FETCH reads it through the icache agent at every view from the      *)
  (* instruction view up once that view has passed the stamp             *)
  (* ([ctx_phys_xfetch_ok] / [_bytes_ok], [HartMFetch.fobl_ifetch]'s     *)
  (* shape); [ctx_phys_xstamp] mints it from a running context's fact at *)
  (* a [fence.i], whose drain covers every timestamp the context owns.   *)
  (* ================================================================== *)
  Definition ctx_phys_xpointsto_def (ξ : CtxId) (IK : nat) (a : Arch.pa)
      (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ t : nat,
       phys_pointsto a dq v ∗
       a ↪[ts_name]{dq} (t, ts_pay_none) ∗
       (llb (ctx_bound_name ξ) t ∨ dset_in (ctx_dirty_name ξ) (t, a)) ∗
       ⌜(t <= IK)%nat⌝)%I.
  Lemma ctx_phys_xpointsto_aux : { f | f = ctx_phys_xpointsto_def }.
  Proof. by eexists. Qed.
  Definition ctx_phys_xpointsto (ξ : CtxId) (IK : nat) (a : Arch.pa)
      (dq : dfrac) (v : bv 8) : iProp Σ :=
    proj1_sig ctx_phys_xpointsto_aux ξ IK a dq v.
  Lemma ctx_phys_xpointsto_unseal (ξ : CtxId) (IK : nat) (a : Arch.pa)
      (dq : dfrac) (v : bv 8) :
    ctx_phys_xpointsto ξ IK a dq v = ctx_phys_xpointsto_def ξ IK a dq v.
  Proof.
    unfold ctx_phys_xpointsto. by rewrite (proj2_sig ctx_phys_xpointsto_aux).
  Qed.

  Global Instance ctx_phys_xpointsto_timeless ξ IK a dq v :
    Timeless (ctx_phys_xpointsto ξ IK a dq v).
  Proof. rewrite ctx_phys_xpointsto_unseal /ctx_phys_xpointsto_def. apply _. Qed.

  Lemma ctx_phys_xpointsto_forget ξ IK a dq v :
    ctx_phys_xpointsto ξ IK a dq v ⊢ ctx_phys_pointsto ξ a dq v.
  Proof.
    rewrite ctx_phys_xpointsto_unseal /ctx_phys_xpointsto_def
            ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iIntros "(%t & Hp & Hts & Hbit & _)". iExists t. by iFrame.
  Qed.

  Lemma ctx_phys_xpointsto_mono ξ IK IK' a dq v :
    (IK <= IK')%nat ->
    ctx_phys_xpointsto ξ IK a dq v ⊢ ctx_phys_xpointsto ξ IK' a dq v.
  Proof.
    intros Hle. rewrite !ctx_phys_xpointsto_unseal /ctx_phys_xpointsto_def.
    iIntros "(%t & Hp & Hts & Hbit & %Ht)". iExists t. iFrame. iPureIntro. lia.
  Qed.

  (* the stamp, at a fence.i: [ctx_xstamp]'s physical twin *)
  Lemma ctx_phys_xstamp `{CID : CpuId} (g : gstate) (ξ : CtxId) (IK : nat)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    (g.(gtv) cpu_id <= IK)%nat ->
    (own_pub (hart_agent cpu_id) g.(glog) <= IK)%nat ->
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ctx_phys_pointsto ξ a dq v -∗
    tso_interp_at riscv_eraGS g ∗ own_context ξ ∗ ctx_phys_xpointsto ξ IK a dq v.
  Proof.
    intros Htv Hpub.
    rewrite own_context_unseal /own_context_def
            ctx_phys_pointsto_unseal /ctx_phys_pointsto_def
            ctx_phys_xpointsto_unseal /ctx_phys_xpointsto_def.
    iIntros "Hint Hrun Hfact".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as ((Hflat & Htv0 & Hcov) & Hera).
    iDestruct "Hrun"
      as "(%B & %K & %W & %D & [Hb Hd] & #HK & %HBK & #HW & %HDW & #Hoks)".
    iDestruct "Hfact" as "(%t & Hpt & Htse & Hbit)".
    iDestruct (view_auth_valid with "Hv HK") as %HKtvs.
    rewrite avf_hart in HKtvs.
    iAssert (⌜(t <= IK)%nat⌝)%I as %HtIK.
    { iDestruct "Hbit" as "[Hcl | Hdt]".
      - iDestruct (llb_valid with "Hb Hcl") as %HtB. iPureIntro. lia.
      - iDestruct (dset_lookup with "Hd Hdt") as %HDt.
        iDestruct (big_sepS_elem_of _ _ _ HDt with "Hoks") as "[%HtB | Hown]".
        + iPureIntro. simpl in HtB. lia.
        + iDestruct "Hown" as (i mg) "(%Hti & Hi & %Htid)".
          iDestruct (ghost_map_lookup with "Hm Hi") as %HLi.
          iPureIntro. simpl in Hti. rewrite Hti. rewrite HLM in HLi.
          pose proof (own_pub_lookup _ _ _ _ HLi Htid). lia. }
    iSplitL "Hts Hm Hlen Hv".
    { iExists TM, LM. iFrame. iPureIntro. split_and!; done. }
    iSplitL "Hb Hd".
    { iExists B, K, W, D. iFrame "Hb Hd HK HW Hoks". by iPureIntro. }
    iExists t. iFrame "Hpt Htse Hbit". by iPureIntro.
  Qed.

  (* a stamped byte loads like any context byte: forget the stamp *)
  Lemma ctx_phys_xload_ok `{CID : CpuId} (g : gstate) (ξ : CtxId) (IK : nat)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    own_context ξ -∗
    ctx_phys_xpointsto ξ IK a dq v -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝.
  Proof.
    iIntros "Hgh Hint Hrun Hx". iDestruct (ctx_phys_xpointsto_forget with "Hx") as "Hf".
    iApply (ctx_phys_load_ok with "Hgh Hint Hrun Hf").
  Qed.

  (* THE FETCH GATE, one byte: the icache agent sees no store forwarding,
     so the read at a view [tv'] is the latest write only if that write is
     under [tv'] -- which the stamp and the receipt [IK <= itv] give. *)
  Lemma ctx_phys_xfetch_ok `{CID : CpuId} (g : gstate) (ξ : CtxId)
      (IK itv : nat) (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    (IK <= itv)%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    ctx_phys_xpointsto ξ IK a dq v -∗
    ⌜forall tv' : nat, (itv <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (ifetch_agent (hart_agent cpu_id)) tv' a
       = Some v⌝.
  Proof.
    intros HIK.
    rewrite ctx_phys_xpointsto_unseal /ctx_phys_xpointsto_def.
    iIntros "Hgh Hint Hfact".
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    iDestruct "Hfact" as "(%t & Hpt & Htse & Hbit & %HtIK)".
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iPureIntro. intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|].
    apply visibleb_below. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE PIN'S THREE GATES (tso-pin-memo.md §5).                        *)
  (* ---------------------------------------------------------------- *)

  (* (1) THE MINT, at the pin's PUBLICATION point.  One-way, done once,  *)
  (* and it CREATES NO ELEMENT -- it updates one at full fraction, so    *)
  (* A6.9's "the ledger has no mint" rule stands.  The obligation is     *)
  (* exactly A6.47's refuted [t ≤ B] tie: false as a standing invariant, *)
  (* TRUE here, which is the whole re-framing.                           *)
  Lemma ledger_pin_mint (g : gstate) (a : Arch.pa) (v : bv 8)
      (t B : nat) (Sv : gset (bv 8)) :
    (t <= B)%nat -> v ∈ Sv ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_at a (DfracOwn 1) v t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗
    phys_ledger_pin a (DfracOwn 1) v t B Sv.
  Proof.
    iIntros (HtB Hv) "Hgh Hint [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iMod (ghost_map_update ((t, ts_pay_pin Sv B) : ts_elem) with "Hauth Hts")
      as "[Hauth Hts]".
    iModIntro. iFrame "Hgh Hpt Hts".
    iExists (<[a := ((t, ts_pay_pin Sv B) : ts_elem)]> TM), LM.
    iFrame "Hauth Hm Hlen Hvw".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom.
      assert (Ha : a ∈ dom g.(gmem)) by (by eapply elem_of_dom_2).
      set_solver. }
    iSplitR; last (iPureIntro; split; [exact HLM | exact (conj Hmm Hera)]).
    iPureIntro. intros a' e Hlk.
    destruct (decide (a' = a)) as [->|Hne].
    - rewrite lookup_insert in Hlk. injection Hlk as <-.
      split_and!; [ | | by move => W0 HW0 | by move => R0 HR0 | by move => Wp HWp ].
      + exists v. split; [exact Hgm | exact Hlat].
      + intros Sv' B' Heq. cbn in Heq. injection Heq as <- <-.
        exact (pin_ok_mint _ _ _ _ _ t v Hlat HtB Hv).
    - rewrite lookup_insert_ne in Hlk; last done. exact (Htie _ _ Hlk).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* THE RACY PAYLOAD'S MINT (A6.79, RE-CUT AT THE FLOOR -- A6.82 §(4)). *)
  (*                                                                   *)
  (* A6.79's mint needed an UNWRITTEN cell ([e.1 = 0]): the interp's    *)
  (* tie at a timestamp-0 element says "no message in the log writes    *)
  (* this byte at all", which discharged the whole-log conjuncts        *)
  (* vacuously.  A6.81 refuted its SITE -- [initlock] is also called on *)
  (* a [kalloc]'d page, whose bytes [kfree]'s memset has already        *)
  (* written -- and the floor is the repair.                           *)
  (*                                                                   *)
  (* WHAT THE FLOORED MINT NEEDS IS THE SAME FACT AT THE CELL'S OWN     *)
  (* TIMESTAMP RATHER THAN AT ZERO: [latest img log a t v] says [t]     *)
  (* wrote the byte and NOTHING ABOVE [t] did, so at floor [t] the      *)
  (* relativised conjunct (1) is about the message at [t] alone -- and  *)
  (* that message wrote the WHOLE window, because every byte's own      *)
  (* element names the SAME [t].  Conjunct (2b) is that message read as *)
  (* the floor.  The pure content is [TsoMemPa.win_ok1_of_latest]; the  *)
  (* old [e.1 = 0] mint is its instance at [t = 0].                     *)
  (*                                                                   *)
  (* AND THAT IS WHY THE ORDER INVERTS TO STORE-THEN-MINT.  The [n]     *)
  (* cells share a timestamp exactly when one store wrote them all, so  *)
  (* the mint runs on the cells the clear-word store has just moved to  *)
  (* the top, INSIDE the same store leaf's [==∗] (A6.81 §(3): the       *)
  (* datum-parametric store AU lends the interp out at [==∗]).  Minting *)
  (* first would name a floor message that does not exist yet.          *)
  (*                                                                   *)
  (* [tw_z] IS THE CELLS' CURRENT VALUES, not a parameter -- the tie    *)
  (* determines them.  [tw_cp] IS free (conjunct (1)'s only message is  *)
  (* the floor's, which wrote [z]), and both are then fixed for the     *)
  (* payload's life: [win_ok1_app_store] re-establishes the claim only  *)
  (* at the same [z], [cp] and [lo]; only [own] ever moves.             *)
  (* ---------------------------------------------------------------- *)

  (* the interp's tie, projected: what the ledger element SAYS about the
     log.  Consuming, and used only inside an [iAssert (⌜_⌝)] block. *)
  Lemma ledger_latest_ok (g : gstate) (a : Arch.pa) (dq : dfrac) (v : bv 8)
      (t : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_at a dq v t -∗
    ⌜latest g.(gimg) g.(glog) a t v⌝.
  Proof.
    iIntros "Hgh Hint [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTM)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-. by iPureIntro.
  Qed.

  (* ================================================================== *)
  (* THE M4 LOCK KIT'S LEDGER-TIER GATES (tso-m4-memo.md; A6.84).        *)
  (*                                                                    *)
  (* The lock's two cells cannot live in the ctx tower: the WORD is      *)
  (* written by whichever hart wins the AMO, and the OWNER cell carries  *)
  (* a claim about the log that only a ledger element can hold.  Both    *)
  (* therefore sit at the LEDGER tier, which is ξ-FREE -- and that is    *)
  (* what keeps [is_lock] a closed term (tso-port.md §0.19′) with no ∃ξ  *)
  (* at all, rather than an existential nothing can eliminate.           *)
  (*                                                                    *)
  (* What a ledger cell does NOT carry is the address's MAPPING, so the  *)
  (* lock's invariant carries the two [wordw_claim]s persistently        *)
  (* instead.  That is the trade the tier change makes, and it is a good *)
  (* one: the claim is about the ADDRESS, not the value, so it is        *)
  (* persistent and one peek serves every leaf.                          *)
  (* ================================================================== *)

  (* AT KT0 A CTX BYTE IS A LEDGER BYTE, and the bridge is the tier pin
     the cell already carries: [ktier_pin KT0 ppn a] IS [pa_of ppn a = a]
     ([ktier_pin_id]), so no external claim is needed.  ONE-WAY, as
     always: the ctx residue (the clean/dirty bit) is dropped, and a cell
     that has left the tower does not come back. *)
  Lemma ctx_pointsto_ledger_kt0 (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (v : bv 8) :
    ctx_pointsto (KTR := KT0) ξ a dq v ⊢ phys_ledger a dq v.
  Proof.
    rewrite (ctx_pointsto_phys (KTR := KT0) ξ a dq v).
    iIntros "(%ppn & _ & _ & %Hpin & Hb)".
    rewrite (ktier_pin_id ppn a Hpin).
    by iApply ctx_phys_pointsto_ledger.
  Qed.

  (* ---- THE FOUR-BYTE LEDGER WORD: the lock word's carrier ---- *)
  Definition phys_ledger_word4 (a : Arch.pa) (dq : dfrac) (w : bv 32) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
     [∗ list] j ∈ seq 0 4, phys_ledger (pa_add a j) dq (nth_byte w j))%I.

  Lemma phys_ledger_word4_unfold a dq w :
    phys_ledger_word4 a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
    ([∗ list] j ∈ seq 0 4, phys_ledger (pa_add a j) dq (nth_byte w j)).
  Proof. reflexivity. Qed.

  (* ================================================================== *)
  (* A6.88: THE WORD'S HELD ARM -- the same asymmetry A6.78 §(2) named for  *)
  (* the owner CELL, one field over.  [holding()] reads BOTH lock fields,   *)
  (* and the holder's read of the word it wrote itself must be EXACT for    *)
  (* the same reason the owner cell's is: the invariant knows the CURRENT   *)
  (* value, and under TSO a load may return an older one unless the reader  *)
  (* can point at its OWN write.  [ledger_vis]'s author arm is that point.  *)
  (*                                                                      *)
  (* Nothing new is needed underneath: the store gate already hands the     *)
  (* append's own message fragment back ([ledger_store_win_at_ok]) and      *)
  (* [ledger_read_bytes_vis_ok] already consumes exactly this shape.  This  *)
  (* is the word-width wrapper for the pair.                                *)
  (* ================================================================== *)
  Definition phys_ledger_word4_vis (h : agent) (B : nat) (a : Arch.pa)
      (dq : dfrac) (w : bv 32) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
     [∗ list] j ∈ seq 0 4, ∃ t : nat,
       ledger_vis h B t ∗ phys_ledger_at (pa_add a j) dq (nth_byte w j) t)%I.

  Global Instance phys_ledger_word4_vis_timeless h B a dq w :
    Timeless (phys_ledger_word4_vis h B a dq w).
  Proof. rewrite /phys_ledger_word4_vis. apply _. Qed.

  (* the held form forgets its receipt and becomes the ordinary word, at
     the cost of the exactness the holder had -- [lk_cpu_cell_ex_forget]'s
     twin, and what release spends on the way out *)
  Lemma phys_ledger_word4_vis_forget h B a dq w :
    phys_ledger_word4_vis h B a dq w ⊢ phys_ledger_word4 a dq w.
  Proof.
    rewrite /phys_ledger_word4_vis /phys_ledger_word4.
    iIntros "[$ Hb]". iApply (big_sepL_impl with "Hb").
    iIntros "!>" (k j _) "(%t & _ & Hbj)".
    by iApply phys_ledger_at_ledger.
  Qed.

  Lemma phys_ledger_word4_vis_aligned_p h B a dq w :
    phys_ledger_word4_vis h B a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 4 = true⌝.
  Proof. iIntros "[$ _]". Qed.


  Lemma phys_ledger_word4_aligned_p a dq w :
    phys_ledger_word4 a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 4 = true⌝.
  Proof. iIntros "[$ _]". Qed.


  Global Instance phys_ledger_word4_timeless a dq w :
    Timeless (phys_ledger_word4 a dq w).
  Proof. rewrite /phys_ledger_word4. apply _. Qed.

  (* the creator's crossing: a KT0 ctx word IS the ledger word *)
  Lemma ctx_word4_ledger_kt0 (ξ : CtxId) (a : Arch.pa) (dq : dfrac) (w : bv 32) :
    ctx_word4_pointsto (KTR := KT0) ξ a dq w ⊢ phys_ledger_word4 a dq w.
  Proof.
    rewrite ctx_word4_pointsto_unfold /phys_ledger_word4.
    iIntros "[$ Hb]".
    iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "H".
    by iApply ctx_pointsto_ledger_kt0.
  Qed.


  (* (2) THE READ, and it is a PROJECTION: the pin's tie IS the           *)
  (* conclusion, so all this does is turn the reader's receipt into       *)
  (* [B ≤ tv'].  Agent-generic on purpose -- the confinement holds of     *)
  (* every agent, which is what makes it usable inside [fobl_ram]'s       *)
  (* ∀-quantified view.                                                   *)
  Lemma ledger_read_pin_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t B : nat) (Sv : gset (bv 8)) :
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    phys_ledger_pin a dq v t B Sv -∗
    ⌜forall (h : agent) (tv' : nat), (g.(gtv) cpu_id <= tv')%nat ->
       exists b, tso_read g.(gimg) g.(glog) h tv' a = Some b /\ b ∈ Sv⌝.
  Proof.
    iIntros "Hint #HB [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    pose proof (ts_ok_pin _ _ _ _ _ _ _ (Htie _ _ HTM) eq_refl) as Hpin.
    iDestruct (view_auth_valid with "Hvw HB") as %HBtvs.
    rewrite avf_hart in HBtvs.
    iPureIntro. intros h tv' Htv'. apply Hpin. lia.
  Qed.

  (* the window form of the general gate *)
  (* ---------------------------------------------------------------- *)
  (* (4) THE RACY GATE (tso-m4-memo.md §3; the kit is TsoMemPa §12/§12c). *)
  (*                                                                    *)
  (* ================================================================= *)
  (* §0.41′ / A6.126: THE RELEASE ARM'S CELLS.  A [phys_ledger_rpay]      *)
  (* cell carries [TsoMemPa.ts_pay_rel R]: since the floor, every message *)
  (* touching it is a recorded history position writing the whole        *)
  (* window.  The mint (at n cells sharing a stamp), the drop, the        *)
  (* AUTHOR's store (drop, store through the generic gate, re-mint with   *)
  (* the history extended by the store's own position -- so no map-level *)
  (* gate clone is needed) and the read gate ([TsoMemPa.rel_read] against *)
  (* the reader's floor receipt).                                         *)
  (* ================================================================= *)
  Definition phys_ledger_rpay (a : Arch.pa) (dq : dfrac) (v : bv 8) (t : nat)
      (R : ts_rel) : iProp Σ :=
    (phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, ts_pay_rel R))%I.

  Global Instance phys_ledger_rpay_timeless a dq v t R :
    Timeless (phys_ledger_rpay a dq v t R).
  Proof. rewrite /phys_ledger_rpay. apply _. Qed.

  Lemma phys_ledger_rpay_forget a dq v t R :
    phys_ledger_rpay a dq v t R ⊢ phys_pointsto a dq v.
  Proof. by iIntros "[$ _]". Qed.

  (* the window's OTHER form, before the mint: plain stamped cells.  Both
     forms answer a reader the same way (below), which is what lets a lease
     hold either and mint lazily at its first author's store. *)
  Definition rel_pre_cells (base : Arch.pa) (n : nat) (tf : nat -> nat)
      (f : nat -> bv 8) : iProp Σ :=
    ([∗ list] j ∈ seq 0 n,
       phys_ledger_at (pa_add base j) (DfracOwn 1) (f j) (tf j))%I.

  Definition rel_cells (base : Arch.pa) (n : nat) (dq : dfrac) (auth : agent)
      (lo : nat) (tf : nat -> nat) (fv f : nat -> bv 8)
      (hist : list (nat * (nat -> bv 8))) : iProp Σ :=
    ([∗ list] j ∈ seq 0 n, ∃ t : nat,
       phys_ledger_rpay (pa_add base j) dq (f j) t
         (TsRel base n j auth lo tf fv hist))%I.

  Global Instance rel_pre_cells_timeless base n tf f :
    Timeless (rel_pre_cells base n tf f).
  Proof. rewrite /rel_pre_cells. apply _. Qed.
  Global Instance rel_cells_timeless base n dq auth lo tf fv f hist :
    Timeless (rel_cells base n dq auth lo tf fv f hist).
  Proof. rewrite /rel_cells. apply _. Qed.

  (* the visibility premise both readers take: each byte's floor write *)
  Definition rel_floor_vis (h : agent) (K : nat) (n : nat) (tf : nat -> nat)
      : iProp Σ :=
    ([∗ list] k ∈ seq 0 n, ledger_vis h K (tf k))%I.
  Global Instance rel_floor_vis_persistent h K n tf :
    Persistent (rel_floor_vis h K n tf).
  Proof. rewrite /rel_floor_vis. apply _. Qed.


  Lemma rel_floor_vis_visibleb `{CID : CpuId} (g : gstate) (K n : nat)
      (tf : nat -> nat) :
    tso_interp_at riscv_eraGS g -∗
    rel_floor_vis (hart_agent cpu_id) K n tf -∗
    ⌜forall tv : nat, (K <= tv)%nat -> forall k, (k < n)%nat ->
       visibleb (hart_agent cpu_id) tv g.(glog) (tf k) = true⌝.
  Proof.
    iIntros "Hint #Hv". rewrite /rel_floor_vis.
    iAssert (⌜forall k, (k < n)%nat -> forall tv : nat, (K <= tv)%nat ->
               visibleb (hart_agent cpu_id) tv g.(glog) (tf k) = true⌝)%I as %H.
    { rewrite bi.pure_forall. iIntros (k). rewrite bi.pure_impl. iIntros (Hk).
      iDestruct (big_sepL_lookup _ (seq 0 n) k k with "Hv") as "Hvk".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_vis_visibleb with "Hint Hvk"). }
    iPureIntro. intros tv Htv k Hk. exact (H k Hk tv Htv).
  Qed.

  (* a hist entry's message is the author's; a reader that is NOT the author
     sees it only from a view at or past its position *)
  Lemma visibleb_le_other (h h' : agent) (tv : nat) (log : list pwmsg)
      (i : nat) (mg : pwmsg) :
    log !! i = Some mg -> pm_tid mg = h' -> h <> h' ->
    visibleb h tv log (S i) = true -> (S i <= tv)%nat.
  Proof.
    intros Hlk Htid Hne Hv. rewrite /visibleb Hlk in Hv.
    apply orb_true_iff in Hv. destruct Hv as [Hv | Hv].
    - apply bool_decide_eq_true in Hv. exact Hv.
    - apply bool_decide_eq_true in Hv. exfalso. apply Hne. by rewrite -Hv.
  Qed.

  (* THE READ GATE for the minted window: [TsoMemPa.rel_read] against the
     interp.  The reader's word is the floor's bytes (no history entry
     visible) or the LATEST visible history entry's; a non-author reader
     then has that entry's position in its view. *)
  Lemma ledger_read_rel_ok `{CID : CpuId} (g : gstate)
      (base : Arch.pa) (n : nat) (dq : dfrac) (auth : agent)
      (lo : nat) (tf : nat -> nat) (fv f : nat -> bv 8)
      (hist : list (nat * (nat -> bv 8))) (K : nat) :
    (0 < n)%nat ->
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) K -∗
    rel_floor_vis (hart_agent cpu_id) K n tf -∗
    rel_cells base n dq auth lo tf fv f hist -∗
    ⌜forall tv : nat, (g.(gtv) cpu_id <= tv)%nat ->
       ((forall j, (j < n)%nat ->
           tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add base j)
           = Some (fv j))
        /\ (forall q g0, (q, g0) ∈ hist ->
              visibleb (hart_agent cpu_id) tv g.(glog) q = false))
       \/ (exists T g0, (T, g0) ∈ hist
             /\ visibleb (hart_agent cpu_id) tv g.(glog) T = true
             /\ (hart_agent cpu_id <> auth -> (T <= tv)%nat)
             /\ (forall j, (j < n)%nat ->
                   tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add base j)
                   = Some (g0 j))
             /\ (forall q g1, (q, g1) ∈ hist ->
                   visibleb (hart_agent cpu_id) tv g.(glog) q = true -> (q <= T)%nat))⌝.
  Proof.
    iIntros (Hn) "Hint #HK #Hfv Hb". rewrite /rel_cells.
    iDestruct (rel_floor_vis_visibleb g K n tf with "Hint Hfv") as %Hvis.
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (view_auth_valid with "Hvw HK") as %HKtvs.
    rewrite avf_hart in HKtvs.
    iAssert (⌜forall j : nat, (j < n)%nat ->
               rel_ok1 g.(gimg) g.(glog) (pa_add base j)
                 (TsRel base n j auth lo tf fv hist)⌝)%I
      as %Hcov.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hb") as (tj) "[_ Hej]".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iDestruct (ghost_map_lookup with "Hauth Hej") as %HTMj.
      iPureIntro.
      exact (ts_ok_rel _ _ _ _ _ _ (Htie _ _ HTMj) eq_refl). }
    iPureIntro. intros tv Htv.
    have Hvf : forall k, (k < n)%nat ->
        visibleb (hart_agent cpu_id) tv g.(glog) (tf k) = true
      := Hvis tv ltac:(lia).
    case: (rel_read g.(gimg) g.(glog) base n auth lo tf fv hist Hn Hcov
             (hart_agent cpu_id) tv Hvf)
      => [[Hrd Hinv] | [T [g0 [Hin [HvT [Hrd Hmax]]]]]].
    - left. split; [exact Hrd | exact Hinv].
    - right. exists T, g0. split_and!; [exact Hin | exact HvT | | exact Hrd | exact Hmax].
      intros Hne.
      have [_ [_ [_ [_ [H1b _]]]]] := Hcov 0%nat Hn.
      cbn [tr_base tr_n tr_j tr_auth tr_lo tr_fl tr_fv tr_hist] in H1b.
      have [_ [i [mg [HT [Hlk [Htid _]]]]]] := H1b T g0 Hin.
      rewrite HT in HvT. rewrite HT.
      exact (visibleb_le_other _ _ _ _ _ _ Hlk Htid Hne HvT).
  Qed.

  (* ================================================================= *)
  (* §12f / A6.143: THE WORD-SET PIN'S LEDGER CELLS.  The rpay block's   *)
  (* mirror one arm over: extraction of the pure claim, the mint AT A    *)
  (* PURE [pinw_ok1] PREMISE (the arm store and the author's member      *)
  (* store both route through it -- [TsoMemPa.pinw_ok1_mint] after the   *)
  (* arm append, [TsoMemPa.pinw_ok1_app_member] across a member append   *)
  (* -- so no map-level store-gate clone is needed here either), the     *)
  (* drop, and the read gate ([TsoMemPa.pinw_read] against the reader's  *)
  (* view receipt at the window's floor).                                *)
  (* ================================================================= *)
  Definition phys_ledger_pinw (a : Arch.pa) (dq : dfrac) (v : bv 8)
      (t : nat) (W : ts_pinw) : iProp Σ :=
    (phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, ts_pay_pinw W))%I.

  Global Instance phys_ledger_pinw_timeless a dq v t W :
    Timeless (phys_ledger_pinw a dq v t W).
  Proof. rewrite /phys_ledger_pinw. apply _. Qed.

  Lemma ledger_pinw_ok (g : gstate) (a : Arch.pa) (dq : dfrac) (v : bv 8)
      (t : nat) (W : ts_pinw) :
    tso_interp_at riscv_eraGS g -∗
    phys_ledger_pinw a dq v t W -∗
    ⌜pinw_ok1 g.(gimg) g.(glog) a W⌝.
  Proof.
    iIntros "Hint [Hpt Hts]".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (ghost_map_lookup with "Hauth Hts") as %HTM.
    iPureIntro. exact (ts_ok_pinw _ _ _ _ _ _ (Htie _ _ HTM) eq_refl).
  Qed.


  (* A6.146: the same gate, at the TWO-ARMED licence ([ledger_vis]) -- the
     window is readable below the receipt OR the reader authored the arm
     store itself ([visibleb]'s own-message arm: store forwarding).  This
     is what serves iget's FRESH slot: its ilock-time racy read runs before
     any drain of the arm store, on the author's own receipt. *)
  Lemma ledger_read_pinw_vis `{CID : CpuId} (g : gstate) (base : Arch.pa)
      (nn lo K : nat) (Sw : (nat -> bv 8) -> Prop) (dq : dfrac)
      (f : nat -> bv 8) :
    (0 < nn)%nat ->
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) K -∗
    ledger_vis (hart_agent cpu_id) K lo -∗
    ([∗ list] j ∈ seq 0 nn, ∃ t : nat,
       phys_ledger_pinw (pa_add base j) dq (f j) t (TsPinw base nn j lo Sw)) -∗
    ⌜forall tv : nat, (g.(gtv) cpu_id <= tv)%nat ->
       exists fw : nat -> bv 8,
         Sw fw /\
         forall j, (j < nn)%nat ->
           tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add base j)
           = Some (fw j)⌝.
  Proof.
    iIntros (Hn) "Hint #HK #Hvis Hb".
    iAssert (⌜forall j, (j < nn)%nat ->
               pinw_ok1 g.(gimg) g.(glog) (pa_add base j)
                 (TsPinw base nn j lo Sw)⌝)%I as %Hok.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 nn) j j with "Hb") as (t) "Hbj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_pinw_ok g (pa_add base j) dq (f j) t _ with "Hint Hbj"). }
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    iDestruct (view_auth_valid with "Hvw HK") as %HKtv.
    rewrite avf_hart in HKtv.
    iDestruct "Hvis" as "[%HloK | (%i & %m & %Hloi & #Hmsg & %Htid)]".
    - iPureIntro. intros tv Htv.
      apply (TsoMemPa.pinw_read g.(gimg) g.(glog) base nn lo Sw
               (hart_agent cpu_id) tv Hn Hok).
      apply TsoMemPa.visibleb_below. lia.
    - iDestruct (ghost_map_lookup with "Hm Hmsg") as %HLi.
      iPureIntro. intros tv Htv.
      apply (TsoMemPa.pinw_read g.(gimg) g.(glog) base nn lo Sw
               (hart_agent cpu_id) tv Hn Hok).
      subst lo.
      apply (TsoMemPa.visibleb_own (hart_agent cpu_id) tv g.(glog) i m);
        [| exact Htid].
      rewrite -HLM. exact HLi.
  Qed.

  (* the hand-back: a stamped cell whose stamp the context's floor covers is
     a CLEAN ctx cell (A6.126 §6: the reclaimed slot's bytes return to the
     publisher through the lock payload's floor) *)
  Lemma ctx_phys_pointsto_of_at_floor (ξ : CtxId) (a : Arch.pa) (v : bv 8)
      (t : nat) :
    phys_ledger_at a (DfracOwn 1) v t -∗ ctx_floor ξ t -∗
    ctx_phys_pointsto ξ a (DfracOwn 1) v.
  Proof.
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def /phys_ledger_at /ctx_floor.
    iIntros "[Hpt Hts] #Hfl". iExists t. iFrame "Hpt Hts". by iLeft.
  Qed.

  (* The one read in the tree with NO receipt and NO synchronisation:    *)
  (* [holding()]'s [ld a5,16(a0)] of [lk->cpu] by a hart that does not    *)
  (* hold the lock.  It cannot conclude a VALUE -- the pin's shape --     *)
  (* only an EXCLUSION, and the exclusion is a property of the READER'S   *)
  (* OWN WRITE HISTORY, not of the value.                                *)
  (*                                                                    *)
  (* WHAT IS IN THE PREMISES NOW, AND WHY (A6.82).  The unrelativised    *)
  (* gate was VIEW-FREE -- [own h = Some t] with [t] visible at every     *)
  (* view was enough, so no receipt could make it better.  With a FLOOR   *)
  (* the payload's history claims start at [tw_lo], and the reader must   *)
  (* show its view has PASSED the floor: the gate takes                   *)
  (* [view_lb … K] and [⌜lo ≤ K⌝] and concludes at every [tv' ≥ gtv].     *)
  (* That is [ledger_read_pin_ok]'s shape exactly -- the receipt/stamp    *)
  (* pair -- which is the design rhyme (every history-shaped claim in     *)
  (* this port carries a floor and is claimed against a monotone          *)
  (* receipt) arriving at the Iris tier as well as the pure one.          *)
  (* ---------------------------------------------------------------- *)

  Lemma ledger_read_racy_ok `{CID : CpuId} (g : gstate)
      (base : Arch.pa) (n : nat) (dq : dfrac) (f : nat -> bv 8)
      (z : nat -> bv 8) (cp : agent -> nat -> bv 8)
      (own : agent -> option nat) (lo t K : nat) :
    (0 < n)%nat ->
    (* MY own-last record AT OR ABOVE THE FLOOR: where my last write to
       this window is.  The MINTER's own entry is the floor itself. *)
    own (hart_agent cpu_id) = Some t ->
    (* >>> A6.111 (§0.36′(a)'s author arm at the lock tier, composed with
       §0.38′'s received-or-wrote reading; owner informed, veto standing).
       THE RECEIPT DOMINATING THE FLOOR IS NOW ONE OF TWO ARMS.  A hart that
       RECEIVED the handle passes the floor by its view ([lo ≤ K], the old
       premise); the hart that WROTE the floor -- the lock's creator, whose
       [initlock] store IS the mint store, so its own anchor and the floor
       coincide -- passes it by AUTHORSHIP, at every view and with no
       receipt.  The pure half below is the ANCHOR's reachability and the
       resource half is the FLOOR's visibility; [ledger_vis] is exactly the
       two-armed predicate and needed no inventing (A6.110 §4).

       FORBIDDEN REASONING, recorded in place: "the creator will have taken
       some other lock in between, and any AMO upgrades every right-arm
       handle at once" is TRUE ([hart_view_lb_get] does it, and `sys_pipe`'s
       [filealloc] does in fact intervene) but must never be the story -- it
       makes [initlock]'s contract depend on what its caller does next. <<< *)
    (* the clear word is not mine ... *)
    (exists k, (k < n)%nat /\ z k <> cp (hart_agent cpu_id) k) ->
    (* ... and no other agent's word is mine.  BOTH premises are
       WORD-level and ask only for a distinguishing offset PER OTHER
       AGENT -- which is exactly what the [cpus_ptr] layout provides and a
       byte-keyed kit would not (tso-m4-memo.md §3's computation). *)
    (forall h', h' <> hart_agent cpu_id ->
       exists k, (k < n)%nat /\ cp h' k <> cp (hart_agent cpu_id) k) ->
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) K -∗
    (* the FLOOR's visibility: [lo ≤ K] for a hart that received the handle,
       authorship for the one that wrote it *)
    ledger_vis (hart_agent cpu_id) K lo -∗
    (* the ANCHOR's, off the cell's own invariant (A6.114 §2) *)
    ledger_vis (hart_agent cpu_id) lo t -∗
    (* A6.119: the ∃-FORM window, which is what every producer in the tree
       hands out ([ledger_store_win_wpay_ok], [WpLock.lk_cpu_pay]).  The
       [ts]-function spelling was the outlier and nothing here needed it:
       the proof reads only the per-byte WINDOW claim off each element. *)
    ([∗ list] j ∈ seq 0 n, ∃ tj : nat,
       phys_ledger_wpay (pa_add base j) dq (f j) tj
         (TsWin base n j z cp own lo)) -∗
    ⌜forall tv : nat, (g.(gtv) cpu_id <= tv)%nat -> exists k, (k < n)%nat /\
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add base k)
       <> Some (cp (hart_agent cpu_id) k)⌝.
  Proof.
    iIntros (Hn Hown Hzk Hinj) "Hint #HK #Hfv #Hav Hb".
    iDestruct "Hint"
      as "(%TM & %LM & Hauth & %Hdom & %Htie & Hm & %HLM & Hlen & Hvw & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (view_auth_valid with "Hvw HK") as %HKtvs.
    rewrite avf_hart in HKtvs.
    (* every byte's element carries its own copy of the window claim *)
    iAssert (⌜forall j : nat, (j < n)%nat ->
               win_ok1 g.(gimg) g.(glog) (pa_add base j)
                 (win_at base n z cp own lo j)⌝)%I as %Hcov.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hb") as (tj) "[_ Hej]".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iDestruct (ghost_map_lookup with "Hauth Hej") as %HTMj.
      iPureIntro.
      exact (ts_ok_win _ _ _ _ _ _ (Htie _ _ HTMj) eq_refl). }
    iDestruct (ledger_vis_visibleb g K lo with "[$Hauth $Hm $Hlen $Hvw //] Hfv")
      as %Hfvis.
    iDestruct (ledger_vis_anchor g lo t with "[$Hauth $Hm $Hlen $Hvw //] Hav")
      as %Hanc.
    iPureIntro. intros tv Htv.
    exact (win_assemble_not_mine g.(gimg) g.(glog) base n z cp own lo Hn Hcov
             (hart_agent cpu_id) t tv Hown
             (Hfvis tv ltac:(lia)) Hanc Hzk Hinj).
  Qed.


  (* ...and the WORD form the leaf actually consumes: a byte that differs
     makes the assembled word differ.  [n = 8] at the lock, but stated at
     the general width so the [bv] step is done once. *)
  Lemma ledger_read_racy_word_ok `{CID : CpuId} (g : gstate)
      (base : Arch.pa) (n : nat) (dq : dfrac) (f : nat -> bv 8)
      (z : nat -> bv 8) (cp : agent -> nat -> bv 8)
      (own : agent -> option nat) (lo t K : nat) {m : N} (cpw : bv m) :
    (0 < n)%nat ->
    own (hart_agent cpu_id) = Some t ->
    (forall k, (k < n)%nat -> nth_byte cpw k = cp (hart_agent cpu_id) k) ->
    (exists k, (k < n)%nat /\ z k <> cp (hart_agent cpu_id) k) ->
    (forall h', h' <> hart_agent cpu_id ->
       exists k, (k < n)%nat /\ cp h' k <> cp (hart_agent cpu_id) k) ->
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) K -∗
    ledger_vis (hart_agent cpu_id) K lo -∗
    ledger_vis (hart_agent cpu_id) lo t -∗
    ([∗ list] j ∈ seq 0 n, ∃ tj : nat,
       phys_ledger_wpay (pa_add base j) dq (f j) tj
         (TsWin base n j z cp own lo)) -∗
    ⌜forall (tv : nat), (g.(gtv) cpu_id <= tv)%nat -> forall (w : bv m),
       tso_read_bytes g.(gimg) g.(glog) (hart_agent cpu_id) tv base
         (N.of_nat n) w -> w <> cpw⌝.
  Proof.
    iIntros (Hn Hown Hcpw Hzk Hinj) "Hint #HK #Hfv #Hav Hb".
    iDestruct (ledger_read_racy_ok g base n dq f z cp own lo t K
                 Hn Hown Hzk Hinj with "Hint HK Hfv Hav Hb") as %Hex.
    iPureIntro. intros tv Htv w Hrd ->.
    destruct (Hex tv Htv) as (k & Hk & Hne). apply Hne.
    rewrite (Hrd k ltac:(lia)). by rewrite (Hcpw k Hk).
  Qed.

  (* A6.123: THE EXACT READ ON THE TWO-ARMED FLOOR.  [ledger_read_at_ok]
     wants the reader's view past the cell's stamp; a lock-payload cell
     whose floor arrived through [WpLock.lk_floor] discharges that on the
     LEFT arm and, for the hart that wrote it, on the RIGHT (store
     forwarding: [visibleb]'s own-author arm, via [ledger_vis_visibleb]).
     Same conclusion, the premise [WpLock.lk_floor_vis] hands out. *)
  Lemma ledger_read_at_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t F : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) F -∗
    ledger_vis (hart_agent cpu_id) F t -∗
    phys_ledger_at a dq v t -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝.
  Proof.
    iIntros "Hgh Hint #HF #Hvis [Hpt Htse]".
    iDestruct (ledger_vis_visibleb with "Hint Hvis") as %Hvisb.
    iDestruct "Hint"
      as "(%TM & %LM & Hts & %Hdom & %Htie & Hm & %HLM & Hlen & Hv & %Hmm)".
    destruct Hmm as (Hmm & Hera).
    iDestruct (phys_valid with "Hgh Hpt") as %Hgm.
    iDestruct (ghost_map_lookup with "Hts Htse") as %HTMt.
    destruct (ts_ok_latest _ _ _ _ _ (Htie _ _ HTMt)) as (v0 & Hgm0 & Hlat).
    rewrite Hgm in Hgm0. injection Hgm0 as <-.
    iDestruct (view_auth_valid with "Hv HF") as %HFtvs.
    rewrite avf_hart in HFtvs.
    iPureIntro. intros tv' Htv'.
    apply (tso_read_of_latest _ _ _ _ _ t); [exact Hlat|].
    apply Hvisb. lia.
  Qed.

  (* THE READ GATE for the pre-mint window: the same premises, the floor's
     answer -- each byte from its own stamped cell *)
  Lemma ledger_read_relpre_ok `{CID : CpuId} (g : gstate)
      (base : Arch.pa) (n : nat) (tf : nat -> nat) (f : nat -> bv 8) (K : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) K -∗
    rel_floor_vis (hart_agent cpu_id) K n tf -∗
    rel_pre_cells base n tf f -∗
    ⌜forall tv : nat, (g.(gtv) cpu_id <= tv)%nat ->
       forall j, (j < n)%nat ->
         tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add base j)
         = Some (f j)⌝.
  Proof.
    iIntros "Hgh Hint #HK #Hfv Hb". rewrite /rel_pre_cells /rel_floor_vis.
    iAssert (⌜forall j, (j < n)%nat -> forall tv : nat, (g.(gtv) cpu_id <= tv)%nat ->
               tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add base j)
               = Some (f j)⌝)%I as %H.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hb") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hfv") as "Hvj".
      { rewrite lookup_seq_lt; [reflexivity|lia]. }
      iApply (ledger_read_at_vis_ok g (pa_add base j) (DfracOwn 1) (f j) (tf j) K
                with "Hgh Hint HK Hvj Hbj"). }
    iPureIntro. intros tv Htv j Hj. exact (H j Hj tv Htv).
  Qed.


  (* ---------------------------------------------------------------- *)
  (* THE 8-BYTE PHYSICAL LEDGER WORD -- [phys_word_pointsto]'s twin, and *)
  (* the resource THREE of A6.14's four members actually hold ([↦ₚ₈]):   *)
  (* [WpMmodeStore]'s target cell, [KptTree]'s PT slot, and the DMA      *)
  (* lease's descriptor doubleword.  Character for character            *)
  (* [ctx_word_pointsto] at the physical tier, so the towers' law names  *)
  (* line up.                                                           *)
  (* ---------------------------------------------------------------- *)
  Definition ctx_phys_word_pointsto (ξ : CtxId) (a : Arch.pa) (dq : dfrac)
      (w : bv 64) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
     [∗ list] j ∈ seq 0 8, ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j))%I.

  Lemma ctx_phys_word_pointsto_unfold ξ a dq w :
    ctx_phys_word_pointsto ξ a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
    ([∗ list] j ∈ seq 0 8, ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j)).
  Proof. reflexivity. Qed.

  Lemma ctx_phys_word_pointsto_aligned_p ξ a dq w :
    ctx_phys_word_pointsto ξ a dq w ⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
  Proof. iIntros "[$ _]". Qed.

  Lemma ctx_phys_word_pointsto_bytes ξ a dq w :
    ctx_phys_word_pointsto ξ a dq w ⊢
    [∗ list] j ∈ seq 0 8, ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j).
  Proof. iIntros "[_ $]". Qed.

  Lemma ctx_phys_word_pointsto_intro ξ a dq w :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, ctx_phys_pointsto ξ (pa_add a j) dq (nth_byte w j))
    ⊢ ctx_phys_word_pointsto ξ a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.

  Global Instance ctx_phys_word_pointsto_timeless ξ a dq w :
    Timeless (ctx_phys_word_pointsto ξ a dq w).
  Proof. rewrite /ctx_phys_word_pointsto. apply _. Qed.
  Global Instance ctx_phys_word_pointsto_discarded_persistent ξ a w :
    Persistent (ctx_phys_word_pointsto ξ a DfracDiscarded w).
  Proof. rewrite /ctx_phys_word_pointsto. apply _. Qed.

  Lemma ctx_phys_word_pointsto_forget ξ a dq w :
    ctx_phys_word_pointsto ξ a dq w ⊢ phys_word_pointsto a dq w.
  Proof.
    iIntros "[%Hal Hb]". rewrite /phys_word_pointsto. iSplitR; first done.
    iApply (big_sepL_impl with "Hb"). iIntros "!>" (k j _) "H".
    by iApply ctx_phys_pointsto_forget.
  Qed.


  (* ---------------------------------------------------------------- *)
  (* THE IDENTITY-MAPPED CROSSING between the VA ledger family and the  *)
  (* PHYSICAL one, BOTH DIRECTIONS AND LOSSLESS (A6.16).                *)
  (*                                                                   *)
  (* This is what repairs A6.14's [KptTree] entry.  The PT-slot pair    *)
  (* [pt_slot_phys_to_mem] / [pt_slot_mem_to_phys] is an OUT-AND-BACK   *)
  (* with a STORE inside, and A6.9 says a byte that leaves the ledger   *)
  (* can never come back -- true, and the reason the residue trick      *)
  (* fails.  But the round trip never has to leave: at an IDENTITY      *)
  (* mapping the two families are the SAME resource under a persistent  *)
  (* [kmap_at], so the crossing is an isomorphism and the timestamp and *)
  (* the bit ride through it untouched.  The tier the walker takes a    *)
  (* slot down to is not the RAW tier, it is the physical LEDGER.       *)
  (* ---------------------------------------------------------------- *)
  Lemma ctx_pointsto_to_phys `{KTR : !CurKtier} (ξ : CtxId) (ppn : mword 44)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    pa_of ppn a = a ->
    kmap_at (svpn_of a) ppn KP_rw -∗ ctx_pointsto ξ a dq v -∗
    ctx_phys_pointsto ξ a dq v.
  Proof.
    intros Hid. rewrite ctx_pointsto_phys.
    iIntros "#Hk (%ppn' & #Hk' & _ & _ & Hb)".
    iDestruct (kmap_at_agree with "Hk Hk'") as %[<- _].
    by rewrite Hid.
  Qed.

  Lemma ctx_pointsto_of_phys `{KTR : !CurKtier} (ξ : CtxId) (ppn : mword 44)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) :
    pa_of ppn a = a ->
    (uint a < 274877906944)%Z ->
    ktier_pin cur_ktier ppn a ->
    kmap_at (svpn_of a) ppn KP_rw -∗ ctx_phys_pointsto ξ a dq v -∗
    ctx_pointsto ξ a dq v.
  Proof.
    intros Hid Hc Hp. rewrite ctx_pointsto_phys.
    iIntros "#Hk Hb". iExists ppn. iFrame "Hk".
    iSplit; first done. iSplit; first done. by rewrite Hid.
  Qed.

End ctx.

(* The notation family, mirroring [mem_pointsto]'s ([RiscvPtsto.v]) with
   [↦c] in place of [↦ₘ]: the context index is AMBIENT ([cur_ctx], like
   the tier), so converted spec text reads as before --
   [a ↦c[ktb] v], [a ↦c v], [a ↦c{dq} v], [a ↦c□ v].  A statement that
   needs an EXPLICIT context (lock internals, the kit) spells
   [ctx_pointsto] directly.  At the M1 notation flip these became the
   [↦ₘ] spellings and [↦c] is retired by attrition.  The tier-bracket form
   goes through Iris's custom [dfrac] entry for the same lexer reason as
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

   IT IS A COMBINATOR, NOT A λ.  Any [CurCtx]-typed binder -- even
   anonymous -- is a TC candidate inside [P], resolved site-dependently
   (the silent-drop hazard, measured live twice); with [const_pay], [P]
   is elaborated as the combinator's ARGUMENT -- outside any
   [CurCtx]-typed binder -- so its ambient facts always bind the
   caller's context, identically at every site.
   THE SPELLING IS [<{ P }>] AND NOT [<[ P ]>]: stdpp's insert notation
   shares the [<[] prefix and Coq reports the two as incompatible
   (measured on the branch; the brace form is free). *)
Definition const_pay {Σ : gFunctors} (P : iProp Σ) : CtxId → iProp Σ :=
  λ _, P.
Notation "<{ P }>" := (const_pay P%I)
  (at level 0, P at level 200, format "<{  P  }>").

(* the combinator's transport obligation: same guard role and priority
   story as [ctx_morph_const] (which still serves bare λ-spellings). *)
Global Instance ctx_morph_const_pay `{!riscvGS Σ} (P : iProp Σ) :
  CtxMorph (const_pay P) | 0.
(* PRIORITY 0, NOT 99 (main's M2 fix, re-applied on the cutover 2026-09-03):
   at 99, [apply _] on [CtxMorph <{ big payload }>] unfolds the payload and
   "succeeds" structurally through its big-ops with a proof term the next
   tactic never finishes with (claude-notes/optimization.md; the memory note
   "ctx_morph_const_pay priority").  The build-time audit of 2026-09-03 found
   the cutover had inherited flip's 99. *)
Proof. iIntros (ξ ξ') "Hd HP !>". iFrame. Qed.

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
   imports this one after [RiscvPtsto].  Files below this one -- the kit
   -- never import it and keep the raw meanings; that split IS the seam.
   The spellings are character-identical, which is the whole point:
   statement text above the seam does not change, its MEANING does.
   [↦c] is a synonym, retired by attrition.  Stage 2 flips
   [↦₄]/[↦₂]/[↦ₛ]/[↦ₚ]; [↦ₓ] (text) and [↦ᵣ] (registers) NEVER flip --
   text is timestamp-0 context-free by the port's ruling, and registers
   are per-hart machine state. *)
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

(* ================================================================== *)
(* M1 STAGE 2: the [↦₂] and [↦₄] families.  Same mechanism as stage 1 --
   the spellings are character-identical, the MEANING becomes the
   context-indexed tower, and import order decides (a file that imports
   this one after RiscvPtsto parses the flipped meaning; the kit below
   never imports it and keeps the raw one).  All four dfrac spellings of
   each family are re-declared, bracket form included, with the modifiers
   copied EXACTLY -- an omitted [dq custom dfrac at level 1] leaves the
   ε-dq spellings parsing raw, silently.

   [↦ₛ] flips too; its block is below. *)
Notation "a ↦₂{ dq } w" := (ctx_word2_pointsto cur_ctx a dq w)
  (at level 20, format "a  ↦₂{ dq }  w") : bi_scope.
Notation "a ↦₂ w" := (ctx_word2_pointsto cur_ctx a (DfracOwn 1) w)
  (at level 20, format "a  ↦₂  w") : bi_scope.
Notation "a ↦₂□ w" := (ctx_word2_pointsto cur_ctx a DfracDiscarded w)
  (at level 20, format "a  ↦₂□  w") : bi_scope.
Notation "a ↦₂[ kt ] dq w" := (ctx_word2_pointsto (KTR := kt) cur_ctx a dq w)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦₂[ kt ] dq  w") : bi_scope.

Notation "a ↦₄{ dq } w" := (ctx_word4_pointsto cur_ctx a dq w)
  (at level 20, format "a  ↦₄{ dq }  w") : bi_scope.
Notation "a ↦₄ w" := (ctx_word4_pointsto cur_ctx a (DfracOwn 1) w)
  (at level 20, format "a  ↦₄  w") : bi_scope.
Notation "a ↦₄□ w" := (ctx_word4_pointsto cur_ctx a DfracDiscarded w)
  (at level 20, format "a  ↦₄□  w") : bi_scope.
Notation "a ↦₄[ kt ] dq w" := (ctx_word4_pointsto (KTR := kt) cur_ctx a dq w)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦₄[ kt ] dq  w") : bi_scope.

(* ================================================================== *)
(* M1 STAGE 3: the [↦ₛ] family (tso-port.md §0.21′/§0.22′).  Same
   mechanism, all four dfrac spellings, bracket form included.

   THE ASSESSMENT THIS REPLACES (this workspace's A6.15, recorded here so
   nobody re-derives it) said [↦ₛ] must not move, for two reasons, and
   BOTH were wrong in the same way -- they read the tier off its rodata
   instances only:

   1. "It would put a context inside [is_lock]."  It would, if the handle
      carried the tier's ordinary fact.  It does not: [WpLock.lock_name] /
      [SleepLock.sl_name] carry [ctx_string_all] (above), the ∀-context
      DERIVED form, so [is_lock] / [is_sleeplock] stay closed terms and
      §0.8′ ruling 2 is intact.  The park rows do not move.
   2. "Every string fact in this tree is a discarded image literal, whose
      load obligation the pristine gate discharges."  FALSE: [p->name] is
      written by [safestrcpy] (proc.c:290, exec.c:132) and read by
      [printk("%s", p->name)].  Those bytes are as ordinary as any other
      RAM, and a tier that cannot speak about them is not the string tier.
      They only escaped notice because the proofs walked them through the
      ad-hoc [ProcDefs.pname_cells] byte big-op, never through [↦ₛ] -- and
      that big-op is itself context-indexed already.

   So the tier is context-relative at arbitrary timestamps and the
   pristine case is DERIVED, which is the general rule this port keeps
   re-learning: the definition covers the dynamic case, the static case is
   a lemma ([ctx_string_all_of_pristine] is that lemma, and it is where
   the boot carve's pristine receipts get spent at this tier).
   [ProcDefs.pname_cells] stays its OWN resource (a fixed-size array with
   an embedded string, carrying [ProcGeom.pname_wf]); the bridge to [↦ₛ]
   is the positional borrow/return pair in that file
   ([pname_cells_borrow] / [pname_cells_return]), not a conversion. *)
Notation "a ↦ₛ{ dq } s" := (ctx_string_pointsto cur_ctx a dq s)
  (at level 20, format "a  ↦ₛ{ dq }  s") : bi_scope.
Notation "a ↦ₛ□ s" := (ctx_string_pointsto cur_ctx a DfracDiscarded s)
  (at level 20, format "a  ↦ₛ□  s") : bi_scope.
Notation "a ↦ₛ s" := (ctx_string_pointsto cur_ctx a (DfracOwn 1) s)
  (at level 20, format "a  ↦ₛ  s") : bi_scope.
Notation "a ↦ₛ[ kt ] dq s" := (ctx_string_pointsto (KTR := kt) cur_ctx a dq s)
  (at level 20, kt at level 50, dq custom dfrac at level 1,
   format "a  ↦ₛ[ kt ] dq  s") : bi_scope.

(* The seal.  [ctx_dom] and [hart_view_lb] stay opaque too: nothing above
   this file may learn their bodies, and nothing may learn what
   [ctx_parked] does with its stamp. *)
Global Typeclasses Opaque own_context ctx_parked hart_view_lb
  ctx_pointsto ctx_dom ctx_phys_pointsto.
Global Opaque own_context ctx_parked hart_view_lb ctx_pointsto ctx_dom
  ctx_phys_pointsto.
(* [ctx_phys_pointsto] (A6.16) is sealed for exactly [ctx_pointsto]'s
   reason: the rehearsal's finding was that a PERMEABLE seal lets ctx↔raw
   cross silently by δ, and the physical family faces [phys_pointsto] the
   way the VA one faces [mem_pointsto].  [ctx_phys_word_pointsto] is NOT
   sealed -- a tower over the sealed byte, like [ctx_word_pointsto]. *)
(* [ctx_word_pointsto] -- and its siblings [ctx_word2_pointsto] /
   [ctx_word4_pointsto] / [ctx_string_pointsto] / [ctx_string_all] -- are
   NOT sealed at all: each is a tower OVER the sealed byte fact, so
   exposing its ⌜aligned⌝ ∗ big-op shape leaks nothing -- and the tree's
   proofs destruct/frame the word shape structurally. *)

(* ======================================================================= *)
(* MAIN-COMPAT APPENDIX (the tso-cutover branch).  Vocabulary main's SC     *)
(* port coined that the flip tree spells otherwise; each is a transparent   *)
(* alias or a body-independent structural instance, so nothing here opens   *)
(* the seal.  Consumers migrate to the flip spellings as their files take   *)
(* the cutover; delete each entry when its last consumer goes.              *)
(* ======================================================================= *)
Section main_compat.
  Context `{!riscvGS Σ}.

  (* main's [log_lb] is the flip's [llb] at the era's log-length name. *)
  Definition log_lb (lo : nat) : iProp Σ := TsoGhost.llb loglen_name lo.
  Global Instance log_lb_persistent lo : Persistent (log_lb lo).
  Proof. apply _. Qed.
  Global Instance log_lb_timeless lo : Timeless (log_lb lo).
  Proof. apply _. Qed.

  (* THE READ LICENCE AT ONE TIMESTAMP, main's above-seal spelling of the
     T-leg's [ledger_vis]: under the bound, or the context wrote it. *)
  Definition ctx_vis (ξ : CtxId) (K t : nat) : iProp Σ :=
    (⌜(t ≤ K)%nat⌝ ∨ ∃ a : Arch.pa, ctx_wrote ξ t a)%I.
  Global Instance ctx_vis_persistent ξ K t : Persistent (ctx_vis ξ K t).
  Proof. rewrite /ctx_vis. apply _. Qed.

  (* the structural [CtxMorph] combinators main added (body-independent) *)
  Global Instance ctx_morph_or (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, R1 ξ ∨ R2 ξ)%I.
  Proof.
    iIntros (H1 H2 ξ ξ') "Hd [HR|HR]".
    - iMod (ctx_morph with "Hd HR") as "[Hd HR]".
      iModIntro. iFrame "Hd". iLeft. iExact "HR".
    - iMod (ctx_morph with "Hd HR") as "[Hd HR]".
      iModIntro. iFrame "Hd". iRight. iExact "HR".
  Qed.

  Global Instance ctx_morph_big_sepS `{Countable A} (X : gset A)
      (Φ : A → CtxId → iProp Σ) :
    (∀ x, CtxMorph (Φ x)) → CtxMorph (λ ξ, [∗ set] x ∈ X, Φ x ξ)%I.
  Proof.
    intros HΦ. induction X as [|x X Hx IH] using set_ind_L.
    - iIntros (ξ ξ') "Hd _". rewrite big_sepS_empty. iModIntro. by iFrame.
    - iIntros (ξ ξ') "Hd HR".
      iDestruct (big_sepS_insert _ _ _ Hx with "HR") as "[HR HRs]".
      iMod (ctx_morph with "Hd HR") as "[Hd HR]".
      iMod (IH with "Hd HRs") as "[Hd HRs]".
      iModIntro. iFrame "Hd". rewrite big_sepS_insert; [| exact Hx]. iFrame.
  Qed.

  Global Instance ctx_morph_if_then (b : bool) (R : CtxId → iProp Σ) :
    CtxMorph R → CtxMorph (λ ξ, if b then R ξ else emp)%I.
  Proof.
    intros HR. destruct b; [| iIntros (ξ ξ') "Hd _"; iModIntro; by iFrame ].
    iIntros (ξ ξ') "Hd H". by iApply (ctx_morph with "Hd H").
  Qed.

  Global Instance ctx_morph_if_else (b : bool) (R : CtxId → iProp Σ) :
    CtxMorph R → CtxMorph (λ ξ, if b then emp else R ξ)%I.
  Proof.
    intros HR. destruct b; [ iIntros (ξ ξ') "Hd _"; iModIntro; by iFrame |].
    iIntros (ξ ξ') "Hd H". by iApply (ctx_morph with "Hd H").
  Qed.
  Global Instance ctx_morph_string (kt : ktier) a dq s :
    CtxMorph (λ ξ, ctx_string_pointsto (KTR := kt) ξ a dq s).
  Proof.
    iIntros (ξ ξ') "Hd H".
    iMod (ctx_morph_big_sepL (cstring_bytes s)
            (λ j b ξ0, ctx_pointsto (KTR := kt) ξ0 (pa_add a j) dq b)
            (λ i x, ctx_morph_pointsto _ _ _ _)
            ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame "Hd". iExact "H".
  Qed.
End main_compat.
