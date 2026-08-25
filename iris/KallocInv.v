(* KallocInv.v -- the LOGICAL specification layer for xv6's page allocator
   (kalloc/kfree), built on the CSL spin-lock of WpLock.v.

   Design (mirrors xv6's [kernel/kalloc.c]):
     struct run { struct run *next; };
     struct { struct spinlock lock; struct run *freelist; } kmem;

   The free list is a singly-linked chain THROUGH the free pages themselves:
   each free page's first 8 bytes hold the [next] pointer, and the whole 4KB is
   owned by the allocator.  The allocator's protected resource [kmem_res fl]
   owns the global head pointer (at address [fl] = &kmem.freelist) plus every
   page in the chain.  It becomes the resource [R] of a spin-lock over
   &kmem.lock, giving [is_kmem γ lk fl := is_lock γ lk "kmem" <{ kmem_res fl }>].

   THE PAGE-COUNT GHOST.  On top of the chain, the protected resource carries
   an authoritative count of the free pages, [kmem_avail_auth γk (length
   pages)], mirrored by a caller-side resource [kalloc_avail γk on] with
   [on : option nat] covering the allocator's two epochs in ONE spec:

     kalloc_avail γk (Some n)  -- boot mode: an EXCLUSIVE token asserting the
        free list holds exactly [n] pages.  It is a one-shot "pending" token
        [kalloc_pending] plus half of a ghost_var whose other half sits inside
        the lock invariant.  While anyone holds it, NO other thread can call
        kalloc/kfree at all (a [None]-mode call needs the sealed witness below,
        which cannot coexist with pending) -- formalizing "no concurrency
        during early boot".  With [Some (S k)], kalloc CANNOT return null.
     kalloc_avail γk None      -- steady state: the one-shot has fired; a
        PERSISTENT witness [kalloc_sealed] with no count.  The lock invariant
        drops its ghost_var half at the next lock acquisition (the auth is a
        disjunction), the exact count is forgotten forever, and kalloc may
        fail.  [kalloc_avail_seal] converts [Some n ==∗ None]; there is no way
        back.

   Specs (caller-facing, plain sequential Hoare triples -- NOT logically atomic):
     {{ is_kmem γ γk lk fl ∗ kalloc_avail γk on }}
         kalloc()  {{ r, kalloc_post γk on r }}
        kalloc_post γk on r :=
            (r = null ∗ avail_zero on ∗ kalloc_avail γk on)
          ∨ (page_valid r ∗ page_own r ∗ kalloc_avail γk (avail_dec on))
     {{ is_kmem γ γk lk fl ∗ kfree_pre p ∗ kalloc_avail γk on }}
         kfree(p)  {{ kalloc_avail γk (avail_inc on) }}
        kfree_pre p := page_valid p ∗ page_own p
   i.e. kalloc hands back full ownership of a fresh 4KB page (or null -- but
   only when the count is unknown or exactly 0), decrementing the count; kfree
   absorbs the page and increments it.  Boot code threads [Some n]; after
   sealing, everyone threads the trivially-available persistent [None].

   This file proves the separation-logic CORE of those triples -- the ghost
   count lemmas ([kmem_avail_dec]/[kmem_avail_inc]/[kalloc_avail_zero]) and how
   the invariant reassembles ([kmem_res_close]/[kmem_res_push]).  The
   instruction-level proofs (ProofKalloc/ProofKfree) open [is_kmem] around
   kalloc/kfree's loads/stores and discharge the triples using these lemmas. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.algebra Require Import excl agree csum.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_var.
From iris.program_logic Require Import weakestpre.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto WpLock.
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
Require Import TsoCtxShim.   (* THE SEAM MARKER (tso-port M3, kmem worked
   instance): this file's payload is context-indexed but the page-byte tier
   below it ([byte_any]/[page_own]) is not yet -- the ctx↔mem word bridges
   ([word_at_of_mem]/[word_at_to_mem]) cross that boundary and die at the
   M1 notation flip. *)
Require Export PageGeom.  (* the pure page geometry: page_valid / page_base / nullp *)
Local Open Scope Z_scope.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
Import Defs.


(* pure bookkeeping on the caller-side count [on : option nat]:
   [None] = count unknown (sealed);  [Some n] = exactly n pages free. *)
Definition avail_dec (on : option nat) : option nat :=
  match on with Some n => Some (Nat.pred n) | None => None end.
Definition avail_inc (on : option nat) : option nat :=
  match on with Some n => Some (S n) | None => None end.
Definition avail_zero (on : option nat) : Prop :=
  match on with Some n => n = 0%nat | None => True end.

(* iterated predecessor: the counter after [k] successful kallocs.  Defined
   THROUGH [avail_dec] so each step is one [Nat.iter] unfold (walk/mappages
   per-step accounting); [avail_sub_Some] gives the closed form (kvmmake
   budget arithmetic). *)
Definition avail_sub (on : option nat) (k : nat) : option nat :=
  Nat.iter k avail_dec on.

Lemma avail_sub_0 (on : option nat) : avail_sub on 0%nat = on.
Proof. reflexivity. Qed.
Lemma avail_sub_S (on : option nat) (k : nat) :
  avail_sub on (S k) = avail_dec (avail_sub on k).
Proof. reflexivity. Qed.
Lemma avail_sub_None (k : nat) : avail_sub None k = None.
Proof. induction k as [|k IH]; [reflexivity | rewrite avail_sub_S IH; reflexivity]. Qed.
Lemma avail_sub_Some (n k : nat) : avail_sub (Some n) k = Some (n - k)%nat.
Proof.
  induction k as [|k IH]; [rewrite avail_sub_0; f_equal; lia |].
  rewrite avail_sub_S IH. unfold avail_dec. f_equal. lia.
Qed.

(* composing two consumption runs: [a] then [b] more kallocs = [a+b] kallocs.
   The walk chain uses this to fold per-iteration node growth additively
   (mappages' loop accumulator) without any nat subtraction. *)
Lemma avail_sub_add (on : option nat) (a b : nat) :
  avail_sub on (a + b)%nat = avail_sub (avail_sub on a) b.
Proof.
  induction b as [|b IH].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. rewrite !avail_sub_S. rewrite IH. reflexivity.
Qed.

Section Kalloc.
  Context `{!riscvGS Σ, !lockG Σ, !kallocG Σ}.


  Definition byte_any (a : Arch.pa) : iProp Σ := (∃ b : bv 8, a ↦ₘ b)%I.
  (* THE CONTEXT-INDEXED WORD CELL (tso-port M3, the kmem worked instance):
     an 8-byte little-endian word owned by the CURRENT THREAD OF CONTROL --
     [↦c] is [ctx_pointsto cur_ctx], and the ambient context here is the
     section's [XI], bound by the payload wrapper at every [kmem_res]
     mention.  These are the facts that live UNDER the kmem lock (the
     freelist head cell, each free page's next pointer): deposited at the
     releaser's identity, handed to the acquirer at its own
     ([SpecAcquire]'s [R cur_ctx]).  The alignment conjunct mirrors
     [word_pointsto_unfold]'s shape, so the mem bridges below are
     one-liners. *)
  (* THE CONTEXT IS AN EXPLICIT ARGUMENT, NOT AMBIENT -- the audited rule
     (tso-port.md §2d): a definition that is genuinely a function of the
     thread of control must NAME it, because an ambient [CurCtx] left to
     instance resolution inside the payload wrapper resolves differently
     at different elaboration sites (measured here: one site bound the
     wrapper's context, another silently bound the file's -- the
     silent-drop hazard, verbatim).  Converted payloads are spelled
     [(λ ξ, kmem_res ξ …)]; the [<{ }>] wrapper remains for UNCONVERTED
     constant payloads only, where the ambiguity is harmless. *)
  Definition word_at (ξc : CtxId) (a : mword 64) (w : mword 64) : iProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
     [∗ list] j ∈ seq 0 8,
       ctx_pointsto ξc (pa_add a j) (DfracOwn 1) (nth_byte w j))%I.

  (* THE MEM BRIDGES -- the file's ctx↔mem seam, derived from the shim
     (SC-only; at cutover the flip has converted the byte tier and these
     die with their last consumer). *)
  Lemma word_at_of_mem {ξc : CtxId} (a : mword 64) (w : mword 64) :
    word_pointsto a (DfracOwn 1) w -∗ word_at ξc a w.
  Proof.
    rewrite word_pointsto_unfold /word_at. iIntros "[$ H]".
    iApply (big_sepL_impl with "H").
    iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_of_mem.
  Qed.

  Lemma word_at_to_mem {ξc : CtxId} (a : mword 64) (w : mword 64) :
    word_at ξc a w -∗ word_pointsto a (DfracOwn 1) w.
  Proof.
    rewrite word_pointsto_unfold /word_at. iIntros "[$ H]".
    iApply (big_sepL_impl with "H").
    iIntros "!>" (k j Hj) "Hb". by iApply ctx_pointsto_to_mem.
  Qed.
  Definition page_head8 (p : mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, byte_any (pa_add p j))%I.
  Definition page_rest (p : mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 8 4088, byte_any (pa_add p j))%I.
  Definition page_own (p : mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4096, byte_any (pa_add p j))%I.
  Definition run_page (ξc : CtxId) (p next : mword 64) : iProp Σ :=
    (word_at ξc p next ∗ page_rest p)%I.

  (* Seal the big-op leaves so [iFrame]/typeclass search treat each as an atom
     rather than recursing into its ~4096 per-byte conjuncts. *)
  Typeclasses Opaque byte_any word_at page_head8 page_rest page_own run_page.

  Lemma page_own_split p : page_own p ⊣⊢ page_head8 p ∗ page_rest p.
  Proof.
    rewrite /page_own /page_head8 /page_rest.
    replace 4096%nat with (8 + 4088)%nat by lia.
    rewrite seq_app big_sepL_app //.
  Qed.

  Lemma word_at_head8 {ξc : CtxId} p w : word_at ξc p w ⊢ page_head8 p.
  Proof.
    iIntros "H". iDestruct (word_at_to_mem with "H") as "H".
    rewrite /page_head8 word_pointsto_unfold. iDestruct "H" as "[_ H]".
    iApply (big_sepL_mono with "H"). iIntros (k j _) "Hb". iExists _. iExact "Hb".
  Qed.

  (* the converse direction kfree's [sd r->next] needs: the 8 arbitrary bytes of
     a page's head slot can be viewed as SOME 64-bit word window ready to be
     overwritten (word_pointsto also carries the required 8-alignment). *)
  Lemma page_head8_word_at {ξc : CtxId} p :
    page_valid p -> page_head8 p ⊢ ∃ w : mword 64, word_at ξc p w.
  Proof.
    intros Hv. rewrite /page_head8 /byte_any.
    change (seq 0 8) with [0;1;2;3;4;5;6;7]%nat.
    iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _)".
    iDestruct "H0" as (b0) "H0". iDestruct "H1" as (b1) "H1".
    iDestruct "H2" as (b2) "H2". iDestruct "H3" as (b3) "H3".
    iDestruct "H4" as (b4) "H4". iDestruct "H5" as (b5) "H5".
    iDestruct "H6" as (b6) "H6". iDestruct "H7" as (b7) "H7".
    set (bs := [b0;b1;b2;b3;b4;b5;b6;b7]).
    set (w := Z_to_bv 64 (assemble_bytes bs) : mword 64).
    iExists w. iApply word_at_of_mem.
    rewrite /word_pointsto.
    iSplitR; [iPureIntro; by apply page_valid_aligned8|].
    assert (E0 : nth_byte w 0%nat = b0) by (subst w bs; apply nth_byte_assemble8; [reflexivity | lia]).
    assert (E1 : nth_byte w 1%nat = b1) by (subst w bs; apply nth_byte_assemble8; [reflexivity | lia]).
    assert (E2 : nth_byte w 2%nat = b2) by (subst w bs; apply nth_byte_assemble8; [reflexivity | lia]).
    assert (E3 : nth_byte w 3%nat = b3) by (subst w bs; apply nth_byte_assemble8; [reflexivity | lia]).
    assert (E4 : nth_byte w 4%nat = b4) by (subst w bs; apply nth_byte_assemble8; [reflexivity | lia]).
    assert (E5 : nth_byte w 5%nat = b5) by (subst w bs; apply nth_byte_assemble8; [reflexivity | lia]).
    assert (E6 : nth_byte w 6%nat = b6) by (subst w bs; apply nth_byte_assemble8; [reflexivity | lia]).
    assert (E7 : nth_byte w 7%nat = b7) by (subst w bs; apply nth_byte_assemble8; [reflexivity | lia]).
    change (seq 0 8) with [0;1;2;3;4;5;6;7]%nat. simpl.
    rewrite E0 E1 E2 E3 E4 E5 E6 E7. iFrame.
  Qed.

  Lemma run_page_page_own {ξc : CtxId} p next : run_page ξc p next ⊢ page_own p.
  Proof.
    rewrite /run_page page_own_split. iIntros "[Hw $]". by iApply word_at_head8.
  Qed.

  (* the free list: [pages] chained through each page's [next] field *)
  Fixpoint freelist_chain (ξc : CtxId) (head : mword 64) (pages : list (mword 64)) : iProp Σ :=
    match pages with
    | [] => ⌜head = nullp⌝
    | p :: ps => ⌜head = p⌝ ∗ ⌜page_valid p⌝ ∗
                 (∃ nxt : mword 64, run_page ξc p nxt ∗ freelist_chain ξc nxt ps)
    end%I.

  Lemma freelist_chain_cons {ξc : CtxId} head p ps :
    freelist_chain ξc head (p :: ps)
    = (⌜head = p⌝ ∗ ⌜page_valid p⌝ ∗ (∃ nxt : mword 64, run_page ξc p nxt ∗ freelist_chain ξc nxt ps))%I.
  Proof. reflexivity. Qed.

  (* ===== the page-count ghost (see the header) ===== *)

  (* the one-shot seal: [pending] is the exclusive boot-mode token; firing it
     yields the persistent [sealed] witness.  They cannot coexist. *)
  Definition kalloc_pending (γs : gname) : iProp Σ :=
    own γs (Cinl (Excl ()) : kalloc_oneshotR).
  Definition kalloc_sealed (γs : gname) : iProp Σ :=
    own γs (Cinr (to_agree ()) : kalloc_oneshotR).
  Global Instance kalloc_sealed_persistent γs : Persistent (kalloc_sealed γs).
  Proof. apply _. Qed.

  Lemma kalloc_pending_sealed γs : kalloc_pending γs -∗ kalloc_sealed γs -∗ False.
  Proof. iIntros "Hp Hs". iDestruct (own_valid_2 with "Hp Hs") as %[]. Qed.

  (* the caller-side count: exclusive exact count (boot) or persistent no-info
     witness (steady state). *)
  Definition kalloc_avail (γk : gname * gname) (on : option nat) : iProp Σ :=
    match on with
    | Some n => kalloc_pending γk.2 ∗ ghost_var γk.1 (1/2)%Qp n
    | None   => kalloc_sealed γk.2
    end%I.
  Global Instance kalloc_avail_None_persistent γk : Persistent (kalloc_avail γk None).
  Proof. apply _. Qed.

  (* the invariant-side authority: while counting, the ghost_var's other half
     (tied to [length pages]); once the seal has fired, any lock holder may
     reclose into the count-free [sealed] arm -- and after the first such
     reclose the count is gone for good. *)
  Definition kmem_avail_auth (γk : gname * gname) (npages : nat) : iProp Σ :=
    (ghost_var γk.1 (1/2)%Qp npages ∨ kalloc_sealed γk.2)%I.

  Lemma kalloc_avail_alloc n :
    ⊢ |==> ∃ γk, kalloc_avail γk (Some n) ∗ kmem_avail_auth γk n.
  Proof.
    iMod (ghost_var_alloc n) as (γc) "Hg".
    iEval (rewrite -Qp.half_half) in "Hg".
    iDestruct (ghost_var_split with "Hg") as "[H1 H2]".
    iMod (own_alloc (Cinl (Excl ()) : kalloc_oneshotR)) as (γs) "Hp"; [done|].
    iModIntro. iExists (γc, γs). cbn. iFrame "Hp H1". iLeft. iFrame "H2".
  Qed.

  (* boot -> steady state: fire the one-shot, forget the count.  Irreversible;
     the result is persistent, so it can be handed to every later caller. *)
  Lemma kalloc_avail_seal γk n :
    kalloc_avail γk (Some n) ==∗ kalloc_avail γk None.
  Proof.
    iIntros "[Hp _]". iApply (own_update with "Hp").
    by apply cmra_update_exclusive.
  Qed.

  (* boot mode agrees with the invariant's count *)
  Lemma kalloc_avail_agree γk n npages :
    kalloc_avail γk (Some n) -∗ kmem_avail_auth γk npages -∗ ⌜n = npages⌝.
  Proof.
    iIntros "[Hp Hv] [Hv'|Hs]".
    - iApply (ghost_var_agree with "Hv Hv'").
    - iExFalso. iApply (kalloc_pending_sealed with "Hp Hs").
  Qed.

  (* an empty free list forces the caller's count (if any) to be 0 *)
  Lemma kalloc_avail_zero γk on :
    kalloc_avail γk on -∗ kmem_avail_auth γk 0%nat -∗ ⌜avail_zero on⌝.
  Proof.
    destruct on as [n|]; cbn.
    - iIntros "Hav Hauth". iApply (kalloc_avail_agree with "Hav Hauth").
    - auto.
  Qed.

  (* kalloc's ghost step: pop one page off the count *)
  Lemma kmem_avail_dec γk on npages :
    kalloc_avail γk on -∗ kmem_avail_auth γk (S npages) ==∗
    kalloc_avail γk (avail_dec on) ∗ kmem_avail_auth γk npages.
  Proof.
    iIntros "Hav Hauth". destruct on as [n|]; cbn.
    - iDestruct "Hav" as "[Hp Hv]".
      iDestruct "Hauth" as "[Hv'|Hs]";
        [| iExFalso; iApply (kalloc_pending_sealed with "Hp Hs")].
      iDestruct (ghost_var_agree with "Hv Hv'") as %->.
      iMod (ghost_var_update_halves npages with "Hv Hv'") as "[Hv Hv']".
      iModIntro. iFrame "Hp Hv". iLeft. iFrame "Hv'".
    - iDestruct "Hav" as "#Hs". iModIntro. iSplitR; [iExact "Hs" | iRight; iExact "Hs"].
  Qed.

  (* kfree's ghost step: push one page onto the count *)
  Lemma kmem_avail_inc γk on npages :
    kalloc_avail γk on -∗ kmem_avail_auth γk npages ==∗
    kalloc_avail γk (avail_inc on) ∗ kmem_avail_auth γk (S npages).
  Proof.
    iIntros "Hav Hauth". destruct on as [n|]; cbn.
    - iDestruct "Hav" as "[Hp Hv]".
      iDestruct "Hauth" as "[Hv'|Hs]";
        [| iExFalso; iApply (kalloc_pending_sealed with "Hp Hs")].
      iDestruct (ghost_var_agree with "Hv Hv'") as %->.
      iMod (ghost_var_update_halves (S npages) with "Hv Hv'") as "[Hv Hv']".
      iModIntro. iFrame "Hp Hv". iLeft. iFrame "Hv'".
    - iDestruct "Hav" as "#Hs". iModIntro. iSplitR; [iExact "Hs" | iRight; iExact "Hs"].
  Qed.

  (* the allocator's protected resource: the global freelist head pointer at
     [fl], ownership of every page currently in the list, and the count
     authority tied to the list's length. *)
  Definition kmem_res (ξc : CtxId) (γk : gname * gname) (fl : mword 64) : iProp Σ :=
    (∃ (head : mword 64) (pages : list (mword 64)),
        word_at ξc fl head ∗ freelist_chain ξc head pages ∗
        kmem_avail_auth γk (length pages))%I.

  (* the whole allocator = a spinlock whose resource is [kmem_res].  Persistent. *)
  Definition is_kmem (γ : gname) (γk : gname * gname) (lk fl : mword 64) : iProp Σ :=
    is_lock γ lk "kmem"%string (λ ξ : CtxId, kmem_res ξ γk fl).
  Global Instance is_kmem_persistent γ γk lk fl : Persistent (is_kmem γ γk lk fl).
  Proof. apply _. Qed.

  Lemma kmem_res_close {ξc : CtxId} γk fl head pages :
    word_at ξc fl head ∗ freelist_chain ξc head pages ∗ kmem_avail_auth γk (length pages)
    ⊢ kmem_res ξc γk fl.
  Proof. iIntros "H". iExists head, pages. iExact "H". Qed.

  (* ==================================================================
     THE PAYLOAD'S CtxMorph INSTANCES (tso-port M3): the obligation the
     acquire/release Parameters carry, exported beside the sealed
     definitions ([Typeclasses Opaque] above stops structural search from
     unfolding them, so each sealed shape gets its one instance here).
     These are REAL morphs -- the word cells re-index between threads of
     control -- unlike the constant embeddings of unconverted payloads;
     the page bodies ([page_rest]) are still context-free and ride the
     const instance until the M1 flip. *)
  Global Instance word_at_morph (a w : mword 64) :
    CtxMorph (λ ξ0 : CtxId, word_at ξ0 a w).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /word_at.
    iDestruct "H" as "[%Hal H]".
    (* instance search cannot do the higher-order big-op unification, so
       the structural instances are applied as terms *)
    iMod (ctx_morph_big_sepL (seq 0 8)
            (λ _ j ξ0, ctx_pointsto ξ0 (pa_add a j) (DfracOwn 1) (nth_byte w j))
            (λ i x, ctx_morph_pointsto _ _ _ _)
            ξ ξ' with "Hd H") as "[Hd H]".
    iModIntro. iFrame "Hd". iSplit; [done|]. iExact "H".
  Qed.

  Global Instance run_page_morph (p next : mword 64) :
    CtxMorph (λ ξ0 : CtxId, run_page ξ0 p next).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /run_page.
    iDestruct "H" as "[Hw Hr]".
    iMod (word_at_morph p next ξ ξ' with "Hd Hw") as "[Hd Hw]".
    iModIntro. iFrame.
  Qed.

  Global Instance freelist_chain_morph (head : mword 64)
      (pages : list (mword 64)) :
    CtxMorph (λ ξ0 : CtxId, freelist_chain ξ0 head pages).
  Proof.
    revert head. induction pages as [|p ps IH] => head.
    - iIntros (ξ ξ') "Hd H". iModIntro. iFrame.
    - iIntros (ξ ξ') "Hd H". simpl.
      iDestruct "H" as "(%Hh & %Hv & %nxt & Hrun & Hchain)".
      iMod (run_page_morph p nxt ξ ξ' with "Hd Hrun") as "[Hd Hrun]".
      iMod (IH nxt ξ ξ' with "Hd Hchain") as "[Hd Hchain]".
      iModIntro. iFrame "Hd".
      iSplit; [done|]. iSplit; [done|]. iExists nxt. iFrame.
  Qed.

  Global Instance kmem_res_morph (γk : gname * gname) (fl : mword 64) :
    CtxMorph (λ ξ0 : CtxId, kmem_res ξ0 γk fl).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /kmem_res.
    iDestruct "H" as (head pages) "(Hw & Hchain & Hauth)".
    iMod (word_at_morph fl head ξ ξ' with "Hd Hw") as "[Hd Hw]".
    iMod (freelist_chain_morph head pages ξ ξ' with "Hd Hchain")
      as "[Hd Hchain]".
    iModIntro. iFrame "Hd". iExists head, pages. iFrame.
  Qed.

  (* kalloc's logical core: the opened invariant either has an empty list (put
     it back unchanged, kalloc returns null -- [kalloc_avail_zero] pins the
     caller's count) or exposes the head page [p] -- its [next] pointer, its
     4KB, and the tail -- for the caller to take ([kmem_avail_dec] then steps
     the count down before reclosing with the tail). *)

  (* kfree's logical core: after the function has written [p->next := oldhead]
     and [fl := p], the pieces refold into the invariant with [p] prepended and
     the count stepped up. *)
  Lemma kmem_res_push {ξc : CtxId} γk fl p oldhead pages on :
    page_valid p ->
    kalloc_avail γk on -∗
    word_at ξc fl p -∗
    run_page ξc p oldhead -∗
    freelist_chain ξc oldhead pages -∗
    kmem_avail_auth γk (length pages) ==∗
    kalloc_avail γk (avail_inc on) ∗ kmem_res ξc γk fl.
  Proof.
    iIntros (Hp) "Hav Hfl Hrun Hchain Hauth".
    iMod (kmem_avail_inc γk on (length pages) with "Hav Hauth") as "[Hav Hauth]".
    iModIntro. iFrame "Hav".
    iApply (kmem_res_close γk fl p (p :: pages)). iFrame "Hfl".
    iSplitR "Hauth"; [| iExact "Hauth"].
    rewrite freelist_chain_cons. iSplit; [done|]. iSplit; [done|].
    iExists oldhead. iFrame "Hrun Hchain".
  Qed.

  (* ---- the caller-facing pre/post conditions ---- *)
  Definition kalloc_post (γk : gname * gname) (on : option nat) (r : mword 64) : iProp Σ :=
    ((⌜r = nullp⌝ ∗ ⌜avail_zero on⌝ ∗ kalloc_avail γk on)
     ∨ (⌜page_valid r⌝ ∗ page_own r ∗ kalloc_avail γk (avail_dec on)))%I.
  Definition kfree_pre (p : mword 64) : iProp Σ :=
    (⌜page_valid p⌝ ∗ page_own p)%I.

  (* boot-mode corollary: with a positive exact count, kalloc CANNOT fail *)
  Lemma kalloc_post_success γk k r :
    kalloc_post γk (Some (S k)) r -∗
    ⌜page_valid r⌝ ∗ page_own r ∗ kalloc_avail γk (Some k).
  Proof.
    iIntros "[(_ & %Hz & _) | H]"; [discriminate | iExact "H"].
  Qed.

  (* Intended Hoare triples -- the operation is the kernel's kalloc/kfree
     instruction stream, discharged by the instruction-level proofs
     (ProofKalloc / ProofKfree), which open [is_kmem] around their atomic
     loads/stores and apply the transfer lemmas above:

       {{ is_kmem γ γk lk fl ∗ kalloc_avail γk on }}
           kalloc()  {{ r, kalloc_post γk on r }}
       {{ is_kmem γ γk lk fl ∗ kfree_pre p ∗ kalloc_avail γk on }}
           kfree(p)  {{ kalloc_avail γk (avail_inc on) }}                  *)
End Kalloc.
