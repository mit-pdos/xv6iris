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
   &kmem.lock, giving [is_kmem γ lk fl := is_lock γ lk (kmem_res fl)].

   Specs (caller-facing, plain sequential Hoare triples -- NOT logically atomic):
     {{ is_kmem γ lk fl }}                kalloc()  {{ r, kalloc_post r }}
        kalloc_post r := r = null  ∨  (r ≠ null ∗ page_own r)
     {{ is_kmem γ lk fl ∗ kfree_pre p }}  kfree(p)  {{ True }}
        kfree_pre p  := p ≠ null ∗ page_own p
   i.e. kalloc hands back full ownership of a fresh 4KB page (or null); kfree
   demands full ownership of the page (contents irrelevant, existentially
   quantified per byte).

   This file proves the separation-logic CORE of those triples -- how the
   invariant releases a page ([kmem_res_pop]) and absorbs one ([kmem_res_push]).
   The instruction-level proof (later) opens [is_kmem] around kalloc/kfree's
   atomic loads/stores and discharges the triples using these lemmas. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants own.
From iris.program_logic Require Import weakestpre.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto WpLock.
Local Open Scope Z_scope.
Import Defs.

Section Kalloc.
  Context `{!riscvGS Σ, !lockG Σ}.

  Definition nullp : mword 64 := mword_of_int 0.

  Definition byte_any (a : Arch.pa) : iProp Σ := (∃ b : bv 8, a ↦ₘ b)%I.
  Definition word_at (a : mword 64) (w : mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ nth_byte w j)%I.
  Definition page_head8 (p : mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, byte_any (pa_add p j))%I.
  Definition page_rest (p : mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 8 4088, byte_any (pa_add p j))%I.
  Definition page_own (p : mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4096, byte_any (pa_add p j))%I.
  Definition run_page (p next : mword 64) : iProp Σ :=
    (word_at p next ∗ page_rest p)%I.

  (* Seal the big-op leaves so [iFrame]/typeclass search treat each as an atom
     rather than recursing into its ~4096 per-byte conjuncts. *)
  Typeclasses Opaque byte_any word_at page_head8 page_rest page_own run_page.

  Lemma page_own_split p : page_own p ⊣⊢ page_head8 p ∗ page_rest p.
  Proof.
    rewrite /page_own /page_head8 /page_rest.
    replace 4096%nat with (8 + 4088)%nat by lia.
    rewrite seq_app big_sepL_app //.
  Qed.

  Lemma word_at_head8 p w : word_at p w ⊢ page_head8 p.
  Proof.
    rewrite /word_at /page_head8. iIntros "H".
    iApply (big_sepL_mono with "H"). iIntros (k j _) "Hb". iExists _. iExact "Hb".
  Qed.

  Lemma run_page_page_own p next : run_page p next ⊢ page_own p.
  Proof.
    rewrite /run_page page_own_split. iIntros "[Hw $]". by iApply word_at_head8.
  Qed.

  (* the free list: [pages] chained through each page's [next] field *)
  Fixpoint freelist_chain (head : mword 64) (pages : list (mword 64)) : iProp Σ :=
    match pages with
    | [] => ⌜head = nullp⌝
    | p :: ps => ⌜head = p⌝ ∗ ⌜p ≠ nullp⌝ ∗
                 (∃ nxt : mword 64, run_page p nxt ∗ freelist_chain nxt ps)
    end%I.

  Lemma freelist_chain_cons head p ps :
    freelist_chain head (p :: ps)
    = (⌜head = p⌝ ∗ ⌜p ≠ nullp⌝ ∗ (∃ nxt : mword 64, run_page p nxt ∗ freelist_chain nxt ps))%I.
  Proof. reflexivity. Qed.

  (* the allocator's protected resource: the global freelist head pointer at
     [fl], plus ownership of every page currently in the list. *)
  Definition kmem_res (fl : mword 64) : iProp Σ :=
    (∃ (head : mword 64) (pages : list (mword 64)),
        word_at fl head ∗ freelist_chain head pages)%I.

  (* the whole allocator = a spinlock whose resource is [kmem_res].  Persistent. *)
  Definition is_kmem (γ : gname) (lk fl : mword 64) : iProp Σ :=
    is_lock γ lk (kmem_res fl).
  Global Instance is_kmem_persistent γ lk fl : Persistent (is_kmem γ lk fl).
  Proof. apply _. Qed.

  Lemma kmem_res_close fl head pages :
    word_at fl head ∗ freelist_chain head pages ⊢ kmem_res fl.
  Proof. iIntros "H". iExists head, pages. iExact "H". Qed.

  (* kalloc's logical core: the opened invariant either has an empty list (put
     it back unchanged, kalloc returns null) or exposes the head page [p] -- its
     [next] pointer, its 4KB, and the tail -- for the caller to take. *)
  Lemma kmem_res_pop fl :
    kmem_res fl ⊢
       (kmem_res fl)
     ∨ (∃ (p nxt : mword 64) (ps : list (mword 64)),
          ⌜p ≠ nullp⌝ ∗ word_at fl p ∗ run_page p nxt ∗ freelist_chain nxt ps).
  Proof.
    iIntros "H". iDestruct "H" as (head pages) "[Hfl Hchain]".
    destruct pages as [|p ps].
    - iLeft. iApply kmem_res_close. iFrame.
    - iRight. rewrite freelist_chain_cons.
      iDestruct "Hchain" as "(-> & %Hp & Hrun)".
      iDestruct "Hrun" as (nxt) "[Hrun Hchain]".
      iExists p, nxt, ps. iFrame "Hfl Hrun Hchain". done.
  Qed.

  (* kfree's logical core: after the function has written [p->next := oldhead]
     and [fl := p], the pieces refold into the invariant with [p] prepended. *)
  Lemma kmem_res_push fl p oldhead pages :
    p ≠ nullp ->
    word_at fl p ∗ run_page p oldhead ∗ freelist_chain oldhead pages ⊢ kmem_res fl.
  Proof.
    iIntros (Hp) "(Hfl & Hrun & Hchain)".
    iApply (kmem_res_close fl p (p :: pages)). iFrame "Hfl".
    rewrite freelist_chain_cons. iSplit; [done|]. iSplit; [done|].
    iExists oldhead. iFrame "Hrun Hchain".
  Qed.

  (* ---- the caller-facing pre/post conditions ---- *)
  Definition kalloc_post (r : mword 64) : iProp Σ :=
    (⌜r = nullp⌝ ∨ (⌜r ≠ nullp⌝ ∗ page_own r))%I.
  Definition kfree_pre (p : mword 64) : iProp Σ :=
    (⌜p ≠ nullp⌝ ∗ page_own p)%I.

  (* Intended Hoare triples -- the operation is the kernel's kalloc/kfree
     instruction stream, discharged by the (later) instruction-level proof,
     which opens [is_kmem] around its atomic loads/stores and applies the
     transfer lemmas above:

       {{ is_kmem γ lk fl }}                  kalloc()  {{ r, kalloc_post r }}
       {{ is_kmem γ lk fl ∗ kfree_pre p }}    kfree(p)  {{ True }}          *)
End Kalloc.
