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
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto WpLock.
Local Open Scope Z_scope.
Import Defs.

Section Kalloc.
  Context `{!riscvGS Σ, !lockG Σ}.

  Definition nullp : mword 64 := mword_of_int 0.

  (* A free page must be exactly what the real [kfree]/[kalloc] enforce: a
     4096-byte-aligned physical address within [end, PHYSTOP).  kfree PANICS
     otherwise (bounds + [pa % PGSIZE] checks), and kalloc only ever hands out
     pages it earlier took in, so the invariant must CARRY this validity to make
     kalloc's result re-freeable.  [end = 0x80023558], [PHYSTOP = 17 << 27]. *)
  Definition PGSIZE  : Z := 4096.
  Definition kmem_lo : Z := 0x80023558.   (* <end> *)
  Definition kmem_hi : Z := 0x88000000.   (* PHYSTOP = 17 << 27 *)
  Definition page_aligned (p : mword 64) : Prop := (uint p) mod PGSIZE = 0.
  Definition page_in_range (p : mword 64) : Prop := kmem_lo <= uint p < kmem_hi.
  Definition page_valid (p : mword 64) : Prop := page_aligned p /\ page_in_range p.

  (* a valid page is never the null pointer (its address is >= [end] > 0) *)
  Lemma page_valid_ne_null p : page_valid p -> p <> nullp.
  Proof.
    intros [_ [Hlo _]] Heq. subst p. unfold nullp in Hlo.
    assert (uint (mword_of_int 0 : mword 64) = 0) as H0 by reflexivity.
    rewrite H0 in Hlo. unfold kmem_lo in Hlo. lia.
  Qed.

  (* PGSIZE(4096)-alignment implies doubleword(8)-alignment, in the exact
     [is_aligned_paddr] shape [word_pointsto]/[word_at] demand. *)
  Lemma page_valid_aligned8 p : page_valid p -> is_aligned_paddr (Physaddr p) 8 = true.
  Proof.
    intros [Hal _]. unfold page_aligned, PGSIZE in Hal.
    unfold is_aligned_paddr. apply Z.eqb_eq.
    assert (Hnn : 0 <= uint p) by (unfold uint; pose proof (bv_unsigned_in_range 64 p); lia).
    assert (Hrem : Z.rem (uint p) 8 = (uint p) mod 8) by (apply Z.rem_mod_nonneg; lia).
    rewrite Hrem.
    apply Z.mod_divide in Hal; [| lia]. apply Z.mod_divide; [lia|].
    apply (Z.divide_trans 8 4096); [ exists 512; reflexivity | exact Hal ].
  Qed.

  (* the little-endian 64-bit word built from 8 bytes reproduces those bytes *)
  Lemma nth_byte_assemble8 (bs : list (bv 8)) (j : nat) :
    length bs = 8%nat -> (j < 8)%nat ->
    nth_byte (Z_to_bv 64 (assemble_bytes bs) : mword 64) j = bs !!! j.
  Proof.
    intros Hlen Hj. apply bv_eq. rewrite nth_byte_unsigned.
    rewrite Z_to_bv_unsigned.
    pose proof (assemble_bytes_bound bs) as [Hlo Hhi]. rewrite Hlen in Hhi. simpl in Hhi.
    assert (Hws : bv_wrap 64 (assemble_bytes bs) = assemble_bytes bs).
    { apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
    rewrite Hws.
    assert (Hab : (assemble_bytes bs ≫ Z.of_nat (8 * j)) `mod` 2 ^ 8 = bv_unsigned (bs !!! j))
      by (apply assemble_bytes_byte; lia).
    rewrite <- Hab.
    f_equal. f_equal. lia.
  Qed.

  Definition byte_any (a : Arch.pa) : iProp Σ := (∃ b : bv 8, a ↦ₘ b)%I.
  (* an 8-byte little-endian word, now expressed via the [word_pointsto]
     abstraction (so it also carries the doubleword-alignment of [a]). *)
  Definition word_at (a : mword 64) (w : mword 64) : iProp Σ :=
    word_pointsto a (DfracOwn 1) w.
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
    rewrite /word_at /page_head8 word_pointsto_unfold. iIntros "[_ H]".
    iApply (big_sepL_mono with "H"). iIntros (k j _) "Hb". iExists _. iExact "Hb".
  Qed.

  (* the converse direction kfree's [sd r->next] needs: the 8 arbitrary bytes of
     a page's head slot can be viewed as SOME 64-bit word window ready to be
     overwritten (word_pointsto also carries the required 8-alignment). *)
  Lemma page_head8_word_at p :
    page_valid p -> page_head8 p ⊢ ∃ w : mword 64, word_at p w.
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
    iExists w.
    rewrite /word_at /word_pointsto.
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

  Lemma run_page_page_own p next : run_page p next ⊢ page_own p.
  Proof.
    rewrite /run_page page_own_split. iIntros "[Hw $]". by iApply word_at_head8.
  Qed.

  (* the free list: [pages] chained through each page's [next] field *)
  Fixpoint freelist_chain (head : mword 64) (pages : list (mword 64)) : iProp Σ :=
    match pages with
    | [] => ⌜head = nullp⌝
    | p :: ps => ⌜head = p⌝ ∗ ⌜page_valid p⌝ ∗
                 (∃ nxt : mword 64, run_page p nxt ∗ freelist_chain nxt ps)
    end%I.

  Lemma freelist_chain_cons head p ps :
    freelist_chain head (p :: ps)
    = (⌜head = p⌝ ∗ ⌜page_valid p⌝ ∗ (∃ nxt : mword 64, run_page p nxt ∗ freelist_chain nxt ps))%I.
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
          ⌜page_valid p⌝ ∗ word_at fl p ∗ run_page p nxt ∗ freelist_chain nxt ps).
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
    page_valid p ->
    word_at fl p ∗ run_page p oldhead ∗ freelist_chain oldhead pages ⊢ kmem_res fl.
  Proof.
    iIntros (Hp) "(Hfl & Hrun & Hchain)".
    iApply (kmem_res_close fl p (p :: pages)). iFrame "Hfl".
    rewrite freelist_chain_cons. iSplit; [done|]. iSplit; [done|].
    iExists oldhead. iFrame "Hrun Hchain".
  Qed.

  (* ---- the caller-facing pre/post conditions ---- *)
  Definition kalloc_post (r : mword 64) : iProp Σ :=
    (⌜r = nullp⌝ ∨ (⌜page_valid r⌝ ∗ page_own r))%I.
  Definition kfree_pre (p : mword 64) : iProp Σ :=
    (⌜page_valid p⌝ ∗ page_own p)%I.

  (* Intended Hoare triples -- the operation is the kernel's kalloc/kfree
     instruction stream, discharged by the (later) instruction-level proof,
     which opens [is_kmem] around its atomic loads/stores and applies the
     transfer lemmas above:

       {{ is_kmem γ lk fl }}                  kalloc()  {{ r, kalloc_post r }}
       {{ is_kmem γ lk fl ∗ kfree_pre p }}    kfree(p)  {{ True }}          *)
End Kalloc.
