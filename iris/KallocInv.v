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
   &kmem.lock, giving [is_kmem γ lk fl := is_lock γ lk "kmem" (kmem_res fl)].

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
Local Open Scope Z_scope.
Import Defs.

(* ghost state for the page-count layer: a nat-valued ghost_var (the count,
   γk.1) and a one-shot (the boot->steady seal, γk.2). *)
Definition kalloc_oneshotR := csumR (exclR unitO) (agreeR unitO).
Class kallocG (Σ : gFunctors) := KallocG {
  kalloc_count_inG :: ghost_varG Σ nat;
  kalloc_seal_inG :: inG Σ kalloc_oneshotR;
}.
Definition kallocΣ : gFunctors := #[ghost_varΣ nat; GFunctor kalloc_oneshotR].
Global Instance subG_kallocΣ {Σ} : subG kallocΣ Σ -> kallocG Σ.
Proof. solve_inG. Qed.

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

  (* ...which is what decides the [bnez a0] every caller of a page-returning
     routine (walkaddr, vmfault, kalloc) branches on: a page it handed back is
     never NULL, so the branch is not a case split. *)
  Lemma page_valid_neq_zero (q : mword 64) : page_valid q -> neq_vec q zero_reg = true.
  Proof.
    intro Hv. unfold neq_vec.
    assert (Hzr : (zero_reg : mword 64) = mword_of_int 0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hzr.
    destruct (eq_vec q (mword_of_int 0)) eqn:E; [| reflexivity].
    apply eq_vec_true_iff in E.
    destruct (page_valid_ne_null q Hv E).
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

  (* --- bridge to the kernel data region (RiscvPtsto's [addr_is_kdata]) ---

     [uint]/[bv_unsigned] bridge and the additive-offset fact for [pa_add],
     re-derived here rather than pulled from SmodePte.v (which drags in the
     whole InstrBytes/WP stack) -- see [uint_unsigned]/[uint_pa_add] in
     SmodePte.v / WpSmodeGpr.v for the upstream originals; this is the same
     one-line proof, kept local so KallocInv's Require chain stays light. *)
  Local Lemma kalloc_uint_unsigned (a : mword 64) : uint a = bv_unsigned a.
  Proof.
    pose proof (bv_unsigned_in_range _ a) as Hr.
    unfold uint, get_word, MachineWord.MachineWord.word_to_N.
    rewrite Z2N.id; [ reflexivity | lia ].
  Qed.

  Local Lemma kalloc_uint_pa_add (a : mword 64) (j : nat) :
    (uint a + Z.of_nat j < 18446744073709551616)%Z ->
    uint (pa_add a j) = uint a + Z.of_nat j.
  Proof.
    intro Hlt. rewrite !kalloc_uint_unsigned in Hlt |- *.
    unfold pa_add, add_vec_int, add_vec, Operators_mwords.word_binop,
      Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
    unfold MachineWord.MachineWord.add.
    rewrite bv_add_unsigned.
    assert (Hj : bv_unsigned (mword_of_int (Z.of_nat j) : mword 64) = Z.of_nat j).
    { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small.
      pose proof (bv_unsigned_in_range 64 a) as Har. destruct Har as [Har _].
      assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
      split.
      - apply Nat2Z.is_nonneg.
      - apply Z.le_lt_trans with (bv_unsigned a + Z.of_nat j).
        + rewrite <- (Z.add_0_l (Z.of_nat j)) at 1. apply Z.add_le_mono_r. exact Har.
        + exact Hlt. }
    rewrite Hj.
    apply bv_wrap_small.
    pose proof (bv_unsigned_in_range 64 a) as Har. destruct Har as [Har _].
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
    split.
    - apply Z.add_nonneg_nonneg. exact Har. apply Nat2Z.is_nonneg.
    - exact Hlt.
  Qed.

  (* THE BRIDGE LEMMA: every byte of a kalloc page lies in the kernel data
     region [RiscvPtsto.addr_is_kdata] = [etext, PHYSTOP).  Pure arithmetic on
     the concrete literals: [kmem_lo] (0x80023558) > [text_end]
     (0x80007000), and [kmem_hi] (0x88000000) = [ram_base]+[ram_size] =
     PHYSTOP.  Page-alignment of both [p] and [kmem_hi] is what keeps
     [uint p + j] strictly below [kmem_hi] for every in-page offset [j] --
     [page_in_range] alone (without [page_aligned]) is not enough. *)
  Lemma page_in_range_addr_is_kdata (p : mword 64) (j : nat) :
    page_valid p -> (j < 4096)%nat -> addr_is_kdata (pa_add p j).
  Proof.
    intros [Hal [Hlo Hhi]] Hj.
    assert (Hlit : text_end <= kmem_lo) by (unfold text_end, kmem_lo; lia).
    assert (Hhilit : kmem_hi = ram_base + ram_size)
      by (unfold kmem_hi, ram_base, ram_size; lia).
    assert (Hhimod : kmem_hi mod 4096 = 0) by (unfold kmem_hi; vm_compute; reflexivity).
    (* [uint p] is a multiple of 4096 (from [page_aligned]) strictly below
       [kmem_hi], itself a multiple of 4096, so [uint p <= kmem_hi - 4096]. *)
    assert (Hstep : uint p <= kmem_hi - 4096).
    { unfold page_aligned, PGSIZE in Hal.
      apply Z.mod_divide in Hal; [ | lia ]. apply Z.mod_divide in Hhimod; [ | lia ].
      destruct Hal as [ka Hka]. destruct Hhimod as [kb Hkb]. lia. }
    assert (Hno : (uint p + Z.of_nat j < 18446744073709551616)%Z)
      by (unfold kmem_hi in Hhi; lia).
    unfold addr_is_kdata. rewrite (kalloc_uint_pa_add p j Hno). lia.
  Qed.

  (* the width-8 instance of [RiscvModelBytes.nth_byte_assemble_len]. *)
  Lemma nth_byte_assemble8 (bs : list (bv 8)) (j : nat) :
    length bs = 8%nat -> (j < 8)%nat ->
    nth_byte (Z_to_bv 64 (assemble_bytes bs) : mword 64) j = bs !!! j.
  Proof. intros Hlen Hj. apply nth_byte_assemble_len; lia. Qed.

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
  Definition kmem_res (γk : gname * gname) (fl : mword 64) : iProp Σ :=
    (∃ (head : mword 64) (pages : list (mword 64)),
        word_at fl head ∗ freelist_chain head pages ∗
        kmem_avail_auth γk (length pages))%I.

  (* the whole allocator = a spinlock whose resource is [kmem_res].  Persistent. *)
  Definition is_kmem (γ : gname) (γk : gname * gname) (lk fl : mword 64) : iProp Σ :=
    is_lock γ lk "kmem"%string (kmem_res γk fl).
  Global Instance is_kmem_persistent γ γk lk fl : Persistent (is_kmem γ γk lk fl).
  Proof. apply _. Qed.

  Lemma kmem_res_close γk fl head pages :
    word_at fl head ∗ freelist_chain head pages ∗ kmem_avail_auth γk (length pages)
    ⊢ kmem_res γk fl.
  Proof. iIntros "H". iExists head, pages. iExact "H". Qed.

  (* kalloc's logical core: the opened invariant either has an empty list (put
     it back unchanged, kalloc returns null -- [kalloc_avail_zero] pins the
     caller's count) or exposes the head page [p] -- its [next] pointer, its
     4KB, and the tail -- for the caller to take ([kmem_avail_dec] then steps
     the count down before reclosing with the tail). *)

  (* kfree's logical core: after the function has written [p->next := oldhead]
     and [fl := p], the pieces refold into the invariant with [p] prepended and
     the count stepped up. *)
  Lemma kmem_res_push γk fl p oldhead pages on :
    page_valid p ->
    kalloc_avail γk on -∗
    word_at fl p -∗
    run_page p oldhead -∗
    freelist_chain oldhead pages -∗
    kmem_avail_auth γk (length pages) ==∗
    kalloc_avail γk (avail_inc on) ∗ kmem_res γk fl.
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
