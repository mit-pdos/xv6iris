(* ByteBuf.v -- the byte-buffer algebra the copy loops run on.

   A "buffer" here is exactly the shape memmove's contract (SpecMemmove.v)
   consumes and produces:

       [∗ list] j ∈ seq 0 n, pa_add p j ↦ₘ f j

   -- [n] consecutive bytes from [p], with their values named by a function.
   copyin / copyout walk such a buffer one page-chunk at a time, so they need
   three things this file provides, all of them independent of what is being
   copied:

     SPLIT / JOIN a buffer into PREFIX / CHUNK / SUFFIX ([bb_split3],
       [bb_join3]), so the chunk can be handed to memmove re-anchored at its
       own base and put back afterwards.  The THREE-way form is the primary
       one and the one a copy loop should call: the two-way [bb_split] leaves
       the caller to unify [f (k + j)] against a metavariable [?f j], which is
       higher-order and fragile at a SYMBOLIC offset, whereas [bb_split3]
       spells all three windows and their naming functions explicitly.  The
       total length is a PREMISE ([a + b + c = L]) rather than the literal
       shape of the goal, so no [rewrite]-the-index dance is needed either.
       [bb_split]/[bb_join] remain as the two-way special cases ([c = 0]);
     NAME the bytes of an anonymous region ([bb_any_named]) -- kalloc's
       [page_own] and [ProcPtOwn]'s user pages are contents-EXISTENTIAL, and
       memmove wants a named source; and the converse ([bb_named_any]), used
       to give the page back;
     REBRAND the naming function ([bb_ext], [bb_join]), because the two halves
       of a buffer are named by two different functions and the caller's
       postcondition names the whole of it by one.

   A buffer is also read and written a WORD at a time -- a C struct laid over
   it ([struct logheader]'s [n] and [block[]]) is 4-byte fields, not bytes --
   so the same window vocabulary has a 32-bit twin: [bb_mk] (the word four
   consecutive named bytes spell), [bb_set] (the naming function a 4-byte
   store leaves behind), and [bb_word4_acc], which borrows the aligned cell
   at an offset out of a window and gives it back holding a new value.

   Nothing here mentions page tables, so it is reusable by copyinstr and by
   any future byte-range code. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvPtsto.
Require Import InstrBytes.
Require Import KallocInv.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* A C STRING inside a buffer, as a property of the naming function.      *)
(* ===================================================================== *)
(* [bb_nonul f d]: the first [d] bytes are all non-NUL.  [bb_cstr f k]: the
   buffer holds a NUL-terminated string of length [k] -- the NUL is at [k]
   and nowhere before it, so [k] is the length [strlen] will report.  This is
   the whole of what copyinstr promises and the whole of what strlen assumes;
   nothing is said about the bytes past the terminator, which is why the
   predicate is on the naming function rather than on the resource.

   Deliberately NOT [RiscvPtsto]'s [↦ₛ]: that indexes a region by a Coq
   [string] and is meant for the kernel's read-only literals (persistent,
   contents known).  Bytes copied out of USER memory have no known contents,
   and the buffer they land in is longer than the string, so the naming
   function -- the same one [bb_split3] / [bb_byte_acc] already move around --
   is both the weaker and the more usable form.  Convert to [↦ₛ] later if a
   caller ever wants it. *)
Definition bb_nonul (f : nat -> bv 8) (d : nat) : Prop :=
  forall j, (j < d)%nat -> f j <> (mword_of_int 0 : mword 8).

Definition bb_cstr (f : nat -> bv 8) (k : nat) : Prop :=
  bb_nonul f k /\ f k = (mword_of_int 0 : mword 8).

Lemma bb_nonul_0 (f : nat -> bv 8) : bb_nonul f 0%nat.
Proof. intros j Hj. exfalso. lia. Qed.

(* the two ways a byte-at-a-time copy extends the prefix it has built *)
Lemma bb_nonul_step (f : nat -> bv 8) (d : nat) :
  bb_nonul f d -> f d <> (mword_of_int 0 : mword 8) -> bb_nonul f (S d).
Proof.
  intros Hn Hd j Hj.
  destruct (Nat.eq_dec j d) as [-> | Hne]; [exact Hd | apply Hn; lia].
Qed.

Lemma bb_cstr_intro (f : nat -> bv 8) (k : nat) :
  bb_nonul f k -> f k = (mword_of_int 0 : mword 8) -> bb_cstr f k.
Proof. intros H1 H2. split; [exact H1 | exact H2]. Qed.

(* [bb_cstr] pins the terminator's index: there is only ONE NUL-terminated
   reading of a buffer.  This is what lets strlen's loop conclude that the
   zero byte it stopped at is the [k] its precondition named. *)
Lemma bb_cstr_uniq (f : nat -> bv 8) (k d : nat) :
  bb_cstr f k -> bb_nonul f d -> f d = (mword_of_int 0 : mword 8) -> d = k.
Proof.
  intros [Hnk Hzk] Hnd Hzd.
  destruct (Nat.lt_trichotomy d k) as [Hlt | [Heq | Hgt]].
  - exfalso. exact (Hnk d Hlt Hzd).
  - exact Heq.
  - exfalso. exact (Hnd k Hgt Hzk).
Qed.

(* the functional update a single-byte store performs on the naming function *)
Definition bb_upd (f : nat -> bv 8) (d : nat) (b : bv 8) : nat -> bv 8 :=
  fun j => if Nat.eq_dec j d then b else f j.

Lemma bb_upd_eq (f : nat -> bv 8) (d : nat) (b : bv 8) : bb_upd f d b d = b.
Proof. rewrite /bb_upd. destruct (Nat.eq_dec d d); [reflexivity | done]. Qed.

Lemma bb_upd_ne (f : nat -> bv 8) (d : nat) (b : bv 8) (j : nat) :
  j <> d -> bb_upd f d b j = f j.
Proof. intro H. rewrite /bb_upd. destruct (Nat.eq_dec j d); [done | reflexivity]. Qed.

Lemma bb_nonul_upd (f : nat -> bv 8) (d : nat) (b : bv 8) :
  bb_nonul f d -> b <> (mword_of_int 0 : mword 8) -> bb_nonul (bb_upd f d b) (S d).
Proof.
  intros Hn Hb. apply bb_nonul_step.
  - intros j Hj. rewrite bb_upd_ne; [apply Hn; exact Hj | lia].
  - rewrite bb_upd_eq. exact Hb.
Qed.

Lemma bb_cstr_upd (f : nat -> bv 8) (d : nat) :
  bb_nonul f d -> bb_cstr (bb_upd f d (mword_of_int 0 : mword 8)) d.
Proof.
  intro Hn. apply bb_cstr_intro; [| apply bb_upd_eq].
  intros j Hj. rewrite bb_upd_ne; [apply Hn; exact Hj | lia].
Qed.

(* ===================================================================== *)
(* A FOUR-BYTE WORD inside a buffer, as a property of the naming function. *)
(* ===================================================================== *)
(* The byte-at-a-time vocabulary above has a word-at-a-time twin, and any
   code that lays a C struct over a tracked byte window needs it: a 4-byte
   store moves the window's naming function by [bb_set], and every reading
   of a word OUT of the window -- including the one that says what a store
   just left there -- is [bb_mk].  The two are mutually inverse
   ([bb_mk_set] one way, [bb_set_mk] the other), which is what lets a proof
   that borrowed a cell and put it back UNCHANGED recover the window it
   started with.  All of it is over plain [nat]/[Z] and closed words, so no
   solver ever runs inside a WP context. *)

(* the naming-function update a 4-byte store performs *)
Definition bb_set (f : nat -> bv 8) (o : nat) (w : mword 32) : nat -> bv 8 :=
  fun j => if decide ((o <= j)%nat /\ (j < o + 4)%nat)
           then nth_byte w (j - o)%nat else f j.

Lemma bb_set_in (f : nat -> bv 8) (o : nat) (w : mword 32) (j : nat) :
  (o <= j)%nat -> (j < o + 4)%nat -> bb_set f o w j = nth_byte w (j - o)%nat.
Proof. intros H1 H2. rewrite /bb_set decide_True; [reflexivity | split; assumption]. Qed.

Lemma bb_set_out (f : nat -> bv 8) (o : nat) (w : mword 32) (j : nat) :
  ((j < o)%nat \/ (o + 4 <= j)%nat) -> bb_set f o w j = f j.
Proof. intro H. rewrite /bb_set decide_False; [reflexivity | intros [A B]; lia]. Qed.

(* the word four consecutive named bytes spell *)
Definition bb_mk (f : nat -> bv 8) (o : nat) : mword 32 :=
  Z_to_bv 32 (assemble_bytes
                [f o; f (o + 1)%nat; f (o + 2)%nat; f (o + 3)%nat]).

Lemma bb_mk_byte (f : nat -> bv 8) (o j : nat) : (j < 4)%nat ->
  nth_byte (bb_mk f o) j = f (o + j)%nat.
Proof.
  intro Hj. rewrite /bb_mk.
  rewrite (nth_byte_assemble_len 32
             [f o; f (o + 1)%nat; f (o + 2)%nat; f (o + 3)%nat] j
             ltac:(cbn; lia) ltac:(cbn; lia)).
  destruct j as [|[|[|[|j']]]]; cbn;
    [ f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia | lia ].
Qed.

Lemma bb_assemble_len4 (bs : list (bv 8)) : length bs = 4%nat ->
  bv_unsigned (Z_to_bv 32 (assemble_bytes bs) : mword 32) = assemble_bytes bs.
Proof.
  intro Hlen. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (assemble_bytes_bound bs) as [Hlo Hhi].
  rewrite Hlen in Hhi.
  assert (Hb : (2 ^ (8 * Z.of_nat 4%nat))%Z = 4294967296%Z)
    by (vm_compute; reflexivity).
  rewrite Hb in Hhi.
  assert (Hm : bv_modulus (MachineWord.Z_idx 32) = 4294967296%Z)
    by (vm_compute; reflexivity).
  rewrite Hm. lia.
Qed.

(* four bytes that ARE a word's bytes assemble to that word's value *)
Lemma bb_word_bytes (bs : list (bv 8)) (w : mword 32) :
  length bs = 4%nat ->
  (forall j, (j < 4)%nat -> bs !!! j = nth_byte w j) ->
  assemble_bytes bs = bv_unsigned w.
Proof.
  intros Hlen Hbs.
  assert (Heq : (Z_to_bv 32 (assemble_bytes bs) : mword 32) = w).
  { apply (bv_eq_of_bytes (n := 4)). intros j Hj.
    assert (Hj4 : (j < 4)%nat) by lia.
    rewrite (nth_byte_assemble_len 32 bs j
               ltac:(rewrite Hlen; cbn; lia) ltac:(rewrite Hlen; lia)).
    apply Hbs. exact Hj4. }
  transitivity (bv_unsigned (Z_to_bv 32 (assemble_bytes bs) : mword 32)).
  - symmetry. apply (bb_assemble_len4 bs Hlen).
  - rewrite Heq. reflexivity.
Qed.

(* WRITE then READ: the cell holds what the store put there *)
Lemma bb_mk_set (f : nat -> bv 8) (o : nat) (w : mword 32) :
  bb_mk (bb_set f o w) o = w.
Proof.
  rewrite /bb_mk.
  rewrite (bb_set_in f o w o ltac:(lia) ltac:(lia)).
  rewrite (bb_set_in f o w (o + 1)%nat ltac:(lia) ltac:(lia)).
  rewrite (bb_set_in f o w (o + 2)%nat ltac:(lia) ltac:(lia)).
  rewrite (bb_set_in f o w (o + 3)%nat ltac:(lia) ltac:(lia)).
  replace (o - o)%nat with 0%nat by lia.
  replace (o + 1 - o)%nat with 1%nat by lia.
  replace (o + 2 - o)%nat with 2%nat by lia.
  replace (o + 3 - o)%nat with 3%nat by lia.
  apply (bv_eq_of_bytes (n := 4)). intros j Hj.
  assert (Hj4 : (j < 4)%nat) by lia.
  rewrite (nth_byte_assemble_len 32
             [nth_byte w 0%nat; nth_byte w 1%nat;
              nth_byte w 2%nat; nth_byte w 3%nat]
             j ltac:(cbn; lia) ltac:(cbn; lia)).
  destruct j as [|[|[|[|j']]]]; cbn; try reflexivity. lia.
Qed.

(* READ then WRITE BACK: a cell given back unchanged leaves the window
   pointwise as it was -- no index bound needed, so a caller that borrows
   and returns is exactly where it started. *)
Lemma bb_set_mk (f : nat -> bv 8) (o j : nat) : bb_set f o (bb_mk f o) j = f j.
Proof.
  rewrite /bb_set.
  destruct (decide ((o <= j)%nat /\ (j < o + 4)%nat)) as [[H1 H2] | _];
    [| reflexivity].
  rewrite (bb_mk_byte f o (j - o)%nat ltac:(lia)). f_equal. lia.
Qed.

(* ---- the list <-> naming-function bridge ---- *)
Lemma bb_list_id (l : list (bv 8)) :
  ((fun j => l !!! j) <$> seq 0 (length l)) = l.
Proof.
  apply list_eq. intros i. rewrite list_lookup_fmap.
  destruct (decide (i < length l)%nat) as [Hi|Hi].
  - assert (Hs : seq 0 (length l) !! i = Some i)
      by (apply lookup_seq; split; [lia | exact Hi]).
    rewrite Hs /=.
    destruct (lookup_lt_is_Some_2 l i Hi) as [x Hx].
    rewrite Hx. by rewrite (list_lookup_total_correct l i x Hx).
  - assert (Hs : seq 0 (length l) !! i = None).
    { apply lookup_ge_None. rewrite length_seq. lia. }
    rewrite Hs /=. symmetry. apply lookup_ge_None. lia.
Qed.

Lemma bb_fmap_len (f : nat -> bv 8) (n : nat) : length (f <$> seq 0 n) = n.
Proof. rewrite length_fmap length_seq. reflexivity. Qed.

(* ---- the two arithmetic side conditions a word window keeps asking for ---- *)
(* 4-ALIGNMENT of an address once it has been reduced to a [Z] literal.  A
   buffer-geometry lemma (write_head's and initlog's [*_align4]) does the
   [pa_add]/[bnode] reduction itself and then lands here. *)
Lemma bb_align_z (x : Z) :
  0 <= x -> x < 18446744073709551616 -> x `mod` 4 = 0 ->
  Z.rem (bv_wrap 64 x) 4 = 0.
Proof.
  intros H0 H1 Hm.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z.
  change (2 ^ 64)%Z with 18446744073709551616%Z.
  rewrite (Z.mod_small x); [| lia].
  rewrite Z.rem_mod_nonneg; [ exact Hm | lia | lia ].
Qed.

(* [uint] at width 32 -- the twin of [RiscvExtras.uint_unsigned], which is
   stated at 64 only.  A word loaded out of a buffer is an [mword 32], and
   every bound on it is stated with [bv_unsigned]. *)
Lemma bb_uint32 (a : mword 32) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ reflexivity | lia ].
Qed.

Section ByteBuf.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.
  (* A byte run is memory like any other: a disk buffer or a page is KT0, a
     STACK buffer rides its hart's regime.  So the family takes the ambient
     tier (StackOwn.v / StackBytes.v's KTR discipline) and every existing KT0
     consumer keeps resolving it to [curktier_default] for free.  The two
     [page_own] lemmas are OUTSIDE this section: [KallocInv.byte_any] is
     KT0-fixed, so they cannot be stated at a variable tier. *)
  Context `{KTR : !CurKtier}.

  (* ------------------------------------------------------------------ *)
  (* Re-anchoring a window.  (InstrBytes has this as a [Local] lemma;    *)
  (* restated here so the copy loops can use it.)                        *)
  (* ------------------------------------------------------------------ *)
  Lemma bb_seq_shift (P : nat -> iProp Σ) (o n : nat) :
    ([∗ list] j ∈ seq o n, P j) ⊣⊢ ([∗ list] j ∈ seq 0 n, P ((o + j)%nat)).
  Proof.
    assert (Hf : seq o n = (Nat.add o) <$> seq 0 n).
    { rewrite fmap_add_seq. by rewrite Nat.add_0_r. }
    rewrite Hf big_sepL_fmap. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* SPLIT / JOIN.  The two-way CUT is the induction step; everything     *)
  (* callers use is the three-way form below it.                          *)
  (* ------------------------------------------------------------------ *)
  (* AT THE CALLER'S FRACTION.  A window is only ever RE-ANCHORED here --
     nothing in the split writes a byte -- so the fraction is a parameter and
     the rule the tree follows applies: a run that is only READ takes the
     caller's dfrac, a run the callee WRITES stays whole.  Every full-ownership
     caller passes [DfracOwn 1] and is unchanged; kexec's path buffer, which
     arrives at [dqpv] because the same .rodata literal is also argv[0], is the
     consumer that made it a parameter. *)
  Local Lemma bb_cut (p : mword 64) (k n : nat) (f : nat -> bv 8) (dq : dfrac) :
    ([∗ list] j ∈ seq 0 (k + n), pa_add p j ↦ₘ{dq} f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 k, pa_add p j ↦ₘ{dq} f j) ∗
       ([∗ list] j ∈ seq 0 n, pa_add (pa_add p k) j ↦ₘ{dq} f (k + j)%nat).
  Proof.
    rewrite seq_app big_sepL_app.
    rewrite (bb_seq_shift (fun j => pa_add p j ↦ₘ{dq} f j)%I (0 + k)%nat n).
    apply bi.sep_proper; [reflexivity |].
    apply big_sepL_proper. intros i j Hj.
    rewrite Nat.add_0_l. rewrite pa_add_add. reflexivity.
  Qed.

  (* PREFIX / CHUNK / SUFFIX, with every window, base and naming function
     spelled out and the total length given as a premise.  This is what a
     page-at-a-time copy loop calls, once per buffer per iteration. *)
  Lemma bb_split3 (p : mword 64) (a b c L : nat) (f : nat -> bv 8) (dq : dfrac) :
    (a + b + c = L)%nat ->
    ([∗ list] j ∈ seq 0 L, pa_add p j ↦ₘ{dq} f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 a, pa_add p j ↦ₘ{dq} f j)
      ∗ ([∗ list] j ∈ seq 0 b, pa_add (pa_add p a) j ↦ₘ{dq} f (a + j)%nat)
      ∗ ([∗ list] j ∈ seq 0 c, pa_add (pa_add (pa_add p a) b) j ↦ₘ{dq} f (a + (b + j))%nat).
  Proof.
    intros <-.
    replace (a + b + c)%nat with (a + (b + c))%nat by lia.
    rewrite (bb_cut p a (b + c) f dq).
    apply bi.sep_proper; [reflexivity |].
    rewrite (bb_cut (pa_add p a) b c (fun j => f (a + j)%nat) dq).
    reflexivity.
  Qed.

  (* the two-way form, as the [c = 0] special case *)
  Lemma bb_split (p : mword 64) (k n : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 (k + n), pa_add p j ↦ₘ f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 k, pa_add p j ↦ₘ f j) ∗
       ([∗ list] j ∈ seq 0 n, pa_add (pa_add p k) j ↦ₘ f (k + j)%nat).
  Proof.
    rewrite (bb_split3 p k n 0 (k + n) f (DfracOwn 1) ltac:(lia)).
    rewrite big_sepL_nil bi.sep_emp. reflexivity.
  Qed.

  (* REGROUPING a buffer into equal-sized RECORDS.  A buffer of [k * n]
     bytes is [k] records of [n] bytes, each re-anchored at its own base
     [p + i*n] and named by the corresponding slice of [f].  This is what a
     caller wants when the region is an ARRAY of structs (the eight
     descriptor-table entries of a virtio queue, the eight avail-ring
     entries) rather than one flat window: the per-record work is then a
     single lemma applied under [big_sepL_mono], with no offset arithmetic
     in the caller.  One direction only -- nobody has needed the join. *)
  Lemma bb_chunk (n : nat) :
    forall (k : nat) (p : mword 64) (f : nat -> bv 8),
    ([∗ list] j ∈ seq 0 (k * n), pa_add p j ↦ₘ f j)
    ⊢ [∗ list] i ∈ seq 0 k,
        [∗ list] j ∈ seq 0 n, pa_add (pa_add p (i * n)) j ↦ₘ f (i * n + j)%nat.
  Proof.
    induction k as [| k IH]; intros p f.
    - iIntros "_". done.
    - replace (S k * n)%nat with (n + k * n)%nat by lia.
      rewrite (bb_split p n (k * n) f).
      iIntros "[Hh Ht]". cbn [seq]. rewrite big_sepL_cons.
      iSplitL "Hh".
      + rewrite Nat.mul_0_l.
        iApply (big_sepL_mono with "Hh"). intros i j Hj.
        apply lookup_seq in Hj as [-> _].
        rewrite !pa_add_add !Nat.add_0_l. reflexivity.
      + rewrite (bb_seq_shift
                   (fun i => [∗ list] j ∈ seq 0 n,
                      pa_add (pa_add p (i * n)) j ↦ₘ f (i * n + j)%nat)%I 1 k).
        iDestruct (IH (pa_add p n) (fun j => f (n + j)%nat) with "Ht") as "Ht".
        iApply (big_sepL_mono with "Ht"). intros i j Hj.
        apply lookup_seq in Hj as [-> _].
        iIntros "H". iApply (big_sepL_mono with "H"). intros i' j' Hj'.
        apply lookup_seq in Hj' as [-> _].
        rewrite !pa_add_add !Nat.add_0_l.
        assert (He : (n + (i * n + i'))%nat = ((1 + i) * n + i')%nat) by lia.
        rewrite He. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* ONE BYTE of a buffer, borrowed and put back.                        *)
  (* ------------------------------------------------------------------ *)
  (* A byte-at-a-time loop (copyinstr's inner loop) reads and writes a
     buffer ONE INDEX at a time, so what it wants is not a chunk split but a
     single-index accessor.  The returning wand takes the NEW naming
     function explicitly, with the obligation that it agrees with the old one
     off the index touched: that keeps the caller in control of the buffer's
     contents -- which is what a [bb_join3]-style existential would throw
     away, and copyinstr's postcondition (a NUL-TERMINATED string, see
     [bb_cstr]) needs the values, not just the ownership.  Reading is the
     [g := f] instance, so this is one lemma and not two. *)
  Lemma bb_byte_acc (p : mword 64) (n d : nat) (f : nat -> bv 8) (dq : dfrac) :
    (d < n)%nat ->
    ([∗ list] j ∈ seq 0 n, pa_add p j ↦ₘ{dq} f j) ⊢
    pa_add p d ↦ₘ{dq} f d ∗
    (∀ g : nat -> bv 8,
       ⌜forall j, (j < n)%nat -> j <> d -> g j = f j⌝ -∗
       pa_add p d ↦ₘ{dq} g d -∗
       [∗ list] j ∈ seq 0 n, pa_add p j ↦ₘ{dq} g j).
  Proof.
    intro Hd.
    assert (Hlk : seq 0 n !! d = Some d)
      by (apply lookup_seq; split; [lia | exact Hd]).
    rewrite (big_sepL_delete (fun _ y => (pa_add p y ↦ₘ{dq} f y)%I) (seq 0 n) d d Hlk).
    iIntros "[Hd Hrest]". iFrame "Hd".
    iIntros (g) "%Hag Hd".
    rewrite (big_sepL_delete (fun _ y => (pa_add p y ↦ₘ{dq} g y)%I) (seq 0 n) d d Hlk).
    iSplitL "Hd"; [iExact "Hd" |].
    iApply (big_sepL_mono with "Hrest"). intros i j Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    destruct (decide (i = d)) as [-> | Hne]; [reflexivity |].
    rewrite Hag; [reflexivity | lia | exact Hne].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* REBRANDING the naming function.                                     *)
  (* ------------------------------------------------------------------ *)
  Lemma bb_ext (p : mword 64) (n : nat) (f g : nat -> bv 8) :
    (forall j, (j < n)%nat -> f j = g j) ->
    ([∗ list] j ∈ seq 0 n, pa_add p j ↦ₘ f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 n, pa_add p j ↦ₘ g j).
  Proof.
    intros Hfg. apply big_sepL_proper. intros i j Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Hfg; [reflexivity | lia].
  Qed.

  (* the inverse of [bb_split3]: three separately-named windows become one
     buffer named by one function -- the shape a caller's postcondition
     wants.  The three pieces need NOT be named by restrictions of a common
     function (memmove hands the middle one back named by the SOURCE's
     naming), which is exactly why the result is an existential. *)
  (* THE NAMED JOIN.  [bb_join3]'s existential is the right shape when the
     caller has nothing to say about the bytes; a caller that must state
     what the buffer HOLDS -- copyin's promise that its destination is the
     process's memory -- needs the naming function to survive the join, so
     it supplies it and discharges three pointwise equations. *)
  Lemma bb_join3_fn (p : mword 64) (a b c L : nat) (f g h u : nat -> bv 8) :
    (a + b + c = L)%nat ->
    (forall j, (j < a)%nat -> u j = f j) ->
    (forall i, (i < b)%nat -> u (a + i)%nat = g i) ->
    (forall i, (i < c)%nat -> u (a + (b + i))%nat = h i) ->
    ([∗ list] j ∈ seq 0 a, pa_add p j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 b, pa_add (pa_add p a) j ↦ₘ g j) -∗
    ([∗ list] j ∈ seq 0 c, pa_add (pa_add (pa_add p a) b) j ↦ₘ h j) -∗
    [∗ list] j ∈ seq 0 L, pa_add p j ↦ₘ u j.
  Proof.
    intros <- Hf Hg Hh. iIntros "HA HB HC".
    rewrite (bb_split3 p a b c (a + b + c) u (DfracOwn 1) ltac:(lia)).
    iSplitL "HA"; [| iSplitL "HB"].
    - iApply (big_sepL_mono with "HA"). intros i j Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l Hf; [reflexivity | lia].
    - iApply (big_sepL_mono with "HB"). intros i j Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l Hg; [reflexivity | lia].
    - iApply (big_sepL_mono with "HC"). intros i j Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l Hh; [reflexivity | lia].
  Qed.

  Lemma bb_join3 (p : mword 64) (a b c L : nat) (f g h : nat -> bv 8) :
    (a + b + c = L)%nat ->
    ([∗ list] j ∈ seq 0 a, pa_add p j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 b, pa_add (pa_add p a) j ↦ₘ g j) -∗
    ([∗ list] j ∈ seq 0 c, pa_add (pa_add (pa_add p a) b) j ↦ₘ h j) -∗
    ∃ u : nat -> bv 8, [∗ list] j ∈ seq 0 L, pa_add p j ↦ₘ u j.
  Proof.
    intros <-. iIntros "HA HB HC".
    iExists (fun j => if decide (j < a)%nat then f j
                      else if decide (j < a + b)%nat then g (j - a)%nat
                      else h (j - a - b)%nat).
    rewrite (bb_split3 p a b c (a + b + c) _ (DfracOwn 1) ltac:(lia)).
    iSplitL "HA"; [| iSplitL "HB"].
    - iApply (big_sepL_mono with "HA"). intros i j Hj.
      apply lookup_seq in Hj as [Heq Hlt].
      rewrite decide_True; [reflexivity | lia].
    - iApply (big_sepL_mono with "HB"). intros i j Hj.
      apply lookup_seq in Hj as [Heq Hlt].
      rewrite decide_False; [| lia]. rewrite decide_True; [| lia].
      replace (a + j - a)%nat with j by lia. reflexivity.
    - iApply (big_sepL_mono with "HC"). intros i j Hj.
      apply lookup_seq in Hj as [Heq Hlt].
      rewrite decide_False; [| lia]. rewrite decide_False; [| lia].
      replace (a + (b + j) - a - b)%nat with j by lia. reflexivity.
  Qed.

  (* the two-way form, again as the [c = 0] special case *)
  Lemma bb_join (p : mword 64) (k n : nat) (f g : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 k, pa_add p j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 n, pa_add (pa_add p k) j ↦ₘ g j) -∗
    ∃ h : nat -> bv 8, [∗ list] j ∈ seq 0 (k + n), pa_add p j ↦ₘ h j.
  Proof.
    iIntros "Hlo Hhi".
    iApply (bb_join3 p k n 0 (k + n) f g (fun _ => bv_0 8) ltac:(lia)
              with "Hlo Hhi []").
    done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* NAMING an anonymous region, and forgetting the names again.         *)
  (* ------------------------------------------------------------------ *)
  Lemma bb_named_any (p : mword 64) (n : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 n, pa_add p j ↦ₘ f j)
    ⊢ [∗ list] j ∈ seq 0 n, ∃ b : bv 8, pa_add p j ↦ₘ b.
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (i j _) "Hb". iExists (f j). iExact "Hb".
  Qed.

  (* CHOICE over a [seq] window: a window of existentials is an existential
     FUNCTION over the window.  (This is also what kvmmake needs to name the
     bytes of the freshly-kalloc'ed root page before memset-ing it.) *)
  Lemma bb_choose (n : nat) :
    forall (start : nat) (P : nat -> bv 8 -> iProp Σ),
      ([∗ list] k ∈ seq start n, ∃ b : bv 8, P k b)
      ⊢ ∃ f : nat -> bv 8, [∗ list] k ∈ seq start n, P k (f k).
  Proof.
    induction n as [| n IH]; intros start P.
    - iIntros "_". iExists (fun _ => bv_0 8). done.
    - cbn [seq]. rewrite big_sepL_cons.
      iIntros "[Hh Ht]". iDestruct "Hh" as (b) "Hh".
      iDestruct (IH (S start) P with "Ht") as (f) "Ht".
      iExists (fun k => if Nat.eq_dec k start then b else f k).
      rewrite big_sepL_cons. iSplitL "Hh".
      + destruct (Nat.eq_dec start start) as [_ | Hne]; [iExact "Hh" | done].
      + iApply (big_sepL_impl with "Ht"). iIntros "!>" (k y Hy) "H".
        destruct (Nat.eq_dec y start) as [He | _].
        * exfalso. apply elem_of_list_lookup_2 in Hy. apply elem_of_seq in Hy. lia.
        * iExact "H".
  Qed.

  Lemma bb_any_named (p : mword 64) (n : nat) :
    ([∗ list] j ∈ seq 0 n, ∃ b : bv 8, pa_add p j ↦ₘ b)
    ⊢ ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 n, pa_add p j ↦ₘ f j.
  Proof. exact (bb_choose n 0 (fun k b => pa_add p k ↦ₘ b)%I). Qed.


  (* ------------------------------------------------------------------ *)
  (* A [uint64 *] AS A BUFFER.                                          *)
  (* ------------------------------------------------------------------ *)
  (* A [↦₈] cell IS an 8-byte buffer plus its alignment fact, so a copy
     INTO a caller's word-sized out-parameter (fetchaddr's [*ip]) borrows
     it as one and gets it back holding SOME value -- which is all a
     contents-existential copy postcondition can say.

     ONE accessor, not two lemmas: the alignment is what the rebuild needs
     and the eight bytes no longer carry it, so it has to be captured
     before the split (the [word_pointsto_split4] discipline).  The
     returned value is existential because the copy names its bytes by an
     arbitrary function; [nth_byte_assemble_len] is what turns eight
     arbitrary bytes back into a word. *)
  Lemma bb_word_acc (a : mword 64) (w : mword 64) :
    a ↦₈ w -∗
    ([∗ list] j ∈ seq 0 8, pa_add a j ↦ₘ nth_byte w j) ∗
    (∀ f : nat -> bv 8,
       ([∗ list] j ∈ seq 0 8, pa_add a j ↦ₘ f j) -∗ ∃ w' : mword 64, a ↦₈ w').
  Proof.
    iIntros "Hw".
    iDestruct (ctx_word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (ctx_word_pointsto_bytes with "Hw") as "$".
    iIntros (f) "Hf".
    set (bs := [f 0%nat; f 1%nat; f 2%nat; f 3%nat;
                f 4%nat; f 5%nat; f 6%nat; f 7%nat]).
    iExists (Z_to_bv 64 (assemble_bytes bs) : mword 64).
    iApply (ctx_word_pointsto_intro _ _ _ _ Hal).
    iApply (big_sepL_mono with "Hf"). intros i j Hj.
    apply lookup_seq in Hj as [-> Hlt].
    rewrite (nth_byte_assemble_len 64 bs i ltac:(cbn; lia) ltac:(cbn; lia)).
    assert (Hbs : bs !!! i = f i).
    { unfold bs.
      destruct i as [|[|[|[|[|[|[|[|i']]]]]]]]; try reflexivity. cbn in Hlt. lia. }
    rewrite Hbs. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* ONE 4-BYTE CELL of a buffer, borrowed and put back.                 *)
  (* ------------------------------------------------------------------ *)
  (* [bb_bytes] names the [seq]-indexed, function-named window itself, so a
     resource that carries a byte LIST (a [buf_own]-style block) can be
     traded for it once ([bb_bytes_of_list]) and materialised back at the
     end ([bb_bytes_to_list]) instead of being re-indexed at every store.

     [bb_word4_acc] is then the word-sized analogue of [bb_byte_acc]: the
     window splits at [o] ([bb_split3]), the middle four bytes become a
     [↦₄] cell holding [bb_mk f o], and the returning wand takes the new
     value EXPLICITLY -- the naming function becomes [bb_set f o w], which
     is what keeps the caller in control of the contents.  Reading is the
     [w := bb_mk f o] instance ([bb_set_mk] then says the window is
     unchanged), so this is one lemma and not two.  The alignment fact is a
     premise rather than something derived: the four bytes do not carry it
     and the caller's geometry lemma is where it belongs. *)
  Definition bb_bytes (a : mword 64) (n : nat) (f : nat -> bv 8) : iProp Σ :=
    ([∗ list] j ∈ seq 0 n, pa_add a j ↦ₘ f j)%I.

  Lemma bb_bytes_of_list (a : mword 64) (l : list (bv 8)) :
    ([∗ list] j ↦ x ∈ l, pa_add a j ↦ₘ x)
    ⊣⊢ bb_bytes a (length l) (fun j => l !!! j).
  Proof.
    rewrite /bb_bytes.
    rewrite -{1}(bb_list_id l) big_sepL_fmap.
    apply big_sepL_proper. intros i jj Hj.
    apply lookup_seq in Hj as [-> _]. reflexivity.
  Qed.

  Lemma bb_bytes_to_list (a : mword 64) (n : nat) (f : nat -> bv 8) :
    bb_bytes a n f ⊣⊢ ([∗ list] j ↦ x ∈ (f <$> seq 0 n), pa_add a j ↦ₘ x).
  Proof.
    rewrite /bb_bytes big_sepL_fmap.
    apply big_sepL_proper. intros i jj Hj.
    apply lookup_seq in Hj as [-> _]. reflexivity.
  Qed.

  Lemma bb_word4_acc (a : mword 64) (n o r : nat) (f : nat -> bv 8) :
    (o + 4 + r)%nat = n ->
    is_aligned_paddr (Physaddr (pa_add a o)) 4 = true ->
    bb_bytes a n f -∗
    pa_add a o ↦₄ bb_mk f o ∗
    (∀ w : mword 32,
       pa_add a o ↦₄ w -∗ bb_bytes a n (bb_set f o w)).
  Proof.
    intros Hn Hal.
    rewrite /bb_bytes (bb_split3 a o 4 r n f (DfracOwn 1) Hn).
    iIntros "(Hpre & Hmid & Hsuf)".
    iSplitL "Hmid".
    { iApply (word4_pointsto_intro _ _ _ Hal).
      iApply (big_sepL_mono with "Hmid"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (bb_mk_byte f o i Hlt). reflexivity. }
    iIntros (w) "Hw".
    rewrite (bb_split3 a o 4 r n (bb_set f o w) (DfracOwn 1) Hn).
    iDestruct (word4_pointsto_bytes with "Hw") as "Hw".
    iSplitL "Hpre".
    { iApply (big_sepL_mono with "Hpre"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (bb_set_out f o w i ltac:(left; lia)). reflexivity. }
    iSplitL "Hw".
    { iApply (big_sepL_mono with "Hw"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (bb_set_in f o w (o + i)%nat ltac:(lia) ltac:(lia)).
      replace (o + i - o)%nat with i by lia. reflexivity. }
    { iApply (big_sepL_mono with "Hsuf"). intros i jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (bb_set_out f o w (o + (4 + i))%nat ltac:(right; lia)). reflexivity. }
  Qed.

End ByteBuf.

(* The two instances the copy loops actually use: a page, and a window inside
   a page.  KT0 ONLY, and outside the section above for that reason:
   [KallocInv.page_own] is a run of [byte_any], which is a physical,
   identity-mapped page and carries no tier index. *)
Section ByteBufPage.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.

  Lemma bb_page_named (q : mword 64) :
    page_own q ⊢ ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 4096, pa_add q j ↦ₘ f j.
  Proof. rewrite /page_own /byte_any. apply bb_any_named. Qed.

  Lemma bb_page_of_named (q : mword 64) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 4096, pa_add q j ↦ₘ f j) ⊢ page_own q.
  Proof. rewrite /page_own /byte_any. apply bb_named_any. Qed.
End ByteBufPage.

