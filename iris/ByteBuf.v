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

   Nothing here mentions page tables, so it is reusable by copyinstr and by
   any future byte-range code. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import KallocInv.
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

Section ByteBuf.
  Context `{!riscvGS Σ}.

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
  Local Lemma bb_cut (p : mword 64) (k n : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 (k + n), pa_add p j ↦ₘ f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 k, pa_add p j ↦ₘ f j) ∗
       ([∗ list] j ∈ seq 0 n, pa_add (pa_add p k) j ↦ₘ f (k + j)%nat).
  Proof.
    rewrite seq_app big_sepL_app.
    rewrite (bb_seq_shift (fun j => pa_add p j ↦ₘ f j)%I (0 + k)%nat n).
    apply bi.sep_proper; [reflexivity |].
    apply big_sepL_proper. intros i j Hj.
    rewrite Nat.add_0_l. rewrite pa_add_add. reflexivity.
  Qed.

  (* PREFIX / CHUNK / SUFFIX, with every window, base and naming function
     spelled out and the total length given as a premise.  This is what a
     page-at-a-time copy loop calls, once per buffer per iteration. *)
  Lemma bb_split3 (p : mword 64) (a b c L : nat) (f : nat -> bv 8) :
    (a + b + c = L)%nat ->
    ([∗ list] j ∈ seq 0 L, pa_add p j ↦ₘ f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 a, pa_add p j ↦ₘ f j)
      ∗ ([∗ list] j ∈ seq 0 b, pa_add (pa_add p a) j ↦ₘ f (a + j)%nat)
      ∗ ([∗ list] j ∈ seq 0 c, pa_add (pa_add (pa_add p a) b) j ↦ₘ f (a + (b + j))%nat).
  Proof.
    intros <-.
    replace (a + b + c)%nat with (a + (b + c))%nat by lia.
    rewrite (bb_cut p a (b + c) f).
    apply bi.sep_proper; [reflexivity |].
    rewrite (bb_cut (pa_add p a) b c (fun j => f (a + j)%nat)).
    reflexivity.
  Qed.

  (* the two-way form, as the [c = 0] special case *)
  Lemma bb_split (p : mword 64) (k n : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 (k + n), pa_add p j ↦ₘ f j)
    ⊣⊢ ([∗ list] j ∈ seq 0 k, pa_add p j ↦ₘ f j) ∗
       ([∗ list] j ∈ seq 0 n, pa_add (pa_add p k) j ↦ₘ f (k + j)%nat).
  Proof.
    rewrite (bb_split3 p k n 0 (k + n) f ltac:(lia)).
    rewrite big_sepL_nil bi.sep_emp. reflexivity.
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
    rewrite (bb_split3 p a b c (a + b + c) _ ltac:(lia)).
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
    ⊢ [∗ list] j ∈ seq 0 n, byte_any (pa_add p j).
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iIntros "!>" (i j _) "Hb". rewrite /byte_any. iExists (f j). iExact "Hb".
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
    ([∗ list] j ∈ seq 0 n, byte_any (pa_add p j))
    ⊢ ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 n, pa_add p j ↦ₘ f j.
  Proof. rewrite /byte_any. exact (bb_choose n 0 (fun k b => pa_add p k ↦ₘ b)%I). Qed.

  (* the two instances the copy loops actually use: a page, and a window
     inside a page *)
  Lemma bb_page_named (q : mword 64) :
    page_own q ⊢ ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 4096, pa_add q j ↦ₘ f j.
  Proof. rewrite /page_own. apply bb_any_named. Qed.

  Lemma bb_page_of_named (q : mword 64) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 4096, pa_add q j ↦ₘ f j) ⊢ page_own q.
  Proof. rewrite /page_own. apply bb_named_any. Qed.

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
    iDestruct (word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (word_pointsto_bytes with "Hw") as "$".
    iIntros (f) "Hf".
    set (bs := [f 0%nat; f 1%nat; f 2%nat; f 3%nat;
                f 4%nat; f 5%nat; f 6%nat; f 7%nat]).
    iExists (Z_to_bv 64 (assemble_bytes bs) : mword 64).
    iApply (word_pointsto_intro _ _ _ Hal).
    iApply (big_sepL_mono with "Hf"). intros i j Hj.
    apply lookup_seq in Hj as [-> Hlt].
    rewrite (nth_byte_assemble_len 64 bs i ltac:(cbn; lia) ltac:(cbn; lia)).
    assert (Hbs : bs !!! i = f i).
    { unfold bs.
      destruct i as [|[|[|[|[|[|[|[|i']]]]]]]]; try reflexivity. cbn in Hlt. lia. }
    rewrite Hbs. reflexivity.
  Qed.

End ByteBuf.
