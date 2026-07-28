(* ByteBuf.v -- the byte-buffer algebra the copy loops run on.

   A "buffer" here is exactly the shape memmove's contract (SpecMemmove.v)
   consumes and produces:

       [∗ list] j ∈ seq 0 n, pa_add p j ↦ₘ f j

   -- [n] consecutive bytes from [p], with their values named by a function.
   copyin / copyout walk such a buffer one page-chunk at a time, so they need
   three things this file provides, all of them independent of what is being
   copied:

     SPLIT / JOIN at an offset ([bb_split]), so the next chunk can be handed
       to memmove re-anchored at its own base;
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
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KallocInv.
Local Open Scope Z_scope.

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
  (* SPLIT / JOIN.                                                       *)
  (* ------------------------------------------------------------------ *)
  Lemma bb_split (p : mword 64) (k n : nat) (f : nat -> bv 8) :
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

  (* the two halves, named separately, become one buffer named by one
     function -- the shape a caller's postcondition wants *)
  Lemma bb_join (p : mword 64) (k n : nat) (f g : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 k, pa_add p j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 n, pa_add (pa_add p k) j ↦ₘ g j) -∗
    ∃ h : nat -> bv 8, [∗ list] j ∈ seq 0 (k + n), pa_add p j ↦ₘ h j.
  Proof.
    iIntros "Hlo Hhi".
    iExists (fun j => if decide (j < k)%nat then f j else g (j - k)%nat).
    rewrite bb_split. iSplitL "Hlo".
    - iApply (big_sepL_mono with "Hlo"). intros i j Hj.
      apply lookup_seq in Hj as [Heq Hlt].
      rewrite decide_True; [reflexivity | lia].
    - iApply (big_sepL_mono with "Hhi"). intros i j Hj.
      apply lookup_seq in Hj as [Heq Hlt].
      rewrite decide_False; [| lia].
      replace (k + j - k)%nat with j by lia. reflexivity.
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
     FUNCTION over the window.  (ProofKvmmake.v has this as a local
     [kmk_bytes_choose]; that copy can be retired in favour of this one.) *)
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

End ByteBuf.
