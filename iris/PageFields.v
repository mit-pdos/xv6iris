(* PageFields.v -- carving a kalloc'd page into typed struct fields.

   [kalloc] hands back [page_own p]: 4096 anonymous bytes.  Every kernel
   object built on a page ([struct pipe], a page table, a kstack) has to turn
   that into the FIELD cells its code actually loads and stores -- a [↦₄] at
   one offset, a [↦₈] at another, a byte window in between -- and hand the
   whole page back when it is freed.  This file is that bridge, once:

     bwin_split   -- chop a byte window in two
     bwin_rebase  -- a window at offset [o] of [p] is a window at offset 0
                     of [pa_add p o] (so every field lemma is stated at 0)
     bytes_word4  -- 4 aligned anonymous bytes ARE some [↦₄] cell
     bytes_word8  -- 8 aligned anonymous bytes ARE some [↦₈] cell
     page_off_aligned -- the alignment side condition, from [page_valid]
                     plus divisibility of the offset

   Only the forward direction is here (page -> fields), because that is what
   an object's constructor needs.  The converse (fields -> page, for kfree)
   is the same three lemmas run backwards -- [bwin_split] and [bwin_rebase]
   are already equivalences; the missing piece is [word{4,8}_pointsto_bytes],
   which RiscvPtsto already provides.

   The non-wrapping add ([pa_add_unsigned]) is stated here rather than reused
   because the two existing copies ([UserBits.uint_add_vec_int_small],
   [Pt4kWalk.pt_add_vec_int_small]) both sit in the user-mode / page-table
   stacks; the three should be folded into RiscvExtras next to [avi0]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import InstrBytes.
Require Import KallocInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvExtras.
Require Import TsoCtx.
Require TsoCtxShim.   (* [bytes_word4]: ↦₄ has not flipped yet *)
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Address arithmetic  ([pa_add_add] lives in InstrBytes.v)           *)
(* ------------------------------------------------------------------ *)


Lemma pa_add_unsigned (a : mword 64) (j : Z) :
  0 <= j ->
  bv_unsigned a + j < 18446744073709551616 ->
  bv_unsigned (add_vec_int a j) = bv_unsigned a + j.
Proof.
  intros Hj Hfit.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hjv : bv_unsigned (mword_of_int j : mword 64) = j).
  { unfold mword_of_int, Values.to_word, get_word.
    cbn.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus. cbn.
    pose proof (bv_unsigned_in_range _ a). lia. }
  rewrite Hjv.
  apply bv_wrap_small.
  unfold bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64)) with 18446744073709551616 in Hr.
  lia.
Qed.

(* The arithmetic, over plain [Z] variables: [lia] returns "Cannot find
   witness" under the [bitvector.tactics] zify hook as soon as the goal (or,
   here, the context) mentions [bv_unsigned], so the reasoning is packaged
   away from the bitvectors and fed their values -- the recipe in
   claude-notes/durable-notes.md. *)
Lemma page_off_arith (up oz w : Z) :
  0 <= up -> up < 2281701376 -> up mod 4096 = 0 ->
  0 <= oz -> oz < 4096 -> 0 < w -> (w | 4096) -> (w | oz) ->
  up + oz < 18446744073709551616 /\ Z.rem (up + oz) w = 0.
Proof.
  intros Hnn Hhi Hal Honn Ho Hwpos Hw4096 Hwo.
  split; [lia|].
  assert (Hrem : Z.rem (up + oz) w = (up + oz) mod w)
    by (apply Z.rem_mod_nonneg; lia).
  rewrite Hrem. apply Z.mod_divide; [lia|].
  apply Z.divide_add_r; [| exact Hwo].
  apply Z.mod_divide in Hal; [| lia].
  exact (Z.divide_trans w 4096 up Hw4096 Hal).
Qed.

(* the alignment side condition every field cell needs: a page is 4096-aligned,
   so an offset divisible by the access width lands on an aligned address. *)
Lemma page_off_aligned (p : mword 64) (o : nat) (w : Z) :
  page_valid p -> (o < 4096)%nat -> 0 < w -> (w | 4096) -> (w | Z.of_nat o) ->
  is_aligned_paddr (Physaddr (pa_add p o)) w = true.
Proof.
  intros [Hal [Hlo Hhi]] Ho Hwpos Hw4096 Hwo.
  pose proof (bv_unsigned_in_range 64 p) as [Hnn _].
  unfold page_aligned, PGSIZE in Hal.
  rewrite uint_unsigned in Hal, Hhi.
  assert (Hhi' : bv_unsigned p < 2281701376) by (unfold kmem_hi in Hhi; exact Hhi).
  assert (Honn : 0 <= Z.of_nat o) by apply Nat2Z.is_nonneg.
  assert (Holt : Z.of_nat o < 4096) by (apply (Nat2Z.inj_lt o 4096) in Ho; exact Ho).
  destruct (page_off_arith (bv_unsigned p) (Z.of_nat o) w
              Hnn Hhi' Hal Honn Holt Hwpos Hw4096 Hwo) as [Hfit Hrem].
  unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite uint_unsigned.
  change (pa_add p o) with (add_vec_int p (Z.of_nat o)).
  rewrite (pa_add_unsigned p (Z.of_nat o) Honn Hfit).
  exact Hrem.
Qed.

(* the 32-bit instance of [RiscvModelBytes.nth_byte_assemble_len]. *)
Lemma nth_byte_assemble4 (bs : list (bv 8)) (j : nat) :
  length bs = 4%nat -> (j < 4)%nat ->
  nth_byte (Z_to_bv 32 (assemble_bytes bs) : mword 32) j = bs !!! j.
Proof. intros Hlen Hj. apply nth_byte_assemble_len; lia. Qed.

Section PageFields.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.

  (* ---- chopping and re-basing byte windows ---- *)

  Lemma bwin_split (p : mword 64) (o a b : nat) :
    ([∗ list] j ∈ seq o (a + b), byte_any (pa_add p j)) ⊣⊢
    ([∗ list] j ∈ seq o a, byte_any (pa_add p j)) ∗
    ([∗ list] j ∈ seq (o + a) b, byte_any (pa_add p j)).
  Proof. by rewrite seq_app big_sepL_app. Qed.

  Lemma bwin_rebase (p : mword 64) (o n : nat) :
    ([∗ list] j ∈ seq o n, byte_any (pa_add p j)) ⊣⊢
    ([∗ list] j ∈ seq 0 n, byte_any (pa_add (pa_add p o) j)).
  Proof.
    rewrite -{1}(Nat.add_0_r o) -fmap_add_seq big_sepL_fmap.
    apply big_sepL_proper. intros k j _. by rewrite pa_add_add.
  Qed.

  (* a window of anonymous bytes IS some concrete byte list: the shape a
     content-tracking buffer (a pipe's [data], a page-table page) wants. *)
  Lemma bwin_bytes_list (a : mword 64) (n : nat) :
    ([∗ list] j ∈ seq 0 n, byte_any (pa_add a j)) ⊢
    ∃ bs : list (bv 8), ⌜length bs = n⌝ ∗ ([∗ list] j ↦ b ∈ bs, pa_add a j ↦ₘ b).
  Proof.
    induction n as [|n IH].
    - iIntros "_". iExists []. iSplit; done.
    - rewrite seq_S big_sepL_app.
      iIntros "[Hpre Hlast]".
      iDestruct (IH with "Hpre") as (bs) "[%Hlen Hbs]".
      rewrite big_sepL_singleton.
      (* [byte_any] is Global TC-opaque since the flip; open it for the
         ∃-destruct *)
      iEval (rewrite /byte_any) in "Hlast".
      iDestruct "Hlast" as (b) "Hb".
      iExists (bs ++ [b])%list.
      iSplit; [iPureIntro; rewrite length_app Hlen; simpl; lia|].
      rewrite big_sepL_app big_sepL_singleton Hlen.
      iFrame "Hbs".
      replace (n + 0)%nat with (0 + n)%nat by lia.
      iExact "Hb".
  Qed.

  (* ---- anonymous bytes ARE a word cell ---- *)

  Lemma bytes_word4 (a : mword 64) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    ([∗ list] j ∈ seq 0 4, byte_any (pa_add a j)) ⊢ ∃ w : mword 32, a ↦₄ w.
  Proof.
    intro Hal. rewrite /byte_any.
    change (seq 0 4) with [0;1;2;3]%nat.
    iIntros "(H0 & H1 & H2 & H3 & _)".
    iDestruct "H0" as (b0) "H0". iDestruct "H1" as (b1) "H1".
    iDestruct "H2" as (b2) "H2". iDestruct "H3" as (b3) "H3".
    (* [↦₄] has not flipped yet (M1 stage 2), so the ctx bytes cross the
       seam here; these four lines die when the 4-byte tower flips. *)
    iDestruct (TsoCtxShim.ctx_pointsto_to_mem with "H0") as "H0".
    iDestruct (TsoCtxShim.ctx_pointsto_to_mem with "H1") as "H1".
    iDestruct (TsoCtxShim.ctx_pointsto_to_mem with "H2") as "H2".
    iDestruct (TsoCtxShim.ctx_pointsto_to_mem with "H3") as "H3".
    set (bs := [b0;b1;b2;b3]).
    set (w := Z_to_bv 32 (assemble_bytes bs) : mword 32).
    iExists w.
    rewrite /word4_pointsto.
    iSplitR; [iPureIntro; exact Hal|].
    assert (E0 : nth_byte w 0%nat = b0) by (subst w bs; apply nth_byte_assemble4; [reflexivity | lia]).
    assert (E1 : nth_byte w 1%nat = b1) by (subst w bs; apply nth_byte_assemble4; [reflexivity | lia]).
    assert (E2 : nth_byte w 2%nat = b2) by (subst w bs; apply nth_byte_assemble4; [reflexivity | lia]).
    assert (E3 : nth_byte w 3%nat = b3) by (subst w bs; apply nth_byte_assemble4; [reflexivity | lia]).
    change (seq 0 4) with [0;1;2;3]%nat. simpl.
    rewrite E0 E1 E2 E3. iFrame.
  Qed.

  Lemma bytes_word8 (a : mword 64) :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, byte_any (pa_add a j)) ⊢ ∃ w : mword 64, a ↦₈ w.
  Proof.
    intro Hal. rewrite /byte_any.
    change (seq 0 8) with [0;1;2;3;4;5;6;7]%nat.
    iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _)".
    iDestruct "H0" as (b0) "H0". iDestruct "H1" as (b1) "H1".
    iDestruct "H2" as (b2) "H2". iDestruct "H3" as (b3) "H3".
    iDestruct "H4" as (b4) "H4". iDestruct "H5" as (b5) "H5".
    iDestruct "H6" as (b6) "H6". iDestruct "H7" as (b7) "H7".
    set (bs := [b0;b1;b2;b3;b4;b5;b6;b7]).
    set (w := Z_to_bv 64 (assemble_bytes bs) : mword 64).
    iExists w.
    rewrite /ctx_word_pointsto.
    iSplitR; [iPureIntro; exact Hal|].
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

  (* the two field forms in one step, at a page offset: the caller supplies the
     offset's divisibility and gets the cell. *)
  Lemma page_field4 (p : mword 64) (o : nat) :
    page_valid p -> (o + 4 <= 4096)%nat -> (4 | Z.of_nat o) ->
    ([∗ list] j ∈ seq o 4, byte_any (pa_add p j)) ⊢ ∃ w : mword 32, pa_add p o ↦₄ w.
  Proof.
    intros Hpv Ho Hdvd. rewrite bwin_rebase.
    apply bytes_word4. apply (page_off_aligned p o 4 Hpv ltac:(lia) ltac:(lia));
      [ exists 1024; reflexivity | exact Hdvd ].
  Qed.

  Lemma page_field8 (p : mword 64) (o : nat) :
    page_valid p -> (o + 8 <= 4096)%nat -> (8 | Z.of_nat o) ->
    ([∗ list] j ∈ seq o 8, byte_any (pa_add p j)) ⊢ ∃ w : mword 64, pa_add p o ↦₈ w.
  Proof.
    intros Hpv Ho Hdvd. rewrite bwin_rebase.
    apply bytes_word8. apply (page_off_aligned p o 8 Hpv ltac:(lia) ltac:(lia));
      [ exists 512; reflexivity | exact Hdvd ].
  Qed.

  (* ---- a RUN of word cells out of a page's prefix ----

     One field is [page_field8]; an ARRAY of them (the 36 [struct trapframe]
     words allocproc carves out of a fresh page) is this.  Contents are
     existential, which is all a page kalloc just handed over can say; the
     length is the caller's [n].  Stated over [pa_add p (8 * i)] -- the same
     form [ProcInv.a_tf_word] is defined at -- so a consumer needs no address
     rewriting. *)
  Lemma page_words8 (p : mword 64) (n : nat) :
    page_valid p -> (8 * n <= 4096)%nat ->
    ([∗ list] j ∈ seq 0 (8 * n), byte_any (pa_add p j)) ⊢
    ∃ ws : list (mword 64), ⌜length ws = n⌝ ∗
      ([∗ list] i ↦ w ∈ ws, pa_add p (8 * i)%nat ↦₈ w).
  Proof.
    intro Hpv. induction n as [|n IH]; intro Hn.
    - iIntros "_". iExists []. by iSplit.
    - replace (8 * S n)%nat with (8 * n + 8)%nat by lia.
      rewrite (bwin_split p 0 (8 * n) 8).
      iIntros "[Hpre Hlast]".
      iDestruct (IH ltac:(lia) with "Hpre") as (ws) "[%Hlen Hws]".
      rewrite Nat.add_0_l.
      iDestruct (page_field8 p (8 * n)%nat Hpv ltac:(lia)
                   ltac:(exists (Z.of_nat n); lia) with "Hlast") as (w) "Hw".
      iExists (ws ++ [w])%list.
      iSplit; [iPureIntro; rewrite length_app Hlen /=; lia|].
      rewrite big_sepL_app big_sepL_singleton Hlen. iFrame "Hws".
      rewrite Nat.add_0_r. iExact "Hw".
  Qed.

  (* ---- and back: a word cell IS anonymous bytes ----

     The converse direction, for reclaiming a page: an object being torn down
     hands its typed fields back and they have to become the 4096 anonymous
     bytes kfree wants.  [bwin_split] / [bwin_rebase] above are already
     equivalences, so only the leaves need a backward twin. *)
  Lemma word4_bwin (a : mword 64) (w : mword 32) :
    a ↦₄ w ⊢ [∗ list] j ∈ seq 0 4, byte_any (pa_add a j).
  Proof.
    rewrite word4_pointsto_bytes. apply big_sepL_mono.
    intros k j _. iIntros "H". rewrite /byte_any. iExists (nth_byte w j).
    iApply (TsoCtxShim.ctx_pointsto_of_mem with "H").
  Qed.

  Lemma word8_bwin (a : mword 64) (w : mword 64) :
    a ↦₈ w ⊢ [∗ list] j ∈ seq 0 8, byte_any (pa_add a j).
  Proof.
    rewrite ctx_word_pointsto_bytes. apply big_sepL_mono.
    intros k j _. iIntros "H". by iExists (nth_byte w j).
  Qed.

  Lemma page_field4_back (p : mword 64) (o : nat) (w : mword 32) :
    pa_add p o ↦₄ w ⊢ [∗ list] j ∈ seq o 4, byte_any (pa_add p j).
  Proof. rewrite bwin_rebase. apply word4_bwin. Qed.

  Lemma page_field8_back (p : mword 64) (o : nat) (w : mword 64) :
    pa_add p o ↦₈ w ⊢ [∗ list] j ∈ seq o 8, byte_any (pa_add p j).
  Proof. rewrite bwin_rebase. apply word8_bwin. Qed.

  (* the converse of [page_words8]: a run of word cells forgets its contents
     and becomes a window again.  This is the direction an object being TORN
     DOWN needs -- freeproc handing a trapframe page back to kfree is the
     first consumer. *)
  Lemma page_words8_back (p : mword 64) (ws : list (mword 64)) :
    ([∗ list] i ↦ w ∈ ws, pa_add p (8 * i)%nat ↦₈ w) ⊢
    [∗ list] j ∈ seq 0 (8 * length ws), byte_any (pa_add p j).
  Proof.
    induction ws as [|w ws IH] using rev_ind; [ by iIntros "_" | ].
    (* NO [/=] here: [simpl] would unfold the [8 * _] and the [bwin_split]
       instance below would then match nothing. *)
    replace (8 * length (ws ++ [w]))%nat with (8 * length ws + 8)%nat
      by (rewrite length_app; cbn [length]; lia).
    rewrite (bwin_split p 0 (8 * length ws) 8) Nat.add_0_l.
    rewrite big_sepL_app big_sepL_singleton Nat.add_0_r.
    iIntros "[Hpre Hlast]".
    iSplitL "Hpre"; [ by iApply IH | ].
    iApply (page_field8_back p (8 * length ws)%nat w with "Hlast").
  Qed.

  (* the converse of [bwin_bytes_list]: a tracked byte list forgets its
     contents and becomes a window again. *)
  Lemma bytes_list_bwin (a : mword 64) (bs : list (bv 8)) :
    ([∗ list] j ↦ b ∈ bs, pa_add a j ↦ₘ b) ⊢
    [∗ list] j ∈ seq 0 (length bs), byte_any (pa_add a j).
  Proof.
    induction bs as [|b bs IH] using rev_ind; [ by iIntros "_" | ].
    rewrite length_app /= Nat.add_1_r seq_S big_sepL_app big_sepL_singleton.
    rewrite big_sepL_app big_sepL_singleton.
    iIntros "[Hpre Hlast]".
    iSplitL "Hpre"; [ by iApply IH | ].
    rewrite Nat.add_0_r. by iExists b.
  Qed.

End PageFields.
