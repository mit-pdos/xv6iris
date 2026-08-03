(* StackBytes.v -- a BYTE buffer carved out of a function's own stack frame.

   A C local that is an array of char (printint's [buf[20]], printk's format
   scratch) lives inside the frame at a byte offset, so it straddles the 8-byte
   slots [stack_own] hands out: printint's [buf] starts at [s0-56], which is
   slot 7 of its 8-slot frame, and runs 20 bytes -- all of slot 7, all of slot
   6, and the low half of slot 5.  The frame resource speaks in [↦₈] words and
   the [sb]/[lbu] leaves speak in [↦ₘ] bytes, so something has to carve one into
   the other and put it back.  That is this file, and it is deliberately NOT
   printint-specific: any stack array wants it.

   [bytes_own dq base n] is [n] bytes at [base], each individually owned, with
   contents UNSPECIFIED -- an array of chars nobody has written yet is exactly
   that, and after the loop has written it the contents are again whatever was
   written.  The two directions are:

     [slot_bytes_own] : a frame word IS eight such bytes,
     [bytes_own_slot] : eight such bytes are a frame word again -- the value
       being [Z_to_bv 64 (assemble_bytes ..)], which is why the rebuild needs
       [nth_byte_assemble_len] (RiscvModelBytes) and not just a fold.

   The alignment fact travels separately ([word_pointsto_aligned_p]): a word
   points-to carries it, a byte run does not, so take it out BEFORE splitting --
   the rebuild needs it and the bytes no longer have it.  That is the same
   discipline [InstrBytes.word_pointsto_split4] documents for the 4-byte split. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import StackOwn.
Require Import RiscvExtras.
Local Open Scope Z_scope.

(* [pa_add] composes into a single offset -- the byte-run analogue of
   [pa_stk_assoc].  Everything below is index arithmetic on top of it. *)
Lemma pa_add_add (p : mword 64) (i j : nat) :
  pa_add (pa_add p i) j = pa_add p (i + j).
Proof.
  unfold pa_add, add_vec_int. apply bv_eq.
  rewrite !add_vec64_unsigned !moi64_unsigned.
  rewrite !bv_wrap_add_idemp_r. rewrite !bv_wrap_add_idemp_l.
  f_equal. lia.
Qed.

(* the two ends of that composition, at the offsets a byte-at-a-time WALK
   uses: index 0 is the base, and [addi p,p,1] steps the index. *)
Lemma pa_add_0 (p : mword 64) : pa_add p 0 = p.
Proof.
  unfold pa_add, add_vec_int. apply bv_eq.
  rewrite add_vec64_unsigned moi64_unsigned.
  change (bv_wrap 64 (Z.of_nat 0)) with 0. rewrite Z.add_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma pa_add_S (p : mword 64) (i : nat) :
  add_vec (pa_add p i) (mword_of_int 1 : mword 64) = pa_add p (S i).
Proof.
  unfold pa_add, add_vec_int. apply bv_eq.
  rewrite !add_vec64_unsigned !moi64_unsigned.
  rewrite !bv_wrap_add_idemp_r. rewrite !bv_wrap_add_idemp_l.
  f_equal. lia.
Qed.

(* the eight bytes of the word they assemble into -- the rebuild's only
   arithmetic, instantiated at the one length a frame slot has. *)
Lemma nth_byte8 (b0 b1 b2 b3 b4 b5 b6 b7 : bv 8) (j : nat) :
  (j < 8)%nat ->
  nth_byte (Z_to_bv 64 (assemble_bytes [b0;b1;b2;b3;b4;b5;b6;b7]) : bv 64) j
  = [b0;b1;b2;b3;b4;b5;b6;b7] !!! j.
Proof. intro Hj. apply nth_byte_assemble_len; cbn [length]; lia. Qed.

Section StackBytes.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* [n] bytes at [base], individually owned, contents unspecified. *)
  Definition bytes_own (dq : dfrac) (base : Arch.pa) (n : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 n, ∃ b : bv 8, (pa_add base j) ↦ₘ{dq} b)%I.

  Lemma bytes_own_0 dq base : bytes_own dq base 0 ⊣⊢ emp.
  Proof. rewrite /bytes_own. by rewrite big_sepL_nil. Qed.

  (* split a run at any point; the tail is indexed from the shifted base, which
     is what lets a caller name a sub-array (printint's [buf] inside the three
     slots it borrowed) without re-indexing. *)
  Lemma bytes_own_app dq base (n1 n2 : nat) :
    bytes_own dq base (n1 + n2) ⊣⊢ bytes_own dq base n1 ∗ bytes_own dq (pa_add base n1) n2.
  Proof.
    rewrite /bytes_own seq_app big_sepL_app.
    replace (seq (0 + n1) n2) with ((Nat.add n1) <$> seq 0 n2)
      by (rewrite fmap_add_seq; f_equal; lia).
    rewrite big_sepL_fmap.
    apply bi.sep_proper; [reflexivity | ].
    apply big_sepL_proper. intros k j Hk.
    by rewrite pa_add_add.
  Qed.

  (* borrow byte [i] of a run and give it back *)
  Lemma bytes_own_acc dq base (n i : nat) :
    (i < n)%nat ->
    bytes_own dq base n ⊢
    (∃ b : bv 8, (pa_add base i) ↦ₘ{dq} b) ∗
    (∀ b : bv 8, (pa_add base i) ↦ₘ{dq} b -∗ bytes_own dq base n).
  Proof.
    intro Hi. rewrite /bytes_own.
    iIntros "H".
    iDestruct (big_sepL_lookup_acc _ _ i i with "H") as "[Hb Hcl]".
    { rewrite lookup_seq_lt; [reflexivity | exact Hi]. }
    iFrame "Hb". iIntros (b) "Hb". iApply "Hcl". by iExists b.
  Qed.

  (* ---- one 8-byte frame word <-> eight bytes ---- *)

  Lemma slot_bytes_own (a : Arch.pa) (w : bv 64) :
    a ↦₈ w ⊢ ⌜ is_aligned_paddr (Physaddr a) 8 = true ⌝ ∗ bytes_own (DfracOwn 1) a 8.
  Proof.
    iIntros "Hw".
    iDestruct (word_pointsto_aligned_p with "Hw") as %Hal.
    iSplitR; [done | ].
    iDestruct (word_pointsto_bytes with "Hw") as "Hbs".
    rewrite /bytes_own. iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (k j Hk) "Hb". by iExists (nth_byte w j).
  Qed.

  Lemma bytes_own_slot (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 8 = true ->
    bytes_own (DfracOwn 1) a 8 ⊢ ∃ w : bv 64, a ↦₈ w.
  Proof.
    intro Hal. rewrite /bytes_own.
    (* name the eight bytes, then reassemble them into the word whose
       [nth_byte]s they are *)
    cbn [seq]. iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _)".
    iDestruct "H0" as (b0) "H0". iDestruct "H1" as (b1) "H1".
    iDestruct "H2" as (b2) "H2". iDestruct "H3" as (b3) "H3".
    iDestruct "H4" as (b4) "H4". iDestruct "H5" as (b5) "H5".
    iDestruct "H6" as (b6) "H6". iDestruct "H7" as (b7) "H7".
    (* turn each OWNED byte into the corresponding [nth_byte] of the assembled
       word -- rewriting the hypotheses, not the goal, so nothing has to match
       under the big-op *)
    set (W := Z_to_bv 64 (assemble_bytes [b0;b1;b2;b3;b4;b5;b6;b7]) : bv 64).
    assert (Hw0 : b0 = nth_byte W 0%nat) by (symmetry; apply nth_byte8; lia).
    assert (Hw1 : b1 = nth_byte W 1%nat) by (symmetry; apply nth_byte8; lia).
    assert (Hw2 : b2 = nth_byte W 2%nat) by (symmetry; apply nth_byte8; lia).
    assert (Hw3 : b3 = nth_byte W 3%nat) by (symmetry; apply nth_byte8; lia).
    assert (Hw4 : b4 = nth_byte W 4%nat) by (symmetry; apply nth_byte8; lia).
    assert (Hw5 : b5 = nth_byte W 5%nat) by (symmetry; apply nth_byte8; lia).
    assert (Hw6 : b6 = nth_byte W 6%nat) by (symmetry; apply nth_byte8; lia).
    assert (Hw7 : b7 = nth_byte W 7%nat) by (symmetry; apply nth_byte8; lia).
    iEval (rewrite Hw0) in "H0". iEval (rewrite Hw1) in "H1".
    iEval (rewrite Hw2) in "H2". iEval (rewrite Hw3) in "H3".
    iEval (rewrite Hw4) in "H4". iEval (rewrite Hw5) in "H5".
    iEval (rewrite Hw6) in "H6". iEval (rewrite Hw7) in "H7".
    iExists W.
    iApply word_pointsto_intro; [exact Hal | ].
    cbn [seq].
    iFrame "H0 H1 H2 H3 H4 H5 H6 H7". done.
  Qed.

  (* ---- a RUN of frame slots <-> a byte run ----

     Slot [k] is the LOWEST address of the run ([pa_stk sp k = sp - 8k]), so
     slots [k], [k-1], ... are ascending 8-byte blocks and the byte run starts
     at slot [k].  Stated for the two lengths the kernel's stack arrays need
     (printint borrows three slots); the general [r] version would need
     [pa_stk sp (k - i)] index arithmetic that buys nothing here. *)

  Lemma pa_stk_next (sp : Arch.pa) (k : nat) :
    (1 <= k)%nat -> pa_add (pa_stk sp k) 8 = pa_stk sp (k - 1).
  Proof.
    intro Hk. unfold pa_add, pa_stk, add_vec_int. apply bv_eq.
    rewrite !add_vec64_unsigned !moi64_unsigned.
    rewrite !bv_wrap_add_idemp_r. rewrite !bv_wrap_add_idemp_l.
    f_equal. lia.
  Qed.

  Lemma slots3_bytes_own (sp : Arch.pa) (k : nat) (w1 w2 w3 : bv 64) :
    (2 <= k)%nat ->
    (pa_stk sp k) ↦₈ w1 -∗ (pa_stk sp (k - 1)) ↦₈ w2 -∗ (pa_stk sp (k - 2)) ↦₈ w3 -∗
    ⌜ is_aligned_paddr (Physaddr (pa_stk sp k)) 8 = true /\
      is_aligned_paddr (Physaddr (pa_stk sp (k - 1))) 8 = true /\
      is_aligned_paddr (Physaddr (pa_stk sp (k - 2))) 8 = true ⌝ ∗
    bytes_own (DfracOwn 1) (pa_stk sp k) 24.
  Proof.
    intro Hk.
    assert (E1 : pa_add (pa_stk sp k) 8 = pa_stk sp (k - 1))
      by (apply pa_stk_next; lia).
    assert (E2 : pa_add (pa_stk sp (k - 1)) 8 = pa_stk sp (k - 1 - 1))
      by (apply pa_stk_next; lia).
    assert (E2' : (k - 1 - 1)%nat = (k - 2)%nat) by lia.
    rewrite E2' in E2.
    iIntros "H1 H2 H3".
    iDestruct (slot_bytes_own with "H1") as "[%Ha1 B1]".
    iDestruct (slot_bytes_own with "H2") as "[%Ha2 B2]".
    iDestruct (slot_bytes_own with "H3") as "[%Ha3 B3]".
    iSplitR; [done | ].
    change 24%nat with (8 + (8 + 8))%nat.
    rewrite bytes_own_app. iSplitL "B1"; [iExact "B1" | ].
    rewrite bytes_own_app E1. iSplitL "B2"; [iExact "B2" | ].
    by rewrite E2.
  Qed.

  Lemma bytes_own_slots3 (sp : Arch.pa) (k : nat) :
    (2 <= k)%nat ->
    is_aligned_paddr (Physaddr (pa_stk sp k)) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp (k - 1))) 8 = true ->
    is_aligned_paddr (Physaddr (pa_stk sp (k - 2))) 8 = true ->
    bytes_own (DfracOwn 1) (pa_stk sp k) 24 ⊢
    ∃ w1 w2 w3 : bv 64,
      (pa_stk sp k) ↦₈ w1 ∗ (pa_stk sp (k - 1)) ↦₈ w2 ∗ (pa_stk sp (k - 2)) ↦₈ w3.
  Proof.
    intros Hk Ha1 Ha2 Ha3.
    assert (E1 : pa_add (pa_stk sp k) 8 = pa_stk sp (k - 1))
      by (apply pa_stk_next; lia).
    assert (E2 : pa_add (pa_stk sp (k - 1)) 8 = pa_stk sp (k - 1 - 1))
      by (apply pa_stk_next; lia).
    assert (E2' : (k - 1 - 1)%nat = (k - 2)%nat) by lia.
    rewrite E2' in E2.
    iIntros "B".
    change 24%nat with (8 + (8 + 8))%nat.
    rewrite bytes_own_app. iDestruct "B" as "[B1 B]".
    rewrite E1 bytes_own_app. iDestruct "B" as "[B2 B3]".
    rewrite E2.
    iDestruct (bytes_own_slot _ Ha1 with "B1") as (w1) "H1".
    iDestruct (bytes_own_slot _ Ha2 with "B2") as (w2) "H2".
    iDestruct (bytes_own_slot _ Ha3 with "B3") as (w3) "H3".
    iExists w1, w2, w3. iFrame.
  Qed.

End StackBytes.
