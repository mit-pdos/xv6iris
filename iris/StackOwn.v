(* StackOwn.v -- an abstraction for stack-memory ownership in the whole-function
   WP proofs.

   Function-call WPs (e.g. [wp_mycpu], the S-mode leaf functions) need to own a
   chunk of scratch stack memory: the words their prologue saves callee-saved
   registers into, and -- transitively -- the words any function they call
   needs.  Historically each such WP listed those words one by one, as explicit
   SP-relative [a ↦₈ v] hypotheses (e.g. [(sp-8) ↦₈ raold], [(sp-16) ↦₈ s0old]),
   with the caller responsible for spelling out every address and threading a
   fresh existential value through the pre- and post-condition.

   [stack_own sp n] replaces that with a single predicate: ownership of the [n]
   eight-byte stack slots immediately *below* [sp] -- the region [sp-8n, sp) --
   with existentially-quantified (scratch) contents.  A function that needs a
   frame of [f] slots and calls children needing at most [c] more slots declares
   in its precondition [stack_own sp n] with [f + c ≤ n]; it uses the top [f]
   slots for its own frame and hands [stack_own (sp-8f) (n-f)] to its callees.

   The stack grows downward, so "depth [n]" means the [n] slots below the
   current SP.  The core algebra is [stack_own_app] (a region splits into a
   top part adjacent to SP and a deeper part), from which the "needs depth at
   least [k]" pattern (peel [k] off an arbitrary [n ≥ k]) follows.  Individual
   slots are recovered/rebuilt with [stack_own_1]; the addresses line up with
   the existing [↦₈] spellings via [pa_stk] and [avi_assoc]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Local Open Scope Z_scope.

(* [pa_stk sp k] is the address [8*k] bytes below [sp] -- the base of the [k]-th
   stack slot counted downward from [sp].  [pa_stk sp 0 = sp]; the word saved at
   the top of the frame lives at [pa_stk sp 1 = sp-8]. *)
Definition pa_stk (sp : Arch.pa) (k : nat) : Arch.pa :=
  add_vec_int sp (- (8 * Z.of_nat k)).

Lemma pa_stk_0 (sp : Arch.pa) : pa_stk sp 0 = sp.
Proof. unfold pa_stk. change (- (8 * Z.of_nat 0)) with 0. apply avi0. Qed.

(* stacking two downward shifts adds the depths: sp minus 8a minus 8b is sp
   minus 8(a+b).  This is the address-geometry heart of [stack_own_app]. *)
Lemma pa_stk_assoc (sp : Arch.pa) (a b : nat) :
  pa_stk (pa_stk sp a) b = pa_stk sp (a + b).
Proof.
  unfold pa_stk. rewrite avi_assoc. f_equal. rewrite Nat2Z.inj_add. ring.
Qed.

Lemma pa_stk_shift (sp : Arch.pa) (a i : nat) :
  pa_stk sp (S (a + i)) = pa_stk (pa_stk sp a) (S i).
Proof. rewrite pa_stk_assoc. f_equal. lia. Qed.

(* Address-arithmetic bridge for converting a proof's raw SP-relative slot
   spelling [add_vec (add_vec sp Cframe) Coffset] into [pa_stk sp k].  These
   mirror [VcGen.mword_of_int_wrap/_uint/add_vec_off2] but are kept here (early,
   depending only on [InstrBytes.avi_assoc]) so functions that don't import
   VcGen can still discharge the bridge; distinct names avoid clashing when both
   are in scope. *)
Lemma stk_mword_of_int_wrap (z : Z) :
  (mword_of_int (bv_wrap 64 z) : mword 64) = mword_of_int z.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  apply bv_wrap_bv_wrap. lia.
Qed.

Lemma stk_mword_of_int_uint (w : mword 64) : mword_of_int (uint w) = w.
Proof.
  unfold mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite uint_unsigned.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma pa_stk_off2 (x o1 o2 : mword 64) :
  add_vec (add_vec x o1) o2 = add_vec x (mword_of_int (bv_wrap 64 (uint o1 + uint o2))).
Proof.
  rewrite -{1}(stk_mword_of_int_uint o1) -{1}(stk_mword_of_int_uint o2).
  rewrite stk_mword_of_int_wrap.
  change (add_vec (add_vec x (mword_of_int (uint o1))) (mword_of_int (uint o2)))
    with (add_vec_int (add_vec_int x (uint o1)) (uint o2)).
  change (add_vec x (mword_of_int (uint o1 + uint o2)))
    with (add_vec_int x (uint o1 + uint o2)).
  apply avi_assoc.
Qed.

Section stack_own.
  Context `{!riscvGS Σ}.

  (* Ownership of the [n] eight-byte stack slots just below [sp], region
     [sp-8n, sp), with existential (scratch) contents.  Slot [i] (0-based,
     counted downward from [sp]) holds some word at [pa_stk sp (S i)]. *)
  Definition stack_own (sp : Arch.pa) (n : nat) : iProp Σ :=
    (∃ ws : list (bv 64), ⌜length ws = n⌝ ∗
       [∗ list] i ↦ w ∈ ws, word_pointsto (pa_stk sp (S i)) (DfracOwn 1) w)%I.

  Lemma stack_own_0 (sp : Arch.pa) : stack_own sp 0 ⊣⊢ emp.
  Proof.
    rewrite /stack_own. iSplit.
    - iIntros "H". done.
    - iIntros "_". iExists []. by iSplit.
  Qed.

  (* the workhorse: a depth-[n1+n2] region splits into the top [n1] slots
     (adjacent to [sp]) and the deeper [n2] slots (anchored at [sp-8*n1]). *)
  Lemma stack_own_app (sp : Arch.pa) (n1 n2 : nat) :
    stack_own sp (n1 + n2) ⊣⊢ stack_own sp n1 ∗ stack_own (pa_stk sp n1) n2.
  Proof.
    rewrite /stack_own. iSplit.
    - iIntros "H". iDestruct "H" as (ws) "[%Hlen H]".
      rewrite -(take_drop n1 ws) big_sepL_app.
      iDestruct "H" as "[H1 H2]".
      assert (Hle : (n1 ≤ length ws)%nat) by lia.
      iSplitL "H1".
      + iExists (take n1 ws). iFrame "H1". iPureIntro.
        rewrite length_take. lia.
      + iExists (drop n1 ws). iSplitR.
        { iPureIntro. rewrite length_drop. lia. }
        rewrite length_take_le; [| exact Hle].
        iApply (big_sepL_proper with "H2").
        intros i w _. by rewrite pa_stk_shift.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (ws1) "[%Hlen1 H1]".
      iDestruct "H2" as (ws2) "[%Hlen2 H2]".
      iExists (app ws1 ws2). iSplitR.
      { iPureIntro. rewrite length_app. lia. }
      rewrite big_sepL_app. iFrame "H1".
      rewrite Hlen1.
      iApply (big_sepL_proper with "H2").
      intros i w _. by rewrite pa_stk_shift.
  Qed.

  (* peel a needed depth [a] off the front of an arbitrary-depth [n ≥ a]
     region: the "needs depth at least [a]" precondition pattern. *)
  Lemma stack_own_split (sp : Arch.pa) (a n : nat) :
    (a ≤ n)%nat ->
    stack_own sp n ⊣⊢ stack_own sp a ∗ stack_own (pa_stk sp a) (n - a).
  Proof.
    intro Hle. replace n with (a + (n - a))%nat at 1 by lia.
    apply stack_own_app.
  Qed.

  (* a single slot is exactly one existential word points-to at [sp-8]. *)
  Lemma stack_own_1 (sp : Arch.pa) :
    stack_own sp 1 ⊣⊢ ∃ w : bv 64, word_pointsto (pa_stk sp 1) (DfracOwn 1) w.
  Proof.
    rewrite /stack_own. iSplit.
    - iIntros "H". iDestruct "H" as (ws) "[%Hlen H]".
      destruct ws as [| w [| ??]]; simpl in Hlen; try lia.
      iExists w. iDestruct "H" as "[$ _]".
    - iIntros "H". iDestruct "H" as (w) "H".
      iExists [w]. iSplitR; [done|]. simpl. iFrame.
  Qed.

  Lemma stack_own_1_intro (sp : Arch.pa) (w : bv 64) :
    word_pointsto (pa_stk sp 1) (DfracOwn 1) w ⊢ stack_own sp 1.
  Proof. rewrite stack_own_1. iIntros "H". by iExists w. Qed.

  (* ---- directional forms of the split, for [iDestruct] / [iApply] ---- *)
  Lemma stack_own_split_1 (sp : Arch.pa) (a n : nat) :
    (a ≤ n)%nat ->
    stack_own sp n ⊢ stack_own sp a ∗ stack_own (pa_stk sp a) (n - a).
  Proof. intro Hle. by rewrite (stack_own_split sp a n Hle). Qed.

  Lemma stack_own_split_2 (sp : Arch.pa) (a n : nat) :
    (a ≤ n)%nat ->
    stack_own sp a ∗ stack_own (pa_stk sp a) (n - a) ⊢ stack_own sp n.
  Proof. intro Hle. by rewrite (stack_own_split sp a n Hle). Qed.

  (* ---- the common two-slot frame (e.g. saving ra + s0), spelled with the
     clean [pa_stk sp 1] / [pa_stk sp 2] addresses. ---- *)
  Lemma stack_own_2_elim (sp : Arch.pa) :
    stack_own sp 2 ⊢ ∃ w1 w2 : bv 64,
      word_pointsto (pa_stk sp 1) (DfracOwn 1) w1 ∗
      word_pointsto (pa_stk sp 2) (DfracOwn 1) w2.
  Proof.
    rewrite (stack_own_app sp 1 1) stack_own_1.
    iIntros "[H1 H2]". iDestruct "H1" as (w1) "H1".
    rewrite stack_own_1 (pa_stk_assoc sp 1 1).
    iDestruct "H2" as (w2) "H2". iExists w1, w2. iFrame.
  Qed.

  Lemma stack_own_2_intro (sp : Arch.pa) (w1 w2 : bv 64) :
    word_pointsto (pa_stk sp 1) (DfracOwn 1) w1 -∗
    word_pointsto (pa_stk sp 2) (DfracOwn 1) w2 -∗
    stack_own sp 2.
  Proof.
    iIntros "H1 H2". rewrite (stack_own_app sp 1 1). iSplitL "H1".
    - by iApply stack_own_1_intro.
    - rewrite -(pa_stk_assoc sp 1 1). by iApply stack_own_1_intro.
  Qed.

End stack_own.
