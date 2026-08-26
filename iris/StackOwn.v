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
Require Import RiscvPtsto RiscvExtras.
Require Import InstrBytes.
(* THE M1 FLIP (tso-port): a stack FRAME is thread data -- saved registers,
   spilled locals -- so its slots are context-indexed like every other
   thread-owned byte.  [stack_own_phys] (the boot-side physical carve,
   below) stays raw; the boot chain converts at the hand-off to the first
   thread of control, which is the honest seam. *)
Require Import TsoCtx.
Require TsoCtxShim.   (* [stack_ktier_mono] rides the raw tier law *)
Local Open Scope Z_scope.

(* [pa_stk sp k] is the address [8*k] bytes below [sp] -- the base of the [k]-th
   stack slot counted downward from [sp].  [pa_stk sp 0 = sp]; the word saved at
   the top of the frame lives at [pa_stk sp 1 = sp-8]. *)
Definition pa_stk (sp : Arch.pa) (k : nat) : Arch.pa :=
  add_vec_int sp (- (8 * Z.of_nat k)).


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

(* the unsigned value of an address [8*k] bytes below [sp], when the
   subtraction does not underflow.  Stated with [sp : mword 64] (never
   [Arch.pa], whose width is an unreduced [if] -- durable-notes), like
   [RiscvExtras.uint_pa_add], whose proof shape this mirrors.  Both consumers
   are boot-path: BootBridge's physical->VA stack conversion and BootCarve's
   carve of a hart's stack out of the raw boot image. *)
Lemma z_stk_sub (u d : Z) :
  0 <= d -> d <= u -> u < 18446744073709551616 ->
  bv_wrap 64 (u + bv_wrap 64 (- d)) = u - d.
Proof.
  intros Hd Hdu Hu. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.add_mod_idemp_r; [| lia].
  apply Z.mod_small. lia.
Qed.

Lemma uint_pa_stk (a : mword 64) (k : nat) :
  (8 * Z.of_nat k <= uint a)%Z ->
  uint (pa_stk a k) = (uint a - 8 * Z.of_nat k)%Z.
Proof.
  intro Hle. rewrite !uint_unsigned in Hle |- *.
  unfold pa_stk, add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word.
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hj : bv_unsigned (mword_of_int (- (8 * Z.of_nat k)) : mword 64)
               = bv_wrap 64 (- (8 * Z.of_nat k))).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. reflexivity. }
  rewrite Hj.
  match goal with |- context [bv_wrap ?W _] => change (bv_wrap W) with (bv_wrap 64) end.
  pose proof (bv_unsigned_in_range _ a) as [Hlo Hhi].
  assert (Hhi' : (bv_unsigned a < 18446744073709551616)%Z).
  { revert Hhi. unfold bv_modulus.
    assert (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616)
      as -> by (vm_compute; reflexivity). lia. }
  apply z_stk_sub; [ lia | exact Hle | exact Hhi' ].
Qed.

Section stack_own.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.
  (* The ambient TIER.  [stack_own] is a plain NAME (no notation) used
     textually at ~330 sites, so the tier rides in as an instance-implicit
     argument rather than as a positional one: [stack_own sp n] is
     unchanged everywhere, and a file that pins [CurKtier] gets its stack
     at that tier.  Every lemma in this section is thereby tier-generic --
     the boot stack (KT0, the identity-mapped [stack0]) and a KSTACK frame
     (KT1) share one algebra, which is the whole point of the project. *)
  Context `{KTR : !CurKtier}.

  (* Ownership of the [n] eight-byte stack slots just below [sp], region
     [sp-8n, sp), with existential (scratch) contents.  Slot [i] (0-based,
     counted downward from [sp]) holds some word at [pa_stk sp (S i)]. *)
  Definition stack_own (sp : Arch.pa) (n : nat) : iProp Σ :=
    (∃ ws : list (bv 64), ⌜length ws = n⌝ ∗
       [∗ list] i ↦ w ∈ ws, ctx_word_pointsto cur_ctx (pa_stk sp (S i)) (DfracOwn 1) w)%I.

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
    stack_own sp 1 ⊣⊢ ∃ w : bv 64, ctx_word_pointsto cur_ctx (pa_stk sp 1) (DfracOwn 1) w.
  Proof.
    rewrite /stack_own. iSplit.
    - iIntros "H". iDestruct "H" as (ws) "[%Hlen H]".
      destruct ws as [| w [| ??]]; simpl in Hlen; try lia.
      iExists w. iDestruct "H" as "[$ _]".
    - iIntros "H". iDestruct "H" as (w) "H".
      iExists [w]. iSplitR; [done|]. simpl. iFrame.
  Qed.

  Lemma stack_own_1_intro (sp : Arch.pa) (w : bv 64) :
    ctx_word_pointsto cur_ctx (pa_stk sp 1) (DfracOwn 1) w ⊢ stack_own sp 1.
  Proof. rewrite stack_own_1. iIntros "H". by iExists w. Qed.

  (* Expose the whole region as [n] cleanly-addressed slots (slot [k] at
     [pa_stk sp k], k = 1..n).  With [cbn [seq]] the [big_sepL] over a concrete
     [seq 1 n] unfolds to a flat conjunction, so an N-slot frame peels/rebundles
     with a single [iDestruct "(S1 & .. & Sn & _)"] and no nested [pa_stk]. *)
  Lemma stack_own_slots (sp : Arch.pa) (n : nat) :
    stack_own sp n ⊣⊢
    [∗ list] k ∈ seq 1 n, ∃ w : bv 64, ctx_word_pointsto cur_ctx (pa_stk sp k) (DfracOwn 1) w.
  Proof.
    revert sp. induction n as [|n IH]; intro sp.
    - rewrite stack_own_0. by rewrite big_sepL_nil.
    - replace (S n) with (1 + n)%nat by lia.
      rewrite stack_own_app stack_own_1 IH.
      change (seq 1 (1 + n)) with (1%nat :: seq 2 n).
      rewrite big_sepL_cons.
      f_equiv.
      rewrite -(fmap_S_seq 1 n) big_sepL_fmap.
      apply big_sepL_proper. intros k y _.
      by rewrite (pa_stk_assoc sp 1 y).
  Qed.

  (* Base-anchored enumeration: the same region as [n] slots counted UP
     from the region's BASE [pa_stk sp n] (slot [j] at base + 8j,
     j = 0..n-1).  This is the shape an sp-move ledger uses: after
     [sp' = sp - 8n] the freed region [sp', sp) is exactly the [n]
     positive-offset words at the NEW sp. *)
  Lemma pa_stk_base_S (sp : Arch.pa) (n j : nat) :
    add_vec_int (pa_stk sp (S n)) (8 * Z.of_nat (S j))
    = add_vec_int (pa_stk sp n) (8 * Z.of_nat j).
  Proof. unfold pa_stk. rewrite !avi_assoc. f_equal. lia. Qed.

  Lemma stack_own_base (sp : Arch.pa) (n : nat) :
    stack_own sp n ⊣⊢
    [∗ list] j ∈ seq 0 n, ∃ w : bv 64,
      ctx_word_pointsto cur_ctx (add_vec_int (pa_stk sp n) (8 * Z.of_nat j)) (DfracOwn 1) w.
  Proof.
    induction n as [|n IH].
    - rewrite stack_own_0. by rewrite big_sepL_nil.
    - replace (S n) with (n + 1)%nat at 1 by lia.
      rewrite stack_own_app IH stack_own_1 (pa_stk_assoc sp n 1).
      replace (n + 1)%nat with (S n) by lia.
      change (seq 0 (S n)) with (0%nat :: seq 1 n).
      rewrite big_sepL_cons.
      change (8 * Z.of_nat 0) with 0. rewrite avi0.
      rewrite -(fmap_S_seq 0 n) big_sepL_fmap.
      iSplit.
      + iIntros "[HL HS]". iFrame "HS".
        iApply (big_sepL_mono with "HL").
        intros k y _. by rewrite pa_stk_base_S.
      + iIntros "[HS HL]". iFrame "HS".
        iApply (big_sepL_mono with "HL").
        intros k y _. by rewrite pa_stk_base_S.
  Qed.

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
      ctx_word_pointsto cur_ctx (pa_stk sp 1) (DfracOwn 1) w1 ∗
      ctx_word_pointsto cur_ctx (pa_stk sp 2) (DfracOwn 1) w2.
  Proof.
    rewrite (stack_own_app sp 1 1) stack_own_1.
    iIntros "[H1 H2]". iDestruct "H1" as (w1) "H1".
    rewrite stack_own_1 (pa_stk_assoc sp 1 1).
    iDestruct "H2" as (w2) "H2". iExists w1, w2. iFrame.
  Qed.

  Lemma stack_own_2_intro (sp : Arch.pa) (w1 w2 : bv 64) :
    ctx_word_pointsto cur_ctx (pa_stk sp 1) (DfracOwn 1) w1 -∗
    ctx_word_pointsto cur_ctx (pa_stk sp 2) (DfracOwn 1) w2 -∗
    stack_own sp 2.
  Proof.
    iIntros "H1 H2". rewrite (stack_own_app sp 1 1). iSplitL "H1".
    - by iApply stack_own_1_intro.
    - rewrite -(pa_stk_assoc sp 1 1). by iApply stack_own_1_intro.
  Qed.


  (* ---- the four-slot frame (a 32-byte C frame saving ra + s0 and holding
     two locals), the twin of the two-slot pair above. ---- *)
  Lemma stack_own_4_elim (sp : Arch.pa) :
    stack_own sp 4 ⊢ ∃ w1 w2 w3 w4 : bv 64,
      ctx_word_pointsto cur_ctx (pa_stk sp 1) (DfracOwn 1) w1 ∗
      ctx_word_pointsto cur_ctx (pa_stk sp 2) (DfracOwn 1) w2 ∗
      ctx_word_pointsto cur_ctx (pa_stk sp 3) (DfracOwn 1) w3 ∗
      ctx_word_pointsto cur_ctx (pa_stk sp 4) (DfracOwn 1) w4.
  Proof.
    assert (E3 : pa_stk (pa_stk sp 2) 1 = pa_stk sp 3) by (rewrite pa_stk_assoc; reflexivity).
    assert (E4 : pa_stk (pa_stk sp 2) 2 = pa_stk sp 4) by (rewrite pa_stk_assoc; reflexivity).
    rewrite (stack_own_split sp 2 4 ltac:(lia)).
    iIntros "[H12 H34]".
    iDestruct (stack_own_2_elim with "H12") as (w1 w2) "[H1 H2]".
    change (4 - 2)%nat with 2%nat.
    iDestruct (stack_own_2_elim with "H34") as (w3 w4) "[H3 H4]".
    iEval (rewrite E3) in "H3". iEval (rewrite E4) in "H4".
    iExists w1, w2, w3, w4. iFrame.
  Qed.

  Lemma stack_own_4_intro (sp : Arch.pa) (w1 w2 w3 w4 : bv 64) :
    ctx_word_pointsto cur_ctx (pa_stk sp 1) (DfracOwn 1) w1 -∗
    ctx_word_pointsto cur_ctx (pa_stk sp 2) (DfracOwn 1) w2 -∗
    ctx_word_pointsto cur_ctx (pa_stk sp 3) (DfracOwn 1) w3 -∗
    ctx_word_pointsto cur_ctx (pa_stk sp 4) (DfracOwn 1) w4 -∗
    stack_own sp 4.
  Proof.
    assert (E3 : pa_stk (pa_stk sp 2) 1 = pa_stk sp 3) by (rewrite pa_stk_assoc; reflexivity).
    assert (E4 : pa_stk (pa_stk sp 2) 2 = pa_stk sp 4) by (rewrite pa_stk_assoc; reflexivity).
    iIntros "H1 H2 H3 H4".
    rewrite (stack_own_split sp 2 4 ltac:(lia)).
    iSplitL "H1 H2".
    - iApply (stack_own_2_intro sp with "H1 H2").
    - change (4 - 2)%nat with 2%nat.
      iEval (rewrite -E3) in "H3". iEval (rewrite -E4) in "H4".
      iApply (stack_own_2_intro (pa_stk sp 2) with "H3 H4").
  Qed.


  (* ------------------------------------------------------------------ *)
  (* WHERE the stack IS: an owned frame pins sp away from 0.             *)
  (* ------------------------------------------------------------------ *)
  (* A C function that passes [&local] to a callee which null-checks the
     pointer (argfd's [if (pfd)]) owes the callee a disequality, and the
     caller must be able to DISCHARGE it rather than assume it (the
     "caller obligation" rule in durable-notes).  It can: every address in
     an owned frame is CANONICAL (< 2^38, [mem_canonical]), and an sp below
     8 would put the very next slot at ~2^64 -- so owning one slot already
     forces [8 <= sp], and the canonical bound caps it from above.  Nothing
     about the kernel's stack layout is assumed. *)
  Local Lemma z_stk_bounds (u v : Z) :
    (0 <= u < 18446744073709551616)%Z ->
    v = bv_wrap 64 (u - 8) ->
    (v < 274877906944)%Z ->
    (8 <= u < 274877906944 + 8)%Z.
  Proof.
    intros Hu Hv Hlt. unfold bv_wrap, bv_modulus in Hv.
    change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in Hv.
    destruct (Z_lt_le_dec u 8) as [Hsm | Hge].
    - exfalso.
      assert (Hmod : ((u - 8) mod 18446744073709551616)%Z = (u - 8 + 18446744073709551616)%Z).
      { rewrite <- (Z.mod_add (u - 8) 1 18446744073709551616); [| lia].
        apply Z.mod_small. lia. }
      lia.
    - assert (Hmod : ((u - 8) mod 18446744073709551616)%Z = (u - 8)%Z)
        by (apply Z.mod_small; lia).
      lia.
  Qed.

  Lemma stack_own_sp_bounds (sp : Arch.pa) (n : nat) :
    (0 < n)%nat -> stack_own sp n ⊢ ⌜(8 <= uint sp < 274877906944 + 8)%Z⌝.
  Proof.
    intro Hn. rewrite (stack_own_split_1 sp 1 n ltac:(lia)).
    iIntros "[H1 _]". rewrite stack_own_1. iDestruct "H1" as (w) "H1".
    rewrite ctx_word_pointsto_unfold. iDestruct "H1" as "[_ Hbs]".
    assert (Hs : seq 0 8 = (0%nat :: seq 1 7)%list) by reflexivity.
    rewrite Hs. iDestruct "Hbs" as "[Hb0 _]".
    rewrite pa_add_0.
    iDestruct (mem_canonical with "Hb0") as %Hc.
    iPureIntro.
    rewrite uint_unsigned. rewrite uint_unsigned in Hc.
    pose proof (bv_unsigned_in_range _ sp) as [Hlo Hhi'].
    (* [Arch.pa]'s width is an unreduced [if]; both bounds are convertible to
       the width-64 ones, so [exact] (which converts) crosses the gap. *)
    assert (Hhi : (bv_unsigned sp < 18446744073709551616)%Z)
      by (unfold bv_modulus in Hhi'; exact Hhi').
    apply (z_stk_bounds (bv_unsigned sp) (bv_unsigned (pa_stk sp 1)));
      [ split; [exact Hlo | exact Hhi] | | exact Hc ].
    unfold pa_stk, add_vec_int, add_vec, Operators_mwords.word_binop,
      Operators_mwords.with_word', SailStdpp.Values.with_word, to_word, get_word,
      MachineWord.MachineWord.add.
    rewrite bv_add_unsigned.
    assert (H8 : bv_unsigned (mword_of_int (- (8 * Z.of_nat 1)) : mword 64)
                 = 18446744073709551608%Z) by (vm_compute; reflexivity).
    rewrite H8.
    match goal with |- context [bv_wrap ?W _] => change (bv_wrap W) with (bv_wrap 64) end.
    unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
    rewrite <- (Z.mod_add (bv_unsigned sp - 8) 1 18446744073709551616); [| lia].
    generalize (bv_unsigned sp); intro u. f_equal. lia.
  Qed.

End stack_own.

(* THE WEAKENING ALONG THE TIER ORDER.  A stack region is a big-op of
   [word_pointsto]s at one tier, and each of those weakens
   ([RiscvPtsto.word_ktier_mono]), so the region does -- which is what makes
   the bundles built over it ([IntrDefs.sie_cap]) tier-COVARIANT.

   OUTSIDE the section, necessarily: a heterogeneous statement has to name
   the two tiers, and a section-local definition is NOT parameterized over
   its own section variables -- [stack_own (KTR := kt)] written above fails
   with "Wrong argument name KTR", the same rule the hart binder obeys
   (durable-notes, "CpuId IS A CLASS, SO A CROSSING NEEDS A NEW SECTION"). *)
(* SHIM-TIER (dies at cutover): a stack region re-indexed between two
   contexts -- the swtch hand-off crosses the M2 seam here at SC. *)
Lemma stack_own_reindex `{!riscvGS Σ} `{KTR : !CurKtier} (ξ ξ' : CtxId)
    (sp : Arch.pa) (n : nat) :
  stack_own (XI := ξ) sp n ⊢ stack_own (XI := ξ') sp n.
Proof.
  rewrite /stack_own. iIntros "H". iDestruct "H" as (ws) "[%Hlen H]".
  iExists ws. iSplitR; [done |].
  iApply (big_sepL_mono with "H"). iIntros (i w _) "H".
  iDestruct (TsoCtxShim.ctx_word_to_mem with "H") as "H".
  iApply (TsoCtxShim.ctx_word_of_mem with "H").
Qed.

Lemma stack_ktier_mono `{!riscvGS Σ} `{XI : CurCtx} (kt kt' : ktier) `{!KtierLe kt kt'}
    (sp : Arch.pa) (n : nat) :
  stack_own (KTR := kt) sp n ⊢ stack_own (KTR := kt') sp n.
Proof.
  rewrite /stack_own. iIntros "H". iDestruct "H" as (ws) "[%Hlen H]".
  iExists ws. iSplitR; [done |].
  iApply (big_sepL_mono with "H"). iIntros (i w _) "H".
  (* per-slot through the shim: the raw tier-weakening law, re-indexed *)
  iDestruct (TsoCtxShim.ctx_word_to_mem with "H") as "H".
  iApply TsoCtxShim.ctx_word_of_mem.
  iApply (word_ktier_mono kt kt' with "H").
Qed.

(* [zero_reg] is the null pointer a C null test compares against. *)
Lemma uint_zero_reg : uint (zero_reg : mword 64) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

(* an address at a NON-NEGATIVE, canonical offset from a sound sp is non-null:
   the sum cannot wrap, and it is at least 8.  Stated at [mword 64] rather
   than [Arch.pa] so every rewrite below sees the reduced width (Arch.pa's is
   an unreduced [if], and [bv_unsigned] then elaborates at THAT width -- see
   durable-notes); call sites cross the gap by conversion. *)
Lemma stack_off_nonzero (sp : SailStdpp.Values.mword 64) (c : Z) :
  (8 <= uint sp < 274877906944 + 8)%Z -> (0 <= c < 274877906944)%Z ->
  add_vec_int sp c <> (zero_reg : mword 64).
Proof.
  intros Hsp Hc Heq.
  assert (Hu : uint (add_vec_int sp c) = 0%Z) by (rewrite Heq; apply uint_zero_reg).
  rewrite uint_unsigned in Hu. rewrite uint_unsigned in Hsp.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', SailStdpp.Values.with_word, to_word, get_word,
    MachineWord.MachineWord.add in Hu.
  rewrite bv_add_unsigned in Hu.
  rewrite (moi64_unsigned c) in Hu.
  rewrite (bv_wrap_small 64 c) in Hu;
    [| unfold bv_modulus; change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z; lia].
  unfold bv_wrap, bv_modulus in Hu.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in Hu.
  revert Hu Hsp. generalize (bv_unsigned sp); intros u Hu Hsp.
  rewrite (Z.mod_small (u + c) 18446744073709551616) in Hu; lia.
Qed.

(* the degenerate offset-0 case of [stack_off_nonzero], stated on the bound
   alone so a caller that already has it need not re-open the capability. *)
Lemma sp_bounds_nonzero (x : SailStdpp.Values.mword 64) :
  (8 <= uint x < 274877906944 + 8)%Z -> x <> (zero_reg : mword 64).
Proof. intros Hb He. rewrite He uint_zero_reg in Hb. lia. Qed.

Lemma stack_own_sp_nonzero `{!riscvGS Σ} `{XI : CurCtx} (sp : Arch.pa) (n : nat) :
  (0 < n)%nat -> stack_own sp n ⊢ ⌜sp <> (zero_reg : mword 64)⌝.
Proof.
  intro Hn. iIntros "H".
  iDestruct (stack_own_sp_bounds sp n Hn with "H") as %Hb.
  iPureIntro. intro Heq. rewrite Heq uint_zero_reg in Hb. lia.
Qed.

Section stack_own_phys.
  Context `{!riscvGS Σ}.

  (* ===== PHYSICAL-tier stack ownership (M-mode boot owns ↦ₚ, uniform-
     claims): the [↦ₚ₈] mirror of [stack_own], same lemma suite. ===== *)
  Definition stack_own_phys (sp : Arch.pa) (n : nat) : iProp Σ :=
    (∃ ws : list (bv 64), ⌜length ws = n⌝ ∗
       [∗ list] i ↦ w ∈ ws, phys_word_pointsto (pa_stk sp (S i)) (DfracOwn 1) w)%I.

  Lemma stack_own_phys_0 (sp : Arch.pa) : stack_own_phys sp 0 ⊣⊢ emp.
  Proof.
    rewrite /stack_own_phys. iSplit.
    - iIntros "H". done.
    - iIntros "_". iExists []. by iSplit.
  Qed.

  Lemma stack_own_phys_app (sp : Arch.pa) (n1 n2 : nat) :
    stack_own_phys sp (n1 + n2) ⊣⊢ stack_own_phys sp n1 ∗ stack_own_phys (pa_stk sp n1) n2.
  Proof.
    rewrite /stack_own_phys. iSplit.
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

  Lemma stack_own_phys_split (sp : Arch.pa) (a n : nat) :
    (a ≤ n)%nat ->
    stack_own_phys sp n ⊣⊢ stack_own_phys sp a ∗ stack_own_phys (pa_stk sp a) (n - a).
  Proof.
    intro Hle. replace n with (a + (n - a))%nat at 1 by lia.
    apply stack_own_phys_app.
  Qed.

  Lemma stack_own_phys_1 (sp : Arch.pa) :
    stack_own_phys sp 1 ⊣⊢ ∃ w : bv 64, phys_word_pointsto (pa_stk sp 1) (DfracOwn 1) w.
  Proof.
    rewrite /stack_own_phys. iSplit.
    - iIntros "H". iDestruct "H" as (ws) "[%Hlen H]".
      destruct ws as [| w [| ??]]; simpl in Hlen; try lia.
      iExists w. iDestruct "H" as "[$ _]".
    - iIntros "H". iDestruct "H" as (w) "H".
      iExists [w]. iSplitR; [done|]. simpl. iFrame.
  Qed.

  Lemma stack_own_phys_1_intro (sp : Arch.pa) (w : bv 64) :
    phys_word_pointsto (pa_stk sp 1) (DfracOwn 1) w ⊢ stack_own_phys sp 1.
  Proof. rewrite stack_own_phys_1. iIntros "H". by iExists w. Qed.

  Lemma stack_own_phys_split_1 (sp : Arch.pa) (a n : nat) :
    (a ≤ n)%nat ->
    stack_own_phys sp n ⊢ stack_own_phys sp a ∗ stack_own_phys (pa_stk sp a) (n - a).
  Proof. intro Hle. by rewrite (stack_own_phys_split sp a n Hle). Qed.

  Lemma stack_own_phys_split_2 (sp : Arch.pa) (a n : nat) :
    (a ≤ n)%nat ->
    stack_own_phys sp a ∗ stack_own_phys (pa_stk sp a) (n - a) ⊢ stack_own_phys sp n.
  Proof. intro Hle. by rewrite (stack_own_phys_split sp a n Hle). Qed.

  Lemma stack_own_phys_2_elim (sp : Arch.pa) :
    stack_own_phys sp 2 ⊢ ∃ w1 w2 : bv 64,
      phys_word_pointsto (pa_stk sp 1) (DfracOwn 1) w1 ∗
      phys_word_pointsto (pa_stk sp 2) (DfracOwn 1) w2.
  Proof.
    rewrite (stack_own_phys_app sp 1 1) stack_own_phys_1.
    iIntros "[H1 H2]". iDestruct "H1" as (w1) "H1".
    rewrite stack_own_phys_1 (pa_stk_assoc sp 1 1).
    iDestruct "H2" as (w2) "H2". iExists w1, w2. iFrame.
  Qed.

  Lemma stack_own_phys_2_intro (sp : Arch.pa) (w1 w2 : bv 64) :
    phys_word_pointsto (pa_stk sp 1) (DfracOwn 1) w1 -∗
    phys_word_pointsto (pa_stk sp 2) (DfracOwn 1) w2 -∗
    stack_own_phys sp 2.
  Proof.
    iIntros "H1 H2". rewrite (stack_own_phys_app sp 1 1). iSplitL "H1".
    - by iApply stack_own_phys_1_intro.
    - rewrite -(pa_stk_assoc sp 1 1). by iApply stack_own_phys_1_intro.
  Qed.

End stack_own_phys.
