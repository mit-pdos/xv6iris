(* PtAdBits.v -- bit-level laws of the PTE A/D-variance constructor
   [pte_set_ad] (PtTree.v's "same mapping, arbitrary A/D" witness).

   [pte_set_ad w a d] rewrites the A (bit 6) and D (bit 7) flag bits of a
   64-bit PTE word -- the EXACT update shape [update_PTE_Bits] produces
   on the Svadu/ADUE write-back path.  This file proves, by the
   MstatusBits testbit-chasing style (iris-FREE dialect so [rewrite ... by]
   parses):
     - [update_PTE_Bits_set_ad] : the write-back word is a variant;
     - [pte_set_ad_refl]        : every word is a variant of itself;
     - [pte_set_ad_testbit]     : THE bitwise reading -- bit 6 is [a], bit
                                  7 is [d], every other bit is the word's
                                  own.  The three laws below are corollaries
                                  of it, and so is anything that has to
                                  commute [pte_set_ad] with another bit
                                  operation (ProcPtOwn's clear-U block);
     - [pte_set_ad_absorb]      : re-varying absorbs (variance is stable
                                  under further A/D write-backs);
     - [pte_set_ad_ppn] / [pte_set_ad_ext] : the PPN and extension fields
                                  are untouched (variants translate to the
                                  same page, cache the same pteAddr);
     - [pte_set_ad_nonleaf]     : leaf-ness is untouched.               *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.   (* [nth_byte] / [bv_eq_of_bytes]: §5.5's
                                     byte -> word reassembly lives here *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(* The constructor.                                                       *)
(* ===================================================================== *)

Definition pte_set_ad (w : mword 64) (a d : mword 1) : mword 64 :=
  update_subrange_vec_dec w 7 0
    (_update_PTE_Flags_D (_update_PTE_Flags_A
       (Mk_PTE_Flags (subrange_vec_dec w 7 0)) a) d).

(* the write-back word is an A/D variant of the walked leaf *)
Lemma update_PTE_Bits_set_ad (w w' : mword 64) (acc : MemoryAccessType mem_payload) :
  update_PTE_Bits w acc = Some w' ->
  exists a d, w' = pte_set_ad w a d.
Proof.
  unfold update_PTE_Bits. cbn zeta.
  destruct (orb _ _); [| discriminate].
  intros H. injection H as <-.
  eexists _, _. unfold pte_set_ad. reflexivity.
Qed.

(* ===================================================================== *)
(* Testbit machinery (clone of MstatusBits' mw_prep / zn_norm / tb_rw).    *)
(* ===================================================================== *)

Ltac mw_prep :=
  unfold subrange_vec_dec, update_subrange_vec_dec;
  unfold MachineWord.update_slice, MachineWord.slice;
  cbn [get_word];
  rewrite ?autocast_refl;
  unfold to_word_idx, to_word, get_word;
  rewrite ?MachineWord.MachineWord.cast_idx_refl.

Ltac zn_norm :=
  repeat match goal with
  | |- context [MachineWord.Z_idx ?z] => progress reduce_closed (MachineWord.Z_idx z)
  end;
  repeat match goal with
  | |- context [N.add ?a ?b] => progress reduce_closed (N.add a b)
  | |- context [N.sub ?a ?b] => progress reduce_closed (N.sub a b)
  end;
  repeat match goal with
  | |- context [Z.of_N ?a] => progress reduce_closed (Z.of_N a)
  end.

(* one chase step over a goal with a SYMBOLIC bit index: the wrap/shift/
   negative-index rewrites are wrapped in [match goal] so the search
   BACKTRACKS across occurrences until the side condition is provable
   (a plain first-occurrence [rewrite ... by lia] stalls when the first
   occurrence's side condition is the unprovable one).                    *)
Ltac tbk_step :=
  first
    [ rewrite bv_extract_unsigned
    | rewrite bv_concat_unsigned'
    | rewrite Z.sub_0_r
    | rewrite Z.lor_spec
    | match goal with |- context [Z.testbit (bv_wrap ?n ?z) ?i] =>
        rewrite (bv_wrap_spec_low n z i) by lia end
    | match goal with |- context [Z.testbit (bv_wrap ?n ?z) ?i] =>
        rewrite (bv_wrap_spec_high n z i) by lia end
    | match goal with |- context [Z.testbit (Z.shiftl ?z ?m) ?i] =>
        rewrite (Z.shiftl_spec z m i) by lia end
    | match goal with |- context [Z.testbit (Z.shiftr ?z ?m) ?i] =>
        rewrite (Z.shiftr_spec z m i) by lia end
    | match goal with |- context [Z.testbit ?z ?i] =>
        rewrite (Z.testbit_neg_r z i) by lia end
    | rewrite Z.bits_0
    | progress unfold Mk_PTE_Flags
    | progress unfold Mk_PTE_Ext
    | progress zn_norm
    | progress rewrite ?orb_false_l, ?orb_false_r, ?andb_true_l, ?andb_false_l
    ].
Ltac tbk := zn_norm; repeat tbk_step;
            first [ reflexivity | f_equal; lia | lia ].

Lemma bv_eq_testbit (n : N) (y z : bv n) :
  (forall k, 0 <= k < Z.of_N n ->
     Z.testbit (bv_unsigned y) k = Z.testbit (bv_unsigned z) k) ->
  y = z.
Proof.
  intros H. apply bv_eq.
  rewrite <- (bv_wrap_bv_unsigned n y), <- (bv_wrap_bv_unsigned n z).
  apply Z.bits_inj'; intros k Hk.
  destruct (decide (k < Z.of_N n)).
  - rewrite !bv_wrap_spec_low by lia. apply H. lia.
  - rewrite !bv_wrap_spec_high by lia. reflexivity.
Qed.

Ltac tb1 := apply (bv_eq_testbit 1); intros k Hk;
            assert (k = 0) as -> by lia; tbk.

(* ===================================================================== *)
(* The variance laws.                                                     *)
(* ===================================================================== *)

(* every word is an A/D variant of itself (choose its own bits) *)
Lemma pte_set_ad_refl (w : mword 64) :
  exists a d : mword 1, w = pte_set_ad w a d.
Proof.
  exists (subrange_vec_dec w 6 6), (subrange_vec_dec w 7 7).
  unfold pte_set_ad, _update_PTE_Flags_D, _update_PTE_Flags_A, Mk_PTE_Flags.
  mw_prep.
  apply (bv_eq_testbit 64); intros k Hk.
  destruct (decide (k < 6)); [tbk |].
  destruct (decide (k = 6)) as [-> |]; [tbk |].
  destruct (decide (k = 7)) as [-> |]; [tbk |].
  tbk.
Qed.

(* THE BITWISE READING OF [pte_set_ad], from which the three laws below all
   fall out: bit 6 comes from [a], bit 7 from [d], and every other bit is
   the word's own.  Anything that has to know how [pte_set_ad] interacts
   with another bit operation (clearing U, masking the flag byte) states
   itself against this. *)
Lemma pte_set_ad_testbit (z : mword 64) (a d : mword 1) (k : Z) :
  0 <= k < 64 ->
  Z.testbit (bv_unsigned (pte_set_ad z a d)) k
  = (if Z.eqb k 6 then Z.testbit (bv_unsigned a) 0
     else if Z.eqb k 7 then Z.testbit (bv_unsigned d) 0
     else Z.testbit (bv_unsigned z) k).
Proof.
  intros Hk.
  unfold pte_set_ad, _update_PTE_Flags_D, _update_PTE_Flags_A, Mk_PTE_Flags.
  mw_prep.
  destruct (decide (k = 6)) as [->|H6].
  { rewrite Z.eqb_refl. cbv iota. tbk. }
  destruct (decide (k = 7)) as [->|H7].
  { rewrite (proj2 (Z.eqb_neq 7 6) ltac:(lia)), Z.eqb_refl. cbv iota. tbk. }
  rewrite (proj2 (Z.eqb_neq k 6) H6), (proj2 (Z.eqb_neq k 7) H7). cbv iota.
  destruct (decide (k < 8)) as [Hlt|Hge].
  - tbk.
  - tbk.
Qed.

(* the two PTE FIELD extractions, read bit by bit: the PPN sits at 53:10 and
   the extension at 63:54, so a field bit is a word bit at a fixed offset.
   These are what turn [pte_set_ad_testbit] into the two field laws. *)
Local Lemma ppn_field_testbit (x : mword 64) (k : Z) :
  0 <= k < 44 ->
  Z.testbit (bv_unsigned (PPN_of_PTE x)) k = Z.testbit (bv_unsigned x) (k + 10).
Proof.
  intros Hk.
  unfold PPN_of_PTE.
  change (Z.eqb 64 32) with false. cbv iota.
  rewrite !autocast_refl.
  mw_prep. tbk.
Qed.

Local Lemma ext_field_testbit (x : mword 64) (k : Z) :
  0 <= k < 10 ->
  Z.testbit (bv_unsigned (ext_bits_of_PTE x)) k = Z.testbit (bv_unsigned x) (k + 54).
Proof.
  intros Hk.
  unfold ext_bits_of_PTE.
  change (Z.eqb 64 64) with true. cbv iota.
  unfold Mk_PTE_Ext.
  mw_prep. tbk.
Qed.

(* a variant of a variant is a variant of the base (write-backs absorb) *)
Lemma pte_set_ad_absorb (w : mword 64) (a d a' d' : mword 1) :
  pte_set_ad (pte_set_ad w a d) a' d' = pte_set_ad w a' d'.
Proof.
  apply (bv_eq_testbit 64); intros k Hk.
  assert (Hk' : 0 <= k < 64) by (change (Z.of_N 64) with 64 in Hk; lia).
  rewrite !(pte_set_ad_testbit _ _ _ k Hk').
  destruct (Z.eqb k 6); [reflexivity |].
  destruct (Z.eqb k 7); reflexivity.
Qed.

(* the PPN field (bits 53:10) is untouched: variants map to the same page *)
Lemma pte_set_ad_ppn (w : mword 64) (a d : mword 1) :
  PPN_of_PTE (pte_set_ad w a d) = PPN_of_PTE w.
Proof.
  apply (bv_eq_testbit 44); intros k Hk.
  assert (Hk' : 0 <= k < 44) by (change (Z.of_N 44) with 44 in Hk; lia).
  rewrite !(ppn_field_testbit _ k Hk').
  rewrite (pte_set_ad_testbit w a d (k + 10) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (k + 10) 6) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (k + 10) 7) ltac:(lia)).
  cbv iota. reflexivity.
Qed.

(* the extension bits (63:54) are untouched *)
Lemma pte_set_ad_ext (w : mword 64) (a d : mword 1) :
  ext_bits_of_PTE (pte_set_ad w a d) = ext_bits_of_PTE w.
Proof.
  apply (bv_eq_testbit 10); intros k Hk.
  assert (Hk' : 0 <= k < 10) by (change (Z.of_N 10) with 10 in Hk; lia).
  rewrite !(ext_field_testbit _ k Hk').
  rewrite (pte_set_ad_testbit w a d (k + 54) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (k + 54) 6) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (k + 54) 7) ltac:(lia)).
  cbv iota. reflexivity.
Qed.

(* the R/W/X flags are untouched, hence so is leaf-ness *)



Lemma pte_set_ad_flag_G (w : mword 64) (a d : mword 1) :
  _get_PTE_Flags_G (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
  = _get_PTE_Flags_G (Mk_PTE_Flags (subrange_vec_dec w 7 0)).
Proof.
  unfold _get_PTE_Flags_G, Mk_PTE_Flags,
    pte_set_ad, _update_PTE_Flags_D, _update_PTE_Flags_A.
  mw_prep. tb1.
Qed.

(* ... and so are V / R / W / X.  These four are what make the model's
   CLASSIFIERS A/D-stable: [pte_is_non_leaf] reads exactly X, W, R, and
   [pte_is_invalid] reads V, R, W, X plus the extension bits (already
   covered by [pte_set_ad_ext]).  PtTree's [pte_set_ad_leaf] /
   [pte_set_ad_valid] are one rewrite each off these; that stability is
   what lets an A/D-canonicalised page table AGREE with the live one
   (claude-notes/completed/kpt-share.md). *)
Lemma pte_set_ad_flag_V (w : mword 64) (a d : mword 1) :
  _get_PTE_Flags_V (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
  = _get_PTE_Flags_V (Mk_PTE_Flags (subrange_vec_dec w 7 0)).
Proof.
  unfold _get_PTE_Flags_V, Mk_PTE_Flags,
    pte_set_ad, _update_PTE_Flags_D, _update_PTE_Flags_A.
  mw_prep. tb1.
Qed.

Lemma pte_set_ad_flag_R (w : mword 64) (a d : mword 1) :
  _get_PTE_Flags_R (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
  = _get_PTE_Flags_R (Mk_PTE_Flags (subrange_vec_dec w 7 0)).
Proof.
  unfold _get_PTE_Flags_R, Mk_PTE_Flags,
    pte_set_ad, _update_PTE_Flags_D, _update_PTE_Flags_A.
  mw_prep. tb1.
Qed.

Lemma pte_set_ad_flag_W (w : mword 64) (a d : mword 1) :
  _get_PTE_Flags_W (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
  = _get_PTE_Flags_W (Mk_PTE_Flags (subrange_vec_dec w 7 0)).
Proof.
  unfold _get_PTE_Flags_W, Mk_PTE_Flags,
    pte_set_ad, _update_PTE_Flags_D, _update_PTE_Flags_A.
  mw_prep. tb1.
Qed.

Lemma pte_set_ad_flag_X (w : mword 64) (a d : mword 1) :
  _get_PTE_Flags_X (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
  = _get_PTE_Flags_X (Mk_PTE_Flags (subrange_vec_dec w 7 0)).
Proof.
  unfold _get_PTE_Flags_X, Mk_PTE_Flags,
    pte_set_ad, _update_PTE_Flags_D, _update_PTE_Flags_A.
  mw_prep. tb1.
Qed.

(* ===================================================================== *)
(* THE A/D-CANONICAL FORM.  [pte_canon w] zeroes A and D; two words have  *)
(* the same canonical form exactly when each is an A/D variant of the     *)
(* other.  This is the equivalence a SHARED page table is agreed upon     *)
(* modulo: the Svadu write-back moves a leaf word inside its canonical    *)
(* class and never between classes, so the canonical table is INVARIANT   *)
(* (not merely monotone) under it.                                        *)
(* ===================================================================== *)

Definition pte_canon (w : mword 64) : mword 64 :=
  pte_set_ad w (mword_of_int 0) (mword_of_int 0).

Lemma pte_canon_set_ad (w : mword 64) (a d : mword 1) :
  pte_canon (pte_set_ad w a d) = pte_canon w.
Proof. unfold pte_canon. apply pte_set_ad_absorb. Qed.

(* THE INVERSION: equal canonical forms means A/D-variance.  (Used to turn
   an agreement between a hart's SNAPSHOT of the canonical table and the
   live one back into the per-entry variance [tlb_ok_pt] speaks of.) *)
Lemma pte_canon_inv (w w' : mword 64) :
  pte_canon w' = pte_canon w -> exists a d : mword 1, w' = pte_set_ad w a d.
Proof.
  intros H.
  destruct (pte_set_ad_refl w') as (a & d & Hw').
  exists a, d. rewrite Hw'.
  apply (bv_eq_testbit 64); intros k Hk.
  assert (Hk' : 0 <= k < 64) by (change (Z.of_N 64) with 64 in Hk; lia).
  rewrite !(pte_set_ad_testbit _ _ _ k Hk').
  destruct (Z.eqb k 6) eqn:H6; [reflexivity |].
  destruct (Z.eqb k 7) eqn:H7; [reflexivity |].
  apply (f_equal (fun x : mword 64 => Z.testbit (bv_unsigned x) k)) in H.
  unfold pte_canon in H.
  rewrite !(pte_set_ad_testbit _ _ _ k Hk') in H.
  rewrite H6 in H. rewrite H7 in H. cbv iota in H. exact H.
Qed.


(* the V flag reads bit 0 of the word: bit 0 clear means V = 0 (what
   makes the C walk's raw V-bit test agree with the model's classifier) *)
Lemma pte_flags_V_bit0 (w : mword 64) :
  Z.testbit (bv_unsigned w) 0 = false ->
  _get_PTE_Flags_V (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = ('b"0" : mword 1).
Proof.
  intros Hb.
  unfold _get_PTE_Flags_V, Mk_PTE_Flags.
  mw_prep.
  apply (bv_eq_testbit 1). intros k Hk.
  assert (k = 0) as -> by lia.
  zn_norm. repeat tbk_step.
  replace (0 + 0 + 0) with 0 by lia. exact Hb.
Qed.

(* a 1-bit machine word is 0 or 1 *)
Lemma mword1_cases (x : mword 1) :
  x = mword_of_int 0 \/ x = mword_of_int 1.
Proof.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  change (bv_modulus (MachineWord.Z_idx 1)) with 2 in Hr.
  destruct (decide (bv_unsigned x = 0)) as [He|He].
  - left. apply bv_eq.
    cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
    rewrite Z_to_bv_unsigned. rewrite He. reflexivity.
  - right. apply bv_eq.
    cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
    rewrite Z_to_bv_unsigned. change (bv_wrap (MachineWord.Z_idx 1) 1) with 1.
    lia.
Qed.

(* ===================================================================== *)
(* Concrete-flag bridge: [pte_set_ad] on an (abstract-ppn, concrete-flag) *)
(* PTE word rewrites the FLAG constant -- so instances built from         *)
(* [mk_pte]-shaped words (the kernel table) can dispatch every            *)
(* classification/check/update fact per A/D case by [vm_compute],         *)
(* reusing KptPt §12's machinery.                                         *)
(* ===================================================================== *)

(* For a 1-bit value every bit above bit 0 is zero -- lets the A/D
   contributions reduce to [false] SYMBOLICALLY (no case split on a/d). *)
Lemma mword1_testbit_high (a : mword 1) (j : Z) :
  1 <= j -> Z.testbit (bv_unsigned a) j = false.
Proof.
  intros Hj. pose proof (bv_unsigned_in_range _ a) as Hr.
  change (bv_modulus _) with 2 in Hr.
  apply Z.bits_above_log2; [ lia | ].
  apply Z.le_lt_trans with (m := Z.log2 1);
    [ apply Z.log2_le_mono; lia | rewrite Z.log2_1; lia ].
Qed.

(* THE bit-level projection of a zero-extended (p:44 ++ 10-bit-value) word,
   proved ONCE for an arbitrary 10-bit payload [g] and reused for BOTH sides
   of [pte_set_ad_zext_concat] below.  Without this, each of the lemma's two
   [zero_extend'/concat_vec] occurrences had to be unfolded and testbit-chased
   in place -- and [pte_set_ad] itself writes its 8-bit flags back into [w]
   with [update_subrange_vec_dec w 7 0 (...)], mentioning [w] TWICE (once
   directly, once inside the [subrange_vec_dec w 7 0] that reads the old
   flags), so the left-hand side alone re-triggered the chase twice.  Landing
   this projection once cut the call site's cost from ~16s to ~0.5s
   (`coqc -time`, isolated) -- see claude-notes/optimization.md's "unfold
   set_reg is a 3^N tree bomb" entry for the general shape.

   Gotcha this lemma exists to paper over: after [apply (bv_eq_testbit 64)]
   the goal's RIGHT-hand [bv_unsigned] carries the WIDTH literally as [64%N]
   (substituted from [bv_eq_testbit]'s own [n] argument), while a WIDTH that
   arrives via a later [rewrite] (as [pte_set_ad_testbit] below produces on
   the LEFT-hand side) carries it as [MachineWord.Z_idx 64] (the "natural"
   elaboration of [mword 64]) -- definitionally equal, not syntactically
   equal, so a plain [rewrite] with this lemma finds only one of the two
   occurrences.  The call site normalises both to the [64%N] form (with
   [cbn [MachineWord.Z_idx Z.to_N]]) before applying this lemma, and this
   lemma is stated in that same normalised form so ONE [rewrite] finds
   both. *)
(* [tbk]'s stock [tbk_step] never has to cross a [zero_extend]/[Z_to_word]
   (no other lemma in this file unfolds one); [zext_concat_testbit]'s proof
   does, so it needs the two extra projections for THOSE MachineWord
   primitives on top of [tbk_step]'s usual set. *)
Local Ltac zct_step := first [ tbk_step | rewrite bv_zero_extend_unsigned'
                                         | rewrite Z_to_bv_unsigned ].
Local Ltac zct := zn_norm; repeat zct_step;
                   first [ reflexivity | f_equal; lia | lia ].

Local Lemma zext_concat_testbit (p : mword 44) (g : Z) (k : Z) :
  0 <= k < 64 ->
  Z.testbit (@bv_unsigned (64%N) (zero_extend' 64 (concat_vec p (mword_of_int g : mword 10)))) k
  = if Z.ltb k 10 then Z.testbit g k
    else if Z.ltb k 54 then Z.testbit (bv_unsigned p) (k - 10)
    else false.
Proof.
  intros Hk.
  unfold zero_extend', Operators_mwords.zero_extend, extz_vec, concat_vec,
    mword_of_int, Values.mword_of_int.
  cbn [get_word].
  mw_prep.
  unfold MachineWord.MachineWord.zero_extend, MachineWord.MachineWord.concat,
    MachineWord.MachineWord.Z_to_word.
  destruct (decide (k < 10)) as [Hlt10|Hge10].
  - rewrite (proj2 (Z.ltb_lt k 10) Hlt10). zct.
  - rewrite (proj2 (Z.ltb_ge k 10) ltac:(lia)).
    destruct (decide (k < 54)) as [Hlt54|Hge54].
    + rewrite (proj2 (Z.ltb_lt k 54) Hlt54). zct.
    + rewrite (proj2 (Z.ltb_ge k 54) ltac:(lia)). zct.
Qed.

Lemma pte_set_ad_zext_concat (p : mword 44) (f : Z) (a d : mword 1) :
  0 <= f < 1024 ->
  pte_set_ad (zero_extend' 64 (concat_vec p (mword_of_int f : mword 10))) a d
  = zero_extend' 64 (concat_vec p (mword_of_int
      (Z.lor (Z.land f 831)
             (Z.lor (Z.shiftl (bv_unsigned a) 6)
                    (Z.shiftl (bv_unsigned d) 7))) : mword 10)).
Proof.
  intros Hf.
  (* Read both sides bit-by-bit via the two projection lemmas above instead
     of unfolding [pte_set_ad]/[zero_extend'/concat_vec] in place -- see
     [zext_concat_testbit]'s comment for why this is the fix and what the
     [cbn]/[64%N] dance right below is for. *)
  apply (bv_eq_testbit 64); intros k Hk.
  assert (Hk' : 0 <= k < 64) by (change (Z.of_N 64) with 64 in Hk; lia).
  rewrite (pte_set_ad_testbit _ a d k Hk').
  cbn [MachineWord.Z_idx Z.to_N].
  repeat match goal with
  | |- context [Z.testbit (@bv_unsigned (64%N) (zero_extend' 64 (@concat_vec 44 10 p (@mword_of_int 10 ?g)))) k] =>
      rewrite (zext_concat_testbit p g k Hk')
  end.
  (* a,d stay symbolic; [mword1_testbit_high] zeroes their high bits.
     Everything below is now pure Z arithmetic -- no more bitvector
     plumbing, so the case split is cheap regardless of its branch count. *)
  destruct (decide (k = 0)) as [->|];
  [| destruct (decide (k = 1)) as [->|];
  [| destruct (decide (k = 2)) as [->|];
  [| destruct (decide (k = 3)) as [->|];
  [| destruct (decide (k = 4)) as [->|];
  [| destruct (decide (k = 5)) as [->|];
  [| destruct (decide (k = 6)) as [->|];
  [| destruct (decide (k = 7)) as [->|];
  [| destruct (decide (k = 8)) as [->|];
  [| destruct (decide (k = 9)) as [->|];
  [| destruct (decide (k < 54)) ]]]]]]]]]].
  all: repeat (first
     [ match goal with |- context [Z.eqb ?a ?b] => progress reduce_closed (Z.eqb a b) end
     | match goal with |- context [Z.ltb ?a ?b] => progress reduce_closed (Z.ltb a b) end
     | match goal with H : ?kk <> ?c |- context [Z.eqb ?kk ?c] =>
         rewrite (proj2 (Z.eqb_neq kk c) H) end
     | match goal with |- context [Z.ltb ?kk 10] =>
         rewrite (proj2 (Z.ltb_ge kk 10) ltac:(lia)) end
     | progress cbv iota
     | rewrite Z.lor_spec
     | rewrite Z.land_spec
     | match goal with |- context [Z.testbit (Z.shiftl ?z ?m) ?i] =>
         rewrite (Z.shiftl_spec z m i) by lia end
     | match goal with |- context [Z.testbit ?z ?i] =>
         rewrite (Z.testbit_neg_r z i) by lia end
     | rewrite Z.bits_0
     | progress (rewrite (mword1_testbit_high a) by lia)
     | progress (rewrite (mword1_testbit_high d) by lia)
     | progress zn_norm
     | progress rewrite ?orb_false_l, ?orb_false_r, ?andb_true_l,
         ?andb_false_l, ?andb_true_r, ?andb_false_r
     ]).
  all: repeat match goal with
   | |- context [Z.testbit ?x ?i] => progress reduce_closed (Z.testbit x i)
   end.
  all: rewrite ?andb_true_r, ?andb_false_r, ?andb_true_l, ?andb_false_l,
     ?orb_false_l, ?orb_false_r, ?orb_true_l, ?orb_true_r.
  all: first [ reflexivity | f_equal; lia | lia ].
Qed.

(* ===================================================================== *)
(* THE BYTE VIEW OF A/D VARIANCE, AND THE REASSEMBLY (tso-pin-memo §5.5). *)
(*                                                                       *)
(* The canon pin hands the kernel-PT walk one ALLOWED SET per byte of a  *)
(* leaf slot: bytes 1..7 pin to singletons, byte 0 to the four-element   *)
(* A/D class (§2's measurement -- [pte_set_ad] touches bits 6 and 7 and  *)
(* nothing else, so all its variance is inside byte 0).  What the walk   *)
(* owes is a WORD certificate, [pte_canon w = pte_canon leaf0].  These   *)
(* four lemmas are the step between, and they are the whole of it.       *)
(* ===================================================================== *)

(* the byte projection, read bit by bit *)
Lemma nth_byte_testbit {m : N} (w : bv m) (j : nat) (k : Z) :
  0 <= k < 8 ->
  Z.testbit (bv_unsigned (nth_byte w j)) k
  = Z.testbit (bv_unsigned w) (8 * Z.of_nat j + k).
Proof.
  intros Hk. rewrite nth_byte_unsigned.
  rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.shiftr_spec by lia.
  f_equal. rewrite N2Z.inj_mul, nat_N_Z. lia.
Qed.

(* MEMO §2, AT THE BYTE: A/D variance lives entirely in byte 0. *)
Lemma pte_set_ad_nth_byte_high (w : mword 64) (a d : mword 1) (j : nat) :
  (1 <= j < 8)%nat -> nth_byte (pte_set_ad w a d) j = nth_byte w j.
Proof.
  intros Hj. apply (bv_eq_testbit 8). intros k Hk.
  change (Z.of_N 8) with 8 in Hk.
  rewrite !(nth_byte_testbit _ j k ltac:(lia)).
  rewrite (pte_set_ad_testbit w a d (8 * Z.of_nat j + k) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (8 * Z.of_nat j + k) 6) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (8 * Z.of_nat j + k) 7) ltac:(lia)).
  reflexivity.
Qed.

(* THE REASSEMBLY.  A word whose byte 0 is one of the leaf's A/D variants'
   byte 0 and whose bytes 1..7 are the leaf's own IS that variant, hence
   canon-equal to the leaf. *)
Lemma pte_bytes_canon (leaf0 w : mword 64) (a d : mword 1) :
  nth_byte w 0%nat = nth_byte (pte_set_ad leaf0 a d) 0%nat ->
  (forall j : nat, (1 <= j < 8)%nat -> nth_byte w j = nth_byte leaf0 j) ->
  pte_canon w = pte_canon leaf0.
Proof.
  intros H0 Hhi.
  assert (Hall : forall j : nat, (j < 8)%nat ->
            nth_byte w j = nth_byte (pte_set_ad leaf0 a d) j).
  { intros j Hj. destruct j as [|j']; [exact H0 |].
    rewrite (Hhi (S j') ltac:(lia)).
    symmetry. exact (pte_set_ad_nth_byte_high leaf0 a d (S j') ltac:(lia)). }
  assert (Hw : w = pte_set_ad leaf0 a d).
  { apply (bv_eq_of_bytes (n := 8%N)). intros j Hj. apply Hall. lia. }
  rewrite Hw. apply pte_canon_set_ad.
Qed.

(* ...and the form the pin actually hands over: the byte-0 SET membership
   as an existential over the A/D pair (the four-element class of §2). *)
Definition pte_byte0_class (leaf0 : mword 64) (b : bv 8) : Prop :=
  exists a d : mword 1, b = nth_byte (pte_set_ad leaf0 a d) 0%nat.

Lemma pte_bytes_canon_class (leaf0 w : mword 64) :
  pte_byte0_class leaf0 (nth_byte w 0%nat) ->
  (forall j : nat, (1 <= j < 8)%nat -> nth_byte w j = nth_byte leaf0 j) ->
  pte_canon w = pte_canon leaf0.
Proof.
  intros (a & d & H0) Hhi. exact (pte_bytes_canon leaf0 w a d H0 Hhi).
Qed.

(* the class is inhabited by the leaf itself (the mint's obligation) and by
   every write-back variant (the store gate's [vnew ∈ S]) *)
Lemma pte_byte0_class_self (leaf0 : mword 64) :
  pte_byte0_class leaf0 (nth_byte leaf0 0%nat).
Proof.
  destruct (pte_set_ad_refl leaf0) as (a & d & Hw).
  exists a, d. by rewrite <- Hw.
Qed.

Lemma pte_byte0_class_set_ad (leaf0 : mword 64) (a d : mword 1) :
  pte_byte0_class leaf0 (nth_byte (pte_set_ad leaf0 a d) 0%nat).
Proof. by exists a, d. Qed.
