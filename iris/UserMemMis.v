(* UserMemMis.v -- THE MISALIGNED USER-MODE ACCESS.
 *
 * The 2026-08 sail bump moved the misaligned split.  It used to happen at the
 * VMEM level, where every chunk got its own [translateAddr]; it now happens in
 * TWO places, and neither is where it was:
 *
 *   - [vmem_read_addr]/[vmem_write_addr] split only across a PAGE boundary, at
 *     most two ways, and each part gets one translation;
 *   - [checked_mem_read]/[checked_mem_write] split the PHYSICAL access by the
 *     region's Misaligned Atomicity Granule, under a single translation and
 *     with no fault of their own.
 *
 * So the iris-level work is per PAGE, not per chunk: the chunk sequence is a
 * pure [exec] computation ([MemAccessGen]'s physical split kit) whose per-chunk
 * leaves all come from ONE page's ownership.  This file is that layer: the page
 * window facts a misaligned (hence unaligned-window) access needs, the chunk
 * plan derivation, and the two user-level composers the classifier calls.
 *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import UserBits SmodeCore CommonWalk UptTree UserPtTree.
Require Import MemAccessGen UserMemPt UserMemAccess.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §11 The ctz split-derivation: for a misaligned va of width W in {2,4,8}, *)
(*     reduce split_misaligned to the concrete chunk count/size (bytes =    *)
(*     2^ctz(va), N = W/bytes) + per-chunk alignment.  count_trailing_zeros *)
(*     is characterized via a foreach_Z_down' suffix invariant.            *)
(* ===================================================================== *)
Lemma shiftr_mod2_testbit (x i : Z) : 0 <= i ->
  (Z.shiftr x i) mod 2 = Z.b2z (Z.testbit x i).
Proof.
  intros Hi.
  rewrite Zmod_odd.
  rewrite <- Z.bit0_odd.
  rewrite Z.shiftr_spec; [| lia].
  replace (0 + i) with i; [| lia].
  destruct (Z.testbit x i); reflexivity.
Qed.

Lemma access_unsigned_64 (w : mword 64) (i : Z) : 0 <= i ->
  bv_unsigned (access_vec_dec w i) = Z.b2z (Z.testbit (bv_unsigned w) i).
Proof.
  intros Hi.
  unfold access_vec_dec, access_mword_dec.
  unfold MachineWord.MachineWord.slice.
  cbv [get_word].
  rewrite bv_extract_unsigned.
  unfold bv_wrap.
  change (bv_modulus (MachineWord.MachineWord.Z_idx 1)) with 2.
  replace (Z.of_N (MachineWord.MachineWord.Z_idx i)) with i.
  2:{ unfold MachineWord.MachineWord.Z_idx. rewrite Z2N.id; [| lia]. reflexivity. }
  apply shiftr_mod2_testbit; lia.
Qed.

Lemma bvu_moi1 : bv_unsigned (mword_of_int 1 : mword 1) = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma allowed_misaligned_false (a : mword 64) (W : Z) :
  (W = 2 \/ W = 4 \/ W = 8) -> allowed_misaligned a W 0 = false.
Proof.
  intros HW. unfold allowed_misaligned.
  destruct HW as [ -> | [ -> | -> ] ]; reflexivity.
Qed.

Section WithVa.
Variable va : mword 64.

Definition body (i r : Z) : Z :=
  if eq_vec (access_vec_dec va i) (mword_of_int 1) then i else r.

Lemma body_eq (i r : Z) :
  body i r = (if eq_vec (access_vec_dec va i) (mword_of_int 1) then i else r).
Proof. reflexivity. Qed.

Lemma bit_set (i : Z) : 0 <= i ->
  Z.testbit (bv_unsigned va) i = true ->
  eq_vec (access_vec_dec va i) (mword_of_int 1) = true.
Proof.
  intros Hi Hb. apply eq_vec_true_iff. apply bv_eq.
  rewrite access_unsigned_64; [| lia]. rewrite Hb. rewrite bvu_moi1. reflexivity.
Qed.

Lemma bit_clear (i : Z) : 0 <= i ->
  Z.testbit (bv_unsigned va) i = false ->
  eq_vec (access_vec_dec va i) (mword_of_int 1) = false.
Proof.
  intros Hi Hb. apply eq_vec_false_iff. intro Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite access_unsigned_64 in Heq; [| lia]. rewrite Hb in Heq.
  rewrite bvu_moi1 in Heq. simpl in Heq. discriminate.
Qed.

Lemma fold_low_clear : forall (n : nat) (off r : Z),
  (forall j, 0 <= j <= 63 + off -> eq_vec (access_vec_dec va j) (mword_of_int 1) = false) ->
  foreach_Z_down' 63 0 1 off n r body = r.
Proof.
  induction n as [|n IH]; intros off r Hclear.
  - cbn [foreach_Z_down'].
    destruct (sumbool_of_bool (0 <=? 63 + off)); reflexivity.
  - cbn [foreach_Z_down'].
    destruct (sumbool_of_bool (0 <=? 63 + off)) as [Hg|Hg]; [ | reflexivity ].
    apply Z.leb_le in Hg.
    rewrite body_eq.
    rewrite (Hclear (63 + off)); [ | lia ].
    cbn match.
    apply IH. intros j Hj. apply Hclear. lia.
Qed.

Lemma fold_gives_k : forall (n : nat) (off k : Z),
  0 <= k <= 63 + off ->
  n = S (Z.to_nat (63 + off)) ->
  Z.testbit (bv_unsigned va) k = true ->
  (forall j, 0 <= j < k -> Z.testbit (bv_unsigned va) j = false) ->
  forall (r : Z), foreach_Z_down' 63 0 1 off n r body = k.
Proof.
  induction n as [|n IH]; intros off k Hk Hn Hset Hlow r.
  - discriminate Hn.
  - cbn [foreach_Z_down'].
    destruct (sumbool_of_bool (0 <=? 63 + off)) as [Hg|Hg].
    2:{ apply Z.leb_gt in Hg. lia. }
    apply Z.leb_le in Hg.
    injection Hn as Hn'.
    destruct (Z.eq_dec k (63 + off)) as [Hkeq|Hkne].
    + rewrite body_eq.
      rewrite <- Hkeq.
      rewrite (bit_set k ltac:(lia) Hset).
      cbn match.
      apply fold_low_clear.
      intros j Hj. apply bit_clear; [ lia | apply Hlow; lia ].
    + rewrite body_eq.
      apply IH.
      * lia.
      * rewrite Hn'.
        replace (63 + (off - 1)) with (62 + off); [| lia].
        replace (63 + off) with (Z.succ (62 + off)); [| lia].
        rewrite Z2Nat.inj_succ; [| lia]. reflexivity.
      * exact Hset.
      * exact Hlow.
Qed.

Lemma ctz_val (k : Z) :
  0 <= k <= 63 ->
  Z.testbit (bv_unsigned va) k = true ->
  (forall j, 0 <= j < k -> Z.testbit (bv_unsigned va) j = false) ->
  count_trailing_zeros va = k.
Proof.
  intros Hk Hset Hlow.
  transitivity (foreach_Z_down' 63 0 1 0 64 64 body).
  { unfold count_trailing_zeros, foreach_Z_down. reflexivity. }
  apply (fold_gives_k 64 0 k).
  - lia.
  - reflexivity.
  - exact Hset.
  - exact Hlow.
Qed.

Lemma low_bits_zero_mod (m : nat) :
  (forall j, 0 <= j < Z.of_nat m -> Z.testbit (bv_unsigned va) j = false) ->
  bv_unsigned va mod (2 ^ Z.of_nat m) = 0.
Proof.
  intros H.
  apply (proj1 (Z.bits_inj_iff' (bv_unsigned va mod 2 ^ Z.of_nat m) 0)).
  intros i Hi. rewrite Z.bits_0.
  destruct (Z.lt_ge_cases i (Z.of_nat m)) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low; [| lia]. apply H. lia.
  - rewrite Z.mod_pow2_bits_high; [| lia]. reflexivity.
Qed.

Lemma chunk_aligned (bytes j : Z) :
  0 < bytes -> (bytes | 4096) -> 0 <= j < 4096 ->
  bv_unsigned va mod bytes = 0 -> j mod bytes = 0 ->
  is_aligned_vaddr (Virtaddr (add_vec_int va j)) bytes = true.
Proof.
  intros Hb Hdvd Hj Hva Hjm.
  unfold is_aligned_vaddr. apply Z.eqb_eq.
  rewrite (uint_unsigned_n _).
  rewrite Z.rem_mod_nonneg;
    [ | pose proof (bv_unsigned_in_range _ (add_vec_int va j)); lia | exact Hb ].
  rewrite (Znumtheory.Zmod_div_mod bytes 4096 _ Hb ltac:(lia) Hdvd).
  pose proof (uint_add_vec_int_mod4096 va j Hj) as Hm.
  rewrite !(uint_unsigned_n _) in Hm.
  rewrite Hm.
  rewrite <- (Znumtheory.Zmod_div_mod bytes 4096 _ Hb ltac:(lia) Hdvd).
  rewrite Z.add_mod; [| lia].
  rewrite Hva. rewrite Hjm. rewrite Z.add_0_l. apply Zmod_0_l.
Qed.

Lemma exec_split (W k g : Z) (sp : Splittability) (s : mstate) :
  generic_eq sp CannotSplit = false ->
  Z.eqb (Z.rem (uint va) W) 0 = false ->
  allowed_misaligned (subrange_vec_dec va (xlen - 1) 0) W g = false ->
  count_trailing_zeros va = k ->
  Z.min k (count_trailing_zeros (to_bits (Z.add 12 1) W)) = k ->
  Z.eqb W (Z.quot W (pow2 k) * pow2 k) = true ->
  exec (split_misaligned (Physaddr va) W g sp) s
    = Some ((Z.quot W (pow2 k), pow2 k), s).
Proof.
  intros Hsp Hmis Hallow Hctz Hmin Hguard.
  unfold split_misaligned.
  unfold sys_misaligned_byte_by_byte.
  cbn zeta.
  change (bits_of_physaddr (Physaddr va)) with va.
  rewrite Hsp. rewrite Hmis. rewrite Hallow.
  cbn [orb].
  cbn match.
  unfold split_access. cbn zeta.
  rewrite Hctz. rewrite Hmin.
  rewrite Hguard.
  erewrite exec_bind_Some.
  2:{ unfold assert_exp'. cbn match. apply exec_returnm. }
  cbn beta. apply exec_returnm.
Qed.

Lemma assemble (W k bytes num g : Z) (sp : Splittability) (Nn : nat) (s : mstate) :
  generic_eq sp CannotSplit = false ->
  Z.eqb (Z.rem (uint va) W) 0 = false ->
  allowed_misaligned (subrange_vec_dec va (xlen - 1) 0) W g = false ->
  count_trailing_zeros va = k ->
  Z.min k (count_trailing_zeros (to_bits (Z.add 12 1) W)) = k ->
  bytes = pow2 k ->
  num = Z.quot W bytes ->
  Z.of_nat Nn = num ->
  (1 <= Nn)%nat ->
  0 < bytes -> bytes < W -> W <= 8 ->
  (bytes | 4096) ->
  uint (to_bits 64 bytes) = bytes ->
  Z.of_nat Nn * bytes = W ->
  Z.eqb W (num * bytes) = true ->
  exists (N : nat) (bytes0 : Z),
    (1 <= N)%nat /\ Z.of_nat N * bytes0 = W /\ 0 < bytes0 /\ bytes0 <= W /\
    (bytes0 | 4096) /\ uint (to_bits 64 bytes0) = bytes0 /\
    exec (split_misaligned (Physaddr va) W g sp) s = Some ((Z.of_nat N, bytes0), s).
Proof.
  intros Hsp Hmis Hallow Hctz Hmin Hbytes Hnum HN HNn Hbpos HbltW HWle Hdvd Hub HNbW Hguard.
  exists Nn, bytes.
  split; [ exact HNn |].
  split; [ exact HNbW |].
  split; [ exact Hbpos |].
  split; [ lia |].
  split; [ exact Hdvd |].
  split; [ exact Hub |].
  rewrite HN. rewrite Hnum. rewrite Hbytes.
  apply (exec_split W k g sp s Hsp Hmis Hallow Hctz Hmin).
  rewrite <- Hbytes. rewrite <- Hnum. exact Hguard.
Qed.

End WithVa.

(* THE PHYSICAL CHUNK PLAN.  Unconditional: whichever answer the PMA's
   Misaligned Atomicity Granule gave, [split_misaligned] resolves to a chunk
   count and a chunk width that multiply to [W] and that the per-width RAM
   leaves cover.  The two answers are the two branches: the access fits in one
   granule (or the plan is [CannotSplit], or the address is aligned after all)
   and it is ONE operation of the full width; otherwise it is [W / 2^ctz(pa)]
   operations of [2^ctz(pa)] bytes. *)
Lemma split_misaligned_phys_derive (W : Z) (va : mword 64) (g : Z)
    (sp : Splittability) (s : mstate) :
  (W = 2 \/ W = 4 \/ W = 8) ->
  exists (N : nat) (bytes : Z),
    (1 <= N)%nat /\ Z.of_nat N * bytes = W /\ 0 < bytes /\ bytes <= W /\
    (bytes | 4096) /\ uint (to_bits 64 bytes) = bytes /\
    exec (split_misaligned (Physaddr va) W g sp) s = Some ((Z.of_nat N, bytes), s).
Proof.
  intros HW.
  assert (HWpos : 0 < W) by (destruct HW as [ -> | [ -> | -> ] ]; lia).
  (* the [do_not_split] disjunction, once *)
  destruct (generic_eq sp CannotSplit) eqn:Hsp.
  { exists 1%nat, W. repeat split; try lia.
    - destruct HW as [ -> | [ -> | -> ] ];
        [ exists 2048 | exists 1024 | exists 512 ]; reflexivity.
    - destruct HW as [ -> | [ -> | -> ] ]; vm_compute; reflexivity.
    - unfold split_misaligned. cbn zeta.
      change (bits_of_physaddr (Physaddr va)) with va.
      rewrite Hsp. cbn [orb]. cbn match. apply exec_returnm. }
  destruct (Z.eqb (Z.rem (uint va) W) 0) eqn:Halignb.
  { exists 1%nat, W. repeat split; try lia.
    - destruct HW as [ -> | [ -> | -> ] ];
        [ exists 2048 | exists 1024 | exists 512 ]; reflexivity.
    - destruct HW as [ -> | [ -> | -> ] ]; vm_compute; reflexivity.
    - unfold split_misaligned. cbn zeta.
      change (bits_of_physaddr (Physaddr va)) with va.
      rewrite Hsp. rewrite Halignb. cbn [orb]. cbn match. apply exec_returnm. }
  destruct (allowed_misaligned (subrange_vec_dec va (xlen - 1) 0) W g) eqn:Hallow.
  { exists 1%nat, W. repeat split; try lia.
    - destruct HW as [ -> | [ -> | -> ] ];
        [ exists 2048 | exists 1024 | exists 512 ]; reflexivity.
    - destruct HW as [ -> | [ -> | -> ] ]; vm_compute; reflexivity.
    - unfold split_misaligned. cbn zeta.
      change (bits_of_physaddr (Physaddr va)) with va.
      rewrite Hsp. rewrite Halignb. rewrite Hallow. cbn [orb]. cbn match.
      apply exec_returnm. }
  (* the genuine split: chunk width 2^ctz(pa) *)
  assert (Hmodne : bv_unsigned va mod W <> 0).
  { apply Z.eqb_neq in Halignb.
    rewrite (uint_unsigned_n _) in Halignb.
    rewrite Z.rem_mod_nonneg in Halignb;
      [ exact Halignb | pose proof (bv_unsigned_in_range _ va); lia | exact HWpos ]. }
  destruct HW as [ -> | [ -> | -> ] ].
  - destruct (Z.testbit (bv_unsigned va) 0) eqn:E0.
    + apply (assemble va 2 0 1 2 g sp 2%nat s).
      * exact Hsp.
      * exact Halignb.
      * exact Hallow.
      * apply ctz_val; [ lia | exact E0 | intros j Hj; lia ].
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * lia.
      * lia.
      * lia.
      * lia.
      * exists 4096; vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
    + exfalso. apply Hmodne. change 2 with (2 ^ Z.of_nat 1).
      apply low_bits_zero_mod. intros j Hj.
      assert (j = 0) as -> by lia. exact E0.
  - destruct (Z.testbit (bv_unsigned va) 0) eqn:E0.
    + apply (assemble va 4 0 1 4 g sp 4%nat s).
      * exact Hsp.
      * exact Halignb.
      * exact Hallow.
      * apply ctz_val; [ lia | exact E0 | intros j Hj; lia ].
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * lia.
      * lia.
      * lia.
      * lia.
      * exists 4096; vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
    + destruct (Z.testbit (bv_unsigned va) 1) eqn:E1.
      * apply (assemble va 4 1 2 2 g sp 2%nat s).
        -- exact Hsp.
        -- exact Halignb.
        -- exact Hallow.
        -- apply ctz_val; [ lia | exact E1 | intros j Hj; assert (j = 0) as -> by lia; exact E0 ].
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- exists 2048; vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
      * exfalso. apply Hmodne. change 4 with (2 ^ Z.of_nat 2).
        apply low_bits_zero_mod. intros j Hj.
        assert (j = 0 \/ j = 1) as [ -> | -> ] by lia; [ exact E0 | exact E1 ].
  - destruct (Z.testbit (bv_unsigned va) 0) eqn:E0.
    + apply (assemble va 8 0 1 8 g sp 8%nat s).
      * exact Hsp.
      * exact Halignb.
      * exact Hallow.
      * apply ctz_val; [ lia | exact E0 | intros j Hj; lia ].
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * lia.
      * lia.
      * lia.
      * lia.
      * exists 4096; vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
      * vm_compute; reflexivity.
    + destruct (Z.testbit (bv_unsigned va) 1) eqn:E1.
      * apply (assemble va 8 1 2 4 g sp 4%nat s).
        -- exact Hsp.
        -- exact Halignb.
        -- exact Hallow.
        -- apply ctz_val; [ lia | exact E1 | intros j Hj; assert (j = 0) as -> by lia; exact E0 ].
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- exists 2048; vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
        -- vm_compute; reflexivity.
      * destruct (Z.testbit (bv_unsigned va) 2) eqn:E2.
        -- apply (assemble va 8 2 4 2 g sp 2%nat s).
           ++ exact Hsp.
           ++ exact Halignb.
           ++ exact Hallow.
           ++ apply ctz_val; [ lia | exact E2
              | intros j Hj; assert (j = 0 \/ j = 1) as [ -> | -> ] by lia; [ exact E0 | exact E1 ] ].
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ exists 1024; vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
           ++ vm_compute; reflexivity.
        -- exfalso. apply Hmodne. change 8 with (2 ^ Z.of_nat 3).
           apply low_bits_zero_mod. intros j Hj.
           assert (j = 0 \/ j = 1 \/ j = 2) as [ -> | [ -> | -> ] ] by lia;
             [ exact E0 | exact E1 | exact E2 ].
Qed.



Lemma pow2_le8 (b : Z) : 0 < b -> b < 8 -> (b | 4096) -> b = 1 \/ b = 2 \/ b = 4.
Proof.
  intros Hpos Hlt Hdvd.
  assert (Hb : b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7) by lia.
  destruct Hdvd as [q Hq].
  destruct Hb as [H|[H|[H|[H|[H|[H|H]]]]]]; subst b;
    try (left; reflexivity); try (right; left; reflexivity);
    try (right; right; reflexivity); exfalso; lia.
Qed.

Lemma pow2_le8' (b : Z) : 0 < b -> b <= 8 -> (b | 4096) ->
  b = 1 \/ b = 2 \/ b = 4 \/ b = 8.
Proof.
  intros Hpos Hle Hdvd.
  destruct (Z.eq_dec b 8) as [He8|Hne]; [ subst b; tauto | ].
  destruct (pow2_le8 b Hpos ltac:(lia) Hdvd) as [He|[He|He]]; subst b; tauto.
Qed.

(* ===================================================================== *)
(* §b THE PAGE WINDOW.  A misaligned access is by definition not aligned   *)
(*    to its width, so nothing about it is a "k-aligned window" -- but      *)
(*    every window fact the ownership side needs only ever used alignment   *)
(*    to conclude that the access stays inside ONE page.  [in_one_page] is  *)
(*    that conclusion, taken as the primitive; the aligned case is a        *)
(*    corollary and the page-straddling case is its negation.               *)
(* ===================================================================== *)

Definition in_one_page (a : mword 64) (w : Z) : Prop :=
  bv_unsigned a mod 4096 + w <= 4096.

Lemma in_one_page_aligned (a : mword 64) (w : Z) :
  0 < w -> (w | 4096) -> is_aligned_vaddr (Virtaddr a) w = true -> in_one_page a w.
Proof.
  intros Hw Hdvd Hal.
  unfold in_one_page.
  pose proof (off_bound_div a w Hw Hdvd Hal) as Hb.
  rewrite uint_subrange11 in Hb. rewrite (uint_unsigned_n _) in Hb. exact Hb.
Qed.

(* the address arithmetic: an access that stays in a page cannot wrap 2^64,
   and its last byte has the same page number as its first *)
Lemma in_one_page_room (a : mword 64) (w : Z) :
  0 < w -> in_one_page a w -> bv_unsigned a + (w - 1) < 2 ^ 64.
Proof.
  intros Hw Hp. unfold in_one_page in Hp.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  assert (H64 : (2:Z) ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite H64 in Hr. rewrite H64.
  assert (Hdm : bv_unsigned a = 4096 * (bv_unsigned a / 4096) + bv_unsigned a mod 4096)
    by (apply Z.div_mod; lia).
  assert (Hq : bv_unsigned a / 4096 < 4503599627370496)
    by (apply Z.div_lt_upper_bound; lia).
  assert (Hmnn : 0 <= bv_unsigned a mod 4096) by (apply Z.mod_pos_bound; lia).
  lia.
Qed.

Lemma z_shiftr12_stable_page (u w : Z) :
  0 <= u -> 0 < w -> u mod 4096 + w <= 4096 ->
  Z.shiftr u 12 = Z.shiftr (u + (w - 1)) 12.
Proof.
  intros Hu Hw Hp.
  assert (Hd : Z.shiftr u 12 = u / 4096) by (apply Z.shiftr_div_pow2; lia).
  assert (Hd' : Z.shiftr (u + (w - 1)) 12 = (u + (w - 1)) / 4096)
    by (apply Z.shiftr_div_pow2; lia).
  rewrite Hd. rewrite Hd'.
  assert (Hge : 0 <= u mod 4096) by (apply Z.mod_pos_bound; lia).
  assert (Hsplit : u = 4096 * (u / 4096) + u mod 4096) by (apply Z.div_mod; lia).
  assert (Hq : (4096 * (u / 4096) + (u mod 4096 + (w - 1))) / 4096 = u / 4096).
  { rewrite (Z.mul_comm 4096 (u / 4096)).
    assert (Hda : ((u / 4096) * 4096 + (u mod 4096 + (w - 1))) / 4096
                  = u / 4096 + (u mod 4096 + (w - 1)) / 4096)
      by (apply Z.div_add_l; lia).
    rewrite Hda.
    assert (Hs0 : (u mod 4096 + (w - 1)) / 4096 = 0) by (apply Z.div_small; lia).
    rewrite Hs0. lia. }
  assert (Heq : u + (w - 1) = 4096 * (u / 4096) + (u mod 4096 + (w - 1))) by lia.
  rewrite Heq. rewrite Hq. reflexivity.
Qed.

Lemma exec_split_on_page_boundary_intra (a : mword 64) (w : Z) s :
  0 < w -> in_one_page a w ->
  exec (split_on_page_boundary a w) s = Some ((w, 0), s).
Proof.
  intros Hpos Hp.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  destruct Hr as [Hr0 Hr1].
  pose proof (in_one_page_room a w Hpos Hp) as Hnw.
  assert (Hwle : w <= 4096).
  { unfold in_one_page in Hp.
    pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)). lia. }
  assert (Hsub : bv_unsigned (sub_vec_int (add_vec_int a w) 1) = bv_unsigned a + (w - 1)).
  { unfold sub_vec_int, add_vec_int.
    rewrite sub_vec64_unsigned. rewrite add_vec64_unsigned.
    rewrite !moi64_unsigned.
    assert (Hww : bv_wrap 64 w = w)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    assert (Hw1 : bv_wrap 64 1 = 1)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    rewrite Hww. rewrite Hw1.
    rewrite bv_wrap_sub_idemp_l.
    assert (Hsimp : bv_unsigned a + w - 1 = bv_unsigned a + (w - 1)) by (clear; lia).
    rewrite Hsimp.
    apply bv_wrap_small. rewrite bv_modulus64.
    assert (H64 : (2:Z) ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
    rewrite <- H64. split; [ clear - Hr0 Hpos; lia | exact Hnw ]. }
  unfold split_on_page_boundary.
  assert (Hintra : eq_vec (and_vec a (update_subrange_vec_dec ((ones 64) : bits 64)
                                        (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1)))))
                          (and_vec (sub_vec_int (add_vec_int a w) 1)
                                   (update_subrange_vec_dec ((ones 64) : bits 64)
                                      (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1))))) = true).
  { apply eq_vec_true_iff. apply bv_eq.
    rewrite !and_vec64_unsigned. rewrite page_mask64_val.
    rewrite Hsub.
    assert (Hnn : 0 <= bv_unsigned a + (w - 1)) by (clear - Hr0 Hpos; lia).
    rewrite (z_land_pagemask (bv_unsigned a) Hr0 Hr1).
    rewrite (z_land_pagemask (bv_unsigned a + (w - 1)) Hnn Hnw).
    rewrite <- (z_shiftr12_stable_page (bv_unsigned a) w Hr0 Hpos Hp). reflexivity. }
  rewrite Hintra. apply exec_returnm.
Qed.

(* the page window, at an arbitrary in-page offset *)
Lemma u_walk_pa_window_page (pte0 va : mword 64) (k : Z) (j : nat) :
  0 < k -> in_one_page va k -> (j < Z.to_nat k)%nat ->
  pa_add (u_walk_pa pte0 va) j = u_walk_pa pte0 (add_vec_int va (Z.of_nat j)).
Proof.
  intros Hk Hp Hj. unfold in_one_page in Hp.
  assert (Hk0 : 0 <= k) by lia.
  assert (Hjk : Z.of_nat j < k).
  { pose proof (Z2Nat.id k Hk0) as Hid.
    apply Nat2Z.inj_lt in Hj. lia. }
  apply pa_window.
  rewrite uint_subrange11. rewrite (uint_unsigned_n _ va). lia.
Qed.

(* ===================================================================== *)
(* §c THE MISALIGNED [pmaCheck].  Same walk as [RiscvExtras.pma_ok_peel],  *)
(*    but the tail keeps whatever PLAN the Misaligned Atomicity Granule    *)
(*    check answered instead of pinning [pma_ok_aligned]: at a misaligned  *)
(*    address the answer depends on the granule, and this development      *)
(*    never needs to know which one it got.                                *)
(* ===================================================================== *)

Lemma exec_pma_misaligned_exception_load (pma : PMA) s :
  (pma.(PMA_misaligned_exceptions)).(PMAMisalignedExceptions_load_store) = None ->
  exec (pma_misaligned_exception pma (Load Data)) s = Some (None, s).
Proof.
  intro H. unfold pma_misaligned_exception. cbn match. rewrite H. apply exec_returnM.
Qed.

Lemma exec_pma_misaligned_exception_store (pma : PMA) s :
  (pma.(PMA_misaligned_exceptions)).(PMAMisalignedExceptions_load_store) = None ->
  exec (pma_misaligned_exception pma (Store Data)) s = Some (None, s).
Proof.
  intro H. unfold pma_misaligned_exception. cbn match. rewrite H. apply exec_returnM.
Qed.

Lemma exec_mag_pma_check_plan (pma : PMA) (acc : MemoryAccessType mem_payload)
    (paddr : physaddr) (width : Z) (b : bool) s :
  exec (is_mag_applicable_access acc width) s = Some (b, s) ->
  exec (pma_misaligned_exception pma acc) s = Some (None, s) ->
  exists (sp : Splittability) (g : Z),
    exec (mag_pma_check pma acc paddr width) s = Some (Ok (sp, g), s).
Proof.
  intros Hma Hme.
  unfold mag_pma_check.
  rewrite (exec_bind_Some _ _ _ _ _ Hma).
  destruct (orb (is_aligned_paddr paddr width)
                (andb b (within_pma_mag pma paddr width (is_vector_access acc)))) eqn:E.
  - exists CannotSplit, 0. apply exec_returnM.
  - rewrite (exec_bind_Some _ _ _ _ _ Hme). cbn match.
    destruct b; destruct (mag_of_pma pma (is_vector_access acc)) as [mag|];
      cbn match; eexists; eexists; apply exec_returnM.
Qed.

Ltac pma_plan_peel Hmatch Hfield Hmag :=
  unfold pmaCheck; rewrite exec_catch_early_return;
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg pma_regions _)); cbn beta;
  rewrite Hmatch;
  cbn [PMA_Region_attributes] in Hfield |- *;
  cbn match;
  rewrite execR_bind; rewrite execR_returnR; cbn match beta;
  cbn [Riscv.rv64d.not negb];
  rewrite execR_bind;
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ _)); cbn beta;
  rewrite execR_returnR; cbn match beta;
  rewrite Hfield; cbn [Riscv.rv64d.not negb];
  rewrite (execR_liftR_seq _ _ _ _ _ Hmag);
  cbn beta; cbn match; rewrite execR_returnR; reflexivity.

Lemma exec_pmaCheck_ram_load_plan (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_misaligned_exceptions)).(PMAMisalignedExceptions_load_store) = None ->
  exists plan : Phys_Mem_Access_Info,
    exec (pmaCheck (Physaddr addr) k (Load Data) pbmt false) s = Some (Ok plan, s).
Proof.
  intros Hmatch Hread Hme.
  destruct (exec_mag_pma_check_plan (override_PMA (PMA_Region_attributes region) pbmt)
              (Load Data) (Physaddr addr) k _ s
              (exec_is_mag_applicable_load_data k s)
              (exec_pma_misaligned_exception_load _ s Hme)) as (sp & g & Hmag).
  exists {| Phys_Mem_Access_Info_splittable := sp;
            Phys_Mem_Access_Info_granule_size_exp := g |}.
  destruct region as [rbase rsize rattr rdtree].
  pma_plan_peel Hmatch Hread Hmag.
Qed.

Lemma exec_pmaCheck_ram_store_plan (k : Z) (addr : mword 64) (pbmt : page_based_mem_type)
    (region : PMA_Region) s :
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_misaligned_exceptions)).(PMAMisalignedExceptions_load_store) = None ->
  exists plan : Phys_Mem_Access_Info,
    exec (pmaCheck (Physaddr addr) k (Store Data) pbmt false) s = Some (Ok plan, s).
Proof.
  intros Hmatch Hwrite Hme.
  destruct (exec_mag_pma_check_plan (override_PMA (PMA_Region_attributes region) pbmt)
              (Store Data) (Physaddr addr) k _ s
              (exec_is_mag_applicable_store_data k s)
              (exec_pma_misaligned_exception_store _ s Hme)) as (sp & g & Hmag).
  exists {| Phys_Mem_Access_Info_splittable := sp;
            Phys_Mem_Access_Info_granule_size_exp := g |}.
  destruct region as [rbase rsize rattr rdtree].
  pma_plan_peel Hmatch Hwrite Hmag.
Qed.

(* ===================================================================== *)
(* §d THE PAGE-WINDOW OWNERSHIP FACTS.  [udata_read_word_g] needed the      *)
(*    window to be width-ALIGNED, and used that only to know it stayed      *)
(*    inside the page; these are the same facts over [in_one_page].  They   *)
(*    also drop the VALUE: a misaligned access's value is existential all   *)
(*    the way up, so all that is needed is that the bytes are THERE.        *)
(* ===================================================================== *)

(* [read_bytes] succeeds as soon as every byte of the window is present. *)
Lemma read_bytes_is_Some mm pa n :
  (forall j : nat, (N.of_nat j < n)%N -> is_Some (mm !! RiscvModelBytes.pa_add pa j)) ->
  read_bytes mm pa n <> None.
Proof.
  intros Hb. unfold read_bytes.
  case_match eqn:Hm; [ congruence | exfalso ].
  apply mapM_None_1, Exists_exists in Hm.
  destruct Hm as (j & Hj & Hnone).
  apply in_seq in Hj.
  destruct (Hb j ltac:(lia)) as [b Hbj].
  rewrite Hbj in Hnone. congruence.
Qed.

(* The per-chunk read value, as a FUNCTION of the state rather than an
   existential: [exec] is a function, so the value a successful [read_ram]
   yields is determined, and reading it back out is what lets the physical
   split loop be instantiated (a [nat]-indexed existential cannot be turned
   into the [nat -> mword _] the loop wants). *)
Definition ram_chunk (rk : read_kind) (a : mword 64) (bytes : Z) (meta : bool)
    (s : mstate) : mword (8 * bytes) :=
  match exec (read_ram rk (Physaddr a) bytes meta) s with
  | Some (v, _, _) => v
  | None => zeros' (8 * bytes)
  end.

Lemma exec_read_ram_chunk (rk : read_kind) (a : mword 64) (bytes : Z) (meta : bool) s :
  (exists v, exec (read_ram rk (Physaddr a) bytes meta) s = Some ((v, tt), s)) ->
  exec (read_ram rk (Physaddr a) bytes meta) s
    = Some ((ram_chunk rk a bytes meta s, tt), s).
Proof. intros [v Hv]. unfold ram_chunk. rewrite Hv. reflexivity. Qed.

Section MisWindow.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma udata_window_facts (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (k : Z) (σ : mstate) :
    0 < k ->
    um !! svpn_of va = Some w ->
    udata_cov um data ->
    in_one_page va k ->
    gen_heap_interp σ.(mem) -∗ udata_own data -∗
    ⌜forall j : nat, (j < Z.to_nat k)%nat ->
       is_Some (σ.(mem) !! pa_add (u_walk_pa w va) j)
       /\ addr_is_ram (pa_add (u_walk_pa w va) j)
       /\ pa_add (u_walk_pa w va) j ∈ data⌝.
  Proof.
    iIntros (Hk Hl Hcov Hp) "Hmem Hdata".
    iDestruct "Hdata" as (dm) "[%Hdom Hbytes]".
    set (pa := u_walk_pa w va).
    assert (Hin : forall j : nat, (j < Z.to_nat k)%nat -> pa_add pa j ∈ data).
    { intros j Hj. unfold pa.
      rewrite (u_walk_pa_window_page w va k j Hk Hp Hj).
      exact (Hcov (svpn_of va) w (add_vec_int va (Z.of_nat j)) Hl). }
    iAssert (⌜forall (a : Arch.pa) (b : bv 8), dm !! a = Some b ->
               σ.(mem) !! a = Some b /\ addr_is_ram a⌝)%I as %Hmm.
    { iIntros (a b Hab).
      iDestruct (big_sepM_lookup_acc _ _ _ _ Hab with "Hbytes") as "[Hab Hrest]".
      iDestruct (phys_valid with "Hmem Hab") as %Hv.
      iDestruct (phys_ram with "Hab") as %Hr.
      iPureIntro. exact (conj Hv Hr). }
    iPureIntro. intros j Hj.
    assert (Hd : pa_add pa j ∈ dom dm) by (rewrite Hdom; apply Hin; exact Hj).
    apply elem_of_dom in Hd. destruct Hd as [b Hb].
    destruct (Hmm _ _ Hb) as [Hv Hr].
    split; [ exists b; exact Hv | split; [ exact Hr | apply Hin; exact Hj ] ].
  Qed.

  Lemma udata_own_store_window (data : gset Arch.pa) (pa : Arch.pa) (k : Z)
      {wd : N} (v : bv wd) (m : _) :
    (forall j : nat, (j < Z.to_nat k)%nat -> pa_add pa j ∈ data) ->
    gen_heap_interp (hG := riscv_memGS) m -∗ udata_own data ==∗
    gen_heap_interp (hG := riscv_memGS) (write_bytes m pa (Z.to_N k) v) ∗ udata_own data.
  Proof.
    intros Hin. unfold write_bytes. rewrite Z_N_nat.
    apply (udata_own_upd data (seq 0 (Z.to_nat k)) pa v m).
    intros j Hj. apply Hin. apply elem_of_seq in Hj. lia.
  Qed.

End MisWindow.

(* ===================================================================== *)
(* §e THE PHYSICAL SIDE of a misaligned in-page access.  Every chunk the    *)
(*    plan asks for lies inside the access's own window, so the PMP grant,  *)
(*    the (false) MMIO test and the RAM leaf are the same three facts the   *)
(*    aligned path uses -- at the chunk's address and width instead of the  *)
(*    access's.  Nothing here is iris: the page's RAM/present facts come in *)
(*    as a plain window hypothesis.                                        *)
(* ===================================================================== *)

Lemma pa_add_chunk (pa : mword 64) (k : nat) (bytes : Z) :
  0 <= bytes -> add_vec_int pa (Z.of_nat k * bytes) = pa_add pa (k * Z.to_nat bytes).
Proof.
  intros Hb. unfold pa_add. f_equal.
  rewrite Nat2Z.inj_mul. rewrite Z2Nat.id; [reflexivity | exact Hb].
Qed.

Lemma pa_add_bump2 (p : mword 64) (d n : nat) : pa_add (pa_add p d) n = pa_add p (d + n).
Proof.
  unfold pa_add, add_vec_int. apply bv_eq.
  rewrite !add_vec64_unsigned. rewrite !moi64_unsigned.
  rewrite !bv_wrap_add_idemp_r. rewrite !bv_wrap_add_idemp_l. f_equal.
  rewrite Nat2Z.inj_add. ring.
Qed.

Lemma ws_seq_all_true (N : nat) : ws_seq (fun _ => true) N = true.
Proof. induction N as [|N IH]; [reflexivity | cbn [ws_seq]; rewrite IH; reflexivity]. Qed.

Section MisPhys.
  Context (pa : mword 64) (W : Z) (s : mstate).
  Context (HW : W = 2 \/ W = 4 \/ W = 8).
  Context (HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR).
  Context (Hord : zopz0zKzJ_u (zeros' 64)
                    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false).
  Context (Hcovp : (ram_base + ram_size
                    <= uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) * 4)%Z).
  Context (Hhtif : register_lookup htif_tohost_base s.(sregs) = None).
  Context (Hall : pma_allows_all (register_lookup pma_regions s.(sregs))).
  Context (Hwin : forall j : nat, (j < Z.to_nat W)%nat -> addr_is_ram (pa_add pa j)).

  Local Lemma HWpos : 0 < W.
  Proof. destruct HW as [ -> | [ -> | -> ] ]; lia. Qed.
  Local Lemma HWle : W <= 8.
  Proof. destruct HW as [ -> | [ -> | -> ] ]; lia. Qed.

  (* offset arithmetic: chunk [k] of [bytes] at byte [j] is offset
     [k*bytes + j] of the access, and that stays inside it *)
  Local Lemma chunk_off (bytes : Z) (N k j : nat) :
    0 < bytes -> Z.of_nat N * bytes = W -> (k < N)%nat -> (j < Z.to_nat bytes)%nat ->
    (k * Z.to_nat bytes + j < Z.to_nat W)%nat.
  Proof.
    intros Hb Hw Hk Hj.
    assert (HbN : Z.to_nat W = (N * Z.to_nat bytes)%nat).
    { rewrite <- Hw. rewrite Z2Nat.inj_mul; [| lia | lia]. rewrite Nat2Z.id. reflexivity. }
    rewrite HbN. nia.
  Qed.

  Local Lemma chunk_ram (bytes : Z) (N k j : nat) :
    0 < bytes -> Z.of_nat N * bytes = W -> (k < N)%nat -> (j < Z.to_nat bytes)%nat ->
    addr_is_ram (pa_add (add_vec_int pa (Z.of_nat k * bytes)) j).
  Proof.
    intros Hb Hw Hk Hj.
    rewrite (pa_add_chunk pa k bytes ltac:(lia)).
    rewrite pa_add_bump2.
    exact (Hwin _ (chunk_off bytes N k j Hb Hw Hk Hj)).
  Qed.

  (* the three per-chunk leaves *)
  Local Lemma chunk_pmp (acc : MemoryAccessType mem_payload) (bytes : Z) (N k : nat) :
    (acc = Load Data /\ eq_vec (_get_Pmpcfg_ent_R
        (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true) \/
    (acc = Store Data /\ eq_vec (_get_Pmpcfg_ent_W
        (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true) ->
    0 < bytes -> bytes <= 8 -> uint (to_bits 64 bytes) = bytes ->
    Z.of_nat N * bytes = W -> (k < N)%nat ->
    exec (pmpCheck (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes acc User) s
      = Some (None, s).
  Proof.
    intros Hacc Hb Hb8 Hbu Hw Hk.
    assert (Hlast : (Z.to_nat bytes - 1 < Z.to_nat bytes)%nat) by lia.
    assert (Hr0 : addr_is_ram (add_vec_int pa (Z.of_nat k * bytes))).
    { rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
      exact (chunk_ram bytes N k 0%nat Hb Hw Hk ltac:(lia)). }
    assert (HrL : addr_is_ram (pa_add (add_vec_int pa (Z.of_nat k * bytes))
                                 (Z.to_nat bytes - 1)))
      by exact (chunk_ram bytes N k (Z.to_nat bytes - 1)%nat Hb Hw Hk Hlast).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
              (uint (add_vec_int pa (Z.of_nat k * bytes))) (uint (to_bits 64 bytes)) = PMP_Match)
      by exact (ram_fetch_pmp _ _ bytes (Z.to_nat bytes - 1)%nat Hb Hb8 Hbu
                  ltac:(lia) Hr0 HrL Hcovp).
    destruct Hacc as [ [ Ha HRp ] | [ Ha HWp ] ]; subst acc.
    - exact (exec_pmpCheck_user_grant_load _ bytes s HA Hord Hrange HRp).
    - exact (exec_pmpCheck_user_grant_store _ bytes s HA Hord Hrange HWp).
  Qed.

  Local Lemma chunk_mmio_r (bytes : Z) (N k : nat) :
    0 < bytes -> Z.of_nat N * bytes = W -> (k < N)%nat ->
    exec (within_mmio_readable (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes) s
      = Some (false, s).
  Proof.
    intros Hb Hw Hk.
    assert (Hr0 : addr_is_ram (add_vec_int pa (Z.of_nat k * bytes))).
    { rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
      exact (chunk_ram bytes N k 0%nat Hb Hw Hk ltac:(lia)). }
    unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _
               (within_clint_false _ bytes s (addr_is_ram_not_in_clint _ Hr0) Hb)). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _
               (within_sig_false _ bytes s (addr_is_ram_not_in_sig _ Hr0) Hb)). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false _ bytes s Hhtif)). cbn match.
    reflexivity.
  Qed.

  Local Lemma chunk_mmio_w (bytes : Z) (N k : nat) :
    0 < bytes -> Z.of_nat N * bytes = W -> (k < N)%nat ->
    exec (within_mmio_writable (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes) s
      = Some (false, s).
  Proof.
    intros Hb Hw Hk.
    assert (Hr0 : addr_is_ram (add_vec_int pa (Z.of_nat k * bytes))).
    { rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
      exact (chunk_ram bytes N k 0%nat Hb Hw Hk ltac:(lia)). }
    unfold within_mmio_writable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _
               (within_clint_false _ bytes s (addr_is_ram_not_in_clint _ Hr0) Hb)). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _
               (within_sig_false _ bytes s (addr_is_ram_not_in_sig _ Hr0) Hb)). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false _ bytes s Hhtif)). cbn match.
    reflexivity.
  Qed.


  (* ---- the misaligned in-page READ, at the full width ---- *)
  Lemma exec_mem_read_mis_U :
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    eq_vec (_get_Pmpcfg_ent_R
              (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    (forall j : nat, (j < Z.to_nat W)%nat -> is_Some (s.(mem) !! pa_add pa j)) ->
    exists dv : mword (8 * W),
      exec (mem_read (Load Data) PBMT_PMA (Physaddr pa) W false false false) s
        = Some (Ok dv, s).
  Proof.
    intros Hmprv Hcp HRp Hpres.
    pose proof HWpos as Hpos. pose proof HWle as Hle.
    assert (Hr0 : addr_is_ram pa).
    { rewrite <- (pa_add_0 pa). apply Hwin. lia. }
    assert (HrL : addr_is_ram (pa_add pa (Z.to_nat W - 1))) by (apply Hwin; lia).
    destruct (pma_all_ram Hall pa W
                (pma_access_ram_at pa W (Z.to_nat W - 1)%nat ltac:(lia) Hr0 HrL
                   (pma_width_le W 8 Hpos Hle eq_refl)))
      as (region & Hpmam & _ & Hrd & _ & _ & _ & _ & Hmisx).
    destruct (exec_pmaCheck_ram_load_plan W pa PBMT_PMA region s Hpmam Hrd Hmisx)
      as (plan & Hpma).
    assert (Hcpp : exec (check_pma_with_pmp_priority (Load Data) PBMT_PMA User
                           (Physaddr pa) W false) s = Some (Ok plan, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _ Hpma). cbn match. apply exec_returnM. }
    destruct (split_misaligned_phys_derive W pa
                (Phys_Mem_Access_Info_granule_size_exp plan)
                (Phys_Mem_Access_Info_splittable plan) s HW)
      as (N & bytes & HN & Hwidth & Hbpos & Hble & Hbdvd & Hbuint & Hsplit).
    assert (Hb8 : bytes <= 8) by lia.
    assert (Hpmp : forall k, (k < N)%nat ->
              exec (pmpCheck (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes
                      (Load Data) User) s = Some (None, s)).
    { intros k Hk.
      exact (chunk_pmp (Load Data) bytes N k (or_introl (conj eq_refl HRp))
               Hbpos Hb8 Hbuint Hwidth Hk). }
    assert (Hmmio : forall k, (k < N)%nat ->
              exec (within_mmio_readable
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes) s
              = Some (false, s))
      by (intros k Hk; exact (chunk_mmio_r bytes N k Hbpos Hwidth Hk)).
    assert (Hramc : forall k, (k < N)%nat ->
              exec (read_ram Read_plain
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes false) s
              = Some ((ram_chunk Read_plain (add_vec_int pa (Z.of_nat k * bytes))
                         bytes false s, tt), s)).
    { intros k Hk. apply exec_read_ram_chunk.
      apply exec_read_ram_plain_gen.
      - apply addr_is_ram_not_dev.
        rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
        exact (chunk_ram bytes N k 0%nat Hbpos Hwidth Hk ltac:(lia)).
      - apply read_bytes_is_Some. intros j Hj.
        rewrite (pa_add_chunk pa k bytes ltac:(lia)). rewrite pa_add_bump2.
        apply Hpres. exact (chunk_off bytes N k j Hbpos Hwidth Hk ltac:(lia)). }
    assert (Heff : exec (effectivePrivilege (Load Data)
                           (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (User, s)).
    { rewrite <- Hcp. apply exec_effectivePrivilege_mprv0. exact Hmprv. }
    pose proof (exec_checked_mem_read_split (Load Data) PBMT_PMA User pa W bytes N
                  false false false false Read_plain
                  (fun k => ram_chunk Read_plain (add_vec_int pa (Z.of_nat k * bytes))
                              bytes false s) s HN Hpmp Hmmio Hramc plan Hcpp Hsplit
                  ltac:(unfold read_kind_of_flags; apply exec_returnM)) as Hchk.
    eexists.
    exact (exec_mem_read_of_checked_plain (Load Data) PBMT_PMA pa W _ User s Heff Hchk).
  Qed.

  (* ---- the misaligned in-page effective-address announcement ---- *)
  Lemma exec_mem_write_ea_mis_U :
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    eq_vec (_get_Pmpcfg_ent_W
              (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    exec (mem_write_ea (Physaddr pa) W (Store Data) PBMT_PMA false false false) s
      = Some (Ok tt, s).
  Proof.
    intros Hmprv Hcp HWp.
    pose proof HWpos as Hpos. pose proof HWle as Hle.
    assert (Hr0 : addr_is_ram pa).
    { rewrite <- (pa_add_0 pa). apply Hwin. lia. }
    assert (HrL : addr_is_ram (pa_add pa (Z.to_nat W - 1))) by (apply Hwin; lia).
    destruct (pma_all_ram Hall pa W
                (pma_access_ram_at pa W (Z.to_nat W - 1)%nat ltac:(lia) Hr0 HrL
                   (pma_width_le W 8 Hpos Hle eq_refl)))
      as (region & Hpmam & _ & _ & Hwr & _ & _ & _ & Hmisx).
    destruct (exec_pmaCheck_ram_store_plan W pa PBMT_PMA region s Hpmam Hwr Hmisx)
      as (plan & Hpma).
    assert (Hcpp : exec (check_pma_with_pmp_priority (Store Data) PBMT_PMA User
                           (Physaddr pa) W false) s = Some (Ok plan, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _ Hpma). cbn match. apply exec_returnM. }
    destruct (split_misaligned_phys_derive W pa
                (Phys_Mem_Access_Info_granule_size_exp plan)
                (Phys_Mem_Access_Info_splittable plan) s HW)
      as (N & bytes & HN & Hwidth & Hbpos & Hble & Hbdvd & Hbuint & Hsplit).
    assert (Hb8 : bytes <= 8) by lia.
    assert (Hpmp : forall k, (k < N)%nat ->
              exec (pmpCheck (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes
                      (Store Data) User) s = Some (None, s)).
    { intros k Hk.
      exact (chunk_pmp (Store Data) bytes N k (or_intror (conj eq_refl HWp))
               Hbpos Hb8 Hbuint Hwidth Hk). }
    assert (Heff : exec (effectivePrivilege (Store Data)
                           (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (User, s)).
    { rewrite <- Hcp. apply exec_effectivePrivilege_mprv0. exact Hmprv. }
    exact (exec_mem_write_ea_split (Store Data) PBMT_PMA User pa W bytes N
             rv64d_types.Write_plain s HN Hpmp plan Heff Hcpp Hsplit
             ltac:(unfold write_kind_of_flags; cbn match; apply exec_returnM)).
  Qed.


  (* ---- the misaligned in-page WRITE.  The per-chunk [write_ram]s thread
     the state, so the post-state is a CHAIN; [wchain k] is the state after
     the first [k] chunks.  Its memory is [s.(mem)] with [k] windows
     overwritten, which is all the page's ownership needs to survive it. ---- *)
  Fixpoint wchain (bytes : Z) (dat : mword (8 * W)) (k : nat) : mstate :=
    match k with
    | O => s
    | S k' =>
        let s' := wchain bytes dat k' in
        match exec (write_ram rv64d_types.Write_plain
                      (Physaddr (add_vec_int pa (Z.of_nat k' * bytes))) bytes
                      (wvc W bytes dat k') tt) s' with
        | Some (_, s'') => s''
        | None => s'
        end
    end.

  Local Lemma wchain_step (bytes : Z) (N k : nat) (dat : mword (8 * W)) :
    0 < bytes -> Z.of_nat N * bytes = W -> (k < N)%nat ->
    exec (write_ram rv64d_types.Write_plain
            (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes
            (wvc W bytes dat k) tt) (wchain bytes dat k)
      = Some (true, wchain bytes dat (S k))
    /\ (exists (nn : BinNums.N) (v : bv nn),
          wchain bytes dat (S k)
          = MState (wchain bytes dat k).(sregs)
              (write_bytes (wchain bytes dat k).(mem)
                 (add_vec_int pa (Z.of_nat k * bytes)) (Z.to_N bytes) v)
              (wchain bytes dat k).(mdev)).
  Proof.
    intros Hb Hw Hk.
    assert (Hdev : dev_addr (add_vec_int pa (Z.of_nat k * bytes)) = false).
    { apply addr_is_ram_not_dev.
      rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
      exact (chunk_ram bytes N k 0%nat Hb Hw Hk ltac:(lia)). }
    destruct (exec_write_ram_plain_gen bytes (add_vec_int pa (Z.of_nat k * bytes))
                (wvc W bytes dat k) (wchain bytes dat k) Hdev) as (nn & v & Hwr).
    split.
    - cbn [wchain]. rewrite Hwr. reflexivity.
    - exists nn, v. cbn [wchain]. rewrite Hwr. reflexivity.
  Qed.

  Local Lemma wchain_regs (bytes : Z) (N : nat) (dat : mword (8 * W)) :
    0 < bytes -> Z.of_nat N * bytes = W ->
    forall k, (k <= N)%nat ->
      (wchain bytes dat k).(sregs) = s.(sregs) /\ (wchain bytes dat k).(mdev) = s.(mdev).
  Proof.
    intros Hb Hw k. induction k as [|k IH]; intro Hk.
    - split; reflexivity.
    - destruct (proj2 (wchain_step bytes N k dat Hb Hw ltac:(lia))) as (nn & v & Heq).
      destruct (IH ltac:(lia)) as [Hs Hd].
      rewrite Heq. cbn [sregs mdev]. split; assumption.
  Qed.

  Lemma exec_mem_write_value_mis_U (dat : mword (8 * W)) :
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    eq_vec (_get_Pmpcfg_ent_W
              (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    exists (bytes : Z) (N : nat),
      0 < bytes /\ Z.of_nat N * bytes = W /\ (1 <= N)%nat /\
      exec (mem_write_value (Physaddr pa) W dat (Store Data) PBMT_PMA false false false) s
        = Some (Ok true, wchain bytes dat N).
  Proof.
    intros Hmprv Hcp HWp.
    pose proof HWpos as Hpos. pose proof HWle as Hle.
    assert (Hr0 : addr_is_ram pa).
    { rewrite <- (pa_add_0 pa). apply Hwin. lia. }
    assert (HrL : addr_is_ram (pa_add pa (Z.to_nat W - 1))) by (apply Hwin; lia).
    destruct (pma_all_ram Hall pa W
                (pma_access_ram_at pa W (Z.to_nat W - 1)%nat ltac:(lia) Hr0 HrL
                   (pma_width_le W 8 Hpos Hle eq_refl)))
      as (region & Hpmam & _ & _ & Hwr & _ & _ & _ & Hmisx).
    destruct (exec_pmaCheck_ram_store_plan W pa PBMT_PMA region s Hpmam Hwr Hmisx)
      as (plan & Hpma).
    assert (Hcpp : exec (check_pma_with_pmp_priority (Store Data) PBMT_PMA User
                           (Physaddr pa) W false) s = Some (Ok plan, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _ Hpma). cbn match. apply exec_returnM. }
    destruct (split_misaligned_phys_derive W pa
                (Phys_Mem_Access_Info_granule_size_exp plan)
                (Phys_Mem_Access_Info_splittable plan) s HW)
      as (N & bytes & HN & Hwidth & Hbpos & Hble & Hbdvd & Hbuint & Hsplit).
    assert (Hb8 : bytes <= 8) by lia.
    exists bytes, N. split; [exact Hbpos|]. split; [exact Hwidth|]. split; [exact HN|].
    (* every chunk's state along the chain has the same registers as [s], so
       the per-chunk PMP/MMIO facts transport unchanged *)
    assert (Hregs : forall k, (k <= N)%nat ->
              (wchain bytes dat k).(sregs) = s.(sregs))
      by (intros k Hk; exact (proj1 (wchain_regs bytes N dat Hbpos Hwidth k Hk))).
    assert (Hpmp : forall k, (k < N)%nat ->
              exec (pmpCheck (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes
                      (Store Data) User) (wchain bytes dat k)
              = Some (None, wchain bytes dat k)).
    { intros k Hk.
      apply (exec_pmpCheck_user_grant_store _ bytes _).
      - rewrite (Hregs k ltac:(lia)). exact HA.
      - rewrite (Hregs k ltac:(lia)). exact Hord.
      - rewrite (Hregs k ltac:(lia)).
        assert (Hr0k : addr_is_ram (add_vec_int pa (Z.of_nat k * bytes))).
        { rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
          exact (chunk_ram bytes N k 0%nat Hbpos Hwidth Hk ltac:(lia)). }
        exact (ram_fetch_pmp _ _ bytes (Z.to_nat bytes - 1)%nat Hbpos Hb8 Hbuint
                 ltac:(lia) Hr0k
                 (chunk_ram bytes N k (Z.to_nat bytes - 1)%nat Hbpos Hwidth Hk ltac:(lia))
                 Hcovp).
      - rewrite (Hregs k ltac:(lia)). exact HWp. }
    assert (Hmmio : forall k, (k < N)%nat ->
              exec (within_mmio_writable
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes)
                (wchain bytes dat k) = Some (false, wchain bytes dat k)).
    { intros k Hk.
      assert (Hr0k : addr_is_ram (add_vec_int pa (Z.of_nat k * bytes))).
      { rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
        exact (chunk_ram bytes N k 0%nat Hbpos Hwidth Hk ltac:(lia)). }
      assert (Hh : register_lookup htif_tohost_base (wchain bytes dat k).(sregs) = None)
        by (rewrite (Hregs k ltac:(lia)); exact Hhtif).
      unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _
                 (within_clint_false _ bytes (wchain bytes dat k)
                    (addr_is_ram_not_in_clint _ Hr0k) Hbpos)).
      cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _
                 (within_sig_false _ bytes (wchain bytes dat k)
                    (addr_is_ram_not_in_sig _ Hr0k) Hbpos)).
      cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _
                 (within_htif_false _ bytes (wchain bytes dat k) Hh)).
      cbn match. reflexivity. }
    assert (Hwram : forall k, (k < N)%nat ->
              exec (write_ram rv64d_types.Write_plain
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes
                      (wvc W bytes dat k) tt) (wchain bytes dat k)
              = Some (true, wchain bytes dat (S k)))
      by (intros k Hk; exact (proj1 (wchain_step bytes N k dat Hbpos Hwidth Hk))).
    assert (Heff : exec (effectivePrivilege (Store Data)
                           (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (User, s)).
    { rewrite <- Hcp. apply exec_effectivePrivilege_mprv0. exact Hmprv. }
    pose proof (exec_checked_mem_write_split (Store Data) PBMT_PMA User pa W bytes N
                  false false false tt rv64d_types.Write_plain dat (fun _ => true)
                  (wchain bytes dat) HN Hpmp Hmmio Hwram plan Hcpp Hsplit
                  ltac:(unfold write_kind_of_flags; cbn match; apply exec_returnM)) as Hchk.
    rewrite (ws_seq_all_true N) in Hchk.
    exact (exec_mem_write_value_of_checked_plain (Store Data) PBMT_PMA pa W dat true
             User s _ Heff Hchk).
  Qed.

End MisPhys.

(* ===================================================================== *)
(* §f THE TWO USER-LEVEL COMPOSERS: one translation, then the physically   *)
(*    split full-width access.  Same shape as [UserMemPt]'s aligned        *)
(*    [user_pt_load_data_g]/[user_pt_store_data_g]; the only difference is  *)
(*    that the window is pinned by [in_one_page] rather than by alignment,  *)
(*    and that the store's post-state is the per-chunk WRITE CHAIN.         *)
(* ===================================================================== *)

(* the write chain leaves the registers and the devices alone, and every
   chunk it touches is RAM -- the two facts its consumers need about it *)
Lemma chunk_dev_false (pa : mword 64) (W bytes : Z) (N : nat) :
  0 < bytes -> Z.of_nat N * bytes = W ->
  (forall j : nat, (j < Z.to_nat W)%nat -> addr_is_ram (pa_add pa j)) ->
  forall k, (k < N)%nat -> dev_addr (add_vec_int pa (Z.of_nat k * bytes)) = false.
Proof.
  intros Hb Hw Hram k Hk.
  assert (HbN : Z.to_nat W = (N * Z.to_nat bytes)%nat).
  { rewrite <- Hw. rewrite Z2Nat.inj_mul; [| lia | lia]. rewrite Nat2Z.id. reflexivity. }
  apply addr_is_ram_not_dev.
  rewrite (pa_add_chunk pa k bytes ltac:(lia)).
  apply Hram. rewrite HbN. nia.
Qed.

Lemma wchain_regs_gen (pa : mword 64) (W : Z) (sg : mstate) (bytes : Z) (N : nat)
    (dat : mword (8 * W)) :
  (forall k, (k < N)%nat -> dev_addr (add_vec_int pa (Z.of_nat k * bytes)) = false) ->
  forall k, (k <= N)%nat ->
    (wchain pa W sg bytes dat k).(sregs) = sg.(sregs) /\
    (wchain pa W sg bytes dat k).(mdev) = sg.(mdev).
Proof.
  intros Hdev k. induction k as [|k IH]; intro Hk.
  - split; reflexivity.
  - destruct (exec_write_ram_plain_gen bytes (add_vec_int pa (Z.of_nat k * bytes))
                (wvc W bytes dat k) (wchain pa W sg bytes dat k) (Hdev k ltac:(lia)))
      as (nn & v & Hwr).
    assert (Hstep : wchain pa W sg bytes dat (S k)
              = MState (wchain pa W sg bytes dat k).(sregs)
                  (write_bytes (wchain pa W sg bytes dat k).(mem)
                     (add_vec_int pa (Z.of_nat k * bytes)) (Z.to_N bytes) v)
                  (wchain pa W sg bytes dat k).(mdev))
      by (cbn [wchain]; rewrite Hwr; reflexivity).
    destruct (IH ltac:(lia)) as [Hs Hd].
    rewrite Hstep. cbn [sregs mdev]. split; assumption.
Qed.

Section MisUser.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the ghost side of the write chain: each step overwrites one chunk window
     inside [data], so [udata_own data] survives all N of them *)
  Lemma wchain_own (pa : mword 64) (W : Z) (σ : mstate) (data : gset Arch.pa)
      (bytes : Z) (N : nat) (dat : mword (8 * W)) :
    0 < bytes -> Z.of_nat N * bytes = W ->
    (forall j : nat, (j < Z.to_nat W)%nat -> pa_add pa j ∈ data) ->
    (forall k, (k < N)%nat -> dev_addr (add_vec_int pa (Z.of_nat k * bytes)) = false) ->
    forall k, (k <= N)%nat ->
      gen_heap_interp σ.(mem) -∗ udata_own data ==∗
      gen_heap_interp (wchain pa W σ bytes dat k).(mem) ∗ udata_own data.
  Proof.
    intros Hb Hw Hdata Hdev k.
    assert (HbN : Z.to_nat W = (N * Z.to_nat bytes)%nat).
    { rewrite <- Hw. rewrite Z2Nat.inj_mul; [| lia | lia]. rewrite Nat2Z.id. reflexivity. }
    induction k as [|k IH]; intro Hk.
    - cbn [wchain]. iIntros "Hm Hd". iModIntro. iFrame.
    - iIntros "Hm Hd".
      iMod (IH ltac:(lia) with "Hm Hd") as "[Hm Hd]".
      destruct (exec_write_ram_plain_gen bytes (add_vec_int pa (Z.of_nat k * bytes))
                  (wvc W bytes dat k) (wchain pa W σ bytes dat k) (Hdev k ltac:(lia)))
        as (nn & v & Hwr).
      assert (Hstep : wchain pa W σ bytes dat (S k)
                = MState (wchain pa W σ bytes dat k).(sregs)
                    (write_bytes (wchain pa W σ bytes dat k).(mem)
                       (add_vec_int pa (Z.of_nat k * bytes)) (Z.to_N bytes) v)
                    (wchain pa W σ bytes dat k).(mdev))
        by (cbn [wchain]; rewrite Hwr; reflexivity).
      rewrite Hstep. cbn [mem].
      iMod (udata_own_store_window data (add_vec_int pa (Z.of_nat k * bytes)) bytes v
              _ ltac:(intros j Hj;
                      rewrite (pa_add_chunk pa k bytes ltac:(lia));
                      rewrite pa_add_bump2; apply Hdata; rewrite HbN; nia)
              with "Hm Hd") as "[Hm Hd]".
      iModIntro. iFrame.
  Qed.

  Lemma user_pt_load_data_mis (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (W : Z) (σ : mstate) :
    (W = 2 \/ W = 4 \/ W = 8) ->
    um !! svpn_of va = Some w ->
    uleaf_ok (Load Data) w ->
    udata_cov um data ->
    in_one_page va W ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ (dv : mword (8 * W)) (σ' : mstate),
      ⌜exec (translateAddr (Virtaddr va) (Load Data)) σ
        = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
      ⌜exec (mem_read (Load Data) PBMT_PMA (Physaddr (u_walk_pa w va)) W false false false) σ'
        = Some (Ok dv, σ')⌝ ∗
      ⌜σ'.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros HW Hl Hchk Hcov Hp Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    assert (HWpos : 0 < W) by (destruct HW as [ -> | [ -> | -> ] ]; lia).
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HRp & HWp & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (Load Data) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (Load Data)
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (Load Data) σ (or_intror (or_introl eq_refl))) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne. destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_window_facts um data w va W σ' HWpos Hl Hcov Hp with "Hgh Hdata")
      as %Hwin.
    iModIntro.
    destruct (exec_mem_read_mis_U (u_walk_pa w va) W σ' HW
                (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp))
                (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif))
                (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall))
                (fun j Hj => proj1 (proj2 (Hwin j Hj)))
                (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HRp))
                (fun j Hj => proj1 (Hwin j Hj)))
      as (dv & Hrd).
    iExists dv, σ'. iFrame "Hri Hgh Hinv Hdata". iPureIntro.
    split; [exact Htr|]. split; [exact Hrd|]. split; [exact Hmdev | exact Hsregs].
  Qed.


  Lemma user_pt_store_data_mis (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (data : gset Arch.pa)
      (w va : mword 64) (W : Z) (dat : mword (8 * W)) (σ : mstate) :
    (W = 2 \/ W = 4 \/ W = 8) ->
    um !! svpn_of va = Some w ->
    uleaf_ok (Store Data) w ->
    udata_cov um data ->
    in_one_page va W ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = User ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus σ.(sregs))) ('b"1") = false ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    utlb_inv_pt uroot tfp um -∗ udata_own data ==∗
    ∃ (σ' σ'' : mstate),
      ⌜exec (translateAddr (Virtaddr va) (Store Data)) σ
        = Some (Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw), σ')⌝ ∗
      ⌜exec (mem_write_ea (Physaddr (u_walk_pa w va)) W (Store Data) PBMT_PMA
               false false false) σ' = Some (Ok tt, σ')⌝ ∗
      ⌜exec (mem_write_value (Physaddr (u_walk_pa w va)) W dat (Store Data) PBMT_PMA
               false false false) σ' = Some (Ok true, σ'')⌝ ∗
      ⌜σ''.(sregs) = σ'.(sregs)⌝ ∗ ⌜σ''.(mdev) = σ.(mdev)⌝ ∗
      ⌜(σ'.(sregs) = σ.(sregs) \/
        exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type⌝ ∗
      reg_interp σ''.(sregs) ∗ gen_heap_interp σ''.(mem) ∗
      utlb_inv_pt uroot tfp um ∗ udata_own data.
  Proof.
    intros HW Hl Hchk Hcov Hp Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
    assert (HWpos : 0 < W) by (destruct HW as [ -> | [ -> | -> ] ]; lia).
    iDestruct (utlb_inv_pt_pmp_facts uroot tfp um σ with "Hri Hinv")
      as %(HA & Hord & HX & HRp & HWp & Hcovp).
    iMod (utlb_inv_pt_translateAddr_u (Store Data) uroot tfp um w va
            (u_walk_pa w va) σ Hl Hchk Hcanon eq_refl Hmisa Hmenv Hhtif Hcp HSXL
            (exec_effectivePrivilege_mprv0 (Store Data)
               (register_lookup mstatus σ.(sregs)) User σ Hmprv)
            (exec_is_shadow_stack_u_acc (Store Data) σ
               (or_intror (or_intror (or_introl eq_refl)))) Hall
            with "Hri Hgh Hinv")
      as (σ') "(%Htr & %Hmdev & %Hsregs & Hri & Hgh & Hinv)".
    assert (Tr : forall r : register, register_beq r tlb = false ->
              register_lookup r σ'.(sregs) = register_lookup r σ.(sregs)).
    { intros r Hne. destruct Hsregs as [Heq | (tv & Heq)]; rewrite Heq;
        [ reflexivity | apply irrelevant_register_set; exact Hne ]. }
    iDestruct (udata_window_facts um data w va W σ' HWpos Hl Hcov Hp with "Hgh Hdata")
      as %Hwin.
    set (pa := u_walk_pa w va).
    assert (Hea : exec (mem_write_ea (Physaddr pa) W (Store Data) PBMT_PMA
                          false false false) σ' = Some (Ok tt, σ')).
    { exact (exec_mem_write_ea_mis_U pa W σ' HW
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp))
               (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall))
               (fun j Hj => proj1 (proj2 (Hwin j Hj)))
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HWp))). }
    destruct (exec_mem_write_value_mis_U pa W σ' HW
                (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
                (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
                (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp))
                (ltac:(rewrite (Tr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif))
                (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall))
                (fun j Hj => proj1 (proj2 (Hwin j Hj)))
                dat
                (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
                (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
                (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HWp)))
      as (bytes & N & Hbpos & Hwidth & HN & Hwv).
    pose proof (chunk_dev_false pa W bytes N Hbpos Hwidth
                  (fun j Hj => proj1 (proj2 (Hwin j Hj)))) as Hdev.
    destruct (wchain_regs_gen pa W σ' bytes N dat Hdev N ltac:(lia)) as [Hcs Hcd].
    iMod (wchain_own pa W σ' data bytes N dat Hbpos Hwidth
            (fun j Hj => proj2 (proj2 (Hwin j Hj))) Hdev N ltac:(lia)
            with "Hgh Hdata") as "[Hgh Hdata]".
    iModIntro.
    iExists σ', (wchain pa W σ' bytes dat N).
    rewrite Hcs. iFrame "Hri Hgh Hinv Hdata". iPureIntro.
    split; [exact Htr|]. split; [exact Hea|]. split; [exact Hwv|].
    split; [reflexivity|]. split; [rewrite Hcd; exact Hmdev|]. exact Hsregs.
  Qed.

End MisUser.
