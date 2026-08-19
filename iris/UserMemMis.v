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
Require Import HartMemRun HartMemAsm PtWalkCert.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §a THE PHYSICAL CHUNK PLAN.                                             *)
(*                                                                         *)
(* [split_misaligned] on the PHYSICAL address, under whatever plan the      *)
(* Misaligned Atomicity Granule check answered, always resolves to a chunk  *)
(* count and a chunk width that multiply to the access width.  Two          *)
(* branches: the access does not split (the plan is [CannotSplit], or the   *)
(* address is aligned after all, or it fits in one granule) and it is ONE   *)
(* operation of the full width; otherwise [split_access] gives              *)
(* [2^min(ctz(pa), ctz(W))]-byte chunks.  NOTHING here needs to know which  *)
(* branch was taken or what the granule is -- which is why the granule can  *)
(* stay a platform detail that [pma_allows_all] does not pin.               *)
(*                                                                         *)
(* The chunk width divides [W] because [min(ctz(pa),ctz(W)) <= ctz(W)] and  *)
(* [2^ctz(W)] divides [W]; only that last fact is width-specific, and for   *)
(* the eight widths a vmem-level access part can have it is a [vm_compute]. *)
(* (This replaces a ~200-line characterization of [count_trailing_zeros] as *)
(* a [foreach_Z_down'] suffix invariant: the old vmem-level split needed    *)
(* the chunk ADDRESSES to be aligned, and so needed ctz exactly; the        *)
(* physical split needs only that the chunk width divides the access.)      *)
(* ===================================================================== *)

Lemma foreach_Z_down'_nonneg (b : Z -> Z -> Z) :
  (forall i r, 0 <= i -> 0 <= r -> 0 <= b i r) ->
  forall (n : nat) (from off r : Z), 0 <= r ->
  0 <= foreach_Z_down' from 0 1 off n r b.
Proof.
  intros Hb n. induction n as [|n IH]; intros from off r Hr.
  - cbn [foreach_Z_down']. destruct (sumbool_of_bool (0 <=? from + off)); exact Hr.
  - cbn [foreach_Z_down'].
    destruct (sumbool_of_bool (0 <=? from + off)) as [Hg|Hg]; [| exact Hr].
    apply Z.leb_le in Hg.
    apply IH. apply Hb; [exact Hg | exact Hr].
Qed.

Lemma ctz_nonneg {n : Z} (x : mword n) : 0 <= n -> 0 <= count_trailing_zeros x.
Proof.
  intro Hn. unfold count_trailing_zeros, foreach_Z_down.
  apply foreach_Z_down'_nonneg; [| exact Hn ].
  intros i r Hi Hr. destruct (eq_vec (access_vec_dec x i) (mword_of_int 1)); assumption.
Qed.

(* the one width-specific fact: [2^ctz(W)] divides [W].  A vmem-level access
   part is at most 8 bytes wide (and at least 1), so this is eight cases. *)
Lemma width_ctz_facts (W : Z) : 0 < W -> W <= 8 ->
  let kw := count_trailing_zeros (to_bits (Z.add 12 1) W) in
  0 <= kw /\ (2 ^ kw | W) /\ 2 ^ kw <= W.
Proof.
  intros Hpos Hle. cbn zeta.
  assert (HWv : W = 1 \/ W = 2 \/ W = 3 \/ W = 4 \/ W = 5 \/ W = 6 \/ W = 7 \/ W = 8)
    by lia.
  destruct HWv as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ];
    (split; [ vm_compute; discriminate
            | split; [ | vm_compute; discriminate ] ]);
    match goal with |- (2 ^ ?k | ?w) => let v := eval vm_compute in k in
      change k with v end;
    [ exists 1 | exists 1 | exists 3 | exists 1 | exists 5 | exists 3 | exists 7 | exists 1 ];
    reflexivity.
Qed.

Lemma split_misaligned_phys_derive (W : Z) (pa : mword 64) (g : Z)
    (sp : Splittability) (s : mstate) :
  0 < W -> W <= 8 ->
  exists (N : nat) (bytes : Z),
    (1 <= N)%nat /\ Z.of_nat N * bytes = W /\ 0 < bytes /\ bytes <= W /\
    uint (to_bits 64 bytes) = bytes /\
    exec (split_misaligned (Physaddr pa) W g sp) s = Some ((Z.of_nat N, bytes), s).
Proof.
  intros HWpos HWle.
  assert (HWu : uint (to_bits 64 W) = W).
  { assert (HWv : W = 1 \/ W = 2 \/ W = 3 \/ W = 4 \/ W = 5 \/ W = 6 \/ W = 7 \/ W = 8)
      by lia.
    destruct HWv as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ];
      vm_compute; reflexivity. }
  (* the [do_not_split] disjunction: any of its three arms gives ONE
     operation of the full width *)
  destruct (orb (generic_eq sp CannotSplit)
              (orb (Z.eqb (Z.rem (uint (bits_of_physaddr (Physaddr pa))) W) 0)
                 (allowed_misaligned
                    (subrange_vec_dec (bits_of_physaddr (Physaddr pa)) (Z.sub xlen 1) 0)
                    W g))) eqn:Ends.
  { exists 1%nat, W. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact HWu|].
    unfold split_misaligned. cbn zeta. rewrite Ends. cbn match. apply exec_returnm. }
  (* ...otherwise [split_access].  Reduce the goal FIRST, so the chunk width
     can be named exactly as it appears in it. *)
  unfold split_misaligned. cbn zeta. rewrite Ends. cbn match.
  unfold sys_misaligned_byte_by_byte. cbn match.
  unfold split_access. cbn zeta.
  change (bits_of_physaddr (Physaddr pa)) with pa.
  destruct (width_ctz_facts W HWpos HWle) as (Hkw0 & Hkwd & Hkwle).
  set (kw := count_trailing_zeros (to_bits (Z.add 12 1) W)) in *.
  assert (Hka0 : 0 <= count_trailing_zeros pa) by (apply ctz_nonneg; lia).
  set (ka := count_trailing_zeros pa) in *.
  set (m := Z.min ka kw) in *.
  assert (Hm0 : 0 <= m) by (unfold m; lia).
  assert (Hmkw : m <= kw) by (unfold m; lia).
  assert (Hpw : pow2 m = 2 ^ m) by reflexivity.
  rewrite Hpw.
  assert (Hbpos : 0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (Hbdvd : (2 ^ m | W)).
  { apply (Z.divide_trans _ (2 ^ kw) _); [| exact Hkwd].
    exists (2 ^ (kw - m)). rewrite <- Z.pow_add_r; [| lia | lia].
    f_equal. lia. }
  assert (Hble : 2 ^ m <= W).
  { apply (Z.le_trans _ (2 ^ kw) _); [| exact Hkwle].
    apply Z.pow_le_mono_r; lia. }
  destruct Hbdvd as [q Hq].
  assert (Hqpos : 0 < q) by nia.
  assert (Hquot : Z.quot W (2 ^ m) = q) by (rewrite Hq; rewrite Z.quot_mul; lia).
  rewrite Hquot.
  exists (Z.to_nat q), (2 ^ m).
  split; [lia|].
  split; [rewrite Z2Nat.id; lia|].
  split; [exact Hbpos|].
  split; [exact Hble|].
  split.
  { assert (Hm3 : m <= 3).
    { destruct (Z_le_gt_dec m 3) as [Hle3|Hgt3]; [exact Hle3|].
      exfalso. assert (2 ^ 4 <= 2 ^ m) by (apply Z.pow_le_mono_r; lia). lia. }
    assert (Hmv : m = 0 \/ m = 1 \/ m = 2 \/ m = 3) by lia.
    destruct Hmv as [ Hv | [ Hv | [ Hv | Hv ] ] ]; rewrite Hv;
      vm_compute; reflexivity. }
  replace (Z.eqb W (q * 2 ^ m)) with true by (symmetry; apply Z.eqb_eq; lia).
  erewrite exec_bind_Some.
  2:{ unfold assert_exp'. cbn match. apply exec_returnm. }
  cbn beta. rewrite Z2Nat.id; [| lia]. apply exec_returnm.
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

Lemma page_mask_eq_intra (a : mword 64) (w : Z) :
  0 < w -> in_one_page a w ->
  eq_vec (and_vec a (update_subrange_vec_dec ((ones 64) : bits 64)
                       (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1)))))
         (and_vec (sub_vec_int (add_vec_int a w) 1)
                  (update_subrange_vec_dec ((ones 64) : bits 64)
                     (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1))))) = true.
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
  apply eq_vec_true_iff. apply bv_eq.
  rewrite !and_vec64_unsigned. rewrite page_mask64_val.
  rewrite Hsub.
  assert (Hnn : 0 <= bv_unsigned a + (w - 1)) by (clear - Hr0 Hpos; lia).
  rewrite (z_land_pagemask (bv_unsigned a) Hr0 Hr1).
  rewrite (z_land_pagemask (bv_unsigned a + (w - 1)) Hnn Hnw).
  rewrite <- (z_shiftr12_stable_page (bv_unsigned a) w Hr0 Hpos Hp). reflexivity.
Qed.

Lemma goodmb_split_on_page_boundary_intra (Dr Dw : register -> bool)
    (a : mword 64) (w : Z) s mm :
  0 < w -> in_one_page a w ->
  goodmb Dr Dw (split_on_page_boundary a w) s mm = true.
Proof.
  intros Hpos Hp. unfold split_on_page_boundary.
  rewrite (page_mask_eq_intra a w Hpos Hp). apply goodmb_returnm.
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

Lemma goodmb_pma_misaligned_exception_load (Dr Dw : register -> bool) (pma : PMA) s mm :
  (pma.(PMA_misaligned_exceptions)).(PMAMisalignedExceptions_load_store) = None ->
  goodmb Dr Dw (pma_misaligned_exception pma (Load Data)) s mm = true.
Proof.
  intro H. unfold pma_misaligned_exception. cbn match. rewrite H. apply goodmb_returnm.
Qed.

Lemma exec_pma_misaligned_exception_store (pma : PMA) s :
  (pma.(PMA_misaligned_exceptions)).(PMAMisalignedExceptions_load_store) = None ->
  exec (pma_misaligned_exception pma (Store Data)) s = Some (None, s).
Proof.
  intro H. unfold pma_misaligned_exception. cbn match. rewrite H. apply exec_returnM.
Qed.

Lemma goodmb_pma_misaligned_exception_store (Dr Dw : register -> bool) (pma : PMA) s mm :
  (pma.(PMA_misaligned_exceptions)).(PMAMisalignedExceptions_load_store) = None ->
  goodmb Dr Dw (pma_misaligned_exception pma (Store Data)) s mm = true.
Proof.
  intro H. unfold pma_misaligned_exception. cbn match. rewrite H. apply goodmb_returnm.
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

Lemma goodmb_mag_pma_check_plan (Dr Dw : register -> bool) (pma : PMA)
    (acc : MemoryAccessType mem_payload)
    (paddr : physaddr) (width : Z) (b : bool) s mm :
  goodmb Dr Dw (is_mag_applicable_access acc width) s mm = true ->
  exec (is_mag_applicable_access acc width) s = Some (b, s) ->
  goodmb Dr Dw (pma_misaligned_exception pma acc) s mm = true ->
  exec (pma_misaligned_exception pma acc) s = Some (None, s) ->
  goodmb Dr Dw (mag_pma_check pma acc paddr width) s mm = true.
Proof.
  intros Hmag Hma Hmeg Hme.
  unfold mag_pma_check.
  erewrite (gm_bind Dr Dw _ _ s s mm b Hmag Hma).
  destruct (orb (is_aligned_paddr paddr width)
                (andb b (within_pma_mag pma paddr width (is_vector_access acc)))) eqn:E.
  - apply goodmb_returnm.
  - erewrite (gm_bind Dr Dw _ _ s s mm None Hmeg Hme). cbn match.
    destruct b; destruct (mag_of_pma pma (is_vector_access acc)) as [mag|];
      cbn match; apply goodmb_returnm.
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

Ltac gm_pma_plan_peel Hrg Hfield Hmatch Hmagg Hmage :=
  unfold pmaCheck; apply goodmb_cer;
  match goal with |- goodmb _ _ _ ?st _ = _ =>
    gmm_lift Hrg (exec_read_reg pma_regions st) end;
  rewrite Hmatch; cbn [PMA_Region_attributes] in Hfield |- *; cbn match;
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ];
  cbn match beta; cbn [Riscv.rv64d.not negb];
  match goal with
  | |- goodmb ?dr ?dw ?T ?st ?m = _ =>
      match T with context[Defs.assert_exp' true ?msg] =>
        gmxlR (goodmb_assert_exp'_true dr dw msg st m)
              (exec_assert_exp'_true msg st) end
  end;
  rewrite mbind_Ret; rewrite bindR_ret;
  rewrite Hfield; cbn [Riscv.rv64d.not negb];
  gmm_lift Hmagg Hmage; cbn beta; cbn match; apply goodmb_returnm.

Lemma goodmb_pmaCheck_ram_load_plan (Dr Dw : register -> bool)
    (k : Z) (addr : mword 64) (pbmt : page_based_mem_type) (region : PMA_Region) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_misaligned_exceptions)).(PMAMisalignedExceptions_load_store) = None ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (Load Data) pbmt false) s mm = true.
Proof.
  intros HD Hmatch Hread Hme.
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  destruct (exec_mag_pma_check_plan (override_PMA (PMA_Region_attributes region) pbmt)
              (Load Data) (Physaddr addr) k _ s
              (exec_is_mag_applicable_load_data k s)
              (exec_pma_misaligned_exception_load _ s Hme)) as (sp & g & Hmage).
  pose proof (goodmb_mag_pma_check_plan Dr Dw
                (override_PMA (PMA_Region_attributes region) pbmt)
                (Load Data) (Physaddr addr) k _ s mm
                (goodmb_returnm Dr Dw _ s mm)
                (exec_is_mag_applicable_load_data k s)
                (goodmb_pma_misaligned_exception_load Dr Dw _ s mm Hme)
                (exec_pma_misaligned_exception_load _ s Hme)) as Hmagg.
  destruct region as [rbase rsize rattr rdtree].
  gm_pma_plan_peel Hrg Hread Hmatch Hmagg Hmage.
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

Lemma goodmb_pmaCheck_ram_store_plan (Dr Dw : register -> bool)
    (k : Z) (addr : mword 64) (pbmt : page_based_mem_type) (region : PMA_Region) s mm :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) k
    = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  ((override_PMA (PMA_Region_attributes region) pbmt).(PMA_misaligned_exceptions)).(PMAMisalignedExceptions_load_store) = None ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) k (Store Data) pbmt false) s mm = true.
Proof.
  intros HD Hmatch Hwrite Hme.
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  destruct (exec_mag_pma_check_plan (override_PMA (PMA_Region_attributes region) pbmt)
              (Store Data) (Physaddr addr) k _ s
              (exec_is_mag_applicable_store_data k s)
              (exec_pma_misaligned_exception_store _ s Hme)) as (sp & g & Hmage).
  pose proof (goodmb_mag_pma_check_plan Dr Dw
                (override_PMA (PMA_Region_attributes region) pbmt)
                (Store Data) (Physaddr addr) k _ s mm
                (goodmb_returnm Dr Dw _ s mm)
                (exec_is_mag_applicable_store_data k s)
                (goodmb_pma_misaligned_exception_store Dr Dw _ s mm Hme)
                (exec_pma_misaligned_exception_store _ s Hme)) as Hmagg.
  destruct region as [rbase rsize rattr rdtree].
  gm_pma_plan_peel Hrg Hwrite Hmatch Hmagg Hmage.
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

(* the twin: the read node's two pure obligations, and the [read_bytes]
   premise of [HartMemAsm.goodmb_read_ram] taken off the read's own [exec]
   fact ([UserMemPt.goodmb_read_ram_of_exec]) rather than off a byte
   hypothesis -- at a SYMBOLIC width the two spellings of the value's index
   ([bv (8 * Z.to_N k)] vs [mword (8 * k)]) do not unify. *)
Lemma goodmb_read_ram_chunk (Dr Dw : register -> bool) (rk : read_kind)
    (a : mword 64) (bytes : Z) (meta : bool) s mm :
  rk_ram_ok rk = true ->
  dev_addr a = false ->
  bytes_owned mm a (Z.to_N bytes) = true ->
  (exists v, exec (read_ram rk (Physaddr a) bytes meta) s = Some ((v, tt), s)) ->
  goodmb Dr Dw (read_ram rk (Physaddr a) bytes meta) s mm = true.
Proof.
  intros Hrk Hdev Hown [v Hv].
  exact (goodmb_read_ram_of_exec Dr Dw rk bytes a meta (v, tt) s s mm
           Hrk Hdev Hown Hv).
Qed.

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

(* ===================================================================== *)
(* THE [untilMT] CHAIN'S CERTIFICATE.                                      *)
(* ===================================================================== *)

Lemma gm_untilMT'_last (Dr Dw : register -> bool) {R Vars} (limit : Z)
   (vars vars' : Vars)
   (cond : Vars -> Defs.monadR R exception bool)
   (body : Vars -> Defs.monadR R exception Vars)
   s s' mm (acc : Acc (Zwf 0) limit) :
  (limit >= 0)%Z ->
  goodmb Dr Dw (body vars) s mm = true ->
  execR (body vars) s = Some (inr vars', s') ->
  goodmb Dr Dw (cond vars') s' mm = true ->
  execR (cond vars') s' = Some (inr true, s') ->
  goodmb Dr Dw (Defs.untilMT' limit vars cond body acc) s mm = true.
Proof.
  intros Hlim Hbg Hb Hcg Hc. destruct acc as [acc_fn]. cbn [Defs.untilMT'].
  destruct (Z_ge_dec limit 0) as [Hge|Hge]; [| lia].
  erewrite (gm_bindR Dr Dw _ _ s s' mm vars' Hbg Hb).
  erewrite (gm_bindR Dr Dw _ _ s' s' mm true Hcg Hc).
  cbn match. apply goodmb_returnm.
Qed.

Lemma gm_untilMT'_step (Dr Dw : register -> bool) {R Vars} (limit : Z)
   (vars vars' : Vars)
   (cond : Vars -> Defs.monadR R exception bool)
   (body : Vars -> Defs.monadR R exception Vars)
   s s' mm (acc : Acc (Zwf 0) limit) :
  (limit >= 0)%Z ->
  goodmb Dr Dw (body vars) s mm = true ->
  execR (body vars) s = Some (inr vars', s') ->
  goodmb Dr Dw (cond vars') s' mm = true ->
  execR (cond vars') s' = Some (inr false, s') ->
  exists acc' : Acc (Zwf 0) (limit - 1),
    goodmb Dr Dw (Defs.untilMT' limit vars cond body acc) s mm
    = goodmb Dr Dw (Defs.untilMT' (limit - 1) vars' cond body acc') s' mm.
Proof.
  intros Hlim Hbg Hb Hcg Hc. destruct acc as [acc_fn]. cbn [Defs.untilMT'].
  destruct (Z_ge_dec limit 0) as [Hge|Hge]; [| lia].
  erewrite (gm_bindR Dr Dw _ _ s s' mm vars' Hbg Hb).
  erewrite (gm_bindR Dr Dw _ _ s' s' mm false Hcg Hc).
  cbn match. eexists. reflexivity.
Qed.

Lemma gm_untilMT'_chain (Dr Dw : register -> bool) {R Vars}
   (cond : Vars -> Defs.monadR R exception bool)
   (body : Vars -> Defs.monadR R exception Vars) mm :
   forall (N : nat) (v : nat -> Vars) (st : nat -> mstate) (limit0 : Z)
          (acc : Acc (Zwf 0) limit0),
   (1 <= N)%nat ->
   (limit0 >= Z.of_nat N - 1)%Z ->
   (forall k, (k < N)%nat -> goodmb Dr Dw (body (v k)) (st k) mm = true) ->
   (forall k, (k < N)%nat -> execR (body (v k)) (st k)
                             = Some (inr (v (S k)), st (S k))) ->
   (forall k, (k < N)%nat -> goodmb Dr Dw (cond (v (S k))) (st (S k)) mm = true) ->
   (forall k, (S k < N)%nat -> execR (cond (v (S k))) (st (S k))
                               = Some (inr false, st (S k))) ->
   execR (cond (v N)) (st N) = Some (inr true, st N) ->
   goodmb Dr Dw (Defs.untilMT' limit0 (v 0%nat) cond body acc) (st 0%nat) mm = true.
Proof.
  intros N. induction N as [|N' IH]; [ lia | ].
  intros v st limit0 acc HN Hlim Hbodyg Hbody Hcondg Hcondf Hcondt.
  destruct (Nat.eq_dec N' 0) as [->|Hn0].
  - apply (gm_untilMT'_last Dr Dw limit0 (v 0%nat) (v 1%nat) cond body
             (st 0%nat) (st 1%nat) mm acc).
    + lia.
    + apply (Hbodyg 0%nat). lia.
    + apply (Hbody 0%nat). lia.
    + apply (Hcondg 0%nat). lia.
    + apply Hcondt.
  - edestruct (gm_untilMT'_step Dr Dw limit0 (v 0%nat) (v 1%nat) cond body
                 (st 0%nat) (st 1%nat) mm acc) as [acc' Hstep].
    + lia.
    + apply (Hbodyg 0%nat). lia.
    + apply (Hbody 0%nat). lia.
    + apply (Hcondg 0%nat). lia.
    + apply (Hcondf 0%nat). lia.
    + rewrite Hstep.
      apply (IH (fun k => v (S k)) (fun k => st (S k)) (limit0 - 1) acc').
      * lia.
      * lia.
      * intros k Hk. apply (Hbodyg (S k)). lia.
      * intros k Hk. apply (Hbody (S k)). lia.
      * intros k Hk. apply (Hcondg (S k)). lia.
      * intros k Hk. apply (Hcondf (S k)). lia.
      * apply Hcondt.
Qed.

(* [returnR tt >> B] is [B] by conversion, but Sail's [>>] binds TIGHTER than
   [>>=], so the collapsed node sits one bind IN and no [execR_bind0_Some]
   rewrite finds it.  [change] does, at either level and on either side. *)
Ltac gm_ret_bind0 :=
  first
    [ match goal with |- execR (Defs.bind (Defs.bind0 _ ?B) ?kk) ?ss = ?RR =>
        change (execR (Defs.bind B kk) ss = RR) end
    | match goal with |- execR (Defs.bind0 _ ?B) ?ss = ?RR =>
        change (execR B ss = RR) end
    | match goal with
      | |- goodmb ?dr ?dw (Defs.bind (Defs.bind0 _ ?B) ?kk) ?ss ?m = ?RR =>
          change (goodmb dr dw (Defs.bind B kk) ss m = RR) end
    | match goal with |- goodmb ?dr ?dw (Defs.bind0 _ ?B) ?ss ?m = ?RR =>
        change (goodmb dr dw B ss m = RR) end ].

Section GmCheckedMemReadSplit.
  Context (Dr Dw : register -> bool).
  Context (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
          (priv : Privilege).
  Context (pa : mword 64) (width bytes : Z) (N : nat)
          (aq rl res meta : bool) (rk : read_kind).
  Context (val : nat -> mword (8 * bytes)) (s : mstate) (mm : PtBytes.pamap).
  Context (HN : (1 <= N)%nat) (Hbytes : 0 < bytes).

  Notation n := (Z.of_nat N).
  Notation cpa k := (Physaddr (add_vec_int pa (Z.of_nat k * bytes))).

  Hypothesis Hpmp : forall k, (k < N)%nat ->
    exec (pmpCheck (cpa k) bytes acc priv) s = Some (None, s).
  Hypothesis Hpmpg : forall k, (k < N)%nat ->
    goodmb Dr Dw (pmpCheck (cpa k) bytes acc priv) s mm = true.
  Hypothesis Hmmio : forall k, (k < N)%nat ->
    exec (within_mmio_readable (cpa k) bytes) s = Some (false, s).
  Hypothesis Hmmiog : forall k, (k < N)%nat ->
    goodmb Dr Dw (within_mmio_readable (cpa k) bytes) s mm = true.
  Hypothesis Hram : forall k, (k < N)%nat ->
    exec (read_ram rk (cpa k) bytes meta) s = Some ((val k, tt), s).
  Hypothesis Hramg : forall k, (k < N)%nat ->
    goodmb Dr Dw (read_ram rk (cpa k) bytes meta) s mm = true.

  Lemma goodmb_checked_mem_read_split (plan : Phys_Mem_Access_Info) :
    goodmb Dr Dw (check_pma_with_pmp_priority acc pbmt priv (Physaddr pa) width res)
      s mm = true ->
    exec (check_pma_with_pmp_priority acc pbmt priv (Physaddr pa) width res) s
      = Some (Ok plan, s) ->
    goodmb Dr Dw (split_misaligned (Physaddr pa) width
            (Phys_Mem_Access_Info_granule_size_exp plan)
            (Phys_Mem_Access_Info_splittable plan)) s mm = true ->
    exec (split_misaligned (Physaddr pa) width
            (Phys_Mem_Access_Info_granule_size_exp plan)
            (Phys_Mem_Access_Info_splittable plan)) s = Some ((n, bytes), s) ->
    goodmb Dr Dw (read_kind_of_flags aq rl res) s mm = true ->
    exec (read_kind_of_flags aq rl res) s = Some (rk, s) ->
    goodmb Dr Dw (checked_mem_read acc pbmt priv (Physaddr pa) width aq rl res meta)
      s mm = true.
  Proof.
    intros Hpacg Hpac Hsplitg Hsplit Hrkg Hrk.
    unfold checked_mem_read. apply goodmb_cer.
    gmm_lift Hpacg Hpac. cbn beta. cbn match.
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match beta.
    gmm_lift Hsplitg Hsplit. cbn beta zeta match.
    rewrite misaligned_order_split. cbn zeta.
    gmm_lift Hrkg Hrk. cbn beta.
    match goal with
    | |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
        assert (Hu : execR (Defs.untilMT vs m0 c bb) s
                     = Some (inr (MemAccessGen.rsplit_var bytes N val N), s));
        [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m0 c bb) s mm = true) ]
    end.
    { rewrite <- (MemAccessGen.rsplit_var0 bytes N val HN).
      unfold Defs.untilMT.
      match goal with
      | |- execR (Defs.untilMT' ?L _ ?c ?b _) _ = _ =>
          set (LL := L); set (CC := c); set (BB := b)
      end.
      assert (HL : LL = n)
        by (unfold LL; rewrite (MemAccessGen.rsplit_var0 bytes N val HN); reflexivity).
      clearbody LL. rewrite HL.
      apply (MemAccessGen.execR_untilMT'_chain CC BB N
               (MemAccessGen.rsplit_var bytes N val) (fun _ => s) n).
      - exact HN.
      - lia.
      - intros k Hk. unfold BB, MemAccessGen.rsplit_var.
        replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.min k (N - 1)) with k by lia.
        cbn match.
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr pa)) with pa.
        rewrite (execR_liftR_seq _ _ _ _ _ (Hpmp k Hk)). cbn match.
        gm_ret_bind0.
        rewrite (execR_liftR_seq _ _ _ _ _ (Hmmio k Hk)). cbn match beta.
        match goal with
        | |- execR (Defs.bind ?m0 ?post) s = _ =>
            assert (Hrr : execR m0 s = Some (inr (val k), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _ (Hram k Hk)). cbn match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hrr). cbn beta.
        destruct (Z.eqb (Z.of_nat k) (n - 1)) eqn:Eq; cbn match;
          rewrite execR_returnR_fwd; do 3 f_equal; unfold MemAccessGen.rsplit_var.
        + apply Z.eqb_eq in Eq.
          replace (Nat.eqb (S k) N) with true by (symmetry; apply Nat.eqb_eq; lia).
          replace (Nat.min (S k) (N - 1)) with k by lia. reflexivity.
        + apply Z.eqb_neq in Eq.
          replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
          replace (Nat.min (S k) (N - 1)) with (S k) by lia.
          replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. reflexivity.
      - intros k Hk. unfold CC, MemAccessGen.rsplit_var. cbn match.
        replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
        apply execR_returnR_fwd.
      - unfold CC, MemAccessGen.rsplit_var. cbn match. rewrite Nat.eqb_refl.
        apply execR_returnR_fwd. }
    { rewrite <- (MemAccessGen.rsplit_var0 bytes N val HN).
      unfold Defs.untilMT.
      match goal with
      | |- goodmb _ _ (Defs.untilMT' ?L _ ?c ?b _) _ _ = _ =>
          set (LL := L); set (CC := c); set (BB := b)
      end.
      assert (HL : LL = n)
        by (unfold LL; rewrite (MemAccessGen.rsplit_var0 bytes N val HN); reflexivity).
      clearbody LL. rewrite HL.
      apply (gm_untilMT'_chain Dr Dw CC BB mm N
               (MemAccessGen.rsplit_var bytes N val) (fun _ => s) n).
      - exact HN.
      - lia.
      - intros k Hk. unfold BB, MemAccessGen.rsplit_var.
        replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.min k (N - 1)) with k by lia.
        cbn match.
        gmm_liftT ltac:(apply goodmb_assert_exp'_true)
                  ltac:(apply exec_assert_exp'_true). cbn beta.
        change (bits_of_physaddr (Physaddr pa)) with pa.
        gmm_lift (Hpmpg k Hk) (Hpmp k Hk). cbn match.
        gm_ret_bind0.
        gmm_lift (Hmmiog k Hk) (Hmmio k Hk). cbn match beta.
        match goal with
        | |- goodmb _ _ (Defs.bind ?m0 ?post) s _ = _ =>
            assert (Hrrg : goodmb Dr Dw m0 s mm = true);
            [ | assert (Hrr : execR m0 s = Some (inr (val k), s)) ]
        end.
        { gmm_lift (Hramg k Hk) (Hram k Hk). cbn match. apply goodmb_returnm. }
        { rewrite (execR_liftR_seq _ _ _ _ _ (Hram k Hk)). cbn match.
          apply execR_returnR_fwd. }
        erewrite (gm_bindR Dr Dw _ _ s s mm (val k) Hrrg Hrr). cbn beta.
        destruct (Z.eqb (Z.of_nat k) (n - 1)) eqn:Eq; cbn match; apply goodmb_returnm.
      - intros k Hk. unfold BB, MemAccessGen.rsplit_var.
        replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.min k (N - 1)) with k by lia.
        cbn match.
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr pa)) with pa.
        rewrite (execR_liftR_seq _ _ _ _ _ (Hpmp k Hk)). cbn match.
        gm_ret_bind0.
        rewrite (execR_liftR_seq _ _ _ _ _ (Hmmio k Hk)). cbn match beta.
        match goal with
        | |- execR (Defs.bind ?m0 ?post) s = _ =>
            assert (Hrr : execR m0 s = Some (inr (val k), s))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _ (Hram k Hk)). cbn match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hrr). cbn beta.
        destruct (Z.eqb (Z.of_nat k) (n - 1)) eqn:Eq; cbn match;
          rewrite execR_returnR_fwd; do 3 f_equal; unfold MemAccessGen.rsplit_var.
        + apply Z.eqb_eq in Eq.
          replace (Nat.eqb (S k) N) with true by (symmetry; apply Nat.eqb_eq; lia).
          replace (Nat.min (S k) (N - 1)) with k by lia. reflexivity.
        + apply Z.eqb_neq in Eq.
          replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
          replace (Nat.min (S k) (N - 1)) with (S k) by lia.
          replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. reflexivity.
      - intros k Hk. unfold CC, MemAccessGen.rsplit_var. cbn match.
        apply goodmb_returnm.
      - intros k Hk. unfold CC, MemAccessGen.rsplit_var. cbn match.
        replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
        apply execR_returnR_fwd.
      - unfold CC, MemAccessGen.rsplit_var. cbn match. rewrite Nat.eqb_refl.
        apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s s mm (MemAccessGen.rsplit_var bytes N val N) Hug Hu).
    cbn beta zeta. unfold MemAccessGen.rsplit_var. cbn match.
    apply goodmb_returnm.
  Qed.

End GmCheckedMemReadSplit.

Section GmCheckedMemWriteSplit.
  Context (Dr Dw : register -> bool).
  Context (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
          (priv : Privilege).
  Context (pa : mword 64) (width bytes : Z) (N : nat)
          (aq rl con : bool) (meta : unit) (wk : write_kind).
  Context (dat : mword (8 * width)) (sk : nat -> bool) (sw : nat -> mstate).
  Context (mm : PtBytes.pamap).
  Context (HN : (1 <= N)%nat) (Hbytes : 0 < bytes).

  Notation n := (Z.of_nat N).
  Notation cpa k := (Physaddr (add_vec_int pa (Z.of_nat k * bytes))).

  Hypothesis Hpmp : forall k, (k < N)%nat ->
    exec (pmpCheck (cpa k) bytes acc priv) (sw k) = Some (None, sw k).
  Hypothesis Hpmpg : forall k, (k < N)%nat ->
    goodmb Dr Dw (pmpCheck (cpa k) bytes acc priv) (sw k) mm = true.
  Hypothesis Hmmio : forall k, (k < N)%nat ->
    exec (within_mmio_writable (cpa k) bytes) (sw k) = Some (false, sw k).
  Hypothesis Hmmiog : forall k, (k < N)%nat ->
    goodmb Dr Dw (within_mmio_writable (cpa k) bytes) (sw k) mm = true.
  Hypothesis Hwram : forall k, (k < N)%nat ->
    exec (write_ram wk (cpa k) bytes (MemAccessGen.wvc width bytes dat k) meta) (sw k)
      = Some (sk k, sw (S k)).
  Hypothesis Hwramg : forall k, (k < N)%nat ->
    goodmb Dr Dw (write_ram wk (cpa k) bytes (MemAccessGen.wvc width bytes dat k) meta)
      (sw k) mm = true.

  Lemma goodmb_checked_mem_write_split (plan : Phys_Mem_Access_Info) :
    goodmb Dr Dw (check_pma_with_pmp_priority acc pbmt priv (Physaddr pa) width con)
      (sw 0%nat) mm = true ->
    exec (check_pma_with_pmp_priority acc pbmt priv (Physaddr pa) width con) (sw 0%nat)
      = Some (Ok plan, sw 0%nat) ->
    goodmb Dr Dw (split_misaligned (Physaddr pa) width
            (Phys_Mem_Access_Info_granule_size_exp plan)
            (Phys_Mem_Access_Info_splittable plan)) (sw 0%nat) mm = true ->
    exec (split_misaligned (Physaddr pa) width
            (Phys_Mem_Access_Info_granule_size_exp plan)
            (Phys_Mem_Access_Info_splittable plan)) (sw 0%nat)
      = Some ((n, bytes), sw 0%nat) ->
    goodmb Dr Dw (write_kind_of_flags aq rl con) (sw 0%nat) mm = true ->
    exec (write_kind_of_flags aq rl con) (sw 0%nat) = Some (wk, sw 0%nat) ->
    goodmb Dr Dw (checked_mem_write (Physaddr pa) width dat acc pbmt priv meta aq rl con)
      (sw 0%nat) mm = true.
  Proof.
    intros Hpacg Hpac Hsplitg Hsplit Hwkfg Hwkf.
    unfold checked_mem_write. apply goodmb_cer.
    gmm_lift Hpacg Hpac. cbn beta. cbn match.
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match beta.
    gmm_lift Hsplitg Hsplit. cbn beta zeta match.
    rewrite misaligned_order_split. cbn zeta.
    gmm_lift Hwkfg Hwkf. cbn beta.
    match goal with
    | |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
        assert (Hu : execR (Defs.untilMT vs m0 c bb) (sw 0%nat)
                     = Some (inr (MemAccessGen.wsplit_var N sk N), sw N));
        [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m0 c bb) (sw 0%nat) mm = true) ]
    end.
    { rewrite <- (MemAccessGen.wsplit_var0 N sk HN).
      unfold Defs.untilMT.
      match goal with
      | |- execR (Defs.untilMT' ?L _ ?c ?b _) _ = _ =>
          set (LL := L); set (CC := c); set (BB := b)
      end.
      assert (HL : LL = n)
        by (unfold LL; rewrite (MemAccessGen.wsplit_var0 N sk HN); reflexivity).
      clearbody LL. rewrite HL.
      apply (MemAccessGen.execR_untilMT'_chain CC BB N
               (MemAccessGen.wsplit_var N sk) sw n).
      - exact HN.
      - lia.
      - intros k Hk. unfold BB, MemAccessGen.wsplit_var.
        replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.min k (N - 1)) with k by lia.
        cbn match.
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ (sw k))). cbn beta.
        change (bits_of_physaddr (Physaddr pa)) with pa.
        rewrite (execR_liftR_seq _ _ _ _ _ (Hpmp k Hk)). cbn match.
        gm_ret_bind0.
        rewrite (execR_liftR_seq _ _ _ _ _ (Hmmio k Hk)). cbn match beta zeta.
        match goal with
        | |- execR (Defs.bind ?m0 ?post) (sw k) = _ =>
            assert (Hrr : execR m0 (sw k)
                          = Some (inr (andb (MemAccessGen.ws_seq sk k) (sk k)), sw (S k)))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _ (Hwram k Hk)). cbn beta.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hrr). cbn beta.
        destruct (Z.eqb (Z.of_nat k) (n - 1)) eqn:Eq; cbn match;
          rewrite execR_returnR_fwd; do 3 f_equal; unfold MemAccessGen.wsplit_var.
        + apply Z.eqb_eq in Eq.
          replace (Nat.eqb (S k) N) with true by (symmetry; apply Nat.eqb_eq; lia).
          replace (Nat.min (S k) (N - 1)) with k by lia. reflexivity.
        + apply Z.eqb_neq in Eq.
          replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
          replace (Nat.min (S k) (N - 1)) with (S k) by lia.
          replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. reflexivity.
      - intros k Hk. unfold CC, MemAccessGen.wsplit_var. cbn match.
        replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
        apply execR_returnR_fwd.
      - unfold CC, MemAccessGen.wsplit_var. cbn match. rewrite Nat.eqb_refl.
        apply execR_returnR_fwd. }
    { rewrite <- (MemAccessGen.wsplit_var0 N sk HN).
      unfold Defs.untilMT.
      match goal with
      | |- goodmb _ _ (Defs.untilMT' ?L _ ?c ?b _) _ _ = _ =>
          set (LL := L); set (CC := c); set (BB := b)
      end.
      assert (HL : LL = n)
        by (unfold LL; rewrite (MemAccessGen.wsplit_var0 N sk HN); reflexivity).
      clearbody LL. rewrite HL.
      apply (gm_untilMT'_chain Dr Dw CC BB mm N (MemAccessGen.wsplit_var N sk) sw n).
      - exact HN.
      - lia.
      - intros k Hk. unfold BB, MemAccessGen.wsplit_var.
        replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.min k (N - 1)) with k by lia.
        cbn match.
        gmm_liftT ltac:(apply goodmb_assert_exp'_true)
                  ltac:(apply exec_assert_exp'_true). cbn beta.
        change (bits_of_physaddr (Physaddr pa)) with pa.
        gmm_lift (Hpmpg k Hk) (Hpmp k Hk). cbn match.
        gm_ret_bind0.
        gmm_lift (Hmmiog k Hk) (Hmmio k Hk). cbn match beta zeta.
        match goal with
        | |- goodmb _ _ (Defs.bind ?m0 ?post) (sw k) _ = _ =>
            assert (Hrrg : goodmb Dr Dw m0 (sw k) mm = true);
            [ | assert (Hrr : execR m0 (sw k)
                        = Some (inr (andb (MemAccessGen.ws_seq sk k) (sk k)), sw (S k))) ]
        end.
        { gmm_lift (Hwramg k Hk) (Hwram k Hk). cbn beta. apply goodmb_returnm. }
        { rewrite (execR_liftR_seq _ _ _ _ _ (Hwram k Hk)). cbn beta.
          apply execR_returnR_fwd. }
        erewrite (gm_bindR Dr Dw _ _ (sw k) (sw (S k)) mm _ Hrrg Hrr). cbn beta.
        destruct (Z.eqb (Z.of_nat k) (n - 1)) eqn:Eq; cbn match; apply goodmb_returnm.
      - intros k Hk. unfold BB, MemAccessGen.wsplit_var.
        replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.min k (N - 1)) with k by lia.
        cbn match.
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ (sw k))). cbn beta.
        change (bits_of_physaddr (Physaddr pa)) with pa.
        rewrite (execR_liftR_seq _ _ _ _ _ (Hpmp k Hk)). cbn match.
        gm_ret_bind0.
        rewrite (execR_liftR_seq _ _ _ _ _ (Hmmio k Hk)). cbn match beta zeta.
        match goal with
        | |- execR (Defs.bind ?m0 ?post) (sw k) = _ =>
            assert (Hrr : execR m0 (sw k)
                          = Some (inr (andb (MemAccessGen.ws_seq sk k) (sk k)), sw (S k)))
        end.
        { rewrite (execR_liftR_seq _ _ _ _ _ (Hwram k Hk)). cbn beta.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hrr). cbn beta.
        destruct (Z.eqb (Z.of_nat k) (n - 1)) eqn:Eq; cbn match;
          rewrite execR_returnR_fwd; do 3 f_equal; unfold MemAccessGen.wsplit_var.
        + apply Z.eqb_eq in Eq.
          replace (Nat.eqb (S k) N) with true by (symmetry; apply Nat.eqb_eq; lia).
          replace (Nat.min (S k) (N - 1)) with k by lia. reflexivity.
        + apply Z.eqb_neq in Eq.
          replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
          replace (Nat.min (S k) (N - 1)) with (S k) by lia.
          replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. reflexivity.
      - intros k Hk. unfold CC, MemAccessGen.wsplit_var. cbn match.
        apply goodmb_returnm.
      - intros k Hk. unfold CC, MemAccessGen.wsplit_var. cbn match.
        replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
        apply execR_returnR_fwd.
      - unfold CC, MemAccessGen.wsplit_var. cbn match. rewrite Nat.eqb_refl.
        apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ (sw 0%nat) (sw N) mm
                (MemAccessGen.wsplit_var N sk N) Hug Hu).
    cbn beta zeta. unfold MemAccessGen.wsplit_var. cbn match.
    apply goodmb_returnm.
  Qed.

End GmCheckedMemWriteSplit.

Section GmMemWriteEaSplit.
  Context (Dr Dw : register -> bool).
  Context (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
          (ep : Privilege).
  Context (pa : mword 64) (width bytes : Z) (N : nat) (wk : write_kind) (s : mstate).
  Context (mm : PtBytes.pamap).
  Context (HN : (1 <= N)%nat).

  Notation n := (Z.of_nat N).
  Notation cpa k := (Physaddr (add_vec_int pa (Z.of_nat k * bytes))).

  Hypothesis Hpmp : forall k, (k < N)%nat ->
    exec (pmpCheck (cpa k) bytes acc ep) s = Some (None, s).
  Hypothesis Hpmpg : forall k, (k < N)%nat ->
    goodmb Dr Dw (pmpCheck (cpa k) bytes acc ep) s mm = true.

  Lemma goodmb_mem_write_ea_split (plan : Phys_Mem_Access_Info) :
    Dr mstatus = true -> Dr cur_privilege = true ->
    goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
            (register_lookup cur_privilege s.(sregs))) s mm = true ->
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
            (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
    goodmb Dr Dw (check_pma_with_pmp_priority acc pbmt ep (Physaddr pa) width false)
      s mm = true ->
    exec (check_pma_with_pmp_priority acc pbmt ep (Physaddr pa) width false) s
      = Some (Ok plan, s) ->
    goodmb Dr Dw (split_misaligned (Physaddr pa) width
            (Phys_Mem_Access_Info_granule_size_exp plan)
            (Phys_Mem_Access_Info_splittable plan)) s mm = true ->
    exec (split_misaligned (Physaddr pa) width
            (Phys_Mem_Access_Info_granule_size_exp plan)
            (Phys_Mem_Access_Info_splittable plan)) s = Some ((n, bytes), s) ->
    goodmb Dr Dw (write_kind_of_flags false false false) s mm = true ->
    exec (write_kind_of_flags false false false) s = Some (wk, s) ->
    goodmb Dr Dw (mem_write_ea (Physaddr pa) width acc pbmt false false false) s mm
      = true.
  Proof.
    intros HDm HDc Heffg Heff Hpacg Hpac Hsplitg Hsplit Hwkfg Hwkf.
    assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
      by (rewrite goodmb_read_reg; exact HDm).
    assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
      by (rewrite goodmb_read_reg; exact HDc).
    unfold mem_write_ea. apply goodmb_cer.
    gmm_lift Hmst (exec_read_reg mstatus s). cbn beta.
    gmm_lift Hcpr (exec_read_reg cur_privilege s). cbn beta.
    gmm_lift Heffg Heff. cbn beta.
    gmm_lift Hpacg Hpac. cbn beta. cbn match.
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match beta.
    gmm_lift Hsplitg Hsplit. cbn beta zeta match.
    rewrite misaligned_order_split. cbn zeta.
    gmm_lift Hwkfg Hwkf. cbn beta.
    match goal with
    | |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?bb) _] =>
        assert (Hu : execR (Defs.untilMT vs m0 c bb) s
                     = Some (inr (MemAccessGen.eavar N N), s));
        [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m0 c bb) s mm = true) ]
    end.
    { rewrite <- (MemAccessGen.eavar0 N HN).
      unfold Defs.untilMT.
      match goal with
      | |- execR (Defs.untilMT' ?L _ ?c ?b _) _ = _ =>
          set (LL := L); set (CC := c); set (BB := b)
      end.
      assert (HL : LL = n)
        by (unfold LL; rewrite (MemAccessGen.eavar0 N HN); reflexivity).
      clearbody LL. rewrite HL.
      apply (MemAccessGen.execR_untilMT'_chain CC BB N (MemAccessGen.eavar N)
               (fun _ => s) n).
      - exact HN.
      - lia.
      - intros k Hk. unfold BB, MemAccessGen.eavar.
        replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.min k (N - 1)) with k by lia.
        cbn match.
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr pa)) with pa.
        rewrite (execR_liftR_seq _ _ _ _ _ (Hpmp k Hk)). cbn match.
        gm_ret_bind0.
        destruct (Z.eqb (Z.of_nat k) (n - 1)) eqn:Eq; cbn match zeta;
          rewrite execR_returnR_fwd; do 3 f_equal; unfold MemAccessGen.eavar.
        + apply Z.eqb_eq in Eq.
          replace (Nat.eqb (S k) N) with true by (symmetry; apply Nat.eqb_eq; lia).
          replace (Nat.min (S k) (N - 1)) with k by lia. reflexivity.
        + apply Z.eqb_neq in Eq.
          replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
          replace (Nat.min (S k) (N - 1)) with (S k) by lia.
          replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. reflexivity.
      - intros k Hk. unfold CC, MemAccessGen.eavar. cbn match.
        replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
        apply execR_returnR_fwd.
      - unfold CC, MemAccessGen.eavar. cbn match. rewrite Nat.eqb_refl.
        apply execR_returnR_fwd. }
    { rewrite <- (MemAccessGen.eavar0 N HN).
      unfold Defs.untilMT.
      match goal with
      | |- goodmb _ _ (Defs.untilMT' ?L _ ?c ?b _) _ _ = _ =>
          set (LL := L); set (CC := c); set (BB := b)
      end.
      assert (HL : LL = n)
        by (unfold LL; rewrite (MemAccessGen.eavar0 N HN); reflexivity).
      clearbody LL. rewrite HL.
      apply (gm_untilMT'_chain Dr Dw CC BB mm N (MemAccessGen.eavar N) (fun _ => s) n).
      - exact HN.
      - lia.
      - intros k Hk. unfold BB, MemAccessGen.eavar.
        replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.min k (N - 1)) with k by lia.
        cbn match.
        gmm_liftT ltac:(apply goodmb_assert_exp'_true)
                  ltac:(apply exec_assert_exp'_true). cbn beta.
        change (bits_of_physaddr (Physaddr pa)) with pa.
        gmm_lift (Hpmpg k Hk) (Hpmp k Hk). cbn match.
        gm_ret_bind0.
        destruct (Z.eqb (Z.of_nat k) (n - 1)) eqn:Eq; cbn match zeta;
          apply goodmb_returnm.
      - intros k Hk. unfold BB, MemAccessGen.eavar.
        replace (Nat.eqb k N) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace (Nat.min k (N - 1)) with k by lia.
        cbn match.
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr pa)) with pa.
        rewrite (execR_liftR_seq _ _ _ _ _ (Hpmp k Hk)). cbn match.
        gm_ret_bind0.
        destruct (Z.eqb (Z.of_nat k) (n - 1)) eqn:Eq; cbn match zeta;
          rewrite execR_returnR_fwd; do 3 f_equal; unfold MemAccessGen.eavar.
        + apply Z.eqb_eq in Eq.
          replace (Nat.eqb (S k) N) with true by (symmetry; apply Nat.eqb_eq; lia).
          replace (Nat.min (S k) (N - 1)) with k by lia. reflexivity.
        + apply Z.eqb_neq in Eq.
          replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
          replace (Nat.min (S k) (N - 1)) with (S k) by lia.
          replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. reflexivity.
      - intros k Hk. unfold CC, MemAccessGen.eavar. cbn match.
        apply goodmb_returnm.
      - intros k Hk. unfold CC, MemAccessGen.eavar. cbn match.
        replace (Nat.eqb (S k) N) with false by (symmetry; apply Nat.eqb_neq; lia).
        apply execR_returnR_fwd.
      - unfold CC, MemAccessGen.eavar. cbn match. rewrite Nat.eqb_refl.
        apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s s mm (MemAccessGen.eavar N N) Hug Hu).
    cbn beta zeta. unfold MemAccessGen.eavar. cbn match.
    apply goodmb_returnm.
  Qed.

End GmMemWriteEaSplit.

Lemma goodmb_mem_write_value_of_checked_plain (Dr Dw : register -> bool)
    (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (pa : mword 64) (width : Z) (dat : mword (8 * width)) (b : bool)
    (ep : Privilege) s s' mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (checked_mem_write (Physaddr pa) width dat acc pbmt ep default_meta
                  false false false) s mm = true ->
  exec (checked_mem_write (Physaddr pa) width dat acc pbmt ep default_meta
          false false false) s = Some (Ok b, s') ->
  goodmb Dr Dw (mem_write_value (Physaddr pa) width dat acc pbmt false false false)
    s mm = true.
Proof.
  intros HDm HDc Heffg Heff Hchkg Hchk.
  assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDc).
  unfold mem_write_value, mem_write_value_meta.
  gmm_peel Hmst (exec_read_reg mstatus s).
  gmm_peel Hcpr (exec_read_reg cur_privilege s).
  gmm_peel Heffg Heff.
  unfold mem_write_value_priv_meta.
  gmm_peel Hchkg Hchk. cbn match.
  unfold mem_write_callback. apply goodmb_returnm.
Qed.

Lemma bytes_owned_of_spec (mm : PtBytes.pamap) (pa : Arch.pa) (n : N) :
  (forall j : nat, (N.of_nat j < n)%N -> is_Some (mm !! RiscvModelBytes.pa_add pa j)) ->
  bytes_owned mm pa n = true.
Proof.
  intros H. unfold bytes_owned. apply List.forallb_forall. intros j Hin.
  apply List.in_seq in Hin. apply bool_decide_eq_true_2. apply H. lia.
Qed.

Lemma bytes_owned_chunk (mm : PtBytes.pamap) (pa : mword 64) (W bytes : Z) (N k : nat) :
  0 < bytes -> Z.of_nat N * bytes = W -> (k < N)%nat ->
  bytes_owned mm pa (Z.to_N W) = true ->
  bytes_owned mm (add_vec_int pa (Z.of_nat k * bytes)) (Z.to_N bytes) = true.
Proof.
  intros Hb Hw Hk Hown.
  assert (HbN : Z.to_nat W = (N * Z.to_nat bytes)%nat).
  { rewrite <- Hw. rewrite Z2Nat.inj_mul; [| lia | lia]. rewrite Nat2Z.id. reflexivity. }
  apply bytes_owned_of_spec. intros j Hj.
  rewrite (pa_add_chunk pa k bytes ltac:(lia)). rewrite pa_add_bump2.
  apply (bytes_owned_spec mm pa (Z.to_N W) Hown).
  assert (Hjn : (j < Z.to_nat bytes)%nat) by lia.
  assert (Hlt : (k * Z.to_nat bytes + j < Z.to_nat W)%nat) by (rewrite HbN; nia).
  lia.
Qed.

Lemma exec_bind_assert_false {X} (msg : string) (f : false = true -> M X) s :
  exec (Defs.bind (Defs.assert_exp' false msg) f) s = None.
Proof. reflexivity. Qed.

Lemma goodmb_assert_seq_of_exec (Dr Dw : register -> bool) {X}
    (b : bool) (msg : string) (f : b = true -> M X) s mm r s' :
  exec (Defs.bind (Defs.assert_exp' b msg) f) s = Some (r, s') ->
  (forall e : b = true, goodmb Dr Dw (f e) s mm = true) ->
  goodmb Dr Dw (Defs.bind (Defs.assert_exp' b msg) f) s mm = true.
Proof.
  intros He Hf. destruct b.
  - erewrite gm_bind;
      [ | apply goodmb_assert_exp'_true | apply exec_assert_exp'_true ].
    apply Hf.
  - rewrite exec_bind_assert_false in He. discriminate He.
Qed.

Lemma goodmb_split_misaligned_of_exec (Dr Dw : register -> bool)
    (paddr : physaddr) (width awe : Z) (sp : Splittability) s mm r s' :
  exec (split_misaligned paddr width awe sp) s = Some (r, s') ->
  goodmb Dr Dw (split_misaligned paddr width awe sp) s mm = true.
Proof.
  destruct paddr as [addr]. intros He.
  unfold split_misaligned in He |- *. cbn zeta in He |- *.
  destruct (orb (generic_eq sp CannotSplit)
              (orb (Z.eqb (Z.rem (uint addr) width) 0)
                 (allowed_misaligned (subrange_vec_dec addr (Z.sub xlen 1) 0)
                    width awe))) eqn:E.
  - apply goodmb_returnm.
  - unfold sys_misaligned_byte_by_byte in He |- *. cbn match in He |- *.
    unfold split_access in He |- *. cbn zeta in He |- *.
    eapply goodmb_assert_seq_of_exec; [ exact He | intros; apply goodmb_returnm ].
Qed.

Section MisPhys.
  Context (pa : mword 64) (W : Z) (s : mstate).
  Context (HWpos : 0 < W) (HWle : W <= 8).
  Context (HA : pmpAddrMatchType_encdec_backwards
                  (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR).
  Context (Hord : zopz0zKzJ_u (zeros' 64)
                    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false).
  Context (Hcovp : (ram_base + ram_size
                    <= uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) * 4)%Z).
  Context (Hhtif : register_lookup htif_tohost_base s.(sregs) = None).
  Context (Hall : pma_allows_all (register_lookup pma_regions s.(sregs))).
  Context (Hwin : forall j : nat, (j < Z.to_nat W)%nat -> addr_is_ram (pa_add pa j)).

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
      by exact (ram_fetch_pmp _ _ bytes (Z.to_nat bytes - 1)%nat Hb ltac:(lia) Hbu
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

  Local Lemma chunk_range (bytes : Z) (N k : nat) :
    0 < bytes -> bytes <= 8 -> uint (to_bits 64 bytes) = bytes ->
    Z.of_nat N * bytes = W -> (k < N)%nat ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint (add_vec_int pa (Z.of_nat k * bytes))) (uint (to_bits 64 bytes)) = PMP_Match.
  Proof.
    intros Hb Hb8 Hbu Hw Hk.
    assert (Hlast : (Z.to_nat bytes - 1 < Z.to_nat bytes)%nat) by lia.
    assert (Hr0 : addr_is_ram (add_vec_int pa (Z.of_nat k * bytes))).
    { rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
      exact (chunk_ram bytes N k 0%nat Hb Hw Hk ltac:(lia)). }
    assert (HrL : addr_is_ram (pa_add (add_vec_int pa (Z.of_nat k * bytes))
                                 (Z.to_nat bytes - 1)))
      by exact (chunk_ram bytes N k (Z.to_nat bytes - 1)%nat Hb Hw Hk Hlast).
    exact (ram_fetch_pmp _ _ bytes (Z.to_nat bytes - 1)%nat Hb ltac:(lia) Hbu
             ltac:(lia) Hr0 HrL Hcovp).
  Qed.

  Local Lemma chunk_clint (bytes : Z) (N k : nat) :
    0 < bytes -> Z.of_nat N * bytes = W -> (k < N)%nat -> forall (t : mstate),
    exec (within_clint (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes) t
      = Some (false, t).
  Proof.
    intros Hb Hw Hk t.
    assert (Hr0 : addr_is_ram (add_vec_int pa (Z.of_nat k * bytes))).
    { rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
      exact (chunk_ram bytes N k 0%nat Hb Hw Hk ltac:(lia)). }
    exact (within_clint_false _ bytes t (addr_is_ram_not_in_clint _ Hr0) Hb).
  Qed.

  Local Lemma chunk_sig (bytes : Z) (N k : nat) :
    0 < bytes -> Z.of_nat N * bytes = W -> (k < N)%nat -> forall (t : mstate),
    exec (within_sig (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes) t
      = Some (false, t).
  Proof.
    intros Hb Hw Hk t.
    assert (Hr0 : addr_is_ram (add_vec_int pa (Z.of_nat k * bytes))).
    { rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
      exact (chunk_ram bytes N k 0%nat Hb Hw Hk ltac:(lia)). }
    exact (within_sig_false _ bytes t (addr_is_ram_not_in_sig _ Hr0) Hb).
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
      as (region & Hpmam & _ & Hrd & _ & _ & _ & _ & Hmisx & _).
    destruct (exec_pmaCheck_ram_load_plan W pa PBMT_PMA region s Hpmam Hrd Hmisx)
      as (plan & Hpma).
    assert (Hcpp : exec (check_pma_with_pmp_priority (Load Data) PBMT_PMA User
                           (Physaddr pa) W false) s = Some (Ok plan, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _ Hpma). cbn match. apply exec_returnM. }
    destruct (split_misaligned_phys_derive W pa
                (Phys_Mem_Access_Info_granule_size_exp plan)
                (Phys_Mem_Access_Info_splittable plan) s HWpos HWle)
      as (N & bytes & HN & Hwidth & Hbpos & Hble & Hbuint & Hsplit).
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

  Lemma goodmb_mem_read_mis_U (Dr Dw : register -> bool) mm :
    Dr mstatus = true -> Dr cur_privilege = true ->
    Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
    Dr pma_regions = true -> Dr htif_tohost_base = true ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    eq_vec (_get_Pmpcfg_ent_R
              (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    (forall j : nat, (j < Z.to_nat W)%nat -> is_Some (s.(mem) !! pa_add pa j)) ->
    bytes_owned mm pa (Z.to_N W) = true ->
    goodmb Dr Dw (mem_read (Load Data) PBMT_PMA (Physaddr pa) W false false false)
      s mm = true.
  Proof.
    intros HDm HDcp HDc HDa HDp HDh Hmprv Hcp HRp Hpres Hown.
    pose proof HWpos as Hpos. pose proof HWle as Hle.
    assert (Hr0 : addr_is_ram pa).
    { rewrite <- (pa_add_0 pa). apply Hwin. lia. }
    assert (HrL : addr_is_ram (pa_add pa (Z.to_nat W - 1))) by (apply Hwin; lia).
    destruct (pma_all_ram Hall pa W
                (pma_access_ram_at pa W (Z.to_nat W - 1)%nat ltac:(lia) Hr0 HrL
                   (pma_width_le W 8 Hpos Hle eq_refl)))
      as (region & Hpmam & _ & Hrd & _ & _ & _ & _ & Hmisx & _).
    destruct (exec_pmaCheck_ram_load_plan W pa PBMT_PMA region s Hpmam Hrd Hmisx)
      as (plan & Hpma).
    pose proof (goodmb_pmaCheck_ram_load_plan Dr Dw W pa PBMT_PMA region s mm
                  HDp Hpmam Hrd Hmisx) as Hpmag.
    assert (Hcpp : exec (check_pma_with_pmp_priority (Load Data) PBMT_PMA User
                           (Physaddr pa) W false) s = Some (Ok plan, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _ Hpma). cbn match. apply exec_returnM. }
    pose proof (goodmb_check_pma_with_pmp_priority Dr Dw (Load Data) PBMT_PMA User
                  (Physaddr pa) W false plan s mm Hpmag Hpma) as Hcppg.
    destruct (split_misaligned_phys_derive W pa
                (Phys_Mem_Access_Info_granule_size_exp plan)
                (Phys_Mem_Access_Info_splittable plan) s HWpos HWle)
      as (N & bytes & HN & Hwidth & Hbpos & Hble & Hbuint & Hsplit).
    pose proof (goodmb_split_misaligned_of_exec Dr Dw (Physaddr pa) W
                  (Phys_Mem_Access_Info_granule_size_exp plan)
                  (Phys_Mem_Access_Info_splittable plan) s mm _ _ Hsplit) as Hsplitg.
    assert (Hb8 : bytes <= 8) by lia.
    assert (Hrange : forall k, (k < N)%nat ->
              pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
                (uint (add_vec_int pa (Z.of_nat k * bytes))) (uint (to_bits 64 bytes))
              = PMP_Match)
      by (intros k Hk; exact (chunk_range bytes N k Hbpos Hb8 Hbuint Hwidth Hk)).
    assert (Hpmp : forall k, (k < N)%nat ->
              exec (pmpCheck (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes
                      (Load Data) User) s = Some (None, s))
      by (intros k Hk;
          exact (exec_pmpCheck_user_grant_load _ bytes s HA Hord (Hrange k Hk) HRp)).
    assert (Hpmpg : forall k, (k < N)%nat ->
              goodmb Dr Dw (pmpCheck (Physaddr (add_vec_int pa (Z.of_nat k * bytes)))
                              bytes (Load Data) User) s mm = true)
      by (intros k Hk;
          exact (goodmb_pmpCheck_user_grant_load Dr Dw _ bytes s mm HDc HDa HA Hord
                   (Hrange k Hk) HRp)).
    assert (Hmmio : forall k, (k < N)%nat ->
              exec (within_mmio_readable
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes) s
              = Some (false, s)).
    { intros k Hk. unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ (chunk_clint bytes N k Hbpos Hwidth Hk s)).
      cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ (chunk_sig bytes N k Hbpos Hwidth Hk s)).
      cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false _ bytes s Hhtif)).
      cbn match. reflexivity. }
    assert (Hmmiog : forall k, (k < N)%nat ->
              goodmb Dr Dw (within_mmio_readable
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes) s mm = true)
      by (intros k Hk;
          exact (goodmb_within_mmio_readable Dr Dw _ bytes s mm HDh Hhtif
                   (chunk_clint bytes N k Hbpos Hwidth Hk s)
                   (chunk_sig bytes N k Hbpos Hwidth Hk s))).
    assert (Hdevk : forall k, (k < N)%nat ->
              dev_addr (add_vec_int pa (Z.of_nat k * bytes)) = false).
    { intros k Hk. apply addr_is_ram_not_dev.
      rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
      exact (chunk_ram bytes N k 0%nat Hbpos Hwidth Hk ltac:(lia)). }
    assert (Hramc : forall k, (k < N)%nat ->
              exec (read_ram Read_plain
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes false) s
              = Some ((ram_chunk Read_plain (add_vec_int pa (Z.of_nat k * bytes))
                         bytes false s, tt), s)).
    { intros k Hk. apply exec_read_ram_chunk.
      apply exec_read_ram_plain_gen.
      - exact (Hdevk k Hk).
      - apply read_bytes_is_Some. intros j Hj.
        rewrite (pa_add_chunk pa k bytes ltac:(lia)). rewrite pa_add_bump2.
        apply Hpres. exact (chunk_off bytes N k j Hbpos Hwidth Hk ltac:(lia)). }
    assert (Hramcg : forall k, (k < N)%nat ->
              goodmb Dr Dw (read_ram Read_plain
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes false)
                s mm = true).
    { intros k Hk.
      exact (goodmb_read_ram_of_exec Dr Dw Read_plain bytes
               (add_vec_int pa (Z.of_nat k * bytes)) false _ s s mm eq_refl
               (Hdevk k Hk)
               (bytes_owned_chunk mm pa W bytes N k Hbpos Hwidth Hk Hown)
               (Hramc k Hk)). }
    assert (Hrkf : exec (read_kind_of_flags false false false) s
                   = Some (rv64d_types.Read_plain, s))
      by (unfold read_kind_of_flags; apply exec_returnM).
    assert (Hrkg : goodmb Dr Dw (read_kind_of_flags false false false) s mm = true)
      by (unfold read_kind_of_flags; apply goodmb_returnm).
    pose proof (exec_checked_mem_read_split (Load Data) PBMT_PMA User pa W bytes N
                  false false false false Read_plain
                  (fun k => ram_chunk Read_plain (add_vec_int pa (Z.of_nat k * bytes))
                              bytes false s) s HN Hpmp Hmmio Hramc plan Hcpp Hsplit
                  Hrkf) as Hchk.
    pose proof (goodmb_checked_mem_read_split Dr Dw (Load Data) PBMT_PMA User pa W
                  bytes N false false false false Read_plain
                  (fun k => ram_chunk Read_plain (add_vec_int pa (Z.of_nat k * bytes))
                              bytes false s) s mm HN
                  Hpmp Hpmpg Hmmio Hmmiog Hramc Hramcg plan
                  Hcppg Hcpp Hsplitg Hsplit Hrkg Hrkf) as Hchkg.
    exact (goodmb_mem_read_data_U Dr Dw W PBMT_PMA pa _ s mm
             HDm HDcp Hmprv Hcp Hchkg Hchk).
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
      as (region & Hpmam & _ & _ & Hwr & _ & _ & _ & Hmisx & _).
    destruct (exec_pmaCheck_ram_store_plan W pa PBMT_PMA region s Hpmam Hwr Hmisx)
      as (plan & Hpma).
    assert (Hcpp : exec (check_pma_with_pmp_priority (Store Data) PBMT_PMA User
                           (Physaddr pa) W false) s = Some (Ok plan, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _ Hpma). cbn match. apply exec_returnM. }
    destruct (split_misaligned_phys_derive W pa
                (Phys_Mem_Access_Info_granule_size_exp plan)
                (Phys_Mem_Access_Info_splittable plan) s HWpos HWle)
      as (N & bytes & HN & Hwidth & Hbpos & Hble & Hbuint & Hsplit).
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

  Lemma goodmb_mem_write_ea_mis_U (Dr Dw : register -> bool) mm :
    Dr mstatus = true -> Dr cur_privilege = true ->
    Dr pmpcfg_n = true -> Dr pmpaddr_n = true -> Dr pma_regions = true ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    eq_vec (_get_Pmpcfg_ent_W
              (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    goodmb Dr Dw (mem_write_ea (Physaddr pa) W (Store Data) PBMT_PMA false false false)
      s mm = true.
  Proof.
    intros HDm HDcp HDc HDa HDp Hmprv Hcp HWp.
    pose proof HWpos as Hpos. pose proof HWle as Hle.
    assert (Hr0 : addr_is_ram pa).
    { rewrite <- (pa_add_0 pa). apply Hwin. lia. }
    assert (HrL : addr_is_ram (pa_add pa (Z.to_nat W - 1))) by (apply Hwin; lia).
    destruct (pma_all_ram Hall pa W
                (pma_access_ram_at pa W (Z.to_nat W - 1)%nat ltac:(lia) Hr0 HrL
                   (pma_width_le W 8 Hpos Hle eq_refl)))
      as (region & Hpmam & _ & _ & Hwr & _ & _ & _ & Hmisx & _).
    destruct (exec_pmaCheck_ram_store_plan W pa PBMT_PMA region s Hpmam Hwr Hmisx)
      as (plan & Hpma).
    pose proof (goodmb_pmaCheck_ram_store_plan Dr Dw W pa PBMT_PMA region s mm
                  HDp Hpmam Hwr Hmisx) as Hpmag.
    assert (Hcpp : exec (check_pma_with_pmp_priority (Store Data) PBMT_PMA User
                           (Physaddr pa) W false) s = Some (Ok plan, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _ Hpma). cbn match. apply exec_returnM. }
    pose proof (goodmb_check_pma_with_pmp_priority Dr Dw (Store Data) PBMT_PMA User
                  (Physaddr pa) W false plan s mm Hpmag Hpma) as Hcppg.
    destruct (split_misaligned_phys_derive W pa
                (Phys_Mem_Access_Info_granule_size_exp plan)
                (Phys_Mem_Access_Info_splittable plan) s HWpos HWle)
      as (N & bytes & HN & Hwidth & Hbpos & Hble & Hbuint & Hsplit).
    pose proof (goodmb_split_misaligned_of_exec Dr Dw (Physaddr pa) W
                  (Phys_Mem_Access_Info_granule_size_exp plan)
                  (Phys_Mem_Access_Info_splittable plan) s mm _ _ Hsplit) as Hsplitg.
    assert (Hb8 : bytes <= 8) by lia.
    assert (Hrange : forall k, (k < N)%nat ->
              pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
                (uint (add_vec_int pa (Z.of_nat k * bytes))) (uint (to_bits 64 bytes))
              = PMP_Match)
      by (intros k Hk; exact (chunk_range bytes N k Hbpos Hb8 Hbuint Hwidth Hk)).
    assert (Hpmp : forall k, (k < N)%nat ->
              exec (pmpCheck (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes
                      (Store Data) User) s = Some (None, s))
      by (intros k Hk;
          exact (exec_pmpCheck_user_grant_store _ bytes s HA Hord (Hrange k Hk) HWp)).
    assert (Hpmpg : forall k, (k < N)%nat ->
              goodmb Dr Dw (pmpCheck (Physaddr (add_vec_int pa (Z.of_nat k * bytes)))
                              bytes (Store Data) User) s mm = true)
      by (intros k Hk;
          exact (goodmb_pmpCheck_user_grant_store Dr Dw _ bytes s mm HDc HDa HA Hord
                   (Hrange k Hk) HWp)).
    assert (Heff : exec (effectivePrivilege (Store Data)
                           (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (User, s)).
    { rewrite <- Hcp. apply exec_effectivePrivilege_mprv0. exact Hmprv. }
    assert (Heffg : goodmb Dr Dw (effectivePrivilege (Store Data)
                           (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s mm = true)
      by (apply goodmb_effectivePrivilege_mprv0; exact Hmprv).
    assert (Hwkf : exec (write_kind_of_flags false false false) s
                   = Some (rv64d_types.Write_plain, s))
      by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
    assert (Hwkg : goodmb Dr Dw (write_kind_of_flags false false false) s mm = true)
      by (unfold write_kind_of_flags; cbn match; apply goodmb_returnm).
    exact (goodmb_mem_write_ea_split Dr Dw (Store Data) PBMT_PMA User pa W bytes N
             rv64d_types.Write_plain s mm HN Hpmp Hpmpg plan
             HDm HDcp Heffg Heff Hcppg Hcpp Hsplitg Hsplit Hwkg Hwkf).
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
      as (region & Hpmam & _ & _ & Hwr & _ & _ & _ & Hmisx & _).
    destruct (exec_pmaCheck_ram_store_plan W pa PBMT_PMA region s Hpmam Hwr Hmisx)
      as (plan & Hpma).
    assert (Hcpp : exec (check_pma_with_pmp_priority (Store Data) PBMT_PMA User
                           (Physaddr pa) W false) s = Some (Ok plan, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _ Hpma). cbn match. apply exec_returnM. }
    destruct (split_misaligned_phys_derive W pa
                (Phys_Mem_Access_Info_granule_size_exp plan)
                (Phys_Mem_Access_Info_splittable plan) s HWpos HWle)
      as (N & bytes & HN & Hwidth & Hbpos & Hble & Hbuint & Hsplit).
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
        exact (ram_fetch_pmp _ _ bytes (Z.to_nat bytes - 1)%nat Hbpos ltac:(lia) Hbuint
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

  Lemma goodmb_mem_write_value_mis_U (Dr Dw : register -> bool)
      (dat : mword (8 * W)) mm :
    Dr mstatus = true -> Dr cur_privilege = true ->
    Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
    Dr pma_regions = true -> Dr htif_tohost_base = true ->
    eq_vec (_get_Mstatus_MPRV (register_lookup mstatus s.(sregs))) ('b"1") = false ->
    register_lookup cur_privilege s.(sregs) = User ->
    eq_vec (_get_Pmpcfg_ent_W
              (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
    bytes_owned mm pa (Z.to_N W) = true ->
    goodmb Dr Dw (mem_write_value (Physaddr pa) W dat (Store Data) PBMT_PMA
                    false false false) s mm = true.
  Proof.
    intros HDm HDcp HDc HDa HDp HDh Hmprv Hcp HWp Hown.
    pose proof HWpos as Hpos. pose proof HWle as Hle.
    assert (Hr0 : addr_is_ram pa).
    { rewrite <- (pa_add_0 pa). apply Hwin. lia. }
    assert (HrL : addr_is_ram (pa_add pa (Z.to_nat W - 1))) by (apply Hwin; lia).
    destruct (pma_all_ram Hall pa W
                (pma_access_ram_at pa W (Z.to_nat W - 1)%nat ltac:(lia) Hr0 HrL
                   (pma_width_le W 8 Hpos Hle eq_refl)))
      as (region & Hpmam & _ & _ & Hwr & _ & _ & _ & Hmisx & _).
    destruct (exec_pmaCheck_ram_store_plan W pa PBMT_PMA region s Hpmam Hwr Hmisx)
      as (plan & Hpma).
    pose proof (goodmb_pmaCheck_ram_store_plan Dr Dw W pa PBMT_PMA region s mm
                  HDp Hpmam Hwr Hmisx) as Hpmag.
    assert (Hcpp : exec (check_pma_with_pmp_priority (Store Data) PBMT_PMA User
                           (Physaddr pa) W false) s = Some (Ok plan, s)).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _ Hpma). cbn match. apply exec_returnM. }
    pose proof (goodmb_check_pma_with_pmp_priority Dr Dw (Store Data) PBMT_PMA User
                  (Physaddr pa) W false plan s mm Hpmag Hpma) as Hcppg.
    destruct (split_misaligned_phys_derive W pa
                (Phys_Mem_Access_Info_granule_size_exp plan)
                (Phys_Mem_Access_Info_splittable plan) s HWpos HWle)
      as (N & bytes & HN & Hwidth & Hbpos & Hble & Hbuint & Hsplit).
    pose proof (goodmb_split_misaligned_of_exec Dr Dw (Physaddr pa) W
                  (Phys_Mem_Access_Info_granule_size_exp plan)
                  (Phys_Mem_Access_Info_splittable plan) s mm _ _ Hsplit) as Hsplitg.
    assert (Hb8 : bytes <= 8) by lia.
    assert (Hdevk : forall k, (k < N)%nat ->
              dev_addr (add_vec_int pa (Z.of_nat k * bytes)) = false).
    { intros k Hk. apply addr_is_ram_not_dev.
      rewrite <- (pa_add_0 (add_vec_int pa (Z.of_nat k * bytes))).
      exact (chunk_ram bytes N k 0%nat Hbpos Hwidth Hk ltac:(lia)). }
    assert (Hregs : forall k, (k <= N)%nat ->
              (wchain bytes dat k).(sregs) = s.(sregs))
      by (intros k Hk;
          exact (proj1 (wchain_regs bytes N dat Hbpos Hwidth k Hk))).
    assert (Hrange : forall k, (k < N)%nat ->
              pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
                (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
                (uint (add_vec_int pa (Z.of_nat k * bytes))) (uint (to_bits 64 bytes))
              = PMP_Match)
      by (intros k Hk; exact (chunk_range bytes N k Hbpos Hb8 Hbuint Hwidth Hk)).
    assert (Hpmp : forall k, (k < N)%nat ->
              exec (pmpCheck (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes
                      (Store Data) User) (wchain bytes dat k)
              = Some (None, wchain bytes dat k)).
    { intros k Hk.
      apply (exec_pmpCheck_user_grant_store _ bytes _).
      - rewrite (Hregs k ltac:(lia)). exact HA.
      - rewrite (Hregs k ltac:(lia)). exact Hord.
      - rewrite (Hregs k ltac:(lia)). exact (Hrange k Hk).
      - rewrite (Hregs k ltac:(lia)). exact HWp. }
    assert (Hpmpg : forall k, (k < N)%nat ->
              goodmb Dr Dw (pmpCheck (Physaddr (add_vec_int pa (Z.of_nat k * bytes)))
                      bytes (Store Data) User) (wchain bytes dat k) mm = true).
    { intros k Hk.
      apply (goodmb_pmpCheck_user_grant_store Dr Dw _ bytes _ mm HDc HDa).
      - rewrite (Hregs k ltac:(lia)). exact HA.
      - rewrite (Hregs k ltac:(lia)). exact Hord.
      - rewrite (Hregs k ltac:(lia)). exact (Hrange k Hk).
      - rewrite (Hregs k ltac:(lia)). exact HWp. }
    assert (Hh : forall k, (k <= N)%nat ->
              register_lookup htif_tohost_base (wchain bytes dat k).(sregs) = None)
      by (intros k Hk; rewrite (Hregs k Hk); exact Hhtif).
    assert (Hmmio : forall k, (k < N)%nat ->
              exec (within_mmio_writable
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes)
                (wchain bytes dat k) = Some (false, wchain bytes dat k)).
    { intros k Hk. unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _
                 (chunk_clint bytes N k Hbpos Hwidth Hk (wchain bytes dat k))).
      cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _
                 (chunk_sig bytes N k Hbpos Hwidth Hk (wchain bytes dat k))).
      cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _
                 (within_htif_false _ bytes (wchain bytes dat k)
                    (Hh k ltac:(lia)))).
      cbn match. reflexivity. }
    assert (Hmmiog : forall k, (k < N)%nat ->
              goodmb Dr Dw (within_mmio_writable
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes)
                (wchain bytes dat k) mm = true)
      by (intros k Hk;
          exact (goodmb_within_mmio_writable Dr Dw _ bytes (wchain bytes dat k) mm
                   HDh (Hh k ltac:(lia))
                   (chunk_clint bytes N k Hbpos Hwidth Hk (wchain bytes dat k))
                   (chunk_sig bytes N k Hbpos Hwidth Hk (wchain bytes dat k)))).
    assert (Hwram : forall k, (k < N)%nat ->
              exec (write_ram rv64d_types.Write_plain
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes
                      (MemAccessGen.wvc W bytes dat k) tt) (wchain bytes dat k)
              = Some (true, wchain bytes dat (S k))).
    { intros k Hk.
      destruct (exec_write_ram_plain_gen bytes (add_vec_int pa (Z.of_nat k * bytes))
                  (MemAccessGen.wvc W bytes dat k) (wchain bytes dat k)
                  (Hdevk k Hk)) as (nn & v & Hwr2).
      cbn [wchain]. rewrite Hwr2. reflexivity. }
    assert (Hwramg : forall k, (k < N)%nat ->
              goodmb Dr Dw (write_ram rv64d_types.Write_plain
                      (Physaddr (add_vec_int pa (Z.of_nat k * bytes))) bytes
                      (MemAccessGen.wvc W bytes dat k) tt) (wchain bytes dat k) mm
              = true)
      by (intros k Hk;
          exact (goodmb_write_ram Dr Dw rv64d_types.Write_plain bytes
                   (add_vec_int pa (Z.of_nat k * bytes))
                   (MemAccessGen.wvc W bytes dat k) (wchain bytes dat k) mm
                   eq_refl (Hdevk k Hk)
                   (bytes_owned_chunk mm pa W bytes N k Hbpos Hwidth Hk Hown))).
    assert (Heff : exec (effectivePrivilege (Store Data)
                           (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s = Some (User, s)).
    { rewrite <- Hcp. apply exec_effectivePrivilege_mprv0. exact Hmprv. }
    assert (Heffg : goodmb Dr Dw (effectivePrivilege (Store Data)
                           (register_lookup mstatus s.(sregs))
                           (register_lookup cur_privilege s.(sregs))) s mm = true)
      by (apply goodmb_effectivePrivilege_mprv0; exact Hmprv).
    assert (Hwkf : exec (write_kind_of_flags false false false) s
                   = Some (rv64d_types.Write_plain, s))
      by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
    assert (Hwkg : goodmb Dr Dw (write_kind_of_flags false false false) s mm = true)
      by (unfold write_kind_of_flags; cbn match; apply goodmb_returnm).
    pose proof (exec_checked_mem_write_split (Store Data) PBMT_PMA User pa W bytes N
                  false false false tt rv64d_types.Write_plain dat (fun _ => true)
                  (wchain bytes dat) HN Hpmp Hmmio Hwram plan Hcpp Hsplit Hwkf) as Hchk.
    pose proof (goodmb_checked_mem_write_split Dr Dw (Store Data) PBMT_PMA User pa W
                  bytes N false false false tt rv64d_types.Write_plain dat
                  (fun _ => true) (wchain bytes dat) mm HN
                  Hpmp Hpmpg Hmmio Hmmiog Hwram Hwramg plan
                  Hcppg Hcpp Hsplitg Hsplit Hwkg Hwkf) as Hchkg.
    exact (goodmb_mem_write_value_of_checked_plain Dr Dw (Store Data) PBMT_PMA pa W
             dat _ User s _ mm HDm HDcp Heffg Heff Hchkg Hchk).
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
    0 < W -> W <= 8 ->
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
    intros HWpos HWle Hl Hchk Hcov Hp Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
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
    destruct (exec_mem_read_mis_U (u_walk_pa w va) W σ' HWpos HWle
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
    0 < W -> W <= 8 ->
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
    intros HWpos HWle Hl Hchk Hcov Hp Hcanon Hmisa Hmenv Hhtif Hcp HSXL Hmprv Hall.
    iIntros "Hri Hgh Hinv Hdata".
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
    { exact (exec_mem_write_ea_mis_U pa W σ' HWpos HWle
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord))
               (ltac:(rewrite (Tr pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp))
               (ltac:(rewrite (Tr pma_regions ltac:(vm_compute; reflexivity)); exact Hall))
               (fun j Hj => proj1 (proj2 (Hwin j Hj)))
               (ltac:(rewrite (Tr mstatus ltac:(vm_compute; reflexivity)); exact Hmprv))
               (ltac:(rewrite (Tr cur_privilege ltac:(vm_compute; reflexivity)); exact Hcp))
               (ltac:(rewrite (Tr pmpcfg_n ltac:(vm_compute; reflexivity)); exact HWp))). }
    destruct (exec_mem_write_value_mis_U pa W σ' HWpos HWle
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

(* ===================================================================== *)
(* §g THE PAGE-STRADDLING VMEM ACCESS.  [do_split_access] is TRUE, so the   *)
(*    model performs TWO translate-and-access steps, in ASCENDING order     *)
(*    ([sys_misaligned_order_decreasing] is false): [in_page_bytes] at       *)
(*    [va], then [next_page_bytes] at [va + in_page_bytes].  This is the     *)
(*    ONLY place the vmem level still splits, and it is at most two ways;    *)
(*    either part can translate-fault, so each direction has an Ok arm and   *)
(*    two Err arms.                                                        *)
(* ===================================================================== *)

Lemma exec_vmem_read_addr_split2 (W p q : Z) (va pa1 pa2 : mword 64)
    (v1 : mword (8 * p)) (v2 : mword (8 * q))
    (acc : MemoryAccessType mem_payload) (aq rl : bool)
    (ep : Privilege) (md : SATPMode) s s1 s2 :
  0 < p -> 0 < q ->
  exec (split_on_page_boundary va W) s = Some ((p, q), s) ->
  plat_misaligned_exception acc false = None ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  generic_neq md Bare = true ->
  exec (translate_and_read_value (Virtaddr va) p acc aq rl false) s
    = Some (Ok (Physaddr pa1, v1), s1) ->
  exec (translate_and_read_value (Virtaddr (add_vec_int va p)) q acc aq rl false) s1
    = Some (Ok (Physaddr pa2, v2), s2) ->
  exists dvv : mword (8 * W),
    exec (vmem_read_addr (Virtaddr va) W acc aq rl false) s = Some (Ok dvv, s2).
Proof.
  intros Hp Hq Hsplit Hpme Heff Htm Hbare Htrv1 Htrv2.
  eexists.
  unfold vmem_read_addr. rewrite exec_catch_early_return.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hg : execR G s = Some (inr tt, s)) end.
  { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
  rewrite (execR_bind0_Some _ _ _ _ Hg).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hsplit). cbn beta zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
    replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hds). cbn match beta zeta.
  unfold sys_misaligned_order_decreasing. cbn [andb]. cbn match beta.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (zeros' (8 * W)) s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Htrv1). cbn match beta.
  match goal with |- context[Defs.bind (Defs.bind0 ?IF ?rr) ?k] =>
    assert (Hseq : execR (Defs.bind0 IF rr) s1
                   = Some (inr (update_subrange_vec_dec (zeros' (8 * W))
                                  (8 * p - 1) 0 (autocast (T := mword) v1)), s1)) end.
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta.
  cbn [Riscv.rv64d.not negb andb]. cbn match beta.
  cbn [Riscv.rv64d.not negb].
  (* the assert-bind is the LEFT operand of the outer data bind, so
     [execR_liftR_seq] has nothing to match until it is [assert]ed on its own *)
  match goal with
  | |- context[execR (Defs.bind ?inner ?k2) s1] =>
      assert (Hin : execR inner s1
              = Some (inr (update_subrange_vec_dec
                             (update_subrange_vec_dec (zeros' (8 * W)) (8 * p - 1) 0
                                (autocast (T := mword) v1))
                             (8 * W - 1) (8 * p) (autocast (T := mword) v2)), s2))
  end.
  { rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s1)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ Htrv2). cbn match beta.
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hin). cbn beta.
  rewrite execR_returnR. reflexivity.
Qed.

Lemma goodmb_vmem_read_addr_split2 (Dr Dw : register -> bool)
    (W p q : Z) (va pa1 pa2 : mword 64)
    (v1 : mword (8 * p)) (v2 : mword (8 * q))
    (acc : MemoryAccessType mem_payload) (aq rl : bool)
    (ep : Privilege) (md : SATPMode) s s1 s2 mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  0 < p -> 0 < q ->
  goodmb Dr Dw (split_on_page_boundary va W) s mm = true ->
  exec (split_on_page_boundary va W) s = Some ((p, q), s) ->
  plat_misaligned_exception acc false = None ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  generic_neq md Bare = true ->
  goodmb Dr Dw (translate_and_read_value (Virtaddr va) p acc aq rl false) s mm = true ->
  exec (translate_and_read_value (Virtaddr va) p acc aq rl false) s
    = Some (Ok (Physaddr pa1, v1), s1) ->
  goodmb Dr Dw (translate_and_read_value (Virtaddr (add_vec_int va p)) q acc aq rl false)
    s1 mm = true ->
  exec (translate_and_read_value (Virtaddr (add_vec_int va p)) q acc aq rl false) s1
    = Some (Ok (Physaddr pa2, v2), s2) ->
  goodmb Dr Dw (vmem_read_addr (Virtaddr va) W acc aq rl false) s mm = true.
Proof.
  intros HDm HDc Hp Hq Hsplitg Hsplit Hpme Heffg Heff Htmg Htm Hbare
         Htrv1g Htrv1 Htrv2g Htrv2.
  assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDc).
  unfold vmem_read_addr. apply goodmb_cer.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hgg : goodmb Dr Dw G s mm = true);
    [ | assert (Hg : execR G s = Some (inr tt, s)) ] end.
  { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply goodmb_returnm.
    - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply goodmb_returnm. }
  { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
  erewrite (gm_bind0R Dr Dw _ _ s s mm Hgg Hg).
  cbn [bits_of_virtaddr]. cbn zeta.
  gmm_lift Hsplitg Hsplit. cbn beta zeta match.
  gmm_lift Hmst (exec_read_reg mstatus s). cbn beta.
  gmm_lift Hcpr (exec_read_reg cur_privilege s). cbn beta.
  gmm_lift Heffg Heff. cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true);
    [ | assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) ] end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true);
      [ | assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                       = Some (inr (generic_neq md Bare), s)) ] end.
    { erewrite gm_liftR_seq; [ | exact Htmg | exact Htm ]. cbn beta.
      apply goodmb_returnm. }
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s s mm _ Hlg Hl). rewrite Hbare. cbn match beta.
    replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
    apply goodmb_returnm. }
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
    replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
    apply execR_returnR_fwd. }
  erewrite (gm_bindR Dr Dw _ _ s s mm true Hdsg Hds). cbn match beta zeta.
  unfold sys_misaligned_order_decreasing. cbn [andb]. cbn match beta.
  erewrite gm_bindR;
    [ | apply goodmb_returnm | apply (execR_returnR_fwd (zeros' (8 * W)) s) ]. cbn beta.
  gmm_lift Htrv1g Htrv1. cbn match beta.
  match goal with |- context[Defs.bind (Defs.bind0 ?IF ?rr) ?k] =>
    assert (Hseqg : goodmb Dr Dw (Defs.bind0 IF rr) s1 mm = true);
    [ | assert (Hseq : execR (Defs.bind0 IF rr) s1
                   = Some (inr (update_subrange_vec_dec (zeros' (8 * W))
                                  (8 * p - 1) 0 (autocast (T := mword) v1)), s1)) ] end.
  { erewrite gm_bind0R; [ | apply goodmb_returnm | apply (execR_returnR_fwd tt s1) ].
    apply goodmb_returnm. }
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
    apply execR_returnR_fwd. }
  erewrite (gm_bindR Dr Dw _ _ s1 s1 mm _ Hseqg Hseq). cbn beta.
  cbn [Riscv.rv64d.not negb andb]. cbn match beta.
  cbn [Riscv.rv64d.not negb].
  match goal with
  | |- context[goodmb _ _ (Defs.bind ?inner ?k2) s1 _] =>
      assert (Hing : goodmb Dr Dw inner s1 mm = true);
      [ | assert (Hin : execR inner s1
              = Some (inr (update_subrange_vec_dec
                             (update_subrange_vec_dec (zeros' (8 * W)) (8 * p - 1) 0
                                (autocast (T := mword) v1))
                             (8 * W - 1) (8 * p) (autocast (T := mword) v2)), s2)) ]
  end.
  { match goal with |- context[Defs.assert_exp' _ ?msg] =>
      gmm_lift (goodmb_assert_exp'_true Dr Dw msg s1 mm)
               (exec_assert_exp'_true msg s1) end.
    cbn beta.
    gmm_lift Htrv2g Htrv2. cbn match beta.
    apply goodmb_returnm. }
  { rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s1)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ Htrv2). cbn match beta.
    apply execR_returnR_fwd. }
  erewrite (gm_bindR Dr Dw _ _ s1 s2 mm _ Hing Hin). cbn beta.
  apply goodmb_returnm.
Qed.

(* an early return propagates through any number of binds *)
Lemma execR_bind_inl {R X Y} (m : Defs.monadR R exception Y)
    (f : Y -> Defs.monadR R exception X) s s' (r : R) :
  execR m s = Some (inl r, s') -> execR (Defs.bind m f) s = Some (inl r, s').
Proof. intro H. rewrite execR_bind. rewrite H. reflexivity. Qed.

Lemma exec_vmem_read_addr_split2_err1 (W p q : Z) (va : mword 64)
    (er : ExecutionResult) (acc : MemoryAccessType mem_payload) (aq rl : bool)
    (ep : Privilege) (md : SATPMode) s s1 :
  0 < p -> 0 < q ->
  exec (split_on_page_boundary va W) s = Some ((p, q), s) ->
  plat_misaligned_exception acc false = None ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  generic_neq md Bare = true ->
  exec (translate_and_read_value (Virtaddr va) p acc aq rl false) s = Some (Err er, s1) ->
  exec (vmem_read_addr (Virtaddr va) W acc aq rl false) s = Some (Err er, s1).
Proof.
  intros Hp Hq Hsplit Hpme Heff Htm Hbare Htrv1.
  unfold vmem_read_addr. rewrite exec_catch_early_return.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hg : execR G s = Some (inr tt, s)) end.
  { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
  rewrite (execR_bind0_Some _ _ _ _ Hg).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hsplit). cbn beta zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
    replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hds). cbn match beta zeta.
  unfold sys_misaligned_order_decreasing. cbn [andb]. cbn match beta.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (zeros' (8 * W)) s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Htrv1). cbn match beta.
  (* the early return propagates through the data binds *)
  match goal with |- context[execR (Defs.bind ?m1 ?k1) s1] =>
    assert (Hin : execR m1 s1 = Some (inl (Err er), s1)) end.
  { rewrite execR_bind0. rewrite execR_early_ret. reflexivity. }
  rewrite (execR_bind_inl _ _ _ _ _ Hin). cbn match. reflexivity.
Qed.

Lemma goodmb_vmem_read_addr_split2_err1 (Dr Dw : register -> bool)
    (W p q : Z) (va : mword 64)
    (er : ExecutionResult) (acc : MemoryAccessType mem_payload) (aq rl : bool)
    (ep : Privilege) (md : SATPMode) s s1 mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  0 < p -> 0 < q ->
  goodmb Dr Dw (split_on_page_boundary va W) s mm = true ->
  exec (split_on_page_boundary va W) s = Some ((p, q), s) ->
  plat_misaligned_exception acc false = None ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  generic_neq md Bare = true ->
  goodmb Dr Dw (translate_and_read_value (Virtaddr va) p acc aq rl false) s mm = true ->
  exec (translate_and_read_value (Virtaddr va) p acc aq rl false) s = Some (Err er, s1) ->
  goodmb Dr Dw (vmem_read_addr (Virtaddr va) W acc aq rl false) s mm = true.
Proof.
  intros HDm HDc Hp Hq Hsplitg Hsplit Hpme Heffg Heff Htmg Htm Hbare Htrv1g Htrv1.
  assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDc).
  unfold vmem_read_addr.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hgg : goodmb Dr Dw G s mm = true);
    [ | assert (Hg : execR G s = Some (inr tt, s)) ] end.
  { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply goodmb_returnm.
    - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply goodmb_returnm. }
  { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
  erewrite gm_cer_bind0; [ | exact Hgg | exact Hg ].
  cbn [bits_of_virtaddr]. cbn zeta.
  gmm_lift Hsplitg Hsplit. cbn beta zeta match.
  gmm_lift Hmst (exec_read_reg mstatus s). cbn beta.
  gmm_lift Hcpr (exec_read_reg cur_privilege s). cbn beta.
  gmm_lift Heffg Heff. cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true);
    [ | assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) ] end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true);
      [ | assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                       = Some (inr (generic_neq md Bare), s)) ] end.
    { erewrite gm_liftR_seq; [ | exact Htmg | exact Htm ]. cbn beta.
      apply goodmb_returnm. }
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s s mm _ Hlg Hl). rewrite Hbare. cbn match beta.
    replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
    apply goodmb_returnm. }
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
    replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
    apply execR_returnR_fwd. }
  erewrite gm_cer_bind; [ | exact Hdsg | exact Hds ]. cbn match beta zeta.
  unfold sys_misaligned_order_decreasing. cbn [andb]. cbn match beta.
  erewrite gm_cer_bind;
    [ | apply goodmb_returnm | apply (execR_returnR_fwd (zeros' (8 * W)) s) ]. cbn beta.
  gmm_lift Htrv1g Htrv1. cbn match beta.
  apply goodmb_returnm.
Qed.

Lemma exec_vmem_read_addr_split2_err2 (W p q : Z) (va pa1 : mword 64)
    (v1 : mword (8 * p)) (er : ExecutionResult)
    (acc : MemoryAccessType mem_payload) (aq rl : bool)
    (ep : Privilege) (md : SATPMode) s s1 s2 :
  0 < p -> 0 < q ->
  exec (split_on_page_boundary va W) s = Some ((p, q), s) ->
  plat_misaligned_exception acc false = None ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  exec (translationMode ep) s = Some (md, s) ->
  generic_neq md Bare = true ->
  exec (translate_and_read_value (Virtaddr va) p acc aq rl false) s
    = Some (Ok (Physaddr pa1, v1), s1) ->
  exec (translate_and_read_value (Virtaddr (add_vec_int va p)) q acc aq rl false) s1
    = Some (Err er, s2) ->
  exec (vmem_read_addr (Virtaddr va) W acc aq rl false) s = Some (Err er, s2).
Proof.
  intros Hp Hq Hsplit Hpme Heff Htm Hbare Htrv1 Htrv2.
  unfold vmem_read_addr. rewrite exec_catch_early_return.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hg : execR G s = Some (inr tt, s)) end.
  { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
  rewrite (execR_bind0_Some _ _ _ _ Hg).
  cbn [bits_of_virtaddr]. cbn zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ Hsplit). cbn beta zeta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
    replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hds). cbn match beta zeta.
  unfold sys_misaligned_order_decreasing. cbn [andb]. cbn match beta.
  rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd (zeros' (8 * W)) s)). cbn beta.
  rewrite (execR_liftR_seq _ _ _ _ _ Htrv1). cbn match beta.
  match goal with |- context[Defs.bind (Defs.bind0 ?IF ?rr) ?k] =>
    assert (Hseq : execR (Defs.bind0 IF rr) s1
                   = Some (inr (update_subrange_vec_dec (zeros' (8 * W))
                                  (8 * p - 1) 0 (autocast (T := mword) v1)), s1)) end.
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
    apply execR_returnR_fwd. }
  rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta.
  cbn [Riscv.rv64d.not negb andb]. cbn match beta.
  cbn [Riscv.rv64d.not negb].
  match goal with
  | |- context[execR (Defs.bind ?inner ?k2) s1] =>
      assert (Hin : execR inner s1 = Some (inl (Err er), s2))
  end.
  { rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s1)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ Htrv2). cbn match beta.
    rewrite execR_bind0. rewrite execR_early_ret. reflexivity. }
  rewrite (execR_bind_inl _ _ _ _ _ Hin). cbn match. reflexivity.
Qed.

Lemma goodmb_vmem_read_addr_split2_err2 (Dr Dw : register -> bool)
    (W p q : Z) (va pa1 : mword 64)
    (v1 : mword (8 * p)) (er : ExecutionResult)
    (acc : MemoryAccessType mem_payload) (aq rl : bool)
    (ep : Privilege) (md : SATPMode) s s1 s2 mm :
  Dr mstatus = true -> Dr cur_privilege = true ->
  0 < p -> 0 < q ->
  goodmb Dr Dw (split_on_page_boundary va W) s mm = true ->
  exec (split_on_page_boundary va W) s = Some ((p, q), s) ->
  plat_misaligned_exception acc false = None ->
  goodmb Dr Dw (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s mm = true ->
  exec (effectivePrivilege acc (register_lookup mstatus s.(sregs))
          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s) ->
  goodmb Dr Dw (translationMode ep) s mm = true ->
  exec (translationMode ep) s = Some (md, s) ->
  generic_neq md Bare = true ->
  goodmb Dr Dw (translate_and_read_value (Virtaddr va) p acc aq rl false) s mm = true ->
  exec (translate_and_read_value (Virtaddr va) p acc aq rl false) s
    = Some (Ok (Physaddr pa1, v1), s1) ->
  goodmb Dr Dw (translate_and_read_value (Virtaddr (add_vec_int va p)) q acc aq rl false)
    s1 mm = true ->
  exec (translate_and_read_value (Virtaddr (add_vec_int va p)) q acc aq rl false) s1
    = Some (Err er, s2) ->
  goodmb Dr Dw (vmem_read_addr (Virtaddr va) W acc aq rl false) s mm = true.
Proof.
  intros HDm HDc Hp Hq Hsplitg Hsplit Hpme Heffg Heff Htmg Htm Hbare
         Htrv1g Htrv1 Htrv2g Htrv2.
  assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDm).
  assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDc).
  unfold vmem_read_addr.
  match goal with |- context[Defs.bind0 ?G ?k] =>
    assert (Hgg : goodmb Dr Dw G s mm = true);
    [ | assert (Hg : execR G s = Some (inr tt, s)) ] end.
  { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply goodmb_returnm.
    - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply goodmb_returnm. }
  { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
    - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
    - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
  erewrite gm_cer_bind0; [ | exact Hgg | exact Hg ].
  cbn [bits_of_virtaddr]. cbn zeta.
  gmm_lift Hsplitg Hsplit. cbn beta zeta match.
  gmm_lift Hmst (exec_read_reg mstatus s). cbn beta.
  gmm_lift Hcpr (exec_read_reg cur_privilege s). cbn beta.
  gmm_lift Heffg Heff. cbn beta.
  match goal with |- context[Defs.and_boolM ?A ?B] =>
    assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true);
    [ | assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) ] end.
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true);
      [ | assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                       = Some (inr (generic_neq md Bare), s)) ] end.
    { erewrite gm_liftR_seq; [ | exact Htmg | exact Htm ]. cbn beta.
      apply goodmb_returnm. }
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s s mm _ Hlg Hl). rewrite Hbare. cbn match beta.
    replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
    apply goodmb_returnm. }
  { unfold Defs.and_boolM.
    match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
      assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                   = Some (inr (generic_neq md Bare), s)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
    replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
    apply execR_returnR_fwd. }
  erewrite gm_cer_bind; [ | exact Hdsg | exact Hds ]. cbn match beta zeta.
  unfold sys_misaligned_order_decreasing. cbn [andb]. cbn match beta.
  erewrite gm_cer_bind;
    [ | apply goodmb_returnm | apply (execR_returnR_fwd (zeros' (8 * W)) s) ]. cbn beta.
  gmm_lift Htrv1g Htrv1. cbn match beta.
  match goal with |- context[Defs.bind (Defs.bind0 ?IF ?rr) ?k] =>
    assert (Hseqg : goodmb Dr Dw (Defs.bind0 IF rr) s1 mm = true);
    [ | assert (Hseq : execR (Defs.bind0 IF rr) s1
                   = Some (inr (update_subrange_vec_dec (zeros' (8 * W))
                                  (8 * p - 1) 0 (autocast (T := mword) v1)), s1)) ] end.
  { erewrite gm_bind0R; [ | apply goodmb_returnm | apply (execR_returnR_fwd tt s1) ].
    apply goodmb_returnm. }
  { rewrite (execR_bind0_Some _ _ _ _ (execR_returnR_fwd tt s1)).
    apply execR_returnR_fwd. }
  erewrite gm_cer_bind; [ | exact Hseqg | exact Hseq ]. cbn beta.
  cbn [Riscv.rv64d.not negb andb]. cbn match beta.
  cbn [Riscv.rv64d.not negb].
  match goal with |- context[Defs.assert_exp' _ ?msg] =>
    gmm_lift (goodmb_assert_exp'_true Dr Dw msg s1 mm)
             (exec_assert_exp'_true msg s1) end.
  cbn beta.
  gmm_lift Htrv2g Htrv2. cbn match beta.
  apply goodmb_returnm.
Qed.


(* ---- the STORE side of the page straddle.  The first part is a bare
   [translateAddr] + [mem_write_ea] + [mem_write_value] (the model does not use
   [translate_and_write_value] there, because the reservation check sits
   between the translation and the write); the second part is the bundled
   [translate_and_write_value] at [va + in_page_bytes]. ---- *)

(* TWO THINGS ABOUT [cbn] IN THIS PROOF, both of which cost real time once.
   [cbn match beta] -- rule flags, NO whitelist -- does no delta, so it cannot
   unfold [mem_write_ea]; that is what makes it safe here.  [cbn [f]] and a
   bare [cbn] BOTH get into [mem_write_ea] (whose body opens with
   [read_reg mstatus]) and the goal explodes into the monad's bind fixpoint --
   and neither [Local Opaque] nor [Arguments : simpl never] stops them.
   And the reservation [if] is DEPENDENT, so the Ltac1 pattern
   [if ?c then ?T else ?E] does not match it; the pattern that does is the raw
   [match _ as x in bool return @?P x with …] one below, which is how
   [MemAccessGen.exec_vmem_write_addr_intra] strips the same [if]. *)

Section StraddleWrite.
  Context (W p q : Z) (va pa1 : mword 64) (dat : mword (8 * W)).
  Context (ep : Privilege) (md : SATPMode) (s s1 s2 s3 : mstate).
  Context (Hpq : (0 < p /\ 0 < q)%Z).
  Context (Hsplit : exec (split_on_page_boundary va W) s = Some ((p, q), s)).
  Context (Hpme : plat_misaligned_exception (Store Data) false = None).
  Context (Heff : exec (effectivePrivilege (Store Data)
                          (register_lookup mstatus s.(sregs))
                          (register_lookup cur_privilege s.(sregs))) s = Some (ep, s)).
  Context (Htm : exec (translationMode ep) s = Some (md, s)).
  Context (Hbare : generic_neq md Bare = true).

  Lemma exec_vmem_write_addr_split2 (b : bool) :
    exec (translateAddr (Virtaddr va) (Store Data)) s
      = Some (Ok (Physaddr pa1, PBMT_PMA, init_ext_ptw), s1) ->
    exec (mem_write_ea (Physaddr pa1) p (Store Data) PBMT_PMA false false false) s1
      = Some (Ok tt, s1) ->
    exec (mem_write_value (Physaddr pa1) p
            (autocast (T := mword) (subrange_vec_dec dat (8 * p - 1) 0))
            (Store Data) PBMT_PMA false false false) s1 = Some (Ok true, s2) ->
    exec (translate_and_write_value (Virtaddr (add_vec_int va p)) q
            (autocast (T := mword) (subrange_vec_dec dat (8 * W - 1) (8 * p)))
            (Store Data) false false false) s2 = Some (Ok b, s3) ->
    exec (vmem_write_addr (Virtaddr va) W dat (Store Data) false false false) s
      = Some (Ok b, s3).
  Proof.
    intros Htr Hea Hwv Htwv. destruct Hpq as [Hp Hq].
    unfold vmem_write_addr. rewrite exec_catch_early_return.
    match goal with |- context[Defs.bind0 ?G ?k] =>
      assert (Hg : execR G s = Some (inr tt, s)) end.
    { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
      - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
      - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
    rewrite (execR_bind0_Some _ _ _ _ Hg).
    cbn [bits_of_virtaddr]. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hsplit). cbn beta zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
        assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                     = Some (inr (generic_neq md Bare), s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
      replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hds). cbn match beta zeta.
    (* the DECREASING-order block is not taken *)
    unfold sys_misaligned_order_decreasing.
    rewrite andb_false_l. cbn match beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd true s)). cbn beta zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match beta.
    (* the first part: the reservation check, then ea + value *)
    match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
      assert (Hsc : execR (Defs.liftR asrt
                           : Defs.monadR (result bool ExecutionResult) exception unit) s1
                    = Some (inr tt, s1))
        by (rewrite execR_liftR; reflexivity) end.
    match goal with
    | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
        assert (Hwr1 : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s1 = Some (inr true, s2))
    end.
    { match goal with |- execR (Defs.bind0 _ ?Nbody) s1 = _ => set (NN := Nbody) end.
      rewrite (execR_bind0_Some _ _ _ _ Hsc).
      unfold NN; clear NN.
      match goal with
      | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
          change (execR B ss = R)
      end.
      rewrite (execR_liftR_seq _ _ _ _ _ Hea).
      cbn match.
      rewrite (execR_liftR_seq _ _ _ _ _ Hwv).
      cbn match. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hwr1). cbn beta.
    (* the ASCENDING-order block IS taken: the next page's part *)
    change (andb (Riscv.rv64d.not false) true) with true. cbn match beta.
    match goal with
    | |- context[execR (Defs.bind ?inner ?k2) s2] =>
        assert (Hin : execR inner s2 = Some (inr b, s3))
    end.
    { match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
        assert (Hsc2 : execR (Defs.liftR asrt
                              : Defs.monadR (result bool ExecutionResult) exception unit) s2
                       = Some (inr tt, s2))
          by (rewrite execR_liftR; reflexivity) end.
      rewrite (execR_bind0_Some _ _ _ _ Hsc2).
      rewrite (execR_liftR_seq _ _ _ _ _ Htwv). cbn match beta.
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hin). cbn beta.
    rewrite execR_returnR. reflexivity.
  Qed.

  Lemma goodmb_vmem_write_addr_split2 (Dr Dw : register -> bool) (b : bool) mm :
    Dr mstatus = true -> Dr cur_privilege = true ->
    goodmb Dr Dw (split_on_page_boundary va W) s mm = true ->
    goodmb Dr Dw (effectivePrivilege (Store Data)
                    (register_lookup mstatus s.(sregs))
                    (register_lookup cur_privilege s.(sregs))) s mm = true ->
    goodmb Dr Dw (translationMode ep) s mm = true ->
    goodmb Dr Dw (translateAddr (Virtaddr va) (Store Data)) s mm = true ->
    exec (translateAddr (Virtaddr va) (Store Data)) s
      = Some (Ok (Physaddr pa1, PBMT_PMA, init_ext_ptw), s1) ->
    goodmb Dr Dw (mem_write_ea (Physaddr pa1) p (Store Data) PBMT_PMA false false false)
      s1 mm = true ->
    exec (mem_write_ea (Physaddr pa1) p (Store Data) PBMT_PMA false false false) s1
      = Some (Ok tt, s1) ->
    goodmb Dr Dw (mem_write_value (Physaddr pa1) p
            (autocast (T := mword) (subrange_vec_dec dat (8 * p - 1) 0))
            (Store Data) PBMT_PMA false false false) s1 mm = true ->
    exec (mem_write_value (Physaddr pa1) p
            (autocast (T := mword) (subrange_vec_dec dat (8 * p - 1) 0))
            (Store Data) PBMT_PMA false false false) s1 = Some (Ok true, s2) ->
    goodmb Dr Dw (translate_and_write_value (Virtaddr (add_vec_int va p)) q
            (autocast (T := mword) (subrange_vec_dec dat (8 * W - 1) (8 * p)))
            (Store Data) false false false) s2 mm = true ->
    exec (translate_and_write_value (Virtaddr (add_vec_int va p)) q
            (autocast (T := mword) (subrange_vec_dec dat (8 * W - 1) (8 * p)))
            (Store Data) false false false) s2 = Some (Ok b, s3) ->
    goodmb Dr Dw (vmem_write_addr (Virtaddr va) W dat (Store Data) false false false) s mm
      = true.
  Proof.
    intros HDm HDc Hsplitg Heffg Htmg Htrg Htr Heag Hea Hwvg Hwv Htwvg Htwv.
    destruct Hpq as [Hp Hq].
    assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
      by (rewrite goodmb_read_reg; exact HDm).
    assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
      by (rewrite goodmb_read_reg; exact HDc).
    unfold vmem_write_addr. apply goodmb_cer.
    match goal with |- context[Defs.bind0 ?G ?k] =>
      assert (Hgg : goodmb Dr Dw G s mm = true);
      [ | assert (Hg : execR G s = Some (inr tt, s)) ] end.
    { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
      - cbn [Riscv.rv64d.not negb]. apply goodmb_returnm.
      - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply goodmb_returnm. }
    { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
      - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
      - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
    erewrite (gm_bind0R Dr Dw _ _ s s mm Hgg Hg).
    cbn [bits_of_virtaddr]. cbn zeta.
    gmm_lift Hsplitg Hsplit. cbn beta zeta match.
    gmm_lift Hmst (exec_read_reg mstatus s). cbn beta.
    gmm_lift Hcpr (exec_read_reg cur_privilege s). cbn beta.
    gmm_lift Heffg Heff. cbn beta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true);
      [ | assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
        assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true);
        [ | assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                         = Some (inr (generic_neq md Bare), s)) ] end.
      { erewrite gm_liftR_seq; [ | exact Htmg | exact Htm ]. cbn beta.
        apply goodmb_returnm. }
      { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
      erewrite (gm_bindR Dr Dw _ _ s s mm _ Hlg Hl). rewrite Hbare. cbn match beta.
      replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
      apply goodmb_returnm. }
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
        assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                     = Some (inr (generic_neq md Bare), s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
      replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
      apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s s mm true Hdsg Hds). cbn match beta zeta.
    unfold sys_misaligned_order_decreasing.
    rewrite andb_false_l. cbn match beta.
    erewrite gm_bindR; [ | apply goodmb_returnm | apply (execR_returnR_fwd true s) ].
    cbn beta zeta.
    gmm_lift Htrg Htr. cbn match beta.
    match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
      assert (Hscg : goodmb Dr Dw (Defs.liftR asrt
                             : Defs.monadR (result bool ExecutionResult) exception unit)
                       s1 mm = true) by apply goodmb_returnm;
      assert (Hsc : execR (Defs.liftR asrt
                           : Defs.monadR (result bool ExecutionResult) exception unit) s1
                    = Some (inr tt, s1))
        by (rewrite execR_liftR; reflexivity) end.
    match goal with
    | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
        assert (Hwr1g : goodmb Dr Dw (Defs.bind0 (Defs.liftR asrt) Nbody) s1 mm = true);
        [ | assert (Hwr1 : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s1
                           = Some (inr true, s2)) ]
    end.
    { match goal with |- goodmb _ _ (Defs.bind0 _ ?Nbody) s1 _ = _ =>
        set (NN := Nbody) end.
      erewrite gm_bind0R; [ | exact Hscg | exact Hsc ].
      unfold NN; clear NN.
      match goal with
      | |- goodmb ?dr ?dw (match _ as x in bool return @?P x with
                           | true => _ | false => ?B end) ?ss ?m = ?R =>
          change (goodmb dr dw B ss m = R)
      end.
      gmm_lift Heag Hea. cbn match.
      gmm_lift Hwvg Hwv. cbn match. apply goodmb_returnm. }
    { match goal with |- execR (Defs.bind0 _ ?Nbody) s1 = _ => set (NN := Nbody) end.
      rewrite (execR_bind0_Some _ _ _ _ Hsc).
      unfold NN; clear NN.
      match goal with
      | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
          change (execR B ss = R)
      end.
      rewrite (execR_liftR_seq _ _ _ _ _ Hea).
      cbn match.
      rewrite (execR_liftR_seq _ _ _ _ _ Hwv).
      cbn match. apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s1 s2 mm true Hwr1g Hwr1). cbn beta.
    change (andb (Riscv.rv64d.not false) true) with true. cbn match beta.
    match goal with
    | |- context[goodmb _ _ (Defs.bind ?inner ?k2) s2 _] =>
        assert (Hing : goodmb Dr Dw inner s2 mm = true);
        [ | assert (Hin : execR inner s2 = Some (inr b, s3)) ]
    end.
    { match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
        assert (Hsc2g : goodmb Dr Dw (Defs.liftR asrt
                              : Defs.monadR (result bool ExecutionResult) exception unit)
                          s2 mm = true) by apply goodmb_returnm;
        assert (Hsc2 : execR (Defs.liftR asrt
                              : Defs.monadR (result bool ExecutionResult) exception unit) s2
                       = Some (inr tt, s2))
          by (rewrite execR_liftR; reflexivity) end.
      erewrite gm_bind0R; [ | exact Hsc2g | exact Hsc2 ].
      gmm_lift Htwvg Htwv. cbn match beta.
      apply goodmb_returnm. }
    { match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
        assert (Hsc2 : execR (Defs.liftR asrt
                              : Defs.monadR (result bool ExecutionResult) exception unit) s2
                       = Some (inr tt, s2))
          by (rewrite execR_liftR; reflexivity) end.
      rewrite (execR_bind0_Some _ _ _ _ Hsc2).
      rewrite (execR_liftR_seq _ _ _ _ _ Htwv). cbn match beta.
      apply execR_returnR_fwd. }
    erewrite (gm_bindR Dr Dw _ _ s2 s3 mm b Hing Hin). cbn beta.
    apply goodmb_returnm.
  Qed.

  (* the first part's translation faults *)
  Lemma exec_vmem_write_addr_split2_err1 (e : ExceptionType) (er : ExecutionResult) :
    exec (translateAddr (Virtaddr va) (Store Data)) s = Some (Err (e, tt), s1) ->
    exec (memory_exception (Virtaddr va) e) s1 = Some (er, s1) ->
    exec (vmem_write_addr (Virtaddr va) W dat (Store Data) false false false) s
      = Some (Err er, s1).
  Proof.
    intros Htr Hme. destruct Hpq as [Hp Hq].
    unfold vmem_write_addr. rewrite exec_catch_early_return.
    match goal with |- context[Defs.bind0 ?G ?k] =>
      assert (Hg : execR G s = Some (inr tt, s)) end.
    { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
      - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
      - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
    rewrite (execR_bind0_Some _ _ _ _ Hg).
    cbn [bits_of_virtaddr]. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hsplit). cbn beta zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
        assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                     = Some (inr (generic_neq md Bare), s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
      replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hds). cbn match beta zeta.
    unfold sys_misaligned_order_decreasing.
    rewrite andb_false_l. cbn match beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd true s)). cbn beta zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match beta.
    match goal with |- context[execR (Defs.bind ?m1 ?k1) s1] =>
      assert (Hin : execR m1 s1 = Some (inl (Err er), s1)) end.
    { rewrite (execR_liftR_seq _ _ _ _ _ Hme). cbn match beta.
      rewrite execR_bind0. rewrite execR_early_ret. reflexivity. }
    rewrite (execR_bind_inl _ _ _ _ _ Hin). cbn match. reflexivity.
  Qed.

  Lemma goodmb_vmem_write_addr_split2_err1 (Dr Dw : register -> bool)
      (e : ExceptionType) (er : ExecutionResult) mm :
    Dr mstatus = true -> Dr cur_privilege = true ->
    goodmb Dr Dw (split_on_page_boundary va W) s mm = true ->
    goodmb Dr Dw (effectivePrivilege (Store Data)
                    (register_lookup mstatus s.(sregs))
                    (register_lookup cur_privilege s.(sregs))) s mm = true ->
    goodmb Dr Dw (translationMode ep) s mm = true ->
    goodmb Dr Dw (translateAddr (Virtaddr va) (Store Data)) s mm = true ->
    exec (translateAddr (Virtaddr va) (Store Data)) s = Some (Err (e, tt), s1) ->
    goodmb Dr Dw (memory_exception (Virtaddr va) e) s1 mm = true ->
    exec (memory_exception (Virtaddr va) e) s1 = Some (er, s1) ->
    goodmb Dr Dw (vmem_write_addr (Virtaddr va) W dat (Store Data) false false false) s mm
      = true.
  Proof.
    intros HDm HDc Hsplitg Heffg Htmg Htrg Htr Hmeg Hme.
    destruct Hpq as [Hp Hq].
    assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
      by (rewrite goodmb_read_reg; exact HDm).
    assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
      by (rewrite goodmb_read_reg; exact HDc).
    unfold vmem_write_addr.
    match goal with |- context[Defs.bind0 ?G ?k] =>
      assert (Hgg : goodmb Dr Dw G s mm = true);
      [ | assert (Hg : execR G s = Some (inr tt, s)) ] end.
    { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
      - cbn [Riscv.rv64d.not negb]. apply goodmb_returnm.
      - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply goodmb_returnm. }
    { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
      - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
      - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
    erewrite gm_cer_bind0; [ | exact Hgg | exact Hg ].
    cbn [bits_of_virtaddr]. cbn zeta.
    gmm_lift Hsplitg Hsplit. cbn beta zeta match.
    gmm_lift Hmst (exec_read_reg mstatus s). cbn beta.
    gmm_lift Hcpr (exec_read_reg cur_privilege s). cbn beta.
    gmm_lift Heffg Heff. cbn beta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true);
      [ | assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
        assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true);
        [ | assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                         = Some (inr (generic_neq md Bare), s)) ] end.
      { erewrite gm_liftR_seq; [ | exact Htmg | exact Htm ]. cbn beta.
        apply goodmb_returnm. }
      { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
      erewrite (gm_bindR Dr Dw _ _ s s mm _ Hlg Hl). rewrite Hbare. cbn match beta.
      replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
      apply goodmb_returnm. }
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
        assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                     = Some (inr (generic_neq md Bare), s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
      replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
      apply execR_returnR_fwd. }
    erewrite gm_cer_bind; [ | exact Hdsg | exact Hds ]. cbn match beta zeta.
    unfold sys_misaligned_order_decreasing.
    rewrite andb_false_l. cbn match beta.
    erewrite gm_cer_bind; [ | apply goodmb_returnm | apply (execR_returnR_fwd true s) ].
    cbn beta zeta.
    gmm_lift Htrg Htr. cbn match beta.
    gmm_lift Hmeg Hme. cbn match beta.
    apply goodmb_returnm.
  Qed.

  (* the first part lands, the SECOND part's translation faults *)
  Lemma exec_vmem_write_addr_split2_err2 (er : ExecutionResult) :
    exec (translateAddr (Virtaddr va) (Store Data)) s
      = Some (Ok (Physaddr pa1, PBMT_PMA, init_ext_ptw), s1) ->
    exec (mem_write_ea (Physaddr pa1) p (Store Data) PBMT_PMA false false false) s1
      = Some (Ok tt, s1) ->
    exec (mem_write_value (Physaddr pa1) p
            (autocast (T := mword) (subrange_vec_dec dat (8 * p - 1) 0))
            (Store Data) PBMT_PMA false false false) s1 = Some (Ok true, s2) ->
    exec (translate_and_write_value (Virtaddr (add_vec_int va p)) q
            (autocast (T := mword) (subrange_vec_dec dat (8 * W - 1) (8 * p)))
            (Store Data) false false false) s2 = Some (Err er, s3) ->
    exec (vmem_write_addr (Virtaddr va) W dat (Store Data) false false false) s
      = Some (Err er, s3).
  Proof.
    intros Htr Hea Hwv Htwv. destruct Hpq as [Hp Hq].
    unfold vmem_write_addr. rewrite exec_catch_early_return.
    match goal with |- context[Defs.bind0 ?G ?k] =>
      assert (Hg : execR G s = Some (inr tt, s)) end.
    { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
      - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
      - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
    rewrite (execR_bind0_Some _ _ _ _ Hg).
    cbn [bits_of_virtaddr]. cbn zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Hsplit). cbn beta zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (execR_liftR_seq _ _ _ _ _ Heff). cbn beta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
        assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                     = Some (inr (generic_neq md Bare), s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
      replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
      apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hds). cbn match beta zeta.
    unfold sys_misaligned_order_decreasing.
    rewrite andb_false_l. cbn match beta.
    rewrite (execR_bind_Some _ _ _ _ _ (execR_returnR_fwd true s)). cbn beta zeta.
    rewrite (execR_liftR_seq _ _ _ _ _ Htr). cbn match beta.
    match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
      assert (Hsc : execR (Defs.liftR asrt
                           : Defs.monadR (result bool ExecutionResult) exception unit) s1
                    = Some (inr tt, s1))
        by (rewrite execR_liftR; reflexivity) end.
    match goal with
    | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
        assert (Hwr1 : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s1 = Some (inr true, s2))
    end.
    { match goal with |- execR (Defs.bind0 _ ?Nbody) s1 = _ => set (NN := Nbody) end.
      rewrite (execR_bind0_Some _ _ _ _ Hsc).
      unfold NN; clear NN.
      match goal with
      | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
          change (execR B ss = R)
      end.
      rewrite (execR_liftR_seq _ _ _ _ _ Hea).
      cbn match.
      rewrite (execR_liftR_seq _ _ _ _ _ Hwv).
      cbn match. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hwr1). cbn beta.
    change (andb (Riscv.rv64d.not false) true) with true. cbn match beta.
    match goal with
    | |- context[execR (Defs.bind ?inner ?k2) s2] =>
        assert (Hin : execR inner s2 = Some (inl (Err er), s3))
    end.
    { match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
        assert (Hsc2 : execR (Defs.liftR asrt
                              : Defs.monadR (result bool ExecutionResult) exception unit) s2
                       = Some (inr tt, s2))
          by (rewrite execR_liftR; reflexivity) end.
      rewrite (execR_bind0_Some _ _ _ _ Hsc2).
      rewrite (execR_liftR_seq _ _ _ _ _ Htwv). cbn match beta.
      rewrite execR_bind0. rewrite execR_early_ret. reflexivity. }
    rewrite (execR_bind_inl _ _ _ _ _ Hin). cbn match. reflexivity.
  Qed.

  Lemma goodmb_vmem_write_addr_split2_err2 (Dr Dw : register -> bool)
      (er : ExecutionResult) mm :
    Dr mstatus = true -> Dr cur_privilege = true ->
    goodmb Dr Dw (split_on_page_boundary va W) s mm = true ->
    goodmb Dr Dw (effectivePrivilege (Store Data)
                    (register_lookup mstatus s.(sregs))
                    (register_lookup cur_privilege s.(sregs))) s mm = true ->
    goodmb Dr Dw (translationMode ep) s mm = true ->
    goodmb Dr Dw (translateAddr (Virtaddr va) (Store Data)) s mm = true ->
    exec (translateAddr (Virtaddr va) (Store Data)) s
      = Some (Ok (Physaddr pa1, PBMT_PMA, init_ext_ptw), s1) ->
    goodmb Dr Dw (mem_write_ea (Physaddr pa1) p (Store Data) PBMT_PMA false false false)
      s1 mm = true ->
    exec (mem_write_ea (Physaddr pa1) p (Store Data) PBMT_PMA false false false) s1
      = Some (Ok tt, s1) ->
    goodmb Dr Dw (mem_write_value (Physaddr pa1) p
            (autocast (T := mword) (subrange_vec_dec dat (8 * p - 1) 0))
            (Store Data) PBMT_PMA false false false) s1 mm = true ->
    exec (mem_write_value (Physaddr pa1) p
            (autocast (T := mword) (subrange_vec_dec dat (8 * p - 1) 0))
            (Store Data) PBMT_PMA false false false) s1 = Some (Ok true, s2) ->
    goodmb Dr Dw (translate_and_write_value (Virtaddr (add_vec_int va p)) q
            (autocast (T := mword) (subrange_vec_dec dat (8 * W - 1) (8 * p)))
            (Store Data) false false false) s2 mm = true ->
    exec (translate_and_write_value (Virtaddr (add_vec_int va p)) q
            (autocast (T := mword) (subrange_vec_dec dat (8 * W - 1) (8 * p)))
            (Store Data) false false false) s2 = Some (Err er, s3) ->
    goodmb Dr Dw (vmem_write_addr (Virtaddr va) W dat (Store Data) false false false) s mm
      = true.
  Proof.
    intros HDm HDc Hsplitg Heffg Htmg Htrg Htr Heag Hea Hwvg Hwv Htwvg Htwv.
    destruct Hpq as [Hp Hq].
    assert (Hmst : goodmb Dr Dw (Defs.read_reg mstatus : M _) s mm = true)
      by (rewrite goodmb_read_reg; exact HDm).
    assert (Hcpr : goodmb Dr Dw (Defs.read_reg cur_privilege : M _) s mm = true)
      by (rewrite goodmb_read_reg; exact HDc).
    unfold vmem_write_addr.
    match goal with |- context[Defs.bind0 ?G ?k] =>
      assert (Hgg : goodmb Dr Dw G s mm = true);
      [ | assert (Hg : execR G s = Some (inr tt, s)) ] end.
    { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
      - cbn [Riscv.rv64d.not negb]. apply goodmb_returnm.
      - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply goodmb_returnm. }
    { destruct (is_aligned_vaddr (Virtaddr va) W) eqn:E.
      - cbn [Riscv.rv64d.not negb]. apply execR_returnR_fwd.
      - cbn [Riscv.rv64d.not negb]. rewrite Hpme. apply execR_returnR_fwd. }
    erewrite gm_cer_bind0; [ | exact Hgg | exact Hg ].
    cbn [bits_of_virtaddr]. cbn zeta.
    gmm_lift Hsplitg Hsplit. cbn beta zeta match.
    gmm_lift Hmst (exec_read_reg mstatus s). cbn beta.
    gmm_lift Hcpr (exec_read_reg cur_privilege s). cbn beta.
    gmm_lift Heffg Heff. cbn beta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hdsg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true);
      [ | assert (Hds : execR (Defs.and_boolM A B) s = Some (inr true, s)) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
        assert (Hlg : goodmb Dr Dw (Defs.bind (Defs.liftR m) k1) s mm = true);
        [ | assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                         = Some (inr (generic_neq md Bare), s)) ] end.
      { erewrite gm_liftR_seq; [ | exact Htmg | exact Htm ]. cbn beta.
        apply goodmb_returnm. }
      { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
      erewrite (gm_bindR Dr Dw _ _ s s mm _ Hlg Hl). rewrite Hbare. cbn match beta.
      replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
      apply goodmb_returnm. }
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (Defs.liftR ?m) ?k1) _] =>
        assert (Hl : execR (Defs.bind (Defs.liftR m) k1) s
                     = Some (inr (generic_neq md Bare), s)) end.
      { rewrite (execR_liftR_seq _ _ _ _ _ Htm). cbn beta. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hl). rewrite Hbare. cbn match beta.
      replace (Z.gtb q 0) with true by (symmetry; apply Z.gtb_lt; lia).
      apply execR_returnR_fwd. }
    erewrite gm_cer_bind; [ | exact Hdsg | exact Hds ]. cbn match beta zeta.
    unfold sys_misaligned_order_decreasing.
    rewrite andb_false_l. cbn match beta.
    erewrite gm_cer_bind; [ | apply goodmb_returnm | apply (execR_returnR_fwd true s) ].
    cbn beta zeta.
    gmm_lift Htrg Htr. cbn match beta.
    match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
      assert (Hscg : goodmb Dr Dw (Defs.liftR asrt
                             : Defs.monadR (result bool ExecutionResult) exception unit)
                       s1 mm = true) by apply goodmb_returnm;
      assert (Hsc : execR (Defs.liftR asrt
                           : Defs.monadR (result bool ExecutionResult) exception unit) s1
                    = Some (inr tt, s1))
        by (rewrite execR_liftR; reflexivity) end.
    match goal with
    | |- context [ Defs.bind (Defs.bind0 (Defs.liftR ?asrt) ?Nbody) ?post ] =>
        assert (Hwr1g : goodmb Dr Dw (Defs.bind0 (Defs.liftR asrt) Nbody) s1 mm = true);
        [ | assert (Hwr1 : execR (Defs.bind0 (Defs.liftR asrt) Nbody) s1
                           = Some (inr true, s2)) ]
    end.
    { match goal with |- goodmb _ _ (Defs.bind0 _ ?Nbody) s1 _ = _ =>
        set (NN := Nbody) end.
      erewrite gm_bind0R; [ | exact Hscg | exact Hsc ].
      unfold NN; clear NN.
      match goal with
      | |- goodmb ?dr ?dw (match _ as x in bool return @?P x with
                           | true => _ | false => ?B end) ?ss ?m = ?R =>
          change (goodmb dr dw B ss m = R)
      end.
      gmm_lift Heag Hea. cbn match.
      gmm_lift Hwvg Hwv. cbn match. apply goodmb_returnm. }
    { match goal with |- execR (Defs.bind0 _ ?Nbody) s1 = _ => set (NN := Nbody) end.
      rewrite (execR_bind0_Some _ _ _ _ Hsc).
      unfold NN; clear NN.
      match goal with
      | |- execR (match _ as x in bool return @?P x with | true => _ | false => ?B end) ?ss = ?R =>
          change (execR B ss = R)
      end.
      rewrite (execR_liftR_seq _ _ _ _ _ Hea).
      cbn match.
      rewrite (execR_liftR_seq _ _ _ _ _ Hwv).
      cbn match. apply execR_returnR_fwd. }
    erewrite gm_cer_bind; [ | exact Hwr1g | exact Hwr1 ]. cbn beta.
    change (andb (Riscv.rv64d.not false) true) with true. cbn match beta.
    match goal with |- context[Defs.bind0 (Defs.liftR ?asrt) _] =>
      assert (Hsc2g : goodmb Dr Dw (Defs.liftR asrt
                            : Defs.monadR (result bool ExecutionResult) exception unit)
                        s2 mm = true) by apply goodmb_returnm;
      assert (Hsc2 : execR (Defs.liftR asrt
                            : Defs.monadR (result bool ExecutionResult) exception unit) s2
                     = Some (inr tt, s2))
        by (rewrite execR_liftR; reflexivity) end.
    gmxc Hsc2g Hsc2.
    rewrite mbind0_Ret.
    gmm_lift Htwvg Htwv. cbn match beta.
    apply goodmb_returnm.
  Qed.

End StraddleWrite.

(* ===================================================================== *)
(* §h The [translate_and_*] bridges the straddle composers consume.  The   *)
(*    Ok ones for the read exist in MemAccessGen; these are the fault arms  *)
(*    and the store direction, which the page straddle needs and the        *)
(*    aligned path never did (there the vmem level calls [translateAddr]    *)
(*    itself).                                                             *)
(* ===================================================================== *)

Lemma exec_translate_and_read_value_err (width : Z) (va : mword 64)
    (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (e : ExceptionType) (er : ExecutionResult) s s1 :
  exec (translateAddr (Virtaddr va) acc) s = Some (Err (e, tt), s1) ->
  exec (memory_exception (Virtaddr va) e) s1 = Some (er, s1) ->
  exec (translate_and_read_value (Virtaddr va) width acc aq rl res) s
    = Some (Err er, s1).
Proof.
  intros Htr Hme.
  unfold translate_and_read_value.
  rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hme). cbn match beta.
  apply exec_returnM.
Qed.

Lemma goodmb_translate_and_read_value_err (Dr Dw : register -> bool) (width : Z)
    (va : mword 64) (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (e : ExceptionType) (er : ExecutionResult) s s1 mm :
  goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true ->
  exec (translateAddr (Virtaddr va) acc) s = Some (Err (e, tt), s1) ->
  goodmb Dr Dw (memory_exception (Virtaddr va) e) s1 mm = true ->
  exec (memory_exception (Virtaddr va) e) s1 = Some (er, s1) ->
  goodmb Dr Dw (translate_and_read_value (Virtaddr va) width acc aq rl res) s mm = true.
Proof.
  intros Htrg Htr Hmeg Hme.
  unfold translate_and_read_value.
  gmm_peel Htrg Htr. cbn match beta.
  gmm_peel Hmeg Hme. cbn match beta.
  apply goodmb_returnm.
Qed.

Lemma exec_translate_and_write_value_gen (width : Z) (va pa : mword 64)
    (value : mword (8 * width)) (acc : MemoryAccessType mem_payload)
    (aq rl res : bool) (pbmt : page_based_mem_type) (b : bool) s s1 s2 :
  exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, pbmt, init_ext_ptw), s1) ->
  exec (mem_write_ea (Physaddr pa) width acc pbmt aq rl res) s1 = Some (Ok tt, s1) ->
  exec (mem_write_value (Physaddr pa) width value acc pbmt aq rl res) s1
    = Some (Ok b, s2) ->
  exec (translate_and_write_value (Virtaddr va) width value acc aq rl res) s
    = Some (Ok b, s2).
Proof.
  intros Htr Hea Hwv.
  unfold translate_and_write_value.
  rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hea). cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hwv). cbn match beta.
  apply exec_returnM.
Qed.

Lemma goodmb_translate_and_write_value_gen (Dr Dw : register -> bool) (width : Z)
    (va pa : mword 64) (value : mword (8 * width))
    (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (pbmt : page_based_mem_type) (b : bool) s s1 s2 mm :
  goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true ->
  exec (translateAddr (Virtaddr va) acc) s
    = Some (Ok (Physaddr pa, pbmt, init_ext_ptw), s1) ->
  goodmb Dr Dw (mem_write_ea (Physaddr pa) width acc pbmt aq rl res) s1 mm = true ->
  exec (mem_write_ea (Physaddr pa) width acc pbmt aq rl res) s1 = Some (Ok tt, s1) ->
  goodmb Dr Dw (mem_write_value (Physaddr pa) width value acc pbmt aq rl res) s1 mm
    = true ->
  exec (mem_write_value (Physaddr pa) width value acc pbmt aq rl res) s1
    = Some (Ok b, s2) ->
  goodmb Dr Dw (translate_and_write_value (Virtaddr va) width value acc aq rl res) s mm
    = true.
Proof.
  intros Htrg Htr Heag Hea Hwvg Hwv.
  unfold translate_and_write_value.
  gmm_peel Htrg Htr. cbn match beta.
  gmm_peel Heag Hea. cbn match beta.
  gmm_peel Hwvg Hwv. cbn match beta.
  apply goodmb_returnm.
Qed.

Lemma exec_translate_and_write_value_err (width : Z) (va : mword 64)
    (value : mword (8 * width)) (acc : MemoryAccessType mem_payload)
    (aq rl res : bool) (e : ExceptionType) (er : ExecutionResult) s s1 :
  exec (translateAddr (Virtaddr va) acc) s = Some (Err (e, tt), s1) ->
  exec (memory_exception (Virtaddr va) e) s1 = Some (er, s1) ->
  exec (translate_and_write_value (Virtaddr va) width value acc aq rl res) s
    = Some (Err er, s1).
Proof.
  intros Htr Hme.
  unfold translate_and_write_value.
  rewrite (exec_bind_Some _ _ _ _ _ Htr). cbn match beta.
  rewrite (exec_bind_Some _ _ _ _ _ Hme). cbn match beta.
  apply exec_returnM.
Qed.

Lemma goodmb_translate_and_write_value_err (Dr Dw : register -> bool) (width : Z)
    (va : mword 64) (value : mword (8 * width))
    (acc : MemoryAccessType mem_payload) (aq rl res : bool)
    (e : ExceptionType) (er : ExecutionResult) s s1 mm :
  goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true ->
  exec (translateAddr (Virtaddr va) acc) s = Some (Err (e, tt), s1) ->
  goodmb Dr Dw (memory_exception (Virtaddr va) e) s1 mm = true ->
  exec (memory_exception (Virtaddr va) e) s1 = Some (er, s1) ->
  goodmb Dr Dw (translate_and_write_value (Virtaddr va) width value acc aq rl res) s mm
    = true.
Proof.
  intros Htrg Htr Hmeg Hme.
  unfold translate_and_write_value.
  gmm_peel Htrg Htr. cbn match beta.
  gmm_peel Hmeg Hme. cbn match beta.
  apply goodmb_returnm.
Qed.

(* ===================================================================== *)
(* §i THE PAGE SPLIT ITSELF, on the straddling side.  The model's           *)
(*    [nbytes_to_boundary] is [8 - addr[2:0]], not [4096 - addr[11:0]] --   *)
(*    which agrees with the page distance exactly because an access of at   *)
(*    most 8 bytes can only cross a page boundary from the last 8 bytes of  *)
(*    a page.  Both parts are then [in_one_page] by construction, which is  *)
(*    what lets the per-page composers serve them.                          *)
(* ===================================================================== *)

Lemma page_num_differs (a : mword 64) (w : Z) :
  0 < w -> w <= 8 -> ~ in_one_page a w ->
  Z.shiftr (bv_unsigned a) 12 <> Z.shiftr (bv_wrap 64 (bv_unsigned a + (w - 1))) 12.
Proof.
  intros Hw Hw8 Hout. unfold in_one_page in Hout.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  assert (H64 : (2:Z) ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  rewrite H64 in Hr. destruct Hr as [Hr0 Hr1].
  assert (Hmod : 0 <= bv_unsigned a mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
  assert (Hdm : bv_unsigned a = 4096 * (bv_unsigned a / 4096) + bv_unsigned a mod 4096)
    by (apply Z.div_mod; lia).
  assert (Hd0 : Z.shiftr (bv_unsigned a) 12 = bv_unsigned a / 4096)
    by (apply Z.shiftr_div_pow2; lia).
  destruct (Z_le_gt_dec (bv_unsigned a + (w - 1)) (2 ^ 64 - 1)) as [Hnw | Hwr].
  - (* no wrap: the last byte is one page further up *)
    assert (Hbw : bv_wrap 64 (bv_unsigned a + (w - 1)) = bv_unsigned a + (w - 1))
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    rewrite Hbw.
    assert (Hd1 : Z.shiftr (bv_unsigned a + (w - 1)) 12 = (bv_unsigned a + (w - 1)) / 4096)
      by (apply Z.shiftr_div_pow2; lia).
    rewrite Hd0. rewrite Hd1.
    assert (Hq : (bv_unsigned a + (w - 1)) / 4096 = bv_unsigned a / 4096 + 1).
    { assert (He : bv_unsigned a + (w - 1)
                   = 4096 * (bv_unsigned a / 4096 + 1) + (bv_unsigned a mod 4096 + w - 1 - 4096))
        by lia.
      rewrite He. rewrite Z.mul_comm.
      rewrite Z.div_add_l; [| lia].
      assert (Hs : (bv_unsigned a mod 4096 + w - 1 - 4096) / 4096 = 0)
        by (apply Z.div_small; lia).
      rewrite Hs. lia. }
    rewrite Hq. lia.
  - (* wrap: the last byte is at the very bottom of the space *)
    assert (Hbw : bv_wrap 64 (bv_unsigned a + (w - 1)) = bv_unsigned a + (w - 1) - 2 ^ 64).
    { unfold bv_wrap. rewrite bv_modulus64. rewrite H64.
      rewrite <- (Z.mod_add (bv_unsigned a + (w - 1)) (-1) 18446744073709551616); [| lia].
      apply Z.mod_small. lia. }
    rewrite Hbw.
    assert (Hd1 : Z.shiftr (bv_unsigned a + (w - 1) - 2 ^ 64) 12
                  = (bv_unsigned a + (w - 1) - 2 ^ 64) / 4096)
      by (apply Z.shiftr_div_pow2; lia).
    rewrite Hd0. rewrite Hd1.
    assert (Hlo : (bv_unsigned a + (w - 1) - 2 ^ 64) / 4096 = 0)
      by (apply Z.div_small; rewrite H64; lia).
    rewrite Hlo.
    assert (Hhi : 0 < bv_unsigned a / 4096).
    { apply Z.div_str_pos. rewrite H64 in Hwr. lia. }
    lia.
Qed.

Lemma exec_split_on_page_boundary_straddle (a : mword 64) (w : Z) s :
  0 < w -> w <= 8 -> ~ in_one_page a w ->
  exec (split_on_page_boundary a w) s
    = Some ((4096 - bv_unsigned a mod 4096,
             w - (4096 - bv_unsigned a mod 4096)), s).
Proof.
  intros Hw Hw8 Hout.
  pose proof Hout as Hout'. unfold in_one_page in Hout'.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  assert (Hmod : 0 <= bv_unsigned a mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
  (* the last 8 bytes of a page: [a mod 8] determines the page distance *)
  assert (Hm8 : bv_unsigned a mod 4096 mod 8 = bv_unsigned a mod 4096 - 4088).
  { assert (Hd : (8 | 4088)) by (exists 511; reflexivity).
    assert (Hlo : 4088 <= bv_unsigned a mod 4096) by lia.
    rewrite <- (Z.mod_add (bv_unsigned a mod 4096) (-511) 8); [| lia].
    apply Z.mod_small. lia. }
  assert (Hm8' : bv_unsigned a mod 8 = bv_unsigned a mod 4096 - 4088).
  { rewrite <- Hm8. symmetry. apply Z.mod_mod_divide. exists 512; reflexivity. }
  unfold split_on_page_boundary.
  assert (Hintra : eq_vec (and_vec a (update_subrange_vec_dec ((ones 64) : bits 64)
                                        (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1)))))
                          (and_vec (sub_vec_int (add_vec_int a w) 1)
                                   (update_subrange_vec_dec ((ones 64) : bits 64)
                                      (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1))))) = false).
  { apply eq_vec_false_iff. intro Heq.
    apply (f_equal bv_unsigned) in Heq.
    rewrite !and_vec64_unsigned in Heq. rewrite page_mask64_val in Heq.
    assert (Hsub : bv_unsigned (sub_vec_int (add_vec_int a w) 1)
                   = bv_wrap 64 (bv_unsigned a + (w - 1))).
    { unfold sub_vec_int, add_vec_int.
      rewrite sub_vec64_unsigned. rewrite add_vec64_unsigned.
      rewrite !moi64_unsigned.
      assert (Hww : bv_wrap 64 w = w)
        by (apply bv_wrap_small; rewrite bv_modulus64; lia).
      assert (Hw1 : bv_wrap 64 1 = 1)
        by (apply bv_wrap_small; rewrite bv_modulus64; lia).
      rewrite Hww. rewrite Hw1. rewrite bv_wrap_sub_idemp_l.
      f_equal. lia. }
    rewrite Hsub in Heq.
    pose proof (bv_wrap_in_range 64 (bv_unsigned a + (w - 1))) as Hbr.
    unfold bv_modulus in Hbr.
    change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hbr.
    rewrite (z_land_pagemask (bv_unsigned a) (proj1 Hr) (proj2 Hr)) in Heq.
    rewrite (z_land_pagemask _ (proj1 Hbr) (proj2 Hbr)) in Heq.
    apply (page_num_differs a w Hw Hw8 Hout).
    (* [Z.shiftl _ 12] is injective: shift the equation back down *)
    apply (f_equal (fun z => Z.shiftr z 12)) in Heq.
    rewrite !Z.shiftr_shiftl_l in Heq; [| lia | lia].
    change (12 - 12)%Z with 0%Z in Heq.
    rewrite !Z.shiftl_0_r in Heq. exact Heq. }
  rewrite Hintra. cbn match.
  assert (Hs3 : uint (subrange_vec_dec a (Z.sub 3 1) 0) = bv_unsigned a mod 8).
  { rewrite (uint_unsigned_n _).
    exact (subrange_dec_unsigned_lo0 a 2 8 ltac:(lia) ltac:(vm_compute; reflexivity)). }
  rewrite Hs3.
  replace (Z.ltb (pow2 3 - bv_unsigned a mod 8) w) with true.
  2:{ symmetry. apply Z.ltb_lt. change (pow2 3) with 8. lia. }
  erewrite exec_bind_Some.
  2:{ unfold assert_exp'. cbn match. apply exec_returnm. }
  cbn beta.
  replace (pow2 3 - bv_unsigned a mod 8) with (4096 - bv_unsigned a mod 4096)
    by (change (pow2 3) with 8; lia).
  apply exec_returnm.
Qed.

Lemma page_mask_eq_straddle (a : mword 64) (w : Z) :
  0 < w -> w <= 8 -> ~ in_one_page a w ->
  eq_vec (and_vec a (update_subrange_vec_dec ((ones 64) : bits 64)
                       (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1)))))
         (and_vec (sub_vec_int (add_vec_int a w) 1)
                  (update_subrange_vec_dec ((ones 64) : bits 64)
                     (pagesize_bits - 1) 0 (zeros' (12 - 1 - (0 - 1))))) = false.
Proof.
  intros Hw Hw8 Hout.
  pose proof Hout as Hout'. unfold in_one_page in Hout'.
  pose proof (bv_unsigned_in_range _ a) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hr.
  assert (Hmod : 0 <= bv_unsigned a mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
  apply eq_vec_false_iff. intro Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite !and_vec64_unsigned in Heq. rewrite page_mask64_val in Heq.
  assert (Hsub : bv_unsigned (sub_vec_int (add_vec_int a w) 1)
                 = bv_wrap 64 (bv_unsigned a + (w - 1))).
  { unfold sub_vec_int, add_vec_int.
    rewrite sub_vec64_unsigned. rewrite add_vec64_unsigned.
    rewrite !moi64_unsigned.
    assert (Hww : bv_wrap 64 w = w)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    assert (Hw1 : bv_wrap 64 1 = 1)
      by (apply bv_wrap_small; rewrite bv_modulus64; lia).
    rewrite Hww. rewrite Hw1. rewrite bv_wrap_sub_idemp_l.
    f_equal. lia. }
  rewrite Hsub in Heq.
  pose proof (bv_wrap_in_range 64 (bv_unsigned a + (w - 1))) as Hbr.
  unfold bv_modulus in Hbr.
  change (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (2 ^ 64) in Hbr.
  rewrite (z_land_pagemask (bv_unsigned a) (proj1 Hr) (proj2 Hr)) in Heq.
  rewrite (z_land_pagemask _ (proj1 Hbr) (proj2 Hbr)) in Heq.
  apply (page_num_differs a w Hw Hw8 Hout).
  apply (f_equal (fun z => Z.shiftr z 12)) in Heq.
  rewrite !Z.shiftr_shiftl_l in Heq; [| lia | lia].
  change (12 - 12)%Z with 0%Z in Heq.
  rewrite !Z.shiftl_0_r in Heq. exact Heq.
Qed.

Lemma goodmb_split_on_page_boundary_straddle (Dr Dw : register -> bool)
    (a : mword 64) (w : Z) s mm :
  0 < w -> w <= 8 -> ~ in_one_page a w ->
  goodmb Dr Dw (split_on_page_boundary a w) s mm = true.
Proof.
  intros Hw Hw8 Hout.
  pose proof Hout as Hout'. unfold in_one_page in Hout'.
  assert (Hmod : 0 <= bv_unsigned a mod 4096 < 4096) by (apply Z.mod_pos_bound; lia).
  assert (Hm8 : bv_unsigned a mod 4096 mod 8 = bv_unsigned a mod 4096 - 4088).
  { assert (Hd : (8 | 4088)) by (exists 511; reflexivity).
    assert (Hlo : 4088 <= bv_unsigned a mod 4096) by lia.
    rewrite <- (Z.mod_add (bv_unsigned a mod 4096) (-511) 8); [| lia].
    apply Z.mod_small. lia. }
  assert (Hm8' : bv_unsigned a mod 8 = bv_unsigned a mod 4096 - 4088).
  { rewrite <- Hm8. symmetry. apply Z.mod_mod_divide. exists 512; reflexivity. }
  unfold split_on_page_boundary.
  rewrite (page_mask_eq_straddle a w Hw Hw8 Hout). cbn match.
  assert (Hs3 : uint (subrange_vec_dec a (Z.sub 3 1) 0) = bv_unsigned a mod 8).
  { rewrite (uint_unsigned_n _).
    exact (subrange_dec_unsigned_lo0 a 2 8 ltac:(lia) ltac:(vm_compute; reflexivity)). }
  rewrite Hs3.
  replace (Z.ltb (pow2 3 - bv_unsigned a mod 8) w) with true.
  2:{ symmetry. apply Z.ltb_lt. change (pow2 3) with 8. lia. }
  erewrite gm_bind; [ | apply goodmb_assert_exp'_true | apply exec_assert_exp'_true ].
  cbn beta. apply goodmb_returnm.
Qed.

(* the two parts' own geometry: both lie in one page, and both are non-empty *)
Lemma straddle_bounds (a : mword 64) (w : Z) :
  0 < w -> w <= 8 -> ~ in_one_page a w ->
  0 < 4096 - bv_unsigned a mod 4096 /\
  0 < w - (4096 - bv_unsigned a mod 4096) /\
  4096 - bv_unsigned a mod 4096 <= 8 /\
  w - (4096 - bv_unsigned a mod 4096) <= 8.
Proof.
  intros Hw Hw8 Hout. unfold in_one_page in Hout.
  pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)). lia.
Qed.

Lemma straddle_part1_in_page (a : mword 64) (w : Z) :
  in_one_page a (4096 - bv_unsigned a mod 4096).
Proof. unfold in_one_page. lia. Qed.

Lemma straddle_part2_in_page (a : mword 64) (w : Z) :
  0 < w -> w <= 8 -> ~ in_one_page a w ->
  in_one_page (add_vec_int a (4096 - bv_unsigned a mod 4096))
              (w - (4096 - bv_unsigned a mod 4096)).
Proof.
  intros Hw Hw8 Hout. pose proof Hout as Hout'. unfold in_one_page in Hout' |- *.
  assert (Hz : bv_unsigned (add_vec_int a (4096 - bv_unsigned a mod 4096)) mod 4096 = 0).
  { unfold add_vec_int. rewrite add_vec64_unsigned. rewrite moi64_unsigned.
    rewrite bv_wrap_add_idemp_r. unfold bv_wrap.
    rewrite (Z.mod_mod_divide _ (bv_modulus 64) 4096);
      [| rewrite bv_modulus64; exists 4503599627370496; reflexivity].
    assert (He : bv_unsigned a + (4096 - bv_unsigned a mod 4096)
                 = 4096 * (bv_unsigned a / 4096 + 1))
      by (pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)); lia).
    rewrite He. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  rewrite Hz.
  pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)). lia.
Qed.
