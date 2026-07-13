(* Pt4kWalk.v -- the privilege-S, vpn-SYMBOLIC 4KB (level-0 leaf) Sv39
   3-level page walk and the access-generic three-way translate, factored
   out of TrampPt.v / TrampTlb.v so the faithful (kvmmake-shaped) all-4KB
   kernel page table can drive it from SmodeCore's fetch chain and from
   the data-access towers.  All lemmas are verbatim moves.  This file is
   deliberately IRIS-FREE (vanilla Ltac: [rewrite a, b] / [rewrite .. by ..]),
   matching the moved proofs' original environment; the ssreflect-env
   support lemmas live in SmodePte.v.  *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpGprCsrwCommon WpGprCsrwB.
Require Import SmodePte.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 4. The PTE layer + the 3-level 4KB walk + tlb4k entry (from TrampPt). *)
(* ===================================================================== *)

(* ===================================================================== *)
(* 2. PTEs.  [mk_pte ppn flags]: bits 63:54 = 0, 53:10 = ppn, 9:0 = flags. *)
(* ===================================================================== *)

Definition mk_pte (ppn : mword 44) (flags : Z) : mword 64 :=
  zero_extend' 64 (concat_vec ppn (mword_of_int flags : mword 10)).

(* the PTE physical address for table page [base] at walk index [idx]. *)
Definition pte_addr_at (base : mword 44) (idx : mword 9) : mword 64 :=
  zero_extend' 64 (concat_vec base (concat_vec idx (zeros' 3 : mword 3))).

(* PTE flag bytes: V=1 non-leaf pointer; leaf X|R|A|V for the trampoline
   (kvmmap/proc_pagetable map it PTE_R|PTE_X; A preset); leaf D|A|W|R|V for
   the trapframe (PTE_R|PTE_W; A/D preset). *)
Definition PTE_PTR   : Z := 0x01.
Definition PTE_TRAMP : Z := 0x4B.
Definition PTE_TF    : Z := 0xC7.

(* ===================================================================== *)
(* 3. Field extraction with a SYMBOLIC ppn.                               *)
(* ===================================================================== *)

(* Z arithmetic: a shifted value and a small value have disjoint bits, and a
   disjoint or is an add. *)
Lemma Z_land_shift_low (a f k : Z) :
  0 <= k -> 0 <= f < 2 ^ k ->
  Z.land (a * 2 ^ k) f = 0.
Proof.
  intros Hk Hf.
  apply Z.bits_inj_iff'; intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec i k) as [Hlt | Hge].
  - replace (Z.testbit (a * 2 ^ k) i) with false;
      [ reflexivity
      | symmetry; rewrite <- Z.shiftl_mul_pow2 by lia; apply Z.shiftl_spec_low; lia ].
  - destruct (Z.ltb_spec 0 f) as [Hpos | Hnp].
    + replace (Z.testbit f i) with false; [ apply andb_false_r |].
      symmetry; apply Z.bits_above_log2; [lia |].
      assert (Z.log2 f < k); [| lia].
      apply Z.log2_lt_pow2; [exact Hpos | exact (proj2 Hf)].
    + replace f with 0 by lia. rewrite Z.bits_0. apply andb_false_r.
Qed.

Lemma Z_lor_disjoint_add (a b : Z) :
  Z.land a b = 0 -> Z.lor a b = a + b.
Proof.
  intro Hd. rewrite <- (Z.lxor_lor _ _ Hd).
  symmetry. apply Z.add_nocarry_lxor. exact Hd.
Qed.

Lemma mk_pte_unsigned (p : mword 44) (f : Z) :
  0 <= f < 1024 ->
  bv_unsigned (mk_pte p f) = bv_unsigned p * 1024 + f.
Proof.
  intros Hf.
  unfold mk_pte, zero_extend', concat_vec.
  cbv [Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  destruct (Z.eq_dec (Z.of_N (44 + 10)) (44 + 10)) as [e | ne]; [| exfalso; exact (ne eq_refl)].
  rewrite (TypeCasts.cast_Z_refl (H := e)).
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.zero_extend, MachineWord.MachineWord.concat, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  erewrite bv_concat_unsigned by (cbn; lia).
  cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
  rewrite Z_to_bv_unsigned.
  rewrite (bv_wrap_small (MachineWord.MachineWord.Z_idx 10) f
             ltac:(unfold bv_modulus; change (Z.of_N (MachineWord.MachineWord.Z_idx 10)) with 10; lia)).
  change (Z.of_N 10) with 10.
  rewrite Z.shiftl_mul_pow2 by lia.
  change 1024 with (2 ^ 10).
  apply Z_lor_disjoint_add.
  apply Z_land_shift_low; [lia | change (2 ^ 10) with 1024; exact Hf].
Qed.

(* subrange extraction over the UNSIGNED value at the three concrete PTE
   fields: flags (7..0), ppn (53..10), ext (63..54).  All are
   (x >> lo) mod 2^(hi-lo+1). *)
Lemma subrange64_unsigned_7_0 (x : mword 64) :
  bv_unsigned (subrange_vec_dec x 7 0) = bv_unsigned x `mod` 2 ^ 8.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0.
  rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (7 - 0 + 1)) with 8%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma subrange64_unsigned_53_10 (x : mword 64) :
  bv_unsigned (subrange_vec_dec x 53 10) = (bv_unsigned x ≫ 10) `mod` 2 ^ 44.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 10)) with 10.
  change (MachineWord.MachineWord.Z_idx (53 - 10 + 1)) with 44%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma subrange64_unsigned_63_54 (x : mword 64) :
  bv_unsigned (subrange_vec_dec x 63 54) = (bv_unsigned x ≫ 54) `mod` 2 ^ 10.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 54)) with 54.
  change (MachineWord.MachineWord.Z_idx (63 - 54 + 1)) with 10%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

(* the three field-extraction corollaries with a SYMBOLIC ppn. *)
Lemma mk_pte_flags (p : mword 44) (f : Z) :
  0 <= f < 256 ->
  subrange_vec_dec (mk_pte p f) 7 0 = (mword_of_int f : mword 8).
Proof.
  intros Hf. apply bv_eq.
  rewrite subrange64_unsigned_7_0.
  rewrite (mk_pte_unsigned p f ltac:(lia)).
  cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
  rewrite Z_to_bv_unsigned.
  rewrite (bv_wrap_small (MachineWord.MachineWord.Z_idx 8) f
             ltac:(unfold bv_modulus; change (Z.of_N (MachineWord.MachineWord.Z_idx 8)) with 8; lia)).
  replace (bv_unsigned p * 1024 + f) with (f + (bv_unsigned p * 4) * 2 ^ 8) by lia.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

Lemma mk_pte_ppn_field (p : mword 44) (f : Z) :
  0 <= f < 1024 ->
  subrange_vec_dec (mk_pte p f) 53 10 = p.
Proof.
  intros Hf. apply bv_eq.
  rewrite subrange64_unsigned_53_10.
  rewrite (mk_pte_unsigned p f Hf).
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 10) with 1024.
  rewrite Z.div_add_l by lia.
  rewrite (Z.div_small f 1024) by lia.
  rewrite Z.add_0_r.
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ p) as Hp. unfold bv_modulus in Hp.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 44)) with 44 in Hp.
  exact Hp.
Qed.

Lemma mk_pte_ext (p : mword 44) (f : Z) :
  0 <= f < 1024 ->
  subrange_vec_dec (mk_pte p f) 63 54 = (mword_of_int 0 : mword 10).
Proof.
  intros Hf. apply bv_eq.
  rewrite subrange64_unsigned_63_54.
  rewrite (mk_pte_unsigned p f Hf).
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (bv_unsigned_in_range _ p) as Hp. unfold bv_modulus in Hp.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 44)) with 44 in Hp.
  rewrite (Z.div_small _ (2 ^ 54)) by (change (2 ^ 54) with (2 ^ 44 * 1024); nia).
  reflexivity.
Qed.

(* alignment: every PTE address ends in 3 zero bits, hence is 8-aligned. *)
Lemma pte_addr_at_unsigned (base : mword 44) (idx : mword 9) :
  bv_unsigned (pte_addr_at base idx) = bv_unsigned base * 4096 + bv_unsigned idx * 8.
Proof.
  unfold pte_addr_at, zero_extend', concat_vec.
  cbv [Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  destruct (Z.eq_dec (Z.of_N (9 + 3)) (9 + 3)) as [e1 | ne]; [| exfalso; exact (ne eq_refl)].
  rewrite (TypeCasts.cast_Z_refl (H := e1)).
  destruct (Z.eq_dec (Z.of_N (44 + Z.to_N (9 + 3))) (44 + (9 + 3))) as [e2 | ne]; [| exfalso; exact (ne eq_refl)].
  rewrite (TypeCasts.cast_Z_refl (H := e2)).
  unfold to_word_idx. rewrite !MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.zero_extend, MachineWord.MachineWord.concat, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  erewrite bv_concat_unsigned by (cbn; lia).
  erewrite bv_concat_unsigned by (cbn; lia).
  change (bv_unsigned (MachineWord.MachineWord.zeros 3)) with 0.
  rewrite Z.lor_0_r.
  change (Z.of_N 3) with 3.
  change (Z.of_N (Z.to_N (9 + 3))) with 12.
  rewrite !Z.shiftl_mul_pow2 by lia.
  pose proof (bv_unsigned_in_range _ idx) as Hi. unfold bv_modulus in Hi.
  change (MachineWord.MachineWord.Z_idx 9) with 9%N in Hi.
  change (Z.of_N 9%N) with 9 in Hi.
  change (2 ^ 9) with 512 in Hi.
  replace (bv_unsigned idx * 2 ^ 3) with (bv_unsigned idx * 8) by lia.
  replace (bv_unsigned base * 2 ^ 12) with (bv_unsigned base * 4096) by lia.
  apply Z_lor_disjoint_add.
  change 4096 with (2 ^ 12).
  apply Z_land_shift_low; [lia |].
  change (2 ^ 12) with 4096. lia.
Qed.

Lemma pte_addr_at_aligned8 (base : mword 44) (idx : mword 9) :
  is_aligned_paddr (Physaddr (pte_addr_at base idx)) 8 = true.
Proof.
  unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite uint_unsigned.
  rewrite pte_addr_at_unsigned.
  replace (bv_unsigned base * 4096 + bv_unsigned idx * 8)
    with ((bv_unsigned base * 512 + bv_unsigned idx) * 8) by lia.
  apply Z.rem_mul. lia.
Qed.

(* ===================================================================== *)
(* 4. currentlyEnabled Ext_Svnapot (level-0 walks probe it; misa.S=1).    *)
(* ===================================================================== *)

Lemma exec_hartSupports_Svnapot s : exec (hartSupports Ext_Svnapot) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Svnapot) 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm eq_refl s)).
  replace (andb true (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
  apply exec_returnM.
Qed.

Lemma exec_currentlyEnabled_Svnapot s :
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (currentlyEnabled Ext_Svnapot) s = Some (true, s).
Proof.
  intro HS. unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  change (Z.geb (currentlyEnabled_measure Ext_Svnapot) 0) with true. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Svnapot s)). cbn match.
  match goal with |- context[_rec_currentlyEnabled Ext_Sv39 ?k ?a] => destruct a end.
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  match goal with |- context[Z.geb ?kk 0] => change (Z.geb kk 0) with true end.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnm eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Sv39 s)). cbn match.
  crush_rec_cE_S s. rewrite HS. reflexivity.
Qed.

(* ===================================================================== *)
(* 5. The three-level Sv39 page walk through [mk_pte] tables.             *)
(*    Stated per level with CONCRETE reclimits (pt_walk at level 2 uses   *)
(*    reclimit 2 -> 1 -> 0) but a GENERIC [Acc] argument, since the       *)
(*    nested recursive call's [_limit_reduces_bool] is opaque and only    *)
(*    [destruct]ing the Acc term exposes constructor form for [cbn].      *)
(* ===================================================================== *)

Section TrampWalk.
  Context (access : MemoryAccessType mem_payload) (mxr do_sum : bool).
  Context (vpn : mword 27).
  (* table page ppns root -> l1 -> l0, and the leaf ppn/flags. *)
  Context (p2 p1 p0 lppn : mword 44) (lflags : Z).
  Context (region2 region1 region0 : PMA_Region).
  Context (menvcfg0 : mword 64).
  Context (s : mstate).

  Local Notation idx2 := (subrange_vec_dec vpn 26 18).
  Local Notation idx1 := (subrange_vec_dec vpn 17 9).
  Local Notation idx0 := (subrange_vec_dec vpn 8 0).
  Local Notation a2 := (pte_addr_at p2 idx2).
  Local Notation a1 := (pte_addr_at p1 idx1).
  Local Notation a0 := (pte_addr_at p0 idx0).
  Local Notation pte2 := (mk_pte p1 PTE_PTR).
  Local Notation pte1 := (mk_pte p0 PTE_PTR).
  Local Notation pte0 := (mk_pte lppn lflags).

  Hypothesis Hlf : 0 <= lflags < 256.

  (* leaf-flag reductions (concrete once lflags / access are instantiated) *)
  Hypothesis Hinv0 : forall s', exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int lflags)) (Mk_PTE_Ext (mword_of_int 0))) s' = Some (false, s').
  Hypothesis Hnl0 : pte_is_non_leaf (Mk_PTE_Flags (mword_of_int lflags : mword 8)) = false.
  Hypothesis Hchk0 : forall s', exec (check_PTE_permission access Supervisor mxr do_sum (Mk_PTE_Flags (mword_of_int lflags)) (Mk_PTE_Ext (mword_of_int 0)) tt) s' = Some (PTE_Check_Success tt, s').
  Hypothesis HextN0 : eq_vec (_get_PTE_Ext_N (Mk_PTE_Ext (mword_of_int 0 : mword 10))) ('b"1") = false.
  Hypothesis HG0 : eq_vec (_get_PTE_Flags_G (Mk_PTE_Flags (mword_of_int lflags : mword 8))) ('b"1") = false.

  (* misa.S (for the level-0 Svnapot probe) *)
  Hypothesis HmisaS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.

  (* shared PMP facts at s *)
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.

  (* menvcfg *)
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = menvcfg0.
  Hypothesis HPBMTE : eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true.

  (* per-level PTE-read facts at s *)
  Hypothesis Hrange2 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a2) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis Hmatch2 : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a2) 8 = Some region2.
  Hypothesis Hpte2 : (override_PMA (PMA_Region_attributes region2) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis Hc2 : exec (within_clint (Physaddr a2) 8) s = Some (false, s).
  Hypothesis Hsig2 : exec (within_sig (Physaddr a2) 8) s = Some (false, s).
  Hypothesis Hh2 : exec (within_htif_readable (Physaddr a2) 8) s = Some (false, s).
  Hypothesis Hdev2 : dev_addr a2 = false.
  Hypothesis Hbytes2 : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add a2 j) = Some (nth_byte pte2 j).

  Hypothesis Hrange1 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a1) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis Hmatch1 : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a1) 8 = Some region1.
  Hypothesis Hpte1 : (override_PMA (PMA_Region_attributes region1) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis Hc1 : exec (within_clint (Physaddr a1) 8) s = Some (false, s).
  Hypothesis Hsig1 : exec (within_sig (Physaddr a1) 8) s = Some (false, s).
  Hypothesis Hh1 : exec (within_htif_readable (Physaddr a1) 8) s = Some (false, s).
  Hypothesis Hdev1 : dev_addr a1 = false.
  Hypothesis Hbytes1 : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add a1 j) = Some (nth_byte pte1 j).

  Hypothesis Hrange0 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a0) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis Hmatch0 : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a0) 8 = Some region0.
  Hypothesis Hpte0 : (override_PMA (PMA_Region_attributes region0) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis Hc0 : exec (within_clint (Physaddr a0) 8) s = Some (false, s).
  Hypothesis Hsig0 : exec (within_sig (Physaddr a0) 8) s = Some (false, s).
  Hypothesis Hh0 : exec (within_htif_readable (Physaddr a0) 8) s = Some (false, s).
  Hypothesis Hdev0 : dev_addr a0 = false.
  Hypothesis Hbytes0 : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add a0 j) = Some (nth_byte pte0 j).

  (* the walk's leaf output *)
  Definition tramp_walk_out : PTW_Output 39 :=
    Build_PTW_Output 39 lppn (autocast (T := mword) pte0) (Physaddr a0) 0 PBMT_PMA false.

  Lemma exec_rec_pt_walk_l0 (acc : Acc (Zwf 0) 0) :
    exec (_rec_pt_walk 39 vpn access Supervisor mxr do_sum p0 0 false tt 0 acc) s
    = Some (Ok (tramp_walk_out, tt), s).
  Proof.
    destruct acc.
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    assert (Hae1 : exec (Defs.assert_exp' (0 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold Defs.assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold Defs.assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with a0 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_read_pte_S a0 region0 pte0 s
                  HA Hord Hrange0 HR Hmatch0 (pte_addr_at_aligned8 p0 idx0) Hpte0 Hc0 Hsig0 Hh0 Hdev0 Hbytes0)).
    match goal with |- context[Mk_PTE_Flags (@subrange_vec_dec ?w _ 7 0)] =>
      change w with 64 end.
    rewrite (mk_pte_flags lppn lflags Hlf).
    unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
    rewrite (mk_pte_ext lppn lflags ltac:(lia)).
    rewrite (execR_liftR_seq _ _ _ _ _ (Hinv0 s)).
    cbn match.
    rewrite Hnl0. cbv iota beta.
    change (Z.gtb 0 0) with false. cbv iota beta.
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR (Defs.bind0 A B) s = Some (inr (PTE_Check_Success tt), s)) end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR. rewrite (Hchk0 s). cbn match. reflexivity. }
    rewrite (execR_bind_Some _ _ _ _ _ HAB).
    cbv iota beta. cbn match.
    change (Z.gtb 0 0) with false. cbv iota beta.
    (* Svnapot probe: enabled, but the PTE's N bit is 0; the ppn stage
       returns [autocast (PPN_of_PTE pte0)]. *)
    match goal with |- context[Defs.bind (and_boolM ?A ?B) ?f] =>
      assert (Hppn : execR (Defs.bind (and_boolM A B) f) s
                     = Some (inr (autocast (T := mword) (PPN_of_PTE (mk_pte lppn lflags))), s)) end.
    { rewrite (execR_bind_Some _ _ _ false s).
      2:{ unfold and_boolM.
          rewrite (execR_liftR_seq _ _ _ _ _ (exec_currentlyEnabled_Svnapot s HmisaS)).
          cbv iota beta. rewrite HextN0. apply execR_returnR_fwd. }
      cbv iota beta. apply execR_returnR_fwd. }
    rewrite (execR_bind_Some _ _ _ _ _ Hppn).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg menvcfg s)).
    rewrite Hmenv. rewrite HPBMTE. cbv iota beta.
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    rewrite execR_returnR. cbn match.
    unfold tramp_walk_out.
    rewrite HG0. cbn [orb].
    unfold PPN_of_PTE. change (Z.eqb 64 32) with false. cbv iota beta.
    rewrite (mk_pte_ppn_field lppn lflags ltac:(lia)).
    rewrite !autocast_id. reflexivity.
  Qed.

  Lemma exec_rec_pt_walk_l1 (acc : Acc (Zwf 0) 1) :
    exec (_rec_pt_walk 39 vpn access Supervisor mxr do_sum p1 1 false tt 1 acc) s
    = Some (Ok (tramp_walk_out, tt), s).
  Proof.
    destruct acc.
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    assert (Hae1 : exec (Defs.assert_exp' (1 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold Defs.assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold Defs.assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with a1 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_read_pte_S a1 region1 pte1 s
                  HA Hord Hrange1 HR Hmatch1 (pte_addr_at_aligned8 p1 idx1) Hpte1 Hc1 Hsig1 Hh1 Hdev1 Hbytes1)).
    match goal with |- context[Mk_PTE_Flags (@subrange_vec_dec ?w _ 7 0)] =>
      change w with 64 end.
    rewrite (mk_pte_flags p0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
    rewrite (mk_pte_ext p0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    assert (Hinv : exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int PTE_PTR)) (Mk_PTE_Ext (mword_of_int 0))) s = Some (false, s))
      by (vm_compute; reflexivity).
    rewrite (execR_liftR_seq _ _ _ _ _ Hinv).
    cbn match.
    replace (pte_is_non_leaf (Mk_PTE_Flags (mword_of_int PTE_PTR : mword 8))) with true
      by (vm_compute; reflexivity).
    cbv iota beta.
    change (Z.gtb 1 0) with true. cbv iota beta.
    replace (orb false (eq_vec (_get_PTE_Flags_G (Mk_PTE_Flags (mword_of_int PTE_PTR : mword 8))) ('b"1"))) with false
      by (vm_compute; reflexivity).
    unfold PPN_of_PTE. change (Z.eqb 64 32) with false. cbv iota beta.
    rewrite (mk_pte_ppn_field p0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite !autocast_id.
    change (Z.sub 1 1) with 0.
    rewrite execR_liftR.
    rewrite exec_rec_pt_walk_l0.
    reflexivity.
  Qed.

  Lemma exec_rec_pt_walk_l2 (acc : Acc (Zwf 0) 2) :
    exec (_rec_pt_walk 39 vpn access Supervisor mxr do_sum p2 2 false tt 2 acc) s
    = Some (Ok (tramp_walk_out, tt), s).
  Proof.
    destruct acc.
    cbn [_rec_pt_walk].
    rewrite exec_catch_early_return.
    assert (Hae1 : exec (Defs.assert_exp' (2 >=? 0) "recursion limit reached") s = Some (eq_refl, s))
      by (unfold Defs.assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae1).
    assert (Hae2 : exec (Defs.assert_exp' ((39 =? 32) || (xlen =? 64)) "sys/vmem.sail:128.36-128.37") s = Some (eq_refl, s))
      by (unfold Defs.assert_exp'; cbn match; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with a2 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    rewrite (execR_liftR_seq _ _ _ _ _
               (exec_read_pte_S a2 region2 pte2 s
                  HA Hord Hrange2 HR Hmatch2 (pte_addr_at_aligned8 p2 idx2) Hpte2 Hc2 Hsig2 Hh2 Hdev2 Hbytes2)).
    match goal with |- context[Mk_PTE_Flags (@subrange_vec_dec ?w _ 7 0)] =>
      change w with 64 end.
    rewrite (mk_pte_flags p1 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
    rewrite (mk_pte_ext p1 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    assert (Hinv : exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int PTE_PTR)) (Mk_PTE_Ext (mword_of_int 0))) s = Some (false, s))
      by (vm_compute; reflexivity).
    rewrite (execR_liftR_seq _ _ _ _ _ Hinv).
    cbn match.
    replace (pte_is_non_leaf (Mk_PTE_Flags (mword_of_int PTE_PTR : mword 8))) with true
      by (vm_compute; reflexivity).
    cbv iota beta.
    change (Z.gtb 2 0) with true. cbv iota beta.
    replace (orb false (eq_vec (_get_PTE_Flags_G (Mk_PTE_Flags (mword_of_int PTE_PTR : mword 8))) ('b"1"))) with false
      by (vm_compute; reflexivity).
    unfold PPN_of_PTE. change (Z.eqb 64 32) with false. cbv iota beta.
    rewrite (mk_pte_ppn_field p1 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite !autocast_id.
    change (Z.sub 2 1) with 1.
    rewrite execR_liftR.
    rewrite exec_rec_pt_walk_l1.
    reflexivity.
  Qed.

  (* the whole 3-level walk. *)
  Lemma exec_pt_walk_tramp3 :
    exec (pt_walk 39 vpn access Supervisor mxr do_sum p2 2 false tt) s
    = Some (Ok (tramp_walk_out, tt), s).
  Proof.
    unfold pt_walk.
    apply exec_rec_pt_walk_l2.
  Qed.

End TrampWalk.

(* ===================================================================== *)
(* 6. The 4K TLB entry the level-0 walk installs, and its TLB lemmas.     *)
(* ===================================================================== *)

(* small bitvector identities, keyed on the mask's UNSIGNED value (the bv
   record's well-formedness field blocks syntactic [change]/[replace]). *)
Lemma and27_ones (x m : mword 27) :
  bv_unsigned m = 2 ^ 27 - 1 -> and_vec x m = x.
Proof.
  intro Hm. apply bv_eq.
  cbv [and_vec Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context[Z.land ?a ?b] =>
    replace b with (2 ^ 27 - 1) by (symmetry; exact Hm) end.
  change (2 ^ 27 - 1) with (Z.ones 27).
  rewrite Z.land_ones by lia.
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 27)) with 27 in Hx. exact Hx.
Qed.

Lemma and44_ones (x m : mword 44) :
  bv_unsigned m = 2 ^ 44 - 1 -> and_vec x m = x.
Proof.
  intro Hm. apply bv_eq.
  cbv [and_vec Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context[Z.land ?a ?b] =>
    replace b with (2 ^ 44 - 1) by (symmetry; exact Hm) end.
  change (2 ^ 44 - 1) with (Z.ones 44).
  rewrite Z.land_ones by lia.
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 44)) with 44 in Hx. exact Hx.
Qed.

Lemma and64_zero_r (x m : mword 64) :
  bv_unsigned m = 0 -> and_vec x m = (zeros' 64 : mword 64).
Proof.
  intro Hm. apply bv_eq.
  cbv [and_vec Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context[Z.land ?a ?b] =>
    replace b with 0 by (symmetry; exact Hm) end.
  rewrite Z.land_0_r.
  vm_compute (bv_unsigned (zeros' 64 : mword 64)). reflexivity.
Qed.

Lemma zero_extend64_id (x : mword 64) : zero_extend' 64 x = x.
Proof.
  apply bv_eq.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.with_word' to_word get_word SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.zero_extend, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  reflexivity.
Qed.

Lemma zero_extend44_id (x : mword 44) : zero_extend' 44 x = x.
Proof.
  apply bv_eq.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.with_word' to_word get_word SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.zero_extend, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  reflexivity.
Qed.

Lemma zext44_and_ones (x m : mword 44) :
  bv_unsigned m = 2 ^ 44 - 1 -> zero_extend' 44 (and_vec x m) = x.
Proof.
  intro Hm. rewrite (and44_ones x m Hm). apply zero_extend44_id.
Qed.

Lemma subrange64_63_0_id (x : mword 64) : subrange_vec_dec x 63 0 = x.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0.
  rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (63 - 0 + 1)) with 64%N.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ x) as Hx.
  change (MachineWord.MachineWord.Z_idx 64) with 64%N in Hx.
  exact Hx.
Qed.

(* the 4K (level-0, non-global) TLB entry. *)
Definition tlb4k_entry (asid : mword 16) (vpn : mword 27) (pp : mword 44)
    (pte : mword 64) (ptea : mword 64) : TLB_Entry := {|
  TLB_Entry_asid     := asid;
  TLB_Entry_global   := false;
  TLB_Entry_vpn      := sign_extend' 45 vpn;
  TLB_Entry_levelMask := mword_of_int 0;
  TLB_Entry_ppn      := pp;
  TLB_Entry_pte      := pte;
  TLB_Entry_pteAddr  := Physaddr ptea;
|}.

(* add_to_TLB at level 0 installs [tlb4k_entry] at the direct-mapped slot. *)
Lemma exec_add_to_TLB_4k (asid : mword 16) (vpn : mword 27) (pp : mword 44)
    (pte ptea : mword 64) s :
  exec (add_to_TLB 39 asid vpn pp pte (Physaddr ptea) 0 false) s
  = Some (tt, set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                               (tlb_hash (__id 39) vpn)
                               (Some (tlb4k_entry asid vpn pp pte ptea)))).
Proof.
  unfold add_to_TLB. cbn zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
  match goal with |- context[Defs.bind (Defs.bind0 (Defs.write_reg ?r ?v) ?n) ?k] =>
    assert (Hwr : exec (Defs.bind0 (Defs.write_reg r v) n) s
                  = Some (v, set_reg s r v)) end.
  { rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg _ _ s)).
    rewrite (exec_read_reg tlb _).
    unfold set_reg; cbn [sregs]; rewrite register_lookup_set; reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ Hwr).
  cbv beta. rewrite exec_returnM.
  unfold tlb_add_callback.
  do 5 f_equal. unfold tlb4k_entry.
  change (__id 39 - 12) with 27.
  change (if __id 39 =? 32 then 22 else 44) with 44.
  f_equal;
  lazymatch goal with
  | |- context[and_vec vpn _] =>
      first [ apply and27_ones; vm_compute; reflexivity
            | f_equal; first [ apply and27_ones; vm_compute; reflexivity
                             | reflexivity ] ]
  | |- context[and_vec pp _] =>
      first [ apply zext44_and_ones; vm_compute; reflexivity
            | f_equal; first [ apply zext44_and_ones; vm_compute; reflexivity
                             | reflexivity ] ]
  | |- context[zero_extend' 64 pte] => apply zero_extend64_id
  | |- _ => apply bv_eq; vm_compute; reflexivity
  end.
Qed.

(* ===================================================================== *)
(* 5. 4K TLB lookup / translate (from TrampTlb).                          *)
(* ===================================================================== *)

(* ===================================================================== *)
(* 7. TLB lookup / translate through a 4K entry.                          *)
(* ===================================================================== *)

Lemma exec_lookup_TLB_nonmatch (vpn : mword 27) (asid : mword 16)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (ent : TLB_Entry) s :
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
  match_TLB_Entry ent asid (sign_extend' (57 - 12) vpn) = false ->
  exec (lookup_TLB 39 asid vpn) s = Some (None, s).
Proof.
  intros Htlb Hvec Hm.
  unfold lookup_TLB.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
  rewrite Htlb. rewrite Hvec.
  match goal with |- context[match_TLB_Entry ?e ?a ?v] =>
    replace (match_TLB_Entry e a v) with false by (symmetry; exact Hm) end.
  apply exec_returnm.
Qed.

Lemma exec_lookup_TLB_hit_ent (vpn : mword 27) (asid : mword 16)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (ent : TLB_Entry) s :
  register_lookup tlb s.(sregs) = tlbvec ->
  vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent ->
  match_TLB_Entry ent asid (sign_extend' (57 - 12) vpn) = true ->
  exec (lookup_TLB 39 asid vpn) s = Some (Some (tlb_hash (__id 39) vpn, ent), s).
Proof.
  intros Htlb Hvec Hm.
  unfold lookup_TLB.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
  rewrite Htlb. rewrite Hvec.
  match goal with |- context[match_TLB_Entry ?e ?a ?v] =>
    replace (match_TLB_Entry e a v) with true by (symmetry; exact Hm) end.
  apply exec_returnm.
Qed.

(* [tlb_get_ppn] on a 4K entry (levelMask 0) is the entry's ppn, for ANY
   looked-up vpn. *)
Lemma or64_zeros_r (x : mword 64) : or_vec x (zeros' 64) = x.
Proof.
  apply bv_eq.
  cbv [or_vec Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.or.
  rewrite bv_or_unsigned.
  change (bv_unsigned (zeros' 64 : mword 64)) with 0.
  rewrite Z.lor_0_r.
  reflexivity.
Qed.

Lemma trunc44_zext (x : mword 44) : trunc 44 (zero_extend' 64 x) = x.
Proof.
  apply bv_eq.
  unfold trunc, vector_truncate, slice.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  cbv [zero_extend' Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.with_word' to_word get_word SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.zero_extend, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0.
  rewrite Z.shiftr_0_r.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ x) as Hx.
  change (MachineWord.MachineWord.Z_idx 44) with 44%N in Hx.
  unfold bv_modulus in Hx |- *.
  change (MachineWord.MachineWord.Z_idx 44) with 44%N.
  exact Hx.
Qed.

Lemma tlb_get_ppn_4k (asid : mword 16) (vpn vpn' : mword 27) (pp : mword 44)
    (pte ptea : mword 64) :
  tlb_get_ppn 39 (tlb4k_entry asid vpn pp pte ptea) vpn' = pp.
Proof.
  unfold tlb_get_ppn, tlb4k_entry.
  cbn [TLB_Entry_levelMask TLB_Entry_ppn].
  match goal with |- context[and_vec ?x ?m] =>
    replace (and_vec x m) with (zeros' 64 : mword 64);
    [| symmetry; apply and64_zero_r; vm_compute; reflexivity] end.
  rewrite or64_zeros_r.
  apply trunc44_zext.
Qed.

(* [tlb_get_pte] on a 4K entry is the stored 64-bit PTE. *)
Lemma tlb_get_pte_4k (asid : mword 16) (vpn : mword 27) (pp : mword 44)
    (pte ptea : mword 64) :
  tlb_get_pte 8 (tlb4k_entry asid vpn pp pte ptea) = autocast (T := mword) pte.
Proof.
  unfold tlb_get_pte, tlb4k_entry. cbn [TLB_Entry_pte].
  f_equal.
  match goal with |- @subrange_vec_dec ?w _ ?hi ?lo = _ =>
    change hi with 63; change lo with 0 end.
  apply subrange64_63_0_id.
Qed.

Lemma and45_ones (x m : mword 45) :
  bv_unsigned m = 2 ^ 45 - 1 -> and_vec x m = x.
Proof.
  intro Hm. apply bv_eq.
  cbv [and_vec Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.and.
  rewrite bv_and_unsigned.
  match goal with |- context[Z.land ?a ?b] =>
    replace b with (2 ^ 45 - 1) by (symmetry; exact Hm) end.
  change (2 ^ 45 - 1) with (Z.ones 45).
  rewrite Z.land_ones by lia.
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 45)) with 45 in Hx. exact Hx.
Qed.

(* a 4K entry with asid 0 always matches its own vpn under asid 0. *)
Lemma match_tlb4k_self (vpn : mword 27) (pp : mword 44) (pte ptea : mword 64) :
  match_TLB_Entry (tlb4k_entry (mword_of_int 0) vpn pp pte ptea)
    (mword_of_int 0) (sign_extend' (57 - 12) vpn) = true.
Proof.
  unfold match_TLB_Entry, tlb4k_entry.
  cbn [TLB_Entry_asid TLB_Entry_global TLB_Entry_vpn TLB_Entry_levelMask].
  apply andb_true_intro. split.
  - vm_compute; reflexivity.
  - unfold eq_vec. rewrite MachineWord.MachineWord.eqb_true_iff.
    symmetry. apply and45_ones. vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* 7b. translate / translateAddr through the trampoline-style 4K mapping. *)
(*     Same ambient hypotheses as [TrampWalk]; additionally the access's  *)
(*     effectivePrivilege / shadow-stack reductions and the satp facts.   *)
(* ===================================================================== *)

Section TrampTranslate.
  Context (access : MemoryAccessType mem_payload).
  Context (vpn : mword 27).
  Context (p2 p1 p0 lppn : mword 44) (lflags : Z).
  Context (region2 region1 region0 : PMA_Region).
  Context (menvcfg0 : mword 64).
  Context (s : mstate).

  Local Notation idx2 := (subrange_vec_dec vpn 26 18).
  Local Notation idx1 := (subrange_vec_dec vpn 17 9).
  Local Notation idx0 := (subrange_vec_dec vpn 8 0).
  Local Notation a2 := (pte_addr_at p2 idx2).
  Local Notation a1 := (pte_addr_at p1 idx1).
  Local Notation a0 := (pte_addr_at p0 idx0).
  Local Notation pte2 := (mk_pte p1 PTE_PTR).
  Local Notation pte1 := (mk_pte p0 PTE_PTR).
  Local Notation pte0 := (mk_pte lppn lflags).

  Hypothesis Hlf : 0 <= lflags < 256.
  Hypothesis Hinv0 : forall s', exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int lflags)) (Mk_PTE_Ext (mword_of_int 0))) s' = Some (false, s').
  Hypothesis Hnl0 : pte_is_non_leaf (Mk_PTE_Flags (mword_of_int lflags : mword 8)) = false.
  Hypothesis Hchk0 : forall (mxr do_sum : bool) s', exec (check_PTE_permission access Supervisor mxr do_sum (Mk_PTE_Flags (mword_of_int lflags)) (Mk_PTE_Ext (mword_of_int 0)) tt) s' = Some (PTE_Check_Success tt, s').
  Hypothesis HextN0 : eq_vec (_get_PTE_Ext_N (Mk_PTE_Ext (mword_of_int 0 : mword 10))) ('b"1") = false.
  Hypothesis HG0 : eq_vec (_get_PTE_Flags_G (Mk_PTE_Flags (mword_of_int lflags : mword 8))) ('b"1") = false.
  Hypothesis HmisaS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = menvcfg0.
  Hypothesis HPBMTE : eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true.
  Hypothesis Hrange2 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a2) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis Hmatch2 : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a2) 8 = Some region2.
  Hypothesis Hpte2 : (override_PMA (PMA_Region_attributes region2) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis Hc2 : exec (within_clint (Physaddr a2) 8) s = Some (false, s).
  Hypothesis Hsig2 : exec (within_sig (Physaddr a2) 8) s = Some (false, s).
  Hypothesis Hh2 : exec (within_htif_readable (Physaddr a2) 8) s = Some (false, s).
  Hypothesis Hdev2 : dev_addr a2 = false.
  Hypothesis Hbytes2 : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add a2 j) = Some (nth_byte pte2 j).
  Hypothesis Hrange1 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a1) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis Hmatch1 : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a1) 8 = Some region1.
  Hypothesis Hpte1 : (override_PMA (PMA_Region_attributes region1) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis Hc1 : exec (within_clint (Physaddr a1) 8) s = Some (false, s).
  Hypothesis Hsig1 : exec (within_sig (Physaddr a1) 8) s = Some (false, s).
  Hypothesis Hh1 : exec (within_htif_readable (Physaddr a1) 8) s = Some (false, s).
  Hypothesis Hdev1 : dev_addr a1 = false.
  Hypothesis Hbytes1 : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add a1 j) = Some (nth_byte pte1 j).
  Hypothesis Hrange0 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a0) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis Hmatch0 : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a0) 8 = Some region0.
  Hypothesis Hpte0 : (override_PMA (PMA_Region_attributes region0) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis Hc0 : exec (within_clint (Physaddr a0) 8) s = Some (false, s).
  Hypothesis Hsig0 : exec (within_sig (Physaddr a0) 8) s = Some (false, s).
  Hypothesis Hh0 : exec (within_htif_readable (Physaddr a0) 8) s = Some (false, s).
  Hypothesis Hdev0 : dev_addr a0 = false.
  Hypothesis Hbytes0 : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add a0 j) = Some (nth_byte pte0 j).

  (* the leaf never needs an A/D update *)
  Hypothesis Hupd0 : update_PTE_Bits (mk_pte lppn lflags) access = None.

  (* the entry the miss path installs (asid 0, user table's l0). *)
  Definition tramp_tlb_ent : TLB_Entry :=
    tlb4k_entry (mword_of_int 0) vpn lppn (mk_pte lppn lflags) a0.

  Lemma exec_translate_TLB_miss_4k (mxr do_sum : bool) :
    exec (translate_TLB_miss 39 (mword_of_int 0) p2 vpn access Supervisor mxr do_sum tt) s
    = Some (Ok (lppn, PBMT_PMA, tt),
            set_reg s tlb (vec_update_dec (register_lookup tlb s.(sregs))
                             (tlb_hash (__id 39) vpn) (Some tramp_tlb_ent))).
  Proof.
    unfold translate_TLB_miss. cbn zeta.
    match goal with |- context[pt_walk 39 _ _ _ _ _ _ ?l false ?e] =>
      change l with 2 end.
    rewrite (exec_bind_Some _ _ _ _ _
               (exec_pt_walk_tramp3 access mxr do_sum vpn p2 p1 p0 lppn lflags
                  region2 region1 region0 menvcfg0 s
                  Hlf Hinv0 Hnl0 (Hchk0 mxr do_sum) HextN0 HG0 HmisaS HA Hord HR Hmenv HPBMTE
                  Hrange2 Hmatch2 Hpte2 Hc2 Hsig2 Hh2 Hdev2 Hbytes2
                  Hrange1 Hmatch1 Hpte1 Hc1 Hsig1 Hh1 Hdev1 Hbytes1
                  Hrange0 Hmatch0 Hpte0 Hc0 Hsig0 Hh0 Hdev0 Hbytes0)).
    unfold tramp_walk_out. cbn match. cbn zeta.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?p ?ac] =>
        change w with 64 end.
      rewrite !autocast_id.
      rewrite Hupd0.
      cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_add_to_TLB_4k (mword_of_int 0) vpn lppn _ _ s)).
    rewrite exec_returnM.
    unfold tramp_tlb_ent. do 3 f_equal.
  Qed.

  (* HIT on a same-shaped 4K entry (any pteAddr: phase B hits the KERNEL
     table's entry, phase C the user table's own). *)
  Lemma exec_translate_TLB_hit_4k (mxr do_sum : bool) (asid : mword 16) (ptea : mword 64) (idx : Z) :
    exec (translate_TLB_hit 39 asid vpn access Supervisor mxr do_sum tt idx
            (tlb4k_entry (mword_of_int 0) vpn lppn (mk_pte lppn lflags) ptea)) s
    = Some (Ok (lppn, PBMT_PMA, tt), s).
  Proof.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite (tlb_get_pte_4k (mword_of_int 0) vpn lppn (mk_pte lppn lflags) ptea).
    rewrite autocast_id.
    match goal with |- context[Mk_PTE_Flags (@subrange_vec_dec ?w _ 7 0)] =>
      change w with 64 end.
    rewrite (mk_pte_flags lppn lflags Hlf).
    unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
    rewrite (mk_pte_ext lppn lflags ltac:(lia)).
    rewrite (exec_bind_Some _ _ _ _ _ (Hchk0 mxr do_sum s)). cbn match.
    match goal with |- context[update_and_write_pte ?a ?wd ?p ?ac] =>
      assert (Hupd : exec (update_and_write_pte a wd p ac) s = Some (Ok None, s)) end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?p ?ac] =>
        change w with 64 end.
      try rewrite !autocast_id.
      rewrite Hupd0.
      cbn match. apply exec_returnM. }
    rewrite (exec_bind_Some _ _ _ _ _ Hupd). cbn match.
    match goal with |- context[tlb_get_pbmt ?e] =>
      assert (Hpbmt : exec (tlb_get_pbmt e) s = Some (PBMT_PMA, s)) end.
    { unfold tlb_get_pbmt, tlb4k_entry. cbn [TLB_Entry_pte].
      unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
      rewrite (mk_pte_ext lppn lflags ltac:(lia)).
      vm_compute (page_based_mem_type_forwards _). apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ Hpbmt).
    rewrite (tlb_get_ppn_4k (mword_of_int 0) vpn vpn lppn (mk_pte lppn lflags) ptea).
    apply exec_returnm.
  Qed.

  (* combined hit-or-walk translate at asid 0 through base table p2. *)
  Lemma exec_translate_tramp (mxr do_sum : bool) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    register_lookup tlb s.(sregs) = tlbvec ->
    (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
     (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent /\
                  match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) vpn) = false) \/
     (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
                   = Some (tlb4k_entry (mword_of_int 0) vpn lppn (mk_pte lppn lflags) ptea))) ->
    exists s',
      exec (translate 39 (mword_of_int 0 : mword 16) p2 vpn access Supervisor mxr do_sum tt) s
      = Some (Ok (lppn, PBMT_PMA, tt), s')
      /\ (s' = s \/
          s' = set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some tramp_tlb_ent))).
  Proof.
    intros Htlb Hslot.
    unfold translate.
    destruct Hslot as [Hnone | [ (ent & Hent & Hnm) | (ptea & Hhit) ]].
    - eexists. split.
      + rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec s Htlb Hnone)).
        cbn match. rewrite <- Htlb. apply exec_translate_TLB_miss_4k.
      + right. rewrite Htlb. reflexivity.
    - eexists. split.
      + rewrite (exec_bind_Some _ _ _ _ _ (exec_lookup_TLB_nonmatch vpn (mword_of_int 0) tlbvec ent s Htlb Hent Hnm)).
        cbn match. rewrite <- Htlb. apply exec_translate_TLB_miss_4k.
      + right. rewrite Htlb. reflexivity.
    - eexists. split.
      + rewrite (exec_bind_Some _ _ _ _ _
                   (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ s Htlb Hhit
                      (match_tlb4k_self vpn lppn (mk_pte lppn lflags) ptea))).
        cbn match. apply (exec_translate_TLB_hit_4k mxr do_sum (mword_of_int 0) ptea).
      + left. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* translateAddr: front matter differs per access type; the reductions *)
  (* are HYPOTHESES here, discharged by exec_effectivePrivilege_fetch /  *)
  (* _load_S and exec_is_shadow_stack_fetch / _load at instantiation.    *)
  (* ------------------------------------------------------------------ *)
  Context (satp0 : mword 64) (pa : mword 64) (va : mword 64).
  Hypothesis Heff : exec (effectivePrivilege access (register_lookup mstatus s.(sregs)) Supervisor) s = Some (Supervisor, s).
  Hypothesis Hss : exec (is_shadow_stack_access access) s = Some (false, s).
  Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
  Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
  Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
  Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
  Hypothesis Hppn : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = p2.
  Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
  (* va geometry: canonical, its vpn is [vpn], and the OUTPUT page is lppn *)
  Hypothesis Hcanon : neq_vec (bits_of_virtaddr (Virtaddr va))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false.
  Hypothesis Hvpn_def : autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn.
  Hypothesis Hident : zero_extend' 64 (concat_vec lppn
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa.

  Lemma exec_translateAddr_tramp (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
    register_lookup tlb s.(sregs) = tlbvec ->
    (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
     (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent /\
                  match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) vpn) = false) \/
     (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
                   = Some (tlb4k_entry (mword_of_int 0) vpn lppn (mk_pte lppn lflags) ptea))) ->
    exists s',
      exec (translateAddr (Virtaddr va) access) s
      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), s')
      /\ (s' = s \/
          s' = set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn) (Some tramp_tlb_ent))).
  Proof.
    intros Htlb Hslot.
    destruct (exec_translate_tramp
                (eq_vec (_get_Mstatus_MXR (register_lookup mstatus s.(sregs))) ('b"1"))
                (eq_vec (_get_Mstatus_SUM (register_lookup mstatus s.(sregs))) ('b"1"))
                tlbvec Htlb Hslot) as (s' & Htr & Hcase).
    exists s'. split; [| exact Hcase].
    unfold translateAddr.
    rewrite exec_catch_early_return.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg cur_privilege s)).
    rewrite Hcp.
    rewrite (execR_liftR_seq _ _ _ _ _ Heff).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_translationMode_S_sv39 satp0 s HSXL Hsatp Hmode)).
    rewrite (execR_liftR_seq _ _ _ _ _ Hss).
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    rewrite execR_bind. rewrite execR_returnR. cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    rewrite (execR_liftR_seq _ _ _ _ _ Hwidth).
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
        unfold assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hgs).
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true by (vm_compute; reflexivity).
      unfold assert_exp'. cbn match. apply exec_returnm. }
    rewrite (execR_liftR_seq _ _ _ _ _ Hae2).
    rewrite Hcanon. cbn match.
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    rewrite (execR_liftR_seq _ _ _ _ _ (exec_read_reg mstatus s)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace bppn with p2 by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    rewrite (execR_liftR_seq _ _ _ _ _ Htr).
    cbn match.
    rewrite execR_returnR. cbn match.
    match goal with |- context[Physaddr ?e] =>
      replace e with pa by (symmetry; exact Hident) end.
    reflexivity.
  Qed.

End TrampTranslate.

