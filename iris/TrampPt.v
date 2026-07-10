(* TrampPt.v -- the TRAMPOLINE page's page-table structure, for verifying the
   [userret] trampoline (kernel/trampoline.S) that switches from the kernel
   page table to a user-process page table and sret's to user mode.

   Layout facts (xv6, Sv39):
   - TRAMPOLINE  = MAXVA - PGSIZE = 0x3F_FFFF_F000 (vpn 0x3FFFFFF, hash slot 63)
   - TRAPFRAME   = TRAMPOLINE - PGSIZE            (vpn 0x3FFFFFE, hash slot 62)
   - the trampoline page's PHYSICAL home is kernel text: KernelSyms.trampoline
     = 0x80006000 (ppn 0x80006); [userret] sits at +0x9c.
   - BOTH the kernel page table and every user page table map TRAMPOLINE to
     that physical page via a full 3-level walk (root[255] -> l1[511] ->
     l0[511]); a user table additionally maps TRAPFRAME (l0[510]) to the
     process's trapframe page.

   This file provides the PURE / exec-twin layer:
   - [mk_pte] (a PTE with ppn field + low flags) and its field-extraction
     lemmas usable with a SYMBOLIC ppn;
   - the three-level Sv39 page WALK reading the three owned PTEs (stated per
     level over a GENERIC Acc argument, since the nested [_rec_pt_walk]
     call's [_limit_reduces_bool] is opaque);
   - TLB lemmas for the resulting 4K entries: miss / non-matching-entry miss,
     [add_to_TLB] at level 0, hit, and [tlb_get_ppn];
   - [translateAddr] compositions for InstructionFetch and Load Data through
     a 4K mapping where the OUTPUT physical page differs from the va's page;
   - the [SFENCE_VMA] execute reduction (flush_TLB clears every slot) and the
     S-mode [csrw satp] execute reduction (TVM=0).

   As with [pte_super] (SmodeCore), the leaf PTEs are pinned with the A (and,
   for the writable trapframe, D) bits already SET, so the walk never writes
   the PTE back ([update_PTE_Bits] = None): we verify the steady state after
   the hardware's first-use A/D update. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpDecode WpGprCsrwCommon WpGprCsrwB.
Require Import SmodeCore.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. Constants: the two top-of-VA pages and their vpn/slot geometry.     *)
(* ===================================================================== *)

Definition TRAMPOLINE : Z := 0x3FFFFFF000.
Definition TRAPFRAME  : Z := 0x3FFFFFE000.

Definition tramp_vpn : mword 27 := mword_of_int 0x3FFFFFF.
Definition tf_vpn    : mword 27 := mword_of_int 0x3FFFFFE.

(* the trampoline page's physical page number (KernelSyms.trampoline >> 12). *)
Definition tramp_ppn : mword 44 := mword_of_int 0x80006.

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
  Hypothesis Hbytes2 : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add a2 j) = Some (nth_byte pte2 j).

  Hypothesis Hrange1 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a1) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis Hmatch1 : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a1) 8 = Some region1.
  Hypothesis Hpte1 : (override_PMA (PMA_Region_attributes region1) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis Hc1 : exec (within_clint (Physaddr a1) 8) s = Some (false, s).
  Hypothesis Hsig1 : exec (within_sig (Physaddr a1) 8) s = Some (false, s).
  Hypothesis Hh1 : exec (within_htif_readable (Physaddr a1) 8) s = Some (false, s).
  Hypothesis Hbytes1 : forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add a1 j) = Some (nth_byte pte1 j).

  Hypothesis Hrange0 : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
      (uint a0) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis Hmatch0 : matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr a0) 8 = Some region0.
  Hypothesis Hpte0 : (override_PMA (PMA_Region_attributes region0) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis Hc0 : exec (within_clint (Physaddr a0) 8) s = Some (false, s).
  Hypothesis Hsig0 : exec (within_sig (Physaddr a0) 8) s = Some (false, s).
  Hypothesis Hh0 : exec (within_htif_readable (Physaddr a0) 8) s = Some (false, s).
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
                  HA Hord Hrange0 HR Hmatch0 (pte_addr_at_aligned8 p0 idx0) Hpte0 Hc0 Hsig0 Hh0 Hbytes0)).
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
                  HA Hord Hrange1 HR Hmatch1 (pte_addr_at_aligned8 p1 idx1) Hpte1 Hc1 Hsig1 Hh1 Hbytes1)).
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
                  HA Hord Hrange2 HR Hmatch2 (pte_addr_at_aligned8 p2 idx2) Hpte2 Hc2 Hsig2 Hh2 Hbytes2)).
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

