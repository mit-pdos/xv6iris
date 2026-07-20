(* KptPt.v -- the faithful xv6 KERNEL PAGE TABLE (the shape [kvmmake]
   builds, xv6-riscv/kernel/vm.c): a 3-level Sv39 table whose leaves are
   all 4KB pages, providing IDENTITY mappings for
     - the UART   (va = pa = 0x10000000, R|W, one page),
     - the VIRTIO (va = pa = 0x10001000, R|W, one page),
     - the PLIC   (va = pa = [0x0c000000, 0x10000000), R|W, 64 MB), and
     - all of DRAM (va = pa = [0x80000000, 0x90000000) = the model's whole
       RAM window, R|W|X).
   Table PAGES sit at consecutive ppns from the (abstract) root:
     root+0   = the root (level-2) table:   [0] -> l1_dev, [2] -> l1_dram
     root+1   = l1_dev  (level-1, vpn2=0):  [96+k] -> l0_dev k, k in [0,33)
     root+2+k = l0_dev k (level-0):         PLIC leaves (k<32); k=32 holds
                the UART leaf (slot 0) and the VIRTIO leaf (slot 1)
     root+35  = l1_dram (level-1, vpn2=2):  [j] -> l0_dram j, j in [0,128)
     root+36+j = l0_dram j (level-0):       512 identity DRAM leaves each.
   Deliberate DEVIATIONS from kvmmake (kept to avoid touching the spec
   layer above the leaves; see iris/CLAUDE.md):
     - DRAM is uniformly R|W|X (xv6 maps kernel text R|X and data R|W;
       distinguishing them would add an addr-in-text/data premise to every
       fetch/store leaf);
     - leaf A/D bits are PRESET in the default instance (xv6 leaves them
       clear).  §12 below generalizes the whole layer over a per-leaf A/D
       assignment [kpt_adf].  This build is Svadu (menvcfg.ADUE = 1): an
       access needing an A/D update has it written back.  The success
       lemmas require A (and D for stores) on the touched page so that no
       update is needed ([update_PTE_Bits = None]) and the walk therefore
       leaves the state UNCHANGED; without it the write-back would perturb
       the state and the clean success lemma would not hold;
     - table pages are CONSECUTIVE from the root (kalloc's actual boot
       order yields descending pages);
     - the TRAMPOLINE mapping (root[255]) and the per-proc kernel stacks
       are NOT included: the trampoline path stays client-owned
       (TrampPt/TrampTlb, userret layer), and kernel stacks are dynamic.
   This file is IRIS-FREE and in the vanilla-Ltac dialect (like Pt4kWalk);
   the Iris ownership bundle for the PT bytes lives in SmodeCore. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import SmodePte.
Require Import Pt4kWalk.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. Layout.                                                             *)
(* ===================================================================== *)

Definition PTE_RAM : Z := 0xCF.   (* D A - - X W R V *)
Definition PTE_DEV : Z := 0xC7.   (* D A - - - W R V *)

Definition kpt_pages : Z := 164.

Definition kpt_page (root : mword 44) (k : Z) : mword 44 :=
  add_vec root (mword_of_int k).

Definition kpt_l1_dev  (root : mword 44) : mword 44 := kpt_page root 1.
Definition kpt_l0_dev  (root : mword 44) (k : Z) : mword 44 := kpt_page root (2 + k).
Definition kpt_l1_dram (root : mword 44) : mword 44 := kpt_page root 35.
Definition kpt_l0_dram (root : mword 44) (j : Z) : mword 44 := kpt_page root (36 + j).

(* the whole PT region sits inside RAM (and hence far from 2^44 wrap). *)
Definition kpt_ok (root : mword 44) : Prop :=
  ram_base <= bv_unsigned root * 4096 /\
  (bv_unsigned root + kpt_pages) * 4096 <= ram_base + ram_size.

(* ===================================================================== *)
(* 2. Per-vpn geometry: the mapped vpns, their leaf table / flags / PTE.  *)
(* ===================================================================== *)

Definition vpn1_of (vpn : mword 27) : mword 9 := subrange_vec_dec vpn 17 9.
Definition vpn0_of (vpn : mword 27) : mword 9 := subrange_vec_dec vpn 8 0.

Definition kpt_dram_vpn (vpn : mword 27) : Prop := 0x80000 <= bv_unsigned vpn < 0x90000.
Definition kpt_dev_vpn  (vpn : mword 27) : Prop := 0xC000 <= bv_unsigned vpn < 0x10002.
Definition kpt_mapped (vpn : mword 27) : Prop := kpt_dram_vpn vpn \/ kpt_dev_vpn vpn.

Definition kpt_lflags (vpn : mword 27) : Z :=
  if Z.leb 0x80000 (bv_unsigned vpn) then PTE_RAM else PTE_DEV.

(* the level-0 table page holding [vpn]'s leaf *)
Definition kpt_l0_of (root : mword 44) (vpn : mword 27) : mword 44 :=
  if Z.leb 0x80000 (bv_unsigned vpn)
  then kpt_l0_dram root (bv_unsigned (vpn1_of vpn) )
  else kpt_l0_dev root (bv_unsigned (vpn1_of vpn) - 96).

Definition kpt_leaf_ppn (vpn : mword 27) : mword 44 := zero_extend' 44 vpn.
Definition kpt_leaf_pte (vpn : mword 27) : mword 64 :=
  mk_pte (kpt_leaf_ppn vpn) (kpt_lflags vpn).
Definition kpt_slot0_pa (root : mword 44) (vpn : mword 27) : mword 64 :=
  pte_addr_at (kpt_l0_of root vpn) (vpn0_of vpn).

(* the TLB entry the walk of a mapped [vpn] installs *)
Definition kpt_tlb_ent (root : mword 44) (vpn : mword 27) : TLB_Entry :=
  tlb4k_entry (mword_of_int 0) vpn (kpt_leaf_ppn vpn) (kpt_leaf_pte vpn)
    (kpt_slot0_pa root vpn).

(* THE legal-TLB-entry set of the kernel page table (the [P] of
   [tlb_consistent] / [tlb_inv_gen]): any mapped vpn's own 4KB leaf entry. *)
Definition P_kpt (root : mword 44) (e : TLB_Entry) : Prop :=
  exists vpn, kpt_mapped vpn /\ e = kpt_tlb_ent root vpn.

(* ===================================================================== *)
(* 3. vpn subrange arithmetic (27-bit clones of TrampPt's 64-bit facts).  *)
(* ===================================================================== *)

Lemma subrange27_unsigned_26_18 (x : mword 27) :
  bv_unsigned (subrange_vec_dec x 26 18) = (bv_unsigned x ≫ 18) `mod` 2 ^ 9.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 18)) with 18.
  change (MachineWord.MachineWord.Z_idx (26 - 18 + 1)) with 9%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma subrange27_unsigned_17_9 (x : mword 27) :
  bv_unsigned (subrange_vec_dec x 17 9) = (bv_unsigned x ≫ 9) `mod` 2 ^ 9.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 9)) with 9.
  change (MachineWord.MachineWord.Z_idx (17 - 9 + 1)) with 9%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma subrange27_unsigned_8_0 (x : mword 27) :
  bv_unsigned (subrange_vec_dec x 8 0) = bv_unsigned x `mod` 2 ^ 9.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0.
  rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (8 - 0 + 1)) with 9%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma subrange64_unsigned_11_0 (x : mword 64) :
  bv_unsigned (subrange_vec_dec x 11 0) = bv_unsigned x `mod` 2 ^ 12.
Proof.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (MachineWord.MachineWord.Z_idx 0) with 0%N.
  change (Z.of_N 0) with 0.
  rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (11 - 0 + 1)) with 12%N.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.

(* ===================================================================== *)
(* 4. Page / slot address arithmetic and RAM-ness.                        *)
(* ===================================================================== *)

Lemma kpt_page_unsigned (root : mword 44) (k : Z) :
  0 <= k ->
  bv_unsigned root + k < 2 ^ 44 ->
  bv_unsigned (kpt_page root k) = bv_unsigned root + k.
Proof.
  intros Hk Hnw. unfold kpt_page.
  cbv [add_vec Operators_mwords.word_binop Operators_mwords.with_word' to_word
       get_word SailStdpp.Values.with_word].
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
  rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ root) as Hr.
  change (MachineWord.MachineWord.Z_idx 44) with 44%N in *.
  assert (Hkr : bv_wrap 44 k = k).
  { apply bv_wrap_small. unfold bv_modulus.
    change (Z.of_N 44%N) with 44. lia. }
  rewrite Hkr.
  apply bv_wrap_small. unfold bv_modulus.
  change (Z.of_N 44%N) with 44.
  unfold bv_modulus in Hr. change (Z.of_N 44%N) with 44 in Hr. lia.
Qed.

(* a slot of any PT page is (both ends) in RAM *)
Lemma kpt_slot_ram (root : mword 44) (k : Z) (idx : mword 9) :
  kpt_ok root -> 0 <= k < kpt_pages ->
  addr_is_ram (pte_addr_at (kpt_page root k) idx) /\
  addr_is_ram (pa_add (pte_addr_at (kpt_page root k) idx) 7).
Proof.
  intros [Hlo Hhi] Hk. unfold kpt_pages in *.
  assert (Hm44 : bv_modulus (MachineWord.MachineWord.Z_idx 44) = 17592186044416)
    by (vm_compute; reflexivity).
  assert (Hm9 : bv_modulus (MachineWord.MachineWord.Z_idx 9) = 512)
    by (vm_compute; reflexivity).
  pose proof (bv_unsigned_in_range _ root) as Hr. rewrite Hm44 in Hr.
  assert (Hrbound : bv_unsigned root + k < 2 ^ 44)
    by (change (2 ^ 44) with 17592186044416; unfold ram_base, ram_size in *; lia).
  pose proof (kpt_page_unsigned root k ltac:(lia) Hrbound) as Hpg.
  pose proof (pte_addr_at_unsigned (kpt_page root k) idx) as Hslot.
  pose proof (bv_unsigned_in_range _ idx) as Hi. rewrite Hm9 in Hi.
  assert (Hin : ram_base <= bv_unsigned (pte_addr_at (kpt_page root k) idx) /\
                bv_unsigned (pte_addr_at (kpt_page root k) idx) + 8 <= ram_base + ram_size).
  { rewrite Hslot. rewrite Hpg. unfold ram_base, ram_size in *. lia. }
  destruct Hin as [Hin1 Hin2].
  assert (Hnw : bv_unsigned (pte_addr_at (kpt_page root k) idx) + Z.of_nat 7 < 18446744073709551616)
    by (unfold ram_base, ram_size in *; lia).
  split.
  - unfold addr_is_ram. rewrite uint_unsigned. unfold ram_base, ram_size in *. lia.
  - unfold addr_is_ram.
    rewrite uint_pa_add;
      [ rewrite uint_unsigned; unfold ram_base, ram_size in *; change (Z.of_nat 7) with 7; lia
      | rewrite uint_unsigned; exact Hnw ].
Qed.

(* the mapped-DRAM vpn range from an owned RAM address *)
Lemma ram_svpn_range (a : mword 64) :
  addr_is_ram a -> 0x80000 <= bv_unsigned (svpn_of a) < 0x90000.
Proof.
  intros Hram. pose proof Hram as [Hlo Hhi].
  rewrite uint_unsigned in Hlo, Hhi.
  rewrite (svpn_of_unsigned a Hram).
  rewrite uint_unsigned.
  rewrite Z.shiftr_div_pow2 by lia.
  unfold ram_base, ram_size in *.
  change (2 ^ 12) with 4096 in *.
  split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

(* DRAM vpn1 lands in [0,128) *)
Lemma dram_vpn1_range (vpn : mword 27) :
  kpt_dram_vpn vpn -> bv_unsigned (vpn1_of vpn) < 128.
Proof.
  intros [Hlo Hhi]. unfold vpn1_of.
  rewrite subrange27_unsigned_17_9.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 9) with 512 in *.
  assert (Hd : 1024 <= bv_unsigned vpn / 512 < 1152).
  { split.
    - apply Z.div_le_lower_bound; lia.
    - apply Z.div_lt_upper_bound; lia. }
  assert (He : (bv_unsigned vpn / 512) `mod` 512 = bv_unsigned vpn / 512 - 1024).
  { symmetry. apply Zmod_unique with (q := 2); lia. }
  lia.
Qed.

(* the DRAM l1 slot index selects exactly [vpn]'s l0 table *)
Lemma dram_l0_of (root : mword 44) (vpn : mword 27) :
  kpt_dram_vpn vpn ->
  kpt_l0_of root vpn = kpt_l0_dram root (bv_unsigned (vpn1_of vpn)).
Proof.
  intros [Hlo Hhi]. unfold kpt_l0_of.
  rewrite (proj2 (Z.leb_le 0x80000 (bv_unsigned vpn)) Hlo).
  reflexivity.
Qed.

Lemma dram_lflags (vpn : mword 27) :
  kpt_dram_vpn vpn -> kpt_lflags vpn = PTE_RAM.
Proof.
  intros [Hlo Hhi]. unfold kpt_lflags.
  rewrite (proj2 (Z.leb_le 0x80000 (bv_unsigned vpn)) Hlo).
  reflexivity.
Qed.

(* ===================================================================== *)
(* 5. The 4KB identity translation: a mapped va translates to itself.     *)
(* ===================================================================== *)

(* zero_extend' 64 (concat (x:44) (y:12)) as unsigned arithmetic
   (clone of Pt4kWalk's [pte_addr_at_unsigned] with an arbitrary tail) *)
Lemma zext64_concat44_12_unsigned (x : mword 44) (y : mword 12) :
  bv_unsigned (zero_extend' 64 (concat_vec x y) : mword 64)
  = bv_unsigned x * 4096 + bv_unsigned y.
Proof.
  unfold zero_extend', concat_vec.
  cbv [Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.word_binop Operators_mwords.with_word' to_word get_word
       SailStdpp.Values.with_word autocast].
  cbn.
  destruct (Z.eq_dec (Z.of_N (44 + 12)) (44 + 12)) as [e2 | ne]; [| exfalso; exact (ne eq_refl)].
  rewrite (TypeCasts.cast_Z_refl (H := e2)).
  unfold to_word_idx. rewrite !MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.zero_extend, MachineWord.MachineWord.concat, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  erewrite bv_concat_unsigned by (cbn; lia).
  change (Z.of_N (MachineWord.MachineWord.Z_idx 12)) with 12.
  rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (bv_unsigned_in_range _ y) as Hy. unfold bv_modulus in Hy.
  change (MachineWord.MachineWord.Z_idx 12) with 12%N in Hy.
  change (Z.of_N 12%N) with 12 in Hy.
  change (2 ^ 12) with 4096 in Hy.
  replace (bv_unsigned x * 2 ^ 12) with (bv_unsigned x * 4096) by lia.
  apply Z_lor_disjoint_add.
  change 4096 with (2 ^ 12).
  apply Z_land_shift_low; [lia |].
  change (2 ^ 12) with 4096. lia.
Qed.

Lemma zext44_27_unsigned (v : mword 27) :
  bv_unsigned (zero_extend' 44 v : mword 44) = bv_unsigned v.
Proof.
  unfold zero_extend'.
  cbv [Operators_mwords.zero_extend Operators_mwords.extz_vec
       Operators_mwords.with_word' to_word get_word SailStdpp.Values.with_word autocast].
  cbn.
  unfold MachineWord.MachineWord.zero_extend, Values.to_word.
  erewrite bv_zero_extend_unsigned by (cbn; lia).
  reflexivity.
Qed.

(* the identity: a RAM va's leaf-ppn re-concatenated with its page offset
   is the va itself.  (4KB analogue of SmodeCore's [ram_ident].) *)
Lemma ram_ident_4k (a : mword 64) :
  addr_is_ram a ->
  zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a))
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub pagesize_bits 1) 0)) = a.
Proof.
  intros Hram.
  apply bv_eq.
  cbn [bits_of_virtaddr].
  change (Z.sub pagesize_bits 1) with 11.
  rewrite zext64_concat44_12_unsigned.
  unfold kpt_leaf_ppn.
  rewrite zext44_27_unsigned.
  rewrite (svpn_of_unsigned a Hram).
  rewrite subrange64_unsigned_11_0.
  rewrite uint_unsigned.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096.
  pose proof (bv_unsigned_in_range _ a) as Ha.
  pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096) as Hdm.
  lia.
Qed.

(* ===================================================================== *)
(* 6. TLB-entry discrimination: a foreign vpn's 4K entry never matches.   *)
(* ===================================================================== *)

(* (local copy of CommonWalk's [u_sext45_inj]; CommonWalk sits above us) *)
Lemma kpt_sext45_inj (x y : mword 27) :
  sign_extend' (57 - 12) x = sign_extend' (57 - 12) y -> x = y.
Proof.
  intros H.
  apply (f_equal bv_signed) in H.
  cbv [sign_extend' Operators_mwords.sign_extend exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend] in H.
  rewrite !bv_sign_extend_signed in H; [| apply N.leb_le; vm_compute; reflexivity ..].
  apply bv_eq_signed. exact H.
Qed.

Lemma match_tlb4k_other (vpn vpn' : mword 27) (pp : mword 44) (pte ptea : mword 64) :
  vpn' <> vpn ->
  match_TLB_Entry (tlb4k_entry (mword_of_int 0) vpn' pp pte ptea)
    (mword_of_int 0) (sign_extend' (57 - 12) vpn) = false.
Proof.
  intros Hne.
  unfold match_TLB_Entry, tlb4k_entry.
  cbn [TLB_Entry_asid TLB_Entry_global TLB_Entry_vpn TLB_Entry_levelMask].
  match goal with |- context[eq_vec (sign_extend' 45 vpn') ?rhs] =>
    assert (Hm : rhs = sign_extend' (57 - 12) vpn)
      by (apply and45_ones; vm_compute; reflexivity)
  end.
  rewrite Hm.
  match goal with |- (_ && ?b)%bool = false => destruct b eqn:E end.
  - exfalso. apply Hne.
    apply kpt_sext45_inj.
    unfold eq_vec in E. rewrite MachineWord.MachineWord.eqb_true_iff in E. exact E.
  - apply andb_false_r.
Qed.

(* every legal kernel-PT entry either IS this RAM va's own entry or fails
   to match its tag *)
Lemma P_kpt_disc (root : mword 44) (a : mword 64) (e : TLB_Entry) :
  addr_is_ram a ->
  P_kpt root e ->
  e = kpt_tlb_ent root (svpn_of a) \/
  match_TLB_Entry e (mword_of_int 0) (sign_extend' (57 - 12) (svpn_of a)) = false.
Proof.
  intros Hram (vpn & Hm & ->).
  destruct (decide (vpn = svpn_of a)) as [-> | Hne].
  - left. reflexivity.
  - right. unfold kpt_tlb_ent. apply match_tlb4k_other. exact Hne.
Qed.

(* every RAM va's own entry is legal *)
Lemma P_kpt_ram (root : mword 44) (a : mword 64) :
  addr_is_ram a -> P_kpt root (kpt_tlb_ent root (svpn_of a)).
Proof.
  intros Hram. exists (svpn_of a). split; [| reflexivity].
  left. exact (ram_svpn_range a Hram).
Qed.

(* ===================================================================== *)
(* 7. Flag-byte facts for the two leaf kinds (A/D preset).                *)
(* ===================================================================== *)

(* A/D preset => the walk never needs a PTE write-back, for ANY access *)
Lemma update_PTE_Bits_mk_pte_AD (p : mword 44) (f : Z)
    (access : MemoryAccessType mem_payload) :
  0 <= f < 256 ->
  eq_vec (_get_PTE_Flags_D (Mk_PTE_Flags (mword_of_int f : mword 8))) ('b"0") = false ->
  eq_vec (_get_PTE_Flags_A (Mk_PTE_Flags (mword_of_int f : mword 8))) ('b"0") = false ->
  update_PTE_Bits (mk_pte p f) access = None.
Proof.
  intros Hf HD HA.
  unfold update_PTE_Bits.
  rewrite (mk_pte_flags p f Hf).
  cbn zeta.
  rewrite HD, HA.
  cbn [andb orb]. reflexivity.
Qed.

Lemma update_PTE_Bits_kpt_ram (p : mword 44) (access : MemoryAccessType mem_payload) :
  update_PTE_Bits (mk_pte p PTE_RAM) access = None.
Proof.
  apply update_PTE_Bits_mk_pte_AD;
    [ unfold PTE_RAM; lia | vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.

Lemma update_PTE_Bits_kpt_dev (p : mword 44) (access : MemoryAccessType mem_payload) :
  update_PTE_Bits (mk_pte p PTE_DEV) access = None.
Proof.
  apply update_PTE_Bits_mk_pte_AD;
    [ unfold PTE_DEV; lia | vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.

(* ===================================================================== *)
(* 8. The PT's memory image, as a pure predicate over an [mstate]'s mem.  *)
(*    (The Iris bundle in SmodeCore produces this once per step; every    *)
(*    walk consumes it.)                                                  *)
(* ===================================================================== *)

Definition kpt_slot_in (s : mstate) (a : mword 64) (w : mword 64) : Prop :=
  forall j : nat, (N.of_nat j < 8)%N -> s.(mem) !! (pa_add a j) = Some (nth_byte w j).

Definition kpt_mem (s : mstate) (root : mword 44) : Prop :=
  kpt_slot_in s (pte_addr_at root (mword_of_int 0)) (mk_pte (kpt_l1_dev root) PTE_PTR)
  /\ kpt_slot_in s (pte_addr_at root (mword_of_int 2)) (mk_pte (kpt_l1_dram root) PTE_PTR)
  /\ (forall i : mword 9, 96 <= bv_unsigned i < 129 ->
        kpt_slot_in s (pte_addr_at (kpt_l1_dev root) i)
          (mk_pte (kpt_l0_dev root (bv_unsigned i - 96)) PTE_PTR))
  /\ (forall i : mword 9, bv_unsigned i < 128 ->
        kpt_slot_in s (pte_addr_at (kpt_l1_dram root) i)
          (mk_pte (kpt_l0_dram root (bv_unsigned i)) PTE_PTR))
  /\ (forall vpn : mword 27, kpt_mapped vpn ->
        kpt_slot_in s (kpt_slot0_pa root vpn) (kpt_leaf_pte vpn)).


(* mword_of_int round-trips on the unsigned value (9- and 27-bit). *)
Lemma mword_of_int_unsigned_9 (x : mword 9) : mword_of_int (bv_unsigned x) = x.
Proof.
  apply bv_eq.
  cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
  rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma mword_of_int_unsigned_27 (x : mword 27) : mword_of_int (bv_unsigned x) = x.
Proof.
  apply bv_eq.
  cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
  rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* ===================================================================== *)
(* 9. Concrete-flag reductions for the DRAM leaf (PTE_RAM = 0xCF).        *)
(* ===================================================================== *)

Lemma kpt_ram_inv_red : forall s',
  exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int PTE_RAM)) (Mk_PTE_Ext (mword_of_int 0))) s'
  = Some (false, s').
Proof. intro s'. vm_compute; reflexivity. Qed.

Lemma kpt_ram_nonleaf_red :
  pte_is_non_leaf (Mk_PTE_Flags (mword_of_int PTE_RAM : mword 8)) = false.
Proof. vm_compute; reflexivity. Qed.

Lemma kpt_ram_G_red :
  eq_vec (_get_PTE_Flags_G (Mk_PTE_Flags (mword_of_int PTE_RAM : mword 8))) ('b"1") = false.
Proof. vm_compute; reflexivity. Qed.

Lemma kpt_extN_red :
  eq_vec (_get_PTE_Ext_N (Mk_PTE_Ext (mword_of_int 0 : mword 10))) ('b"1") = false.
Proof. vm_compute; reflexivity. Qed.

(* check_PTE_permission at the R|W|X U=0 leaf succeeds in S-mode for all
   three access kinds, any mxr / do_sum *)
Lemma kpt_ram_check_fetch : forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int PTE_RAM)) (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof. intros mxr do_sum s'. destruct mxr, do_sum; vm_compute; reflexivity. Qed.

Lemma kpt_ram_check_load : forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (Load Data) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int PTE_RAM)) (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof. intros mxr do_sum s'. destruct mxr, do_sum; vm_compute; reflexivity. Qed.

Lemma kpt_ram_check_store : forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (Store Data) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int PTE_RAM)) (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof. intros mxr do_sum s'. destruct mxr, do_sum; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* 10. PMA / PMP per-slot facts.                                          *)
(* ===================================================================== *)

(* the concrete boot PMA table lets every 8-byte aligned RAM read serve as
   a PTE read.  (Same fact WpSmodeUart / UptInv thread; they can alias.)  *)
Definition pma_allows_pte_read (regions : list PMA_Region) : Prop :=
  forall (a : mword 64), exists r,
    matching_pma_region regions (Physaddr a) 8 = Some r /\
    (override_PMA (PMA_Region_attributes r) PBMT_PMA).(PMA_supports_pte_read) = true.

(* the 8-byte PTE read at a RAM address matches the kernel's TOR entry 0 *)
Lemma ram_pte_pmp8 (a pmpaddr0 : mword 64) :
  addr_is_ram a -> addr_is_ram (pa_add a 7) ->
  ram_base + ram_size <= uint pmpaddr0 * 4 ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint pmpaddr0) 4)
    (uint a) (uint (to_bits 64 8)) = PMP_Match.
Proof.
  intros Hram Hram7 Hcov.
  assert (Hlo : (ram_base <= uint a)%Z) by (destruct Hram as [Hl _]; exact Hl).
  assert (Hfit : (uint a + 8 <= ram_base + ram_size)%Z).
  { assert (Hnw : (uint a + Z.of_nat 7 < 18446744073709551616)%Z).
    { destruct Hram as [_ Hh]. unfold ram_base, ram_size in Hh. change (Z.of_nat 7) with 7. lia. }
    pose proof (uint_pa_add a 7 Hnw) as Heq.
    destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7. change (Z.of_nat 7) with 7 in Hhi7.
    unfold ram_base, ram_size in *. lia. }
  exact (ram_pmp_match_w a pmpaddr0 8 ltac:(lia) ltac:(vm_compute; reflexivity) Hlo Hfit Hcov).
Qed.

(* the root page is page 0 *)
Lemma kpt_page_0 (root : mword 44) : kpt_page root 0 = root.
Proof.
  unfold kpt_page. apply bv_eq.
  cbv [add_vec Operators_mwords.word_binop Operators_mwords.with_word' to_word
       get_word SailStdpp.Values.with_word].
  unfold MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  cbv [mword_of_int Values.mword_of_int MachineWord.MachineWord.Z_to_word].
  rewrite Z_to_bv_unsigned.
  assert (H0 : bv_wrap (MachineWord.MachineWord.Z_idx 44) 0 = 0) by (vm_compute; reflexivity).
  rewrite H0. rewrite Z.add_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* ===================================================================== *)
(* 11. THE RAM-va translate: the kernel PT's three-way 4KB translateAddr  *)
(*     for ANY in-RAM virtual address (access-generic).  Instantiates     *)
(*     Pt4kWalk's [exec_translateAddr_tramp] with the kernel PT's tables  *)
(*     and derives every per-slot fact from [kpt_ok]/[kpt_mem].           *)
(* ===================================================================== *)

Section KptRamTranslate.
Context (access : MemoryAccessType mem_payload).
Context (root : mword 44).
Context (menvcfg0 satp0 va : mword 64).
Context (s : mstate).

Local Notation vpn := (svpn_of va).
Local Notation pmpaddr0 := (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0).

Hypothesis Hok : kpt_ok root.
Hypothesis Hmem : kpt_mem s root.
Hypothesis Hram : addr_is_ram va.
(* access front matter *)
Hypothesis Heff : exec (effectivePrivilege access (register_lookup mstatus s.(sregs)) Supervisor) s = Some (Supervisor, s).
Hypothesis Hss : exec (is_shadow_stack_access access) s = Some (false, s).
Hypothesis Hchk0 : forall (mxr do_sum : bool) s', exec (check_PTE_permission access Supervisor mxr do_sum (Mk_PTE_Flags (mword_of_int PTE_RAM)) (Mk_PTE_Ext (mword_of_int 0)) tt) s' = Some (PTE_Check_Success tt, s').
(* ambient config *)
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hppn : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root.
Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
Hypothesis HmisaS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = menvcfg0.
Hypothesis HPBMTE : eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true.
Hypothesis Hhtif : register_lookup htif_tohost_base s.(sregs) = None.
(* PMP TOR entry 0 covers RAM *)
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) pmpaddr0 = false.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
Hypothesis Hcov : ram_base + ram_size <= uint pmpaddr0 * 4.
Hypothesis Hpma : pma_allows_pte_read (register_lookup pma_regions s.(sregs)).

Lemma exec_translateAddr_kpt_ram (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  register_lookup tlb s.(sregs) = tlbvec ->
  (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
   (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent /\
                match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) vpn) = false) \/
   (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
                 = Some (tlb4k_entry (mword_of_int 0) vpn (kpt_leaf_ppn vpn)
                           (mk_pte (kpt_leaf_ppn vpn) PTE_RAM) ptea))) ->
  exists s',
    exec (translateAddr (Virtaddr va) access) s
    = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s')
    /\ (s' = s \/
        s' = set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                              (Some (kpt_tlb_ent root vpn)))).
Proof.
  intros Htlb Hslot.
  pose proof (ram_svpn_range va Hram) as Hvr.
  assert (Hdram : kpt_dram_vpn vpn) by (exact Hvr).
  pose proof (dram_vpn1_range vpn Hdram) as Hv1.
  (* the three table pages *)
  set (p1 := kpt_l1_dram root).
  set (p0 := kpt_l0_of root vpn).
  set (lppn := kpt_leaf_ppn vpn).
  (* per-slot byte-presence, at the walk's slot addresses *)
  destruct Hmem as (Hmr0 & Hmr2 & Hmdev & Hml1 & Hml0).
  assert (Hb2 : forall j : nat, (N.of_nat j < 8)%N ->
            s.(mem) !! (pa_add (pte_addr_at root (subrange_vec_dec vpn 26 18)) j)
            = Some (nth_byte (mk_pte p1 PTE_PTR) j)).
  { rewrite (ram_svpn2 va Hram). exact Hmr2. }
  assert (Hb1 : forall j : nat, (N.of_nat j < 8)%N ->
            s.(mem) !! (pa_add (pte_addr_at p1 (subrange_vec_dec vpn 17 9)) j)
            = Some (nth_byte (mk_pte p0 PTE_PTR) j)).
  { unfold p0. rewrite (dram_l0_of root vpn Hdram).
    exact (Hml1 (subrange_vec_dec vpn 17 9) Hv1). }
  assert (Hb0 : forall j : nat, (N.of_nat j < 8)%N ->
            s.(mem) !! (pa_add (pte_addr_at p0 (subrange_vec_dec vpn 8 0)) j)
            = Some (nth_byte (mk_pte lppn PTE_RAM) j)).
  { pose proof (Hml0 vpn (or_introl Hdram)) as H0.
    unfold kpt_slot0_pa, vpn0_of in H0.
    unfold kpt_leaf_pte in H0. rewrite (dram_lflags vpn Hdram) in H0.
    exact H0. }
  (* per-slot RAM-ness *)
  assert (Hram2 : addr_is_ram (pte_addr_at root (subrange_vec_dec vpn 26 18)) /\
                  addr_is_ram (pa_add (pte_addr_at root (subrange_vec_dec vpn 26 18)) 7)).
  { rewrite <- (kpt_page_0 root) at 1 2.
    apply (kpt_slot_ram root 0); [exact Hok | unfold kpt_pages; lia]. }
  assert (Hram1 : addr_is_ram (pte_addr_at p1 (subrange_vec_dec vpn 17 9)) /\
                  addr_is_ram (pa_add (pte_addr_at p1 (subrange_vec_dec vpn 17 9)) 7)).
  { apply (kpt_slot_ram root 35); [exact Hok | unfold kpt_pages; lia]. }
  assert (Hram0 : addr_is_ram (pte_addr_at p0 (subrange_vec_dec vpn 8 0)) /\
                  addr_is_ram (pa_add (pte_addr_at p0 (subrange_vec_dec vpn 8 0)) 7)).
  { unfold p0. rewrite (dram_l0_of root vpn Hdram). unfold kpt_l0_dram.
    apply (kpt_slot_ram root (36 + bv_unsigned (vpn1_of vpn)));
      [exact Hok | ].
    pose proof (bv_unsigned_in_range _ (vpn1_of vpn)) as Hnn.
    unfold kpt_pages. lia. }
  destruct Hram2 as [Hram2 Hram2']. destruct Hram1 as [Hram1 Hram1']. destruct Hram0 as [Hram0 Hram0'].
  (* per-slot PMP range matches *)
  pose proof (ram_pte_pmp8 _ pmpaddr0 Hram2 Hram2' Hcov) as Hrange2.
  pose proof (ram_pte_pmp8 _ pmpaddr0 Hram1 Hram1' Hcov) as Hrange1.
  pose proof (ram_pte_pmp8 _ pmpaddr0 Hram0 Hram0' Hcov) as Hrange0.
  (* per-slot PMA regions *)
  destruct (Hpma (pte_addr_at root (subrange_vec_dec vpn 26 18))) as (region2 & Hmatch2 & Hpte2).
  destruct (Hpma (pte_addr_at p1 (subrange_vec_dec vpn 17 9))) as (region1 & Hmatch1 & Hpte1).
  destruct (Hpma (pte_addr_at p0 (subrange_vec_dec vpn 8 0))) as (region0 & Hmatch0 & Hpte0).
  (* per-slot MMIO / device disjointness *)
  pose proof (within_clint_false _ 8 s (addr_is_ram_not_in_clint _ Hram2) ltac:(lia)) as Hc2.
  pose proof (within_clint_false _ 8 s (addr_is_ram_not_in_clint _ Hram1) ltac:(lia)) as Hc1.
  pose proof (within_clint_false _ 8 s (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hc0.
  pose proof (within_sig_false _ 8 s (addr_is_ram_not_in_sig _ Hram2) ltac:(lia)) as Hsig2.
  pose proof (within_sig_false _ 8 s (addr_is_ram_not_in_sig _ Hram1) ltac:(lia)) as Hsig1.
  pose proof (within_sig_false _ 8 s (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hsig0.
  pose proof (within_htif_false (pte_addr_at root (subrange_vec_dec vpn 26 18)) 8 s Hhtif) as Hh2.
  pose proof (within_htif_false (pte_addr_at p1 (subrange_vec_dec vpn 17 9)) 8 s Hhtif) as Hh1.
  pose proof (within_htif_false (pte_addr_at p0 (subrange_vec_dec vpn 8 0)) 8 s Hhtif) as Hh0.
  pose proof (addr_is_ram_not_dev _ Hram2) as Hdev2.
  pose proof (addr_is_ram_not_dev _ Hram1) as Hdev1.
  pose proof (addr_is_ram_not_dev _ Hram0) as Hdev0.
  destruct (exec_translateAddr_tramp access vpn root p1 p0 lppn PTE_RAM
              region2 region1 region0 menvcfg0 s
              ltac:(unfold PTE_RAM; lia) kpt_ram_inv_red kpt_ram_nonleaf_red Hchk0
              kpt_extN_red kpt_ram_G_red HmisaS HA Hord HR Hmenv HPBMTE
              Hrange2 Hmatch2 Hpte2 Hc2 Hsig2 Hh2 Hdev2 Hb2
              Hrange1 Hmatch1 Hpte1 Hc1 Hsig1 Hh1 Hdev1 Hb1
              Hrange0 Hmatch0 Hpte0 Hc0 Hsig0 Hh0 Hdev0 Hb0
              (update_PTE_Bits_kpt_ram lppn access)
              satp0 va va
              Heff Hss Hcp HSXL Hsatp Hmode Hppn Hasid
              (ram_canonical va Hram) eq_refl (ram_ident_4k va Hram)
              tlbvec Htlb Hslot)
    as (s' & Htr & Hcase).
  exists s'. split; [exact Htr|].
  destruct Hcase as [-> | ->].
  - left. reflexivity.
  - right.
    unfold tramp_tlb_ent, kpt_tlb_ent, kpt_leaf_pte, kpt_slot0_pa, vpn0_of.
    rewrite (dram_lflags vpn Hdram).
    unfold p0, lppn. reflexivity.
Qed.

End KptRamTranslate.

(* transport [kpt_mem] across a memory-preserving state change *)
Lemma kpt_mem_eq (s s' : mstate) (root : mword 44) :
  s'.(mem) = s.(mem) -> kpt_mem s root -> kpt_mem s' root.
Proof.
  intros Hm (H0 & H2 & Hdev & Hl1 & Hl0).
  unfold kpt_mem, kpt_slot_in in *.
  rewrite Hm.
  repeat split; assumption.
Qed.

(* ===================================================================== *)
(* 12. ARBITRARY A/D BITS.  The layer above fixes every leaf's A/D bits   *)
(* to 1 (the [kpt_adf1] instance below).  Here the kernel PT is           *)
(* generalized over a PER-LEAF A/D assignment [adf : mword 27 -> bool *   *)
(* bool] ((A, D) per vpn), so the faithful kvmmake initial state (A/D     *)
(* CLEAR) is representable.  Model-imposed side conditions (this build    *)
(* runs Svadu semantics, menvcfg.ADUE = 1, so the walk WRITES A/D back    *)
(* on an access that needs them): an access through an A=0 leaf -- or a   *)
(* store through a D=0 leaf -- would perturb the PTE, so the clean        *)
(* no-state-change success lemmas require A=1 (and D=1 for stores); D     *)
(* stays ARBITRARY on pages that are only fetched/loaded.                 *)
(* ===================================================================== *)

Definition kpt_adf : Type := mword 27 -> bool * bool.
Definition kpt_adf1 : kpt_adf := fun _ => (true, true).

(* flag byte: base perms (V|R|W[|X]) + A (bit 6) + D (bit 7) *)
Definition kpt_ad_bits (ad : bool * bool) : Z :=
  (if fst ad then 64 else 0) + (if snd ad then 128 else 0).
Definition PTE_RAM_ad (ad : bool * bool) : Z := 0x0F + kpt_ad_bits ad.
Definition PTE_DEV_ad (ad : bool * bool) : Z := 0x07 + kpt_ad_bits ad.

Definition kpt_lflags_ad (adf : kpt_adf) (vpn : mword 27) : Z :=
  if Z.leb 0x80000 (bv_unsigned vpn) then PTE_RAM_ad (adf vpn) else PTE_DEV_ad (adf vpn).

Definition kpt_leaf_pte_ad (adf : kpt_adf) (vpn : mword 27) : mword 64 :=
  mk_pte (kpt_leaf_ppn vpn) (kpt_lflags_ad adf vpn).

Definition kpt_tlb_ent_ad (adf : kpt_adf) (root : mword 44) (vpn : mword 27) : TLB_Entry :=
  tlb4k_entry (mword_of_int 0) vpn (kpt_leaf_ppn vpn) (kpt_leaf_pte_ad adf vpn)
    (kpt_slot0_pa root vpn).

Definition P_kpt_ad (adf : kpt_adf) (root : mword 44) (e : TLB_Entry) : Prop :=
  exists vpn, kpt_mapped vpn /\ e = kpt_tlb_ent_ad adf root vpn.

Definition kpt_mem_ad (adf : kpt_adf) (s : mstate) (root : mword 44) : Prop :=
  kpt_slot_in s (pte_addr_at root (mword_of_int 0)) (mk_pte (kpt_l1_dev root) PTE_PTR)
  /\ kpt_slot_in s (pte_addr_at root (mword_of_int 2)) (mk_pte (kpt_l1_dram root) PTE_PTR)
  /\ (forall i : mword 9, 96 <= bv_unsigned i < 129 ->
        kpt_slot_in s (pte_addr_at (kpt_l1_dev root) i)
          (mk_pte (kpt_l0_dev root (bv_unsigned i - 96)) PTE_PTR))
  /\ (forall i : mword 9, bv_unsigned i < 128 ->
        kpt_slot_in s (pte_addr_at (kpt_l1_dram root) i)
          (mk_pte (kpt_l0_dram root (bv_unsigned i)) PTE_PTR))
  /\ (forall vpn : mword 27, kpt_mapped vpn ->
        kpt_slot_in s (kpt_slot0_pa root vpn) (kpt_leaf_pte_ad adf vpn)).

(* ---- preset bridges: the A/D=1 instance is the fixed-flag layer ---- *)

Lemma kpt_lflags_adf1 (vpn : mword 27) : kpt_lflags_ad kpt_adf1 vpn = kpt_lflags vpn.
Proof.
  unfold kpt_lflags_ad, kpt_lflags, PTE_RAM_ad, PTE_DEV_ad, kpt_adf1, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn)); reflexivity.
Qed.

Lemma kpt_leaf_pte_adf1 (vpn : mword 27) : kpt_leaf_pte_ad kpt_adf1 vpn = kpt_leaf_pte vpn.
Proof. unfold kpt_leaf_pte_ad, kpt_leaf_pte. rewrite kpt_lflags_adf1. reflexivity. Qed.

Lemma kpt_tlb_ent_adf1 (root : mword 44) (vpn : mword 27) :
  kpt_tlb_ent_ad kpt_adf1 root vpn = kpt_tlb_ent root vpn.
Proof. unfold kpt_tlb_ent_ad, kpt_tlb_ent. rewrite kpt_leaf_pte_adf1. reflexivity. Qed.

Lemma P_kpt_adf1 (root : mword 44) (e : TLB_Entry) :
  P_kpt_ad kpt_adf1 root e <-> P_kpt root e.
Proof.
  split; intros (vpn & Hm & ->); exists vpn; (split; [exact Hm|]).
  - apply kpt_tlb_ent_adf1.
  - symmetry; apply kpt_tlb_ent_adf1.
Qed.

Lemma kpt_mem_adf1 (s : mstate) (root : mword 44) :
  kpt_mem_ad kpt_adf1 s root <-> kpt_mem s root.
Proof.
  unfold kpt_mem_ad, kpt_mem.
  split; intros (H0 & H2 & Hdev & Hl1 & Hl0);
    refine (conj H0 (conj H2 (conj Hdev (conj Hl1 _))));
    intros vpn Hv; specialize (Hl0 vpn Hv).
  - rewrite (kpt_leaf_pte_adf1 vpn) in Hl0. exact Hl0.
  - rewrite (kpt_leaf_pte_adf1 vpn). exact Hl0.
Qed.

(* ---- parametric flag-byte facts (any A/D) ---- *)

Lemma kpt_lflags_ad_bound (adf : kpt_adf) (vpn : mword 27) :
  0 <= kpt_lflags_ad adf vpn < 256.
Proof.
  unfold kpt_lflags_ad, PTE_RAM_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    destruct (adf vpn) as [a d]; destruct a, d; cbn; lia.
Qed.

Lemma kpt_inv_red_ad (adf : kpt_adf) (vpn : mword 27) : forall s',
  exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn)))
          (Mk_PTE_Ext (mword_of_int 0))) s'
  = Some (false, s').
Proof.
  intro s'.
  unfold kpt_lflags_ad, PTE_RAM_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    destruct (adf vpn) as [a d]; destruct a, d; vm_compute; reflexivity.
Qed.

Lemma kpt_nonleaf_red_ad (adf : kpt_adf) (vpn : mword 27) :
  pte_is_non_leaf (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn) : mword 8)) = false.
Proof.
  unfold kpt_lflags_ad, PTE_RAM_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    destruct (adf vpn) as [a d]; destruct a, d; vm_compute; reflexivity.
Qed.

Lemma kpt_G_red_ad (adf : kpt_adf) (vpn : mword 27) :
  eq_vec (_get_PTE_Flags_G (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn) : mword 8)))
    ('b"1") = false.
Proof.
  unfold kpt_lflags_ad, PTE_RAM_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    destruct (adf vpn) as [a d]; destruct a, d; vm_compute; reflexivity.
Qed.

(* permission checks ignore A/D: fetch needs the DRAM (X) base; loads and
   stores pass on both bases *)
Lemma kpt_check_fetch_ad (adf : kpt_adf) (vpn : mword 27) :
  kpt_dram_vpn vpn ->
  forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros [Hlo _] mxr do_sum s'.
  unfold kpt_lflags_ad, PTE_RAM_ad, kpt_ad_bits.
  rewrite (proj2 (Z.leb_le 0x80000 (bv_unsigned vpn)) Hlo).
  destruct (adf vpn) as [a d]; destruct a, d, mxr, do_sum; vm_compute; reflexivity.
Qed.

Lemma kpt_check_load_ad (adf : kpt_adf) (vpn : mword 27) :
  forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (Load Data) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros mxr do_sum s'.
  unfold kpt_lflags_ad, PTE_RAM_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    destruct (adf vpn) as [a d]; destruct a, d, mxr, do_sum; vm_compute; reflexivity.
Qed.

Lemma kpt_check_store_ad (adf : kpt_adf) (vpn : mword 27) :
  forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (Store Data) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros mxr do_sum s'.
  unfold kpt_lflags_ad, PTE_RAM_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    destruct (adf vpn) as [a d]; destruct a, d, mxr, do_sum; vm_compute; reflexivity.
Qed.

(* A/D update conditions: A=1 suffices for non-writing accesses (D free);
   stores additionally need D=1. *)
Lemma update_PTE_Bits_mk_pte_fetch (p : mword 44) (f : Z) :
  0 <= f < 256 ->
  eq_vec (_get_PTE_Flags_A (Mk_PTE_Flags (mword_of_int f : mword 8))) ('b"0") = false ->
  update_PTE_Bits (mk_pte p f) (InstructionFetch tt) = None.
Proof.
  intros Hf HA.
  unfold update_PTE_Bits.
  rewrite (mk_pte_flags p f Hf).
  cbn zeta.
  rewrite HA.
  rewrite andb_false_r. cbn [andb orb]. reflexivity.
Qed.

Lemma update_PTE_Bits_mk_pte_load (p : mword 44) (f : Z) :
  0 <= f < 256 ->
  eq_vec (_get_PTE_Flags_A (Mk_PTE_Flags (mword_of_int f : mword 8))) ('b"0") = false ->
  update_PTE_Bits (mk_pte p f) (Load Data) = None.
Proof.
  intros Hf HA.
  unfold update_PTE_Bits.
  rewrite (mk_pte_flags p f Hf).
  cbn zeta.
  rewrite HA.
  rewrite andb_false_r. cbn [andb orb]. reflexivity.
Qed.

Lemma kpt_A_red_ad (adf : kpt_adf) (vpn : mword 27) :
  fst (adf vpn) = true ->
  eq_vec (_get_PTE_Flags_A (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn) : mword 8))) ('b"0") = false.
Proof.
  intro Ha.
  unfold kpt_lflags_ad, PTE_RAM_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    destruct (adf vpn) as [a d]; cbn in Ha; subst a; destruct d; vm_compute; reflexivity.
Qed.

Lemma kpt_D_red_ad (adf : kpt_adf) (vpn : mword 27) :
  snd (adf vpn) = true ->
  eq_vec (_get_PTE_Flags_D (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn) : mword 8))) ('b"0") = false.
Proof.
  intro Hd.
  unfold kpt_lflags_ad, PTE_RAM_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    destruct (adf vpn) as [a d]; cbn in Hd; subst d; destruct a; vm_compute; reflexivity.
Qed.

Lemma kpt_upd_fetch_ad (adf : kpt_adf) (vpn : mword 27) (p : mword 44) :
  fst (adf vpn) = true ->
  update_PTE_Bits (mk_pte p (kpt_lflags_ad adf vpn)) (InstructionFetch tt) = None.
Proof.
  intro Ha.
  apply update_PTE_Bits_mk_pte_fetch;
    [ apply kpt_lflags_ad_bound | apply kpt_A_red_ad; exact Ha ].
Qed.

Lemma kpt_upd_load_ad (adf : kpt_adf) (vpn : mword 27) (p : mword 44) :
  fst (adf vpn) = true ->
  update_PTE_Bits (mk_pte p (kpt_lflags_ad adf vpn)) (Load Data) = None.
Proof.
  intro Ha.
  apply update_PTE_Bits_mk_pte_load;
    [ apply kpt_lflags_ad_bound | apply kpt_A_red_ad; exact Ha ].
Qed.

Lemma kpt_upd_store_ad (adf : kpt_adf) (vpn : mword 27) (p : mword 44) :
  fst (adf vpn) = true ->
  snd (adf vpn) = true ->
  update_PTE_Bits (mk_pte p (kpt_lflags_ad adf vpn)) (Store Data) = None.
Proof.
  intros Ha Hd.
  apply update_PTE_Bits_mk_pte_AD;
    [ apply kpt_lflags_ad_bound
    | apply kpt_D_red_ad; exact Hd
    | apply kpt_A_red_ad; exact Ha ].
Qed.

(* ---- generalized discrimination / slot facts ---- *)

Lemma P_kpt_ad_disc (adf : kpt_adf) (root : mword 44) (a : mword 64) (e : TLB_Entry) :
  addr_is_ram a ->
  P_kpt_ad adf root e ->
  e = kpt_tlb_ent_ad adf root (svpn_of a) \/
  match_TLB_Entry e (mword_of_int 0) (sign_extend' (57 - 12) (svpn_of a)) = false.
Proof.
  intros Hram (vpn & Hm & ->).
  destruct (decide (vpn = svpn_of a)) as [-> | Hne].
  - left. reflexivity.
  - right. unfold kpt_tlb_ent_ad. apply match_tlb4k_other. exact Hne.
Qed.

Lemma P_kpt_ad_ram (adf : kpt_adf) (root : mword 44) (a : mword 64) :
  addr_is_ram a -> P_kpt_ad adf root (kpt_tlb_ent_ad adf root (svpn_of a)).
Proof.
  intros Hram. exists (svpn_of a). split; [| reflexivity].
  left. exact (ram_svpn_range a Hram).
Qed.

(* ===================================================================== *)
(* 13. THE arbitrary-A/D RAM-va translate: [exec_translateAddr_kpt_ram]   *)
(*     generalized over the leaf A/D assignment.  The permission check    *)
(*     and the A/D-update condition (A=1; D=1 for writing accesses) are   *)
(*     HYPOTHESES, dischargeable via [kpt_check_*_ad] / [kpt_upd_*_ad].   *)
(* ===================================================================== *)

Section KptRamTranslateAD.
Context (adf : kpt_adf).
Context (access : MemoryAccessType mem_payload).
Context (root : mword 44).
Context (menvcfg0 satp0 va : mword 64).
Context (s : mstate).

Local Notation vpn := (svpn_of va).
Local Notation pmpaddr0 := (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0).

Hypothesis Hok : kpt_ok root.
Hypothesis Hmem : kpt_mem_ad adf s root.
Hypothesis Hram : addr_is_ram va.
(* access front matter *)
Hypothesis Heff : exec (effectivePrivilege access (register_lookup mstatus s.(sregs)) Supervisor) s = Some (Supervisor, s).
Hypothesis Hss : exec (is_shadow_stack_access access) s = Some (false, s).
Hypothesis Hchk0 : forall (mxr do_sum : bool) s', exec (check_PTE_permission access Supervisor mxr do_sum (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn))) (Mk_PTE_Ext (mword_of_int 0)) tt) s' = Some (PTE_Check_Success tt, s').
(* the A/D-update side condition (A=1; also D=1 for writing accesses) *)
Hypothesis Hupd0 : update_PTE_Bits (mk_pte (kpt_leaf_ppn vpn) (kpt_lflags_ad adf vpn)) access = None.
(* ambient config *)
Hypothesis Hcp : register_lookup cur_privilege s.(sregs) = Supervisor.
Hypothesis HSXL : _get_Mstatus_SXL (register_lookup mstatus s.(sregs)) = 'b"10".
Hypothesis Hsatp : register_lookup satp s.(sregs) = satp0.
Hypothesis Hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4).
Hypothesis Hppn : autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root.
Hypothesis Hasid : zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16).
Hypothesis HmisaS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
Hypothesis Hmenv : register_lookup menvcfg s.(sregs) = menvcfg0.
Hypothesis HPBMTE : eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true.
Hypothesis Hhtif : register_lookup htif_tohost_base s.(sregs) = None.
(* PMP TOR entry 0 covers RAM *)
Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
Hypothesis Hord : zopz0zKzJ_u (zeros' 64) pmpaddr0 = false.
Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
Hypothesis Hcov : ram_base + ram_size <= uint pmpaddr0 * 4.
Hypothesis Hpma : pma_allows_pte_read (register_lookup pma_regions s.(sregs)).

Lemma exec_translateAddr_kpt_ram_ad (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  register_lookup tlb s.(sregs) = tlbvec ->
  (vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = None \/
   (exists ent, vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some ent /\
                match_TLB_Entry ent (mword_of_int 0) (sign_extend' (57 - 12) vpn) = false) \/
   (exists ptea, vec_access_dec tlbvec (tlb_hash (__id 39) vpn)
                 = Some (tlb4k_entry (mword_of_int 0) vpn (kpt_leaf_ppn vpn)
                           (mk_pte (kpt_leaf_ppn vpn) (kpt_lflags_ad adf vpn)) ptea))) ->
  exists s',
    exec (translateAddr (Virtaddr va) access) s
    = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), s')
    /\ (s' = s \/
        s' = set_reg s tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                              (Some (kpt_tlb_ent_ad adf root vpn)))).
Proof.
  intros Htlb Hslot.
  pose proof (ram_svpn_range va Hram) as Hvr.
  assert (Hdram : kpt_dram_vpn vpn) by (exact Hvr).
  pose proof (dram_vpn1_range vpn Hdram) as Hv1.
  (* the three table pages *)
  set (p1 := kpt_l1_dram root).
  set (p0 := kpt_l0_of root vpn).
  set (lppn := kpt_leaf_ppn vpn).
  set (lflags := kpt_lflags_ad adf vpn).
  (* per-slot byte-presence, at the walk's slot addresses *)
  destruct Hmem as (Hmr0 & Hmr2 & Hmdev & Hml1 & Hml0).
  assert (Hb2 : forall j : nat, (N.of_nat j < 8)%N ->
            s.(mem) !! (pa_add (pte_addr_at root (subrange_vec_dec vpn 26 18)) j)
            = Some (nth_byte (mk_pte p1 PTE_PTR) j)).
  { rewrite (ram_svpn2 va Hram). exact Hmr2. }
  assert (Hb1 : forall j : nat, (N.of_nat j < 8)%N ->
            s.(mem) !! (pa_add (pte_addr_at p1 (subrange_vec_dec vpn 17 9)) j)
            = Some (nth_byte (mk_pte p0 PTE_PTR) j)).
  { unfold p0. rewrite (dram_l0_of root vpn Hdram).
    exact (Hml1 (subrange_vec_dec vpn 17 9) Hv1). }
  assert (Hb0 : forall j : nat, (N.of_nat j < 8)%N ->
            s.(mem) !! (pa_add (pte_addr_at p0 (subrange_vec_dec vpn 8 0)) j)
            = Some (nth_byte (mk_pte lppn lflags) j)).
  { pose proof (Hml0 vpn (or_introl Hdram)) as H0.
    unfold kpt_slot0_pa, vpn0_of, kpt_leaf_pte_ad in H0.
    exact H0. }
  (* per-slot RAM-ness *)
  assert (Hram2 : addr_is_ram (pte_addr_at root (subrange_vec_dec vpn 26 18)) /\
                  addr_is_ram (pa_add (pte_addr_at root (subrange_vec_dec vpn 26 18)) 7)).
  { rewrite <- (kpt_page_0 root) at 1 2.
    apply (kpt_slot_ram root 0); [exact Hok | unfold kpt_pages; lia]. }
  assert (Hram1 : addr_is_ram (pte_addr_at p1 (subrange_vec_dec vpn 17 9)) /\
                  addr_is_ram (pa_add (pte_addr_at p1 (subrange_vec_dec vpn 17 9)) 7)).
  { apply (kpt_slot_ram root 35); [exact Hok | unfold kpt_pages; lia]. }
  assert (Hram0 : addr_is_ram (pte_addr_at p0 (subrange_vec_dec vpn 8 0)) /\
                  addr_is_ram (pa_add (pte_addr_at p0 (subrange_vec_dec vpn 8 0)) 7)).
  { unfold p0. rewrite (dram_l0_of root vpn Hdram). unfold kpt_l0_dram.
    apply (kpt_slot_ram root (36 + bv_unsigned (vpn1_of vpn)));
      [exact Hok | ].
    pose proof (bv_unsigned_in_range _ (vpn1_of vpn)) as Hnn.
    unfold kpt_pages. lia. }
  destruct Hram2 as [Hram2 Hram2']. destruct Hram1 as [Hram1 Hram1']. destruct Hram0 as [Hram0 Hram0'].
  (* per-slot PMP range matches *)
  pose proof (ram_pte_pmp8 _ pmpaddr0 Hram2 Hram2' Hcov) as Hrange2.
  pose proof (ram_pte_pmp8 _ pmpaddr0 Hram1 Hram1' Hcov) as Hrange1.
  pose proof (ram_pte_pmp8 _ pmpaddr0 Hram0 Hram0' Hcov) as Hrange0.
  (* per-slot PMA regions *)
  destruct (Hpma (pte_addr_at root (subrange_vec_dec vpn 26 18))) as (region2 & Hmatch2 & Hpte2).
  destruct (Hpma (pte_addr_at p1 (subrange_vec_dec vpn 17 9))) as (region1 & Hmatch1 & Hpte1).
  destruct (Hpma (pte_addr_at p0 (subrange_vec_dec vpn 8 0))) as (region0 & Hmatch0 & Hpte0).
  (* per-slot MMIO / device disjointness *)
  pose proof (within_clint_false _ 8 s (addr_is_ram_not_in_clint _ Hram2) ltac:(lia)) as Hc2.
  pose proof (within_clint_false _ 8 s (addr_is_ram_not_in_clint _ Hram1) ltac:(lia)) as Hc1.
  pose proof (within_clint_false _ 8 s (addr_is_ram_not_in_clint _ Hram0) ltac:(lia)) as Hc0.
  pose proof (within_sig_false _ 8 s (addr_is_ram_not_in_sig _ Hram2) ltac:(lia)) as Hsig2.
  pose proof (within_sig_false _ 8 s (addr_is_ram_not_in_sig _ Hram1) ltac:(lia)) as Hsig1.
  pose proof (within_sig_false _ 8 s (addr_is_ram_not_in_sig _ Hram0) ltac:(lia)) as Hsig0.
  pose proof (within_htif_false (pte_addr_at root (subrange_vec_dec vpn 26 18)) 8 s Hhtif) as Hh2.
  pose proof (within_htif_false (pte_addr_at p1 (subrange_vec_dec vpn 17 9)) 8 s Hhtif) as Hh1.
  pose proof (within_htif_false (pte_addr_at p0 (subrange_vec_dec vpn 8 0)) 8 s Hhtif) as Hh0.
  pose proof (addr_is_ram_not_dev _ Hram2) as Hdev2.
  pose proof (addr_is_ram_not_dev _ Hram1) as Hdev1.
  pose proof (addr_is_ram_not_dev _ Hram0) as Hdev0.
  destruct (exec_translateAddr_tramp access vpn root p1 p0 lppn lflags
              region2 region1 region0 menvcfg0 s
              (kpt_lflags_ad_bound adf vpn) (kpt_inv_red_ad adf vpn)
              (kpt_nonleaf_red_ad adf vpn) Hchk0
              kpt_extN_red (kpt_G_red_ad adf vpn) HmisaS HA Hord HR Hmenv HPBMTE
              Hrange2 Hmatch2 Hpte2 Hc2 Hsig2 Hh2 Hdev2 Hb2
              Hrange1 Hmatch1 Hpte1 Hc1 Hsig1 Hh1 Hdev1 Hb1
              Hrange0 Hmatch0 Hpte0 Hc0 Hsig0 Hh0 Hdev0 Hb0
              Hupd0
              satp0 va va
              Heff Hss Hcp HSXL Hsatp Hmode Hppn Hasid
              (ram_canonical va Hram) eq_refl (ram_ident_4k va Hram)
              tlbvec Htlb Hslot)
    as (s' & Htr & Hcase).
  exists s'. split; [exact Htr|].
  destruct Hcase as [-> | ->].
  - left. reflexivity.
  - right.
    unfold tramp_tlb_ent, kpt_tlb_ent_ad, kpt_leaf_pte_ad, kpt_slot0_pa, vpn0_of.
    unfold p0, lppn, lflags. reflexivity.
Qed.

End KptRamTranslateAD.

Lemma kpt_mem_ad_eq (adf : kpt_adf) (s s' : mstate) (root : mword 44) :
  s'.(mem) = s.(mem) -> kpt_mem_ad adf s root -> kpt_mem_ad adf s' root.
Proof.
  intros Hm (H0 & H2 & Hdev & Hl1 & Hl0).
  unfold kpt_mem_ad, kpt_slot_in in *.
  rewrite Hm.
  repeat split; assumption.
Qed.

(* ===================================================================== *)
(* 14. EXISTENTIALLY-QUANTIFIED A/D BITS (per PT entry).                  *)
(* [kpt_adf] above is keyed by vpn -- one (A, D) pair per PT ENTRY of     *)
(* this table (two virtual pages mapping the same physical page are two   *)
(* entries with independent pairs) -- but as a lemma PARAMETER it forces  *)
(* a single globally-agreed assignment.  The forms below quantify the     *)
(* bits existentially instead: [P_kpt_e] admits, per RESIDENT TLB entry,  *)
(* ANY (A, D) pair, and (in SmodeCore) [tlb_inv_e] hides the whole        *)
(* assignment.  Specs state these; a proof that must EXECUTE opens the    *)
(* existential and works at the skolem map, because success genuinely     *)
(* depends on the bits (an access through A=0 -- or a store through D=0 -- *)
(* needs a write-back the clean success lemma cannot absorb), so per-page  *)
(* bit facts about the skolem are exactly the undischargeable residue.     *)
(* ===================================================================== *)

(* a single entry with explicit bits: the constant-map instance *)
Definition kpt_tlb_ent_b (root : mword 44) (vpn : mword 27) (ad : bool * bool) : TLB_Entry :=
  kpt_tlb_ent_ad (fun _ => ad) root vpn.

(* per-entry existential legal set: any mapped vpn's leaf, ANY A/D bits *)
Definition P_kpt_e (root : mword 44) (e : TLB_Entry) : Prop :=
  exists vpn ad, kpt_mapped vpn /\ e = kpt_tlb_ent_b root vpn ad.

Lemma kpt_tlb_ent_ad_b (adf : kpt_adf) (root : mword 44) (vpn : mword 27) :
  kpt_tlb_ent_ad adf root vpn = kpt_tlb_ent_b root vpn (adf vpn).
Proof. reflexivity. Qed.

Lemma P_kpt_ad_to_e (adf : kpt_adf) (root : mword 44) (e : TLB_Entry) :
  P_kpt_ad adf root e -> P_kpt_e root e.
Proof.
  intros (vpn & Hm & ->).
  exists vpn, (adf vpn). split; [exact Hm | apply kpt_tlb_ent_ad_b].
Qed.

Lemma P_kpt_to_e (root : mword 44) (e : TLB_Entry) :
  P_kpt root e -> P_kpt_e root e.
Proof.
  intros HP. apply (P_kpt_ad_to_e kpt_adf1).
  destruct HP as (vpn & Hm & ->).
  exists vpn. split; [exact Hm | symmetry; apply kpt_tlb_ent_adf1].
Qed.

(* per-entry discrimination: ANY-bits entries still discriminate by vpn
   tag alone, so the fetch/data chains work over [P_kpt_e]-consistent TLBs *)
Lemma P_kpt_e_disc (root : mword 44) (a : mword 64) (e : TLB_Entry) :
  addr_is_ram a ->
  P_kpt_e root e ->
  (exists ad, e = kpt_tlb_ent_b root (svpn_of a) ad) \/
  match_TLB_Entry e (mword_of_int 0) (sign_extend' (57 - 12) (svpn_of a)) = false.
Proof.
  intros Hram (vpn & ad & Hm & ->).
  destruct (decide (vpn = svpn_of a)) as [-> | Hne].
  - left. exists ad. reflexivity.
  - right. unfold kpt_tlb_ent_b, kpt_tlb_ent_ad. apply match_tlb4k_other. exact Hne.
Qed.
