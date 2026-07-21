(* KptPt.v -- the faithful xv6 KERNEL PAGE TABLE (the shape [kvmmake]
   builds, xv6-riscv/kernel/vm.c): a 3-level Sv39 table whose leaves are
   all 4KB pages, providing IDENTITY mappings for
     - the UART   (va = pa = 0x10000000, R|W, one page),
     - the VIRTIO (va = pa = 0x10001000, R|W, one page),
     - the PLIC   (va = pa = [0x0c000000, 0x10000000), R|W, 64 MB),
     - kernel TEXT (va = pa = [KERNBASE, etext) = [0x80000000, 0x80007000),
       R|X), and
     - kernel DATA + free RAM (va = pa = [etext, PHYSTOP)
       = [0x80007000, 0x88000000), R|W; PHYSTOP = KERNBASE + 128 MiB
       = the model's whole RAM window, see [ram_size]).
   kvmmake additionally maps the TRAMPOLINE page (va = MAXVA-PGSIZE,
   pa = KernelSyms.trampoline, R|X) and the NPROC per-proc kernel stacks
   (va = KSTACK(p), pa = kalloc-chosen, R|W); those two NON-IDENTITY
   region families live in KptTree.v (the trampoline leaf [pte_tramp] and
   the kstack extension), not here -- this file holds the identity regions.
   Table PAGES sit at consecutive ppns from the (abstract) root:
     root+0   = the root (level-2) table:   [0] -> l1_dev, [2] -> l1_dram
     root+1   = l1_dev  (level-1, vpn2=0):  [96+k] -> l0_dev k, k in [0,33)
     root+2+k = l0_dev k (level-0):         PLIC leaves (k<32); k=32 holds
                the UART leaf (slot 0) and the VIRTIO leaf (slot 1)
     root+35  = l1_dram (level-1, vpn2=2):  [j] -> l0_dram j, j in [0,64)
     root+36+j = l0_dram j (level-0):       512 identity DRAM leaves each.
   Deliberate DEVIATIONS from kvmmake (kept to avoid touching the spec
   layer above the leaves; see iris/CLAUDE.md):
     - leaf A/D bits are PRESET in the default instance (xv6 leaves them
       clear).  §12 below generalizes the whole layer over a per-leaf A/D
       assignment [kpt_adf].  This build is Svadu (menvcfg.ADUE = 1): an
       access needing an A/D update has it written back.  The success
       lemmas require A (and D for stores) on the touched page so that no
       update is needed ([update_PTE_Bits = None]) and the walk therefore
       leaves the state UNCHANGED; without it the write-back would perturb
       the state and the clean success lemma would not hold;
     - table pages are CONSECUTIVE from the root (kalloc's actual boot
       order yields descending pages).  The layout-free spec layer
       ([kpt_tree_spec], KptTree.v) does not see this choice.
   This file is IRIS-FREE and in the vanilla-Ltac dialect (like Pt4kWalk);
   the Iris ownership bundle for the PT bytes lives in SmodeCore. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import Pt4kWalk.
(* [etext_vpn], [addr_in_text], [addr_in_data] live in KptExecMap (below
   InstrBytes) so the fetch layer can name the text region without a cycle;
   re-export so this file's existing consumers keep seeing those names. *)
Require Export KptExecMap.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. Layout.                                                             *)
(* ===================================================================== *)

(* Leaf flag bytes, A/D PRESET (the default [kpt_adf1] instance; §12
   generalizes).  Base perms follow kvmmake exactly: text R|X, data R|W,
   devices R|W. *)
Definition PTE_TEXT : Z := 0x4B.  (* - A - - X - R V *)
Definition PTE_DATA : Z := 0xC7.  (* D A - - - W R V *)
Definition PTE_DEV  : Z := 0xC7.  (* D A - - - W R V *)
(* LEGACY: the pre-reconciliation uniform-RWX DRAM flag.  No longer
   produced by [kpt_lflags]; §9-§11 lemmas still stated on it must be
   re-stated per region (PTE_TEXT / PTE_DATA) -- or better, generalized
   over the flag byte -- during the proof repair (see
   claude-notes/projects/kpt-xv6-reconcile.md). *)
Definition PTE_RAM : Z := 0xCF.   (* D A - - X W R V *)

(* [etext_vpn] (= 0x80007) now lives in KptExecMap (re-exported above). *)

Definition kpt_pages : Z := 100.

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

Definition kpt_dram_vpn (vpn : mword 27) : Prop := 0x80000 <= bv_unsigned vpn < 0x88000.
Definition kpt_dev_vpn  (vpn : mword 27) : Prop := 0xC000 <= bv_unsigned vpn < 0x10002.
Definition kpt_mapped (vpn : mword 27) : Prop := kpt_dram_vpn vpn \/ kpt_dev_vpn vpn.

(* the text/data split of the DRAM range (kvmmake maps [KERNBASE, etext)
   R|X and [etext, PHYSTOP) R|W) *)
Definition kpt_text_vpn (vpn : mword 27) : Prop :=
  0x80000 <= bv_unsigned vpn < etext_vpn.
Definition kpt_data_vpn (vpn : mword 27) : Prop :=
  etext_vpn <= bv_unsigned vpn < 0x88000.

(* the same split at the ADDRESS level ([addr_in_text]/[addr_in_data]) now
   lives in KptExecMap (re-exported above). *)

Definition kpt_lflags (vpn : mword 27) : Z :=
  if Z.leb 0x80000 (bv_unsigned vpn)
  then (if Z.ltb (bv_unsigned vpn) etext_vpn then PTE_TEXT else PTE_DATA)
  else PTE_DEV.

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

(* THE legal-TLB-entry set of the kernel page table (the [P] of
   [tlb_consistent] / [tlb_inv_gen]): any mapped vpn's own 4KB leaf entry. *)

(* ===================================================================== *)
(* 3. vpn subrange arithmetic (27-bit clones of TrampPt's 64-bit facts).  *)
(* ===================================================================== *)




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


(* a slot of any PT page is (both ends) in RAM *)

(* the mapped-DRAM vpn range from an owned RAM address *)
Lemma ram_svpn_range (a : mword 64) :
  addr_is_ram a -> 0x80000 <= bv_unsigned (svpn_of a) < 0x88000.
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

(* the region sub-ranges embed into RAM *)
Lemma addr_in_text_ram (a : mword 64) : addr_in_text a -> addr_is_ram a.
Proof.
  intros [Hlo Hhi]. unfold addr_is_ram.
  unfold ram_base, ram_size, etext_vpn in *. lia.
Qed.

Lemma addr_in_data_ram (a : mword 64) : addr_in_data a -> addr_is_ram a.
Proof.
  intros [Hlo Hhi]. unfold addr_is_ram.
  unfold ram_base, ram_size, etext_vpn in *. lia.
Qed.

(* ... and their vpns land in the corresponding vpn regions (the clones of
   [ram_svpn_range] at the text/data bounds) *)
Lemma text_svpn_range (a : mword 64) :
  addr_in_text a -> kpt_text_vpn (svpn_of a).
Proof.
  intros Hin. pose proof (addr_in_text_ram a Hin) as Hram.
  destruct Hin as [Hlo Hhi].
  rewrite uint_unsigned in Hlo, Hhi.
  unfold kpt_text_vpn.
  rewrite (svpn_of_unsigned a Hram).
  rewrite uint_unsigned.
  rewrite Z.shiftr_div_pow2 by lia.
  unfold ram_base, etext_vpn in *.
  change (2 ^ 12) with 4096 in *.
  split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma data_svpn_range (a : mword 64) :
  addr_in_data a -> kpt_data_vpn (svpn_of a).
Proof.
  intros Hin. pose proof (addr_in_data_ram a Hin) as Hram.
  destruct Hin as [Hlo Hhi].
  rewrite uint_unsigned in Hlo, Hhi.
  unfold kpt_data_vpn.
  rewrite (svpn_of_unsigned a Hram).
  rewrite uint_unsigned.
  rewrite Z.shiftr_div_pow2 by lia.
  unfold ram_base, ram_size, etext_vpn in *.
  change (2 ^ 12) with 4096 in *.
  split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma data_svpn_not_text (a : mword 64) :
  addr_in_data a -> ~ kpt_text_vpn (svpn_of a).
Proof.
  intros Hin [_ Hhi].
  destruct (data_svpn_range a Hin) as [Hlo _]. lia.
Qed.

Lemma dev_not_text (vpn : mword 27) :
  kpt_dev_vpn vpn -> ~ kpt_text_vpn vpn.
Proof. intros [_ Hhi] [Hlo _]. lia. Qed.

(* DRAM vpn1 lands in [0,64) *)

(* the DRAM l1 slot index selects exactly [vpn]'s l0 table *)

Lemma text_lflags (vpn : mword 27) :
  kpt_text_vpn vpn -> kpt_lflags vpn = PTE_TEXT.
Proof.
  intros [Hlo Hhi]. unfold kpt_lflags.
  rewrite (proj2 (Z.leb_le 0x80000 (bv_unsigned vpn)) Hlo).
  rewrite (proj2 (Z.ltb_lt (bv_unsigned vpn) etext_vpn) Hhi).
  reflexivity.
Qed.

Lemma data_lflags (vpn : mword 27) :
  kpt_data_vpn vpn -> kpt_lflags vpn = PTE_DATA.
Proof.
  intros [Hlo Hhi]. unfold kpt_lflags.
  assert (H8 : 0x80000 <= bv_unsigned vpn) by (unfold etext_vpn in Hlo; lia).
  rewrite (proj2 (Z.leb_le 0x80000 (bv_unsigned vpn)) H8).
  rewrite (proj2 (Z.ltb_ge (bv_unsigned vpn) etext_vpn) Hlo).
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


(* every legal kernel-PT entry either IS this RAM va's own entry or fails
   to match its tag *)

(* every RAM va's own entry is legal *)

(* ===================================================================== *)
(* 7. Flag-byte facts for the two leaf kinds (A/D preset).                *)
(* ===================================================================== *)

(* A/D preset => the walk never needs a PTE write-back, for ANY access *)

(* (The concrete-flag [update_PTE_Bits] instances for the leaf kinds are the
   flag-generic [kpt_upd_fetch_ad] / [kpt_upd_load_ad] / [kpt_upd_store_ad]
   in §12, over [kpt_lflags_ad]; there is no separate PTE_RAM instance.) *)

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
  /\ (forall i : mword 9, bv_unsigned i < 64 ->
        kpt_slot_in s (pte_addr_at (kpt_l1_dram root) i)
          (mk_pte (kpt_l0_dram root (bv_unsigned i)) PTE_PTR))
  /\ (forall vpn : mword 27, kpt_mapped vpn ->
        kpt_slot_in s (kpt_slot0_pa root vpn) (kpt_leaf_pte vpn)).


(* mword_of_int round-trips on the unsigned value (9- and 27-bit). *)


(* ===================================================================== *)
(* 9. Concrete-flag reductions.  The flag-DEPENDENT reductions (invalid /  *)
(*    non-leaf / G / check) are stated flag-GENERICALLY over [kpt_lflags_ad] *)
(*    in §12 ([kpt_inv_red_ad], [kpt_nonleaf_red_ad], [kpt_G_red_ad],       *)
(*    [kpt_check_{fetch,load,store}_ad]); there are no separate per-flag     *)
(*    (PTE_RAM) instances.  [kpt_extN_red] is flag-INDEPENDENT (the ext N    *)
(*    bit of a 0 extension byte) and stays here.                            *)
(* ===================================================================== *)

Lemma kpt_extN_red :
  eq_vec (_get_PTE_Ext_N (Mk_PTE_Ext (mword_of_int 0 : mword 10))) ('b"1") = false.
Proof. vm_compute; reflexivity. Qed.

(* (check_PTE_permission at each leaf kind: the flag-generic
   [kpt_check_{fetch,load,store}_ad] in §12 — fetch needs the TEXT (X) base,
   loads pass everywhere, stores need any non-TEXT (W) base.) *)

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

(* the root page is page 0 *)

(* ===================================================================== *)
(* 11. THE RAM-va translate is the flag-generic [exec_translateAddr_kpt_ram_ad] *)
(*     of §13 (over [kpt_lflags_ad]); there is no separate PTE_RAM instance. *)
(* ===================================================================== *)
(* transport [kpt_mem] across a memory-preserving state change *)

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
(* The preset A/D assignment reproducing the un-suffixed [kpt_lflags]: A is
   set everywhere; D is set on the writable regions (data / devices) but
   CLEAR on text ([0x80000, etext_vpn)), which is never dirtied.  This
   matches the baked-in presets of the flag literals -- PTE_TEXT = 0x4B
   (A, no D), PTE_DATA / PTE_DEV = 0xC7 (A, D) -- so [kpt_lflags_adf1]
   below holds.  (A uniform [fun _ => (true,true)] would give text D=1,
   i.e. 0xCB, and would NOT reproduce PTE_TEXT.) *)
Definition kpt_adf1 : kpt_adf := fun vpn =>
  (true, negb (Z.leb 0x80000 (bv_unsigned vpn) && Z.ltb (bv_unsigned vpn) etext_vpn)).

(* flag byte: base perms (V|R|W[|X]) + A (bit 6) + D (bit 7) *)
Definition kpt_ad_bits (ad : bool * bool) : Z :=
  (if fst ad then 64 else 0) + (if snd ad then 128 else 0).
Definition PTE_TEXT_ad (ad : bool * bool) : Z := 0x0B + kpt_ad_bits ad.
Definition PTE_DATA_ad (ad : bool * bool) : Z := 0x07 + kpt_ad_bits ad.
Definition PTE_DEV_ad  (ad : bool * bool) : Z := 0x07 + kpt_ad_bits ad.
(* LEGACY uniform-RWX flag (see PTE_RAM above). *)
Definition PTE_RAM_ad (ad : bool * bool) : Z := 0x0F + kpt_ad_bits ad.

Definition kpt_lflags_ad (adf : kpt_adf) (vpn : mword 27) : Z :=
  if Z.leb 0x80000 (bv_unsigned vpn)
  then (if Z.ltb (bv_unsigned vpn) etext_vpn
        then PTE_TEXT_ad (adf vpn) else PTE_DATA_ad (adf vpn))
  else PTE_DEV_ad (adf vpn).

Definition kpt_leaf_pte_ad (adf : kpt_adf) (vpn : mword 27) : mword 64 :=
  mk_pte (kpt_leaf_ppn vpn) (kpt_lflags_ad adf vpn).



Definition kpt_mem_ad (adf : kpt_adf) (s : mstate) (root : mword 44) : Prop :=
  kpt_slot_in s (pte_addr_at root (mword_of_int 0)) (mk_pte (kpt_l1_dev root) PTE_PTR)
  /\ kpt_slot_in s (pte_addr_at root (mword_of_int 2)) (mk_pte (kpt_l1_dram root) PTE_PTR)
  /\ (forall i : mword 9, 96 <= bv_unsigned i < 129 ->
        kpt_slot_in s (pte_addr_at (kpt_l1_dev root) i)
          (mk_pte (kpt_l0_dev root (bv_unsigned i - 96)) PTE_PTR))
  /\ (forall i : mword 9, bv_unsigned i < 64 ->
        kpt_slot_in s (pte_addr_at (kpt_l1_dram root) i)
          (mk_pte (kpt_l0_dram root (bv_unsigned i)) PTE_PTR))
  /\ (forall vpn : mword 27, kpt_mapped vpn ->
        kpt_slot_in s (kpt_slot0_pa root vpn) (kpt_leaf_pte_ad adf vpn)).

(* ---- preset bridges: the A/D=1 instance is the fixed-flag layer ---- *)

Lemma kpt_lflags_adf1 (vpn : mword 27) : kpt_lflags_ad kpt_adf1 vpn = kpt_lflags vpn.
Proof.
  unfold kpt_lflags_ad, kpt_lflags, kpt_adf1, kpt_ad_bits,
    PTE_TEXT_ad, PTE_DATA_ad, PTE_DEV_ad, PTE_TEXT, PTE_DATA, PTE_DEV.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    [ destruct (Z.ltb (bv_unsigned vpn) etext_vpn) | ]; reflexivity.
Qed.





(* ---- parametric flag-byte facts (any A/D) ---- *)

Lemma kpt_lflags_ad_bound (adf : kpt_adf) (vpn : mword 27) :
  0 <= kpt_lflags_ad adf vpn < 256.
Proof.
  unfold kpt_lflags_ad, PTE_TEXT_ad, PTE_DATA_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    [ destruct (Z.ltb (bv_unsigned vpn) etext_vpn) | ];
    destruct (adf vpn) as [a d]; destruct a, d; cbn; lia.
Qed.

Lemma kpt_inv_red_ad (adf : kpt_adf) (vpn : mword 27) : forall s',
  exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn)))
          (Mk_PTE_Ext (mword_of_int 0))) s'
  = Some (false, s').
Proof.
  intro s'.
  unfold kpt_lflags_ad, PTE_TEXT_ad, PTE_DATA_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    [ destruct (Z.ltb (bv_unsigned vpn) etext_vpn) | ];
    destruct (adf vpn) as [a d]; destruct a, d; vm_compute; reflexivity.
Qed.

Lemma kpt_nonleaf_red_ad (adf : kpt_adf) (vpn : mword 27) :
  pte_is_non_leaf (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn) : mword 8)) = false.
Proof.
  unfold kpt_lflags_ad, PTE_TEXT_ad, PTE_DATA_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    [ destruct (Z.ltb (bv_unsigned vpn) etext_vpn) | ];
    destruct (adf vpn) as [a d]; destruct a, d; vm_compute; reflexivity.
Qed.

Lemma kpt_G_red_ad (adf : kpt_adf) (vpn : mword 27) :
  eq_vec (_get_PTE_Flags_G (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn) : mword 8)))
    ('b"1") = false.
Proof.
  unfold kpt_lflags_ad, PTE_TEXT_ad, PTE_DATA_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    [ destruct (Z.ltb (bv_unsigned vpn) etext_vpn) | ];
    destruct (adf vpn) as [a d]; destruct a, d; vm_compute; reflexivity.
Qed.

(* permission checks ignore A/D: fetch needs the TEXT (X) base; loads
   pass on every base (R everywhere); stores need W, i.e. any base but
   TEXT (data and devices are both R|W) *)
(* PROOF-REPAIR(kpt-xv6-reconcile): re-dispatch the three check lemmas on
   the 3-way kpt_lflags_ad split (text/data/dev). *)
Lemma kpt_check_fetch_ad (adf : kpt_adf) (vpn : mword 27) :
  kpt_text_vpn vpn ->
  forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros [Hlo Hhi] mxr do_sum s'.
  unfold kpt_lflags_ad, PTE_TEXT_ad, kpt_ad_bits.
  rewrite (proj2 (Z.leb_le 0x80000 (bv_unsigned vpn)) Hlo).
  rewrite (proj2 (Z.ltb_lt (bv_unsigned vpn) etext_vpn) Hhi).
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
  unfold kpt_lflags_ad, PTE_TEXT_ad, PTE_DATA_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    [ destruct (Z.ltb (bv_unsigned vpn) etext_vpn) | ];
    destruct (adf vpn) as [a d]; destruct a, d, mxr, do_sum; vm_compute; reflexivity.
Qed.

Lemma kpt_check_store_ad (adf : kpt_adf) (vpn : mword 27) :
  ~ kpt_text_vpn vpn ->
  forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (Store Data) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros Hnt mxr do_sum s'.
  unfold kpt_lflags_ad, PTE_TEXT_ad, PTE_DATA_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn)) eqn:Hleb.
  - (* 0x80000 <= vpn; not-text forces vpn >= etext_vpn (the DATA leaf) *)
    assert (Hge : etext_vpn <= bv_unsigned vpn).
    { apply Z.leb_le in Hleb.
      destruct (Z_lt_le_dec (bv_unsigned vpn) etext_vpn) as [Hlt | Hge]; [| exact Hge].
      exfalso. apply Hnt. split; [exact Hleb | exact Hlt]. }
    rewrite (proj2 (Z.ltb_ge (bv_unsigned vpn) etext_vpn) Hge).
    destruct (adf vpn) as [a d]; destruct a, d, mxr, do_sum; vm_compute; reflexivity.
  - (* vpn < 0x80000: the DEV leaf *)
    destruct (adf vpn) as [a d]; destruct a, d, mxr, do_sum; vm_compute; reflexivity.
Qed.

(* A/D update conditions: A=1 suffices for non-writing accesses (D free);
   stores additionally need D=1. *)


Lemma kpt_A_red_ad (adf : kpt_adf) (vpn : mword 27) :
  fst (adf vpn) = true ->
  eq_vec (_get_PTE_Flags_A (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn) : mword 8))) ('b"0") = false.
Proof.
  intro Ha.
  unfold kpt_lflags_ad, PTE_TEXT_ad, PTE_DATA_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    [ destruct (Z.ltb (bv_unsigned vpn) etext_vpn) | ];
    destruct (adf vpn) as [a d]; cbn in Ha; subst a; destruct d; vm_compute; reflexivity.
Qed.

Lemma kpt_D_red_ad (adf : kpt_adf) (vpn : mword 27) :
  snd (adf vpn) = true ->
  eq_vec (_get_PTE_Flags_D (Mk_PTE_Flags (mword_of_int (kpt_lflags_ad adf vpn) : mword 8))) ('b"0") = false.
Proof.
  intro Hd.
  unfold kpt_lflags_ad, PTE_TEXT_ad, PTE_DATA_ad, PTE_DEV_ad, kpt_ad_bits.
  destruct (Z.leb 0x80000 (bv_unsigned vpn));
    [ destruct (Z.ltb (bv_unsigned vpn) etext_vpn) | ];
    destruct (adf vpn) as [a d]; cbn in Hd; subst d; destruct a; vm_compute; reflexivity.
Qed.




(* ---- generalized discrimination / slot facts ---- *)



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


End KptRamTranslateAD.


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

(* per-entry existential legal set: any mapped vpn's leaf, ANY A/D bits *)




(* per-entry discrimination: ANY-bits entries still discriminate by vpn
   tag alone, so the fetch/data chains work over [P_kpt_e]-consistent TLBs *)
