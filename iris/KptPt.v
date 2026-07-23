(* KptPt.v -- the faithful xv6 KERNEL PAGE TABLE (the shape [kvmmake]
   builds, xv6-riscv/kernel/vm.c): a 3-level Sv39 table whose leaves are
   all 4KB pages, providing IDENTITY mappings for
     - the UART   (va = pa = 0x10000000, R|W, one page),
     - the VIRTIO (va = pa = 0x10001000, R|W, one page),
     - the PLIC   (va = pa = [0x0c000000, 0x10000000), R|W, 64 MB), and
     - all of DRAM (va = pa = [0x80000000, 0x88000000) = the model's whole
       RAM window, R|W|X).
   Table PAGES sit at consecutive ppns from the (abstract) root:
     root+0   = the root (level-2) table:   [0] -> l1_dev, [2] -> l1_dram
     root+1   = l1_dev  (level-1, vpn2=0):  [96+k] -> l0_dev k, k in [0,33)
     root+2+k = l0_dev k (level-0):         PLIC leaves (k<32); k=32 holds
                the UART leaf (slot 0) and the VIRTIO leaf (slot 1)
     root+35  = l1_dram (level-1, vpn2=2):  [j] -> l0_dram j, j in [0,64)
     root+36+j = l0_dram j (level-0):       512 identity DRAM leaves each.
   Deliberate DEVIATIONS from kvmmake (kept to avoid touching the spec
   layer above the leaves; see iris/CLAUDE.md):
     - DRAM is now split per kvmmake at the tree/invariant layer (rwx-kmap):
       kernel text [ram_base, text_end) is R|X and data [text_end, PHYSTOP)
       is R|W, classified by §15's [kperm]/[kmap_class] and carried through
       the M-indexed [kpt_tree_spec_gen] (KptTree).  The §1 byte-level image
       constants ([PTE_RAM]/[kpt_lflags]/[kpt_mem]) are uniformly R|W|X and
       survive only as the pre-tree byte-level [tlb_inv] layer that
       SmodeCore still consumes;
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
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap list_numbers bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import Pt4kWalk.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. Layout.                                                             *)
(* ===================================================================== *)

Definition PTE_RAM : Z := 0xCF.   (* D A - - X W R V *)
Definition PTE_DEV : Z := 0xC7.   (* D A - - - W R V *)

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

(* rwx-kmap: the DRAM range split at etext = 0x80007000 -- text pages
   [0x80000, 0x80007), data pages [0x80007, 0x88000).  (Cross-checked
   against KernelSyms.etext by vm_compute where the kernel dump is in
   scope; the base memory layer stays off the dump.) *)
Definition kpt_text_vpn (vpn : mword 27) : Prop := 0x80000 <= bv_unsigned vpn < 0x80007.
Definition kpt_data_vpn (vpn : mword 27) : Prop := 0x80007 <= bv_unsigned vpn < 0x88000.

Lemma kpt_dram_vpn_split (vpn : mword 27) :
  kpt_dram_vpn vpn <-> kpt_text_vpn vpn \/ kpt_data_vpn vpn.
Proof. unfold kpt_dram_vpn, kpt_text_vpn, kpt_data_vpn. lia. Qed.

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

(* DRAM vpn1 lands in [0,64) *)

(* the DRAM l1 slot index selects exactly [vpn]'s l0 table *)


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
(* 9. Concrete-flag reductions for the DRAM leaf (PTE_RAM = 0xCF).        *)
(* ===================================================================== *)




Lemma kpt_extN_red :
  eq_vec (_get_PTE_Ext_N (Mk_PTE_Ext (mword_of_int 0 : mword 10))) ('b"1") = false.
Proof. vm_compute; reflexivity. Qed.

(* check_PTE_permission at the R|W|X U=0 leaf succeeds in S-mode for all
   three access kinds, any mxr / do_sum *)



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
(* 11. THE RAM-va translate: the kernel PT's three-way 4KB translateAddr  *)
(*     for ANY in-RAM virtual address (access-generic).  Instantiates     *)
(*     Pt4kWalk's [exec_translateAddr_tramp] with the kernel PT's tables  *)
(*     and derives every per-slot fact from [kpt_ok]/[kpt_mem].           *)
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

(* flag byte: base perms (V|R|W[|X]) + A (bit 6) + D (bit 7) *)
Definition kpt_ad_bits (ad : bool * bool) : Z :=
  (if fst ad then 64 else 0) + (if snd ad then 128 else 0).






(* ---- preset bridges: the A/D=1 instance is the fixed-flag layer ---- *)






(* ---- parametric flag-byte facts (any A/D) ---- *)





(* permission checks ignore A/D: fetch needs the DRAM (X) base; loads and
   stores pass on both bases *)



(* A/D update conditions: A=1 suffices for non-writing accesses (D free);
   stores additionally need D=1. *)







(* ---- generalized discrimination / slot facts ---- *)



(* ===================================================================== *)
(* 13. THE arbitrary-A/D RAM-va translate: [exec_translateAddr_kpt_ram]   *)
(*     generalized over the leaf A/D assignment.  The permission check    *)
(*     and the A/D-update condition (A=1; D=1 for writing accesses) are   *)
(*     HYPOTHESES, dischargeable via [kpt_check_*_ad] / [kpt_upd_*_ad].   *)
(* ===================================================================== *)



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

(* ===================================================================== *)
(* 15. R/W/X PERMISSION CLASSES AND THE STATIC KERNEL MAP (rwx-kmap).     *)
(* The kvmmake-faithful TWO flag bytes: kernel text is R|X (0xCB with     *)
(* A/D preset), data and devices are R|W (0xC7).  [kmap_class]            *)
(* classifies every statically (identity-)mapped vpn; [kmap_M0] is the    *)
(* same classification as a gmap -- the initial kernel-mapping ghost map  *)
(* of KMap.v (see claude-notes/projects/rwx-kmap.md).                     *)
(* HAZARD: NEVER normalize [kmap_M0] (no simpl/vm_compute may touch the   *)
(* ~49k-entry comprehension) -- every use goes through [kmap_M0_lookup].  *)
(* ===================================================================== *)

(* [kperm] (KP_rx | KP_rw) itself lives in RiscvPtsto, above [riscvGS],
   so the class can carry the kernel-mapping ghost over it. *)

(* base perm bits (V|R|X = 0x0B, V|R|W = 0x07) + the A/D pair on top;
   at A/D preset these are the two real kvmmake flag bytes 0xCB / 0xC7 *)
Definition kperm_base (pc : kperm) : Z :=
  match pc with KP_rx => 0x0B | KP_rw => 0x07 end.
Definition kperm_flags_ad (pc : kperm) (ad : bool * bool) : Z :=
  kperm_base pc + kpt_ad_bits ad.
Definition kperm_flags (pc : kperm) : Z := kperm_flags_ad pc (true, true).

(* which access kinds a class admits: fetch only from text (R|X), store
   and AMO only to R|W pages, loads from BOTH (both bases grant R -- this
   is what keeps every identity load path's key unchanged) *)
Definition kperm_allows (pc : kperm) (acc : MemoryAccessType mem_payload) : Prop :=
  match acc with
  | InstructionFetch _ => pc = KP_rx
  | Load _ => True
  | _ => pc = KP_rw
  end.

(* the A/D pair picked out by two flag bits (pair form of KptTree's
   [kpt_adf_of]) *)
Definition ad_of (a d : mword 1) : bool * bool :=
  (eq_vec a ('b"1"), eq_vec d ('b"1")).

(* ---- the classifier and the static predicate ---- *)

Definition kmap_class (vpn : mword 27) : option kperm :=
  if andb (Z.leb 0x80000 (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) 0x80007)
  then Some KP_rx
  else if orb (andb (Z.leb 0x80007 (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) 0x88000))
              (andb (Z.leb 0xC000 (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) 0x10002))
  then Some KP_rw
  else None.

Definition kmap_static (vpn : mword 27) (pc : kperm) : Prop :=
  kmap_class vpn = Some pc.

Lemma kmap_class_text (vpn : mword 27) :
  kpt_text_vpn vpn -> kmap_class vpn = Some KP_rx.
Proof.
  intros [Hlo Hhi]. unfold kmap_class.
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  reflexivity.
Qed.

Lemma kmap_class_rw (vpn : mword 27) :
  kpt_data_vpn vpn \/ kpt_dev_vpn vpn -> kmap_class vpn = Some KP_rw.
Proof.
  intros Hd. unfold kmap_class.
  unfold kpt_data_vpn, kpt_dev_vpn in Hd.
  destruct (andb (Z.leb 0x80000 (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) 0x80007)) eqn:Ht.
  { apply andb_prop in Ht. destruct Ht as [Ht1 Ht2].
    apply Z.leb_le in Ht1. apply Z.ltb_lt in Ht2. lia. }
  destruct Hd as [[Hlo Hhi] | [Hlo Hhi]];
    rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi);
    [rewrite Bool.andb_true_l, Bool.orb_true_l | rewrite Bool.andb_true_l, Bool.orb_true_r];
    reflexivity.
Qed.

Lemma kmap_class_cases (vpn : mword 27) (pc : kperm) :
  kmap_class vpn = Some pc ->
  (kpt_text_vpn vpn /\ pc = KP_rx) \/
  ((kpt_data_vpn vpn \/ kpt_dev_vpn vpn) /\ pc = KP_rw).
Proof.
  unfold kmap_class, kpt_text_vpn, kpt_data_vpn, kpt_dev_vpn.
  destruct (andb (Z.leb 0x80000 (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) 0x80007)) eqn:Ht.
  { apply andb_prop in Ht. destruct Ht as [Ht1 Ht2].
    apply Z.leb_le in Ht1. apply Z.ltb_lt in Ht2.
    intros [= <-]. left. split; [lia | reflexivity]. }
  destruct (orb (andb (Z.leb 0x80007 (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) 0x88000))
                (andb (Z.leb 0xC000 (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) 0x10002))) eqn:Hr;
    [| discriminate].
  apply Bool.orb_prop in Hr.
  intros [= <-]. right. split; [| reflexivity].
  destruct Hr as [Hr | Hr]; apply andb_prop in Hr; destruct Hr as [Hr1 Hr2];
    apply Z.leb_le in Hr1; apply Z.ltb_lt in Hr2; [left | right]; lia.
Qed.

Lemma kmap_static_mapped (vpn : mword 27) (pc : kperm) :
  kmap_static vpn pc -> kpt_mapped vpn.
Proof.
  intros Hc. destruct (kmap_class_cases vpn pc Hc) as [[Ht _] | [Hd _]].
  - left. apply kpt_dram_vpn_split. left. exact Ht.
  - destruct Hd as [Hd | Hd]; [left | right; exact Hd].
    apply kpt_dram_vpn_split. right. exact Hd.
Qed.

Lemma kpt_mapped_static (vpn : mword 27) :
  kpt_mapped vpn -> exists pc, kmap_static vpn pc.
Proof.
  intros [Hd | Hd].
  - apply kpt_dram_vpn_split in Hd. destruct Hd as [Hd | Hd].
    + exists KP_rx. apply kmap_class_text. exact Hd.
    + exists KP_rw. apply kmap_class_rw. left. exact Hd.
  - exists KP_rw. apply kmap_class_rw. right. exact Hd.
Qed.

(* an owned RAM va's vpn is statically classified (text or data) *)
Lemma ram_svpn_static (a : mword 64) :
  addr_is_ram a -> exists pc, kmap_static (svpn_of a) pc.
Proof.
  intros Hram. apply kpt_mapped_static. left. exact (ram_svpn_range a Hram).
Qed.

(* address-level regions land in the matching vpn class -- the conversion
   hooks the engines use: a fetch chunk's own [↦ₓ□] bytes give
   [addr_is_text] hence a KP_rx claim; a store's own [↦ₘ] bytes give
   [addr_is_kdata] hence a KP_rw claim (both via [kmap_at_static]). *)
Lemma text_svpn_class (a : mword 64) :
  addr_is_text a -> kmap_static (svpn_of a) KP_rx.
Proof.
  intros Hin. pose proof Hin as [Hlo Hhi].
  apply kmap_class_text.
  pose proof (ram_svpn_range a (addr_is_text_ram a Hin)) as [Hvlo _].
  split; [exact Hvlo |].
  rewrite (svpn_of_unsigned a (addr_is_text_ram a Hin)).
  rewrite uint_unsigned in Hhi. rewrite uint_unsigned.
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 12) with 4096.
  apply Z.div_lt_upper_bound; [lia |].
  unfold text_end in Hhi. lia.
Qed.

(* the identity re-concatenation for ANY statically classified vpn: every
   static vpn (text/data/DEVICES) sits in the POSITIVE half of the va
   space (all class ranges < 2^20 pages), so a canonical va with a static
   vpn is exactly vpn ++ offset.  Generalizes [ram_ident_4k] beyond RAM;
   the Bare regime honors static claims with it (a device va under Bare
   translates identically too).
   PROOF PLAN: from canonical (va = sign_extend of low 39 bits) and the
   class range (bv_unsigned (svpn_of a) < 0x88000 < 2^20 ⟹ bits 38:32 of
   a are 0 ⟹ bit 38 = 0 ⟹ sign-extend = zero-extend), va's unsigned is
   svpn·4096 + offset; then the [zext64_concat44_12_unsigned] /
   [zext44_27_unsigned] / [subrange64_unsigned_11_0] arithmetic exactly
   as in [ram_ident_4k]. *)
(* svpn_of as the top-27 extraction of the low-39-bit window, unconditional
   (the [uint < 2^38]-free part of [svpn_of_unsigned_lo]) *)
Lemma svpn_of_extract (a : mword 64) :
  bv_unsigned (svpn_of a)
  = Z.shiftr (bv_unsigned (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) 12.
Proof.
  unfold svpn_of. rewrite autocast_id.
  unfold subrange_vec_dec at 1. rewrite autocast_id.
  unfold to_word_idx, to_word. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice.
  change (MachineWord.MachineWord.Z_idx pagesize_bits) with 12%N.
  rewrite bv_extract_unsigned.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) as Hr.
  destruct Hr as [Hlo Hhi].
  match type of Hhi with (_ < ?m)%Z => assert (m = 549755813888) as EM39 by (vm_compute; reflexivity) end.
  rewrite EM39 in Hhi.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
  split.
  - apply Z.div_pos; lia.
  - match goal with |- (_ < ?m)%Z => assert (m = 134217728) as EM27 by (vm_compute; reflexivity); rewrite EM27 end.
    apply Z.div_lt_upper_bound; lia.
Qed.

(* every statically classified vpn is below 2^20 (all class ranges are) *)
Lemma static_svpn_bound (a : mword 64) (pc : kperm) :
  kmap_static (svpn_of a) pc -> bv_unsigned (svpn_of a) < 0x88000.
Proof.
  intro Hs. destruct (kmap_class_cases (svpn_of a) pc Hs) as [[Ht _] | [Hd _]].
  - unfold kpt_text_vpn in Ht. lia.
  - destruct Hd as [Hd | Hd]; unfold kpt_data_vpn, kpt_dev_vpn in Hd; lia.
Qed.

(* canonical + a static (hence < 2^20) vpn ⟹ va sits in the positive half:
   [uint a < 2^38].  (svpn < 2^20 ⟹ bit 38 of the sign-extended window is 0,
   so the sign-extension is a zero-extension.) *)
Lemma static_canon_lo (a : mword 64) (pc : kperm) :
  kmap_static (svpn_of a) pc ->
  neq_vec (bits_of_virtaddr (Virtaddr a))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false ->
  uint a < 274877906944.
Proof.
  intros Hstat Hcanon.
  pose proof (static_svpn_bound a pc Hstat) as Hsv.
  rewrite svpn_of_extract in Hsv.
  rewrite Z.shiftr_div_pow2 in Hsv by lia. change (2 ^ 12) with 4096 in Hsv.
  set (b := subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) in *.
  pose proof (bv_unsigned_in_range _ b) as [Hblo Hbhi].
  match type of Hbhi with (_ < ?m)%Z => assert (m = 549755813888) as EMb by (vm_compute; reflexivity) end.
  rewrite EMb in Hbhi.
  assert (Hb38 : bv_unsigned b < 2281701376).
  { pose proof (Z_div_mod_eq_full (bv_unsigned b) 4096) as Hdm.
    assert (0 <= bv_unsigned b mod 4096 < 4096) by (apply Z_mod_lt; lia). lia. }
  unfold neq_vec in Hcanon. rewrite negb_false_iff in Hcanon. unfold eq_vec in Hcanon.
  rewrite MachineWord.MachineWord.eqb_true_iff in Hcanon. unfold get_word in Hcanon.
  apply (f_equal bv_unsigned) in Hcanon.
  change (bits_of_virtaddr (Virtaddr a)) with a in Hcanon.
  rewrite uint_unsigned. rewrite Hcanon.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  rewrite bv_sign_extend_unsigned. unfold bv_signed.
  rewrite bv_swrap_small.
  2:{ match goal with |- (- ?h <= _ < ?h)%Z => assert (h = 274877906944) as EH by (vm_compute; reflexivity); rewrite EH end. lia. }
  rewrite bv_wrap_small.
  2:{ match goal with |- (0 <= _ < ?m)%Z => assert (m = 18446744073709551616) as EM64 by (vm_compute; reflexivity); rewrite EM64 end. lia. }
  lia.
Qed.

Lemma static_ident_4k (a : mword 64) (pc : kperm) :
  kmap_static (svpn_of a) pc ->
  neq_vec (bits_of_virtaddr (Virtaddr a))
     (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0)) = false ->
  zero_extend' 64 (concat_vec (kpt_leaf_ppn (svpn_of a))
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub pagesize_bits 1) 0)) = a.
Proof.
  intros Hstat Hcanon.
  pose proof (static_canon_lo a pc Hstat Hcanon) as Hlt.
  apply bv_eq.
  cbn [bits_of_virtaddr].
  change (Z.sub pagesize_bits 1) with 11.
  rewrite zext64_concat44_12_unsigned.
  unfold kpt_leaf_ppn.
  rewrite zext44_27_unsigned.
  rewrite (svpn_of_unsigned_lo a Hlt).
  rewrite subrange64_unsigned_11_0.
  rewrite uint_unsigned.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096.
  pose proof (bv_unsigned_in_range _ a) as Ha.
  pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096) as Hdm.
  lia.
Qed.

Lemma kdata_svpn_class (a : mword 64) :
  addr_is_kdata a -> kmap_static (svpn_of a) KP_rw.
Proof.
  intros Hin. pose proof Hin as [Hlo Hhi].
  apply kmap_class_rw. left.
  pose proof (ram_svpn_range a (addr_is_kdata_ram a Hin)) as [_ Hvhi].
  split; [| exact Hvhi].
  rewrite (svpn_of_unsigned a (addr_is_kdata_ram a Hin)).
  rewrite uint_unsigned in Hlo. rewrite uint_unsigned.
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 12) with 4096.
  apply Z.div_le_lower_bound; [lia |].
  unfold text_end in Hlo. lia.
Qed.

(* ---- flag-byte facts (mirror §12's, keyed by class) ---- *)

Lemma kperm_flags_ad_bound (pc : kperm) (ad : bool * bool) :
  0 <= kperm_flags_ad pc ad < 256.
Proof.
  unfold kperm_flags_ad, kperm_base, kpt_ad_bits.
  destruct pc; destruct ad as [a d]; destruct a, d; cbn; lia.
Qed.

Lemma kperm_flags_bound (pc : kperm) : 0 <= kperm_flags pc < 1024.
Proof.
  pose proof (kperm_flags_ad_bound pc (true, true)). unfold kperm_flags. lia.
Qed.

Lemma kperm_inv_red (pc : kperm) (ad : bool * bool) : forall s',
  exec (pte_is_invalid (Mk_PTE_Flags (mword_of_int (kperm_flags_ad pc ad)))
          (Mk_PTE_Ext (mword_of_int 0))) s'
  = Some (false, s').
Proof.
  intro s'. destruct pc; destruct ad as [a d]; destruct a, d; vm_compute; reflexivity.
Qed.

Lemma kperm_nonleaf_red (pc : kperm) (ad : bool * bool) :
  pte_is_non_leaf (Mk_PTE_Flags (mword_of_int (kperm_flags_ad pc ad) : mword 8)) = false.
Proof.
  destruct pc; destruct ad as [a d]; destruct a, d; vm_compute; reflexivity.
Qed.

(* permission checks: fetch needs the text (X) base; loads pass on both;
   stores and AMOs need the R|W base.  A store check against KP_rx is NOT
   provable -- stores to kernel text are unsound by construction. *)
Lemma kperm_check_fetch (ad : bool * bool) : forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (InstructionFetch tt) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kperm_flags_ad KP_rx ad)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros mxr do_sum s'. destruct ad as [a d]; destruct a, d, mxr, do_sum;
    vm_compute; reflexivity.
Qed.

Lemma kperm_check_load (pc : kperm) (ad : bool * bool) : forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (Load Data) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kperm_flags_ad pc ad)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros mxr do_sum s'. destruct pc; destruct ad as [a d]; destruct a, d, mxr, do_sum;
    vm_compute; reflexivity.
Qed.

Lemma kperm_check_store (ad : bool * bool) : forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (Store Data) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kperm_flags_ad KP_rw ad)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros mxr do_sum s'. destruct ad as [a d]; destruct a, d, mxr, do_sum;
    vm_compute; reflexivity.
Qed.

Lemma kperm_check_amo (ad : bool * bool) : forall (mxr do_sum : bool) s',
  exec (check_PTE_permission (Atomic (AMOSWAP, Data, Data)) Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kperm_flags_ad KP_rw ad)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros mxr do_sum s'. destruct ad as [a d]; destruct a, d, mxr, do_sum;
    vm_compute; reflexivity.
Qed.

(* the class-keyed dispatcher: any allowed (class, access) pair passes.
   (The 4-way access disjunction is SRegime's [s_acc_ok], inlined --
   SRegime sits above this file.) *)
Lemma kperm_check (pc : kperm) (acc : MemoryAccessType mem_payload) (ad : bool * bool) :
  (acc = InstructionFetch tt \/ acc = Load Data \/ acc = Store Data \/
   acc = Atomic (AMOSWAP, Data, Data)) ->
  kperm_allows pc acc ->
  forall (mxr do_sum : bool) s',
  exec (check_PTE_permission acc Supervisor mxr do_sum
          (Mk_PTE_Flags (mword_of_int (kperm_flags_ad pc ad)))
          (Mk_PTE_Ext (mword_of_int 0)) tt) s'
  = Some (PTE_Check_Success tt, s').
Proof.
  intros [-> | [-> | [-> | ->]]] Hall.
  - cbn in Hall. subst pc. apply kperm_check_fetch.
  - apply kperm_check_load.
  - cbn in Hall. subst pc. apply kperm_check_store.
  - cbn in Hall. subst pc. apply kperm_check_amo.
Qed.

(* ---- the static kernel map [kmap_M0] ---- *)

(* one identity region as an association list: vpns [lo, lo+len) at class
   [pc], each mapping to its own ppn *)
Definition kmap_seq (lo len : Z) (pc : kperm) : list (mword 27 * (mword 44 * kperm)) :=
  (fun z => ((mword_of_int z : mword 27),
             (kpt_leaf_ppn (mword_of_int z), pc))) <$> seqZ lo len.

(* text [0x80000, 0x80007) RX; data [0x80007, 0x88000) RW;
   devices [0xC000, 0x10002) RW *)
Definition kmap_M0 : gmap (mword 27) (mword 44 * kperm) :=
  list_to_map (kmap_seq 0x80000 0x7 KP_rx
               ++ kmap_seq 0x80007 0x7FF9 KP_rw
               ++ kmap_seq 0xC000 0x4002 KP_rw).

(* Keep typeclass search from unfolding the ~49k-entry comprehension: the only
   place that ever looks inside is [kmap_M0_lookup] (via [unfold], unaffected by
   this).  Without it, [ghost_map_alloc kmap_M0] at the two auth-mint sites
   ([kmap_alloc] here / adequacy init) makes TC resolution materialize the whole
   map -- ~262 s PER site.  [Typeclasses Opaque] (never [Opaque]) leaves
   [unfold]/[vm_compute] working, so the HAZARD above still holds. *)
Global Typeclasses Opaque kmap_M0.

(* round-trip: a Z in [0, 2^27) survives [mword_of_int : mword 27] and back *)
Lemma mword27_unsigned (z : Z) :
  0 <= z < 134217728 -> bv_unsigned (mword_of_int z : mword 27) = z.
Proof.
  intro Hz. unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 27) = 134217728) as -> by (vm_compute; reflexivity).
  exact Hz.
Qed.

Lemma vpn27_bound (vpn : mword 27) : 0 <= bv_unsigned vpn < 134217728.
Proof.
  pose proof (bv_unsigned_in_range _ vpn) as Hr.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 27) = 134217728) as Hm by (vm_compute; reflexivity).
  rewrite Hm in Hr. exact Hr.
Qed.

Lemma mword27_of_unsigned (vpn : mword 27) : mword_of_int (bv_unsigned vpn) = vpn.
Proof.
  apply bv_eq. rewrite mword27_unsigned; [reflexivity | apply vpn27_bound].
Qed.

(* the key column of one region-seq is [mword_of_int] over [seqZ] *)
Lemma kmap_seq_keys (lo len : Z) (pc : kperm) :
  (kmap_seq lo len pc).*1 = (fun z => (mword_of_int z : mword 27)) <$> seqZ lo len.
Proof.
  unfold kmap_seq. rewrite <- list_fmap_compose. reflexivity.
Qed.

(* one region-seq's lookup, purely symbolic (never normalizes seqZ) *)
Lemma kmap_seq_lookup (lo len : Z) (pc : kperm) (vpn : mword 27) :
  0 <= lo -> lo + len <= 134217728 ->
  (list_to_map (kmap_seq lo len pc) : gmap (mword 27) (mword 44 * kperm)) !! vpn
  = if andb (Z.leb lo (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) (lo + len))
    then Some (kpt_leaf_ppn vpn, pc) else None.
Proof.
  intros Hlo Hhi.
  assert (Hnd : base.NoDup ((kmap_seq lo len pc).*1)).
  { rewrite kmap_seq_keys.
    apply (NoDup_fmap_2_strong (fun z => (mword_of_int z : mword 27)) (seqZ lo len));
      [| apply NoDup_seqZ].
    intros x y Hx Hy Heq. apply elem_of_seqZ in Hx, Hy.
    assert (bv_unsigned (mword_of_int x : mword 27) = bv_unsigned (mword_of_int y : mword 27))
      as Hbv by (rewrite Heq; reflexivity).
    rewrite (mword27_unsigned x), (mword27_unsigned y) in Hbv; lia. }
  destruct (andb (Z.leb lo (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) (lo + len))) eqn:Hc.
  - apply andb_prop in Hc. destruct Hc as [Hc1 Hc2].
    apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2.
    apply elem_of_list_to_map; [exact Hnd|].
    unfold kmap_seq. apply elem_of_list_fmap.
    exists (bv_unsigned vpn). split.
    + rewrite mword27_of_unsigned. reflexivity.
    + apply elem_of_seqZ. lia.
  - apply not_elem_of_list_to_map.
    rewrite kmap_seq_keys. intro Hin. apply elem_of_list_fmap in Hin.
    destruct Hin as [z [Hz Hzin]]. apply elem_of_seqZ in Hzin.
    assert (bv_unsigned vpn = z) as Hbv.
    { rewrite Hz. apply mword27_unsigned. lia. }
    rewrite Hbv in Hc.
    apply andb_false_iff in Hc. destruct Hc as [Hc | Hc].
    + apply Z.leb_nle in Hc. lia.
    + apply Z.ltb_nlt in Hc. lia.
Qed.

(* THE characterization -- the only lemma that ever looks inside kmap_M0;
   everything downstream goes through it *)
Lemma kmap_M0_lookup (vpn : mword 27) :
  kmap_M0 !! vpn = (fun pc => (kpt_leaf_ppn vpn, pc)) <$> kmap_class vpn.
Proof.
  unfold kmap_M0.
  rewrite list_to_map_app, list_to_map_app.
  rewrite !lookup_union.
  rewrite (kmap_seq_lookup 0x80000 0x7 KP_rx vpn ltac:(lia) ltac:(lia)).
  rewrite (kmap_seq_lookup 0x80007 0x7FF9 KP_rw vpn ltac:(lia) ltac:(lia)).
  rewrite (kmap_seq_lookup 0xC000 0x4002 KP_rw vpn ltac:(lia) ltac:(lia)).
  change (0x80000 + 0x7) with 0x80007.
  change (0x80007 + 0x7FF9) with 0x88000.
  change (0xC000 + 0x4002) with 0x10002.
  unfold kmap_class.
  destruct (andb (Z.leb 0x80000 (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) 0x80007));
  destruct (andb (Z.leb 0x80007 (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) 0x88000));
  destruct (andb (Z.leb 0xC000 (bv_unsigned vpn)) (Z.ltb (bv_unsigned vpn) 0x10002));
  reflexivity.
Qed.
