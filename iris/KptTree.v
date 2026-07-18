(* KptTree.v -- the kernel S-mode page table as a PtTree INSTANCE, and
   the GENERALIZED kernel translation invariant [tlb_inv_pt].

   Where [tlb_inv] (SmodeCore.v) enumerates the kvmmake layout slot by
   slot with PRESET A/D bits ([kpt_bytes]), [tlb_inv_pt] owns the table
   as ONE recursive tree ([ptree_own], PtTree.v) constrained only by the
   layout-free MAPPING spec [kpt_tree_spec]:

     - every kvmmake-mapped vpn (DRAM identity RWX / device identity RW)
       walks through some pointer path to a leaf that is an A/D VARIANT
       ([pte_set_ad]) of the canonical [kpt_leaf_pte] -- the A/D bits
       are whatever happens to be in the page-table page, as Svadu/ADUE
       requires (the hardware write-back is absorbed inside the
       invariant: [ptree_set_leaf] + [tlb_ok_pt_set_leaf]);
     - every other vpn's walk stops at an invalid entry (page fault);
     - nothing else is pinned: not the physical placement of the
       intermediate pages (kalloc's real allocation order is fine, the
       CONSECUTIVE-pages deviation of KptPt.v disappears), not the A/D
       bits, not the TLB contents beyond [tlb_ok_pt] (resident entries
       are walk entries of mapped vpns, stale in A/D at most).

   The A/D-variance bridge [pte_set_ad_kpt_leaf] rewrites a variant leaf
   into KptPt §12's [kpt_leaf_pte_ad] form, so ALL the concrete-flag
   dispatch machinery there (validity / leafness / permission checks /
   update_PTE_Bits conditions, proved for every A/D assignment) applies
   to the tree's leaves verbatim -- see the [kpt_variant_*] corollaries,
   which discharge exactly the hypotheses [ptree_maps] and the exec walk
   lemmas consume.

   Worklist (see iris/CLAUDE.md): the tree-generic translateAddr lemmas
   (success incl. the ADUE write-back arm, fault), the engine rework
   [wp_instr_s_tlbinv] -> [tlb_inv_pt], the concrete kvmmake witness
   tree + boot introduction, and porting UserPt.v onto [ptree].          *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import SmodePte.
Require Import PtAdBits.
Require Import Pt4kWalk.
Require Import CommonWalk.
Require Import PtTree.
Require Import PtTreeAdue.
Require Import KptPt.
Require Import SmodeCore.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The A/D-variance bridge into KptPt §12's concrete-flag form.        *)
(* ===================================================================== *)

(* the constant per-leaf A/D assignment picked out by two flag bits *)
Definition kpt_adf_of (a d : mword 1) : kpt_adf :=
  fun _ => (eq_vec a ('b"1"), eq_vec d ('b"1")).

Lemma kpt_lflags_bound (vpn : mword 27) : 0 <= kpt_lflags vpn < 1024.
Proof.
  unfold kpt_lflags, PTE_RAM, PTE_DEV.
  destruct (Z.leb 0x80000 (bv_unsigned vpn)); lia.
Qed.

(* an A/D variant of the canonical kernel leaf IS the §12 leaf at the
   corresponding constant assignment *)
Lemma pte_set_ad_kpt_leaf (vpn : mword 27) (a d : mword 1) :
  pte_set_ad (kpt_leaf_pte vpn) a d = kpt_leaf_pte_ad (kpt_adf_of a d) vpn.
Proof.
  unfold kpt_leaf_pte, kpt_leaf_pte_ad, mk_pte.
  rewrite (pte_set_ad_zext_concat (kpt_leaf_ppn vpn) (kpt_lflags vpn) a d
             (kpt_lflags_bound vpn)).
  assert (Hz : (mword_of_int
                  (Z.lor (Z.land (kpt_lflags vpn) 831)
                     (Z.lor (Z.shiftl (bv_unsigned a) 6)
                            (Z.shiftl (bv_unsigned d) 7))) : mword 10)
               = mword_of_int (kpt_lflags_ad (kpt_adf_of a d) vpn)).
  { unfold kpt_lflags_ad, kpt_lflags, PTE_RAM_ad, PTE_DEV_ad, PTE_RAM, PTE_DEV,
      kpt_ad_bits, kpt_adf_of.
    destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
      destruct (Z.leb 0x80000 (bv_unsigned vpn));
      apply bv_eq; vm_compute; reflexivity. }
  rewrite Hz. reflexivity.
Qed.

(* ===================================================================== *)
(* §2 Per-leaf dispatch facts for the tree's leaves: exactly the shapes   *)
(*    [ptree_maps] and the walk lemmas consume, discharged from §12.      *)
(* ===================================================================== *)

Lemma kpt_variant_flags (vpn : mword 27) (a d : mword 1) :
  subrange_vec_dec (pte_set_ad (kpt_leaf_pte vpn) a d) 7 0
  = (mword_of_int (kpt_lflags_ad (kpt_adf_of a d) vpn) : mword 8).
Proof.
  rewrite pte_set_ad_kpt_leaf. unfold kpt_leaf_pte_ad.
  apply mk_pte_flags. apply kpt_lflags_ad_bound.
Qed.

Lemma kpt_variant_ext (vpn : mword 27) (a d : mword 1) :
  ext_bits_of_PTE (pte_set_ad (kpt_leaf_pte vpn) a d)
  = Mk_PTE_Ext (mword_of_int 0).
Proof.
  rewrite pte_set_ad_kpt_leaf. unfold kpt_leaf_pte_ad.
  unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
  rewrite mk_pte_ext; [reflexivity |].
  pose proof (kpt_lflags_ad_bound (kpt_adf_of a d) vpn). lia.
Qed.

(* classification: every A/D variant of a kernel leaf is a valid 4K leaf
   with clear extension bits *)
Lemma kpt_variant_valid (vpn : mword 27) (a d : mword 1) :
  pte_valid (pte_set_ad (kpt_leaf_pte vpn) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite kpt_variant_flags. rewrite kpt_variant_ext.
  apply kpt_inv_red_ad.
Qed.

Lemma kpt_variant_leaf (vpn : mword 27) (a d : mword 1) :
  pte_leaf (pte_set_ad (kpt_leaf_pte vpn) a d).
Proof.
  unfold pte_leaf, Mk_PTE_Flags.
  rewrite kpt_variant_flags.
  apply kpt_nonleaf_red_ad.
Qed.

Lemma kpt_variant_no_napot (vpn : mword 27) (a d : mword 1) :
  pte_no_napot (pte_set_ad (kpt_leaf_pte vpn) a d).
Proof.
  unfold pte_no_napot.
  rewrite kpt_variant_ext.
  apply kpt_extN_red.
Qed.

Lemma kpt_variant_pbmt0 (vpn : mword 27) (a d : mword 1) :
  pte_pbmt0 (pte_set_ad (kpt_leaf_pte vpn) a d).
Proof.
  unfold pte_pbmt0.
  rewrite kpt_variant_ext.
  vm_compute. reflexivity.
Qed.

(* permission checks pass regardless of A/D (fetch needs the DRAM base) *)
Lemma kpt_variant_check_fetch (vpn : mword 27) (a d : mword 1) (mxr do_sum : bool) :
  kpt_dram_vpn vpn ->
  pte_check_ok (InstructionFetch tt) Supervisor mxr do_sum
    (pte_set_ad (kpt_leaf_pte vpn) a d).
Proof.
  intros Hdram s. unfold Mk_PTE_Flags.
  rewrite kpt_variant_flags. rewrite kpt_variant_ext.
  apply kpt_check_fetch_ad. exact Hdram.
Qed.

Lemma kpt_variant_check_load (vpn : mword 27) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Load Data) Supervisor mxr do_sum
    (pte_set_ad (kpt_leaf_pte vpn) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite kpt_variant_flags. rewrite kpt_variant_ext.
  apply kpt_check_load_ad.
Qed.

Lemma kpt_variant_check_store (vpn : mword 27) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Store Data) Supervisor mxr do_sum
    (pte_set_ad (kpt_leaf_pte vpn) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite kpt_variant_flags. rewrite kpt_variant_ext.
  apply kpt_check_store_ad.
Qed.

(* update_PTE_Bits: no write-back is needed exactly when A (and D, for
   stores) is already set in the variant *)
Lemma kpt_variant_upd_fetch (vpn : mword 27) (a d : mword 1) :
  eq_vec a ('b"1") = true ->
  update_PTE_Bits (pte_set_ad (kpt_leaf_pte vpn) a d) (InstructionFetch tt) = None.
Proof.
  intros Ha.
  rewrite pte_set_ad_kpt_leaf. unfold kpt_leaf_pte_ad.
  apply kpt_upd_fetch_ad. cbn. exact Ha.
Qed.

Lemma kpt_variant_upd_load (vpn : mword 27) (a d : mword 1) :
  eq_vec a ('b"1") = true ->
  update_PTE_Bits (pte_set_ad (kpt_leaf_pte vpn) a d) (Load Data) = None.
Proof.
  intros Ha.
  rewrite pte_set_ad_kpt_leaf. unfold kpt_leaf_pte_ad.
  apply kpt_upd_load_ad. cbn. exact Ha.
Qed.

Lemma kpt_variant_upd_store (vpn : mword 27) (a d : mword 1) :
  eq_vec a ('b"1") = true -> eq_vec d ('b"1") = true ->
  update_PTE_Bits (pte_set_ad (kpt_leaf_pte vpn) a d) (Store Data) = None.
Proof.
  intros Ha Hd.
  rewrite pte_set_ad_kpt_leaf. unfold kpt_leaf_pte_ad.
  apply kpt_upd_store_ad; cbn; assumption.
Qed.

(* ===================================================================== *)
(* §3 The layout-free kernel mapping spec.                                *)
(* ===================================================================== *)

Definition kpt_tree_spec (root : mword 44) (t : ptree) : Prop :=
  pt_base t = root /\
  (forall vpn, kpt_mapped vpn ->
     exists p2 p1 (a d : mword 1),
       ptree_maps t vpn p2 p1 (pte_set_ad (kpt_leaf_pte vpn) a d)) /\
  (forall vpn, ~ kpt_mapped vpn -> ptree_blocks t vpn).

(* the spec survives the ADUE write-back of any mapped vpn's leaf *)
Lemma kpt_tree_spec_set_leaf (root : mword 44) (t : ptree)
    (vpn : mword 27) (p2 p1 p0 : mword 64) (a d : mword 1) :
  kpt_tree_spec root t ->
  ptree_maps t vpn p2 p1 p0 ->
  kpt_mapped vpn ->
  (exists a0 d0 : mword 1, p0 = pte_set_ad (kpt_leaf_pte vpn) a0 d0) ->
  kpt_tree_spec root (ptree_set_leaf t vpn (pte_set_ad p0 a d)).
Proof.
  intros (Hbase & Hmap & Hblk) Hmaps Hm (a0 & d0 & Hp0).
  assert (Hvar : pte_set_ad p0 a d = pte_set_ad (kpt_leaf_pte vpn) a d).
  { rewrite Hp0. apply pte_set_ad_absorb. }
  split; [| split].
  - (* the base page is untouched *)
    rewrite <- Hbase.
    unfold ptree_set_leaf.
    destruct (pt_kids t (vpn_idx 2 vpn)); [| reflexivity].
    destruct (pt_kids p (vpn_idx 1 vpn)); reflexivity.
  - intros vpn' Hm'.
    destruct (decide (vpn' = vpn)) as [-> | Hne].
    + exists p2, p1, a, d.
      rewrite <- Hvar.
      apply (ptree_set_leaf_maps_self t vpn p2 p1 p0); [exact Hmaps | ..];
        rewrite Hvar.
      * apply kpt_variant_valid.
      * apply kpt_variant_leaf.
      * apply kpt_variant_no_napot.
      * apply kpt_variant_pbmt0.
    + destruct (Hmap vpn' Hm') as (q2 & q1 & a' & d' & Hm2).
      exists q2, q1, a', d'.
      apply (ptree_set_leaf_maps_other t vpn vpn' _ _ _ _ Hne Hm2).
  - intros vpn' Hm'.
    apply (ptree_set_leaf_blocks t vpn vpn' p2 p1 p0); [exact Hmaps |].
    apply (Hblk vpn' Hm').
Qed.

(* ===================================================================== *)
(* §4 THE GENERALIZED KERNEL TRANSLATION INVARIANT.  Same satp / PMP      *)
(*    bundling as [tlb_inv], but the page table is owned as a TREE with   *)
(*    arbitrary A/D bits and the TLB is consistent MODULO A/D.            *)
(* ===================================================================== *)

Section KptTreeInv.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Definition tlb_inv_pt (root_ppn : mword 44) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t : ptree),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt (mword_of_int 0) t tlbvec ⌝ ∗
       ⌜ kpt_tree_spec root_ppn t ⌝ ∗
       ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
       ptree_own 2 (DfracOwn 1) t ∗
       pmp_config root_ppn)%I.

  Lemma tlb_inv_pt_intro (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t : ptree) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    kpt_tree_spec root_ppn t ->
    (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0) ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ ptree_own 2 (DfracOwn 1) t -∗
    pmp_config root_ppn -∗
    tlb_inv_pt root_ppn.
  Proof.
    intros Hmode Hasid Hppn Hok Hspec Hpmaw. iIntros "Hsatp Htlb Ht Hpmp".
    iExists satp0, tlbvec, t. iFrame "Hsatp Htlb Ht Hpmp". iPureIntro. tauto.
  Qed.

  Lemma tlb_inv_pt_open (root_ppn : mword 44) :
    tlb_inv_pt root_ppn -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t : ptree),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt (mword_of_int 0) t tlbvec ⌝ ∗
      ⌜ kpt_tree_spec root_ppn t ⌝ ∗
      ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
      ptree_own 2 (DfracOwn 1) t ∗
      pmp_config root_ppn.
  Proof. iIntros "H". iExact "H". Qed.

End KptTreeInv.

(* the variant leaf's output ppn is the identity leaf ppn *)
Lemma kpt_variant_ppn (vpn : mword 27) (a d : mword 1) :
  autocast (T := mword) ((autocast (T := mword)
     (PPN_of_PTE (pte_set_ad (kpt_leaf_pte vpn) a d : mword 64))) : mword 44)
  = kpt_leaf_ppn vpn.
Proof.
  rewrite !autocast_id.
  rewrite pte_set_ad_ppn.
  unfold kpt_leaf_pte, PPN_of_PTE.
  change (Z.eqb 64 32) with false. cbv iota.
  rewrite autocast_id.
  apply mk_pte_ppn_field.
  pose proof (kpt_lflags_bound vpn). lia.
Qed.

(* ===================================================================== *)
(* §5 THE TOTAL TRANSLATION CASE ANALYSIS: at any state satisfying the    *)
(*    invariant's facts, an in-RAM va ALWAYS translates to itself, and    *)
(*    the state moves in one of exactly three invariant-absorbable ways:  *)
(*      O1  unchanged                    (TLB hit, A/D already sufficient) *)
(*      O2  TLB fill with the leaf       (walk, A/D already sufficient)    *)
(*      O3  leaf slot A/D write-back + TLB fill/refresh with the updated   *)
(*          word                         (the Svadu/ADUE arm)              *)
(*    No A/D precondition anywhere: insufficient bits take O3 instead of   *)
(*    faulting.                                                            *)
(* ===================================================================== *)

Section KptTranslate.
  Context (acc : MemoryAccessType mem_payload).

  (* per-access dispatch on any DRAM-leaf A/D variant (fetch/load/store
     instantiate via [kpt_variant_check_*]) *)
  Variable Hchk : forall (vpn : mword 27) (a d : mword 1) (mxr do_sum : bool),
    kpt_dram_vpn vpn ->
    pte_check_ok acc Supervisor mxr do_sum (pte_set_ad (kpt_leaf_pte vpn) a d).

  (* shared miss path: the TLB slot misses (empty or foreign), so the walk
     runs -- filling cleanly (O2) or writing the A/D update back (O3) *)
  Lemma kpt_translate_miss_core (root_ppn : mword 44) (va : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6))
        (p2 p1 : mword 64) (a0 d0 : mword 1) (σ : mstate) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad (kpt_leaf_pte vpn) a0 d0 in
    addr_is_ram va ->
    pte_valid p2 -> pte_ptr p2 ->
    pte_valid p1 -> pte_ptr p1 ->
    pte_valid p0 -> pte_leaf p0 -> pte_no_napot p0 ->
    pt_slot_mem σ (pt_addr0 p1 vpn) p0 ->
    exec (read_pte (Physaddr (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18))) 8) σ
      = Some (Ok p2, σ) ->
    exec (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) σ
      = Some (Ok p1, σ) ->
    exec (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) σ
      = Some (Ok p0, σ) ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup tlb σ.(sregs) = tlbvec ->
    exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_write (register_lookup pma_regions σ.(sregs)) ->
    exists σ',
      (forall mxr do_sum,
         exec (translate 39 (mword_of_int 0 : mword 16) root_ppn vpn acc Supervisor mxr do_sum tt) σ
         = Some (Ok (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44), PBMT_PMA, tt), σ'))
      /\ ( σ' = set_reg σ tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                                 (Some (u_walk_entry vpn p2 p1 p0 (mword_of_int 0))))
         \/ (exists (a1 d1 : mword 1),
              σ' = set_reg (MState σ.(sregs)
                              (write_bytes σ.(mem) (pt_addr0 p1 vpn) 8
                                 (pte_set_ad p0 a1 d1))
                              σ.(mdev))
                     tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                            (Some (u_walk_entry vpn p2 p1 (pte_set_ad p0 a1 d1) (mword_of_int 0)))))).
  Proof.
    intros vpn p0 Hram Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
           Hrd2 Hrd1 Hrd0 Hmisa Hmenv Hhtif Htlb Hlk
           HA Hord HW Hcov Hpmaw.
    assert (Hdram : kpt_dram_vpn vpn) by exact (ram_svpn_range va Hram).
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hup.
    - (* O3: the walk writes the A/D-updated leaf back *)
      destruct Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
      destruct (Hpmaw (pt_addr0 p1 vpn)) as (region0 & Hm0 & Hw0).
      assert (Hwr : exec (write_pte
                 (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
                 (p0' : mword 64)) σ
               = Some (Ok true, MState σ.(sregs)
                          (write_bytes σ.(mem) (pt_addr0 p1 vpn) 8 p0') σ.(mdev))).
      { exact (exec_write_pte_ram (pt_addr0 p1 vpn) p0' region0 σ
                 Hram0 Hram0' Hal0 HA Hord HW Hcov Hm0 Hw0 Hhtif). }
      destruct (update_PTE_Bits_set_ad _ _ _ Hup) as (a1 & d1 & Hq).
      eexists. split.
      + intros mxr do_sum.
        unfold translate.
        rewrite (exec_bind_Some _ _ _ _ _ Hlk).
        cbn match. rewrite <- Htlb.
        apply (exec_translate_TLB_miss_pt_upd acc Supervisor mxr do_sum
                 vpn root_ppn p2 p1 p0 p0' MENVCFG_S (mword_of_int 0) _ σ
                 Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap
                 (Hchk vpn a0 d0 mxr do_sum Hdram) Hup
                 Hrd2 Hrd1 Hrd0 Hmisa Hmenv HPBMTE HADUE Hwr eq_refl).
      + right. exists a1, d1.
        rewrite <- Hq. rewrite Htlb. reflexivity.
    - (* O2: clean fill *)
      assert (Hupd : update_PTE_Bits (autocast (T := mword) p0 : mword 64) acc = None)
        by exact Hup.
      eexists. split.
      + intros mxr do_sum.
        unfold translate.
        rewrite (exec_bind_Some _ _ _ _ _ Hlk).
        cbn match. rewrite <- Htlb.
        apply (exec_translate_TLB_miss_user vpn root_ppn p2 p1 p0 acc Supervisor mxr do_sum
                 Hv2 Hn2 Hv1 Hn1 Hv0 Hl0
                 (Hchk vpn a0 d0 mxr do_sum Hdram) Hnap
                 (mword_of_int 0) MENVCFG_S σ Hmisa Hupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE).
      + left. rewrite Htlb. reflexivity.
  Qed.

End KptTranslate.

Section KptTranslateAddr.
  Context (acc : MemoryAccessType mem_payload).

  Variable Hchk : forall (vpn : mword 27) (a d : mword 1) (mxr do_sum : bool),
    kpt_dram_vpn vpn ->
    pte_check_ok acc Supervisor mxr do_sum (pte_set_ad (kpt_leaf_pte vpn) a d).

  Lemma kpt_translateAddr_cases (root_ppn : mword 44) (va satp0 : mword 64)
        (t : ptree) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
        (p2 p1 : mword 64) (a0 d0 : mword 1) (σ : mstate) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad (kpt_leaf_pte vpn) a0 d0 in
    addr_is_ram va ->
    kpt_tree_spec root_ppn t ->
    ptree_maps t vpn p2 p1 p0 ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    pt_slot_mem σ (pt_addr2 t vpn) p2 ->
    pt_slot_mem σ (pt_addr1 p2 vpn) p1 ->
    pt_slot_mem σ (pt_addr0 p1 vpn) p0 ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    register_lookup satp σ.(sregs) = satp0 ->
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb σ.(sregs) = tlbvec ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_read (register_lookup pma_regions σ.(sregs)) ->
    pma_allows_pte_write (register_lookup pma_regions σ.(sregs)) ->
    exists σ',
      exec (translateAddr (Virtaddr va) acc) σ
      = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), σ')
      /\ ( σ' = σ
         \/ σ' = set_reg σ tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                                  (Some (u_walk_entry vpn p2 p1 p0 (mword_of_int 0))))
         \/ (exists (a1 d1 : mword 1),
              σ' = set_reg (MState σ.(sregs)
                              (write_bytes σ.(mem) (pt_addr0 p1 vpn) 8
                                 (pte_set_ad p0 a1 d1))
                              σ.(mdev))
                     tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                            (Some (u_walk_entry vpn p2 p1 (pte_set_ad p0 a1 d1) (mword_of_int 0)))))).
  Proof.
    intros vpn p0 Hram Hspec Hmaps Htlbok Hsm2 Hsm1 Hsm0
           Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hsatp Hmode Hppn Hasid Htlb
           HA Hord HR HW Hcov Hpmar Hpmaw.
    assert (Hdram : kpt_dram_vpn vpn) by exact (ram_svpn_range va Hram).
    destruct Hspec as (Hbase & Hmapspec & Hblkspec).
    pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                         Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
    (* the three PTE reads, at the walk's canonical slot spellings *)
    assert (Hsm2' : pt_slot_mem σ (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) p2).
    { assert (Ha2 : pt_addr2 t vpn = u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hsm2. exact Hsm2. }
    assert (Hsm1' : pt_slot_mem σ (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)) p1)
      by exact Hsm1.
    assert (Hsm0' : pt_slot_mem σ (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)) p0)
      by exact Hsm0.
    destruct (Hpmar (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)))
      as (region2 & Hm2 & Hs2).
    destruct (Hpmar (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9)))
      as (region1 & Hm1 & Hs1).
    destruct (Hpmar (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)))
      as (region0 & Hm0r & Hs0).
    pose proof (pt_read_pte_slot σ _ p2 region2 Hsm2' HA Hord HR Hcov Hm2 Hs2 Hhtif) as Hrd2.
    pose proof (pt_read_pte_slot σ _ p1 region1 Hsm1' HA Hord HR Hcov Hm1 Hs1 Hhtif) as Hrd1.
    pose proof (pt_read_pte_slot σ _ p0 region0 Hsm0' HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrd0.
    (* identity geometry *)
    assert (Hid : zero_extend' 64 (concat_vec
              ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (p0 : mword 64))) : mword 44)) : mword 44)
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va).
    { unfold p0. rewrite kpt_variant_ppn. exact (ram_ident_4k va Hram). }
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - (* resident entry *)
      destruct (Htlbok vpn ent Hslot) as (vpn0 & q2 & q1 & qp0 & a' & d' & Hm0 & Hh & ->).
      destruct (decide (vpn0 = vpn)) as [-> | Hne].
      + (* HIT on this vpn's own (A/D-variant) entry *)
        destruct (ptree_maps_det t vpn q2 q1 qp0 p2 p1 p0 Hm0 Hmaps) as (-> & -> & ->).
        assert (Hchkc : forall mxr do_sum,
                  pte_check_ok acc Supervisor mxr do_sum (pte_set_ad p0 a' d')).
        { intros mxr do_sum.
          assert (Habs : pte_set_ad p0 a' d' = pte_set_ad (kpt_leaf_pte vpn) a' d')
            by exact (pte_set_ad_absorb (kpt_leaf_pte vpn) a0 d0 a' d').
          rewrite Habs. exact (Hchk vpn a' d' mxr do_sum Hdram). }
        assert (Hpbc : pte_pbmt0 (pte_set_ad p0 a' d')).
        { assert (Habs : pte_set_ad p0 a' d' = pte_set_ad (kpt_leaf_pte vpn) a' d')
            by exact (pte_set_ad_absorb (kpt_leaf_pte vpn) a0 d0 a' d').
          rewrite Habs. apply kpt_variant_pbmt0. }
        assert (Hidc : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = va).
        { rewrite pte_set_ad_ppn. exact Hid. }
        destruct (update_PTE_Bits (pte_set_ad p0 a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * (* hit + write-back (O3) *)
          destruct Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
          destruct (Hpmaw (pt_addr0 p1 vpn)) as (regionw & Hmw & Hww).
          assert (Hwr : exec (write_pte
                     (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
                     (q0' : mword 64)) σ
                   = Some (Ok true, MState σ.(sregs)
                              (write_bytes σ.(mem) (pt_addr0 p1 vpn) 8 q0') σ.(mdev)))
            by exact (exec_write_pte_ram (pt_addr0 p1 vpn) q0' regionw σ
                        Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif).
          destruct (update_PTE_Bits_set_ad _ _ _ Hupq) as (a1 & d1 & Hq).
          assert (Hq' : q0' = pte_set_ad p0 a1 d1)
            by exact (eq_trans Hq (pte_set_ad_absorb p0 a' d' a1 d1)).
          eexists. split.
          { apply (exec_translateAddr_pt_front acc vpn root_ppn
                     (autocast (T := mword) ((autocast (T := mword)
                        (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                     satp0 va va σ _
                     Heff Hss Hcp HSXL Hsatp Hmode Hppn Hasid
                     (ram_canonical va Hram) eq_refl).
            2:{ exact Hidc. }
            intros mxr do_sum.
            unfold translate.
            rewrite (exec_bind_Some _ _ _ _ _
                       (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                          (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
            cbn match.
            apply (exec_translate_TLB_hit_pt_upd acc Supervisor mxr do_sum
                     vpn p2 p1 (pte_set_ad p0 a' d') q0' MENVCFG_S (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) _ σ
                     (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE Hwr eq_refl). }
          right. right. exists a1, d1.
          rewrite <- Hq'. rewrite Htlb. reflexivity.
        * (* hit, A/D already sufficient (O1) *)
          assert (Hupq' : update_PTE_Bits
                    (autocast (T := mword) (pte_set_ad p0 a' d') : mword 64) acc = None)
            by exact Hupq.
          eexists. split.
          { apply (exec_translateAddr_pt_front acc vpn root_ppn
                     (autocast (T := mword) ((autocast (T := mword)
                        (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                     satp0 va va σ _
                     Heff Hss Hcp HSXL Hsatp Hmode Hppn Hasid
                     (ram_canonical va Hram) eq_refl).
            2:{ exact Hidc. }
            intros mxr do_sum.
            unfold translate.
            rewrite (exec_bind_Some _ _ _ _ _
                       (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                          (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
            cbn match.
            apply (exec_translate_TLB_hit_pt acc Supervisor mxr do_sum
                     vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) σ
                     (Hchkc mxr do_sum) Hupq' Hpbc). }
          left. reflexivity.
      + (* foreign entry: rejected by the tag, so the walk runs *)
        assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
          by exact (exec_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec σ Htlb Hslot
                      (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad qp0 a' d')
                         (mword_of_int 0) Hne)).
        destruct (kpt_translate_miss_core acc Hchk root_ppn va tlbvec p2 p1 a0 d0 σ
                    Hram Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                    Hrd2 Hrd1 Hrd0 Hmisa Hmenv Hhtif Htlb Hlk
                    HA Hord HW Hcov Hpmaw)
          as (σ' & Htr & Hshape).
        exists σ'. split.
        { apply (exec_translateAddr_pt_front acc vpn root_ppn
                   (autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (p0 : mword 64))) : mword 44))
                   satp0 va va σ σ'
                   Heff Hss Hcp HSXL Hsatp Hmode Hppn Hasid
                   (ram_canonical va Hram) eq_refl Htr Hid). }
        destruct Hshape as [Ho2 | Ho3]; [right; left; exact Ho2 | right; right; exact Ho3].
    - (* empty slot: the walk runs *)
      assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
        by exact (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec σ Htlb Hslot).
      destruct (kpt_translate_miss_core acc Hchk root_ppn va tlbvec p2 p1 a0 d0 σ
                  Hram Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                  Hrd2 Hrd1 Hrd0 Hmisa Hmenv Hhtif Htlb Hlk
                  HA Hord HW Hcov Hpmaw)
        as (σ' & Htr & Hshape).
      exists σ'. split.
      { apply (exec_translateAddr_pt_front acc vpn root_ppn
                 (autocast (T := mword) ((autocast (T := mword)
                    (PPN_of_PTE (p0 : mword 64))) : mword 44))
                 satp0 va va σ σ'
                 Heff Hss Hcp HSXL Hsatp Hmode Hppn Hasid
                 (ram_canonical va Hram) eq_refl Htr Hid). }
      destruct Hshape as [Ho2 | Ho3]; [right; left; exact Ho2 | right; right; exact Ho3].
  Qed.

End KptTranslateAddr.

(* ===================================================================== *)
(* §6 THE INVARIANT ABSORBS TRANSLATION.  Opening [tlb_inv_pt] around a   *)
(*    translateAddr of any in-RAM va: translation always succeeds at the  *)
(*    identity pa, and whatever the machine did -- nothing, a TLB fill,   *)
(*    or the Svadu A/D write-back into the page table -- the invariant    *)
(*    (and the register/memory interpretations) re-establish at the       *)
(*    post-state.  Clients never see the page-table write.                *)
(* ===================================================================== *)

Section KptTranslateIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload).

  Variable Hchk : forall (vpn : mword 27) (a d : mword 1) (mxr do_sum : bool),
    kpt_dram_vpn vpn ->
    pte_check_ok acc Supervisor mxr do_sum (pte_set_ad (kpt_leaf_pte vpn) a d).

  Lemma tlb_inv_pt_translateAddr (root_ppn : mword 44) (va : mword 64) (σ : mstate) :
    addr_is_ram va ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_inv_pt root_ppn ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr va, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt root_ppn.
  Proof.
    intros Hram Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    iIntros "Hri Hgh Hinv".
    iDestruct "Hinv" as (satp0 tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hpmawimpl & Ht & Hpmp)".
    pose proof (Hpmawimpl _ Hall) as Hpmaw.
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %Hpmarimpl & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    set (vpn := svpn_of va).
    assert (Hdram : kpt_dram_vpn vpn) by exact (ram_svpn_range va Hram).
    pose proof Hspec as (Hbase & Hmapspec & Hblkspec).
    destruct (Hmapspec vpn (or_introl Hdram)) as (p2 & p1 & a0 & d0 & Hmaps).
    iDestruct (ptree_own_path_mem σ (DfracOwn 1) t vpn p2 p1 _ Hmaps with "Hgh Ht")
      as %(Hsm2 & Hsm1 & Hsm0).
    assert (HA' : pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) = TOR)
      by (rewrite Hpcv; exact HA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64)
      (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) = false)
      by (rewrite Hpav; exact Hord).
    assert (HR' : eq_vec (_get_Pmpcfg_ent_R
      (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HR).
    assert (HW' : eq_vec (_get_Pmpcfg_ent_W
      (vec_access_dec (register_lookup pmpcfg_n σ.(sregs)) 0)) ('b"1") = true)
      by (rewrite Hpcv; exact HW).
    assert (Hcov' : (ram_base + ram_size
      <= uint (vec_access_dec (register_lookup pmpaddr_n σ.(sregs)) 0) * 4)%Z)
      by (rewrite Hpav; exact Hcov).
    pose proof (Hpmarimpl _ Hall) as Hpmar.
    destruct (kpt_translateAddr_cases acc Hchk root_ppn va satp0 t tlbvec p2 p1 a0 d0 σ
                Hram Hspec Hmaps Htlbok Hsm2 Hsm1 Hsm0
                Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hsatpv Hmode Hppn Hasid Htlbv
                HA' Hord' HR' HW' Hcov' Hpmar Hpmaw)
      as (σ' & Htrans & Hshape).
    destruct Hshape as [-> | [ -> | (a1 & d1 & ->) ]].
    - (* O1: nothing moved *)
      iModIntro. iExists σ.
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; left; reflexivity |].
      iFrame "Hri Hgh".
      iApply (tlb_inv_pt_intro root_ppn satp0 tlbvec t
                Hmode Hasid Hppn Htlbok Hspec Hpmawimpl with "Hsatp Htlb Ht").
      iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                HA Hord Hpmarimpl HX HW HR Hcov with "Hpc Hpa").
    - (* O2: TLB fill with the current leaf *)
      iMod (reg_update σ.(sregs) tlb tlbvec
              (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (u_walk_entry vpn p2 p1 (pte_set_ad (kpt_leaf_pte vpn) a0 d0)
                          (mword_of_int 0))))
              with "Hri Htlb") as "[Hri Htlb]".
      iModIntro.
      iExists (set_reg σ tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (u_walk_entry vpn p2 p1 (pte_set_ad (kpt_leaf_pte vpn) a0 d0)
                          (mword_of_int 0))))).
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iFrame "Hri Hgh".
      iApply (tlb_inv_pt_intro root_ppn satp0 _ t
                Hmode Hasid Hppn
                (tlb_ok_pt_fill_self (mword_of_int 0) t tlbvec vpn p2 p1 _ Hmaps Htlbok)
                Hspec Hpmawimpl with "Hsatp Htlb Ht").
      iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                HA Hord Hpmarimpl HX HW HR Hcov with "Hpc Hpa").
    - (* O3: the Svadu write-back, absorbed *)
      set (p0 := pte_set_ad (kpt_leaf_pte vpn) a0 d0) in *.
      set (w' := pte_set_ad p0 a1 d1) in *.
      assert (Habs : w' = pte_set_ad (kpt_leaf_pte vpn) a1 d1)
        by exact (pte_set_ad_absorb (kpt_leaf_pte vpn) a0 d0 a1 d1).
      assert (Hv' : pte_valid w') by (rewrite Habs; apply kpt_variant_valid).
      assert (Hl' : pte_leaf w') by (rewrite Habs; apply kpt_variant_leaf).
      assert (Hn' : pte_no_napot w') by (rewrite Habs; apply kpt_variant_no_napot).
      assert (Hp' : pte_pbmt0 w') by (rewrite Habs; apply kpt_variant_pbmt0).
      iDestruct (ptree_own_path_upd (DfracOwn 1) t vpn p2 p1 p0 Hmaps with "Ht")
        as "(Hs2 & Hs1 & Hs0 & Hrest)".
      iMod (word_pointsto_write σ.(mem) (pt_addr0 p1 vpn) p0 w' with "Hgh Hs0")
        as "[Hgh Hs0]".
      iDestruct ("Hrest" $! w' with "Hs2 Hs1 Hs0") as "Ht".
      iMod (reg_update σ.(sregs) tlb tlbvec
              (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (u_walk_entry vpn p2 p1 w' (mword_of_int 0))))
              with "Hri Htlb") as "[Hri Htlb]".
      iModIntro.
      iExists (set_reg (MState σ.(sregs)
                          (write_bytes σ.(mem) (pt_addr0 p1 vpn) 8 w') σ.(mdev))
                 tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                        (Some (u_walk_entry vpn p2 p1 w' (mword_of_int 0))))).
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iFrame "Hri Hgh".
      iApply (tlb_inv_pt_intro root_ppn satp0 _ (ptree_set_leaf t vpn w')
                Hmode Hasid Hppn
                (tlb_ok_pt_fill_self (mword_of_int 0) (ptree_set_leaf t vpn w') tlbvec
                   vpn p2 p1 w'
                   (ptree_set_leaf_maps_self t vpn p2 p1 p0 w' Hmaps Hv' Hl' Hn' Hp')
                   (tlb_ok_pt_set_leaf (mword_of_int 0) t tlbvec vpn p2 p1 p0 a1 d1
                      Hmaps Hv' Hl' Hn' Hp' Htlbok))
                (kpt_tree_spec_set_leaf root_ppn t vpn p2 p1 p0 a1 d1
                   Hspec Hmaps (or_introl Hdram)
                   (ex_intro _ a0 (ex_intro _ d0 eq_refl)))
                Hpmawimpl
                with "Hsatp Htlb Ht").
      iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
                HA Hord Hpmarimpl HX HW HR Hcov with "Hpc Hpa").
  Qed.

End KptTranslateIris.

(* the three access instantiations: the dispatch hypothesis is exactly
   KptPt §12's per-A/D-case machinery via the [kpt_variant_*] bridges *)
Section KptTranslateIrisAcc.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Definition tlb_inv_pt_translateAddr_fetch :=
    fun root_ppn va σ =>
      tlb_inv_pt_translateAddr (InstructionFetch tt)
        (fun vpn a d mxr do_sum Hdram => kpt_variant_check_fetch vpn a d mxr do_sum Hdram)
        root_ppn va σ.

  Definition tlb_inv_pt_translateAddr_load :=
    fun root_ppn va σ =>
      tlb_inv_pt_translateAddr (Load Data)
        (fun vpn a d mxr do_sum _ => kpt_variant_check_load vpn a d mxr do_sum)
        root_ppn va σ.

  Definition tlb_inv_pt_translateAddr_store :=
    fun root_ppn va σ =>
      tlb_inv_pt_translateAddr (Store Data)
        (fun vpn a d mxr do_sum _ => kpt_variant_check_store vpn a d mxr do_sum)
        root_ppn va σ.

End KptTranslateIrisAcc.
