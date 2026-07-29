(* KptTree.v -- the kernel S-mode page table as a PtTree INSTANCE, and
   the GENERALIZED kernel translation invariant [tlb_inv_pt].

   Where [tlb_inv] (SmodeCore.v) enumerates the kvmmake layout slot by
   slot with PRESET A/D bits ([kpt_bytes]), [tlb_inv_pt] owns the table
   as ONE recursive tree ([ptree_own], PtTree.v) constrained only by the
   layout-free MAPPING spec [kpt_tree_spec_gen], the EXACT
   representation of the mapping ghost's map M (§3b):

     - every vpn M maps (text R|X / data R|W / devices R|W / trampoline /
       the per-proc kernel stacks -- all just entries of M) walks through
       some pointer path to a leaf that is an A/D VARIANT ([pte_set_ad])
       of the canonical [kpt_leaf_pte_of vpn e] -- the A/D bits
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
   to the tree's leaves verbatim -- see §2c's [kperm_variant_*]
   corollaries (arbitrary ppn, class-keyed), which discharge exactly the
   hypotheses [ptree_maps] and the exec walk lemmas consume.

   The absorption theorem is the ONE claim-keyed
   [tlb_inv_pt_translateAddr_at] (§6): a consumer holding
   [kmap_at (svpn_of va) ppn pc] plus [kperm_allows pc acc] translates va
   to ppn's page -- so a fetch is provable only at KP_rx and a store only
   at KP_rw, and identity is just the case where the claim's ppn is
   [kpt_leaf_ppn].  See claude-notes/design/tlb-translation.md.        *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import SmodePte.
Require Import PtAdBits.
Require Import Pt4kWalk.
Require Import CommonWalk.
Require Import PtTree.
Require Import PtTreeAdue.
Require Import KptPt.
Require Import KptExecMap.
Require Import KMap.
Require Import Pt4kWalk.
Require Import SmodeCore.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The A/D-variance bridge into KptPt §12's concrete-flag form.        *)
(* ===================================================================== *)

(* the constant per-leaf A/D assignment picked out by two flag bits *)

Lemma kpt_lflags_bound (vpn : mword 27) : 0 <= kpt_lflags vpn < 1024.
Proof.
  unfold kpt_lflags, PTE_RAM, PTE_DEV.
  destruct (Z.leb 0x80000 (bv_unsigned vpn)); lia.
Qed.

(* an A/D variant of the canonical kernel leaf IS the §12 leaf at the
   corresponding constant assignment *)

(* ===================================================================== *)
(* §2 Per-leaf dispatch facts for the tree's leaves: exactly the shapes   *)
(*    [ptree_maps] and the walk lemmas consume, discharged from §12.      *)
(* ===================================================================== *)



(* classification: every A/D variant of a kernel leaf is a valid 4K leaf
   with clear extension bits *)




(* permission checks pass regardless of A/D (fetch needs the DRAM base) *)



(* AMO variants of KptPt's check lemmas (A/D-variant leaf passes the
   check for amoswap.w at Supervisor). *)


(* ===================================================================== *)
(* §2c CLASS-KEYED LEAVES WITH ARBITRARY PPN (rwx-kmap).  The same        *)
(*     dispatch facts for A/D variants of [mk_pte ppn (kperm_flags pc)],  *)
(*     feeding [kpt_tree_spec_gen]'s uniform maps-clause: identity        *)
(*     text/data/device leaves AND the dynamic kstack leaves are all      *)
(*     instances (KptPt §15; claude-notes/design/tlb-translation.md).     *)
(* ===================================================================== *)

(* an A/D variant of a class-keyed leaf IS the leaf at the corresponding
   A/D pair (arbitrary-ppn analogue of [pte_set_ad_kpt_leaf]) *)
Lemma kperm_set_ad_leaf (ppn : mword 44) (pc : kperm) (a d : mword 1) :
  pte_set_ad (mk_pte ppn (kperm_flags pc)) a d
  = mk_pte ppn (kperm_flags_ad pc (ad_of a d)).
Proof.
  unfold mk_pte.
  rewrite (pte_set_ad_zext_concat ppn (kperm_flags pc) a d (kperm_flags_bound pc)).
  assert (Hz : (mword_of_int
                  (Z.lor (Z.land (kperm_flags pc) 831)
                     (Z.lor (Z.shiftl (bv_unsigned a) 6)
                            (Z.shiftl (bv_unsigned d) 7))) : mword 10)
               = mword_of_int (kperm_flags_ad pc (ad_of a d))).
  { unfold kperm_flags, kperm_flags_ad, kperm_base, kpt_ad_bits, ad_of.
    destruct pc;
      destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
      apply bv_eq; vm_compute; reflexivity. }
  rewrite Hz. reflexivity.
Qed.

Lemma kperm_variant_flags (ppn : mword 44) (pc : kperm) (a d : mword 1) :
  subrange_vec_dec (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d) 7 0
  = (mword_of_int (kperm_flags_ad pc (ad_of a d)) : mword 8).
Proof.
  rewrite kperm_set_ad_leaf.
  apply mk_pte_flags. apply kperm_flags_ad_bound.
Qed.

Lemma kperm_variant_ext (ppn : mword 44) (pc : kperm) (a d : mword 1) :
  ext_bits_of_PTE (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d)
  = Mk_PTE_Ext (mword_of_int 0).
Proof.
  rewrite kperm_set_ad_leaf.
  unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
  rewrite mk_pte_ext; [reflexivity |].
  pose proof (kperm_flags_ad_bound pc (ad_of a d)). lia.
Qed.

(* classification: every A/D variant of a class-keyed leaf is a valid 4K
   leaf with clear extension bits *)
Lemma kperm_variant_valid (ppn : mword 44) (pc : kperm) (a d : mword 1) :
  pte_valid (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite kperm_variant_flags. rewrite kperm_variant_ext.
  apply kperm_inv_red.
Qed.

Lemma kperm_variant_leaf (ppn : mword 44) (pc : kperm) (a d : mword 1) :
  pte_leaf (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d).
Proof.
  unfold pte_leaf, Mk_PTE_Flags.
  rewrite kperm_variant_flags.
  apply kperm_nonleaf_red.
Qed.

Lemma kperm_variant_no_napot (ppn : mword 44) (pc : kperm) (a d : mword 1) :
  pte_no_napot (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d).
Proof.
  unfold pte_no_napot.
  rewrite kperm_variant_ext.
  apply kpt_extN_red.
Qed.

Lemma kperm_variant_pbmt0 (ppn : mword 44) (pc : kperm) (a d : mword 1) :
  pte_pbmt0 (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d).
Proof.
  unfold pte_pbmt0.
  rewrite kperm_variant_ext.
  vm_compute. reflexivity.
Qed.

(* permission checks, class-keyed: fetch only from RX, loads from both,
   store/AMO only to RW.  A store check on an RX leaf is NOT provable --
   stores to kernel text are unsound by construction. *)
Lemma kperm_variant_check_fetch (ppn : mword 44) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (InstructionFetch tt) Supervisor mxr do_sum
    (pte_set_ad (mk_pte ppn (kperm_flags KP_rx)) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite kperm_variant_flags. rewrite kperm_variant_ext.
  apply kperm_check_fetch.
Qed.

Lemma kperm_variant_check_load (ppn : mword 44) (pc : kperm) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Load Data) Supervisor mxr do_sum
    (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite kperm_variant_flags. rewrite kperm_variant_ext.
  apply kperm_check_load.
Qed.

Lemma kperm_variant_check_store (ppn : mword 44) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Store Data) Supervisor mxr do_sum
    (pte_set_ad (mk_pte ppn (kperm_flags KP_rw)) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite kperm_variant_flags. rewrite kperm_variant_ext.
  apply kperm_check_store.
Qed.

Lemma kperm_variant_check_amo (ppn : mword 44) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Atomic (AMOSWAP, Data, Data)) Supervisor mxr do_sum
    (pte_set_ad (mk_pte ppn (kperm_flags KP_rw)) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite kperm_variant_flags. rewrite kperm_variant_ext.
  apply kperm_check_amo.
Qed.

(* the class-keyed dispatcher (the 4-way access disjunction is SRegime's
   [s_acc_ok], inlined -- SRegime sits above this file) *)
Lemma kperm_variant_check (ppn : mword 44) (pc : kperm)
    (acc : MemoryAccessType mem_payload) (a d : mword 1) (mxr do_sum : bool) :
  (acc = InstructionFetch tt \/ acc = Load Data \/ acc = Store Data \/
   acc = Atomic (AMOSWAP, Data, Data)) ->
  kperm_allows pc acc ->
  pte_check_ok acc Supervisor mxr do_sum (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d).
Proof.
  intros Hacc Hall s. unfold Mk_PTE_Flags.
  rewrite kperm_variant_flags. rewrite kperm_variant_ext.
  apply kperm_check; assumption.
Qed.

(* update_PTE_Bits: no write-back is needed exactly when A (and D, for
   stores) is already set in the variant *)



(* ===================================================================== *)
(* §2b The TRAMPOLINE leaf.  The kernel table (and every user table) maps  *)
(*     [tramp_vpn] to the kernel-text trampoline page with X|R U=0 flags;  *)
(*     as everywhere in the tree layer, the leaf is kept modulo A/D.       *)
(* ===================================================================== *)

Definition pte_tramp : mword 64 := mk_pte tramp_ppn PTE_TRAMP.

Lemma tramp_variant_flags (a d : mword 1) :
  subrange_vec_dec (pte_set_ad pte_tramp a d) 7 0
  = (mword_of_int (Z.lor (Z.land PTE_TRAMP 831)
       (Z.lor (Z.shiftl (bv_unsigned a) 6) (Z.shiftl (bv_unsigned d) 7))) : mword 8).
Proof.
  unfold pte_tramp, mk_pte.
  rewrite (pte_set_ad_zext_concat tramp_ppn PTE_TRAMP a d ltac:(unfold PTE_TRAMP; lia)).
  apply mk_pte_flags.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute; intuition congruence.
Qed.

Lemma tramp_variant_ext (a d : mword 1) :
  ext_bits_of_PTE (pte_set_ad pte_tramp a d) = Mk_PTE_Ext (mword_of_int 0).
Proof.
  rewrite pte_set_ad_ext.
  unfold pte_tramp.
  unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
  rewrite mk_pte_ext; [reflexivity | unfold PTE_TRAMP; lia].
Qed.

Lemma tramp_variant_ppn (a d : mword 1) :
  autocast (T := mword) ((autocast (T := mword)
     (PPN_of_PTE (pte_set_ad pte_tramp a d : mword 64))) : mword 44)
  = tramp_ppn.
Proof.
  rewrite !autocast_id.
  rewrite pte_set_ad_ppn.
  unfold pte_tramp, PPN_of_PTE.
  change (Z.eqb 64 32) with false. cbv iota.
  rewrite autocast_id.
  apply mk_pte_ppn_field. unfold PTE_TRAMP; lia.
Qed.

Lemma tramp_variant (a d : mword 1) :
  pte_valid (pte_set_ad pte_tramp a d) /\ pte_leaf (pte_set_ad pte_tramp a d) /\
  pte_no_napot (pte_set_ad pte_tramp a d) /\ pte_pbmt0 (pte_set_ad pte_tramp a d).
Proof.
  repeat split.
  - intros s. unfold Mk_PTE_Flags.
    rewrite tramp_variant_flags. rewrite tramp_variant_ext.
    destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
      vm_compute; reflexivity.
  - unfold pte_leaf, Mk_PTE_Flags.
    rewrite tramp_variant_flags.
    destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
      vm_compute; reflexivity.
  - unfold pte_no_napot.
    rewrite tramp_variant_ext.
    apply kpt_extN_red.
  - unfold pte_pbmt0.
    rewrite tramp_variant_ext.
    vm_compute. reflexivity.
Qed.

(* the S-mode fetch check passes on any A/D variant of the trampoline leaf *)
Lemma tramp_variant_check_fetch (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (InstructionFetch tt) Supervisor mxr do_sum
    (pte_set_ad pte_tramp a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite tramp_variant_flags. rewrite tramp_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    destruct mxr, do_sum; vm_compute; reflexivity.
Qed.

(* the trampoline vpn sits at the top of the VA space, far above every
   kernel-mapped (DRAM / device) vpn *)

(* stage-C bridge: the trampoline's real table word [PTE_TRAMP = 0x4B] is
   the KP_rx class leaf modulo the A/D bits -- both mask to 0x0B under
   [pte_set_ad] -- so an ordinary M entry [tramp_vpn ↦ (tramp_ppn, KP_rx)]
   produces EXACTLY the [pte_tramp] variants the pt2 window machinery
   ([pt2_tramp_spec], TransPt) still expresses through [pte_tramp]. *)
Lemma kperm_rx_tramp_variant (a d : mword 1) :
  pte_set_ad (mk_pte tramp_ppn (kperm_flags KP_rx)) a d = pte_set_ad pte_tramp a d.
Proof.
  unfold pte_tramp, mk_pte.
  rewrite (pte_set_ad_zext_concat tramp_ppn (kperm_flags KP_rx) a d (kperm_flags_bound KP_rx)).
  rewrite (pte_set_ad_zext_concat tramp_ppn PTE_TRAMP a d ltac:(unfold PTE_TRAMP; lia)).
  assert (Hl : Z.land (kperm_flags KP_rx) 831 = Z.land PTE_TRAMP 831)
    by (vm_compute; reflexivity).
  rewrite Hl. reflexivity.
Qed.

(* ===================================================================== *)
(* §3 The layout-free kernel mapping spec.                                *)
(* ===================================================================== *)


(* the spec survives the ADUE write-back of any mapped vpn's leaf *)

(* ===================================================================== *)
(* §3b THE GENERALIZED (M-INDEXED) MAPPING SPEC (rwx-kmap).  The region   *)
(*     clauses collapse into ONE per-vpn match over the kernel-mapping    *)
(*     map M (KMap.v's auth): text/data/device identity leaves, dynamic   *)
(*     kstack leaves AND the trampoline are all just entries of M, each   *)
(*     mapped as an A/D variant of its class-keyed PTE; every vpn outside *)
(*     M BLOCKS (stage C: the dedicated trampoline clause is gone).       *)
(* ===================================================================== *)

Definition kpt_leaf_pte_of (vpn : mword 27) (e : mword 44 * kperm) : mword 64 :=
  mk_pte e.1 (kperm_flags e.2).

(* THE final one-clause form (uniform-claims stage C): for every vpn,
   the tree agrees with M -- an M entry is mapped as an A/D variant of
   its class-keyed PTE, everything else BLOCKS.  The blocks direction is
   what makes the invariant characterize the table EXACTLY (and is the
   real guard on kmap_insert: an entry can only enter M because
   re-establishing the invariant forces the physical table to map it).
   The TRAMPOLINE is an ordinary M entry (tramp_vpn ↦ (tramp_ppn, KP_rx),
   minted at the boot switch): pte_set_ad (mk_pte tramp_ppn 0xCB) 1 0 IS
   the real table's 0x4B trampoline word, so the old dedicated clause
   and the pte_tramp/tramp_variant family are subsumed by the
   kperm_variant_* lemmas at KP_rx. *)
Definition kpt_tree_spec_gen (root : mword 44)
    (M : gmap (mword 27) (mword 44 * kperm)) (t : ptree) : Prop :=
  pt_base t = root /\
  (forall vpn,
     match M !! vpn with
     | Some e =>
         exists p2 p1 (a d : mword 1),
           ptree_maps t vpn p2 p1 (pte_set_ad (kpt_leaf_pte_of vpn e) a d)
     | None => ptree_blocks t vpn
     end).

(* the generalized spec survives the ADUE write-back of any M-mapped
   vpn's leaf -- ONE lemma for every entry, the trampoline included
   (stage C: no tramp premise, no tramp case) *)
Lemma kpt_tree_spec_gen_set_leaf (root : mword 44)
    (M : gmap (mword 27) (mword 44 * kperm)) (t : ptree)
    (vpn : mword 27) (e : mword 44 * kperm)
    (p2 p1 p0 : mword 64) (a d : mword 1) :
  kpt_tree_spec_gen root M t ->
  ptree_maps t vpn p2 p1 p0 ->
  M !! vpn = Some e ->
  (exists a0 d0 : mword 1, p0 = pte_set_ad (kpt_leaf_pte_of vpn e) a0 d0) ->
  kpt_tree_spec_gen root M (ptree_set_leaf t vpn (pte_set_ad p0 a d)).
Proof.
  intros (Hbase & Hall) Hmaps He (a0 & d0 & Hp0).
  assert (Hvar : pte_set_ad p0 a d = pte_set_ad (kpt_leaf_pte_of vpn e) a d).
  { rewrite Hp0. apply pte_set_ad_absorb. }
  split.
  - rewrite <- Hbase.
    unfold ptree_set_leaf.
    destruct (pt_kids t (vpn_idx 2 vpn)); [| reflexivity].
    destruct (pt_kids p (vpn_idx 1 vpn)); reflexivity.
  - intros vpn'.
    destruct (decide (vpn' = vpn)) as [-> | Hne].
    + rewrite He.
      exists p2, p1, a, d.
      rewrite <- Hvar.
      apply (ptree_set_leaf_maps_self t vpn p2 p1 p0); [exact Hmaps | ..];
        rewrite Hvar; unfold kpt_leaf_pte_of.
      * apply kperm_variant_valid.
      * apply kperm_variant_leaf.
      * apply kperm_variant_no_napot.
      * apply kperm_variant_pbmt0.
    + specialize (Hall vpn').
      destruct (M !! vpn') as [e' |] eqn:He'.
      * destruct Hall as (q2 & q1 & a' & d' & Hm2).
        exists q2, q1, a', d'.
        apply (ptree_set_leaf_maps_other t vpn vpn' _ _ _ _ Hne Hm2).
      * apply (ptree_set_leaf_blocks t vpn vpn' p2 p1 p0); [exact Hmaps |].
        exact Hall.
Qed.

(* ===================================================================== *)
(* §3d PT-SLOT TIER BRIDGE (uniform-claims PHYSICAL TIER, item 1).         *)
(*                                                                        *)
(* A PT node owns its 512 slot words PHYSICALLY ([↦ₚ₈], through           *)
(* [ptree_own]/[pt_page_own]), but the S-mode walk code reads/writes a    *)
(* slot through TRANSLATION and needs the VA-tier [↦₈].  For the kernel   *)
(* PT the node page is identity-mapped kdata, so a slot address           *)
(* [u_pte_addr b idx] translates to itself -- and the node carries its    *)
(* OWN identity claim ([pt_node_claim b], inside [pt_page_own]), which is  *)
(* everything the byte-level [phys_to_mem_claim]/[mem_to_phys_claim] need. *)
(* So the walk converts a slot word [↦ₚ₈ ⇄ ↦₈] LOCALLY, threading nothing *)
(* but the tree ownership.  ([svpn_of_pa_add]/[pa_of_pa_add] carry the    *)
(* per-byte facts across the 8-byte window; [pte_addr_at_unsigned] pins   *)
(* the slot's page offset to [idx*8 < 4096].)                             *)
(* ===================================================================== *)

Section PtSlotBridge.
  Context `{!riscvGS Σ}.

  (* svpn of a within-page address is its ppn field: [x = b*4096 + r],
     [0 <= r < 4096], canonical *)
  Local Lemma svpn_of_page (x : mword 64) (b : mword 44) (r : Z) :
    (0 <= r < 4096)%Z ->
    bv_unsigned x = bv_unsigned b * 4096 + r ->
    (uint x < 274877906944)%Z ->
    bv_unsigned (svpn_of x) = bv_unsigned b.
  Proof.
    intros Hr Hx Hcan.
    rewrite (svpn_of_unsigned_lo x Hcan). rewrite uint_unsigned Hx.
    rewrite Z.shiftr_div_pow2; [| lia]. change (2 ^ 12) with 4096.
    rewrite Z.div_add_l; [| lia].
    rewrite (Z.div_small r 4096 Hr). lia.
  Qed.

  (* the per-byte discharge for a slot [u_pte_addr b idx], byte offset
     [j < 8]: [pa_of]-identity, ram, canonicality and svpn-constancy,
     all from the node's [node_kdata b]. *)
  Lemma u_pte_slot_facts (b : mword 44) (idx : mword 9) (j : nat) :
    node_kdata b -> (j < 8)%nat ->
    pa_of b (pa_add (u_pte_addr b idx) j) = pa_add (u_pte_addr b idx) j /\
    addr_is_ram (pa_add (u_pte_addr b idx) j) /\
    (uint (pa_add (u_pte_addr b idx) j) < 274877906944)%Z /\
    svpn_of (pa_add (u_pte_addr b idx) j) = pt_page_vpn b.
  Proof.
    intros [Hklo Hkhi] Hj.
    assert (Ha : bv_unsigned (u_pte_addr b idx) = bv_unsigned b * 4096 + bv_unsigned idx * 8)
      by exact (pte_addr_at_unsigned b idx).
    pose proof (pt_bv9_range idx) as Hidxr.
    unfold node_kdata in *. unfold ram_base, ram_size in Hklo, Hkhi.
    (* the shifted address is in the SAME page: unsigned is b*4096 + idx*8 + j *)
    assert (Hpaj : bv_unsigned (pa_add (u_pte_addr b idx) j)
                   = bv_unsigned b * 4096 + bv_unsigned idx * 8 + Z.of_nat j).
    { unfold pa_add. rewrite pt_add_vec_int_small.
      - rewrite Ha. reflexivity.
      - lia.
      - rewrite Ha. lia. }
    assert (Hram : addr_is_ram (pa_add (u_pte_addr b idx) j)).
    { unfold addr_is_ram, ram_base, ram_size.
      rewrite uint_unsigned Hpaj. lia. }
    assert (Hcanpa : (uint (pa_add (u_pte_addr b idx) j) < 274877906944)%Z).
    { rewrite uint_unsigned Hpaj. lia. }
    (* canonicality of the page base (idx = 0) for [pt_page_vpn] *)
    assert (Ha0 : bv_unsigned (u_pte_addr b (mword_of_int 0)) = bv_unsigned b * 4096).
    { rewrite (pte_addr_at_unsigned b (mword_of_int 0)).
      replace (bv_unsigned (mword_of_int 0 : mword 9)) with 0 by (vm_compute; reflexivity). lia. }
    assert (Hcana0 : (uint (u_pte_addr b (mword_of_int 0)) < 274877906944)%Z).
    { rewrite uint_unsigned Ha0. lia. }
    split; [| split; [exact Hram | split; [exact Hcanpa |]]].
    - (* pa_of b (pa_add a j) = pa_add a j *)
      apply bv_eq. unfold pa_of. rewrite zext64_concat44_12_unsigned.
      rewrite subrange64_unsigned_11_0. change (2 ^ 12) with 4096.
      rewrite Hpaj.
      replace (bv_unsigned b * 4096 + bv_unsigned idx * 8 + Z.of_nat j)
        with ((bv_unsigned idx * 8 + Z.of_nat j) + bv_unsigned b * 4096) by lia.
      rewrite Z_mod_plus_full.
      rewrite (Z.mod_small (bv_unsigned idx * 8 + Z.of_nat j) 4096 ltac:(lia)). lia.
    - (* svpn_of (pa_add a j) = pt_page_vpn b *)
      apply bv_eq. unfold pt_page_vpn.
      rewrite (svpn_of_page (pa_add (u_pte_addr b idx) j) b (bv_unsigned idx * 8 + Z.of_nat j)
                 ltac:(lia) ltac:(rewrite Hpaj; lia) Hcanpa).
      rewrite (svpn_of_page (u_pte_addr b (mword_of_int 0)) b 0
                 ltac:(lia) ltac:(rewrite Ha0; lia) Hcana0).
      reflexivity.
  Qed.

  (* the word-level ↦ₚ₈ → ↦₈ bridge for a PT slot, from the node's claim *)
  Lemma pt_slot_phys_to_mem (b : mword 44) (idx : mword 9) (dq : dfrac) (w : mword 64) :
    pt_node_claim b -∗
    u_pte_addr b idx ↦ₚ₈{dq} w -∗
    u_pte_addr b idx ↦₈{dq} w.
  Proof.
    iIntros "(%Hkd & %Hpv & #Hk) Hw".
    iApply word_pointsto_intro; [exact (pte_addr_at_aligned8 b idx) |].
    iDestruct (phys_word_pointsto_bytes with "Hw") as "Hbs".
    iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (k j Hkj) "Hp".
    apply lookup_seq in Hkj. destruct Hkj as [-> Hjlt].
    destruct (u_pte_slot_facts b idx (0 + k)%nat Hkd ltac:(lia)) as (Hid & Hram & Hcan & Hsvpn).
    iAssert (kmap_at (svpn_of (pa_add (u_pte_addr b idx) (0 + k))) b KP_rw) as "#Hk'".
    { rewrite Hsvpn. iExact "Hk". }
    iApply (phys_to_mem_claim (pa_add (u_pte_addr b idx) (0 + k)) b dq (nth_byte w (0 + k))
              Hid Hram Hcan with "Hk' Hp").
  Qed.

  (* the reverse ↦₈ → ↦ₚ₈ (walk restores the physical slot after its load /
     stores the rewritten leaf word) *)
  Lemma pt_slot_mem_to_phys (b : mword 44) (idx : mword 9) (dq : dfrac) (w : mword 64) :
    pt_node_claim b -∗
    u_pte_addr b idx ↦₈{dq} w -∗
    u_pte_addr b idx ↦ₚ₈{dq} w.
  Proof.
    iIntros "(%Hkd & %Hpv & #Hk) Hw".
    iApply phys_word_pointsto_intro; [exact (pte_addr_at_aligned8 b idx) |].
    iDestruct (word_pointsto_bytes with "Hw") as "Hbs".
    iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (k j Hkj) "Hp".
    apply lookup_seq in Hkj. destruct Hkj as [-> Hjlt].
    destruct (u_pte_slot_facts b idx (0 + k)%nat Hkd ltac:(lia)) as (Hid & _ & _ & Hsvpn).
    iAssert (kmap_at (svpn_of (pa_add (u_pte_addr b idx) (0 + k))) b KP_rw) as "#Hk'".
    { rewrite Hsvpn. iExact "Hk". }
    iApply (mem_to_phys_claim (pa_add (u_pte_addr b idx) (0 + k)) b dq (nth_byte w (0 + k))
              Hid with "Hk' Hp").
  Qed.

  (* build a fresh node's [pt_node_claim] from the static-claims bundle: a
     kalloc page is a kdata page ([node_kdata b]) and is identity-mapped, so
     its page-vpn's static claim is the node's own claim.  Every caller
     ([zero_page_to_node]'s in ProofWalk, uvmcreate's and kvmmake's root)
     has just taken the page out of kalloc, so the SINGLE premise it needs
     is kalloc's own [page_valid] -- [node_kdata] and the [text_end] bound
     both follow ([PtTree.page_valid_node_kdata]).  [page_valid] is also
     what the claim now RECORDS, so freewalk can hand the node back to
     kfree. *)
  Lemma pt_node_claim_from_static (b : mword 44) :
    page_valid (page_base b) ->
    kmap_static_claims -∗ pt_node_claim b.
  Proof.
    intros Hpv. iIntros "#Hb".
    destruct (page_valid_node_kdata b Hpv) as (Hkd & Hkda).
    pose proof Hkd as [Hlo Hhi].
    unfold text_end, ram_base, ram_size in Hlo, Hhi, Hkda.
    assert (Ha0 : bv_unsigned (u_pte_addr b (mword_of_int 0)) = bv_unsigned b * 4096).
    { rewrite (pte_addr_at_unsigned b (mword_of_int 0)).
      replace (bv_unsigned (mword_of_int 0 : mword 9)) with 0 by (vm_compute; reflexivity). lia. }
    assert (Hkda0 : addr_is_kdata (u_pte_addr b (mword_of_int 0))).
    { unfold addr_is_kdata, text_end, ram_base, ram_size. rewrite uint_unsigned Ha0. lia. }
    assert (Hcana0 : (uint (u_pte_addr b (mword_of_int 0)) < 274877906944)%Z).
    { rewrite uint_unsigned Ha0. lia. }
    assert (Hstat : kmap_static (svpn_of (u_pte_addr b (mword_of_int 0))) KP_rw)
      by (apply kdata_svpn_class; exact Hkda0).
    assert (Hleaf : kpt_leaf_ppn (pt_page_vpn b) = b).
    { apply bv_eq. unfold kpt_leaf_ppn, pt_page_vpn. rewrite zext44_27_unsigned.
      rewrite (svpn_of_page (u_pte_addr b (mword_of_int 0)) b 0
                 ltac:(lia) ltac:(rewrite Ha0; lia) Hcana0). reflexivity. }
    rewrite /pt_node_claim. iSplitR; [iPureIntro; exact Hkd |].
    iSplitR; [iPureIntro; exact Hpv |].
    iDestruct (kmap_static_claims_at (pt_page_vpn b) KP_rw Hstat with "Hb") as "#Hk".
    rewrite Hleaf. iExact "Hk".
  Qed.

End PtSlotBridge.

(* ===================================================================== *)
(* §4 THE GENERALIZED KERNEL TRANSLATION INVARIANT.  Same satp / PMP      *)
(*    bundling as [tlb_inv], but the page table is owned as a TREE with   *)
(*    arbitrary A/D bits and the TLB is consistent MODULO A/D.            *)
(* ===================================================================== *)

Section KptTreeInv.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* The generalized invariant (rwx-kmap): the table is constrained by the
     M-INDEXED spec [kpt_tree_spec_gen], and the kernel-mapping auth
     [kmap_auth M] (KMap.v) rides inside.  The signature keeps only
     [root_ppn] -- M is existential -- so [intr_frame]/[strans_inv] and
     every other carrier is unchanged. *)
  Definition tlb_inv_pt (root_ppn : mword 44) : iProp Σ :=
    (∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t : ptree)
       (M : gmap (mword 27) (mword 44 * kperm)),
       satp ↦ᵣ satp0 ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt (mword_of_int 0) t tlbvec ⌝ ∗
       ⌜ kpt_tree_spec_gen root_ppn M t ⌝ ∗
       kmap_auth M ∗
       ptree_own 2 (DfracOwn 1) t ∗
       pmp_config root_ppn)%I.

  Lemma tlb_inv_pt_intro (root_ppn : mword 44) (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t : ptree)
      (M : gmap (mword 27) (mword 44 * kperm)) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    kpt_tree_spec_gen root_ppn M t ->
    satp ↦ᵣ satp0 -∗ tlb ↦ᵣ tlbvec -∗ kmap_auth M -∗
    ptree_own 2 (DfracOwn 1) t -∗
    pmp_config root_ppn -∗
    tlb_inv_pt root_ppn.
  Proof.
    intros Hmode Hasid Hppn Hok Hspec. iIntros "Hsatp Htlb HM Ht Hpmp".
    iExists satp0, tlbvec, t, M. iFrame "Hsatp Htlb HM Ht Hpmp". iPureIntro. tauto.
  Qed.

  Lemma tlb_inv_pt_open (root_ppn : mword 44) :
    tlb_inv_pt root_ppn -∗
    ∃ (satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t : ptree)
      (M : gmap (mword 27) (mword 44 * kperm)),
      satp ↦ᵣ satp0 ∗
      ⌜ _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ⌝ ∗
      tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt (mword_of_int 0) t tlbvec ⌝ ∗
      ⌜ kpt_tree_spec_gen root_ppn M t ⌝ ∗
      kmap_auth M ∗
      ptree_own 2 (DfracOwn 1) t ∗
      pmp_config root_ppn.
  Proof. iIntros "H". iExact "H". Qed.

End KptTreeInv.

(* the variant leaf's output ppn is the identity leaf ppn *)

(* ... and for the class-keyed leaf with ARBITRARY ppn (rwx-kmap) *)
Lemma kperm_variant_ppn' (ppn : mword 44) (pc : kperm) (a d : mword 1) :
  autocast (T := mword) ((autocast (T := mword)
     (PPN_of_PTE (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d : mword 64))) : mword 44)
  = ppn.
Proof.
  rewrite !autocast_id.
  rewrite pte_set_ad_ppn.
  unfold PPN_of_PTE.
  change (Z.eqb 64 32) with false. cbv iota.
  rewrite autocast_id.
  apply mk_pte_ppn_field.
  pose proof (kperm_flags_bound pc). lia.
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
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  (* shared miss path: the TLB slot misses (empty or foreign), so the walk
     runs -- filling cleanly (O2) or writing the A/D update back (O3) *)
  Lemma ptree_translate_miss_core (root_ppn : mword 44) (va w : mword 64)
        (tlbvec : vec (option TLB_Entry) (2 ^ 6))
        (p2 p1 : mword 64) (a0 d0 : mword 1) (σ : mstate) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc p mxr do_sum (pte_set_ad w a d)) ->
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
         exec (translate 39 (mword_of_int 0 : mword 16) root_ppn vpn acc p mxr do_sum tt) σ
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
    intros vpn p0 Hchk Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
           Hrd2 Hrd1 Hrd0 Hmisa Hmenv Hhtif Htlb Hlk
           HA Hord HW Hcov Hpmaw.
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
        apply (exec_translate_TLB_miss_pt_upd acc p mxr do_sum
                 vpn root_ppn p2 p1 p0 p0' MENVCFG_S (mword_of_int 0) _ σ
                 Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap
                 (Hchk a0 d0 mxr do_sum) Hup
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
        apply (exec_translate_TLB_miss_user vpn root_ppn p2 p1 p0 acc p mxr do_sum
                 Hv2 Hn2 Hv1 Hn1 Hv0 Hl0
                 (Hchk a0 d0 mxr do_sum) Hnap
                 (mword_of_int 0) MENVCFG_S σ Hmisa Hupd Hrd2 Hrd1 Hrd0 Hmenv HPBMTE).
      + left. rewrite Htlb. reflexivity.
  Qed.

End KptTranslate.

Section KptTranslateAddr.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  Lemma ptree_translateAddr_cases (root_ppn : mword 44) (va w pa satp0 : mword 64)
        (t : ptree) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
        (p2 p1 : mword 64) (a0 d0 : mword 1) (σ : mstate) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc p mxr do_sum (pte_set_ad w a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d)) ->
    pt_base t = root_ppn ->
    ptree_maps t vpn p2 p1 p0 ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    pt_slot_mem σ (pt_addr2 t vpn) p2 ->
    pt_slot_mem σ (pt_addr1 p2 vpn) p1 ->
    pt_slot_mem σ (pt_addr0 p1 vpn) p0 ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = p ->
    exec (translationMode p) σ = Some (Sv39, σ) ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) p) σ
      = Some (p, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    register_lookup satp σ.(sregs) = satp0 ->
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
      = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ')
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
    intros vpn p0 Hchk Hcanon Hout Hvarp Hbase Hmaps Htlbok Hsm2 Hsm1 Hsm0
           Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatp Hppn Hasid Htlb
           HA Hord HR HW Hcov Hpmar Hpmaw.
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
              (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { unfold p0. rewrite pte_set_ad_ppn. exact Hout. }
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
                  pte_check_ok acc p mxr do_sum (pte_set_ad p0 a' d')).
        { intros mxr do_sum.
          assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w a0 d0 a' d').
          rewrite Habs. exact (Hchk a' d' mxr do_sum). }
        assert (Hpbc : pte_pbmt0 (pte_set_ad p0 a' d')).
        { assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
            by exact (pte_set_ad_absorb w a0 d0 a' d').
          rewrite Habs. apply Hvarp. }
        assert (Hidc : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
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
          { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                     (autocast (T := mword) ((autocast (T := mword)
                        (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                     satp0 va pa σ _
                     Heff Hss Hcp Htm Hsatp Hppn Hasid
                     Hcanon eq_refl).
            2:{ exact Hidc. }
            intros mxr do_sum.
            unfold translate.
            rewrite (exec_bind_Some _ _ _ _ _
                       (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                          (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
            cbn match.
            apply (exec_translate_TLB_hit_pt_upd acc p mxr do_sum
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
          { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                     (autocast (T := mword) ((autocast (T := mword)
                        (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                     satp0 va pa σ _
                     Heff Hss Hcp Htm Hsatp Hppn Hasid
                     Hcanon eq_refl).
            2:{ exact Hidc. }
            intros mxr do_sum.
            unfold translate.
            rewrite (exec_bind_Some _ _ _ _ _
                       (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ σ Htlb Hslot
                          (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d')))).
            cbn match.
            apply (exec_translate_TLB_hit_pt acc p mxr do_sum
                     vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                     (tlb_hash (__id 39) vpn) σ
                     (Hchkc mxr do_sum) Hupq' Hpbc). }
          left. reflexivity.
      + (* foreign entry: rejected by the tag, so the walk runs *)
        assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
          by exact (exec_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec σ Htlb Hslot
                      (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad qp0 a' d')
                         (mword_of_int 0) Hne)).
        destruct (ptree_translate_miss_core acc p root_ppn va w tlbvec p2 p1 a0 d0 σ Hchk
                    Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                    Hrd2 Hrd1 Hrd0 Hmisa Hmenv Hhtif Htlb Hlk
                    HA Hord HW Hcov Hpmaw)
          as (σ' & Htr & Hshape).
        exists σ'. split.
        { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                   (autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (p0 : mword 64))) : mword 44))
                   satp0 va pa σ σ'
                   Heff Hss Hcp Htm Hsatp Hppn Hasid
                   Hcanon eq_refl Htr Hid). }
        destruct Hshape as [Ho2 | Ho3]; [right; left; exact Ho2 | right; right; exact Ho3].
    - (* empty slot: the walk runs *)
      assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) σ = Some (None, σ))
        by exact (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec σ Htlb Hslot).
      destruct (ptree_translate_miss_core acc p root_ppn va w tlbvec p2 p1 a0 d0 σ Hchk
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                  Hrd2 Hrd1 Hrd0 Hmisa Hmenv Hhtif Htlb Hlk
                  HA Hord HW Hcov Hpmaw)
        as (σ' & Htr & Hshape).
      exists σ'. split.
      { apply (exec_translateAddr_pt_front acc p vpn root_ppn
                 (autocast (T := mword) ((autocast (T := mword)
                    (PPN_of_PTE (p0 : mword 64))) : mword 44))
                 satp0 va pa σ σ'
                 Heff Hss Hcp Htm Hsatp Hppn Hasid
                 Hcanon eq_refl Htr Hid). }
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

Section PtTranslateOwn.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  (* THE GENERIC ABSORPTION CORE, over the raw pieces: any owned tree, any
     canonical leaf [w] mapped at [va]'s vpn as an A/D variant, any output
     page [pa].  Translation succeeds at [pa]; the tree and the TLB move by
     at most a fill or the Svadu A/D write-back, tracked in the returned
     [t']/[tlbvec'] with consistency re-established.  The kernel and user
     page-table invariants both instantiate this. *)
  Lemma ptree_translateAddr_own (root_ppn : mword 44) (t : ptree)
      (w va pa satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (p2 p1 : mword 64) (a0 d0 : mword 1) (σ : mstate) :
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc p mxr do_sum (pte_set_ad w a d)) ->
    (forall a d : mword 1,
       pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
       pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    pt_base t = root_ppn ->
    ptree_maps t (svpn_of va) p2 p1 (pte_set_ad w a0 d0) ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = p ->
    exec (translationMode p) σ = Some (Sv39, σ) ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) p) σ
      = Some (p, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    register_lookup satp σ.(sregs) = satp0 ->
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
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗
    tlb ↦ᵣ tlbvec -∗ ptree_own 2 (DfracOwn 1) t ==∗
    ∃ (σ' : mstate) (t' : ptree) (tlbvec' : vec (option TLB_Entry) (2 ^ 6)),
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      ⌜ (t' = t \/ exists (a1 d1 : mword 1),
           t' = ptree_set_leaf t (svpn_of va) (pte_set_ad w a1 d1))%type ⌝ ∗
      ⌜ tlb_ok_pt (mword_of_int 0) t' tlbvec' ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗
      tlb ↦ᵣ tlbvec' ∗ ptree_own 2 (DfracOwn 1) t'.
  Proof.
    intros Hchk Hvar Hcanon Hout Hbase Hmaps Htlbok
           Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatpv Hppn Hasid Htlbv
           HA' Hord' HR' HW' Hcov' Hpmar Hpmaw.
    iIntros "Hri Hgh Htlb Ht".
    set (vpn := svpn_of va) in *.
    iDestruct (ptree_own_path_mem σ (DfracOwn 1) t vpn p2 p1 _ Hmaps with "Hgh Ht")
      as %(Hsm2 & Hsm1 & Hsm0).
    assert (Hvarp : forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d))
      by (intros a d; exact (proj2 (proj2 (proj2 (Hvar a d))))).
    destruct (ptree_translateAddr_cases acc p root_ppn va w pa satp0 t tlbvec p2 p1 a0 d0 σ
                Hchk Hcanon Hout Hvarp Hbase Hmaps Htlbok Hsm2 Hsm1 Hsm0
                Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatpv Hppn Hasid Htlbv
                HA' Hord' HR' HW' Hcov' Hpmar Hpmaw)
      as (σ' & Htrans & Hshape).
    destruct Hshape as [-> | [ -> | (a1 & d1 & ->) ]].
    - (* O1: nothing moved *)
      iModIntro. iExists σ, t, tlbvec.
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; left; reflexivity |].
      iSplit; [iPureIntro; left; reflexivity |].
      iSplit; [iPureIntro; exact Htlbok |].
      iFrame "Hri Hgh Htlb Ht".
    - (* O2: TLB fill with the current leaf *)
      iMod (reg_update σ.(sregs) tlb tlbvec
              (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (u_walk_entry vpn p2 p1 (pte_set_ad w a0 d0) (mword_of_int 0))))
              with "Hri Htlb") as "[Hri Htlb]".
      iModIntro.
      iExists (set_reg σ tlb (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (u_walk_entry vpn p2 p1 (pte_set_ad w a0 d0) (mword_of_int 0))))),
              t,
              (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (u_walk_entry vpn p2 p1 (pte_set_ad w a0 d0) (mword_of_int 0)))).
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iSplit; [iPureIntro; left; reflexivity |].
      iSplit; [iPureIntro;
        exact (tlb_ok_pt_fill_self (mword_of_int 0) t tlbvec vpn p2 p1 _ Hmaps Htlbok) |].
      iFrame "Hri Hgh Htlb Ht".
    - (* O3: the Svadu write-back, absorbed *)
      set (p0 := pte_set_ad w a0 d0) in *.
      set (w' := pte_set_ad p0 a1 d1) in *.
      assert (Habs : w' = pte_set_ad w a1 d1)
        by exact (pte_set_ad_absorb w a0 d0 a1 d1).
      assert (Hv' : pte_valid w') by (rewrite Habs; exact (proj1 (Hvar a1 d1))).
      assert (Hl' : pte_leaf w') by (rewrite Habs; exact (proj1 (proj2 (Hvar a1 d1)))).
      assert (Hn' : pte_no_napot w')
        by (rewrite Habs; exact (proj1 (proj2 (proj2 (Hvar a1 d1))))).
      assert (Hp' : pte_pbmt0 w')
        by (rewrite Habs; exact (proj2 (proj2 (proj2 (Hvar a1 d1))))).
      iDestruct (ptree_own_path_upd (DfracOwn 1) t vpn p2 p1 p0 Hmaps with "Ht")
        as "(Hs2 & Hs1 & Hs0 & Hrest)".
      iMod (phys_word_pointsto_write σ.(mem) (pt_addr0 p1 vpn) p0 w' with "Hgh Hs0")
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
                        (Some (u_walk_entry vpn p2 p1 w' (mword_of_int 0))))),
              (ptree_set_leaf t vpn w'),
              (vec_update_dec tlbvec (tlb_hash (__id 39) vpn)
                 (Some (u_walk_entry vpn p2 p1 w' (mword_of_int 0)))).
      cbn [set_reg sregs mem mdev].
      iSplit; [iPureIntro; exact Htrans |].
      iSplit; [iPureIntro; reflexivity |].
      iSplit; [iPureIntro; right; eexists; reflexivity |].
      iSplit; [iPureIntro; right; exists a1, d1; rewrite <- Habs; reflexivity |].
      iSplit; [iPureIntro;
        exact (tlb_ok_pt_fill_self (mword_of_int 0) (ptree_set_leaf t vpn w') tlbvec
                 vpn p2 p1 w'
                 (ptree_set_leaf_maps_self t vpn p2 p1 p0 w' Hmaps Hv' Hl' Hn' Hp')
                 (tlb_ok_pt_set_leaf (mword_of_int 0) t tlbvec vpn p2 p1 p0 a1 d1
                    Hmaps Hv' Hl' Hn' Hp' Htlbok)) |].
      iFrame "Hri Hgh Htlb Ht".
  Qed.

End PtTranslateOwn.

Section KptTranslateIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload).

  (* THE re-keyed absorption (rwx-kmap): keyed on a kernel-mapping CLAIM
     [kmap_at (svpn_of va) ppn pc] instead of blanket [addr_is_ram]; the
     output pa is the claim's ppn re-concatenated with the page offset
     (identity consumers instantiate ppn := kpt_leaf_ppn (svpn_of va) and
     pa := va via [ram_ident_4k]).  Single-path: both claim arms land in
     the same M-clause leaf via [kmap_at_lookup]. *)
  Lemma tlb_inv_pt_translateAddr_at (root_ppn : mword 44) (va pa : mword 64)
      (ppn : mword 44) (pc : kperm) (σ : mstate) :
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum
         (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d)) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    kmap_at (svpn_of va) ppn pc -∗
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ tlb_inv_pt root_ppn ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ tlb_inv_pt root_ppn.
  Proof.
    intros Hchk Hcanon Hid4k Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    iIntros "Hat Hri Hgh Hinv".
    iDestruct "Hinv" as (satp0 tlbvec t M)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & HM & Ht & Hpmp)".
    iDestruct (kmap_at_lookup with "HM Hat") as %HMlk.
    pose proof (pma_allows_all_pte_write _ Hall) as Hpmaw.
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    set (vpn := svpn_of va) in *.
    pose proof Hspec as (Hbase & Hmapspec).
    pose proof (Hmapspec vpn) as Hmapv. rewrite HMlk in Hmapv.
    destruct Hmapv as (p2 & p1 & a0 & d0 & Hmaps).
    assert (Hlf : kpt_leaf_pte_of vpn (ppn, pc) = mk_pte ppn (kperm_flags pc))
      by reflexivity.
    rewrite Hlf in Hmaps.
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
    pose proof (pma_allows_all_pte_read _ Hall) as Hpmar.
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (mk_pte ppn (kperm_flags pc) : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (kperm_variant_ppn' ppn pc ('b"1") ('b"1")) in Hid4k.
      rewrite pte_set_ad_ppn in Hid4k. exact Hid4k. }
    assert (Hvar : forall a d : mword 1,
       pte_valid (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d) /\
       pte_leaf (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d) /\
       pte_no_napot (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d) /\
       pte_pbmt0 (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d)).
    { intros a d. repeat split.
      - apply kperm_variant_valid.
      - apply kperm_variant_leaf.
      - apply kperm_variant_no_napot.
      - apply kperm_variant_pbmt0. }
    assert (Htm : exec (translationMode Supervisor) σ = Some (Sv39, σ))
      by exact (exec_translationMode_S_sv39 satp0 σ HSXL Hsatpv Hmode).
    iMod (ptree_translateAddr_own acc Supervisor root_ppn t
            (mk_pte ppn (kperm_flags pc)) va pa satp0
            tlbvec p2 p1 a0 d0 σ
            Hchk Hvar Hcanon Hout Hbase Hmaps Htlbok
            Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatpv Hppn Hasid Htlbv
            HA' Hord' HR' HW' Hcov' Hpmar Hpmaw
            with "Hri Hgh Htlb Ht")
      as (σ' t' tlbvec') "(%Htrans & %Hmdev & %Hsregs & %Htsh & %Htlbok' & Hri & Hgh & Htlb & Ht)".
    iModIntro. iExists σ'.
    iSplit; [iPureIntro; exact Htrans |].
    iSplit; [iPureIntro; exact Hmdev |].
    iSplit; [iPureIntro; exact Hsregs |].
    iFrame "Hri Hgh".
    assert (Hspec' : kpt_tree_spec_gen root_ppn M t').
    { destruct Htsh as [-> | (a1 & d1 & ->)]; [exact Hspec |].
      rewrite <- (pte_set_ad_absorb (mk_pte ppn (kperm_flags pc)) a0 d0 a1 d1).
      apply (kpt_tree_spec_gen_set_leaf root_ppn M t vpn (ppn, pc) p2 p1
               (pte_set_ad (mk_pte ppn (kperm_flags pc)) a0 d0) a1 d1
               Hspec Hmaps HMlk).
      exists a0, d0. rewrite Hlf. reflexivity. }
    iApply (tlb_inv_pt_intro root_ppn satp0 tlbvec' t' M
              Hmode Hasid Hppn Htlbok' Hspec' with "Hsatp Htlb HM Ht").
    iApply (pmp_config_intro root_ppn pmpcfg0 pmpaddr00
              HA Hord HX HW HR Hcov with "Hpc Hpa").
  Qed.

End KptTranslateIris.

(* Stage C: the dedicated trampoline translation lemmas
   ([tlb_inv_pt_translateAddr_tramp] and its [_fetch] wrapper) are GONE.
   The trampoline is an ordinary M entry [tramp_vpn ↦ (tramp_ppn, KP_rx)],
   so a trampoline-page fetch goes through the general
   [tlb_inv_pt_translateAddr_at] at [ppn := tramp_ppn], [pc := KP_rx],
   fed the claim [kmap_at tramp_vpn tramp_ppn KP_rx] (threaded up from the
   post-switch caller): see [ktramp_fetch_habs] in TrampStepPt. *)
