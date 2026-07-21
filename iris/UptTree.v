(* UptTree.v -- the USER page table over the general page-table tree
   abstraction (PtTree.v), mirroring the kernel's KptTree.v.

   A user-mode table (xv6 Sv39) maps exactly:
   - the TRAMPOLINE page (S-mode only, at TRAMPOLINE = top of VA space) to
     the kernel-text trampoline page -- the shared [pte_tramp] leaf;
   - the TRAPFRAME page (S-mode only, one page below) to the process's
     trapframe page [tfp] -- the [pte_tf tfp] leaf;
   - whatever user-accessible pages sit BELOW the trapframe -- an abstract
     finite map [um : gmap vpn leaf] from vpns to canonical leaf words.
   Everything else BLOCKS (faults).  As everywhere in the tree layer, every
   leaf is kept modulo the Svadu/ADUE A/D bits ([pte_set_ad] variants).

   [utlb_inv_pt uroot tfp um] is the [tlb_inv_pt] mirror: satp holds the
   user root, the TLB is consistent modulo A/D ([tlb_ok_pt]), the table is
   owned as a tree constrained only by the layout-free [upt_tree_spec], and
   the ambient PMP configuration rides along.  The absorption theorem
   instantiates the generic [ptree_translateAddr_own] core: an S-mode
   trampoline fetch or trapframe load/store (the userret / uservec paths)
   translates to the mapped physical page and the invariant absorbs
   whatever the walk did (nothing / TLB fill / A-D write-back). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import SmodePte.
Require Import PtAdBits.
Require Import Pt4kWalk.
Require Import PtTree.
Require Import PtTreeAdue.
Require Import KptPt.
Require Import TrampPt.
Require Import SmodeCore.
Require Import KptTree.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The TRAPFRAME leaf and its A/D-variant classification.  (The        *)
(*    trampoline leaf [pte_tramp] and its lemmas live in KptTree.v --     *)
(*    both tables share that mapping.)                                    *)
(* ===================================================================== *)

Definition pte_tf (tfp : mword 44) : mword 64 := mk_pte tfp PTE_TF.

Lemma tf_variant_flags (tfp : mword 44) (a d : mword 1) :
  subrange_vec_dec (pte_set_ad (pte_tf tfp) a d) 7 0
  = (mword_of_int (Z.lor (Z.land PTE_TF 831)
       (Z.lor (Z.shiftl (bv_unsigned a) 6) (Z.shiftl (bv_unsigned d) 7))) : mword 8).
Proof.
  unfold pte_tf, mk_pte.
  rewrite (pte_set_ad_zext_concat tfp PTE_TF a d ltac:(unfold PTE_TF; lia)).
  apply mk_pte_flags.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    vm_compute; intuition congruence.
Qed.

Lemma tf_variant_ext (tfp : mword 44) (a d : mword 1) :
  ext_bits_of_PTE (pte_set_ad (pte_tf tfp) a d) = Mk_PTE_Ext (mword_of_int 0).
Proof.
  rewrite pte_set_ad_ext.
  unfold pte_tf.
  unfold ext_bits_of_PTE. change (Z.eqb 64 64) with true. cbv iota beta.
  rewrite mk_pte_ext; [reflexivity | unfold PTE_TF; lia].
Qed.

Lemma tf_variant_ppn (tfp : mword 44) (a d : mword 1) :
  autocast (T := mword) ((autocast (T := mword)
     (PPN_of_PTE (pte_set_ad (pte_tf tfp) a d : mword 64))) : mword 44)
  = tfp.
Proof.
  rewrite !autocast_id.
  rewrite pte_set_ad_ppn.
  unfold pte_tf, PPN_of_PTE.
  change (Z.eqb 64 32) with false. cbv iota.
  rewrite autocast_id.
  apply mk_pte_ppn_field. unfold PTE_TF; lia.
Qed.

Lemma tf_variant (tfp : mword 44) (a d : mword 1) :
  pte_valid (pte_set_ad (pte_tf tfp) a d) /\ pte_leaf (pte_set_ad (pte_tf tfp) a d) /\
  pte_no_napot (pte_set_ad (pte_tf tfp) a d) /\ pte_pbmt0 (pte_set_ad (pte_tf tfp) a d).
Proof.
  repeat split.
  - intros s. unfold Mk_PTE_Flags.
    rewrite tf_variant_flags. rewrite tf_variant_ext.
    destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
      vm_compute; reflexivity.
  - unfold pte_leaf, Mk_PTE_Flags.
    rewrite tf_variant_flags.
    destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
      vm_compute; reflexivity.
  - unfold pte_no_napot.
    rewrite tf_variant_ext.
    apply kpt_extN_red.
  - unfold pte_pbmt0.
    rewrite tf_variant_ext.
    vm_compute. reflexivity.
Qed.

(* S-mode data accesses to the trapframe pass the permission check on any
   A/D variant (the leaf is R|W with U=0). *)
Lemma tf_variant_check_load (tfp : mword 44) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Load Data) Supervisor mxr do_sum (pte_set_ad (pte_tf tfp) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite tf_variant_flags. rewrite tf_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    destruct mxr, do_sum; vm_compute; reflexivity.
Qed.

Lemma tf_variant_check_store (tfp : mword 44) (a d : mword 1) (mxr do_sum : bool) :
  pte_check_ok (Store Data) Supervisor mxr do_sum (pte_set_ad (pte_tf tfp) a d).
Proof.
  intros s. unfold Mk_PTE_Flags.
  rewrite tf_variant_flags. rewrite tf_variant_ext.
  destruct (mword1_cases a) as [-> | ->]; destruct (mword1_cases d) as [-> | ->];
    destruct mxr, do_sum; vm_compute; reflexivity.
Qed.

(* vpn disequalities of the two top pages *)
Lemma tf_vpn_ne_tramp : tf_vpn <> tramp_vpn.
Proof.
  intro H.
  assert (Hu : bv_unsigned tf_vpn = bv_unsigned tramp_vpn) by (rewrite H; reflexivity).
  vm_compute in Hu. congruence.
Qed.

Lemma tf_vpn_unsigned : bv_unsigned tf_vpn = 67108862.
Proof. vm_compute; reflexivity. Qed.

Lemma tramp_vpn_unsigned : bv_unsigned tramp_vpn = 67108863.
Proof. vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* §2 The layout-free USER mapping spec.                                  *)
(* ===================================================================== *)

(* well-formedness of the user map: every user page sits BELOW the
   trapframe, and its canonical leaf is a proper 4K leaf on every A/D
   variant (established once when the map is built, from the concrete
   R/W/X/U flag byte of each entry). *)
Definition upt_map_wf (um : gmap (mword 27) (mword 64)) : Prop :=
  forall vpn w, um !! vpn = Some w ->
    (bv_unsigned vpn < bv_unsigned tf_vpn)%Z /\
    (forall a d : mword 1,
       pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
       pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d)).

Lemma upt_map_wf_not_tramp (um : gmap (mword 27) (mword 64)) (vpn : mword 27) (w : mword 64) :
  upt_map_wf um -> um !! vpn = Some w -> vpn <> tramp_vpn.
Proof.
  intros Hwf Hl ->.
  destruct (Hwf _ _ Hl) as (Hlt & _).
  rewrite tramp_vpn_unsigned tf_vpn_unsigned in Hlt. lia.
Qed.

Lemma upt_map_wf_not_tf (um : gmap (mword 27) (mword 64)) (vpn : mword 27) (w : mword 64) :
  upt_map_wf um -> um !! vpn = Some w -> vpn <> tf_vpn.
Proof.
  intros Hwf Hl ->.
  destruct (Hwf _ _ Hl) as (Hlt & _). lia.
Qed.

(* the user table's mapping spec: trampoline + trapframe + the user map,
   everything else blocks *)
Definition upt_tree_spec (uroot tfp : mword 44)
    (um : gmap (mword 27) (mword 64)) (t : ptree) : Prop :=
  pt_base t = uroot /\
  (exists p2 p1 (a d : mword 1),
     ptree_maps t tramp_vpn p2 p1 (pte_set_ad pte_tramp a d)) /\
  (exists p2 p1 (a d : mword 1),
     ptree_maps t tf_vpn p2 p1 (pte_set_ad (pte_tf tfp) a d)) /\
  (forall vpn w, um !! vpn = Some w ->
     exists p2 p1 (a d : mword 1),
       ptree_maps t vpn p2 p1 (pte_set_ad w a d)) /\
  (forall vpn, vpn <> tramp_vpn -> vpn <> tf_vpn -> um !! vpn = None ->
     ptree_blocks t vpn).

(* which canonical leaf a mapped vpn carries *)
Definition upt_leaf_at (tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w : mword 64) : Prop :=
  (vpn = tramp_vpn /\ w = pte_tramp) \/
  (vpn = tf_vpn /\ w = pte_tf tfp) \/
  (um !! vpn = Some w).

Lemma upt_spec_maps (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) (vpn : mword 27) (w : mword 64) :
  upt_tree_spec uroot tfp um t ->
  upt_leaf_at tfp um vpn w ->
  exists p2 p1 (a d : mword 1), ptree_maps t vpn p2 p1 (pte_set_ad w a d).
Proof.
  intros (Hbase & Htr & Htf & Hum & Hblk) [(-> & ->) | [(-> & ->) | Hl]].
  - exact Htr.
  - exact Htf.
  - exact (Hum _ _ Hl).
Qed.

Lemma upt_variant (tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (vpn : mword 27) (w : mword 64) :
  upt_map_wf um ->
  upt_leaf_at tfp um vpn w ->
  forall a d : mword 1,
    pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
    pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d).
Proof.
  intros Hwf [(-> & ->) | [(-> & ->) | Hl]] a d.
  - exact (tramp_variant a d).
  - exact (tf_variant tfp a d).
  - exact (proj2 (Hwf _ _ Hl) a d).
Qed.

(* the spec survives the A/D write-back at any mapped vpn *)
Lemma upt_tree_spec_set_leaf (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
    (t : ptree) (vpn : mword 27) (w p2 p1 : mword 64) (a0 d0 a d : mword 1) :
  upt_map_wf um ->
  upt_tree_spec uroot tfp um t ->
  upt_leaf_at tfp um vpn w ->
  ptree_maps t vpn p2 p1 (pte_set_ad w a0 d0) ->
  upt_tree_spec uroot tfp um (ptree_set_leaf t vpn (pte_set_ad w a d)).
Proof.
  intros Hwf Hspec Hleaf Hmaps.
  pose proof Hspec as (Hbase & Htr & Htf & Hum & Hblk).
  assert (Hvarw := upt_variant tfp um vpn w Hwf Hleaf).
  assert (Hself : exists p2' p1' (a' d' : mword 1),
    ptree_maps (ptree_set_leaf t vpn (pte_set_ad w a d)) vpn p2' p1' (pte_set_ad w a' d')).
  { exists p2, p1, a, d.
    rewrite <- (pte_set_ad_absorb w a0 d0 a d).
    apply (ptree_set_leaf_maps_self t vpn p2 p1 (pte_set_ad w a0 d0));
      [exact Hmaps | ..]; rewrite (pte_set_ad_absorb w a0 d0 a d).
    - exact (proj1 (Hvarw a d)).
    - exact (proj1 (proj2 (Hvarw a d))).
    - exact (proj1 (proj2 (proj2 (Hvarw a d)))).
    - exact (proj2 (proj2 (proj2 (Hvarw a d)))). }
  split; [| split; [| split; [| split]]].
  - rewrite <- Hbase.
    unfold ptree_set_leaf.
    destruct (pt_kids t (vpn_idx 2 vpn)); [| reflexivity].
    destruct (pt_kids p (vpn_idx 1 vpn)); reflexivity.
  - (* trampoline *)
    destruct (decide (vpn = tramp_vpn)) as [-> | Hne].
    + destruct Hleaf as [(_ & ->) | [(Heq & _) | Hl]].
      * exact Hself.
      * exfalso. exact (tf_vpn_ne_tramp (eq_sym Heq)).
      * exfalso. exact (upt_map_wf_not_tramp um _ _ Hwf Hl eq_refl).
    + destruct Htr as (q2 & q1 & a' & d' & Hm2).
      exists q2, q1, a', d'.
      apply (ptree_set_leaf_maps_other t vpn tramp_vpn _ _ _ _
               (not_eq_sym Hne) Hm2).
  - (* trapframe *)
    destruct (decide (vpn = tf_vpn)) as [-> | Hne].
    + destruct Hleaf as [(Heq & _) | [(_ & ->) | Hl]].
      * exfalso. exact (tf_vpn_ne_tramp Heq).
      * exact Hself.
      * exfalso. exact (upt_map_wf_not_tf um _ _ Hwf Hl eq_refl).
    + destruct Htf as (q2 & q1 & a' & d' & Hm2).
      exists q2, q1, a', d'.
      apply (ptree_set_leaf_maps_other t vpn tf_vpn _ _ _ _
               (not_eq_sym Hne) Hm2).
  - (* the user map *)
    intros vpn' w' Hl'.
    destruct (decide (vpn' = vpn)) as [-> | Hne].
    + assert (Hw : w' = w).
      { destruct Hleaf as [(-> & _) | [(-> & _) | Hl]].
        - exfalso. exact (upt_map_wf_not_tramp um _ _ Hwf Hl' eq_refl).
        - exfalso. exact (upt_map_wf_not_tf um _ _ Hwf Hl' eq_refl).
        - congruence. }
      subst w'. exact Hself.
    + destruct (Hum _ _ Hl') as (q2 & q1 & a' & d' & Hm2).
      exists q2, q1, a', d'.
      apply (ptree_set_leaf_maps_other t vpn vpn' _ _ _ _ Hne Hm2).
  - intros vpn' Hn1 Hn2 Hn3.
    apply (ptree_set_leaf_blocks t vpn vpn' p2 p1 (pte_set_ad w a0 d0));
      [exact Hmaps |].
    apply (Hblk vpn' Hn1 Hn2 Hn3).
Qed.

(* ===================================================================== *)
(* §3 THE USER TRANSLATION INVARIANT.                                     *)
(* ===================================================================== *)

Section UptTreeInv.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Definition utlb_inv_pt (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) : iProp Σ :=
    (∃ (usatp : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t : ptree),
       satp ↦ᵣ usatp ∗
       ⌜ _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ⌝ ∗
       ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
       ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ⌝ ∗
       tlb ↦ᵣ tlbvec ∗ ⌜ tlb_ok_pt (mword_of_int 0) t tlbvec ⌝ ∗
       ⌜ upt_tree_spec uroot tfp um t ⌝ ∗
       ⌜ upt_map_wf um ⌝ ∗
       ⌜ forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0 ⌝ ∗
       ptree_own 2 (DfracOwn 1) t ∗
       pmp_config uroot)%I.

  Lemma utlb_inv_pt_intro (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64))
      (usatp : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (t : ptree) :
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    upt_tree_spec uroot tfp um t ->
    upt_map_wf um ->
    (forall pmar0, pma_allows_all pmar0 -> pma_allows_pte_write pmar0) ->
    satp ↦ᵣ usatp -∗ tlb ↦ᵣ tlbvec -∗ ptree_own 2 (DfracOwn 1) t -∗
    pmp_config uroot -∗
    utlb_inv_pt uroot tfp um.
  Proof.
    intros Hmode Hasid Hppn Hok Hspec Hwf Hpmaw. iIntros "Hsatp Htlb Ht Hpmp".
    iExists usatp, tlbvec, t. iFrame "Hsatp Htlb Ht Hpmp". iPureIntro. tauto.
  Qed.


End UptTreeInv.

(* ===================================================================== *)
(* §4 THE USER INVARIANT ABSORBS TRANSLATION (S-mode: trampoline fetch,   *)
(*    trapframe data -- the userret/uservec paths).                       *)
(* ===================================================================== *)

Section UptTranslateIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (acc : MemoryAccessType mem_payload) (p : Privilege).

  (* PRIVILEGE-GENERIC: the mode dispatch comes in as a callback premise
     ([Htmk] -- the satp value lives inside the invariant, so the caller
     cannot supply the closed [translationMode] fact directly); Supervisor
     callers pass [exec_translationMode_S_sv39], User callers
     [exec_translationMode_U_sv39]. *)
  Lemma utlb_inv_pt_translateAddr (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (w va pa : mword 64) (σ : mstate) :
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc p mxr do_sum (pte_set_ad w a d)) ->
    upt_leaf_at tfp um (svpn_of va) w ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = p ->
    (forall satp0 : mword 64,
       register_lookup satp σ.(sregs) = satp0 ->
       _get_Satp64_Mode (Mk_Satp64 satp0) = ('b"1000" : mword 4) ->
       exec (translationMode p) σ = Some (Sv39, σ)) ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) p) σ
      = Some (p, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) acc) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hchk Hleaf Hcanon Hout Hmisa Hmenv Hhtif Hcp Htmk Heff Hss Hall.
    iIntros "Hri Hgh Hinv".
    iDestruct "Hinv" as (usatp tlbvec t)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Htlbok & %Hspec & %Hwf & %Hpmawimpl & Ht & Hpmp)".
    pose proof (Hpmawimpl _ Hall) as Hpmaw.
    iDestruct (reg_valid_dq with "Hri Hsatp") as %Hsatpv.
    iDestruct (reg_valid_dq with "Hri Htlb") as %Htlbv.
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00)
      "(Hpc & Hpa & %HA & %Hord & %Hpmarimpl & %HX & %HW & %HR & %Hcov)".
    iDestruct (reg_valid_dq with "Hri Hpc") as %Hpcv.
    iDestruct (reg_valid_dq with "Hri Hpa") as %Hpav.
    destruct (upt_spec_maps uroot tfp um t (svpn_of va) w Hspec Hleaf)
      as (p2 & p1 & a0 & d0 & Hmaps).
    pose proof Hspec as (Hbase & _).
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
    assert (Htm : exec (translationMode p) σ = Some (Sv39, σ))
      by exact (Htmk usatp Hsatpv Hmode).
    iMod (ptree_translateAddr_own acc p uroot t w va pa usatp
            tlbvec p2 p1 a0 d0 σ
            Hchk (upt_variant tfp um (svpn_of va) w Hwf Hleaf) Hcanon Hout Hbase Hmaps Htlbok
            Hmisa Hmenv Hhtif Hcp Htm Heff Hss Hsatpv Hppn Hasid Htlbv
            HA' Hord' HR' HW' Hcov' Hpmar Hpmaw
            with "Hri Hgh Htlb Ht")
      as (σ' t' tlbvec') "(%Htrans & %Hmdev & %Hsregs & %Htsh & %Htlbok' & Hri & Hgh & Htlb & Ht)".
    iModIntro. iExists σ'.
    iSplit; [iPureIntro; exact Htrans |].
    iSplit; [iPureIntro; exact Hmdev |].
    iSplit; [iPureIntro; exact Hsregs |].
    iFrame "Hri Hgh".
    assert (Hspec' : upt_tree_spec uroot tfp um t').
    { destruct Htsh as [-> | (a1 & d1 & ->)]; [exact Hspec |].
      exact (upt_tree_spec_set_leaf uroot tfp um t (svpn_of va) w p2 p1 a0 d0 a1 d1
               Hwf Hspec Hleaf Hmaps). }
    iApply (utlb_inv_pt_intro uroot tfp um usatp tlbvec' t'
              Hmode Hasid Hppn Htlbok' Hspec' Hwf Hpmawimpl with "Hsatp Htlb Ht").
    iApply (pmp_config_intro uroot pmpcfg0 pmpaddr00
              HA Hord Hpmarimpl HX HW HR Hcov with "Hpc Hpa").
  Qed.

End UptTranslateIris.

(* the S-mode instantiations for the userret / uservec paths: trampoline
   fetch and trapframe load/store, with the concrete-geometry premises in
   the caller-friendly [tramp_ppn]/[tfp] compose forms. *)
Section UptTranslateIrisAcc.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma utlb_inv_pt_translateAddr_tramp_fetch (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pa : mword 64) (σ : mstate) :
    svpn_of va = tramp_vpn ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec tramp_ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege (InstructionFetch tt) (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access (InstructionFetch tt)) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) (InstructionFetch tt)) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hvpn Hcanon Hid Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tramp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tramp_variant_ppn ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    apply (utlb_inv_pt_translateAddr (InstructionFetch tt) Supervisor uroot tfp um pte_tramp va pa σ
             (fun a d mxr do_sum => tramp_variant_check_fetch a d mxr do_sum)
             (or_introl (conj Hvpn eq_refl))
             Hcanon Hout Hmisa Hmenv Hhtif Hcp
             (fun satp0 Hs Hm => exec_translationMode_S_sv39 satp0 σ HSXL Hs Hm)
             Heff Hss Hall).
  Qed.

  Lemma utlb_inv_pt_translateAddr_tf_load (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pa : mword 64) (σ : mstate) :
    svpn_of va = tf_vpn ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec tfp
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege (Load Data) (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access (Load Data)) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) (Load Data)) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hvpn Hcanon Hid Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tf tfp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tf_variant_ppn tfp ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    apply (utlb_inv_pt_translateAddr (Load Data) Supervisor uroot tfp um (pte_tf tfp) va pa σ
             (fun a d mxr do_sum => tf_variant_check_load tfp a d mxr do_sum)
             (or_intror (or_introl (conj Hvpn eq_refl)))
             Hcanon Hout Hmisa Hmenv Hhtif Hcp
             (fun satp0 Hs Hm => exec_translationMode_S_sv39 satp0 σ HSXL Hs Hm)
             Heff Hss Hall).
  Qed.

  Lemma utlb_inv_pt_translateAddr_tf_store (uroot tfp : mword 44)
      (um : gmap (mword 27) (mword 64)) (va pa : mword 64) (σ : mstate) :
    svpn_of va = tf_vpn ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec tfp
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege (Store Data) (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access (Store Data)) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ utlb_inv_pt uroot tfp um ==∗
    ∃ σ' : mstate,
      ⌜ exec (translateAddr (Virtaddr va) (Store Data)) σ
        = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
      ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
      ⌜ (σ'.(sregs) = σ.(sregs) \/
         exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
      reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ utlb_inv_pt uroot tfp um.
  Proof.
    intros Hvpn Hcanon Hid Hmisa Hmenv Hhtif Hcp HSXL Heff Hss Hall.
    assert (Hout : zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword)
            (PPN_of_PTE (pte_tf tfp : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
    { rewrite <- (tf_variant_ppn tfp ('b"1") ('b"1")) in Hid.
      rewrite pte_set_ad_ppn in Hid. exact Hid. }
    apply (utlb_inv_pt_translateAddr (Store Data) Supervisor uroot tfp um (pte_tf tfp) va pa σ
             (fun a d mxr do_sum => tf_variant_check_store tfp a d mxr do_sum)
             (or_intror (or_introl (conj Hvpn eq_refl)))
             Hcanon Hout Hmisa Hmenv Hhtif Hcp
             (fun satp0 Hs Hm => exec_translationMode_S_sv39 satp0 σ HSXL Hs Hm)
             Heff Hss Hall).
  Qed.

End UptTranslateIrisAcc.
