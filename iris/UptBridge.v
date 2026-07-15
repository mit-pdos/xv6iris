(* UptBridge.v -- reconciling the TWO user-page-table invariants:

     [utlb_inv]  (WpUserret)  -- active DURING userret, after the satp
                                 switch: satp/tlb cells + the four owned
                                 trampoline/trapframe PTEs + PMP bundle,
                                 with slot-precise TLB consistency; and

     [upt_inv]   (UptInv)     -- the arbitrary-user-execution theory's
                                 invariant: a PT slot map + a walk spec,
                                 with [upt_tlb_ok] TLB consistency held
                                 in the user loop frame.

   The userret PT fragment IS a upt slot-map/spec: [ur_slots]/[ur_spec]
   describe exactly the two mappings (TRAMPOLINE -> tramp_ppn, TRAPFRAME
   -> tfp), the TLB entries userret can leave behind are exactly the
   [upt_entry]s of those two vpns, and [utlb_inv] converts into
   [upt_inv ur_slots ur_spec] plus the loop frame's satp/tlb/PMP cells
   and pure facts ([utlb_inv_to_upt]).  So wp_userret's postcondition
   feeds wp_user_exec's frame directly; a caller owning the REST of the
   process page table separately can extend the slot map/spec by
   disjoint union. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvFetchExec.
Require Import SmodeCore.
Require Import UptInv.
Require Import CommonWalk.
Require Import TrampPt WpUserret WpUserretEntry.
Require Import WpMmodeLeafBase.
Local Open Scope Z_scope.
Import Defs.

Local Notation idx2t := (subrange_vec_dec tramp_vpn 26 18).
Local Notation idx1t := (subrange_vec_dec tramp_vpn 17 9).
Local Notation idx0t := (subrange_vec_dec tramp_vpn 8 0).
Local Notation idx0f := (subrange_vec_dec tf_vpn 8 0).

(* ===================================================================== *)
(* 1. The userret PT fragment as a [upt_spec] slot map / walk spec.        *)
(* ===================================================================== *)

Definition ur_tramp_info (ul1 ul0 : mword 44) : uwalk_info :=
  {| uw_pte2 := pte_ptr ul1; uw_pte1 := pte_ptr ul0; uw_pte0 := pte_tramp |}.
Definition ur_tf_info (ul1 ul0 tfp : mword 44) : uwalk_info :=
  {| uw_pte2 := pte_ptr ul1; uw_pte1 := pte_ptr ul0; uw_pte0 := pte_tf tfp |}.

Definition ur_slots (uroot ul1 ul0 tfp : mword 44) : gmap (mword 64) (mword 64) :=
  <[pte_addr_at uroot idx2t := pte_ptr ul1]>
  (<[pte_addr_at ul1 idx1t := pte_ptr ul0]>
   (<[pte_addr_at ul0 idx0t := pte_tramp]>
    {[pte_addr_at ul0 idx0f := pte_tf tfp]})).

Definition ur_spec (ul1 ul0 tfp : mword 44) : gmap (mword 27) uwalk_info :=
  <[tramp_vpn := ur_tramp_info ul1 ul0]> {[tf_vpn := ur_tf_info ul1 ul0 tfp]}.

(* ---- the two theories' primitives coincide ---- *)
Lemma u_pte_addr_eq (base : mword 44) (idx : mword 9) :
  u_pte_addr base idx = pte_addr_at base idx.
Proof. reflexivity. Qed.

Lemma ext_bits_mk (p : mword 44) (f : Z) :
  0 <= f < 1024 ->
  ext_bits_of_PTE (mk_pte p f) = Mk_PTE_Ext (mword_of_int 0 : mword 10).
Proof.
  intro Hf.
  change (ext_bits_of_PTE (mk_pte p f))
    with (Mk_PTE_Ext (subrange_vec_dec (mk_pte p f) 63 54)).
  f_equal. apply mk_pte_ext. exact Hf.
Qed.

Lemma u_next_base_mk (p : mword 44) (f : Z) :
  0 <= f < 1024 ->
  u_next_base (mk_pte p f) = p.
Proof.
  intro Hf.
  unfold u_next_base.
  change (PPN_of_PTE (mk_pte p f))
    with (autocast (T := mword) (n := (if Z.eqb 64 32 then 22 else 44))
            (subrange_vec_dec (mk_pte p f) 53 10)).
  rewrite (mk_pte_ppn_field p f Hf).
  rewrite !autocast_id. reflexivity.
Qed.

(* ===================================================================== *)
(* 2. Structural well-formedness of the two walks ([uw_wf]).              *)
(* ===================================================================== *)

Lemma upte_ptr_inv (p : mword 44) : forall s,
  exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec (pte_ptr p) 7 0))
          (ext_bits_of_PTE (pte_ptr p))) s = Some (false, s).
Proof.
  intro s. unfold pte_ptr.
  rewrite (mk_pte_flags p PTE_PTR ltac:(unfold PTE_PTR; lia)).
  rewrite (ext_bits_mk p PTE_PTR ltac:(unfold PTE_PTR; lia)).
  vm_compute; reflexivity.
Qed.

Lemma upte_ptr_nonleaf (p : mword 44) :
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec (pte_ptr p) 7 0)) = true.
Proof.
  unfold pte_ptr.
  rewrite (mk_pte_flags p PTE_PTR ltac:(unfold PTE_PTR; lia)).
  vm_compute; reflexivity.
Qed.

Lemma upte_tf_inv (tfp : mword 44) : forall s,
  exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec (pte_tf tfp) 7 0))
          (ext_bits_of_PTE (pte_tf tfp))) s = Some (false, s).
Proof.
  intro s. unfold pte_tf.
  rewrite (mk_pte_flags tfp PTE_TF ltac:(unfold PTE_TF; lia)).
  rewrite (ext_bits_mk tfp PTE_TF ltac:(unfold PTE_TF; lia)).
  vm_compute; reflexivity.
Qed.

Lemma upte_tf_leaf (tfp : mword 44) :
  pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec (pte_tf tfp) 7 0)) = false.
Proof.
  unfold pte_tf.
  rewrite (mk_pte_flags tfp PTE_TF ltac:(unfold PTE_TF; lia)).
  vm_compute; reflexivity.
Qed.

Lemma ur_tramp_wf (ul1 ul0 : mword 44) : uw_wf (ur_tramp_info ul1 ul0).
Proof.
  unfold uw_wf, ur_tramp_info; cbn [uw_pte2 uw_pte1 uw_pte0].
  refine (conj (upte_ptr_inv ul1)
          (conj (upte_ptr_nonleaf ul1)
          (conj (upte_ptr_inv ul0)
          (conj (upte_ptr_nonleaf ul0)
          (conj _ (conj _ (conj _ (conj _ _)))))))).
  - intro s. unfold pte_tramp.
    rewrite (mk_pte_flags tramp_ppn PTE_TRAMP ltac:(unfold PTE_TRAMP; lia)).
    rewrite (ext_bits_mk tramp_ppn PTE_TRAMP ltac:(unfold PTE_TRAMP; lia)).
    vm_compute; reflexivity.
  - unfold pte_tramp.
    rewrite (mk_pte_flags tramp_ppn PTE_TRAMP ltac:(unfold PTE_TRAMP; lia)).
    vm_compute; reflexivity.
  - unfold pte_tramp.
    rewrite (ext_bits_mk tramp_ppn PTE_TRAMP ltac:(unfold PTE_TRAMP; lia)).
    vm_compute; reflexivity.
  - unfold u_global, u_gbit, pte_ptr, pte_tramp.
    rewrite (mk_pte_flags ul1 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite (mk_pte_flags ul0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite (mk_pte_flags tramp_ppn PTE_TRAMP ltac:(unfold PTE_TRAMP; lia)).
    vm_compute; reflexivity.
  - unfold pte_tramp.
    rewrite (ext_bits_mk tramp_ppn PTE_TRAMP ltac:(unfold PTE_TRAMP; lia)).
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma ur_tf_wf (ul1 ul0 tfp : mword 44) : uw_wf (ur_tf_info ul1 ul0 tfp).
Proof.
  unfold uw_wf, ur_tf_info; cbn [uw_pte2 uw_pte1 uw_pte0].
  refine (conj (upte_ptr_inv ul1)
          (conj (upte_ptr_nonleaf ul1)
          (conj (upte_ptr_inv ul0)
          (conj (upte_ptr_nonleaf ul0)
          (conj (upte_tf_inv tfp)
          (conj (upte_tf_leaf tfp) (conj _ (conj _ _)))))))).
  - unfold pte_tf.
    rewrite (ext_bits_mk tfp PTE_TF ltac:(unfold PTE_TF; lia)).
    vm_compute; reflexivity.
  - unfold u_global, u_gbit, pte_ptr, pte_tf.
    rewrite (mk_pte_flags ul1 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite (mk_pte_flags ul0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite (mk_pte_flags tfp PTE_TF ltac:(unfold PTE_TF; lia)).
    vm_compute; reflexivity.
  - unfold pte_tf.
    rewrite (ext_bits_mk tfp PTE_TF ltac:(unfold PTE_TF; lia)).
    apply bv_eq; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(* 3. Slot-address disequalities (distinct table pages).                   *)
(* ===================================================================== *)

Lemma pte_addr_at_ne_page (p q : mword 44) (i j : mword 9) :
  p <> q -> pte_addr_at p i <> pte_addr_at q j.
Proof.
  intros Hpq He. apply Hpq. apply bv_eq.
  apply (f_equal bv_unsigned) in He.
  rewrite !pte_addr_at_unsigned in He.
  pose proof (bv_unsigned_in_range _ i) as Hi.
  pose proof (bv_unsigned_in_range _ j) as Hj.
  unfold bv_modulus in Hi, Hj.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 9)) with 9 in Hi, Hj.
  change (2 ^ 9) with 512 in Hi, Hj.
  lia.
Qed.

Lemma ur_leaf_slots_ne (p : mword 44) :
  pte_addr_at p idx0t <> pte_addr_at p idx0f.
Proof.
  intro He. apply (f_equal bv_unsigned) in He.
  rewrite !pte_addr_at_unsigned in He.
  assert (H1 : bv_unsigned (idx0t : mword 9) = 511) by (vm_compute; reflexivity).
  assert (H2 : bv_unsigned (idx0f : mword 9) = 510) by (vm_compute; reflexivity).
  rewrite H1 in He. rewrite H2 in He. lia.
Qed.

(* ===================================================================== *)
(* 4. The pure spec: [ur_slots] describes both walks.                      *)
(* ===================================================================== *)

Lemma ur_leaf_slots_ne' (p : mword 44) :
  pte_addr_at p idx0f <> pte_addr_at p idx0t.
Proof. intro He. apply (ur_leaf_slots_ne p). symmetry. exact He. Qed.

Lemma ur_upt_spec (uroot ul1 ul0 tfp : mword 44) :
  uroot <> ul1 -> ul1 <> ul0 -> uroot <> ul0 ->
  upt_spec uroot (ur_slots uroot ul1 ul0 tfp) (ur_spec ul1 ul0 tfp).
Proof.
  intros Hru1 Hu1u0 Hru0.
  assert (Hidx2 : subrange_vec_dec tf_vpn 26 18 = idx2t)
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Hidx1 : subrange_vec_dec tf_vpn 17 9 = idx1t)
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Hvpn_ne : tramp_vpn <> tf_vpn).
  { intro He. apply (f_equal bv_unsigned) in He. vm_compute in He. congruence. }
  intros vpn i Hlk.
  unfold ur_spec in Hlk.
  destruct (decide (vpn = tramp_vpn)) as [-> | Hne].
  - rewrite lookup_insert in Hlk. injection Hlk as <-.
    unfold uw_addr2, uw_addr1, uw_addr0, ur_tramp_info;
      cbn [uw_pte2 uw_pte1 uw_pte0].
    rewrite !u_pte_addr_eq.
    rewrite (u_next_base_mk ul1 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite (u_next_base_mk ul0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    unfold ur_slots.
    split; [| split; [| split]].
    + apply lookup_insert.
    + rewrite lookup_insert_ne;
        [apply lookup_insert | apply pte_addr_at_ne_page; congruence].
    + rewrite lookup_insert_ne;
        [| apply pte_addr_at_ne_page; congruence].
      rewrite lookup_insert_ne;
        [apply lookup_insert | apply pte_addr_at_ne_page; congruence].
    + apply ur_tramp_wf.
  - rewrite lookup_insert_ne in Hlk; [| congruence].
    destruct (decide (vpn = tf_vpn)) as [-> | Hne2].
    2:{ rewrite lookup_singleton_ne in Hlk; [discriminate | congruence]. }
    rewrite lookup_singleton in Hlk. injection Hlk as <-.
    unfold uw_addr2, uw_addr1, uw_addr0, ur_tf_info;
      cbn [uw_pte2 uw_pte1 uw_pte0].
    rewrite !u_pte_addr_eq.
    rewrite (u_next_base_mk ul1 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite (u_next_base_mk ul0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite Hidx2. rewrite Hidx1.
    unfold ur_slots.
    split; [| split; [| split]].
    + apply lookup_insert.
    + rewrite lookup_insert_ne;
        [apply lookup_insert | apply pte_addr_at_ne_page; congruence].
    + rewrite lookup_insert_ne;
        [| apply pte_addr_at_ne_page; congruence].
      rewrite lookup_insert_ne;
        [| apply pte_addr_at_ne_page; congruence].
      rewrite lookup_insert_ne;
        [apply lookup_singleton | apply ur_leaf_slots_ne].
    + apply ur_tf_wf.
Qed.

(* ===================================================================== *)
(* 5. The TLB entries coincide: userret's stale entries ARE the walk       *)
(*    entries of the two spec-mapped vpns.                                 *)
(* ===================================================================== *)

Lemma upt_entry_tramp (ul1 ul0 : mword 44) :
  upt_entry tramp_vpn (ur_tramp_info ul1 ul0) = tramp_ent ul0.
Proof.
  unfold upt_entry, ur_tramp_info; cbn [uw_pte2 uw_pte1 uw_pte0].
  unfold u_walk_entry, tramp_ent, tlb4k_entry.
  f_equal.
  - (* global *)
    unfold u_global, u_gbit, pte_ptr, pte_tramp.
    rewrite (mk_pte_flags ul1 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite (mk_pte_flags ul0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite (mk_pte_flags tramp_ppn PTE_TRAMP ltac:(unfold PTE_TRAMP; lia)).
    vm_compute; reflexivity.
  - (* pteAddr *)
    f_equal.
    rewrite (u_next_base_mk ul0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    reflexivity.
Qed.

Lemma upt_entry_tf (ul1 ul0 tfp : mword 44) :
  upt_entry tf_vpn (ur_tf_info ul1 ul0 tfp) = tf_ent ul0 tfp.
Proof.
  unfold upt_entry, ur_tf_info; cbn [uw_pte2 uw_pte1 uw_pte0].
  unfold u_walk_entry, tf_ent, tlb4k_entry.
  assert (Hppn : autocast (T := mword) (PPN_of_PTE (pte_tf tfp)) = tfp).
  { unfold pte_tf.
    change (PPN_of_PTE (mk_pte tfp PTE_TF))
      with (autocast (T := mword) (n := (if Z.eqb 64 32 then 22 else 44))
              (subrange_vec_dec (mk_pte tfp PTE_TF) 53 10)).
    rewrite (mk_pte_ppn_field tfp PTE_TF ltac:(unfold PTE_TF; lia)).
    rewrite !autocast_id. reflexivity. }
  f_equal.
  - (* global *)
    unfold u_global, u_gbit, pte_ptr, pte_tf.
    rewrite (mk_pte_flags ul1 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite (mk_pte_flags ul0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    rewrite (mk_pte_flags tfp PTE_TF ltac:(unfold PTE_TF; lia)).
    vm_compute; reflexivity.
  - (* ppn *)
    rewrite Hppn.
    assert (Hmask : bv_unsigned (not_vec (zero_extend' 44 (ones 0 : mword 0)) : mword 44)
                    = 2 ^ 44 - 1) by (vm_compute; reflexivity).
    rewrite (and44_ones tfp _ Hmask).
    apply zero_extend44_id.
  - (* pte *)
    rewrite autocast_id. apply zero_extend64_id.
  - (* pteAddr *)
    f_equal.
    rewrite (u_next_base_mk ul0 PTE_PTR ltac:(unfold PTE_PTR; lia)).
    reflexivity.
Qed.

(* ===================================================================== *)
(* 6. TLB consistency: userret's slot-precise invariant refines            *)
(*    [upt_tlb_ok] at the two-vpn spec.                                    *)
(* ===================================================================== *)

Lemma utlb_consistent_upt_ok (ul1 ul0 tfp : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  utlb_consistent ul0 tfp tlbvec ->
  upt_tlb_ok (ur_spec ul1 ul0 tfp) tlbvec.
Proof.
  intros Hc vpn' ent Hget.
  assert (Hvpn_ne : tramp_vpn <> tf_vpn).
  { intro He. apply (f_equal bv_unsigned) in He. vm_compute in He. congruence. }
  pose proof (tlb_hash_range vpn') as Hr.
  destruct (Hc (tlb_hash (__id 39) vpn') Hr) as [Hn | [[Hi He] | [Hi He]]].
  - rewrite Hn in Hget. discriminate.
  - (* slot 63: the trampoline entry *)
    rewrite He in Hget. injection Hget as <-.
    exists tramp_vpn, (ur_tramp_info ul1 ul0).
    split; [| split].
    + unfold ur_spec. apply lookup_insert.
    + rewrite tramp_hash. rewrite Hi. reflexivity.
    + symmetry. apply upt_entry_tramp.
  - (* slot 62: the trapframe entry *)
    rewrite He in Hget. injection Hget as <-.
    exists tf_vpn, (ur_tf_info ul1 ul0 tfp).
    split; [| split].
    + unfold ur_spec.
      rewrite lookup_insert_ne; [apply lookup_singleton | congruence].
    + rewrite tf_hash. rewrite Hi. reflexivity.
    + symmetry. apply upt_entry_tf.
Qed.

(* ===================================================================== *)
(* 7. The Iris bridge: [utlb_inv] converts into [upt_inv] + the user       *)
(*    loop frame's satp/tlb/PMP cells and pure facts.                      *)

(* ===================================================================== *)
(* 8. The CONVERSE: re-entering the kernel through uservec.  A trap from  *)
(* user mode lands in the trampoline's uservec, which runs under the      *)
(* USER page table until IT switches satp back to the kernel table.  The  *)
(* user-execution frame's pieces reconstruct [utlb_inv], so the uservec   *)
(* WP can drive the trampoline-page engines (wp_instr_u) from the state   *)
(* the user loop leaves behind.                                           *)
(* ===================================================================== *)

(* the direct-mapped hash is surjective on [0,64): slot i is the hash of
   the 27-bit vpn i *)
Lemma tlb_hash_surj (i : Z) :
  0 <= i < 64 ->
  exists vpn' : mword 27, tlb_hash (__id 39) vpn' = i.
Proof.
  intro Hi.
  assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31 \/ i = 32 \/ i = 33 \/ i = 34 \/ i = 35 \/ i = 36 \/ i = 37 \/ i = 38 \/ i = 39 \/ i = 40 \/ i = 41 \/ i = 42 \/ i = 43 \/ i = 44 \/ i = 45 \/ i = 46 \/ i = 47 \/ i = 48 \/ i = 49 \/ i = 50 \/ i = 51 \/ i = 52 \/ i = 53 \/ i = 54 \/ i = 55 \/ i = 56 \/ i = 57 \/ i = 58 \/ i = 59 \/ i = 60 \/ i = 61 \/ i = 62 \/ i = 63) by lia.
  repeat (destruct H as [-> | H];
    [ match goal with |- exists _, _ = ?k =>
        exists (mword_of_int k : mword 27); vm_compute; reflexivity end |]).
  subst i.
  exists (mword_of_int 63 : mword 27); vm_compute; reflexivity.
Qed.

(* [upt_tlb_ok] at the two-vpn spec gives back the slot-precise userret
   TLB consistency: every present slot is the hash-slot of a spec-mapped
   vpn, and only slots 63/62 qualify. *)
Lemma upt_ok_utlb_consistent (ul1 ul0 tfp : mword 44)
    (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  upt_tlb_ok (ur_spec ul1 ul0 tfp) tlbvec ->
  utlb_consistent ul0 tfp tlbvec.
Proof.
  intros Hok i Hi.
  destruct (vec_access_dec tlbvec i) as [ent |] eqn:Hslot; [| left; reflexivity].
  destruct (tlb_hash_surj i ltac:(change (2 ^ 6) with 64 in Hi; lia)) as (vpn' & Hh).
  rewrite <- Hh in Hslot.
  destruct (Hok vpn' ent Hslot) as (vpn & inf & Hspec & Hhash & ->).
  unfold ur_spec in Hspec.
  destruct (decide (vpn = tramp_vpn)) as [-> | Hne].
  - rewrite lookup_insert in Hspec. injection Hspec as <-.
    right; left. split.
    + rewrite <- Hh. rewrite <- Hhash. apply tramp_hash.
    + rewrite upt_entry_tramp. reflexivity.
  - rewrite lookup_insert_ne in Hspec; [| congruence].
    destruct (decide (vpn = tf_vpn)) as [-> | Hne2].
    2:{ rewrite lookup_singleton_ne in Hspec; [discriminate | congruence]. }
    rewrite lookup_singleton in Hspec. injection Hspec as <-.
    right; right. split.
    + rewrite <- Hh. rewrite <- Hhash. apply tf_hash.
    + rewrite upt_entry_tf. reflexivity.
Qed.

(* ===================================================================== *)

Section UptBridge.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* one owned userret PTE, as a upt slot word *)
  Lemma pte8_word_pointsto (base : mword 44) (idx : mword 9) (v : mword 64) :
    pte8 (pte_addr_at base idx) v (DfracOwn 1) -∗ pte_addr_at base idx ↦₈ v.
  Proof.
    iIntros "H". iSplitR; [iPureIntro; apply pte_addr_at_aligned8 |].
    iExact "H".
  Qed.

  Lemma utlb_inv_to_upt (uroot ul1 ul0 tfp : mword 44) :
    uroot <> ul1 -> ul1 <> ul0 -> uroot <> ul0 ->
    utlb_inv uroot ul1 ul0 tfp -∗
    ∃ (usatp : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n),
      ⌜ _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ⌝ ∗
      ⌜ zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ⌝ ∗
      ⌜ autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ⌝ ∗
      ⌜ upt_tlb_ok (ur_spec ul1 ul0 tfp) tlbvec ⌝ ∗
      ⌜ pmpAddrMatchType_encdec_backwards
          (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ⌝ ∗
      ⌜ zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ⌝ ∗
      ⌜ eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ⌝ ∗
      ⌜ eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ⌝ ∗
      ⌜ eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ⌝ ∗
      ⌜ (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ⌝ ∗
      satp ↦ᵣ usatp ∗
      tlb ↦ᵣ tlbvec ∗
      pmpcfg_n ↦ᵣ pmpcfg0 ∗
      pmpaddr_n ↦ᵣ pmpaddr00 ∗
      upt_inv uroot (ur_slots uroot ul1 ul0 tfp) (ur_spec ul1 ul0 tfp).
  Proof.
    intros Hru1 Hu1u0 Hru0.
    iIntros "Hutlb".
    iDestruct (utlb_inv_open with "Hutlb") as (usatp tlbvec)
      "(Hsatp & %Hmode & %Hasid & %Hppn & Htlb & %Hcons & Hpbytes & Hpmp)".
    iDestruct "Hpmp" as (pmpcfg0 pmpaddr00 rg2 rg1 rg0t rg0f)
      "(Hpmpc & Hpmpa & %Hp2 & %Hp1 & %Hp0 & %Hpf & %Hpteregion & %HX & %HW & %HR & %Hcov)".
    destruct Hp2 as (HA & Hord & _ & _).
    iDestruct "Hpbytes" as "(Hpb2 & Hpb1 & Hpb0t & Hpb0f)".
    iExists usatp, tlbvec, pmpcfg0, pmpaddr00.
    iFrame "Hsatp Htlb Hpmpc Hpmpa".
    iSplitR; [iPureIntro; exact Hmode |].
    iSplitR; [iPureIntro; exact Hasid |].
    iSplitR; [iPureIntro; exact Hppn |].
    iSplitR; [iPureIntro; exact (utlb_consistent_upt_ok ul1 ul0 tfp tlbvec Hcons) |].
    iSplitR; [iPureIntro; exact HA |].
    iSplitR; [iPureIntro; exact Hord |].
    iSplitR; [iPureIntro; exact HX |].
    iSplitR; [iPureIntro; exact HW |].
    iSplitR; [iPureIntro; exact HR |].
    iSplitR; [iPureIntro; exact Hcov |].
    (* the upt_inv body: the four slots as a big_sepM + the pure spec *)
    unfold upt_inv, upt_slots, ur_slots.
    iSplitL.
    2:{ iPureIntro. apply ur_upt_spec; assumption. }
    rewrite big_sepM_insert.
    2:{ rewrite lookup_insert_ne;
          [| apply pte_addr_at_ne_page; congruence].
        rewrite lookup_insert_ne;
          [| apply pte_addr_at_ne_page; congruence].
        apply lookup_singleton_ne. apply pte_addr_at_ne_page; congruence. }
    rewrite big_sepM_insert.
    2:{ rewrite lookup_insert_ne;
          [| apply pte_addr_at_ne_page; congruence].
        apply lookup_singleton_ne. apply pte_addr_at_ne_page; congruence. }
    rewrite big_sepM_insert.
    2:{ apply lookup_singleton_ne. apply ur_leaf_slots_ne'. }
    rewrite big_sepM_singleton.
    iSplitL "Hpb2"; [iApply (pte8_word_pointsto with "Hpb2") |].
    iSplitL "Hpb1"; [iApply (pte8_word_pointsto with "Hpb1") |].
    iSplitL "Hpb0t"; [iApply (pte8_word_pointsto with "Hpb0t") |].
    iApply (pte8_word_pointsto with "Hpb0f").
  Qed.


  (* the Iris converse: the user frame's satp/tlb/PMP cells + [upt_inv]
     reconstruct [utlb_inv] for the uservec trampoline steps.  The PMA
     pte-read regions come back as premises (they are boot facts, exactly
     as wp_userret takes them). *)
  Lemma upt_to_utlb_inv (uroot ul1 ul0 tfp : mword 44) (usatp : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (pmpcfg0 : type_of_register pmpcfg_n) (pmpaddr00 : type_of_register pmpaddr_n)
      (rg2 rg1 rg0t rg0f : PMA_Region) :
    uroot <> ul1 -> ul1 <> ul0 -> uroot <> ul0 ->
    _get_Satp64_Mode (Mk_Satp64 usatp) = ('b"1000" : mword 4) ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) usatp : mword 64)) = (mword_of_int 0 : mword 16) ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) usatp : mword 64)) = uroot ->
    upt_tlb_ok (ur_spec ul1 ul0 tfp) tlbvec ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pmpcfg0 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec pmpaddr00 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pmpcfg0 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec pmpaddr00 0) * 4)%Z ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at uroot idx2t)) 8 = Some rg2 /\
       (override_PMA (PMA_Region_attributes rg2) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at ul1 idx1t)) 8 = Some rg1 /\
       (override_PMA (PMA_Region_attributes rg1) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at ul0 idx0t)) 8 = Some rg0t /\
       (override_PMA (PMA_Region_attributes rg0t) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    (forall pmar0, pma_allows_all pmar0 ->
       matching_pma_region pmar0 (Physaddr (pte_addr_at ul0 idx0f)) 8 = Some rg0f /\
       (override_PMA (PMA_Region_attributes rg0f) PBMT_PMA).(PMA_supports_pte_read) = true) ->
    satp ↦ᵣ usatp -∗
    tlb ↦ᵣ tlbvec -∗
    pmpcfg_n ↦ᵣ pmpcfg0 -∗
    pmpaddr_n ↦ᵣ pmpaddr00 -∗
    upt_inv uroot (ur_slots uroot ul1 ul0 tfp) (ur_spec ul1 ul0 tfp) -∗
    utlb_inv uroot ul1 ul0 tfp.
  Proof.
    intros Hru1 Hu1u0 Hru0 Hmode Hasid Hppn Hok HA Hord HX HW HR Hcov
      Hr2 Hr1 Hr0t Hr0f.
    iIntros "Hsatp Htlb Hpmpc Hpmpa [Hslots _]".
    unfold upt_slots, ur_slots.
    rewrite big_sepM_insert.
    2:{ rewrite lookup_insert_ne;
          [| apply pte_addr_at_ne_page; congruence].
        rewrite lookup_insert_ne;
          [| apply pte_addr_at_ne_page; congruence].
        apply lookup_singleton_ne. apply pte_addr_at_ne_page; congruence. }
    rewrite big_sepM_insert.
    2:{ rewrite lookup_insert_ne;
          [| apply pte_addr_at_ne_page; congruence].
        apply lookup_singleton_ne. apply pte_addr_at_ne_page; congruence. }
    rewrite big_sepM_insert.
    2:{ apply lookup_singleton_ne. apply ur_leaf_slots_ne'. }
    rewrite big_sepM_singleton.
    iDestruct "Hslots" as "(Hw2 & Hw1 & Hw0t & Hw0f)".
    iDestruct "Hw2" as "[_ Hpb2]".
    iDestruct "Hw1" as "[_ Hpb1]".
    iDestruct "Hw0t" as "[_ Hpb0t]".
    iDestruct "Hw0f" as "[_ Hpb0f]".
    iDestruct (pte8_ram_bounds with "Hpb2") as %[Hlo2 Hfit2].
    iDestruct (pte8_ram_bounds with "Hpb1") as %[Hlo1 Hfit1].
    iDestruct (pte8_ram_bounds with "Hpb0t") as %[Hlo0t Hfit0t].
    iDestruct (pte8_ram_bounds with "Hpb0f") as %[Hlo0f Hfit0f].
    pose proof (conj HA (conj Hord (conj (ram_pmp_match _ _ Hlo2 Hfit2 Hcov) HR))) as Hp2.
    pose proof (conj HA (conj Hord (conj (ram_pmp_match _ _ Hlo1 Hfit1 Hcov) HR))) as Hp1.
    pose proof (conj HA (conj Hord (conj (ram_pmp_match _ _ Hlo0t Hfit0t Hcov) HR))) as Hp0t.
    pose proof (conj HA (conj Hord (conj (ram_pmp_match _ _ Hlo0f Hfit0f Hcov) HR))) as Hp0f.
    iApply (utlb_inv_intro uroot ul1 ul0 tfp usatp tlbvec Hmode Hasid Hppn
              (upt_ok_utlb_consistent ul1 ul0 tfp tlbvec Hok)
              with "Hsatp Htlb [Hpb2 Hpb1 Hpb0t Hpb0f] [Hpmpc Hpmpa]").
    { iSplitL "Hpb2"; [iExact "Hpb2" |].
      iSplitL "Hpb1"; [iExact "Hpb1" |].
      iSplitL "Hpb0t"; [iExact "Hpb0t" |].
      iExact "Hpb0f". }
    iExists pmpcfg0, pmpaddr00, rg2, rg1, rg0t, rg0f.
    iFrame "Hpmpc Hpmpa". iPureIntro.
    exact (conj Hp2 (conj Hp1 (conj Hp0t (conj Hp0f (conj
            (fun pmar Hall => conj (Hr2 pmar Hall)
               (conj (Hr1 pmar Hall) (conj (Hr0t pmar Hall) (Hr0f pmar Hall))))
            (conj HX (conj HW (conj HR Hcov)))))))).
  Qed.

End UptBridge.
