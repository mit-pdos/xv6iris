(* WpKvminithart.v -- support lemmas for the rwx-kmap STAGE 6c whole-function
   proof of kvminithart (the Bare->Sv39 kernel-page-table switch).

   Currently lands the ghost-side switch fold [kvm_M_mint] (rwx-kmap
   deliverable 2): the switch dissolves the Bare arm's [kmap_auth kmap_M0]
   and mints, in one update, the target auth [kmap_auth (kvm_M pas)] together
   with the 65 persistent claims it hands the boot code -- the trampoline
   claim + the 64 kstack claims.  Freshness comes purely from the KvmMap
   characterizations (kmap_M0_lookup + the tramp/kstack classifiers +
   kstack_vpn_inj); no map literal is ever normalized. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import KptPt KptExecMap.
Require Import KMap.
Require Import KvmMap.
Local Open Scope Z_scope.

Section KvmMint.
  Context `{!riscvGS Σ}.

  (* the trampoline vpn is not statically classified (mirrors KvmMap's
     [kmap_class_tramp_None], which is Local there). *)
  Local Lemma kmi_class_tramp_None : kmap_class tramp_vpn = None.
  Proof. unfold kmap_class. rewrite tramp_vpn_uns. reflexivity. Qed.

  (* the auth-map kstack layer misses off the kstack vpns (mirrors KvmMap's
     Local [kvm_M_stacks_miss]). *)
  Local Lemma kmi_stacks_miss (pas : nat -> mword 44) (k : nat)
      (M : gmap (mword 27) (mword 44 * kperm)) (vpn : mword 27) :
    (forall i : nat, (i < k)%nat -> vpn <> kstack_vpn i) ->
    kvm_M_stacks pas k M !! vpn = M !! vpn.
  Proof.
    induction k as [|k' IH]; intros Hne.
    - reflexivity.
    - cbn [kvm_M_stacks]. rewrite lookup_insert_ne;
        [ apply IH; intros i Hi; apply Hne; lia
        | apply not_eq_sym; apply Hne; lia ].
  Qed.

  (* fold the 64 kstack inserts, persisting each fragment as a claim.  The
     freshness of [kstack_vpn k'] against the accumulator is [kmi_stacks_miss]
     (it is not one of the earlier kstacks, by [kstack_vpn_inj]) plus the
     base-map freshness premise. *)
  Local Lemma kvm_M_stacks_mint (pas : nat -> mword 44) (k : nat)
      (M0 : gmap (mword 27) (mword 44 * kperm)) :
    (k <= 64)%nat ->
    (forall i : nat, (i < k)%nat -> M0 !! kstack_vpn i = None) ->
    kmap_auth M0 ==∗ kmap_auth (kvm_M_stacks pas k M0) ∗
      ([∗ list] i ∈ seq 0 k, kmap_at (kstack_vpn i) (pas i) KP_rw).
  Proof.
    induction k as [|k' IH]; iIntros (Hk Hfresh) "Hauth".
    - iModIntro. iFrame "Hauth". done.
    - iMod (IH ltac:(lia) ltac:(intros i Hi; apply Hfresh; lia) with "Hauth")
        as "[Hauth Hclaims]".
      assert (Hfr : kvm_M_stacks pas k' M0 !! kstack_vpn k' = None).
      { rewrite kmi_stacks_miss.
        - apply Hfresh; lia.
        - intros i Hi. apply kstack_vpn_inj; lia. }
      iMod (kmap_insert _ (kstack_vpn k') (pas k') KP_rw Hfr with "Hauth")
        as "[Hauth #Hcl]".
      iModIntro. cbn [kvm_M_stacks]. iFrame "Hauth".
      rewrite seq_S big_sepL_app big_sepL_singleton.
      replace (0 + k')%nat with k' by lia.
      iFrame "Hclaims Hcl".
  Qed.

  (* THE ghost fold (rwx-kmap deliverable 2): the Bare arm's exact static
     auth becomes the target auth, releasing the trampoline claim + the 64
     kstack claims.  [kvm_M pas] is definitionally
     [kvm_M_stacks pas 64 (<[tramp_vpn := (tramp_ppn, KP_rx)]> kmap_M0)]. *)
  Lemma kvm_M_mint (pas : nat -> mword 44) :
    kmap_auth kmap_M0 ==∗ kmap_auth (kvm_M pas) ∗
      kmap_at tramp_vpn tramp_ppn KP_rx ∗
      ([∗ list] i ∈ seq 0 64, kmap_at (kstack_vpn i) (pas i) KP_rw).
  Proof.
    iIntros "Hauth".
    (* the trampoline is fresh in [kmap_M0] (not statically classified) *)
    assert (Htf : kmap_M0 !! tramp_vpn = None).
    { rewrite kmap_M0_lookup kmi_class_tramp_None. reflexivity. }
    iMod (kmap_insert _ tramp_vpn tramp_ppn KP_rx Htf with "Hauth")
      as "[Hauth #Htr]".
    (* each kstack vpn is fresh in [<[tramp := ...]> kmap_M0] (not tramp,
       not statically classified) *)
    assert (Hksf : forall i : nat, (i < 64)%nat ->
              (<[tramp_vpn := (tramp_ppn, KP_rx)]> kmap_M0) !! kstack_vpn i = None).
    { intros i Hi. rewrite lookup_insert_ne.
      - rewrite kmap_M0_lookup. rewrite (kstack_not_class _ i Hi eq_refl). reflexivity.
      - apply not_eq_sym. apply kstack_not_tramp. exact Hi. }
    iMod (kvm_M_stacks_mint pas 64 (<[tramp_vpn := (tramp_ppn, KP_rx)]> kmap_M0)
            ltac:(lia) Hksf with "Hauth") as "[Hauth Hks]".
    iModIntro. unfold kvm_M. iFrame "Hauth Htr Hks".
  Qed.

End KvmMint.
