(* UART S-mode device access under the NATIVE kernel page table (kvmmake-faithful
   all-4KB PT).  The refactored [tlb_inv root_ppn] already maps the UART (device
   vpn 0x10000, PTE_DEV) via [kpt_bytes]/[P_kpt], so the device leaves no longer
   need the [tlb_inv_gen (P_uart4k …)] switch or the client [uart_map] resource:
   the three UART PTE bytes come straight from the invariant's [kpt_bytes].

   This file provides the pure bridge lemmas (Phase 1): the UART page's kernel-PT
   walk pages, its byte/RAM facts sourced from [kpt_mem], its [P_kpt] membership +
   fill, and [tlb_consistent] monotonicity (which lets the reworked leaves feed
   the invariant's [tlb_consistent (P_kpt root)] straight into the unchanged
   [exec_translateAddr_uart], since P_kpt ⟹ P_uart4k). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes DevModel.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes.
Require Import SmodePte Pt4kWalk KptPt SmodeCore CommonWalk.
Require Import WpGpr.
Require Import WpLoad WpMmodeLeafBase.
Require Import WpSmodeGpr.
Require Import WpUart WpSmodeUart.
Require Import TrampPt TrampTlb.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Phase 1: pure bridge lemmas.                                            *)
(* ===================================================================== *)

(* [tlb_consistent] is monotone in the legal-entry predicate. *)
Lemma tlb_consistent_mono (P Q : TLB_Entry -> Prop) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  (forall e, P e -> Q e) -> tlb_consistent P tlbvec -> tlb_consistent Q tlbvec.
Proof.
  intros HPQ HP i Hi. destruct (HP i Hi) as [Hn | (e & He & HPe)].
  - left; exact Hn.
  - right; exists e; split; [exact He | apply HPQ; exact HPe].
Qed.

(* the UART page is a mapped (device) vpn. *)
Lemma uart_kpt_mapped : kpt_mapped uart_vpn.
Proof.
  right. unfold kpt_dev_vpn.
  assert (bv_unsigned uart_vpn = 65536) as -> by (vm_compute; reflexivity). lia.
Qed.

(* the UART leaf is a legal kernel-PT TLB entry. *)
Lemma P_kpt_uart (root : mword 44) : P_kpt root (kpt_tlb_ent root uart_vpn).
Proof. exists uart_vpn. split; [exact uart_kpt_mapped | reflexivity]. Qed.

(* the UART vpn's kernel-PT walk pages: root -> l1_dev -> l0_dev 32. *)
Lemma uart_l0_of_eq (root : mword 44) : kpt_l0_of root uart_vpn = kpt_l0_dev root 32.
Proof.
  unfold kpt_l0_of.
  assert (Z.leb 0x80000 (bv_unsigned uart_vpn) = false) as -> by (vm_compute; reflexivity).
  assert (bv_unsigned (vpn1_of uart_vpn) = 128) as -> by (vm_compute; reflexivity).
  unfold kpt_l0_dev. reflexivity.
Qed.

(* the UART leaf PTE flags are the device flags. *)
Lemma uart_lflags_eq : kpt_lflags uart_vpn = PTE_DEV.
Proof.
  unfold kpt_lflags.
  assert (Z.leb 0x80000 (bv_unsigned uart_vpn) = false) as -> by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* the three UART PTE-page slot addresses sit in RAM (both word ends). *)
Lemma uart_kpt_ram (root : mword 44) :
  kpt_ok root ->
  addr_is_ram (pte_addr_at root (subrange_vec_dec uart_vpn 26 18))
  /\ addr_is_ram (pa_add (pte_addr_at root (subrange_vec_dec uart_vpn 26 18)) 7)
  /\ addr_is_ram (pte_addr_at (kpt_l1_dev root) (subrange_vec_dec uart_vpn 17 9))
  /\ addr_is_ram (pa_add (pte_addr_at (kpt_l1_dev root) (subrange_vec_dec uart_vpn 17 9)) 7)
  /\ addr_is_ram (pte_addr_at (kpt_l0_of root uart_vpn) (subrange_vec_dec uart_vpn 8 0))
  /\ addr_is_ram (pa_add (pte_addr_at (kpt_l0_of root uart_vpn) (subrange_vec_dec uart_vpn 8 0)) 7).
Proof.
  intros Hok.
  pose proof (kpt_slot_ram root 0 (subrange_vec_dec uart_vpn 26 18) Hok
                ltac:(unfold kpt_pages; lia)) as [Hr2 Hr2'].
  rewrite kpt_page_0 in Hr2. rewrite kpt_page_0 in Hr2'.
  pose proof (kpt_slot_ram root 1 (subrange_vec_dec uart_vpn 17 9) Hok
                ltac:(unfold kpt_pages; lia)) as [Hr1 Hr1'].
  pose proof (kpt_slot_ram root 34 (subrange_vec_dec uart_vpn 8 0) Hok
                ltac:(unfold kpt_pages; lia)) as [Hr0 Hr0'].
  change (kpt_l1_dev root) with (kpt_page root 1).
  rewrite uart_l0_of_eq. change (kpt_l0_dev root 32) with (kpt_page root 34).
  split; [exact Hr2|]. split; [exact Hr2'|]. split; [exact Hr1|].
  split; [exact Hr1'|]. split; [exact Hr0 | exact Hr0'].
Qed.

(* the three UART PTE bytes, sourced from the invariant's [kpt_mem]: the
   walk reads root[0]->l1_dev, l1_dev[128]->l0_dev 32, l0_dev 32[0]->uart leaf. *)
Lemma uart_kpt_bytes (root : mword 44) (s : mstate) :
  kpt_mem s root ->
  (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add (pte_addr_at root (subrange_vec_dec uart_vpn 26 18)) j)
     = Some (nth_byte (mk_pte (kpt_l1_dev root) PTE_PTR) j))
  /\ (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add (pte_addr_at (kpt_l1_dev root) (subrange_vec_dec uart_vpn 17 9)) j)
     = Some (nth_byte (mk_pte (kpt_l0_of root uart_vpn) PTE_PTR) j))
  /\ (forall j : nat, (N.of_nat j < 8)%N ->
     s.(mem) !! (pa_add (pte_addr_at (kpt_l0_of root uart_vpn) (subrange_vec_dec uart_vpn 8 0)) j)
     = Some (nth_byte (mk_pte (kpt_leaf_ppn uart_vpn) PTE_DEV) j)).
Proof.
  intros (H0 & _H2 & Hl1 & _Hl2 & Hleaf).
  assert (Huv2 : subrange_vec_dec uart_vpn 26 18 = (mword_of_int 0 : mword 9))
    by (apply bv_eq; vm_compute; reflexivity).
  assert (Huv1 : subrange_vec_dec uart_vpn 17 9 = (mword_of_int 128 : mword 9))
    by (apply bv_eq; vm_compute; reflexivity).
  split; [| split].
  - (* root[0] -> l1_dev *)
    rewrite Huv2. exact H0.
  - (* l1_dev[128] -> l0_dev 32 = l0_of uart_vpn *)
    intros j Hj.
    specialize (Hl1 (subrange_vec_dec uart_vpn 17 9)).
    rewrite Huv1 in Hl1.
    assert (Hi : 96 <= bv_unsigned (mword_of_int 128 : mword 9) < 129)
      by (assert (bv_unsigned (mword_of_int 128 : mword 9) = 128) as -> by (vm_compute; reflexivity); lia).
    specialize (Hl1 Hi j Hj).
    (* l0_dev (128-96) = l0_dev 32 = l0_of uart_vpn *)
    assert (Hle : kpt_l0_dev root (bv_unsigned (mword_of_int 128 : mword 9) - 96) = kpt_l0_of root uart_vpn).
    { rewrite uart_l0_of_eq. reflexivity. }
    rewrite Hle in Hl1. rewrite Huv1. exact Hl1.
  - (* l0 leaf -> uart leaf *)
    intros j Hj.
    specialize (Hleaf uart_vpn uart_kpt_mapped j Hj).
    unfold kpt_slot0_pa, vpn0_of, kpt_leaf_pte in Hleaf.
    rewrite uart_lflags_eq in Hleaf.
    exact Hleaf.
Qed.

(* the filled entry the UART walk installs IS the kernel PT's own uart entry. *)
Lemma uart_filled_is_kpt (root : mword 44) :
  uart_tlb_ent (kpt_leaf_ppn uart_vpn) (mk_pte (kpt_leaf_ppn uart_vpn) PTE_DEV)
    (kpt_slot0_pa root uart_vpn)
  = kpt_tlb_ent root uart_vpn.
Proof.
  unfold uart_tlb_ent, kpt_tlb_ent, kpt_leaf_pte. rewrite uart_lflags_eq. reflexivity.
Qed.

(* filling the UART hash slot with the uart entry preserves [tlb_consistent (P_kpt root)]. *)
Lemma uart_kpt_fill (root : mword 44) (tlbvec : vec (option TLB_Entry) (2 ^ 6)) :
  tlb_consistent (P_kpt root) tlbvec ->
  tlb_consistent (P_kpt root)
    (vec_update_dec tlbvec (tlb_hash (__id 39) uart_vpn) (Some (kpt_tlb_ent root uart_vpn))).
Proof.
  intro Hcons.
  apply (tlb_consistent_fill (P_kpt root) tlbvec (kpt_tlb_ent root uart_vpn)
           (tlb_hash (__id 39) uart_vpn) (tlb_hash_range uart_vpn) (P_kpt_uart root) Hcons).
Qed.
