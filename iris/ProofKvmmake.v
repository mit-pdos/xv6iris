(* ProofKvmmake.v -- whole-function proof of kvmmake (kernel/vm.c):
   kalloc a fresh root page, memset it, run the six kvmmap regions
   (UART/VIRTIO/PLIC RW, text RX, data RW, trampoline RX) then
   proc_mapstacks.  Straight-line code, no branches; every failure arm is
   dead under the 166-page budget.

   The file opens with the PURE LAYER: the pt_missing upper-bound kit, the
   census kit (structural lower bound pinning pt_nodes = 102), and the
   KvmMap region facts (no-remap + presence lookups per accumulator).  The
   sealed functor [KvmmakeProof] follows. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad list_numbers bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore RegFile WpMmodeLeafBase.
Require Import IntrDefs WpSmodeIntr WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpNext.
Require Import WpLock CpuOwn.
Require Import CalleeSaved StackOwn.
Require Import InstrBytes KernelText.
Require Import KallocInv.
Require Import ByteBuf.   (* bb_choose: a window of existentials is an existential function *)
Require Import PtTree PtBuild KptPt KptExecMap KMap KptTree KvmMap KvmSpec.
Require Import CodeKvmmake.
Require Import SpecKalloc SpecMemset SpecKvmmap SpecProcMapstacks SpecKvmmake.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* PURE LAYER §A -- pt_missing upper-bound kit.                           *)
(* ===================================================================== *)

Lemma sum_list_with_1 {A} (l : list A) : sum_list_with (fun _ => 1%nat) l = length l.
Proof. induction l; cbn; lia. Qed.

Lemma l0_absent_le_1 (t : ptree) (q : Z) : (l0_absent t q <= 1)%nat.
Proof.
  unfold l0_absent. destruct (pt_kids t (mword_of_int (q / 512) : mword 9)); [| lia].
  destruct (pt_kids _ (mword_of_int (q mod 512) : mword 9)); lia.
Qed.

Lemma l1_absent_le_1 (t : ptree) (r : Z) : (l1_absent t r <= 1)%nat.
Proof. unfold l1_absent. destruct (pt_kids t (mword_of_int r : mword 9)); lia. Qed.

Lemma l0count_le_len (t : ptree) (lo hi : Z) :
  (l0count t lo hi <= Z.to_nat (hi - lo + 1))%nat.
Proof.
  unfold l0count.
  transitivity (sum_list_with (fun _ => 1%nat) (seqZ lo (hi - lo + 1))).
  { apply sum_list_with_le. intros x _. apply l0_absent_le_1. }
  rewrite sum_list_with_1. rewrite length_seqZ. lia.
Qed.

Lemma l1count_le_len (t : ptree) (lo hi : Z) :
  (l1count t lo hi <= Z.to_nat (hi - lo + 1))%nat.
Proof.
  unfold l1count.
  transitivity (sum_list_with (fun _ => 1%nat) (seqZ lo (hi - lo + 1))).
  { apply sum_list_with_le. intros x _. apply l1_absent_le_1. }
  rewrite sum_list_with_1. rewrite length_seqZ. lia.
Qed.

(* dropping one provably-present group *)
Lemma sum_indicator_drop (L : list Z) (a : Z) :
  base.NoDup L -> a ∈ L ->
  (sum_list_with (fun k => if decide (k = a) then 0%nat else 1%nat) L + 1 = length L)%nat.
Proof.
  intros Hnd Hin.
  pose proof (sum_list_with_override (fun _ => 1%nat) L a 0%nat Hnd Hin) as Hov.
  rewrite sum_list_with_1 in Hov. cbn beta in Hov. lia.
Qed.

Lemma l0count_le_present (t : ptree) (lo hi a : Z) :
  (lo <= a <= hi)%Z -> l0_absent t a = 0%nat ->
  (l0count t lo hi <= Z.to_nat (hi - lo))%nat.
Proof.
  intros Ha Habs. unfold l0count.
  transitivity (sum_list_with (fun k => if decide (k = a) then 0%nat else 1%nat) (seqZ lo (hi - lo + 1))).
  { apply sum_list_with_le. intros x _.
    destruct (decide (x = a)) as [->|_]; [rewrite Habs; lia | apply l0_absent_le_1]. }
  pose proof (sum_indicator_drop (seqZ lo (hi - lo + 1)) a (NoDup_seqZ _ _)
                ltac:(apply elem_of_seqZ; lia)) as Hd.
  rewrite length_seqZ in Hd.
  assert (Hsucc : Z.to_nat (hi - lo + 1) = S (Z.to_nat (hi - lo))).
  { rewrite (Z2Nat.inj_add (hi - lo) 1 ltac:(lia) ltac:(lia)). cbn. lia. }
  lia.
Qed.

Lemma l1count_le_present (t : ptree) (lo hi a : Z) :
  (lo <= a <= hi)%Z -> l1_absent t a = 0%nat ->
  (l1count t lo hi <= Z.to_nat (hi - lo))%nat.
Proof.
  intros Ha Habs. unfold l1count.
  transitivity (sum_list_with (fun k => if decide (k = a) then 0%nat else 1%nat) (seqZ lo (hi - lo + 1))).
  { apply sum_list_with_le. intros x _.
    destruct (decide (x = a)) as [->|_]; [rewrite Habs; lia | apply l1_absent_le_1]. }
  pose proof (sum_indicator_drop (seqZ lo (hi - lo + 1)) a (NoDup_seqZ _ _)
                ltac:(apply elem_of_seqZ; lia)) as Hd.
  rewrite length_seqZ in Hd.
  assert (Hsucc : Z.to_nat (hi - lo + 1) = S (Z.to_nat (hi - lo))).
  { rewrite (Z2Nat.inj_add (hi - lo) 1 ltac:(lia) ltac:(lia)). cbn. lia. }
  lia.
Qed.

(* pt_rep0 gives the two present-group facts at a mapped vpn *)
Lemma pt_rep0_absent_0 (t : ptree) (m : gmap (mword 27) (mword 64)) (vpn : mword 27) (w : mword 64) :
  pt_rep0 t m -> m !! vpn = Some w ->
  l0_absent t (bv_unsigned vpn / 512) = 0%nat /\
  l1_absent t (bv_unsigned vpn / 262144) = 0%nat.
Proof.
  intros (Hmap & _) Hl. destruct (Hmap vpn w Hl) as (p2 & p1 & Hpm).
  pose proof (ptree_maps_level0 t vpn p2 p1 w Hpm) as Hl0.
  split; [ exact (ptree_level0_l0_absent t vpn p2 p1 w Hl0)
         | exact (ptree_level0_l1_absent t vpn p2 p1 w Hl0) ].
Qed.

Lemma pt_missing_empty (b : mword 44) (v : mword 27) :
  pt_missing (pt_empty_node b) v 1 = 2%nat.
Proof.
  rewrite pt_missing_1_eq. unfold l0_absent, l1_absent, pt_empty_node. cbn [pt_kids]. reflexivity.
Qed.

(* ===================================================================== *)
(* PURE LAYER §B -- census kit (structural pt_nodes lower bound).         *)
(* ===================================================================== *)

Lemma sum_list_with_submseteq {A} (f : A -> nat) (l1 l2 : list A) :
  l1 ⊆+ l2 -> (sum_list_with f l1 <= sum_list_with f l2)%nat.
Proof. induction 1; cbn; lia. Qed.

Lemma seqZ_sublist_sum (F : Z -> nat) (js : list Z) (lo len : Z) :
  base.NoDup js -> (forall j, j ∈ js -> lo <= j < lo + len) ->
  (sum_list_with F js <= sum_list_with F (seqZ lo len))%nat.
Proof.
  intros Hnd Hin. apply sum_list_with_submseteq.
  apply NoDup_submseteq; [exact Hnd |].
  intros x Hx. apply elem_of_seqZ. apply Hin. exact Hx.
Qed.

(* a level-1 node with [length js] distinct present kid slots has >= 1 + length js nodes *)
Lemma pt_nodes_lvl1_ge (c : ptree) (js : list Z) :
  base.NoDup js ->
  (forall j, j ∈ js -> (0 <= j < 512)%Z /\ is_Some (pt_kids c (mword_of_int j : mword 9))) ->
  (1 + length js <= pt_nodes_lvl 1 c)%nat.
Proof.
  intros Hnd Hall. rewrite pt_nodes_lvl_S.
  set (G := fun k => pt_kid_nodes 0 (pt_kids c (mword_of_int k : mword 9))).
  assert (Hjs : (length js <= sum_list_with G js)%nat).
  { rewrite <- (sum_list_with_1 js).
    apply sum_list_with_le. intros x Hx.
    destruct (Hall x Hx) as (_ & c0 & Hc0). unfold G. rewrite Hc0. cbn [pt_kid_nodes]. cbn [pt_nodes_lvl]. lia. }
  assert (Hsub : (sum_list_with G js <= sum_list_with G (seqZ 0 512))%nat).
  { apply (seqZ_sublist_sum G js 0 512 Hnd).
    intros j Hj. destruct (Hall j Hj) as (Hb & _). lia. }
  lia.
Qed.

(* the root node's census: sum of witnessed level-1 node bounds + 1 *)
Lemma pt_nodes_ge_census (t : ptree) (iset : list Z) (lb : Z -> nat) :
  base.NoDup iset ->
  (forall i, i ∈ iset -> (0 <= i < 512)%Z /\
     exists c, pt_kids t (mword_of_int i : mword 9) = Some c /\ (lb i <= pt_nodes_lvl 1 c)%nat) ->
  (1 + sum_list_with lb iset <= pt_nodes t)%nat.
Proof.
  intros Hnd Hall. unfold pt_nodes. rewrite (pt_nodes_lvl_S 1 t).
  set (G := fun k => pt_kid_nodes 1 (pt_kids t (mword_of_int k : mword 9))).
  assert (Hlb : (sum_list_with lb iset <= sum_list_with G iset)%nat).
  { apply sum_list_with_le. intros x Hx.
    destruct (Hall x Hx) as (_ & c & Hc & Hbnd). unfold G. rewrite Hc. cbn [pt_kid_nodes]. exact Hbnd. }
  assert (Hsub : (sum_list_with G iset <= sum_list_with G (seqZ 0 512))%nat).
  { apply (seqZ_sublist_sum G iset 0 512 Hnd).
    intros i Hi. destruct (Hall i Hi) as (Hb & _). lia. }
  lia.
Qed.

(* pt_rep0 kid extraction: a mapped vpn's root/L0 kids are present *)
Lemma rep_kid_present (t : ptree) (m : gmap (mword 27) (mword 64)) (vpn : mword 27) (w : mword 64) :
  pt_rep0 t m -> m !! vpn = Some w ->
  exists c, pt_kids t (vpn_idx 2 vpn) = Some c /\ is_Some (pt_kids c (vpn_idx 1 vpn)).
Proof.
  intros (Hmap & _) Hl. destruct (Hmap vpn w Hl) as (p2 & p1 & c1 & c0 & Hk2 & Hk1 & _).
  exists c1. split; [exact Hk2 | exists c0; exact Hk1].
Qed.

(* ===================================================================== *)
(* PURE LAYER §C -- KvmMap region facts: accumulator no-remap + presence  *)
(* lookups, the census (pt_nodes >= 102), and kstacks_missing = 0.        *)
(* ===================================================================== *)

Local Ltac lebT := apply (proj2 (Z.leb_le _ _)); lia.
Local Ltac lebF := apply (proj2 (Z.leb_gt _ _)); lia.
Local Ltac ltbT := apply (proj2 (Z.ltb_lt _ _)); lia.
Local Ltac ltbF := apply (proj2 (Z.ltb_ge _ _)); lia.

(* ---- the six kvmmap calls' no-remap facts ---- *)
Lemma kvm_m1_none_virtio : kvm_m1 !! virtio_vpn = None.
Proof.
  rewrite kvm_m1_peel. rewrite virtio_vpn_uns.
  assert ((0x10000 <=? 0x10001) && (0x10001 <? 0x10001) = false) as -> by (apply andb_false_iff; right; ltbF).
  reflexivity.
Qed.

Lemma kvm_m2_none_plic (v : mword 27) : (0xC000 <= bv_unsigned v < 0x10000)%Z -> kvm_m2 !! v = None.
Proof.
  intro H. rewrite kvm_m2_peel.
  assert ((0x10001 <=? bv_unsigned v) && (bv_unsigned v <? 0x10002) = false) as -> by (apply andb_false_iff; left; lebF).
  rewrite kvm_m1_peel.
  assert ((0x10000 <=? bv_unsigned v) && (bv_unsigned v <? 0x10001) = false) as -> by (apply andb_false_iff; left; lebF).
  reflexivity.
Qed.

Lemma kvm_m3_none_text (v : mword 27) : (0x80000 <= bv_unsigned v < 0x80007)%Z -> kvm_m3 !! v = None.
Proof.
  intro H. rewrite kvm_m3_peel.
  assert ((0xC000 <=? bv_unsigned v) && (bv_unsigned v <? 0x10000) = false) as -> by (apply andb_false_iff; right; ltbF).
  rewrite kvm_m2_peel.
  assert ((0x10001 <=? bv_unsigned v) && (bv_unsigned v <? 0x10002) = false) as -> by (apply andb_false_iff; right; ltbF).
  rewrite kvm_m1_peel.
  assert ((0x10000 <=? bv_unsigned v) && (bv_unsigned v <? 0x10001) = false) as -> by (apply andb_false_iff; right; ltbF).
  reflexivity.
Qed.

Lemma kvm_m4_none_data (v : mword 27) : (0x80007 <= bv_unsigned v < 0x88000)%Z -> kvm_m4 !! v = None.
Proof.
  intro H. rewrite kvm_m4_peel.
  assert ((0x80000 <=? bv_unsigned v) && (bv_unsigned v <? 0x80007) = false) as -> by (apply andb_false_iff; right; ltbF).
  rewrite kvm_m3_peel.
  assert ((0xC000 <=? bv_unsigned v) && (bv_unsigned v <? 0x10000) = false) as -> by (apply andb_false_iff; right; ltbF).
  rewrite kvm_m2_peel.
  assert ((0x10001 <=? bv_unsigned v) && (bv_unsigned v <? 0x10002) = false) as -> by (apply andb_false_iff; right; ltbF).
  rewrite kvm_m1_peel.
  assert ((0x10000 <=? bv_unsigned v) && (bv_unsigned v <? 0x10001) = false) as -> by (apply andb_false_iff; right; ltbF).
  reflexivity.
Qed.

Lemma kvm_m5_none_tramp : kvm_m5 !! tramp_vpn = None.
Proof.
  rewrite kvm_m5_peel.
  assert ((0x80007 <=? bv_unsigned tramp_vpn) && (bv_unsigned tramp_vpn <? 0x88000) = false) as ->
    by (rewrite tramp_vpn_uns; apply andb_false_iff; right; ltbF).
  rewrite kvm_m4_peel.
  assert ((0x80000 <=? bv_unsigned tramp_vpn) && (bv_unsigned tramp_vpn <? 0x80007) = false) as ->
    by (rewrite tramp_vpn_uns; apply andb_false_iff; right; ltbF).
  rewrite kvm_m3_peel.
  assert ((0xC000 <=? bv_unsigned tramp_vpn) && (bv_unsigned tramp_vpn <? 0x10000) = false) as ->
    by (rewrite tramp_vpn_uns; apply andb_false_iff; right; ltbF).
  rewrite kvm_m2_peel.
  assert ((0x10001 <=? bv_unsigned tramp_vpn) && (bv_unsigned tramp_vpn <? 0x10002) = false) as ->
    by (rewrite tramp_vpn_uns; apply andb_false_iff; right; ltbF).
  rewrite kvm_m1_peel.
  assert ((0x10000 <=? bv_unsigned tramp_vpn) && (bv_unsigned tramp_vpn <? 0x10001) = false) as ->
    by (rewrite tramp_vpn_uns; apply andb_false_iff; right; ltbF).
  reflexivity.
Qed.

(* ---- presence facts feeding the pt_missing upper bounds ---- *)
Lemma kvm_m1_uart_some : is_Some (kvm_m1 !! uart_vpn).
Proof.
  rewrite kvm_m1_peel. rewrite uart_vpn_uns.
  assert ((0x10000 <=? 0x10000) && (0x10000 <? 0x10001) = true) as -> by (apply andb_true_iff; split; [lebT | ltbT]).
  eexists; reflexivity.
Qed.

Lemma kvm_m2_uart_some : is_Some (kvm_m2 !! uart_vpn).
Proof.
  rewrite kvm_m2_peel. rewrite uart_vpn_uns.
  assert ((0x10001 <=? 0x10000) && (0x10000 <? 0x10002) = false) as -> by (apply andb_false_iff; left; lebF).
  rewrite kvm_m1_peel. rewrite uart_vpn_uns.
  assert ((0x10000 <=? 0x10000) && (0x10000 <? 0x10001) = true) as -> by (apply andb_true_iff; split; [lebT | ltbT]).
  eexists; reflexivity.
Qed.

Lemma kvm_m4_text_some : is_Some (kvm_m4 !! text_vpn0).
Proof.
  rewrite kvm_m4_peel. rewrite text_vpn_uns.
  assert ((0x80000 <=? 0x80000) && (0x80000 <? 0x80007) = true) as -> by (apply andb_true_iff; split; [lebT | ltbT]).
  eexists; reflexivity.
Qed.

(* ---- kmap_class forward evaluation (device / dram ranges) ---- *)
Lemma kmap_class_dev_some (v : mword 27) : (0xC000 <= bv_unsigned v < 0x10002)%Z -> is_Some (kmap_class v).
Proof.
  intro H. unfold kmap_class.
  assert ((0x80000 <=? bv_unsigned v) && (bv_unsigned v <? 0x80007) = false) as -> by (apply andb_false_iff; left; lebF).
  assert ((0xC000 <=? bv_unsigned v) && (bv_unsigned v <? 0x10002) = true) as Ht by (apply andb_true_iff; split; [lebT | ltbT]).
  rewrite Ht orb_true_r. eexists; reflexivity.
Qed.

Lemma kmap_class_dram_some (v : mword 27) : (0x80000 <= bv_unsigned v < 0x88000)%Z -> is_Some (kmap_class v).
Proof.
  intro H. unfold kmap_class.
  destruct ((0x80000 <=? bv_unsigned v) && (bv_unsigned v <? 0x80007)) eqn:E1.
  - eexists; reflexivity.
  - apply andb_false_iff in E1.
    assert (Hge : (0x80007 <= bv_unsigned v)%Z).
    { destruct E1 as [E1 | E1]; [apply Z.leb_gt in E1; lia | apply Z.ltb_ge in E1; lia]. }
    assert ((0x80007 <=? bv_unsigned v) && (bv_unsigned v <? 0x88000) = true) as Ht
      by (apply andb_true_iff; split; [lebT | ltbT]).
    rewrite Ht orb_true_l. eexists; reflexivity.
Qed.

Lemma kmap_class_tramp : kmap_class tramp_vpn = None.
Proof. unfold kmap_class. rewrite tramp_vpn_uns. vm_compute. reflexivity. Qed.

Lemma kvm_map_some_of_class (v : mword 27) : is_Some (kmap_class v) -> is_Some (kvm_map !! v).
Proof. intros [pc Hpc]. rewrite kvm_map_lookup. rewrite Hpc. eexists; reflexivity. Qed.

Lemma kvm_map_some_tramp : is_Some (kvm_map !! tramp_vpn).
Proof.
  rewrite kvm_map_lookup. rewrite kmap_class_tramp.
  destruct (decide (tramp_vpn = tramp_vpn)) as [_ | Hne]; [eexists; reflexivity | congruence].
Qed.

(* ---- census witness arithmetic ---- *)
Lemma census_witness_idx (i2 i1 : Z) : (0 <= i2 < 512)%Z -> (0 <= i1 < 512)%Z ->
  vpn_idx 2 (mword_of_int (i2 * 262144 + i1 * 512) : mword 27) = (mword_of_int i2 : mword 9) /\
  vpn_idx 1 (mword_of_int (i2 * 262144 + i1 * 512) : mword 27) = (mword_of_int i1 : mword 9).
Proof.
  intros H2 H1.
  assert (Hv : bv_unsigned (mword_of_int (i2 * 262144 + i1 * 512) : mword 27) = i2 * 262144 + i1 * 512)
    by (apply mword27_unsigned; nia).
  split.
  - rewrite <- (group_i2 (mword_of_int (i2 * 262144 + i1 * 512) : mword 27)). rewrite Hv. f_equal.
    rewrite (Z.div_add_l i2 262144 (i1 * 512) ltac:(lia)).
    rewrite (Z.div_small (i1 * 512) 262144 ltac:(nia)). lia.
  - rewrite <- (group_i1_of_q0 (mword_of_int (i2 * 262144 + i1 * 512) : mword 27)). rewrite Hv. f_equal.
    replace (i2 * 262144 + i1 * 512)%Z with ((i2 * 512 + i1) * 512)%Z by lia.
    rewrite (Z.div_mul (i2 * 512 + i1) 512 ltac:(lia)).
    replace (i2 * 512 + i1)%Z with (i1 + i2 * 512)%Z by lia.
    rewrite (Z_mod_plus_full i1 i2 512). rewrite (Z.mod_small i1 512 ltac:(lia)). reflexivity.
Qed.

Lemma census_dev_witness (i1 : Z) : (96 <= i1 <= 128)%Z ->
  is_Some (kvm_map !! (mword_of_int (0 * 262144 + i1 * 512) : mword 27)).
Proof.
  intro H. apply kvm_map_some_of_class. apply kmap_class_dev_some.
  rewrite (mword27_unsigned (0 * 262144 + i1 * 512) ltac:(nia)). lia.
Qed.

Lemma census_dram_witness (i1 : Z) : (0 <= i1 <= 63)%Z ->
  is_Some (kvm_map !! (mword_of_int (2 * 262144 + i1 * 512) : mword 27)).
Proof.
  intro H. apply kvm_map_some_of_class. apply kmap_class_dram_some.
  rewrite (mword27_unsigned (2 * 262144 + i1 * 512) ltac:(nia)). lia.
Qed.

Lemma tramp_idx :
  vpn_idx 2 tramp_vpn = (mword_of_int 255 : mword 9) /\ vpn_idx 1 tramp_vpn = (mword_of_int 511 : mword 9).
Proof.
  split.
  - rewrite <- (group_i2 tramp_vpn). rewrite tramp_vpn_uns. reflexivity.
  - rewrite <- (group_i1_of_q0 tramp_vpn). rewrite tramp_vpn_uns. reflexivity.
Qed.

(* a present sub-kid at a parametric witness *)
Lemma census_present (t : ptree) (i2 i1 : Z) (c : ptree) :
  pt_rep0 t kvm_map -> (0 <= i2 < 512)%Z -> (0 <= i1 < 512)%Z ->
  is_Some (kvm_map !! (mword_of_int (i2 * 262144 + i1 * 512) : mword 27)) ->
  pt_kids t (mword_of_int i2 : mword 9) = Some c ->
  is_Some (pt_kids c (mword_of_int i1 : mword 9)).
Proof.
  intros Hrep H2 H1 [w Hw] Hc.
  destruct (rep_kid_present t kvm_map _ w Hrep Hw) as (c' & Hk2 & Hk1).
  destruct (census_witness_idx i2 i1 H2 H1) as (E2 & E1).
  rewrite E2 in Hk2. rewrite E1 in Hk1. rewrite Hc in Hk2. injection Hk2 as <-. exact Hk1.
Qed.

Lemma census_root_kid (t : ptree) (i2 i1 : Z) :
  pt_rep0 t kvm_map -> (0 <= i2 < 512)%Z -> (0 <= i1 < 512)%Z ->
  is_Some (kvm_map !! (mword_of_int (i2 * 262144 + i1 * 512) : mword 27)) ->
  exists c, pt_kids t (mword_of_int i2 : mword 9) = Some c.
Proof.
  intros Hrep H2 H1 [w Hw].
  destruct (rep_kid_present t kvm_map _ w Hrep Hw) as (c & Hk2 & _).
  destruct (census_witness_idx i2 i1 H2 H1) as (E2 & _).
  rewrite E2 in Hk2. exists c. exact Hk2.
Qed.

(* the census: the built table has at least 102 nodes *)
Lemma pt_nodes_ge_102 (t : ptree) : pt_rep0 t kvm_map -> (102 <= pt_nodes t)%nat.
Proof.
  intro Hrep.
  pose (lb := fun i : Z => if (i =? 0)%Z then 34%nat else if (i =? 2)%Z then 65%nat else 2%nat).
  assert (Hsum : sum_list_with lb [0; 2; 255]%Z = 101%nat) by (unfold lb; vm_compute; reflexivity).
  apply (Nat.le_trans _ (1 + sum_list_with lb [0; 2; 255]%Z)%nat); [rewrite Hsum; lia |].
  apply (pt_nodes_ge_census t [0; 2; 255]%Z lb).
  - apply NoDup_cons_2; [set_solver |].
    apply NoDup_cons_2; [set_solver |].
    apply NoDup_cons_2; [set_solver |].
    apply NoDup_nil_2.
  - intros i Hi.
    apply elem_of_cons in Hi as [-> | Hi].
    { (* device l1 group 0 : 33 kids in [96,128] *)
      split; [lia |].
      destruct (census_root_kid t 0 96 Hrep ltac:(lia) ltac:(lia) (census_dev_witness 96 ltac:(lia))) as [c Hc].
      exists c. split; [exact Hc |].
      assert (Hlb : lb 0 = 34%nat) by (unfold lb; reflexivity). rewrite Hlb.
      apply (Nat.le_trans _ (1 + length (seqZ 96 33))%nat).
      { rewrite length_seqZ. reflexivity. }
      apply (pt_nodes_lvl1_ge c (seqZ 96 33)); [apply NoDup_seqZ |].
      intros j Hj. apply elem_of_seqZ in Hj.
      split; [lia |].
      apply (census_present t 0 j c Hrep ltac:(lia) ltac:(lia) (census_dev_witness j ltac:(lia)) Hc). }
    apply elem_of_cons in Hi as [-> | Hi].
    { (* text/data l1 group 2 : 64 kids in [0,63] *)
      split; [lia |].
      destruct (census_root_kid t 2 0 Hrep ltac:(lia) ltac:(lia) (census_dram_witness 0 ltac:(lia))) as [c Hc].
      exists c. split; [exact Hc |].
      assert (Hlb : lb 2 = 65%nat) by (unfold lb; reflexivity). rewrite Hlb.
      apply (Nat.le_trans _ (1 + length (seqZ 0 64))%nat).
      { rewrite length_seqZ. reflexivity. }
      apply (pt_nodes_lvl1_ge c (seqZ 0 64)); [apply NoDup_seqZ |].
      intros j Hj. apply elem_of_seqZ in Hj.
      split; [lia |].
      apply (census_present t 2 j c Hrep ltac:(lia) ltac:(lia) (census_dram_witness j ltac:(lia)) Hc). }
    apply elem_of_cons in Hi as [-> | Hi]; [| by apply elem_of_nil in Hi].
    { (* trampoline l1 group 255 : 1 kid at slot 511 *)
      split; [lia |].
      destruct (tramp_idx) as [T2 T1].
      destruct kvm_map_some_tramp as [w Hw].
      destruct (rep_kid_present t kvm_map tramp_vpn w Hrep Hw) as (c & Hk2 & Hk1).
      rewrite T2 in Hk2. rewrite T1 in Hk1.
      exists c. split; [exact Hk2 |].
      assert (Hlb : lb 255 = 2%nat) by (unfold lb; reflexivity). rewrite Hlb.
      apply (Nat.le_trans _ (1 + length [511%Z])%nat); [reflexivity |].
      apply (pt_nodes_lvl1_ge c [511%Z]); [apply NoDup_singleton |].
      intros j Hj. apply elem_of_list_singleton in Hj. subst j. split; [lia | exact Hk1]. }
Qed.

(* every kstack vpn (i<64) lives in the trampoline's l0/l1 groups *)
Lemma kstack_groups (i : nat) : (i < 64)%nat ->
  (bv_unsigned (kstack_vpn i) / 512 = 131071)%Z /\ (bv_unsigned (kstack_vpn i) / 262144 = 255)%Z.
Proof.
  intro Hi. rewrite (kstack_vpn_uns i Hi).
  set (d := (2 * (Z.of_nat i + 1))%Z). assert (Hd : (2 <= d <= 128)%Z) by (unfold d; lia).
  split.
  - replace (0x3FFFFFF - d)%Z with (131071 * 512 + (511 - d))%Z by lia.
    rewrite (Z.div_add_l 131071 512 (511 - d) ltac:(lia)).
    rewrite (Z.div_small (511 - d) 512 ltac:(lia)). lia.
  - replace (0x3FFFFFF - d)%Z with (255 * 262144 + (262143 - d))%Z by lia.
    rewrite (Z.div_add_l 255 262144 (262143 - d) ltac:(lia)).
    rewrite (Z.div_small (262143 - d) 262144 ltac:(lia)). lia.
Qed.

(* kstacks_missing = 0 on the built table (all kstack vpns share the tramp groups) *)
Lemma kstacks_missing_zero (t : ptree) : pt_rep0 t kvm_map -> kstacks_missing t = 0%nat.
Proof.
  intro Hrep.
  destruct kvm_map_some_tramp as [w Hw].
  destruct (pt_rep0_absent_0 t kvm_map tramp_vpn w Hrep Hw) as (Hl0 & Hl1).
  rewrite tramp_vpn_uns in Hl0, Hl1.
  assert (Ht0 : (0x3FFFFFF / 512 = 131071)%Z) by (vm_compute; reflexivity).
  assert (Ht1 : (0x3FFFFFF / 262144 = 255)%Z) by (vm_compute; reflexivity).
  rewrite Ht0 in Hl0. rewrite Ht1 in Hl1.
  unfold kstacks_missing.
  rewrite (sum_list_with_ext' (fun i => pt_missing t (kstack_vpn i) 1) (fun _ => 0%nat) (seq 0 64)).
  - apply sum_list_with_0.
  - intros i Hi. apply elem_of_seq in Hi. destruct Hi as [_ Hi].
    rewrite pt_missing_1_eq.
    destruct (kstack_groups i ltac:(lia)) as (Hg0 & Hg1).
    rewrite Hg0 Hg1. rewrite Hl0 Hl1. reflexivity.
Qed.

(* the pms no-remap: every kstack vpn is absent from the built kvm_map
   (disjoint from the static class ranges and from the trampoline). *)
Lemma kmk_kstack_None (i : nat) : (i < 64)%nat -> kvm_map !! kstack_vpn i = None.
Proof.
  intro Hi. rewrite kvm_map_lookup. rewrite (kstack_not_class (kstack_vpn i) i Hi eq_refl).
  rewrite decide_False; [reflexivity | apply kstack_not_tramp; exact Hi].
Qed.

(* ===================================================================== *)
(* PURE LAYER §D -- the six per-call pt_missing upper bounds (budget       *)
(* ledger 2/0/32/2/63/2, summing to 101) and perm_ok 6/10.                *)
(* ===================================================================== *)

Local Ltac nat_le := apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
Local Ltac nat_lt := apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity.
Local Ltac z_le := apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity.

Lemma pt_missing_pos (t : ptree) (v : mword 27) (n : nat) : (0 < n)%nat ->
  pt_missing t v n =
    (l0count t (bv_unsigned v / 512) ((bv_unsigned v + Z.of_nat n - 1) / 512)
   + l1count t (bv_unsigned v / 262144) ((bv_unsigned v + Z.of_nat n - 1) / 262144))%nat.
Proof. intro Hn. unfold pt_missing. destruct n; [inversion Hn | reflexivity]. Qed.

Lemma bound_uart (b : mword 44) : (pt_missing (pt_empty_node b) uart_vpn 1 <= 2)%nat.
Proof. rewrite pt_missing_empty. nat_le. Qed.

Lemma bound_virtio (t : ptree) : pt_rep0 t kvm_m1 -> (pt_missing t virtio_vpn 1 <= 0)%nat.
Proof.
  intro Hrep. destruct kvm_m1_uart_some as [w Hw].
  destruct (pt_rep0_absent_0 t kvm_m1 uart_vpn w Hrep Hw) as (Hl0 & Hl1).
  rewrite uart_vpn_uns in Hl0, Hl1.
  rewrite pt_missing_1_eq. rewrite virtio_vpn_uns.
  replace (0x10001 / 512)%Z with (0x10000 / 512)%Z by (vm_compute; reflexivity).
  replace (0x10001 / 262144)%Z with (0x10000 / 262144)%Z by (vm_compute; reflexivity).
  rewrite Hl0 Hl1. nat_le.
Qed.

Lemma bound_plic (t : ptree) : pt_rep0 t kvm_m2 -> (pt_missing t plic_vpn plic_npages <= 32)%nat.
Proof.
  intro Hrep. destruct kvm_m2_uart_some as [w Hw].
  destruct (pt_rep0_absent_0 t kvm_m2 uart_vpn w Hrep Hw) as (_ & Hl1).
  rewrite uart_vpn_uns in Hl1.
  replace (0x10000 / 262144)%Z with 0%Z in Hl1 by (vm_compute; reflexivity).
  rewrite (pt_missing_pos t plic_vpn plic_npages ltac:(unfold plic_npages; nat_lt)).
  rewrite plic_vpn_uns.
  replace (Z.of_nat plic_npages) with 16384%Z by (unfold plic_npages; vm_compute; reflexivity).
  replace (0xC000 / 262144)%Z with 0%Z by (vm_compute; reflexivity).
  replace ((0xC000 + 16384 - 1) / 262144)%Z with 0%Z by (vm_compute; reflexivity).
  apply Nat.le_trans with (32 + 0)%nat; [| nat_le].
  apply Nat.add_le_mono.
  - eapply Nat.le_trans; [apply l0count_le_len |].
    replace (Z.to_nat ((0xC000 + 16384 - 1) / 512 - 0xC000 / 512 + 1)) with 32%nat by (vm_compute; reflexivity).
    apply Nat.le_refl.
  - eapply Nat.le_trans; [apply (l1count_le_present t 0 0 0 ltac:(split; z_le) Hl1) |].
    replace (Z.to_nat (0 - 0)) with 0%nat by (vm_compute; reflexivity).
    apply Nat.le_refl.
Qed.

Lemma bound_text (t : ptree) : (pt_missing t text_vpn0 text_npages <= 2)%nat.
Proof.
  rewrite (pt_missing_pos t text_vpn0 text_npages ltac:(unfold text_npages; nat_lt)).
  rewrite text_vpn_uns.
  replace (Z.of_nat text_npages) with 7%Z by (unfold text_npages; vm_compute; reflexivity).
  apply Nat.le_trans with (1 + 1)%nat; [| nat_le].
  apply Nat.add_le_mono.
  - eapply Nat.le_trans; [apply l0count_le_len |].
    replace (Z.to_nat ((0x80000 + 7 - 1) / 512 - 0x80000 / 512 + 1)) with 1%nat by (vm_compute; reflexivity).
    apply Nat.le_refl.
  - eapply Nat.le_trans; [apply l1count_le_len |].
    replace (Z.to_nat ((0x80000 + 7 - 1) / 262144 - 0x80000 / 262144 + 1)) with 1%nat by (vm_compute; reflexivity).
    apply Nat.le_refl.
Qed.

Lemma bound_data (t : ptree) : pt_rep0 t kvm_m4 -> (pt_missing t data_vpn0 data_npages <= 63)%nat.
Proof.
  intro Hrep. destruct kvm_m4_text_some as [w Hw].
  destruct (pt_rep0_absent_0 t kvm_m4 text_vpn0 w Hrep Hw) as (Hl0 & Hl1).
  rewrite text_vpn_uns in Hl0, Hl1.
  replace (0x80000 / 512)%Z with 1024%Z in Hl0 by (vm_compute; reflexivity).
  replace (0x80000 / 262144)%Z with 2%Z in Hl1 by (vm_compute; reflexivity).
  rewrite (pt_missing_pos t data_vpn0 data_npages ltac:(unfold data_npages; nat_lt)).
  rewrite data_vpn_uns.
  replace (Z.of_nat data_npages) with 32761%Z by (unfold data_npages; vm_compute; reflexivity).
  replace (0x80007 / 262144)%Z with 2%Z by (vm_compute; reflexivity).
  replace ((0x80007 + 32761 - 1) / 262144)%Z with 2%Z by (vm_compute; reflexivity).
  replace (0x80007 / 512)%Z with 1024%Z by (vm_compute; reflexivity).
  replace ((0x80007 + 32761 - 1) / 512)%Z with 1087%Z by (vm_compute; reflexivity).
  apply Nat.le_trans with (63 + 0)%nat; [| nat_le].
  apply Nat.add_le_mono.
  - eapply Nat.le_trans; [apply (l0count_le_present t 1024 1087 1024 ltac:(split; z_le) Hl0) |].
    replace (Z.to_nat (1087 - 1024)) with 63%nat by (vm_compute; reflexivity).
    apply Nat.le_refl.
  - eapply Nat.le_trans; [apply (l1count_le_present t 2 2 2 ltac:(split; z_le) Hl1) |].
    replace (Z.to_nat (2 - 2)) with 0%nat by (vm_compute; reflexivity).
    apply Nat.le_refl.
Qed.

Lemma bound_tramp (t : ptree) : (pt_missing t tramp_vpn 1 <= 2)%nat.
Proof.
  rewrite pt_missing_1_eq.
  apply Nat.le_trans with (1 + 1)%nat; [| nat_le].
  apply Nat.add_le_mono; [apply l0_absent_le_1 | apply l1_absent_le_1].
Qed.

Lemma kmk_perm_ok6 : mappages_perm_ok 6.
Proof.
  unfold mappages_perm_ok. split; [lia|].
  split; [intro s; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma kmk_perm_ok10 : mappages_perm_ok 10.
Proof.
  unfold mappages_perm_ok. split; [lia|].
  split; [intro s; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

(* clean-context (mword-free) nat arithmetic for the budget ledger, so the
   zify hook (broken by this file's heavy imports whenever an mword is in
   context) never sees these -- the WP body applies them as closed facts. *)
Lemma budget_arm (pm bnd gs Bprev nb : nat) :
  (pm <= bnd)%nat -> (gs <= Bprev)%nat ->
  (1 + Bprev + bnd <= 102)%nat -> (166 < nb)%nat ->
  (pm < nb - (1 + gs))%nat.
Proof. lia. Qed.

Lemma avail_recomb (nb a b : nat) :
  avail_sub (Some (nb - (1 + a))%nat) b = avail_sub (Some nb) (1 + (a + b))%nat.
Proof. rewrite !avail_sub_Some. f_equal. lia. Qed.

Lemma gsum_step (gs Bprev g bnd : nat) :
  (gs <= Bprev)%nat -> (g <= bnd)%nat -> (gs + g <= Bprev + bnd)%nat.
Proof. lia. Qed.

Lemma pms_budget_arm (gs B nb : nat) :
  (gs <= B)%nat -> (1 + B <= 102)%nat -> (166 < nb)%nat ->
  (64 + 0 < nb - (1 + gs))%nat.
Proof. lia. Qed.

(* ===================================================================== *)
(* THE WP HOUSE.                                                          *)
(* ===================================================================== *)

Section KvmmakeHouse.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  Ltac peel_reg :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ];
    reflexivity.

  (* ================================================================= *)
  (* THE SEALED EPILOGUE (+0xa2..+0xac): mv a0,s1; restore ra/s0/s1;    *)
  (* addi sp,32; ret -- producing the success-only kvmmake post.        *)
  (* ================================================================= *)
  (* [CID0] is its OWN binder here (shadowing the section's fixed [Context
     CID]): this epilogue is invoked from [wp_kvmmake_sconf_gen] only after
     the prologue + six regions + proc_mapstacks have each already migrated
     the hart some [b]-generic number of times, so its own entry hart need
     not be the whole function's.  Its OWN [wp_next] obligation, though, is
     handed straight to the CALLER's outer [Hcont] (the [KVMMAKE] contract's,
     stated relative to the whole function's TRUE entry [CID]) -- so THAT
     [wp_next] must be pinned to [CID] explicitly, exactly as
     [ProofUvmdealloc.wp_uvmdealloc_epi] is. *)
  Lemma wp_kvmmake_epilogue_sconf `{CID0 : CpuId} (γa : gname)
      (mm Mf : regfile) (tf : ptree) (pas : nat -> mword 44)
      (K lvl : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
    lvl = 0%nat ->
    (48 <= K)%nat ->
    (b = false \/ p = zero_reg -> (CID0 : CPU) = (CID : CPU)) ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 9 : mword 5)
      = zero_extend' 64 (concat_vec (pt_base tf) (zeros' 12 : mword 12)) ->
    Mf !!! Regidx (mword_of_int 18 : mword 5) = mm !!! Regidx (mword_of_int 18) ->
    Mf !!! Regidx (mword_of_int 19 : mword 5) = mm !!! Regidx (mword_of_int 19) ->
    Mf !!! Regidx (mword_of_int 20 : mword 5) = mm !!! Regidx (mword_of_int 20) ->
    Mf !!! Regidx (mword_of_int 21 : mword 5) = mm !!! Regidx (mword_of_int 21) ->
    Mf !!! Regidx (mword_of_int 22 : mword 5) = mm !!! Regidx (mword_of_int 22) ->
    Mf !!! Regidx (mword_of_int 23 : mword 5) = mm !!! Regidx (mword_of_int 23) ->
    Mf !!! Regidx (mword_of_int 24 : mword 5) = mm !!! Regidx (mword_of_int 24) ->
    Mf !!! Regidx (mword_of_int 25 : mword 5) = mm !!! Regidx (mword_of_int 25) ->
    Mf !!! Regidx (mword_of_int 26 : mword 5) = mm !!! Regidx (mword_of_int 26) ->
    Mf !!! Regidx (mword_of_int 27 : mword 5) = mm !!! Regidx (mword_of_int 27) ->
    pt_rep0 tf (kvm_map_full pas) ->
    pt_nodes tf = 102%nat ->
    kvm_pas_ok pas ->
    sie_cap_gpr Mf (K - 4)%nat b p -∗ cpu_own lvl eb p b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.kvmmake + 0xa2)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    (∃ v4 : bv 64, pa_stk sp0 4 ↦₈ v4) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γa (avail_sub on K_kvmmake) -∗
    ([∗ list] i ∈ seq 0 64,
       page_own (zero_extend' 64 (concat_vec (pas i) (zeros' 12 : mword 12)))) -∗
    wp_next (CID0 := CID) b p (fun (CID : CpuId) =>
      ∀ (mr : regfile) (t : ptree) (pas' : nat -> mword 44),
      sie_cap_gpr mr K b p -∗ cpu_own lvl eb p b lks -∗ pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t -∗
      ⌜mr !!! Regidx (mword_of_int 10)
         = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))⌝ -∗
      ⌜pt_rep0 t (kvm_map_full pas')⌝ -∗
      ⌜pt_nodes t = 102%nat⌝ -∗
      kalloc_env γa (avail_sub on K_kvmmake) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜kvm_pas_ok pas'⌝ -∗
      ([∗ list] i ∈ seq 0 64,
         page_own (zero_extend' 64 (concat_vec (pas' i) (zeros' 12 : mword 12)))) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr ret_tgt Hlvl HK Hcross Hsp Hs1 Hx18 Hx19 Hx20 Hx21 Hx22 Hx23 Hx24 Hx25 Hx26 Hx27
      Hrep Hnodes Hpasok.
    iIntros "Hcg Hcnt #Htext Hpc Hc1 Hc2 Hc3 Hc4 Hptree Henv Hpages Hcont".
    (* the frame-cell address facts *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 4 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (kmki_a2 with "Htext") as "Hia2".
    iPoseProof (kmki_a4 with "Htext") as "Hia4".
    iPoseProof (kmki_a6 with "Htext") as "Hia6".
    iPoseProof (kmki_a8 with "Htext") as "Hia8".
    iPoseProof (kmki_aa with "Htext") as "Hiaa".
    iPoseProof (kmki_ac with "Htext") as "Hiac".
    (* +0xa2 mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0xa2)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              Mf (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia2").
    iIntros (CID1 Hs1cr) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (E0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (Mf !!! Regidx (mword_of_int 9 : mword 5)))]> Mf).
    assert (Hpa4 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0xa2) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa4) in "Hpc".
    assert (HE0sp : E0 !!! Regidx csp_rs1 = spr) by (rewrite /E0; rewrite upd_ne; [| reg_neq]; exact Hsp).
    (* +0xa4 ld ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kvmmake + 0xa4)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              E0 (K - 4)%nat (mm !!! Regidx (mword_of_int 1 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia4 [Hc1]").
    { iEval (rewrite HE0sp Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2cr) "Hcg Hpc Hc1". iEval (rewrite HE0sp Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> E0).
    assert (Hpa6 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0xa4) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa6) in "Hpc".
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1; rewrite upd_ne; [| reg_neq]; exact HE0sp).
    (* +0xa6 ld s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kvmmake + 0xa6)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 4)%nat (mm !!! Regidx (mword_of_int 8 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia6 [Hc2]").
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3cr) "Hcg Hpc Hc2". iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hpa8 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0xa6) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa8) in "Hpc".
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2; rewrite upd_ne; [| reg_neq]; exact HE1sp).
    (* +0xa8 ld s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.kvmmake + 0xa8)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 4)%nat (mm !!! Regidx (mword_of_int 9 : mword 5)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia8 [Hc3]").
    { iEval (rewrite HE2sp Hb3). iExact "Hc3". }
    iIntros (CID4 Hs4cr) "Hcg Hpc Hc3". iEval (rewrite HE2sp Hb3) in "Hc3".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hpaa : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0xa8) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0xaa)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpaa) in "Hpc".
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3; rewrite upd_ne; [| reg_neq]; exact HE2sp).
    (* +0xaa addi sp,sp,32 -- the frame pop *)
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HE3sp. unfold spr. apply frame_cancel_32. }
    assert (Hpop : E3 !!! Regidx csp_rs1
                   = pa_stk (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HE3sp. symmetry. exact Hsprstk. }
    iAssert (stack_own sp0 4) with "[Hc1 Hc2 Hc3 Hc4]" as "Hframe".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hc1". { iExists (mm !!! Regidx (mword_of_int 1)). iExact "Hc1". }
      iSplitL "Hc2". { iExists (mm !!! Regidx (mword_of_int 8)). iExact "Hc2". }
      iSplitL "Hc3". { iExists (mm !!! Regidx (mword_of_int 9)). iExact "Hc3". }
      iSplitL "Hc4". { iDestruct "Hc4" as (v4) "Hc4". iExists v4. iExact "Hc4". }
      done. }
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.kvmmake + 0xaa)) (mword_of_int 2 : mword 6)
              E3 (K - 4)%nat 4 b Hpop with "Hcg Hpc Hiaa Hframe").
    iIntros (CID5 Hs5cr) "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpac : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0xaa) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpac) in "Hpc".
    (* +0xac ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by peel_reg.
    assert (Hrt : ret_pc (E4 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt) by (rewrite HE4ra; reflexivity).
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.kvmmake + 0xac)) (mword_of_int 1 : mword 5) E4 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hiac").
    iIntros (CID6 Hs6cr) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    iEval (rewrite Hrt) in "Hpc".
    (* a0 = root byte address *)
    assert (HE4a0 : E4 !!! Regidx (mword_of_int 10 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base tf) (zeros' 12 : mword 12))).
    { rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3. rewrite upd_ne; [| reg_neq].
      rewrite /E2. rewrite upd_ne; [| reg_neq]. rewrite /E1. rewrite upd_ne; [| reg_neq].
      rewrite /E0 upd_eq. rewrite add_vec_zero_l. exact Hs1. }
    iDestruct (cpu_own_transport CID0 CID6 lvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID6 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! E4 tf pas with "Hcg Hcnt Hpc Hptree [%] [%] [%] Henv [%] [%] Hpages").
    { exact HE4a0. }
    { exact Hrep. }
    { exact Hnodes. }
    { (* callee_saved mm E4 *)
      unfold callee_saved.
      split. { rewrite /E4 upd_eq. rewrite HE3sp. unfold spr. apply frame_cancel_32. }
      split. { rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3. rewrite upd_ne; [| reg_neq]. rewrite /E2 upd_eq. reflexivity. }
      split. { rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3 upd_eq. reflexivity. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Hx18. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Hx19. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Hx20. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Hx21. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Hx22. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Hx23. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Hx24. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Hx25. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Hx26. }
      { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Hx27. } }
    { exact Hpasok. }
  Qed.

End KvmmakeHouse.

(* clean-context cap bounds (no mword in scope, so [lia] is safe here). *)
Lemma cap_bounds (K : nat) : (48 <= K)%nat ->
  (4 <= K)%nat /\ (2 <= K - 4)%nat /\ (14 <= K - 4)%nat /\
  (34 <= K - 4)%nat /\ (44 <= K - 4)%nat.
Proof. lia. Qed.

Lemma lt1 (i : nat) : (i < 1)%nat -> i = 0%nat.
Proof. lia. Qed.

(* Z-only (bv-free) node-page range arithmetic, so [lia] never sees a bv. *)
(* The lower bound is [PageGeom.kmem_lo] -- kalloc's own [page_in_range]
   floor, which IS the dumped `end` symbol -- rather than a transcribed
   address: its body is a [Z] literal computed from [KernelSyms.end_], so
   [unfold kmem_lo] leaves [lia] a number to work with. *)
Lemma kdata_bound_arith (z : Z) :
  (z mod 4096 = 0)%Z -> (kmem_lo <= z)%Z -> (z < 0x88000000)%Z ->
  (ram_base <= z)%Z /\ (z + 4096 <= ram_base + ram_size)%Z.
Proof.
  intros Hm Hlo Hhi. apply Z.mod_divide in Hm; [| lia]. destruct Hm as [k Hk].
  unfold kmem_lo in Hlo. unfold ram_base, ram_size. lia.
Qed.

Lemma kda_arith (z : Z) : (kmem_lo <= z)%Z -> (text_end <= z)%Z.
Proof. unfold text_end, kmem_lo. lia. Qed.

(* per-region no-remap arithmetic: from the nat page index bound derive the
   [vpn_at]-fit (< 2^27) and the region-disjointness range for the §C none
   lemmas.  Stated mword-free so [lia] is safe (the region proofs, which have
   an mword in context, apply them as closed facts). *)
Lemma nlt_Z (i n : nat) : (i < n)%nat -> (Z.of_nat i < Z.of_nat n)%Z.
Proof. intro H. apply (proj1 (Nat2Z.inj_lt i n)). exact H. Qed.
Lemma plic_range (z : Z) : (0 <= z)%Z -> (z < 16384)%Z ->
  (0xC000 + z < 134217728)%Z /\ (0xC000 <= 0xC000 + z < 0x10000)%Z.
Proof. intros. lia. Qed.
Lemma text_range (z : Z) : (0 <= z)%Z -> (z < 7)%Z ->
  (0x80000 + z < 134217728)%Z /\ (0x80000 <= 0x80000 + z < 0x80007)%Z.
Proof. intros. lia. Qed.
Lemma data_range (z : Z) : (0 <= z)%Z -> (z < 32761)%Z ->
  (0x80007 + z < 134217728)%Z /\ (0x80007 <= 0x80007 + z < 0x88000)%Z.
Proof. intros. lia. Qed.
Lemma plic_bounds (i : nat) : (i < 16384)%nat ->
  (0xC000 + Z.of_nat i < 134217728)%Z /\ (0xC000 <= 0xC000 + Z.of_nat i < 0x10000)%Z.
Proof. intro H. apply plic_range; [apply Nat2Z.is_nonneg | change 16384%Z with (Z.of_nat 16384); apply nlt_Z; exact H]. Qed.
Lemma text_bounds (i : nat) : (i < 7)%nat ->
  (0x80000 + Z.of_nat i < 134217728)%Z /\ (0x80000 <= 0x80000 + Z.of_nat i < 0x80007)%Z.
Proof. intro H. apply text_range; [apply Nat2Z.is_nonneg | change 7%Z with (Z.of_nat 7); apply nlt_Z; exact H]. Qed.
Lemma data_bounds (i : nat) : (i < 32761)%nat ->
  (0x80007 + Z.of_nat i < 134217728)%Z /\ (0x80007 <= 0x80007 + Z.of_nat i < 0x88000)%Z.
Proof. intro H. apply data_range; [apply Nat2Z.is_nonneg | change 32761%Z with (Z.of_nat 32761); apply nlt_Z; exact H]. Qed.

(* running growth-sum ledger (mword-free so [lia] is safe): each region's
   growth bound accumulates into the next region's [gsprev] bound. *)
Lemma acc_step (s g ob gb nb : nat) :
  (s <= ob)%nat -> (g <= gb)%nat -> (ob + gb <= nb)%nat -> (s + g <= nb)%nat.
Proof. lia. Qed.

(* the census pin: the individual growth bounds (2/0/32/2/63/2, sum 101) plus
   the structural lower bound [102 <= pt_nodes t6] force pt_nodes t6 = 102 and
   the growth-sum = 101 exactly. *)
Lemma pin_all (n6 g1 g2 g3 g4 g5 g6 : nat) :
  n6 = (1 + g1 + g2 + g3 + g4 + g5 + g6)%nat ->
  (g1 <= 2)%nat -> (g2 <= 0)%nat -> (g3 <= 32)%nat -> (g4 <= 2)%nat -> (g5 <= 63)%nat -> (g6 <= 2)%nat ->
  (102 <= n6)%nat ->
  n6 = 102%nat /\ (0 + g1 + g2 + g3 + g4 + g5 + g6)%nat = 101%nat.
Proof. lia. Qed.

Lemma kmk_consume (nb gt g7 : nat) :
  (166 < nb)%nat -> gt = 101%nat -> g7 = 0%nat ->
  ((nb - (1 + gt)) - (64 + g7))%nat = (nb - K_kvmmake)%nat.
Proof. lia. Qed.

(* ===================================================================== *)
(* STEP 3-4: prologue (4-slot frame push, ra/s0/s1 saves, s0:=sp+32),     *)
(* the root kalloc, and memset -> the empty root node [t0].  Sealed and    *)
(* parameterized by the callee WP lemmas so it compiles standalone.        *)
(* ===================================================================== *)
Section KvmmakeBody.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* Each callee hypothesis is [CID]-GENERIC (its own fresh `{CID} binder,
     shadowing this Section's fixed ambient one): every one of the region /
     prologue helpers below invokes it only after several of its OWN
     [b]-generic leaf steps have already migrated the hart away from this
     Section's entry, so a hypothesis pinned to the Section's own [CID]
     would not apply at the call site.  Left implicit-generic here, each
     call's own implicit gets resolved from the resource ("Hcg"/"Hcnt")
     already held at that point -- no explicit [CID:=...] needed at any
     call site. *)
  Hypothesis wp_kalloc :
    forall `{CID : CpuId} (γl : gname) (γk : gname * gname)
      (fl : mword 64) (m : regfile) (on : option nat)
      (n : nat) (eb : bool) (p : mword 64) (K : nat) (b : bool) (lks : gset string),
      wp_kalloc_sconf_body γl γk fl m on n eb p K b lks.
  Hypothesis wp_memset :
    forall `{CID : CpuId} (m0 : regfile) (n : nat) (len : nat)
      (cval : mword 64) (olds : nat -> bv 8) (b : bool) (pcur : mword 64),
      wp_memset_sconf_body m0 n len cval olds b pcur.
  Hypothesis wp_kvmmap :
    forall `{CID : CpuId} (γa : gname) (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (lvl K : nat)
      (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string),
      wp_kvmmap_sconf_body γa mm t m npages perm lvl K eb p on b lks.
  Hypothesis wp_pms :
    forall `{CID : CpuId} (γa : gname) (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (lvl K : nat)
      (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string),
      wp_proc_mapstacks_sconf_body γa mm t m lvl K eb p on b lks.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.
  Ltac peel_reg_step :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].
  Ltac peel_reg := peel_reg_step; reflexivity.

  Lemma wp_kmk_prologue_node `{CID0 : CpuId}
      (γa : gname) (mm : regfile) (K : nat)
      (eb : bool) (p : mword 64) (nb : nat) (b : bool) (lks : gset string) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    locks_below lks "kmem" ->
    (48 <= K)%nat ->
    (K_kvmmake < nb)%nat ->
    sie_cap_gpr mm K b p -∗
    cpu_own 0%nat eb p b lks -∗ kernel_text -∗
    pc_is (mword_of_int KernelSyms.kvmmake) -∗
    kalloc_env γa (Some nb) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (M : regfile) (bppn : mword 44),
      sie_cap_gpr M (K - 4)%nat b p -∗
      cpu_own 0%nat eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.kvmmake + 0x18)) -∗
      ptree_own 2 (DfracOwn 1) (pt_empty_node bppn) -∗
      kalloc_env γa (avail_sub (Some nb) 1) -∗
      pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
      pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
      pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
      (∃ v4 : bv 64, pa_stk sp0 4 ↦₈ v4) -∗
      ⌜M !!! Regidx (mword_of_int 9)
         = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))⌝ -∗
      ⌜M !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜M !!! Regidx (mword_of_int 18) = mm !!! Regidx (mword_of_int 18)⌝ -∗
      ⌜M !!! Regidx (mword_of_int 19) = mm !!! Regidx (mword_of_int 19)⌝ -∗
      ⌜M !!! Regidx (mword_of_int 20) = mm !!! Regidx (mword_of_int 20)⌝ -∗
      ⌜M !!! Regidx (mword_of_int 21) = mm !!! Regidx (mword_of_int 21)⌝ -∗
      ⌜M !!! Regidx (mword_of_int 22) = mm !!! Regidx (mword_of_int 22)⌝ -∗
      ⌜M !!! Regidx (mword_of_int 23) = mm !!! Regidx (mword_of_int 23)⌝ -∗
      ⌜M !!! Regidx (mword_of_int 24) = mm !!! Regidx (mword_of_int 24)⌝ -∗
      ⌜M !!! Regidx (mword_of_int 25) = mm !!! Regidx (mword_of_int 25)⌝ -∗
      ⌜M !!! Regidx (mword_of_int 26) = mm !!! Regidx (mword_of_int 26)⌝ -∗
      ⌜M !!! Regidx (mword_of_int 27) = mm !!! Regidx (mword_of_int 27)⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr Hbelow HK Hnb.
    pose proof (cap_bounds K HK) as (Hc4 & Hc2 & Hc14 & Hc34 & Hc44).
    iIntros "Hcg Hcnt #Htext Hpc Henv Hcont".
    (* frame-cell address facts (same 4-slot frame as the sealed epilogue) *)
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (kmki_00 with "Htext") as "Hi00".
    iPoseProof (kmki_02 with "Htext") as "Hi02".
    iPoseProof (kmki_04 with "Htext") as "Hi04".
    iPoseProof (kmki_06 with "Htext") as "Hi06".
    iPoseProof (kmki_08 with "Htext") as "Hi08".
    iPoseProof (kmki_0a with "Htext") as "Hi0a".
    iPoseProof (kmki_0e with "Htext") as "Hi0e".
    iPoseProof (kmki_10 with "Htext") as "Hi10".
    iPoseProof (kmki_12 with "Htext") as "Hi12".
    iPoseProof (kmki_14 with "Htext") as "Hi14".
    (* +0x00 addi sp,sp,-32 : 4-slot frame push *)
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = pa_stk (mm !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf (mword_of_int KernelSyms.kvmmake) (mword_of_int 32 : mword 6) mm K 4 b Hc4 Hpush
              with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    iDestruct "S3" as (v3) "Hc3". iDestruct "S4" as (v4) "Hc4".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr) by (rewrite /W1; rewrite upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KernelSyms.kvmmake : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,24(sp) -> slot 1 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 4)%nat v1 b with "Hcg Hpc Hi02 [Hc1]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1". iEval (rewrite HspW1 Hb1) in "Hc1".
    iEval (rgne) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,16(sp) -> slot 2 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 4)%nat v2 b with "Hcg Hpc Hi04 [Hc2]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2". iEval (rewrite HspW1 Hb2) in "Hc2".
    iEval (rgne) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 sd s1,8(sp) -> slot 3 *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              W1 (K - 4)%nat v3 b with "Hcg Hpc Hi06 [Hc3]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc3". iEval (rewrite HspW1 Hb3) in "Hc3".
    iEval (rgne) in "Hc3".
    assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r9) in "Hc3".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 addi s0,sp,32 (value unused; s0 reloaded from slot 2 at the epilogue) *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 4)%nat b ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> W1).
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a jal kalloc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095636 : mword 21)
              W2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x0a) : mword 64) 4)]> W2).
    assert (Htgtk : add_vec (mword_of_int (KernelSyms.kvmmake + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095636 : mword 21)) = mword_of_int KernelSyms.kalloc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtk) in "Hpc".
    iDestruct "Henv" as (γk) "(#Hlock & Havail)".
    assert (HJsp : J !!! Regidx csp_rs1 = spr).
    { rewrite /J /W2. repeat (rewrite upd_ne; [| reg_neq]). exact HspW1. }
    iDestruct (cpu_own_transport CID0 CID6 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (wp_kalloc γa γk (mword_of_int (KernelSyms.kmem + 24))
              J (Some nb) 0%nat eb p (K - 4)%nat b lks
              Hc14
              ltac:(reflexivity)
              ltac:(vm_compute; reflexivity)
              Hbelow
              with "Hcg Hcnt Htext Hpc Hlock Havail").
    iIntros (CID7 Hs7 mr0) "Hcg Hcnt Hpc %Hkcs0 Hkpost".
    assert (Hret0e : ret_pc (J !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kvmmake + 0x0e)).
    { rewrite /J upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret0e) in "Hpc".
    (* success arm: nb > 166 so kalloc cannot fail *)
    assert (Hcnt : Some nb = Some (S (nb - 1))).
    { f_equal. lia. }
    iEval (rewrite Hcnt) in "Hkpost".
    iDestruct (kalloc_post_success with "Hkpost") as "(%Hpv & Hpage & Havail2)".
    assert (Hav1 : Some (nb - 1)%nat = avail_sub (Some nb) 1).
    { rewrite avail_sub_Some. reflexivity. }
    iEval (rewrite Hav1) in "Havail2".
    iAssert (kalloc_env γa (avail_sub (Some nb) 1))
      with "[Havail2]" as "Henv".
    { iExists γk. iFrame "Hlock Havail2". }
    set (root0 := mr0 !!! Regidx (mword_of_int 10 : mword 5)).
    (* recover callee-saved through kalloc *)
    assert (Hmr0sp : mr0 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs0 csp_rs1 ltac:(vm_compute; reflexivity)). exact HJsp. }
    (* +0x0e mv s1,a0 : s1 := root page *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mr0 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (M1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (mr0 !!! Regidx (mword_of_int 10 : mword 5)))]> mr0).
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 lui a2,0x1 : a2 := 4096 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x10)) (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              M1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi10").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (M2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> M1).
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* +0x12 li a1,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x12)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
              M2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi12").
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (M3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> M2).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x12) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 jal memset *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x14)) (mword_of_int 1 : mword 5) (mword_of_int 2096036 : mword 21)
              M3 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x14) : mword 64) 4)]> M3).
    assert (Htgtm : add_vec (mword_of_int (KernelSyms.kvmmake + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2096036 : mword 21)) = mword_of_int KernelSyms.memset) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtm) in "Hpc".
    (* memset(root, 0, 4096): bridge page_own to the per-byte buffer *)
    assert (HM4a0 : M4 !!! Regidx (mword_of_int 10 : mword 5) = root0).
    { rewrite /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HM4a1 : M4 !!! Regidx (mword_of_int 11 : mword 5) = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))).
    { rewrite /M4. rewrite upd_ne; [| reg_neq]. rewrite /M3 upd_eq. reflexivity. }
    assert (HM4a2 : M4 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int (Z.of_nat 4096)).
    { rewrite /M4 /M3. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M2 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite /page_own /byte_any) in "Hpage".
    iDestruct (bb_choose 4096 0 (fun j b => ((pa_add root0 j) ↦ₘ b)%I) with "Hpage") as (olds) "Hbuf".
    iApply (wp_memset M4 (K - 4)%nat 4096 (M4 !!! Regidx (mword_of_int 11 : mword 5)) olds b p
              Hc2 ltac:(vm_compute; reflexivity) ltac:(reflexivity) HM4a2
              with "Hcg Htext Hpc [Hbuf]").
    { iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H". rewrite HM4a0. iExact "H". }
    iIntros (CID12 Hs12 mfin) "Hcg Hpc Hbytes %Hmcs".
    assert (Hret18 : ret_pc (M4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kvmmake + 0x18)).
    { rewrite /M4 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret18) in "Hpc".
    (* the written buffer is all-zero bytes *)
    assert (Hcb : nth_byte (autocast (T := mword) (subrange_vec_dec (M4 !!! Regidx (mword_of_int 11 : mword 5)) (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 = (mword_of_int 0 : mword 8)).
    { rewrite HM4a1. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hcb HM4a0) in "Hbytes".
    (* page facts: alignment + range *)
    pose proof Hpv as Hpv'. destruct Hpv' as [Hpal [Hplo Hphi]].
    unfold page_aligned, PGSIZE in Hpal. unfold page_in_range, kmem_lo, kmem_hi in Hplo, Hphi.
    rewrite uint_unsigned in Hpal, Hplo, Hphi.
    set (bppn := autocast (T := mword) (subrange_vec_dec root0 55 12) : mword 44).
    assert (Hpbase : zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12)) = root0).
    { unfold bppn. apply walk_alloc_page_base.
      - rewrite uint_unsigned. exact Hpal.
      - rewrite uint_unsigned. apply (Z.lt_trans _ 0x88000000); [exact Hphi | apply Z.ltb_lt; vm_compute; reflexivity]. }
    (* physical-tier bytes + node claim from the static kdata claims *)
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
    iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
    iDestruct (mem_page_to_phys root0 (DfracOwn 1) (mword_of_int 0 : mword 8)
                 ltac:(intros j Hj; apply kdata_svpn_class; apply page_in_range_addr_is_kdata; [exact Hpv | exact Hj])
                 with "Hkmapb Hbytes") as "Hbytes".
    iEval (rewrite -Hpbase) in "Hbytes".
    assert (Hbppn4k : bv_unsigned bppn * 4096 = bv_unsigned root0).
    { rewrite <- (page_base_unsigned bppn). rewrite Hpbase. reflexivity. }
    assert (Hnpv : page_valid (page_base bppn)).
    { unfold page_base. rewrite Hpbase. exact Hpv. }
    iDestruct (pt_node_claim_from_static bppn Hnpv with "Hkmapb") as "#Hbclaim".
    iDestruct (zero_page_to_node 2 (DfracOwn 1) bppn with "Hbclaim Hbytes") as "Hptree".
    (* callee-saved recovery for the output register-map [mfin] *)
    assert (Hbase9 : mfin !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { rewrite (callee_saved_lookup Hmcs (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /M4 /M3 /M2. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M1 upd_eq.
      rewrite add_vec_zero_l. rewrite Hpbase. reflexivity. }
    assert (Hfsp : mfin !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hmcs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr0sp. }
    (* the s2..s11 registers: untouched since [mm] (through kalloc/memset callee-saved) *)
    iDestruct (cpu_own_transport CID7 CID12 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID12 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! mfin bppn with "Hcg Hcnt Hpc Hptree Henv Hc1 Hc2 Hc3 [Hc4] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]").
    { iExists v4. iExact "Hc4". }
    { exact Hbase9. }
    { exact Hfsp. }
    all: try (
      match goal with
      | |- _ !!! Regidx (mword_of_int ?k) = _ !!! Regidx (mword_of_int ?k) =>
        rewrite (callee_saved_lookup Hmcs (mword_of_int k) ltac:(vm_compute; reflexivity));
        rewrite /M4 /M3 /M2 /M1; repeat (rewrite upd_ne; [| reg_neq]);
        rewrite (callee_saved_lookup Hkcs0 (mword_of_int k) ltac:(vm_compute; reflexivity));
        rewrite /J /W2 /W1; repeat (rewrite upd_ne; [| reg_neq]); reflexivity
      end).
  Qed.

  (* ================================================================= *)
  (* REGION 1 -- UART (+0x18..+0x24): li a4,6; lui a3,0x1; lui a2,      *)
  (* 0x10000000; mv a1,a2; mv a0,s1; jal kvmmap.  t0 = pt_empty_node.   *)
  (* ================================================================= *)
  Lemma wp_kmk_region_uart `{CID0 : CpuId}
      (γa : gname) (mm M : regfile) (bppn : mword 44)
      (K : nat) (eb : bool) (p : mword 64) (nb gsprev : nat) (b : bool) (lks : gset string) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    locks_below lks "kmem" ->
    (48 <= K)%nat ->
    (166 < nb)%nat ->
    (gsprev <= 0)%nat ->
    M !!! Regidx csp_rs1 = spr ->
    M !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12)) ->
    sie_cap_gpr M (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.kvmmake + 0x18)) -∗
    ptree_own 2 (DfracOwn 1) (pt_empty_node bppn) -∗
    kalloc_env γa (avail_sub (Some nb) (1 + gsprev)) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
      sie_cap_gpr mr (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.kvmmake + 0x28)) -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γa (avail_sub (Some nb) (1 + (gsprev + g))) -∗
      ⌜callee_saved M mr⌝ -∗
      ⌜mr !!! Regidx (mword_of_int 9) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))⌝ -∗
      ⌜mr !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜pt_base t' = bppn⌝ -∗
      ⌜pt_rep0 t' kvm_m1⌝ -∗
      ⌜pt_nodes t' = (1 + g)%nat⌝ -∗
      ⌜(g <= 2)%nat⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr Hbelow HK Hnb Hgs Hsp HM9.
    pose proof (cap_bounds K HK) as (Hc4 & Hc2 & Hc14 & Hc34 & Hc44).
    iIntros "Hcg Hcnt #Htext Hpc Hptree Henv Hcont".
    iPoseProof (kmki_18 with "Htext") as "Hi18".
    iPoseProof (kmki_1a with "Htext") as "Hi1a".
    iPoseProof (kmki_1c with "Htext") as "Hi1c".
    iPoseProof (kmki_20 with "Htext") as "Hi20".
    iPoseProof (kmki_22 with "Htext") as "Hi22".
    iPoseProof (kmki_24 with "Htext") as "Hi24".
    (* +0x18 li a4,6 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x18)) (mword_of_int 14 : mword 5) (mword_of_int 6 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))
              M (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi18").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (U14 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))]> M).
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x18) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* +0x1a lui a3,0x1 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x1a)) (mword_of_int 13 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              U14 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi1a").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (U13 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> U14).
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x1a) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    (* +0x1c lui a2,0x10000 *)
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x1c)) (mword_of_int 12 : mword 5) (mword_of_int 65536 : mword 20) (luival (mword_of_int 65536 : mword 20))
              U13 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi1c").
    iIntros (CID3 Hs3) "Hcg Hpc".
    set (U12 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (mword_of_int 65536 : mword 20))]> U13).
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    (* +0x20 mv a1,a2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x20)) (mword_of_int 11 : mword 5) (mword_of_int 12 : mword 5)
              U12 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi20").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (U12 !!! Regidx (mword_of_int 12 : mword 5)))]> U12).
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    (* +0x22 mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x22)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              U11 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi22").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (U10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (U11 !!! Regidx (mword_of_int 9 : mword 5)))]> U11).
    assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x22) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24 jal kvmmap *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x24)) (mword_of_int 1 : mword 5) (mword_of_int 2097076 : mword 21)
              U10 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi24").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (Wk := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x24) : mword 64) 4)]> U10).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.kvmmake + 0x24) : mword 64) (sign_extend' 64 (mword_of_int 2097076 : mword 21)) = mword_of_int KernelSyms.kvmmap) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt) in "Hpc".
    (* register values at the kvmmap entry *)
    assert (HWka1 : Wk !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int 0x10000000).
    { rewrite /Wk /U10. repeat (rewrite upd_ne; [| reg_neq]). rewrite /U11 upd_eq. rewrite add_vec_zero_l.
      rewrite /U12 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka2 : Wk !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 0x10000000).
    { rewrite /Wk /U10 /U11. repeat (rewrite upd_ne; [| reg_neq]). rewrite /U12 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka3 : Wk !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int (Z.of_nat 1 * 4096)).
    { rewrite /Wk /U10 /U11 /U12. repeat (rewrite upd_ne; [| reg_neq]). rewrite /U13 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka4 : Wk !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 6).
    { rewrite /Wk /U10 /U11 /U12 /U13. repeat (rewrite upd_ne; [| reg_neq]). rewrite /U14 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka0 : Wk !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { rewrite /Wk. rewrite upd_ne; [| reg_neq]. rewrite /U10 upd_eq. rewrite add_vec_zero_l.
      rewrite /U11 /U12 /U13 /U14. repeat (rewrite upd_ne; [| reg_neq]). exact HM9. }
    assert (HWksp : Wk !!! Regidx csp_rs1 = spr).
    { rewrite /Wk /U10 /U11 /U12 /U13 /U14. repeat (rewrite upd_ne; [| reg_neq]). exact Hsp. }
    (* the represented map is empty (kvm_m0); ppn0 folds to uart_ppn *)
    assert (Hppn : (autocast (T := mword) (subrange_vec_dec (Wk !!! Regidx (mword_of_int 12 : mword 5)) 55 12) : mword 44) = uart_ppn).
    { rewrite HWka2. apply bv_eq; vm_compute; reflexivity. }
    assert (Hsvpn : svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5)) = uart_vpn) by (rewrite HWka1; apply bv_eq; vm_compute; reflexivity).
    assert (Havin : avail_sub (Some nb) (1 + gsprev) = Some (nb - (1 + gsprev))%nat) by (rewrite avail_sub_Some; reflexivity).
    iEval (rewrite Havin) in "Henv".
    (* budget arm *)
    assert (Hbud : (pt_missing (pt_empty_node bppn) (svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5))) 1 < nb - (1 + gsprev))%nat).
    { rewrite Hsvpn. apply (budget_arm _ 2 gsprev 0 nb (bound_uart bppn) Hgs ltac:(nat_le) Hnb). }
    iDestruct (cpu_own_transport CID0 CID6 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (wp_kvmmap γa Wk (pt_empty_node bppn) ∅ 1 6 0%nat (K - 4)%nat eb p (Some (nb - (1 + gsprev))%nat) b lks
              ltac:(vm_compute; reflexivity) Hc34 ltac:(rewrite HWka0; rewrite pt_empty_node_base; reflexivity)
              ltac:(rewrite HWka1; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HWka2; apply bv_eq; vm_compute; reflexivity)
              HWka3 ltac:(nat_le) HWka4 kmk_perm_ok6
              ltac:(rewrite HWka1; rewrite uint_unsigned; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
              ltac:(rewrite HWka2; rewrite uint_unsigned; apply (proj1 (Z.ltb_lt _ _)); vm_compute; reflexivity)
              (pt_rep0_empty bppn)
              ltac:(intros i Hi; rewrite (lt1 i Hi); apply lookup_empty)
              ltac:(eexists; split; [reflexivity | exact Hbud])
              Hbelow
              with "Hcg Hcnt Htext Hpc Hptree [Henv]").
    { iExact "Henv". }
    iIntros (CID7 Hs7 mr t' g) "Hcg Hcnt Hpc Hptree %Hnodes' Henv %Hkcs %Hbase' %Hrep' %Hpres %Hgmiss".
    assert (Hret : ret_pc (Wk !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kvmmake + 0x28)).
    { rewrite /Wk upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret) in "Hpc".
    iEval (rewrite avail_recomb) in "Henv".
    (* fold post map into kvm_m1 *)
    rewrite Hsvpn Hppn in Hrep'.
    (* callee-saved recovery *)
    assert (HcsMWk : callee_saved M Wk).
    { rewrite /Wk /U10 /U11 /U12 /U13 /U14.
      repeat (apply callee_saved_insert_r; [vm_compute; reflexivity |]). apply callee_saved_refl. }
    assert (HcsMmr : callee_saved M mr) by (apply (callee_saved_trans _ Wk _ HcsMWk Hkcs)).
    iSpecialize ("Hcont" $! CID7 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! mr t' g with "Hcg Hcnt Hpc Hptree Henv [%] [%] [%] [%] [%] [%] [%]").
    { exact HcsMmr. }
    { rewrite (callee_saved_lookup HcsMmr (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact HM9. }
    { rewrite (callee_saved_lookup HcsMmr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp. }
    { rewrite Hbase'. apply pt_empty_node_base. }
    { unfold kvm_m1. exact Hrep'. }
    { rewrite Hnodes'. unfold pt_nodes. rewrite (pt_nodes_lvl_empty 2 bppn). reflexivity. }
    { apply (Nat.le_trans _ _ _ Hgmiss). rewrite Hsvpn. exact (bound_uart bppn). }
  Qed.

  (* ================================================================= *)
  (* REGION 2 -- VIRTIO (+0x28..+0x34).  t in: kvm_m1, out: kvm_m2.     *)
  (* ================================================================= *)
  Lemma wp_kmk_region_virtio `{CID0 : CpuId}
      (γa : gname) (mm M : regfile) (bppn : mword 44)
      (t : ptree) (K : nat) (eb : bool) (p : mword 64) (nb gsprev : nat) (b : bool) (lks : gset string) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    locks_below lks "kmem" ->
    (48 <= K)%nat -> (166 < nb)%nat -> (gsprev <= 2)%nat ->
    M !!! Regidx csp_rs1 = spr ->
    M !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12)) ->
    pt_base t = bppn -> pt_rep0 t kvm_m1 ->
    sie_cap_gpr M (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.kvmmake + 0x28)) -∗
    ptree_own 2 (DfracOwn 1) t -∗
    kalloc_env γa (avail_sub (Some nb) (1 + gsprev)) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
      sie_cap_gpr mr (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.kvmmake + 0x38)) -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γa (avail_sub (Some nb) (1 + (gsprev + g))) -∗
      ⌜callee_saved M mr⌝ -∗
      ⌜mr !!! Regidx (mword_of_int 9) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))⌝ -∗
      ⌜mr !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜pt_base t' = bppn⌝ -∗ ⌜pt_rep0 t' kvm_m2⌝ -∗
      ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗ ⌜(g <= 0)%nat⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr Hbelow HK Hnb Hgs Hsp HM9 Hbase Hrep.
    pose proof (cap_bounds K HK) as (Hc4 & Hc2 & Hc14 & Hc34 & Hc44).
    iIntros "Hcg Hcnt #Htext Hpc Hptree Henv Hcont".
    iPoseProof (kmki_28 with "Htext") as "Hi28".
    iPoseProof (kmki_2a with "Htext") as "Hi2a".
    iPoseProof (kmki_2c with "Htext") as "Hi2c".
    iPoseProof (kmki_30 with "Htext") as "Hi30".
    iPoseProof (kmki_32 with "Htext") as "Hi32".
    iPoseProof (kmki_34 with "Htext") as "Hi34".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x28)) (mword_of_int 14 : mword 5) (mword_of_int 6 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))
              M (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi28").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (V14 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))]> M).
    assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x28) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x2a)) (mword_of_int 13 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              V14 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi2a").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (V13 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> V14).
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x2c)) (mword_of_int 12 : mword 5) (mword_of_int 65537 : mword 20) (luival (mword_of_int 65537 : mword 20))
              V13 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi2c").
    iIntros (CID3 Hs3) "Hcg Hpc".
    set (V12 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (mword_of_int 65537 : mword 20))]> V13).
    assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x2c) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x30)) (mword_of_int 11 : mword 5) (mword_of_int 12 : mword 5)
              V12 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi30").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (V11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (V12 !!! Regidx (mword_of_int 12 : mword 5)))]> V12).
    assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x32)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              V11 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi32").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (V10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (V11 !!! Regidx (mword_of_int 9 : mword 5)))]> V11).
    assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x34)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp34) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x34)) (mword_of_int 1 : mword 5) (mword_of_int 2097060 : mword 21)
              V10 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi34").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (Wk := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x34) : mword 64) 4)]> V10).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.kvmmake + 0x34) : mword 64) (sign_extend' 64 (mword_of_int 2097060 : mword 21)) = mword_of_int KernelSyms.kvmmap) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt) in "Hpc".
    assert (HWka1 : Wk !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int 0x10001000).
    { rewrite /Wk /V10. repeat (rewrite upd_ne; [| reg_neq]). rewrite /V11 upd_eq. rewrite add_vec_zero_l.
      rewrite /V12 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka2 : Wk !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 0x10001000).
    { rewrite /Wk /V10 /V11. repeat (rewrite upd_ne; [| reg_neq]). rewrite /V12 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka3 : Wk !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int (Z.of_nat 1 * 4096)).
    { rewrite /Wk /V10 /V11 /V12. repeat (rewrite upd_ne; [| reg_neq]). rewrite /V13 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka4 : Wk !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 6).
    { rewrite /Wk /V10 /V11 /V12 /V13. repeat (rewrite upd_ne; [| reg_neq]). rewrite /V14 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka0 : Wk !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { rewrite /Wk. rewrite upd_ne; [| reg_neq]. rewrite /V10 upd_eq. rewrite add_vec_zero_l.
      rewrite /V11 /V12 /V13 /V14. repeat (rewrite upd_ne; [| reg_neq]). exact HM9. }
    assert (Hppn : (autocast (T := mword) (subrange_vec_dec (Wk !!! Regidx (mword_of_int 12 : mword 5)) 55 12) : mword 44) = virtio_ppn) by (rewrite HWka2; apply bv_eq; vm_compute; reflexivity).
    assert (Hsvpn : svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5)) = virtio_vpn) by (rewrite HWka1; apply bv_eq; vm_compute; reflexivity).
    assert (Havin : avail_sub (Some nb) (1 + gsprev) = Some (nb - (1 + gsprev))%nat) by (rewrite avail_sub_Some; reflexivity).
    iEval (rewrite Havin) in "Henv".
    assert (Hbud : (pt_missing t (svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5))) 1 < nb - (1 + gsprev))%nat).
    { rewrite Hsvpn. apply (budget_arm _ 0 gsprev 2 nb (bound_virtio t Hrep) Hgs ltac:(nat_le) Hnb). }
    iDestruct (cpu_own_transport CID0 CID6 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (wp_kvmmap γa Wk t kvm_m1 1 6 0%nat (K - 4)%nat eb p (Some (nb - (1 + gsprev))%nat) b lks
              ltac:(vm_compute; reflexivity) Hc34 ltac:(rewrite HWka0 Hbase; reflexivity)
              ltac:(rewrite HWka1; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HWka2; apply bv_eq; vm_compute; reflexivity)
              HWka3 ltac:(nat_le) HWka4 kmk_perm_ok6
              ltac:(rewrite HWka1; rewrite uint_unsigned; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
              ltac:(rewrite HWka2; rewrite uint_unsigned; apply (proj1 (Z.ltb_lt _ _)); vm_compute; reflexivity)
              Hrep
              ltac:(intros i Hi; rewrite Hsvpn; rewrite (lt1 i Hi);
                    assert (Hv0 : vpn_at virtio_vpn 0 = virtio_vpn) by (apply bv_eq; apply vpn_at_0_bv);
                    rewrite Hv0; exact kvm_m1_none_virtio)
              ltac:(eexists; split; [reflexivity | exact Hbud])
              Hbelow
              with "Hcg Hcnt Htext Hpc Hptree [Henv]").
    { iExact "Henv". }
    iIntros (CID7 Hs7 mr t' g) "Hcg Hcnt Hpc Hptree %Hnodes' Henv %Hkcs %Hbase' %Hrep' %Hpres %Hgmiss".
    assert (Hret : ret_pc (Wk !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kvmmake + 0x38)).
    { rewrite /Wk upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret) in "Hpc".
    iEval (rewrite avail_recomb) in "Henv".
    rewrite Hsvpn Hppn in Hrep'.
    assert (HcsMWk : callee_saved M Wk).
    { rewrite /Wk /V10 /V11 /V12 /V13 /V14.
      repeat (apply callee_saved_insert_r; [vm_compute; reflexivity |]). apply callee_saved_refl. }
    assert (HcsMmr : callee_saved M mr) by (apply (callee_saved_trans _ Wk _ HcsMWk Hkcs)).
    iSpecialize ("Hcont" $! CID7 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! mr t' g with "Hcg Hcnt Hpc Hptree Henv [%] [%] [%] [%] [%] [%] [%]").
    { exact HcsMmr. }
    { rewrite (callee_saved_lookup HcsMmr (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact HM9. }
    { rewrite (callee_saved_lookup HcsMmr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp. }
    { rewrite Hbase'. exact Hbase. }
    { unfold kvm_m2. exact Hrep'. }
    { rewrite Hnodes'. reflexivity. }
    { apply (Nat.le_trans _ _ _ Hgmiss). rewrite Hsvpn. exact (bound_virtio t Hrep). }
  Qed.

  (* ================================================================= *)
  (* REGION 3 -- PLIC (+0x38..+0x46).  t in: kvm_m2, out: kvm_m3.       *)
  (* ================================================================= *)
  Lemma wp_kmk_region_plic `{CID0 : CpuId}
      (γa : gname) (mm M : regfile) (bppn : mword 44)
      (t : ptree) (K : nat) (eb : bool) (p : mword 64) (nb gsprev : nat) (b : bool) (lks : gset string) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    locks_below lks "kmem" ->
    (48 <= K)%nat -> (166 < nb)%nat -> (gsprev <= 2)%nat ->
    M !!! Regidx csp_rs1 = spr ->
    M !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12)) ->
    pt_base t = bppn -> pt_rep0 t kvm_m2 ->
    sie_cap_gpr M (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.kvmmake + 0x38)) -∗
    ptree_own 2 (DfracOwn 1) t -∗
    kalloc_env γa (avail_sub (Some nb) (1 + gsprev)) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
      sie_cap_gpr mr (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.kvmmake + 0x4a)) -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γa (avail_sub (Some nb) (1 + (gsprev + g))) -∗
      ⌜callee_saved M mr⌝ -∗
      ⌜mr !!! Regidx (mword_of_int 9) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))⌝ -∗
      ⌜mr !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜pt_base t' = bppn⌝ -∗ ⌜pt_rep0 t' kvm_m3⌝ -∗
      ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗ ⌜(g <= 32)%nat⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr Hbelow HK Hnb Hgs Hsp HM9 Hbase Hrep.
    pose proof (cap_bounds K HK) as (Hc4 & Hc2 & Hc14 & Hc34 & Hc44).
    iIntros "Hcg Hcnt #Htext Hpc Hptree Henv Hcont".
    iPoseProof (kmki_38 with "Htext") as "Hi38".
    iPoseProof (kmki_3a with "Htext") as "Hi3a".
    iPoseProof (kmki_3e with "Htext") as "Hi3e".
    iPoseProof (kmki_42 with "Htext") as "Hi42".
    iPoseProof (kmki_44 with "Htext") as "Hi44".
    iPoseProof (kmki_46 with "Htext") as "Hi46".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x38)) (mword_of_int 14 : mword 5) (mword_of_int 6 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))
              M (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi38").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (P14 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))]> M).
    assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x3a)) (mword_of_int 13 : mword 5) (mword_of_int 16384 : mword 20) (luival (mword_of_int 16384 : mword 20))
              P14 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi3a").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (P13 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (luival (mword_of_int 16384 : mword 20))]> P14).
    assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3e) in "Hpc".
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x3e)) (mword_of_int 12 : mword 5) (mword_of_int 49152 : mword 20) (luival (mword_of_int 49152 : mword 20))
              P13 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi3e").
    iIntros (CID3 Hs3) "Hcg Hpc".
    set (P12 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (mword_of_int 49152 : mword 20))]> P13).
    assert (Hp42 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x3e) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp42) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x42)) (mword_of_int 11 : mword 5) (mword_of_int 12 : mword 5)
              P12 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi42").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (P12 !!! Regidx (mword_of_int 12 : mword 5)))]> P12).
    assert (Hp44 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x42) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x44)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp44) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x44)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              P11 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi44").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (P10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (P11 !!! Regidx (mword_of_int 9 : mword 5)))]> P11).
    assert (Hp46 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x44) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp46) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x46)) (mword_of_int 1 : mword 5) (mword_of_int 2097042 : mword 21)
              P10 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi46").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (Wk := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x46) : mword 64) 4)]> P10).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.kvmmake + 0x46) : mword 64) (sign_extend' 64 (mword_of_int 2097042 : mword 21)) = mword_of_int KernelSyms.kvmmap) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt) in "Hpc".
    assert (HWka1 : Wk !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int 0x0C000000).
    { rewrite /Wk /P10. repeat (rewrite upd_ne; [| reg_neq]). rewrite /P11 upd_eq. rewrite add_vec_zero_l.
      rewrite /P12 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka2 : Wk !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 0x0C000000).
    { rewrite /Wk /P10 /P11. repeat (rewrite upd_ne; [| reg_neq]). rewrite /P12 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka3 : Wk !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int (Z.of_nat plic_npages * 4096)).
    { rewrite /Wk /P10 /P11 /P12. repeat (rewrite upd_ne; [| reg_neq]). rewrite /P13 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka4 : Wk !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 6).
    { rewrite /Wk /P10 /P11 /P12 /P13. repeat (rewrite upd_ne; [| reg_neq]). rewrite /P14 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka0 : Wk !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { rewrite /Wk. rewrite upd_ne; [| reg_neq]. rewrite /P10 upd_eq. rewrite add_vec_zero_l.
      rewrite /P11 /P12 /P13 /P14. repeat (rewrite upd_ne; [| reg_neq]). exact HM9. }
    assert (Hppn : (autocast (T := mword) (subrange_vec_dec (Wk !!! Regidx (mword_of_int 12 : mword 5)) 55 12) : mword 44) = plic_ppn) by (rewrite HWka2; apply bv_eq; vm_compute; reflexivity).
    assert (Hsvpn : svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5)) = plic_vpn) by (rewrite HWka1; apply bv_eq; vm_compute; reflexivity).
    assert (Havin : avail_sub (Some nb) (1 + gsprev) = Some (nb - (1 + gsprev))%nat) by (rewrite avail_sub_Some; reflexivity).
    iEval (rewrite Havin) in "Henv".
    assert (Hbud : (pt_missing t (svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5))) plic_npages < nb - (1 + gsprev))%nat).
    { rewrite Hsvpn. apply (budget_arm _ 32 gsprev 2 nb (bound_plic t Hrep) Hgs ltac:(nat_le) Hnb). }
    iDestruct (cpu_own_transport CID0 CID6 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (wp_kvmmap γa Wk t kvm_m2 plic_npages 6 0%nat (K - 4)%nat eb p (Some (nb - (1 + gsprev))%nat) b lks
              ltac:(vm_compute; reflexivity) Hc34 ltac:(rewrite HWka0 Hbase; reflexivity)
              ltac:(rewrite HWka1; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HWka2; apply bv_eq; vm_compute; reflexivity)
              HWka3 ltac:(nat_le) HWka4 kmk_perm_ok6
              ltac:(rewrite HWka1; rewrite uint_unsigned; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
              ltac:(rewrite HWka2; rewrite uint_unsigned; apply (proj1 (Z.ltb_lt _ _)); vm_compute; reflexivity)
              Hrep
              ltac:(intros i Hi; rewrite Hsvpn; apply kvm_m2_none_plic;
                    rewrite (vpn_at_unsigned plic_vpn i ltac:(rewrite plic_vpn_uns; exact (proj1 (plic_bounds i Hi))));
                    rewrite plic_vpn_uns; exact (proj2 (plic_bounds i Hi)))
              ltac:(eexists; split; [reflexivity | exact Hbud])
              Hbelow
              with "Hcg Hcnt Htext Hpc Hptree [Henv]").
    { iExact "Henv". }
    iIntros (CID7 Hs7 mr t' g) "Hcg Hcnt Hpc Hptree %Hnodes' Henv %Hkcs %Hbase' %Hrep' %Hpres %Hgmiss".
    assert (Hret : ret_pc (Wk !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kvmmake + 0x4a)).
    { rewrite /Wk upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret) in "Hpc".
    iEval (rewrite avail_recomb) in "Henv".
    rewrite Hsvpn Hppn in Hrep'.
    assert (HcsMWk : callee_saved M Wk).
    { rewrite /Wk /P10 /P11 /P12 /P13 /P14.
      repeat (apply callee_saved_insert_r; [vm_compute; reflexivity |]). apply callee_saved_refl. }
    assert (HcsMmr : callee_saved M mr) by (apply (callee_saved_trans _ Wk _ HcsMWk Hkcs)).
    iSpecialize ("Hcont" $! CID7 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! mr t' g with "Hcg Hcnt Hpc Hptree Henv [%] [%] [%] [%] [%] [%] [%]").
    { exact HcsMmr. }
    { rewrite (callee_saved_lookup HcsMmr (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact HM9. }
    { rewrite (callee_saved_lookup HcsMmr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp. }
    { rewrite Hbase'. exact Hbase. }
    { unfold kvm_m3. exact Hrep'. }
    { rewrite Hnodes'. reflexivity. }
    { apply (Nat.le_trans _ _ _ Hgmiss). rewrite Hsvpn. exact (bound_plic t Hrep). }
  Qed.

  (* ================================================================= *)
  (* REGION 4 -- text (+0x4a..+0x5c).  t in: kvm_m3, out: kvm_m4.       *)
  (* ================================================================= *)
  Lemma wp_kmk_region_text `{CID0 : CpuId}
      (γa : gname) (mm M : regfile) (bppn : mword 44)
      (t : ptree) (K : nat) (eb : bool) (p : mword 64) (nb gsprev : nat) (b : bool) (lks : gset string) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    locks_below lks "kmem" ->
    (48 <= K)%nat -> (166 < nb)%nat -> (gsprev <= 34)%nat ->
    M !!! Regidx csp_rs1 = spr ->
    M !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12)) ->
    pt_base t = bppn -> pt_rep0 t kvm_m3 ->
    sie_cap_gpr M (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.kvmmake + 0x4a)) -∗
    ptree_own 2 (DfracOwn 1) t -∗
    kalloc_env γa (avail_sub (Some nb) (1 + gsprev)) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
      sie_cap_gpr mr (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.kvmmake + 0x60)) -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γa (avail_sub (Some nb) (1 + (gsprev + g))) -∗
      ⌜callee_saved M mr⌝ -∗
      ⌜mr !!! Regidx (mword_of_int 9) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))⌝ -∗
      ⌜mr !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜pt_base t' = bppn⌝ -∗ ⌜pt_rep0 t' kvm_m4⌝ -∗
      ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗ ⌜(g <= 2)%nat⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr Hbelow HK Hnb Hgs Hsp HM9 Hbase Hrep.
    pose proof (cap_bounds K HK) as (Hc4 & Hc2 & Hc14 & Hc34 & Hc44).
    iIntros "Hcg Hcnt #Htext Hpc Hptree Henv Hcont".
    iPoseProof (kmki_4a with "Htext") as "Hi4a".
    iPoseProof (kmki_4c with "Htext") as "Hi4c".
    iPoseProof (kmki_50 with "Htext") as "Hi50".
    iPoseProof (kmki_54 with "Htext") as "Hi54".
    iPoseProof (kmki_56 with "Htext") as "Hi56".
    iPoseProof (kmki_58 with "Htext") as "Hi58".
    iPoseProof (kmki_5a with "Htext") as "Hi5a".
    iPoseProof (kmki_5c with "Htext") as "Hi5c".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x4a)) (mword_of_int 14 : mword 5) (mword_of_int 10 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 10 : mword 6))))
              M (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi4a").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (T14 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 10 : mword 6))))]> M).
    assert (Hp4c : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x4a) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4c) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x4c)) (mword_of_int 13 : mword 5) (mword_of_int 524294 : mword 20)
              T14 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi4c").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (T13a := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kvmmake + 0x4c)) (auipc_off (mword_of_int 524294 : mword 20)))]> T14).
    assert (Hp50 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x4c) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp50) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x50)) (mword_of_int 13 : mword 5) (mword_of_int 13 : mword 5) (mword_of_int 3826 : mword 12)
              T13a (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi50").
    iIntros (CID3 Hs3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T13 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec (T13a !!! Regidx (mword_of_int 13 : mword 5)) (sign_extend' 64 (mword_of_int 3826 : mword 12)))]> T13a).
    assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x50) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x54)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp54) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x54)) (mword_of_int 12 : mword 5) (mword_of_int 1 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))
              T13 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi54").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (T12a := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> T13).
    assert (Hp56 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp56) in "Hpc".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x56)) (Regidx (mword_of_int 12 : mword 5)) (mword_of_int 12 : mword 5) (mword_of_int 31 : mword 6)
              T12a (K - 4)%nat b eq_refl ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi56").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T12 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (shift_bits_left (T12a !!! Regidx (mword_of_int 12 : mword 5)) (subrange_vec_dec (mword_of_int 31 : mword 6) (Z.sub log2_xlen 1) 0))]> T12a).
    assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x56) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp58) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x58)) (mword_of_int 11 : mword 5) (mword_of_int 12 : mword 5)
              T12 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi58").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (T12 !!! Regidx (mword_of_int 12 : mword 5)))]> T12).
    assert (Hp5a : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x58) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5a) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x5a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              T11 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi5a").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (T11 !!! Regidx (mword_of_int 9 : mword 5)))]> T11).
    assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5c) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x5c)) (mword_of_int 1 : mword 5) (mword_of_int 2097020 : mword 21)
              T10 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi5c").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (Wk := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x5c) : mword 64) 4)]> T10).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.kvmmake + 0x5c) : mword 64) (sign_extend' 64 (mword_of_int 2097020 : mword 21)) = mword_of_int KernelSyms.kvmmap) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt) in "Hpc".
    assert (HWka1 : Wk !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int 0x80000000).
    { rewrite /Wk /T10. repeat (rewrite upd_ne; [| reg_neq]). rewrite /T11 upd_eq. rewrite add_vec_zero_l.
      rewrite /T12 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka2 : Wk !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 0x80000000).
    { rewrite /Wk /T10 /T11. repeat (rewrite upd_ne; [| reg_neq]). rewrite /T12 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka3 : Wk !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int (Z.of_nat text_npages * 4096)).
    { rewrite /Wk /T10 /T11 /T12. repeat (rewrite upd_ne; [| reg_neq]). rewrite /T13 upd_eq. rewrite /T13a upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka4 : Wk !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 10).
    { rewrite /Wk /T10 /T11 /T12 /T13 /T13a. repeat (rewrite upd_ne; [| reg_neq]). rewrite /T14 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka0 : Wk !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { rewrite /Wk. rewrite upd_ne; [| reg_neq]. rewrite /T10 upd_eq. rewrite add_vec_zero_l.
      rewrite /T11 /T12 /T13 /T13a /T14. repeat (rewrite upd_ne; [| reg_neq]). exact HM9. }
    assert (Hppn : (autocast (T := mword) (subrange_vec_dec (Wk !!! Regidx (mword_of_int 12 : mword 5)) 55 12) : mword 44) = text_ppn0) by (rewrite HWka2; apply bv_eq; vm_compute; reflexivity).
    assert (Hsvpn : svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5)) = text_vpn0) by (rewrite HWka1; apply bv_eq; vm_compute; reflexivity).
    assert (Havin : avail_sub (Some nb) (1 + gsprev) = Some (nb - (1 + gsprev))%nat) by (rewrite avail_sub_Some; reflexivity).
    iEval (rewrite Havin) in "Henv".
    assert (Hbud : (pt_missing t (svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5))) text_npages < nb - (1 + gsprev))%nat).
    { rewrite Hsvpn. apply (budget_arm _ 2 gsprev 34 nb (bound_text t) Hgs ltac:(nat_le) Hnb). }
    iDestruct (cpu_own_transport CID0 CID8 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (wp_kvmmap γa Wk t kvm_m3 text_npages 10 0%nat (K - 4)%nat eb p (Some (nb - (1 + gsprev))%nat) b lks
              ltac:(vm_compute; reflexivity) Hc34 ltac:(rewrite HWka0 Hbase; reflexivity)
              ltac:(rewrite HWka1; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HWka2; apply bv_eq; vm_compute; reflexivity)
              HWka3 ltac:(nat_le) HWka4 kmk_perm_ok10
              ltac:(rewrite HWka1; rewrite uint_unsigned; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
              ltac:(rewrite HWka2; rewrite uint_unsigned; apply (proj1 (Z.ltb_lt _ _)); vm_compute; reflexivity)
              Hrep
              ltac:(intros i Hi; rewrite Hsvpn; apply kvm_m3_none_text;
                    rewrite (vpn_at_unsigned text_vpn0 i ltac:(rewrite text_vpn_uns; exact (proj1 (text_bounds i Hi))));
                    rewrite text_vpn_uns; exact (proj2 (text_bounds i Hi)))
              ltac:(eexists; split; [reflexivity | exact Hbud])
              Hbelow
              with "Hcg Hcnt Htext Hpc Hptree [Henv]").
    { iExact "Henv". }
    iIntros (CID9 Hs9 mr t' g) "Hcg Hcnt Hpc Hptree %Hnodes' Henv %Hkcs %Hbase' %Hrep' %Hpres %Hgmiss".
    assert (Hret : ret_pc (Wk !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kvmmake + 0x60)).
    { rewrite /Wk upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret) in "Hpc".
    iEval (rewrite avail_recomb) in "Henv".
    rewrite Hsvpn Hppn in Hrep'.
    assert (HcsMWk : callee_saved M Wk).
    { rewrite /Wk /T10 /T11 /T12 /T13 /T13a /T14.
      repeat (apply callee_saved_insert_r; [vm_compute; reflexivity |]). apply callee_saved_refl. }
    assert (HcsMmr : callee_saved M mr) by (apply (callee_saved_trans _ Wk _ HcsMWk Hkcs)).
    iSpecialize ("Hcont" $! CID9 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! mr t' g with "Hcg Hcnt Hpc Hptree Henv [%] [%] [%] [%] [%] [%] [%]").
    { exact HcsMmr. }
    { rewrite (callee_saved_lookup HcsMmr (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact HM9. }
    { rewrite (callee_saved_lookup HcsMmr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp. }
    { rewrite Hbase'. exact Hbase. }
    { unfold kvm_m4. exact Hrep'. }
    { rewrite Hnodes'. reflexivity. }
    { apply (Nat.le_trans _ _ _ Hgmiss). rewrite Hsvpn. exact (bound_text t). }
  Qed.

  (* ================================================================= *)
  (* REGION 5 -- data (+0x60..+0x7e).  t in: kvm_m4, out: kvm_m5.       *)
  (* ================================================================= *)
  Lemma wp_kmk_region_data `{CID0 : CpuId}
      (γa : gname) (mm M : regfile) (bppn : mword 44)
      (t : ptree) (K : nat) (eb : bool) (p : mword 64) (nb gsprev : nat) (b : bool) (lks : gset string) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    locks_below lks "kmem" ->
    (48 <= K)%nat -> (166 < nb)%nat -> (gsprev <= 36)%nat ->
    M !!! Regidx csp_rs1 = spr ->
    M !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12)) ->
    pt_base t = bppn -> pt_rep0 t kvm_m4 ->
    sie_cap_gpr M (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.kvmmake + 0x60)) -∗
    ptree_own 2 (DfracOwn 1) t -∗
    kalloc_env γa (avail_sub (Some nb) (1 + gsprev)) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
      sie_cap_gpr mr (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.kvmmake + 0x82)) -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γa (avail_sub (Some nb) (1 + (gsprev + g))) -∗
      ⌜callee_saved M mr⌝ -∗
      ⌜mr !!! Regidx (mword_of_int 9) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))⌝ -∗
      ⌜mr !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜pt_base t' = bppn⌝ -∗ ⌜pt_rep0 t' kvm_m5⌝ -∗
      ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗ ⌜(g <= 63)%nat⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr Hbelow HK Hnb Hgs Hsp HM9 Hbase Hrep.
    pose proof (cap_bounds K HK) as (Hc4 & Hc2 & Hc14 & Hc34 & Hc44).
    iIntros "Hcg Hcnt #Htext Hpc Hptree Henv Hcont".
    iPoseProof (kmki_60 with "Htext") as "Hi60".
    iPoseProof (kmki_62 with "Htext") as "Hi62".
    iPoseProof (kmki_66 with "Htext") as "Hi66".
    iPoseProof (kmki_6a with "Htext") as "Hi6a".
    iPoseProof (kmki_6c with "Htext") as "Hi6c".
    iPoseProof (kmki_6e with "Htext") as "Hi6e".
    iPoseProof (kmki_72 with "Htext") as "Hi72".
    iPoseProof (kmki_76 with "Htext") as "Hi76".
    iPoseProof (kmki_7a with "Htext") as "Hi7a".
    iPoseProof (kmki_7c with "Htext") as "Hi7c".
    iPoseProof (kmki_7e with "Htext") as "Hi7e".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x60)) (mword_of_int 14 : mword 5) (mword_of_int 6 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))
              M (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi60").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (D14 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 6 : mword 6))))]> M).
    assert (Hp62 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x60) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp62) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x62)) (mword_of_int 13 : mword 5) (mword_of_int 6 : mword 20)
              D14 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi62").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (D13a := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kvmmake + 0x62)) (auipc_off (mword_of_int 6 : mword 20)))]> D14).
    assert (Hp66 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x62) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x66)) (mword_of_int 13 : mword 5) (mword_of_int 13 : mword 5) (mword_of_int 3804 : mword 12)
              D13a (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi66").
    iIntros (CID3 Hs3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D13b := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (add_vec (D13a !!! Regidx (mword_of_int 13 : mword 5)) (sign_extend' 64 (mword_of_int 3804 : mword 12)))]> D13a).
    assert (Hp6a : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x66) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6a) in "Hpc".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x6a)) (mword_of_int 15 : mword 5) (mword_of_int 17 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 17 : mword 6))))
              D13b (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi6a").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (D15a := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 17 : mword 6))))]> D13b).
    assert (Hp6c : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x6a) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6c) in "Hpc".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x6c)) (Regidx (mword_of_int 15 : mword 5)) (mword_of_int 15 : mword 5) (mword_of_int 27 : mword 6)
              D15a (K - 4)%nat b eq_refl ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi6c").
    iIntros (CID5 Hs5) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D15 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (shift_bits_left (D15a !!! Regidx (mword_of_int 15 : mword 5)) (subrange_vec_dec (mword_of_int 27 : mword 6) (Z.sub log2_xlen 1) 0))]> D15a).
    assert (Hp6e : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6e) in "Hpc".
    iApply (wp_sub_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x6e)) (mword_of_int 13 : mword 5) (mword_of_int 15 : mword 5) (mword_of_int 13 : mword 5) (mword_of_int (Z.of_nat data_npages * 4096))
              D15 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rgne;
                    assert (Hr15 : D15 !!! Regidx (mword_of_int 15 : mword 5) = mword_of_int 0x88000000) by (rewrite /D15 upd_eq; rewrite /D15a upd_eq; apply bv_eq; vm_compute; reflexivity);
                    assert (Hr13 : D15 !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int 0x80007000) by (rewrite /D15 /D15a; repeat (rewrite upd_ne; [| reg_neq]); rewrite /D13b upd_eq; rewrite /D13a upd_eq; apply bv_eq; vm_compute; reflexivity);
                    rewrite Hr15 Hr13; apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi6e").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (D13 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (mword_of_int (Z.of_nat data_npages * 4096))]> D15).
    assert (Hp72 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x6e) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp72) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x72)) (mword_of_int 12 : mword 5) (mword_of_int 6 : mword 20)
              D13 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi72").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (D12a := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kvmmake + 0x72)) (auipc_off (mword_of_int 6 : mword 20)))]> D13).
    assert (Hp76 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x72) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp76) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x76)) (mword_of_int 12 : mword 5) (mword_of_int 12 : mword 5) (mword_of_int 3788 : mword 12)
              D12a (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi76").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D12 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (add_vec (D12a !!! Regidx (mword_of_int 12 : mword 5)) (sign_extend' 64 (mword_of_int 3788 : mword 12)))]> D12a).
    assert (Hp7a : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x76) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7a) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x7a)) (mword_of_int 11 : mword 5) (mword_of_int 12 : mword 5)
              D12 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi7a").
    iIntros (CID9 Hs9) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (D12 !!! Regidx (mword_of_int 12 : mword 5)))]> D12).
    assert (Hp7c : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x7a) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7c) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x7c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              D11 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi7c").
    iIntros (CID10 Hs10) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (D10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (D11 !!! Regidx (mword_of_int 9 : mword 5)))]> D11).
    assert (Hp7e : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x7c) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp7e) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x7e)) (mword_of_int 1 : mword 5) (mword_of_int 2096986 : mword 21)
              D10 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi7e").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (Wk := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x7e) : mword 64) 4)]> D10).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.kvmmake + 0x7e) : mword 64) (sign_extend' 64 (mword_of_int 2096986 : mword 21)) = mword_of_int KernelSyms.kvmmap) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt) in "Hpc".
    assert (HWka1 : Wk !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int 0x80007000).
    { rewrite /Wk /D10. repeat (rewrite upd_ne; [| reg_neq]). rewrite /D11 upd_eq. rewrite add_vec_zero_l.
      rewrite /D12 upd_eq. rewrite /D12a upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka2 : Wk !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 0x80007000).
    { rewrite /Wk /D10 /D11. repeat (rewrite upd_ne; [| reg_neq]). rewrite /D12 upd_eq. rewrite /D12a upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka3 : Wk !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int (Z.of_nat data_npages * 4096)).
    { rewrite /Wk /D10 /D11 /D12 /D12a. repeat (rewrite upd_ne; [| reg_neq]). rewrite /D13 upd_eq. reflexivity. }
    assert (HWka4 : Wk !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 6).
    { rewrite /Wk /D10 /D11 /D12 /D12a /D13 /D15 /D15a. repeat (rewrite upd_ne; [| reg_neq]). rewrite /D13b /D13a. repeat (rewrite upd_ne; [| reg_neq]). rewrite /D14 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka0 : Wk !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { peel_reg_step. rewrite add_vec_zero_l. peel_reg_step. exact HM9. }
    assert (Hppn : (autocast (T := mword) (subrange_vec_dec (Wk !!! Regidx (mword_of_int 12 : mword 5)) 55 12) : mword 44) = data_ppn0) by (rewrite HWka2; apply bv_eq; vm_compute; reflexivity).
    assert (Hsvpn : svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5)) = data_vpn0) by (rewrite HWka1; apply bv_eq; vm_compute; reflexivity).
    assert (Havin : avail_sub (Some nb) (1 + gsprev) = Some (nb - (1 + gsprev))%nat) by (rewrite avail_sub_Some; reflexivity).
    iEval (rewrite Havin) in "Henv".
    assert (Hbud : (pt_missing t (svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5))) data_npages < nb - (1 + gsprev))%nat).
    { rewrite Hsvpn. apply (budget_arm _ 63 gsprev 36 nb (bound_data t Hrep) Hgs ltac:(nat_le) Hnb). }
    iDestruct (cpu_own_transport CID0 CID11 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (wp_kvmmap γa Wk t kvm_m4 data_npages 6 0%nat (K - 4)%nat eb p (Some (nb - (1 + gsprev))%nat) b lks
              ltac:(vm_compute; reflexivity) Hc34 ltac:(rewrite HWka0 Hbase; reflexivity)
              ltac:(rewrite HWka1; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HWka2; apply bv_eq; vm_compute; reflexivity)
              HWka3 ltac:(nat_le) HWka4 kmk_perm_ok6
              ltac:(rewrite HWka1; rewrite uint_unsigned; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
              ltac:(rewrite HWka2; rewrite uint_unsigned; apply (proj1 (Z.ltb_lt _ _)); vm_compute; reflexivity)
              Hrep
              ltac:(intros i Hi; rewrite Hsvpn; apply kvm_m4_none_data;
                    rewrite (vpn_at_unsigned data_vpn0 i ltac:(rewrite data_vpn_uns; exact (proj1 (data_bounds i Hi))));
                    rewrite data_vpn_uns; exact (proj2 (data_bounds i Hi)))
              ltac:(eexists; split; [reflexivity | exact Hbud])
              Hbelow
              with "Hcg Hcnt Htext Hpc Hptree [Henv]").
    { iExact "Henv". }
    iIntros (CID12 Hs12 mr t' g) "Hcg Hcnt Hpc Hptree %Hnodes' Henv %Hkcs %Hbase' %Hrep' %Hpres %Hgmiss".
    assert (Hret : ret_pc (Wk !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kvmmake + 0x82)).
    { rewrite /Wk upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret) in "Hpc".
    iEval (rewrite avail_recomb) in "Henv".
    rewrite Hsvpn Hppn in Hrep'.
    assert (HcsMWk : callee_saved M Wk).
    { rewrite /Wk /D10 /D11 /D12 /D12a /D13 /D15 /D15a /D13b /D13a /D14.
      repeat (apply callee_saved_insert_r; [vm_compute; reflexivity |]). apply callee_saved_refl. }
    assert (HcsMmr : callee_saved M mr) by (apply (callee_saved_trans _ Wk _ HcsMWk Hkcs)).
    iSpecialize ("Hcont" $! CID12 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! mr t' g with "Hcg Hcnt Hpc Hptree Henv [%] [%] [%] [%] [%] [%] [%]").
    { exact HcsMmr. }
    { rewrite (callee_saved_lookup HcsMmr (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact HM9. }
    { rewrite (callee_saved_lookup HcsMmr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp. }
    { rewrite Hbase'. exact Hbase. }
    { unfold kvm_m5. exact Hrep'. }
    { rewrite Hnodes'. reflexivity. }
    { apply (Nat.le_trans _ _ _ Hgmiss). rewrite Hsvpn. exact (bound_data t Hrep). }
  Qed.

  (* ================================================================= *)
  (* REGION 6 -- trampoline (+0x82..+0x98).  t in: kvm_m5, out: kvm_map.*)
  (* ================================================================= *)
  Lemma wp_kmk_region_tramp `{CID0 : CpuId}
      (γa : gname) (mm M : regfile) (bppn : mword 44)
      (t : ptree) (K : nat) (eb : bool) (p : mword 64) (nb gsprev : nat) (b : bool) (lks : gset string) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    locks_below lks "kmem" ->
    (48 <= K)%nat -> (166 < nb)%nat -> (gsprev <= 99)%nat ->
    M !!! Regidx csp_rs1 = spr ->
    M !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12)) ->
    pt_base t = bppn -> pt_rep0 t kvm_m5 ->
    sie_cap_gpr M (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗ kernel_text -∗
    pc_is (mword_of_int (KernelSyms.kvmmake + 0x82)) -∗
    ptree_own 2 (DfracOwn 1) t -∗
    kalloc_env γa (avail_sub (Some nb) (1 + gsprev)) -∗
    wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
      sie_cap_gpr mr (K - 4)%nat b p -∗ cpu_own 0%nat eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.kvmmake + 0x9c)) -∗
      ptree_own 2 (DfracOwn 1) t' -∗
      kalloc_env γa (avail_sub (Some nb) (1 + (gsprev + g))) -∗
      ⌜callee_saved M mr⌝ -∗
      ⌜mr !!! Regidx (mword_of_int 9) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))⌝ -∗
      ⌜mr !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜pt_base t' = bppn⌝ -∗ ⌜pt_rep0 t' kvm_map⌝ -∗
      ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗ ⌜(g <= 2)%nat⌝ -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 spr Hbelow HK Hnb Hgs Hsp HM9 Hbase Hrep.
    pose proof (cap_bounds K HK) as (Hc4 & Hc2 & Hc14 & Hc34 & Hc44).
    iIntros "Hcg Hcnt #Htext Hpc Hptree Henv Hcont".
    iPoseProof (kmki_82 with "Htext") as "Hi82".
    iPoseProof (kmki_84 with "Htext") as "Hi84".
    iPoseProof (kmki_86 with "Htext") as "Hi86".
    iPoseProof (kmki_8a with "Htext") as "Hi8a".
    iPoseProof (kmki_8e with "Htext") as "Hi8e".
    iPoseProof (kmki_92 with "Htext") as "Hi92".
    iPoseProof (kmki_94 with "Htext") as "Hi94".
    iPoseProof (kmki_96 with "Htext") as "Hi96".
    iPoseProof (kmki_98 with "Htext") as "Hi98".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x82)) (mword_of_int 14 : mword 5) (mword_of_int 10 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 10 : mword 6))))
              M (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi82").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (R14 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 10 : mword 6))))]> M).
    assert (Hp84 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x82) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp84) in "Hpc".
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x84)) (mword_of_int 13 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              R14 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi84").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (R13 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> R14).
    assert (Hp86 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x84) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp86) in "Hpc".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x86)) (mword_of_int 12 : mword 5) (mword_of_int 5 : mword 20)
              R13 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi86").
    iIntros (CID3 Hs3) "Hcg Hpc".
    set (R12a := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (add_vec (mword_of_int (KernelSyms.kvmmake + 0x86)) (auipc_off (mword_of_int 5 : mword 20)))]> R13).
    assert (Hp8a : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x86) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8a) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x8a)) (mword_of_int 12 : mword 5) (mword_of_int 12 : mword 5) (mword_of_int 3768 : mword 12)
              R12a (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi8a").
    iIntros (CID4 Hs4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R12 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (add_vec (R12a !!! Regidx (mword_of_int 12 : mword 5)) (sign_extend' 64 (mword_of_int 3768 : mword 12)))]> R12a).
    assert (Hp8e : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x8a) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x8e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp8e) in "Hpc".
    iApply (wp_lui_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x8e)) (mword_of_int 11 : mword 5) (mword_of_int 16384 : mword 20) (luival (mword_of_int 16384 : mword 20))
              R12 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(reflexivity) with "Hcg Hpc Hi8e").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (R11a := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (luival (mword_of_int 16384 : mword 20))]> R12).
    assert (Hp92 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x8e) : mword 64) 4 = mword_of_int (KernelSyms.kvmmake + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp92) in "Hpc".
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x92)) (mword_of_int 11 : mword 5) (mword_of_int 63 : mword 6)
              R11a (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi92").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R11b := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec (R11a !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> R11a).
    assert (Hp94 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x92) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp94) in "Hpc".
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x94)) (Regidx (mword_of_int 11 : mword 5)) (mword_of_int 11 : mword 5) (mword_of_int 12 : mword 6)
              R11b (K - 4)%nat b eq_refl ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi94").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R11 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (shift_bits_left (R11b !!! Regidx (mword_of_int 11 : mword 5)) (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> R11b).
    assert (Hp96 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x94) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x96)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp96) in "Hpc".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x96)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              R11 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi96").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R10 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (R11 !!! Regidx (mword_of_int 9 : mword 5)))]> R11).
    assert (Hp98 : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x96) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x98)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp98) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x98)) (mword_of_int 1 : mword 5) (mword_of_int 2096960 : mword 21)
              R10 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi98").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (Wk := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x98) : mword 64) 4)]> R10).
    assert (Htgt : add_vec (mword_of_int (KernelSyms.kvmmake + 0x98) : mword 64) (sign_extend' 64 (mword_of_int 2096960 : mword 21)) = mword_of_int KernelSyms.kvmmap) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt) in "Hpc".
    assert (HWka1 : Wk !!! Regidx (mword_of_int 11 : mword 5) = mword_of_int 0x3FFFFFF000).
    { rewrite /Wk /R10. repeat (rewrite upd_ne; [| reg_neq]). rewrite /R11 upd_eq. rewrite /R11b upd_eq. rewrite /R11a upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka2 : Wk !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int 0x80006000).
    { rewrite /Wk /R10 /R11 /R11b /R11a. repeat (rewrite upd_ne; [| reg_neq]). rewrite /R12 upd_eq. rewrite /R12a upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka3 : Wk !!! Regidx (mword_of_int 13 : mword 5) = mword_of_int (Z.of_nat 1 * 4096)).
    { rewrite /Wk /R10 /R11 /R11b /R11a /R12 /R12a. repeat (rewrite upd_ne; [| reg_neq]). rewrite /R13 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka4 : Wk !!! Regidx (mword_of_int 14 : mword 5) = mword_of_int 10).
    { rewrite /Wk /R10 /R11 /R11b /R11a /R12 /R12a /R13. repeat (rewrite upd_ne; [| reg_neq]). rewrite /R14 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (HWka0 : Wk !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { peel_reg_step. rewrite add_vec_zero_l. peel_reg_step. exact HM9. }
    assert (Hppn : (autocast (T := mword) (subrange_vec_dec (Wk !!! Regidx (mword_of_int 12 : mword 5)) 55 12) : mword 44) = tramp_ppn) by (rewrite HWka2; apply bv_eq; vm_compute; reflexivity).
    assert (Hsvpn : svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5)) = tramp_vpn) by (rewrite HWka1; apply bv_eq; vm_compute; reflexivity).
    assert (Havin : avail_sub (Some nb) (1 + gsprev) = Some (nb - (1 + gsprev))%nat) by (rewrite avail_sub_Some; reflexivity).
    iEval (rewrite Havin) in "Henv".
    assert (Hbud : (pt_missing t (svpn_of (Wk !!! Regidx (mword_of_int 11 : mword 5))) 1 < nb - (1 + gsprev))%nat).
    { rewrite Hsvpn. apply (budget_arm _ 2 gsprev 99 nb (bound_tramp t) Hgs ltac:(nat_le) Hnb). }
    iDestruct (cpu_own_transport CID0 CID9 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (wp_kvmmap γa Wk t kvm_m5 1 10 0%nat (K - 4)%nat eb p (Some (nb - (1 + gsprev))%nat) b lks
              ltac:(vm_compute; reflexivity) Hc34 ltac:(rewrite HWka0 Hbase; reflexivity)
              ltac:(rewrite HWka1; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite HWka2; apply bv_eq; vm_compute; reflexivity)
              HWka3 ltac:(nat_le) HWka4 kmk_perm_ok10
              ltac:(rewrite HWka1; rewrite uint_unsigned; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity)
              ltac:(rewrite HWka2; rewrite uint_unsigned; apply (proj1 (Z.ltb_lt _ _)); vm_compute; reflexivity)
              Hrep
              ltac:(intros i Hi; rewrite Hsvpn; rewrite (lt1 i Hi);
                    assert (Hv0 : vpn_at tramp_vpn 0 = tramp_vpn) by (apply bv_eq; apply vpn_at_0_bv);
                    rewrite Hv0; exact kvm_m5_none_tramp)
              ltac:(eexists; split; [reflexivity | exact Hbud])
              Hbelow
              with "Hcg Hcnt Htext Hpc Hptree [Henv]").
    { iExact "Henv". }
    iIntros (CID10 Hs10 mr t' g) "Hcg Hcnt Hpc Hptree %Hnodes' Henv %Hkcs %Hbase' %Hrep' %Hpres %Hgmiss".
    assert (Hret : ret_pc (Wk !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kvmmake + 0x9c)).
    { rewrite /Wk upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret) in "Hpc".
    iEval (rewrite avail_recomb) in "Henv".
    rewrite Hsvpn Hppn in Hrep'.
    assert (HcsMWk : callee_saved M Wk).
    { rewrite /Wk /R10 /R11 /R11b /R11a /R12 /R12a /R13 /R14.
      repeat (apply callee_saved_insert_r; [vm_compute; reflexivity |]). apply callee_saved_refl. }
    assert (HcsMmr : callee_saved M mr) by (apply (callee_saved_trans _ Wk _ HcsMWk Hkcs)).
    iSpecialize ("Hcont" $! CID10 with "[]"); [ iPureIntro; wp_next_chain | ].
    iApply ("Hcont" $! mr t' g with "Hcg Hcnt Hpc Hptree Henv [%] [%] [%] [%] [%] [%] [%]").
    { exact HcsMmr. }
    { rewrite (callee_saved_lookup HcsMmr (mword_of_int 9) ltac:(vm_compute; reflexivity)). exact HM9. }
    { rewrite (callee_saved_lookup HcsMmr csp_rs1 ltac:(vm_compute; reflexivity)). exact Hsp. }
    { rewrite Hbase'. exact Hbase. }
    { unfold kvm_map. exact Hrep'. }
    { rewrite Hnodes'. reflexivity. }
    { apply (Nat.le_trans _ _ _ Hgmiss). rewrite Hsvpn. exact (bound_tramp t). }
  Qed.

  (* ================================================================= *)
  (* THE WHOLE-FUNCTION BODY: prologue -> six kvmmap regions ->         *)
  (* proc_mapstacks -> epilogue, with the pt_nodes=102 / consumption-166 *)
  (* pinning.                                                           *)
  (* ================================================================= *)
  Lemma wp_kvmmake_sconf_gen (γa : gname) (mm : regfile)
      (lvl K : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string) :
    wp_kvmmake_sconf_body γa mm lvl K eb p on b lks.
  Proof.
    unfold wp_kvmmake_sconf_body.
    intros Hlvl HK Hex Hbelow.
    destruct Hex as (nb & Hon & Hnbk).
    subst lvl. subst on.
    assert (Hnb : (166 < nb)%nat) by (exact Hnbk).
    pose proof (cap_bounds K HK) as (Hc4 & Hc2 & Hc14 & Hc34 & Hc44).
    iIntros "Hcg Hcnt #Htext Hpc Henv Hcont".
    (* ---- prologue: frame + root kalloc + memset -> pt_empty_node bppn ---- *)
    iApply (wp_kmk_prologue_node γa mm K eb p nb b lks Hbelow HK Hnbk
              with "Hcg Hcnt Htext Hpc Henv").
    iIntros (CIDpr Hspr M0 bppn) "Hcg Hcnt Hpc Hptree Henv Hc1 Hc2 Hc3 Hc4 %H9 %Hsp0 %H18 %H19 %H20 %H21 %H22 %H23 %H24 %H25 %H26 %H27".
    (* ---- region 1: UART ---- *)
    iApply (wp_kmk_region_uart γa mm M0 bppn K eb p nb 0%nat b lks
              Hbelow HK Hnb (Nat.le_0_l 0) Hsp0 H9
              with "Hcg Hcnt Htext Hpc Hptree Henv").
    iIntros (CID1 Hs1 mr1 t1 g1) "Hcg Hcnt Hpc Hptree Henv %Hcs1 %H9_1 %Hsp1 %Hbase1 %Hrep1 %Hnodes1 %Hg1".
    (* ---- region 2: VIRTIO ---- *)
    assert (Bv : (0 + g1 <= 2)%nat) by (rewrite Nat.add_0_l; exact Hg1).
    iApply (wp_kmk_region_virtio γa mm mr1 bppn t1 K eb p nb (0 + g1)%nat b lks
              Hbelow HK Hnb Bv Hsp1 H9_1 Hbase1 Hrep1
              with "Hcg Hcnt Htext Hpc Hptree Henv").
    iIntros (CID2 Hs2 mr2 t2 g2) "Hcg Hcnt Hpc Hptree Henv %Hcs2 %H9_2 %Hsp2 %Hbase2 %Hrep2 %Hnodes2 %Hg2".
    (* ---- region 3: PLIC ---- *)
    assert (Bp : (0 + g1 + g2 <= 2)%nat) by exact (acc_step (0+g1) g2 2 0 2 Bv Hg2 ltac:(nat_le)).
    iApply (wp_kmk_region_plic γa mm mr2 bppn t2 K eb p nb (0 + g1 + g2)%nat b lks
              Hbelow HK Hnb Bp Hsp2 H9_2 Hbase2 Hrep2
              with "Hcg Hcnt Htext Hpc Hptree Henv").
    iIntros (CID3 Hs3 mr3 t3 g3) "Hcg Hcnt Hpc Hptree Henv %Hcs3 %H9_3 %Hsp3 %Hbase3 %Hrep3 %Hnodes3 %Hg3".
    (* ---- region 4: text ---- *)
    assert (Bt : (0 + g1 + g2 + g3 <= 34)%nat) by exact (acc_step (0+g1+g2) g3 2 32 34 Bp Hg3 ltac:(nat_le)).
    iApply (wp_kmk_region_text γa mm mr3 bppn t3 K eb p nb (0 + g1 + g2 + g3)%nat b lks
              Hbelow HK Hnb Bt Hsp3 H9_3 Hbase3 Hrep3
              with "Hcg Hcnt Htext Hpc Hptree Henv").
    iIntros (CID4 Hs4 mr4 t4 g4) "Hcg Hcnt Hpc Hptree Henv %Hcs4 %H9_4 %Hsp4 %Hbase4 %Hrep4 %Hnodes4 %Hg4".
    (* ---- region 5: data ---- *)
    assert (Bd : (0 + g1 + g2 + g3 + g4 <= 36)%nat) by exact (acc_step (0+g1+g2+g3) g4 34 2 36 Bt Hg4 ltac:(nat_le)).
    iApply (wp_kmk_region_data γa mm mr4 bppn t4 K eb p nb (0 + g1 + g2 + g3 + g4)%nat b lks
              Hbelow HK Hnb Bd Hsp4 H9_4 Hbase4 Hrep4
              with "Hcg Hcnt Htext Hpc Hptree Henv").
    iIntros (CID5 Hs5 mr5 t5 g5) "Hcg Hcnt Hpc Hptree Henv %Hcs5 %H9_5 %Hsp5 %Hbase5 %Hrep5 %Hnodes5 %Hg5".
    (* ---- region 6: trampoline ---- *)
    assert (Br : (0 + g1 + g2 + g3 + g4 + g5 <= 99)%nat) by exact (acc_step (0+g1+g2+g3+g4) g5 36 63 99 Bd Hg5 ltac:(nat_le)).
    iApply (wp_kmk_region_tramp γa mm mr5 bppn t5 K eb p nb (0 + g1 + g2 + g3 + g4 + g5)%nat b lks
              Hbelow HK Hnb Br Hsp5 H9_5 Hbase5 Hrep5
              with "Hcg Hcnt Htext Hpc Hptree Henv").
    iIntros (CID6 Hs6 mr6 t6 g6) "Hcg Hcnt Hpc Hptree Henv %Hcs6 %H9_6 %Hsp6 %Hbase6 %Hrep6 %Hnodes6 %Hg6".
    (* ---- census pin: pt_nodes t6 = 102, growth-sum = 101 ---- *)
    assert (HN : pt_nodes t6 = (1 + g1 + g2 + g3 + g4 + g5 + g6)%nat).
    { rewrite Hnodes6 Hnodes5 Hnodes4 Hnodes3 Hnodes2 Hnodes1. reflexivity. }
    destruct (pin_all (pt_nodes t6) g1 g2 g3 g4 g5 g6 HN Hg1 Hg2 Hg3 Hg4 Hg5 Hg6 (pt_nodes_ge_102 t6 Hrep6))
      as (Hnodes6_102 & Hgtot101).
    (* ---- proc_mapstacks: mv a0,s1; jal ---- *)
    iPoseProof (kmki_9c with "Htext") as "Hi9c".
    iPoseProof (kmki_9e with "Htext") as "Hi9e".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x9c)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mr6 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi9c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (Wm := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mr6 !!! Regidx (mword_of_int 9 : mword 5)))]> mr6).
    assert (Hp9e : add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x9c) : mword 64) 2 = mword_of_int (KernelSyms.kvmmake + 0x9e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp9e) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.kvmmake + 0x9e)) (mword_of_int 1 : mword 5) (mword_of_int 1516 : mword 21)
              Wm (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi9e").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (Wp := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.kvmmake + 0x9e) : mword 64) 4)]> Wm).
    assert (Htgtp : add_vec (mword_of_int (KernelSyms.kvmmake + 0x9e) : mword 64) (sign_extend' 64 (mword_of_int 1516 : mword 21)) = mword_of_int KernelSyms.proc_mapstacks) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtp) in "Hpc".
    (* pms-entry register facts *)
    assert (HWp10 : Wp !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 (concat_vec (pt_base t6) (zeros' 12 : mword 12))).
    { rewrite /Wp. rewrite upd_ne; [| reg_neq]. rewrite /Wm upd_eq. rewrite add_vec_zero_l. rewrite H9_6 Hbase6. reflexivity. }
    assert (HcsW : callee_saved mr6 Wp).
    { rewrite /Wp /Wm. repeat (apply callee_saved_insert_r; [vm_compute; reflexivity |]). apply callee_saved_refl. }
    iDestruct (cpu_own_transport CID6 CID8 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (wp_pms γa Wp t6 kvm_map 0%nat (K - 4)%nat eb p (avail_sub (Some nb) (1 + (0 + g1 + g2 + g3 + g4 + g5 + g6))) b lks
              ltac:(vm_compute; reflexivity) Hc44 HWp10 Hrep6 kmk_kstack_None
              ltac:(exists (nb - (1 + (0 + g1 + g2 + g3 + g4 + g5 + g6)))%nat; split;
                    [apply avail_sub_Some
                    | rewrite (kstacks_missing_zero t6 Hrep6);
                      exact (pms_budget_arm (0 + g1 + g2 + g3 + g4 + g5 + g6) 101 nb ltac:(rewrite Hgtot101; nat_le) ltac:(nat_le) Hnb)])
              Hbelow
              with "Hcg Hcnt Htext Hpc Hptree [Henv]").
    { rewrite avail_sub_Some. iExact "Henv". }
    iIntros (CID9 Hs9 mr7 t7 g7 pas) "Hcg Hcnt Hpc Hptree %Hnodes7' Henv %Hcs7 %Hbase7' %Hpasok %Hrep7 %Hg7le Hpages".
    (* g7 = 0 (no growth left) and pt_nodes t7 = 102 *)
    assert (Hg7 : g7 = 0%nat).
    { pose proof (kstacks_missing_zero t6 Hrep6) as Hkm0. rewrite Hkm0 in Hg7le. exact (proj1 (Nat.le_0_r g7) Hg7le). }
    assert (Hnodes7 : pt_nodes t7 = 102%nat).
    { rewrite Hnodes7'. rewrite Hnodes6_102 Hg7. reflexivity. }
    (* pc back at +0xa2 *)
    assert (Hreta2 : ret_pc (Wp !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.kvmmake + 0xa2)).
    { rewrite /Wp upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hreta2) in "Hpc".
    (* consumption folds to K_kvmmake *)
    iEval (rewrite !avail_sub_Some) in "Henv".
    iEval (rewrite (kmk_consume nb (0 + g1 + g2 + g3 + g4 + g5 + g6) g7 Hnb Hgtot101 Hg7)) in "Henv".
    iEval (rewrite <- (avail_sub_Some nb K_kvmmake)) in "Henv".
    (* callee-saved chain from the prologue output to the pms output *)
    assert (HcsAll : callee_saved M0 mr7).
    { eapply callee_saved_trans; [exact Hcs1 |].
      eapply callee_saved_trans; [exact Hcs2 |].
      eapply callee_saved_trans; [exact Hcs3 |].
      eapply callee_saved_trans; [exact Hcs4 |].
      eapply callee_saved_trans; [exact Hcs5 |].
      eapply callee_saved_trans; [exact Hcs6 |].
      eapply callee_saved_trans; [exact HcsW | exact Hcs7]. }
    assert (Hbase7 : pt_base t7 = bppn) by (rewrite Hbase7'; exact Hbase6).
    (* ---- epilogue ---- *)
    (* [wp_kvmmake_epilogue_sconf] was sealed in the EARLIER [KvmmakeHouse]
       section, which already closed: its own [(CID0 := CID)] pin (in its
       own statement) generalized THAT section's ambient [CID] into a
       SEPARATE, auto-inserted leading implicit of the lemma -- distinct
       from EPI's own `{CID0} binder and from THIS section's [CID].  Both
       must be pinned EXPLICITLY here: leaving either bare lets eager
       typeclass resolution (triggered while elaborating this application,
       BEFORE [iApply] ever unifies against "Hcont"/"Hcg") grab whatever
       CpuId happens to be nearest in the tactic's local context -- which
       silently defeats EPI's own [CID0] generality even though EPI's
       OWN standalone type is perfectly correct (checked separately). *)
    iApply (wp_kvmmake_epilogue_sconf (CID := CID) (CID0 := CID9) γa mm mr7 t7 pas K 0%nat eb p (Some nb) b lks
              eq_refl HK
              ltac:(wp_next_chain)
              ltac:(rewrite (callee_saved_lookup HcsAll csp_rs1 ltac:(vm_compute; reflexivity)); exact Hsp0)
              ltac:(rewrite Hbase7; rewrite (callee_saved_lookup HcsAll (mword_of_int 9) ltac:(vm_compute; reflexivity)); exact H9)
              ltac:(rewrite (callee_saved_lookup HcsAll (mword_of_int 18) ltac:(vm_compute; reflexivity)); exact H18)
              ltac:(rewrite (callee_saved_lookup HcsAll (mword_of_int 19) ltac:(vm_compute; reflexivity)); exact H19)
              ltac:(rewrite (callee_saved_lookup HcsAll (mword_of_int 20) ltac:(vm_compute; reflexivity)); exact H20)
              ltac:(rewrite (callee_saved_lookup HcsAll (mword_of_int 21) ltac:(vm_compute; reflexivity)); exact H21)
              ltac:(rewrite (callee_saved_lookup HcsAll (mword_of_int 22) ltac:(vm_compute; reflexivity)); exact H22)
              ltac:(rewrite (callee_saved_lookup HcsAll (mword_of_int 23) ltac:(vm_compute; reflexivity)); exact H23)
              ltac:(rewrite (callee_saved_lookup HcsAll (mword_of_int 24) ltac:(vm_compute; reflexivity)); exact H24)
              ltac:(rewrite (callee_saved_lookup HcsAll (mword_of_int 25) ltac:(vm_compute; reflexivity)); exact H25)
              ltac:(rewrite (callee_saved_lookup HcsAll (mword_of_int 26) ltac:(vm_compute; reflexivity)); exact H26)
              ltac:(rewrite (callee_saved_lookup HcsAll (mword_of_int 27) ltac:(vm_compute; reflexivity)); exact H27)
              ltac:(unfold kvm_map_full; exact Hrep7)
              Hnodes7 Hpasok
              with "Hcg Hcnt Htext Hpc Hc1 Hc2 Hc3 Hc4 Hptree Henv Hpages Hcont").
  Qed.

End KvmmakeBody.

(* ===================================================================== *)
(* THE SEALED FUNCTOR: instantiate the four callee WP hypotheses with the *)
(* callees' proven specs, discharging the KVMMAKE Module Type.            *)
(* ===================================================================== *)
Module KvmmakeProof (AK : KALLOC) (MS : MEMSET) (KM : KVMMAP) (PM : PROC_MAPSTACKS) : KVMMAKE.
  (* [wp_kvmmake_sconf_gen]'s four callee [Hypothesis]es are each their OWN
     fresh `{CID:CpuId}`-generic forall (see the comment above them): passed
     BARE, at this [Definition]'s own ambient [CID], implicit-argument
     insertion would silently collapse that genericity (the exact trap
     documented for [ProofKvminit.v]'s [KvminitProof]).  Eta-expand each. *)
  Definition wp_kvmmake_sconf `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string)
      : wp_kvmmake_sconf_body γa mm lvl K eb p on b lks :=
    wp_kvmmake_sconf_gen
      (fun (CID' : CpuId) => AK.wp_kalloc_sconf (CID := CID'))
      (fun (CID' : CpuId) => MS.wp_memset_sconf (CID := CID'))
      (fun (CID' : CpuId) => KM.wp_kvmmap_sconf (CID := CID'))
      (fun (CID' : CpuId) => PM.wp_proc_mapstacks_sconf (CID := CID'))
      γa mm lvl K eb p on b lks.
End KvmmakeProof.
