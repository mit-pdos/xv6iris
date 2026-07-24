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
Require Import RiscvPtsto RiscvLang RiscvExtras RiscvExec RiscvFetchExec.
Require Import SmodeCore RegFile WpGpr WpMmodeShiftiop WpMmodeMul WpMmodeLeafBase ExecCommon VcGen.
Require Import IntrDefs WpSmodeIntr WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpAuipc.
Require Import WpLock CpuOwn.
Require Import CalleeSaved StackOwn.
Require Import InstrBytes KernelText.
Require Import ProcGeom SwtchCtx.
Require Import KallocInv.
Require Import PtTree PtBuild KptPt KptExecMap KvmMap KvmSpec.
Require Import WpKvmmakeInstr.
Require Import SpecKalloc SpecMemset SpecKvmmap SpecProcMapstacks SpecKvmmake.
From Kernel Require KernelSyms.
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

(* ===================================================================== *)
(* THE WP HOUSE.                                                          *)
(* ===================================================================== *)

(* frame push (-32) then pop (+32) cancels -- avoids vm_compute on a
   symbolic sp (the classic OOM). *)
Lemma kmk_sp_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64) = 18446744073709551584) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64) = 32) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551584 + 32) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

Section KvmmakeHouse.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Notation KMK := KernelSyms.kvmmake.

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
  Lemma wp_kvmmake_epilogue_sconf (γ : gname) (γa : gname)
      (Φ : mval -> iProp Σ)
      (mm Mf : regfile) (tf : ptree) (pas : nat -> mword 44)
      (K lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
    lvl = 0%nat ->
    (48 <= K)%nat ->
    Mf !!! Regidx csp_rs1 = spr ->
    Mf !!! Regidx (mword_of_int 9 : mword 5)
      = zero_extend' 64 (concat_vec (pt_base tf) (zeros' 12 : mword 12)) ->
    Mf !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4) ->
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
    sie_cap_gpr γ Mf (K - 4)%nat -∗ cpu_own γ lvl eb p C -∗
    kernel_text -∗
    pc_is (mword_of_int (KMK + 0xa2)) -∗
    pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
    pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
    pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
    (∃ v4 : bv 64, pa_stk sp0 4 ↦₈ v4) -∗
    ptree_own 2 (DfracOwn 1) tf -∗
    kalloc_env γa (avail_sub on K_kvmmake) (mm !!! Regidx (mword_of_int 4)) -∗
    ([∗ list] i ∈ seq 0 64,
       page_own (zero_extend' 64 (concat_vec (pas i) (zeros' 12 : mword 12)))) -∗
    ( ∀ (mr : regfile) (t : ptree) (pas' : nat -> mword 44),
      sie_cap_gpr γ mr K -∗ cpu_own γ lvl eb p C -∗ pc_is ret_tgt -∗
      ptree_own 2 (DfracOwn 1) t -∗
      ⌜mr !!! Regidx (mword_of_int 10)
         = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))⌝ -∗
      ⌜pt_rep0 t (kvm_map_full pas')⌝ -∗
      ⌜pt_nodes t = 102%nat⌝ -∗
      kalloc_env γa (avail_sub on K_kvmmake) (mm !!! Regidx (mword_of_int 4)) -∗
      ⌜callee_saved mm mr⌝ -∗
      ⌜kvm_pas_ok pas'⌝ -∗
      ([∗ list] i ∈ seq 0 64,
         page_own (zero_extend' 64 (concat_vec (pas' i) (zeros' 12 : mword 12)))) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spr ret_tgt Hlvl HK Hsp Hs1 Htp Hx18 Hx19 Hx20 Hx21 Hx22 Hx23 Hx24 Hx25 Hx26 Hx27
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
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (KMK + 0xa2)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              Mf (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hia2 [-]").
    iIntros "Hcg Hpc".
    set (E0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (Mf !!! Regidx (mword_of_int 9 : mword 5)))]> Mf).
    assert (Hpa4 : add_vec_int (mword_of_int (KMK + 0xa2) : mword 64) 2 = mword_of_int (KMK + 0xa4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa4) in "Hpc".
    assert (HE0sp : E0 !!! Regidx csp_rs1 = spr) by (rewrite /E0; rewrite upd_ne; [| reg_neq]; exact Hsp).
    (* +0xa4 ld ra,24(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (KMK + 0xa4)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              E0 (K - 4)%nat (mm !!! Regidx (mword_of_int 1 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hia4 [Hc1] [-]").
    { iEval (rewrite HE0sp Hb1). iExact "Hc1". }
    iIntros "Hcg Hpc Hc1". iEval (rewrite HE0sp Hb1) in "Hc1".
    set (E1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 1 : mword 5))]> E0).
    assert (Hpa6 : add_vec_int (mword_of_int (KMK + 0xa4) : mword 64) 2 = mword_of_int (KMK + 0xa6)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa6) in "Hpc".
    assert (HE1sp : E1 !!! Regidx csp_rs1 = spr) by (rewrite /E1; rewrite upd_ne; [| reg_neq]; exact HE0sp).
    (* +0xa6 ld s0,16(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (KMK + 0xa6)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              E1 (K - 4)%nat (mm !!! Regidx (mword_of_int 8 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hia6 [Hc2] [-]").
    { iEval (rewrite HE1sp Hb2). iExact "Hc2". }
    iIntros "Hcg Hpc Hc2". iEval (rewrite HE1sp Hb2) in "Hc2".
    set (E2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 8 : mword 5))]> E1).
    assert (Hpa8 : add_vec_int (mword_of_int (KMK + 0xa6) : mword 64) 2 = mword_of_int (KMK + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpa8) in "Hpc".
    assert (HE2sp : E2 !!! Regidx csp_rs1 = spr) by (rewrite /E2; rewrite upd_ne; [| reg_neq]; exact HE1sp).
    (* +0xa8 ld s1,8(sp) *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (KMK + 0xa8)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              E2 (K - 4)%nat (mm !!! Regidx (mword_of_int 9 : mword 5))
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hia8 [Hc3] [-]").
    { iEval (rewrite HE2sp Hb3). iExact "Hc3". }
    iIntros "Hcg Hpc Hc3". iEval (rewrite HE2sp Hb3) in "Hc3".
    set (E3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (mm !!! Regidx (mword_of_int 9 : mword 5))]> E2).
    assert (Hpaa : add_vec_int (mword_of_int (KMK + 0xa8) : mword 64) 2 = mword_of_int (KMK + 0xaa)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpaa) in "Hpc".
    assert (HE3sp : E3 !!! Regidx csp_rs1 = spr) by (rewrite /E3; rewrite upd_ne; [| reg_neq]; exact HE2sp).
    (* +0xaa addi sp,sp,32 -- the frame pop *)
    set (E4 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3).
    assert (Hwv : add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HE3sp. unfold spr. apply kmk_sp_cancel. }
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
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (KMK + 0xaa)) (mword_of_int 2 : mword 6)
              E3 (K - 4)%nat 4 Hpop with "Hcg Hpc Hiaa Hframe [-]").
    iIntros "Hcg Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (E3 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> E3) with E4.
    assert (Hnk : ((K - 4) + 4)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpac : add_vec_int (mword_of_int (KMK + 0xaa) : mword 64) 2 = mword_of_int (KMK + 0xac)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpac) in "Hpc".
    (* +0xac ret *)
    assert (HE4ra : E4 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by peel_reg.
    assert (Hrt : ret_pc (E4 !!! Regidx (mword_of_int 1 : mword 5)) = ret_tgt) by (rewrite HE4ra; reflexivity).
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (KMK + 0xac)) (mword_of_int 1 : mword 5) E4 K
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hiac [-]").
    iIntros "Hcg Hpc". iEval (rewrite Hrt) in "Hpc".
    (* a0 = root byte address *)
    assert (HE4a0 : E4 !!! Regidx (mword_of_int 10 : mword 5)
                    = zero_extend' 64 (concat_vec (pt_base tf) (zeros' 12 : mword 12))).
    { rewrite /E4. rewrite upd_ne; [| reg_neq]. rewrite /E3. rewrite upd_ne; [| reg_neq].
      rewrite /E2. rewrite upd_ne; [| reg_neq]. rewrite /E1. rewrite upd_ne; [| reg_neq].
      rewrite /E0 upd_eq. rewrite add_vec_zero_l. exact Hs1. }
    iApply ("Hcont" $! E4 tf pas with "Hcg Hcnt Hpc Hptree [%] [%] [%] Henv [%] [%] Hpages").
    { exact HE4a0. }
    { exact Hrep. }
    { exact Hnodes. }
    { (* callee_saved mm E4 *)
      unfold callee_saved.
      split. { rewrite /E4 upd_eq. rewrite HE3sp. unfold spr. apply kmk_sp_cancel. }
      split. { rewrite /E4 /E3 /E2 /E1 /E0. repeat (rewrite upd_ne; [| reg_neq]). exact Htp. }
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
