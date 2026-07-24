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
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras RiscvExec RiscvFetchExec.
Require Import SmodeCore RegFile WpGpr WpMmodeShiftiop WpMmodeMul WpMmodeLeafBase ExecCommon VcGen.
Require Import IntrDefs WpSmodeIntr WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl WpAuipc.
Require Import WpLock CpuOwn.
Require Import CalleeSaved StackOwn.
Require Import InstrBytes KernelText.
Require Import ProcGeom SwtchCtx.
Require Import KallocInv.
Require Import PtTree PtBuild KptPt KptExecMap KMap KptTree KvmMap KvmSpec.
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

(* clean-context cap bounds (no mword in scope, so [lia] is safe here). *)
Lemma cap_bounds (K : nat) : (48 <= K)%nat ->
  (4 <= K)%nat /\ (2 <= K - 4)%nat /\ (14 <= K - 4)%nat /\
  (34 <= K - 4)%nat /\ (44 <= K - 4)%nat.
Proof. lia. Qed.

Lemma lt1 (i : nat) : (i < 1)%nat -> i = 0%nat.
Proof. lia. Qed.

(* Z-only (bv-free) node-page range arithmetic, so [lia] never sees a bv. *)
Lemma kdata_bound_arith (z : Z) :
  (z mod 4096 = 0)%Z -> (0x80023558 <= z)%Z -> (z < 0x88000000)%Z ->
  (ram_base <= z)%Z /\ (z + 4096 <= ram_base + ram_size)%Z.
Proof.
  intros Hm Hlo Hhi. apply Z.mod_divide in Hm; [| lia]. destruct Hm as [k Hk].
  unfold ram_base, ram_size. lia.
Qed.

Lemma kda_arith (z : Z) : (0x80023558 <= z)%Z -> (text_end <= z)%Z.
Proof. unfold text_end. lia. Qed.

(* ===================================================================== *)
(* STEP 3-4: prologue (4-slot frame push, ra/s0/s1 saves, s0:=sp+32),     *)
(* the root kalloc, and memset -> the empty root node [t0].  Sealed and    *)
(* parameterized by the callee WP lemmas so it compiles standalone.        *)
(* ===================================================================== *)
Section KvmmakeBody.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{CID : CpuId}.

  Notation KMK := KernelSyms.kvmmake.

  Hypothesis wp_kalloc :
    forall (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (γk : gname * gname)
      (fl : mword 64) (m : regfile) (cpuold : mword 64) (on : option nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat),
      wp_kalloc_sconf_body γ Φ γl γk fl m cpuold on n eb p C K.
  Hypothesis wp_memset :
    forall (γ : gname) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (len : nat)
      (cval : mword 64) (olds : nat -> bv 8),
      wp_memset_sconf_body γ Φ m0 n len cval olds.

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

  Local Lemma kmk_bytes_choose (n : nat) :
    forall (start : nat) (P : nat -> bv 8 -> iProp Σ),
    ([∗ list] k ∈ seq start n, ∃ b : bv 8, P k b) ⊢
    ∃ f : nat -> bv 8, [∗ list] k ∈ seq start n, P k (f k).
  Proof.
    induction n as [|n IH]; intros start P.
    - iIntros "_". iExists (fun _ => bv_0 8). done.
    - cbn [seq]. rewrite big_sepL_cons.
      iIntros "[Hh Ht]". iDestruct "Hh" as (b) "Hh".
      iDestruct (IH (S start) P with "Ht") as (f) "Ht".
      iExists (fun k => if Nat.eq_dec k start then b else f k).
      rewrite big_sepL_cons. iSplitL "Hh".
      + destruct (Nat.eq_dec start start) as [_|Hne]; [ iExact "Hh" | done ].
      + iApply (big_sepL_impl with "Ht"). iIntros "!>" (k y Hy) "H".
        destruct (Nat.eq_dec y start) as [He|_].
        * exfalso. apply elem_of_list_lookup_2 in Hy. apply elem_of_seq in Hy. lia.
        * iExact "H".
  Qed.

  Lemma wp_kmk_prologue_node
      (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (K : nat)
      (eb : bool) (p : mword 64) (C : iProp Σ) (nb : nat) :
    let sp0 := mm !!! Regidx csp_rs1 in
    let spr := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) in
    (48 <= K)%nat ->
    (K_kvmmake < nb)%nat ->
    mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
    sie_cap_gpr γ mm K -∗
    cpu_own γ 0%nat eb p C -∗ kernel_text -∗
    pc_is (mword_of_int KMK) -∗
    kalloc_env γa (Some nb) (mm !!! Regidx (mword_of_int 4)) -∗
    ( ∀ (M : regfile) (bppn : mword 44),
      sie_cap_gpr γ M (K - 4)%nat -∗
      cpu_own γ 0%nat eb p C -∗
      pc_is (mword_of_int (KMK + 0x18)) -∗
      ptree_own 2 (DfracOwn 1) (pt_empty_node bppn) -∗
      kalloc_env γa (avail_sub (Some nb) 1) (mm !!! Regidx (mword_of_int 4)) -∗
      pa_stk sp0 1 ↦₈ (mm !!! Regidx (mword_of_int 1)) -∗
      pa_stk sp0 2 ↦₈ (mm !!! Regidx (mword_of_int 8)) -∗
      pa_stk sp0 3 ↦₈ (mm !!! Regidx (mword_of_int 9)) -∗
      (∃ v4 : bv 64, pa_stk sp0 4 ↦₈ v4) -∗
      ⌜M !!! Regidx (mword_of_int 9)
         = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))⌝ -∗
      ⌜M !!! Regidx csp_rs1 = spr⌝ -∗
      ⌜M !!! Regidx (mword_of_int 4) = mm !!! Regidx (mword_of_int 4)⌝ -∗
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
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros sp0 spr HK Hnb Hcid.
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
    iApply (wp_caddi_sp_push_s_sconf γ Φ (mword_of_int KMK) (mword_of_int 32 : mword 6) mm K 4 Hc4 Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    set (W1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> mm).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (v1) "Hc1". iDestruct "S2" as (v2) "Hc2".
    iDestruct "S3" as (v3) "Hc3". iDestruct "S4" as (v4) "Hc4".
    assert (HspW1 : W1 !!! Regidx csp_rs1 = spr) by (rewrite /W1; rewrite upd_eq; reflexivity).
    assert (Hp02 : add_vec_int (mword_of_int KMK : mword 64) 2 = mword_of_int (KMK + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02 sd ra,24(sp) -> slot 1 *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (KMK + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              W1 (K - 4)%nat v1 with "Hcg Hpc Hi02 [Hc1] [-]").
    { iEval (rewrite HspW1 Hb1). iExact "Hc1". }
    iIntros "Hcg Hpc Hc1". iEval (rewrite HspW1 Hb1) in "Hc1".
    assert (HW1r1 : W1 !!! Regidx (mword_of_int 1 : mword 5) = mm !!! Regidx (mword_of_int 1)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r1) in "Hc1".
    assert (Hp04 : add_vec_int (mword_of_int (KMK + 0x02) : mword 64) 2 = mword_of_int (KMK + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* +0x04 sd s0,16(sp) -> slot 2 *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (KMK + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              W1 (K - 4)%nat v2 with "Hcg Hpc Hi04 [Hc2] [-]").
    { iEval (rewrite HspW1 Hb2). iExact "Hc2". }
    iIntros "Hcg Hpc Hc2". iEval (rewrite HspW1 Hb2) in "Hc2".
    assert (HW1r8 : W1 !!! Regidx (mword_of_int 8 : mword 5) = mm !!! Regidx (mword_of_int 8)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r8) in "Hc2".
    assert (Hp06 : add_vec_int (mword_of_int (KMK + 0x04) : mword 64) 2 = mword_of_int (KMK + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 sd s1,8(sp) -> slot 3 *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (KMK + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              W1 (K - 4)%nat v3 with "Hcg Hpc Hi06 [Hc3] [-]").
    { iEval (rewrite HspW1 Hb3). iExact "Hc3". }
    iIntros "Hcg Hpc Hc3". iEval (rewrite HspW1 Hb3) in "Hc3".
    assert (HW1r9 : W1 !!! Regidx (mword_of_int 9 : mword 5) = mm !!! Regidx (mword_of_int 9)) by (rewrite /W1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HW1r9) in "Hc3".
    assert (Hp08 : add_vec_int (mword_of_int (KMK + 0x06) : mword 64) 2 = mword_of_int (KMK + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 addi s0,sp,32 (value unused; s0 reloaded from slot 2 at the epilogue) *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (KMK + 0x08)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8) (mword_of_int 8 : mword 5)
              W1 (K - 4)%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    set (W2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (W1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> W1).
    assert (Hp0a : add_vec_int (mword_of_int (KMK + 0x08) : mword 64) 2 = mword_of_int (KMK + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a jal kalloc *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (KMK + 0x0a)) (mword_of_int 1 : mword 5) (mword_of_int 2095638 : mword 21)
              W2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    set (J := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KMK + 0x0a) : mword 64) 4)]> W2).
    assert (Htgtk : add_vec (mword_of_int (KMK + 0x0a) : mword 64) (sign_extend' 64 (mword_of_int 2095638 : mword 21)) = mword_of_int KernelSyms.kalloc) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtk) in "Hpc".
    iDestruct "Henv" as (γk qcpu) "(%Hqne & %H0ne & #Hlock & Havail & Hqcpu)".
    assert (HJ4 : J !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite /J /W2 /W1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HJsp : J !!! Regidx csp_rs1 = spr).
    { rewrite /J /W2. repeat (rewrite upd_ne; [| reg_neq]). exact HspW1. }
    iApply (wp_kalloc γ Φ γa γk (mword_of_int (KernelSyms.kmem + 24))
              J qcpu (Some nb) 0%nat eb p C (K - 4)%nat
              Hc14
              ltac:(rewrite HJ4; exact Hqne)
              ltac:(rewrite HJ4; exact Hcid)
              ltac:(reflexivity)
              ltac:(vm_compute; reflexivity)
              with "Hcg Hcnt Htext Hpc Hlock Havail Hqcpu [-]").
    iIntros (mr0) "Hcg Hcnt Hpc %Hkcs0 Hkpost Hcpu2".
    assert (Hret0e : ret_pc (J !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KMK + 0x0e)).
    { rewrite /J upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret0e) in "Hpc".
    (* success arm: nb > 166 so kalloc cannot fail *)
    assert (Hcnt : Some nb = Some (S (nb - 1))).
    { f_equal. unfold K_kvmmake in Hnb. lia. }
    iEval (rewrite Hcnt) in "Hkpost".
    iDestruct (kalloc_post_success with "Hkpost") as "(%Hpv & Hpage & Havail2)".
    assert (Hav1 : Some (nb - 1)%nat = avail_sub (Some nb) 1).
    { rewrite avail_sub_Some. reflexivity. }
    iEval (rewrite Hav1) in "Havail2".
    iAssert (kalloc_env γa (avail_sub (Some nb) 1) (mm !!! Regidx (mword_of_int 4)))
      with "[Hcpu2 Havail2]" as "Henv".
    { iExists γk, (zero_reg : mword 64). iSplitR. { iPureIntro; exact H0ne. }
      iSplitR. { iPureIntro; exact H0ne. } iFrame "Hlock". iFrame "Havail2". iExact "Hcpu2". }
    set (root0 := mr0 !!! Regidx (mword_of_int 10 : mword 5)).
    (* recover callee-saved through kalloc *)
    assert (Hmr0sp : mr0 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs0 csp_rs1 ltac:(vm_compute; reflexivity)). exact HJsp. }
    assert (Hmr0tp : mr0 !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite (callee_saved_lookup Hkcs0 (mword_of_int 4) ltac:(vm_compute; reflexivity)). exact HJ4. }
    (* +0x0e mv s1,a0 : s1 := root page *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (KMK + 0x0e)) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
              mr0 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0e [-]").
    iIntros "Hcg Hpc".
    set (M1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (add_vec zero_reg (mr0 !!! Regidx (mword_of_int 10 : mword 5)))]> mr0).
    assert (Hp10 : add_vec_int (mword_of_int (KMK + 0x0e) : mword 64) 2 = mword_of_int (KMK + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 lui a2,0x1 : a2 := 4096 *)
    iApply (wp_clui_s_sconf γ Φ (mword_of_int (KMK + 0x10)) (mword_of_int 12 : mword 5) (sign_extend' 20 (mword_of_int 1 : mword 6)) (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))
              M1 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(reflexivity) with "Hcg Hpc Hi10 [-]").
    iIntros "Hcg Hpc".
    set (M2 := <[Regidx (mword_of_int 12 : mword 5) := regval_into_reg (luival (sign_extend' 20 (mword_of_int 1 : mword 6)))]> M1).
    assert (Hp12 : add_vec_int (mword_of_int (KMK + 0x10) : mword 64) 2 = mword_of_int (KMK + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* +0x12 li a1,0 *)
    iApply (wp_cli_s_sconf γ Φ (mword_of_int (KMK + 0x12)) (mword_of_int 11 : mword 5) (mword_of_int 0 : mword 6) (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))
              M2 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(reflexivity) with "Hcg Hpc Hi12 [-]").
    iIntros "Hcg Hpc".
    set (M3 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))))]> M2).
    assert (Hp14 : add_vec_int (mword_of_int (KMK + 0x12) : mword 64) 2 = mword_of_int (KMK + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 jal memset *)
    iApply (wp_jal_s_sconf γ Φ (mword_of_int (KMK + 0x14)) (mword_of_int 1 : mword 5) (mword_of_int 2096038 : mword 21)
              M3 (K - 4)%nat ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    set (M4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KMK + 0x14) : mword 64) 4)]> M3).
    assert (Htgtm : add_vec (mword_of_int (KMK + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2096038 : mword 21)) = mword_of_int KernelSyms.memset) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtm) in "Hpc".
    (* memset(root, 0, 4096): bridge page_own to the per-byte buffer *)
    assert (HM4a0 : M4 !!! Regidx (mword_of_int 10 : mword 5) = root0).
    { rewrite /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). reflexivity. }
    assert (HM4a1 : M4 !!! Regidx (mword_of_int 11 : mword 5) = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))).
    { rewrite /M4. rewrite upd_ne; [| reg_neq]. rewrite /M3 upd_eq. reflexivity. }
    assert (HM4a2 : M4 !!! Regidx (mword_of_int 12 : mword 5) = mword_of_int (Z.of_nat 4096)).
    { rewrite /M4 /M3. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M2 upd_eq. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite /page_own /byte_any) in "Hpage".
    iDestruct (kmk_bytes_choose 4096 0 (fun j b => ((pa_add root0 j) ↦ₘ b)%I) with "Hpage") as (olds) "Hbuf".
    iApply (wp_memset γ Φ M4 (K - 4)%nat 4096 (M4 !!! Regidx (mword_of_int 11 : mword 5)) olds
              Hc2 ltac:(vm_compute; reflexivity) ltac:(reflexivity) HM4a2
              with "Hcg Htext Hpc [Hbuf] [-]").
    { iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H". rewrite HM4a0. iExact "H". }
    iIntros (mfin) "Hcg Hpc Hbytes %Hmcs".
    assert (Hret18 : ret_pc (M4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KMK + 0x18)).
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
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
    iDestruct (mem_page_to_phys root0 (DfracOwn 1) (mword_of_int 0 : mword 8)
                 ltac:(intros j Hj; apply kdata_svpn_class; apply page_in_range_addr_is_kdata; [exact Hpv | exact Hj])
                 with "Hkmapb Hbytes") as "Hbytes".
    iEval (rewrite -Hpbase) in "Hbytes".
    assert (Hbppn4k : bv_unsigned bppn * 4096 = bv_unsigned root0).
    { rewrite <- (page_base_unsigned bppn). rewrite Hpbase. reflexivity. }
    assert (Hnkd : node_kdata bppn).
    { unfold node_kdata. rewrite Hbppn4k. exact (kdata_bound_arith (bv_unsigned root0) Hpal Hplo Hphi). }
    assert (Hkda : (text_end <= bv_unsigned bppn * 4096)%Z).
    { rewrite Hbppn4k. exact (kda_arith (bv_unsigned root0) Hplo). }
    iDestruct (pt_node_claim_from_static bppn Hnkd Hkda with "Hkmapb") as "#Hbclaim".
    iDestruct (zero_page_to_node 2 (DfracOwn 1) bppn with "Hbclaim Hbytes") as "Hptree".
    (* callee-saved recovery for the output register-map [mfin] *)
    assert (Hbase9 : mfin !!! Regidx (mword_of_int 9 : mword 5) = zero_extend' 64 (concat_vec bppn (zeros' 12 : mword 12))).
    { rewrite (callee_saved_lookup Hmcs (mword_of_int 9) ltac:(vm_compute; reflexivity)).
      rewrite /M4 /M3 /M2. repeat (rewrite upd_ne; [| reg_neq]). rewrite /M1 upd_eq.
      rewrite add_vec_zero_l. rewrite Hpbase. reflexivity. }
    assert (Hfsp : mfin !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hmcs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr0sp. }
    assert (Hftp : mfin !!! Regidx (mword_of_int 4 : mword 5) = mm !!! Regidx (mword_of_int 4)).
    { rewrite (callee_saved_lookup Hmcs (mword_of_int 4) ltac:(vm_compute; reflexivity)).
      rewrite /M4 /M3 /M2 /M1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmr0tp. }
    (* the s2..s11 registers: untouched since [mm] (through kalloc/memset callee-saved) *)
    iApply ("Hcont" $! mfin bppn with "Hcg Hcnt Hpc Hptree Henv Hc1 Hc2 Hc3 [Hc4] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]").
    { iExists v4. iExact "Hc4". }
    { exact Hbase9. }
    { exact Hfsp. }
    { exact Hftp. }
    all: try (
      match goal with
      | |- _ !!! Regidx (mword_of_int ?k) = _ !!! Regidx (mword_of_int ?k) =>
        rewrite (callee_saved_lookup Hmcs (mword_of_int k) ltac:(vm_compute; reflexivity));
        rewrite /M4 /M3 /M2 /M1; repeat (rewrite upd_ne; [| reg_neq]);
        rewrite (callee_saved_lookup Hkcs0 (mword_of_int k) ltac:(vm_compute; reflexivity));
        rewrite /J /W2 /W1; repeat (rewrite upd_ne; [| reg_neq]); reflexivity
      end).
  Qed.

End KvmmakeBody.
