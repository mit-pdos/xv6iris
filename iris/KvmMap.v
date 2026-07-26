(* KvmMap.v -- the CONCRETE kernel map kvmmake builds (kvm-spec item ii):
   the xv6 memory-layout constants, the six-region [kvm_map] gmap literal
   (chained [pt_insert_run]s in kvmmake's call order) + the 64 kstack
   entries, and THE BRIDGE: a table representing [kvm_map_full pas]
   satisfies the kpt mapping invariants ([kpt_tree_spec_gen] at the
   target auth map [kvm_M pas] = kmap_M0 ∪ kstacks) -- what the boot
   switch (rwx-kmap stage 6) installs into [tlb_inv_pt].

   The A/D story is free: kvmmake writes A/D-CLEAR words
   [mappages_pte ppn perm i = mk_pte (ppn+i) (perm|1)], and the gen tree
   spec's maps-clause admits ANY A/D variant --
   [pte_set_ad (mk_pte p (kperm_flags pc)) 0 0] IS [mk_pte p (perm|1)]
   (0xCB -> 0x0B text, 0xC7 -> 0x07 data/dev), and
   [pte_set_ad pte_tramp 0 0] IS the trampoline word (0x4B -> 0x0B).

   Pure (no Iris): the ghost/auth side of the switch stays in stage 6.
   See claude-notes/projects/kvm-spec.md. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list_numbers bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import RiscvExtras.
Require Import Pt4kWalk.
Require Import KptPt.
Require Import KptExecMap.
Require Import PtAdBits.
Require Import PtTree.
Require Import PtBuild.
Require Import KptTree.
Local Open Scope Z_scope.
Import Defs.

(* Keep typeclass search (rewrite/lookup resolution) from unfolding the
   [pt_insert_run] Fixpoint over the large page counts (plic 16384, data 32761)
   -- materializing those ~49k-entry maps is what makes the run rewrites blow up
   (same hazard as [kmap_M0] in KptPt).  [unfold]/[cbn] still work. *)
Global Typeclasses Opaque pt_insert_run.

(* ===================================================================== *)
(* §1 Memory-layout constants (xv6 kernel/memlayout.h; page counts).      *)
(*    KERNBASE/PHYSTOP are RiscvPtsto's ram_base/ram_base+ram_size;       *)
(*    etext is text_end; TRAMPOLINE is TrampPt's.  Only the genuinely     *)
(*    new ones are named here, at vpn/ppn granularity (the map literal    *)
(*    is vpn-keyed).                                                      *)
(* ===================================================================== *)

Definition uart_vpn   : mword 27 := mword_of_int 0x10000.
Definition virtio_vpn : mword 27 := mword_of_int 0x10001.
Definition plic_vpn   : mword 27 := mword_of_int 0xC000.
Definition text_vpn0  : mword 27 := mword_of_int 0x80000.
Definition data_vpn0  : mword 27 := mword_of_int 0x80007.

Definition plic_npages : nat := 16384%nat.  (* 0x4000000 bytes *)
Definition text_npages : nat := 7%nat.      (* [KERNBASE, etext)  *)
Definition data_npages : nat := 32761%nat.  (* 0x7FF9 = [etext, PHYSTOP);
   NOTE: the old checkpoint note said "31977" -- that was a decimal typo
   for 0x7FF9; the hex byte count 0x7FF9000 was always right, and
   0x80007 + 0x7FF9 = 0x88000 exactly (cross-checked by
   [kvm_map_lookup] against kmap_class's data range). *)

(* the identity regions' pa = va, so ppn0 = zero-extended vpn0 *)
Definition uart_ppn   : mword 44 := kpt_leaf_ppn uart_vpn.
Definition virtio_ppn : mword 44 := kpt_leaf_ppn virtio_vpn.
Definition plic_ppn   : mword 44 := kpt_leaf_ppn plic_vpn.
Definition text_ppn0  : mword 44 := kpt_leaf_ppn text_vpn0.
Definition data_ppn0  : mword 44 := kpt_leaf_ppn data_vpn0.

(* KSTACK(p) = TRAMPOLINE - (p+1)*2*PGSIZE: stack pages at even offsets
   below the trampoline vpn (odd offsets are the unmapped guard pages).
   Matches KMap's [kstack_vpn_range] window. *)
Definition kstack_vpn (i : nat) : mword 27 :=
  mword_of_int (0x3FFFFFF - 2 * (Z.of_nat i + 1)).

(* the PTE perm argument kvmmake passes for a class (WITHOUT V --
   mappages ORs V in): R|X = 10 for text/trampoline, R|W = 6 *)
Definition kperm_vperm (pc : kperm) : Z :=
  match pc with KP_rx => 10 | KP_rw => 6 end.

(* ===================================================================== *)
(* §2 The map literal, in kvmmake's exact call order.  Each region is a   *)
(*    [pt_insert_run] on the previous accumulator, so the k-th kvmmap     *)
(*    call's post IS the (k+1)-th call's [pt_rep0] precondition           *)
(*    definitionally.                                                     *)
(* ===================================================================== *)

Definition kvm_m1 : gmap (mword 27) (mword 64) :=
  pt_insert_run ∅ uart_vpn uart_ppn 6 1.
Definition kvm_m2 : gmap (mword 27) (mword 64) :=
  pt_insert_run kvm_m1 virtio_vpn virtio_ppn 6 1.
Definition kvm_m3 : gmap (mword 27) (mword 64) :=
  pt_insert_run kvm_m2 plic_vpn plic_ppn 6 plic_npages.
Definition kvm_m4 : gmap (mword 27) (mword 64) :=
  pt_insert_run kvm_m3 text_vpn0 text_ppn0 10 text_npages.
Definition kvm_m5 : gmap (mword 27) (mword 64) :=
  pt_insert_run kvm_m4 data_vpn0 data_ppn0 6 data_npages.
Definition kvm_map : gmap (mword 27) (mword 64) :=
  pt_insert_run kvm_m5 tramp_vpn tramp_ppn 10 1.

(* proc_mapstacks' 64 kstack pages at kalloc-chosen pas *)
Fixpoint kvm_stacks (pas : nat -> mword 44) (k : nat)
    : gmap (mword 27) (mword 64) -> gmap (mword 27) (mword 64) :=
  fun m => match k with
  | O => m
  | S k' => pt_insert_run (kvm_stacks pas k' m) (kstack_vpn k') (pas k') 6 1
  end.

Definition kvm_map_full (pas : nat -> mword 44) : gmap (mword 27) (mword 64) :=
  kvm_stacks pas 64 kvm_map.

(* ===================================================================== *)
(* §3 The TARGET AUTH MAP: kmap_M0 extended with the kstack entries --    *)
(*    exactly what the stage-6 switch folds [kmap_insert] over.           *)
(* ===================================================================== *)

Fixpoint kvm_M_stacks (pas : nat -> mword 44) (k : nat)
    : gmap (mword 27) (mword 44 * kperm) -> gmap (mword 27) (mword 44 * kperm) :=
  fun M => match k with
  | O => M
  | S k' => <[kstack_vpn k' := (pas k', KP_rw)]> (kvm_M_stacks pas k' M)
  end.

(* stage C: the TRAMPOLINE is an ordinary entry of the target map --
   its fragment is minted at the switch together with the kstacks *)
Definition kvm_M (pas : nat -> mword 44) : gmap (mword 27) (mword 44 * kperm) :=
  kvm_M_stacks pas 64 (<[tramp_vpn := (tramp_ppn, KP_rx)]> kmap_M0).

(* legal stack pas: each is a whole kernel-data page -- exactly PtTree's
   [node_kdata] ("ppn's 4096-byte page lies wholly in RAM").  This is what
   kalloc's [page_valid] guarantees (kalloc returns pages at [kmem_lo =
   0x80023558 >= text_end], so every stack page sits in kernel data); the
   RAM lower bound [ram_base] recorded here is the part the downstream
   [page_own_kstack] capstone needs (per-byte [addr_is_ram], which combines
   with the byte's own KP_rw claim to re-key it onto the kstack VA). *)
Definition kvm_pas_ok (pas : nat -> mword 44) : Prop :=
  forall i : nat, (i < 64)%nat -> node_kdata (pas i).

(* The naive per-run table-page cost of proc_mapstacks' 64 one-page kstack
   runs, summed against the SAME (starting) tree [t].  This is an UPPER
   BOUND on the true telescoped cost: proc_mapstacks walks the 64 kstack
   vpns in sequence, each walk grafting at most the tables the previous
   grafts left absent, so successive runs' missing-counts only DECREASE
   relative to what [pt_missing t (kstack_vpn i) 1] reports against the
   original [t].  The whole-function proof pass telescopes this
   (the kstack vpns all live under the same top L1 group just below the
   trampoline, so after the first run's grafts the shared l1 node is
   present and later runs miss at most their own l0 slot); the naive sum
   here is what the caller's budget premise is stated against, and the
   proof discharges [true_cost <= kstacks_missing t] as an obligation --
   NO admit is introduced by using the naive sum. *)
Definition kstacks_missing (t : ptree) : nat :=
  sum_list_with (fun i => pt_missing t (kstack_vpn i) 1) (seq 0 64).

(* ===================================================================== *)
(* §4 Characterizations -- the ONLY lemmas that look inside the literals  *)
(*    (never normalize them: kvm_map has ~49k entries).                   *)
(* ===================================================================== *)

(* the kstack index classifier: Some i iff vpn = kstack_vpn i, i < 64 *)
Definition kstack_index (vpn : mword 27) : option nat :=
  let v := bv_unsigned vpn in
  let d := 0x3FFFFFF - v in
  if (1 <=? d) && (d <=? 128) && (d `mod` 2 =? 0)
  then Some (Z.to_nat (d / 2 - 1)) else None.

(* ---- private arithmetic helpers (non-wrapping adds at widths 27/44) ---- *)

Local Lemma kvm_avi27 (a : mword 27) (j : Z) :
  0 <= j -> bv_unsigned a + j < 134217728 ->
  bv_unsigned (add_vec_int a j) = bv_unsigned a + j.
Proof.
  intros Hj Hfit. pose proof (vpn27_bound a) as Ha.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word,
    MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  rewrite (mword27_unsigned j ltac:(lia)).
  apply bv_wrap_small.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 27) = 134217728) as -> by (vm_compute; reflexivity).
  lia.
Qed.

Local Lemma kvm_avi44 (a : mword 44) (j : Z) :
  0 <= j -> bv_unsigned a + j < 17592186044416 ->
  bv_unsigned (add_vec_int a j) = bv_unsigned a + j.
Proof.
  intros Hj Hfit.
  pose proof (bv_unsigned_in_range _ a) as Ha.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 44) = 17592186044416) as HM by (vm_compute; reflexivity).
  rewrite HM in Ha.
  unfold add_vec_int, add_vec, Operators_mwords.word_binop,
    Operators_mwords.with_word', to_word, get_word, SailStdpp.Values.with_word,
    MachineWord.MachineWord.add.
  rewrite bv_add_unsigned.
  assert (Hjv : bv_unsigned (mword_of_int j : mword 44) = j).
  { unfold mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    assert (bv_modulus (MachineWord.MachineWord.Z_idx 44) = 17592186044416) as -> by (vm_compute; reflexivity). lia. }
  rewrite Hjv. apply bv_wrap_small.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 44) = 17592186044416) as -> by (vm_compute; reflexivity). lia.
Qed.

Local Lemma avi27_0 (a : mword 27) : add_vec_int a 0 = a.
Proof. pose proof (vpn27_bound a). apply bv_eq. rewrite (kvm_avi27 a 0 ltac:(lia) ltac:(lia)). lia. Qed.

Local Lemma avi44_0 (a : mword 44) : add_vec_int a 0 = a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Ha.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 44) = 17592186044416) as HM by (vm_compute; reflexivity).
  rewrite HM in Ha.
  apply bv_eq. rewrite (kvm_avi44 a 0 ltac:(lia) ltac:(lia)). lia.
Qed.

Local Lemma vpn_at_uns (vpn0 : mword 27) (j : nat) :
  bv_unsigned vpn0 + Z.of_nat j < 134217728 ->
  bv_unsigned (vpn_at vpn0 j) = bv_unsigned vpn0 + Z.of_nat j.
Proof. intro. unfold vpn_at. apply kvm_avi27; lia. Qed.

Local Lemma vpn_of_index (vpn0 vpn : mword 27) (j : nat) :
  bv_unsigned vpn0 + Z.of_nat j < 134217728 ->
  bv_unsigned vpn = bv_unsigned vpn0 + Z.of_nat j ->
  vpn = vpn_at vpn0 j.
Proof. intros Hb Hv. apply bv_eq. rewrite vpn_at_uns; [exact Hv | exact Hb]. Qed.

(* the identity ppn arithmetic: a run over [kpt_leaf_ppn vpn0] stays identity *)
Local Lemma kpt_leaf_ppn_run (vpn0 : mword 27) (j : nat) :
  bv_unsigned vpn0 + Z.of_nat j < 134217728 ->
  add_vec_int (kpt_leaf_ppn vpn0) (Z.of_nat j) = kpt_leaf_ppn (vpn_at vpn0 j).
Proof.
  intro Hb. unfold kpt_leaf_ppn. apply bv_eq.
  rewrite (kvm_avi44 (zero_extend' 44 vpn0) (Z.of_nat j) ltac:(lia)
             ltac:(rewrite zext44_27_unsigned; lia)).
  rewrite !zext44_27_unsigned. rewrite vpn_at_uns; [reflexivity | exact Hb].
Qed.

(* ---- per-run lookup: hit at each index, miss outside the run ---- *)
Local Lemma pt_insert_run_lookup_hit (m : gmap (mword 27) (mword 64))
    (vpn0 : mword 27) (ppn0 : mword 44) (perm : Z) (k : nat) :
  forall j : nat, (j < k)%nat -> bv_unsigned vpn0 + Z.of_nat k <= 134217728 ->
  pt_insert_run m vpn0 ppn0 perm k !! vpn_at vpn0 j = Some (mappages_pte ppn0 perm j).
Proof.
  induction k as [|k' IH]; intros j Hjk Hk; [lia|].
  cbn [pt_insert_run].
  destruct (decide (j = k')) as [->|Hne].
  - rewrite lookup_insert. reflexivity.
  - rewrite lookup_insert_ne.
    + apply IH; lia.
    + apply not_eq_sym. apply (vpn_at_ne vpn0 j k'); [lia|].
      pose proof (vpn27_bound vpn0). lia.
Qed.

Local Lemma pt_insert_run_lookup_miss (m : gmap (mword 27) (mword 64))
    (vpn0 : mword 27) (ppn0 : mword 44) (perm : Z) (k : nat) (vpn : mword 27) :
  (forall j : nat, (j < k)%nat -> vpn <> vpn_at vpn0 j) ->
  pt_insert_run m vpn0 ppn0 perm k !! vpn = m !! vpn.
Proof.
  induction k as [|k' IH]; intros Hne.
  - reflexivity.
  - cbn [pt_insert_run]. rewrite lookup_insert_ne.
    + apply IH. intros j Hj. apply Hne. lia.
    + apply not_eq_sym. apply Hne. lia.
Qed.

(* one identity run, as a range-keyed lookup (never normalizes the map) *)
Local Lemma id_run_lookup (m : gmap (mword 27) (mword 64))
    (vpn0 : mword 27) (perm : Z) (npages : nat) (vpn : mword 27) :
  bv_unsigned vpn0 + Z.of_nat npages <= 134217728 ->
  pt_insert_run m vpn0 (kpt_leaf_ppn vpn0) perm npages !! vpn =
    if (bv_unsigned vpn0 <=? bv_unsigned vpn) && (bv_unsigned vpn <? bv_unsigned vpn0 + Z.of_nat npages)
    then Some (mk_pte (kpt_leaf_ppn vpn) (Z.lor perm 1))
    else m !! vpn.
Proof.
  intros Hb. pose proof (vpn27_bound vpn) as Hv.
  destruct ((bv_unsigned vpn0 <=? bv_unsigned vpn) && (bv_unsigned vpn <? bv_unsigned vpn0 + Z.of_nat npages)) eqn:Hc.
  - apply andb_prop in Hc. destruct Hc as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    set (j := Z.to_nat (bv_unsigned vpn - bv_unsigned vpn0)).
    assert (Hjnp : (j < npages)%nat) by (subst j; lia).
    assert (Hjv : bv_unsigned vpn = bv_unsigned vpn0 + Z.of_nat j) by (subst j; lia).
    assert (Hveq : vpn = vpn_at vpn0 j) by (apply vpn_of_index; [lia | exact Hjv]).
    rewrite Hveq.
    rewrite (pt_insert_run_lookup_hit m vpn0 (kpt_leaf_ppn vpn0) perm npages j Hjnp Hb).
    unfold mappages_pte. rewrite (kpt_leaf_ppn_run vpn0 j ltac:(lia)).
    rewrite <- Hveq. reflexivity.
  - apply pt_insert_run_lookup_miss.
    intros j Hj Heq. apply andb_false_iff in Hc.
    assert (Hju : bv_unsigned vpn = bv_unsigned vpn0 + Z.of_nat j)
      by (rewrite Heq; apply vpn_at_uns; lia).
    destruct Hc as [Hc|Hc]; [apply Z.leb_nle in Hc | apply Z.ltb_nlt in Hc]; lia.
Qed.

(* one arbitrary 1-page run *)
Local Lemma one_run_lookup (m : gmap (mword 27) (mword 64))
    (vpn0 vpn : mword 27) (ppn0 : mword 44) (perm : Z) :
  pt_insert_run m vpn0 ppn0 perm 1 !! vpn =
    if decide (vpn = vpn0) then Some (mk_pte ppn0 (Z.lor perm 1)) else m !! vpn.
Proof.
  cbn [pt_insert_run]. unfold vpn_at, mappages_pte.
  change (Z.of_nat 0) with 0. rewrite (avi27_0 vpn0). rewrite (avi44_0 ppn0).
  destruct (decide (vpn = vpn0)) as [->|Hne].
  - apply lookup_insert.
  - apply lookup_insert_ne. congruence.
Qed.

(* kstack vpns: unsigned value, injectivity *)
Lemma kstack_vpn_uns (i : nat) :
  (i < 64)%nat -> bv_unsigned (kstack_vpn i) = 0x3FFFFFF - 2 * (Z.of_nat i + 1).
Proof. intro. unfold kstack_vpn. rewrite mword27_unsigned; [reflexivity | lia]. Qed.

Lemma kstack_vpn_inj (i j : nat) :
  (i < 64)%nat -> (j < 64)%nat -> i <> j -> kstack_vpn i <> kstack_vpn j.
Proof.
  intros Hi Hj Hne Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite (kstack_vpn_uns i Hi), (kstack_vpn_uns j Hj) in Heq. lia.
Qed.

(* ===================================================================== *)
(* The kstack VIRTUAL address KSTACK(i) at byte granularity: page-aligned  *)
(* just below the trampoline, whose Sv39 vpn is [kstack_vpn i].  These pure *)
(* facts are stated so the capstone [page_own_kstack] proof is assembly-    *)
(* only.  Mirrors ProofProcMapstacks' internal [va_i], lifted here as a     *)
(* shared fact (a Proof file must not be imported).                        *)
(* ===================================================================== *)
Definition kstack_va (i : nat) : mword 64 :=
  mword_of_int (0x3FFFFFF000 - 8192 * (Z.of_nat i + 1)).

Lemma kstack_va_uns (i : nat) :
  (i < 64)%nat -> bv_unsigned (kstack_va i) = 0x3FFFFFF000 - 8192 * (Z.of_nat i + 1).
Proof.
  intro Hi. unfold kstack_va, mword_of_int, Values.mword_of_int, MachineWord.MachineWord.Z_to_word.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  assert (bv_modulus (MachineWord.MachineWord.Z_idx 64) = 18446744073709551616) as -> by (vm_compute; reflexivity).
  split; [| lia]. assert (8192 * (Z.of_nat i + 1) <= 8192 * 64) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

(* low 12 bits zero: KSTACK(i) is page-aligned *)
Lemma kstack_va_align (i : nat) :
  (i < 64)%nat -> subrange_vec_dec (kstack_va i) 11 0 = (zeros' 12 : mword 12).
Proof.
  intro Hi. apply bv_eq.
  rewrite subrange64_unsigned_11_0. rewrite (kstack_va_uns i Hi).
  change (2 ^ 12) with 4096.
  replace (0x3FFFFFF000 - 8192 * (Z.of_nat i + 1)) with ((0x3FFFFFF - 2 * (Z.of_nat i + 1)) * 4096) by lia.
  rewrite Z.mod_mul; [| lia]. vm_compute. reflexivity.
Qed.

Lemma kstack_va_canon (i : nat) :
  (i < 64)%nat -> (uint (kstack_va i) < 274877906944)%Z.
Proof.
  intro Hi. rewrite uint_unsigned. rewrite (kstack_va_uns i Hi).
  assert (0 <= 8192 * (Z.of_nat i + 1)) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.

Lemma kstack_va_svpn (i : nat) :
  (i < 64)%nat -> svpn_of (kstack_va i) = kstack_vpn i.
Proof.
  intro Hi. apply bv_eq.
  rewrite (svpn_of_unsigned_lo (kstack_va i) (kstack_va_canon i Hi)).
  rewrite uint_unsigned. rewrite (kstack_va_uns i Hi). rewrite (kstack_vpn_uns i Hi).
  rewrite Z.shiftr_div_pow2; [| lia]. change (2 ^ 12) with 4096.
  replace (0x3FFFFFF000 - 8192 * (Z.of_nat i + 1)) with ((0x3FFFFFF - 2 * (Z.of_nat i + 1)) * 4096) by lia.
  rewrite Z.div_mul; [| lia]. reflexivity.
Qed.

(* the within-page offset premise the KptPt accessors want, for KSTACK(i) *)
Lemma kstack_va_off (i j : nat) :
  (i < 64)%nat -> (j < 4096)%nat ->
  (bv_unsigned (subrange_vec_dec (kstack_va i) 11 0) + Z.of_nat j < 4096)%Z.
Proof.
  intros Hi Hj.
  rewrite subrange64_unsigned_11_0. rewrite (kstack_va_uns i Hi).
  change (2 ^ 12) with 4096.
  replace (0x3FFFFFF000 - 8192 * (Z.of_nat i + 1)) with ((0x3FFFFFF - 2 * (Z.of_nat i + 1)) * 4096) by lia.
  rewrite Z.mod_mul; [| lia]. lia.
Qed.

(* per-byte (j < 4096) facts: the svpn is unchanged, the byte is canonical,
   and [pa_of] of KSTACK(i)+j is the identity page's byte offset j. *)
Lemma kstack_va_svpn_add (i j : nat) :
  (i < 64)%nat -> (j < 4096)%nat ->
  svpn_of (pa_add (kstack_va i) j) = kstack_vpn i.
Proof.
  intros Hi Hj.
  rewrite (svpn_of_pa_add (kstack_va i) j (kstack_va_canon i Hi) (kstack_va_off i j Hi Hj)).
  apply kstack_va_svpn; exact Hi.
Qed.

Lemma kstack_va_canon_add (i j : nat) :
  (i < 64)%nat -> (j < 4096)%nat ->
  (uint (pa_add (kstack_va i) j) < 274877906944)%Z.
Proof.
  intros Hi Hj. rewrite uint_unsigned. unfold pa_add.
  rewrite (pt_add_vec_int_small (kstack_va i) (Z.of_nat j) (Nat2Z.is_nonneg j)
            ltac:(rewrite (kstack_va_uns i Hi);
                  assert (0 <= 8192 * (Z.of_nat i + 1)) by (apply Z.mul_nonneg_nonneg; lia); lia)).
  rewrite (kstack_va_uns i Hi).
  assert (8192 * 1 <= 8192 * (Z.of_nat i + 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma kstack_va_pa_of (ppn : mword 44) (i j : nat) :
  (i < 64)%nat -> (j < 4096)%nat ->
  pa_of ppn (pa_add (kstack_va i) j)
  = pa_add (zero_extend' 64 (concat_vec ppn (zeros' 12 : mword 12))) j.
Proof.
  intros Hi Hj.
  rewrite (pa_of_pa_add ppn (kstack_va i) j (kstack_va_canon i Hi) (kstack_va_off i j Hi Hj)).
  assert (Hpo : pa_of ppn (kstack_va i) = zero_extend' 64 (concat_vec ppn (zeros' 12 : mword 12))).
  { unfold pa_of. rewrite (kstack_va_align i Hi). reflexivity. }
  rewrite Hpo. reflexivity.
Qed.

(* every byte of the identity page [zext (ppn ++ 0^12)] of a [node_kdata] ppn
   is real RAM -- the per-byte [addr_is_ram] the capstone needs. *)
Lemma kstack_ident_ram (ppn : mword 44) (j : nat) :
  node_kdata ppn -> (j < 4096)%nat ->
  addr_is_ram (pa_add (zero_extend' 64 (concat_vec ppn (zeros' 12 : mword 12))) j).
Proof.
  intros [Hlo Hhi] Hj. unfold addr_is_ram.
  assert (Hz : bv_unsigned (zeros' 12 : mword 12) = 0) by (vm_compute; reflexivity).
  assert (HP : bv_unsigned (zero_extend' 64 (concat_vec ppn (zeros' 12 : mword 12)) : mword 64)
               = bv_unsigned ppn * 4096).
  { rewrite zext64_concat44_12_unsigned. lia. }
  rewrite uint_unsigned. unfold pa_add.
  rewrite (pt_add_vec_int_small _ (Z.of_nat j) (Nat2Z.is_nonneg j)
            ltac:(rewrite HP; unfold ram_base, ram_size in *; lia)).
  rewrite HP. unfold ram_base, ram_size in *. lia.
Qed.

(* the kstacks-fixpoint lookup: hit at each kstack vpn, miss elsewhere *)
Lemma kvm_stacks_hit (pas : nat -> mword 44) (k : nat)
    (m : gmap (mword 27) (mword 64)) :
  forall i : nat, (i < k)%nat -> (k <= 64)%nat ->
  kvm_stacks pas k m !! kstack_vpn i = Some (mk_pte (pas i) (Z.lor 6 1)).
Proof.
  induction k as [|k' IH]; intros i Hik Hk; [lia|].
  cbn [kvm_stacks]. rewrite one_run_lookup.
  destruct (decide (i = k')) as [->|Hne].
  - rewrite decide_True; reflexivity.
  - rewrite decide_False; [| apply kstack_vpn_inj; lia].
    apply IH; lia.
Qed.

Lemma kvm_stacks_miss (pas : nat -> mword 44) (k : nat)
    (m : gmap (mword 27) (mword 64)) (vpn : mword 27) :
  (forall i : nat, (i < k)%nat -> vpn <> kstack_vpn i) ->
  kvm_stacks pas k m !! vpn = m !! vpn.
Proof.
  induction k as [|k' IH]; intros Hne.
  - reflexivity.
  - cbn [kvm_stacks]. rewrite one_run_lookup.
    rewrite decide_False; [| apply Hne; lia].
    apply IH. intros i Hi. apply Hne. lia.
Qed.

(* pas-extension congruence: [kvm_stacks] over the first [k] stacks depends
   only on [pas]'s values below [k], so a pas that agrees with [pas'] there
   builds the same map.  proc_mapstacks' loop uses this to swap the running
   [pas] accumulator for the final one. *)
Lemma kvm_stacks_ext (pas pas' : nat -> mword 44) (k : nat)
    (m : gmap (mword 27) (mword 64)) :
  (forall j : nat, (j < k)%nat -> pas j = pas' j) ->
  kvm_stacks pas k m = kvm_stacks pas' k m.
Proof.
  induction k as [|k' IH]; intros Hag.
  - reflexivity.
  - cbn [kvm_stacks]. rewrite (IH ltac:(intros j Hj; apply Hag; lia)).
    rewrite (Hag k' ltac:(lia)). reflexivity.
Qed.

Lemma kstack_index_spec (vpn : mword 27) (i : nat) :
  kstack_index vpn = Some i <-> ((i < 64)%nat /\ vpn = kstack_vpn i).
Proof.
  unfold kstack_index.
  set (v := bv_unsigned vpn). set (d := 0x3FFFFFF - v).
  split.
  - intro H.
    destruct ((1 <=? d) && (d <=? 128) && (d `mod` 2 =? 0)) eqn:Hc; [| discriminate].
    injection H as <-.
    apply andb_prop in Hc. destruct Hc as [Hc12 Hmod].
    apply andb_prop in Hc12. destruct Hc12 as [Hd1 Hd128].
    apply Z.leb_le in Hd1. apply Z.leb_le in Hd128. apply Z.eqb_eq in Hmod.
    pose proof (Z.div_mod d 2 ltac:(lia)) as Hdm. rewrite Hmod in Hdm.
    assert (Hdge : d / 2 - 1 >= 0) by lia.
    split.
    + apply Nat2Z.inj_lt. rewrite Z2Nat.id; lia.
    + apply bv_eq. unfold kstack_vpn.
      rewrite mword27_unsigned;
        [| rewrite Z2Nat.id by lia; pose proof (vpn27_bound vpn); subst v d; lia].
      rewrite Z2Nat.id by lia.
      subst v d. pose proof (vpn27_bound vpn). lia.
  - intros [Hi ->].
    assert (Hvu : v = 0x3FFFFFF - 2 * (Z.of_nat i + 1)) by (subst v; apply kstack_vpn_uns; exact Hi).
    assert (Hd2 : d = 2 * (Z.of_nat i + 1)) by (subst d; lia).
    assert (Hb1 : (1 <=? d) = true) by (apply Z.leb_le; lia).
    assert (Hb2 : (d <=? 128) = true) by (apply Z.leb_le; lia).
    assert (Hb3 : (d `mod` 2 =? 0) = true)
      by (apply Z.eqb_eq; rewrite Hd2, Z.mul_comm; apply Z_mod_mult).
    rewrite Hb1, Hb2, Hb3. cbn [andb].
    f_equal.
    assert (Hidx : d / 2 - 1 = Z.of_nat i)
      by (rewrite Hd2, Z.mul_comm, Z.div_mul by lia; lia).
    rewrite Hidx. apply Nat2Z.id.
Qed.

(* THE map characterization: identity regions ride kmap_class, plus the
   trampoline and the kstacks.  The word is always the A/D-CLEAR
   [perm|V] form. *)
(* ---- region base unsigned values / bounds (never normalize the maps) ---- *)
Lemma uart_vpn_uns   : bv_unsigned uart_vpn   = 0x10000.
Proof. unfold uart_vpn.   apply mword27_unsigned. lia. Qed.
Lemma virtio_vpn_uns : bv_unsigned virtio_vpn = 0x10001.
Proof. unfold virtio_vpn. apply mword27_unsigned. lia. Qed.
Lemma plic_vpn_uns   : bv_unsigned plic_vpn   = 0xC000.
Proof. unfold plic_vpn.   apply mword27_unsigned. lia. Qed.
Lemma text_vpn_uns   : bv_unsigned text_vpn0  = 0x80000.
Proof. unfold text_vpn0.  apply mword27_unsigned. lia. Qed.
Lemma data_vpn_uns   : bv_unsigned data_vpn0  = 0x80007.
Proof. unfold data_vpn0.  apply mword27_unsigned. lia. Qed.
Lemma tramp_vpn_uns  : bv_unsigned tramp_vpn  = 0x3FFFFFF.
Proof. unfold tramp_vpn.   apply mword27_unsigned. lia. Qed.

Local Lemma data_end : bv_unsigned data_vpn0 + Z.of_nat data_npages = 0x88000.
Proof. rewrite data_vpn_uns. unfold data_npages. vm_compute. reflexivity. Qed.
Local Lemma text_end : bv_unsigned text_vpn0 + Z.of_nat text_npages = 0x80007.
Proof. rewrite text_vpn_uns. unfold text_npages. vm_compute. reflexivity. Qed.
Local Lemma plic_end : bv_unsigned plic_vpn + Z.of_nat plic_npages = 0x10000.
Proof. rewrite plic_vpn_uns. unfold plic_npages. vm_compute. reflexivity. Qed.

Local Lemma data_ok : bv_unsigned data_vpn0 + Z.of_nat data_npages <= 134217728.
Proof. rewrite data_end. lia. Qed.
Local Lemma text_ok : bv_unsigned text_vpn0 + Z.of_nat text_npages <= 134217728.
Proof. rewrite text_end. lia. Qed.
Local Lemma plic_ok : bv_unsigned plic_vpn + Z.of_nat plic_npages <= 134217728.
Proof. rewrite plic_end. lia. Qed.

Local Lemma kmap_class_tramp_None : kmap_class tramp_vpn = None.
Proof. unfold kmap_class. rewrite tramp_vpn_uns. reflexivity. Qed.

(* boolean-decision tactics (avoid flat destruct blow-up) *)
Ltac lebT := apply (proj2 (Z.leb_le _ _)); lia.
Ltac lebF := apply (proj2 (Z.leb_gt _ _)); lia.
Ltac ltbT := apply (proj2 (Z.ltb_lt _ _)); lia.
Ltac ltbF := apply (proj2 (Z.ltb_ge _ _)); lia.

(* kmap_class range inversions *)
Local Lemma kmap_class_rx_range (vpn : mword 27) :
  kmap_class vpn = Some KP_rx -> 0x80000 <= bv_unsigned vpn < 0x80007.
Proof.
  unfold kmap_class.
  destruct (0x80000 <=? bv_unsigned vpn) eqn:E1;
  destruct (bv_unsigned vpn <? 0x80007) eqn:E2; cbn [andb]; intro H;
    try (exfalso; destruct (orb _ _) in H; discriminate).
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

Local Lemma kmap_class_rw_range (vpn : mword 27) :
  kmap_class vpn = Some KP_rw ->
  (0x80007 <= bv_unsigned vpn < 0x88000) \/ (0xC000 <= bv_unsigned vpn < 0x10002).
Proof.
  unfold kmap_class.
  destruct (0x80000 <=? bv_unsigned vpn) eqn:E1;
  destruct (bv_unsigned vpn <? 0x80007) eqn:E2; cbn [andb]; intro H;
    try discriminate;
  (destruct (0x80007 <=? bv_unsigned vpn) eqn:E3;
   destruct (bv_unsigned vpn <? 0x88000) eqn:E4;
   destruct (0xC000 <=? bv_unsigned vpn) eqn:E5;
   destruct (bv_unsigned vpn <? 0x10002) eqn:E6; cbn [andb orb] in H;
   try discriminate;
   repeat match goal with
     | E : (_ <=? _) = true |- _ => apply Z.leb_le in E
     | E : (_ <? _) = true |- _ => apply Z.ltb_lt in E
     end; first [ left; lia | right; lia ]).
Qed.

Local Lemma kmap_class_none_range (vpn : mword 27) :
  kmap_class vpn = None ->
  ~ (0x80000 <= bv_unsigned vpn < 0x80007) /\
  ~ (0x80007 <= bv_unsigned vpn < 0x88000) /\
  ~ (0xC000 <= bv_unsigned vpn < 0x10002).
Proof.
  unfold kmap_class.
  destruct (0x80000 <=? bv_unsigned vpn) eqn:E1;
  destruct (bv_unsigned vpn <? 0x80007) eqn:E2; cbn [andb]; intro H;
    try discriminate;
  (destruct (0x80007 <=? bv_unsigned vpn) eqn:E3;
   destruct (bv_unsigned vpn <? 0x88000) eqn:E4;
   destruct (0xC000 <=? bv_unsigned vpn) eqn:E5;
   destruct (bv_unsigned vpn <? 0x10002) eqn:E6; cbn [andb orb] in H;
   try discriminate;
   repeat match goal with
     | E : (_ <=? _) = true  |- _ => apply Z.leb_le in E
     | E : (_ <=? _) = false |- _ => apply Z.leb_gt in E
     | E : (_ <? _) = true   |- _ => apply Z.ltb_lt in E
     | E : (_ <? _) = false  |- _ => apply Z.ltb_ge in E
     end; repeat split; lia).
Qed.

Local Lemma virtio_end : bv_unsigned virtio_vpn + Z.of_nat 1 = 0x10002.
Proof. rewrite virtio_vpn_uns. reflexivity. Qed.
Local Lemma uart_end : bv_unsigned uart_vpn + Z.of_nat 1 = 0x10001.
Proof. rewrite uart_vpn_uns. reflexivity. Qed.

(* the five identity runs, peeled ONE layer at a time with the accumulator
   [kvm_m{k-1}] kept FOLDED -- crucial for speed: unfolding all five runs at
   once builds a giant nested [pt_insert_run] term (with the 16384/32761 page
   counts) that makes every rewrite's traversal ~seconds.  Each peel's own
   [id_run_lookup] rewrite is then instant (the term stays small). *)
Lemma kvm_m5_peel (vpn : mword 27) :
  kvm_m5 !! vpn = if (0x80007 <=? bv_unsigned vpn) && (bv_unsigned vpn <? 0x88000)
    then Some (mk_pte (kpt_leaf_ppn vpn) (Z.lor 6 1)) else kvm_m4 !! vpn.
Proof.
  unfold kvm_m5, data_ppn0.
  rewrite (id_run_lookup kvm_m4 data_vpn0 6 data_npages vpn data_ok), data_end, data_vpn_uns.
  reflexivity.
Qed.
Lemma kvm_m4_peel (vpn : mword 27) :
  kvm_m4 !! vpn = if (0x80000 <=? bv_unsigned vpn) && (bv_unsigned vpn <? 0x80007)
    then Some (mk_pte (kpt_leaf_ppn vpn) (Z.lor 10 1)) else kvm_m3 !! vpn.
Proof.
  unfold kvm_m4, text_ppn0.
  rewrite (id_run_lookup kvm_m3 text_vpn0 10 text_npages vpn text_ok), text_end, text_vpn_uns.
  reflexivity.
Qed.
Lemma kvm_m3_peel (vpn : mword 27) :
  kvm_m3 !! vpn = if (0xC000 <=? bv_unsigned vpn) && (bv_unsigned vpn <? 0x10000)
    then Some (mk_pte (kpt_leaf_ppn vpn) (Z.lor 6 1)) else kvm_m2 !! vpn.
Proof.
  unfold kvm_m3, plic_ppn.
  rewrite (id_run_lookup kvm_m2 plic_vpn 6 plic_npages vpn plic_ok), plic_end, plic_vpn_uns.
  reflexivity.
Qed.
Lemma kvm_m2_peel (vpn : mword 27) :
  kvm_m2 !! vpn = if (0x10001 <=? bv_unsigned vpn) && (bv_unsigned vpn <? 0x10002)
    then Some (mk_pte (kpt_leaf_ppn vpn) (Z.lor 6 1)) else kvm_m1 !! vpn.
Proof.
  unfold kvm_m2, virtio_ppn.
  rewrite (id_run_lookup kvm_m1 virtio_vpn 6 1 vpn ltac:(rewrite virtio_vpn_uns; lia)),
    virtio_end, virtio_vpn_uns.
  reflexivity.
Qed.
Lemma kvm_m1_peel (vpn : mword 27) :
  kvm_m1 !! vpn = if (0x10000 <=? bv_unsigned vpn) && (bv_unsigned vpn <? 0x10001)
    then Some (mk_pte (kpt_leaf_ppn vpn) (Z.lor 6 1)) else None.
Proof.
  unfold kvm_m1, uart_ppn.
  rewrite (id_run_lookup ∅ uart_vpn 6 1 vpn ltac:(rewrite uart_vpn_uns; lia)),
    uart_end, uart_vpn_uns, lookup_empty.
  reflexivity.
Qed.

Lemma kvm_m5_lookup (vpn : mword 27) :
  kvm_m5 !! vpn = match kmap_class vpn with
    | Some pc => Some (mk_pte (kpt_leaf_ppn vpn) (Z.lor (kperm_vperm pc) 1))
    | None => None end.
Proof.
  pose proof (vpn27_bound vpn) as Hvb.
  rewrite kvm_m5_peel, kvm_m4_peel, kvm_m3_peel, kvm_m2_peel, kvm_m1_peel.
  set (z := bv_unsigned vpn) in *.
  destruct (kmap_class vpn) as [[|]|] eqn:Hc.
  - (* KP_rx : z ∈ [0x80000, 0x80007) *)
    pose proof (kmap_class_rx_range vpn Hc) as Hr. fold z in Hr.
    assert ((0x80007 <=? z) = false) as -> by lebF.
    assert ((0x80000 <=? z) = true) as -> by lebT.
    assert ((z <? 0x80007) = true) as -> by ltbT.
    reflexivity.
  - (* KP_rw : z in the data range or the (lower) device range, both -> R|W *)
    pose proof (kmap_class_rw_range vpn Hc) as Hr. fold z in Hr.
    destruct Hr as [Hd | Hv].
    + (* data: z ∈ [0x80007, 0x88000) *)
      assert ((0x80007 <=? z) = true) as -> by lebT.
      assert ((z <? 0x88000) = true) as -> by ltbT.
      reflexivity.
    + (* dev: z ∈ [0xC000, 0x10002), strictly below the text/data ranges *)
      assert (Cd : (0x80007 <=? z) && (z <? 0x88000) = false)
        by (apply andb_false_iff; left; lebF).
      assert (Ct : (0x80000 <=? z) && (z <? 0x80007) = false)
        by (apply andb_false_iff; left; lebF).
      rewrite Cd, Ct.
      destruct (decide (z < 0x10000)) as [Hlo | Hhi].
      * assert ((0xC000 <=? z) = true) as -> by lebT.
        assert ((z <? 0x10000) = true) as -> by ltbT.
        reflexivity.
      * assert (Cp : (0xC000 <=? z) && (z <? 0x10000) = false)
          by (apply andb_false_iff; right; ltbF).
        rewrite Cp.
        destruct (decide (z = 0x10001)) as [Hveq | Hvne].
        -- assert ((0x10001 <=? z) = true) as -> by lebT.
           assert ((z <? 0x10002) = true) as -> by ltbT.
           reflexivity.
        -- assert (Cvi : (0x10001 <=? z) && (z <? 0x10002) = false)
             by (apply andb_false_iff; left; lebF).
           rewrite Cvi.
           assert ((0x10000 <=? z) = true) as -> by lebT.
           assert ((z <? 0x10001) = true) as -> by ltbT.
           reflexivity.
  - (* None : each run's whole condition is false *)
    pose proof (kmap_class_none_range vpn Hc) as (Hnt & Hnd & Hnv). fold z in Hnt, Hnd, Hnv.
    assert (Cd : (0x80007 <=? z) && (z <? 0x88000) = false)
      by (apply andb_false_iff; destruct (Z_lt_le_dec z 0x80007); [left; lebF | right; ltbF]).
    assert (Ct : (0x80000 <=? z) && (z <? 0x80007) = false)
      by (apply andb_false_iff; destruct (Z_lt_le_dec z 0x80000); [left; lebF | right; ltbF]).
    assert (Cp : (0xC000 <=? z) && (z <? 0x10000) = false)
      by (apply andb_false_iff; destruct (Z_lt_le_dec z 0xC000); [left; lebF | right; ltbF]).
    assert (Cvi : (0x10001 <=? z) && (z <? 0x10002) = false)
      by (apply andb_false_iff; destruct (Z_lt_le_dec z 0x10001); [left; lebF | right; ltbF]).
    assert (Cu : (0x10000 <=? z) && (z <? 0x10001) = false)
      by (apply andb_false_iff; destruct (Z_lt_le_dec z 0x10000); [left; lebF | right; ltbF]).
    rewrite Cd, Ct, Cp, Cvi, Cu. reflexivity.
Qed.

Lemma kvm_map_lookup (vpn : mword 27) :
  kvm_map !! vpn = match kmap_class vpn with
    | Some pc => Some (mk_pte (kpt_leaf_ppn vpn) (Z.lor (kperm_vperm pc) 1))
    | None => if decide (vpn = tramp_vpn)
              then Some (mk_pte tramp_ppn (Z.lor 10 1)) else None
    end.
Proof.
  unfold kvm_map. rewrite one_run_lookup.
  destruct (decide (vpn = tramp_vpn)) as [->|Hnt].
  - rewrite kmap_class_tramp_None. reflexivity.
  - rewrite kvm_m5_lookup. destruct (kmap_class vpn); reflexivity.
Qed.

(* kstack vpns are disjoint from the static class ranges and from tramp *)
Lemma kstack_not_class (vpn : mword 27) (i : nat) :
  (i < 64)%nat -> vpn = kstack_vpn i -> kmap_class vpn = None.
Proof.
  intros Hi ->. unfold kmap_class. rewrite (kstack_vpn_uns i Hi).
  set (z := 0x3FFFFFF - 2 * (Z.of_nat i + 1)).
  assert (Hr : 0x3FFFF7F <= z <= 0x3FFFFFD) by (subst z; lia).
  assert ((z <? 0x80007) = false) as -> by ltbF.
  assert ((z <? 0x88000) = false) as -> by ltbF.
  assert ((z <? 0x10002) = false) as -> by ltbF.
  rewrite !andb_false_r. reflexivity.
Qed.

Lemma kstack_not_tramp (i : nat) :
  (i < 64)%nat -> kstack_vpn i <> tramp_vpn.
Proof.
  intros Hi Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite (kstack_vpn_uns i Hi), tramp_vpn_uns in Heq. lia.
Qed.

Lemma kvm_map_full_lookup (pas : nat -> mword 44) (vpn : mword 27) :
  kvm_map_full pas !! vpn =
    match kmap_class vpn with
    | Some pc => Some (mk_pte (kpt_leaf_ppn vpn) (Z.lor (kperm_vperm pc) 1))
    | None =>
        if decide (vpn = tramp_vpn)
        then Some (mk_pte tramp_ppn (Z.lor 10 1))
        else match kstack_index vpn with
             | Some i => Some (mk_pte (pas i) (Z.lor 6 1))
             | None => None
             end
    end.
Proof.
  unfold kvm_map_full.
  destruct (kstack_index vpn) as [i|] eqn:Hks.
  - (* a kstack vpn: hits the stacks layer *)
    apply kstack_index_spec in Hks. destruct Hks as [Hi ->].
    rewrite (kvm_stacks_hit pas 64 kvm_map i Hi ltac:(lia)).
    rewrite (kstack_not_class _ i Hi eq_refl).
    rewrite decide_False; [reflexivity | apply kstack_not_tramp; exact Hi].
  - (* not a kstack vpn: falls through to kvm_map *)
    rewrite kvm_stacks_miss.
    2:{ intros i Hi Heq. rewrite Heq in Hks.
        rewrite (proj2 (kstack_index_spec _ i) (conj Hi eq_refl)) in Hks. discriminate. }
    rewrite kvm_map_lookup.
    destruct (kmap_class vpn) as [pc|]; [reflexivity |].
    destruct (decide (vpn = tramp_vpn)); reflexivity.
Qed.

(* ... and the target auth map's (mirror shape, entry form) *)
(* the kstack layer of the auth map (plain inserts, mirror of kvm_stacks) *)
Local Lemma kvm_M_stacks_hit (pas : nat -> mword 44) (k : nat)
    (M : gmap (mword 27) (mword 44 * kperm)) :
  forall i : nat, (i < k)%nat -> (k <= 64)%nat ->
  kvm_M_stacks pas k M !! kstack_vpn i = Some (pas i, KP_rw).
Proof.
  induction k as [|k' IH]; intros i Hik Hk; [lia|].
  cbn [kvm_M_stacks].
  destruct (decide (i = k')) as [->|Hne].
  - rewrite lookup_insert. reflexivity.
  - rewrite lookup_insert_ne; [apply IH; lia | apply kstack_vpn_inj; lia].
Qed.

Local Lemma kvm_M_stacks_miss (pas : nat -> mword 44) (k : nat)
    (M : gmap (mword 27) (mword 44 * kperm)) (vpn : mword 27) :
  (forall i : nat, (i < k)%nat -> vpn <> kstack_vpn i) ->
  kvm_M_stacks pas k M !! vpn = M !! vpn.
Proof.
  induction k as [|k' IH]; intros Hne.
  - reflexivity.
  - cbn [kvm_M_stacks]. rewrite lookup_insert_ne; [apply IH; intros i Hi; apply Hne; lia
                                                   | apply not_eq_sym; apply Hne; lia].
Qed.

Lemma kvm_M_lookup (pas : nat -> mword 44) (vpn : mword 27) :
  kvm_M pas !! vpn =
    match kmap_class vpn with
    | Some pc => Some (kpt_leaf_ppn vpn, pc)
    | None =>
        if decide (vpn = tramp_vpn)
        then Some (tramp_ppn, KP_rx)
        else match kstack_index vpn with
             | Some i => Some (pas i, KP_rw)
             | None => None
             end
    end.
Proof.
  unfold kvm_M.
  destruct (kstack_index vpn) as [i|] eqn:Hks.
  - apply kstack_index_spec in Hks. destruct Hks as [Hi Hvpn].
    rewrite (kstack_not_class vpn i Hi Hvpn).
    rewrite Hvpn, (kvm_M_stacks_hit pas 64 _ i Hi ltac:(lia)).
    rewrite decide_False; [reflexivity | apply kstack_not_tramp; exact Hi].
  - rewrite kvm_M_stacks_miss.
    2:{ intros i Hi Heq. rewrite Heq in Hks.
        rewrite (proj2 (kstack_index_spec _ i) (conj Hi eq_refl)) in Hks. discriminate. }
    destruct (decide (vpn = tramp_vpn)) as [->|Hnt].
    + rewrite lookup_insert, kmap_class_tramp_None.
      destruct (decide (tramp_vpn = tramp_vpn)) as [_|Hne]; [reflexivity | congruence].
    + rewrite lookup_insert_ne; [| exact (not_eq_sym Hnt)].
      rewrite kmap_M0_lookup.
      destruct (kmap_class vpn) as [pc|]; reflexivity.
Qed.

(* the A/D bridge: the map's word IS the zero-A/D variant of the
   class-keyed leaf (per class), and of the trampoline leaf *)
Lemma kvm_word_variant (p : mword 44) (pc : kperm) :
  mk_pte p (Z.lor (kperm_vperm pc) 1)
  = pte_set_ad (mk_pte p (kperm_flags pc)) ('b"0") ('b"0").
Proof.
  rewrite kperm_set_ad_leaf.
  replace (Z.lor (kperm_vperm pc) 1) with (kperm_flags_ad pc (ad_of ('b"0") ('b"0")))
    by (destruct pc; vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma kvm_word_tramp :
  mk_pte tramp_ppn (Z.lor 10 1) = pte_set_ad pte_tramp ('b"0") ('b"0").
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* §5 THE BRIDGE (the deliverable): a table representing the full kvm     *)
(*    map satisfies the kpt mapping invariants at the target auth map,   *)
(*    and that map is wf (so the stage-6 switch can install it).          *)
(* ===================================================================== *)

(* the full-map word at an M-entry IS the zero-A/D variant of the class leaf *)
Local Lemma kvm_full_of_M (pas : nat -> mword 44) (vpn : mword 27) (e : mword 44 * kperm) :
  kvm_M pas !! vpn = Some e ->
  kvm_map_full pas !! vpn = Some (pte_set_ad (kpt_leaf_pte_of vpn e) ('b"0") ('b"0")).
Proof.
  rewrite kvm_M_lookup, kvm_map_full_lookup.
  destruct (kmap_class vpn) as [pc|] eqn:Hc.
  - intro H. injection H as <-. unfold kpt_leaf_pte_of. cbn [fst snd].
    f_equal. apply kvm_word_variant.
  - destruct (decide (vpn = tramp_vpn)) as [->|Hnt].
    + (* the trampoline is now an ordinary M entry [(tramp_ppn, KP_rx)]:
         its full-map word [0x4B] IS the '0/'0 KP_rx variant *)
      intro H. injection H as <-. unfold kpt_leaf_pte_of. cbn [fst snd].
      rewrite kperm_rx_tramp_variant. rewrite kvm_word_tramp. reflexivity.
    + destruct (kstack_index vpn) as [i|] eqn:Hks; intro H; [| discriminate].
      injection H as <-.
      unfold kpt_leaf_pte_of. cbn [fst snd]. f_equal. exact (kvm_word_variant (pas i) KP_rw).
Qed.

Local Lemma kvm_full_none (pas : nat -> mword 44) (vpn : mword 27) :
  kvm_M pas !! vpn = None -> kvm_map_full pas !! vpn = None.
Proof.
  intros Hnone. rewrite kvm_map_full_lookup. rewrite kvm_M_lookup in Hnone.
  destruct (kmap_class vpn) as [pc|] eqn:Hc; [discriminate|].
  destruct (decide (vpn = tramp_vpn)) as [->|Hnt]; [discriminate|].
  destruct (kstack_index vpn) as [i|] eqn:Hks; [discriminate|].
  reflexivity.
Qed.

Lemma kvm_bridge (pas : nat -> mword 44) (t : ptree) (root : mword 44) :
  kvm_pas_ok pas ->
  pt_base t = root ->
  pt_rep0 t (kvm_map_full pas) ->
  kpt_tree_spec_gen root (kvm_M pas) t.
Proof.
  intros Hpas Hbase (Hmap & Hblk).
  split; [exact Hbase |].
  intros vpn.
  destruct (kvm_M pas !! vpn) as [e|] eqn:HM.
  - (* every M entry (text/data/dev/kstack AND the trampoline) maps as the
       '0/'0 A/D variant of its class leaf *)
    destruct (Hmap vpn _ (kvm_full_of_M pas vpn e HM)) as (p2 & p1 & Hm).
    exists p2, p1, ('b"0"), ('b"0"). exact Hm.
  - (* off M the two masters agree on None *)
    apply ptree_blocks0_blocks. apply Hblk. apply kvm_full_none. exact HM.
Qed.
