(* ====================================================================== *)
(* VirtioProto.v -- the Iris-level driver protocol over the DMA lease.     *)
(*                                                                         *)
(* This replaces the bare [virtio_lease] in [dev_inv_body]: the same       *)
(* [dma_own] byte lease, but with the queue obligation held in the KEYED   *)
(* form of VirtioQueue.v, plus the per-request resources the driver        *)
(* deposits and withdraws:                                                 *)
(*                                                                         *)
(*  - a pending/done slot carries the caller's DISK POINTS-TO fragments    *)
(*    for the sector range its request touches (DiskPtsto.v), so the       *)
(*    autonomous device step can perform the disk ghost update (a write    *)
(*    request) or read off the promised contents (a read request);         *)
(*  - the ghost_map RECEIPT [disk_receipt] is minted at publish and        *)
(*    presented at reclaim; its value records the slot AND its pin map,    *)
(*    so the reclaimer gets back exactly the bytes it handed over;         *)
(*  - [disk_pub] (half of a ghost_var over the published count) is THE     *)
(*    publisher credential: it rides in the vdisk_lock's resource, forces  *)
(*    the live branch, and pins [np] -- only a lock holder can publish;    *)
(*  - [mono_nat] over the completed count lets an interrupt handler carry  *)
(*    its used-index observation to its later per-slot reads.              *)
(*                                                                         *)
(* The four PROTOCOL OPERATIONS are stated as ACCESSORS: they expose the   *)
(* target bytes as physical points-tos for exactly one machine access,     *)
(* and the close-wand performs the ghost transition.  The device-thread    *)
(* rules ([virtio_proto_not_stalled]/[virtio_proto_step]) keep the exact   *)
(* signatures of the old lease rules, so [wp_dev_loop] ports mechanically. *)
(*                                                                         *)
(* Design rationale: claude-notes/design/virtio-driver.md.                 *)
(* ====================================================================== *)
(* IMPORTANT: mirror RiscvPtsto's imports -- do NOT add SailStdpp.Base /
   SailStdpp.Values here (Countable-instance mismatch on gmap Arch.pa;
   see WpVirtio.v's header). *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var mono_nat invariants.
From iris.program_logic Require Import weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import VirtioModel.
Require Import WpVirtio.
Require Import VirtioQueue.
Require Import DiskPtsto.
Require Import PermInv.

Local Open Scope Z_scope.

(* ====================================================================== *)
(* PURE LAYER: finite byte maps built by [foldr]-insert, their lookups,    *)
(* the framing facts ("this write missed that address"), and the used-page *)
(* geometry.  All of it is over abstract sets/maps, so no [set_solver] ever *)
(* has to look at [pa_range _ 4096].                                       *)
(* ====================================================================== *)

(* THE canonical finite byte map: [n] bytes at [a], contents given by [f].
   [write_bytes] over the empty map is literally this. *)
Definition range_map (a : Arch.pa) (n : nat) (f : nat -> bv 8)
  : gmap Arch.pa (bv 8) :=
  foldr (fun j acc => <[ pa_add a j := f j ]> acc) ∅ (seq 0 n).

Lemma write_bytes_range_map {w : N} (a : Arch.pa) (n : N) (v : bv w) :
  write_bytes ∅ a n v = range_map a (N.to_nat n) (nth_byte v).
Proof. reflexivity. Qed.

(* -- the two generic [foldr]-insert lookup facts -- *)

Lemma foldr_ins_lookup_ne {A : Type} (f : A -> Arch.pa) (g : A -> bv 8)
    (l : list A) (mm : gmap Arch.pa (bv 8)) (x : Arch.pa) :
  (forall y, y ∈ l -> f y ≠ x) ->
  foldr (fun y acc => <[ f y := g y ]> acc) mm l !! x = mm !! x.
Proof.
  induction l as [|y l IH]; intro Hne; [reflexivity|].
  cbn [foldr]. rewrite lookup_insert_ne.
  - apply IH. intros z Hz. apply Hne, elem_of_list_further, Hz.
  - apply Hne, elem_of_list_here.
Qed.

Lemma foldr_ins_lookup_hit {A : Type} (f : A -> Arch.pa) (g : A -> bv 8)
    (l : list A) (mm : gmap Arch.pa (bv 8)) (y : A) :
  y ∈ l -> (forall z, z ∈ l -> f z = f y -> g z = g y) ->
  foldr (fun z acc => <[ f z := g z ]> acc) mm l !! f y = Some (g y).
Proof.
  induction l as [|z l IH]; intros Hin Hfun.
  { exfalso. exact (not_elem_of_nil y Hin). }
  cbn [foldr]. destruct (decide (f z = f y)) as [Heq|Hne].
  - rewrite Heq lookup_insert. f_equal.
    apply Hfun; [ apply elem_of_list_here | exact Heq ].
  - rewrite lookup_insert_ne; [| exact Hne ].
    apply IH.
    + apply elem_of_cons in Hin as [->|Hin];
        [ exfalso; exact (Hne eq_refl) | exact Hin ].
    + intros wz Hw. apply Hfun, elem_of_list_further, Hw.
Qed.

(* -- [write_bytes] / [write_byte_list]: what they hit and what they miss -- *)

Lemma write_bytes_lookup_out {w : N} (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (n : N) (v : bv w) (x : Arch.pa) :
  x ∉ pa_range pa (N.to_nat n) -> write_bytes mm pa n v !! x = mm !! x.
Proof.
  intro Hx. unfold write_bytes.
  apply (foldr_ins_lookup_ne (pa_add pa) (nth_byte v)).
  intros j Hj Heq. apply elem_of_seq in Hj.
  assert (H2 : pa_add pa j ∈ pa_range pa (N.to_nat n))
    by (apply pa_range_intro; lia).
  rewrite Heq in H2. exact (Hx H2).
Qed.

Lemma imap_pairs_elem (bs : list (bv 8)) (z : nat * bv 8) :
  z ∈ imap (fun (j : nat) (b : bv 8) => (j, b)) bs -> bs !! (fst z) = Some (snd z).
Proof.
  intro Hz. apply elem_of_list_lookup in Hz as (i & Hi).
  rewrite list_lookup_imap in Hi.
  destruct (bs !! i) as [b|] eqn:Hb; [| discriminate ].
  cbn in Hi. injection Hi as <-. cbn [fst snd]. exact Hb.
Qed.

Lemma write_byte_list_lookup_out (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (bs : list (bv 8)) (x : Arch.pa) :
  x ∉ pa_range pa (length bs) -> write_byte_list mm pa bs !! x = mm !! x.
Proof.
  intro Hx. unfold write_byte_list.
  apply (foldr_ins_lookup_ne (fun jb => pa_add pa (fst jb)) snd).
  intros z Hz Heq. apply imap_pairs_elem in Hz.
  assert (Hlt : (fst z < length bs)%nat) by (apply lookup_lt_Some in Hz; exact Hz).
  assert (H2 : pa_add pa (fst z) ∈ pa_range pa (length bs))
    by (apply pa_range_intro; exact Hlt).
  rewrite Heq in H2. exact (Hx H2).
Qed.

Lemma write_byte_list_lookup (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (bs : list (bv 8)) (j : nat) (b : bv 8) :
  Z.of_nat (length bs) < 18446744073709551616 -> bs !! j = Some b ->
  write_byte_list mm pa bs !! pa_add pa j = Some b.
Proof.
  intros Hlen Hj. unfold write_byte_list.
  assert (Hjlt : (j < length bs)%nat) by (apply lookup_lt_Some in Hj; exact Hj).
  assert (Hin : (j, b) ∈ imap (fun (i : nat) (c : bv 8) => (i, c)) bs).
  { apply elem_of_list_lookup. exists j. rewrite list_lookup_imap Hj. reflexivity. }
  assert (Hfun : forall z, z ∈ imap (fun (i : nat) (c : bv 8) => (i, c)) bs ->
            pa_add pa (fst z) = pa_add pa (fst (j, b)) -> snd z = snd (j, b)).
  { intros z Hz Heq. cbn [fst snd] in Heq |- *.
    apply imap_pairs_elem in Hz.
    assert (Hlt : (fst z < length bs)%nat) by (apply lookup_lt_Some in Hz; exact Hz).
    assert (Hfz : fst z = j) by (apply (pa_add_inj pa); [lia|lia|exact Heq]).
    rewrite Hfz in Hz. congruence. }
  exact (foldr_ins_lookup_hit (fun jb => pa_add pa (fst jb)) snd _ mm (j, b) Hin Hfun).
Qed.

(* -- [range_map] -- *)

Lemma range_map_dom (a : Arch.pa) (n : nat) (f : nat -> bv 8) :
  dom (range_map a n f) = pa_range a n.
Proof.
  unfold range_map, pa_range.
  rewrite (foldr_ins_dom (pa_add a) f (seq 0 n) ∅) dom_empty_L.
  apply gset_eq_of_elem. intro x. rewrite elem_of_union. split.
  - intros [H|H]; [ exact H | exfalso; exact (proj1 (elem_of_empty x) H) ].
  - intro H. left. exact H.
Qed.

Lemma range_map_lookup (a : Arch.pa) (n : nat) (f : nat -> bv 8) (j : nat) :
  Z.of_nat n < 18446744073709551616 -> (j < n)%nat ->
  range_map a n f !! pa_add a j = Some (f j).
Proof.
  intros Hn Hj. unfold range_map.
  apply (foldr_ins_lookup_hit (pa_add a) f (seq 0 n) ∅ j).
  - apply elem_of_seq. lia.
  - intros z Hz Heq. apply elem_of_seq in Hz.
    assert (Hzj : z = j) by (apply (pa_add_inj a); [lia|lia|exact Heq]).
    rewrite Hzj. reflexivity.
Qed.

Lemma range_map_lookup_out (a : Arch.pa) (n : nat) (f : nat -> bv 8) (x : Arch.pa) :
  x ∉ pa_range a n -> range_map a n f !! x = None.
Proof.
  intro Hx. unfold range_map.
  rewrite (foldr_ins_lookup_ne (pa_add a) f (seq 0 n) ∅ x).
  - apply lookup_empty.
  - intros j Hj Heq. apply elem_of_seq in Hj.
    assert (H2 : pa_add a j ∈ pa_range a n) by (apply pa_range_intro; lia).
    rewrite Heq in H2. exact (Hx H2).
Qed.

Lemma range_map_ext (a : Arch.pa) (n : nat) (f g : nat -> bv 8) :
  Z.of_nat n < 18446744073709551616 ->
  (forall j, (j < n)%nat -> f j = g j) -> range_map a n f = range_map a n g.
Proof.
  intros Hn Hfg. apply map_eq. intro x.
  destruct (decide (x ∈ pa_range a n)) as [Hin|Hout].
  - apply pa_range_elim in Hin as (j & Hj & ->).
    rewrite (range_map_lookup a n f j Hn Hj) (range_map_lookup a n g j Hn Hj).
    f_equal. exact (Hfg j Hj).
  - rewrite (range_map_lookup_out a n f x Hout)
            (range_map_lookup_out a n g x Hout). reflexivity.
Qed.

Lemma range_map_sub (a : Arch.pa) (n : nat) (f : nat -> bv 8)
    (mm : gmap Arch.pa (bv 8)) :
  Z.of_nat n < 18446744073709551616 ->
  (forall j, (j < n)%nat -> mm !! pa_add a j = Some (f j)) ->
  range_map a n f ⊆ mm.
Proof.
  intros Hn Hf. apply map_subseteq_spec. intros x b Hx.
  destruct (decide (x ∈ pa_range a n)) as [Hin|Hout].
  - apply pa_range_elim in Hin as (j & Hj & ->).
    rewrite (range_map_lookup a n f j Hn Hj) in Hx. injection Hx as <-.
    exact (Hf j Hj).
  - rewrite (range_map_lookup_out a n f x Hout) in Hx. discriminate.
Qed.

(* -- byte-LIST reads, pointwise -- *)

Lemma read_byte_list_spec (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : nat)
    (bs : list (bv 8)) :
  read_byte_list mm pa n = Some bs ->
  length bs = n /\
  forall (j : nat) (b : bv 8), bs !! j = Some b -> mm !! pa_add pa j = Some b.
Proof.
  unfold read_byte_list. intro Hm. apply mapM_Some_1 in Hm.
  pose proof (Forall2_length _ _ _ Hm) as Hlen. rewrite length_seq in Hlen.
  split; [lia|].
  intros j b Hj.
  assert (Hjlt : (j < n)%nat) by (apply lookup_lt_Some in Hj; lia).
  assert (Hseq : seq 0 n !! j = Some j) by (apply (lookup_seq_lt 0 n j Hjlt)).
  exact (Forall2_lookup_lr
           (fun (x : nat) (y : bv 8) => mm !! pa_add pa x = Some y)
           _ _ _ _ _ Hm Hseq Hj).
Qed.

Lemma read_byte_list_intro (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : nat)
    (bs : list (bv 8)) :
  length bs = n ->
  (forall (j : nat) (b : bv 8), bs !! j = Some b -> mm !! pa_add pa j = Some b) ->
  read_byte_list mm pa n = Some bs.
Proof.
  intros Hlen Hf. unfold read_byte_list. apply mapM_Some.
  apply Forall2_same_length_lookup_2; [ rewrite length_seq; lia | ].
  intros i j b Hi Hj.
  apply lookup_seq in Hi as [Hij _].
  assert (Hji : j = i) by lia. rewrite Hji. exact (Hf i b Hj).
Qed.

Lemma read_bytes_transfer (m1 m2 : gmap Arch.pa (bv 8)) (pa : Arch.pa) (n : N)
    (w : bv (8 * n)) :
  (forall j : nat, (N.of_nat j < n)%N -> m2 !! pa_add pa j = m1 !! pa_add pa j) ->
  read_bytes m1 pa n = Some w -> read_bytes m2 pa n = Some w.
Proof.
  intros Hf Hr. apply read_bytes_of_list. intros j Hj.
  rewrite (Hf j Hj). exact (read_bytes_spec m1 pa n w Hr j Hj).
Qed.

Lemma read_byte_list_transfer (m1 m2 : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (n : nat) (bs : list (bv 8)) :
  (forall j : nat, (j < n)%nat -> m2 !! pa_add pa j = m1 !! pa_add pa j) ->
  read_byte_list m1 pa n = Some bs -> read_byte_list m2 pa n = Some bs.
Proof.
  intros Hf Hr. destruct (read_byte_list_spec m1 pa n bs Hr) as [Hlen Hlk].
  apply read_byte_list_intro; [exact Hlen|].
  intros j b Hj.
  assert (Hjlt : (j < n)%nat) by (apply lookup_lt_Some in Hj; lia).
  rewrite (Hf j Hjlt). exact (Hlk j b Hj).
Qed.

Lemma replicate_fmap_seq {A : Type} (n : nat) (x : A) :
  replicate n x = (fun _ : nat => x) <$> seq 0 n.
Proof.
  apply list_eq. intro i. rewrite list_lookup_fmap.
  destruct (decide (i < n)%nat) as [Hi|Hi].
  - rewrite (lookup_seq_lt 0 n i Hi) (lookup_replicate_2 n x i Hi). reflexivity.
  - rewrite (lookup_seq_ge 0 n i); [| lia].
    cbn [fmap option_fmap option_map]. apply lookup_ge_None_2.
    rewrite length_replicate. lia.
Qed.

Lemma list_eq_total (bs : list (bv 8)) :
  bs = (fun j : nat => bs !!! j) <$> seq 0 (length bs).
Proof.
  apply list_eq. intro i. rewrite list_lookup_fmap.
  destruct (decide (i < length bs)%nat) as [Hi|Hi].
  - rewrite (lookup_seq_lt 0 (length bs) i Hi).
    cbn [fmap option_fmap option_map].
    destruct (lookup_lt_is_Some_2 bs i Hi) as [b Hb].
    rewrite Hb. f_equal. symmetry. apply list_lookup_total_correct. exact Hb.
  - rewrite (lookup_seq_ge 0 (length bs) i); [| lia].
    cbn [fmap option_fmap option_map]. apply lookup_ge_None_2. lia.
Qed.

(* -- small map lemmas -- *)

Lemma dom_union_sub {A : Type} (w m : gmap Arch.pa A) :
  dom w ⊆ dom m -> dom (w ∪ m) = dom m.
Proof. intro H. rewrite dom_union_L. apply subseteq_union_1_L. exact H. Qed.

Lemma map_sub_difference (m1 m2 mm : gmap Arch.pa (bv 8)) :
  m1 ⊆ m2 -> dom m1 ## dom mm -> m1 ⊆ m2 ∖ mm.
Proof.
  intros Hs Hd. apply map_subseteq_spec. intros x b Hx.
  rewrite lookup_difference.
  assert (Hmm : mm !! x = None).
  { apply not_elem_of_dom. intro Hin.
    exact (proj1 (elem_of_disjoint _ _) Hd x (elem_of_dom_2 _ _ _ Hx) Hin). }
  rewrite Hmm. exact (lookup_weaken _ _ _ _ Hx Hs).
Qed.

Lemma lookup_difference_out (m mm : gmap Arch.pa (bv 8)) (x : Arch.pa) :
  x ∉ dom mm -> (m ∖ mm) !! x = m !! x.
Proof.
  intro Hx. rewrite lookup_difference.
  rewrite (proj1 (not_elem_of_dom mm x) Hx). reflexivity.
Qed.

Lemma lookup_union_out {A : Type} (w m : gmap Arch.pa A) (x : Arch.pa) :
  x ∉ dom w -> (w ∪ m) !! x = m !! x.
Proof.
  intro Hx. apply lookup_union_r, (proj1 (not_elem_of_dom w x) Hx).
Qed.

(* -- used-page geometry -- *)

Lemma wrap16_mod8 (p : nat) : bv_unsigned (wrap16 p) `mod` 8 = Z.of_nat p `mod` 8.
Proof.
  unfold wrap16. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 16) with 65536. apply vq_mod_65536_8.
Qed.

Lemma z4096 : Z.of_nat 4096 = 4096.
Proof. vm_compute. reflexivity. Qed.

Lemma used_off_in_page (c : virtio_cfg) (z : Z) (j : nat) :
  0 <= z -> z + Z.of_nat j < 4096 ->
  pa_add (pa_off (vc_used c) z) j ∈ used_page_pas c.
Proof.
  intros Hz Hlt. unfold used_page_pas. apply pa_off_range; [exact Hz|].
  rewrite z4096. exact Hlt.
Qed.

Lemma used_idx_in_page (c : virtio_cfg) (j : nat) :
  (j < 2)%nat -> pa_add (used_idx_pa c) j ∈ used_page_pas c.
Proof.
  intro Hj. unfold used_idx_pa, vq_idx_off. apply used_off_in_page; lia.
Qed.

Lemma used_elem_in_page (c : virtio_cfg) (s : Z) (j : nat) :
  0 <= s < 8 -> (j < 8)%nat ->
  pa_add (pa_off (vc_used c)
            (vq_used_ring_off + vq_used_elem_size * s)) j ∈ used_page_pas c.
Proof.
  intros Hs Hj. unfold vq_used_ring_off, vq_used_elem_size.
  apply used_off_in_page; lia.
Qed.

Lemma used_off_ne (c : virtio_cfg) (z1 z2 : Z) (i j : nat) :
  0 <= z1 -> 0 <= z2 -> z1 + Z.of_nat i < 4096 -> z2 + Z.of_nat j < 4096 ->
  z1 + Z.of_nat i ≠ z2 + Z.of_nat j ->
  pa_add (pa_off (vc_used c) z1) i ≠ pa_add (pa_off (vc_used c) z2) j.
Proof.
  intros Hz1 Hz2 H1 H2 Hne Heq. rewrite !pa_off_add in Heq.
  assert (Hnn : (Z.to_nat z1 + i)%nat = (Z.to_nat z2 + j)%nat)
    by (apply (pa_add_inj (vc_used c)); [lia|lia|exact Heq]).
  lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* What the determined device step [vslot_writes] HITS and what it MISSES.  *)
(* Everything is keyed on the used page's byte offsets: the completion       *)
(* record for ring slot [s] occupies [used+4+8s .. +8), the index field      *)
(* [used+2 .. +2), and the slot's own writable bytes are outside the page.   *)
(* ---------------------------------------------------------------------- *)

Definition used_elem_at (c : virtio_cfg) (ui : bv 16) : Arch.pa :=
  pa_off (vc_used c) (vq_used_ring_off + vq_used_elem_size * (bv_unsigned ui `mod` 8)).

Lemma used_elem_at_wrap (c : virtio_cfg) (p : nat) :
  used_elem_at c (wrap16 p) = used_elem_pa c p.
Proof. unfold used_elem_at, used_elem_pa. rewrite wrap16_mod8. reflexivity. Qed.

Lemma ui_mod8_bound (ui : bv 16) : 0 <= bv_unsigned ui `mod` 8 < 8.
Proof. apply Z.mod_pos_bound. lia. Qed.

Lemma pa_add_off4_ne (a : Arch.pa) (i k : nat) :
  (i < 4)%nat -> (k < 4)%nat -> pa_add a i ≠ pa_add (pa_off a 4) k.
Proof.
  intros Hi Hk Heq. rewrite pa_off_add in Heq.
  assert (Hn : i = (Z.to_nat 4 + k)%nat)
    by (apply (pa_add_inj a); [lia|lia|exact Heq]).
  change (Z.to_nat 4) with 4%nat in Hn. lia.
Qed.

Lemma virtio_used_writes_unfold (c : virtio_cfg) (ui : bv 16) (r : vio_req) :
  vc_qnum c = Z_to_bv 32 8 ->
  virtio_used_writes c ui r
  = write_bytes
      (write_bytes
         (write_bytes ∅ (used_elem_at c ui) 4
            (Z_to_bv 32 (bv_unsigned (vr_head r))))
         (pa_off (used_elem_at c ui) 4) 4 (vr_len r))
      (used_idx_pa c) 2 (bv_add ui (Z_to_bv 16 1)).
Proof.
  intro Hq. unfold virtio_used_writes, used_elem_at, used_idx_pa. cbv zeta.
  rewrite Hq.
  assert (Hq8 : bv_unsigned (Z_to_bv 32 8) = 8) by (vm_compute; reflexivity).
  rewrite Hq8. reflexivity.
Qed.

Lemma used_writes_out (c : virtio_cfg) (ui : bv 16) (r : vio_req) (x : Arch.pa) :
  vc_qnum c = Z_to_bv 32 8 ->
  x ∉ pa_range (used_elem_at c ui) 8 ->
  x ∉ pa_range (used_idx_pa c) 2 ->
  virtio_used_writes c ui r !! x = None.
Proof.
  intros Hq H8 H2. rewrite (virtio_used_writes_unfold c ui r Hq).
  rewrite (write_bytes_lookup_out _ (used_idx_pa c) 2
             (bv_add ui (Z_to_bv 16 1)) x H2).
  rewrite (write_bytes_lookup_out _ (pa_off (used_elem_at c ui) 4) 4
             (vr_len r) x).
  2:{ intro Hc. apply pa_range_elim in Hc as (k & Hk & ->). apply H8.
      rewrite pa_off_add. apply pa_range_intro.
      change (N.to_nat 4) with 4%nat in Hk. change (Z.to_nat 4) with 4%nat. lia. }
  rewrite (write_bytes_lookup_out _ (used_elem_at c ui) 4
             (Z_to_bv 32 (bv_unsigned (vr_head r))) x).
  2:{ intro Hc. apply pa_range_elim in Hc as (k & Hk & ->). apply H8.
      apply pa_range_intro. change (N.to_nat 4) with 4%nat in Hk. lia. }
  apply lookup_empty.
Qed.

Lemma used_writes_elem (c : virtio_cfg) (ui : bv 16) (r : vio_req) (j : nat) :
  vc_qnum c = Z_to_bv 32 8 -> (j < 4)%nat ->
  virtio_used_writes c ui r !! pa_add (used_elem_at c ui) j
  = Some (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head r))) j).
Proof.
  intros Hq Hj. rewrite (virtio_used_writes_unfold c ui r Hq).
  pose proof (ui_mod8_bound ui) as Hs.
  rewrite (write_bytes_lookup_out _ (used_idx_pa c) 2
             (bv_add ui (Z_to_bv 16 1)) (pa_add (used_elem_at c ui) j)).
  2:{ intro Hc. apply pa_range_elim in Hc as (k & Hk & Heq).
      change (N.to_nat 2) with 2%nat in Hk.
      unfold used_elem_at, used_idx_pa, vq_used_ring_off, vq_used_elem_size,
        vq_idx_off in Heq.
      exact (used_off_ne c (4 + 8 * (bv_unsigned ui `mod` 8)) 2 j k
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq). }
  rewrite (write_bytes_lookup_out _ (pa_off (used_elem_at c ui) 4) 4
             (vr_len r) (pa_add (used_elem_at c ui) j)).
  2:{ intro Hc. apply pa_range_elim in Hc as (k & Hk & Heq).
      change (N.to_nat 4) with 4%nat in Hk.
      exact (pa_add_off4_ne (used_elem_at c ui) j k Hj Hk Heq). }
  apply write_bytes_lookup; lia.
Qed.

Lemma used_writes_idx (c : virtio_cfg) (ui : bv 16) (r : vio_req) (j : nat) :
  vc_qnum c = Z_to_bv 32 8 -> (j < 2)%nat ->
  virtio_used_writes c ui r !! pa_add (used_idx_pa c) j
  = Some (nth_byte (bv_add ui (Z_to_bv 16 1)) j).
Proof.
  intros Hq Hj. rewrite (virtio_used_writes_unfold c ui r Hq).
  apply write_bytes_lookup; lia.
Qed.

(* -- lifted to [vslot_writes] (the status insert and the read-buffer fill) -- *)

Lemma vs_len_bound (sl : vslot) : Z.of_nat (vs_len sl) < 18446744073709551616.
Proof.
  unfold vs_len.
  pose proof (bv_unsigned_in_range 32 (vr_len (vs_req sl))) as [Hl Hh].
  unfold bv_modulus in Hh. change (2 ^ Z.of_N 32) with 4294967296 in Hh. lia.
Qed.

Lemma vslot_writes_out_of_wr (c : virtio_cfg) (ui : bv 16) (dk : Z -> bv 8)
    (sl : vslot) (x : Arch.pa) :
  x ∉ slot_wr sl ->
  vslot_writes c ui dk sl !! x = virtio_used_writes c ui (vs_req sl) !! x.
Proof.
  intro Hx. unfold vslot_writes. cbv zeta.
  assert (Hst : vr_status (vs_req sl) ≠ x).
  { intros <-. apply Hx. unfold slot_wr.
    apply elem_of_union_l, elem_of_singleton. reflexivity. }
  destruct (vs_is_out sl) eqn:Hout.
  - rewrite lookup_insert_ne; [reflexivity | exact Hst].
  - rewrite write_byte_list_lookup_out.
    + rewrite lookup_insert_ne; [reflexivity | exact Hst].
    + rewrite disk_read_length. intro Hc. apply Hx.
      unfold slot_wr. rewrite Hout. apply elem_of_union_r. exact Hc.
Qed.

Lemma vslot_writes_none (c : virtio_cfg) (ui : bv 16) (dk : Z -> bv 8)
    (sl : vslot) (x : Arch.pa) :
  vc_qnum c = Z_to_bv 32 8 ->
  x ∉ slot_wr sl ->
  x ∉ pa_range (used_elem_at c ui) 8 ->
  x ∉ pa_range (used_idx_pa c) 2 ->
  vslot_writes c ui dk sl !! x = None.
Proof.
  intros Hq Hwr H8 H2.
  rewrite (vslot_writes_out_of_wr c ui dk sl x Hwr).
  exact (used_writes_out c ui (vs_req sl) x Hq H8 H2).
Qed.

Lemma vslot_writes_idx (c : virtio_cfg) (ui : bv 16) (dk : Z -> bv 8)
    (sl : vslot) (j : nat) :
  vc_qnum c = Z_to_bv 32 8 -> (j < 2)%nat ->
  slot_wr sl ## used_page_pas c ->
  vslot_writes c ui dk sl !! pa_add (used_idx_pa c) j
  = Some (nth_byte (bv_add ui (Z_to_bv 16 1)) j).
Proof.
  intros Hq Hj Hdisj.
  assert (Hwr : pa_add (used_idx_pa c) j ∉ slot_wr sl).
  { intro Hc. exact (proj1 (elem_of_disjoint _ _) Hdisj _ Hc
                       (used_idx_in_page c j Hj)). }
  rewrite (vslot_writes_out_of_wr c ui dk sl _ Hwr).
  exact (used_writes_idx c ui (vs_req sl) j Hq Hj).
Qed.

Lemma vslot_writes_elem (c : virtio_cfg) (ui : bv 16) (dk : Z -> bv 8)
    (sl : vslot) (j : nat) :
  vc_qnum c = Z_to_bv 32 8 -> (j < 4)%nat ->
  slot_wr sl ## used_page_pas c ->
  vslot_writes c ui dk sl !! pa_add (used_elem_at c ui) j
  = Some (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) j).
Proof.
  intros Hq Hj Hdisj. pose proof (ui_mod8_bound ui) as Hs.
  assert (Hwr : pa_add (used_elem_at c ui) j ∉ slot_wr sl).
  { intro Hc. apply (proj1 (elem_of_disjoint _ _) Hdisj _ Hc).
    unfold used_elem_at. apply used_elem_in_page; lia. }
  rewrite (vslot_writes_out_of_wr c ui dk sl _ Hwr).
  exact (used_writes_elem c ui (vs_req sl) j Hq Hj).
Qed.

Lemma vslot_writes_status (c : virtio_cfg) (ui : bv 16) (dk : Z -> bv 8)
    (sl : vslot) :
  (vs_is_out sl = false ->
     vr_status (vs_req sl) ∉ pa_range (vr_buf (vs_req sl)) (vs_len sl)) ->
  vslot_writes c ui dk sl !! vr_status (vs_req sl) = Some byte_zero.
Proof.
  intro Hst. unfold vslot_writes. cbv zeta.
  destruct (vs_is_out sl) eqn:Hout.
  - apply lookup_insert.
  - rewrite write_byte_list_lookup_out.
    + apply lookup_insert.
    + rewrite disk_read_length. exact (Hst eq_refl).
Qed.

Lemma vslot_writes_buf (c : virtio_cfg) (ui : bv 16) (dk : Z -> bv 8)
    (sl : vslot) (j : nat) (b : bv 8) :
  vs_is_out sl = false ->
  disk_read dk (vs_sector_off sl) (vs_len sl) !! j = Some b ->
  vslot_writes c ui dk sl !! pa_add (vr_buf (vs_req sl)) j = Some b.
Proof.
  intros Hout Hj. unfold vslot_writes. cbv zeta. rewrite Hout.
  apply write_byte_list_lookup; [| exact Hj].
  rewrite disk_read_length. apply vs_len_bound.
Qed.

(* the used-ring records of OTHER positions survive: distinct positions mod 8
   report into disjoint elements, and none of them is the index field *)
Lemma used_elem_pa_ne_elem (c : virtio_cfg) (p : nat) (s : Z) (i : nat) :
  0 <= s < 8 -> Z.of_nat p `mod` 8 ≠ s -> (i < 4)%nat ->
  pa_add (used_elem_pa c p) i
  ∉ pa_range (pa_off (vc_used c)
                (vq_used_ring_off + vq_used_elem_size * s)) 8.
Proof.
  intros Hs Hne Hi Hc. apply pa_range_elim in Hc as (k & Hk & Heq).
  pose proof (Z.mod_pos_bound (Z.of_nat p) 8 ltac:(lia)) as Hpb.
  unfold used_elem_pa, vq_used_ring_off, vq_used_elem_size in Heq.
  exact (used_off_ne c (4 + 8 * (Z.of_nat p `mod` 8)) (4 + 8 * s) i k
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq).
Qed.

Lemma used_elem_pa_ne_idx (c : virtio_cfg) (p : nat) (i : nat) :
  (i < 4)%nat -> pa_add (used_elem_pa c p) i ∉ pa_range (used_idx_pa c) 2.
Proof.
  intros Hi Hc. apply pa_range_elim in Hc as (k & Hk & Heq).
  pose proof (Z.mod_pos_bound (Z.of_nat p) 8 ltac:(lia)) as Hpb.
  unfold used_elem_pa, used_idx_pa, vq_used_ring_off, vq_used_elem_size,
    vq_idx_off in Heq.
  exact (used_off_ne c (4 + 8 * (Z.of_nat p `mod` 8)) 2 i k
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq).
Qed.

Lemma used_elem_pa_in_page (c : virtio_cfg) (p : nat) (i : nat) :
  (i < 4)%nat -> pa_add (used_elem_pa c p) i ∈ used_page_pas c.
Proof.
  intro Hi. pose proof (Z.mod_pos_bound (Z.of_nat p) 8 ltac:(lia)) as Hpb.
  unfold used_elem_pa. apply used_elem_in_page; lia.
Qed.

Lemma gset_union_comm3 {A : Type} `{Countable A} (X Y Z : gset A) :
  X ∪ (Y ∪ Z) = Z ∪ (X ∪ Y).
Proof. apply gset_eq_of_elem. intro x. rewrite !elem_of_union. tauto. Qed.

Lemma pins_union_off_standing (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D ->
  dom (pins_union (vp_pin pr)) ## avail_idx_dom c ∪ used_page_pas c.
Proof.
  intro Hok. apply elem_of_disjoint. intros a Ha Hb.
  apply pins_union_dom_inv in Ha as (q & mq & Hq & Hmq).
  destruct (vproto_slot_of_pin c pr D q mq Hok Hq) as [slq Hsq].
  exact (proj1 (elem_of_disjoint _ _)
           (vpo_standing _ _ _ Hok q slq mq Hsq Hq) a
           (slot_fp_pin slq mq a Hmq) Hb).
Qed.

Lemma pins_union_ctl (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D -> pins_union (vp_pin pr) ⊆ vproto_ctl c pr.
Proof.
  intro Hok. unfold vproto_ctl.
  apply virtio_ctl_union; [| reflexivity ].
  rewrite avail_idx_bytes_dom. apply gset_disj_sym.
  apply (gset_disj_sub_r _ _ (avail_idx_dom c ∪ used_page_pas c));
    [ apply union_subseteq_l | exact (pins_union_off_standing c pr D Hok) ].
Qed.

(* record projections, as rewrite rules ([cbn] does not open these) *)
Lemma vpp_nc (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_nc (vproto_publish_state pr sl pin) = vp_nc pr.
Proof. reflexivity. Qed.
Lemma vpp_np (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_np (vproto_publish_state pr sl pin) = S (vp_np pr).
Proof. reflexivity. Qed.
Lemma vpp_pend (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_pend (vproto_publish_state pr sl pin) = <[ vp_np pr := sl ]> (vp_pend pr).
Proof. reflexivity. Qed.
Lemma vpp_done (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_done (vproto_publish_state pr sl pin) = vp_done pr.
Proof. reflexivity. Qed.

Lemma vpr_nc (pr : vproto) (p : nat) :
  vp_nc (vproto_reclaim_state pr p) = vp_nc pr.
Proof. reflexivity. Qed.
Lemma vpr_np (pr : vproto) (p : nat) :
  vp_np (vproto_reclaim_state pr p) = vp_np pr.
Proof. reflexivity. Qed.
Lemma vpr_pend (pr : vproto) (p : nat) :
  vp_pend (vproto_reclaim_state pr p) = vp_pend pr.
Proof. reflexivity. Qed.
Lemma vpr_done (pr : vproto) (p : nat) :
  vp_done (vproto_reclaim_state pr p) = delete p (vp_done pr).
Proof. reflexivity. Qed.

(* record projections, as rewrite rules ([cbn] does not open these) *)
Lemma vslot_post_cfg (v : virtio_state) (sl : vslot) :
  v_cfg (vslot_post v sl) = v_cfg v.
Proof. reflexivity. Qed.
Lemma vslot_post_seen (v : virtio_state) (sl : vslot) :
  v_seen (vslot_post v sl) = bv_add (v_seen v) (Z_to_bv 16 1).
Proof. reflexivity. Qed.
Lemma vslot_post_uidx (v : virtio_state) (sl : vslot) :
  v_used_idx (vslot_post v sl) = bv_add (v_used_idx v) (Z_to_bv 16 1).
Proof. reflexivity. Qed.
(* THE COMPLETION MOVES NO DISK BYTE (sector-atomic-disk.md stage 2): the
   request's sectors landed one at a time, before it was enabled. *)
Lemma vslot_post_disk (v : virtio_state) (sl : vslot) :
  v_disk (vslot_post v sl) = v_disk v.
Proof. reflexivity. Qed.

Lemma vps_nc (pr : vproto) (sl : vslot) :
  vp_nc (vproto_step_state pr sl) = S (vp_nc pr).
Proof. reflexivity. Qed.
Lemma vps_np (pr : vproto) (sl : vslot) :
  vp_np (vproto_step_state pr sl) = vp_np pr.
Proof. reflexivity. Qed.
Lemma vps_pend (pr : vproto) (sl : vslot) :
  vp_pend (vproto_step_state pr sl) = delete (vp_nc pr) (vp_pend pr).
Proof. reflexivity. Qed.
Lemma vps_done (pr : vproto) (sl : vslot) :
  vp_done (vproto_step_state pr sl) = <[ vp_nc pr := sl ]> (vp_done pr).
Proof. reflexivity. Qed.

Lemma used_elem_at_in_page (c : virtio_cfg) (ui : bv 16) (i : nat) :
  (i < 8)%nat -> pa_add (used_elem_at c ui) i ∈ used_page_pas c.
Proof.
  intro Hi. pose proof (ui_mod8_bound ui) as Hs.
  unfold used_elem_at. apply used_elem_in_page; lia.
Qed.

(* an address outside the slot's writable bytes and outside the used page is
   untouched by the step -- this frames every OTHER slot's record *)
Lemma vslot_writes_none_of_page (c : virtio_cfg) (ui : bv 16) (dk : Z -> bv 8)
    (sl : vslot) (x : Arch.pa) :
  vc_qnum c = Z_to_bv 32 8 -> x ∉ slot_wr sl -> x ∉ used_page_pas c ->
  vslot_writes c ui dk sl !! x = None.
Proof.
  intros Hq Hwr Hpg. apply vslot_writes_none; [exact Hq | exact Hwr | | ].
  - intro Hc. apply pa_range_elim in Hc as (i & Hi & ->). apply Hpg.
    exact (used_elem_at_in_page c ui i Hi).
  - intro Hc. apply pa_range_elim in Hc as (i & Hi & ->). apply Hpg.
    change (N.to_nat 2) with 2%nat in Hi. exact (used_idx_in_page c i Hi).
Qed.

(* ...and ANOTHER position's used-ring element is untouched too *)
Lemma vslot_writes_none_other_elem (c : virtio_cfg) (dk : Z -> bv 8)
    (sl : vslot) (p q : nat) (i : nat) :
  vc_qnum c = Z_to_bv 32 8 -> slot_wr sl ## used_page_pas c ->
  Z.of_nat q `mod` 8 ≠ Z.of_nat p `mod` 8 -> (i < 4)%nat ->
  vslot_writes c (wrap16 p) dk sl !! pa_add (used_elem_pa c q) i = None.
Proof.
  intros Hq Hdisj Hne Hi.
  pose proof (Z.mod_pos_bound (Z.of_nat p) 8 ltac:(lia)) as Hpb.
  apply vslot_writes_none; [exact Hq | | | ].
  - intro Hc. exact (proj1 (elem_of_disjoint _ _) Hdisj _ Hc
                       (used_elem_pa_in_page c q i Hi)).
  - rewrite used_elem_at_wrap.
    apply used_elem_pa_ne_elem; [ lia | exact Hne | exact Hi ].
  - exact (used_elem_pa_ne_idx c q i Hi).
Qed.

(* -- the lease [virtio_disk_init] hands over: the avail-index field (zero)  *)
(*    plus the whole zeroed used page --                                    *)

Lemma avail_idx_bytes_range (c : virtio_cfg) (np : nat) :
  avail_idx_bytes c np = range_map (avail_idx_pa c) 2 (nth_byte (wrap16 np)).
Proof. reflexivity. Qed.

Definition vinit_dma (c : virtio_cfg) : gmap Arch.pa (bv 8) :=
  range_map (avail_idx_pa c) 2 (nth_byte (wrap16 0))
  ∪ range_map (vc_used c) 4096 (fun _ : nat => byte_zero).

Lemma nth_byte_wrap16_0 (j : nat) :
  (j < 2)%nat -> nth_byte (wrap16 0) j = byte_zero.
Proof.
  intro Hj. destruct j as [|[|j]].
  - apply bv_eq. vm_compute. reflexivity.
  - apply bv_eq. vm_compute. reflexivity.
  - lia.
Qed.

Lemma vinit_dma_disj (c : virtio_cfg) :
  avail_idx_dom c ## used_page_pas c ->
  range_map (avail_idx_pa c) 2 (nth_byte (wrap16 0))
    ##ₘ range_map (vc_used c) 4096 (fun _ : nat => byte_zero).
Proof.
  (* [range_map_dom] lands on [pa_range _ 4096]; [avail_idx_dom]/[used_page_pas]
     are that same term behind one delta step, but leaving the fold to
     [exact]'s conversion makes it normalise a 4096-element [list_to_set] over
     [gset Arch.pa] -- 3.7 s here and 3.5 s in [vinit_dma_dom] below, plus as
     much again at each [Qed].  Unfolding both names first makes the match
     syntactic. *)
  intro Hd. apply map_disjoint_dom. rewrite !range_map_dom.
  unfold avail_idx_dom, used_page_pas in Hd. exact Hd.
Qed.

Lemma vinit_dma_dom (c : virtio_cfg) :
  dom (vinit_dma c) = avail_idx_dom c ∪ used_page_pas c.
Proof.
  unfold vinit_dma, avail_idx_dom, used_page_pas.
  rewrite dom_union_L !range_map_dom. reflexivity.
Qed.

Lemma vinit_dma_ctl (c : virtio_cfg) : vproto_ctl c vproto0 ⊆ vinit_dma c.
Proof.
  rewrite (vproto0_ctl c) (avail_idx_bytes_range c 0).
  unfold vinit_dma. apply map_union_subseteq_l.
Qed.

Lemma vinit_dma_uidx (c : virtio_cfg) :
  avail_idx_dom c ## used_page_pas c ->
  read_bytes (vinit_dma c) (used_idx_pa c) 2 = Some (wrap16 0).
Proof.
  intro Hd. apply read_bytes_of_list. intros j Hj.
  assert (Hj2 : (j < 2)%nat) by lia.
  assert (Hin : pa_add (used_idx_pa c) j ∈ used_page_pas c)
    by (apply used_idx_in_page; exact Hj2).
  unfold vinit_dma. rewrite lookup_union_out.
  2:{ rewrite range_map_dom. intro Hc.
      exact (proj1 (elem_of_disjoint _ _) Hd _ Hc Hin). }
  assert (Heq : pa_add (used_idx_pa c) j = pa_add (vc_used c) (2 + j)%nat).
  { unfold used_idx_pa. rewrite pa_off_add. reflexivity. }
  rewrite Heq (range_map_lookup (vc_used c) 4096 (fun _ : nat => byte_zero)
                 (2 + j)%nat).
  - f_equal. symmetry. exact (nth_byte_wrap16_0 j Hj2).
  - rewrite z4096. lia.
  - lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* the protocol state's ghost_map value: each slot paired with its pin, and *)
(* how the three surgeries move it                                          *)
(* ---------------------------------------------------------------------- *)

Definition vp_spins (pr : vproto) : gmap nat (vslot * gmap Arch.pa (bv 8)) :=
  map_zip (vp_slots pr) (vp_pin pr).

Lemma vp_spins_lookup (pr : vproto) (p : nat) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) :
  vp_spins pr !! p = Some (sl, pin) ->
  vp_slots pr !! p = Some sl /\ vp_pin pr !! p = Some pin.
Proof.
  intro H. apply map_lookup_zip_Some in H as [H1 H2]. exact (conj H1 H2).
Qed.

Lemma vp_spins_none (pr : vproto) (p : nat) :
  vp_slots pr !! p = None -> vp_spins pr !! p = None.
Proof.
  intro H. unfold vp_spins.
  apply map_lookup_zip_with_None. left. exact H.
Qed.

Lemma vproto_step_slots (pr : vproto) (sl : vslot) :
  vp_pend pr !! vp_nc pr = Some sl ->
  vp_slots (vproto_step_state pr sl) = vp_slots pr.
Proof.
  intro Hsl. unfold vp_slots, vproto_step_state. cbn [vp_pend vp_done vp_nc].
  apply map_eq. intro q. destruct (decide (q = vp_nc pr)) as [->|Hne].
  - rewrite lookup_union_r.
    2:{ apply lookup_delete. }
    rewrite lookup_insert. symmetry. apply lookup_union_Some_l. exact Hsl.
  - rewrite !lookup_union lookup_delete_ne; [| congruence ].
    rewrite lookup_insert_ne; [| congruence ]. reflexivity.
Qed.

Lemma vp_spins_step (pr : vproto) (sl : vslot) :
  vp_pend pr !! vp_nc pr = Some sl ->
  vp_spins (vproto_step_state pr sl) = vp_spins pr.
Proof.
  intro H. unfold vp_spins. rewrite (vproto_step_slots pr sl H). reflexivity.
Qed.

Lemma vproto_publish_slots (pr : vproto) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) :
  vp_slots (vproto_publish_state pr sl pin) = <[ vp_np pr := sl ]> (vp_slots pr).
Proof.
  unfold vp_slots, vproto_publish_state. cbn [vp_pend vp_done vp_np].
  symmetry. apply insert_union_l.
Qed.

Lemma vp_spins_publish (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_spins (vproto_publish_state pr sl pin)
  = <[ vp_np pr := (sl, pin) ]> (vp_spins pr).
Proof.
  unfold vp_spins. rewrite (vproto_publish_slots pr sl pin).
  assert (Hp : vp_pin (vproto_publish_state pr sl pin)
               = <[ vp_np pr := pin ]> (vp_pin pr)) by reflexivity.
  rewrite Hp. symmetry. apply (map_insert_zip_with pair).
Qed.

Lemma vproto_pend_none (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) :
  vproto_ok c pr D -> vp_done pr !! p = Some sl -> vp_pend pr !! p = None.
Proof.
  intros Hok Hdone.
  assert (Hplt : (p < vp_nc pr)%nat)
    by (apply (vpo_done_lt _ _ _ Hok), elem_of_dom; exists sl; exact Hdone).
  apply not_elem_of_dom. rewrite (vpo_pend_dom _ _ _ Hok). intro Hc.
  apply elem_of_set_seq in Hc. lia.
Qed.

Lemma vproto_done_slot (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) :
  vproto_ok c pr D -> vp_done pr !! p = Some sl -> vp_slots pr !! p = Some sl.
Proof.
  intros Hok Hdone. unfold vp_slots. rewrite lookup_union_r.
  - exact Hdone.
  - exact (vproto_pend_none c pr D p sl Hok Hdone).
Qed.

Lemma vproto_reclaim_slots (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) :
  vproto_ok c pr D -> vp_done pr !! p = Some sl ->
  vp_slots (vproto_reclaim_state pr p) = delete p (vp_slots pr).
Proof.
  intros Hok Hdone.
  assert (Hdn : delete p (vp_pend pr) = vp_pend pr)
    by (apply delete_notin; exact (vproto_pend_none c pr D p sl Hok Hdone)).
  unfold vp_slots, vproto_reclaim_state. cbn [vp_pend vp_done].
  rewrite delete_union Hdn. reflexivity.
Qed.

Lemma vp_spins_reclaim (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p : nat) (sl : vslot) :
  vproto_ok c pr D -> vp_done pr !! p = Some sl ->
  vp_spins (vproto_reclaim_state pr p) = delete p (vp_spins pr).
Proof.
  intros Hok Hdone. unfold vp_spins.
  rewrite (vproto_reclaim_slots c pr D p sl Hok Hdone).
  assert (Hp : vp_pin (vproto_reclaim_state pr p) = delete p (vp_pin pr))
    by reflexivity.
  rewrite Hp. symmetry. apply (map_delete_zip_with pair).
Qed.

Lemma vp_slots_init : vp_slots vproto0 = (∅ : gmap nat vslot).
Proof.
  unfold vp_slots. cbn [vp_pend vp_done]. apply map_eq. intro q.
  rewrite lookup_union !lookup_empty. reflexivity.
Qed.

Lemma vp_spins_init : vp_spins vproto0 = ∅.
Proof.
  unfold vp_spins. rewrite vp_slots_init.
  assert (Hp : vp_pin vproto0 = (∅ : gmap nat (gmap Arch.pa (bv 8))))
    by reflexivity.
  rewrite Hp. apply (map_zip_with_empty pair).
Qed.

(* THE window separation fact, in the form the used-ring framing needs: two
   distinct in-flight positions pin DISTINCT ring entries, hence differ mod 8,
   hence report into DISTINCT used-ring elements. *)
Lemma vproto_mod8_ne (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
    (p q : nat) (slp slq : vslot) (pinp pinq : gmap Arch.pa (bv 8)) :
  vproto_ok c pr D -> p ≠ q ->
  vp_slots pr !! p = Some slp -> vp_pin pr !! p = Some pinp ->
  vp_slots pr !! q = Some slq -> vp_pin pr !! q = Some pinq ->
  Z.of_nat p `mod` 8 ≠ Z.of_nat q `mod` 8.
Proof.
  intros Hok Hne H1 H2 H3 H4 Hmod.
  assert (Hring : ring_entry_pa c q = ring_entry_pa c p).
  { unfold ring_entry_pa. rewrite Hmod. reflexivity. }
  assert (Hdp : ring_entry_pa c p ∈ dom pinp).
  { pose proof (spo_ring _ _ _ _ (vpo_slot _ _ _ Hok p slp pinp H1 H2)) as Hr.
    apply (read_bytes_dom_sub pinp (ring_entry_pa c p) 2 _ Hr).
    apply pa_range_base. change (N.to_nat 2) with 2%nat. lia. }
  assert (Hdq : ring_entry_pa c p ∈ dom pinq).
  { pose proof (spo_ring _ _ _ _ (vpo_slot _ _ _ Hok q slq pinq H3 H4)) as Hr.
    rewrite Hring in Hr.
    apply (read_bytes_dom_sub pinq (ring_entry_pa c p) 2 _ Hr).
    apply pa_range_base. change (N.to_nat 2) with 2%nat. lia. }
  pose proof (vpo_fp_disj _ _ _ Hok p q slp slq pinp pinq Hne H1 H2 H3 H4) as Hd.
  exact (proj1 (elem_of_disjoint _ _) Hd _
           (slot_fp_pin slp pinp _ Hdp) (slot_fp_pin slq pinq _ Hdq)).
Qed.

(* pure alignment/geometry facts about the live configuration's three pages,
   established once by [virtio_disk_init]'s caller and carried in the
   protocol so the word-level accessors can rebuild aligned points-tos *)
Definition virtio_pages_aligned (c : virtio_cfg) : Prop :=
  bv_unsigned (vc_desc c) `mod` 4096 = 0
  /\ bv_unsigned (vc_avail c) `mod` 4096 = 0
  /\ bv_unsigned (vc_used c) `mod` 4096 = 0.

Section VirtioProto.
  Context `{!riscvGS Σ, !diskGhostG Σ}.

  (* -- byte-window sugar over the physical points-to -------------------- *)

  Definition phys_word2 (a : Arch.pa) (w : bv 16) : iProp Σ :=
    ([∗ list] j ∈ seq 0 2, phys_pointsto (pa_add a j) (DfracOwn 1) (nth_byte w j))%I.
  Definition phys_word4 (a : Arch.pa) (w : bv 32) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, phys_pointsto (pa_add a j) (DfracOwn 1) (nth_byte w j))%I.
  Definition phys_map (mm : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ mm, phys_pointsto a (DfracOwn 1) b)%I.
  Definition phys_list (a : Arch.pa) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] j ↦ b ∈ bs, phys_pointsto (pa_add a j) (DfracOwn 1) b)%I.

  (* -- byte windows <-> byte maps --------------------------------------- *)

  Lemma dma_own_phys_map (dma : gmap Arch.pa (bv 8)) :
    dma_own dma ⊣⊢ phys_map dma.
  Proof. reflexivity. Qed.

  Lemma phys_map_idx_list (a : Arch.pa) (l : list nat) (f : nat -> bv 8) :
    NoDup l -> (forall j, j ∈ l -> Z.of_nat j < 18446744073709551616) ->
    phys_map (foldr (fun j acc => <[ pa_add a j := f j ]> acc) ∅ l)
    ⊣⊢ ([∗ list] j ∈ l, phys_pointsto (pa_add a j) (DfracOwn 1) (f j)).
  Proof.
    induction l as [|i l IH]; intros Hnd Hb.
    - rewrite /phys_map big_sepM_empty big_sepL_nil. reflexivity.
    - apply NoDup_cons in Hnd as [Hi Hnd].
      assert (Hnone : foldr (fun j acc => <[ pa_add a j := f j ]> acc)
                        (∅ : gmap Arch.pa (bv 8)) l !! pa_add a i = None).
      { rewrite (foldr_ins_lookup_ne (pa_add a) f l
                   (∅ : gmap Arch.pa (bv 8)) (pa_add a i)).
        - apply lookup_empty.
        - intros z Hz Heq. exfalso. apply Hi.
          assert (Hzi : z = i)
            by (apply (pa_add_inj a);
                [ apply Hb, elem_of_list_further, Hz
                | apply Hb, elem_of_list_here | exact Heq ]).
          rewrite Hzi in Hz. exact Hz. }
      cbn [foldr]. rewrite /phys_map big_sepM_insert; [| exact Hnone ].
      rewrite big_sepL_cons. cbv beta.
      apply bi.sep_proper; [reflexivity|].
      apply IH; [ exact Hnd | intros j Hj; apply Hb, elem_of_list_further, Hj ].
  Qed.

  Lemma phys_map_range (a : Arch.pa) (n : nat) (f : nat -> bv 8) :
    Z.of_nat n < 18446744073709551616 ->
    phys_map (range_map a n f)
    ⊣⊢ ([∗ list] j ∈ seq 0 n, phys_pointsto (pa_add a j) (DfracOwn 1) (f j)).
  Proof.
    intro Hn. apply phys_map_idx_list; [ apply NoDup_seq | ].
    intros j Hj. apply elem_of_seq in Hj. lia.
  Qed.

  Lemma phys_word2_map (a : Arch.pa) (w : bv 16) :
    phys_word2 a w ⊣⊢ phys_map (range_map a 2 (nth_byte w)).
  Proof.
    rewrite /phys_word2. symmetry. apply (phys_map_range a 2 (nth_byte w)). lia.
  Qed.

  Lemma phys_word4_map (a : Arch.pa) (w : bv 32) :
    phys_word4 a w ⊣⊢ phys_map (range_map a 4 (nth_byte w)).
  Proof.
    rewrite /phys_word4. symmetry. apply (phys_map_range a 4 (nth_byte w)). lia.
  Qed.

  Lemma phys_list_of_fun (a : Arch.pa) (n : nat) (g : nat -> bv 8)
      (bs : list (bv 8)) :
    bs = g <$> seq 0 n ->
    phys_list a bs
    ⊣⊢ ([∗ list] j ∈ seq 0 n, phys_pointsto (pa_add a j) (DfracOwn 1) (g j)).
  Proof.
    intros ->. rewrite /phys_list big_sepL_fmap.
    apply big_sepL_proper. intros k y Hk.
    apply lookup_seq in Hk as [Hy _].
    assert (Hyk : y = k) by lia. rewrite Hyk. reflexivity.
  Qed.

  Lemma phys_list_replicate (a : Arch.pa) (n : nat) (b : bv 8) :
    Z.of_nat n < 18446744073709551616 ->
    phys_list a (replicate n b) ⊣⊢ phys_map (range_map a n (fun _ => b)).
  Proof.
    intro Hn.
    rewrite (phys_list_of_fun a n (fun _ : nat => b) (replicate n b)
               (replicate_fmap_seq n b)).
    symmetry. apply phys_map_range. exact Hn.
  Qed.

  Lemma phys_list_map (a : Arch.pa) (bs : list (bv 8)) :
    Z.of_nat (length bs) < 18446744073709551616 ->
    phys_list a bs ⊣⊢ phys_map (range_map a (length bs) (fun j => bs !!! j)).
  Proof.
    intro Hn.
    rewrite (phys_list_of_fun a (length bs) (fun j : nat => bs !!! j) bs
               (list_eq_total bs)).
    symmetry. apply phys_map_range. exact Hn.
  Qed.

  (* -- ownership forces disjointness ------------------------------------ *)

  Lemma phys_map_disj (m1 m2 : gmap Arch.pa (bv 8)) :
    phys_map m1 -∗ phys_map m2 -∗ ⌜m1 ##ₘ m2⌝.
  Proof.
    induction m1 as [|a b m1' Hnew IH] using map_ind; iIntros "H1 H2".
    { iPureIntro. apply map_disjoint_empty_l. }
    rewrite /phys_map big_sepM_insert; [| exact Hnew ].
    iDestruct "H1" as "[Ha H1]".
    iDestruct (IH with "H1 H2") as %Hdisj.
    destruct (m2 !! a) as [b2|] eqn:Hb2.
    - iDestruct (big_sepM_lookup _ _ a b2 Hb2 with "H2") as "Hb2".
      rewrite /phys_pointsto.
      iDestruct "Ha" as "[Ha _]". iDestruct "Hb2" as "[Hb2 _]".
      iDestruct (pointsto_ne with "Ha Hb2") as %Hne.
      iPureIntro. destruct (Hne eq_refl).
    - iPureIntro. apply map_disjoint_insert_l. split; [exact Hb2 | exact Hdisj].
  Qed.

  Lemma dma_own_disj (dma mm : gmap Arch.pa (bv 8)) :
    dma_own dma -∗ phys_map mm -∗ ⌜dom mm ## dom dma⌝.
  Proof.
    iIntros "Hd Hm".
    iDestruct (phys_map_disj with "Hm Hd") as %Hdisj.
    iPureIntro. by apply map_disjoint_dom.
  Qed.

  (* -- opening and closing a window of the lease ------------------------ *)

  Lemma dma_own_split (mm dma : gmap Arch.pa (bv 8)) :
    mm ⊆ dma -> dma_own dma ⊣⊢ phys_map mm ∗ dma_own (dma ∖ mm).
  Proof.
    intro Hsub.
    assert (Hd : mm ∪ (dma ∖ mm) = dma) by (apply map_difference_union; exact Hsub).
    assert (Hdj : mm ##ₘ dma ∖ mm)
      by (apply (map_disjoint_difference_r dma mm mm); reflexivity).
    assert (Heq : dma_own dma ⊣⊢ dma_own (mm ∪ (dma ∖ mm)))
      by (rewrite Hd; reflexivity).
    rewrite Heq /dma_own.
    rewrite (big_sepM_union (fun a b => phys_pointsto a (DfracOwn 1) b)
               mm (dma ∖ mm) Hdj).
    reflexivity.
  Qed.

  Lemma dma_own_acc (mm mm' dma : gmap Arch.pa (bv 8)) :
    mm ⊆ dma -> dom mm' = dom mm ->
    dma_own dma -∗ phys_map mm ∗ (phys_map mm' -∗ dma_own (mm' ∪ dma)).
  Proof.
    intros Hsub Hdom.
    assert (Hdj : mm ##ₘ dma ∖ mm)
      by (apply (map_disjoint_difference_r dma mm mm); reflexivity).
    rewrite (dma_own_split mm dma Hsub).
    iIntros "[$ Hrest]". iIntros "Hmm'".
    assert (Heq : mm' ∪ dma = mm' ∪ (dma ∖ mm)).
    { apply map_eq. intro x. destruct (mm' !! x) as [b|] eqn:Hx.
      - rewrite (lookup_union_Some_l mm' dma x b Hx)
                (lookup_union_Some_l mm' (dma ∖ mm) x b Hx). reflexivity.
      - rewrite (lookup_union_r mm' dma x Hx)
                (lookup_union_r mm' (dma ∖ mm) x Hx).
        symmetry. apply lookup_difference_out.
        assert (Hnd : x ∉ dom mm') by (by apply not_elem_of_dom).
        rewrite Hdom in Hnd. exact Hnd. }
    assert (Hdj' : mm' ##ₘ dma ∖ mm).
    { apply map_disjoint_dom. rewrite Hdom. by apply map_disjoint_dom. }
    rewrite Heq /dma_own.
    rewrite (big_sepM_union (fun a b => phys_pointsto a (DfracOwn 1) b)
               mm' (dma ∖ mm) Hdj').
    iFrame "Hmm' Hrest".
  Qed.

  Lemma dma_own_acc_same (mm dma : gmap Arch.pa (bv 8)) :
    mm ⊆ dma ->
    dma_own dma -∗ phys_map mm ∗ (phys_map mm -∗ dma_own dma).
  Proof.
    intro Hsub.
    assert (Hun : mm ∪ dma = dma) by (apply map_subseteq_union; exact Hsub).
    iIntros "Hd".
    iDestruct (dma_own_acc mm mm dma Hsub eq_refl with "Hd") as "[$ Hback]".
    iIntros "Hmm". iDestruct ("Hback" with "Hmm") as "Hd". rewrite Hun. iFrame "Hd".
  Qed.

  (* -- the driver-facing tokens ----------------------------------------- *)

  (* the publisher credential: half of the published count.  The other half
     is inside [virtio_proto]'s live branch, so holding this half (it lives
     in the vdisk_lock's resource) proves the queue is live and pins np. *)
  Definition disk_pub (γ : disk_names) (np : nat) : iProp Σ :=
    ghost_var (dn_np γ) (1/2) np.

  (* the receipt for position [p]: the slot and the exact pin map that was
     handed over at publish -- reclaim returns exactly those bytes *)
  Definition disk_receipt (γ : disk_names) (p : nat) (sl : vslot)
      (pin : gmap Arch.pa (bv 8)) : iProp Σ :=
    p ↪[dn_slot γ] (sl, pin).

  (* a lower bound on the completed count (persistent) *)
  Definition disk_done_lb (γ : disk_names) (n : nat) : iProp Σ :=
    mono_nat_lb_own (dn_nc γ) n.

  (* -- per-slot resources ----------------------------------------------- *)

  (* For an OUT request the block's CURRENT content is arbitrary (the device
     is about to overwrite it), so it stays existential; for an IN request it
     is [vs_data sl] -- the content the publisher asserted when it published,
     and the content the device will copy into the buffer.  Pinning it here is
     what lets the woken publisher identify the fragments it gets back with
     the [disk_block] it handed in.

     THE CRASH WRITE PERMIT ITSELF CANNOT LIVE HERE, AND ITS KEY MUST
     (claude-notes/design/crash.md, and the M5b entry in completed/crash.md).
     The natural home for the enqueuer's obligation is this record -- it is
     the [vs_data] precedent, an exclusive resource recorded where the
     invariant keys on the request -- but [disk_inv_body] MUST BE [Timeless]:
     every driver site that opens it (eight of them today) does so inside an
     MMIO atomic-update accessor, where there is no step left to absorb a
     [▷], so a non-timeless body cannot be used at all.  A permit is an iProp
     (a wand over an arbitrary [riscv_crash_pred]) and is therefore never
     timeless, and there is no way to smuggle an iProp through a timeless
     invariant -- saved propositions are not timeless either ([own γ (to_agree
     (Next P))] over a non-discrete OFE).  So the permit lives in its own
     non-timeless invariant ([PermInv.perm_inv (dn_perm γ)]) and what rides
     HERE is its TIMELESS SKELETON: the ghost-map element [perm_pend], keyed
     by the pure [vs_perm sl] the slot records. *)
  (* -- THE SLOT'S PERMIT TOKEN (sector-atomic-disk.md §6e) -------------- *)

  (* ONE KEY PER REQUEST, RE-INDEXED AS THE SECTORS LAND.  A 512-byte SECTOR
     lands atomically and a 1024-byte BLOCK does not, so an OUT request's
     data reaches the durable image one sector at a time
     ([VirtioModel.virtio_sector_step]) and each landing is its own
     linearization point.  The request's obligation is therefore a SINGLE
     SEQUENTIAL permit ([RiscvPtsto.disk_seq_permit]) that unfolds a branch
     at a time: the channel cell at [vs_perm sl] carries it, each landing
     spends one branch and re-deposits the residual at the SAME key, and the
     cell's index -- the sectors still to land -- is [vs_todo sl ld], a pure
     function of the landed set the protocol already tracks.

     WHY ONE OBJECT AND NOT ONE PERMIT PER SECTOR.  A crash permit is a
     stateless view shift with no input slot and no invariant it may open at
     mask [∅], so an exclusive resource a LATER sector needs (the WAL's
     mirror half; what an earlier sector learned) could be curried into only
     one of several independent permits and would be unreachable from the
     others.  In the sequential form it travels inside the residual, and the
     device's free choice of landing order is the permit's own conjunction.

     THE COMPLETION IS THE LEAF.  It moves the used ring, the status byte and
     the interrupt -- and NO disk byte at all
     ([VirtioQueue.vslot_post_disk]) -- so the last thing the cell holds is
     the identity permit at [None], which is where the client's receipt is
     delivered in BOTH directions.  A READ has no sectors, so its cell is at
     the leaf from the start; that is what keeps [virtio_proto_step] and
     [WpUart.wp_disk_loop]'s completion arm DIRECTION-AGNOSTIC. *)
  Definition slot_perms_done (γ : disk_names) (sl : vslot) : iProp Σ :=
    perm_done (dn_perm γ) (vs_perm sl) (vs_wr sl).

  Global Instance slot_perms_done_timeless γ sl : Timeless (slot_perms_done γ sl).
  Proof. rewrite /slot_perms_done. apply _. Qed.

  Definition slot_pend_res (γ : disk_names) (ld : gset nat) (sl : vslot)
      : iProp Σ :=
    (∃ bs : list (bv 8),
       ⌜length bs = vs_len sl⌝ ∗
       ⌜vs_is_out sl = false -> bs = vs_data sl⌝ ∗
       (* THE TORN CONTENT (sector-atomic-disk.md).  The block's durable
          bytes are the OLD ones in the sectors that have not landed and the
          PAYLOAD's in the ones that have -- which is what makes a crash
          between two landings leave a half-written block, and what the
          publisher's fragments have to say while the request is in flight. *)
       ⌜vs_torn sl ld bs⌝ ∗
       disk_bytes γ (vs_sector_off sl) bs ∗
       (* THE REQUEST'S ONE CHANNEL ENTRY, at the sectors STILL TO LAND. *)
       perm_pend (dn_perm γ) (vs_perm sl) (vs_wr sl) (vs_todo sl ld))%I.

  Definition slot_done_res (γ : disk_names) (c : virtio_cfg)
      (dma : gmap Arch.pa (bv 8)) (p : nat) (sl : vslot) : iProp Σ :=
    (∃ bs : list (bv 8),
       ⌜length bs = vs_len sl⌝ ∗ disk_bytes γ (vs_sector_off sl) bs ∗
       (* AFTER the completion the block holds [vs_data sl] in BOTH
          directions: an OUT request has just written it, an IN request never
          changed it and [slot_pend_res] pinned it. *)
       ⌜bs = vs_data sl⌝ ∗
       (* the completion record the interrupt handler reads: the used-ring
          element names the head, the status byte is OK, and (for a read
          request) the buffer holds the block *)
       ⌜read_bytes dma (used_elem_pa c p) 4
          = Some (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl))))⌝ ∗
       ⌜dma !! vr_status (vs_req sl) = Some byte_zero⌝ ∗
       ⌜vs_is_out sl = false ->
          read_byte_list dma (vr_buf (vs_req sl)) (vs_len sl) = Some bs⌝ ∗
       (* the SPENT permits' tokens: the sector landings and the completion
          each moved their cell to [false] and parked their receipt in
          [PermInv]; these are what the woken publisher presents to collect
          them.  The publisher's payoff is therefore the separating
          conjunction of the per-sector receipts, plus the completion's. *)
       slot_perms_done γ sl)%I.

  (* the completion record mentions only three windows of the lease, so it
     rides through any change to the lease that leaves those bytes alone *)
  Lemma slot_done_res_mono (γ : disk_names) (c : virtio_cfg)
      (dma dma' : gmap Arch.pa (bv 8)) (p : nat) (sl : vslot) :
    (forall j : nat, (j < 4)%nat ->
       dma' !! pa_add (used_elem_pa c p) j = dma !! pa_add (used_elem_pa c p) j) ->
    dma' !! vr_status (vs_req sl) = dma !! vr_status (vs_req sl) ->
    (vs_is_out sl = false -> forall j : nat, (j < vs_len sl)%nat ->
       dma' !! pa_add (vr_buf (vs_req sl)) j
       = dma !! pa_add (vr_buf (vs_req sl)) j) ->
    slot_done_res γ c dma p sl -∗ slot_done_res γ c dma' p sl.
  Proof.
    intros Helem Hstat Hbuf. iIntros "H".
    iDestruct "H" as (bs)
      "(%Hlen & Hbs & %Hout & %Hre & %Hst & %Hbl & Hperm)".
    iExists bs. iFrame "Hbs Hperm". iPureIntro. split_and!.
    - exact Hlen.
    - exact Hout.
    - apply (read_bytes_transfer dma dma'); [| exact Hre ].
      intros j Hj. apply Helem. lia.
    - rewrite Hstat. exact Hst.
    - intros Hin. apply (read_byte_list_transfer dma dma'); [| exact (Hbl Hin) ].
      intros j Hj. exact (Hbuf Hin j Hj).
  Qed.

  (* -- THE protocol invariant (rides in dev_inv_body) ------------------- *)

  (* THE IMAGE AUTH IS NOT HERE (claude-notes/design/crash.md).  The auth+tie
     (⌜disk_view dmap (v_disk v)⌝) lives in [state_interp]'s era conjunct
     [RiscvPtsto.disk_dur_interp] instead -- it must be in the hand of
     whoever is stepping the machine, since it is pinned to the state's own
     [v_disk] -- and the two lemmas that move it --
     the live flip's predecessor [virtio_proto_intro_gen] (which no longer
     needs it at all) and the DMA completion [virtio_proto_step] (which takes
     it as an explicit premise and returns it updated) -- speak about it
     explicitly.  What stays here is exactly the queue/slot/claim protocol,
     which SHOULD die with the era: in-flight requests vanish at the device
     reset. *)
  (* WHICH SECTORS OF WHICH SLOT HAVE LANDED.  The device's landed set
     ([VirtioModel.v_landed]) belongs to the HEAD request -- the one at
     [v_seen], i.e. protocol position [vp_nc] -- and every other pending slot
     has landed nothing yet.  This is the function that says so, and it is
     what carries [v_landed] into the per-slot resource without putting a
     mutable field into the (immutable, receipt-pinned) [vslot] record. *)
  Definition pend_landed (pr : vproto) (ld : gset nat) (p : nat) : gset nat :=
    if bool_decide (p = vp_nc pr) then ld else ∅.

  Lemma pend_landed_other (pr : vproto) (ld : gset nat) (p : nat) :
    p <> vp_nc pr -> pend_landed pr ld p = ∅.
  Proof. intro H. rewrite /pend_landed bool_decide_eq_false_2 //. Qed.

  Lemma pend_landed_head (pr : vproto) (ld : gset nat) :
    pend_landed pr ld (vp_nc pr) = ld.
  Proof. rewrite /pend_landed bool_decide_eq_true_2 //. Qed.

  (* after a COMPLETION the device's landed set is empty again, so every
     still-pending slot is back to "nothing landed" *)
  Lemma pend_landed_empty (pr : vproto) (p : nat) : pend_landed pr ∅ p = ∅.
  Proof. rewrite /pend_landed. by destruct (bool_decide (p = vp_nc pr)). Qed.

  Definition virtio_proto (γ : disk_names) (v : virtio_state) : iProp Σ :=
    (if virtio_live (v_cfg v) then
        ∃ (pr : vproto) (dma : gmap Arch.pa (bv 8)),
          disk_cfg γ (v_cfg v) ∗
          dma_own dma ∗
          ⌜vproto_ctl (v_cfg v) pr ⊆ dma⌝ ∗
          ⌜vproto_ok (v_cfg v) pr (dom dma)⌝ ∗
          ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
          ⌜v_seen v = wrap16 (vp_nc pr)⌝ ∗
          ⌜v_used_idx v = wrap16 (vp_nc pr)⌝ ∗
          ⌜read_bytes dma (used_idx_pa (v_cfg v)) 2 = Some (wrap16 (vp_nc pr))⌝ ∗
          (* NOTHING PENDING MEANS NOTHING LANDED.  A sector step needs a
             pending request ([VirtioModel.virtio_sector_step] is gated on
             [virtio_pending]) and the completion clears the set
             ([virtio_complete_landed]), so an idle queue's landed set is
             empty -- which is what lets the NEXT publish hand its fresh slot
             in with all its permits still pending. *)
          ⌜vp_nc pr = vp_np pr -> v_landed v = ∅⌝ ∗
          ghost_map_auth (dn_slot γ) 1 (vp_spins pr) ∗
          mono_nat_auth_own (dn_nc γ) 1 (vp_nc pr) ∗
          ghost_var (dn_np γ) (1/2) (vp_np pr) ∗
          ([∗ map] p ↦ sl ∈ vp_pend pr, slot_pend_res γ (pend_landed pr (v_landed v) p) sl) ∗
          ([∗ map] p ↦ sl ∈ vp_done pr, slot_done_res γ (v_cfg v) dma p sl)
      else
        (* THE CONFIG TRACKER (2026-07-29).  While the queue is not live the
           invariant holds only HALF of the config cell, at the state's own
           [v_cfg v]; the boot chain holds the other half.  That is what lets
           [virtio_disk_init] run UNDER this invariant and still know
           deterministically which configuration it has programmed so far --
           the device never writes [v_cfg] ([virtio_req_step_cfg], and the
           whole not-live arm is unreachable from a device step anyway), so
           the pair is stable across device steps, and only a holder of BOTH
           halves can move it.  At the live flip the halves rejoin into the
           exclusive fraction [disk_cfg_set] consumes, which is where the
           persistent [disk_cfg] of the live arm is minted. *)
        disk_cfg_is γ (DfracOwn (1/2)) (v_cfg v) ∗
        (* THE RING COUNTERS ARE PINNED AT ZERO.  A device that is not live
           makes no step at all ([virtio_req_step_not_live]), and a device
           BECOMES not-live only through the reset command, which zeroes both
           counters ([virtio_reset]) -- so "not live" really does mean "has
           consumed nothing and produced nothing".  Recording it is what lets
           [virtio_disk_init] establish the live arm's [v_seen v = wrap16
           (vp_nc pr)] / [v_used_idx v = wrap16 (vp_nc pr)] at the flip: the
           driver zeroes the RINGS in memory, but only the invariant can tell
           it that the DEVICE's own counters agree with them. *)
        ⌜v_seen v = zero16⌝ ∗ ⌜v_used_idx v = zero16⌝ ∗
        (* ...and neither has anything LANDED: a device that is not live
           takes no sector step either ([virtio_sector_step_not_live]), and
           the reset that made it not live cleared the set
           ([virtio_reset_landed]).  Recording it is what lets the LIVE FLIP
           establish the live arm's "nothing pending means nothing landed". *)
        ⌜v_landed v = ∅⌝ ∗
        ghost_map_auth (dn_slot γ) 1 (∅ : gmap nat (vslot * gmap Arch.pa (bv 8))) ∗
        mono_nat_auth_own (dn_nc γ) 1 0%nat ∗
        ghost_var (dn_np γ) 1 0%nat)%I.

  Global Instance virtio_proto_timeless γ v : Timeless (virtio_proto γ v).
  Proof. rewrite /virtio_proto. destruct (virtio_live (v_cfg v)); apply _. Qed.

  (* ==================================================================== *)
  (* allocation and construction                                          *)
  (* ==================================================================== *)

  (* power-on: the queue is not live, nothing is owed (what adequacy runs).
     The caller keeps the config tracker's other half -- the boot chain needs
     it to program the queue from inside the invariant -- AND the two tokens
     the vdisk_lock's resource ([DiskInv.disk_res]) wants at birth but that
     [virtio_proto] itself never holds: the [dn_claim] ghost-map authority
     (empty: nothing is published at power-on) and the persistent lower bound
     [disk_done_lb _ 0] on the completed count.  Both are minted here because
     this is where the gnames are chosen; discarding them (as this lemma used
     to) left main() with no way to assemble [disk_res] for its [newlock].

     ERA-FRESH THROUGHOUT, AND THE IMAGE IS CONSTRUCTED, NOT ALLOCATED:
     [dn_img] is the AMBIENT ERA's image gname [disk_img_name], whose map the
     POWER THREAD minted at this boot, at the preserved disk content, handing
     the full fragments to the boot client ([RiscvAdequacy.power_boot_res];
     claude-notes/design/fs-log.md, stage 4).  Allocating a second map here
     would be unusable -- the auth [state_interp] holds, hence the one
     [virtio_proto_step] updates, is the era's. *)
  Lemma disk_ghosts_alloc (gd : nat) (v : virtio_state) :
    virtio_live (v_cfg v) = false ->
    v_seen v = zero16 -> v_used_idx v = zero16 -> v_landed v = ∅ ->
    ⊢ |==> ∃ γ : disk_names,
        (* the image name IS the era's: this is what lets the device thread
           identify the auth [state_interp] hands it with the fragments this
           invariant holds ([virtio_proto_step]). *)
        ⌜dn_img γ = disk_img_name⌝ ∗
        virtio_proto γ v ∗ disk_cfg_is γ (DfracOwn (1/2)) (v_cfg v) ∗
        ghost_map_auth (dn_claim γ) 1 (∅ : gmap nat dclaim) ∗
        disk_done_lb γ 0%nat ∗
        (* THE CRASH-PERMIT CHANNEL, empty: nothing is in flight at power-on,
           so no permit is owed.  Handed out as the BODY (not the invariant)
           because [WpUart.dev_inv_alloc] is what seals it, beside
           [disk_inv].  [gd] is the ERA's generation: the channel only ever
           holds permits its own era authored (PermInv.v). *)
        perm_inv_body gd (dn_perm γ).
  Proof.
    intros Hlive Hsn Hui Hld.
    iMod (ghost_map_alloc_empty (K:=nat)
            (V:=(vslot * gmap Arch.pa (bv 8))%type)) as (gslot) "Hslot".
    iMod (mono_nat_own_alloc 0) as (gnc) "[Hnc Hlb]".
    iMod (ghost_var_alloc 0%nat) as (gnp) "Hnp".
    iMod (ghost_map_alloc_empty (K:=nat) (V:=dclaim)) as (gclaim) "Hclaim".
    iMod (disk_cfg_alloc (v_cfg v)) as (gcfg) "Hcfg".
    iMod (perm_ghost_alloc gd) as (gperm) "Hperm".
    iDestruct (disk_cfg_is_split
                 (DiskNames disk_img_name gslot gnc gnp gclaim gcfg gperm)
                 (v_cfg v) with "[Hcfg]") as "[Hcfg1 Hcfg2]".
    { rewrite /disk_cfg_is. cbn [dn_cfg]. iExact "Hcfg". }
    iModIntro.
    iExists (DiskNames disk_img_name gslot gnc gnp gclaim gcfg gperm).
    iSplitR; [iPureIntro; reflexivity|].
    iFrame "Hcfg2".
    rewrite /disk_done_lb. cbn [dn_nc dn_claim dn_perm].
    iFrame "Hclaim Hlb Hperm".
    rewrite /virtio_proto.
    cbn [dn_img dn_slot dn_nc dn_np dn_claim dn_cfg dn_perm].
    rewrite Hlive.
    iSplitL "Hcfg1"; [iExact "Hcfg1"|].
    iSplitR; [iPureIntro; exact Hsn|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hld|].
    iFrame "Hslot Hnc Hnp".
  Qed.

  (* the live protocol, over an ABSTRACT configuration: the whole content of
     [virtio_proto_intro] with the [virtio_init_cfg] noise factored out *)
  Lemma virtio_proto_intro_gen (γ : disk_names) (v1 : virtio_state)
      (c : virtio_cfg) :
    v_cfg v1 = c ->
    virtio_live c = true ->
    vc_qnum c = Z_to_bv 32 8 ->
    virtio_pages_aligned c ->
    avail_idx_dom c ## used_page_pas c ->
    v_seen v1 = wrap16 0 ->
    v_used_idx v1 = wrap16 0 ->
    (* the empty landed set the not-live arm was recording all along *)
    v_landed v1 = ∅ ->
    disk_cfg γ c -∗
    ghost_map_auth (dn_slot γ) 1 (∅ : gmap nat (vslot * gmap Arch.pa (bv 8))) -∗
    mono_nat_auth_own (dn_nc γ) 1 0%nat -∗
    ghost_var (dn_np γ) (1/2) 0%nat -∗
    phys_word2 (avail_idx_pa c) (wrap16 0) -∗
    phys_list (vc_used c) (replicate 4096 byte_zero) -∗
    virtio_proto γ v1.
  Proof.
    intros Hcfg Hlive Hqnum Hal Hdisj Hseen Hui Hld.
    iIntros "#Hcfgp Hslot Hnc Hnp Hidx Hpage".
    assert (H4k : Z.of_nat 4096 < 18446744073709551616) by (rewrite z4096; lia).
    rewrite phys_word2_map (phys_list_replicate (vc_used c) 4096 byte_zero H4k).
    iAssert (dma_own (vinit_dma c)) with "[Hidx Hpage]" as "Hdma".
    { rewrite /vinit_dma /dma_own.
      rewrite (big_sepM_union (fun a b => phys_pointsto a (DfracOwn 1) b) _ _
                 (vinit_dma_disj c Hdisj)).
      iFrame "Hidx Hpage". }
    rewrite /virtio_proto.
    rewrite Hcfg Hlive.
    iExists vproto0, (vinit_dma c).
    rewrite vp_spins_init.
    iFrame "Hcfgp Hdma Hslot Hnc Hnp".
    iSplitR; [iPureIntro; apply vinit_dma_ctl|].
    iSplitR.
    { iPureIntro. rewrite vinit_dma_dom.
      apply vproto_ok_init; [exact Hqnum | exact Hlive | exact Hdisj]. }
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact (vinit_dma_uidx c Hdisj)|].
    iSplitR; [iPureIntro; intros _; exact Hld|].
    assert (Hpe : vp_pend vproto0 = (∅ : gmap nat vslot)) by reflexivity.
    assert (Hde : vp_done vproto0 = (∅ : gmap nat vslot)) by reflexivity.
    rewrite Hpe Hde !big_sepM_empty. iSplit; done.
  Qed.

  (* [zero16] and [wrap16 0] are the same halfword; the not-live arm speaks the
     model's vocabulary and the live arm the queue protocol's. *)
  Lemma zero16_wrap16 : zero16 = wrap16 0%nat.
  Proof. reflexivity. Qed.

  (* THE LIVE FLIP.  This is the transition [virtio_disk_init] performs at its
     LAST MMIO write (STATUS |= DRIVER_OK -- the write that makes
     [virtio_live] true): the freshly-zeroed avail-index bytes and the zeroed
     used page are paid in as the DMA lease, nothing is pending, the publisher
     token comes out for the vdisk_lock's resource, and the configuration the
     driver programmed is FROZEN into the persistent [disk_cfg] that
     [DiskInv.disk_geom] is built on.

     [v1] is given by PROJECTIONS rather than as a literal [VirtioState]: at
     the flip the driver knows the write is config-only (so the counters ride
     through unchanged) but knows nothing about [v_isr], which the live arm
     does not mention.  The counters being ZERO is read off the not-live arm,
     which is exactly what that arm records it for.  NOTHING is said about
     [v_disk]: since the image auth left this invariant for the fixed layer
     (crash.md), the flip has nothing to re-tie. *)
  Lemma virtio_proto_intro (γ : disk_names) (v0 v1 : virtio_state)
      (pd pav pu : Arch.pa) :
    virtio_live (v_cfg v0) = false ->
    v_cfg v1 = virtio_init_cfg pd pav pu ->
    v_seen v1 = v_seen v0 -> v_used_idx v1 = v_used_idx v0 ->
    v_landed v1 = v_landed v0 ->
    virtio_pages_aligned (virtio_init_cfg pd pav pu) ->
    avail_idx_dom (virtio_init_cfg pd pav pu)
      ## used_page_pas (virtio_init_cfg pd pav pu) ->
    virtio_proto γ v0 -∗
    (* the boot chain's half of the config tracker: it is what recombines
       with the invariant's half into the exclusive fraction the freeze needs,
       and holding it is what made the driver's knowledge of [v_cfg v0]
       deterministic all the way to this point. *)
    disk_cfg_is γ (DfracOwn (1/2)) (v_cfg v0) -∗
    phys_word2 (avail_idx_pa (virtio_init_cfg pd pav pu)) (wrap16 0) -∗
    phys_list pu (replicate 4096 byte_zero) -∗
    |==> virtio_proto γ v1 ∗ disk_pub γ 0 ∗
         disk_cfg γ (virtio_init_cfg pd pav pu).
  Proof.
    intros Hlive0 Hc1 Hsn Hui Hlde Hal Hdisj. iIntros "Hp Hmine Hidx Hpage".
    rewrite {1}/virtio_proto.
    rewrite Hlive0.
    iDestruct "Hp" as "(Hcfg & %Hsn0 & %Hui0 & %Hld0 & Hslot & Hnc & Hnp)".
    iDestruct (disk_cfg_is_join with "Hcfg Hmine") as "Hcfg".
    iMod (disk_cfg_set γ (v_cfg v0) (virtio_init_cfg pd pav pu) with "Hcfg")
      as "#Hcfg".
    iEval (rewrite -Qp.half_half) in "Hnp".
    iDestruct (ghost_var_split with "Hnp") as "[Hnp1 Hnp2]".
    iModIntro. rewrite /disk_pub. iFrame "Hnp2 Hcfg".
    assert (Hs1 : v_seen v1 = wrap16 0%nat)
      by (rewrite Hsn Hsn0; exact zero16_wrap16).
    assert (Hu1 : v_used_idx v1 = wrap16 0%nat)
      by (rewrite Hui Hui0; exact zero16_wrap16).
    assert (Hl1 : v_landed v1 = ∅) by (rewrite Hlde; exact Hld0).
    iApply (virtio_proto_intro_gen γ v1 (virtio_init_cfg pd pav pu)
              Hc1 (virtio_init_cfg_live pd pav pu) eq_refl Hal Hdisj Hs1 Hu1 Hl1
              with "Hcfg Hslot Hnc Hnp1 Hidx Hpage").
  Qed.

  (* THE PRE-FLIP CONFIGURATION WRITE.  Each of the fourteen MMIO writes
     [virtio_disk_init] performs before the flip moves the invariant from [v]
     to [v'] while the queue stays not live -- and it can, because the
     not-live arm holds nothing but the config tracker's half, the counter
     facts and the three empty-protocol ghosts.  BOTH halves of the tracker
     move together, which is what keeps the driver's knowledge of what it has
     programmed so far deterministic. *)
  Lemma virtio_proto_cfg_write (γ : disk_names) (v v' : virtio_state)
      (c' : virtio_cfg) :
    virtio_live (v_cfg v) = false ->
    virtio_live c' = false ->
    v_cfg v' = c' ->
    v_seen v' = zero16 -> v_used_idx v' = zero16 -> v_landed v' = ∅ ->
    virtio_proto γ v -∗ disk_cfg_is γ (DfracOwn (1/2)) (v_cfg v) ==∗
    virtio_proto γ v' ∗ disk_cfg_is γ (DfracOwn (1/2)) c'.
  Proof.
    intros Hlive0 Hlive1 Hc1 Hsn Hui Hld. iIntros "Hp Hmine".
    rewrite {1}/virtio_proto.
    rewrite Hlive0.
    iDestruct "Hp" as "(Hcfg & _ & _ & _ & Hslot & Hnc & Hnp)".
    iDestruct (disk_cfg_is_join with "Hcfg Hmine") as "Hcfg".
    iMod (disk_cfg_is_move γ (v_cfg v) c' with "Hcfg") as "Hcfg".
    iDestruct (disk_cfg_is_split with "Hcfg") as "[Hcfg1 Hcfg2]".
    iModIntro. iFrame "Hcfg2".
    rewrite /virtio_proto.
    rewrite Hc1 Hlive1.
    iFrame "Hcfg1".
    iSplitR; [iPureIntro; exact Hsn|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hld|].
    iFrame "Hslot Hnc Hnp".
  Qed.

  (* ...and what the driver READS off the arm without consuming it: while the
     queue is not live, the configuration is the one the tracker's other half
     names.  This is the identification every MMIO access performs when it
     opens [disk_inv] -- and it is also how the LIVE arm is refuted, since
     that arm exports the persistent [disk_cfg γ (v_cfg v)] which agrees with
     the caller's half just as well. *)
  Lemma virtio_proto_cfg_agree (γ : disk_names) (v : virtio_state)
      (c : virtio_cfg) :
    virtio_proto γ v -∗ disk_cfg_is γ (DfracOwn (1/2)) c -∗ ⌜v_cfg v = c⌝.
  Proof.
    iIntros "Hp Hmine". rewrite /virtio_proto.
    destruct (virtio_live (v_cfg v)).
    - iDestruct "Hp" as (pr dma) "(#Hcfg & _)".
      iApply (disk_cfg_is_agree with "Hcfg Hmine").
    - iDestruct "Hp" as "(Hcfg & _)".
      iApply (disk_cfg_is_agree with "Hcfg Hmine").
  Qed.

  (* THE LIVE-ARM REFUTATION, and the not-live arm's whole pure content in one
     accessor.  A driver that knows its tracked configuration is not live --
     [virtio_disk_init] from its precondition, and thereafter from the
     configuration it has itself programmed -- learns, at every opening of
     [disk_inv], that the invariant is in the not-live arm and hence that the
     device's two ring counters are still zero.  The refutation costs nothing:
     the LIVE arm exports the persistent [disk_cfg γ (v_cfg v)], which
     dfrac-agrees with the caller's half just as the not-live arm's own half
     does, so [v_cfg v = c] either way -- and then [virtio_live c = false]
     contradicts the live arm's own guard. *)
  Lemma virtio_proto_not_live_cfg (γ : disk_names) (v : virtio_state)
      (c : virtio_cfg) :
    virtio_live c = false ->
    virtio_proto γ v -∗ disk_cfg_is γ (DfracOwn (1/2)) c -∗
    ⌜v_cfg v = c /\ v_seen v = zero16 /\ v_used_idx v = zero16
     /\ v_landed v = ∅⌝.
  Proof.
    iIntros (Hlive) "Hp Hmine". rewrite /virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hl.
    - iDestruct "Hp" as (pr dma) "(#Hcfg & _)".
      iDestruct (disk_cfg_is_agree with "Hcfg Hmine") as %Hc.
      rewrite Hc Hlive in Hl. discriminate.
    - iDestruct "Hp" as "(Hcfg & %Hsn & %Hui & %Hld & _)".
      iDestruct (disk_cfg_is_agree with "Hcfg Hmine") as %Hc.
      iPureIntro. split_and!; [exact Hc | exact Hsn | exact Hui | exact Hld].
  Qed.

  (* ==================================================================== *)
  (* stability: MMIO writes that keep cfg / seen / used_idx                *)
  (* ==================================================================== *)

  (* THE LANDED SET IS PART OF THE PROTOCOL NOW (sector-atomic-disk.md): an
     in-flight write's landed sectors decide which of its permits are still
     pending, so a store that carried the protocol across on cfg/seen/used
     alone has to leave [v_landed] alone too.  Both stores the live driver
     makes do ([VirtioModel.virtio_write_landed] at [vio_cfg_stable]). *)
  Lemma virtio_proto_stable (γ : disk_names) (v v' : virtio_state) :
    v_cfg v' = v_cfg v -> v_seen v' = v_seen v ->
    v_used_idx v' = v_used_idx v -> v_landed v' = v_landed v ->
    virtio_proto γ v -∗ virtio_proto γ v'.
  Proof.
    intros Hc Hs Hu Hl. rewrite /virtio_proto Hc Hs Hu Hl. iIntros "$".
  Qed.

  (* ==================================================================== *)
  (* the DEVICE-THREAD rules (drop-in for the old lease rules)            *)
  (* ==================================================================== *)

  Lemma virtio_proto_not_stalled (m : gmap Arch.pa (bv 8)) (v : virtio_state)
      (mv : vmem) (γ : disk_names) :
    mem_view m mv ->
    gen_heap_interp m -∗ virtio_proto γ v -∗ ⌜virtio_stalled v mv = false⌝.
  Proof.
    iIntros (Hview) "Hm Hp".
    rewrite /virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hlive.
    2:{ iPureIntro. exact (virtio_not_live_not_stalled v mv Hlive). }
    iDestruct "Hp" as (pr dma)
      "(Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & Hrest)".
    iDestruct (dma_agree with "Hm Hdma") as %Hsub.
    iPureIntro.
    assert (Hctlm : vproto_ctl (v_cfg v) pr ⊆ m)
      by (etransitivity; [exact Hctl | exact Hsub]).
    apply (virtio_queue_not_stalled v (vproto_ctl (v_cfg v) pr) (dom dma)
             (set_map wrap16 (dom (vp_pend pr))) (wrap16 (vp_np pr)) mv).
    - rewrite Hseen. exact (vproto_flat (v_cfg v) pr (dom dma) Hok).
    - exact (mem_view_subseteq _ m mv Hctlm Hview).
  Qed.

  (* THE DMA COMPLETION -- the one step in the whole machine that moves
     [v_disk], and hence the one place the era's image auth
     ([RiscvPtsto.disk_dur_interp], handed over by [RiscvExec.wp_disk_step])
     is updated.  It travels as an explicit premise+return rather than inside
     [virtio_proto]: the auth is pinned to the machine's own [v_disk], so it
     belongs to whoever is stepping the machine (claude-notes/design/crash.md).

     IT IS AN ACCESSOR OVER THE CRASH-PERMIT CHANNEL.  The completing slot
     parked a [perm_pend] token ([slot_pend_res]); this lemma hands that
     token OUT and demands the SPENT one ([perm_done] at the same key) back,
     which is exactly the shape [WpUart.wp_disk_loop] needs: between the two
     it opens [crashN] and [PermInv.permN] and runs the client's view shift
     on the crash predicate, at the very instant the durable image changes.
     The key [kq] is EXISTENTIAL here because the caller does not know, and
     does not want to know, which request completed or in which direction --
     permits are uniform, so there is nothing to case-split on.  The auth
     handoff ([disk_img_auth] in, updated out) is unchanged; it simply rides
     the close-wand now. *)
  Lemma virtio_proto_step (γ : disk_names) (v : virtio_state)
      (m : gmap Arch.pa (bv 8)) (mv : vmem) (v' : virtio_state)
      (w : gmap Arch.pa (bv 8)) :
    mem_view m mv ->
    virtio_req_step v mv = Some (v', w) ->
    gen_heap_interp m -∗ disk_img_auth (dn_img γ) (v_disk v) -∗
    virtio_proto γ v ==∗
      ∃ (kq : nat * gname) (wr : disk_wr),
        (* THE COMPLETION MOVES NO DISK BYTE (sector-atomic-disk.md): every
           sector of an OUT request's data landed at its own earlier step, so
           the index here is [None] in BOTH directions and the cell is at the
           sequential permit's LEAF -- nothing left to land. *)
        ⌜v_disk v' = wr_apply None (v_disk v)⌝ ∗
        perm_pend (dn_perm γ) kq wr ∅ ∗
        (perm_done (dn_perm γ) kq wr -∗
           gen_heap_interp (w ∪ m) ∗ disk_img_auth (dn_img γ) (v_disk v') ∗
           virtio_proto γ v').
  Proof.
    iIntros (Hview Hstep) "Hm Hauth Hp".
    iDestruct "Hauth" as (dmap) "[Hauth %Hdv]".
    rewrite {1}/virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { exfalso. rewrite (virtio_req_step_not_live v mv Hlive) in Hstep.
      discriminate. }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hlde &
        Hslot & Hnc & Hnp & Hpend & Hdone)".
    iDestruct (dma_agree with "Hm Hdma") as %Hsub.
    assert (Hctlm : vproto_ctl (v_cfg v) pr ⊆ m)
      by (etransitivity; [exact Hctl | exact Hsub]).
    assert (Hvctl : mem_view (vproto_ctl (v_cfg v) pr) mv)
      by exact (mem_view_subseteq _ m mv Hctlm Hview).
    destruct (vproto_step_det (v_cfg v) pr (dom dma) v mv v' w
                Hok eq_refl Hseen Hvctl Hstep)
      as (sl & pin & Hsl & Hpin & Hlt & Hslotok & Hvpin & Hsdone & Hv1 & Hw1).
    subst v' w. rewrite Hui.
    (* the pure protocol facts about the slot the device is completing *)
    pose proof (vproto_pend_slot pr _ _ Hsl) as Hs.
    pose proof (vpo_standing _ _ _ Hok _ sl pin Hs Hpin) as Hstand.
    pose proof (vpo_qnum _ _ _ Hok) as Hqnum.
    assert (Hwrpage : slot_wr sl ## used_page_pas (v_cfg v)).
    { apply (gset_disj_mono (slot_wr sl) (slot_fp sl pin)
               (used_page_pas (v_cfg v))
               (avail_idx_dom (v_cfg v) ∪ used_page_pas (v_cfg v)));
        [ apply slot_fp_wr | apply union_subseteq_r | exact Hstand ]. }
    destruct (vslot_writes_dom (v_cfg v) pr (dom dma) sl pin
                (wrap16 (vp_nc pr)) (v_disk v) Hok Hsl Hpin) as [HwD Hwctl].
    assert (HwDdma : dom (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl)
                     ⊆ dom dma).
    { etransitivity; [exact HwD|]. apply union_least.
      - etransitivity; [ apply slot_fp_wr
                       | exact (vpo_fp_D _ _ _ Hok _ sl pin Hs Hpin) ].
      - exact (vpo_used_D _ _ _ Hok). }
    (* THE COMPLETING SLOT.  Its disk fragments do not MOVE here -- every
       sector of an OUT request landed at its own earlier step -- so all this
       block does is read off what they already say: the block holds the
       payload, because [virtio_sectors_done] says every sector landed and
       [vs_torn] says a landed sector holds the payload. *)
    iDestruct (big_sepM_delete _ (vp_pend pr) (vp_nc pr) sl Hsl with "Hpend")
      as "[Hslres Hpend]".
    rewrite pend_landed_head.
    iDestruct "Hslres" as (bs)
      "(%Hbslen & %Hbspin & %Hbstorn & Hbs & Hpend0)".
    pose proof (vslot_vreq_nsectors (v_cfg v) (vp_nc pr) sl pin mv Hslotok Hvpin)
      as Hns.
    assert (Hall : forall i, (i < wr_nsectors (vs_wr sl))%nat -> i ∈ v_landed v).
    { intros i Hi.
      apply (proj1 (virtio_sectors_done_spec v (vs_req sl)) Hsdone).
      rewrite Hns. exact Hi. }
    assert (Hout' : bs = vs_data sl).
    { destruct (vs_is_out sl) eqn:Hout; [| exact (Hbspin eq_refl) ].
      pose proof (vslot_data_len (v_cfg v) (vp_nc pr) sl pin Hslotok Hout) as Hdl.
      apply (vs_torn_full sl (v_landed v) bs Hbslen Hdl); [| exact Hbstorn ].
      intros i Hi. apply Hall.
      rewrite -Hns (vslot_nsectors_out sl Hout). exact Hi. }
    iDestruct (disk_bytes_read γ dmap (v_disk v) (vs_sector_off sl) bs Hdv
                 with "Hauth Hbs") as %Hrd.
    assert (Hin' : vs_is_out sl = false ->
              disk_read (v_disk v) (vs_sector_off sl) (vs_len sl) = bs)
      by (intros _; rewrite <- Hbslen; exact Hrd).
    (* ...so the request's channel entry has nothing left to land: its cell
       is at the LEAF, the completion's own identity permit. *)
    assert (Htodo : vs_todo sl (v_landed v) = ∅)
      by exact (vs_todo_done sl (v_landed v) Hall).
    rewrite Htodo.
    assert (Hdv' : disk_view dmap (v_disk (vslot_post v sl)))
      by (rewrite vslot_post_disk; exact Hdv).
    (* the byte lease and the counters *)
    iMod (dma_update _ m dma HwDdma with "Hm Hdma") as "[Hm Hdma]".
    assert (Hle : (vp_nc pr <= S (vp_nc pr))%nat) by lia.
    iMod (mono_nat_own_update (S (vp_nc pr)) Hle with "Hnc") as "[Hnc _]".
    (* the frames: every OTHER done record survives *)
    assert (Hmono : forall k x, vp_done pr !! k = Some x ->
              slot_done_res γ (v_cfg v) dma k x
              ⊢ slot_done_res γ (v_cfg v)
                  (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl ∪ dma)
                  k x).
    { intros k x Hk. apply bi.wand_entails.
      pose proof (vproto_done_slot (v_cfg v) pr (dom dma) k x Hok Hk) as Hks.
      assert (Hkpin : exists pinq, vp_pin pr !! k = Some pinq).
      { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
        apply elem_of_dom. exists x. exact Hks. }
      destruct Hkpin as [pinq Hpinq].
      assert (Hkne : k ≠ vp_nc pr).
      { intro Hc. rewrite Hc in Hk.
        pose proof (vpo_done_lt _ _ _ Hok (vp_nc pr) (elem_of_dom_2 _ _ _ Hk)).
        lia. }
      pose proof (vpo_fp_disj _ _ _ Hok k (vp_nc pr) x sl pinq pin
                    Hkne Hks Hpinq Hs Hpin) as Hfpd.
      pose proof (vpo_standing _ _ _ Hok k x pinq Hks Hpinq) as Hstq.
      assert (Hmod : Z.of_nat k `mod` 8 ≠ Z.of_nat (vp_nc pr) `mod` 8)
        by exact (vproto_mod8_ne (v_cfg v) pr (dom dma) k (vp_nc pr) x sl
                    pinq pin Hok Hkne Hks Hpinq Hs Hpin).
      apply slot_done_res_mono.
      - intros j Hj. apply lookup_union_r.
        exact (vslot_writes_none_other_elem (v_cfg v) (v_disk v) sl
                 (vp_nc pr) k j Hqnum Hwrpage Hmod Hj).
      - apply lookup_union_r.
        apply vslot_writes_none_of_page; [exact Hqnum | | ].
        + intro Hc. apply (proj1 (elem_of_disjoint _ _) Hfpd (vr_status (vs_req x))).
          * apply slot_fp_wr. unfold slot_wr.
            apply elem_of_union_l, elem_of_singleton. reflexivity.
          * apply slot_fp_wr. exact Hc.
        + intro Hc. apply (proj1 (elem_of_disjoint _ _) Hstq (vr_status (vs_req x))).
          * apply slot_fp_wr. unfold slot_wr.
            apply elem_of_union_l, elem_of_singleton. reflexivity.
          * apply elem_of_union_r. exact Hc.
      - intros Hox j Hj. apply lookup_union_r.
        apply vslot_writes_none_of_page; [exact Hqnum | | ].
        + intro Hc. apply (proj1 (elem_of_disjoint _ _) Hfpd
                             (pa_add (vr_buf (vs_req x)) j)).
          * apply slot_fp_wr. unfold slot_wr. rewrite Hox.
            apply elem_of_union_r, pa_range_intro. exact Hj.
          * apply slot_fp_wr. exact Hc.
        + intro Hc. apply (proj1 (elem_of_disjoint _ _) Hstq
                             (pa_add (vr_buf (vs_req x)) j)).
          * apply slot_fp_wr. unfold slot_wr. rewrite Hox.
            apply elem_of_union_r, pa_range_intro. exact Hj.
          * apply elem_of_union_r. exact Hc. }
    (* rebuild, AS THE ACCESSOR: the completing slot's pending token goes
       out, and the caller owes the spent one back at the same key. *)
    iModIntro. iExists (vs_perm sl), (vs_wr sl).
    iSplitR; [iPureIntro; apply vslot_post_wr|].
    iFrame "Hpend0". iIntros "Hdone0".
    iFrame "Hm".
    iSplitL "Hauth".
    { iExists dmap. iFrame "Hauth". iPureIntro. exact Hdv'. }
    rewrite /virtio_proto vslot_post_cfg vslot_post_landed Hlive.
    iExists (vproto_step_state pr sl),
      (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl ∪ dma).
    rewrite (vp_spins_step pr sl Hsl) vps_nc vps_np vps_pend vps_done.
    iFrame "Hcfg Hdma Hslot Hnc Hnp".
    (* the pure conjuncts *)
    iSplitR.
    { iPureIntro. rewrite (vproto_step_ctl (v_cfg v) pr sl).
      exact (virtio_ctl_union _ _ _ Hwctl Hctl). }
    iSplitR.
    { iPureIntro. rewrite (dom_union_sub _ dma HwDdma).
      exact (vproto_ok_step (v_cfg v) pr (dom dma) sl Hok Hsl). }
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR.
    { iPureIntro. rewrite vslot_post_seen Hseen. symmetry. apply wrap16_S. }
    iSplitR.
    { iPureIntro. rewrite vslot_post_uidx Hui. symmetry. apply wrap16_S. }
    iSplitR.
    { iPureIntro.
      apply read_bytes_of_list. intros j Hj.
      assert (Hj2 : (j < 2)%nat) by lia.
      apply lookup_union_Some_l.
      rewrite (vslot_writes_idx (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl j
                 Hqnum Hj2 Hwrpage).
      rewrite <- wrap16_S. reflexivity. }
    iSplitR; [iPureIntro; intros _; reflexivity|].
    (* the pending map lost [nc] -- and the landed set is empty again, so the
       slots still pending are back to "nothing landed" *)
    assert (Hpmono : forall k x, delete (vp_nc pr) (vp_pend pr) !! k = Some x ->
              slot_pend_res γ (pend_landed pr (v_landed v) k) x
              ⊢ slot_pend_res γ (pend_landed (vproto_step_state pr sl) ∅ k) x).
    { intros k x Hk. apply bi.wand_entails.
      apply lookup_delete_Some in Hk as [Hne _].
      rewrite (pend_landed_other pr (v_landed v) k (fun e => Hne (eq_sym e)))
              (pend_landed_empty (vproto_step_state pr sl) k). iIntros "$". }
    iSplitL "Hpend".
    { iApply (big_sepM_mono _ _ _ Hpmono). iExact "Hpend". }
    assert (Hdnone : vp_done pr !! vp_nc pr = None).
    { apply not_elem_of_dom. intro Hc.
      pose proof (vpo_done_lt _ _ _ Hok _ Hc). lia. }
    rewrite (big_sepM_insert _ (vp_done pr) (vp_nc pr) sl Hdnone).
    iSplitL "Hbs Hdone0".
    { iExists bs. rewrite /slot_perms_done. iFrame "Hbs Hdone0".
      iPureIntro. split_and!.
      - exact Hbslen.
      - exact Hout'.
      - apply read_bytes_of_list. intros j Hj.
        assert (Hj2 : (j < 4)%nat) by lia.
        apply lookup_union_Some_l.
        rewrite <- (used_elem_at_wrap (v_cfg v) (vp_nc pr)).
        exact (vslot_writes_elem (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl j
                 Hqnum Hj2 Hwrpage).
      - apply lookup_union_Some_l.
        apply vslot_writes_status. exact (spo_stat _ _ _ _ Hslotok).
      - intro Hin. apply read_byte_list_intro; [exact Hbslen|].
        intros j b Hj. apply lookup_union_Some_l.
        apply (vslot_writes_buf (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl j b Hin).
        rewrite (Hin' Hin). exact Hj. }
    iApply (big_sepM_mono _ _ _ Hmono). iExact "Hdone".
  Qed.

  (* THE SECTOR LANDING -- the step that actually moves the durable image
     (claude-notes/completed/sector-atomic-disk.md).  512 bytes of the head
     request's data reach the disk and NOTHING else moves: no memory write, no
     used-ring entry, no interrupt, and the device does not advance to the
     next available-ring entry.  So this -- and no longer the completion -- is
     the linearization point of a disk write, which is why
     [WpUart.wp_disk_loop] opens [crashN] in THIS arm and no other.

     Same accessor shape as [virtio_proto_step]: the landing sector's PENDING
     token goes out, its SPENT one is owed back at the same key, and the
     write identity handed over is the sector's own slice
     [wr_sector (vs_wr sl) i] -- so the client's view shift is about exactly
     the 512 bytes that just became durable. *)
  Lemma virtio_proto_sector_step (γ : disk_names) (v : virtio_state)
      (m : gmap Arch.pa (bv 8)) (mv : vmem) (i : nat) (v' : virtio_state) :
    mem_view m mv ->
    virtio_sector_step v mv i = Some v' ->
    gen_heap_interp m -∗ disk_img_auth (dn_img γ) (v_disk v) -∗
    virtio_proto γ v ==∗
      ∃ (kq : nat * gname) (wr : disk_wr) (todo : gset nat),
        ⌜i ∈ todo⌝ ∗
        ⌜v_disk v' = wr_apply (wr_sector wr i) (v_disk v)⌝ ∗
        perm_pend (dn_perm γ) kq wr todo ∗
        (perm_pend (dn_perm γ) kq wr (todo ∖ {[ i ]}) -∗
           gen_heap_interp m ∗ disk_img_auth (dn_img γ) (v_disk v') ∗
           virtio_proto γ v').
  Proof.
    iIntros (Hview Hstep) "Hm Hauth Hp".
    iDestruct "Hauth" as (dmap) "[Hauth %Hdv]".
    rewrite {1}/virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { exfalso. rewrite (virtio_sector_step_not_live v mv i Hlive) in Hstep.
      discriminate. }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hlde &
        Hslot & Hnc & Hnp & Hpend & Hdone)".
    iDestruct (dma_agree with "Hm Hdma") as %Hsub.
    assert (Hctlm : vproto_ctl (v_cfg v) pr ⊆ m)
      by (etransitivity; [exact Hctl | exact Hsub]).
    assert (Hvctl : mem_view (vproto_ctl (v_cfg v) pr) mv)
      by exact (mem_view_subseteq _ m mv Hctlm Hview).
    destruct (vproto_sector_det (v_cfg v) pr (dom dma) v mv i v'
                Hok eq_refl Hseen Hvctl Hstep)
      as (sl & pin & Hsl & Hpin & Hlt & Hslotok & Hout & Hilt & Hnl & Hv1).
    (* the landing slot's pending resource *)
    iDestruct (big_sepM_delete _ (vp_pend pr) (vp_nc pr) sl Hsl with "Hpend")
      as "[Hslres Hpend]".
    rewrite pend_landed_head.
    iDestruct "Hslres" as (bs)
      "(%Hbslen & %Hbspin & %Hbstorn & Hbs & Hpend0)".
    (* the sector is one of the ones still to land, so the request's cell is
       at a branch of the sequential permit and [i] is the branch taken *)
    assert (Hitd : i ∈ vs_todo sl (v_landed v))
      by exact (vs_todo_in sl (v_landed v) i Hilt Hnl).
    (* the disk fragments move by exactly this sector *)
    pose proof (vslot_data_len (v_cfg v) (vp_nc pr) sl pin Hslotok Hout) as Hdl.
    iDestruct (disk_bytes_read γ dmap (v_disk v) (vs_sector_off sl) bs Hdv
                 with "Hauth Hbs") as %Hrd.
    rewrite Hbslen in Hrd.
    set (bs' := disk_read (wr_apply (wr_sector (vs_wr sl) i) (v_disk v))
                          (vs_sector_off sl) (vs_len sl)).
    assert (Hlen' : length bs' = length bs)
      by (unfold bs'; rewrite vq_disk_read_length Hbslen; reflexivity).
    iMod (disk_bytes_update γ dmap (vs_sector_off sl) bs bs' Hlen'
            with "Hauth Hbs") as (dmap') "(Hauth & Hbs & %Hupd)".
    assert (Hdisk' : disk_write (v_disk v) (vs_sector_off sl) bs'
                     = v_disk v').
    { unfold bs'. rewrite (vs_sector_image sl (v_disk v) i Hdl).
      rewrite Hv1. reflexivity. }
    assert (Hdv' : disk_view dmap' (v_disk v'))
      by (rewrite <- Hdisk'; exact (Hupd (v_disk v) Hdv)).
    assert (Htorn' : vs_torn sl ({[ i ]} ∪ v_landed v) bs').
    { unfold bs'. apply (vs_torn_sector sl (v_disk v) (v_landed v) i Hout Hdl).
      rewrite Hrd. exact Hbstorn. }
    iModIntro. iExists (vs_perm sl), (vs_wr sl), (vs_todo sl (v_landed v)).
    iSplitR; [iPureIntro; exact Hitd|].
    iSplitR; [iPureIntro; rewrite Hv1; reflexivity|].
    iFrame "Hpend0". iIntros "Hpend0".
    rewrite -(vs_todo_step sl (v_landed v) i).
    iFrame "Hm".
    iSplitL "Hauth".
    { iExists dmap'. iFrame "Hauth". iPureIntro. exact Hdv'. }
    rewrite /virtio_proto Hv1.
    cbn [v_cfg v_isr v_seen v_used_idx v_disk v_landed].
    rewrite Hlive.
    iExists pr, dma. iFrame "Hcfg Hdma Hslot Hnc Hnp Hdone".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact Hok|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; intro Hc; exfalso; lia|].
    (* the pending map: the head slot's landed set grew, the others are
       still empty *)
    assert (Hpmono : forall k x, delete (vp_nc pr) (vp_pend pr) !! k = Some x ->
              slot_pend_res γ (pend_landed pr (v_landed v) k) x
              ⊢ slot_pend_res γ (pend_landed pr ({[ i ]} ∪ v_landed v) k) x).
    { intros k x Hk. apply bi.wand_entails.
      apply lookup_delete_Some in Hk as [Hne _].
      rewrite (pend_landed_other pr (v_landed v) k (fun e => Hne (eq_sym e)))
              (pend_landed_other pr ({[ i ]} ∪ v_landed v) k
                 (fun e => Hne (eq_sym e))). iIntros "$". }
    iApply (big_sepM_delete _ (vp_pend pr) (vp_nc pr) sl Hsl).
    rewrite pend_landed_head.
    iSplitR "Hpend".
    { iExists bs'. iFrame "Hbs Hpend0". iPureIntro. split_and!.
      - rewrite Hlen'. exact Hbslen.
      - intro Hc. rewrite Hout in Hc. discriminate.
      - exact Htorn'. }
    iApply (big_sepM_mono _ _ _ Hpmono). iExact "Hpend".
  Qed.

  (* ==================================================================== *)
  (* driver operation 1: OBSERVE the published index (rw's avail-idx lhu) *)
  (* ==================================================================== *)

  Lemma virtio_proto_avail_idx_acc (γ : disk_names) (v : virtio_state) (np : nat) :
    virtio_proto γ v -∗ disk_pub γ np -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
    phys_word2 (avail_idx_pa (v_cfg v)) (wrap16 np) ∗
    (phys_word2 (avail_idx_pa (v_cfg v)) (wrap16 np) -∗
       virtio_proto γ v ∗ disk_pub γ np).
  Proof.
    iIntros "Hp Hpub". rewrite /virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & Hslot & Hnc & Hnp)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hlde &
        Hslot & Hnc & Hnp & Hpend & Hdone)".
    iDestruct (ghost_var_agree with "Hnp Hpub") as %Hnpeq.
    pose proof (vproto_ctl_idx (v_cfg v) pr (dom dma) Hok) as Hidx0.
    rewrite Hnpeq in Hidx0.
    pose proof (read_bytes_mono _ _ _ _ _ Hctl Hidx0) as Hread.
    assert (Hsub : range_map (avail_idx_pa (v_cfg v)) 2 (nth_byte (wrap16 np))
                     ⊆ dma).
    { apply range_map_sub; [lia|]. intros j Hj.
      apply (read_bytes_spec dma (avail_idx_pa (v_cfg v)) 2 (wrap16 np) Hread).
      lia. }
    iDestruct (dma_own_acc_same _ dma Hsub with "Hdma") as "[Hmm Hback]".
    rewrite !phys_word2_map.
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iSplitR; [iPureIntro; exact Hal|].
    iFrame "Hmm". iIntros "Hmm".
    iDestruct ("Hback" with "Hmm") as "Hdma".
    iFrame "Hpub". iExists pr, dma. iFrame "Hcfg Hdma Hslot Hnc Hnp Hpend Hdone".
    iPureIntro. split_and!; assumption.
  Qed.

  (* ==================================================================== *)
  (* driver operation 2: PUBLISH (rw's avail-idx sh, np -> np+1)          *)
  (* ==================================================================== *)

  (* The publisher supplies: the new slot's pin (as owned bytes -- their
     disjointness from the lease is by ownership), the writable footprint
     (status byte + a read request's buffer, any contents), and the disk
     fragments for the sector range.  The accessor exposes the index bytes;
     the close-wand takes them back UPDATED (the sh wrote wrap16 (S np)) and
     performs the protocol transition, minting the receipt. *)
  Lemma virtio_proto_publish_acc (γ : disk_names) (v : virtio_state)
      (np : nat) (sl : vslot) (pin wrb : gmap Arch.pa (bv 8)) :
    slot_pin_ok (v_cfg v) np sl pin ->
    dom wrb = slot_wr sl ->
    slot_wr sl ## dom pin ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    phys_map pin -∗ phys_map wrb -∗
    (* NOTHING HAS LANDED YET: a freshly published request has every one of
       its per-sector permits still pending. *)
    slot_pend_res γ ∅ sl -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    phys_word2 (avail_idx_pa (v_cfg v)) (wrap16 np) ∗
    (phys_word2 (avail_idx_pa (v_cfg v)) (wrap16 (S np)) ==∗
       virtio_proto γ v ∗ disk_pub γ (S np) ∗ disk_receipt γ np sl pin).
  Proof.
    intros Hslotok Hwrbdom Hwrpin.
    iIntros "Hp Hpub Hpin Hwrb Hpres".
    rewrite {1}/virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & Hslot & Hnc & Hnp)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hlde &
        Hslot & Hnc & Hnp & Hpend & Hdone)".
    iDestruct (ghost_var_agree with "Hnp Hpub") as %Hnpeq.
    iDestruct (dma_own_disj with "Hdma Hpin") as %Hpind.
    iDestruct (dma_own_disj with "Hdma Hwrb") as %Hwrbd.
    rewrite Hwrbdom in Hwrbd.
    iDestruct (phys_map_disj with "Hpin Hwrb") as %Hpw.
    apply map_disjoint_dom in Hpw.
    (* the window of the lease we hand out *)
    pose proof (vproto_ctl_idx (v_cfg v) pr (dom dma) Hok) as Hidx0.
    rewrite Hnpeq in Hidx0.
    pose proof (read_bytes_mono _ _ _ _ _ Hctl Hidx0) as Hread.
    assert (Hmmsub : range_map (avail_idx_pa (v_cfg v)) 2 (nth_byte (wrap16 np))
                       ⊆ dma).
    { apply range_map_sub; [lia|]. intros j Hj.
      apply (read_bytes_spec dma (avail_idx_pa (v_cfg v)) 2 (wrap16 np) Hread).
      lia. }
    assert (Hdomeq : dom (range_map (avail_idx_pa (v_cfg v)) 2
                            (nth_byte (wrap16 (S np))))
                     = dom (range_map (avail_idx_pa (v_cfg v)) 2
                              (nth_byte (wrap16 np))))
      by (rewrite !range_map_dom; reflexivity).
    assert (HdomMMS : dom (range_map (avail_idx_pa (v_cfg v)) 2
                             (nth_byte (wrap16 (S np)))) = avail_idx_dom (v_cfg v))
      by (rewrite range_map_dom; reflexivity).
    assert (HMMSdma : dom (range_map (avail_idx_pa (v_cfg v)) 2
                             (nth_byte (wrap16 (S np)))) ⊆ dom dma)
      by (rewrite Hdomeq; apply subseteq_dom; exact Hmmsub).
    iDestruct (dma_own_acc _ _ dma Hmmsub Hdomeq with "Hdma") as "[Hmm Hback]".
    rewrite !phys_word2_map.
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iFrame "Hmm". iIntros "Hmm".
    iDestruct ("Hback" with "Hmm") as "Hdma".
    (* the enlarged lease *)
    assert (Hun_dom : dom (range_map (avail_idx_pa (v_cfg v)) 2
                             (nth_byte (wrap16 (S np))) ∪ dma) = dom dma)
      by (apply dom_union_sub; exact HMMSdma).
    assert (Hd2 : wrb ##ₘ (range_map (avail_idx_pa (v_cfg v)) 2
                             (nth_byte (wrap16 (S np))) ∪ dma)).
    { apply map_disjoint_dom. rewrite Hun_dom Hwrbdom. exact Hwrbd. }
    assert (Hd1 : pin ##ₘ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
                             (nth_byte (wrap16 (S np))) ∪ dma))).
    { apply map_disjoint_dom. rewrite dom_union_L Hun_dom.
      apply gset_disj_union_r; [exact Hpw | exact Hpind]. }
    iAssert (dma_own (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
                             (nth_byte (wrap16 (S np))) ∪ dma))))
      with "[Hpin Hwrb Hdma]" as "Hdma".
    { rewrite /dma_own.
      rewrite (big_sepM_union (fun a b => phys_pointsto a (DfracOwn 1) b) _ _ Hd1).
      rewrite (big_sepM_union (fun a b => phys_pointsto a (DfracOwn 1) b) _ _ Hd2).
      iFrame "Hpin Hwrb Hdma". }
    (* the framing fact: everything old and outside the index field is intact *)
    assert (Hframe : forall x : Arch.pa, x ∈ dom dma ->
              x ∉ avail_idx_dom (v_cfg v) ->
              (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
                 (nth_byte (wrap16 (S np))) ∪ dma))) !! x = dma !! x).
    { intros x Hx Hnx.
      rewrite lookup_union_r.
      2:{ apply not_elem_of_dom. intro Hc.
          exact (proj1 (elem_of_disjoint _ _) Hpind x Hc Hx). }
      rewrite lookup_union_r.
      2:{ apply not_elem_of_dom. intro Hc. rewrite Hwrbdom in Hc.
          exact (proj1 (elem_of_disjoint _ _) Hwrbd x Hc Hx). }
      rewrite lookup_union_r; [reflexivity|].
      apply not_elem_of_dom. rewrite HdomMMS. exact Hnx. }
    (* the pure protocol surgery *)
    assert (Hslotok' : slot_pin_ok (v_cfg v) (vp_np pr) sl pin)
      by (rewrite Hnpeq; exact Hslotok).
    assert (Hfpd : slot_fp sl pin ## dom dma).
    { unfold slot_fp. apply gset_disj_union_l; [exact Hpind | exact Hwrbd]. }
    pose proof (vproto_ok_publish (v_cfg v) pr (dom dma) sl pin
                  Hok Hslotok' Hwrpin Hfpd) as Hok'.
    pose proof (vproto_publish_ctl (v_cfg v) pr (dom dma) sl pin Hok Hfpd) as Hctl'.
    rewrite Hnpeq in Hctl'.
    pose proof (pins_union_ctl (v_cfg v) pr (dom dma) Hok) as Hpuctl.
    assert (Hpudma : pins_union (vp_pin pr) ⊆ dma)
      by (etransitivity; [exact Hpuctl | exact Hctl]).
    assert (Hpudom : dom (pins_union (vp_pin pr)) ⊆ dom dma)
      by (apply subseteq_dom; exact Hpudma).
    (* ghost moves *)
    assert (Hslnone : vp_slots pr !! vp_np pr = None).
    { apply not_elem_of_dom. unfold vp_slots. rewrite dom_union_L. intro Hc.
      apply elem_of_union in Hc as [Hc|Hc].
      - rewrite (vpo_pend_dom _ _ _ Hok) in Hc. apply elem_of_set_seq in Hc. lia.
      - pose proof (vpo_done_lt _ _ _ Hok _ Hc).
        pose proof (vpo_ncnp _ _ _ Hok). lia. }
    assert (Hpendnone : vp_pend pr !! vp_np pr = None).
    { destruct (vp_pend pr !! vp_np pr) as [x|] eqn:Hc; [| reflexivity ].
      rewrite (vproto_pend_slot pr _ _ Hc) in Hslnone. discriminate. }
    iMod (ghost_map_insert (vp_np pr) (sl, pin) with "Hslot") as "[Hslot Hrec]";
      [ exact (vp_spins_none pr (vp_np pr) Hslnone) |].
    iMod (ghost_var_update_halves (S np) with "Hnp Hpub") as "[Hnp Hpub]".
    (* rebuild *)
    iModIntro. iFrame "Hpub".
    rewrite /disk_receipt. rewrite Hnpeq. iFrame "Hrec".
    rewrite /virtio_proto Hlive.
    iExists (vproto_publish_state pr sl pin),
      (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
         (nth_byte (wrap16 (S np))) ∪ dma))).
    rewrite (vp_spins_publish pr sl pin) vpp_nc vpp_np vpp_pend vpp_done Hnpeq.
    iFrame "Hcfg Hdma Hslot Hnc Hnp".
    iSplitR.
    { iPureIntro. rewrite Hctl'. apply map_union_least.
      - rewrite (avail_idx_bytes_range (v_cfg v) (S np)).
        apply virtio_ctl_union.
        { apply gset_disj_sym. rewrite HdomMMS. apply gset_disj_sym.
          apply (gset_disj_sub_r _ _ (dom dma)); [| exact Hpind ].
          rewrite HdomMMS in HMMSdma. exact HMMSdma. }
        apply virtio_ctl_union.
        { apply gset_disj_sym. rewrite HdomMMS. apply gset_disj_sym.
          rewrite Hwrbdom.
          apply (gset_disj_sub_r _ _ (dom dma)); [| exact Hwrbd ].
          rewrite HdomMMS in HMMSdma. exact HMMSdma. }
        apply map_union_subseteq_l.
      - apply map_union_least; [ apply map_union_subseteq_l |].
        apply virtio_ctl_union.
        { apply gset_disj_sym.
          apply (gset_disj_sub_l _ (dom dma)); [ exact Hpudom |].
          apply gset_disj_sym. exact Hpind. }
        apply virtio_ctl_union.
        { apply gset_disj_sym. rewrite Hwrbdom.
          apply (gset_disj_sub_l _ (dom dma)); [ exact Hpudom |].
          apply gset_disj_sym. exact Hwrbd. }
        apply virtio_ctl_union.
        { rewrite HdomMMS. apply gset_disj_sym.
          apply (gset_disj_sub_r _ _ (avail_idx_dom (v_cfg v)
                   ∪ used_page_pas (v_cfg v)));
            [ apply union_subseteq_l
            | exact (pins_union_off_standing (v_cfg v) pr (dom dma) Hok) ]. }
        exact Hpudma. }
    iSplitR.
    { iPureIntro.
      assert (Hdd : dom (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
                      (nth_byte (wrap16 (S np))) ∪ dma)))
                    = dom dma ∪ slot_fp sl pin).
      { rewrite dom_union_L dom_union_L Hun_dom Hwrbdom. unfold slot_fp.
        apply gset_union_comm3. }
      rewrite Hdd. exact Hok'. }
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR.
    { iPureIntro. apply (read_bytes_transfer dma); [| exact Hridx].
      intros j Hj. assert (Hj2 : (j < 2)%nat) by lia.
      apply Hframe.
      - apply (vpo_used_D _ _ _ Hok). exact (used_idx_in_page (v_cfg v) j Hj2).
      - intro Hc. exact (proj1 (elem_of_disjoint _ _) (vpo_idx_used _ _ _ Hok)
                           _ Hc (used_idx_in_page (v_cfg v) j Hj2)). }
    (* NOTHING PENDING MEANS NOTHING LANDED, one publish later: the queue is
       no longer idle, so the conjunct is vacuous. *)
    iSplitR.
    { iPureIntro. intro Hc. exfalso.
      pose proof (vpo_ncnp _ _ _ Hok) as Hle. rewrite Hnpeq in Hle. lia. }
    (* the pending map gains [np]; the done records survive *)
    rewrite Hnpeq in Hpendnone.
    rewrite (big_sepM_insert _ (vp_pend pr) np sl Hpendnone).
    assert (Hnpland :
      pend_landed (vproto_publish_state pr sl pin) (v_landed v) np = ∅).
    { rewrite /pend_landed vpp_nc.
      destruct (bool_decide (np = vp_nc pr)) eqn:Hb; [|reflexivity].
      apply bool_decide_eq_true in Hb. apply Hlde. by rewrite Hnpeq Hb. }
    assert (Hpmono : forall k x, vp_pend pr !! k = Some x ->
              slot_pend_res γ (pend_landed pr (v_landed v) k) x
              ⊢ slot_pend_res γ
                  (pend_landed (vproto_publish_state pr sl pin) (v_landed v) k) x).
    { intros k x _. apply bi.wand_entails. rewrite /pend_landed vpp_nc.
      iIntros "$". }
    iSplitL "Hpres Hpend".
    { rewrite Hnpland. iFrame "Hpres".
      iApply (big_sepM_mono _ _ _ Hpmono). iExact "Hpend". }
    assert (Hmono : forall k x, vp_done pr !! k = Some x ->
              slot_done_res γ (v_cfg v) dma k x
              ⊢ slot_done_res γ (v_cfg v)
                  (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
                     (nth_byte (wrap16 (S np))) ∪ dma))) k x).
    { intros k x Hk. apply bi.wand_entails.
      pose proof (vproto_done_slot (v_cfg v) pr (dom dma) k x Hok Hk) as Hks.
      assert (Hkpin : exists pinq, vp_pin pr !! k = Some pinq).
      { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
        apply elem_of_dom. exists x. exact Hks. }
      destruct Hkpin as [pinq Hpinq].
      pose proof (vpo_standing _ _ _ Hok k x pinq Hks Hpinq) as Hstq.
      pose proof (vpo_fp_D _ _ _ Hok k x pinq Hks Hpinq) as HfpD.
      apply slot_done_res_mono.
      - intros j Hj. apply Hframe.
        + apply (vpo_used_D _ _ _ Hok).
          exact (used_elem_pa_in_page (v_cfg v) k j Hj).
        + intro Hc. exact (proj1 (elem_of_disjoint _ _) (vpo_idx_used _ _ _ Hok)
                             _ Hc (used_elem_pa_in_page (v_cfg v) k j Hj)).
      - assert (Hstin : vr_status (vs_req x) ∈ slot_fp x pinq).
        { apply slot_fp_wr. unfold slot_wr.
          apply elem_of_union_l, elem_of_singleton. reflexivity. }
        apply Hframe; [ exact (HfpD _ Hstin) |].
        intro Hc. exact (proj1 (elem_of_disjoint _ _) Hstq _ Hstin
                           (elem_of_union_l _ _ _ Hc)).
      - intros Hox j Hj.
        assert (Hbin : pa_add (vr_buf (vs_req x)) j ∈ slot_fp x pinq).
        { apply slot_fp_wr. unfold slot_wr. rewrite Hox.
          apply elem_of_union_r, pa_range_intro. exact Hj. }
        apply Hframe; [ exact (HfpD _ Hbin) |].
        intro Hc. exact (proj1 (elem_of_disjoint _ _) Hstq _ Hbin
                           (elem_of_union_l _ _ _ Hc)). }
    iApply (big_sepM_mono _ _ _ Hmono). iExact "Hdone".
  Qed.

  (* ==================================================================== *)
  (* driver operation 3: OBSERVE the used index (intr's used-idx lhu)     *)
  (* ==================================================================== *)

  (* The caller presents whatever completed-count lower bound it already has
     ([nr]); the accessor reports the current count [nc] ABOVE it, so two
     successive observations are comparable. *)
  Lemma virtio_proto_used_idx_acc (γ : disk_names) (v : virtio_state)
      (np nr : nat) :
    virtio_proto γ v -∗ disk_pub γ np -∗ disk_done_lb γ nr -∗
    ∃ nc : nat,
      ⌜(nr <= nc)%nat⌝ ∗
      ⌜(nc <= np)%nat⌝ ∗
      disk_cfg γ (v_cfg v) ∗
      ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
      disk_done_lb γ nc ∗
      phys_word2 (used_idx_pa (v_cfg v)) (wrap16 nc) ∗
      (phys_word2 (used_idx_pa (v_cfg v)) (wrap16 nc) -∗
         virtio_proto γ v ∗ disk_pub γ np).
  Proof.
    iIntros "Hp Hpub Hlb0". rewrite /virtio_proto /disk_pub /disk_done_lb.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & Hslot & Hnc & Hnp)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hlde &
        Hslot & Hnc & Hnp & Hpend & Hdone)".
    iDestruct (ghost_var_agree with "Hnp Hpub") as %Hnpeq.
    iDestruct (mono_nat_lb_own_valid with "Hnc Hlb0") as %[_ Hnr].
    iDestruct (mono_nat_lb_own_get with "Hnc") as "#Hlb".
    assert (Hsub : range_map (used_idx_pa (v_cfg v)) 2
                     (nth_byte (wrap16 (vp_nc pr))) ⊆ dma).
    { apply range_map_sub; [lia|]. intros j Hj.
      apply (read_bytes_spec dma (used_idx_pa (v_cfg v)) 2
               (wrap16 (vp_nc pr)) Hridx). lia. }
    iDestruct (dma_own_acc_same _ dma Hsub with "Hdma") as "[Hmm Hback]".
    iExists (vp_nc pr). rewrite !phys_word2_map.
    iSplitR; [iPureIntro; exact Hnr|].
    iSplitR.
    { iPureIntro. pose proof (vpo_ncnp _ _ _ Hok). lia. }
    iSplitR; [iExact "Hcfg"|]. iSplitR; [iPureIntro; exact Hal|].
    iFrame "Hlb Hmm". iIntros "Hmm".
    iDestruct ("Hback" with "Hmm") as "Hdma".
    iFrame "Hpub". iExists pr, dma. iFrame "Hcfg Hdma Hslot Hnc Hnp Hpend Hdone".
    iPureIntro. split_and!; assumption.
  Qed.

  (* ==================================================================== *)
  (* driver operation 4: RECLAIM a completed slot (intr's used-elem lw)   *)
  (* ==================================================================== *)

  (* The reclaimer presents the receipt plus evidence the device is past
     the slot ([disk_done_lb] from operation 3).  The accessor exposes the
     used-ring element for exactly one 4-byte load -- its value is the
     slot's head index -- and the close-wand withdraws the whole payoff:
     the pin bytes exactly as deposited, the status byte at 0, the buffer
     (for a read request) holding the block's bytes, and the disk
     fragments at the block's current contents. *)
  (* ------------------------------------------------------------------- *)
  (* THE USED-ELEMENT WORD, READ-ONLY.                                     *)
  (*                                                                      *)
  (* [virtio_proto_reclaim_acc]'s closing wand is a ONE-SHOT update: it     *)
  (* SPENDS the receipt, bumps [disk_done_lb] and hands out the payoff      *)
  (* map.  A caller that only needs the element's ADDRESS CLAIM cannot use  *)
  (* it -- and under per-node stepping every such caller needs exactly      *)
  (* that, because [WpSconfMem.wordw_claim] must arrive BESIDE the atomic   *)
  (* update rather than inside it (the access translates several nodes      *)
  (* before the memory node where the update is opened).  Deriving the      *)
  (* claim from the static map instead is forbidden (the standing ruling:   *)
  (* every address claim comes off the accessed bytes' own points-to), so   *)
  (* this is the same walk down to the word, stopping at the [dma_own]      *)
  (* borrow and handing everything straight back.                          *)
  (*                                                                      *)
  (* Invariant-internal by construction: no leaf and no spec statement      *)
  (* changes, which is the shape the ruling of 2026-08-18 asked for.        *)
  (* ------------------------------------------------------------------- *)
  Lemma virtio_proto_used_peek (γ : disk_names) (v : virtio_state)
      (np c p : nat) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
    (p < c)%nat ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    disk_receipt γ p sl pin -∗ disk_done_lb γ c -∗
    (* the config, so the caller can identify the element's ADDRESS: it is
       persistent, so handing it out costs the invariant nothing *)
    disk_cfg γ (v_cfg v) ∗
    phys_word4 (used_elem_pa (v_cfg v) p)
               (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) ∗
    (phys_word4 (used_elem_pa (v_cfg v) p)
                (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) -∗
       virtio_proto γ v ∗ disk_pub γ np ∗ disk_receipt γ p sl pin ∗
       disk_done_lb γ c).
  Proof.
    intros Hpc. iIntros "Hp Hpub Hrecpt Hlb".
    rewrite /virtio_proto /disk_pub /disk_receipt /disk_done_lb.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & Hslot & Hnc & Hnp)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hlde &
        Hslot & Hnc & Hnp & Hpend & Hdone)".
    iDestruct (ghost_map_lookup with "Hslot Hrecpt") as %Hspin.
    destruct (vp_spins_lookup pr p sl pin Hspin) as [Hs Hpin].
    iDestruct (mono_nat_lb_own_valid with "Hnc Hlb") as %[_ Hcle].
    assert (Hpnc : (p < vp_nc pr)%nat) by lia.
    assert (Hpendnone : vp_pend pr !! p = None).
    { apply not_elem_of_dom. rewrite (vpo_pend_dom _ _ _ Hok). intro Hc'.
      apply elem_of_set_seq in Hc'. lia. }
    assert (Hdone : vp_done pr !! p = Some sl).
    { unfold vp_slots in Hs.
      rewrite (lookup_union_r (vp_pend pr) (vp_done pr) p Hpendnone) in Hs.
      exact Hs. }
    iDestruct (big_sepM_delete _ (vp_done pr) p sl Hdone with "Hdone")
      as "[Hdres Hdone]".
    iDestruct "Hdres" as (bs) "(%Hbslen & Hbs & %Hout & %Hre & %Hst & %Hbl & Hdone0)".
    assert (HEMsub : range_map (used_elem_pa (v_cfg v) p) 4
                       (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))))
                     ⊆ dma).
    { apply range_map_sub; [lia|]. intros j Hj.
      apply (read_bytes_spec dma (used_elem_pa (v_cfg v) p) 4 _ Hre). lia. }
    iDestruct (dma_own_acc_same _ dma HEMsub with "Hdma") as "[Hem Hback]".
    rewrite !phys_word4_map.
    iSplitR; [iExact "Hcfg" |].
    iFrame "Hem". iIntros "Hem".
    iDestruct ("Hback" with "Hem") as "Hdma".
    iFrame "Hpub Hrecpt Hlb".
    iExists pr, dma. iFrame "Hcfg Hdma Hslot Hnc Hnp Hpend".
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; [done|].
    iApply (big_sepM_delete _ (vp_done pr) p sl Hdone).
    iSplitR "Hdone"; [| iExact "Hdone"].
    iExists bs. iFrame "Hbs Hdone0".
    all: try (iPureIntro; split_and!; assumption).
  Qed.

  Lemma virtio_proto_reclaim_acc (γ : disk_names) (v : virtio_state)
      (np c p : nat) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
    (p < c)%nat ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    disk_receipt γ p sl pin -∗ disk_done_lb γ c -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
    (* the pin still says what it said at publish -- in particular it CONTAINS
       the avail-ring entry bytes, which the interrupt handler splits off *)
    ⌜slot_pin_ok (v_cfg v) p sl pin⌝ ∗
    phys_word4 (used_elem_pa (v_cfg v) p)
               (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) ∗
    (phys_word4 (used_elem_pa (v_cfg v) p)
                (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) ==∗
       virtio_proto γ v ∗ disk_pub γ np ∗ disk_done_lb γ (S p) ∗
       phys_map pin ∗
       phys_pointsto (vr_status (vs_req sl)) (DfracOwn 1) byte_zero ∗
       (* the SPENT crash permits' tokens: each sector landing and the
          completion already ran their view shift and parked their receipt in
          [PermInv]; these are what the woken publisher presents to collect
          them. *)
       slot_perms_done γ sl ∗
       (∃ bs : list (bv 8),
          ⌜length bs = vs_len sl⌝ ∗
          ⌜bs = vs_data sl⌝ ∗
          disk_bytes γ (vs_sector_off sl) bs ∗
          (if vs_is_out sl then emp
           else phys_list (vr_buf (vs_req sl)) bs))).
  Proof.
    intros Hpc. iIntros "Hp Hpub Hrecpt Hlb".
    rewrite {1}/virtio_proto /disk_pub /disk_receipt /disk_done_lb.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & Hslot & Hnc & Hnp)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hlde &
        Hslot & Hnc & Hnp & Hpend & Hdone)".
    iDestruct (ghost_map_lookup with "Hslot Hrecpt") as %Hspin.
    destruct (vp_spins_lookup pr p sl pin Hspin) as [Hs Hpin].
    iDestruct (mono_nat_lb_own_valid with "Hnc Hlb") as %[_ Hcle].
    (* [p] is completed, hence in [done] *)
    assert (Hpnc : (p < vp_nc pr)%nat) by lia.
    assert (Hpendnone : vp_pend pr !! p = None).
    { apply not_elem_of_dom. rewrite (vpo_pend_dom _ _ _ Hok). intro Hc'.
      apply elem_of_set_seq in Hc'. lia. }
    assert (Hdone : vp_done pr !! p = Some sl).
    { unfold vp_slots in Hs.
      rewrite (lookup_union_r (vp_pend pr) (vp_done pr) p Hpendnone) in Hs.
      exact Hs. }
    pose proof (vpo_slot _ _ _ Hok p sl pin Hs Hpin) as Hslotok.
    pose proof (vpo_wr_pin _ _ _ Hok p sl pin Hs Hpin) as Hwrpin.
    pose proof (vpo_standing _ _ _ Hok p sl pin Hs Hpin) as Hstand.
    iDestruct (big_sepM_delete _ (vp_done pr) p sl Hdone with "Hdone")
      as "[Hdres Hdone]".
    iDestruct "Hdres" as (bs) "(%Hbslen & Hbs & %Hout & %Hre & %Hst & %Hbl & Hdone0)".
    (* the used-ring element the reclaimer reads *)
    assert (HEMsub : range_map (used_elem_pa (v_cfg v) p) 4
                       (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))))
                     ⊆ dma).
    { apply range_map_sub; [lia|]. intros j Hj.
      apply (read_bytes_spec dma (used_elem_pa (v_cfg v) p) 4 _ Hre). lia. }
    iDestruct (dma_own_acc_same _ dma HEMsub with "Hdma") as "[Hem Hback]".
    rewrite !phys_word4_map.
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hslotok|].
    iFrame "Hem". iIntros "Hem".
    iDestruct ("Hback" with "Hem") as "Hdma".
    (* the payoff map: the pin, the status byte, and (for a read) the buffer *)
    assert (HdomSB : dom ({[ vr_status (vs_req sl) := byte_zero ]}
                          ∪ (if vs_is_out sl then ∅
                             else range_map (vr_buf (vs_req sl)) (length bs)
                                    (fun j : nat => bs !!! j)))
                     = slot_wr sl).
    { rewrite dom_union_L dom_singleton_L. unfold slot_wr. f_equal.
      destruct (vs_is_out sl); [ apply dom_empty_L |].
      rewrite range_map_dom Hbslen. reflexivity. }
    assert (HdSB : {[ vr_status (vs_req sl) := byte_zero ]}
                   ##ₘ (if vs_is_out sl then ∅
                        else range_map (vr_buf (vs_req sl)) (length bs)
                               (fun j : nat => bs !!! j))).
    { apply map_disjoint_dom. rewrite dom_singleton_L.
      destruct (vs_is_out sl) eqn:Hoo.
      - rewrite dom_empty_L. apply elem_of_disjoint. intros a _ Hb.
        exact (proj1 (elem_of_empty a) Hb).
      - rewrite range_map_dom Hbslen. apply elem_of_disjoint. intros a Ha Hb.
        apply elem_of_singleton in Ha. rewrite Ha in Hb.
        exact (spo_stat _ _ _ _ Hslotok Hoo Hb). }
    assert (HdPIN : pin ##ₘ ({[ vr_status (vs_req sl) := byte_zero ]}
                             ∪ (if vs_is_out sl then ∅
                                else range_map (vr_buf (vs_req sl)) (length bs)
                                       (fun j : nat => bs !!! j)))).
    { apply map_disjoint_dom. rewrite HdomSB. apply gset_disj_sym. exact Hwrpin. }
    assert (HdomMM : dom (pin ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
                          ∪ (if vs_is_out sl then ∅
                             else range_map (vr_buf (vs_req sl)) (length bs)
                                    (fun j : nat => bs !!! j))))
                     = slot_fp sl pin).
    { rewrite dom_union_L HdomSB. reflexivity. }
    assert (HPINsub : pin ⊆ dma)
      by (etransitivity;
          [ exact (vproto_pin_ctl (v_cfg v) pr (dom dma) p pin Hok Hpin)
          | exact Hctl ]).
    assert (HMMsub : pin ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
                     ∪ (if vs_is_out sl then ∅
                        else range_map (vr_buf (vs_req sl)) (length bs)
                               (fun j : nat => bs !!! j))) ⊆ dma).
    { apply map_union_least; [exact HPINsub|]. apply map_union_least.
      - apply insert_subseteq_l; [ exact Hst | apply map_empty_subseteq ].
      - destruct (vs_is_out sl) eqn:Hoo; [ apply map_empty_subseteq |].
        apply range_map_sub; [ rewrite Hbslen; apply vs_len_bound |].
        intros j Hj.
        destruct (read_byte_list_spec dma (vr_buf (vs_req sl)) (vs_len sl) bs
                    (Hbl eq_refl)) as [Hl Hlk].
        destruct (lookup_lt_is_Some_2 bs j ltac:(lia)) as [b Hb].
        rewrite (list_lookup_total_correct bs j b Hb). exact (Hlk j b Hb). }
    rewrite (dma_own_split _ dma HMMsub).
    iDestruct "Hdma" as "[Hmm Hdma]".
    rewrite {1}/phys_map.
    rewrite (big_sepM_union (fun a b => phys_pointsto a (DfracOwn 1) b) _ _ HdPIN).
    iDestruct "Hmm" as "[Hpin Hsb]".
    rewrite (big_sepM_union (fun a b => phys_pointsto a (DfracOwn 1) b) _ _ HdSB).
    iDestruct "Hsb" as "[Hstm Hbuf]".
    rewrite big_sepM_singleton.
    (* the framing fact for the shrunk lease *)
    assert (Hframe : forall x : Arch.pa, x ∉ slot_fp sl pin ->
              (dma ∖ (pin ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
                 ∪ (if vs_is_out sl then ∅
                    else range_map (vr_buf (vs_req sl)) (length bs)
                           (fun j : nat => bs !!! j))))) !! x = dma !! x).
    { intros x Hx. apply lookup_difference_out. rewrite HdomMM. exact Hx. }
    assert (Hdomdiff : dom (dma ∖ (pin ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
                 ∪ (if vs_is_out sl then ∅
                    else range_map (vr_buf (vs_req sl)) (length bs)
                           (fun j : nat => bs !!! j)))))
                       = dom dma ∖ slot_fp sl pin)
      by (rewrite dom_difference_L HdomMM; reflexivity).
    (* the pure surgery *)
    destruct (vproto_reclaim_ctl (v_cfg v) pr (dom dma) p sl pin Hok Hdone Hpin)
      as (Hctlr & Hdisjr & Hctlsplit).
    assert (HAsub : avail_idx_bytes (v_cfg v) (vp_np pr)
                    ∪ pins_union (delete p (vp_pin pr)) ⊆ dma).
    { etransitivity; [ apply (map_union_subseteq_r _ _ Hdisjr) |].
      rewrite <- Hctlsplit. exact Hctl. }
    assert (HAdisj : dom (avail_idx_bytes (v_cfg v) (vp_np pr)
                          ∪ pins_union (delete p (vp_pin pr)))
                     ## slot_fp sl pin).
    { apply elem_of_disjoint. intros a Ha Hb.
      rewrite dom_union_L avail_idx_bytes_dom in Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      - exact (proj1 (elem_of_disjoint _ _) Hstand a Hb (elem_of_union_l _ _ _ Ha)).
      - apply pins_union_dom_inv in Ha as (q & mq & Hq & Hmq).
        apply lookup_delete_Some in Hq as [Hne Hq].
        destruct (vproto_slot_of_pin (v_cfg v) pr (dom dma) q mq Hok Hq)
          as [slq Hsq].
        exact (proj1 (elem_of_disjoint _ _)
                 (vpo_fp_disj _ _ _ Hok p q sl slq pin mq
                    Hne Hs Hpin Hsq Hq) a Hb
                 (slot_fp_pin slq mq a Hmq)). }
    (* ghost moves *)
    iMod (ghost_map_delete with "Hslot Hrecpt") as "Hslot".
    iDestruct (mono_nat_lb_own_get with "Hnc") as "#Hlbnc".
    assert (Hsp : (S p <= vp_nc pr)%nat) by lia.
    iDestruct (mono_nat_lb_own_le (S p) Hsp with "Hlbnc") as "#Hlbp".
    (* rebuild *)
    iModIntro. iFrame "Hpub Hlbp Hpin Hstm Hdone0".
    iSplitR "Hbs Hbuf"; last first.
    { iExists bs. iFrame "Hbs". iSplitR; [iPureIntro; exact Hbslen|].
      iSplitR; [iPureIntro; exact Hout|].
      destruct (vs_is_out sl) eqn:Hoo; [done|].
      rewrite (phys_list_map (vr_buf (vs_req sl)) bs
                 ltac:(rewrite Hbslen; apply vs_len_bound)).
      iFrame "Hbuf". }
    rewrite /virtio_proto Hlive.
    iExists (vproto_reclaim_state pr p),
      (dma ∖ (pin ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
         ∪ (if vs_is_out sl then ∅
            else range_map (vr_buf (vs_req sl)) (length bs)
                   (fun j : nat => bs !!! j))))).
    rewrite (vp_spins_reclaim (v_cfg v) pr (dom dma) p sl Hok Hdone)
            vpr_nc vpr_np vpr_pend vpr_done.
    iFrame "Hcfg Hdma Hslot Hnc Hnp Hpend".
    iSplitR.
    { iPureIntro. rewrite Hctlr. apply map_sub_difference; [exact HAsub|].
      rewrite HdomMM. exact HAdisj. }
    iSplitR.
    { iPureIntro. rewrite Hdomdiff.
      exact (vproto_ok_reclaim (v_cfg v) pr (dom dma) p sl pin Hok Hdone Hpin). }
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR.
    { iPureIntro. apply (read_bytes_transfer dma); [| exact Hridx].
      intros j Hj. assert (Hj2 : (j < 2)%nat) by lia.
      apply Hframe. intro Hc'.
      exact (proj1 (elem_of_disjoint _ _) Hstand _ Hc'
               (elem_of_union_r _ _ _ (used_idx_in_page (v_cfg v) j Hj2))). }
    iSplitR; [iPureIntro; exact Hlde|].
    (* the OTHER done records survive the shrink *)
    assert (Hmono : forall k x, delete p (vp_done pr) !! k = Some x ->
              slot_done_res γ (v_cfg v) dma k x
              ⊢ slot_done_res γ (v_cfg v)
                  (dma ∖ (pin ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
                     ∪ (if vs_is_out sl then ∅
                        else range_map (vr_buf (vs_req sl)) (length bs)
                               (fun j : nat => bs !!! j))))) k x).
    { intros k x Hk. apply bi.wand_entails.
      apply lookup_delete_Some in Hk as [Hkne Hk].
      pose proof (vproto_done_slot (v_cfg v) pr (dom dma) k x Hok Hk) as Hks.
      assert (Hkpin : exists pinq, vp_pin pr !! k = Some pinq).
      { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
        apply elem_of_dom. exists x. exact Hks. }
      destruct Hkpin as [pinq Hpinq].
      pose proof (vpo_fp_disj _ _ _ Hok k p x sl pinq pin
                    (fun e => Hkne (eq_sym e)) Hks Hpinq Hs Hpin) as Hfpd.
      apply slot_done_res_mono.
      - intros j Hj. apply Hframe. intro Hc'.
        exact (proj1 (elem_of_disjoint _ _) Hstand _ Hc'
                 (elem_of_union_r _ _ _ (used_elem_pa_in_page (v_cfg v) k j Hj))).
      - apply Hframe. intro Hc'.
        apply (proj1 (elem_of_disjoint _ _) Hfpd (vr_status (vs_req x))).
        + apply slot_fp_wr. unfold slot_wr.
          apply elem_of_union_l, elem_of_singleton. reflexivity.
        + exact Hc'.
      - intros Hox j Hj. apply Hframe. intro Hc'.
        apply (proj1 (elem_of_disjoint _ _) Hfpd (pa_add (vr_buf (vs_req x)) j)).
        + apply slot_fp_wr. unfold slot_wr. rewrite Hox.
          apply elem_of_union_r, pa_range_intro. exact Hj.
        + exact Hc'. }
    iApply (big_sepM_mono _ _ _ Hmono). iExact "Hdone".
  Qed.

End VirtioProto.
