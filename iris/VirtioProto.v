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
Require Import DiskAddrs.   (* [disk.info[i].b] -- the receipt names it *)
Require Import BufOwn.      (* [b_disk] *)
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
         (pa_off (used_elem_at c ui) 4) 4 (vreq_used_len r))
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
             (vreq_used_len r) x).
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
             (vreq_used_len r) (pa_add (used_elem_at c ui) j)).
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
  dom (pins_union (vp_pin pr))
  ## avail_idx_dom c ∪ ring_cells_dom c ∪ used_page_pas c.
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
  apply gset_disj_sym.
  apply (gset_disj_sub_r _ _
           (avail_idx_dom c ∪ ring_cells_dom c ∪ used_page_pas c));
    [| exact (pins_union_off_standing c pr D Hok) ].
  rewrite dom_union_L avail_idx_bytes_dom. apply union_least.
  - etransitivity; [ apply union_subseteq_l | apply union_subseteq_l ].
  - etransitivity; [ apply ring_bytes_dom |].
    etransitivity; [ apply union_subseteq_r | apply union_subseteq_l ].
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
Lemma vpp_tk (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_tk (vproto_publish_state pr sl pin) = vp_tk pr.
Proof. reflexivity. Qed.
Lemma vpp_uix (pr : vproto) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
  vp_uix (vproto_publish_state pr sl pin) = vp_uix pr.
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
Lemma vpr_nr (pr : vproto) (p : nat) :
  vp_nr (vproto_reclaim_state pr p) = S (vp_nr pr).
Proof. reflexivity. Qed.
Lemma vpr_uix (pr : vproto) (p : nat) :
  vp_uix (vproto_reclaim_state pr p) = vp_uix pr.
Proof. reflexivity. Qed.

(* record projections, as rewrite rules ([cbn] does not open these) *)
Lemma vslot_post_cfg (v : virtio_state) (sl : vslot) (i : bv 16) :
  v_cfg (vslot_post v sl i) = v_cfg v.
Proof. reflexivity. Qed.
Lemma vslot_post_seen (v : virtio_state) (sl : vslot) (i : bv 16) :
  v_seen (vslot_post v sl i) = v_seen v.
Proof. reflexivity. Qed.
Lemma vslot_post_inflight (v : virtio_state) (sl : vslot) (i : bv 16) :
  v_inflight (vslot_post v sl i) = v_inflight v ∖ {[ i ]}.
Proof. reflexivity. Qed.
Lemma vslot_post_uidx (v : virtio_state) (sl : vslot) (i : bv 16) :
  v_used_idx (vslot_post v sl i) = bv_add (v_used_idx v) (Z_to_bv 16 1).
Proof. reflexivity. Qed.
(* THE COMPLETION MOVES NO DISK BYTE (sector-atomic-disk.md stage 2): the
   request's sectors landed one at a time, before it was enabled. *)
Lemma vslot_post_disk (v : virtio_state) (sl : vslot) (i : bv 16) :
  v_disk (vslot_post v sl i) = v_disk v.
Proof. reflexivity. Qed.

Lemma vps_nc (pr : vproto) (p : nat) (sl : vslot) :
  vp_nc (vproto_step_state pr p sl) = S (vp_nc pr).
Proof. reflexivity. Qed.
Lemma vps_np (pr : vproto) (p : nat) (sl : vslot) :
  vp_np (vproto_step_state pr p sl) = vp_np pr.
Proof. reflexivity. Qed.
Lemma vps_tk (pr : vproto) (p : nat) (sl : vslot) :
  vp_tk (vproto_step_state pr p sl)
  = (if bool_decide (vp_tk pr = Some p) then None else vp_tk pr).
Proof. reflexivity. Qed.
Lemma vps_pend (pr : vproto) (p : nat) (sl : vslot) :
  vp_pend (vproto_step_state pr p sl) = delete p (vp_pend pr).
Proof. reflexivity. Qed.
Lemma vps_done (pr : vproto) (p : nat) (sl : vslot) :
  vp_done (vproto_step_state pr p sl) = <[ p := sl ]> (vp_done pr).
Proof. reflexivity. Qed.
Lemma vps_uix (pr : vproto) (p : nat) (sl : vslot) :
  vp_uix (vproto_step_state pr p sl) = <[ p := vp_nc pr ]> (vp_uix pr).
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

(* THE LEASE THE LIVE FLIP HANDS OVER: the published index, the eight ring
   cells (zero, like the rest of the page the driver just cleared) and the
   whole used page. *)
Definition vinit_dma (c : virtio_cfg) : gmap Arch.pa (bv 8) :=
  (range_map (avail_idx_pa c) 2 (nth_byte (wrap16 0))
   ∪ ring_bytes c (fun _ : nat => zero16))
  ∪ range_map (vc_used c) 4096 (fun _ : nat => byte_zero).

Lemma zero16_wrap16_pure : zero16 = wrap16 0%nat.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

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
  ring_cells_dom c ## used_page_pas c ->
  (range_map (avail_idx_pa c) 2 (nth_byte (wrap16 0))
   ∪ ring_bytes c (fun _ : nat => zero16))
    ##ₘ range_map (vc_used c) 4096 (fun _ : nat => byte_zero).
Proof.
  (* [range_map_dom] lands on [pa_range _ 4096]; [avail_idx_dom]/[used_page_pas]
     are that same term behind one delta step, but leaving the fold to
     [exact]'s conversion makes it normalise a 4096-element [list_to_set] over
     [gset Arch.pa] -- 3.7 s here and 3.5 s in [vinit_dma_dom] below, plus as
     much again at each [Qed].  Unfolding both names first makes the match
     syntactic. *)
  intros Hd Hdr. apply map_disjoint_dom.
  rewrite dom_union_L !range_map_dom ring_bytes_dom_eq.
  unfold avail_idx_dom, used_page_pas in Hd, Hdr.
  apply disjoint_union_l. split; [exact Hd | exact Hdr].
Qed.

(* the index bytes and the ring cells are different bytes of the avail page *)
Lemma vinit_idx_ring_disj (c : virtio_cfg) :
  range_map (avail_idx_pa c) 2 (nth_byte (wrap16 0))
  ##ₘ ring_bytes c (fun _ : nat => zero16).
Proof.
  apply map_disjoint_dom. rewrite range_map_dom ring_bytes_dom_eq.
  apply gset_disj_sym. apply ring_cells_idx_disj.
Qed.

Lemma vinit_dma_dom (c : virtio_cfg) :
  dom (vinit_dma c)
  = avail_idx_dom c ∪ ring_cells_dom c ∪ used_page_pas c.
Proof.
  unfold vinit_dma, avail_idx_dom, used_page_pas.
  rewrite !dom_union_L !range_map_dom ring_bytes_dom_eq. reflexivity.
Qed.

Lemma vinit_dma_ctl (c : virtio_cfg) : vproto_ctl c vproto0 ⊆ vinit_dma c.
Proof.
  rewrite (vproto0_ctl c) (avail_idx_bytes_range c 0).
  unfold vinit_dma. apply map_union_subseteq_l.
Qed.

Lemma vinit_dma_uidx (c : virtio_cfg) :
  avail_idx_dom c ## used_page_pas c ->
  ring_cells_dom c ## used_page_pas c ->
  read_bytes (vinit_dma c) (used_idx_pa c) 2 = Some (wrap16 0).
Proof.
  intros Hd Hdr. apply read_bytes_of_list. intros j Hj.
  assert (Hj2 : (j < 2)%nat) by lia.
  assert (Hin : pa_add (used_idx_pa c) j ∈ used_page_pas c)
    by (apply used_idx_in_page; exact Hj2).
  unfold vinit_dma. rewrite lookup_union_out.
  2:{ rewrite dom_union_L range_map_dom ring_bytes_dom_eq.
      intro Hc. apply elem_of_union in Hc as [Hc|Hc].
      - exact (proj1 (elem_of_disjoint _ _) Hd _ Hc Hin).
      - exact (proj1 (elem_of_disjoint _ _) Hdr _ Hc Hin). }
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

Lemma vproto_step_slots (pr : vproto) (p : nat) (sl : vslot) :
  vp_pend pr !! p = Some sl ->
  vp_slots (vproto_step_state pr p sl) = vp_slots pr.
Proof.
  intro Hsl. unfold vp_slots, vproto_step_state. cbn [vp_pend vp_done vp_nc].
  apply map_eq. intro q. destruct (decide (q = p)) as [->|Hne].
  - rewrite lookup_union_r.
    2:{ apply lookup_delete. }
    rewrite lookup_insert. symmetry. apply lookup_union_Some_l. exact Hsl.
  - rewrite !lookup_union lookup_delete_ne; [| congruence ].
    rewrite lookup_insert_ne; [| congruence ]. reflexivity.
Qed.

Lemma vp_spins_step (pr : vproto) (p : nat) (sl : vslot) :
  vp_pend pr !! p = Some sl ->
  vp_spins (vproto_step_state pr p sl) = vp_spins pr.
Proof.
  intro H. unfold vp_spins. rewrite (vproto_step_slots pr p sl H). reflexivity.
Qed.

Lemma vproto_publish_slots (pr : vproto) (sl : vslot)
    (pin : gmap Arch.pa (bv 8)) :
  vp_slots (vproto_publish_state pr sl pin) = <[ vp_np pr := sl ]> (vp_slots pr).
Proof.
  unfold vp_slots, vproto_publish_state. cbn [vp_pend vp_done vp_np].
  symmetry. apply insert_union_l.
Qed.

(* the POP touches no slot and no pin, so the per-slot map is untouched *)
Lemma vp_spins_pop (pr : vproto) (sl : vslot) :
  vp_spins (vproto_pop_state pr sl) = vp_spins pr.
Proof. reflexivity. Qed.

(* ...and neither does the RING STORE *)
Lemma vp_spins_ring (pr : vproto) (h : bv 16) :
  vp_spins (vproto_ring_state pr h) = vp_spins pr.
Proof. reflexivity. Qed.

(* one cell of a left-biased union replaced under a common prefix *)
Lemma map_union_mono_r (m m1 m2 : gmap Arch.pa (bv 8)) :
  m1 ⊆ m2 -> m ∪ m1 ⊆ m ∪ m2.
Proof.
  intro Hsub. apply map_subseteq_spec. intros a b Ha.
  apply lookup_union_Some_raw in Ha as [Ha|[Hn Ha]].
  - by apply lookup_union_Some_l.
  - rewrite lookup_union_r; [| exact Hn ].
    exact (lookup_weaken _ _ _ _ Ha Hsub).
Qed.

(* a cell sits inside the region the eight of them cover *)
(* THE EIGHT CELLS OF A FRESHLY CLEARED PAGE.  [virtio_disk_init] zeroes the
   available page before the flip, so the lease's ring region starts life as
   sixteen zero bytes -- which is what lets the boot chain hand
   [virtio_proto_intro] the [phys_map] it wants. *)
Lemma ring_bytes_zero_range (c : virtio_cfg) :
  ring_bytes c (fun _ : nat => zero16)
  = range_map (ring_slot_pa c 0) 16 (fun _ : nat => byte_zero).
Proof.
  assert (Hbase : ring_slot_pa c 0 = pa_off (vc_avail c) vq_avail_ring_off).
  { unfold ring_slot_pa. f_equal; lia. }
  apply map_eq. intro a.
  destruct (decide (a ∈ pa_range (ring_slot_pa c 0) 16)) as [Hin|Hout].
  - apply pa_range_elim in Hin as (i & Hi & ->).
    change (N.to_nat 16) with 16%nat in Hi.
    rewrite (range_map_lookup (ring_slot_pa c 0) 16
               (fun _ : nat => byte_zero) i ltac:(lia) Hi).
    (* the address is byte [i mod 2] of cell [i / 2] *)
    assert (Hd8 : (i / 2 < 8)%nat) by (apply Nat.div_lt_upper_bound; lia).
    assert (Hm2 : (i `mod` 2 < 2)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Heq : pa_add (ring_slot_pa c 0) i
                  = pa_add (ring_slot_pa c (i / 2)%nat) (i `mod` 2)%nat).
    { unfold ring_slot_pa, pa_off. rewrite !pa_add_add. f_equal.
      (* [lia] cannot see through [Z.to_nat] of a symbolic sum; the same
         shape [ring_bytes_dom_eq] handles, handled the same way *)
      assert (Hz0 : Z.to_nat (vq_avail_ring_off + 2 * Z.of_nat 0)
                    = Z.to_nat vq_avail_ring_off)
        by (unfold vq_avail_ring_off; lia).
      assert (Hz : Z.to_nat (vq_avail_ring_off + 2 * Z.of_nat (i / 2)%nat)
                   = (Z.to_nat vq_avail_ring_off + 2 * (i / 2))%nat)
        by (unfold vq_avail_ring_off; lia).
      rewrite Hz0 Hz. pose proof (Nat.div_mod i 2 ltac:(lia)). lia. }
    rewrite Heq.
    rewrite (read_bytes_spec (ring_bytes c (fun _ : nat => zero16))
               (ring_slot_pa c (i / 2)%nat) 2 zero16
               (ring_bytes_read c (fun _ : nat => zero16) (i / 2)%nat Hd8)
               (i `mod` 2)%nat ltac:(lia)).
    rewrite zero16_wrap16_pure.
    by rewrite (nth_byte_wrap16_0 (i `mod` 2)%nat Hm2).
  - rewrite (range_map_lookup_out _ 16 (fun _ : nat => byte_zero) a Hout).
    apply not_elem_of_dom.
    rewrite (ring_bytes_dom_eq c (fun _ : nat => zero16)).
    unfold ring_cells_dom. rewrite <- Hbase. exact Hout.
Qed.

Lemma pa_range_ring_cells (c : virtio_cfg) (k : nat) :
  (k < 8)%nat -> pa_range (ring_slot_pa c k) 2 ⊆ ring_cells_dom c.
Proof.
  intro Hk.
  rewrite -(ring_bytes_dom_eq c (fun _ => zero16)).
  apply (read_bytes_dom_sub (ring_bytes c (fun _ => zero16))
           (ring_slot_pa c k) 2 zero16).
  exact (ring_bytes_read c (fun _ => zero16) k Hk).
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
  (* SERVED, hence not pending: the counters no longer decide this -- the
     served SET does ([vpo_done_lt] lands in it, and [vpo_pend_dom] is its
     complement). *)
  assert (Hsrv : p ∈ vp_srv pr)
    by (apply (vpo_done_lt _ _ _ Hok), elem_of_dom; exists sl; exact Hdone).
  apply not_elem_of_dom. intro Hc.
  destruct (proj1 (vpo_pend_dom _ _ _ Hok p) Hc) as [_ Hns]. exact (Hns Hsrv).
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

  (* THE COMPLETION RECORD (finding 5): position [p]'s completion was
     reported at used index [u].  Persistent -- it is identification, not
     ownership -- and the interrupt handler, which walks used indices, is
     what reads it.  Two records at one position agree, which is how the
     handler knows the position it just learned about is not one it has
     already processed. *)
  Definition disk_ord (γ : disk_names) (p u : nat) : iProp Σ :=
    p ↪[dn_ord γ]□ u.

  Global Instance disk_ord_persistent γ p u : Persistent (disk_ord γ p u).
  Proof. rewrite /disk_ord. apply _. Qed.
  Global Instance disk_ord_timeless γ p u : Timeless (disk_ord γ p u).
  Proof. rewrite /disk_ord. apply _. Qed.

  Lemma disk_ord_agree (γ : disk_names) (p u1 u2 : nat) :
    disk_ord γ p u1 -∗ disk_ord γ p u2 -∗ ⌜u1 = u2⌝.
  Proof.
    iIntros "H1 H2". rewrite /disk_ord.
    by iDestruct (ghost_map_elem_agree with "H1 H2") as %->.
  Qed.

  (* THE READ WATERMARK ([disk.used_idx]): the other half of the invariant's
     cell, held by whoever is walking the used ring -- in xv6 the interrupt
     handler, under the vdisk_lock.  Presenting it at reclaim is what says
     "the record I am taking is the one at the watermark", and reclaim hands
     back the advanced half.  Reading the ring IN ORDER is therefore not an
     assumption about the driver but a condition the driver must meet to
     reclaim at all; xv6's handler meets it by construction. *)
  Definition disk_read_at (γ : disk_names) (n : nat) : iProp Σ :=
    ghost_var (dn_nr γ) (1/2) n.

  Lemma disk_read_at_agree (γ : disk_names) (n1 n2 : nat) :
    disk_read_at γ n1 -∗ disk_read_at γ n2 -∗ ⌜n1 = n2⌝.
  Proof.
    iIntros "H1 H2". rewrite /disk_read_at.
    by iDestruct (ghost_var_agree with "H1 H2") as %->.
  Qed.

  (* THE STAGED HEAD, between the two stores of a publish.  [None] at rest;
     the ring store sets it to the head it wrote, and the index bump consumes
     it -- which is exactly how the publisher tells the invariant that the
     cell position [np] is about to use already names its chain, across an
     invariant closure it cannot see through. *)
  Definition disk_stage (γ : disk_names) (s : option (bv 16)) : iProp Σ :=
    ghost_var (dn_stage γ) (1/2) s.

  Lemma disk_stage_agree (γ : disk_names) (s1 s2 : option (bv 16)) :
    disk_stage γ s1 -∗ disk_stage γ s2 -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "H1 H2". rewrite /disk_stage.
    by iDestruct (ghost_var_agree with "H1 H2") as %->.
  Qed.

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
     data reaches the durable image one sector at a time -- through the
     device's volatile cache, at the DRAINS ([VirtioModel.virtio_drain_step],
     claude-notes/completed/async-disk.md) -- and each drain is its own
     linearization point.  The request's obligation is therefore a SINGLE
     SEQUENTIAL permit ([RiscvPtsto.disk_seq_permit]) that unfolds a branch
     at a time: the channel cell at [vs_perm sl] carries it, each drain
     spends one branch and re-deposits the residual at the SAME key, and the
     cell's index -- the sectors still to drain -- is [pend_todo] below, a
     pure function of the device's own cache.

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

  (* INDEXED BY WHAT IS STILL OWED (claude-notes/completed/async-disk.md).
     [td] is the set of sector indices whose bytes have NOT yet reached the
     durable image -- the sequential permit's own index, which is why the
     [perm_pend] row below takes it verbatim and the publish site needs no
     conversion ([PermInv.perm_deposit_kq] deposits at [vs_all sl]).  What
     [vs_torn] speaks about is the complement, [vs_kept sl td]: the sectors
     that HAVE drained and therefore hold the payload. *)
  Definition slot_pend_res (γ : disk_names) (td : gset nat) (sl : vslot)
      : iProp Σ :=
    (∃ bs : list (bv 8),
       ⌜length bs = vs_len sl⌝ ∗
       ⌜vs_is_out sl = false -> bs = vs_data sl⌝ ∗
       (* THE TORN CONTENT (sector-atomic-disk.md).  The block's durable
          bytes are the OLD ones in the sectors that have not landed and the
          PAYLOAD's in the ones that have -- which is what makes a crash
          between two landings leave a half-written block, and what the
          publisher's fragments have to say while the request is in flight. *)
       ⌜vs_torn sl (vs_kept sl td) bs⌝ ∗
       disk_bytes γ (vs_sector_off sl) bs ∗
       (* THE REQUEST'S ONE CHANNEL ENTRY, at the sectors STILL TO LAND. *)
       perm_pend (dn_perm γ) (vs_perm sl) (vs_wr sl) td)%I.

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
  (* WHAT EACH PENDING SLOT STILL OWES (claude-notes/completed/async-disk.md).
     The device's volatile write CACHE ([VirtioModel.v_cache]) belongs to the
     HEAD request -- the one at [v_seen], i.e. protocol position [vp_nc] --
     and every other pending slot has drained nothing at all, so its whole
     write is still owed.  BEFORE the head's CAPTURE nothing is cached either
     and the head owes everything too, which is why [v_taken] appears: it is
     what tells "nothing cached because the bytes have not been read off the
     bus yet" (owes everything) from "nothing cached because every sector has
     drained" (owes nothing, the sequential permit's leaf).  This is the
     function that carries the device's cache into the per-slot resource
     without putting a mutable field into the (immutable, receipt-pinned)
     [vslot] record.  It takes the cache and the flag as ARGUMENTS rather
     than the state, so that a store which leaves both alone carries the
     invariant across by [rewrite] ([virtio_proto_stable]). *)
  (* WHAT COMES BACK FROM THE DEVICE (finding 5): the chain's pinned bytes,
     its status byte, the spent crash permits and the sector data.  Named
     here so the receipt's "it all came back" disjunct below and the payoff
     [virtio_proto_reclaim_acc] releases are literally the same
     proposition -- the handler moves one into the other. *)
  Definition chain_back (γ : disk_names) (sl : vslot)
      (pin : gmap Arch.pa (bv 8)) : iProp Σ :=
    (phys_map pin ∗
     phys_pointsto (vr_status (vs_req sl)) (DfracOwn 1) byte_zero ∗
     slot_perms_done γ sl ∗
     (∃ bs : list (bv 8),
        ⌜length bs = vs_len sl⌝ ∗
        ⌜bs = vs_data sl⌝ ∗
        disk_bytes γ (vs_sector_off sl) bs ∗
        (if vs_is_out sl then emp
         else phys_list (vr_buf (vs_req sl)) bs)))%I.

  (* THE PER-DESCRIPTOR RECEIPT'S CONTENT.
     [HInactive] -- nobody has submitted descriptor [i]; the receipt holds
     NOTHING.  [disk.info[i].b] is driver-private (no descriptor names it),
     so while the slot is idle its cell sits in the lock resource alongside
     the rest of the free slot, and only the publish moves it in here.
     [HActive v] -- descriptor [i] heads a live chain, and the claim [v]
     records what was published.  The entry owns [disk.info[i].b] PINNED to
     that claim's buffer, which is what lets the interrupt handler learn
     which [struct buf] it is looking at by reading the cell rather than by
     looking anything up.  Then either [b->disk = 1] and the invariant does
     not own the chain (the device has it, or the handler is carrying it), or
     [b->disk = 0] and the whole chain is back inside. *)
  Definition head_res (γ : disk_names) (i : nat) (st : hstate) : iProp Σ :=
    match st with
    | HInactive => emp%I
    | HActive v =>
        (⌜Z.to_nat (bv_unsigned (vr_head (vs_req (dc_slot v)))) = i⌝ ∗
         (* THE CLAIM'S IDENTITY: the [dn_claim] fragment for this position.
            Its authority is the vdisk_lock's ([DiskInv.disk_res]), so the
            interrupt handler -- which holds that lock for its whole loop --
            reads the SAME claim off its own map at each of its openings and
            agrees it with this fragment; the woken publisher takes the
            fragment out with the chain and retires the row at free_chain. *)
         dc_pos v ↪[dn_claim γ] v ∗
         d_info_b i ↦₈ (dc_buf v : SailStdpp.Values.mword 64) ∗
         (* EITHER the chain is out -- at the device, or in the interrupt
            handler's hands on its way back -- and the invariant holds only
            the [dn_slot] receipt that names the published position... *)
         ((b_disk (dc_buf v) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1)
           ∗ disk_receipt γ (dc_pos v) (dc_slot v) (dc_pin v))
          (* ...OR it all came back, and [b->disk] says so. *)
          ∨ (b_disk (dc_buf v) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 0)
             ∗ chain_back γ (dc_slot v) (dc_pin v))))%I
    end.

  Global Instance chain_back_timeless γ sl pin : Timeless (chain_back γ sl pin).
  Proof. rewrite /chain_back. apply _. Qed.

  (* [apply _] cannot see through the match on the receipt state *)
  Global Instance head_res_timeless γ i st : Timeless (head_res γ i st).
  Proof. destruct st; rewrite /head_res; apply _. Qed.

  (* the receipts, as they ride in the invariant: total over the eight
     descriptors, exactly like [disk.info[NUM]] and [disk.free[NUM]] in the
     C, so reaching entry [i] needs only [i < 8] and never a domain fact *)
  Definition heads_res (γ : disk_names) : iProp Σ :=
    (∃ hs : gmap nat hstate,
       ⌜dom hs = set_seq 0 8⌝ ∗
       ghost_map_auth (dn_head γ) 1 hs ∗
       ([∗ map] i ↦ st ∈ hs, head_res γ i st))%I.

  (* ...and the same, coupled to the protocol: every slot still live has an
     ACTIVE head whose claim names it.  THIS is what replaces the counting:
     the handler, holding a live slot, reads its receipt straight off. *)
  (* Indexed by the SLOTS MAP, not by the whole protocol state: the receipts
     depend on nothing else, so every transition that leaves [vp_slots] alone
     -- the pop, the capture, the drain, the device's own completion step --
     carries them across by a rewrite rather than by an argument. *)
  Definition heads_res_at (γ : disk_names)
      (spins : gmap nat (vslot * gmap Arch.pa (bv 8))) : iProp Σ :=
    (∃ hs : gmap nat hstate,
       ⌜dom hs = set_seq 0 8⌝ ∗
       (* EVERY LIVE REQUEST'S HEAD IS ACTIVE, and its receipt names the whole
          claim -- slot, pinned bytes and position.  Pinning the pin is what
          lets the interrupt handler rule out "the chain already came back":
          that branch would put [dc_pin] in the receipt while the lease still
          holds it, and a byte cannot be owned twice. *)
       ⌜forall q sl pin, spins !! q = Some (sl, pin) ->
          exists w, hs !! (Z.to_nat (bv_unsigned (vr_head (vs_req sl))))
                    = Some (HActive w)
                    /\ dc_slot w = sl /\ dc_pin w = pin /\ dc_pos w = q⌝ ∗
       ghost_map_auth (dn_head γ) 1 hs ∗
       ([∗ map] i ↦ st ∈ hs, head_res γ i st))%I.

  Global Instance heads_res_timeless γ : Timeless (heads_res γ).
  Proof. rewrite /heads_res. apply _. Qed.

  (* THE RECEIPTS AT THE LIVE FLIP.  The authority has been carried since
     power-on with every entry INACTIVE, and an INACTIVE entry owns nothing,
     so the flip needs no resources at all.  Nothing is published yet, so the
     coupling clause is vacuous. *)
  Lemma heads_res_at_init (γ : disk_names) (hs : gmap nat hstate) :
    dom hs = set_seq 0 8 ->
    (forall i st, hs !! i = Some st -> st = HInactive) ->
    ghost_map_auth (dn_head γ) 1 hs -∗
    heads_res_at γ (vp_spins vproto0).
  Proof.
    intros Hdom Hinact. iIntros "Hauth".
    rewrite /heads_res_at. iExists hs. iFrame "Hauth".
    iSplitR; [by iPureIntro|].
    iSplitR.
    { iPureIntro. intros q sl pin Hq.
      (* [vproto0] has no live requests at all *)
      assert (Hse : vp_spins vproto0 = (∅ : gmap nat (vslot * gmap Arch.pa (bv 8)))).
      { rewrite /vp_spins /vp_slots.
        apply map_eq. intro k. rewrite map_lookup_zip_with !lookup_empty.
        reflexivity. }
      rewrite Hse lookup_empty in Hq. discriminate. }
    (* every entry is INACTIVE, so the body ignores the value *)
    rewrite (big_sepM_proper _ (fun i _ => head_res γ i HInactive));
      [| intros i st Hst; by rewrite (Hinact i st Hst) ].
    rewrite /head_res. by iApply big_sepM_intro.
  Qed.
  (* the coupling only has to cover the slots that are live, so it survives
     any transition that removes some -- the reclaim, in particular *)
  Lemma heads_res_at_mono (γ : disk_names)
      (s1 s2 : gmap nat (vslot * gmap Arch.pa (bv 8))) :
    (forall q x, s2 !! q = Some x -> s1 !! q = Some x) ->
    heads_res_at γ s1 -∗ heads_res_at γ s2.
  Proof.
    intro Hsub. rewrite /heads_res_at.
    iIntros "H". iDestruct "H" as (hs) "(%Hdom & %Hcoup & Hauth & Hbig)".
    iExists hs. iFrame "Hauth Hbig". iSplitR; [by iPureIntro|].
    iPureIntro. intros q sl pin Hq.
    exact (Hcoup q sl pin (Hsub q (sl, pin) Hq)).
  Qed.

  Global Instance heads_res_at_timeless γ slots : Timeless (heads_res_at γ slots).
  Proof. rewrite /heads_res_at. apply _. Qed.

  (* THE RING WINDOW, OFF THE RECEIPTS (VirtioQueue.nat_inj_below8).  The
     unpopped positions [vp_lo, vp_np) are pending, their heads are pairwise
     distinct and each has an ACTIVE receipt -- so a head whose receipt is
     INACTIVE is a further descriptor, and nine descriptors do not fit in
     eight.  This is what a publisher presents in place of any counting of
     the driver's descriptor triples. *)
  Lemma heads_window_pure (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
      (hs : gmap nat hstate) (i : nat) :
    vproto_ok c pr D ->
    dom hs = set_seq 0 8 ->
    (forall q sl pin, vp_spins pr !! q = Some (sl, pin) ->
       exists w, hs !! (Z.to_nat (bv_unsigned (vr_head (vs_req sl))))
                 = Some (HActive w)
                 /\ dc_slot w = sl /\ dc_pin w = pin /\ dc_pos w = q) ->
    hs !! i = Some HInactive ->
    (vp_np pr - vp_lo pr < 8)%nat.
  Proof.
    intros Hok Hdom Hcoup Hi.
    set (f := fun q => match vp_pend pr !! q with
                       | Some sl => Z.to_nat (bv_unsigned (vr_head (vs_req sl)))
                       | None => 0%nat
                       end).
    assert (Hpend : forall q, (vp_lo pr <= q < vp_np pr)%nat ->
              exists sl pin, vp_pend pr !! q = Some sl
                             /\ vp_spins pr !! q = Some (sl, pin)).
    { intros q Hq.
      assert (Hin : q ∈ dom (vp_pend pr)).
      { apply (vpo_pend_dom _ _ _ Hok). split; [lia|].
        intro Hs. pose proof (vpo_srv_lo _ _ _ Hok q Hs). lia. }
      apply elem_of_dom in Hin as [sl Hsl].
      assert (Hs : vp_slots pr !! q = Some sl) by exact (vproto_pend_slot pr q sl Hsl).
      assert (Hpin : exists pin, vp_pin pr !! q = Some pin).
      { apply elem_of_dom. rewrite (vproto_slot_dom c pr D Hok).
        apply elem_of_dom. by exists sl. }
      destruct Hpin as [pin Hpin]. exists sl, pin. split; [exact Hsl|].
      unfold vp_spins. rewrite map_lookup_zip_with Hs Hpin. reflexivity. }
    assert (Hdom8 : forall k st, hs !! k = Some st -> (k < 8)%nat).
    { intros k st Hk.
      assert (Hk' : k ∈ dom hs) by (apply elem_of_dom; by exists st).
      rewrite Hdom in Hk'. apply elem_of_set_seq in Hk'. lia. }
    apply (nat_inj_below8 (vp_lo pr) (vp_np pr) i f).
    - intros q Hq. destruct (Hpend q Hq) as (sl & pin & Hsl & Hsp).
      destruct (Hcoup q sl pin Hsp) as (w & Hw & _).
      unfold f. rewrite Hsl. exact (Hdom8 _ _ Hw).
    - intros q1 q2 Hq1 Hq2 Heq.
      destruct (Hpend q1 Hq1) as (sl1 & pin1 & Hsl1 & _).
      destruct (Hpend q2 Hq2) as (sl2 & pin2 & Hsl2 & _).
      unfold f in Heq. rewrite Hsl1 Hsl2 in Heq.
      destruct (decide (q1 = q2)) as [|Hne]; [assumption|].
      exfalso.
      apply (vpo_hd_inj _ _ _ Hok q1 q2 sl1 sl2 Hne
               (vproto_pend_slot pr q1 sl1 Hsl1) (vproto_pend_slot pr q2 sl2 Hsl2)).
      unfold vs_hd. apply bv_eq.
      destruct (bv_unsigned_in_range _ (vr_head (vs_req sl1))) as [H1 _].
      destruct (bv_unsigned_in_range _ (vr_head (vs_req sl2))) as [H2 _].
      apply Z2Nat.inj; [exact H1 | exact H2 | exact Heq].
    - intros q Hq. destruct (Hpend q Hq) as (sl & pin & Hsl & Hsp).
      destruct (Hcoup q sl pin Hsp) as (w & Hw & _).
      unfold f. rewrite Hsl. intro Heq. rewrite Heq Hi in Hw. discriminate.
    - exact (Hdom8 _ _ Hi).
  Qed.

  Lemma heads_res_at_window (γ : disk_names) (c : virtio_cfg) (pr : vproto)
      (D : gset Arch.pa) (i : nat) :
    vproto_ok c pr D ->
    heads_res_at γ (vp_spins pr) -∗ i ↪[dn_head γ] HInactive -∗
    ⌜(vp_np pr - vp_lo pr < 8)%nat⌝.
  Proof.
    intro Hok. iIntros "H Hfrag". rewrite /heads_res_at.
    iDestruct "H" as (hs) "(%Hdom & %Hcoup & Hauth & _)".
    iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hi.
    iPureIntro. exact (heads_window_pure c pr D hs i Hok Hdom Hcoup Hi).
  Qed.

  Definition pend_todo (pr : vproto) (ca : gmap Z (list (bv 8)))
      (p : nat) (sl : vslot) : gset nat :=
    if bool_decide (vp_tk pr = Some p)
    then vs_todo sl (dom ca)
    else vs_all sl.

  Lemma pend_todo_other (pr : vproto) (ca : gmap Z (list (bv 8)))
      (p : nat) (sl : vslot) :
    vp_tk pr <> Some p -> pend_todo pr ca p sl = vs_all sl.
  Proof. intro H. rewrite /pend_todo bool_decide_eq_false_2 //. Qed.

  Lemma pend_todo_head (pr : vproto) (ca : gmap Z (list (bv 8)))
      (p : nat) (sl : vslot) :
    vp_tk pr = Some p -> pend_todo pr ca p sl = vs_todo sl (dom ca).
  Proof. intro H. rewrite /pend_todo bool_decide_eq_true_2 //. Qed.

  (* nothing captured: EVERY pending slot owes its whole write *)
  Lemma pend_todo_untaken (pr : vproto) (ca : gmap Z (list (bv 8)))
      (p : nat) (sl : vslot) :
    vp_tk pr = None -> pend_todo pr ca p sl = vs_all sl.
  Proof. intro H. rewrite /pend_todo H bool_decide_eq_false_2 //. Qed.

  (* THE WRITETHROUGH DISCIPLINE AT THE PROTOCOL
     ([VirtioModel.virtio_wt_inv] section 6c, in the queue's vocabulary).
     Everything the device is holding belongs to the HEAD request and is
     exactly what that request's capture deposited -- which is both what
     identifies a DRAIN with a sector of the head slot
     ([VirtioQueue.vproto_drain_det]) and what makes a completion find the
     cache empty ([VirtioModel.virtio_req_step_wt_cache]).  With NO head
     request the cache is empty and nothing has been captured, so the next
     publish hands its fresh slot in at the sequential permit's ROOT. *)
  Definition vp_wt (pr : vproto) (ca : gmap Z (list (bv 8))) : Prop :=
    match vp_tk pr with
    | Some p => exists sl, vp_pend pr !! p = Some sl /\ ca ⊆ vslot_cache sl
    | None => ca = ∅
    end.

  (* an idle device satisfies it whatever is queued *)
  Lemma vp_wt_idle (pr : vproto) (ca : gmap Z (list (bv 8))) :
    ca = ∅ -> vp_tk pr = None -> vp_wt pr ca.
  Proof. intros -> Htk. by rewrite /vp_wt Htk. Qed.

  Lemma vp_wt_head (pr : vproto) (ca : gmap Z (list (bv 8))) (p : nat) :
    vp_tk pr = Some p -> vp_wt pr ca ->
    exists sl, vp_pend pr !! p = Some sl /\ ca ⊆ vslot_cache sl.
  Proof. intros Htk H. rewrite /vp_wt Htk in H. exact H. Qed.

  Lemma vp_wt_none (pr : vproto) (ca : gmap Z (list (bv 8))) :
    vp_tk pr = None -> vp_wt pr ca -> ca = ∅.
  Proof. intros Htk H. rewrite /vp_wt Htk in H. exact H. Qed.

  (* ...and it IS the model's state-only invariant, at the head request's
     sector set -- which is the form the completion's payoff needs. *)
  Lemma vp_wt_virtio_wt_inv (c : virtio_cfg) (p q : nat) (pr : vproto)
      (v : virtio_state) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
    slot_pin_ok c p sl pin ->
    vp_tk pr = Some q -> vp_pend pr !! q = Some sl ->
    v_taken v = wrap16 <$> vp_tk pr -> vp_wt pr (v_cache v) ->
    virtio_wt_inv v (vs_sectors sl).
  Proof.
    intros Hslot Htk Hsl Hcoup Hwt.
    destruct (vp_wt_head pr (v_cache v) q Htk Hwt) as (sl' & Hsl' & Hsub).
    rewrite Hsl in Hsl'. injection Hsl' as <-.
    split.
    - rewrite <- (vslot_cache_dom_sectors c p sl pin Hslot).
      by apply subseteq_dom.
    - intro Hnone. rewrite Hcoup Htk in Hnone. discriminate.
  Qed.

  Definition virtio_proto (γ : disk_names) (v : virtio_state) : iProp Σ :=
    (if virtio_live (v_cfg v) then
        ∃ (pr : vproto) (dma : gmap Arch.pa (bv 8)),
          disk_cfg γ (v_cfg v) ∗
          dma_own dma ∗
          ⌜vproto_ctl (v_cfg v) pr ⊆ dma⌝ ∗
          ⌜vproto_ok (v_cfg v) pr (dom dma)⌝ ∗
          ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
          (* THE DEVICE'S WINDOW IS THE KEYED STATE'S (finding 5): the
             watermark, the positions served out of turn, and the request
             whose payload is latched, all read off [pr].  The used index is
             the COMPLETION COUNT and no longer the position of anything --
             that is exactly what the out-of-order fix separated. *)
          ⌜v_seen v = wrap16 (vp_lo pr)⌝ ∗
          ⌜v_inflight v = vp_fl pr⌝ ∗
          (* THE LATCH, ACROSS THE TWO KEYINGS: the device holds the captured
             request's HEAD, the protocol its POSITION.  [vpo_hd_inj] is what
             makes the two agree -- a head names one pending request. *)
          ⌜match vp_tk pr with
            | None => v_taken v = None
            | Some q => exists sl, vp_pend pr !! q = Some sl
                                   /\ v_taken v = Some (vs_hd sl)
            end⌝ ∗
          ⌜v_used_idx v = wrap16 (vp_nc pr)⌝ ∗
          ⌜read_bytes dma (used_idx_pa (v_cfg v)) 2 = Some (wrap16 (vp_nc pr))⌝ ∗
          (* XV6 DECLINED THE WRITE CACHE (claude-notes/completed/async-disk.md
             §2).  [virtio_disk_init] writes DRIVER_FEATURES with the word
             the C computes -- zero at this device's offer
             ([VirtioModel.virtio_xv6_features]) -- so bit 9 (FLUSH) is not
             negotiated and the device is in WRITETHROUGH mode.  This row is
             what [virtio_proto_writethrough] exports and what discharges the
             completion gate below; it is pinned by the persistent
             [disk_cfg], since the device never writes its own config. *)
          ⌜virtio_wce (v_cfg v) = false⌝ ∗
          (* ...and the discipline that follows: the cache holds nothing but
             the LATCHED request's captured sectors, and nothing at all when
             nothing is latched. *)
          ⌜vp_wt pr (v_cache v)⌝ ∗
          ghost_map_auth (dn_slot γ) 1 (vp_spins pr) ∗
          (* the completion records, whose elements are handed out
             persistently as each request completes *)
          ghost_map_auth (dn_ord γ) 1 (vp_uix pr) ∗
          (* ...and a PERSISTENT copy of every one of them, so the invariant
             can hand a completion record out on demand: the auth alone
             cannot produce an element, and the interrupt handler needs one
             to name the position behind the used index it is looking at. *)
          ([∗ map] q ↦ u ∈ vp_uix pr, disk_ord γ q u) ∗
          mono_nat_auth_own (dn_nc γ) 1 (vp_nc pr) ∗
          ghost_var (dn_np γ) (1/2) (vp_np pr) ∗
          (* THE HANDLER'S READ WATERMARK, half here and half in the disk
             lock's resource.  The reclaimer presents its half to say the
             record it is taking is the one at the watermark; that is what
             lets [vp_nr] advance by one and keeps the unread records a
             contiguous run ([vproto_unread_lt8]). *)
          ghost_var (dn_nr γ) (1/2) (vp_nr pr) ∗
          (* THE STAGED HEAD.  A publisher that has done its ring store but
             not yet its index bump has left the cell position [vp_np pr] is
             about to use already naming its chain; this pair is how it says
             so across the invariant closure between the two instructions.
             [None] whenever no publish is half-done, which is every state the
             device can observe a difference in -- the device reads a cell
             only at the pop, and cannot pop an unannounced position. *)
          (∃ st : option (bv 16),
             ghost_var (dn_stage γ) (1/2) st ∗
             ⌜match st with
               | None => True
               | Some h => vp_ring pr (vp_np pr `mod` 8)%nat = h
               end⌝) ∗
          (* THE PER-DESCRIPTOR RECEIPTS, coupled to the live slots *)
          heads_res_at γ (vp_spins pr) ∗
          ([∗ map] p ↦ sl ∈ vp_pend pr,
             slot_pend_res γ (pend_todo pr (v_cache v) p sl) sl) ∗
          (* A DONE SLOT'S RECORD SITS AT THE USED INDEX IT COMPLETED AT, not
             at its own position: with the served order free the two are
             different numbers, and [vp_uix] is what remembers which. *)
          ([∗ map] p ↦ sl ∈ vp_done pr,
             ∃ u : nat, ⌜vp_uix pr !! p = Some u⌝ ∗
                        slot_done_res γ (v_cfg v) dma u sl)
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
        (* ...and neither has anything been CAPTURED or CACHED: the reset
           that made the device not live dropped the whole volatile cache
           ([virtio_reset_cache]/[virtio_reset_taken]) and a not-live device
           takes no capture step ([virtio_capture_step_not_live]).  A DRAIN
           is a different matter -- it is enabled by the cache alone, even
           when the queue is dead -- which is exactly why the empty cache has
           to be RECORDED here: it is what refutes the drain arm of
           [WpUart.wp_disk_loop] on a dead queue.  Recording both is also
           what lets the LIVE FLIP establish the live arm's [vp_wt]. *)
        ⌜v_cache v = ∅⌝ ∗ ⌜v_taken v = None⌝ ∗ ⌜v_inflight v = ∅⌝ ∗
        (* ...and the cache MODE is already declined: the pre-flip
           DRIVER_FEATURES write is the one that decides it, and every write
           after it leaves [vc_dfeat] alone.  Carrying it on this arm too is
           what makes [virtio_proto_writethrough] unconditional. *)
        ⌜virtio_wce (v_cfg v) = false⌝ ∗
        ghost_map_auth (dn_slot γ) 1 (∅ : gmap nat (vslot * gmap Arch.pa (bv 8))) ∗
        (* the completion records' auth rides here too, so the LIVE FLIP has
           one to hand the live arm ([virtio_proto_intro_gen]) *)
        ghost_map_auth (dn_ord γ) 1 (∅ : gmap nat nat) ∗
        mono_nat_auth_own (dn_nc γ) 1 0%nat ∗
        ghost_var (dn_np γ) 1 0%nat ∗
        ghost_var (dn_nr γ) 1 0%nat ∗
        (* nothing is half-published on a dead queue *)
        ghost_var (dn_stage γ) 1 (None : option (bv 16)) ∗
        (* THE RECEIPTS' AUTHORITY, and the fact that all eight are INACTIVE.
           Only the authority: the eight [disk.info[i].b] cells are .bss the
           boot chain still holds at this point, and they arrive with the
           live flip ([virtio_proto_intro_gen]). *)
        (∃ hs : gmap nat hstate,
           ⌜dom hs = set_seq 0 8⌝ ∗
           ⌜forall i st, hs !! i = Some st -> st = HInactive⌝ ∗
           ghost_map_auth (dn_head γ) 1 hs))%I.

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
    v_seen v = zero16 -> v_used_idx v = zero16 ->
    (* the volatile write cache is empty and untaken, and the driver has
       negotiated nothing -- all four hold of ANY reset device
       ([VirtioModel.virtio_reset_cache]/[_taken]/[_wce]) *)
    v_cache v = ∅ -> v_taken v = None -> v_inflight v = ∅ ->
    virtio_wce (v_cfg v) = false ->
    ⊢ |==> ∃ γ : disk_names,
        (* the image name IS the era's: this is what lets the device thread
           identify the auth [state_interp] hands it with the fragments this
           invariant holds ([virtio_proto_step]). *)
        ⌜dn_img γ = disk_img_name⌝ ∗
        virtio_proto γ v ∗ disk_cfg_is γ (DfracOwn (1/2)) (v_cfg v) ∗
        ghost_map_auth (dn_claim γ) 1 (∅ : gmap nat dclaim) ∗
        disk_done_lb γ 0%nat ∗
        (* the eight receipt fragments, INACTIVE: one rides each free
           descriptor, and the allocator hands it to [virtio_disk_rw] *)
        ([∗ map] i ↦ st ∈ gset_to_gmap HInactive (set_seq 0 8 : gset nat),
           i ↪[dn_head γ] st) ∗
        (* THE CRASH-PERMIT CHANNEL, empty: nothing is in flight at power-on,
           so no permit is owed.  Handed out as the BODY (not the invariant)
           because [WpUart.dev_inv_alloc] is what seals it, beside
           [disk_inv].  [gd] is the ERA's generation: the channel only ever
           holds permits its own era authored (PermInv.v). *)
        perm_inv_body gd (dn_perm γ).
  Proof.
    intros Hlive Hsn Hui Hca Htk Hah Hwce.
    iMod (ghost_map_alloc_empty (K:=nat)
            (V:=(vslot * gmap Arch.pa (bv 8))%type)) as (gslot) "Hslot".
    iMod (mono_nat_own_alloc 0) as (gnc) "[Hnc Hlb]".
    iMod (ghost_var_alloc 0%nat) as (gnp) "Hnp".
    iMod (ghost_map_alloc_empty (K:=nat) (V:=dclaim)) as (gclaim) "Hclaim".
    iMod (ghost_map_alloc_empty (K:=nat) (V:=nat)) as (gord) "Hord".
    iMod (ghost_var_alloc 0%nat) as (gnr) "Hnr".
    iMod (ghost_var_alloc (None : option (bv 16))) as (gstage) "Hstage".
    (* the per-descriptor receipts, all eight INACTIVE at power-on *)
    iMod (ghost_map_alloc (gset_to_gmap HInactive (set_seq 0 8 : gset nat)))
      as (ghead) "[Hhead Hhfrags]".
    iMod (disk_cfg_alloc (v_cfg v)) as (gcfg) "Hcfg".
    iMod (perm_ghost_alloc gd) as (gperm) "Hperm".
    iDestruct (disk_cfg_is_split
                 (DiskNames disk_img_name gslot gnc gnp gclaim gcfg gord gnr gstage ghead gperm)
                 (v_cfg v) with "[Hcfg]") as "[Hcfg1 Hcfg2]".
    { rewrite /disk_cfg_is. cbn [dn_cfg]. iExact "Hcfg". }
    iModIntro.
    iExists (DiskNames disk_img_name gslot gnc gnp gclaim gcfg gord gnr gstage ghead gperm).
    iSplitR; [iPureIntro; reflexivity|].
    iFrame "Hcfg2".
    rewrite /disk_done_lb. cbn [dn_nc dn_claim dn_head dn_perm].
    iFrame "Hclaim Hlb Hhfrags Hperm".
    rewrite /virtio_proto.
    cbn [dn_img dn_slot dn_nc dn_np dn_claim dn_cfg dn_ord dn_nr dn_stage
         dn_head dn_perm].
    rewrite Hlive.
    iSplitL "Hcfg1"; [iExact "Hcfg1"|].
    iSplitR; [iPureIntro; exact Hsn|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hca|].
    iSplitR; [iPureIntro; exact Htk|].
    iSplitR; [iPureIntro; exact Hah|].
    iSplitR; [iPureIntro; exact Hwce|].
    iFrame "Hslot Hord Hnc Hnp Hnr Hstage".
    (* the receipts: authority only, every entry INACTIVE *)
    iExists (gset_to_gmap HInactive (set_seq 0 8 : gset nat)).
    iSplitR; [iPureIntro; apply dom_gset_to_gmap|].
    iSplitR.
    { iPureIntro. intros i st Hst.
      apply lookup_gset_to_gmap_Some in Hst as [_ Heq]. exact (eq_sym Heq). }
    iExact "Hhead".
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
    (* the RING/USED disjointness is NOT a premise: it falls out of the two
       resources below, the same way [vdi_dma_disj] gets the index one --
       owning both regions is already proof they do not overlap. *)
    v_seen v1 = wrap16 0 ->
    v_used_idx v1 = wrap16 0 ->
    (* the cache mode the pre-flip DRIVER_FEATURES write decided *)
    virtio_wce c = false ->
    (* the empty, untaken cache the not-live arm was recording all along *)
    v_cache v1 = ∅ -> v_taken v1 = None ->
    v_inflight v1 = ∅ ->
    disk_cfg γ c -∗
    ghost_map_auth (dn_slot γ) 1 (∅ : gmap nat (vslot * gmap Arch.pa (bv 8))) -∗
    ghost_map_auth (dn_ord γ) 1 (∅ : gmap nat nat) -∗
    mono_nat_auth_own (dn_nc γ) 1 0%nat -∗
    ghost_var (dn_np γ) (1/2) 0%nat -∗
    ghost_var (dn_nr γ) (1/2) 0%nat -∗
    (* nothing half-published at the flip *)
    ghost_var (dn_stage γ) (1/2) (None : option (bv 16)) -∗
    (* THE RECEIPTS' AUTHORITY, carried from power-on with every entry
       INACTIVE.  No cells come with it: [disk.info[i].b] is driver-private
       and stays in the lock resource until a publish hands it over. *)
    (∃ hs : gmap nat hstate,
       ⌜dom hs = set_seq 0 8⌝ ∗
       ⌜forall i st, hs !! i = Some st -> st = HInactive⌝ ∗
       ghost_map_auth (dn_head γ) 1 hs) -∗
    phys_word2 (avail_idx_pa c) (wrap16 0) -∗
    (* THE EIGHT RING CELLS, zero like the rest of the page the driver just
       cleared: they belong to the lease now, not to any request. *)
    phys_map (ring_bytes c (fun _ : nat => zero16)) -∗
    phys_list (vc_used c) (replicate 4096 byte_zero) -∗
    virtio_proto γ v1.
  Proof.
    intros Hcfg Hlive Hqnum Hal Hdisj Hseen Hui Hwce Hca Htk Hah.
    iIntros "#Hcfgp Hslot Hord Hnc Hnp Hnr Hstage Hheads Hidx Hring Hpage".
    iDestruct "Hheads" as (hs) "(%Hhdom & %Hhinact & Hhauth)".
    assert (H4k : Z.of_nat 4096 < 18446744073709551616) by (rewrite z4096; lia).
    rewrite phys_word2_map (phys_list_replicate (vc_used c) 4096 byte_zero H4k).
    (* ...and there it is, off the ownership *)
    iDestruct (phys_map_disj with "Hring Hpage") as %Hdring0.
    apply map_disjoint_dom in Hdring0.
    rewrite (ring_bytes_dom_eq c (fun _ : nat => zero16)) range_map_dom
      in Hdring0.
    assert (Hdring : ring_cells_dom c ## used_page_pas c) by exact Hdring0.
    iAssert (dma_own (vinit_dma c)) with "[Hidx Hring Hpage]" as "Hdma".
    { rewrite /vinit_dma /dma_own.
      rewrite (big_sepM_union (fun a b => phys_pointsto a (DfracOwn 1) b) _ _
                 (vinit_dma_disj c Hdisj Hdring)).
      rewrite (big_sepM_union (fun a b => phys_pointsto a (DfracOwn 1) b) _ _
                 (vinit_idx_ring_disj c)).
      iFrame "Hidx Hring Hpage". }
    rewrite /virtio_proto.
    rewrite Hcfg Hlive.
    iExists vproto0, (vinit_dma c).
    rewrite vp_spins_init.
    iFrame "Hcfgp Hdma Hslot Hord Hnc Hnp Hnr".
    iSplitR; [iPureIntro; apply vinit_dma_ctl|].
    iSplitR.
    { iPureIntro. rewrite vinit_dma_dom.
      apply vproto_ok_init;
        [exact Hqnum | exact Hlive | exact Hdisj | exact Hdring]. }
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; by rewrite Hah|].
    iSplitR; [iPureIntro; by rewrite Htk|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact (vinit_dma_uidx c Hdisj Hdring)|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR;
      [iPureIntro; exact (vp_wt_idle vproto0 (v_cache v1) Hca eq_refl)|].
    assert (Hpe : vp_pend vproto0 = (∅ : gmap nat vslot)) by reflexivity.
    assert (Hde : vp_done vproto0 = (∅ : gmap nat vslot)) by reflexivity.
    assert (Hue : vp_uix vproto0 = (∅ : gmap nat nat)) by reflexivity.
    rewrite Hpe Hde Hue !big_sepM_empty.
    iSplitR; [done|].
    iSplitL "Hstage"; [by iExists None; iFrame "Hstage"|].
    (* THE RECEIPTS ARRIVE: authority as carried, every entry empty *)
    iSplitL "Hhauth".
    { iApply (heads_res_at_init γ hs Hhdom Hhinact with "Hhauth"). }
    iSplit; done.
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
    v_cache v1 = v_cache v0 -> v_taken v1 = v_taken v0 ->
    v_inflight v1 = v_inflight v0 ->
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
    (* the eight ring cells, still zero from the driver's page clear *)
    phys_map (ring_bytes (virtio_init_cfg pd pav pu) (fun _ : nat => zero16)) -∗
    phys_list pu (replicate 4096 byte_zero) -∗
    |==> virtio_proto γ v1 ∗ disk_pub γ 0 ∗ disk_read_at γ 0 ∗
         disk_stage γ None ∗
         disk_cfg γ (virtio_init_cfg pd pav pu).
  Proof.
    intros Hlive0 Hc1 Hsn Hui Hcae Htke Hahe Hal Hdisj.
    iIntros "Hp Hmine Hidx Hring Hpage".
    rewrite {1}/virtio_proto.
    rewrite Hlive0.
    iDestruct "Hp" as "(Hcfg & %Hsn0 & %Hui0 & %Hca0 & %Htk0 & %Hah0 & %Hwce0 &
                        Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
    iDestruct (disk_cfg_is_join with "Hcfg Hmine") as "Hcfg".
    iMod (disk_cfg_set γ (v_cfg v0) (virtio_init_cfg pd pav pu) with "Hcfg")
      as "#Hcfg".
    iEval (rewrite -Qp.half_half) in "Hnp".
    iDestruct (ghost_var_split with "Hnp") as "[Hnp1 Hnp2]".
    (* the READ WATERMARK splits the same way: the driver's half is what its
       interrupt handler will present to reclaim in order *)
    iEval (rewrite -Qp.half_half) in "Hnr".
    iDestruct (ghost_var_split with "Hnr") as "[Hnr1 Hnr2]".
    (* ...and so does the STAGED HEAD: nothing is half-published at the flip,
       and the driver's half is what its next publish will set and spend *)
    iEval (rewrite -Qp.half_half) in "Hstage".
    iDestruct (ghost_var_split with "Hstage") as "[Hstage1 Hstage2]".
    iModIntro. rewrite /disk_pub /disk_read_at /disk_stage.
    iFrame "Hnp2 Hnr2 Hstage2 Hcfg".
    assert (Hs1 : v_seen v1 = wrap16 0%nat)
      by (rewrite Hsn Hsn0; exact zero16_wrap16).
    assert (Hu1 : v_used_idx v1 = wrap16 0%nat)
      by (rewrite Hui Hui0; exact zero16_wrap16).
    assert (Hca1 : v_cache v1 = ∅) by (rewrite Hcae; exact Hca0).
    assert (Htk1 : v_taken v1 = None) by (rewrite Htke; exact Htk0).
    assert (Hah1 : v_inflight v1 = ∅) by (rewrite Hahe; exact Hah0).
    iApply (virtio_proto_intro_gen γ v1 (virtio_init_cfg pd pav pu)
              Hc1 (virtio_init_cfg_live pd pav pu) eq_refl Hal Hdisj
              Hs1 Hu1 (virtio_init_cfg_wce pd pav pu) Hca1 Htk1 Hah1
              with "Hcfg Hslot Hord Hnc Hnp1 Hnr1 Hstage1 Hheads Hidx Hring Hpage").
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
    v_seen v' = zero16 -> v_used_idx v' = zero16 ->
    v_cache v' = ∅ -> v_taken v' = None -> v_inflight v' = ∅ ->
    (* THE ONE NEW OBLIGATION ON A PRE-FLIP WRITE (async-disk.md §2): the
       configuration it programs must still decline the cache.  Thirteen of
       the fourteen writes do not touch [vc_dfeat] at all; the DRIVER_FEATURES
       write is the one that decides it, and xv6's negotiation computes to
       zero ([VirtioModel.virtio_xv6_features]). *)
    virtio_wce c' = false ->
    virtio_proto γ v -∗ disk_cfg_is γ (DfracOwn (1/2)) (v_cfg v) ==∗
    virtio_proto γ v' ∗ disk_cfg_is γ (DfracOwn (1/2)) c'.
  Proof.
    intros Hlive0 Hlive1 Hc1 Hsn Hui Hca Htk Hah Hwce. iIntros "Hp Hmine".
    rewrite {1}/virtio_proto.
    rewrite Hlive0.
    iDestruct "Hp"
      as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
    iDestruct (disk_cfg_is_join with "Hcfg Hmine") as "Hcfg".
    iMod (disk_cfg_is_move γ (v_cfg v) c' with "Hcfg") as "Hcfg".
    iDestruct (disk_cfg_is_split with "Hcfg") as "[Hcfg1 Hcfg2]".
    iModIntro. iFrame "Hcfg2".
    rewrite /virtio_proto.
    rewrite Hc1 Hlive1.
    iFrame "Hcfg1".
    iSplitR; [iPureIntro; exact Hsn|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hca|].
    iSplitR; [iPureIntro; exact Htk|].
    iSplitR; [iPureIntro; exact Hah|].
    iSplitR; [iPureIntro; exact Hwce|].
    iFrame "Hslot Hord Hnc Hnp Hnr Hstage Hheads".
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
     /\ v_cache v = ∅ /\ v_taken v = None /\ v_inflight v = ∅⌝.
  Proof.
    iIntros (Hlive) "Hp Hmine". rewrite /virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hl.
    - iDestruct "Hp" as (pr dma) "(#Hcfg & _)".
      iDestruct (disk_cfg_is_agree with "Hcfg Hmine") as %Hc.
      rewrite Hc Hlive in Hl. discriminate.
    - iDestruct "Hp"
        as "(Hcfg & %Hsn & %Hui & %Hca & %Htk & %Hah & %Hwce & _)".
      iDestruct (disk_cfg_is_agree with "Hcfg Hmine") as %Hc.
      iPureIntro. split_and!;
        [exact Hc | exact Hsn | exact Hui | exact Hca | exact Htk | exact Hah].
  Qed.

  (* ==================================================================== *)
  (* stability: MMIO writes that keep cfg / seen / used_idx                *)
  (* ==================================================================== *)

  (* THE WRITE CACHE IS PART OF THE PROTOCOL NOW
     (claude-notes/completed/async-disk.md): what the device is still holding
     decides which branch of an in-flight write's sequential permit is
     outstanding, so a store that carried the protocol across on
     cfg/seen/used alone has to leave [v_cache] and [v_taken] alone too.
     Both stores the live driver makes do
     ([VirtioModel.virtio_write_cache]/[_taken] at [vio_cfg_stable]). *)
  Lemma virtio_proto_stable (γ : disk_names) (v v' : virtio_state) :
    v_cfg v' = v_cfg v -> v_seen v' = v_seen v -> v_inflight v' = v_inflight v ->
    v_used_idx v' = v_used_idx v ->
    v_cache v' = v_cache v -> v_taken v' = v_taken v ->
    virtio_proto γ v -∗ virtio_proto γ v'.
  Proof.
    intros Hc Hs Hah Hu Hca Htk.
    rewrite /virtio_proto Hc Hs Hah Hu Hca Htk. iIntros "$".
  Qed.

  (* ==================================================================== *)
  (* THE THEOREM WORTH NAMING (claude-notes/completed/async-disk.md §2)     *)
  (* ==================================================================== *)

  (* XV6'S DISK IS WRITETHROUGH BECAUSE XV6 DECLINED FLUSH.  The device this
     model offers HAS a volatile write-back cache (VIRTIO_BLK_F_FLUSH and
     _CONFIG_WCE are in [VirtioModel.virtio_device_features]); what makes a
     completed write DURABLE is that [virtio_disk_init] clears bit 9 before
     it writes DRIVER_FEATURES, and this is that fact, held by the protocol
     invariant in BOTH arms and therefore true at every instant of the
     system's life.  It is a property PROVED of the driver's initialisation,
     not a modelling assumption: a driver that negotiated FLUSH would face a
     different permit discipline (async-disk.md §4). *)
  Lemma virtio_proto_writethrough (γ : disk_names) (v : virtio_state) :
    virtio_proto γ v -∗ ⌜virtio_wce (v_cfg v) = false⌝.
  Proof.
    iIntros "Hp". rewrite /virtio_proto.
    destruct (virtio_live (v_cfg v)).
    - iDestruct "Hp" as (pr dma)
        "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hwce & _)". done.
    - iDestruct "Hp" as "(_ & _ & _ & _ & _ & _ & %Hwce & _)". done.
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
      "(Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui &
        %Hridx & Hrest)".
    iDestruct (dma_agree with "Hm Hdma") as %Hsub.
    iPureIntro.
    assert (Hctlm : vproto_ctl (v_cfg v) pr ⊆ m)
      by (etransitivity; [exact Hctl | exact Hsub]).
    apply (virtio_queue_not_stalled v (vproto_ctl (v_cfg v) pr) (dom dma)
             (vp_heads pr) (wrap16 (vp_np pr)) mv).
    - rewrite Hseen Hah. exact (vproto_flat (v_cfg v) pr (dom dma) Hok).
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
      (m : gmap Arch.pa (bv 8)) (mv : vmem) (i : bv 16) (v' : virtio_state)
      (w : gmap Arch.pa (bv 8)) :
    mem_view m mv ->
    virtio_req_step v mv i = Some (v', w) ->
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
    { exfalso. rewrite (virtio_req_step_not_live v mv i Hlive) in Hstep.
      discriminate. }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    iDestruct (dma_agree with "Hm Hdma") as %Hsub.
    assert (Hctlm : vproto_ctl (v_cfg v) pr ⊆ m)
      by (etransitivity; [exact Hctl | exact Hsub]).
    assert (Hvctl : mem_view (vproto_ctl (v_cfg v) pr) mv)
      by exact (mem_view_subseteq _ m mv Hctlm Hview).
    destruct (vproto_step_det (v_cfg v) pr (dom dma) v mv i v' w
                Hok eq_refl Hseen Hah Hvctl Hstep)
      as (p & sl & pin & Hwin & Hip & Hsl & Hpin & Hslotok & Hvpin &
          Hsdone & Hv1 & Hw1).
    (* [Hwin] is now the single fact that the device had POPPED this position *)
    subst i v' w. rewrite Hui.
    (* THE WRITETHROUGH PAYOFF (async-disk.md §2), now stated per REQUEST
       rather than over the whole cache: xv6 declined the cache, so the gate
       demands that none of THIS request's sectors is still held, in either
       direction ([virtio_complete_ok]).  What the device may still be
       holding is some OTHER request's captured payload, and that is exactly
       what the served order being free makes possible. *)
    pose proof (spo_req _ _ _ _ Hslotok mv Hvpin) as Hreq.
    assert (Htouch : vreq_touch (vs_req sl) ∩ dom (v_cache v) = ∅).
    { destruct (decide (bv_unsigned (vr_type (vs_req sl)) = virtio_blk_t_out))
        as [Hout|Hnout].
      - destruct (virtio_complete_ok_out v (vs_req sl) (vs_hd sl) Hout Hsdone)
          as [_ [Hw|Hd]]; [ by rewrite Hwce in Hw | exact Hd ].
      - destruct (decide (bv_unsigned (vr_type (vs_req sl))
                          = virtio_blk_t_flush)) as [Hfl|Hnfl].
        + (* a FLUSH: the gate emptied the whole cache *)
          rewrite (virtio_complete_ok_flush v (vs_req sl) (vs_hd sl)
                     Hnout Hfl Hsdone) dom_empty_L. set_solver.
        + destruct (virtio_complete_ok_read v (vs_req sl) (vs_hd sl)
                      Hnout Hnfl Hsdone) as [Hw|Hd];
            [ by rewrite Hwce in Hw | exact Hd ]. }
    (* ...so a READ's data collapses from the cache-overlaid image back to
       the DURABLE one, on the range it reports. *)
    rewrite (vslot_writes_cache_view (v_cfg v) (wrap16 (vp_nc pr)) v sl
               Htouch).
    (* the pure protocol facts about the slot the device is completing *)
    pose proof (vproto_pend_slot pr _ _ Hsl) as Hs.
    pose proof (vpo_standing _ _ _ Hok _ sl pin Hs Hpin) as Hstand.
    pose proof (vpo_qnum _ _ _ Hok) as Hqnum.
    assert (Hwrpage : slot_wr sl ## used_page_pas (v_cfg v)).
    { apply (gset_disj_mono (slot_wr sl) (slot_fp sl pin)
               (used_page_pas (v_cfg v))
               (avail_idx_dom (v_cfg v) ∪ ring_cells_dom (v_cfg v)
                ∪ used_page_pas (v_cfg v)));
        [ apply slot_fp_wr | apply union_subseteq_r | exact Hstand ]. }
    destruct (vslot_writes_dom (v_cfg v) pr (dom dma) p sl pin
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
    iDestruct (big_sepM_delete _ (vp_pend pr) p sl Hsl with "Hpend")
      as "[Hslres Hpend]".
    (* ...so the request's channel entry has nothing left to land: its cell
       is at the LEAF, the completion's own identity permit.  For an OUT
       request because the gate demanded that none of ITS sectors is still
       held; for a READ because it owes nothing per-sector to begin with. *)
    assert (Htd : pend_todo pr (v_cache v) p sl = ∅).
    { destruct (vs_is_out sl) eqn:Hout; last first.
      { (* a READ owes nothing whatever the latch says *)
        unfold pend_todo. destruct (bool_decide (vp_tk pr = Some p));
          [ apply vs_todo_read; exact Hout | apply vs_all_read; exact Hout ]. }
      (* an OUT: the gate says [p] itself is latched, and that none of its
         sectors is cached, so its todo set is empty *)
      assert (Hout2 : bv_unsigned (vr_type (vs_req sl)) = virtio_blk_t_out)
        by (unfold vs_is_out in Hout; by apply Z.eqb_eq).
      destruct (virtio_complete_ok_out v (vs_req sl) (vs_hd sl) Hout2 Hsdone)
        as [Ht _].
      (* THE DEVICE'S LATCH IS THE PROTOCOL'S.  The gate says the device holds
         THIS request's head; a head names one pending request
         ([vpo_hd_inj]), so the latched POSITION is [p]. *)
      assert (Htkp : vp_tk pr = Some p).
      { destruct (vp_tk pr) as [q|] eqn:Htq; last first.
        { exfalso. rewrite Htkc in Ht. discriminate. }
        destruct Htkc as (slq & Hslq & Htv).
        rewrite Htv in Ht. injection Ht as Ht.
        f_equal. destruct (decide (q = p)) as [->|Hne]; [reflexivity|].
        exfalso.
        exact (vpo_hd_inj _ _ _ Hok q p slq sl Hne
                 (vproto_pend_slot pr _ _ Hslq) Hs Ht). }
      rewrite (pend_todo_head _ _ p sl Htkp).
      apply vs_todo_done. intros k Hk Hin.
      assert (Hks : vs_key sl k ∈ vreq_touch (vs_req sl)).
      { rewrite (vreq_touch_out (vs_req sl) Hout2).
        apply (vs_sectors_spec (v_cfg v) p sl pin _ Hslotok).
        by exists k. }
      assert (Hboth : vs_key sl k ∈ vreq_touch (vs_req sl) ∩ dom (v_cache v))
        by (apply elem_of_intersection; split; [exact Hks | exact Hin]).
      rewrite Htouch in Hboth. by apply elem_of_empty in Hboth. }
    rewrite Htd.
    iDestruct "Hslres" as (bs)
      "(%Hbslen & %Hbspin & %Hbstorn & Hbs & Hpend0)".
    rewrite vs_kept_nil in Hbstorn.
    assert (Hout' : bs = vs_data sl).
    { destruct (vs_is_out sl) eqn:Hout; [| exact (Hbspin eq_refl) ].
      pose proof (vslot_data_len (v_cfg v) p sl pin Hslotok Hout) as Hdl.
      apply (vs_torn_full sl (vs_all sl) bs Hbslen Hdl); [| exact Hbstorn ].
      intros i Hi. apply vs_all_elem.
      rewrite <- (vslot_nsectors_pin (v_cfg v) p sl pin Hslotok).
      rewrite (vslot_nsectors_out sl Hout). exact Hi. }
    iDestruct (disk_bytes_read γ dmap (v_disk v) (vs_sector_off sl) bs Hdv
                 with "Hauth Hbs") as %Hrd.
    assert (Hin' : vs_is_out sl = false ->
              disk_read (v_disk v) (vs_sector_off sl) (vs_len sl) = bs)
      by (intros _; rewrite <- Hbslen; exact Hrd).
    assert (Hdv' : disk_view dmap (v_disk (vslot_post v sl (vs_hd sl))))
      by (rewrite vslot_post_disk; exact Hdv).
    (* the byte lease and the counters *)
    iMod (dma_update _ m dma HwDdma with "Hm Hdma") as "[Hm Hdma]".
    assert (Hle : (vp_nc pr <= S (vp_nc pr))%nat) by lia.
    iMod (mono_nat_own_update (S (vp_nc pr)) Hle with "Hnc") as "[Hnc _]".
    (* THE FRAMES: every OTHER done record survives.  A done record sits at
       the USED INDEX it completed at, and this completion's record lands at
       [vp_nc pr]; the indices the handler has not read yet are a run shorter
       than the ring ([vproto_unread_lt8]), so none of them agrees with the
       new one mod eight and none of their bytes is overwritten. *)
    pose proof (vproto_unread_lt8 (v_cfg v) pr (dom dma) p Hok
                  (elem_of_dom_2 _ _ _ Hsl)) as Hgap.
    (* the completing position is PENDING; every done key is SERVED *)
    assert (Hdne : forall k x, vp_done pr !! k = Some x -> k ≠ p).
    { intros k x Hk Hc. subst k.
      destruct (proj1 (vpo_pend_dom _ _ _ Hok p) (elem_of_dom_2 _ _ _ Hsl))
        as [_ Hns].
      exact (Hns (vpo_done_lt _ _ _ Hok p (elem_of_dom_2 _ _ _ Hk))). }
    assert (Hmono : forall k u x, vp_done pr !! k = Some x ->
              vp_uix pr !! k = Some u ->
              slot_done_res γ (v_cfg v) dma u x
              ⊢ slot_done_res γ (v_cfg v)
                  (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl ∪ dma)
                  u x).
    { intros k u x Hk Hu. apply bi.wand_entails.
      pose proof (vproto_done_slot (v_cfg v) pr (dom dma) k x Hok Hk) as Hks.
      assert (Hkpin : exists pinq, vp_pin pr !! k = Some pinq).
      { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
        apply elem_of_dom. exists x. exact Hks. }
      destruct Hkpin as [pinq Hpinq].
      pose proof (Hdne k x Hk) as Hkne.
      pose proof (vpo_fp_disj _ _ _ Hok k p x sl pinq pin
                    Hkne Hks Hpinq Hs Hpin) as Hfpd.
      pose proof (vpo_standing _ _ _ Hok k x pinq Hks Hpinq) as Hstq.
      (* [k]'s record is one the handler still owes a look, so its used index
         lies in the run [[vp_nr, vp_nc)] -- under eight below the new one *)
      assert (Hunr : (vp_nr pr <= u)%nat).
      { destruct (proj1 (vpo_done_uix _ _ _ Hok k) (elem_of_dom_2 _ _ _ Hk))
          as (u' & Hu' & Hle').
        assert (Hue : u' = u) by congruence. subst u'. exact Hle'. }
      pose proof (vpo_uix_lt _ _ _ Hok k u Hu) as Hult.
      assert (Hmod : Z.of_nat u `mod` 8 ≠ Z.of_nat (vp_nc pr) `mod` 8).
      { intro Hc.
        assert (Hd : (Z.of_nat (vp_nc pr) - Z.of_nat u) `mod` 8 = 0).
        { rewrite Zminus_mod -Hc Z.sub_diag. apply Zmod_0_l. }
        rewrite Z.mod_small in Hd; lia. }
      apply slot_done_res_mono.
      - intros j Hj. apply lookup_union_r.
        exact (vslot_writes_none_other_elem (v_cfg v) (v_disk v) sl
                 (vp_nc pr) u j Hqnum Hwrpage Hmod Hj).
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
    (* the completion RECORD: position [p] answered at used index [nc], minted
       persistent so the interrupt handler can name the position it is
       looking at when it walks the used ring *)
    assert (Hunone : vp_uix pr !! p = None).
    { apply not_elem_of_dom. rewrite (vpo_uix_dom _ _ _ Hok).
      exact (proj2 (proj1 (vpo_pend_dom _ _ _ Hok p)
                     (elem_of_dom_2 _ _ _ Hsl))). }
    iMod (ghost_map_insert_persist p (vp_nc pr) Hunone with "Hord")
      as "[Hord #Hordp]".
    iModIntro. iExists (vs_perm sl), (vs_wr sl).
    iSplitR; [iPureIntro; apply vslot_post_wr|].
    iFrame "Hpend0". iIntros "Hdone0".
    iFrame "Hm".
    iSplitL "Hauth".
    { iExists dmap. iFrame "Hauth". iPureIntro. exact Hdv'. }
    rewrite /virtio_proto vslot_post_cfg vslot_post_cache Hlive.
    iExists (vproto_step_state pr p sl),
      (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl ∪ dma).
    (* the completion moves a slot from pending to done; [vp_spins] -- hence
       the receipts -- is the same map, so this one rewrite serves both the
       slot authority and the receipts' index *)
    rewrite (vp_spins_step pr p sl Hsl) vps_nc vps_np vps_pend vps_done vps_uix.
    (* the PERSISTENT record index gains the new pair; the auth already did *)
    rewrite (big_sepM_insert _ (vp_uix pr) p (vp_nc pr) Hunone).
    iFrame "Hcfg Hdma Hslot Hord Hordp Hordm Hnc Hnp Hnr Hstage Hheads".
    (* the pure conjuncts *)
    iSplitR.
    { iPureIntro. rewrite (vproto_step_ctl (v_cfg v) pr p sl).
      exact (virtio_ctl_union _ _ _ Hwctl Hctl). }
    iSplitR.
    { iPureIntro. rewrite (dom_union_sub _ dma HwDdma).
      exact (vproto_ok_step (v_cfg v) pr (dom dma) p sl Hok Hwin Hsl). }
    iSplitR; [iPureIntro; exact Hal|].
    (* THE WINDOW MOVED EXACTLY AS THE KEYED STATE SAYS, and after the
       pop/complete split that is immediate: the POP index does not move at a
       completion, and the in-flight set loses exactly this request's head. *)
    iSplitR.
    { iPureIntro. rewrite vslot_post_seen. exact Hseen. }
    iSplitR.
    { iPureIntro. rewrite vslot_post_inflight Hah. reflexivity. }
    (* THE LATCH: released exactly when the request that held it completed.
       The device tests its HEAD and the protocol its POSITION, and the two
       agree because a head names one pending request ([vpo_hd_inj]). *)
    iSplitR.
    { iPureIntro. rewrite vslot_post_taken vps_tk.
      destruct (vp_tk pr) as [q|] eqn:Htq.
      - destruct Htkc as (slq & Hslq & Htv).
        destruct (decide (q = p)) as [->|Hne].
        + rewrite Hsl in Hslq. injection Hslq as <-.
          rewrite (bool_decide_eq_true_2 (Some p = Some p) eq_refl).
          rewrite Htv.
          by rewrite (bool_decide_eq_true_2
                        (Some (vs_hd sl) = Some (vs_hd sl)) eq_refl).
        + assert (Hqp : Some q <> Some p)
            by (intro Hc; injection Hc as <-; exact (Hne eq_refl)).
          rewrite (bool_decide_eq_false_2 (Some q = Some p) Hqp).
          rewrite Htv.
          rewrite (bool_decide_eq_false_2
                     (Some (vs_hd slq) = Some (vs_hd sl))).
          * exists slq. split; [| reflexivity ].
            rewrite (lookup_delete_ne (vp_pend pr) p q
                       (fun e => Hne (eq_sym e))).
            exact Hslq.
          * intro Hc. injection Hc as Hc.
            exact (vpo_hd_inj _ _ _ Hok q p slq sl Hne
                     (vproto_pend_slot pr _ _ Hslq) Hs Hc).
      - assert (Hnh : @None (bv 16) <> Some (vs_hd sl)) by discriminate.
        rewrite Htkc.
        by rewrite (bool_decide_eq_false_2 (@None (bv 16) = Some (vs_hd sl)) Hnh). }
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
    iSplitR; [iPureIntro; exact Hwce|].
    (* THE WRITETHROUGH ROW SURVIVES: if the completing request was the
       latched one, the gate left nothing of it in the cache and the latch is
       free; if some OTHER request holds the latch, it is still pending and
       still owns exactly what the cache holds. *)
    iSplitR.
    { iPureIntro. rewrite /vp_wt vps_tk.
      destruct (bool_decide (vp_tk pr = Some p)) eqn:Hb.
      - apply bool_decide_eq_true in Hb.
        destruct (vp_wt_head pr (v_cache v) p Hb Hwt) as (sl' & Hsl' & Hsubp).
        rewrite Hsl in Hsl'. injection Hsl' as <-.
        (* the gate: none of this request's sectors is still cached, and the
           cache holds nothing else *)
        apply map_empty. intro s.
        destruct (v_cache v !! s) as [bs2|] eqn:Hcs; [| reflexivity ].
        exfalso.
        assert (Hin : s ∈ dom (vslot_cache sl))
          by (apply elem_of_dom; exists bs2;
              exact (lookup_weaken _ _ _ _ Hcs Hsubp)).
        rewrite (vslot_cache_dom_sectors (v_cfg v) p sl pin Hslotok) in Hin.
        assert (Hboth : s ∈ vreq_touch (vs_req sl) ∩ dom (v_cache v)).
        { apply elem_of_intersection. split.
          - unfold vs_sectors in Hin.
            destruct (decide (bv_unsigned (vr_type (vs_req sl))
                              = virtio_blk_t_out)) as [Ho|Hno].
            + by rewrite (vreq_touch_out (vs_req sl) Ho).
            + exfalso. rewrite (vreq_sectors_in _ Hno) in Hin.
              by apply elem_of_empty in Hin.
          - apply elem_of_dom. by exists bs2. }
        rewrite Htouch in Hboth. by apply elem_of_empty in Hboth.
      - apply bool_decide_eq_false in Hb.
        destruct (vp_tk pr) as [q|] eqn:Htq; [| exact (vp_wt_none pr _ Htq Hwt) ].
        destruct (vp_wt_head pr (v_cache v) q Htq Hwt) as (slq & Hslq & Hsubq).
        exists slq. split; [| exact Hsubq ]. cbn [vp_pend].
        rewrite lookup_delete_ne; [exact Hslq|].
        intro Hc. apply Hb. by rewrite Hc. }
    (* the pending map lost [p]; every slot still pending owes what it owed *)
    assert (Hpmono : forall k x, delete p (vp_pend pr) !! k = Some x ->
              slot_pend_res γ (pend_todo pr (v_cache v) k x) x
              ⊢ slot_pend_res γ
                  (pend_todo (vproto_step_state pr p sl) (v_cache v) k x) x).
    { intros k x Hk. apply bi.wand_entails.
      apply lookup_delete_Some in Hk as [Hne _].
      unfold pend_todo. rewrite vps_tk.
      destruct (bool_decide (vp_tk pr = Some p)) eqn:Hb.
      - assert (Hnk : @None nat <> Some k) by discriminate.
        rewrite (bool_decide_eq_false_2 (@None nat = Some k) Hnk).
        apply bool_decide_eq_true in Hb.
        rewrite (bool_decide_eq_false_2 (vp_tk pr = Some k));
          [ iIntros "$" | rewrite Hb; intro Hc; injection Hc as <-;
                          exact (Hne eq_refl) ].
      - iIntros "$". }
    iSplitL "Hpend".
    { iApply (big_sepM_mono _ _ _ Hpmono). iExact "Hpend". }
    assert (Hdnone : vp_done pr !! p = None).
    { apply not_elem_of_dom. intro Hc.
      apply elem_of_dom in Hc as [x Hx]. exact (Hdne p x Hx eq_refl). }
    rewrite (big_sepM_insert _ (vp_done pr) p sl Hdnone).
    iSplitL "Hbs Hdone0".
    { iExists (vp_nc pr). iSplitR; [iPureIntro; apply lookup_insert|].
      iExists bs. rewrite /slot_perms_done. iFrame "Hbs Hdone0".
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
    (* THE RETAINED RECORDS keep their own used index: the insert at [p] does
       not disturb a key the done map already had. *)
    iApply (big_sepM_mono
              (fun k x => ∃ u : nat, ⌜vp_uix pr !! k = Some u⌝ ∗
                            slot_done_res γ (v_cfg v) dma u x)%I
              (fun k x => ∃ u : nat,
                            ⌜<[ p := vp_nc pr ]> (vp_uix pr) !! k = Some u⌝ ∗
                            slot_done_res γ (v_cfg v)
                              (vslot_writes (v_cfg v) (wrap16 (vp_nc pr))
                                 (v_disk v) sl ∪ dma) u x)%I).
    { intros k x Hk. iIntros "H". iDestruct "H" as (u) "[%Hu Hr]".
      iExists u. iSplitR.
      { iPureIntro. rewrite lookup_insert_ne; [exact Hu|].
        intro Hc. exact (Hdne k x Hk (eq_sym Hc)). }
      iApply (Hmono k u x Hk Hu). iExact "Hr". }
    iExact "Hdone".
  Qed.

  (* THE CAPTURE -- the head write request's data enters the device's
     volatile cache (claude-notes/completed/async-disk.md §1).  It reads the
     driver's buffer through the DMA lease ONCE, exactly as the old sector
     step did, and NOTHING ELSE MOVES: no memory write, no used-ring entry,
     no interrupt, and -- the point -- no DURABLE disk byte.  So there is no
     permit to spend, no image to move, and no [crashN] to open: a crash here
     loses the whole request, which is what the client's still-unspent
     sequential permit already says.

     WHY THE OWED SET DOES NOT MOVE.  Before the capture the head slot owes
     its whole write because nothing has been read off the bus yet; after it,
     because everything it read is still cached ([VirtioQueue.vs_todo_full]).
     Same set, so the per-slot resources ride through untouched -- which is
     why this accessor is a plain wand and not an update. *)
  (* THE POP.  The device takes the next available-ring entry: it writes no
     memory, moves no disk byte and touches no per-slot resource, so the
     invariant travels by re-keying alone.  The entry it takes names the slot
     at the pop index, and [spo_ring] is what says the head it reads is that
     slot's own. *)
  Lemma virtio_proto_pop_step (γ : disk_names) (v : virtio_state)
      (m : gmap Arch.pa (bv 8)) (mv : vmem) (v' : virtio_state) :
    mem_view m mv ->
    virtio_pop_step v mv = Some v' ->
    gen_heap_interp m -∗ virtio_proto γ v -∗
      gen_heap_interp m ∗ virtio_proto γ v'.
  Proof.
    iIntros (Hview Hstep) "Hm Hp".
    rewrite {1}/virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { exfalso. rewrite (virtio_pop_step_not_live v mv Hlive) in Hstep.
      discriminate. }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    iDestruct (dma_agree with "Hm Hdma") as %Hsub.
    assert (Hctlm : vproto_ctl (v_cfg v) pr ⊆ m)
      by (etransitivity; [exact Hctl | exact Hsub]).
    assert (Hvctl : mem_view (vproto_ctl (v_cfg v) pr) mv)
      by exact (mem_view_subseteq _ m mv Hctlm Hview).
    destruct (virtio_pop_step_shape _ _ _ Hstep) as [Hpok ->].
    unfold virtio_pop_ok in Hpok. apply andb_prop in Hpok as [_ Hne].
    apply negb_true_iff, bool_decide_eq_false in Hne.
    rewrite (avail_idx_pinned (v_cfg v) (vproto_ctl (v_cfg v) pr) mv
               (wrap16 (vp_np pr)) Hvctl (vproto_ctl_idx _ _ _ Hok)) in Hne.
    (* the pop index is strictly below the published count *)
    assert (Hlt : (vp_lo pr < vp_np pr)%nat).
    { pose proof (vpo_lo_np _ _ _ Hok) as Hle.
      destruct (decide (vp_lo pr = vp_np pr)) as [Heq|Hnq]; [| lia].
      exfalso. apply Hne. by rewrite Hseen Heq. }
    (* ...so the entry it takes is a PENDING slot's *)
    assert (Hlopd : vp_lo pr ∈ dom (vp_pend pr)).
    { apply (vpo_pend_dom _ _ _ Hok). split; [exact Hlt|].
      intro Hc. exact (Nat.lt_irrefl _ (vpo_srv_lo _ _ _ Hok _ Hc)). }
    apply elem_of_dom in Hlopd as [sl Hsl].
    assert (Hpin : exists pin, vp_pin pr !! vp_lo pr = Some pin).
    { apply elem_of_dom. rewrite (vpo_pin_dom _ _ _ Hok).
      apply elem_of_union_l, elem_of_dom. by exists sl. }
    destruct Hpin as [pin Hpin].
    pose proof (vpo_slot _ _ _ Hok _ sl pin
                  (vproto_pend_slot pr _ _ Hsl) Hpin) as Hslotok.
    assert (Hvpin : mem_view pin mv).
    { apply (mem_view_subseteq pin (vproto_ctl (v_cfg v) pr) mv);
        [ exact (vproto_pin_ctl _ pr (dom dma) _ pin Hok Hpin) | exact Hvctl ]. }
    (* THE HEAD IT READS IS THIS SLOT'S -- and it reads it out of THE LEASE'S
       OWN CELL, not out of the request's pin.  This is the whole point of
       moving the eight ring cells into the invariant: the device touches a
       ring entry only here, at the pop, so no request need hold its cell
       from publish to reclaim, and the in-flight positions are free to be
       any set rather than an interval. *)
    assert (Hhd : avail_ring_at (v_cfg v) mv (v_seen v) = vs_hd sl).
    { rewrite Hseen (avail_ring_at_wrap _ mv _ (vpo_qnum _ _ _ Hok)).
      rewrite ring_entry_is_slot.
      assert (Hmod8 : (vp_lo pr `mod` 8 < 8)%nat)
        by (apply Nat.mod_upper_bound; lia).
      assert (Hidxring : avail_idx_bytes (v_cfg v) (vp_np pr)
                           ##ₘ ring_bytes (v_cfg v) (vp_ring pr)).
      { apply map_disjoint_dom. rewrite avail_idx_bytes_dom.
        apply (gset_disj_mono (avail_idx_dom (v_cfg v)) (avail_idx_dom (v_cfg v))
                 (dom (ring_bytes (v_cfg v) (vp_ring pr)))
                 (ring_cells_dom (v_cfg v)));
          [ done | apply ring_bytes_dom
          | apply gset_disj_sym; exact (vpo_ring_idx _ _ _ Hok) ]. }
      assert (Hrsub : ring_bytes (v_cfg v) (vp_ring pr)
                        ⊆ vproto_ctl (v_cfg v) pr).
      { unfold vproto_ctl. etransitivity;
          [ apply (map_union_subseteq_r _ _ Hidxring)
          | apply map_union_subseteq_l ]. }
      rewrite (view_word_read (vproto_ctl (v_cfg v) pr) mv _ 2 _ Hvctl
                 (read_bytes_mono _ _ _ 2 _ Hrsub
                    (ring_bytes_read (v_cfg v) (vp_ring pr) _ Hmod8))).
      exact (vpo_ring _ _ _ Hok (vp_lo pr) sl ltac:(lia) Hsl). }
    iFrame "Hm".
    rewrite /virtio_proto virtio_pop_cfg Hlive.
    iExists (vproto_pop_state pr sl), dma.
    rewrite (vp_spins_pop pr sl) vpop_nc vpop_np vpop_pend vpop_done vpop_uix.
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hheads Hpend Hdone".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact (vproto_ok_pop _ _ _ sl Hok Hlt Hsl)|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR.
    { iPureIntro. rewrite virtio_pop_seen vpop_lo Hseen.
      symmetry. apply wrap16_S. }
    iSplitR.
    { iPureIntro. rewrite virtio_pop_inflight vpop_fl Hhd Hah. reflexivity. }
    iSplitR; [iPureIntro; rewrite virtio_pop_taken; exact Htkc|].
    iSplitR; [iPureIntro; rewrite virtio_pop_uidx; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iPureIntro. rewrite /vp_wt virtio_pop_cache. exact Hwt.
  Qed.

  Lemma virtio_proto_capture_step (γ : disk_names) (v : virtio_state)
      (m : gmap Arch.pa (bv 8)) (mv : vmem) (i : bv 16) (v' : virtio_state) :
    mem_view m mv ->
    virtio_capture_step v mv i = Some v' ->
    gen_heap_interp m -∗ virtio_proto γ v -∗
      gen_heap_interp m ∗ virtio_proto γ v'.
  Proof.
    iIntros (Hview Hstep) "Hm Hp".
    rewrite {1}/virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { exfalso. rewrite (virtio_capture_step_not_live v mv i Hlive) in Hstep.
      discriminate. }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    iDestruct (dma_agree with "Hm Hdma") as %Hsub.
    assert (Hctlm : vproto_ctl (v_cfg v) pr ⊆ m)
      by (etransitivity; [exact Hctl | exact Hsub]).
    assert (Hvctl : mem_view (vproto_ctl (v_cfg v) pr) mv)
      by exact (mem_view_subseteq _ m mv Hctlm Hview).
    destruct (vproto_capture_det (v_cfg v) pr (dom dma) v mv i v'
                Hok eq_refl Hseen Hah Hvctl Hstep)
      as (p & sl & pin & Hwin & Hip & Hsl & Hpin & Hslotok & Hout &
          Htk & Hv1).
    (* NOTHING WAS LATCHED, so the cache was empty: the protocol's latch is
       the device's, and [vp_wt] says an unlatched device holds nothing. *)
    assert (Htkp : vp_tk pr = None).
    { destruct (vp_tk pr) as [q|] eqn:Ht; [| reflexivity ].
      exfalso. destruct Htkc as (slq & _ & Htv).
      rewrite Htv in Htk. discriminate. }
    pose proof (vp_wt_none pr (v_cache v) Htkp Hwt) as Hcae.
    assert (Hce : vslot_cache sl ∪ v_cache v = vslot_cache sl)
      by (rewrite Hcae; apply map_union_empty).
    (* the owed sets are the same before and after: nothing was latched, so
       every pending slot owed its whole write, and the newly latched one
       owes exactly the write its capture just deposited *)
    assert (Hpmono : forall k x, vp_pend pr !! k = Some x ->
              slot_pend_res γ (pend_todo pr (v_cache v) k x) x
              ⊢ slot_pend_res γ
                  (pend_todo (vproto_capture_state pr p) (vslot_cache sl) k x)
                  x).
    { intros k x Hk. apply bi.wand_entails.
      assert (Hsrc : pend_todo pr (v_cache v) k x = vs_all x)
        by (apply pend_todo_untaken; exact Htkp).
      assert (Htgt : pend_todo (vproto_capture_state pr p) (vslot_cache sl) k x
                     = vs_all x).
      { destruct (decide (k = p)) as [->|Hne].
        - rewrite Hk in Hsl. injection Hsl as Hxs. rewrite <- Hxs.
          rewrite (pend_todo_head _ _ p x); [| reflexivity ].
          apply vs_todo_full.
        - apply (pend_todo_other (vproto_capture_state pr p) (vslot_cache sl)
                   k x). cbn [vp_tk]. intro Hc. injection Hc as <-.
          exact (Hne eq_refl). }
      rewrite Hsrc Htgt. iIntros "$". }
    iFrame "Hm".
    rewrite /virtio_proto Hv1.
    cbn [v_cfg v_isr v_seen v_inflight v_used_idx v_disk v_cache v_taken].
    rewrite Hlive Hce.
    iExists (vproto_capture_state pr p), dma.
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hheads Hdone".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact (vproto_ok_capture _ _ _ p sl Hok Hsl)|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hah|].
    (* THE CAPTURE LATCHES THIS REQUEST: the protocol names its position, the
       device the head its entry pointed at, and [Hip] is that they agree. *)
    iSplitR; [iPureIntro; cbn [vp_tk]; exists sl; split;
              [exact Hsl | by rewrite Hip]|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR.
    { iPureIntro. rewrite /vp_wt. cbn [vp_tk vp_pend]. exists sl.
      split; [exact Hsl | reflexivity]. }
    iApply (big_sepM_mono _ _ _ Hpmono). iExact "Hpend".
  Qed.

  (* THE DRAIN -- the step that actually moves the durable image
     (claude-notes/completed/sector-atomic-disk.md, restated for the write
     cache).  512 bytes of the head request's CACHED data reach the disk and
     NOTHING else moves: no memory write (the drain reads nothing off the bus
     at all), no used-ring entry, no interrupt, and the device does not
     advance to the next available-ring entry.  So this -- and no longer the
     completion -- is the linearization point of a disk write, which is why
     [WpUart.wp_disk_loop] opens [crashN] in THIS arm and no other.

     Same accessor shape as [virtio_proto_step]: the draining sector's
     PENDING token goes out, the RESIDUAL is owed back at the same key, and
     the write identity handed over is the sector's own slice
     [wr_sector (vs_wr sl) i] -- so the client's view shift is about exactly
     the 512 bytes that just became durable.  It takes NO memory interp and
     NO bus view: what identifies the drained key with a sector index of the
     head slot is the protocol's writethrough row alone
     ([vp_wt] + [VirtioQueue.vproto_drain_det]). *)
  Lemma virtio_proto_drain_step (γ : disk_names) (v : virtio_state)
      (s : Z) (v' : virtio_state) :
    virtio_drain_step v s = Some v' ->
    disk_img_auth (dn_img γ) (v_disk v) -∗ virtio_proto γ v ==∗
      ∃ (kq : nat * gname) (wr : disk_wr) (i : nat) (todo : gset nat),
        ⌜i ∈ todo⌝ ∗
        ⌜v_disk v' = wr_apply (wr_sector wr i) (v_disk v)⌝ ∗
        perm_pend (dn_perm γ) kq wr todo ∗
        (perm_pend (dn_perm γ) kq wr (todo ∖ {[ i ]}) -∗
           disk_img_auth (dn_img γ) (v_disk v') ∗ virtio_proto γ v').
  Proof.
    iIntros (Hstep) "Hauth Hp".
    iDestruct "Hauth" as (dmap) "[Hauth %Hdv]".
    rewrite {1}/virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { (* A DRAIN IS ENABLED BY THE CACHE ALONE -- even on a DEAD queue, since
         it consults no ring at all -- so this arm cannot be refuted from
         liveness the way the completion and the capture are.  What refutes
         it is the not-live arm's own cache row: a device that is not live
         was reset, and a reset drops the whole cache. *)
      iDestruct "Hp" as "(_ & _ & _ & %Hca & _)".
      exfalso. rewrite (virtio_drain_step_empty v s Hca) in Hstep.
      discriminate. }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    (* SOMETHING IS CACHED, SO SOMETHING IS LATCHED, and the drained bytes
       are that request's: [vp_wt] is what says the cache holds nothing else.
       Which POSITION it is no longer follows from the counters -- the latch
       names it, which is the whole point of carrying it. *)
    pose proof (virtio_drain_step_enabled v s v' Hstep) as Hsin.
    assert (Hlatch : exists q, vp_tk pr = Some q).
    { destruct (vp_tk pr) as [q|] eqn:Ht; [by exists q|].
      exfalso. rewrite (vp_wt_none pr (v_cache v) Ht Hwt) dom_empty_L in Hsin.
      by apply elem_of_empty in Hsin. }
    destruct Hlatch as [q Htkq].
    destruct (vp_wt_head pr (v_cache v) q Htkq Hwt) as (sl & Hsl & Hcsub).
    assert (Hqd : q ∈ dom (vp_pend pr))
      by (apply elem_of_dom; by exists sl).
    assert (Hpd : q ∈ dom (vp_pin pr)).
    { rewrite (vpo_pin_dom _ _ _ Hok). by apply elem_of_union_l. }
    apply elem_of_dom in Hpd as [pin Hpin].
    pose proof (vpo_slot _ _ _ Hok q sl pin (vproto_pend_slot pr _ _ Hsl) Hpin)
      as Hslotok.
    assert (Hdom : dom (v_cache v) ⊆ vs_sectors sl).
    { rewrite <- (vslot_cache_dom_sectors (v_cfg v) q sl pin Hslotok).
      by apply subseteq_dom. }
    destruct (vproto_drain_det (v_cfg v) q sl pin v s v'
                Hslotok Hdom Hcsub Hstep)
      as (i & Hi & Hskey & Hlk & Hv1).
    (* the device holds the latched request's HEAD, and [Htkq] names the slot *)
    assert (Htk : v_taken v = Some (vs_hd sl)).
    { rewrite Htkq in Htkc. destruct Htkc as (slq & Hslq & Htv).
      rewrite Hsl in Hslq. by injection Hslq as <-. }
    iDestruct (big_sepM_delete _ (vp_pend pr) q sl Hsl with "Hpend")
      as "[Hslres Hpend]".
    (* the LATCHED slot's owed set, spelled out -- LOCALLY, so that the other
       slots' resources ride through by frame *)
    assert (Hhtd0 : pend_todo pr (v_cache v) q sl
                    = vs_todo sl (dom (v_cache v)))
      by (rewrite (pend_todo_head _ _ q sl Htkq); reflexivity).
    rewrite Hhtd0.
    iDestruct "Hslres" as (bs)
      "(%Hbslen & %Hbspin & %Hbstorn & Hbs & Hpend0)".
    assert (Hitd : i ∈ vs_todo sl (dom (v_cache v))).
    { apply vs_todo_in; [exact Hi|]. rewrite <- Hskey.
      apply elem_of_dom. by exists (wr_sector_bytes (vs_wr sl) i). }
    assert (Hout : vs_is_out sl = true).
    { destruct (vs_is_out sl) eqn:Ho; [reflexivity|]. exfalso.
      rewrite (vs_todo_read sl (dom (v_cache v)) Ho) in Hitd.
      by apply elem_of_empty in Hitd. }
    pose proof (vslot_data_len (v_cfg v) q sl pin Hslotok Hout) as Hdl.
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
    assert (Htorn' : vs_torn sl ({[ i ]} ∪ vs_kept sl (vs_todo sl (dom (v_cache v))))
                       bs').
    { unfold bs'.
      apply (vs_torn_sector sl (v_disk v)
               (vs_kept sl (vs_todo sl (dom (v_cache v)))) i Hout Hdl).
      rewrite Hrd. exact Hbstorn. }
    (* the other pending slots owe their whole write either way *)
    assert (Hpmono : forall k x, delete q (vp_pend pr) !! k = Some x ->
              slot_pend_res γ (pend_todo pr (v_cache v) k x) x
              ⊢ slot_pend_res γ
                  (pend_todo pr (delete s (v_cache v)) k x) x).
    { intros k x Hk. apply bi.wand_entails.
      apply lookup_delete_Some in Hk as [Hne _].
      assert (Hno : vp_tk pr <> Some k)
        by (rewrite Htkq; intro Hc; injection Hc as <-; exact (Hne eq_refl)).
      rewrite (pend_todo_other pr (v_cache v) k x Hno)
              (pend_todo_other pr (delete s (v_cache v)) k x Hno).
      iIntros "$". }
    iModIntro.
    iExists (vs_perm sl), (vs_wr sl), i, (vs_todo sl (dom (v_cache v))).
    iSplitR; [iPureIntro; exact Hitd|].
    iSplitR; [iPureIntro; rewrite Hv1; reflexivity|].
    iFrame "Hpend0". iIntros "Hpend0".
    iSplitL "Hauth".
    { iExists dmap'. iFrame "Hauth". iPureIntro. exact Hdv'. }
    rewrite /virtio_proto Hv1.
    cbn [v_cfg v_isr v_seen v_inflight v_used_idx v_disk v_cache v_taken].
    rewrite Hlive.
    iExists pr, dma. iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hheads Hdone".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact Hok|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hah|].
    iSplitR; [iPureIntro; exact Htkc|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR.
    { iPureIntro. rewrite /vp_wt Htkq. exists sl. split; [exact Hsl|].
      exact (vslot_cache_sub_delete (v_cache v) sl s Hcsub). }
    iApply (big_sepM_delete _ (vp_pend pr) q sl Hsl).
    assert (Hhtd : pend_todo pr (delete s (v_cache v)) q sl
                   = vs_todo sl (dom (v_cache v)) ∖ {[ i ]}).
    { rewrite (pend_todo_head _ _ q sl Htkq) dom_delete_L Hskey.
      apply vs_todo_step. }
    rewrite Hhtd.
    iSplitR "Hpend".
    { iExists bs'. iFrame "Hbs Hpend0". iPureIntro. split_and!.
      - rewrite Hlen'. exact Hbslen.
      - intro Hc. rewrite Hout in Hc. discriminate.
      - rewrite (vs_kept_step sl (vs_todo sl (dom (v_cache v))) i Hi).
        exact Htorn'. }
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
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
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
    iFrame "Hpub". iExists pr, dma. iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hheads Hpend Hdone".
    iPureIntro. split_and!; assumption.
  Qed.

  (* A READ-ONLY LOOK AT A RING CELL.  The store below needs an address
     claim taken off the cell's own points-to before it can run, and taking
     it must not spend the staged head -- so this hands the cell out and
     takes it back exactly as it came, moving no part of the protocol.  The
     read-only sibling of [virtio_proto_ring_acc], as
     [virtio_proto_avail_idx_acc] is of the publish. *)
  Lemma virtio_proto_ring_peek (γ : disk_names) (v : virtio_state)
      (np j : nat) :
    (j < 8)%nat ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
    (∃ w : bv 16,
       phys_word2 (ring_slot_pa (v_cfg v) j) w ∗
       (phys_word2 (ring_slot_pa (v_cfg v) j) w -∗
          virtio_proto γ v ∗ disk_pub γ np)).
  Proof.
    intro Hj.
    iIntros "Hp Hpub". rewrite /virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    iDestruct (ghost_var_agree with "Hnp Hpub") as %Hnpeq.
    assert (Hringsub : ring_bytes (v_cfg v) (vp_ring pr) ⊆ dma).
    { etransitivity; [| exact Hctl ]. unfold vproto_ctl.
      etransitivity;
        [ apply (map_union_subseteq_r _ _
                   (idx_ring_bytes_disj (v_cfg v) (vp_np pr) (vp_ring pr)
                      (vpo_ring_idx _ _ _ Hok)))
        | apply map_union_subseteq_l ]. }
    pose proof (read_bytes_mono _ _ _ 2 _ Hringsub
                  (ring_bytes_read (v_cfg v) (vp_ring pr) j Hj)) as Hcellread.
    assert (Hcellsub : range_map (ring_slot_pa (v_cfg v) j) 2
                         (nth_byte (vp_ring pr j)) ⊆ dma).
    { apply range_map_sub; [lia|]. intros k Hk.
      apply (read_bytes_spec dma (ring_slot_pa (v_cfg v) j) 2 _ Hcellread). lia. }
    iDestruct (dma_own_acc_same _ dma Hcellsub with "Hdma") as "[Hcell Hback]".
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iSplitR; [iPureIntro; exact Hal|].
    iExists (vp_ring pr j). rewrite phys_word2_map. iFrame "Hcell".
    iIntros "Hcell".
    iDestruct ("Hback" with "Hcell") as "Hdma".
    iFrame "Hpub". iExists pr, dma.
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hheads Hpend Hdone".
    iPureIntro. split_and!; assumption.
  Qed.

  (* ==================================================================== *)
  (* driver operation 4: THE POLL, and THE COLLECT                        *)
  (*                                                                      *)
  (*     while (b->disk == 1) { sleep_prepare(b); release; sleep; acquire; }
         disk.info[idx[0]].b = 0;
         free_chain(idx[0]);                                              *)
  (*                                                                      *)
  (* The receipt is what re-authorises the poll on every re-acquire: the   *)
  (* caller has held [HActive dc] since its publish, across [sleep()]'s    *)
  (* release of vdisk_lock, and it names the buffer whose [b->disk] the    *)
  (* loop reads.                                                          *)
  (*                                                                      *)
  (* THE READ IS WHAT COLLECTS.  The value decides: read 1 and the receipt *)
  (* goes back untouched, so the loop may spin any number of times; read 0 *)
  (* and the deposit has already happened, so this step is also where the  *)
  (* whole chain comes home -- the receipt retires to INACTIVE and the     *)
  (* caller walks away owning [chain_back], [disk.info[i].b] and           *)
  (* [b->disk].  Splitting that into a separate collect accessor is not    *)
  (* possible: the loop only ever learns the VALUE 0, never the cell, and  *)
  (* an accessor demanding [b_disk ↦₄ 0] up front could never be applied   *)
  (* (the ACTIVE entry owns that cell too, so the premises are jointly     *)
  (* contradictory and the lemma is vacuous).  Deciding at the read is     *)
  (* what makes the transfer expressible.                                 *)
  (* ==================================================================== *)

  Lemma virtio_proto_poll_acc (γ : disk_names) (v : virtio_state)
      (np i : nat) (dc : dclaim) :
    Z.to_nat (bv_unsigned (vr_head (vs_req (dc_slot dc)))) = i ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    i ↪[dn_head γ] HActive dc -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    (∃ w : SailStdpp.Values.mword 32,
       b_disk (dc_buf dc) ↦₄ w ∗
       (* [b->disk] is 0 exactly when the chain is back inside the receipt --
          which is the whole point of the loop's test, and the value read is
          what decides whether this step also retires the slot *)
       (b_disk (dc_buf dc) ↦₄ w ==∗
          virtio_proto γ v ∗ disk_pub γ np ∗
          ((⌜w = (SailStdpp.Values.mword_of_int (len := 32) 1)⌝ ∗
            i ↪[dn_head γ] HActive dc)
           ∨ (⌜w = (SailStdpp.Values.mword_of_int (len := 32) 0)⌝ ∗
              i ↪[dn_head γ] HInactive ∗
              (* the claim's row, to retire under the lock at free_chain *)
              dc_pos dc ↪[dn_claim γ] dc ∗
              d_info_b i ↦₈ (dc_buf dc : SailStdpp.Values.mword 64) ∗
              b_disk (dc_buf dc) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 0) ∗
              chain_back γ (dc_slot dc) (dc_pin dc))))).
  Proof.
    intro Hhd.
    iIntros "Hp Hpub Hfrag". rewrite /virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    iDestruct "Hheads" as (hs) "(%Hhdom & %Hhcoup & Hhauth & Hhbig)".
    iDestruct (ghost_map_lookup with "Hhauth Hfrag") as %Hhlk.
    iDestruct (big_sepM_delete _ hs i (HActive dc) Hhlk with "Hhbig")
      as "[Hent Hrest]".
    rewrite {1}/head_res.
    iDestruct "Hent" as "(%Hdchd & Hclaim & Hinfo & Hdisj)".
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    (* either way the entry owns [b->disk]; the loop only reads it *)
    iDestruct "Hdisj" as "[[Hbd Hrest2] | [Hbd Hrest2]]".
    - iExists (SailStdpp.Values.mword_of_int (len := 32) 1).
      iFrame "Hbd". iIntros "Hbd". iModIntro.
      iFrame "Hpub". iSplitR "Hfrag"; [| iLeft; by iFrame "Hfrag"].
      iExists pr, dma.
      iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hpend Hdone".
      iSplitR; [iPureIntro; exact Hctl|].
      iSplitR; [iPureIntro; exact Hok|].
      iSplitR; [iPureIntro; exact Hal|].
      iSplitR; [iPureIntro; exact Hseen|].
      iSplitR; [iPureIntro; exact Hah|].
      iSplitR; [iPureIntro; exact Htkc|].
      iSplitR; [iPureIntro; exact Hui|].
      iSplitR; [iPureIntro; exact Hridx|].
      iSplitR; [iPureIntro; exact Hwce|].
      iSplitR; [iPureIntro; exact Hwt|].
      iExists hs. iFrame "Hhauth".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
      rewrite (big_sepM_delete _ hs i (HActive dc) Hhlk).
      iFrame "Hrest". rewrite /head_res.
      iSplitR; [by iPureIntro|]. iFrame "Hclaim Hinfo". iLeft. iFrame "Hbd Hrest2".
    - (* THE CHAIN IS BACK.  This read is the collect: take the disjointness
         the coupling obligation needs while the chain is still a hypothesis,
         then retire the receipt and hand the caller everything. *)
      rewrite {1}/chain_back.
      iDestruct "Hrest2" as "(Hpinm & Hbst & Hbpm & Hbbs)".
      iDestruct (dma_own_disj with "Hdma Hpinm") as %Hdj.
      iAssert (chain_back γ (dc_slot dc) (dc_pin dc))
        with "[Hpinm Hbst Hbpm Hbbs]" as "Hback".
      { rewrite /chain_back. iFrame "Hpinm Hbst Hbpm Hbbs". }
      iExists (SailStdpp.Values.mword_of_int (len := 32) 0).
      iFrame "Hbd". iIntros "Hbd".
      iMod (ghost_map_update HInactive with "Hhauth Hfrag") as "[Hhauth Hfrag]".
      iModIntro. iFrame "Hpub".
      iSplitR "Hfrag Hclaim Hinfo Hbd Hback".
      2:{ iRight. iSplitR; [done|]. iFrame "Hfrag Hclaim Hbd Hback". iExact "Hinfo". }
      iExists pr, dma.
      iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hpend Hdone".
      iSplitR; [iPureIntro; exact Hctl|].
      iSplitR; [iPureIntro; exact Hok|].
      iSplitR; [iPureIntro; exact Hal|].
      iSplitR; [iPureIntro; exact Hseen|].
      iSplitR; [iPureIntro; exact Hah|].
      iSplitR; [iPureIntro; exact Htkc|].
      iSplitR; [iPureIntro; exact Hui|].
      iSplitR; [iPureIntro; exact Hridx|].
      iSplitR; [iPureIntro; exact Hwce|].
      iSplitR; [iPureIntro; exact Hwt|].
      iExists (<[ i := HInactive ]> hs). iFrame "Hhauth".
      iSplitR; [iPureIntro; rewrite dom_insert_L Hhdom;
                apply subseteq_union_1_L, singleton_subseteq_l;
                rewrite -Hhdom; apply elem_of_dom; by exists (HActive dc)|].
      iSplitR.
      { (* THIS REQUEST IS NO LONGER LIVE, so no live one has this head.
           The chain is in the caller's hands now, hence not in the lease --
           and a live request's pinned bytes are.  The head descriptor's own
           byte would have to be in both, which cannot be. *)
        iPureIntro. intros q sl' pin' Hq.
        destruct (Hhcoup q sl' pin' Hq) as (w & Hw & Hws).
        destruct (decide (Z.to_nat (bv_unsigned (vr_head (vs_req sl'))) = i))
          as [Heq|Hne].
        - exfalso. rewrite Heq Hhlk in Hw. injection Hw as <-.
          destruct Hws as (Hsl' & Hpin' & _).
          apply map_lookup_zip_with_Some in Hq as (sl2 & pin2 & Heq2 & Hsl2 & Hpin2).
          injection Heq2 as <- <-.
          pose proof (vpo_fp_D _ _ _ Hok q sl' pin' Hsl2 Hpin2) as HfpD.
          pose proof (spo_desc _ _ _ _ (vpo_slot _ _ _ Hok q sl' pin' Hsl2 Hpin2))
            as Hdesc.
          rewrite Hpin' in Hdj.
          exact (proj1 (elem_of_disjoint _ _) Hdj _ Hdesc
                   (HfpD _ (slot_fp_pin sl' pin' _ Hdesc))).
        - exists w. rewrite lookup_insert_ne; [| exact (not_eq_sym Hne) ].
          by split. }
      rewrite (big_sepM_delete _ (<[ i := HInactive ]> hs) i HInactive);
        [| apply lookup_insert ].
      rewrite delete_insert_delete. rewrite /head_res.
      iSplitR; [done|]. iExact "Hrest".
  Qed.

  (* [b->disk] cannot be owned twice.  [BioInv]'s [word4_pointsto_excl] says
     the same thing but sits above this file, so the two-line proof is
     repeated here rather than inverting the layering. *)
  Lemma vp_word4_excl (a : Arch.pa) (w1 w2 : SailStdpp.Values.mword 32) :
    a ↦₄ w1 -∗ a ↦₄ w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (word4_pointsto_bytes with "H1") as "H1".
    iDestruct (word4_pointsto_bytes with "H2") as "H2".
    cbn [seq].
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (mem_pointsto_ne with "Hb1 Hb2") as %Hne. done.
  Qed.


  (* ==================================================================== *)
  (* driver operation 1b: THE RING STORE                                  *)
  (*                                                                      *)
  (*     disk.avail->ring[disk.avail->idx % NUM] = idx[0];                *)
  (*                                                                      *)
  (* the instruction BEFORE the fence and the index bump.  The cell is the *)
  (* lease's, so the store goes through the invariant rather than through  *)
  (* a cell the request has been holding since its own publish -- which is *)
  (* the whole point of moving the cells: a request that owns no ring cell *)
  (* can stay in flight while the positions around it come and go, and     *)
  (* that is what the out-of-order completion fix needs (finding 5).       *)
  (*                                                                      *)
  (* The invariant is UNCHANGED as a device-visible object: [v] is the     *)
  (* same state, and the device cannot tell -- it reads a cell only when   *)
  (* it pops, and it cannot pop a position [avail->idx] has not announced. *)
  (* What moves is [vp_ring], and the staged-head token records it.        *)
  (* ==================================================================== *)

  Lemma virtio_proto_ring_acc (γ : disk_names) (v : virtio_state)
      (np : nat) (h : bv 16) :
    virtio_proto γ v -∗ disk_pub γ np -∗
    disk_stage γ None -∗
    (* THE HEAD IS FRESH: its receipt is still INACTIVE.  That is what says
       the cell being overwritten is nobody else's -- at most seven positions
       can be waiting to be popped, because their heads and this one would
       otherwise be nine distinct descriptors ([heads_res_at_window]). *)
    (Z.to_nat (bv_unsigned h)) ↪[dn_head γ] HInactive -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
    (∃ w : bv 16, phys_word2 (ring_slot_pa (v_cfg v) (np `mod` 8)%nat) w) ∗
    (phys_word2 (ring_slot_pa (v_cfg v) (np `mod` 8)%nat) h ==∗
       virtio_proto γ v ∗ disk_pub γ np ∗
       disk_stage γ (Some h) ∗
       (Z.to_nat (bv_unsigned h)) ↪[dn_head γ] HInactive).
  Proof.
    iIntros "Hp Hpub Hstg Hfrag". rewrite /virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    iDestruct (ghost_var_agree with "Hnp Hpub") as %Hnpeq.
    iDestruct "Hstage" as (st) "[Hstage %Hstc]".
    iDestruct (ghost_var_agree with "Hstage Hstg") as %->.
    (* work in the invariant's own vocabulary from here: the publish count is
       the protocol's, so the cell index is too, and the projection lemmas
       below produce exactly that form. *)
    subst np.
    iDestruct (heads_res_at_window γ (v_cfg v) pr (dom dma) _ Hok
                 with "Hheads Hfrag") as %Hnotfull.
    assert (Hk8 : ((vp_np pr `mod` 8)%nat < 8)%nat)
      by (apply Nat.mod_upper_bound; lia).
    (* the cell's CURRENT bytes come out of the lease *)
    assert (Hringsub : ring_bytes (v_cfg v) (vp_ring pr) ⊆ dma).
    { etransitivity; [| exact Hctl ]. unfold vproto_ctl.
      etransitivity;
        [ apply (map_union_subseteq_r _ _
                   (idx_ring_bytes_disj (v_cfg v) (vp_np pr) (vp_ring pr)
                      (vpo_ring_idx _ _ _ Hok)))
        | apply map_union_subseteq_l ]. }
    pose proof (read_bytes_mono _ _ _ 2 _ Hringsub
                  (ring_bytes_read (v_cfg v) (vp_ring pr) (vp_np pr `mod` 8)%nat Hk8)) as Hcellread.
    assert (Hcellsub : range_map (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2
                         (nth_byte (vp_ring pr (vp_np pr `mod` 8)%nat)) ⊆ dma).
    { apply range_map_sub; [lia|]. intros j Hj.
      apply (read_bytes_spec dma (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2 _ Hcellread). lia. }
    assert (Hcelldom : dom (range_map (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2 (nth_byte h))
                       = dom (range_map (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2
                                (nth_byte (vp_ring pr (vp_np pr `mod` 8)%nat))))
      by (rewrite !range_map_dom; reflexivity).
    iDestruct (dma_own_acc _ _ dma Hcellsub Hcelldom with "Hdma")
      as "[Hcell Hback]".
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitL "Hcell";
      [ iExists (vp_ring pr (vp_np pr `mod` 8)%nat); rewrite phys_word2_map; iFrame "Hcell" |].
    rewrite phys_word2_map.
    iIntros "Hcell".
    iDestruct ("Hback" with "Hcell") as "Hdma".
    (* the protocol moves to the updated ring *)
    iMod (ghost_var_update_halves (Some h) with "Hstage Hstg") as "[Hstage Hstg]".
    iModIntro.
    (* split the DRIVER's tokens off first: both halves of the staged-head
       cell are in scope here, and framing before the split lets the
       invariant's own row swallow the one the caller is owed. *)
    iSplitR "Hpub Hstg Hfrag"; last first.
    { rewrite /disk_stage. iFrame "Hpub Hstg Hfrag". }
    iExists (vproto_ring_state pr h),
      (range_map (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2 (nth_byte h) ∪ dma).
    rewrite (vp_spins_ring pr h) ?vprg_nc ?vprg_np ?vprg_pend ?vprg_done
            ?vprg_uix ?vprg_lo ?vprg_fl ?vprg_tk ?vprg_nr ?vprg_slots.
    (* the ring store changes only [vp_ring]; the slots -- hence the
       receipts -- are untouched *)
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hheads Hpend".
    assert (Hundom : dom (range_map (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2 (nth_byte h)
                            ∪ dma) = dom dma).
    { apply dom_union_sub. rewrite Hcelldom. apply subseteq_dom. exact Hcellsub. }
    (* THE NEW CONTROL MAP: index and pins as they were, ring cells with one
       byte pair replaced. *)
    assert (Hringnew : ring_bytes (v_cfg v) (vp_ring (vproto_ring_state pr h))
                       = range_map (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2 (nth_byte h)
                         ∪ ring_bytes (v_cfg v) (vp_ring pr)).
    { rewrite ?vprg_ring. apply map_eq. intro a.
      destruct (decide (a ∈ pa_range (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2))
        as [Hin|Hout].
      - apply pa_range_elim in Hin as (i & Hi & ->).
        change (N.to_nat 2) with 2%nat in Hi.
        rewrite (lookup_union_Some_l _ _ _ (nth_byte h i));
          [| apply range_map_lookup; lia ].
        assert (Hread : read_bytes (ring_bytes (v_cfg v)
                          (fun j => if bool_decide (j = (vp_np pr `mod` 8)%nat) then h
                                    else vp_ring pr j))
                          (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2 = Some h).
        { rewrite (ring_bytes_read (v_cfg v) _ (vp_np pr `mod` 8)%nat Hk8).
          by rewrite (bool_decide_eq_true_2 ((vp_np pr `mod` 8)%nat = (vp_np pr `mod` 8)%nat) eq_refl). }
        exact (read_bytes_spec _ _ _ _ Hread i ltac:(lia)).
      - rewrite (lookup_union_r _ _ _
                   (range_map_lookup_out _ 2 (nth_byte h) a Hout)).
        apply (ring_bytes_off (v_cfg v) _ _ (vp_np pr `mod` 8)%nat a Hk8); [| exact Hout ].
        intros j _ Hjk. by rewrite (bool_decide_eq_false_2 (j = (vp_np pr `mod` 8)%nat) Hjk). }
    (* the cell's two bytes sit inside the ring region *)
    assert (Hcellring : pa_range (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2
                        ⊆ ring_cells_dom (v_cfg v))
      by (apply pa_range_ring_cells; exact Hk8).
    assert (Hidxsub : avail_idx_bytes (v_cfg v) (vp_np pr) ⊆ dma).
    { etransitivity; [| exact Hctl ]. unfold vproto_ctl.
      etransitivity; [ apply map_union_subseteq_l | apply map_union_subseteq_l ]. }
    assert (Hpinsub : pins_union (vp_pin pr) ⊆ dma)
      by (etransitivity;
          [ exact (pins_union_ctl (v_cfg v) pr (dom dma) Hok) | exact Hctl ]).
    iSplitR.
    { iPureIntro. rewrite (vproto_ring_ctl (v_cfg v) pr h) Hringnew.
      apply map_union_least.
      - apply map_union_least.
        + (* the index word is untouched and clear of the cell *)
          apply virtio_ctl_union; [| exact Hidxsub ].
          rewrite range_map_dom avail_idx_bytes_dom.
          apply (gset_disj_sub_l _ (ring_cells_dom (v_cfg v)));
            [ exact Hcellring | exact (vpo_ring_idx _ _ _ Hok) ].
        + (* the ring cells: the new pair in front of the lease's own *)
          apply map_union_mono_r. exact Hringsub.
      - (* the pins never overlap the ring region at all *)
        apply virtio_ctl_union; [| exact Hpinsub ].
        rewrite range_map_dom. apply gset_disj_sym.
        apply (gset_disj_sub_r _ _ (avail_idx_dom (v_cfg v)
                 ∪ ring_cells_dom (v_cfg v) ∪ used_page_pas (v_cfg v)));
          [ etransitivity;
              [ exact Hcellring
              | etransitivity;
                  [ apply (union_subseteq_r (avail_idx_dom (v_cfg v)))
                  | apply union_subseteq_l ] ]
          | exact (pins_union_off_standing (v_cfg v) pr (dom dma) Hok) ]. }
    iSplitR; [iPureIntro; rewrite Hundom; exact (vproto_ok_ring _ _ _ h Hok Hnotfull)|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hah|].
    iSplitR; [iPureIntro; exact Htkc|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR.
    { iPureIntro. apply (read_bytes_transfer dma); [| exact Hridx].
      intros j Hj. assert (Hj2 : (j < 2)%nat) by lia.
      rewrite lookup_union_r; [reflexivity|].
      apply range_map_lookup_out. intro Hc.
      apply (pa_range_ring_cells (v_cfg v) (vp_np pr `mod` 8)%nat Hk8) in Hc.
      exact (proj1 (elem_of_disjoint _ _) (vpo_ring_used _ _ _ Hok)
               _ Hc (used_idx_in_page (v_cfg v) j Hj2)). }
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR; [iPureIntro; rewrite /vp_wt vprg_tk vprg_pend; exact Hwt|].
    (* ...the staged head now names the cell just written... *)
    iSplitL "Hstage".
    { iExists (Some h). iFrame "Hstage". iPureIntro.
      rewrite ?vprg_ring ?vprg_np.
      by rewrite (bool_decide_eq_true_2
                    ((vp_np pr `mod` 8)%nat = (vp_np pr `mod` 8)%nat) eq_refl). }
    (* ...and the completed records survive the two changed bytes, which lie
       in the ring region and so touch no used record and no slot. *)
    assert (Hframe : forall x : Arch.pa, x ∉ ring_cells_dom (v_cfg v) ->
              (range_map (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2 (nth_byte h) ∪ dma) !! x
              = dma !! x).
    { intros x Hx. rewrite lookup_union_r; [reflexivity|].
      apply range_map_lookup_out. intro Hc. exact (Hx (Hcellring _ Hc)). }
    assert (Hmono : forall q u x, vp_done pr !! q = Some x ->
              vp_uix pr !! q = Some u ->
              slot_done_res γ (v_cfg v) dma u x
              ⊢ slot_done_res γ (v_cfg v)
                  (range_map (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2 (nth_byte h) ∪ dma)
                  u x).
    { intros q u x Hq Hu. apply bi.wand_entails.
      pose proof (vproto_done_slot (v_cfg v) pr (dom dma) q x Hok Hq) as Hks.
      assert (Hkpin : exists pinq, vp_pin pr !! q = Some pinq).
      { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
        apply elem_of_dom. exists x. exact Hks. }
      destruct Hkpin as [pinq Hpinq].
      pose proof (vpo_standing _ _ _ Hok q x pinq Hks Hpinq) as Hstq.
      apply slot_done_res_mono.
      - intros j Hj. apply Hframe. intro Hc.
        exact (proj1 (elem_of_disjoint _ _) (vpo_ring_used _ _ _ Hok) _ Hc
                 (used_elem_pa_in_page (v_cfg v) u j Hj)).
      - assert (Hstin : vr_status (vs_req x) ∈ slot_fp x pinq).
        { apply slot_fp_wr. unfold slot_wr.
          apply elem_of_union_l, elem_of_singleton. reflexivity. }
        apply Hframe. intro Hc.
        exact (proj1 (elem_of_disjoint _ _) Hstq _ Hstin
                 (elem_of_union_l _ _ _ (elem_of_union_r _ _ _ Hc))).
      - intros Hox j Hj.
        assert (Hbin : pa_add (vr_buf (vs_req x)) j ∈ slot_fp x pinq).
        { apply slot_fp_wr. unfold slot_wr. rewrite Hox.
          apply elem_of_union_r, pa_range_intro. exact Hj. }
        apply Hframe. intro Hc.
        exact (proj1 (elem_of_disjoint _ _) Hstq _ Hbin
                 (elem_of_union_l _ _ _ (elem_of_union_r _ _ _ Hc))). }
    iApply (big_sepM_mono
              (fun q x => ∃ u : nat, ⌜vp_uix pr !! q = Some u⌝ ∗
                            slot_done_res γ (v_cfg v) dma u x)%I
              (fun q x => ∃ u : nat, ⌜vp_uix pr !! q = Some u⌝ ∗
                            slot_done_res γ (v_cfg v)
                              (range_map (ring_slot_pa (v_cfg v) (vp_np pr `mod` 8)%nat) 2
                                 (nth_byte h) ∪ dma) u x)%I).
    { intros q x Hq. iIntros "H". iDestruct "H" as (u) "[%Hu Hr]".
      iExists u. iSplitR; [by iPureIntro|].
      iApply (Hmono q u x Hq Hu). iExact "Hr". }
    iExact "Hdone".
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
      (np : nat) (sl : vslot) (dc : dclaim) (pin wrb : gmap Arch.pa (bv 8)) :
    slot_pin_ok (v_cfg v) np sl pin ->
    (* the receipt below is THIS chain's, at THIS position *)
    dc_slot dc = sl -> dc_pos dc = np -> dc_pin dc = pin ->
    dom wrb = slot_wr sl ->
    slot_wr sl ## dom pin ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    (* THE RING STORE ALREADY HAPPENED.  Spent here: after the bump the cell
       this names is an OLDER position's, so the invariant goes back to
       holding nothing staged. *)
    disk_stage γ (Some (vs_hd sl)) -∗
    (* THE RECEIPT for this chain's head, still INACTIVE -- the allocator
       handed it over with the slot and nothing has published it since. *)
    (Z.to_nat (bv_unsigned (vr_head (vs_req sl)))) ↪[dn_head γ] HInactive -∗
    (* THE CLAIM'S ROW in the vdisk_lock's map, inserted by the publisher
       under the lock ([DiskInv.disk_res]); it goes into the receipt with
       the cells, and comes back out with the chain. *)
    np ↪[dn_claim γ] dc -∗
    (* ...and the two driver-side cells the publish transfers in with it:
       [disk.info[id].b], written back at +0x172, and [b->disk], set to 1 at
       +0x16e.  This store is where the device gets the chain, so this is
       where they stop being the driver's (finding 5). *)
    d_info_b (Z.to_nat (bv_unsigned (vr_head (vs_req sl))))
      ↦₈ (dc_buf dc : SailStdpp.Values.mword 64) -∗
    b_disk (dc_buf dc) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1) -∗
    phys_map pin -∗ phys_map wrb -∗
    (* NOTHING HAS DRAINED YET: a freshly published request owes its whole
       write, which is exactly the root of the sequential permit and exactly
       what [PermInv.perm_deposit_kq] hands the enqueuer back. *)
    slot_pend_res γ (vs_all sl) sl -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    phys_word2 (avail_idx_pa (v_cfg v)) (wrap16 np) ∗
    (phys_word2 (avail_idx_pa (v_cfg v)) (wrap16 (S np)) ==∗
       virtio_proto γ v ∗ disk_pub γ (S np) ∗
       disk_stage γ None ∗
       (* THE RECEIPT GOES ACTIVE.  The [dn_slot] fragment the publish mints
          does NOT come back to the caller: it goes into the receipt, and the
          interrupt handler takes it from there to retire the slot.  What the
          caller keeps is this token, which it holds across [sleep()]. *)
       (Z.to_nat (bv_unsigned (vr_head (vs_req sl)))) ↪[dn_head γ] HActive dc).
  Proof.
    intros Hslotok Hdcsl Hdcpos Hdcpin Hwrbdom Hwrpin.
    iIntros "Hp Hpub Hstg Hfrag Hclaim Hinfo Hbd Hpin Hwrb Hpres".
    rewrite {1}/virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    iDestruct (ghost_var_agree with "Hnp Hpub") as %Hnpeq.
    (* the caller's own receipt, read against the invariant's authority
       while both are in hand -- the observation is pure, so the fragment
       survives to be handed back *)
    iDestruct "Hheads" as (hs) "(%Hhdom & %Hhcoup & Hhauth & Hhbig)".
    iDestruct (ghost_map_lookup with "Hhauth Hfrag") as %Hlk.
    (* THE STAGED HEAD, cashed in: the coupling row says the cell position
       [np] is about to use already names this chain. *)
    iDestruct "Hstage" as (st) "[Hstage %Hstc]".
    iDestruct (ghost_var_agree with "Hstage Hstg") as %->.
    (* ...and the window bound: this head is a ninth descriptor otherwise *)
    pose proof (heads_window_pure (v_cfg v) pr (dom dma) hs _ Hok Hhdom Hhcoup Hlk)
      as Hnotfull.
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
                  Hok Hslotok' Hwrpin Hfpd Hstc Hnotfull) as Hok'.
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
      - destruct (proj1 (vpo_pend_dom _ _ _ Hok (vp_np pr)) Hc) as [Hlt _]. lia.
      - pose proof (vpo_srv_np _ _ _ Hok _ (vpo_done_lt _ _ _ Hok _ Hc)). lia. }
    assert (Hpendnone : vp_pend pr !! vp_np pr = None).
    { destruct (vp_pend pr !! vp_np pr) as [x|] eqn:Hc; [| reflexivity ].
      rewrite (vproto_pend_slot pr _ _ Hc) in Hslnone. discriminate. }
    iMod (ghost_map_insert (vp_np pr) (sl, pin) with "Hslot") as "[Hslot Hrec]";
      [ exact (vp_spins_none pr (vp_np pr) Hslnone) |].
    iMod (ghost_var_update_halves (S np) with "Hnp Hpub") as "[Hnp Hpub]".
    (* THE STAGE GOES BACK TO EMPTY.  It has to: the coupling row speaks about
       the cell at [vp_np], and that is a different cell after the bump. *)
    iMod (ghost_var_update_halves (None : option (bv 16)) with "Hstage Hstg")
      as "[Hstage Hstg]".
    (* the caller's receipt goes ACTIVE *)
    iMod (ghost_map_update (HActive dc) with "Hhauth Hfrag") as "[Hhauth Hfrag]".
    (* rebuild *)
    iModIntro. rewrite /disk_stage.
    iFrame "Hpub Hstg Hfrag".
    rewrite /virtio_proto Hlive.
    iExists (vproto_publish_state pr sl pin),
      (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
         (nth_byte (wrap16 (S np))) ∪ dma))).
    rewrite (vp_spins_publish pr sl pin) vpp_nc vpp_np vpp_pend vpp_done Hnpeq.
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr".
    iSplitR.
    (* the ring cells are the lease's and this publish does not touch them *)
    assert (Hringsub : ring_bytes (v_cfg v) (vp_ring pr) ⊆ dma).
    { etransitivity; [| exact Hctl ]. unfold vproto_ctl.
      etransitivity;
        [ apply (map_union_subseteq_r _ _
                   (idx_ring_bytes_disj (v_cfg v) (vp_np pr) (vp_ring pr)
                      (vpo_ring_idx _ _ _ Hok)))
        | apply map_union_subseteq_l ]. }
    assert (Hringdom : dom (ring_bytes (v_cfg v) (vp_ring pr)) ⊆ dom dma)
      by (apply subseteq_dom; exact Hringsub).
    { iPureIntro. rewrite Hctl'. apply map_union_least.
      - apply map_union_least.
        + rewrite (avail_idx_bytes_range (v_cfg v) (S np)).
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
        + (* ...and they were already in the lease, clear of the pin, of the
             writable footprint, and of the index word *)
          apply virtio_ctl_union.
          { apply gset_disj_sym.
            apply (gset_disj_sub_l _ (dom dma)); [ exact Hringdom |].
            apply gset_disj_sym. exact Hpind. }
          apply virtio_ctl_union.
          { apply gset_disj_sym. rewrite Hwrbdom.
            apply (gset_disj_sub_l _ (dom dma)); [ exact Hringdom |].
            apply gset_disj_sym. exact Hwrbd. }
          apply virtio_ctl_union.
          { rewrite HdomMMS (ring_bytes_dom_eq (v_cfg v) (vp_ring pr)).
            apply gset_disj_sym. exact (vpo_ring_idx _ _ _ Hok). }
          exact Hringsub.
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
                   ∪ ring_cells_dom (v_cfg v) ∪ used_page_pas (v_cfg v)));
            [ etransitivity;
                [ apply (union_subseteq_l (avail_idx_dom (v_cfg v))
                           (ring_cells_dom (v_cfg v)))
                | apply union_subseteq_l ]
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
    iSplitR; [iPureIntro; exact Hah|].
    (* THE LATCH SURVIVES THE PUBLISH: a latched position is pending, hence
       below [np], so the fresh slot's insert does not disturb its slot. *)
    iSplitR.
    { iPureIntro. rewrite vpp_tk.
      destruct (vp_tk pr) as [q|] eqn:Htq; [| exact Htkc ].
      destruct Htkc as (slq & Hslq & Htv). exists slq. split; [| exact Htv ].
      rewrite lookup_insert_ne; [exact Hslq|].
      (* the latched position is PENDING, and [np] is not *)
      intro Hc. congruence. }
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR.
    { iPureIntro. apply (read_bytes_transfer dma); [| exact Hridx].
      intros j Hj. assert (Hj2 : (j < 2)%nat) by lia.
      apply Hframe.
      - apply (vpo_used_D _ _ _ Hok). exact (used_idx_in_page (v_cfg v) j Hj2).
      - intro Hc. exact (proj1 (elem_of_disjoint _ _) (vpo_idx_used _ _ _ Hok)
                           _ Hc (used_idx_in_page (v_cfg v) j Hj2)). }
    iSplitR; [iPureIntro; exact Hwce|].
    (* THE WRITETHROUGH ROW, one publish later.  If the queue was IDLE the
       new slot becomes the head, and the row's "no head" branch already said
       the cache is empty and untaken -- so the fresh slot inherits an empty
       cache, which is what puts its permit at the ROOT.  If the queue was
       busy the head is unchanged and so is the row. *)
    assert (Hwt' : vp_wt (vproto_publish_state pr sl pin) (v_cache v)).
    { rewrite /vp_wt vpp_tk vpp_pend. rewrite /vp_wt in Hwt.
      destruct (vp_tk pr) as [q|] eqn:Htq; [| exact Hwt ].
      destruct Hwt as (slq & Hslq & Hsubq).
      exists slq. split; [| exact Hsubq ].
      rewrite lookup_insert_ne; [exact Hslq|].
      intro Hc. subst q. rewrite Hslq in Hpendnone. discriminate. }
    iSplitR; [iPureIntro; exact Hwt'|].
    (* nothing is staged once the bump has landed *)
    iSplitL "Hstage"; [by iExists None; iFrame "Hstage"|].
    (* THE RECEIPTS: this store is the handover, so the entry flips INACTIVE
       -> ACTIVE here and the two driver-side cells move in with it.  The
       coupling also gains a slot to cover, and the caller's own receipt is
       what covers it. *)
    iSplitL "Hhauth Hhbig Hrec Hclaim Hinfo Hbd".
    { rewrite /heads_res_at.
      set (i := Z.to_nat (bv_unsigned (vr_head (vs_req sl)))).
      iDestruct (big_sepM_delete _ hs i HInactive Hlk with "Hhbig")
        as "[_ Hrest]".
      iExists (<[ i := HActive dc ]> hs). iFrame "Hhauth".
      iSplitR; [iPureIntro; rewrite dom_insert_L Hhdom;
                apply subseteq_union_1_L, singleton_subseteq_l;
                rewrite -Hhdom; apply elem_of_dom; by exists HInactive|].
      iSplitR.
      { (* the rebuild's own rewrite already put [vp_spins] in insert form *)
        iPureIntro. intros q sl' pin' Hq.
        apply lookup_insert_Some in Hq as [[<- Heqx]|[_ Hq]].
        - injection Heqx as <- <-. exists dc.
          subst i. rewrite Hdcsl lookup_insert.
          split_and!; [reflexivity | reflexivity | exact Hdcpin | exact Hdcpos].
        - (* an OLDER live request cannot have this head: the coupling would
             put its entry ACTIVE, and it was INACTIVE *)
          destruct (Hhcoup q sl' pin' Hq) as (w & Hw & Hws).
          destruct (decide (Z.to_nat (bv_unsigned (vr_head (vs_req sl'))) = i))
            as [Heq|Hne].
          + exfalso. subst i. rewrite Heq Hlk in Hw. discriminate.
          + exists w. rewrite lookup_insert_ne; [| exact (not_eq_sym Hne) ].
            by split. }
      rewrite (big_sepM_delete _ (<[ i := HActive dc ]> hs) i (HActive dc));
        [| apply lookup_insert ].
      iSplitL "Hinfo Hbd Hrec Hclaim".
      { rewrite /head_res.
        iSplitR; [iPureIntro; subst i; by rewrite Hdcsl|].
        iEval (rewrite -Hdcpos) in "Hclaim". iFrame "Hclaim Hinfo".
        iLeft. iFrame "Hbd".
        rewrite /disk_receipt Hdcpos Hdcsl Hdcpin. iExact "Hrec". }
      rewrite delete_insert_delete. iExact "Hrest". }
    (* the pending map gains [np]; the done records survive *)
    rewrite Hnpeq in Hpendnone.
    rewrite (big_sepM_insert _ (vp_pend pr) np sl Hpendnone).
    assert (Hnptd :
      pend_todo (vproto_publish_state pr sl pin) (v_cache v) np sl
      = vs_all sl).
    { rewrite /pend_todo vpp_tk.
      destruct (bool_decide (vp_tk pr = Some np)) eqn:Hb; [|reflexivity].
      exfalso. apply bool_decide_eq_true in Hb.
      pose proof (vpo_tk _ _ _ Hok np Hb) as Hin.
      apply elem_of_dom in Hin as [x Hx].
      rewrite Hx in Hpendnone. discriminate. }
    assert (Hpmono : forall k x, vp_pend pr !! k = Some x ->
              slot_pend_res γ (pend_todo pr (v_cache v) k x) x
              ⊢ slot_pend_res γ
                  (pend_todo (vproto_publish_state pr sl pin) (v_cache v) k x) x).
    { intros k x _. apply bi.wand_entails. rewrite /pend_todo vpp_tk.
      iIntros "$". }
    iSplitL "Hpres Hpend".
    { rewrite Hnptd. iFrame "Hpres".
      iApply (big_sepM_mono _ _ _ Hpmono). iExact "Hpend". }
    assert (Hmono : forall k u x, vp_done pr !! k = Some x ->
              vp_uix pr !! k = Some u ->
              slot_done_res γ (v_cfg v) dma u x
              ⊢ slot_done_res γ (v_cfg v)
                  (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
                     (nth_byte (wrap16 (S np))) ∪ dma))) u x).
    { intros k u x Hk Hu. apply bi.wand_entails.
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
          exact (used_elem_pa_in_page (v_cfg v) u j Hj).
        + intro Hc. exact (proj1 (elem_of_disjoint _ _) (vpo_idx_used _ _ _ Hok)
                             _ Hc (used_elem_pa_in_page (v_cfg v) u j Hj)).
      - assert (Hstin : vr_status (vs_req x) ∈ slot_fp x pinq).
        { apply slot_fp_wr. unfold slot_wr.
          apply elem_of_union_l, elem_of_singleton. reflexivity. }
        apply Hframe; [ exact (HfpD _ Hstin) |].
        intro Hc. exact (proj1 (elem_of_disjoint _ _) Hstq _ Hstin
                           (elem_of_union_l _ _ _ (elem_of_union_l _ _ _ Hc))).
      - intros Hox j Hj.
        assert (Hbin : pa_add (vr_buf (vs_req x)) j ∈ slot_fp x pinq).
        { apply slot_fp_wr. unfold slot_wr. rewrite Hox.
          apply elem_of_union_r, pa_range_intro. exact Hj. }
        apply Hframe; [ exact (HfpD _ Hbin) |].
        intro Hc. exact (proj1 (elem_of_disjoint _ _) Hstq _ Hbin
                           (elem_of_union_l _ _ _ (elem_of_union_l _ _ _ Hc))). }
    iApply (big_sepM_mono
              (fun k x => ∃ u : nat, ⌜vp_uix pr !! k = Some u⌝ ∗
                            slot_done_res γ (v_cfg v) dma u x)%I
              (fun k x => ∃ u : nat, ⌜vp_uix pr !! k = Some u⌝ ∗
                            slot_done_res γ (v_cfg v)
                              (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
                                 (nth_byte (wrap16 (S np))) ∪ dma))) u x)%I).
    { intros k x Hk. iIntros "H". iDestruct "H" as (u) "[%Hu Hr]".
      iExists u. iSplitR; [by iPureIntro|].
      iApply (Hmono k u x Hk Hu). iExact "Hr". }
    iExact "Hdone".
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
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
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
    { iPureIntro. pose proof (vproto_ncnp _ _ _ Hok). lia. }
    iSplitR; [iExact "Hcfg"|]. iSplitR; [iPureIntro; exact Hal|].
    iFrame "Hlb Hmm". iIntros "Hmm".
    iDestruct ("Hback" with "Hmm") as "Hdma".
    iFrame "Hpub". iExists pr, dma. iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hheads Hpend Hdone".
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
  (* ------------------------------------------------------------------- *)
  (* THE COMPLETION RECORD AT A USED INDEX (finding 5).                    *)
  (*                                                                      *)
  (*   [virtio_disk_intr] walks USED INDICES; the protocol is keyed by     *)
  (*   POSITION; and with the served order free the two are different      *)
  (*   numbers.  A handler that has observed the used index is entitled to *)
  (*   the record of WHICH request was reported there -- that is what      *)
  (*   [vpo_uix_surj] says exists, and what the invariant's persistent     *)
  (*   copies hand out.  [disk_ord_agree] then tells the handler that the  *)
  (*   position it just learned is not one it has already processed: a     *)
  (*   position completes at exactly one used index.                       *)
  (* ------------------------------------------------------------------- *)
  Lemma virtio_proto_record_at (γ : disk_names) (v : virtio_state)
      (np u : nat) (cm : gmap nat dclaim) :
    virtio_proto γ v -∗ disk_pub γ np -∗ disk_done_lb γ (S u) -∗
    (* the watermark at [u]: the record there is still owed a look, so its
       slot is still live and its receipt holds the claim's row *)
    disk_read_at γ u -∗
    (* THE LOCK'S CLAIM MAP: what the handler carries between its openings.
       The row the receipt holds agrees with it, so the position and the
       claim this returns are facts about the handler's OWN map. *)
    ghost_map_auth (dn_claim γ) 1 cm -∗
    (∃ (p : nat) (dc : dclaim),
       ⌜cm !! p = Some dc⌝ ∗ ⌜dc_pos dc = p⌝ ∗ disk_ord γ p u) ∗
    virtio_proto γ v ∗ disk_pub γ np ∗ disk_done_lb γ (S u) ∗
    disk_read_at γ u ∗ ghost_map_auth (dn_claim γ) 1 cm.
  Proof.
    iIntros "Hp Hpub Hlb Hrd Hcm".
    rewrite /virtio_proto /disk_pub /disk_done_lb.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    iDestruct (mono_nat_lb_own_valid with "Hnc Hlb") as %[_ Hcle].
    (* the used index is below the completion count, so SOME position was
       reported there *)
    destruct (vpo_uix_surj _ _ _ Hok u ltac:(lia)) as [q Hq].
    iDestruct (big_sepM_lookup _ (vp_uix pr) q u Hq with "Hordm") as "#Hqu".
    (* ...and that position is still in [done], so its head's receipt is
       ACTIVE and carries the claim's row -- which the caller's map agrees
       with *)
    assert (Hsrv : q ∈ vp_srv pr).
    { rewrite <- (vpo_uix_dom _ _ _ Hok). apply elem_of_dom. by exists u. }
    assert (Hpendnone : vp_pend pr !! q = None).
    { apply not_elem_of_dom. intro Hc'.
      destruct (proj1 (vpo_pend_dom _ _ _ Hok q) Hc') as [_ Hns].
      exact (Hns Hsrv). }
    rewrite /disk_read_at.
    iDestruct (ghost_var_agree with "Hnr Hrd") as %Hnreq.
    assert (Hdonein : q ∈ dom (vp_done pr)).
    { apply (vpo_done_uix _ _ _ Hok). exists u. split; [exact Hq | lia]. }
    apply elem_of_dom in Hdonein as [sl Hdone].
    assert (Hs : vp_slots pr !! q = Some sl).
    { unfold vp_slots.
      rewrite (lookup_union_r (vp_pend pr) (vp_done pr) q Hpendnone).
      exact Hdone. }
    assert (Hpinin : exists pin, vp_pin pr !! q = Some pin).
    { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
      apply elem_of_dom. by exists sl. }
    destruct Hpinin as [pin Hpin].
    assert (Hspins : vp_spins pr !! q = Some (sl, pin))
      by (unfold vp_spins; rewrite map_lookup_zip_with Hs Hpin; reflexivity).
    iDestruct "Hheads" as (hs) "(%Hhdom & %Hhcoup & Hhauth & Hhbig)".
    destruct (Hhcoup q sl pin Hspins) as (w & Hhlk & Hdcsl & Hdcpin & Hdcpos).
    iDestruct (big_sepM_lookup_acc _ hs _ (HActive w) Hhlk with "Hhbig")
      as "[Hent Hhbig]".
    rewrite {1}/head_res.
    iDestruct "Hent" as "(%Hdchd & Hclaim & Hinfo & Hdisj)".
    iDestruct (ghost_map_lookup with "Hcm Hclaim") as %Hcmw.
    rewrite Hdcpos in Hcmw.
    iDestruct ("Hhbig" with "[Hclaim Hinfo Hdisj]") as "Hhbig".
    { rewrite /head_res. iSplitR; [iPureIntro; exact Hdchd|].
      iFrame "Hclaim Hinfo". iExact "Hdisj". }
    iSplitR; [ iExists q, w; by iFrame "Hqu" |].
    iFrame "Hpub Hlb Hrd Hcm".
    iExists pr, dma.
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hpend Hdone".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact Hok|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hah|].
    iSplitR; [iPureIntro; exact Htkc|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR; [iPureIntro; exact Hwt|].
    rewrite /heads_res_at. iExists hs. iFrame "Hhauth".
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iExact "Hhbig".
  Qed.


  (* ==================================================================== *)
  (* THE HANDLER'S RECORD READ: [int id = disk.used->ring[...].id].       *)
  (*                                                                      *)
  (* Keyed by the completion record, the watermark and the lock's claim   *)
  (* map -- never by a receipt, which the handler does not hold.  Under    *)
  (* out-of-order completion the handler has NOTHING before this read --   *)
  (* the head it is about to learn is what names the chain -- so the       *)
  (* accessor has to find the entry itself, from [disk_ord] and the fact   *)
  (* that the watermark still owes this record a look.  What comes out is  *)
  (* the element's bytes and, with them, WHICH claim they are about.       *)
  (* ==================================================================== *)
  Lemma virtio_proto_used_peek_at (γ : disk_names) (v : virtio_state)
      (np p u : nat) (cm : gmap nat dclaim) (dc : dclaim) :
    (* the claim at [p] in the handler's OWN map ([virtio_proto_record_at]) *)
    cm !! p = Some dc ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    disk_ord γ p u -∗
    disk_read_at γ u -∗
    ghost_map_auth (dn_claim γ) 1 cm -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    (⌜slot_pin_ok (v_cfg v) p (dc_slot dc) (dc_pin dc)⌝ ∗
     phys_word4 (used_elem_pa (v_cfg v) u)
                (Z_to_bv 32 (bv_unsigned (vr_head (vs_req (dc_slot dc))))) ∗
     (phys_word4 (used_elem_pa (v_cfg v) u)
                 (Z_to_bv 32 (bv_unsigned (vr_head (vs_req (dc_slot dc))))) -∗
        virtio_proto γ v ∗ disk_pub γ np ∗ disk_read_at γ u ∗
        ghost_map_auth (dn_claim γ) 1 cm)).
  Proof.
    intro Hcm.
    iIntros "Hp Hpub #Hordp Hrd Hcm".
    rewrite /virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    rewrite /disk_ord.
    iDestruct (ghost_map_lookup with "Hord Hordp") as %Huix.
    assert (Hsrv : p ∈ vp_srv pr).
    { rewrite <- (vpo_uix_dom _ _ _ Hok). apply elem_of_dom. by exists u. }
    assert (Hpendnone : vp_pend pr !! p = None).
    { apply not_elem_of_dom. intro Hc'.
      destruct (proj1 (vpo_pend_dom _ _ _ Hok p) Hc') as [_ Hns].
      exact (Hns Hsrv). }
    rewrite /disk_read_at.
    iDestruct (ghost_var_agree with "Hnr Hrd") as %Hnreq.
    assert (Hdonein : p ∈ dom (vp_done pr)).
    { apply (vpo_done_uix _ _ _ Hok). exists u. split; [exact Huix | lia]. }
    apply elem_of_dom in Hdonein as [sl Hdone].
    assert (Hs : vp_slots pr !! p = Some sl).
    { unfold vp_slots.
      rewrite (lookup_union_r (vp_pend pr) (vp_done pr) p Hpendnone).
      exact Hdone. }
    assert (Hpinin : exists pin, vp_pin pr !! p = Some pin).
    { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
      apply elem_of_dom. by exists sl. }
    destruct Hpinin as [pin Hpin].
    assert (Hspins : vp_spins pr !! p = Some (sl, pin))
      by (unfold vp_spins; rewrite map_lookup_zip_with Hs Hpin; reflexivity).
    iDestruct "Hheads" as (hs) "(%Hhdom & %Hhcoup & Hhauth & Hhbig)".
    destruct (Hhcoup p sl pin Hspins) as (w & Hhlk & Hdcsl & Hdcpin & Hdcpos).
    (* the entry's row agrees with the handler's map: the claim is [dc] *)
    iDestruct (big_sepM_lookup_acc _ hs _ (HActive w) Hhlk with "Hhbig")
      as "[Hent Hhbig]".
    rewrite {1}/head_res.
    iDestruct "Hent" as "(%Hdchd & Hclaim & Hinfo & Hdisj)".
    iDestruct (ghost_map_lookup with "Hcm Hclaim") as %Hcmw.
    rewrite Hdcpos Hcm in Hcmw. injection Hcmw as Heqw. subst w.
    iDestruct ("Hhbig" with "[Hclaim Hinfo Hdisj]") as "Hhbig".
    { rewrite /head_res. iSplitR; [iPureIntro; exact Hdchd|].
      iFrame "Hclaim Hinfo". iExact "Hdisj". }
    iDestruct (big_sepM_delete _ (vp_done pr) p sl Hdone with "Hdone")
      as "[Hdres Hdone]".
    iDestruct "Hdres" as (u') "[%Hu' Hdres]".
    rewrite Huix in Hu'. injection Hu' as <-.
    iDestruct "Hdres" as (bs) "(%Hbslen & Hbs & %Hout & %Hre & %Hst & %Hbl & Hdone0)".
    assert (HEMsub : range_map (used_elem_pa (v_cfg v) u) 4
                       (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))))
                     ⊆ dma).
    { apply range_map_sub; [lia|]. intros j Hj.
      apply (read_bytes_spec dma (used_elem_pa (v_cfg v) u) 4 _ Hre). lia. }
    iDestruct (dma_own_acc_same _ dma HEMsub with "Hdma") as "[Hem Hback]".
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iSplitR.
    { iPureIntro. rewrite Hdcsl Hdcpin.
      exact (vpo_slot _ _ _ Hok p sl pin Hs Hpin). }
    rewrite Hdcsl !phys_word4_map.
    iFrame "Hem". iIntros "Hem".
    iDestruct ("Hback" with "Hem") as "Hdma".
    iSplitR "Hpub Hrd Hcm"; [| by iFrame "Hpub Hrd Hcm"].
    iExists pr, dma.
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hpend".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact Hok|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hah|].
    iSplitR; [iPureIntro; exact Htkc|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR; [iPureIntro; exact Hwt|].
    iSplitL "Hhauth Hhbig".
    { rewrite /heads_res_at. iExists hs. iFrame "Hhauth".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iExact "Hhbig". }
    iApply (big_sepM_delete _ (vp_done pr) p sl Hdone).
    iSplitR "Hdone"; [| iExact "Hdone"].
    iExists u. iSplitR; [done|].
    iExists bs. iFrame "Hbs Hdone0".
    all: try (iPureIntro; split_and!; assumption).
  Qed.

  (* ==================================================================== *)
  (* THE HANDLER'S STATUS CHECK: [if(disk.info[id].status != 0) panic].   *)
  (*                                                                      *)
  (* A PEEK out of the LEASE.  The status byte is one of the bytes the     *)
  (* device wrote, so it is not owned apart from [dma]; what says it reads *)
  (* zero is [slot_done_res]'s pure clause, and the completion record is   *)
  (* what puts the slot in [done].  Keyed like the buf read and the        *)
  (* deposit, so all three speak about the same claim, and it spends       *)
  (* nothing.                                                             *)
  (* ==================================================================== *)
  Lemma virtio_proto_status_peek (γ : disk_names) (v : virtio_state)
      (np p u : nat) (cm : gmap nat dclaim) (dc : dclaim) :
    cm !! p = Some dc ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    disk_ord γ p u -∗
    disk_read_at γ u -∗
    ghost_map_auth (dn_claim γ) 1 cm -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    (⌜slot_pin_ok (v_cfg v) p (dc_slot dc) (dc_pin dc)⌝ ∗
     phys_pointsto (vr_status (vs_req (dc_slot dc))) (DfracOwn 1) byte_zero ∗
     (phys_pointsto (vr_status (vs_req (dc_slot dc))) (DfracOwn 1) byte_zero -∗
        virtio_proto γ v ∗ disk_pub γ np ∗ disk_read_at γ u ∗
        ghost_map_auth (dn_claim γ) 1 cm)).
  Proof.
    intro Hcm.
    iIntros "Hp Hpub #Hordp Hrd Hcm".
    rewrite /virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    rewrite /disk_ord.
    iDestruct (ghost_map_lookup with "Hord Hordp") as %Huix.
    assert (Hsrv : p ∈ vp_srv pr).
    { rewrite <- (vpo_uix_dom _ _ _ Hok). apply elem_of_dom. by exists u. }
    assert (Hpendnone : vp_pend pr !! p = None).
    { apply not_elem_of_dom. intro Hc'.
      destruct (proj1 (vpo_pend_dom _ _ _ Hok p) Hc') as [_ Hns].
      exact (Hns Hsrv). }
    rewrite /disk_read_at.
    iDestruct (ghost_var_agree with "Hnr Hrd") as %Hnreq.
    assert (Hdonein : p ∈ dom (vp_done pr)).
    { apply (vpo_done_uix _ _ _ Hok). exists u. split; [exact Huix | lia]. }
    apply elem_of_dom in Hdonein as [sl Hdone].
    assert (Hs : vp_slots pr !! p = Some sl).
    { unfold vp_slots.
      rewrite (lookup_union_r (vp_pend pr) (vp_done pr) p Hpendnone).
      exact Hdone. }
    assert (Hpinin : exists pin, vp_pin pr !! p = Some pin).
    { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
      apply elem_of_dom. by exists sl. }
    destruct Hpinin as [pin Hpin].
    assert (Hspins : vp_spins pr !! p = Some (sl, pin))
      by (unfold vp_spins; rewrite map_lookup_zip_with Hs Hpin; reflexivity).
    iDestruct "Hheads" as (hs) "(%Hhdom & %Hhcoup & Hhauth & Hhbig)".
    destruct (Hhcoup p sl pin Hspins) as (w & Hhlk & Hdcsl & Hdcpin & Hdcpos).
    (* the entry's row agrees with the handler's map: the claim is [dc] *)
    iDestruct (big_sepM_lookup_acc _ hs _ (HActive w) Hhlk with "Hhbig")
      as "[Hent Hhbig]".
    rewrite {1}/head_res.
    iDestruct "Hent" as "(%Hdchd & Hclaim & Hinfo & Hdisj)".
    iDestruct (ghost_map_lookup with "Hcm Hclaim") as %Hcmw.
    rewrite Hdcpos Hcm in Hcmw. injection Hcmw as Heqw. subst w.
    iDestruct ("Hhbig" with "[Hclaim Hinfo Hdisj]") as "Hhbig".
    { rewrite /head_res. iSplitR; [iPureIntro; exact Hdchd|].
      iFrame "Hclaim Hinfo". iExact "Hdisj". }
    iDestruct (big_sepM_delete _ (vp_done pr) p sl Hdone with "Hdone")
      as "[Hdres Hdone]".
    iDestruct "Hdres" as (u') "[%Hu' Hdres]".
    rewrite Huix in Hu'. injection Hu' as <-.
    iDestruct "Hdres" as (bs) "(%Hbslen & Hbs & %Hout & %Hre & %Hst & %Hbl & Hdone0)".
    (* the byte is in the lease, and [slot_done_res] says it is zero *)
    assert (HSTsub : {[ vr_status (vs_req sl) := byte_zero ]} ⊆ dma)
      by (apply insert_subseteq_l; [ exact Hst | apply map_empty_subseteq ]).
    iDestruct (dma_own_acc_same _ dma HSTsub with "Hdma") as "[Hst1 Hback]".
    rewrite {1}/phys_map big_sepM_singleton.
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iSplitR.
    { iPureIntro. rewrite Hdcsl Hdcpin.
      exact (vpo_slot _ _ _ Hok p sl pin Hs Hpin). }
    rewrite Hdcsl.
    iFrame "Hst1". iIntros "Hst1".
    iDestruct ("Hback" with "[Hst1]") as "Hdma";
      [ rewrite /phys_map big_sepM_singleton; iExact "Hst1" |].
    iSplitR "Hpub Hrd Hcm"; [| by iFrame "Hpub Hrd Hcm"].
    iExists pr, dma.
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hpend".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact Hok|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hah|].
    iSplitR; [iPureIntro; exact Htkc|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR; [iPureIntro; exact Hwt|].
    iSplitL "Hhauth Hhbig".
    { rewrite /heads_res_at. iExists hs. iFrame "Hhauth".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iExact "Hhbig". }
    iApply (big_sepM_delete _ (vp_done pr) p sl Hdone).
    iSplitR "Hdone"; [| iExact "Hdone"].
    iExists u. iSplitR; [done|].
    iExists bs. iFrame "Hbs Hdone0".
    all: try (iPureIntro; split_and!; assumption).
  Qed.

  (* ==================================================================== *)
  (* THE HANDLER'S BUF READ: [struct buf *b = disk.info[id].b].           *)
  (*                                                                      *)
  (* A PEEK, keyed exactly like the deposit below -- the completion        *)
  (* record at [p] plus the watermark still at [u] -- so both accessors    *)
  (* land on the SAME map entry [hs !! id] and therefore the same claim.   *)
  (* That is what lets the handler carry the value it read here across to  *)
  (* the store: not a resource (an invariant cannot lend one across a      *)
  (* close) but the pure fact that the address it now holds in [b] is      *)
  (* [dc_buf dc] for the very claim the deposit will find.                 *)
  (*                                                                      *)
  (* The cell is PINNED to that buffer in both arms of the disjunct, so    *)
  (* this read does not care whether the chain is still out or already     *)
  (* back, and it spends nothing: the watermark comes back unmoved.        *)
  (* ==================================================================== *)
  Lemma virtio_proto_infob_acc (γ : disk_names) (v : virtio_state)
      (np p u : nat) (cm : gmap nat dclaim) (dc : dclaim) :
    cm !! p = Some dc ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    disk_ord γ p u -∗
    disk_read_at γ u -∗
    ghost_map_auth (dn_claim γ) 1 cm -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    (⌜slot_pin_ok (v_cfg v) p (dc_slot dc) (dc_pin dc)⌝ ∗
     d_info_b (Z.to_nat (bv_unsigned (vr_head (vs_req (dc_slot dc)))))
       ↦₈ (dc_buf dc : SailStdpp.Values.mword 64) ∗
     (d_info_b (Z.to_nat (bv_unsigned (vr_head (vs_req (dc_slot dc)))))
        ↦₈ (dc_buf dc : SailStdpp.Values.mword 64) -∗
        virtio_proto γ v ∗ disk_pub γ np ∗ disk_read_at γ u ∗
        ghost_map_auth (dn_claim γ) 1 cm)).
  Proof.
    intro Hcm.
    iIntros "Hp Hpub #Hordp Hrd Hcm".
    rewrite /virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    (* the completion record puts [p] in [srv], hence out of [pend] *)
    rewrite /disk_ord.
    iDestruct (ghost_map_lookup with "Hord Hordp") as %Huix.
    assert (Hsrv : p ∈ vp_srv pr).
    { rewrite <- (vpo_uix_dom _ _ _ Hok). apply elem_of_dom. by exists u. }
    assert (Hpendnone : vp_pend pr !! p = None).
    { apply not_elem_of_dom. intro Hc'.
      destruct (proj1 (vpo_pend_dom _ _ _ Hok p) Hc') as [_ Hns].
      exact (Hns Hsrv). }
    (* the watermark still owes this record a look, so its slot is in [done] *)
    rewrite /disk_read_at.
    iDestruct (ghost_var_agree with "Hnr Hrd") as %Hnreq.
    assert (Hdonein : p ∈ dom (vp_done pr)).
    { apply (vpo_done_uix _ _ _ Hok). exists u. split; [exact Huix | lia]. }
    apply elem_of_dom in Hdonein as [sl Hdone].
    assert (Hs : vp_slots pr !! p = Some sl).
    { unfold vp_slots.
      rewrite (lookup_union_r (vp_pend pr) (vp_done pr) p Hpendnone).
      exact Hdone. }
    assert (Hpinin : exists pin, vp_pin pr !! p = Some pin).
    { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
      apply elem_of_dom. by exists sl. }
    destruct Hpinin as [pin Hpin].
    assert (Hspins : vp_spins pr !! p = Some (sl, pin))
      by (unfold vp_spins; rewrite map_lookup_zip_with Hs Hpin; reflexivity).
    iDestruct "Hheads" as (hs) "(%Hhdom & %Hhcoup & Hhauth & Hhbig)".
    destruct (Hhcoup p sl pin Hspins) as (w & Hhlk & Hdcsl & Hdcpin & Hdcpos).
    iDestruct (big_sepM_delete _ hs _ (HActive w) Hhlk with "Hhbig")
      as "[Hent Hrest]".
    rewrite {1}/head_res.
    iDestruct "Hent" as "(%Hdchd & Hclaim & Hinfo & Hdisj)".
    (* the entry's row agrees with the handler's map: the claim is [dc] *)
    iDestruct (ghost_map_lookup with "Hcm Hclaim") as %Hcmw.
    rewrite Hdcpos Hcm in Hcmw. injection Hcmw as Heqw. subst w.
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iSplitR.
    { iPureIntro. rewrite Hdcsl Hdcpin.
      exact (vpo_slot _ _ _ Hok p sl pin Hs Hpin). }
    (* the entry is keyed by [sl]'s head; the statement says [dc_slot dc] *)
    rewrite Hdcsl.
    iFrame "Hinfo". iIntros "Hinfo".
    (* both halves of [dn_nr] are in scope here, so isolate before framing *)
    iSplitR "Hpub Hrd Hcm"; [| by iFrame "Hpub Hrd Hcm"].
    iExists pr, dma.
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hpend Hdone".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact Hok|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hah|].
    iSplitR; [iPureIntro; exact Htkc|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR; [iPureIntro; exact Hwt|].
    iExists hs. iFrame "Hhauth".
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    rewrite (big_sepM_delete _ hs _ (HActive dc) Hhlk).
    iFrame "Hrest". rewrite /head_res Hdcsl.
    iSplitR; [by iPureIntro|]. iFrame "Hclaim Hinfo". iExact "Hdisj".
  Qed.

  (* ==================================================================== *)
  (* THE HANDLER'S [b->disk] PEEK.                                        *)
  (*                                                                      *)
  (* The store [b->disk = 0] is an atomic-update leaf, and such a leaf     *)
  (* wants the cell's address claim BESIDE the update -- the access        *)
  (* translates before the memory node where the deposit opens.  The       *)
  (* deposit below is one-shot (its closer performs the handover), so it   *)
  (* cannot be peeked and put back; this is its read-only twin, keyed      *)
  (* exactly like it, walking [virtio_proto_infob_acc]'s path to the       *)
  (* ACTIVE entry and refuting the came-back arm the way the deposit does. *)
  (* ==================================================================== *)
  Lemma virtio_proto_bdisk_peek (γ : disk_names) (v : virtio_state)
      (np p u : nat) (cm : gmap nat dclaim) (dc : dclaim) :
    cm !! p = Some dc ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    disk_ord γ p u -∗
    disk_read_at γ u -∗
    ghost_map_auth (dn_claim γ) 1 cm -∗
    b_disk (dc_buf dc) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1) ∗
    (b_disk (dc_buf dc) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1) -∗
       virtio_proto γ v ∗ disk_pub γ np ∗ disk_read_at γ u ∗
       ghost_map_auth (dn_claim γ) 1 cm).
  Proof.
    intro Hcm.
    iIntros "Hp Hpub #Hordp Hrd Hcm".
    rewrite /virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    (* the completion record puts [p] in [srv], hence out of [pend] *)
    rewrite /disk_ord.
    iDestruct (ghost_map_lookup with "Hord Hordp") as %Huix.
    assert (Hsrv : p ∈ vp_srv pr).
    { rewrite <- (vpo_uix_dom _ _ _ Hok). apply elem_of_dom. by exists u. }
    assert (Hpendnone : vp_pend pr !! p = None).
    { apply not_elem_of_dom. intro Hc'.
      destruct (proj1 (vpo_pend_dom _ _ _ Hok p) Hc') as [_ Hns].
      exact (Hns Hsrv). }
    (* the watermark still owes this record a look, so its slot is in [done] *)
    rewrite /disk_read_at.
    iDestruct (ghost_var_agree with "Hnr Hrd") as %Hnreq.
    assert (Hdonein : p ∈ dom (vp_done pr)).
    { apply (vpo_done_uix _ _ _ Hok). exists u. split; [exact Huix | lia]. }
    apply elem_of_dom in Hdonein as [sl Hdone].
    assert (Hs : vp_slots pr !! p = Some sl).
    { unfold vp_slots.
      rewrite (lookup_union_r (vp_pend pr) (vp_done pr) p Hpendnone).
      exact Hdone. }
    assert (Hpinin : exists pin, vp_pin pr !! p = Some pin).
    { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
      apply elem_of_dom. by exists sl. }
    destruct Hpinin as [pin Hpin].
    assert (Hspins : vp_spins pr !! p = Some (sl, pin))
      by (unfold vp_spins; rewrite map_lookup_zip_with Hs Hpin; reflexivity).
    iDestruct "Hheads" as (hs) "(%Hhdom & %Hhcoup & Hhauth & Hhbig)".
    destruct (Hhcoup p sl pin Hspins) as (w & Hhlk & Hdcsl & Hdcpin & Hdcpos).
    iDestruct (big_sepM_delete _ hs _ (HActive w) Hhlk with "Hhbig")
      as "[Hent Hrest]".
    rewrite {1}/head_res.
    iDestruct "Hent" as "(%Hdchd & Hclaim & Hinfo & Hdisj)".
    (* the entry's row agrees with the handler's map: the claim is [dc] *)
    iDestruct (ghost_map_lookup with "Hcm Hclaim") as %Hcmw.
    rewrite Hdcpos Hcm in Hcmw. injection Hcmw as Heqw. subst w.
    (* THE CHAIN IS OUT.  If the entry held it back already it would own
       [dc_pin dc] -- which is [pin], which is in the lease -- and a byte
       cannot be owned twice.  The head descriptor's own bytes are the
       witness ([spo_desc]). *)
    iDestruct "Hdisj" as "[[Hbd Hrecpt] | [_ Hback]]"; last first.
    { rewrite /chain_back. iDestruct "Hback" as "[Hpinm _]".
      rewrite Hdcpin.
      iDestruct (dma_own_disj with "Hdma Hpinm") as %Hdj.
      exfalso.
      pose proof (vpo_fp_D _ _ _ Hok p sl pin Hs Hpin) as HfpD.
      pose proof (spo_desc _ _ _ _ (vpo_slot _ _ _ Hok p sl pin Hs Hpin))
        as Hdesc.
      exact (proj1 (elem_of_disjoint _ _) Hdj _ Hdesc
               (HfpD _ (slot_fp_pin sl pin _ Hdesc))). }
    iFrame "Hbd". iIntros "Hbd".
    (* both halves of [dn_nr] are in scope here, so isolate before framing *)
    iSplitR "Hpub Hrd Hcm"; [| by iFrame "Hpub Hrd Hcm"].
    iExists pr, dma.
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hpend Hdone".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact Hok|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hah|].
    iSplitR; [iPureIntro; exact Htkc|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR; [iPureIntro; exact Hwt|].
    iExists hs. iFrame "Hhauth".
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    rewrite (big_sepM_delete _ hs _ (HActive dc) Hhlk).
    iFrame "Hrest". rewrite /head_res.
    iSplitR; [by iPureIntro|]. iFrame "Hclaim Hinfo".
    iLeft. iFrame "Hbd Hrecpt".
  Qed.

  (* ==================================================================== *)
  (* THE HANDLER'S DEPOSIT: [b->disk = 0].                                *)
  (*                                                                      *)
  (* ONE atomic step does the whole handover.  It has to: a resource       *)
  (* cannot be borrowed out of an invariant across a close without leaving *)
  (* a token behind, so releasing the chain at the [lw] of the used        *)
  (* element and depositing it at this store would need a third receipt    *)
  (* state.  Instead the earlier reads are peeks that put everything back, *)
  (* and this store reclaims AND deposits at once.                        *)
  (*                                                                      *)
  (* NOTHING COMES BACK TO THE HANDLER.  The chain goes straight into the  *)
  (* receipt's "it all came back" disjunct, which is where the sleeping    *)
  (* [virtio_disk_rw] collects it -- and [b->disk = 0] is exactly the      *)
  (* signal that it is there.  The handler needs no claim, no position     *)
  (* lookup and no receipt of its own: the used ring named the record, and *)
  (* the coupling turns that into the entry.                              *)
  (* ==================================================================== *)
  Lemma virtio_proto_deposit_acc (γ : disk_names) (v : virtio_state)
      (np p u : nat) (cm : gmap nat dclaim) (dc : dclaim) :
    cm !! p = Some dc ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    disk_ord γ p u -∗
    (* THE HANDLER IS AT THIS RECORD.  Reclaiming out of order is not merely
       unproved but unsound -- the ninth completion would overwrite the used
       element of a record still owed a look -- so the watermark is a
       PRECONDITION, and it comes back advanced by one. *)
    disk_read_at γ u -∗
    ghost_map_auth (dn_claim γ) 1 cm -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
    (⌜slot_pin_ok (v_cfg v) p (dc_slot dc) (dc_pin dc)⌝ ∗
     b_disk (dc_buf dc) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1) ∗
     (b_disk (dc_buf dc) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 0) ==∗
        virtio_proto γ v ∗ disk_pub γ np ∗ disk_done_lb γ (S u) ∗
        disk_read_at γ (S u) ∗ ghost_map_auth (dn_claim γ) 1 cm)).
  Proof.
    intro Hcm.
    iIntros "Hp Hpub #Hordp Hrd Hcm".
    rewrite {1}/virtio_proto /disk_pub /disk_done_lb.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & _ & Hslot & Hord & Hnc & Hnp & Hnr & Hstage & Hheads)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma)
      "(#Hcfg & Hdma & %Hctl & %Hok & %Hal & %Hseen & %Hah & %Htkc & %Hui & %Hridx &
        %Hwce & %Hwt & Hslot & Hord & #Hordm & Hnc & Hnp & Hnr & Hstage & Hheads & Hpend & Hdone)".
    (* THE COMPLETION RECORD is what says [p] is served, hence in [done] --
       the counters no longer say it, since the served order is free. *)
    rewrite /disk_ord.
    iDestruct (ghost_map_lookup with "Hord Hordp") as %Huix.
    assert (Hsrv : p ∈ vp_srv pr).
    { rewrite <- (vpo_uix_dom _ _ _ Hok). apply elem_of_dom. by exists u. }
    assert (Hpnc : (u < vp_nc pr)%nat) by exact (vpo_uix_lt _ _ _ Hok p u Huix).
    assert (Hpendnone : vp_pend pr !! p = None).
    { apply not_elem_of_dom. intro Hc'.
      destruct (proj1 (vpo_pend_dom _ _ _ Hok p) Hc') as [_ Hns].
      exact (Hns Hsrv). }
    (* THE WATERMARK SAYS THIS RECORD IS STILL OWED A LOOK, so its slot is
       still in [done] -- which is where the slot, the pin and hence the
       receipt come from.  The handler supplies none of them. *)
    rewrite /disk_read_at.
    iDestruct (ghost_var_agree with "Hnr Hrd") as %Hnreq.
    assert (Hdonein : p ∈ dom (vp_done pr)).
    { apply (vpo_done_uix _ _ _ Hok). exists u. split; [exact Huix | lia]. }
    apply elem_of_dom in Hdonein as [sl Hdone].
    assert (Hs : vp_slots pr !! p = Some sl).
    { unfold vp_slots.
      rewrite (lookup_union_r (vp_pend pr) (vp_done pr) p Hpendnone).
      exact Hdone. }
    assert (Hpinin : exists pin, vp_pin pr !! p = Some pin).
    { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
      apply elem_of_dom. by exists sl. }
    destruct Hpinin as [pin Hpin].
    (* ...and the receipt for this chain's head is in the invariant's own
       entry for it, put there by the publish. *)
    assert (Hspins : vp_spins pr !! p = Some (sl, pin))
      by (unfold vp_spins; rewrite map_lookup_zip_with Hs Hpin; reflexivity).
    iDestruct "Hheads" as (hs) "(%Hhdom & %Hhcoup & Hhauth & Hhbig)".
    destruct (Hhcoup p sl pin Hspins) as (w & Hhlk & Hdcsl & Hdcpin & Hdcpos).
    iDestruct (big_sepM_delete _ hs _ (HActive w) Hhlk with "Hhbig")
      as "[Hent Hrest]".
    rewrite {1}/head_res.
    iDestruct "Hent" as "(%Hdchd & Hclaim & Hinfo & Hdisj)".
    (* the entry's row agrees with the handler's map: the claim is [dc] *)
    iDestruct (ghost_map_lookup with "Hcm Hclaim") as %Hcmw.
    rewrite Hdcpos Hcm in Hcmw. injection Hcmw as Heqw. subst w.
    (* THE CHAIN IS OUT.  If the entry held it back already it would own
       [dc_pin dc] -- which is [pin], which is in the lease -- and a byte
       cannot be owned twice.  The head descriptor's own bytes are the
       witness ([spo_desc]). *)
    iDestruct "Hdisj" as "[[Hbd Hrecpt] | [_ Hback]]"; last first.
    { rewrite /chain_back. iDestruct "Hback" as "[Hpinm _]".
      rewrite Hdcpin.
      iDestruct (dma_own_disj with "Hdma Hpinm") as %Hdj.
      exfalso.
      pose proof (vpo_fp_D _ _ _ Hok p sl pin Hs Hpin) as HfpD.
      pose proof (spo_desc _ _ _ _ (vpo_slot _ _ _ Hok p sl pin Hs Hpin))
        as Hdesc.
      exact (proj1 (elem_of_disjoint _ _) Hdj _ Hdesc
               (HfpD _ (slot_fp_pin sl pin _ Hdesc))). }
    (* the receipt the entry was holding, at this chain's own position *)
    iEval (rewrite /disk_receipt Hdcpos Hdcsl Hdcpin) in "Hrecpt".
    pose proof (vpo_slot _ _ _ Hok p sl pin Hs Hpin) as Hslotok.
    pose proof (vpo_wr_pin _ _ _ Hok p sl pin Hs Hpin) as Hwrpin.
    pose proof (vpo_standing _ _ _ Hok p sl pin Hs Hpin) as Hstand.
    iDestruct (big_sepM_delete _ (vp_done pr) p sl Hdone with "Hdone")
      as "[Hdres Hdone]".
    iDestruct "Hdres" as (u') "[%Hu' Hdres]".
    rewrite Huix in Hu'. injection Hu' as <-.
    iDestruct "Hdres" as (bs) "(%Hbslen & Hbs & %Hout & %Hre & %Hst & %Hbl & Hdone0)".
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iSplitR; [iPureIntro; exact Hal|].
    (* what the handler gets is [b->disk], and nothing else: the chain goes
       into the receipt, not to the caller *)
    iSplitR; [iPureIntro; rewrite Hdcsl Hdcpin; exact Hslotok|].
    iFrame "Hbd". iIntros "Hbd".
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
    assert (HAsub : (avail_idx_bytes (v_cfg v) (vp_np pr)
                     ∪ ring_bytes (v_cfg v) (vp_ring pr))
                    ∪ pins_union (delete p (vp_pin pr)) ⊆ dma).
    { assert (Hpindel : pin ##ₘ pins_union (delete p (vp_pin pr)))
        by exact (proj2 (proj1 (map_disjoint_union_r pin _ _) Hdisjr)).
      etransitivity; [| exact Hctl ]. rewrite Hctlsplit.
      apply map_union_mono_r, (map_union_subseteq_r _ _ Hpindel). }
    assert (HAdisj : dom ((avail_idx_bytes (v_cfg v) (vp_np pr)
                           ∪ ring_bytes (v_cfg v) (vp_ring pr))
                          ∪ pins_union (delete p (vp_pin pr)))
                     ## slot_fp sl pin).
    { apply elem_of_disjoint. intros a Ha Hb.
      rewrite dom_union_L dom_union_L avail_idx_bytes_dom
              (ring_bytes_dom_eq (v_cfg v) (vp_ring pr)) in Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      - (* the index word and the ring cells are both STANDING regions: no
           slot's footprint ever meets them *)
        apply elem_of_union in Ha as [Ha|Ha].
        + exact (proj1 (elem_of_disjoint _ _) Hstand a Hb
                   (elem_of_union_l _ _ _ (elem_of_union_l _ _ _ Ha))).
        + exact (proj1 (elem_of_disjoint _ _) Hstand a Hb
                   (elem_of_union_l _ _ _ (elem_of_union_r _ _ _ Ha))).
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
    assert (Hsp : (S u <= vp_nc pr)%nat) by lia.
    iDestruct (mono_nat_lb_own_le (S u) Hsp with "Hlbnc") as "#Hlbp".
    (* THE WATERMARK: the caller's half says it is looking at record [u], so
       [u] IS [vp_nr pr] -- which is the in-order premise [vproto_ok_reclaim]
       wants -- and both halves step to [S u] together. *)
    rewrite /disk_read_at.
    (* the watermark agreement was taken up front, to find the slot *)
    iMod (ghost_var_update_2 (S u) with "Hnr Hrd") as "[Hnr Hrd]";
      [apply Qp.half_half|].
    assert (Huixnr : vp_uix pr !! p = Some (vp_nr pr))
      by (rewrite Hnreq; exact Huix).
    (* THE DEPOSIT.  Everything the device gave back goes into the receipt's
       "it all came back" disjunct, beside [b->disk = 0] -- which is the
       signal the sleeping publisher is waiting on.  The [dn_slot] receipt
       that was in the other disjunct is spent retiring the slot. *)
    iAssert (head_res γ (Z.to_nat (bv_unsigned (vr_head (vs_req sl))))
                      (HActive dc))
      with "[Hclaim Hinfo Hbd Hpin Hstm Hdone0 Hbs Hbuf]" as "Hent".
    { rewrite /head_res. iSplitR; [iPureIntro; by rewrite Hdcsl|].
      iFrame "Hclaim Hinfo". iRight. iFrame "Hbd".
      rewrite /chain_back Hdcsl Hdcpin. iFrame "Hpin Hstm Hdone0".
      iExists bs. iFrame "Hbs". iSplitR; [iPureIntro; exact Hbslen|].
      iSplitR; [iPureIntro; exact Hout|].
      destruct (vs_is_out sl) eqn:Hoo; [done|].
      rewrite (phys_list_map (vr_buf (vs_req sl)) bs
                 ltac:(rewrite Hbslen; apply vs_len_bound)).
      iFrame "Hbuf". }
    iAssert (heads_res_at γ (vp_spins pr)) with "[Hhauth Hrest Hent]" as "Hheadsnew".
    { rewrite /heads_res_at. iExists hs. iFrame "Hhauth".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
      rewrite (big_sepM_delete _ hs _ (HActive dc) Hhlk).
      iFrame "Hent Hrest". }
    (* rebuild *)
    iModIntro. iFrame "Hpub Hlbp Hrd Hcm".
    rewrite /virtio_proto Hlive.
    iExists (vproto_reclaim_state pr p),
      (dma ∖ (pin ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
         ∪ (if vs_is_out sl then ∅
            else range_map (vr_buf (vs_req sl)) (length bs)
                   (fun j : nat => bs !!! j))))).
    rewrite (vp_spins_reclaim (v_cfg v) pr (dom dma) p sl Hok Hdone)
            vpr_nc vpr_np vpr_pend vpr_done vpr_uix.
    rewrite vpr_nr Hnreq.
    (* the retired request leaves [vp_spins]; the receipts' coupling only ever
       had to cover the live ones, so it survives the shrink.  Its entry stays
       in the map -- now holding the whole chain, for the publisher. *)
    iDestruct (heads_res_at_mono γ (vp_spins pr) (delete p (vp_spins pr))
                 with "Hheadsnew") as "Hheads".
    { intros q x Hq. apply lookup_delete_Some in Hq as [_ Hq]. exact Hq. }
    iFrame "Hcfg Hdma Hslot Hord Hordm Hnc Hnp Hnr Hstage Hheads Hpend".
    iSplitR.
    { iPureIntro. rewrite Hctlr. apply map_sub_difference; [exact HAsub|].
      rewrite HdomMM. exact HAdisj. }
    iSplitR.
    { iPureIntro. rewrite Hdomdiff.
      exact (vproto_ok_reclaim (v_cfg v) pr (dom dma) p sl pin Hok Huixnr
               Hdone Hpin). }
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hah|].
    iSplitR; [iPureIntro; exact Htkc|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR.
    { iPureIntro. apply (read_bytes_transfer dma); [| exact Hridx].
      intros j Hj. assert (Hj2 : (j < 2)%nat) by lia.
      apply Hframe. intro Hc'.
      exact (proj1 (elem_of_disjoint _ _) Hstand _ Hc'
               (elem_of_union_r _ _ _ (used_idx_in_page (v_cfg v) j Hj2))). }
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR; [iPureIntro; exact Hwt|].
    (* the OTHER done records survive the shrink *)
    assert (Hmono : forall k u' x, delete p (vp_done pr) !! k = Some x ->
              vp_uix pr !! k = Some u' ->
              slot_done_res γ (v_cfg v) dma u' x
              ⊢ slot_done_res γ (v_cfg v)
                  (dma ∖ (pin ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
                     ∪ (if vs_is_out sl then ∅
                        else range_map (vr_buf (vs_req sl)) (length bs)
                               (fun j : nat => bs !!! j))))) u' x).
    { intros k u' x Hk Hu'. apply bi.wand_entails.
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
                 (elem_of_union_r _ _ _ (used_elem_pa_in_page (v_cfg v) u' j Hj))).
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
    (* the surviving records keep their own used index: reclaim moves the
       watermark, never [vp_uix] *)
    iApply (big_sepM_mono
              (fun k x => ∃ u' : nat, ⌜vp_uix pr !! k = Some u'⌝ ∗
                            slot_done_res γ (v_cfg v) dma u' x)%I
              (fun k x => ∃ u' : nat, ⌜vp_uix pr !! k = Some u'⌝ ∗
                            slot_done_res γ (v_cfg v)
                              (dma ∖ (pin ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
                                 ∪ (if vs_is_out sl then ∅
                                    else range_map (vr_buf (vs_req sl)) (length bs)
                                           (fun j : nat => bs !!! j))))) u' x)%I).
    { intros k x Hk. iIntros "H". iDestruct "H" as (u') "[%Hu' Hr]".
      iExists u'. iSplitR; [by iPureIntro|].
      iApply (Hmono k u' x Hk Hu'). iExact "Hr". }
    iExact "Hdone".
  Qed.

End VirtioProto.
