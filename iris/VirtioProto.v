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
From iris.bi.lib Require Import fractional.
From iris.program_logic Require Import weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
(* A6.48 ruling 4: the byte tier of the whole protocol is [TsoCtx.phys_ledger]
   now -- see [WpVirtio.dma_own]'s header. *)
Require Import RiscvLang.
Require Import TsoCtx.
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

(* ===================================================================== *)
(* A6.126 §6: THE LEASE'S HOLES AND THE DONE SLOTS' FOOTPRINTS.            *)
(* The used-index word is a RELEASE WINDOW (TsoCtx.rel_cells) beside the  *)
(* lease; a done slot's writable bytes and used element are STAMPED cells *)
(* at its completion's position ([slot_done_res]); both are holes in      *)
(* [dma_own_x].  The pure side: the hole sets, the exact domain of a       *)
(* completion's write set, and the history's shape.                       *)
(* ===================================================================== *)
Definition used_idx_dom (c : virtio_cfg) : gset Arch.pa :=
  pa_range (used_idx_pa c) 2.
Definition elem_dom (c : virtio_cfg) (p : nat) : gset Arch.pa :=
  pa_range (used_elem_pa c p) 8.
Definition slot_done_dom (c : virtio_cfg) (p : nat) (sl : vslot) : gset Arch.pa :=
  slot_wr sl ∪ elem_dom c p.
Definition done_dom (c : virtio_cfg) (dn : gmap nat vslot) : gset Arch.pa :=
  map_fold (fun p sl acc => slot_done_dom c p sl ∪ acc) ∅ dn.

Lemma done_dom_empty (c : virtio_cfg) : done_dom c ∅ = ∅.
Proof. unfold done_dom. apply map_fold_empty. Qed.

Lemma done_dom_insert (c : virtio_cfg) (dn : gmap nat vslot) (p : nat) (sl : vslot) :
  dn !! p = None ->
  done_dom c (<[p := sl]> dn) = slot_done_dom c p sl ∪ done_dom c dn.
Proof.
  intro H. unfold done_dom.
  apply (map_fold_insert_L (fun p sl acc => slot_done_dom c p sl ∪ acc) ∅ p sl dn);
    [| exact H].
  intros. set_solver.
Qed.

Lemma done_dom_delete (c : virtio_cfg) (dn : gmap nat vslot) (p : nat) (sl : vslot) :
  dn !! p = Some sl ->
  done_dom c dn = slot_done_dom c p sl ∪ done_dom c (delete p dn).
Proof.
  intro H. rewrite -{1}(insert_delete dn p sl H). apply done_dom_insert.
  apply lookup_delete.
Qed.

Lemma elem_of_done_dom (c : virtio_cfg) (dn : gmap nat vslot) (a : Arch.pa) :
  a ∈ done_dom c dn <-> exists p sl, dn !! p = Some sl /\ a ∈ slot_done_dom c p sl.
Proof.
  induction dn as [|p sl dn Hp IH] using map_ind.
  - rewrite done_dom_empty. split.
    + intro H. exfalso. exact (proj1 (elem_of_empty a) H).
    + intros (q & slq & Hq & _). rewrite lookup_empty in Hq. discriminate.
  - rewrite (done_dom_insert c dn p sl Hp) elem_of_union IH. split.
    + intros [H | (q & slq & Hq & Ha)].
      * exists p, sl. rewrite lookup_insert. by split.
      * exists q, slq. rewrite lookup_insert_ne; [by split |].
        intro Heq. rewrite -Heq Hp in Hq. discriminate.
    + intros (q & slq & Hq & Ha). destruct (decide (q = p)) as [-> | Hne].
      * rewrite lookup_insert in Hq. injection Hq as <-. by left.
      * rewrite lookup_insert_ne in Hq; [| exact (fun e => Hne (eq_sym e))]. right. by exists q, slq.
Qed.

Lemma write_byte_list_dom (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (bs : list (bv 8)) :
  dom (write_byte_list mm pa bs) = pa_range pa (length bs) ∪ dom mm.
Proof.
  unfold write_byte_list.
  rewrite (foldr_ins_dom (fun jb => pa_add pa (fst jb)) snd).
  f_equal. unfold pa_range. apply set_eq. intro x.
  rewrite !elem_of_list_to_set !elem_of_list_fmap. split.
  - intros (jb & -> & Hjb). apply elem_of_list_lookup in Hjb as (i & Hi).
    rewrite list_lookup_imap in Hi.
    destruct (bs !! i) as [b|] eqn:Hb; [| discriminate ].
    cbn in Hi. injection Hi as <-. cbn [fst].
    exists i. split; [reflexivity|]. apply elem_of_seq.
    apply lookup_lt_Some in Hb. lia.
  - intros (j & -> & Hj). apply elem_of_seq in Hj.
    destruct (lookup_lt_is_Some_2 bs j ltac:(lia)) as [b Hb].
    exists (j, b). split; [reflexivity|]. apply elem_of_list_lookup.
    exists j. rewrite list_lookup_imap Hb. reflexivity.
Qed.

Lemma pa_range_split8 (a : Arch.pa) :
  pa_range a 8 = pa_range a 4 ∪ pa_range (pa_off a 4) 4.
Proof.
  apply set_eq. intro x. rewrite elem_of_union. split.
  - intro H. apply pa_range_elim in H as (j & Hj & ->).
    destruct (decide (j < 4)%nat) as [Hl | Hl].
    + left. apply pa_range_intro. exact Hl.
    + right.
      assert (Heq : pa_add a j = pa_add (pa_off a 4) (j - 4)).
      { rewrite pa_off_add. change (Z.to_nat 4) with 4%nat. f_equal. lia. }
      rewrite Heq. apply pa_range_intro. lia.
  - intros [H | H]; apply pa_range_elim in H as (j & Hj & ->).
    + apply pa_range_intro. lia.
    + rewrite pa_off_add. apply pa_range_intro. change (Z.to_nat 4) with 4%nat. lia.
Qed.

(* the EXACT domain of a completion's write set: the slot's writable
   bytes, its used element (8 bytes) and the index word *)
Lemma vslot_writes_dom_eq (c : virtio_cfg) (p : nat) (dk : Z -> bv 8) (sl : vslot) :
  vc_qnum c = Z_to_bv 32 8 ->
  dom (vslot_writes c (wrap16 p) dk sl) = slot_done_dom c p sl ∪ used_idx_dom c.
Proof.
  intro Hq. unfold vslot_writes. cbv zeta.
  rewrite (virtio_used_writes_unfold c (wrap16 p) (vs_req sl) Hq) used_elem_at_wrap.
  assert (Hws : dom (<[ vr_status (vs_req sl) := Z_to_bv 8 virtio_blk_s_ok ]>
       (write_bytes
          (write_bytes
             (write_bytes ∅ (used_elem_pa c p) 4
                (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))))
             (pa_off (used_elem_pa c p) 4) 4 (vreq_used_len (vs_req sl)))
          (used_idx_pa c) 2 (bv_add (wrap16 p) (Z_to_bv 16 1))))
     = {[ vr_status (vs_req sl) ]} ∪ elem_dom c p ∪ used_idx_dom c).
  { rewrite dom_insert_L !write_bytes_dom dom_empty_L.
    unfold elem_dom, used_idx_dom.
    change (N.to_nat 4) with 4%nat. change (N.to_nat 2) with 2%nat.
    rewrite (pa_range_split8 (used_elem_pa c p)). set_solver. }
  destruct (vs_is_out sl) eqn:Hout.
  - rewrite Hws. unfold slot_done_dom, slot_wr. rewrite Hout. cbn match.
    set (E := elem_dom c p). set (U := used_idx_dom c). clearbody E U.
    set_solver.
  - rewrite write_byte_list_dom disk_read_length Hws.
    unfold slot_done_dom, slot_wr. rewrite Hout. cbn match.
    set (E := elem_dom c p). set (U := used_idx_dom c).
    set (B := pa_range (vr_buf (vs_req sl)) (vs_len sl)). clearbody E U B.
    set_solver.
Qed.

(* the two per-byte floor stamps of the index word, as a function *)
Definition tf2 (t0 t1 : nat) : nat -> nat :=
  fun k => match k with O => t0 | _ => t1 end.
Lemma tf2_0 (t0 t1 : nat) : tf2 t0 t1 0 = t0. Proof. reflexivity. Qed.
Lemma tf2_1 (t0 t1 : nat) : tf2 t0 t1 1 = t1. Proof. reflexivity. Qed.

(* the history's shape: one entry per completion, in log order, entry [k]
   writing the index [S k] *)
Definition hist_ok (hist : list (nat * (nat -> bv 8))) (nc : nat) : Prop :=
  length hist = nc
  /\ (forall k q g, hist !! k = Some (q, g) -> g = nth_byte (wrap16 (S k)))
  /\ (forall k k' q q' g g', (k < k')%nat ->
        hist !! k = Some (q, g) -> hist !! k' = Some (q', g') -> (q < q')%nat).

Lemma hist_ok_nil : hist_ok [] 0.
Proof.
  split_and!; [reflexivity | |].
  - intros k q g H. rewrite lookup_nil in H. discriminate.
  - intros k k' q q' g g' _ H. rewrite lookup_nil in H. discriminate.
Qed.

Lemma hist_ok_app (hist : list (nat * (nat -> bv 8))) (nc q : nat) :
  hist_ok hist nc ->
  (forall k q' g, hist !! k = Some (q', g) -> (q' < q)%nat) ->
  hist_ok (hist ++ [(q, nth_byte (wrap16 (S nc)))]) (S nc).
Proof.
  intros (Hlen & Hval & Hsort) Hlt. split_and!.
  - rewrite length_app /=. lia.
  - intros k q0 g Hk. apply lookup_app_Some in Hk as [Hk | [Hge Hk]].
    + exact (Hval k q0 g Hk).
    + destruct (k - length hist)%nat as [|d] eqn:Hd; cbn in Hk; [| discriminate ].
      injection Hk as _ Hg. subst g.
      assert (Hk' : k = nc) by lia. subst k. reflexivity.
  - intros k k' q0 q0' g g' Hkk Hk Hk'.
    apply lookup_app_Some in Hk as [Hk | [Hge Hk]];
      apply lookup_app_Some in Hk' as [Hk' | [Hge' Hk']].
    + exact (Hsort k k' q0 q0' g g' Hkk Hk Hk').
    + destruct (k' - length hist)%nat as [|d] eqn:Hd; cbn in Hk'; [| discriminate ].
      injection Hk' as Hq _. subst q0'. exact (Hlt k q0 g Hk).
    + apply lookup_lt_Some in Hk'. lia.
    + destruct (k - length hist)%nat as [|d] eqn:Hd; cbn in Hk; [| discriminate ].
      destruct (k' - length hist)%nat as [|d'] eqn:Hd'; cbn in Hk'; [| discriminate ].
      lia.
Qed.

Lemma hist_ok_lookup_lt (hist : list (nat * (nat -> bv 8))) (nc k : nat) :
  hist_ok hist nc -> (k < nc)%nat -> exists q, hist !! k = Some (q, nth_byte (wrap16 (S k))).
Proof.
  intros (Hlen & Hval & _) Hk.
  destruct (hist !! k) as [[q g]|] eqn:Hx.
  - exists q. rewrite (Hval k q g Hx). reflexivity.
  - exfalso. apply lookup_ge_None_1 in Hx. lia.
Qed.

(* the used page with the index word carved out: what the lease holds
   sealed at init, beside the word's two stamped cells *)
Definition used_page_rest (c : virtio_cfg) : gmap Arch.pa (bv 8) :=
  filter (fun p : Arch.pa * bv 8 => p.1 ∉ used_idx_dom c)
    (range_map (vc_used c) 4096 (fun _ : nat => byte_zero)).

(* Membership in a [pa_range] is decidable -- stated with the LENGTH
   ABSTRACT so the instance search never meets [seq 0 4096].  Inline
   [decide (a in pa_range b 4096)] pays that search at every call site. *)
Lemma pa_range_decide (b : Arch.pa) (n : nat) (a : Arch.pa) :
  Decision (a ∈ pa_range b n).
Proof. unfold pa_range. apply _. Qed.

(* the used page minus the index word, as the two windows the boot's
   carve-out produces (DiskAvail.used_split_init) *)
Lemma used_page_rest_split (c : virtio_cfg) :
  used_page_rest c
  = range_map (vc_used c) 2 (fun _ : nat => byte_zero)
    ∪ range_map (pa_add (vc_used c) 4) 4092 (fun _ : nat => byte_zero).
Proof.
  assert (Hidx : forall k, pa_add (used_idx_pa c) k = pa_add (vc_used c) (2 + k)).
  { intro k. unfold used_idx_pa, vq_idx_off. rewrite pa_off_add. reflexivity. }
  assert (Hin_idx : forall a, a ∈ used_idx_dom c <->
            exists k, (k < 2)%nat /\ a = pa_add (vc_used c) (2 + k)).
  { intro a. unfold used_idx_dom. split.
    - intro H. apply pa_range_elim in H as (k & Hk & ->). exists k.
      split; [exact Hk | apply Hidx].
    - intros (k & Hk & ->). rewrite -Hidx. apply pa_range_intro. exact Hk. }
  assert (H4096 : Z.of_nat 4096 < 18446744073709551616) by lia.
  unfold used_page_rest. apply map_eq. intro a.
  destruct (pa_range_decide (vc_used c) 4096 a) as [Hin | Hnin].
  - apply pa_range_elim in Hin as (j & Hj & ->).
    assert (Hval : range_map (vc_used c) 4096 (fun _ : nat => byte_zero)
                     !! pa_add (vc_used c) j = Some byte_zero)
      by (apply range_map_lookup; lia).
    assert (Hnotidx : (j < 2)%nat \/ (4 <= j)%nat -> pa_add (vc_used c) j ∉ used_idx_dom c).
    { intros Hor Hc. apply Hin_idx in Hc as (k & Hk & Heq).
      assert (j = 2 + k)%nat by (apply (pa_add_inj (vc_used c)); [lia | lia | exact Heq]).
      lia. }
    assert (Hnot2 : (2 <= j)%nat -> range_map (vc_used c) 2 (fun _ : nat => byte_zero)
                                     !! pa_add (vc_used c) j = None).
    { intro Hge. apply range_map_lookup_out. intro Hc.
      apply pa_range_elim in Hc as (k & Hk & Heq).
      assert (j = k) by (apply (pa_add_inj (vc_used c)); [lia | lia | exact Heq]). lia. }
    destruct (decide (j < 2)%nat) as [Hj2 | Hj2].
    + rewrite (map_lookup_filter_Some_2 _ _ _ _ Hval (Hnotidx (or_introl Hj2))).
      symmetry. apply lookup_union_Some_l. apply range_map_lookup; lia.
    + destruct (decide (j < 4)%nat) as [Hj4 | Hj4].
      * assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ used_idx_dom c)
                       (range_map (vc_used c) 4096 (fun _ : nat => byte_zero))
                       !! pa_add (vc_used c) j = None).
        { apply map_lookup_filter_None. right. intros x _. cbn. intro Hc. apply Hc.
          apply Hin_idx. exists (j - 2)%nat. split; [lia | f_equal; lia]. }
        assert (Hj2' : (2 <= j)%nat) by lia.
        rewrite HL. symmetry. apply lookup_union_None. split; [exact (Hnot2 Hj2')|].
        apply range_map_lookup_out. intro Hc. apply pa_range_elim in Hc as (k & Hk & Heq).
        rewrite pa_add_add in Heq.
        assert (j = 4 + k)%nat by (apply (pa_add_inj (vc_used c)); [lia | lia | exact Heq]).
        lia.
      * assert (Hj4' : (4 <= j)%nat) by lia. assert (Hj2' : (2 <= j)%nat) by lia.
        rewrite (map_lookup_filter_Some_2 _ _ _ _ Hval (Hnotidx (or_intror Hj4'))).
        symmetry. rewrite (lookup_union_r _ _ _ (Hnot2 Hj2')).
        replace (pa_add (vc_used c) j) with (pa_add (pa_add (vc_used c) 4) (j - 4)%nat)
          by (rewrite pa_add_add; f_equal; lia).
        apply range_map_lookup; lia.
  - assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ used_idx_dom c)
                   (range_map (vc_used c) 4096 (fun _ : nat => byte_zero)) !! a = None).
    { apply map_lookup_filter_None. left. apply range_map_lookup_out. exact Hnin. }
    rewrite HL. symmetry. apply lookup_union_None. split.
    + apply range_map_lookup_out. intro Hc. apply Hnin.
      apply pa_range_elim in Hc as (k & Hk & ->). apply pa_range_intro. lia.
    + apply range_map_lookup_out. intro Hc. apply Hnin.
      apply pa_range_elim in Hc as (k & Hk & ->). rewrite pa_add_add.
      apply pa_range_intro. lia.
Qed.

Definition lease_hole_pure (c : virtio_cfg) (pr : vproto) : gset Arch.pa :=
  dom (vproto_ctl c pr) ∪ used_idx_dom c ∪ done_dom c (vp_done pr).

(* the done slots' footprints against each other and against the index word *)
Lemma footprint_idx (c : virtio_cfg) : footprint (used_idx_pa c) 2 = used_idx_dom c.
Proof. reflexivity. Qed.

Lemma elem_dom_in_page (c : virtio_cfg) (p : nat) :
  forall x, x ∈ elem_dom c p -> x ∈ used_page_pas c.
Proof.
  intros x Hx. apply pa_range_elim in Hx as (j & Hj & ->). unfold used_elem_pa.
  apply used_elem_in_page; [apply Z.mod_pos_bound; lia | exact Hj].
Qed.

Lemma elem_dom_disj (c : virtio_cfg) (p q : nat) :
  Z.of_nat p `mod` 8 ≠ Z.of_nat q `mod` 8 -> elem_dom c p ## elem_dom c q.
Proof.
  intro Hne. apply elem_of_disjoint. intros x Hp Hq.
  apply pa_range_elim in Hp as (i & Hi & ->).
  apply pa_range_elim in Hq as (j & Hj & Heq).
  unfold used_elem_pa, vq_used_ring_off, vq_used_elem_size in Heq.
  pose proof (Z.mod_pos_bound (Z.of_nat p) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.of_nat q) 8 ltac:(lia)).
  exact (used_off_ne c (4 + 8 * (Z.of_nat p `mod` 8)) (4 + 8 * (Z.of_nat q `mod` 8)) i j
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq).
Qed.

Lemma elem_idx_disj (c : virtio_cfg) (p : nat) : elem_dom c p ## used_idx_dom c.
Proof.
  apply elem_of_disjoint. intros x Hp Hq.
  apply pa_range_elim in Hp as (i & Hi & ->).
  apply pa_range_elim in Hq as (j & Hj & Heq).
  unfold used_elem_pa, used_idx_pa, vq_used_ring_off, vq_used_elem_size, vq_idx_off in Heq.
  pose proof (Z.mod_pos_bound (Z.of_nat p) 8 ltac:(lia)).
  exact (used_off_ne c (4 + 8 * (Z.of_nat p `mod` 8)) 2 i j
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq).
Qed.

Lemma slot_done_dom_disj (c : virtio_cfg) (p q : nat) (slp slq : vslot) :
  slot_wr slp ## slot_wr slq ->
  slot_wr slp ## used_page_pas c -> slot_wr slq ## used_page_pas c ->
  Z.of_nat p `mod` 8 ≠ Z.of_nat q `mod` 8 ->
  slot_done_dom c p slp ## slot_done_dom c q slq.
Proof.
  intros H1 H2 H3 H4. unfold slot_done_dom.
  pose proof (elem_dom_in_page c p) as Hp. pose proof (elem_dom_in_page c q) as Hq.
  pose proof (elem_dom_disj c p q H4) as He.
  apply elem_of_disjoint. intros x Hx Hy.
  apply elem_of_union in Hx as [Hx | Hx]; apply elem_of_union in Hy as [Hy | Hy].
  - exact (proj1 (elem_of_disjoint _ _) H1 x Hx Hy).
  - exact (proj1 (elem_of_disjoint _ _) H2 x Hx (Hq x Hy)).
  - exact (proj1 (elem_of_disjoint _ _) H3 x Hy (Hp x Hx)).
  - exact (proj1 (elem_of_disjoint _ _) He x Hx Hy).
Qed.

Lemma slot_done_dom_idx_disj (c : virtio_cfg) (p : nat) (sl : vslot) :
  slot_wr sl ## used_page_pas c -> slot_done_dom c p sl ## used_idx_dom c.
Proof.
  intro H. unfold slot_done_dom. apply elem_of_disjoint. intros x Hx Hy.
  apply elem_of_union in Hx as [Hx | Hx].
  - apply (proj1 (elem_of_disjoint _ _) H x Hx).
    apply pa_range_elim in Hy as (j & Hj & ->). apply used_idx_in_page. exact Hj.
  - exact (proj1 (elem_of_disjoint _ _) (elem_idx_disj c p) x Hx Hy).
Qed.

(* a completion writes nothing of another standing slot's done footprint *)
Lemma vslot_writes_none_done (c : virtio_cfg) (dk : Z -> bv 8) (sl slk : vslot)
    (p k : nat) (x : Arch.pa) :
  vc_qnum c = Z_to_bv 32 8 ->
  slot_wr sl ## used_page_pas c -> slot_wr sl ## slot_wr slk ->
  slot_wr slk ## used_page_pas c ->
  Z.of_nat p `mod` 8 ≠ Z.of_nat k `mod` 8 ->
  x ∈ slot_done_dom c k slk ->
  vslot_writes c (wrap16 p) dk sl !! x = None.
Proof.
  intros Hq Hwp Hww Hwk Hne Hx.
  pose proof (slot_done_dom_disj c p k sl slk Hww Hwp Hwk Hne) as Hd.
  apply vslot_writes_none; [exact Hq | | |].
  - intro Hc. exact (proj1 (elem_of_disjoint _ _) Hd x (elem_of_union_l _ _ _ Hc) Hx).
  - rewrite used_elem_at_wrap. intro Hc.
    exact (proj1 (elem_of_disjoint _ _) Hd x (elem_of_union_r _ _ _ Hc) Hx).
  - intro Hc. exact (proj1 (elem_of_disjoint _ _) (slot_done_dom_idx_disj c k slk Hwk) x Hx Hc).
Qed.

Lemma lease_hole_step (c : virtio_cfg) (pr : vproto) (sl : vslot) :
  vp_done pr !! vp_nc pr = None ->
  lease_hole_pure c (vproto_step_state pr sl)
  = lease_hole_pure c pr ∪ slot_done_dom c (vp_nc pr) sl.
Proof.
  intro Hn. unfold lease_hole_pure.
  rewrite (vproto_step_ctl c pr sl) vps_done (done_dom_insert c _ _ _ Hn). set_solver.
Qed.

(* the used element's LENGTH field (bytes 4..7 of the element) *)
Lemma used_writes_len (c : virtio_cfg) (ui : bv 16) (r : vio_req) (j : nat) :
  vc_qnum c = Z_to_bv 32 8 -> (j < 4)%nat ->
  virtio_used_writes c ui r !! pa_add (pa_off (used_elem_at c ui) 4) j
  = Some (nth_byte (vreq_used_len r) j).
Proof.
  intros Hq Hj. rewrite (virtio_used_writes_unfold c ui r Hq).
  pose proof (ui_mod8_bound ui) as Hs.
  rewrite (write_bytes_lookup_out _ (used_idx_pa c) 2
             (bv_add ui (Z_to_bv 16 1)) (pa_add (pa_off (used_elem_at c ui) 4) j)).
  2:{ intro Hc. apply pa_range_elim in Hc as (k & Hk & Heq).
      change (N.to_nat 2) with 2%nat in Hk.
      rewrite pa_off_add in Heq. change (Z.to_nat 4) with 4%nat in Heq.
      unfold used_elem_at, used_idx_pa, vq_used_ring_off, vq_used_elem_size,
        vq_idx_off in Heq.
      exact (used_off_ne c (4 + 8 * (bv_unsigned ui `mod` 8)) 2 (4 + j) k
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq). }
  apply write_bytes_lookup; lia.
Qed.

Lemma vslot_writes_len (c : virtio_cfg) (ui : bv 16) (dk : Z -> bv 8)
    (sl : vslot) (j : nat) :
  vc_qnum c = Z_to_bv 32 8 -> (j < 4)%nat ->
  slot_wr sl ## used_page_pas c ->
  vslot_writes c ui dk sl !! pa_add (pa_off (used_elem_at c ui) 4) j
  = Some (nth_byte (vreq_used_len (vs_req sl)) j).
Proof.
  intros Hq Hj Hdisj. pose proof (ui_mod8_bound ui) as Hs.
  assert (Hwr : pa_add (pa_off (used_elem_at c ui) 4) j ∉ slot_wr sl).
  { intro Hc. apply (proj1 (elem_of_disjoint _ _) Hdisj _ Hc).
    rewrite pa_off_add. change (Z.to_nat 4) with 4%nat.
    unfold used_elem_at. apply used_elem_in_page; lia. }
  rewrite (vslot_writes_out_of_wr c ui dk sl _ Hwr).
  exact (used_writes_len c ui (vs_req sl) j Hq Hj).
Qed.

Lemma elem_head_sub (c : virtio_cfg) (p : nat) :
  forall x, x ∈ pa_range (used_elem_pa c p) 4 -> x ∈ elem_dom c p.
Proof. intros x Hx. unfold elem_dom. rewrite pa_range_split8. apply elem_of_union_l. exact Hx. Qed.
Lemma elem_len_sub (c : virtio_cfg) (p : nat) :
  forall x, x ∈ pa_range (pa_off (used_elem_pa c p) 4) 4 -> x ∈ elem_dom c p.
Proof. intros x Hx. unfold elem_dom. rewrite pa_range_split8. apply elem_of_union_r. exact Hx. Qed.
Lemma elem_len_off_head (c : virtio_cfg) (p : nat) (j : nat) :
  (j < 4)%nat -> pa_add (pa_off (used_elem_pa c p) 4) j ∉ pa_range (used_elem_pa c p) 4.
Proof.
  intros Hj Hc. apply pa_range_elim in Hc as (i & Hi & Heq).
  exact (pa_add_off4_ne (used_elem_pa c p) i j Hi Hj (eq_sym Heq)).
Qed.

(* A6.126 §6: the completion's write set MINUS the index word, as the four
   pieces the done record holds -- the element's head, its length, the
   status byte and (a read) the buffer *)
Definition slot_done_map (c : virtio_cfg) (p : nat) (sl : vslot) (bs : list (bv 8))
    : gmap Arch.pa (bv 8) :=
  range_map (used_elem_pa c p) 4 (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))))
  ∪ (range_map (pa_off (used_elem_pa c p) 4) 4 (nth_byte (vreq_used_len (vs_req sl)))
     ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
        ∪ (if vs_is_out sl then ∅
           else range_map (vr_buf (vs_req sl)) (vs_len sl) (fun j => bs !!! j)))).

Lemma vslot_writes_split (c : virtio_cfg) (p : nat) (dk : Z -> bv 8) (sl : vslot) :
  vc_qnum c = Z_to_bv 32 8 ->
  slot_wr sl ## used_page_pas c ->
  (vs_is_out sl = false ->
     vr_status (vs_req sl) ∉ pa_range (vr_buf (vs_req sl)) (vs_len sl)) ->
  vslot_writes c (wrap16 p) dk sl ∖ snap_of (used_idx_pa c) 2 (wrap16 (S p))
  = slot_done_map c p sl (disk_read dk (vs_sector_off sl) (vs_len sl)).
Proof.
  intros Hq Hwp Hsb.
  assert (H4 : Z.of_nat 4 < 18446744073709551616) by lia.
  assert (Hlenb : Z.of_nat (vs_len sl) < 18446744073709551616) by apply vs_len_bound.
  assert (Hst : vr_status (vs_req sl) ∈ slot_wr sl)
    by (unfold slot_wr; apply elem_of_union_l, elem_of_singleton; reflexivity).
  assert (Hstpg : vr_status (vs_req sl) ∉ used_page_pas c)
    by (intro Hc; exact (proj1 (elem_of_disjoint _ _) Hwp _ Hst Hc)).
  assert (Hbufpg : vs_is_out sl = false -> forall j, (j < vs_len sl)%nat ->
            pa_add (vr_buf (vs_req sl)) j ∉ used_page_pas c).
  { intros Hout j Hj Hc. apply (proj1 (elem_of_disjoint _ _) Hwp (pa_add (vr_buf (vs_req sl)) j)); [| exact Hc].
    unfold slot_wr. rewrite Hout. apply elem_of_union_r, pa_range_intro. exact Hj. }
  assert (Hhpg : forall j, (j < 4)%nat -> pa_add (used_elem_pa c p) j ∈ used_page_pas c)
    by (intros j Hj; apply (elem_dom_in_page c p); apply pa_range_intro; lia).
  assert (Hlpg : forall j, (j < 4)%nat -> pa_add (pa_off (used_elem_pa c p) 4) j ∈ used_page_pas c).
  { intros j Hj. apply (elem_dom_in_page c p). rewrite pa_off_add.
    change (Z.to_nat 4) with 4%nat. apply pa_range_intro. lia. }
  set (R := slot_done_map c p sl (disk_read dk (vs_sector_off sl) (vs_len sl))).
  assert (HRnone : forall a, a ∉ pa_range (used_elem_pa c p) 4 ->
            a ∉ pa_range (pa_off (used_elem_pa c p) 4) 4 ->
            a ≠ vr_status (vs_req sl) ->
            (vs_is_out sl = false -> a ∉ pa_range (vr_buf (vs_req sl)) (vs_len sl)) ->
            R !! a = None).
  { intros a H1 H2 H3 H4'. unfold R, slot_done_map.
    rewrite lookup_union_None. split; [apply range_map_lookup_out; exact H1|].
    rewrite lookup_union_None. split; [apply range_map_lookup_out; exact H2|].
    rewrite lookup_union_None. split.
    { apply lookup_singleton_None. intro Heq. exact (H3 (eq_sym Heq)). }
    destruct (vs_is_out sl) eqn:Hout; [apply lookup_empty|].
    apply range_map_lookup_out. exact (H4' eq_refl). }
  apply map_eq. intro a.
  destruct (decide (a ∈ pa_range (used_idx_pa c) 2)) as [Hidx | Hidx].
  { (* the index word: gone from the left, absent on the right *)
    apply pa_range_elim in Hidx as (j & Hj & ->).
    assert (Hin : pa_add (used_idx_pa c) j ∈ used_page_pas c)
      by (apply used_idx_in_page; exact Hj).
    assert (HL : (vslot_writes c (wrap16 p) dk sl
                  ∖ snap_of (used_idx_pa c) 2 (wrap16 (S p))) !! pa_add (used_idx_pa c) j
                 = None).
    { apply lookup_difference_None. right.
      exists (nth_byte (wrap16 (S p)) j).
      apply (write_bytes_lookup ∅ (used_idx_pa c) 2 (wrap16 (S p)) j); lia. }
    rewrite HL. symmetry. apply HRnone.
    - intro Hc. exact (proj1 (elem_of_disjoint _ _) (elem_idx_disj c p) _
                         (elem_head_sub c p _ Hc) (pa_range_intro _ _ _ Hj)).
    - intro Hc. exact (proj1 (elem_of_disjoint _ _) (elem_idx_disj c p) _
                         (elem_len_sub c p _ Hc) (pa_range_intro _ _ _ Hj)).
    - intro Hc. apply Hstpg. rewrite <- Hc. exact Hin.
    - intros Hout Hc. apply pa_range_elim in Hc as (k & Hk & Heq).
      apply (Hbufpg Hout k Hk). rewrite <- Heq. exact Hin. }
  (* off the index word: the difference is the write set itself *)
  assert (Hsnap : snap_of (used_idx_pa c) 2 (wrap16 (S p)) !! a = None).
  { apply not_elem_of_dom. rewrite dom_snap_of footprint_idx. exact Hidx. }
  assert (HL : forall m : gmap Arch.pa (bv 8),
            (m ∖ snap_of (used_idx_pa c) 2 (wrap16 (S p))) !! a = m !! a).
  { intro m. destruct (m !! a) as [b|] eqn:Hm.
    - apply lookup_difference_Some. split; [exact Hm | exact Hsnap].
    - apply lookup_difference_None. left. exact Hm. }
  rewrite HL.
  destruct (decide (a ∈ pa_range (used_elem_pa c p) 4)) as [Hh | Hh].
  { apply pa_range_elim in Hh as (j & Hj & ->).
    pose proof (vslot_writes_elem c (wrap16 p) dk sl j Hq Hj Hwp) as HE.
    rewrite used_elem_at_wrap in HE. rewrite HE.
    unfold R, slot_done_map. symmetry. apply lookup_union_Some_l.
    apply range_map_lookup; [exact H4 | exact Hj]. }
  destruct (decide (a ∈ pa_range (pa_off (used_elem_pa c p) 4) 4)) as [Hl | Hl].
  { apply pa_range_elim in Hl as (j & Hj & ->).
    pose proof (vslot_writes_len c (wrap16 p) dk sl j Hq Hj Hwp) as HE.
    rewrite used_elem_at_wrap in HE. rewrite HE.
    unfold R, slot_done_map. symmetry.
    rewrite lookup_union_r; [| apply range_map_lookup_out; exact (elem_len_off_head c p j Hj)].
    apply lookup_union_Some_l. apply range_map_lookup; [exact H4 | exact Hj]. }
  destruct (decide (a = vr_status (vs_req sl))) as [-> | Hs].
  { rewrite (vslot_writes_status c (wrap16 p) dk sl Hsb).
    unfold R, slot_done_map. symmetry.
    rewrite lookup_union_r; [| apply range_map_lookup_out; exact Hh].
    rewrite lookup_union_r; [| apply range_map_lookup_out; exact Hl].
    apply lookup_union_Some_l. apply lookup_singleton. }
  destruct (decide (vs_is_out sl = false /\ a ∈ pa_range (vr_buf (vs_req sl)) (vs_len sl)))
    as [[Hout Hb] | Hnb].
  { apply pa_range_elim in Hb as (j & Hj & ->).
    destruct (lookup_lt_is_Some_2 (disk_read dk (vs_sector_off sl) (vs_len sl)) j
                ltac:(rewrite disk_read_length; exact Hj)) as [b Hb].
    rewrite (vslot_writes_buf c (wrap16 p) dk sl j b Hout Hb).
    unfold R, slot_done_map. symmetry.
    rewrite lookup_union_r; [| apply range_map_lookup_out; exact Hh].
    rewrite lookup_union_r; [| apply range_map_lookup_out; exact Hl].
    rewrite lookup_union_r.
    2:{ apply lookup_singleton_None. intro Heq. exact (Hs (eq_sym Heq)). }
    rewrite Hout. rewrite (range_map_lookup _ _ _ j Hlenb Hj).
    rewrite (list_lookup_total_correct _ j b Hb). reflexivity. }
  (* nowhere: nothing written, nothing held *)
  rewrite (vslot_writes_none c (wrap16 p) dk sl a Hq).
  - symmetry. apply HRnone; [exact Hh | exact Hl | exact Hs |].
    intros Hout Hc. apply Hnb. split; [exact Hout | exact Hc].
  - unfold slot_wr. rewrite not_elem_of_union. split.
    + rewrite not_elem_of_singleton. exact Hs.
    + destruct (vs_is_out sl) eqn:Hout; [apply not_elem_of_empty |].
      intro Hc. apply Hnb. split; [reflexivity | exact Hc].
  - rewrite used_elem_at_wrap pa_range_split8. rewrite not_elem_of_union.
    split; [exact Hh | exact Hl].
  - exact Hidx.
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

Lemma lease_hole_sub (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
  vproto_ok c pr D -> lease_hole_pure c pr ⊆ D.
Proof.
  intro Hok. unfold lease_hole_pure. apply union_least; [apply union_least |].
  - unfold vproto_ctl. rewrite dom_union_L avail_idx_bytes_dom.
    apply union_least; [exact (vpo_idx_D _ _ _ Hok) |].
    intros a Ha. apply pins_union_dom_inv in Ha as (q & mq & Hq & Hmq).
    destruct (vproto_slot_of_pin c pr D q mq Hok Hq) as [slq Hsq].
    apply (vpo_fp_D _ _ _ Hok q slq mq Hsq Hq). apply slot_fp_pin. exact Hmq.
  - etransitivity; [| exact (vpo_used_D _ _ _ Hok)]. intros a Ha.
    apply pa_range_elim in Ha as (j & Hj & ->). apply used_idx_in_page. exact Hj.
  - intros a Ha. apply elem_of_done_dom in Ha as (p & sl & Hp & Ha).
    pose proof (vproto_done_slot c pr D p sl Hok Hp) as Hks.
    assert (Hkpin : exists pinq, vp_pin pr !! p = Some pinq).
    { apply elem_of_dom. rewrite (vproto_slot_dom c pr D Hok). apply elem_of_dom.
      by exists sl. }
    destruct Hkpin as [pinq Hpinq].
    unfold slot_done_dom in Ha. apply elem_of_union in Ha as [Ha | Ha].
    + apply (vpo_fp_D _ _ _ Hok p sl pinq Hks Hpinq). apply slot_fp_wr. exact Ha.
    + apply (vpo_used_D _ _ _ Hok). apply (elem_dom_in_page c p). exact Ha.
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
    ([∗ list] j ∈ seq 0 2, phys_ledger (pa_add a j) (DfracOwn 1) (nth_byte w j))%I.
  Definition phys_word4 (a : Arch.pa) (w : bv 32) : iProp Σ :=
    ([∗ list] j ∈ seq 0 4, phys_ledger (pa_add a j) (DfracOwn 1) (nth_byte w j))%I.
  Definition phys_map (mm : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ mm, phys_ledger a (DfracOwn 1) b)%I.
  Definition phys_list (a : Arch.pa) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] j ↦ b ∈ bs, phys_ledger (pa_add a j) (DfracOwn 1) b)%I.

  (* -- byte windows <-> byte maps --------------------------------------- *)

  Lemma dma_own_phys_map (dma : gmap Arch.pa (bv 8)) :
    dma_own dma ⊣⊢ phys_map dma.
  Proof. reflexivity. Qed.

  Lemma phys_map_idx_list (a : Arch.pa) (l : list nat) (f : nat -> bv 8) :
    NoDup l -> (forall j, j ∈ l -> Z.of_nat j < 18446744073709551616) ->
    phys_map (foldr (fun j acc => <[ pa_add a j := f j ]> acc) ∅ l)
    ⊣⊢ ([∗ list] j ∈ l, phys_ledger (pa_add a j) (DfracOwn 1) (f j)).
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
    ⊣⊢ ([∗ list] j ∈ seq 0 n, phys_ledger (pa_add a j) (DfracOwn 1) (f j)).
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
    ⊣⊢ ([∗ list] j ∈ seq 0 n, phys_ledger (pa_add a j) (DfracOwn 1) (g j)).
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
      iDestruct (phys_ledger_ne with "Ha Hb2") as %Hne.
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
    rewrite (big_sepM_union (fun a b => phys_ledger a (DfracOwn 1) b)
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
    rewrite (big_sepM_union (fun a b => phys_ledger a (DfracOwn 1) b)
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

  (* ==================================================================== *)
  (* A6.124: THE LEASE WITH A HOLE, and the ledger cell's halves.          *)
  (*                                                                      *)
  (* The avail-index word is written only by lock holders and read only   *)
  (* by lock holders, so its floor (§0.35′(iv) case 3) belongs in the     *)
  (* LOCK PAYLOAD, not in the device invariant: the payload holds HALF of *)
  (* each of its two ledger cells with the stamp exposed and the floor    *)
  (* beside it ([DiskInv]), and a holder reads with its own half -- no    *)
  (* invariant opened.  The lease keeps the other half, so the device's   *)
  (* view of the word ([dma_agree]) and the publisher's full cell (join   *)
  (* the halves inside the store) are both still there.                   *)
  (*                                                                      *)
  (* So the lease resource has a HOLE at the avail word: [dma_own_x dma D]*)
  (* is [dma_own] over [dma] minus the addresses in [D].  The PURE map    *)
  (* [dma] is unchanged -- every [vproto_ok]/[vproto_ctl] fact stands --  *)
  (* and each carve lemma keeps its shape, plus one premise: the carved   *)
  (* range avoids the hole (all of them do, by [vproto_ok]'s standing     *)
  (* facts).                                                              *)
  (* ==================================================================== *)
  Lemma phys_ledger_at_halves (a : Arch.pa) (v : bv 8) (t : nat) :
    phys_ledger_at a (DfracOwn 1) v t ⊣⊢
    phys_ledger_at a (DfracOwn (1/2)) v t ∗ phys_ledger_at a (DfracOwn (1/2)) v t.
  Proof.
    rewrite /phys_ledger_at /phys_pointsto.
    rewrite (fractional_half (pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn 1) v)).
    rewrite (fractional_half (a ↪[ts_name] (t, TsoMemPa.ts_pay_none))).
    iSplit.
    - iIntros "(([Hp1 Hp2] & %Hr) & [Ht1 Ht2])".
      iSplitL "Hp1 Ht1"; iFrame; by iPureIntro.
    - iIntros "[([Hp1 %Hr] & Ht1) ([Hp2 _] & Ht2)]". iFrame. by iPureIntro.
  Qed.

  Lemma phys_ledger_at_agree (a : Arch.pa) (dq1 dq2 : dfrac) (v1 v2 : bv 8)
      (t1 t2 : nat) :
    phys_ledger_at a dq1 v1 t1 -∗ phys_ledger_at a dq2 v2 t2 -∗
    ⌜v1 = v2 ∧ t1 = t2⌝.
  Proof.
    rewrite /phys_ledger_at /phys_pointsto.
    iIntros "([Hp1 _] & Ht1) ([Hp2 _] & Ht2)".
    iDestruct (pointsto_agree with "Hp1 Hp2") as %Hv.
    iDestruct (ghost_map_elem_agree with "Ht1 Ht2") as %Ht.
    iPureIntro. split; [exact Hv | by injection Ht].
  Qed.

  (* an exposed half meets the lease's sealed half: the same cell *)
  Lemma phys_ledger_at_join_sealed (a : Arch.pa) (v v' : bv 8) (t : nat) :
    phys_ledger_at a (DfracOwn (1/2)) v t -∗ phys_ledger a (DfracOwn (1/2)) v' -∗
    ⌜v' = v⌝ ∗ phys_ledger_at a (DfracOwn 1) v t.
  Proof.
    iIntros "H1 H2". rewrite phys_ledger_unseal /phys_ledger_def.
    iDestruct "H2" as (t') "H2".
    iAssert (phys_ledger_at a (DfracOwn (1/2)) v' t') with "[H2]" as "H2".
    { rewrite /phys_ledger_at. iExact "H2". }
    iDestruct (phys_ledger_at_agree a (DfracOwn (1/2)) (DfracOwn (1/2)) v v' t t'
                 with "H1 H2") as %[<- <-].
    iSplitR; [done|]. rewrite phys_ledger_at_halves. iFrame "H1 H2".
  Qed.

  (* ---- the pure filter algebra ---------------------------------------- *)
  Lemma map_filter_sub_of_disj (mm dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    mm ⊆ dma -> dom mm ## D ->
    mm ⊆ filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma.
  Proof.
    intros Hsub Hd. rewrite elem_of_disjoint in Hd.
    rewrite map_subseteq_spec in Hsub. apply map_subseteq_spec.
    intros a b Hab.
    apply map_lookup_filter_Some_2; [by apply Hsub|].
    cbn. intro Hc. apply (Hd a); [|exact Hc]. apply elem_of_dom. by exists b.
  Qed.

  Lemma map_filter_union_notin (mm dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    dom mm ## D ->
    filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (mm ∪ dma)
    = mm ∪ filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma.
  Proof.
    intro Hd. rewrite elem_of_disjoint in Hd. apply map_eq. intro a.
    destruct (mm !! a) as [b|] eqn:Hm.
    - assert (Ha : a ∉ D).
      { intro Hc. apply (Hd a); [|exact Hc]. apply elem_of_dom. by exists b. }
      rewrite (lookup_union_Some_l _ _ _ _ Hm).
      apply map_lookup_filter_Some_2; [|cbn; exact Ha].
      by rewrite (lookup_union_Some_l _ _ _ _ Hm).
    - rewrite (lookup_union_r _ _ _ Hm).
      destruct (filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma !! a) as [b|] eqn:Hf.
      + apply map_lookup_filter_Some in Hf as [Hdm Ha].
        apply map_lookup_filter_Some_2; [|exact Ha].
        by rewrite (lookup_union_r _ _ _ Hm).
      + apply map_lookup_filter_None.
        apply map_lookup_filter_None in Hf as [Hn | Hp].
        * left. by rewrite (lookup_union_r _ _ _ Hm).
        * right. intros b Hb. rewrite (lookup_union_r _ _ _ Hm) in Hb.
          exact (Hp b Hb).
  Qed.

  Lemma map_filter_union_in (rm dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    dom rm ⊆ D ->
    filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (rm ∪ dma)
    = filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma.
  Proof.
    intro Hsub. apply map_eq. intro a.
    destruct (rm !! a) as [b|] eqn:Hr.
    - assert (Ha : a ∈ D) by (apply Hsub, elem_of_dom; by exists b).
      assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (rm ∪ dma) !! a = None).
      { apply map_lookup_filter_None. right. intros x _. cbn. intro Hc. exact (Hc Ha). }
      assert (HR : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma !! a = None).
      { apply map_lookup_filter_None. right. intros x _. cbn. intro Hc. exact (Hc Ha). }
      by rewrite HL HR.
    - rewrite map_lookup_filter (lookup_union_r _ _ _ Hr). by rewrite map_lookup_filter.
  Qed.

  Lemma map_filter_difference_l (m n : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (m ∖ n)
    = filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) m ∖ n.
  Proof.
    apply map_eq. intro a.
    destruct (n !! a) as [c|] eqn:Hn.
    - assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (m ∖ n) !! a = None).
      { apply map_lookup_filter_None. left. apply lookup_difference_None. right. by exists c. }
      assert (HR : (filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) m ∖ n) !! a = None).
      { apply lookup_difference_None. right. by exists c. }
      by rewrite HL HR.
    - destruct (m !! a) as [b|] eqn:Hm.
      + assert (Hd : (m ∖ n) !! a = Some b) by (apply lookup_difference_Some; by split).
        destruct (decide (a ∈ D)) as [HaD | HaD].
        * assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (m ∖ n) !! a = None).
          { apply map_lookup_filter_None. right. intros x _. cbn. intro Hc. exact (Hc HaD). }
          assert (HR : (filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) m ∖ n) !! a = None).
          { apply lookup_difference_None. left. apply map_lookup_filter_None. right.
            intros x _. cbn. intro Hc. exact (Hc HaD). }
          by rewrite HL HR.
        * assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (m ∖ n) !! a = Some b)
            by (apply map_lookup_filter_Some_2; [exact Hd | cbn; exact HaD]).
          assert (HR : (filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) m ∖ n) !! a = Some b).
          { apply lookup_difference_Some. split; [|exact Hn].
            apply map_lookup_filter_Some_2; [exact Hm | cbn; exact HaD]. }
          by rewrite HL HR.
      + assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (m ∖ n) !! a = None).
        { apply map_lookup_filter_None. left. apply lookup_difference_None. by left. }
        assert (HR : (filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) m ∖ n) !! a = None).
        { apply lookup_difference_None. left. apply map_lookup_filter_None. by left. }
        by rewrite HL HR.
  Qed.

  Lemma dom_filter_notin (dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    dom (filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma) = dom dma ∖ D.
  Proof.
    apply set_eq. intro a. rewrite elem_of_difference !elem_of_dom. split.
    - intros [b Hb]. apply map_lookup_filter_Some in Hb as [Hb Ha].
      split; [by exists b | exact Ha].
    - intros [[b Hb] Ha]. exists b. apply map_lookup_filter_Some_2; [exact Hb | cbn; exact Ha].
  Qed.

  Lemma map_filter_id_notin (dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    dom dma ## D -> filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma = dma.
  Proof.
    intro Hd. rewrite elem_of_disjoint in Hd. apply map_filter_id.
    intros a b Hab. cbn. intro Hc. apply (Hd a); [|exact Hc]. apply elem_of_dom. by exists b.
  Qed.

  (* ---- the holed lease ------------------------------------------------- *)
  Definition dma_own_x (dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) : iProp Σ :=
    dma_own (filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma).

  Lemma dma_own_x_of_own (dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    dom dma ## D -> dma_own dma -∗ dma_own_x dma D.
  Proof. intro Hd. rewrite /dma_own_x (map_filter_id_notin dma D Hd). iIntros "$". Qed.

  Lemma dma_own_x_extend (rm dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    dom rm ⊆ D -> dma_own_x dma D -∗ dma_own_x (rm ∪ dma) D.
  Proof. intro H. rewrite /dma_own_x (map_filter_union_in rm dma D H). iIntros "$". Qed.

  Lemma dma_own_x_acc_same (mm dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    mm ⊆ dma -> dom mm ## D ->
    dma_own_x dma D -∗ phys_map mm ∗ (phys_map mm -∗ dma_own_x dma D).
  Proof.
    intros Hsub Hd. rewrite /dma_own_x. apply dma_own_acc_same.
    exact (map_filter_sub_of_disj _ _ _ Hsub Hd).
  Qed.

  Lemma dma_own_x_acc (mm mm' dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    mm ⊆ dma -> dom mm' = dom mm -> dom mm ## D ->
    dma_own_x dma D -∗ phys_map mm ∗ (phys_map mm' -∗ dma_own_x (mm' ∪ dma) D).
  Proof.
    intros Hsub Hdom Hd. rewrite /dma_own_x. iIntros "Hd".
    iDestruct (dma_own_acc mm mm' _ (map_filter_sub_of_disj _ _ _ Hsub Hd) Hdom
                 with "Hd") as "[$ Hback]".
    iIntros "Hmm". iDestruct ("Hback" with "Hmm") as "Hd".
    rewrite (map_filter_union_notin mm' dma D); [iExact "Hd" | rewrite Hdom; exact Hd].
  Qed.

  Lemma dma_own_x_shrink (mm dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    mm ⊆ dma -> dom mm ## D ->
    dma_own_x dma D -∗ phys_map mm ∗ dma_own_x (dma ∖ mm) D.
  Proof.
    intros Hsub Hd. rewrite /dma_own_x.
    rewrite (dma_own_split mm _ (map_filter_sub_of_disj _ _ _ Hsub Hd)).
    rewrite (map_filter_difference_l dma mm D). iIntros "$".
  Qed.

  Lemma dma_own_x_disj (dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa)
      (mm : gmap Arch.pa (bv 8)) :
    dma_own_x dma D -∗ phys_map mm -∗ ⌜dom mm ## dom dma ∖ D⌝.
  Proof.
    rewrite /dma_own_x. iIntros "Hd Hm".
    iDestruct (dma_own_disj with "Hd Hm") as %H.
    rewrite dom_filter_notin in H. by iPureIntro.
  Qed.

  Lemma dma_acc_x (w dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    dom w ⊆ dom dma -> dom w ## D ->
    dma_own_x dma D -∗
    ∃ old : gmap Arch.pa (bv 8), ⌜dom old = dom w⌝ ∗ ⌜old ⊆ dma⌝ ∗
      ([∗ map] a ↦ b ∈ old, phys_ledger a (DfracOwn 1) b) ∗
      (([∗ map] a ↦ b ∈ w, phys_ledger a (DfracOwn 1) b) -∗ dma_own_x (w ∪ dma) D).
  Proof.
    intros Hdom Hd. rewrite /dma_own_x. iIntros "Hd".
    assert (Hdom' : dom w ⊆ dom (filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma)).
    { rewrite dom_filter_notin. intros a Ha. apply elem_of_difference.
      split; [by apply Hdom|]. intro Hc. rewrite elem_of_disjoint in Hd.
      exact (Hd a Ha Hc). }
    iDestruct (dma_acc w _ Hdom' with "Hd") as (old) "(%Hdo & %Hos & Hold & Hback)".
    iExists old. iSplitR; [done|]. iSplitR.
    { iPureIntro. etransitivity; [exact Hos | apply map_filter_subseteq]. }
    iFrame "Hold". iIntros "Hnew". iDestruct ("Hback" with "Hnew") as "Hd".
    rewrite (map_filter_union_notin w dma D Hd). iExact "Hd".
  Qed.

  Lemma dma_agree_x (m dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    gen_heap_interp m -∗ dma_own_x dma D -∗
    ⌜filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma ⊆ m⌝.
  Proof. rewrite /dma_own_x. apply dma_agree. Qed.

  (* ---- the avail word's lease half ------------------------------------ *)
  Definition avail_lease_half (c : virtio_cfg) (np : nat) : iProp Σ :=
    ([∗ list] j ∈ seq 0 2,
       phys_ledger (pa_add (avail_idx_pa c) j) (DfracOwn (1/2))
         (nth_byte (wrap16 np) j))%I.

  Lemma avail_half_agree (m : gmap Arch.pa (bv 8)) (c : virtio_cfg) (np : nat) :
    gen_heap_interp m -∗ avail_lease_half c np -∗ ⌜avail_idx_bytes c np ⊆ m⌝.
  Proof.
    iIntros "Hm H". rewrite /avail_lease_half avail_idx_bytes_range.
    iAssert (⌜forall j, (j < 2)%nat ->
               m !! pa_add (avail_idx_pa c) j = Some (nth_byte (wrap16 np) j)⌝)%I
      with "[Hm H]" as %HH.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ _ j j with "H") as "Hj";
        [apply lookup_seq; split; lia|].
      iDestruct (phys_ledger_forget with "Hj") as "Hp". rewrite /phys_pointsto.
      iDestruct "Hp" as "[Hp _]". by iDestruct (gen_heap_valid with "Hm Hp") as %?. }
    iPureIntro. apply range_map_sub; [lia|]. exact HH.
  Qed.

  (* the whole pure lease sits in memory: the holed part by [dma_agree_x],
     the hole by its half cells *)
  Lemma lease_agree (m dma : gmap Arch.pa (bv 8)) (c : virtio_cfg) (np : nat) :
    avail_idx_bytes c np ⊆ dma ->
    gen_heap_interp m -∗ dma_own_x dma (avail_idx_dom c) -∗ avail_lease_half c np -∗
    ⌜dma ⊆ m⌝.
  Proof.
    intro Hab. iIntros "Hm Hd Hh".
    iDestruct (dma_agree_x with "Hm Hd") as %Hx.
    iDestruct (avail_half_agree with "Hm Hh") as %Ha.
    iPureIntro. rewrite map_subseteq_spec. intros a b Hab'.
    destruct (decide (a ∈ avail_idx_dom c)) as [HaD | HaD].
    - rewrite -(avail_idx_bytes_dom c np) in HaD. apply elem_of_dom in HaD as [b' Hb'].
      rewrite map_subseteq_spec in Hab. pose proof (Hab a b' Hb') as Hab2.
      rewrite Hab' in Hab2. injection Hab2 as ->.
      rewrite map_subseteq_spec in Ha. by apply Ha.
    - rewrite map_subseteq_spec in Hx. apply Hx.
      apply map_lookup_filter_Some_2; [exact Hab' | cbn; exact HaD].
  Qed.

  (* a full window and the half cells do not overlap *)
  Lemma phys_map_half_disj (mm : gmap Arch.pa (bv 8)) (c : virtio_cfg) (np : nat) :
    phys_map mm -∗ avail_lease_half c np -∗ ⌜dom mm ## avail_idx_dom c⌝.
  Proof.
    iIntros "Hm H". rewrite /phys_map /avail_lease_half.
    iAssert (⌜forall a, a ∈ dom mm -> a ∈ avail_idx_dom c -> False⌝)%I
      with "[Hm H]" as %HH.
    { rewrite bi.pure_forall. iIntros (a). rewrite !bi.pure_impl. iIntros (Ha Hb).
      apply elem_of_dom in Ha as [b Hb'].
      apply pa_range_elim in Hb as (j & Hj & ->).
      iDestruct (big_sepM_lookup _ _ _ _ Hb' with "Hm") as "Ha".
      iDestruct (big_sepL_lookup _ _ j j with "H") as "Hj";
        [apply lookup_seq; split; lia|].
      iDestruct (phys_ledger_forget with "Ha") as "Hp1".
      iDestruct (phys_ledger_forget with "Hj") as "Hp2".
      iEval (rewrite /phys_pointsto) in "Hp1". iEval (rewrite /phys_pointsto) in "Hp2".
      iDestruct "Hp1" as "[Hp1 _]". iDestruct "Hp2" as "[Hp2 _]".
      iDestruct (pointsto_valid_2 with "Hp1 Hp2") as %[Hv _].
      exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
      exact (Qp.not_add_le_l 1 (1/2)%Qp Hv). }
    iPureIntro. rewrite elem_of_disjoint. exact HH.
  Qed.

  Lemma range_disj_avail (c : virtio_cfg) (a : Arch.pa) (n : nat) (f : nat -> bv 8) :
    (forall j, (j < n)%nat -> pa_add a j ∈ used_page_pas c) ->
    avail_idx_dom c ## used_page_pas c ->
    dom (range_map a n f) ## avail_idx_dom c.
  Proof.
    intros Hin Hd. rewrite range_map_dom. apply gset_disj_sym.
    apply (gset_disj_sub_r _ _ (used_page_pas c)); [| exact Hd].
    intros x Hx. apply pa_range_elim in Hx as (j & Hj & ->). exact (Hin j Hj).
  Qed.

  Lemma ctl_avail_sub (c : virtio_cfg) (pr : vproto) (dma : gmap Arch.pa (bv 8)) :
    vproto_ctl c pr ⊆ dma -> avail_idx_bytes c (vp_np pr) ⊆ dma.
  Proof.
    intro H. unfold vproto_ctl in H.
    etransitivity; [ apply map_union_subseteq_l | exact H ].
  Qed.

  (* a full window is disjoint from the WHOLE pure lease: from the holed
     resource off the hole, and from the half cells on it *)
  Lemma lease_disj (dma mm : gmap Arch.pa (bv 8)) (c : virtio_cfg) (np : nat) :
    dma_own_x dma (avail_idx_dom c) -∗ avail_lease_half c np -∗ phys_map mm -∗
    ⌜dom mm ## dom dma⌝.
  Proof.
    iIntros "Hd Hh Hm".
    iDestruct (dma_own_x_disj with "Hd Hm") as %H1.
    iDestruct (phys_map_half_disj with "Hm Hh") as %H2.
    iPureIntro. rewrite elem_of_disjoint. intros x Hx Hy.
    destruct (decide (x ∈ avail_idx_dom c)) as [HD|HD].
    - exact (proj1 (elem_of_disjoint _ _) H2 x Hx HD).
    - apply (proj1 (elem_of_disjoint _ _) H1 x Hx). apply elem_of_difference. by split.
  Qed.

  (* ================================================================= *)
  (* A6.125 step 2: THE HOLE IS THE WHOLE CONTROL SET.  [vproto_ctl c pr]  *)
  (* (the avail-index word plus every leased pin) is exactly the set of    *)
  (* hart-written, device-read cells; the lease keeps ALL of them at HALF  *)
  (* ([half_map]), sealed, and the holed resource covers the rest.  The    *)
  (* avail-specific kit above is the two-byte special case (A6.124).      *)
  (* ================================================================= *)
  Definition half_map (m : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ m, phys_ledger a (DfracOwn (1/2)) b)%I.

  Lemma half_map_union (m1 m2 : gmap Arch.pa (bv 8)) :
    m1 ##ₘ m2 -> half_map (m1 ∪ m2) ⊣⊢ half_map m1 ∗ half_map m2.
  Proof. intro H. rewrite /half_map. by apply big_sepM_union. Qed.

  Lemma half_map_empty : half_map ∅ ⊣⊢ emp.
  Proof. rewrite /half_map. apply big_sepM_empty. Qed.

  (* the dq-generic form of [phys_map_idx_list] *)
  Lemma ledger_map_idx_list (dq : dfrac) (a : Arch.pa) (l : list nat) (f : nat -> bv 8) :
    NoDup l -> (forall j, j ∈ l -> Z.of_nat j < 18446744073709551616) ->
    ([∗ map] x ↦ b ∈ (foldr (fun j acc => <[ pa_add a j := f j ]> acc) ∅ l),
       phys_ledger x dq b)
    ⊣⊢ ([∗ list] j ∈ l, phys_ledger (pa_add a j) dq (f j)).
  Proof.
    induction l as [|i l IH]; intros Hnd Hb.
    - rewrite big_sepM_empty big_sepL_nil. reflexivity.
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
      cbn [foldr]. rewrite big_sepM_insert; [| exact Hnone ].
      rewrite big_sepL_cons. cbv beta.
      apply bi.sep_proper; [reflexivity|].
      apply IH; [ exact Hnd | intros j Hj; apply Hb, elem_of_list_further, Hj ].
  Qed.

  (* the predicate-generic form: any per-cell predicate over a range map *)
  Lemma range_map_big_sepM (Φ : Arch.pa -> bv 8 -> iProp Σ) (a : Arch.pa) (n : nat)
      (f : nat -> bv 8) :
    Z.of_nat n < 18446744073709551616 ->
    ([∗ map] x ↦ b ∈ range_map a n f, Φ x b)
    ⊣⊢ ([∗ list] j ∈ seq 0 n, Φ (pa_add a j) (f j)).
  Proof.
    intro Hn. rewrite /range_map.
    assert (Hnd : NoDup (seq 0 n)) by apply NoDup_seq.
    assert (Hb : forall j, j ∈ seq 0 n -> Z.of_nat j < 18446744073709551616)
      by (intros j Hj; apply elem_of_seq in Hj; lia).
    revert Hnd Hb. generalize (seq 0 n) as l. clear n Hn.
    induction l as [|i l IH]; intros Hnd Hb.
    - rewrite big_sepM_empty big_sepL_nil. reflexivity.
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
      cbn [foldr]. rewrite big_sepM_insert; [| exact Hnone ].
      rewrite big_sepL_cons. cbv beta.
      apply bi.sep_proper; [reflexivity|].
      apply IH; [ exact Hnd | intros j Hj; apply Hb, elem_of_list_further, Hj ].
  Qed.

  Lemma half_map_range (a : Arch.pa) (n : nat) (f : nat -> bv 8) :
    Z.of_nat n < 18446744073709551616 ->
    half_map (range_map a n f)
    ⊣⊢ ([∗ list] j ∈ seq 0 n, phys_ledger (pa_add a j) (DfracOwn (1/2)) (f j)).
  Proof.
    intro Hn. rewrite /half_map. apply ledger_map_idx_list; [ apply NoDup_seq | ].
    intros j Hj. apply elem_of_seq in Hj. lia.
  Qed.

  Lemma avail_lease_half_eq (c : virtio_cfg) (np : nat) :
    avail_lease_half c np ⊣⊢ half_map (avail_idx_bytes c np).
  Proof.
    rewrite /avail_lease_half avail_idx_bytes_range. symmetry.
    apply half_map_range. lia.
  Qed.

  (* a full sealed cell is two sealed halves, and back *)
  Lemma phys_ledger_split_half (a : Arch.pa) (v : bv 8) :
    phys_ledger a (DfracOwn 1) v ⊢
    phys_ledger a (DfracOwn (1/2)) v ∗ phys_ledger a (DfracOwn (1/2)) v.
  Proof.
    rewrite !phys_ledger_unseal /phys_ledger_def. iIntros "(%t & H)".
    iAssert (phys_ledger_at a (DfracOwn 1) v t) with "[H]" as "H"; [iExact "H"|].
    iEval (rewrite phys_ledger_at_halves) in "H".
    iDestruct "H" as "[H1 H2]". iSplitL "H1"; iExists t; [iExact "H1" | iExact "H2"].
  Qed.

  Lemma phys_ledger_join_half (a : Arch.pa) (v v' : bv 8) :
    phys_ledger a (DfracOwn (1/2)) v -∗ phys_ledger a (DfracOwn (1/2)) v' -∗
    ⌜v' = v⌝ ∗ phys_ledger a (DfracOwn 1) v.
  Proof.
    iIntros "H1 H2". rewrite {1}phys_ledger_unseal /phys_ledger_def.
    iDestruct "H1" as "(%t & H1)".
    iDestruct (phys_ledger_at_join_sealed with "H1 H2") as "[$ H]".
    by iApply phys_ledger_at_ledger.
  Qed.

  Lemma phys_map_split_half (m : gmap Arch.pa (bv 8)) :
    phys_map m ⊢ half_map m ∗ half_map m.
  Proof.
    rewrite /phys_map /half_map -big_sepM_sep.
    apply big_sepM_mono. intros a b _. apply phys_ledger_split_half.
  Qed.

  Lemma half_map_agree (m ctl : gmap Arch.pa (bv 8)) :
    gen_heap_interp m -∗ half_map ctl -∗ ⌜ctl ⊆ m⌝.
  Proof.
    iIntros "Hm H". rewrite /half_map.
    iAssert (⌜forall a b, ctl !! a = Some b -> m !! a = Some b⌝)%I with "[Hm H]" as %HH.
    { rewrite bi.pure_forall. iIntros (a). rewrite bi.pure_forall. iIntros (b).
      rewrite bi.pure_impl. iIntros (Hab).
      iDestruct (big_sepM_lookup _ _ _ _ Hab with "H") as "Ha".
      iDestruct (phys_ledger_forget with "Ha") as "Hp". rewrite /phys_pointsto.
      iDestruct "Hp" as "[Hp _]". by iDestruct (gen_heap_valid with "Hm Hp") as %?. }
    iPureIntro. rewrite map_subseteq_spec. exact HH.
  Qed.

  Lemma lease_agree_ctl (m dma ctl : gmap Arch.pa (bv 8)) :
    ctl ⊆ dma ->
    gen_heap_interp m -∗ dma_own_x dma (dom ctl) -∗ half_map ctl -∗ ⌜dma ⊆ m⌝.
  Proof.
    intro Hab. iIntros "Hm Hd Hh".
    iDestruct (dma_agree_x with "Hm Hd") as %Hx.
    iDestruct (half_map_agree with "Hm Hh") as %Ha.
    iPureIntro. rewrite map_subseteq_spec. intros a b Hab'.
    destruct (decide (a ∈ dom ctl)) as [HaD | HaD].
    - apply elem_of_dom in HaD as [b' Hb'].
      rewrite map_subseteq_spec in Hab. pose proof (Hab a b' Hb') as Hab2.
      rewrite Hab' in Hab2. injection Hab2 as ->.
      rewrite map_subseteq_spec in Ha. by apply Ha.
    - rewrite map_subseteq_spec in Hx. apply Hx.
      apply map_lookup_filter_Some_2; [exact Hab' | cbn; exact HaD].
  Qed.

  (* a full window and any half cells do not overlap *)
  Lemma phys_map_half_map_disj (mm ctl : gmap Arch.pa (bv 8)) :
    phys_map mm -∗ half_map ctl -∗ ⌜dom mm ## dom ctl⌝.
  Proof.
    iIntros "Hm H". rewrite /phys_map /half_map.
    iAssert (⌜forall a, a ∈ dom mm -> a ∈ dom ctl -> False⌝)%I
      with "[Hm H]" as %HH.
    { rewrite bi.pure_forall. iIntros (a). rewrite !bi.pure_impl. iIntros (Ha Hb).
      apply elem_of_dom in Ha as [b Hb']. apply elem_of_dom in Hb as [b2 Hb2].
      iDestruct (big_sepM_lookup _ _ _ _ Hb' with "Hm") as "Ha".
      iDestruct (big_sepM_lookup _ _ _ _ Hb2 with "H") as "Hj".
      iDestruct (phys_ledger_forget with "Ha") as "Hp1".
      iDestruct (phys_ledger_forget with "Hj") as "Hp2".
      iEval (rewrite /phys_pointsto) in "Hp1". iEval (rewrite /phys_pointsto) in "Hp2".
      iDestruct "Hp1" as "[Hp1 _]". iDestruct "Hp2" as "[Hp2 _]".
      iDestruct (pointsto_valid_2 with "Hp1 Hp2") as %[Hv _].
      exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
      exact (Qp.not_add_le_l 1 (1/2)%Qp Hv). }
    iPureIntro. rewrite elem_of_disjoint. exact HH.
  Qed.

  Lemma lease_disj_ctl (dma mm ctl : gmap Arch.pa (bv 8)) :
    dma_own_x dma (dom ctl) -∗ half_map ctl -∗ phys_map mm -∗
    ⌜dom mm ## dom dma⌝.
  Proof.
    iIntros "Hd Hh Hm".
    iDestruct (dma_own_x_disj with "Hd Hm") as %H1.
    iDestruct (phys_map_half_map_disj with "Hm Hh") as %H2.
    iPureIntro. rewrite elem_of_disjoint. intros x Hx Hy.
    destruct (decide (x ∈ dom ctl)) as [HD|HD].
    - exact (proj1 (elem_of_disjoint _ _) H2 x Hx HD).
    - apply (proj1 (elem_of_disjoint _ _) H1 x Hx). apply elem_of_difference. by split.
  Qed.

  (* the hole only matters on the map's domain *)

  Lemma map_filter_hole_ext (m : gmap Arch.pa (bv 8)) (D D' : gset Arch.pa) :
    (forall a, a ∈ dom m -> (a ∈ D <-> a ∈ D')) ->
    filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) m
    = filter (fun p : Arch.pa * bv 8 => p.1 ∉ D') m.
  Proof.
    intro H. apply map_filter_ext. intros a b Hab. cbn.
    assert (Ha : a ∈ dom m) by (apply elem_of_dom; by exists b).
    rewrite (H a Ha). reflexivity.
  Qed.

  (* A6.126 §6: a set of the lease's plain bytes leaves it and the hole grows
     by exactly that set -- the completion taking the slot's done footprint *)
  Lemma dma_own_x_take (S : gset Arch.pa) (dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    S ⊆ dom dma -> S ## D ->
    dma_own_x dma D -∗
    ∃ old : gmap Arch.pa (bv 8),
      ⌜dom old = S⌝ ∗ ⌜old ⊆ dma⌝ ∗ phys_map old ∗ dma_own_x dma (D ∪ S).
  Proof.
    intros Hsub Hd. iIntros "Hd".
    set (old := filter (fun p : Arch.pa * bv 8 => p.1 ∈ S) dma).
    assert (Hos : old ⊆ dma) by apply map_filter_subseteq.
    assert (Hdom : dom old = S).
    { apply set_eq. intro a. rewrite elem_of_dom. split.
      - intros [b Hb]. apply map_lookup_filter_Some in Hb as [_ Ha]. exact Ha.
      - intro Ha. pose proof (Hsub a Ha) as Hin. apply elem_of_dom in Hin as [b Hb].
        exists b. apply map_lookup_filter_Some_2; [exact Hb | cbn; exact Ha]. }
    assert (HdD : dom old ## D) by (rewrite Hdom; exact Hd).
    iDestruct (dma_own_x_shrink old dma D Hos HdD with "Hd") as "[Hold Hd]".
    iExists old. iSplitR; [done|]. iSplitR; [done|]. iFrame "Hold".
    rewrite /dma_own_x.
    assert (Heq : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (dma ∖ old)
                  = filter (fun p : Arch.pa * bv 8 => p.1 ∉ D ∪ S) dma).
    { apply map_eq. intro a. destruct (decide (a ∈ S)) as [HaS | HaS].
      - assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (dma ∖ old) !! a = None).
        { apply map_lookup_filter_None. left. apply lookup_difference_None.
          destruct (dma !! a) as [b|] eqn:Hb; [right | left; reflexivity].
          exists b. apply map_lookup_filter_Some_2; [exact Hb | cbn; exact HaS]. }
        assert (HR : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D ∪ S) dma !! a = None).
        { apply map_lookup_filter_None. right. intros b _. cbn. intro Hc.
          apply Hc. apply elem_of_union_r. exact HaS. }
        by rewrite HL HR.
      - assert (Hnone : old !! a = None).
        { apply map_lookup_filter_None. right. intros b _. cbn. exact HaS. }
        destruct (dma !! a) as [b|] eqn:Hb.
        + assert (Hd' : (dma ∖ old) !! a = Some b)
            by (apply lookup_difference_Some; split; [exact Hb | exact Hnone]).
          destruct (decide (a ∈ D)) as [HaD | HaD].
          * assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (dma ∖ old) !! a = None)
              by (apply map_lookup_filter_None; right; intros x _; cbn; intro Hc; exact (Hc HaD)).
            assert (HR : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D ∪ S) dma !! a = None)
              by (apply map_lookup_filter_None; right; intros x _; cbn; intro Hc;
                  apply Hc; apply elem_of_union_l; exact HaD).
            by rewrite HL HR.
          * assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (dma ∖ old) !! a = Some b)
              by (apply map_lookup_filter_Some_2; [exact Hd' | cbn; exact HaD]).
            assert (HR : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D ∪ S) dma !! a = Some b).
            { apply map_lookup_filter_Some_2; [exact Hb | cbn]. intro Hc.
              apply elem_of_union in Hc as [Hc | Hc]; [exact (HaD Hc) | exact (HaS Hc)]. }
            by rewrite HL HR.
        + assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) (dma ∖ old) !! a = None)
            by (apply map_lookup_filter_None; left; apply lookup_difference_None; left; exact Hb).
          assert (HR : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D ∪ S) dma !! a = None)
            by (apply map_lookup_filter_None; left; exact Hb).
          by rewrite HL HR. }
    rewrite Heq. iExact "Hd".
  Qed.

  (* A6.126 §6: cells of the lease's map that were behind a hole come back
     sealed, and the hole shrinks by exactly their addresses -- the reclaimed
     slot's used element returning to the sealed lease *)
  Lemma dma_own_x_fill (em dma : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    em ⊆ dma -> dom em ⊆ D ->
    dma_own_x dma D -∗ phys_map em -∗ dma_own_x dma (D ∖ dom em).
  Proof.
    intros Hsub HD. rewrite /dma_own_x /dma_own /phys_map. iIntros "Hd Hem".
    assert (Heq : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D ∖ dom em) dma
                  = em ∪ filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma).
    { apply map_eq. intro a. destruct (em !! a) as [b|] eqn:He.
      - assert (Hda : dma !! a = Some b)
          by (rewrite map_subseteq_spec in Hsub; exact (Hsub a b He)).
        rewrite (lookup_union_Some_l _ _ _ _ He).
        apply map_lookup_filter_Some_2; [exact Hda | cbn].
        intro Hc. apply elem_of_difference in Hc as [_ Hc]. apply Hc.
        apply elem_of_dom. by exists b.
      - rewrite (lookup_union_r _ _ _ He).
        assert (Hnd : a ∉ dom em) by (apply not_elem_of_dom; exact He).
        destruct (dma !! a) as [b|] eqn:Hda.
        + destruct (decide (a ∈ D)) as [HaD | HaD].
          * assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D ∖ dom em) dma !! a = None).
            { apply map_lookup_filter_None. right. intros x _. cbn. intro Hc.
              apply Hc. apply elem_of_difference. by split. }
            assert (HR : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma !! a = None)
              by (apply map_lookup_filter_None; right; intros x _; cbn; intro Hc; exact (Hc HaD)).
            by rewrite HL HR.
          * assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D ∖ dom em) dma !! a = Some b).
            { apply map_lookup_filter_Some_2; [exact Hda | cbn]. intro Hc.
              apply elem_of_difference in Hc as [Hc _]. exact (HaD Hc). }
            assert (HR : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma !! a = Some b)
              by (apply map_lookup_filter_Some_2; [exact Hda | cbn; exact HaD]).
            by rewrite HL HR.
        + assert (HL : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D ∖ dom em) dma !! a = None)
            by (apply map_lookup_filter_None; left; exact Hda).
          assert (HR : filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma !! a = None)
            by (apply map_lookup_filter_None; left; exact Hda).
          by rewrite HL HR. }
    assert (Hdisj : em ##ₘ filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) dma).
    { apply map_disjoint_dom. rewrite dom_filter_notin. apply elem_of_disjoint.
      intros a Ha Hb. apply elem_of_difference in Hb as [_ Hb]. exact (Hb (HD a Ha)). }
    rewrite Heq (big_sepM_union _ _ _ Hdisj). iFrame "Hem Hd".
  Qed.

  Lemma dma_own_x_hole_ext (m : gmap Arch.pa (bv 8)) (D D' : gset Arch.pa) :
    (forall a, a ∈ dom m -> (a ∈ D <-> a ∈ D')) ->
    dma_own_x m D ⊣⊢ dma_own_x m D'.
  Proof. intro H. rewrite /dma_own_x (map_filter_hole_ext m D D' H). reflexivity. Qed.

  (* dropping a leased region out of the hole AND out of the map *)
  Lemma map_filter_drop_hole (m pin : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    dom pin ⊆ D ->
    filter (fun p : Arch.pa * bv 8 => p.1 ∉ D ∖ dom pin) (m ∖ pin)
    = filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) m.
  Proof.
    intro HsubD. apply map_eq. intro a.
    destruct (filter (fun p : Arch.pa * bv 8 => p.1 ∉ D) m !! a) as [b|] eqn:HR.
    - apply map_lookup_filter_Some in HR as [Hm HnD]. cbn in HnD.
      apply map_lookup_filter_Some. split.
      + apply lookup_difference_Some. split; [exact Hm|].
        apply not_elem_of_dom. intro Hc. apply HnD. apply HsubD. exact Hc.
      + cbn. intro Hc. apply elem_of_difference in Hc as [Hc _]. exact (HnD Hc).
    - apply map_lookup_filter_None in HR as [Hm | HP].
      + apply map_lookup_filter_None. left. apply lookup_difference_None. left. exact Hm.
      + destruct (m !! a) as [b|] eqn:Hm.
        2:{ apply map_lookup_filter_None. left. apply lookup_difference_None. left. exact Hm. }
        specialize (HP b eq_refl). cbn in HP. apply dec_stable in HP.
        apply map_lookup_filter_None.
        destruct (pin !! a) as [b'|] eqn:Hp.
        * left. apply lookup_difference_None. right. by exists b'.
        * right. intros x Hx. apply lookup_difference_Some in Hx as [Hx _].
          cbn. intro Hc. apply Hc. apply elem_of_difference. split; [exact HP|].
          apply not_elem_of_dom. exact Hp.
  Qed.

  Lemma dma_own_x_drop_hole (m pin : gmap Arch.pa (bv 8)) (D : gset Arch.pa) :
    dom pin ⊆ D ->
    dma_own_x m D ⊣⊢ dma_own_x (m ∖ pin) (D ∖ dom pin).
  Proof. intro H. rewrite /dma_own_x (map_filter_drop_hole m pin D H). reflexivity. Qed.

  (* the used page is off the whole control set *)
  Lemma range_disj_ctl (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa)
      (a : Arch.pa) (n : nat) (f : nat -> bv 8) :
    (forall j, (j < n)%nat -> pa_add a j ∈ used_page_pas c) ->
    vproto_ok c pr D ->
    dom (range_map a n f) ## dom (vproto_ctl c pr).
  Proof.
    intros Hin Hok. rewrite range_map_dom. apply elem_of_disjoint.
    intros x Hx Hc. apply pa_range_elim in Hx as (j & Hj & ->).
    unfold vproto_ctl in Hc. rewrite dom_union_L avail_idx_bytes_dom in Hc.
    apply elem_of_union in Hc as [Hc|Hc].
    - exact (proj1 (elem_of_disjoint _ _) (vpo_idx_used _ _ _ Hok) _ Hc (Hin j Hj)).
    - exact (proj1 (elem_of_disjoint _ _) (pins_union_off_standing _ _ _ Hok) _ Hc
               (elem_of_union_r _ _ _ (Hin j Hj))).
  Qed.

  (* the control set splits into the index word and the pins *)
  Lemma ctl_split_disj (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
    vproto_ok c pr D ->
    avail_idx_bytes c (vp_np pr) ##ₘ pins_union (vp_pin pr).
  Proof.
    intro Hok. apply map_disjoint_dom. rewrite avail_idx_bytes_dom. apply gset_disj_sym.
    apply (gset_disj_sub_r _ _ (avail_idx_dom c ∪ used_page_pas c));
      [ apply union_subseteq_l | exact (pins_union_off_standing _ _ _ Hok) ].
  Qed.

  Lemma half_map_ctl_split (c : virtio_cfg) (pr : vproto) (D : gset Arch.pa) :
    vproto_ok c pr D ->
    half_map (vproto_ctl c pr)
    ⊣⊢ avail_lease_half c (vp_np pr) ∗ half_map (pins_union (vp_pin pr)).
  Proof.
    intro Hok. rewrite /vproto_ctl (half_map_union _ _ (ctl_split_disj _ _ _ Hok))
                 avail_lease_half_eq. reflexivity.
  Qed.

  (* THE PIN OFFER.  Exclusivity of a new pin against the lease is an
     OWNERSHIP fact (the pure protocol cannot see it), and against the
     lease's HALF cells only a more-than-half owner conflicts: so the
     publisher offers each pin cell's memory at 1 with its stamp at ½ --
     which is what a ctx cell minus its arm and half its stamp is (A6.125:
     the ctx side keeps ½ stamp + arm, the caller's half of memory comes
     back through [pin_back]).  The lease keeps the sealed half. *)
  Definition pin_offer (m : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ m,
       phys_pointsto a (DfracOwn (1/2)) b ∗ phys_ledger a (DfracOwn (1/2)) b)%I.
  Definition pin_back (m : gmap Arch.pa (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ b ∈ m, phys_pointsto a (DfracOwn (1/2)) b)%I.

  Lemma pin_offer_split (m : gmap Arch.pa (bv 8)) :
    pin_offer m ⊢ half_map m ∗ pin_back m.
  Proof.
    rewrite /pin_offer /half_map /pin_back -big_sepM_sep.
    apply big_sepM_mono. intros a b _. iIntros "[Hp Hl]". iFrame.
  Qed.

  (* the interim caller (sealed full cells) offers by dropping half a stamp *)
  Lemma phys_map_offer (m : gmap Arch.pa (bv 8)) : phys_map m ⊢ pin_offer m.
  Proof.
    rewrite /phys_map /pin_offer. apply big_sepM_mono. intros a b _.
    iIntros "H". iDestruct (phys_ledger_split_half with "H") as "[H1 H2]".
    iDestruct (phys_ledger_forget with "H1") as "H1". iFrame.
  Qed.

  Lemma pin_offer_union (m1 m2 : gmap Arch.pa (bv 8)) :
    m1 ##ₘ m2 -> pin_offer (m1 ∪ m2) ⊣⊢ pin_offer m1 ∗ pin_offer m2.
  Proof. intro H. rewrite /pin_offer. by apply big_sepM_union. Qed.

  Lemma pin_offer_empty : pin_offer ∅ ⊣⊢ emp.
  Proof. rewrite /pin_offer. apply big_sepM_empty. Qed.

  (* an offered cell is a full memory owner: two offers never overlap *)
  Lemma pin_offer_full (a : Arch.pa) (b : bv 8) :
    phys_pointsto a (DfracOwn (1/2)) b ∗ phys_ledger a (DfracOwn (1/2)) b ⊢
    pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn 1) b.
  Proof.
    iIntros "[Hp Hl]". iDestruct (phys_ledger_forget with "Hl") as "Hp'".
    iEval (rewrite /phys_pointsto) in "Hp". iEval (rewrite /phys_pointsto) in "Hp'".
    iDestruct "Hp" as "[Hp _]". iDestruct "Hp'" as "[Hp' _]".
    rewrite (fractional_half (pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn 1) b)).
    iFrame.
  Qed.

  Lemma pin_offer_disj (m1 m2 : gmap Arch.pa (bv 8)) :
    pin_offer m1 -∗ pin_offer m2 -∗ ⌜m1 ##ₘ m2⌝.
  Proof.
    iIntros "H1 H2". rewrite /pin_offer.
    iAssert (⌜forall a, a ∈ dom m1 -> a ∈ dom m2 -> False⌝)%I with "[H1 H2]" as %HH.
    { rewrite bi.pure_forall. iIntros (a). rewrite !bi.pure_impl. iIntros (Ha Hb).
      apply elem_of_dom in Ha as [b Hb']. apply elem_of_dom in Hb as [b2 Hb2].
      iDestruct (big_sepM_lookup _ _ _ _ Hb' with "H1") as "Hc1".
      iDestruct (big_sepM_lookup _ _ _ _ Hb2 with "H2") as "Hc2".
      iDestruct (pin_offer_full with "Hc1") as "Hp1".
      iDestruct (pin_offer_full with "Hc2") as "Hp2".
      iDestruct (pointsto_valid_2 with "Hp1 Hp2") as %[Hv _].
      exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
      exact (Qp.not_add_le_l 1 1 Hv). }
    iPureIntro. apply map_disjoint_dom. rewrite elem_of_disjoint. exact HH.
  Qed.

  Lemma pin_offer_full_disj (mm pin : gmap Arch.pa (bv 8)) :
    phys_map mm -∗ pin_offer pin -∗ ⌜dom pin ## dom mm⌝.
  Proof.
    iIntros "Hm H". rewrite /phys_map /pin_offer.
    iAssert (⌜forall a, a ∈ dom pin -> a ∈ dom mm -> False⌝)%I with "[Hm H]" as %HH.
    { rewrite bi.pure_forall. iIntros (a). rewrite !bi.pure_impl. iIntros (Ha Hb).
      apply elem_of_dom in Ha as [b Hb']. apply elem_of_dom in Hb as [b2 Hb2].
      iDestruct (big_sepM_lookup _ _ _ _ Hb' with "H") as "[Hp1 _]".
      iDestruct (big_sepM_lookup _ _ _ _ Hb2 with "Hm") as "Hj".
      iDestruct (phys_ledger_forget with "Hj") as "Hp2".
      iEval (rewrite /phys_pointsto) in "Hp1". iEval (rewrite /phys_pointsto) in "Hp2".
      iDestruct "Hp1" as "[Hp1 _]". iDestruct "Hp2" as "[Hp2 _]".
      iDestruct (pointsto_valid_2 with "Hp1 Hp2") as %[Hv _].
      exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
      exact (Qp.not_add_le_r _ _ Hv). }
    iPureIntro. rewrite elem_of_disjoint. exact HH.
  Qed.

  Lemma pin_offer_half_disj (ctl pin : gmap Arch.pa (bv 8)) :
    half_map ctl -∗ pin_offer pin -∗ ⌜dom pin ## dom ctl⌝.
  Proof.
    iIntros "Hm H". rewrite /half_map /pin_offer.
    iAssert (⌜forall a, a ∈ dom pin -> a ∈ dom ctl -> False⌝)%I with "[Hm H]" as %HH.
    { rewrite bi.pure_forall. iIntros (a). rewrite !bi.pure_impl. iIntros (Ha Hb).
      apply elem_of_dom in Ha as [b Hb']. apply elem_of_dom in Hb as [b2 Hb2].
      iDestruct (big_sepM_lookup _ _ _ _ Hb' with "H") as "[Hp1 Hl1]".
      iDestruct (phys_ledger_forget with "Hl1") as "Hp1'".
      iDestruct (big_sepM_lookup _ _ _ _ Hb2 with "Hm") as "Hj".
      iDestruct (phys_ledger_forget with "Hj") as "Hp2".
      iEval (rewrite /phys_pointsto) in "Hp1". iEval (rewrite /phys_pointsto) in "Hp1'".
      iEval (rewrite /phys_pointsto) in "Hp2".
      iDestruct "Hp1" as "[Hp1 _]". iDestruct "Hp1'" as "[Hp1' _]".
      iDestruct "Hp2" as "[Hp2 _]".
      iAssert (pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn 1) b)
        with "[Hp1 Hp1']" as "Hp".
      { rewrite (fractional_half (pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn 1) b)).
        iFrame. }
      iDestruct (pointsto_valid_2 with "Hp Hp2") as %[Hv _].
      exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
      exact (Qp.not_add_le_l 1 (1/2)%Qp Hv). }
    iPureIntro. rewrite elem_of_disjoint. exact HH.
  Qed.

  Lemma pin_offer_lease_disj (dma ctl pin : gmap Arch.pa (bv 8)) :
    dma_own_x dma (dom ctl) -∗ half_map ctl -∗ pin_offer pin -∗
    ⌜dom pin ## dom dma⌝.
  Proof.
    iIntros "Hd Hh Hp".
    rewrite /dma_own_x dma_own_phys_map.
    iDestruct (pin_offer_full_disj with "Hd Hp") as %H1.
    iDestruct (pin_offer_half_disj with "Hh Hp") as %H2.
    rewrite dom_filter_notin in H1.
    iPureIntro. rewrite elem_of_disjoint. intros x Hx Hy.
    destruct (decide (x ∈ dom ctl)) as [HD|HD].
    - exact (proj1 (elem_of_disjoint _ _) H2 x Hx HD).
    - apply (proj1 (elem_of_disjoint _ _) H1 x Hx). apply elem_of_difference. by split.
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

  (* ---- A6.126 §6: the release window beside the lease, and the reader's
     ghosts.  The used-index word is [TsoCtx.rel_cells] (once the device
     has completed something) or its pre-mint form [rel_pre_cells] (the init
     hart's two zero bytes, stamped); [hist_ok] ties the history to the
     completed count; the two floor stamps, the reader floor [F] and the
     reclaimed count [nr] are ghost-var halves shared with
     [DiskInv.disk_res]; the completions' positions are a ghost map whose
     fragments ([disk_done_pos]) are persistent. *)
  Definition used_rel_res (c : virtio_cfg) (nc lo : nat) (tf : nat -> nat)
      (hist : list (nat * (nat -> bv 8))) : iProp Σ :=
    (⌜hist_ok hist nc⌝ ∗
     ⌜forall k, (k < 2)%nat -> (tf k <= lo)%nat⌝ ∗
     ⌜exists k, (k < 2)%nat /\ lo = tf k⌝ ∗
     ((⌜hist = []⌝ ∗ TsoCtx.rel_pre_cells (used_idx_pa c) 2 tf (nth_byte (wrap16 0)))
      ∨ TsoCtx.rel_cells (used_idx_pa c) 2 (DfracOwn 1) disk_agent lo tf
          (nth_byte (wrap16 0)) (nth_byte (wrap16 nc)) hist))%I.
  Global Instance used_rel_res_timeless c nc lo tf hist :
    Timeless (used_rel_res c nc lo tf hist).
  Proof. rewrite /used_rel_res. apply _. Qed.

  Definition disk_done_pos (γ : disk_names) (p q : nat) : iProp Σ :=
    (p ↪[dn_pos γ]□ q)%I.
  Global Instance disk_done_pos_persistent γ p q : Persistent (disk_done_pos γ p q).
  Proof. rewrite /disk_done_pos. apply _. Qed.
  Global Instance disk_done_pos_timeless γ p q : Timeless (disk_done_pos γ p q).
  Proof. rewrite /disk_done_pos. apply _. Qed.
  Lemma disk_done_pos_agree γ p q q' :
    disk_done_pos γ p q -∗ disk_done_pos γ p q' -∗ ⌜q = q'⌝.
  Proof.
    rewrite /disk_done_pos. iIntros "H1 H2".
    by iDestruct (ghost_map_elem_agree with "H1 H2") as %->.
  Qed.
  Definition disk_nr (γ : disk_names) (nr : nat) : iProp Σ :=
    ghost_var (dn_nr γ) (1/2) nr.
  Definition disk_flr (γ : disk_names) (F : nat) : iProp Σ :=
    ghost_var (dn_flr γ) (1/2) F.
  Definition disk_fl (γ : disk_names) (t0 t1 : nat) : iProp Σ :=
    (ghost_var (dn_fl0 γ) (1/2) t0 ∗ ghost_var (dn_fl1 γ) (1/2) t1)%I.
  Definition lease_hole (c : virtio_cfg) (pr : vproto) : gset Arch.pa :=
    lease_hole_pure c pr.

  (* a DONE slot's cells, STAMPED at its completion's position [q]: the used
     element's head and length, the status byte and (a read) the buffer --
     what a reader with [q] in view reads exactly, and what the handler
     reclaims into the lock payload with the stamp *)
  Definition slot_done_cells (c : virtio_cfg) (p : nat) (sl : vslot)
      (bs : list (bv 8)) (q : nat) : iProp Σ :=
    (([∗ list] j ∈ seq 0 4,
        phys_ledger_at (pa_add (used_elem_pa c p) j) (DfracOwn 1)
          (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) j) q) ∗
     ([∗ list] j ∈ seq 0 4,
        phys_ledger_at (pa_add (pa_off (used_elem_pa c p) 4) j) (DfracOwn 1)
          (nth_byte (vreq_used_len (vs_req sl)) j) q) ∗
     phys_ledger_at (vr_status (vs_req sl)) (DfracOwn 1) byte_zero q ∗
     (if vs_is_out sl then emp
      else [∗ list] j ∈ seq 0 (vs_len sl),
             phys_ledger_at (pa_add (vr_buf (vs_req sl)) j) (DfracOwn 1) (bs !!! j) q))%I.
  Global Instance slot_done_cells_timeless c p sl bs q :
    Timeless (slot_done_cells c p sl bs q).
  Proof. rewrite /slot_done_cells. destruct (vs_is_out sl); apply _. Qed.

  (* the cells are the write set's stamped map, in pieces *)
  Lemma slot_done_cells_of_map (c : virtio_cfg) (p : nat) (sl : vslot)
      (bs : list (bv 8)) (q : nat) :
    (vs_is_out sl = false ->
       vr_status (vs_req sl) ∉ pa_range (vr_buf (vs_req sl)) (vs_len sl)) ->
    slot_wr sl ## used_page_pas c ->
    ([∗ map] a ↦ b ∈ slot_done_map c p sl bs, phys_ledger_at a (DfracOwn 1) b q)
    ⊣⊢ slot_done_cells c p sl bs q.
  Proof.
    intros Hsb Hwp.
    assert (H4 : Z.of_nat 4 < 18446744073709551616) by lia.
    assert (Hlenb : Z.of_nat (vs_len sl) < 18446744073709551616) by apply vs_len_bound.
    assert (Hst : vr_status (vs_req sl) ∈ slot_wr sl)
      by (unfold slot_wr; apply elem_of_union_l, elem_of_singleton; reflexivity).
    assert (Hstpg : vr_status (vs_req sl) ∉ used_page_pas c)
      by (intro Hc; exact (proj1 (elem_of_disjoint _ _) Hwp _ Hst Hc)).
    assert (Hbufpg : vs_is_out sl = false -> forall j, (j < vs_len sl)%nat ->
              pa_add (vr_buf (vs_req sl)) j ∉ used_page_pas c).
    { intros Hout j Hj Hc. apply (proj1 (elem_of_disjoint _ _) Hwp (pa_add (vr_buf (vs_req sl)) j)); [| exact Hc].
      unfold slot_wr. rewrite Hout. apply elem_of_union_r, pa_range_intro. exact Hj. }
    assert (Hhpg : forall x, x ∈ pa_range (used_elem_pa c p) 4 -> x ∈ used_page_pas c)
      by (intros x Hx; apply (elem_dom_in_page c p); apply (elem_head_sub c p); exact Hx).
    assert (Hlpg : forall x, x ∈ pa_range (pa_off (used_elem_pa c p) 4) 4 -> x ∈ used_page_pas c)
      by (intros x Hx; apply (elem_dom_in_page c p); apply (elem_len_sub c p); exact Hx).
    assert (Hd3 : {[ vr_status (vs_req sl) := byte_zero ]}
                  ##ₘ (if vs_is_out sl then ∅
                       else range_map (vr_buf (vs_req sl)) (vs_len sl) (fun j => bs !!! j))).
    { apply map_disjoint_dom. rewrite dom_singleton_L. destruct (vs_is_out sl) eqn:Hout.
      - rewrite dom_empty_L. apply disjoint_empty_r.
      - rewrite range_map_dom. apply elem_of_disjoint. intros x Hx Hb.
        apply elem_of_singleton in Hx. rewrite Hx in Hb. exact (Hsb eq_refl Hb). }
    assert (Hd2 : range_map (pa_off (used_elem_pa c p) 4) 4 (nth_byte (vreq_used_len (vs_req sl)))
                  ##ₘ ({[ vr_status (vs_req sl) := byte_zero ]}
                       ∪ (if vs_is_out sl then ∅
                          else range_map (vr_buf (vs_req sl)) (vs_len sl) (fun j => bs !!! j)))).
    { apply map_disjoint_dom. rewrite range_map_dom dom_union_L dom_singleton_L.
      apply elem_of_disjoint. intros x Hx Hy. apply elem_of_union in Hy as [Hy | Hy].
      - apply elem_of_singleton in Hy. rewrite Hy in Hx. exact (Hstpg (Hlpg _ Hx)).
      - destruct (vs_is_out sl) eqn:Hout; [rewrite dom_empty_L in Hy; exact (proj1 (elem_of_empty x) Hy) |].
        rewrite range_map_dom in Hy. apply pa_range_elim in Hy as (j & Hj & ->).
        exact (Hbufpg eq_refl j Hj (Hlpg _ Hx)). }
    assert (Hd1 : range_map (used_elem_pa c p) 4 (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))))
                  ##ₘ (range_map (pa_off (used_elem_pa c p) 4) 4 (nth_byte (vreq_used_len (vs_req sl)))
                       ∪ ({[ vr_status (vs_req sl) := byte_zero ]}
                          ∪ (if vs_is_out sl then ∅
                             else range_map (vr_buf (vs_req sl)) (vs_len sl) (fun j => bs !!! j))))).
    { apply map_disjoint_dom. rewrite range_map_dom !dom_union_L range_map_dom dom_singleton_L.
      apply elem_of_disjoint. intros x Hx Hy.
      apply elem_of_union in Hy as [Hy | Hy].
      { apply pa_range_elim in Hy as (j & Hj & ->). exact (elem_len_off_head c p j Hj Hx). }
      apply elem_of_union in Hy as [Hy | Hy].
      - apply elem_of_singleton in Hy. rewrite Hy in Hx. exact (Hstpg (Hhpg _ Hx)).
      - destruct (vs_is_out sl) eqn:Hout; [rewrite dom_empty_L in Hy; exact (proj1 (elem_of_empty x) Hy) |].
        rewrite range_map_dom in Hy. apply pa_range_elim in Hy as (j & Hj & ->).
        exact (Hbufpg eq_refl j Hj (Hhpg _ Hx)). }
    unfold slot_done_map, slot_done_cells.
    rewrite (big_sepM_union _ _ _ Hd1) (big_sepM_union _ _ _ Hd2) (big_sepM_union _ _ _ Hd3).
    rewrite (range_map_big_sepM _ _ _ _ H4) (range_map_big_sepM _ _ _ _ H4) big_sepM_singleton.
    destruct (vs_is_out sl) eqn:Hout.
    - rewrite big_sepM_empty. reflexivity.
    - rewrite (range_map_big_sepM _ _ _ _ Hlenb). reflexivity.
  Qed.

  Definition slot_done_res (γ : disk_names) (c : virtio_cfg)
      (dma : gmap Arch.pa (bv 8)) (hist : list (nat * (nat -> bv 8)))
      (p : nat) (sl : vslot) : iProp Σ :=
    (∃ (bs : list (bv 8)) (q : nat),
       ⌜length bs = vs_len sl⌝ ∗ disk_bytes γ (vs_sector_off sl) bs ∗
       ⌜bs = vs_data sl⌝ ∗
       ⌜read_bytes dma (used_elem_pa c p) 4
          = Some (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl))))⌝ ∗
       ⌜read_bytes dma (pa_off (used_elem_pa c p) 4) 4
          = Some (vreq_used_len (vs_req sl))⌝ ∗
       ⌜dma !! vr_status (vs_req sl) = Some byte_zero⌝ ∗
       ⌜vs_is_out sl = false ->
          read_byte_list dma (vr_buf (vs_req sl)) (vs_len sl) = Some bs⌝ ∗
       ⌜exists g, hist !! p = Some (q, g)⌝ ∗
       slot_done_cells c p sl bs q ∗
       slot_perms_done γ sl)%I.
  Global Instance slot_done_res_timeless γ c dma hist p sl :
    Timeless (slot_done_res γ c dma hist p sl).
  Proof. rewrite /slot_done_res. apply _. Qed.

  Lemma slot_done_res_mono (γ : disk_names) (c : virtio_cfg)
      (dma dma' : gmap Arch.pa (bv 8)) (hist hist' : list (nat * (nat -> bv 8)))
      (p : nat) (sl : vslot) :
    (forall a, a ∈ slot_done_dom c p sl -> dma' !! a = dma !! a) ->
    hist' !! p = hist !! p ->
    slot_done_res γ c dma hist p sl -∗ slot_done_res γ c dma' hist' p sl.
  Proof.
    intros Hsame Hh. iIntros "H".
    iDestruct "H" as (bs q)
      "(%Hlen & Hbs & %Hout & %Hre & %Hrl & %Hst & %Hbl & %Hq & Hcells & Hperm)".
    assert (Hhead : forall j, (j < 4)%nat ->
              dma' !! pa_add (used_elem_pa c p) j = dma !! pa_add (used_elem_pa c p) j).
    { intros j Hj. apply Hsame. unfold slot_done_dom. apply elem_of_union_r.
      apply (elem_head_sub c p). apply pa_range_intro. exact Hj. }
    assert (Hlen' : forall j, (j < 4)%nat ->
              dma' !! pa_add (pa_off (used_elem_pa c p) 4) j
              = dma !! pa_add (pa_off (used_elem_pa c p) 4) j).
    { intros j Hj. apply Hsame. unfold slot_done_dom. apply elem_of_union_r.
      apply (elem_len_sub c p). apply pa_range_intro. exact Hj. }
    assert (Hstat : dma' !! vr_status (vs_req sl) = dma !! vr_status (vs_req sl)).
    { apply Hsame. unfold slot_done_dom. apply elem_of_union_l. unfold slot_wr.
      apply elem_of_union_l, elem_of_singleton. reflexivity. }
    iExists bs, q. iFrame "Hbs Hcells Hperm". iPureIntro. split_and!.
    - exact Hlen.
    - exact Hout.
    - apply (read_bytes_transfer dma dma'); [| exact Hre ].
      intros j Hj. apply Hhead. lia.
    - apply (read_bytes_transfer dma dma'); [| exact Hrl ].
      intros j Hj. apply Hlen'. lia.
    - rewrite Hstat. exact Hst.
    - intros Hin. apply (read_byte_list_transfer dma dma'); [| exact (Hbl Hin) ].
      intros j Hj. apply Hsame. unfold slot_done_dom. apply elem_of_union_l.
      unfold slot_wr. rewrite Hin. apply elem_of_union_r, pa_range_intro. exact Hj.
    - rewrite Hh. exact Hq.
  Qed.

  (* one cell of a done slot, by address, with the byte the lease's map holds *)
  Lemma slot_done_cell_at (γ : disk_names) (c : virtio_cfg) (dma : gmap Arch.pa (bv 8))
      (hist : list (nat * (nat -> bv 8))) (p : nat) (sl : vslot) (a : Arch.pa) :
    a ∈ slot_done_dom c p sl ->
    slot_done_res γ c dma hist p sl -∗
    ∃ (b : bv 8) (q : nat), ⌜dma !! a = Some b⌝ ∗
      (phys_ledger_at a (DfracOwn 1) b q ∗ (phys_ledger_at a (DfracOwn 1) b q -∗ slot_done_res γ c dma hist p sl)).
  Proof.
    intro Ha. iIntros "H".
    iDestruct "H" as (bs q)
      "(%Hlen & Hbs & %Hout & %Hre & %Hrl & %Hst & %Hbl & %Hq & Hcells & Hperm)".
    rewrite /slot_done_cells. iDestruct "Hcells" as "(Hh & Hl & Hs & Hb)".
    unfold slot_done_dom, elem_dom in Ha. rewrite pa_range_split8 in Ha.
    apply elem_of_union in Ha as [Ha | Ha].
    - unfold slot_wr in Ha. apply elem_of_union in Ha as [Ha | Ha].
      + apply elem_of_singleton in Ha. subst a.
        iExists byte_zero, q. iSplitR; [iPureIntro; exact Hst|]. iFrame "Hs".
        iIntros "Hs". iExists bs, q. iFrame "Hbs Hh Hl Hs Hb Hperm". iPureIntro. by split_and!.
      + destruct (vs_is_out sl) eqn:Ho; [exfalso; exact (proj1 (elem_of_empty a) Ha)|].
        apply pa_range_elim in Ha as (j & Hj & ->).
        destruct (read_byte_list_spec dma (vr_buf (vs_req sl)) (vs_len sl) bs (Hbl eq_refl)) as [_ Hlk].
        destruct (lookup_lt_is_Some_2 bs j ltac:(lia)) as [b Hb].
        iDestruct (big_sepL_lookup_acc _ (seq 0 (vs_len sl)) j j with "Hb") as "[Hc Hback]".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iExists b, q. iSplitR; [iPureIntro; exact (Hlk j b Hb)|].
        rewrite (list_lookup_total_correct bs j b Hb). iFrame "Hc".
        iIntros "Hc". iDestruct ("Hback" with "Hc") as "Hb".
        rewrite /slot_done_res /slot_done_cells Ho.
        iExists bs, q. iFrame "Hbs Hh Hl Hs Hb Hperm". iPureIntro. by split_and!.
    - apply elem_of_union in Ha as [Ha | Ha].
      + apply pa_range_elim in Ha as (j & Hj & ->).
        iDestruct (big_sepL_lookup_acc _ (seq 0 4) j j with "Hh") as "[Hc Hback]".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iExists _, q. iSplitR; [iPureIntro; exact (read_bytes_spec dma _ 4 _ Hre j ltac:(lia))|].
        iFrame "Hc". iIntros "Hc". iDestruct ("Hback" with "Hc") as "Hh".
        iExists bs, q. iFrame "Hbs Hh Hl Hs Hb Hperm". iPureIntro. by split_and!.
      + apply pa_range_elim in Ha as (j & Hj & ->).
        iDestruct (big_sepL_lookup_acc _ (seq 0 4) j j with "Hl") as "[Hc Hback]".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iExists _, q. iSplitR; [iPureIntro; exact (read_bytes_spec dma _ 4 _ Hrl j ltac:(lia))|].
        iFrame "Hc". iIntros "Hc". iDestruct ("Hback" with "Hc") as "Hl".
        iExists bs, q. iFrame "Hbs Hh Hl Hs Hb Hperm". iPureIntro. by split_and!.
  Qed.

  (* ---- A6.126 §6: THE WHOLE LEASE against memory and against a foreign
     map.  The three holes' cells -- the half cells (ctl), the index word
     (pre-mint or minted) and the done slots' stamped cells -- each carry a
     [pointsto] at the lease's own byte, so the lease's pure map is in
     memory and nothing else owns a byte of it. ---- *)
  Lemma lease_agree_full (m dma : gmap Arch.pa (bv 8)) (γ : disk_names)
      (c : virtio_cfg) (pr : vproto) (lo : nat) (tf : nat -> nat)
      (hist : list (nat * (nat -> bv 8))) :
    vproto_ctl c pr ⊆ dma ->
    read_bytes dma (used_idx_pa c) 2 = Some (wrap16 (vp_nc pr)) ->
    gen_heap_interp m -∗ dma_own_x dma (lease_hole c pr) -∗
    half_map (vproto_ctl c pr) -∗
    used_rel_res c (vp_nc pr) lo tf hist -∗
    ([∗ map] p ↦ sl ∈ vp_done pr, slot_done_res γ c dma hist p sl) -∗
    ⌜dma ⊆ m⌝.
  Proof.
    intros Hctl Hridx. iIntros "Hm Hd Hh Hrel Hdone".
    iDestruct (dma_agree_x with "Hm Hd") as %Hx.
    iDestruct (half_map_agree with "Hm Hh") as %Ha.
    iAssert (⌜forall j, (j < 2)%nat ->
               m !! pa_add (used_idx_pa c) j = Some (nth_byte (wrap16 (vp_nc pr)) j)⌝)%I
      as %Hidx.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct "Hrel" as "(%Hho & _ & _ & [[%Hnil Hpre] | Hcells])".
      - assert (Hnc0 : vp_nc pr = 0%nat)
          by (destruct Hho as [Hlen _]; rewrite Hnil in Hlen; cbn in Hlen; lia).
        rewrite /TsoCtx.rel_pre_cells.
        iDestruct (big_sepL_lookup _ (seq 0 2) j j with "Hpre") as "Hc".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iDestruct (phys_ledger_at_forget with "Hc") as "Hc". rewrite /phys_pointsto. iDestruct "Hc" as "[Hc _]".
        iDestruct (gen_heap_valid with "Hm Hc") as %Hv. iPureIntro.
        rewrite Hnc0. exact Hv.
      - rewrite /TsoCtx.rel_cells.
        iDestruct (big_sepL_lookup _ (seq 0 2) j j with "Hcells") as (t) "Hc".
        { rewrite lookup_seq_lt; [reflexivity | lia]. }
        iDestruct (phys_ledger_rpay_forget with "Hc") as "Hc". rewrite /phys_pointsto. iDestruct "Hc" as "[Hc _]".
        by iDestruct (gen_heap_valid with "Hm Hc") as %Hv. }
    iAssert (⌜forall a b, a ∈ done_dom c (vp_done pr) -> dma !! a = Some b ->
               m !! a = Some b⌝)%I as %Hdn.
    { rewrite bi.pure_forall. iIntros (a). rewrite bi.pure_forall. iIntros (b).
      rewrite !bi.pure_impl. iIntros (Hin Hab).
      apply elem_of_done_dom in Hin as (p & sl & Hp & Hin).
      iDestruct (big_sepM_lookup _ _ _ _ Hp with "Hdone") as "Hs".
      iDestruct (slot_done_cell_at _ _ _ _ _ _ a Hin with "Hs") as (b' q) "(%Hb' & Hc & _)".
      rewrite Hab in Hb'. injection Hb' as ->.
      iDestruct (phys_ledger_at_forget with "Hc") as "Hc". rewrite /phys_pointsto. iDestruct "Hc" as "[Hc _]".
      by iDestruct (gen_heap_valid with "Hm Hc") as %?. }
    iPureIntro. rewrite map_subseteq_spec. intros a b Hab.
    destruct (decide (a ∈ lease_hole c pr)) as [Hin | Hnin].
    - unfold lease_hole, lease_hole_pure in Hin.
      apply elem_of_union in Hin as [Hin | Hin];
        [ apply elem_of_union in Hin as [Hin | Hin] | ].
      + apply elem_of_dom in Hin as [b' Hb'].
        rewrite map_subseteq_spec in Hctl. pose proof (Hctl a b' Hb') as H.
        rewrite Hab in H. injection H as ->.
        rewrite map_subseteq_spec in Ha. exact (Ha a b' Hb').
      + apply pa_range_elim in Hin as (j & Hj & ->).
        rewrite (read_bytes_spec dma (used_idx_pa c) 2 _ Hridx j ltac:(lia)) in Hab.
        injection Hab as <-. exact (Hidx j Hj).
      + exact (Hdn a b Hin Hab).
    - rewrite map_subseteq_spec in Hx. apply Hx.
      apply map_lookup_filter_Some_2; [exact Hab | cbn; exact Hnin].
  Qed.

  Lemma lease_disj_full (dma mm : gmap Arch.pa (bv 8)) (γ : disk_names)
      (c : virtio_cfg) (pr : vproto) (lo : nat) (tf : nat -> nat)
      (hist : list (nat * (nat -> bv 8))) :
    dma_own_x dma (lease_hole c pr) -∗
    half_map (vproto_ctl c pr) -∗
    used_rel_res c (vp_nc pr) lo tf hist -∗
    ([∗ map] p ↦ sl ∈ vp_done pr, slot_done_res γ c dma hist p sl) -∗
    ([∗ map] a ↦ b ∈ mm, pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn 1) b) -∗
    ⌜dom mm ## dom dma⌝.
  Proof.
    iIntros "Hd Hh Hrel Hdone Hm".
    iAssert (⌜forall a, a ∈ dom mm -> a ∈ dom dma -> False⌝)%I as %HH;
      last (iPureIntro; rewrite elem_of_disjoint; exact HH).
    rewrite bi.pure_forall. iIntros (a). rewrite !bi.pure_impl. iIntros (Hmm Hdma).
    apply elem_of_dom in Hmm as [bm Hbm].
    iDestruct (big_sepM_lookup _ _ _ _ Hbm with "Hm") as "Hpm".
    (* every arm ends by clashing a full [pointsto] of the lease's with [Hpm] *)
    iAssert (∀ dq b, pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn dq) b -∗ False)%I
      with "[Hpm]" as "Hclash".
    { iIntros (dq b) "Hp".
      iDestruct (pointsto_valid_2 with "Hpm Hp") as %[Hv _].
      exfalso. rewrite dfrac_op_own dfrac_valid_own in Hv.
      exact (Qp.not_add_le_l 1 dq Hv). }
    destruct (decide (a ∈ lease_hole c pr)) as [Hin | Hnin].
    - unfold lease_hole, lease_hole_pure in Hin.
      apply elem_of_union in Hin as [Hin | Hin];
        [ apply elem_of_union in Hin as [Hin | Hin] | ].
      + apply elem_of_dom in Hin as [b' Hb'].
        rewrite /half_map.
        iDestruct (big_sepM_lookup _ _ _ _ Hb' with "Hh") as "Hc".
        iDestruct (phys_ledger_forget with "Hc") as "Hc". rewrite /phys_pointsto. iDestruct "Hc" as "[Hc _]".
        iApply ("Hclash" with "Hc").
      + apply pa_range_elim in Hin as (j & Hj & ->).
        iDestruct "Hrel" as "(_ & _ & _ & [[%Hnil Hpre] | Hcells])".
        * rewrite /TsoCtx.rel_pre_cells.
          iDestruct (big_sepL_lookup _ (seq 0 2) j j with "Hpre") as "Hc".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (phys_ledger_at_forget with "Hc") as "Hc". rewrite /phys_pointsto. iDestruct "Hc" as "[Hc _]".
          iApply ("Hclash" with "Hc").
        * rewrite /TsoCtx.rel_cells.
          iDestruct (big_sepL_lookup _ (seq 0 2) j j with "Hcells") as (t) "Hc".
          { rewrite lookup_seq_lt; [reflexivity | lia]. }
          iDestruct (phys_ledger_rpay_forget with "Hc") as "Hc". rewrite /phys_pointsto. iDestruct "Hc" as "[Hc _]".
          iApply ("Hclash" with "Hc").
      + apply elem_of_done_dom in Hin as (p & sl & Hp & Hin).
        iDestruct (big_sepM_lookup _ _ _ _ Hp with "Hdone") as "Hs".
        iDestruct (slot_done_cell_at _ _ _ _ _ _ a Hin with "Hs") as (b' q) "(_ & Hc & _)".
        iDestruct (phys_ledger_at_forget with "Hc") as "Hc". rewrite /phys_pointsto. iDestruct "Hc" as "[Hc _]".
        iApply ("Hclash" with "Hc").
    - apply elem_of_dom in Hdma as [b' Hb'].
      assert (Hf : filter (fun p : Arch.pa * bv 8 => p.1 ∉ lease_hole c pr) dma !! a = Some b')
        by (apply map_lookup_filter_Some_2; [exact Hb' | cbn; exact Hnin]).
      rewrite /dma_own_x /dma_own.
      iDestruct (big_sepM_lookup _ _ _ _ Hf with "Hd") as "Hc".
      iDestruct (phys_ledger_forget with "Hc") as "Hc". rewrite /phys_pointsto. iDestruct "Hc" as "[Hc _]".
      iApply ("Hclash" with "Hc").
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
  Definition pend_todo (pr : vproto) (ca : gmap Z (list (bv 8))) (tk : bool)
      (p : nat) (sl : vslot) : gset nat :=
    if bool_decide (p = vp_nc pr)
    then (if tk then vs_todo sl (dom ca) else vs_all sl)
    else vs_all sl.

  Lemma pend_todo_other (pr : vproto) (ca : gmap Z (list (bv 8))) (tk : bool)
      (p : nat) (sl : vslot) :
    p <> vp_nc pr -> pend_todo pr ca tk p sl = vs_all sl.
  Proof. intro H. rewrite /pend_todo bool_decide_eq_false_2 //. Qed.

  Lemma pend_todo_head (pr : vproto) (ca : gmap Z (list (bv 8))) (tk : bool)
      (sl : vslot) :
    pend_todo pr ca tk (vp_nc pr) sl
    = (if tk then vs_todo sl (dom ca) else vs_all sl).
  Proof. rewrite /pend_todo bool_decide_eq_true_2 //. Qed.

  (* nothing captured: EVERY pending slot owes its whole write *)
  Lemma pend_todo_untaken (pr : vproto) (ca : gmap Z (list (bv 8)))
      (p : nat) (sl : vslot) :
    pend_todo pr ca false p sl = vs_all sl.
  Proof. rewrite /pend_todo. by destruct (bool_decide (p = vp_nc pr)). Qed.

  (* THE WRITETHROUGH DISCIPLINE AT THE PROTOCOL
     ([VirtioModel.virtio_wt_inv] section 6c, in the queue's vocabulary).
     Everything the device is holding belongs to the HEAD request and is
     exactly what that request's capture deposited -- which is both what
     identifies a DRAIN with a sector of the head slot
     ([VirtioQueue.vproto_drain_det]) and what makes a completion find the
     cache empty ([VirtioModel.virtio_req_step_wt_cache]).  With NO head
     request the cache is empty and nothing has been captured, so the next
     publish hands its fresh slot in at the sequential permit's ROOT. *)
  Definition vp_wt (pr : vproto) (ca : gmap Z (list (bv 8))) (tk : bool)
      : Prop :=
    match vp_pend pr !! vp_nc pr with
    | Some sl => (tk = false -> ca = ∅) /\ ca ⊆ vslot_cache sl
    | None => ca = ∅ /\ tk = false
    end.

  (* an idle device satisfies it whatever is queued *)
  Lemma vp_wt_idle (pr : vproto) (ca : gmap Z (list (bv 8))) (tk : bool) :
    ca = ∅ -> tk = false -> vp_wt pr ca tk.
  Proof.
    intros -> ->. rewrite /vp_wt.
    destruct (vp_pend pr !! vp_nc pr) as [sl|];
      [ split; [reflexivity | apply map_empty_subseteq] | by split ].
  Qed.

  Lemma vp_wt_head (pr : vproto) (ca : gmap Z (list (bv 8))) (tk : bool)
      (sl : vslot) :
    vp_pend pr !! vp_nc pr = Some sl -> vp_wt pr ca tk ->
    (tk = false -> ca = ∅) /\ ca ⊆ vslot_cache sl.
  Proof. intros Hsl H. rewrite /vp_wt Hsl in H. exact H. Qed.

  Lemma vp_wt_none (pr : vproto) (ca : gmap Z (list (bv 8))) (tk : bool) :
    vp_pend pr !! vp_nc pr = None -> vp_wt pr ca tk -> ca = ∅ /\ tk = false.
  Proof. intros Hsl H. rewrite /vp_wt Hsl in H. exact H. Qed.

  (* ...and it IS the model's state-only invariant, at the head request's
     sector set -- which is the form the completion's payoff needs. *)
  Lemma vp_wt_virtio_wt_inv (c : virtio_cfg) (p : nat) (pr : vproto)
      (v : virtio_state) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
    slot_pin_ok c p sl pin ->
    vp_pend pr !! vp_nc pr = Some sl ->
    vp_wt pr (v_cache v) (v_taken v) ->
    virtio_wt_inv v (vs_sectors sl).
  Proof.
    intros Hslot Hsl Hwt.
    destruct (vp_wt_head pr (v_cache v) (v_taken v) sl Hsl Hwt) as [Hnil Hsub].
    split; [| exact Hnil].
    rewrite <- (vslot_cache_dom_sectors c p sl pin Hslot).
    by apply subseteq_dom.
  Qed.

  Definition virtio_proto (γ : disk_names) (v : virtio_state) : iProp Σ :=
    (if virtio_live (v_cfg v) then
        ∃ (pr : vproto) (dma : gmap Arch.pa (bv 8)) (t0 t1 lo nr F : nat)
          (hist : list (nat * (nat -> bv 8))) (pm : gmap nat nat),
          disk_cfg γ (v_cfg v) ∗
          (* A6.124: the lease with a HOLE at the avail-index word, whose two
             cells the lease holds at HALF -- the other half, with the stamp
             exposed and the floor beside it, is in the vdisk_lock's payload
             ([DiskInv.disk_res]); see the kit's header above. *)
          dma_own_x dma (lease_hole (v_cfg v) pr) ∗
          half_map (vproto_ctl (v_cfg v) pr) ∗
          ⌜vproto_ctl (v_cfg v) pr ⊆ dma⌝ ∗
          ⌜vproto_ok (v_cfg v) pr (dom dma)⌝ ∗
          ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
          ⌜v_seen v = wrap16 (vp_nc pr)⌝ ∗
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
             the head request's captured sectors, and nothing at all before
             the capture. *)
          ⌜vp_wt pr (v_cache v) (v_taken v)⌝ ∗
          ghost_map_auth (dn_slot γ) 1 (vp_spins pr) ∗
          mono_nat_auth_own (dn_nc γ) 1 (vp_nc pr) ∗
          ghost_var (dn_np γ) (1/2) (vp_np pr) ∗
          (* A6.126 §6: the release window, the reader's ghosts, the positions *)
          used_rel_res (v_cfg v) (vp_nc pr) lo (tf2 t0 t1) hist ∗
          disk_fl γ t0 t1 ∗ disk_nr γ nr ∗ disk_flr γ F ∗
          ghost_map_auth (dn_pos γ) 1 pm ∗
          ⌜forall k q, pm !! k = Some q <-> exists g, hist !! k = Some (q, g)⌝ ∗
          ([∗ list] p ↦ qg ∈ hist, disk_done_pos γ p qg.1) ∗
          ⌜dom (vp_done pr) = set_seq nr (vp_nc pr - nr)⌝ ∗
          ⌜(nr <= vp_nc pr)%nat⌝ ∗
          ⌜forall p q g, hist !! p = Some (q, g) -> (p < nr)%nat -> (q <= F)%nat⌝ ∗
          ([∗ map] p ↦ sl ∈ vp_pend pr,
             slot_pend_res γ (pend_todo pr (v_cache v) (v_taken v) p sl) sl) ∗
          ([∗ map] p ↦ sl ∈ vp_done pr, slot_done_res γ (v_cfg v) dma hist p sl)
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
        ⌜v_cache v = ∅⌝ ∗ ⌜v_taken v = false⌝ ∗
        (* ...and the cache MODE is already declined: the pre-flip
           DRIVER_FEATURES write is the one that decides it, and every write
           after it leaves [vc_dfeat] alone.  Carrying it on this arm too is
           what makes [virtio_proto_writethrough] unconditional. *)
        ⌜virtio_wce (v_cfg v) = false⌝ ∗
        ghost_map_auth (dn_slot γ) 1 (∅ : gmap nat (vslot * gmap Arch.pa (bv 8))) ∗
        mono_nat_auth_own (dn_nc γ) 1 0%nat ∗
        ghost_var (dn_np γ) 1 0%nat ∗
        (* A6.126 §6: the reader's ghosts, whole, at their init values *)
        ghost_var (dn_fl0 γ) 1 0%nat ∗ ghost_var (dn_fl1 γ) 1 0%nat ∗
        ghost_var (dn_nr γ) 1 0%nat ∗ ghost_var (dn_flr γ) 1 0%nat ∗
        ghost_map_auth (dn_pos γ) 1 (∅ : gmap nat nat))%I.

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
    v_cache v = ∅ -> v_taken v = false ->
    virtio_wce (v_cfg v) = false ->
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
    intros Hlive Hsn Hui Hca Htk Hwce.
    iMod (ghost_map_alloc_empty (K:=nat)
            (V:=(vslot * gmap Arch.pa (bv 8))%type)) as (gslot) "Hslot".
    iMod (mono_nat_own_alloc 0) as (gnc) "[Hnc Hlb]".
    iMod (ghost_var_alloc 0%nat) as (gnp) "Hnp".
    iMod (ghost_map_alloc_empty (K:=nat) (V:=dclaim)) as (gclaim) "Hclaim".
    iMod (disk_cfg_alloc (v_cfg v)) as (gcfg) "Hcfg".
    iMod (perm_ghost_alloc gd) as (gperm) "Hperm".
    iMod (ghost_var_alloc 0%nat) as (gfl0) "Hfl0".
    iMod (ghost_var_alloc 0%nat) as (gfl1) "Hfl1".
    iMod (ghost_var_alloc 0%nat) as (gflr) "Hflr".
    iMod (ghost_var_alloc 0%nat) as (gnr) "Hnr".
    iMod (ghost_map_alloc_empty (K:=nat) (V:=nat)) as (gpos) "Hpos".
    iDestruct (disk_cfg_is_split
                 (DiskNames disk_img_name gslot gnc gnp gclaim gcfg gperm gfl0 gfl1 gflr gnr gpos)
                 (v_cfg v) with "[Hcfg]") as "[Hcfg1 Hcfg2]".
    { rewrite /disk_cfg_is. cbn [dn_cfg]. iExact "Hcfg". }
    iModIntro.
    iExists (DiskNames disk_img_name gslot gnc gnp gclaim gcfg gperm gfl0 gfl1 gflr gnr gpos).
    iSplitR; [iPureIntro; reflexivity|].
    iFrame "Hcfg2".
    rewrite /disk_done_lb. cbn [dn_nc dn_claim dn_perm].
    iFrame "Hclaim Hlb Hperm".
    rewrite /virtio_proto.
    cbn [dn_img dn_slot dn_nc dn_np dn_claim dn_cfg dn_perm dn_fl0 dn_fl1 dn_flr dn_nr dn_pos].
    rewrite Hlive.
    iSplitL "Hcfg1"; [iExact "Hcfg1"|].
    iSplitR; [iPureIntro; exact Hsn|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hca|].
    iSplitR; [iPureIntro; exact Htk|].
    iSplitR; [iPureIntro; exact Hwce|].
    iFrame "Hslot Hnc Hnp Hfl0 Hfl1 Hnr Hflr Hpos".
  Qed.

  (* the live protocol, over an ABSTRACT configuration: the whole content of
     [virtio_proto_intro] with the [virtio_init_cfg] noise factored out *)
  Lemma vinit_lease (c : virtio_cfg) :
    avail_idx_dom c ## used_page_pas c ->
    dma_own_x (vinit_dma c) (lease_hole c vproto0) ⊣⊢ phys_map (used_page_rest c).
  Proof.
    intro Hdisj.
    rewrite /dma_own_x /lease_hole /lease_hole_pure /vinit_dma (vproto0_ctl c) avail_idx_bytes_dom.
    assert (Hde : vp_done vproto0 = ∅) by reflexivity. rewrite Hde done_dom_empty.
    assert (Hsub : dom (range_map (avail_idx_pa c) 2 (nth_byte (wrap16 0)))
                   ⊆ avail_idx_dom c ∪ used_idx_dom c ∪ ∅).
    { rewrite range_map_dom. unfold avail_idx_dom. intros x Hx.
      apply elem_of_union_l, elem_of_union_l. exact Hx. }
    rewrite (map_filter_union_in _ _ _ Hsub).
    rewrite (map_filter_hole_ext (range_map (vc_used c) 4096 (fun _ : nat => byte_zero))
               (avail_idx_dom c ∪ used_idx_dom c ∪ ∅) (used_idx_dom c)).
    2:{ intros a Ha. rewrite range_map_dom in Ha. split.
        - intro H. apply elem_of_union in H as [H | H];
            [| exfalso; exact (proj1 (elem_of_empty a) H)].
          apply elem_of_union in H as [H | H]; [| exact H].
          exfalso. exact (proj1 (elem_of_disjoint _ _) Hdisj a H Ha).
        - intro H. apply elem_of_union_l, elem_of_union_r. exact H. }
    rewrite /used_page_rest dma_own_phys_map. reflexivity.
  Qed.

  Lemma virtio_proto_intro_gen (γ : disk_names) (v1 : virtio_state)
      (c : virtio_cfg) (t0 t1 : nat) :
    v_cfg v1 = c ->
    virtio_live c = true ->
    vc_qnum c = Z_to_bv 32 8 ->
    virtio_pages_aligned c ->
    avail_idx_dom c ## used_page_pas c ->
    v_seen v1 = wrap16 0 ->
    v_used_idx v1 = wrap16 0 ->
    virtio_wce c = false ->
    v_cache v1 = ∅ -> v_taken v1 = false ->
    disk_cfg γ c -∗
    ghost_map_auth (dn_slot γ) 1 (∅ : gmap nat (vslot * gmap Arch.pa (bv 8))) -∗
    mono_nat_auth_own (dn_nc γ) 1 0%nat -∗
    ghost_var (dn_np γ) (1/2) 0%nat -∗
    avail_lease_half c 0 -∗
    (* A6.126 §6: the used page MINUS the index word, sealed, and the word's
       two bytes STAMPED (their floor writes; DiskInv holds the floors) *)
    phys_map (used_page_rest c) -∗
    ([∗ list] j ∈ seq 0 2,
       phys_ledger_at (pa_add (used_idx_pa c) j) (DfracOwn 1) byte_zero (tf2 t0 t1 j)) -∗
    disk_fl γ t0 t1 -∗ disk_nr γ 0 -∗ disk_flr γ 0 -∗
    ghost_map_auth (dn_pos γ) 1 (∅ : gmap nat nat) -∗
    virtio_proto γ v1.
  Proof.
    intros Hcfg Hlive Hqnum Hal Hdisj Hseen Hui Hwce Hca Htk.
    iIntros "#Hcfgp Hslot Hnc Hnp Hidx Hpage Hcells Hfl Hnr Hflr Hpos".
    iAssert (dma_own_x (vinit_dma c) (lease_hole c vproto0)) with "[Hpage]" as "Hdma".
    { rewrite (vinit_lease c Hdisj). iExact "Hpage". }
    rewrite /virtio_proto.
    rewrite Hcfg Hlive.
    iExists vproto0, (vinit_dma c), t0, t1, (Nat.max t0 t1), 0%nat, 0%nat, [], ∅.
    rewrite vp_spins_init.
    iEval (rewrite avail_lease_half_eq -(vproto0_ctl c)) in "Hidx".
    iFrame "Hcfgp Hdma Hidx Hslot Hnc Hnp Hfl Hnr Hflr Hpos".
    iSplitR; [iPureIntro; apply vinit_dma_ctl|].
    iSplitR.
    { iPureIntro. rewrite vinit_dma_dom.
      apply vproto_ok_init; [exact Hqnum | exact Hlive | exact Hdisj]. }
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact (vinit_dma_uidx c Hdisj)|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR; [iPureIntro; exact (vp_wt_idle vproto0 (v_cache v1) (v_taken v1) Hca Htk)|].
    iSplitL "Hcells".
    { rewrite /used_rel_res.
      iSplitR; [iPureIntro; exact hist_ok_nil|].
      iSplitR. { iPureIntro. intros k Hk. destruct k as [|k]; cbn [tf2]; lia. }
      iSplitR.
      { iPureIntro. destruct (Nat.max_spec t0 t1) as [[_ Hm] | [_ Hm]]; rewrite Hm.
        - exists 1%nat. split; [lia | reflexivity].
        - exists 0%nat. split; [lia | reflexivity]. }
      iLeft. iSplitR; [done|]. rewrite /TsoCtx.rel_pre_cells.
      iApply (big_sepL_impl with "Hcells"). iIntros "!>" (k j Hkj) "H".
      apply lookup_seq in Hkj as [-> Hj].
      rewrite (nth_byte_wrap16_0 (0 + k)%nat ltac:(lia)). iExact "H". }
    iSplitR.
    { iPureIntro. intros k q. rewrite lookup_empty lookup_nil.
      split; [discriminate | intros [g H]; discriminate]. }
    iSplitR; [by rewrite big_sepL_nil|].
    iSplitR. { iPureIntro. cbn [vp_done vp_nc vproto0]. by rewrite dom_empty_L. }
    iSplitR; [iPureIntro; lia|].
    iSplitR. { iPureIntro. intros p q g H. rewrite lookup_nil in H. discriminate. }
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
      (pd pav pu : Arch.pa) (t0 t1 : nat) :
    virtio_live (v_cfg v0) = false ->
    v_cfg v1 = virtio_init_cfg pd pav pu ->
    v_seen v1 = v_seen v0 -> v_used_idx v1 = v_used_idx v0 ->
    v_cache v1 = v_cache v0 -> v_taken v1 = v_taken v0 ->
    virtio_pages_aligned (virtio_init_cfg pd pav pu) ->
    avail_idx_dom (virtio_init_cfg pd pav pu)
      ## used_page_pas (virtio_init_cfg pd pav pu) ->
    virtio_proto γ v0 -∗
    (* the boot chain's half of the config tracker: it is what recombines
       with the invariant's half into the exclusive fraction the freeze needs,
       and holding it is what made the driver's knowledge of [v_cfg v0]
       deterministic all the way to this point. *)
    disk_cfg_is γ (DfracOwn (1/2)) (v_cfg v0) -∗
    avail_lease_half (virtio_init_cfg pd pav pu) 0 -∗
    phys_map (used_page_rest (virtio_init_cfg pd pav pu)) -∗
    ([∗ list] j ∈ seq 0 2,
       phys_ledger_at (pa_add (used_idx_pa (virtio_init_cfg pd pav pu)) j)
         (DfracOwn 1) byte_zero (tf2 t0 t1 j)) -∗
    |==> virtio_proto γ v1 ∗ disk_pub γ 0 ∗
         disk_cfg γ (virtio_init_cfg pd pav pu) ∗
         disk_fl γ t0 t1 ∗ disk_nr γ 0 ∗ disk_flr γ 0.
  Proof.
    intros Hlive0 Hc1 Hsn Hui Hcae Htke Hal Hdisj. iIntros "Hp Hmine Hidx Hpage Hcells".
    rewrite {1}/virtio_proto.
    rewrite Hlive0.
    iDestruct "Hp" as "(Hcfg & %Hsn0 & %Hui0 & %Hca0 & %Htk0 & %Hwce0 &
                        Hslot & Hnc & Hnp & Hfl0 & Hfl1 & Hnr & Hflr & Hpos)".
    iMod (ghost_var_update t0 with "Hfl0") as "Hfl0".
    iMod (ghost_var_update t1 with "Hfl1") as "Hfl1".
    iEval (rewrite -Qp.half_half) in "Hfl0".
    iDestruct (ghost_var_split with "Hfl0") as "[Hfl0a Hfl0b]".
    iEval (rewrite -Qp.half_half) in "Hfl1".
    iDestruct (ghost_var_split with "Hfl1") as "[Hfl1a Hfl1b]".
    iEval (rewrite -Qp.half_half) in "Hnr".
    iDestruct (ghost_var_split with "Hnr") as "[Hnra Hnrb]".
    iEval (rewrite -Qp.half_half) in "Hflr".
    iDestruct (ghost_var_split with "Hflr") as "[Hflra Hflrb]".
    iDestruct (disk_cfg_is_join with "Hcfg Hmine") as "Hcfg".
    iMod (disk_cfg_set γ (v_cfg v0) (virtio_init_cfg pd pav pu) with "Hcfg")
      as "#Hcfg".
    iEval (rewrite -Qp.half_half) in "Hnp".
    iDestruct (ghost_var_split with "Hnp") as "[Hnp1 Hnp2]".
    iModIntro. rewrite /disk_pub /disk_fl /disk_nr /disk_flr.
    iFrame "Hnp2 Hcfg Hfl0b Hfl1b Hnrb Hflrb".
    assert (Hs1 : v_seen v1 = wrap16 0%nat)
      by (rewrite Hsn Hsn0; exact zero16_wrap16).
    assert (Hu1 : v_used_idx v1 = wrap16 0%nat)
      by (rewrite Hui Hui0; exact zero16_wrap16).
    assert (Hca1 : v_cache v1 = ∅) by (rewrite Hcae; exact Hca0).
    assert (Htk1 : v_taken v1 = false) by (rewrite Htke; exact Htk0).
    iApply (virtio_proto_intro_gen γ v1 (virtio_init_cfg pd pav pu) t0 t1
              Hc1 (virtio_init_cfg_live pd pav pu) eq_refl Hal Hdisj Hs1 Hu1
              (virtio_init_cfg_wce pd pav pu) Hca1 Htk1
              with "Hcfg Hslot Hnc Hnp1 Hidx Hpage Hcells [Hfl0a Hfl1a] Hnra Hflra Hpos").
    rewrite /disk_fl. iFrame "Hfl0a Hfl1a".
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
    v_cache v' = ∅ -> v_taken v' = false ->
    (* THE ONE NEW OBLIGATION ON A PRE-FLIP WRITE (async-disk.md §2): the
       configuration it programs must still decline the cache.  Thirteen of
       the fourteen writes do not touch [vc_dfeat] at all; the DRIVER_FEATURES
       write is the one that decides it, and xv6's negotiation computes to
       zero ([VirtioModel.virtio_xv6_features]). *)
    virtio_wce c' = false ->
    virtio_proto γ v -∗ disk_cfg_is γ (DfracOwn (1/2)) (v_cfg v) ==∗
    virtio_proto γ v' ∗ disk_cfg_is γ (DfracOwn (1/2)) c'.
  Proof.
    intros Hlive0 Hlive1 Hc1 Hsn Hui Hca Htk Hwce. iIntros "Hp Hmine".
    rewrite {1}/virtio_proto.
    rewrite Hlive0.
    iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & Hslot & Hnc & Hnp & Hg)".
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
    iSplitR; [iPureIntro; exact Hwce|].
    iFrame "Hslot Hnc Hnp Hg".
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
    - iDestruct "Hp" as (pr dma t0 t1 lo nr F hist pm) "(#Hcfg & _)".
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
     /\ v_cache v = ∅ /\ v_taken v = false⌝.
  Proof.
    iIntros (Hlive) "Hp Hmine". rewrite /virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hl.
    - iDestruct "Hp" as (pr dma t0 t1 lo nr F hist pm) "(#Hcfg & _)".
      iDestruct (disk_cfg_is_agree with "Hcfg Hmine") as %Hc.
      rewrite Hc Hlive in Hl. discriminate.
    - iDestruct "Hp" as "(Hcfg & %Hsn & %Hui & %Hca & %Htk & %Hwce & _)".
      iDestruct (disk_cfg_is_agree with "Hcfg Hmine") as %Hc.
      iPureIntro. split_and!;
        [exact Hc | exact Hsn | exact Hui | exact Hca | exact Htk].
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
    v_cfg v' = v_cfg v -> v_seen v' = v_seen v ->
    v_used_idx v' = v_used_idx v ->
    v_cache v' = v_cache v -> v_taken v' = v_taken v ->
    virtio_proto γ v -∗ virtio_proto γ v'.
  Proof.
    intros Hc Hs Hu Hca Htk.
    rewrite /virtio_proto Hc Hs Hu Hca Htk. iIntros "$".
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
    - iDestruct "Hp" as (pr dma t0 t1 lo nr F hist pm)
        "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Hwce & _)". done.
    - iDestruct "Hp" as "(_ & _ & _ & _ & _ & %Hwce & _)". done.
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
    iDestruct "Hp" as (pr dma t0 t1 lo nr F hist pm)
      "(Hcfg & Hdma & Hah & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hwce & %Hwt &
        Hslot & Hnc & Hnp & Hrel & Hfl & Hnr & Hflr & Hpos & %Hpm & #Hfrag & %Hdd & %Hnrnc & %HF &
        Hpend & Hdone)".
    iDestruct (lease_agree_full _ _ _ _ _ _ _ _ Hctl Hridx with "Hm Hdma Hah Hrel Hdone") as %Hsub.
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
      ∃ (kq : nat * gname) (wr : disk_wr) (old : gmap Arch.pa (bv 8))
        (nc lo : nat) (tf : nat -> nat) (hist : list (nat * (nat -> bv 8))),
        (* THE COMPLETION MOVES NO DISK BYTE (sector-atomic-disk.md): every
           sector of an OUT request's data landed at its own earlier step, so
           the index here is [None] in BOTH directions and the cell is at the
           sequential permit's LEAF -- nothing left to land. *)
        ⌜v_disk v' = wr_apply None (v_disk v)⌝ ∗
        (* A6.48 ruling 4, THE INSIDE-OUT, and A6.126 §6, THE RELEASE WINDOW.
           The completion APPENDS the write set to the era log; the ledger
           gate that does it ([TsoCtx.ledger_store_rel_map_ok]) moves
           [gen_heap_interp] and [tso_interp_at] together, so the append
           belongs to the one caller that holds both -- [WpUart]'s disk loop.
           The protocol hands OUT the write set's old bytes in two parts --
           the slot's writable bytes and used element, sealed ([old]), and
           the index word as the release window (pre-mint or minted, with
           its history) -- and takes back through the wand the slot's bytes
           STAMPED at the append's position [q] and the window re-minted with
           the history extended.  [gen_heap_interp m] goes in for the
           lease's pure fact and comes straight back UNTOUCHED. *)
        ⌜dom old = dom w ∖ dom (snap_of (used_idx_pa (v_cfg v)) 2 (wrap16 nc))⌝ ∗
        ⌜snap_of (used_idx_pa (v_cfg v)) 2 (wrap16 (S nc)) ⊆ w⌝ ∗
        ⌜hist_ok hist nc⌝ ∗
        ⌜forall k, (k < 2)%nat -> (tf k <= lo)%nat⌝ ∗
        ⌜exists k, (k < 2)%nat /\ lo = tf k⌝ ∗
        gen_heap_interp m ∗
        ([∗ map] a ↦ b ∈ old, phys_ledger a (DfracOwn 1) b) ∗
        ((⌜hist = []⌝ ∗ TsoCtx.rel_pre_cells (used_idx_pa (v_cfg v)) 2 tf (nth_byte (wrap16 0)))
         ∨ TsoCtx.rel_cells (used_idx_pa (v_cfg v)) 2 (DfracOwn 1) disk_agent lo tf
             (nth_byte (wrap16 0)) (nth_byte (wrap16 nc)) hist) ∗
        perm_pend (dn_perm γ) kq wr ∅ ∗
        (∀ q : nat,
           ⌜forall k q' g, hist !! k = Some (q', g) -> (q' < q)%nat⌝ -∗
           perm_done (dn_perm γ) kq wr -∗
           ([∗ map] a ↦ b ∈ w ∖ snap_of (used_idx_pa (v_cfg v)) 2 (wrap16 (S nc)),
              phys_ledger_at a (DfracOwn 1) b q) -∗
           TsoCtx.rel_cells (used_idx_pa (v_cfg v)) 2 (DfracOwn 1) disk_agent lo tf
             (nth_byte (wrap16 0)) (nth_byte (wrap16 (S nc)))
             (hist ++ [(q, nth_byte (wrap16 (S nc)))]) ==∗
           disk_img_auth (dn_img γ) (v_disk v') ∗ virtio_proto γ v').
  Proof.
    iIntros (Hview Hstep) "Hm Hauth Hp".
    iDestruct "Hauth" as (dmap) "[Hauth %Hdv]".
    rewrite {1}/virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { exfalso. rewrite (virtio_req_step_not_live v mv Hlive) in Hstep.
      discriminate. }
    iDestruct "Hp" as (pr dma t0 t1 lo nr F hist pm)
      "(#Hcfg & Hdma & Hah & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hwce & %Hwt &
        Hslot & Hnc & Hnp & Hrel & Hfl & Hnr & Hflr & Hpos & %Hpm & #Hfrag & %Hdd & %Hnrnc & %HF &
        Hpend & Hdone)".
    iDestruct (lease_agree_full _ _ _ _ _ _ _ _ Hctl Hridx with "Hm Hdma Hah Hrel Hdone") as %Hsub.
    assert (Hctlm : vproto_ctl (v_cfg v) pr ⊆ m)
      by (etransitivity; [exact Hctl | exact Hsub]).
    assert (Hvctl : mem_view (vproto_ctl (v_cfg v) pr) mv)
      by exact (mem_view_subseteq _ m mv Hctlm Hview).
    destruct (vproto_step_det (v_cfg v) pr (dom dma) v mv v' w
                Hok eq_refl Hseen Hvctl Hstep)
      as (sl & pin & Hsl & Hpin & Hlt & Hslotok & Hvpin & Hsdone & Hv1 & Hw1).
    subst v' w. rewrite Hui.
    (* THE WRITETHROUGH PAYOFF (async-disk.md §2).  xv6 declined the cache,
       so the completion gate demands that no sector of this request is still
       cached -- and the protocol's own [vp_wt] says nothing ELSE is -- hence
       the device is holding NOTHING at the instant it reports the request
       done.  Every byte it acknowledged is on the durable medium. *)
    pose proof (spo_req _ _ _ _ Hslotok mv Hvpin) as Hreq.
    rewrite <- Hseen in Hreq.
    assert (Hwtinv : virtio_wt_inv v (vreq_sectors (vs_req sl)))
      by exact (vp_wt_virtio_wt_inv (v_cfg v) (vp_nc pr) pr v sl pin
                  Hslotok Hsl Hwt).
    assert (Hcae : v_cache v = ∅)
      by exact (virtio_req_step_wt_cache v mv (vs_req sl) _ _
                  Hwce Hreq Hwtinv Hstep).
    (* ...so a READ's data collapses from the cache-overlaid image back to
       the DURABLE one, exactly as before the cache existed. *)
    rewrite (vslot_writes_cache_view (v_cfg v) (wrap16 (vp_nc pr)) v sl Hcae).
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
    (* ...so the request's channel entry has nothing left to land: its cell
       is at the LEAF, the completion's own identity permit.  For an OUT
       request because the gate demanded [v_taken] and the cache is empty; for
       a READ because it owes nothing per-sector to begin with. *)
    assert (Htd : pend_todo pr (v_cache v) (v_taken v) (vp_nc pr) sl = ∅).
    { rewrite pend_todo_head Hcae dom_empty_L.
      destruct (v_taken v) eqn:Htk; [ apply vs_todo_empty |].
      apply vs_all_read.
      destruct (vs_is_out sl) eqn:Hout; [| reflexivity ]. exfalso.
      assert (Hout2 : bv_unsigned (vr_type (vs_req sl)) = virtio_blk_t_out)
        by (unfold vs_is_out in Hout; by apply Z.eqb_eq).
      destruct (virtio_complete_ok_out v (vs_req sl) Hout2 Hsdone) as [Ht _].
      rewrite Htk in Ht. discriminate. }
    rewrite Htd.
    iDestruct "Hslres" as (bs)
      "(%Hbslen & %Hbspin & %Hbstorn & Hbs & Hpend0)".
    rewrite vs_kept_nil in Hbstorn.
    assert (Hout' : bs = vs_data sl).
    { destruct (vs_is_out sl) eqn:Hout; [| exact (Hbspin eq_refl) ].
      pose proof (vslot_data_len (v_cfg v) (vp_nc pr) sl pin Hslotok Hout) as Hdl.
      apply (vs_torn_full sl (vs_all sl) bs Hbslen Hdl); [| exact Hbstorn ].
      intros i Hi. apply vs_all_elem.
      rewrite <- (vslot_nsectors_pin (v_cfg v) (vp_nc pr) sl pin Hslotok).
      rewrite (vslot_nsectors_out sl Hout). exact Hi. }
    iDestruct (disk_bytes_read γ dmap (v_disk v) (vs_sector_off sl) bs Hdv
                 with "Hauth Hbs") as %Hrd.
    assert (Hin' : vs_is_out sl = false ->
              disk_read (v_disk v) (vs_sector_off sl) (vs_len sl) = bs)
      by (intros _; rewrite <- Hbslen; exact Hrd).
    assert (Hdv' : disk_view dmap (v_disk (vslot_post v sl)))
      by (rewrite vslot_post_disk; exact Hdv).
    (* the byte lease and the counters *)
    (* THE PLAIN PART: the slot's writable bytes and its used element leave
       the sealed lease (the hole grows by them); the index word is behind
       its own hole already. *)
    set (Sw := slot_done_dom (v_cfg v) (vp_nc pr) sl).
    assert (HwD' : dom (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl)
                   = Sw ∪ used_idx_dom (v_cfg v))
      by exact (vslot_writes_dom_eq (v_cfg v) (vp_nc pr) (v_disk v) sl Hqnum).
    assert (HSidx : Sw ## used_idx_dom (v_cfg v))
      by exact (slot_done_dom_idx_disj _ _ _ Hwrpage).
    assert (HSdma : Sw ⊆ dom dma).
    { apply union_least.
      - etransitivity; [apply slot_fp_wr | exact (vpo_fp_D _ _ _ Hok _ sl pin Hs Hpin)].
      - intros x Hx. apply (vpo_used_D _ _ _ Hok). apply (elem_dom_in_page (v_cfg v) (vp_nc pr)). exact Hx. }
    assert (Hdnone : vp_done pr !! vp_nc pr = None).
    { apply not_elem_of_dom. intro Hc.
      pose proof (vpo_done_lt _ _ _ Hok _ Hc). lia. }
    (* every OTHER done slot: writable bytes apart, both off the used page's
       control words, distinct used elements *)
    assert (Hdonek : forall k x, vp_done pr !! k = Some x ->
              slot_wr sl ## slot_wr x /\ slot_wr x ## used_page_pas (v_cfg v)
              /\ Z.of_nat (vp_nc pr) `mod` 8 ≠ Z.of_nat k `mod` 8).
    { intros k x Hk.
      pose proof (vproto_done_slot (v_cfg v) pr (dom dma) k x Hok Hk) as Hks.
      assert (Hkpin : exists pinq, vp_pin pr !! k = Some pinq).
      { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
        apply elem_of_dom. exists x. exact Hks. }
      destruct Hkpin as [pinq Hpinq].
      assert (Hkne : k ≠ vp_nc pr).
      { intro Hc. rewrite Hc in Hk. rewrite Hk in Hdnone. discriminate. }
      pose proof (vpo_fp_disj _ _ _ Hok k (vp_nc pr) x sl pinq pin
                    Hkne Hks Hpinq Hs Hpin) as Hfpd.
      pose proof (vpo_standing _ _ _ Hok k x pinq Hks Hpinq) as Hstq.
      split_and!.
      - apply (gset_disj_mono (slot_wr sl) (slot_fp sl pin) (slot_wr x) (slot_fp x pinq));
          [apply slot_fp_wr | apply slot_fp_wr | apply gset_disj_sym; exact Hfpd].
      - apply (gset_disj_mono (slot_wr x) (slot_fp x pinq) (used_page_pas (v_cfg v))
                 (avail_idx_dom (v_cfg v) ∪ used_page_pas (v_cfg v)));
          [apply slot_fp_wr | apply union_subseteq_r | exact Hstq].
      - exact (vproto_mod8_ne (v_cfg v) pr (dom dma) (vp_nc pr) k sl x pin pinq
                 Hok (fun e => Hkne (eq_sym e)) Hs Hpin Hks Hpinq). }
    assert (HShole : Sw ## lease_hole (v_cfg v) pr).
    { unfold lease_hole, lease_hole_pure.
      apply gset_disj_union_r; [apply gset_disj_union_r |].
      - apply (gset_disj_sub_l _ (dom (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl)));
          [rewrite HwD'; apply union_subseteq_l | exact Hwctl].
      - exact HSidx.
      - apply elem_of_disjoint. intros a HaS Had.
        apply elem_of_done_dom in Had as (k & x & Hk & Hak).
        destruct (Hdonek k x Hk) as (Hww & Hwk & Hmod).
        exact (proj1 (elem_of_disjoint _ _)
                 (slot_done_dom_disj (v_cfg v) (vp_nc pr) k sl x Hww Hwrpage Hwk Hmod)
                 a HaS Hak). }
    iDestruct (dma_own_x_take Sw dma _ HSdma HShole with "Hdma")
      as (old) "(%Hdomold & %Holdsub & Hold & Hdma)".
    assert (Hle : (vp_nc pr <= S (vp_nc pr))%nat) by lia.
    iMod (mono_nat_own_update (S (vp_nc pr)) Hle with "Hnc") as "[Hnc _]".
    (* the frames: every OTHER done record survives -- nothing of its done
       footprint is written, and its history entry is below the append *)
    assert (Hmono : forall k x, vp_done pr !! k = Some x ->
              forall a, a ∈ slot_done_dom (v_cfg v) k x ->
                (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl ∪ dma) !! a
                = dma !! a).
    { intros k x Hk a Ha. apply lookup_union_r.
      destruct (Hdonek k x Hk) as (Hww & Hwk & Hmod).
      exact (vslot_writes_none_done (v_cfg v) (v_disk v) sl x (vp_nc pr) k a
               Hqnum Hwrpage Hww Hwk Hmod Ha). }
    (* rebuild, AS THE ACCESSOR: the completing slot's pending token goes
       out, and the caller owes the spent one back at the same key. *)
    iDestruct "Hrel" as "(%Hho & %Htf & %Hlo & Hcells)".
    iModIntro. iExists (vs_perm sl), (vs_wr sl), old, (vp_nc pr), lo, (tf2 t0 t1), hist.
    iSplitR; [iPureIntro; apply vslot_post_wr|].
    iSplitR.
    { iPureIntro. rewrite Hdomold HwD' dom_snap_of footprint_idx.
      rewrite difference_union_distr_l_L difference_diag_L
        (difference_disjoint_L _ _ HSidx) right_id_L. reflexivity. }
    iSplitR.
    { iPureIntro.
      apply (snap_of_sub (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl)
               (used_idx_pa (v_cfg v)) 2 (wrap16 (S (vp_nc pr)))).
      intros j Hj.
      rewrite (vslot_writes_idx (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl j
                 Hqnum ltac:(lia) Hwrpage).
      rewrite <- wrap16_S. reflexivity. }
    iSplitR; [iPureIntro; exact Hho|].
    iSplitR; [iPureIntro; exact Htf|].
    iSplitR; [iPureIntro; exact Hlo|].
    iFrame "Hm Hold Hcells".
    iFrame "Hpend0". iIntros (q) "%Hqgt Hdone0 Hnew Hrel".
    (* the positions ghost: this completion's entry, persisted *)
    assert (Hpmnone : pm !! vp_nc pr = None).
    { destruct (pm !! vp_nc pr) as [q0|] eqn:Hq0; [| reflexivity]. exfalso.
      apply Hpm in Hq0 as [g Hg]. apply lookup_lt_Some in Hg.
      destruct Hho as [Hlen _]. lia. }
    iMod (ghost_map_insert_persist (vp_nc pr) q Hpmnone with "Hpos") as "[Hpos #Hposnc]".
    iModIntro.
    iAssert (dma_own_x (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl ∪ dma)
               (lease_hole (v_cfg v) (vproto_step_state pr sl)))
      with "[Hdma]" as "Hdma".
    { rewrite {2}/lease_hole (lease_hole_step (v_cfg v) pr sl Hdnone).
      iApply (dma_own_x_extend with "Hdma").
      rewrite HwD'. unfold lease_hole, lease_hole_pure. apply union_least.
      - apply union_subseteq_r.
      - intros x Hx. apply elem_of_union_l, elem_of_union_l, elem_of_union_r. exact Hx. }
    iSplitL "Hauth".
    { iExists dmap. iFrame "Hauth". iPureIntro. exact Hdv'. }
    rewrite /virtio_proto vslot_post_cfg vslot_post_cache vslot_post_taken
            Hlive.
    iExists (vproto_step_state pr sl),
      (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl ∪ dma),
      t0, t1, lo, nr, F, (hist ++ [(q, nth_byte (wrap16 (S (vp_nc pr))))])%list,
      (<[vp_nc pr := q]> pm).
    rewrite (vp_spins_step pr sl Hsl) vps_nc vps_np vps_pend vps_done.
    iEval (rewrite -(vproto_step_ctl (v_cfg v) pr sl)) in "Hah".
    iFrame "Hcfg Hdma Hah Hslot Hnc Hnp Hfl Hnr Hflr Hpos".
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
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR;
      [ iPureIntro;
        exact (vp_wt_idle (vproto_step_state pr sl) (v_cache v) false
                 Hcae eq_refl) |].
    (* the pending map lost [nc] -- and the cache is empty and untaken again,
       so every slot still pending owes its whole write *)
    (* the release window, with the history extended *)
    iSplitL "Hrel".
    { rewrite /used_rel_res.
      iSplitR; [iPureIntro; exact (hist_ok_app hist (vp_nc pr) q Hho Hqgt)|].
      iSplitR; [iPureIntro; exact Htf|].
      iSplitR; [iPureIntro; exact Hlo|].
      iRight. iExact "Hrel". }
    (* the positions map: one more entry *)
    iSplitR.
    { iPureIntro. intros k q0. destruct Hho as [Hlen _]. split.
      - intro Hk. destruct (decide (k = vp_nc pr)) as [-> | Hne].
        + rewrite lookup_insert in Hk. injection Hk as <-.
          exists (nth_byte (wrap16 (S (vp_nc pr)))).
          rewrite lookup_app_r; [| lia]. rewrite Hlen Nat.sub_diag. reflexivity.
        + rewrite lookup_insert_ne in Hk; [| intro Heq; exact (Hne (eq_sym Heq))].
          apply Hpm in Hk as [g Hg]. exists g. apply lookup_app_l_Some. exact Hg.
      - intros [g Hg]. apply lookup_app_Some in Hg as [Hg | [Hge Hg]].
        + assert (Hne : k ≠ vp_nc pr)
            by (intro Hc; subst k; apply lookup_lt_Some in Hg; lia).
          rewrite lookup_insert_ne; [| intro Heq; exact (Hne (eq_sym Heq))]. apply Hpm. by exists g.
        + destruct (k - length hist)%nat as [|d] eqn:Hd; cbn in Hg; [| discriminate].
          injection Hg as Hq _. subst q0.
          assert (Hk : k = vp_nc pr) by lia. subst k. apply lookup_insert. }
    (* the fragments: one more, this completion's *)
    iSplitR.
    { rewrite big_sepL_app big_sepL_singleton. iFrame "Hfrag".
      destruct Hho as [Hlen _]. rewrite Nat.add_0_r Hlen. cbn [fst]. iExact "Hposnc". }
    (* the done set: one more position at the top *)
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdd.
      replace (S (vp_nc pr) - nr)%nat with (S (vp_nc pr - nr)) by lia.
      rewrite set_seq_S_end_union_L. f_equal. f_equal. lia. }
    iSplitR; [iPureIntro; lia|].
    iSplitR.
    { iPureIntro. intros p q0 g Hp Hplt.
      apply lookup_app_Some in Hp as [Hp | [Hge Hp]]; [exact (HF p q0 g Hp Hplt) |].
      destruct Hho as [Hlen _]. lia. }
    assert (Hpmono : forall k x, delete (vp_nc pr) (vp_pend pr) !! k = Some x ->
              slot_pend_res γ (pend_todo pr (v_cache v) (v_taken v) k x) x
              ⊢ slot_pend_res γ
                  (pend_todo (vproto_step_state pr sl) (v_cache v) false k x) x).
    { intros k x Hk. apply bi.wand_entails.
      apply lookup_delete_Some in Hk as [Hne _].
      rewrite (pend_todo_other pr (v_cache v) (v_taken v) k x
                 (fun e => Hne (eq_sym e)))
              (pend_todo_untaken (vproto_step_state pr sl) (v_cache v) k x).
      iIntros "$". }
    iSplitL "Hpend".
    { iApply (big_sepM_mono _ _ _ Hpmono). iExact "Hpend". }
    rewrite (big_sepM_insert _ (vp_done pr) (vp_nc pr) sl Hdnone).
    iSplitL "Hbs Hdone0 Hnew".
    { iExists bs, q. rewrite /slot_perms_done. iFrame "Hbs Hdone0".
      iSplitR; [iPureIntro; exact Hbslen|].
      iSplitR; [iPureIntro; exact Hout'|].
      iSplitR.
      { iPureIntro. apply read_bytes_of_list. intros j Hj.
        assert (Hj2 : (j < 4)%nat) by lia.
        apply lookup_union_Some_l.
        rewrite <- (used_elem_at_wrap (v_cfg v) (vp_nc pr)).
        exact (vslot_writes_elem (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl j
                 Hqnum Hj2 Hwrpage). }
      iSplitR.
      { iPureIntro. apply read_bytes_of_list. intros j Hj.
        assert (Hj2 : (j < 4)%nat) by lia.
        apply lookup_union_Some_l.
        rewrite <- (used_elem_at_wrap (v_cfg v) (vp_nc pr)).
        exact (vslot_writes_len (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl j
                 Hqnum Hj2 Hwrpage). }
      iSplitR.
      { iPureIntro. apply lookup_union_Some_l.
        apply vslot_writes_status. exact (spo_stat _ _ _ _ Hslotok). }
      iSplitR.
      { iPureIntro. intro Hin. apply read_byte_list_intro; [exact Hbslen|].
        intros j b Hj. apply lookup_union_Some_l.
        apply (vslot_writes_buf (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl j b Hin).
        rewrite (Hin' Hin). exact Hj. }
      iSplitR.
      { iPureIntro. exists (nth_byte (wrap16 (S (vp_nc pr)))). destruct Hho as [Hlen _].
        rewrite lookup_app_r; [| lia]. rewrite Hlen Nat.sub_diag. reflexivity. }
      rewrite (vslot_writes_split (v_cfg v) (vp_nc pr) (v_disk v) sl Hqnum Hwrpage
                 (spo_stat _ _ _ _ Hslotok)).
      rewrite (slot_done_cells_of_map (v_cfg v) (vp_nc pr) sl _ q
                 (spo_stat _ _ _ _ Hslotok) Hwrpage).
      destruct (vs_is_out sl) eqn:Hoo.
      - rewrite /slot_done_cells Hoo. iExact "Hnew".
      - iEval (rewrite (Hin' ltac:(first [exact Hoo | reflexivity]))) in "Hnew". iExact "Hnew". }
    assert (Hmono' : forall k x, vp_done pr !! k = Some x ->
              slot_done_res γ (v_cfg v) dma hist k x
              ⊢ slot_done_res γ (v_cfg v)
                  (vslot_writes (v_cfg v) (wrap16 (vp_nc pr)) (v_disk v) sl ∪ dma)
                  (hist ++ [(q, nth_byte (wrap16 (S (vp_nc pr))))]) k x).
    { intros k x Hk. apply bi.wand_entails.
      apply slot_done_res_mono; [exact (Hmono k x Hk) |].
      apply lookup_app_l. destruct Hho as [Hlen _]. rewrite Hlen.
      apply (vpo_done_lt _ _ _ Hok). apply elem_of_dom. by exists x. }
    iApply (big_sepM_mono _ _ _ Hmono'). iExact "Hdone".
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
  Lemma virtio_proto_capture_step (γ : disk_names) (v : virtio_state)
      (m : gmap Arch.pa (bv 8)) (mv : vmem) (v' : virtio_state) :
    mem_view m mv ->
    virtio_capture_step v mv = Some v' ->
    gen_heap_interp m -∗ virtio_proto γ v -∗
      gen_heap_interp m ∗ virtio_proto γ v'.
  Proof.
    iIntros (Hview Hstep) "Hm Hp".
    rewrite {1}/virtio_proto.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { exfalso. rewrite (virtio_capture_step_not_live v mv Hlive) in Hstep.
      discriminate. }
    iDestruct "Hp" as (pr dma t0 t1 lo nr F hist pm)
      "(#Hcfg & Hdma & Hah & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hwce & %Hwt &
        Hslot & Hnc & Hnp & Hrel & Hfl & Hnr & Hflr & Hpos & %Hpm & #Hfrag & %Hdd & %Hnrnc & %HF &
        Hpend & Hdone)".
    iDestruct (lease_agree_full _ _ _ _ _ _ _ _ Hctl Hridx with "Hm Hdma Hah Hrel Hdone") as %Hsub.
    assert (Hctlm : vproto_ctl (v_cfg v) pr ⊆ m)
      by (etransitivity; [exact Hctl | exact Hsub]).
    assert (Hvctl : mem_view (vproto_ctl (v_cfg v) pr) mv)
      by exact (mem_view_subseteq _ m mv Hctlm Hview).
    destruct (vproto_capture_det (v_cfg v) pr (dom dma) v mv v'
                Hok eq_refl Hseen Hvctl Hstep)
      as (sl & pin & Hsl & Hpin & Hlt & Hslotok & Hout & Htk & Hv1).
    (* the cache was EMPTY: the head request had not been taken *)
    destruct (vp_wt_head pr (v_cache v) (v_taken v) sl Hsl Hwt) as [Hnil _].
    pose proof (Hnil Htk) as Hcae.
    assert (Hce : vslot_cache sl ∪ v_cache v = vslot_cache sl)
      by (rewrite Hcae; apply map_union_empty).
    (* the owed sets are the same before and after *)
    assert (Hpmono : forall k x, vp_pend pr !! k = Some x ->
              slot_pend_res γ (pend_todo pr (v_cache v) (v_taken v) k x) x
              ⊢ slot_pend_res γ (pend_todo pr (vslot_cache sl) true k x) x).
    { intros k x Hk. apply bi.wand_entails.
      assert (Hsrc : pend_todo pr (v_cache v) (v_taken v) k x = vs_all x)
        by (rewrite Htk; apply pend_todo_untaken).
      assert (Htgt : pend_todo pr (vslot_cache sl) true k x = vs_all x).
      { destruct (decide (k = vp_nc pr)) as [Hkk|Hne].
        - rewrite Hkk in Hk. rewrite Hk in Hsl. injection Hsl as Hxs.
          rewrite Hkk. rewrite <- Hxs. rewrite pend_todo_head.
          apply vs_todo_full.
        - apply (pend_todo_other pr (vslot_cache sl) true k x Hne). }
      rewrite Hsrc Htgt. iIntros "$". }
    iFrame "Hm".
    rewrite /virtio_proto Hv1.
    cbn [v_cfg v_isr v_seen v_used_idx v_disk v_cache v_taken].
    rewrite Hlive Hce.
    iExists pr, dma, t0, t1, lo, nr, F, hist, pm.
    iFrame "Hcfg Hdma Hah Hslot Hnc Hnp Hrel Hfl Hnr Hflr Hpos Hfrag Hdone".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact Hok|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR.
    { iPureIntro. rewrite /vp_wt Hsl.
      split; [discriminate | reflexivity]. }
    iSplitR; [iPureIntro; exact Hpm|].
    iSplitR; [iPureIntro; exact Hdd|].
    iSplitR; [iPureIntro; exact Hnrnc|].
    iSplitR; [iPureIntro; exact HF|].
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
    iDestruct "Hp" as (pr dma t0 t1 lo nr F hist pm)
      "(#Hcfg & Hdma & Hah & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hwce & %Hwt &
        Hslot & Hnc & Hnp & Hrel & Hfl & Hnr & Hflr & Hpos & %Hpm & #Hfrag & %Hdd & %Hnrnc & %HF &
        Hpend & Hdone)".
    (* something is cached, so there IS a head request *)
    pose proof (virtio_drain_step_enabled v s v' Hstep) as Hsin.
    assert (Hhead : exists sl, vp_pend pr !! vp_nc pr = Some sl).
    { destruct (vp_pend pr !! vp_nc pr) as [sl|] eqn:Hp; [by exists sl|].
      exfalso. destruct (vp_wt_none pr (v_cache v) (v_taken v) Hp Hwt)
        as [Hca _].
      rewrite Hca dom_empty_L in Hsin. by apply elem_of_empty in Hsin. }
    destruct Hhead as [sl Hsl].
    assert (Hlt : (vp_nc pr < vp_np pr)%nat).
    { assert (Hin : vp_nc pr ∈ dom (vp_pend pr))
        by (apply elem_of_dom; by exists sl).
      rewrite (vpo_pend_dom _ _ _ Hok) in Hin.
      apply elem_of_set_seq in Hin. lia. }
    destruct (vproto_head_slot (v_cfg v) pr (dom dma) Hok Hlt)
      as (sl0 & pin & Hsl0 & Hpin & Hslotok).
    rewrite Hsl in Hsl0. injection Hsl0 as Hsl0.
    rewrite <- Hsl0 in Hslotok. clear Hsl0.
    (* the writethrough row identifies the drained key with a sector index *)
    destruct (vp_wt_head pr (v_cache v) (v_taken v) sl Hsl Hwt) as [Hnil Hcsub].
    assert (Hdom : dom (v_cache v) ⊆ vs_sectors sl).
    { rewrite <- (vslot_cache_dom_sectors (v_cfg v) (vp_nc pr) sl pin Hslotok).
      by apply subseteq_dom. }
    destruct (vproto_drain_det (v_cfg v) (vp_nc pr) sl pin v s v'
                Hslotok Hdom Hcsub Hstep)
      as (i & Hi & Hskey & Hlk & Hv1).
    (* ...and the head has been TAKEN: something is cached *)
    assert (Htk : v_taken v = true).
    { destruct (v_taken v) eqn:Ht; [reflexivity|]. exfalso.
      rewrite (Hnil eq_refl) lookup_empty in Hlk. discriminate. }
    iDestruct (big_sepM_delete _ (vp_pend pr) (vp_nc pr) sl Hsl with "Hpend")
      as "[Hslres Hpend]".
    (* the head slot's owed set, spelled out -- LOCALLY, so that the other
       slots' resources keep naming [v_taken v] and ride through by frame *)
    assert (Hhtd0 : pend_todo pr (v_cache v) (v_taken v) (vp_nc pr) sl
                    = vs_todo sl (dom (v_cache v)))
      by (rewrite pend_todo_head Htk; reflexivity).
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
    assert (Htorn' : vs_torn sl ({[ i ]} ∪ vs_kept sl (vs_todo sl (dom (v_cache v))))
                       bs').
    { unfold bs'.
      apply (vs_torn_sector sl (v_disk v)
               (vs_kept sl (vs_todo sl (dom (v_cache v)))) i Hout Hdl).
      rewrite Hrd. exact Hbstorn. }
    (* the other pending slots owe their whole write either way *)
    assert (Hpmono : forall k x, delete (vp_nc pr) (vp_pend pr) !! k = Some x ->
              slot_pend_res γ (pend_todo pr (v_cache v) (v_taken v) k x) x
              ⊢ slot_pend_res γ
                  (pend_todo pr (delete s (v_cache v)) (v_taken v) k x) x).
    { intros k x Hk. apply bi.wand_entails.
      apply lookup_delete_Some in Hk as [Hne _].
      rewrite (pend_todo_other pr (v_cache v) (v_taken v) k x
                 (fun e => Hne (eq_sym e)))
              (pend_todo_other pr (delete s (v_cache v)) (v_taken v) k x
                 (fun e => Hne (eq_sym e))). iIntros "$". }
    iModIntro.
    iExists (vs_perm sl), (vs_wr sl), i, (vs_todo sl (dom (v_cache v))).
    iSplitR; [iPureIntro; exact Hitd|].
    iSplitR; [iPureIntro; rewrite Hv1; reflexivity|].
    iFrame "Hpend0". iIntros "Hpend0".
    iSplitL "Hauth".
    { iExists dmap'. iFrame "Hauth". iPureIntro. exact Hdv'. }
    rewrite /virtio_proto Hv1.
    cbn [v_cfg v_isr v_seen v_used_idx v_disk v_cache v_taken].
    rewrite Hlive.
    iExists pr, dma, t0, t1, lo, nr, F, hist, pm.
    iFrame "Hcfg Hdma Hah Hslot Hnc Hnp Hrel Hfl Hnr Hflr Hpos Hfrag Hdone".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact Hok|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR.
    { iPureIntro. rewrite /vp_wt Hsl. split.
      - rewrite Htk. discriminate.
      - exact (vslot_cache_sub_delete (v_cache v) sl s Hcsub). }
    iSplitR; [iPureIntro; exact Hpm|].
    iSplitR; [iPureIntro; exact Hdd|].
    iSplitR; [iPureIntro; exact Hnrnc|].
    iSplitR; [iPureIntro; exact HF|].
    iApply (big_sepM_delete _ (vp_pend pr) (vp_nc pr) sl Hsl).
    assert (Hhtd : pend_todo pr (delete s (v_cache v)) (v_taken v) (vp_nc pr) sl
                   = vs_todo sl (dom (v_cache v)) ∖ {[ i ]}).
    { rewrite pend_todo_head Htk dom_delete_L Hskey. apply vs_todo_step. }
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
    (* A6.124: the lease's HALF of the word; the holder's own half is in the
       payload, and that is the one a read uses *)
    avail_lease_half (v_cfg v) np ∗
    (avail_lease_half (v_cfg v) np -∗
       virtio_proto γ v ∗ disk_pub γ np).
  Proof.
    iIntros "Hp Hpub". rewrite /virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & Hslot & Hnc & Hnp & _)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma t0 t1 lo nr F hist pm)
      "(#Hcfg & Hdma & Hah & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hwce & %Hwt &
        Hslot & Hnc & Hnp & Hrel & Hfl & Hnr & Hflr & Hpos & %Hpm & #Hfrag & %Hdd & %Hnrnc & %HF &
        Hpend & Hdone)".
    iDestruct (ghost_var_agree with "Hnp Hpub") as %Hnpeq.
    iEval (rewrite (half_map_ctl_split _ _ _ Hok)) in "Hah".
    iDestruct "Hah" as "[Hai Hpins]".
    iEval (rewrite Hnpeq) in "Hai".
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iSplitR; [iPureIntro; exact Hal|].
    iFrame "Hai". iIntros "Hai". iEval (rewrite -Hnpeq) in "Hai".
    iAssert (half_map (vproto_ctl (v_cfg v) pr)) with "[Hai Hpins]" as "Hah".
    { rewrite (half_map_ctl_split _ _ _ Hok). iFrame. }
    iFrame "Hpub". iExists pr, dma, t0, t1, lo, nr, F, hist, pm.
    iFrame "Hcfg Hdma Hah Hslot Hnc Hnp Hrel Hfl Hnr Hflr Hpos Hfrag Hpend Hdone".
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
    pin_offer pin -∗ phys_map wrb -∗
    (* NOTHING HAS DRAINED YET: a freshly published request owes its whole
       write, which is exactly the root of the sequential permit and exactly
       what [PermInv.perm_deposit_kq] hands the enqueuer back. *)
    slot_pend_res γ (vs_all sl) sl -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    (* A6.124: the lease's half of the word goes out; the publisher joins it
       with its own half, stores through the full cell, and hands the
       lease's half back at the new count *)
    avail_lease_half (v_cfg v) np ∗
    (avail_lease_half (v_cfg v) (S np) ==∗
       virtio_proto γ v ∗ disk_pub γ (S np) ∗ disk_receipt γ np sl pin ∗
       pin_back pin).
  Proof.
    intros Hslotok Hwrbdom Hwrpin.
    iIntros "Hp Hpub Hpin Hwrb Hpres".
    rewrite {1}/virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & Hslot & Hnc & Hnp & _)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma t0 t1 lo nr F hist pm)
      "(#Hcfg & Hdma & Hah & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hwce & %Hwt &
        Hslot & Hnc & Hnp & Hrel & Hfl & Hnr & Hflr & Hpos & %Hpm & #Hfrag & %Hdd & %Hnrnc & %HF &
        Hpend & Hdone)".
    iDestruct (ghost_var_agree with "Hnp Hpub") as %Hnpeq.
    iAssert (⌜dom pin ## dom dma⌝)%I as %Hpind.
    { iAssert ([∗ map] a ↦ b ∈ pin, pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn 1) b)%I
        with "[Hpin]" as "Hpp".
      { rewrite /pin_offer. iApply (big_sepM_impl with "Hpin").
        iIntros "!>" (a b _) "H". iApply pin_offer_full. iExact "H". }
      iApply (lease_disj_full with "Hdma Hah Hrel Hdone Hpp"). }
    iAssert (⌜dom wrb ## dom dma⌝)%I as %Hwrbd.
    { iAssert ([∗ map] a ↦ b ∈ wrb, pointsto (L := Arch.pa) (V := bv 8) a (DfracOwn 1) b)%I
        with "[Hwrb]" as "Hpp".
      { rewrite /phys_map. iApply (big_sepM_impl with "Hwrb").
        iIntros "!>" (a b _) "H". iDestruct (phys_ledger_forget with "H") as "H".
        rewrite /phys_pointsto. iDestruct "H" as "[$ _]". }
      iApply (lease_disj_full with "Hdma Hah Hrel Hdone Hpp"). }
    iDestruct (pin_offer_half_disj with "Hah Hpin") as %HpinD.
    iDestruct (phys_map_half_map_disj with "Hwrb Hah") as %HwrbD0.
    rewrite Hwrbdom in Hwrbd.
    iDestruct (pin_offer_full_disj with "Hwrb Hpin") as %Hpw.
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
    iEval (rewrite (half_map_ctl_split _ _ _ Hok)) in "Hah".
    iDestruct "Hah" as "[Hai Hpins]".
    iEval (rewrite Hnpeq) in "Hai".
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iFrame "Hai". iIntros "Hai".
    (* the pure facts about the new state, hoisted: the rebuilt lease's hole
       is the NEW control set *)
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
    assert (HrmD : dom (range_map (avail_idx_pa (v_cfg v)) 2
                          (nth_byte (wrap16 (S np)))) ⊆ avail_idx_dom (v_cfg v))
      by (rewrite HdomMMS; reflexivity).
    assert (Hd2' : wrb ##ₘ filter (fun p : Arch.pa * bv 8 =>
                                    p.1 ∉ lease_hole (v_cfg v) pr) dma).
    { apply map_disjoint_dom. rewrite dom_filter_notin Hwrbdom.
      apply (gset_disj_sub_r _ _ (dom dma)); [| exact Hwrbd].
      intros x Hx. apply elem_of_difference in Hx as [Hx _]. exact Hx. }
    assert (HctlD : dom (vproto_ctl (v_cfg v) pr)
                    = avail_idx_dom (v_cfg v) ∪ dom (pins_union (vp_pin pr)))
      by (unfold vproto_ctl; rewrite dom_union_L avail_idx_bytes_dom; reflexivity).
    assert (HctlD' : dom (vproto_ctl (v_cfg v) (vproto_publish_state pr sl pin))
                     = avail_idx_dom (v_cfg v) ∪ (dom pin ∪ dom (pins_union (vp_pin pr))))
      by (rewrite Hctl' !dom_union_L avail_idx_bytes_dom; reflexivity).
    assert (HavD : avail_idx_dom (v_cfg v) ⊆ dom dma)
      by (rewrite -HdomMMS; exact HMMSdma).
    assert (HdB : pin ##ₘ pins_union (vp_pin pr)).
    { apply map_disjoint_dom.
      apply (gset_disj_sub_r _ _ (dom dma)); [exact Hpudom | exact Hpind]. }
    assert (HdA : avail_idx_bytes (v_cfg v) (S np) ##ₘ (pin ∪ pins_union (vp_pin pr))).
    { apply map_disjoint_dom. rewrite avail_idx_bytes_dom dom_union_L.
      apply gset_disj_union_r.
      - apply gset_disj_sym. apply (gset_disj_sub_r _ _ (dom dma)); [exact HavD | exact Hpind].
      - apply (gset_disj_sub_l _ (avail_idx_dom (v_cfg v) ∪ used_page_pas (v_cfg v)));
          [ apply union_subseteq_l
          | apply gset_disj_sym; exact (pins_union_off_standing _ _ _ Hok) ]. }
    assert (HpinD' : dom pin ⊆ dom (vproto_ctl (v_cfg v) (vproto_publish_state pr sl pin))).
    { rewrite HctlD'. intros x Hx. apply elem_of_union_r, elem_of_union_l. exact Hx. }
    assert (HwrbD' : dom wrb ## dom (vproto_ctl (v_cfg v) (vproto_publish_state pr sl pin))).
    { rewrite HctlD'. apply gset_disj_union_r.
      - apply (gset_disj_sub_r _ _ (dom (vproto_ctl (v_cfg v) pr)));
          [ rewrite HctlD; apply union_subseteq_l | exact HwrbD0 ].
      - apply gset_disj_union_r.
        + apply gset_disj_sym. exact Hpw.
        + apply (gset_disj_sub_r _ _ (dom (vproto_ctl (v_cfg v) pr)));
            [ rewrite HctlD; apply union_subseteq_r | exact HwrbD0 ]. }
    assert (HrmD' : dom (range_map (avail_idx_pa (v_cfg v)) 2 (nth_byte (wrap16 (S np))))
                    ⊆ dom (vproto_ctl (v_cfg v) (vproto_publish_state pr sl pin))).
    { rewrite HctlD' HdomMMS. apply union_subseteq_l. }
    (* A6.126 §6: the hole is the ctl words (grown by the pin), the index
       word and the done slots -- the last two untouched by a publish *)
    assert (Hhole' : lease_hole (v_cfg v) (vproto_publish_state pr sl pin)
                     = lease_hole (v_cfg v) pr ∪ dom pin).
    { unfold lease_hole, lease_hole_pure. rewrite HctlD' HctlD vpp_done.
      apply set_eq. intro x. rewrite !elem_of_union. tauto. }
    assert (HholeSub : lease_hole (v_cfg v) pr ⊆ dom dma)
      by exact (lease_hole_sub (v_cfg v) pr (dom dma) Hok).
    iAssert (dma_own_x (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
                             (nth_byte (wrap16 (S np))) ∪ dma)))
               (lease_hole (v_cfg v) (vproto_publish_state pr sl pin)))
      with "[Hwrb Hdma]" as "Hdma".
    { rewrite /dma_own_x Hhole'.
      assert (Hs1 : dom pin ⊆ lease_hole (v_cfg v) pr ∪ dom pin) by apply union_subseteq_r.
      assert (Hs2 : dom wrb ## lease_hole (v_cfg v) pr ∪ dom pin).
      { rewrite Hwrbdom. apply gset_disj_union_r.
        - apply (gset_disj_sub_r _ _ (dom dma)); [exact HholeSub | exact Hwrbd].
        - apply gset_disj_sym; rewrite -Hwrbdom; exact Hpw. }
      assert (Hs3 : dom (range_map (avail_idx_pa (v_cfg v)) 2 (nth_byte (wrap16 (S np))))
                    ⊆ lease_hole (v_cfg v) pr ∪ dom pin).
      { etransitivity; [exact HrmD |]. etransitivity; [| apply union_subseteq_l].
        unfold lease_hole, lease_hole_pure. rewrite HctlD.
        intros x Hx. apply elem_of_union_l, elem_of_union_l, elem_of_union_l. exact Hx. }
      rewrite (map_filter_union_in pin _ _ Hs1).
      rewrite (map_filter_union_notin wrb _ _ Hs2).
      rewrite (map_filter_union_in _ _ _ Hs3).
      rewrite (map_filter_hole_ext dma (lease_hole (v_cfg v) pr ∪ dom pin)
                 (lease_hole (v_cfg v) pr)).
      2:{ intros a Ha. split.
          - intro H. apply elem_of_union in H as [H|H]; [exact H|].
            exfalso. exact (proj1 (elem_of_disjoint _ _) Hpind a H Ha).
          - intro H. apply elem_of_union_l. exact H. }
      rewrite /dma_own.
      rewrite (big_sepM_union (fun a b => phys_ledger a (DfracOwn 1) b) _ _ Hd2').
      iFrame "Hwrb Hdma". }
    iDestruct (pin_offer_split with "Hpin") as "[Hpinh Hpinb]".
    iAssert (half_map (vproto_ctl (v_cfg v) (vproto_publish_state pr sl pin)))
      with "[Hai Hpins Hpinh]" as "Hah".
    { rewrite Hctl' (half_map_union _ _ HdA) (half_map_union _ _ HdB)
              -avail_lease_half_eq.
      iFrame "Hai Hpinh Hpins". }
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
    rewrite /disk_receipt. rewrite Hnpeq. iFrame "Hrec Hpinb".
    rewrite /virtio_proto Hlive.
    iExists (vproto_publish_state pr sl pin),
      (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
         (nth_byte (wrap16 (S np))) ∪ dma))), t0, t1, lo, nr, F, hist, pm.
    rewrite (vp_spins_publish pr sl pin) vpp_nc vpp_np vpp_pend vpp_done Hnpeq.
    iFrame "Hcfg Hdma Hah Hslot Hnc Hnp Hrel Hfl Hnr Hflr Hpos Hfrag".
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
      assert (Hddu : dom (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
                      (nth_byte (wrap16 (S np))) ∪ dma)))
                    = dom dma ∪ slot_fp sl pin).
      { rewrite dom_union_L dom_union_L Hun_dom Hwrbdom. unfold slot_fp.
        apply gset_union_comm3. }
      rewrite Hddu. exact Hok'. }
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
    iSplitR; [iPureIntro; exact Hwce|].
    (* THE WRITETHROUGH ROW, one publish later.  If the queue was IDLE the
       new slot becomes the head, and the row's "no head" branch already said
       the cache is empty and untaken -- so the fresh slot inherits an empty
       cache, which is what puts its permit at the ROOT.  If the queue was
       busy the head is unchanged and so is the row. *)
    assert (Hwt' : vp_wt (vproto_publish_state pr sl pin) (v_cache v) (v_taken v)).
    { rewrite /vp_wt vpp_nc vpp_pend.
      destruct (decide (vp_nc pr = vp_np pr)) as [Heq|Hne].
      - rewrite Heq lookup_insert.
        assert (Hpn : vp_pend pr !! vp_nc pr = None)
          by (rewrite Heq; exact Hpendnone).
        destruct (vp_wt_none pr (v_cache v) (v_taken v) Hpn Hwt) as [Hca Htk].
        split; [by intros _ | rewrite Hca; apply map_empty_subseteq].
      - rewrite lookup_insert_ne;
          [ rewrite /vp_wt in Hwt; exact Hwt
          | exact (fun Hc => Hne (eq_sym Hc)) ]. }
    iSplitR; [iPureIntro; exact Hwt'|].
    iSplitR; [iPureIntro; exact Hpm|].
    iSplitR; [iPureIntro; exact Hdd|].
    iSplitR; [iPureIntro; exact Hnrnc|].
    iSplitR; [iPureIntro; exact HF|].
    (* the pending map gains [np]; the done records survive *)
    rewrite Hnpeq in Hpendnone.
    rewrite (big_sepM_insert _ (vp_pend pr) np sl Hpendnone).
    assert (Hnptd :
      pend_todo (vproto_publish_state pr sl pin) (v_cache v) (v_taken v) np sl
      = vs_all sl).
    { rewrite /pend_todo vpp_nc.
      destruct (bool_decide (np = vp_nc pr)) eqn:Hb; [|reflexivity].
      apply bool_decide_eq_true in Hb.
      assert (Hpn : vp_pend pr !! vp_nc pr = None)
        by (rewrite <- Hb; exact Hpendnone).
      destruct (vp_wt_none pr (v_cache v) (v_taken v) Hpn Hwt) as [_ Htk].
      by rewrite Htk. }
    assert (Hpmono : forall k x, vp_pend pr !! k = Some x ->
              slot_pend_res γ (pend_todo pr (v_cache v) (v_taken v) k x) x
              ⊢ slot_pend_res γ
                  (pend_todo (vproto_publish_state pr sl pin)
                     (v_cache v) (v_taken v) k x) x).
    { intros k x _. apply bi.wand_entails. rewrite /pend_todo vpp_nc.
      iIntros "$". }
    iSplitL "Hpres Hpend".
    { rewrite Hnptd. iFrame "Hpres".
      iApply (big_sepM_mono _ _ _ Hpmono). iExact "Hpend". }
    assert (Hmono : forall k x, vp_done pr !! k = Some x ->
              slot_done_res γ (v_cfg v) dma hist k x
              ⊢ slot_done_res γ (v_cfg v)
                  (pin ∪ (wrb ∪ (range_map (avail_idx_pa (v_cfg v)) 2
                     (nth_byte (wrap16 (S np))) ∪ dma))) hist k x).
    { intros k x Hk. apply bi.wand_entails.
      pose proof (vproto_done_slot (v_cfg v) pr (dom dma) k x Hok Hk) as Hks.
      assert (Hkpin : exists pinq, vp_pin pr !! k = Some pinq).
      { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
        apply elem_of_dom. exists x. exact Hks. }
      destruct Hkpin as [pinq Hpinq].
      pose proof (vpo_standing _ _ _ Hok k x pinq Hks Hpinq) as Hstq.
      pose proof (vpo_fp_D _ _ _ Hok k x pinq Hks Hpinq) as HfpD.
      apply slot_done_res_mono; [| reflexivity].
      intros a Ha. unfold slot_done_dom in Ha. apply Hframe.
      - apply elem_of_union in Ha as [Ha | Ha].
        + apply HfpD. apply slot_fp_wr. exact Ha.
        + apply (vpo_used_D _ _ _ Hok). apply (elem_dom_in_page (v_cfg v) k). exact Ha.
      - intro Hc. apply elem_of_union in Ha as [Ha | Ha].
        + exact (proj1 (elem_of_disjoint _ _) Hstq _ (slot_fp_wr x pinq a Ha)
                   (elem_of_union_l _ _ _ Hc)).
        + exact (proj1 (elem_of_disjoint _ _) (vpo_idx_used _ _ _ Hok) _ Hc
                   (elem_dom_in_page (v_cfg v) k a Ha)). }
    iApply (big_sepM_mono _ _ _ Hmono). iExact "Hdone".
  Qed.

  (* ==================================================================== *)
  (* driver operation 3: OBSERVE the used index (intr's used-idx lhu)     *)
  (* ==================================================================== *)

  (* The caller presents whatever completed-count lower bound it already has
     ([nr]); the accessor reports the current count [nc] ABOVE it, so two
     successive observations are comparable. *)
  (* ================================================================= *)
  (* A6.126 §6: THE READER SIDE.                                        *)
  (* ================================================================= *)

  (* the completed count against a holder's bounds -- the publisher's window
     peek (ProofVirtioDiskRwD) *)
  Lemma virtio_proto_used_idx_acc (γ : disk_names) (v : virtio_state) (np nr : nat) :
    virtio_proto γ v -∗ disk_pub γ np -∗ disk_done_lb γ nr -∗
    ∃ nc : nat,
      ⌜(nr <= nc)%nat⌝ ∗ ⌜(nc <= np)%nat⌝ ∗
      disk_cfg γ (v_cfg v) ∗ ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
      disk_done_lb γ nc ∗ (virtio_proto γ v ∗ disk_pub γ np).
  Proof.
    iIntros "Hp Hpub Hlb0". rewrite /virtio_proto /disk_pub /disk_done_lb.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & Hslot & Hnc & Hnp & _)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma t0 t1 lo nr' F hist pm)
      "(#Hcfg & Hdma & Hah & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hwce & %Hwt &
        Hslot & Hnc & Hnp & Hrel & Hfl & Hnr & Hflr & Hpos & %Hpm & #Hfrag & %Hdd & %Hnrnc & %HF &
        Hpend & Hdone)".
    iDestruct (ghost_var_agree with "Hnp Hpub") as %Hnpeq.
    iDestruct (mono_nat_lb_own_valid with "Hnc Hlb0") as %[_ Hnrle].
    iDestruct (mono_nat_lb_own_get with "Hnc") as "#Hlb".
    iExists (vp_nc pr).
    iSplitR; [iPureIntro; exact Hnrle|].
    iSplitR. { iPureIntro. pose proof (vpo_ncnp _ _ _ Hok). lia. }
    iSplitR; [iExact "Hcfg"|]. iSplitR; [iPureIntro; exact Hal|].
    iFrame "Hlb Hpub". iExists pr, dma, t0, t1, lo, nr', F, hist, pm.
    iFrame "Hcfg Hdma Hah Hslot Hnc Hnp Hrel Hfl Hnr Hflr Hpos Hfrag Hpend Hdone".
    iPureIntro. split_and!; assumption.
  Qed.

  (* THE WINDOW OPENER: the interrupt handler's atomic read of [used->idx].
     Hands out the release window (pre-mint or minted) with the history's
     shape, the reader-floor facts and the positions' fragments; the
     close-wand takes the window back unchanged. *)
  Lemma virtio_proto_used_idx_open (γ : disk_names) (v : virtio_state)
      (np nr F t0 t1 : nat) :
    virtio_proto γ v -∗ disk_pub γ np -∗ disk_nr γ nr -∗ disk_flr γ F -∗
    disk_fl γ t0 t1 -∗
    ∃ (nc lo : nat) (hist : list (nat * (nat -> bv 8))),
      ⌜(nr <= nc)%nat /\ (nc <= np)%nat⌝ ∗
      disk_cfg γ (v_cfg v) ∗ ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
      disk_done_lb γ nc ∗
      ⌜hist_ok hist nc⌝ ∗
      ⌜forall k, (k < 2)%nat -> (tf2 t0 t1 k <= lo)%nat⌝ ∗
      ⌜exists k, (k < 2)%nat /\ lo = tf2 t0 t1 k⌝ ∗
      ⌜forall p q g, hist !! p = Some (q, g) -> (p < nr)%nat -> (q <= F)%nat⌝ ∗
      ([∗ list] p ↦ qg ∈ hist, disk_done_pos γ p qg.1) ∗
      ((⌜hist = []⌝ ∗ TsoCtx.rel_pre_cells (used_idx_pa (v_cfg v)) 2 (tf2 t0 t1)
                        (nth_byte (wrap16 0)))
       ∨ TsoCtx.rel_cells (used_idx_pa (v_cfg v)) 2 (DfracOwn 1) disk_agent lo (tf2 t0 t1)
           (nth_byte (wrap16 0)) (nth_byte (wrap16 nc)) hist) ∗
      (((⌜hist = []⌝ ∗ TsoCtx.rel_pre_cells (used_idx_pa (v_cfg v)) 2 (tf2 t0 t1)
                         (nth_byte (wrap16 0)))
        ∨ TsoCtx.rel_cells (used_idx_pa (v_cfg v)) 2 (DfracOwn 1) disk_agent lo (tf2 t0 t1)
            (nth_byte (wrap16 0)) (nth_byte (wrap16 nc)) hist) -∗
         virtio_proto γ v ∗ disk_pub γ np ∗ disk_nr γ nr ∗ disk_flr γ F ∗
         disk_fl γ t0 t1).
  Proof.
    iIntros "Hp Hpub Hnr0 Hflr0 Hfl0". rewrite /virtio_proto /disk_pub.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & Hslot & Hnc & Hnp & _)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma t0' t1' lo nr' F' hist pm)
      "(#Hcfg & Hdma & Hah & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hwce & %Hwt &
        Hslot & Hnc & Hnp & Hrel & Hfl & Hnr & Hflr & Hpos & %Hpm & #Hfrag & %Hdd & %Hnrnc & %HF &
        Hpend & Hdone)".
    iDestruct (ghost_var_agree with "Hnp Hpub") as %Hnpeq.
    rewrite /disk_nr /disk_flr /disk_fl.
    iDestruct (ghost_var_agree with "Hnr Hnr0") as %Hnreq. subst nr'.
    iDestruct (ghost_var_agree with "Hflr Hflr0") as %HFeq. subst F'.
    iDestruct "Hfl" as "[Hfl0a Hfl1a]". iDestruct "Hfl0" as "[Hfl0b Hfl1b]".
    iDestruct (ghost_var_agree with "Hfl0a Hfl0b") as %Ht0. subst t0'.
    iDestruct (ghost_var_agree with "Hfl1a Hfl1b") as %Ht1. subst t1'.
    iDestruct (mono_nat_lb_own_get with "Hnc") as "#Hlb".
    iDestruct "Hrel" as "(%Hho & %Htf & %Hlo & Hcells)".
    iExists (vp_nc pr), lo, hist.
    iSplitR. { iPureIntro. pose proof (vpo_ncnp _ _ _ Hok). lia. }
    iSplitR; [iExact "Hcfg"|]. iSplitR; [iPureIntro; exact Hal|].
    iFrame "Hlb". iSplitR; [iPureIntro; exact Hho|].
    iSplitR; [iPureIntro; exact Htf|]. iSplitR; [iPureIntro; exact Hlo|].
    iSplitR; [iPureIntro; exact HF|]. iSplitR; [iExact "Hfrag"|].
    iFrame "Hcells". iIntros "Hcells".
    iFrame "Hpub Hnr0 Hflr0 Hfl0b Hfl1b".
    iFrame "Hnr Hflr Hfl0a Hfl1a".
    iExists pr, dma, lo, hist, pm.
    iFrame "Hcfg Hdma Hah Hslot Hnc Hnp Hpos Hfrag Hpend Hdone".
    iSplitR; [iPureIntro; exact Hctl|].
    iSplitR; [iPureIntro; exact Hok|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hseen|].
    iSplitR; [iPureIntro; exact Hui|].
    iSplitR; [iPureIntro; exact Hridx|].
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR; [iPureIntro; exact Hwt|].
    iSplitL "Hcells".
    { rewrite /used_rel_res. iFrame "Hcells". iPureIntro. split_and!; assumption. }
    iPureIntro. split_and!; assumption.
  Qed.

  (* THE READ THEOREM: what a hart with every floor write in view reads off
     the index word -- [wrap16 k] for some [k] between the reclaimed count
     and the completed count, with every completion below [k] in its view
     (TsoMemPa.rel_read through TsoCtx.ledger_read_rel_ok; the pre-mint
     window reads its floor bytes). *)
  Lemma used_rel_read_ok `{CID : CpuId} (g : gstate) (c : virtio_cfg)
      (nc lo nr F K : nat) (tf : nat -> nat) (hist : list (nat * (nat -> bv 8))) :
    hist_ok hist nc ->
    (forall p q g0, hist !! p = Some (q, g0) -> (p < nr)%nat -> (q <= F)%nat) ->
    (nr <= nc)%nat -> (F <= K)%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    TsoGhost.view_lb view_name loglen_name (hart_agent cpu_id) K -∗
    TsoCtx.rel_floor_vis (hart_agent cpu_id) K 2 tf -∗
    ((⌜hist = []⌝ ∗ TsoCtx.rel_pre_cells (used_idx_pa c) 2 tf (nth_byte (wrap16 0)))
     ∨ TsoCtx.rel_cells (used_idx_pa c) 2 (DfracOwn 1) disk_agent lo tf
         (nth_byte (wrap16 0)) (nth_byte (wrap16 nc)) hist) -∗
    ⌜forall tv : nat, (g.(gtv) cpu_id <= tv)%nat ->
       exists k, (nr <= k)%nat /\ (k <= nc)%nat
         /\ (forall j, (j < 2)%nat ->
               TsoMemPa.tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv (pa_add (used_idx_pa c) j)
               = Some (nth_byte (wrap16 k) j))
         /\ (forall p, (p < k)%nat ->
               exists q g0, hist !! p = Some (q, g0) /\ (q <= tv)%nat)⌝.
  Proof.
    intros Hho HF Hnrnc HFK. iIntros "Hgh Hint #HK #Hfv Hcells".
    iDestruct (TsoCtx.view_lb_le_view with "Hint HK") as %HKtv.
    pose proof Hho as (Hlen & Hval & Hsort).
    iDestruct "Hcells" as "[[%Hnil Hpre] | Hrel]".
    - iDestruct (TsoCtx.ledger_read_relpre_ok g (used_idx_pa c) 2 tf (nth_byte (wrap16 0)) K
                   with "Hgh Hint HK Hfv Hpre") as %Hrd.
      iPureIntro. intros tv Htv. exists 0%nat.
      assert (Hnc0 : nc = 0%nat) by (rewrite Hnil in Hlen; cbn in Hlen; lia).
      split_and!; [lia | lia | |].
      + intros j Hj. exact (Hrd tv Htv j Hj).
      + intros p Hp. lia.
    - iDestruct (TsoCtx.ledger_read_rel_ok g (used_idx_pa c) 2 (DfracOwn 1) disk_agent lo tf
                   (nth_byte (wrap16 0)) (nth_byte (wrap16 nc)) hist K ltac:(lia)
                   with "Hint HK Hfv Hrel") as %Hrd.
      iPureIntro. intros tv Htv.
      assert (Hne : hart_agent cpu_id ≠ disk_agent).
      { unfold hart_agent, disk_agent. pose proof (fin_to_nat_lt cpu_id). lia. }
      destruct (Hrd tv Htv) as [[Hfloor Hinv] | (T & g0 & Hin & HvT & Hle & Hbytes & Hmax)].
      + (* the floor: no history entry visible, so nothing was reclaimed *)
        exists 0%nat. split_and!; [| lia | exact Hfloor | intros p Hp; lia].
        destruct nr as [|nr']; [lia |]. exfalso.
        destruct (hist_ok_lookup_lt hist nc 0 Hho ltac:(lia)) as [q0 Hq0].
        pose proof (HF 0%nat q0 _ Hq0 ltac:(lia)) as HqF.
        pose proof (Hinv q0 _ (elem_of_list_lookup_2 _ _ _ Hq0)) as Hvis.
        rewrite (TsoMemPa.visibleb_below (hart_agent cpu_id) tv g.(glog) q0
                   ltac:(lia)) in Hvis. discriminate Hvis.
      + (* the latest visible entry: completion [k'], index [S k'] *)
        apply elem_of_list_lookup in Hin as [k' Hk'].
        pose proof (Hval k' T g0 Hk') as Hg0. subst g0.
        pose proof (Hle Hne) as HTtv.
        pose proof (lookup_lt_Some _ _ _ Hk') as Hk'len.
        exists (S k'). split_and!.
        * destruct (decide (nr <= S k')%nat) as [Hok' | Hgt]; [exact Hok'|]. exfalso.
          destruct (hist_ok_lookup_lt hist nc (S k') Hho ltac:(lia)) as [q1 Hq1].
          pose proof (HF (S k') q1 _ Hq1 ltac:(lia)) as Hq1F.
          pose proof (Hmax q1 _ (elem_of_list_lookup_2 _ _ _ Hq1)
                        (TsoMemPa.visibleb_below (hart_agent cpu_id) tv g.(glog) q1
                           ltac:(lia))) as Hq1T.
          pose proof (Hsort k' (S k') T q1 _ _ ltac:(lia) Hk' Hq1). lia.
        * lia.
        * exact Hbytes.
        * intros p Hp.
          destruct (hist_ok_lookup_lt hist nc p Hho ltac:(lia)) as [qp Hqp].
          exists qp, (nth_byte (wrap16 (S p))). split; [exact Hqp|].
          destruct (decide (p = k')) as [-> | Hne'].
          -- rewrite Hk' in Hqp. injection Hqp as Hq. subst qp. exact HTtv.
          -- pose proof (Hsort p k' qp T _ _ ltac:(lia) Hqp Hk'). lia.
  Qed.

  (* THE ELEMENT PEEK: a done slot's used element (the head), STAMPED at its
     completion's position, with the position's fragment; read-only *)
  Lemma virtio_proto_used_peek (γ : disk_names) (v : virtio_state)
      (np c p : nat) (sl : vslot) (pin : gmap Arch.pa (bv 8)) :
    (p < c)%nat ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    disk_receipt γ p sl pin -∗ disk_done_lb γ c -∗
    ∃ q : nat,
      disk_cfg γ (v_cfg v) ∗ disk_done_pos γ p q ∗
      ([∗ list] j ∈ seq 0 4,
         phys_ledger_at (pa_add (used_elem_pa (v_cfg v) p) j) (DfracOwn 1)
           (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) j) q) ∗
      (([∗ list] j ∈ seq 0 4,
          phys_ledger_at (pa_add (used_elem_pa (v_cfg v) p) j) (DfracOwn 1)
            (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) j) q) -∗
         virtio_proto γ v ∗ disk_pub γ np ∗ disk_receipt γ p sl pin ∗
         disk_done_lb γ c).
  Proof.
    intros Hpc. iIntros "Hp Hpub Hrecpt Hlb".
    rewrite /virtio_proto /disk_pub /disk_receipt /disk_done_lb.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & Hslot & Hnc & Hnp & _)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma t0 t1 lo nr F hist pm)
      "(#Hcfg & Hdma & Hah & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hwce & %Hwt &
        Hslot & Hnc & Hnp & Hrel & Hfl & Hnr & Hflr & Hpos & %Hpm & #Hfrag & %Hdd & %Hnrnc & %HF &
        Hpend & Hdone)".
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
    iDestruct "Hdres" as (bs q)
      "(%Hbslen & Hbs & %Hout & %Hre & %Hrl & %Hst & %Hbl & %Hq & Hcells & Hdone0)".
    rewrite /slot_done_cells. iDestruct "Hcells" as "(Hh & Hl & Hstm & Hbuf)".
    destruct Hq as [g Hg].
    iDestruct (big_sepL_lookup _ hist p (q, g) Hg with "Hfrag") as "#Hposq".
    iExists q. iSplitR; [iExact "Hcfg"|]. iSplitR; [iExact "Hposq"|].
    iFrame "Hh". iIntros "Hh".
    iFrame "Hpub Hrecpt Hlb".
    iExists pr, dma, t0, t1, lo, nr, F, hist, pm.
    iFrame "Hcfg Hdma Hah Hslot Hnc Hnp Hrel Hfl Hnr Hflr Hpos Hfrag Hpend".
    repeat (iSplitR; [by iPureIntro|]).
    iApply (big_sepM_delete _ (vp_done pr) p sl Hdone).
    iSplitR "Hdone"; [| iExact "Hdone"].
    iExists bs, q. iFrame "Hbs Hdone0". rewrite /slot_done_cells. iFrame "Hh Hl Hstm Hbuf".
    iPureIntro. split_and!; [assumption | assumption | assumption | assumption | assumption | assumption |].
    by exists g.
  Qed.

  (* THE RECLAIM: the handler, having read an index past [p] at a view [V0]
     that has completion [p]'s position [q0] in it, takes the slot's payoff --
     the pin's halves, the status byte and (a read) the buffer, all STAMPED
     at [q0] -- and moves the reader floor to [V0].  The used element's head
     is exposed for the handler's one [lw] and comes back; the whole element
     then returns to the sealed lease. *)
  Lemma virtio_proto_reclaim_acc (γ : disk_names) (v : virtio_state)
      (np c p : nat) (sl : vslot) (pin : gmap Arch.pa (bv 8)) (q0 V0 F : nat) :
    (p < c)%nat ->
    virtio_proto γ v -∗ disk_pub γ np -∗
    disk_receipt γ p sl pin -∗ disk_done_lb γ c -∗
    disk_nr γ p -∗ disk_flr γ F -∗
    disk_done_pos γ p q0 -∗ ⌜(q0 <= V0)%nat⌝ -∗
    ⌜virtio_live (v_cfg v) = true⌝ ∗
    disk_cfg γ (v_cfg v) ∗
    ⌜virtio_pages_aligned (v_cfg v)⌝ ∗
    ⌜slot_pin_ok (v_cfg v) p sl pin⌝ ∗
    ([∗ list] j ∈ seq 0 4,
       phys_ledger_at (pa_add (used_elem_pa (v_cfg v) p) j) (DfracOwn 1)
         (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) j) q0) ∗
    (([∗ list] j ∈ seq 0 4,
        phys_ledger_at (pa_add (used_elem_pa (v_cfg v) p) j) (DfracOwn 1)
          (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))) j) q0) ==∗
       virtio_proto γ v ∗ disk_pub γ np ∗ disk_done_lb γ (S p) ∗
       disk_nr γ (S p) ∗ disk_flr γ (Nat.max F V0) ∗
       half_map pin ∗
       phys_ledger_at (vr_status (vs_req sl)) (DfracOwn 1) byte_zero q0 ∗
       slot_perms_done γ sl ∗
       (∃ bs : list (bv 8),
          ⌜length bs = vs_len sl⌝ ∗
          ⌜bs = vs_data sl⌝ ∗
          disk_bytes γ (vs_sector_off sl) bs ∗
          (if vs_is_out sl then emp
           else [∗ list] j ∈ seq 0 (vs_len sl),
                  phys_ledger_at (pa_add (vr_buf (vs_req sl)) j) (DfracOwn 1) (bs !!! j) q0))).
  Proof.
    intros Hpc. iIntros "Hp Hpub Hrecpt Hlb Hnr0 Hflr0 #Hpos0 %Hq0V".
    rewrite {1}/virtio_proto /disk_pub /disk_receipt /disk_done_lb.
    destruct (virtio_live (v_cfg v)) eqn:Hlive; last first.
    { iDestruct "Hp" as "(Hcfg & _ & _ & _ & _ & _ & Hslot & Hnc & Hnp & _)".
      iDestruct (ghost_var_valid_2 with "Hnp Hpub") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hq). }
    iDestruct "Hp" as (pr dma t0 t1 lo nr F' hist pm)
      "(#Hcfg & Hdma & Hah & %Hctl & %Hok & %Hal & %Hseen & %Hui & %Hridx & %Hwce & %Hwt &
        Hslot & Hnc & Hnp & Hrel & Hfl & Hnr & Hflr & Hpos & %Hpm & #Hfrag & %Hdd & %Hnrnc & %HF &
        Hpend & Hdone)".
    rewrite /disk_nr /disk_flr.
    iDestruct (ghost_var_agree with "Hnr Hnr0") as %Hnreq. subst nr.
    iDestruct (ghost_var_agree with "Hflr Hflr0") as %HFeq. subst F'.
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
    pose proof (vpo_qnum _ _ _ Hok) as Hqnum.
    pose proof (vpo_slot _ _ _ Hok p sl pin Hs Hpin) as Hslotok.
    pose proof (vpo_wr_pin _ _ _ Hok p sl pin Hs Hpin) as Hwrpin.
    pose proof (vpo_standing _ _ _ Hok p sl pin Hs Hpin) as Hstand.
    assert (Hwrpage : slot_wr sl ## used_page_pas (v_cfg v)).
    { apply (gset_disj_mono (slot_wr sl) (slot_fp sl pin) (used_page_pas (v_cfg v))
               (avail_idx_dom (v_cfg v) ∪ used_page_pas (v_cfg v)));
        [ apply slot_fp_wr | apply union_subseteq_r | exact Hstand ]. }
    iDestruct (big_sepM_delete _ (vp_done pr) p sl Hdone with "Hdone")
      as "[Hdres Hdone]".
    iDestruct "Hdres" as (bs q)
      "(%Hbslen & Hbs & %Hout & %Hre & %Hrl & %Hst & %Hbl & %Hq & Hcells & Hdone0)".
    rewrite /slot_done_cells. iDestruct "Hcells" as "(Hh & Hl & Hstm & Hbuf)".
    destruct Hq as [g Hg].
    iDestruct (big_sepL_lookup _ hist p (q, g) Hg with "Hfrag") as "#Hposq".
    iDestruct (disk_done_pos_agree with "Hpos0 Hposq") as %Hqeq. subst q0.
    iSplitR; [done|]. iSplitR; [iExact "Hcfg"|].
    iSplitR; [iPureIntro; exact Hal|].
    iSplitR; [iPureIntro; exact Hslotok|].
    iFrame "Hh". iIntros "Hh".
    (* ---- the lease's map after the reclaim, and its hole ---- *)
    set (SB := ({[ vr_status (vs_req sl) := byte_zero ]}
                ∪ (if vs_is_out sl then ∅
                   else range_map (vr_buf (vs_req sl)) (length bs)
                          (fun j : nat => bs !!! j)))).
    assert (HdomSB : dom SB = slot_wr sl).
    { unfold SB. rewrite dom_union_L dom_singleton_L. unfold slot_wr. f_equal.
      destruct (vs_is_out sl); [ apply dom_empty_L |].
      rewrite range_map_dom Hbslen. reflexivity. }
    assert (HdomMM : dom (pin ∪ SB) = slot_fp sl pin).
    { rewrite dom_union_L HdomSB. reflexivity. }
    destruct (vproto_reclaim_ctl (v_cfg v) pr (dom dma) p sl pin Hok Hdone Hpin)
      as (Hctlr & Hdisjr & Hctlsplit).
    assert (HAsub : avail_idx_bytes (v_cfg v) (vp_np pr)
                    ∪ pins_union (delete p (vp_pin pr)) ⊆ dma).
    { etransitivity; [ apply (map_union_subseteq_r _ _ Hdisjr) |].
      rewrite <- Hctlsplit. exact Hctl. }
    (* the other standing slots against this one and against its element *)
    assert (Hothers : forall k x, delete p (vp_done pr) !! k = Some x ->
              (slot_fp sl pin ∪ elem_dom (v_cfg v) p) ## slot_done_dom (v_cfg v) k x).
    { intros k x Hk. apply lookup_delete_Some in Hk as [Hkne Hk].
      pose proof (vproto_done_slot (v_cfg v) pr (dom dma) k x Hok Hk) as Hks.
      assert (Hkpin : exists pinq, vp_pin pr !! k = Some pinq).
      { apply elem_of_dom. rewrite (vproto_slot_dom (v_cfg v) pr (dom dma) Hok).
        apply elem_of_dom. exists x. exact Hks. }
      destruct Hkpin as [pinq Hpinq].
      pose proof (vpo_fp_disj _ _ _ Hok p k sl x pin pinq
                    Hkne Hs Hpin Hks Hpinq) as Hfpd.
      pose proof (vpo_standing _ _ _ Hok k x pinq Hks Hpinq) as Hstq.
      assert (Hmod : Z.of_nat p `mod` 8 ≠ Z.of_nat k `mod` 8)
        by exact (vproto_mod8_ne (v_cfg v) pr (dom dma) p k sl x pin pinq Hok
                    Hkne Hs Hpin Hks Hpinq).
      assert (Hwk : slot_wr x ## used_page_pas (v_cfg v)).
      { apply (gset_disj_mono (slot_wr x) (slot_fp x pinq) (used_page_pas (v_cfg v))
                 (avail_idx_dom (v_cfg v) ∪ used_page_pas (v_cfg v)));
          [ apply slot_fp_wr | apply union_subseteq_r | exact Hstq ]. }
      pose proof (elem_dom_in_page (v_cfg v) k) as Hkpg.
      pose proof (elem_dom_in_page (v_cfg v) p) as Hppg.
      pose proof (elem_dom_disj (v_cfg v) p k Hmod) as Hed.
      apply elem_of_disjoint. intros a Ha Hb. unfold slot_done_dom in Hb.
      apply elem_of_union in Ha as [Ha | Ha]; apply elem_of_union in Hb as [Hb | Hb].
      - exact (proj1 (elem_of_disjoint _ _) Hfpd a Ha (slot_fp_wr x pinq a Hb)).
      - exact (proj1 (elem_of_disjoint _ _) Hstand a Ha (elem_of_union_r _ _ _ (Hkpg a Hb))).
      - exact (proj1 (elem_of_disjoint _ _) Hwk a Hb (Hppg a Ha)).
      - exact (proj1 (elem_of_disjoint _ _) Hed a Ha Hb). }
    assert (Hdone' : (slot_fp sl pin ∪ elem_dom (v_cfg v) p)
                     ## done_dom (v_cfg v) (delete p (vp_done pr))).
    { apply elem_of_disjoint. intros a Ha Hb.
      apply elem_of_done_dom in Hb as (k & x & Hk & Hb).
      exact (proj1 (elem_of_disjoint _ _) (Hothers k x Hk) a Ha Hb). }
    assert (HctlD' : dom (vproto_ctl (v_cfg v) (vproto_reclaim_state pr p))
                     ## (slot_fp sl pin ∪ elem_dom (v_cfg v) p)).
    { rewrite Hctlr. apply elem_of_disjoint. intros a Ha Hb.
      rewrite dom_union_L avail_idx_bytes_dom in Ha.
      assert (Hused : a ∈ elem_dom (v_cfg v) p -> a ∈ used_page_pas (v_cfg v))
        by (intro H; exact (elem_dom_in_page (v_cfg v) p a H)).
      apply elem_of_union in Ha as [Ha | Ha].
      - apply elem_of_union in Hb as [Hb | Hb].
        + exact (proj1 (elem_of_disjoint _ _) Hstand a Hb (elem_of_union_l _ _ _ Ha)).
        + exact (proj1 (elem_of_disjoint _ _) (vpo_idx_used _ _ _ Hok) a Ha (Hused Hb)).
      - apply pins_union_dom_inv in Ha as (q' & mq & Hq' & Hmq).
        apply lookup_delete_Some in Hq' as [Hne Hq'].
        destruct (vproto_slot_of_pin (v_cfg v) pr (dom dma) q' mq Hok Hq') as [slq Hsq].
        pose proof (vpo_standing _ _ _ Hok q' slq mq Hsq Hq') as Hstq'.
        apply elem_of_union in Hb as [Hb | Hb].
        + exact (proj1 (elem_of_disjoint _ _)
                   (vpo_fp_disj _ _ _ Hok p q' sl slq pin mq Hne Hs Hpin Hsq Hq') a Hb
                   (slot_fp_pin slq mq a Hmq)).
        + exact (proj1 (elem_of_disjoint _ _) Hstq' a (slot_fp_pin slq mq a Hmq)
                   (elem_of_union_r _ _ _ (Hused Hb))). }
    assert (Hpinfp : dom pin ⊆ slot_fp sl pin) by apply slot_fp_pin.
    assert (Hwrfp : slot_wr sl ⊆ slot_fp sl pin) by apply slot_fp_wr.
    (* the used element goes back into the sealed lease *)
    set (em := range_map (used_elem_pa (v_cfg v) p) 4
                 (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))))
               ∪ range_map (pa_off (used_elem_pa (v_cfg v) p) 4) 4
                   (nth_byte (vreq_used_len (vs_req sl)))).
    assert (H4 : Z.of_nat 4 < 18446744073709551616) by lia.
    assert (Hemdisj : range_map (used_elem_pa (v_cfg v) p) 4
                        (nth_byte (Z_to_bv 32 (bv_unsigned (vr_head (vs_req sl)))))
                      ##ₘ range_map (pa_off (used_elem_pa (v_cfg v) p) 4) 4
                            (nth_byte (vreq_used_len (vs_req sl)))).
    { apply map_disjoint_dom. rewrite !range_map_dom. apply elem_of_disjoint.
      intros a Ha Hb. apply pa_range_elim in Hb as (j & Hj & ->).
      exact (elem_len_off_head (v_cfg v) p j Hj Ha). }
    assert (Hemdom : dom em = elem_dom (v_cfg v) p).
    { unfold em, elem_dom. rewrite dom_union_L !range_map_dom pa_range_split8. reflexivity. }
    assert (Hemsub : em ⊆ dma).
    { unfold em. apply map_union_least.
      - apply range_map_sub; [lia|]. intros j Hj.
        apply (read_bytes_spec dma (used_elem_pa (v_cfg v) p) 4 _ Hre). lia.
      - apply range_map_sub; [lia|]. intros j Hj.
        apply (read_bytes_spec dma (pa_off (used_elem_pa (v_cfg v) p) 4) 4 _ Hrl). lia. }
    assert (HemD : dom em ⊆ lease_hole (v_cfg v) pr).
    { rewrite Hemdom. unfold lease_hole, lease_hole_pure.
      rewrite (done_dom_delete (v_cfg v) (vp_done pr) p sl Hdone).
      unfold slot_done_dom. intros x Hx.
      apply elem_of_union_r, elem_of_union_l, elem_of_union_r. exact Hx. }
    iAssert (phys_map em) with "[Hh Hl]" as "Hem".
    { rewrite /phys_map /em (big_sepM_union _ _ _ Hemdisj)
              (range_map_big_sepM _ _ _ _ H4) (range_map_big_sepM _ _ _ _ H4).
      iSplitL "Hh".
      - iApply (big_sepL_impl with "Hh"). iIntros "!>" (k j _) "H".
        iApply (phys_ledger_at_ledger with "H").
      - iApply (big_sepL_impl with "Hl"). iIntros "!>" (k j _) "H".
        iApply (phys_ledger_at_ledger with "H"). }
    iDestruct (dma_own_x_fill em dma _ Hemsub HemD with "Hdma Hem") as "Hdma".
    assert (HmmD : dom (pin ∪ SB) ⊆ lease_hole (v_cfg v) pr ∖ dom em).
    { rewrite HdomMM Hemdom. unfold lease_hole, lease_hole_pure.
      rewrite (done_dom_delete (v_cfg v) (vp_done pr) p sl Hdone) Hctlsplit dom_union_L.
      unfold slot_done_dom.
      assert (Hfe : slot_fp sl pin ## elem_dom (v_cfg v) p).
      { apply elem_of_disjoint. intros a Ha Hb.
        exact (proj1 (elem_of_disjoint _ _) Hstand a Ha
                 (elem_of_union_r _ _ _ (elem_dom_in_page (v_cfg v) p a Hb))). }
      intros x Hx. pose proof Hx as Hx0. unfold slot_fp in Hx0.
      apply elem_of_difference. split.
      - apply elem_of_union in Hx0 as [Hx0 | Hx0].
        + apply elem_of_union_l, elem_of_union_l, elem_of_union_l. exact Hx0.
        + apply elem_of_union_r, elem_of_union_l, elem_of_union_l. exact Hx0.
      - intro Hc. exact (proj1 (elem_of_disjoint _ _) Hfe x Hx Hc). }
    rewrite (dma_own_x_drop_hole _ (pin ∪ SB) _ HmmD).
    assert (HholeD : (lease_hole (v_cfg v) pr ∖ dom em) ∖ dom (pin ∪ SB)
                     = lease_hole (v_cfg v) (vproto_reclaim_state pr p)).
    { rewrite HdomMM Hemdom. unfold lease_hole, lease_hole_pure.
      rewrite (done_dom_delete (v_cfg v) (vp_done pr) p sl Hdone) Hctlsplit dom_union_L vpr_done.
      rewrite Hctlr in HctlD'.
      assert (Hidx : (slot_fp sl pin ∪ elem_dom (v_cfg v) p) ## used_idx_dom (v_cfg v)).
      { apply elem_of_disjoint. intros a Ha Hb.
        apply pa_range_elim in Hb as (j & Hj & ->).
        pose proof (used_idx_in_page (v_cfg v) j Hj) as Hin.
        apply elem_of_union in Ha as [Ha | Ha].
        - exact (proj1 (elem_of_disjoint _ _) Hstand _ Ha (elem_of_union_r _ _ _ Hin)).
        - exact (proj1 (elem_of_disjoint _ _) (elem_idx_disj (v_cfg v) p) _ Ha
                   (pa_range_intro _ _ _ Hj)). }
      unfold slot_done_dom, slot_fp in *. rewrite Hctlr.
      apply set_eq. intro x.
      pose proof (proj1 (elem_of_disjoint _ _) HctlD' x) as H1.
      pose proof (proj1 (elem_of_disjoint _ _) Hidx x) as H2.
      pose proof (proj1 (elem_of_disjoint _ _) Hdone' x) as H3.
      clear - H1 H2 H3.
      rewrite !elem_of_union in H1 H2 H3.
      rewrite !elem_of_difference !elem_of_union. tauto. }
    rewrite HholeD.
    assert (Hframe : forall x : Arch.pa, x ∉ slot_fp sl pin ->
              (dma ∖ (pin ∪ SB)) !! x = dma !! x).
    { intros x Hx. apply lookup_difference_out. rewrite HdomMM. exact Hx. }
    assert (Hdomdiff : dom (dma ∖ (pin ∪ SB)) = dom dma ∖ slot_fp sl pin)
      by (rewrite dom_difference_L HdomMM; reflexivity).
    (* the halves, the counters, the floor *)
    iEval (rewrite Hctlsplit (half_map_union _ _ Hdisjr)) in "Hah".
    iDestruct "Hah" as "[Hpin Hah]".
    iEval (rewrite -Hctlr) in "Hah".
    iMod (ghost_map_delete with "Hslot Hrecpt") as "Hslot".
    iDestruct (mono_nat_lb_own_get with "Hnc") as "#Hlbnc".
    assert (Hsp : (S p <= vp_nc pr)%nat) by lia.
    iDestruct (mono_nat_lb_own_le (S p) Hsp with "Hlbnc") as "#Hlbp".
    iMod (ghost_var_update_halves (S p) with "Hnr Hnr0") as "[Hnr Hnr0]".
    iMod (ghost_var_update_halves (Nat.max F V0) with "Hflr Hflr0") as "[Hflr Hflr0]".
    iModIntro. iFrame "Hpub Hlbp Hnr0 Hflr0 Hpin Hstm Hdone0".
    iSplitR "Hbs Hbuf"; last first.
    { iExists bs. iFrame "Hbs". iSplitR; [iPureIntro; exact Hbslen|].
      iSplitR; [iPureIntro; exact Hout|].
      destruct (vs_is_out sl) eqn:Hoo; [done|]. iExact "Hbuf". }
    rewrite /virtio_proto Hlive.
    iExists (vproto_reclaim_state pr p), (dma ∖ (pin ∪ SB)), t0, t1, lo, (S p),
      (Nat.max F V0), hist, pm.
    rewrite (vp_spins_reclaim (v_cfg v) pr (dom dma) p sl Hok Hdone)
            vpr_nc vpr_np vpr_pend vpr_done.
    iFrame "Hcfg Hdma Hah Hslot Hnc Hnp Hrel Hfl Hnr Hflr Hpos Hfrag Hpend".
    iSplitR.
    { iPureIntro. rewrite Hctlr. apply map_sub_difference; [exact HAsub|].
      rewrite HdomMM. rewrite Hctlr in HctlD'.
      assert (Hd2x : dom (avail_idx_bytes (v_cfg v) (vp_np pr)
                       ∪ pins_union (delete p (vp_pin pr))) ## slot_fp sl pin).
      { apply (gset_disj_sub_r _ _ (slot_fp sl pin ∪ elem_dom (v_cfg v) p));
          [apply union_subseteq_l | exact HctlD']. }
      first [ exact Hd2x | apply gset_disj_sym; exact Hd2x ]. }
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
    iSplitR; [iPureIntro; exact Hwce|].
    iSplitR; [iPureIntro; exact Hwt|].
    iSplitR; [iPureIntro; exact Hpm|].
    iSplitR.
    { iPureIntro. rewrite dom_delete_L Hdd. apply set_eq. intro a.
      rewrite elem_of_difference !elem_of_set_seq not_elem_of_singleton. lia. }
    iSplitR; [iPureIntro; lia|].
    iSplitR.
    { iPureIntro. intros p' q' g' Hp' Hlt.
      destruct (decide (p' = p)) as [-> | Hne].
      - rewrite Hg in Hp'. injection Hp' as Hq' _. subst q'. cbn in Hq0V. lia.
      - pose proof (HF p' q' g' Hp' ltac:(lia)). lia. }
    assert (Hmono : forall k x, delete p (vp_done pr) !! k = Some x ->
              slot_done_res γ (v_cfg v) dma hist k x
              ⊢ slot_done_res γ (v_cfg v) (dma ∖ (pin ∪ SB)) hist k x).
    { intros k x Hk. apply bi.wand_entails.
      apply slot_done_res_mono; [| reflexivity].
      intros a Ha. apply Hframe. intro Hc'.
      exact (proj1 (elem_of_disjoint _ _) (Hothers k x Hk) a (elem_of_union_l _ _ _ Hc') Ha). }
    iApply (big_sepM_mono _ _ _ Hmono). iExact "Hdone".
  Qed.

End VirtioProto.
