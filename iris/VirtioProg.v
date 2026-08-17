(* ====================================================================== *)
(* VirtioProg.v                                                            *)
(*                                                                         *)
(* THE VIRTIO DEVICE AS A PROGRAM: a read / write / fence monad [DM] and    *)
(* the device program [virtio_prog], plus THE EQUIVALENCE that ties it back *)
(* to VirtioModel's atomic autonomous step [virtio_req_step].               *)
(*                                                                         *)
(* Design: claude-notes/design/weak-memory-m5.md, sections `The device     *)
(* program` and `Assumptions`.  M5 makes the disk a weak-memory AGENT       *)
(* rather than a flat-memory oracle: the device acquire-loads the available *)
(* index, plain-loads the ring entry / descriptors / header / data buffer   *)
(* at the view it thereby acquired, stores the completion, FENCES, and only *)
(* then stores the used index -- one Layer-1 memory event per node, at the  *)
(* disk agent's own [wstate], using exactly the labels a hart uses.  This   *)
(* file is the PROGRAM half of that: Iris-free, SC tree untouched, and it   *)
(* depends only on VirtioModel.v.                                           *)
(*                                                                         *)
(* THE WRITE ORDER (a DESIGN decision, not an artefact -- see the FINDING   *)
(* below), for one completed request:                                       *)
(*                                                                          *)
(*     [data buffer]  ;  status byte  ;  used elem .id  ;  used elem .len   *)
(*        ;  FENCE  ;  used ring ->idx                                       *)
(*                                                                          *)
(* The [DFence] is the device-side WRITE BARRIER of the virtio spec: every  *)
(* byte the driver will look at after seeing the index bump is published    *)
(* BEFORE the index bump.  That single fence is the whole synchronisation   *)
(* the driver's completion path relies on ([used->idx read ; fence rw,rw ;  *)
(* used elem read] on the other side), and it is why the QUEUE_NOTIFY       *)
(* doorbell's ordering is irrelevant to safety.  A disk WRITE reads the     *)
(* data buffer BEFORE any store (assumption 1 covers that read too); a disk *)
(* READ writes the data buffer first, so the status byte -- the thing a     *)
(* poller may look at -- is never visible ahead of the data it describes.    *)
(*                                                                          *)
(* READ GRANULARITY: each descriptor is FOUR reads (addr:8 len:4 flags:2    *)
(* next:2), one per [view_word] the model's [desc_at] performs, not one     *)
(* 16-byte read that is then split.  Four reads make every [run_dm] step a  *)
(* CONVERSION ([run_dread_desc] is [reflexivity]); a single 16-byte read    *)
(* would have to re-derive [view_word mv (pa_off base 8) 4] from a slice of *)
(* [view_bytes mv base 16], i.e. [pa_add] associativity, for no gain.  A    *)
(* real device is free to burst; splitting a burst into its fields only     *)
(* ADDS interleavings, so this is the conservative choice as well.          *)
(*                                                                          *)
(* ASSUMPTIONS this model makes about the device (weak-memory-m5.md):        *)
(*  1. The device reads the available index with ACQUIRE ordering relative  *)
(*     to its subsequent ring / descriptor / buffer reads (the spec's       *)
(*     device-side read barrier).  Only that one read sets [aq].            *)
(*  2. The device's completion writes are ordered before its used-index     *)
(*     write (the [DFence]; the spec's device-side write barrier).          *)
(*  3. The device may process a published request at any time (polling);    *)
(*     QUEUE_NOTIFY and the ISR are hints.  A superset of a notify-driven   *)
(*     device.                                                              *)
(*  4. A malformed chain lets the device write anything anywhere ([DWild]), *)
(*     so a driver must PROVE its chains are well formed.                   *)
(*  5. No icache; MMIO registers are fabric state.                          *)
(*                                                                          *)
(* Two further points where the program is deliberately not a transcription *)
(* of [virtio_complete]:                                                    *)
(*                                                                          *)
(*  - A ZERO-LENGTH data transfer emits NO event at all ([dread_data] /     *)
(*    [dwrite_data]).  A store of zero bytes is not a memory event -- the   *)
(*    language's store arm requires a nonempty payload ([dm_wf]) -- and a   *)
(*    zero-byte read has no address to read.  Both are no-ops in the model  *)
(*    too ([view_bytes _ _ 0 = []], [write_byte_list m _ [] = m]), so this  *)
(*    changes nothing but the event count.                                  *)
(*                                                                          *)
(*  - The commit delta takes the CONFIGURATION and the ISR from the state   *)
(*    at COMMIT time and the two ring counters from the state the program   *)
(*    was STARTED at ([vdelta]): a hart's MMIO writes during the burst must *)
(*    not be clobbered, while [v_seen]/[v_used_idx] are the +1 of the       *)
(*    values the burst actually consumed, exactly as [virtio_complete] has  *)
(*    them.                                                                 *)
(*                                                                          *)
(* FINDING (recorded rather than fudged): the model's write MAP and the     *)
(* program's ORDERED writes differ on OVERLAP, and no device-correct        *)
(* emission order can fix that.  [virtio_complete] builds its [gmap] as     *)
(*   data  >  status  >  used->idx  >  elem.len  >  elem.id                 *)
(* (highest precedence first; [<[status:=..]>] and the data [write_byte_    *)
(* list] are applied OUTERMOST, so they win), i.e. as if the device wrote   *)
(* the used index BEFORE the status byte and the data LAST -- the reverse   *)
(* of any device that observes assumption 2.  A later-writes-win fold of    *)
(* the order above gives the reverse precedence.  The two agree exactly     *)
(* when the written regions do not overlap, which is what the DMA lease of  *)
(* the device invariant gives a driver anyway; so [virtio_prog_req_step]    *)
(* carries that as the explicit side condition [virtio_prog_disj] (NoDup on *)
(* the addresses the program writes) and everything else -- the resulting   *)
(* STATE, [DWild], [DIdle], the trichotomy, [dm_wf] -- is unconditional.    *)
(* The emission order above was NOT changed to make the map equation come   *)
(* out; if the discrepancy is ever to be closed it is [virtio_complete]'s   *)
(* nesting that should be re-ordered, not the device's write barrier.       *)
(* ====================================================================== *)

From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.

Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import VirtioModel.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. Prelude: [pa_add a 0 = a].                                           *)
(*                                                                         *)
(*    RiscvExtras proves this, but RiscvExtras imports Iris and this file   *)
(*    must not; the proof is three lines, so it is repeated here rather     *)
(*    than dragging the Iris tower into the device model.                   *)
(* ---------------------------------------------------------------------- *)

Lemma vp_pa_add_0 (a : Arch.pa) : pa_add a 0%nat = a.
Proof.
  unfold pa_add, add_vec_int, add_vec, Operators_mwords.word_binop,
         Operators_mwords.with_word', SailStdpp.Values.with_word,
         SailStdpp.Values.mword_of_int,
         SailStdpp.MachineWord.MachineWord.add,
         SailStdpp.MachineWord.MachineWord.Z_to_word.
  apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  change (Z.of_nat 0) with 0. rewrite bv_wrap_0, Z.add_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. The monad.                                                            *)
(* ---------------------------------------------------------------------- *)

Inductive DM (A : Type) : Type :=
  | DRet   (a : A)
  | DRead  (pa : Arch.pa) (n : nat) (aq : bool) (k : list (bv 8) -> DM A)
  | DWrite (pa : Arch.pa) (bs : list (bv 8)) (k : DM A)
  | DFence (k : DM A).

Arguments DRet {A} a.
Arguments DRead {A} pa n aq k.
Arguments DWrite {A} pa bs k.
Arguments DFence {A} k.

(* The result of one device burst. *)
Inductive dres :=
  | DDone (delta : virtio_state -> virtio_state)
  | DWild
  | DIdle.

(* ---------------------------------------------------------------------- *)
(* 2. Structural well-formedness: what the language's arms will require.    *)
(*                                                                         *)
(*    Every read is of at least one byte (a zero-byte read has no address   *)
(*    to read) and every store carries at least one byte (a store of zero   *)
(*    bytes cannot be a log message).  Closed under continuations at ANY    *)
(*    answers, not just the ones a flat memory would give.                  *)
(* ---------------------------------------------------------------------- *)

Inductive dm_wf {A : Type} : DM A -> Prop :=
  | dm_wf_ret a : dm_wf (DRet a)
  | dm_wf_read pa n aq k :
      (0 < n)%nat -> (forall bs, dm_wf (k bs)) -> dm_wf (DRead pa n aq k)
  | dm_wf_write pa bs k : bs <> [] -> dm_wf k -> dm_wf (DWrite pa bs k)
  | dm_wf_fence k : dm_wf k -> dm_wf (DFence k).

(* ---------------------------------------------------------------------- *)
(* 3. The typed read / write helpers.                                       *)
(*                                                                         *)
(*    [dread_word] is one [view_word] of the model: [run_dm] answers it     *)
(*    with exactly [view_word mv pa n], BY CONVERSION.                      *)
(* ---------------------------------------------------------------------- *)

Definition dread_word {A : Type} (pa : Arch.pa) (n : N) (aq : bool)
    (k : bv (8 * n) -> DM A) : DM A :=
  DRead pa (N.to_nat n) aq (fun bs => k (Z_to_bv (8 * n) (assemble_bytes bs))).

(* the little-endian bytes of an [n]-byte field, i.e. what [write_bytes]
   puts in memory *)
Definition wbytes (n : N) {w : N} (val : bv w) : list (bv 8) :=
  (fun j : nat => nth_byte val j) <$> seq 0 (N.to_nat n).

Definition dwrite_word {A : Type} (pa : Arch.pa) (n : N) {w : N} (val : bv w)
    (k : DM A) : DM A := DWrite pa (wbytes n val) k.

(* a data transfer of zero bytes is no event at all *)
Definition dread_data {A : Type} (pa : Arch.pa) (n : nat)
    (k : list (bv 8) -> DM A) : DM A :=
  match n with
  | O => k []
  | S n' => DRead pa (S n') false k
  end.

Definition dwrite_data {A : Type} (pa : Arch.pa) (bs : list (bv 8))
    (k : DM A) : DM A :=
  match bs with
  | [] => k
  | b :: bs' => DWrite pa (b :: bs') k
  end.

(* the write-list counterpart of [dwrite_data] *)
Definition wcons (pa : Arch.pa) (bs : list (bv 8))
    (ws : list (Arch.pa * list (bv 8))) : list (Arch.pa * list (bv 8)) :=
  match bs with
  | [] => ws
  | b :: bs' => (pa, b :: bs') :: ws
  end.

(* the three virtqueue structures the model reads, as device reads *)
Definition dread_avail_idx (c : virtio_cfg) (k : bv 16 -> DM dres) : DM dres :=
  dread_word (pa_off (vc_avail c) vq_idx_off) 2 true k.

Definition dread_avail_ring (c : virtio_cfg) (i : bv 16)
    (k : bv 16 -> DM dres) : DM dres :=
  dread_word (pa_off (vc_avail c)
                (vq_avail_ring_off
                 + 2 * (bv_unsigned i mod bv_unsigned (vc_qnum c)))) 2 false k.

Definition dread_desc (c : virtio_cfg) (i : Z) (k : vq_desc -> DM dres)
  : DM dres :=
  dread_word (pa_off (vc_desc c) (vq_desc_size * i)) 8 false (fun a =>
  dread_word (pa_off (pa_off (vc_desc c) (vq_desc_size * i)) 8) 4 false (fun l =>
  dread_word (pa_off (pa_off (vc_desc c) (vq_desc_size * i)) 12) 2 false (fun f =>
  dread_word (pa_off (pa_off (vc_desc c) (vq_desc_size * i)) 14) 2 false (fun nx =>
  k (VqDesc a l f nx))))).

(* ---------------------------------------------------------------------- *)
(* 4. The flat runner.                                                      *)
(* ---------------------------------------------------------------------- *)

Fixpoint run_dm {A : Type} (mv : vmem) (p : DM A)
  : A * list (Arch.pa * list (bv 8)) :=
  match p with
  | DRet a => (a, [])
  | DRead pa n _ k => run_dm mv (k (view_bytes mv pa n))
  | DWrite pa bs k => let '(a, ws) := run_dm mv k in (a, (pa, bs) :: ws)
  | DFence k => run_dm mv k
  end.

Lemma run_dread_word {A : Type} (mv : vmem) (pa : Arch.pa) (n : N) (aq : bool)
    (k : bv (8 * n) -> DM A) :
  run_dm mv (dread_word pa n aq k) = run_dm mv (k (view_word mv pa n)).
Proof. reflexivity. Qed.

Lemma run_dread_data {A : Type} (mv : vmem) (pa : Arch.pa) (n : nat)
    (k : list (bv 8) -> DM A) :
  run_dm mv (dread_data pa n k) = run_dm mv (k (view_bytes mv pa n)).
Proof. destruct n; reflexivity. Qed.

Lemma run_dwrite_data {A : Type} (mv : vmem) (pa : Arch.pa) (bs : list (bv 8))
    (k : DM A) :
  run_dm mv (dwrite_data pa bs k)
  = ((run_dm mv k).1, wcons pa bs (run_dm mv k).2).
Proof.
  destruct bs as [|b bs']; cbn [dwrite_data wcons run_dm];
    destruct (run_dm mv k); reflexivity.
Qed.

Lemma run_dread_avail_idx (mv : vmem) (c : virtio_cfg) (k : bv 16 -> DM dres) :
  run_dm mv (dread_avail_idx c k) = run_dm mv (k (avail_idx_at c mv)).
Proof. reflexivity. Qed.

Lemma run_dread_avail_ring (mv : vmem) (c : virtio_cfg) (i : bv 16)
    (k : bv 16 -> DM dres) :
  run_dm mv (dread_avail_ring c i k) = run_dm mv (k (avail_ring_at c mv i)).
Proof. reflexivity. Qed.

Lemma run_dread_desc (mv : vmem) (c : virtio_cfg) (i : Z)
    (k : vq_desc -> DM dres) :
  run_dm mv (dread_desc c i k) = run_dm mv (k (desc_at c mv i)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 5. The flat memory a write LIST denotes: later writes win.               *)
(* ---------------------------------------------------------------------- *)

Definition dm_writes_map (ws : list (Arch.pa * list (bv 8)))
  : gmap Arch.pa (bv 8) :=
  foldl (fun m w => write_byte_list m w.1 w.2) ∅ ws.

(* one write, as (address, byte) pairs *)
Definition wpairs (w : Arch.pa * list (bv 8)) : list (Arch.pa * bv 8) :=
  imap (fun j b => (pa_add w.1 j, b)) w.2.

(* the whole write list, LATEST FIRST -- the order [list_to_map] wants *)
Definition dm_writes_flat (ws : list (Arch.pa * list (bv 8)))
  : list (Arch.pa * bv 8) := concat (rev (wpairs <$> ws)).

(* THE side condition of the write-map half of the equivalence: the
   program's writes touch pairwise distinct addresses. *)
Definition dm_writes_disj (ws : list (Arch.pa * list (bv 8))) : Prop :=
  NoDup ((dm_writes_flat ws).*1).

(* -- [write_byte_list] / [write_bytes] as (address, byte) association lists,
      which is what makes the ORDER of two writes a [Permutation] question -- *)

Lemma ins_list_union (m : gmap Arch.pa (bv 8)) (l : list (Arch.pa * bv 8)) :
  foldr (fun p acc => <[ p.1 := p.2 ]> acc) m l = list_to_map l ∪ m.
Proof.
  induction l as [|[k x] l IH].
  - cbn [foldr]. rewrite list_to_map_nil. by rewrite (left_id_L _ _).
  - cbn [foldr]. rewrite IH, list_to_map_cons. by rewrite insert_union_l.
Qed.

Lemma insert_list_to_map (m : gmap Arch.pa (bv 8)) (k : Arch.pa) (x : bv 8) :
  <[ k := x ]> m = list_to_map [(k, x)] ∪ m.
Proof. exact (ins_list_union m [(k, x)]). Qed.

Lemma wpairs_imap (pa : Arch.pa) (bs : list (bv 8)) :
  wpairs (pa, bs)
  = (fun jb : nat * bv 8 => (pa_add pa jb.1, jb.2)) <$> imap (fun j b => (j, b)) bs.
Proof.
  unfold wpairs. cbn [fst snd]. rewrite fmap_imap.
  apply imap_ext. intros; reflexivity.
Qed.

Lemma write_byte_list_union (m : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (bs : list (bv 8)) :
  write_byte_list m pa bs = list_to_map (wpairs (pa, bs)) ∪ m.
Proof.
  rewrite <- ins_list_union, wpairs_imap, foldr_fmap. reflexivity.
Qed.

Lemma imap_seq0 {B : Type} (g : nat -> nat -> B) (n : nat) :
  imap g (seq 0 n) = (fun j : nat => g j j) <$> seq 0 n.
Proof.
  apply list_eq. intro i. rewrite list_lookup_imap, list_lookup_fmap.
  destruct (decide (i < n)%nat) as [Hi|Hi].
  - by rewrite (lookup_seq_lt 0 n i Hi).
  - rewrite (lookup_seq_ge 0 n i); [reflexivity|lia].
Qed.

(* a machine-word field store IS a byte-list store *)
Lemma write_bytes_byte_list {w : N} (m : gmap Arch.pa (bv 8)) (pa : Arch.pa)
    (n : N) (val : bv w) :
  write_bytes m pa n val = write_byte_list m pa (wbytes n val).
Proof.
  unfold write_byte_list, wbytes.
  rewrite imap_fmap, imap_seq0, foldr_fmap. reflexivity.
Qed.

Lemma dm_writes_map_flat (ws : list (Arch.pa * list (bv 8))) :
  dm_writes_map ws = list_to_map (dm_writes_flat ws).
Proof.
  unfold dm_writes_map, dm_writes_flat.
  induction ws as [|w ws IH] using rev_ind; [reflexivity|].
  destruct w as [pa bs].
  rewrite foldl_app. cbn [foldl fst snd].
  rewrite IH, fmap_app, rev_app_distr. cbn [fmap list_fmap rev app concat].
  rewrite list_to_map_app. apply write_byte_list_union.
Qed.

(* -- permutation transfer -- *)

Lemma fmap_perm {A B : Type} (f : A -> B) (l1 l2 : list A) :
  l1 ≡ₚ l2 -> f <$> l1 ≡ₚ f <$> l2.
Proof.
  induction 1 as [| x l1 l2 _ IH | x y l | l1 l2 l3 _ IH1 _ IH2]; cbn.
  - reflexivity.
  - by apply perm_skip.
  - apply perm_swap.
  - by etrans.
Qed.

Lemma concat_perm {A : Type} (L1 L2 : list (list A)) :
  L1 ≡ₚ L2 -> concat L1 ≡ₚ concat L2.
Proof.
  induction 1 as [| x L1 L2 _ IH | x y L | L1 L2 L3 _ IH1 _ IH2]; cbn [concat].
  - reflexivity.
  - by apply Permutation_app_head.
  - rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
  - by etrans.
Qed.

Lemma dm_writes_flat_perm (ws1 ws2 : list (Arch.pa * list (bv 8))) :
  ws1 ≡ₚ ws2 -> dm_writes_flat ws1 ≡ₚ dm_writes_flat ws2.
Proof.
  intro Hp. unfold dm_writes_flat. apply concat_perm.
  etrans; [symmetry; apply Permutation_rev|].
  etrans; [apply (fmap_perm _ _ _ Hp)|]. apply Permutation_rev.
Qed.

(* THE reordering lemma: on pairwise distinct addresses the order of the
   writes does not matter, so the model's map and the program's ordered
   writes may differ in order and still denote the same memory. *)
Lemma dm_writes_map_perm (ws1 ws2 : list (Arch.pa * list (bv 8))) :
  ws1 ≡ₚ ws2 -> dm_writes_disj ws1 -> dm_writes_map ws1 = dm_writes_map ws2.
Proof.
  intros Hp Hnd. rewrite !dm_writes_map_flat.
  apply list_to_map_proper; [exact Hnd | by apply dm_writes_flat_perm].
Qed.

(* ---------------------------------------------------------------------- *)
(* 6. The device program.                                                  *)
(*                                                                         *)
(*    Structurally [virtio_req_step] / [virtio_stalled], node by node: one  *)
(*    [DRead] per [view_word] / [view_bytes] the model performs, in the     *)
(*    model's own order, and every [chain_at] failure branch is [DWild].    *)
(* ---------------------------------------------------------------------- *)

(* the status byte the model reports -- [virtio_complete]'s [st] *)
Definition vstatus (r : vio_req) : Z :=
  if (bv_unsigned (vr_type r) =? virtio_blk_t_in)
     || (bv_unsigned (vr_type r) =? virtio_blk_t_out)
  then virtio_blk_s_ok else virtio_blk_s_unsupp.

(* THE COMMIT DELTA.  [v] is the state the burst STARTED at, [vc] the state
   at commit time: the configuration and the ISR come from [vc] (a hart's
   MMIO writes during the burst are not clobbered), the two ring counters are
   the +1 of what the burst consumed, and [dkf] is the disk image update. *)
Definition vdelta (v : virtio_state) (dkf : (Z -> bv 8) -> (Z -> bv 8))
  : virtio_state -> virtio_state :=
  fun vc => VirtioState (v_cfg vc)
              (bv_or (v_isr vc) (Z_to_bv 32 vio_isr_used_buffer))
              (bv_add (v_seen v) (Z_to_bv 16 1))
              (bv_add (v_used_idx v) (Z_to_bv 16 1))
              (dkf (v_disk vc)).

(* the disk-image update the FLAT run computes (a disk WRITE only) *)
Definition vdkf (v : virtio_state) (mv : vmem) (r : vio_req)
  : (Z -> bv 8) -> (Z -> bv 8) :=
  if bv_unsigned (vr_type r) =? virtio_blk_t_in then (fun dk => dk)
  else if bv_unsigned (vr_type r) =? virtio_blk_t_out then
    (fun dk => disk_write dk (bv_unsigned (vr_sector r) * virtio_sector_size)
                 (view_bytes mv (vr_buf r) (Z.to_nat (bv_unsigned (vr_len r)))))
  else (fun dk => dk).

(* the bytes the device stores into the driver's buffer (a disk READ only) *)
Definition vdata (v : virtio_state) (r : vio_req) : list (bv 8) :=
  if bv_unsigned (vr_type r) =? virtio_blk_t_in
  then disk_read (v_disk v) (bv_unsigned (vr_sector r) * virtio_sector_size)
                 (Z.to_nat (bv_unsigned (vr_len r)))
  else [].

Definition vused_elem (c : virtio_cfg) (ui : bv 16) : Arch.pa :=
  pa_off (vc_used c) (vq_used_ring_off + vq_used_elem_size
                        * (bv_unsigned ui mod bv_unsigned (vc_qnum c))).

(* the used-ring report: element .id, element .len, FENCE, ->idx *)
Definition dused_tail (c : virtio_cfg) (ui : bv 16) (r : vio_req) (k : DM dres)
  : DM dres :=
  dwrite_word (vused_elem c ui) 4 (Z_to_bv 32 (bv_unsigned (vr_head r)))
    (dwrite_word (pa_off (vused_elem c ui) 4) 4 (vr_len r)
      (DFence (dwrite_word (pa_off (vc_used c) vq_idx_off) 2
                 (bv_add ui (Z_to_bv 16 1)) k))).

Definition dtail (v : virtio_state) (r : vio_req)
    (dkf : (Z -> bv 8) -> (Z -> bv 8)) : DM dres :=
  DWrite (vr_status r) [Z_to_bv 8 (vstatus r)]
    (dused_tail (v_cfg v) (v_used_idx v) r (DRet (DDone (vdelta v dkf)))).

Definition dcomplete (v : virtio_state) (r : vio_req) : DM dres :=
  if bv_unsigned (vr_type r) =? virtio_blk_t_in then
    (* read the disk: the device WRITES the driver's buffer, first *)
    dwrite_data (vr_buf r)
      (disk_read (v_disk v) (bv_unsigned (vr_sector r) * virtio_sector_size)
                 (Z.to_nat (bv_unsigned (vr_len r))))
      (dtail v r (fun dk => dk))
  else if bv_unsigned (vr_type r) =? virtio_blk_t_out then
    (* write the disk: the device READS the driver's buffer, before storing *)
    dread_data (vr_buf r) (Z.to_nat (bv_unsigned (vr_len r))) (fun dat =>
      dtail v r (fun dk => disk_write dk
                   (bv_unsigned (vr_sector r) * virtio_sector_size) dat))
  else (* unsupported: no data transfer, status UNSUPP, same tail *)
    dtail v r (fun dk => dk).

Definition virtio_prog (v : virtio_state) : DM dres :=
  if virtio_live (v_cfg v) then
    dread_avail_idx (v_cfg v) (fun ai =>
    if bv_unsigned ai =? bv_unsigned (v_seen v) then DRet DIdle else
    dread_avail_ring (v_cfg v) (v_seen v) (fun h =>
    if negb (bv_unsigned h <? bv_unsigned (vc_qnum (v_cfg v))) then DRet DWild else
    dread_desc (v_cfg v) (bv_unsigned h) (fun d0 =>
    if negb (vd_has d0 vring_desc_f_next) then DRet DWild else
    if negb (bv_unsigned (vd_next d0) <? bv_unsigned (vc_qnum (v_cfg v)))
    then DRet DWild else
    dread_desc (v_cfg v) (bv_unsigned (vd_next d0)) (fun d1 =>
    if negb (vd_has d1 vring_desc_f_next) then DRet DWild else
    if negb (bv_unsigned (vd_next d1) <? bv_unsigned (vc_qnum (v_cfg v)))
    then DRet DWild else
    dread_desc (v_cfg v) (bv_unsigned (vd_next d1)) (fun d2 =>
    if vd_has d2 vring_desc_f_next then DRet DWild else
    dread_word (vd_addr d0) 4 false (fun ty =>
    dread_word (pa_off (vd_addr d0) 8) 8 false (fun sec =>
    dcomplete v (VioReq h ty sec (vd_addr d1) (vd_len d1) (vd_addr d2)))))))))
  else DRet DIdle.

(* -- the write LISTS, in the program's order and in the model's order -- *)

Definition vused_ws (c : virtio_cfg) (ui : bv 16) (r : vio_req)
  : list (Arch.pa * list (bv 8)) :=
  [ (vused_elem c ui, wbytes 4 (Z_to_bv 32 (bv_unsigned (vr_head r))));
    (pa_off (vused_elem c ui) 4, wbytes 4 (vr_len r));
    (pa_off (vc_used c) vq_idx_off, wbytes 2 (bv_add ui (Z_to_bv 16 1))) ].

Definition vprog_ws (v : virtio_state) (r : vio_req)
  : list (Arch.pa * list (bv 8)) :=
  wcons (vr_buf r) (vdata v r)
    ((vr_status r, [Z_to_bv 8 (vstatus r)])
     :: vused_ws (v_cfg v) (v_used_idx v) r).

(* the same writes in the precedence order [virtio_complete] nests them in *)
Definition vmodel_ws (v : virtio_state) (r : vio_req)
  : list (Arch.pa * list (bv 8)) :=
  vused_ws (v_cfg v) (v_used_idx v) r
  ++ (vr_status r, [Z_to_bv 8 (vstatus r)]) :: wcons (vr_buf r) (vdata v r) [].

Lemma run_dtail (mv : vmem) (v : virtio_state) (r : vio_req)
    (dkf : (Z -> bv 8) -> (Z -> bv 8)) :
  run_dm mv (dtail v r dkf)
  = (DDone (vdelta v dkf),
     (vr_status r, [Z_to_bv 8 (vstatus r)])
     :: vused_ws (v_cfg v) (v_used_idx v) r).
Proof. reflexivity. Qed.

Lemma run_dcomplete (mv : vmem) (v : virtio_state) (r : vio_req) :
  run_dm mv (dcomplete v r) = (DDone (vdelta v (vdkf v mv r)), vprog_ws v r).
Proof.
  unfold dcomplete, vdkf, vprog_ws, vdata.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in) eqn:Hin.
  - rewrite run_dwrite_data, run_dtail. reflexivity.
  - destruct (bv_unsigned (vr_type r) =? virtio_blk_t_out) eqn:Hout.
    + rewrite run_dread_data. cbv beta. rewrite run_dtail. reflexivity.
    + rewrite run_dtail. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 7. THE EQUIVALENCE: running the program at a flat memory IS the model's  *)
(*    autonomous step.                                                     *)
(* ---------------------------------------------------------------------- *)

Local Ltac dwild :=
  match goal with
  | |- context [ if ?b then @DRet dres DWild else _ ] => destruct b eqn:?
  end; cbn [negb andb];
  [ right; left; split; [reflexivity | split; reflexivity ] | ].

(* The workhorse: the flat run of [virtio_prog v] is one of exactly three
   shapes, and each is pinned to the model's own test. *)
Lemma run_virtio_prog (v : virtio_state) (mv : vmem) :
  (virtio_pending v mv = false /\ run_dm mv (virtio_prog v) = (DIdle, []))
  \/ (virtio_pending v mv = true
      /\ chain_at (v_cfg v) mv (v_seen v) = None
      /\ run_dm mv (virtio_prog v) = (DWild, []))
  \/ (exists r, virtio_pending v mv = true
      /\ req_at (v_cfg v) mv (v_seen v) = Some r
      /\ run_dm mv (virtio_prog v)
         = (DDone (vdelta v (vdkf v mv r)), vprog_ws v r)).
Proof.
  unfold virtio_prog, virtio_pending, req_at, chain_at; cbv zeta.
  destruct (virtio_live (v_cfg v)) eqn:Hlive; cbn [andb].
  2:{ left; split; reflexivity. }
  rewrite run_dread_avail_idx; cbv beta.
  destruct (bv_unsigned (avail_idx_at (v_cfg v) mv) =? bv_unsigned (v_seen v))
    eqn:Hai; cbn [negb].
  { left; split; reflexivity. }
  rewrite run_dread_avail_ring; cbv beta.
  dwild.
  rewrite run_dread_desc; cbv beta.
  dwild. dwild.
  rewrite run_dread_desc; cbv beta.
  dwild. dwild.
  rewrite run_dread_desc; cbv beta.
  dwild.
  rewrite run_dread_word; cbv beta.
  rewrite run_dread_word; cbv beta.
  rewrite run_dcomplete.
  right; right. eexists.
  split; [reflexivity | split; [reflexivity | reflexivity]].
Qed.

(* -- the model's map, in the program's write order -- *)

Lemma dm_writes_map_app (ws1 ws2 : list (Arch.pa * list (bv 8))) :
  dm_writes_map (ws1 ++ ws2)
  = foldl (fun m w => write_byte_list m w.1 w.2) (dm_writes_map ws1) ws2.
Proof. unfold dm_writes_map. apply foldl_app. Qed.

Lemma write_byte_list_single (m : gmap Arch.pa (bv 8)) (pa : Arch.pa) (b : bv 8) :
  write_byte_list m pa [b] = <[ pa := b ]> m.
Proof.
  unfold write_byte_list. cbn [imap foldr fst snd]. by rewrite vp_pa_add_0.
Qed.

Lemma foldl_wcons (m : gmap Arch.pa (bv 8)) (pa : Arch.pa) (bs : list (bv 8)) :
  foldl (fun m w => write_byte_list m w.1 w.2) m (wcons pa bs [])
  = write_byte_list m pa bs.
Proof. destruct bs; reflexivity. Qed.

Lemma vused_ws_map (c : virtio_cfg) (ui : bv 16) (r : vio_req) :
  dm_writes_map (vused_ws c ui r) = virtio_used_writes c ui r.
Proof.
  unfold dm_writes_map, vused_ws, virtio_used_writes, vused_elem; cbv zeta.
  cbn [foldl fst snd]. by rewrite !write_bytes_byte_list.
Qed.

Lemma virtio_complete_state (v : virtio_state) (mv : vmem) (r : vio_req) :
  (virtio_complete v mv r).1 = vdelta v (vdkf v mv r) v.
Proof.
  unfold virtio_complete, vdelta, vdkf; cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in); [reflexivity|].
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_out); reflexivity.
Qed.

Lemma virtio_complete_writes (v : virtio_state) (mv : vmem) (r : vio_req) :
  (virtio_complete v mv r).2 = dm_writes_map (vmodel_ws v r).
Proof.
  unfold vmodel_ws. rewrite dm_writes_map_app, vused_ws_map.
  cbn [foldl fst snd]. rewrite foldl_wcons, write_byte_list_single.
  unfold virtio_complete, vstatus, vdata; cbv zeta.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in); cbn [orb];
    [reflexivity|].
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_out); reflexivity.
Qed.

(* the ONE place the design's write order and the model's map nesting part
   company: they are permutations of each other, nothing more *)
Lemma vmodel_vprog_perm (v : virtio_state) (r : vio_req) :
  vmodel_ws v r ≡ₚ vprog_ws v r.
Proof.
  unfold vmodel_ws, vprog_ws. destruct (vdata v r) as [|b bs]; cbn [wcons].
  - apply Permutation_app_comm.
  - etrans;
      [ apply (Permutation_app_comm (vused_ws (v_cfg v) (v_used_idx v) r)
                 [(vr_status r, [Z_to_bv 8 (vstatus r)]); (vr_buf r, b :: bs)]) | ].
    cbn [app]. apply perm_swap.
Qed.

Lemma vprog_writes_map (v : virtio_state) (mv : vmem) (r : vio_req) :
  dm_writes_disj (vprog_ws v r) ->
  (virtio_complete v mv r).2 = dm_writes_map (vprog_ws v r).
Proof.
  intro Hnd. rewrite virtio_complete_writes. symmetry.
  apply dm_writes_map_perm; [symmetry; apply vmodel_vprog_perm | exact Hnd].
Qed.

Lemma virtio_complete_pair (v : virtio_state) (mv : vmem) (r : vio_req) :
  dm_writes_disj (vprog_ws v r) ->
  virtio_complete v mv r
  = (vdelta v (vdkf v mv r) v, dm_writes_map (vprog_ws v r)).
Proof.
  intro H. destruct (virtio_complete v mv r) as [cv cw] eqn:Hc. f_equal.
  - rewrite <- virtio_complete_state, Hc. reflexivity.
  - rewrite <- (vprog_writes_map v mv r H), Hc. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 8. The four theorems.                                                    *)
(* ---------------------------------------------------------------------- *)

(* THE side condition of the write-map half (see the FINDING in the header):
   the program's writes touch pairwise distinct addresses. *)
Definition virtio_prog_disj (v : virtio_state) (mv : vmem) : Prop :=
  dm_writes_disj (run_dm mv (virtio_prog v)).2.

Theorem virtio_prog_req_step (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_prog_disj v mv ->
  (virtio_req_step v mv = Some (v', w) <->
   exists delta ws, run_dm mv (virtio_prog v) = (DDone delta, ws)
                    /\ v' = delta v /\ w = dm_writes_map ws).
Proof.
  intro Hdisj.
  destruct (run_virtio_prog v mv)
    as [[Hp Hr]|[[Hp [Hc Hr]]|[r [Hp [Hq Hr]]]]].
  - split.
    + unfold virtio_req_step. rewrite Hp. cbn [negb]. discriminate.
    + intros (delta & ws & Hrun & _). rewrite Hr in Hrun. discriminate.
  - split.
    + unfold virtio_req_step, req_at. rewrite Hp, Hc. cbn [negb]. discriminate.
    + intros (delta & ws & Hrun & _). rewrite Hr in Hrun. discriminate.
  - unfold virtio_prog_disj in Hdisj. rewrite Hr in Hdisj. cbn [snd] in Hdisj.
    split.
    + unfold virtio_req_step. rewrite Hp. cbn [negb]. rewrite Hq.
      intro H. injection H as H.
      exists (vdelta v (vdkf v mv r)), (vprog_ws v r).
      split; [exact Hr|]. split.
      * rewrite <- virtio_complete_state, H. reflexivity.
      * rewrite <- (vprog_writes_map v mv r Hdisj), H. reflexivity.
    + intros (delta & ws & Hrun & Hv' & Hw). rewrite Hrun in Hr.
      injection Hr as Hd Hws. subst delta ws.
      unfold virtio_req_step. rewrite Hp. cbn [negb]. rewrite Hq.
      rewrite (virtio_complete_pair v mv r Hdisj), Hv', Hw. reflexivity.
Qed.

Theorem virtio_prog_stalled (v : virtio_state) (mv : vmem) :
  virtio_stalled v mv = true <-> run_dm mv (virtio_prog v) = (DWild, []).
Proof.
  unfold virtio_stalled, virtio_chain_ok.
  destruct (run_virtio_prog v mv)
    as [[Hp Hr]|[[Hp [Hc Hr]]|[r [Hp [Hq Hr]]]]].
  - rewrite Hp, Hr. cbn [andb]. split; discriminate.
  - rewrite Hp, Hc, Hr. cbn [andb negb]. split; intros _; reflexivity.
  - rewrite Hp, Hr. unfold req_at in Hq.
    destruct (chain_at (v_cfg v) mv (v_seen v)) as [[[[h d0] d1] d2]|];
      [|discriminate].
    cbn [andb negb]. split; discriminate.
Qed.

Theorem virtio_prog_idle (v : virtio_state) (mv : vmem) :
  virtio_pending v mv = false <-> run_dm mv (virtio_prog v) = (DIdle, []).
Proof.
  destruct (run_virtio_prog v mv)
    as [[Hp Hr]|[[Hp [Hc Hr]]|[r [Hp [Hq Hr]]]]].
  - rewrite Hp, Hr. split; intros _; reflexivity.
  - rewrite Hp, Hr. split; discriminate.
  - rewrite Hp, Hr. split; discriminate.
Qed.

Theorem virtio_prog_trichotomy (v : virtio_state) (mv : vmem) :
  run_dm mv (virtio_prog v) = (DIdle, [])
  \/ run_dm mv (virtio_prog v) = (DWild, [])
  \/ exists delta ws, run_dm mv (virtio_prog v) = (DDone delta, ws).
Proof.
  destruct (run_virtio_prog v mv)
    as [[Hp Hr]|[[Hp [Hc Hr]]|[r [Hp [Hq Hr]]]]].
  - by left.
  - by right; left.
  - right; right. by exists (vdelta v (vdkf v mv r)), (vprog_ws v r).
Qed.

(* The STATE half of the equivalence needs no side condition at all. *)
Theorem virtio_prog_req_step_state (v : virtio_state) (mv : vmem)
    (v' : virtio_state) (w : gmap Arch.pa (bv 8)) :
  virtio_req_step v mv = Some (v', w) ->
  exists delta ws, run_dm mv (virtio_prog v) = (DDone delta, ws) /\ v' = delta v.
Proof.
  destruct (run_virtio_prog v mv)
    as [[Hp Hr]|[[Hp [Hc Hr]]|[r [Hp [Hq Hr]]]]].
  - unfold virtio_req_step. rewrite Hp. cbn [negb]. discriminate.
  - unfold virtio_req_step, req_at. rewrite Hp, Hc. cbn [negb]. discriminate.
  - unfold virtio_req_step. rewrite Hp. cbn [negb]. rewrite Hq.
    intro H. injection H as H.
    exists (vdelta v (vdkf v mv r)), (vprog_ws v r).
    split; [exact Hr|]. rewrite <- virtio_complete_state, H. reflexivity.
Qed.

Theorem virtio_prog_done_step (v : virtio_state) (mv : vmem)
    (delta : virtio_state -> virtio_state) (ws : list (Arch.pa * list (bv 8))) :
  run_dm mv (virtio_prog v) = (DDone delta, ws) ->
  exists w, virtio_req_step v mv = Some (delta v, w).
Proof.
  destruct (run_virtio_prog v mv)
    as [[Hp Hr]|[[Hp [Hc Hr]]|[r [Hp [Hq Hr]]]]].
  - rewrite Hr. discriminate.
  - rewrite Hr. discriminate.
  - rewrite Hr. intro H. injection H as Hd _.
    unfold virtio_req_step. rewrite Hp. cbn [negb]. rewrite Hq.
    exists (virtio_complete v mv r).2.
    destruct (virtio_complete v mv r) as [cv cw] eqn:Hc.
    assert (Hcv : cv = vdelta v (vdkf v mv r) v).
    { rewrite <- virtio_complete_state, Hc. reflexivity. }
    rewrite Hcv, <- Hd. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 9. Structural well-formedness of the device program.                     *)
(*                                                                         *)
(*    Every [DRead] reads at least one byte and every [DWrite] carries at   *)
(*    least one byte, at ANY answers -- not just the ones a flat memory     *)
(*    gives.  The language's load / store arms require both.                *)
(* ---------------------------------------------------------------------- *)

Lemma wbytes_nonempty {w : N} (n : N) (val : bv w) :
  (0 < n)%N -> wbytes n val <> [].
Proof.
  intros Hn Hc. apply (f_equal length) in Hc.
  unfold wbytes in Hc. rewrite length_fmap, length_seq in Hc.
  cbn [length] in Hc. lia.
Qed.

Lemma dm_wf_dread_word {A : Type} (pa : Arch.pa) (n : N) (aq : bool)
    (k : bv (8 * n) -> DM A) :
  (0 < n)%N -> (forall x, dm_wf (k x)) -> dm_wf (dread_word pa n aq k).
Proof. intros Hn Hk. constructor; [lia|]. intros bs. apply Hk. Qed.

Lemma dm_wf_dwrite_word {A : Type} (pa : Arch.pa) (n : N) {w : N} (val : bv w)
    (k : DM A) :
  (0 < n)%N -> dm_wf k -> dm_wf (dwrite_word pa n val k).
Proof. intros Hn Hk. constructor; [by apply wbytes_nonempty|exact Hk]. Qed.

Lemma dm_wf_dread_data {A : Type} (pa : Arch.pa) (n : nat)
    (k : list (bv 8) -> DM A) :
  (forall bs, dm_wf (k bs)) -> dm_wf (dread_data pa n k).
Proof.
  intro Hk. destruct n as [|n']; cbn [dread_data]; [apply Hk|].
  constructor; [lia|exact Hk].
Qed.

Lemma dm_wf_dwrite_data {A : Type} (pa : Arch.pa) (bs : list (bv 8))
    (k : DM A) :
  dm_wf k -> dm_wf (dwrite_data pa bs k).
Proof.
  intro Hk. destruct bs as [|b bs']; cbn [dwrite_data]; [exact Hk|].
  constructor; [discriminate|exact Hk].
Qed.

Lemma dm_wf_dread_desc (c : virtio_cfg) (i : Z) (k : vq_desc -> DM dres) :
  (forall d, dm_wf (k d)) -> dm_wf (dread_desc c i k).
Proof.
  intro Hk. unfold dread_desc.
  apply dm_wf_dread_word; [lia|intro a]; cbv beta.
  apply dm_wf_dread_word; [lia|intro l]; cbv beta.
  apply dm_wf_dread_word; [lia|intro f]; cbv beta.
  apply dm_wf_dread_word; [lia|intro nx]; cbv beta.
  apply Hk.
Qed.

Lemma dm_wf_dtail (v : virtio_state) (r : vio_req)
    (dkf : (Z -> bv 8) -> (Z -> bv 8)) : dm_wf (dtail v r dkf).
Proof.
  unfold dtail, dused_tail. constructor; [discriminate|].
  apply dm_wf_dwrite_word; [lia|]. apply dm_wf_dwrite_word; [lia|].
  constructor. apply dm_wf_dwrite_word; [lia|]. constructor.
Qed.

Lemma dm_wf_dcomplete (v : virtio_state) (r : vio_req) :
  dm_wf (dcomplete v r).
Proof.
  unfold dcomplete.
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_in).
  { apply dm_wf_dwrite_data, dm_wf_dtail. }
  destruct (bv_unsigned (vr_type r) =? virtio_blk_t_out).
  { apply dm_wf_dread_data. intro dat. cbv beta. apply dm_wf_dtail. }
  apply dm_wf_dtail.
Qed.

Local Ltac dsplit :=
  match goal with
  | |- dm_wf (if ?b then _ else _) => destruct b
  end.

Theorem virtio_prog_wf (v : virtio_state) : dm_wf (virtio_prog v).
Proof.
  unfold virtio_prog, dread_avail_idx, dread_avail_ring.
  dsplit; [|constructor].
  apply dm_wf_dread_word; [lia|intro ai]; cbv beta.
  dsplit; [constructor|].
  apply dm_wf_dread_word; [lia|intro h]; cbv beta.
  dsplit; [constructor|].
  apply dm_wf_dread_desc; intro d0; cbv beta.
  dsplit; [constructor|]. dsplit; [constructor|].
  apply dm_wf_dread_desc; intro d1; cbv beta.
  dsplit; [constructor|]. dsplit; [constructor|].
  apply dm_wf_dread_desc; intro d2; cbv beta.
  dsplit; [constructor|].
  apply dm_wf_dread_word; [lia|intro ty]; cbv beta.
  apply dm_wf_dread_word; [lia|intro sec]; cbv beta.
  apply dm_wf_dcomplete.
Qed.
