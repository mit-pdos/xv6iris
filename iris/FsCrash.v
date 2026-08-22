(* ====================================================================== *)
(* FsCrash.v -- THE FILE SYSTEM'S CRASH PREDICATE [P_fs]: the pure         *)
(* recovery relation, the ghosts that carry it across a power cycle, and   *)
(* the escrow [P_fs] itself -- the value the adequacy client will fix the  *)
(* fixed layer's [RiscvPtsto.riscv_crash_pred] at.                         *)
(*                                                                        *)
(* Design: claude-notes/design/fs-log.md, "Stage 4 -- the crash side" and  *)
(* its stage-4 architecture, items 3-6; claude-notes/design/crash.md for   *)
(* [crash_inv]/[riscv_crash_pred] and the [Pc] adequacy parameter.         *)
(*                                                                        *)
(* WHAT IS IN HERE, IN ONE PARAGRAPH.  The FS's durable meaning is a       *)
(* relation between two things: the PHYSICAL disk (call it [P] -- the      *)
(* block view of the machine's own [v_disk]) and the COMMITTED state       *)
(* ([D] -- what recovery would produce from [P] right now).  [fs_recovery] *)
(* is that relation, read off [P] alone: decode the on-disk log header at  *)
(* [logstart]; if it says [n] blocks with write set [W], then [D] is the   *)
(* home blocks of [P] with [W[i]] overwritten by log slot [i]; at [n = 0]  *)
(* it is just the home blocks.  [P_fs] is an escrow over a pure record     *)
(* (P, D, the committed history) asserting exactly that, plus the halves   *)
(* of the ghosts that make it usable: a [ghost_var] TIE whose other half   *)
(* mirrors the machine's [v_disk] from inside [state_interp], and a        *)
(* MONO-LIST of committed [D]s whose persistent lower bounds are the       *)
(* durability receipts [sys_sync] will hand out.                          *)
(*                                                                        *)
(* THE TIE IS NOW THE MACHINE LAYER'S (phase C2a, LANDED).                 *)
(* [RiscvPtsto.riscv_crash_pred] is INDEXED by the disk image and           *)
(* [crash_inv]'s body is [∃ dk, disk_tie dk ∗ riscv_crash_pred dk], so the  *)
(* tie's two halves are [state_interp]'s conjunct and the invariant's own   *)
(* sibling -- the DMA completion holds both and moves them mechanically.    *)
(* [P_fs] therefore does NOT own a tie half: it is a PREDICATE ON [dk],     *)
(* and the machine layer guarantees that [dk] is the real disk.  The block  *)
(* view [fs_blocks dk] is where the FS's own vocabulary starts.            *)
(*                                                                          *)
(* WHAT IS DELIBERATELY *NOT* IN HERE (phases C2b/D):                       *)
(*  - the generation SWAP protocol (the checked-out arm's era binding) --  *)
(*    the arm exists here, the protocol is phase D's.                      *)
(*  - the per-call-site permit fupds (each WAL write kind re-establishing  *)
(*    [fs_rec_wf] at the new [P]) -- phase C2's.                           *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import own ghost_var ghost_map mono_nat invariants.
Require Import RiscvModelBytes.
Require Import RiscvLang.   (* [GenId]/[gen_id], for the seam section's permit *)
Require Import VirtioModel.
Require Import RiscvPtsto.
Require Import WpLock.
Require Export BioDefs.  (* preserve [BSIZE] for existing importers *)
Require Export LogDefs.  (* [hdr_dec]/[le_word], the mirror readings *)
Require Export FsWf.  (* [fs_durable_wf], the P_wf conjunct (ruling 2) *)
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
Local Open Scope Z_scope.

(* ====================================================================== *)
(* 1. THE PURE LAYER.                                                     *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* 1a. The BLOCK VIEW of the disk.                                         *)
(*                                                                         *)
(* The machine's disk is a TOTAL byte function [v_disk : Z -> bv 8]        *)
(* (VirtioModel.v).  Everything above the driver talks in 1024-byte        *)
(* BLOCKS, so the FS's view of the disk is the total block function        *)
(* below -- block [b] is the [BSIZE] bytes at [b * BSIZE].                 *)
(*                                                                         *)
(* TOTAL, not a [gmap] over a range, and that is a deliberate choice: the  *)
(* other half of the tie is destined for [state_interp], which lives in    *)
(* [RiscvPtsto.v] -- BELOW every FS constant.  A finite block map would    *)
(* need the FS's disk size down there (design/fs-log.md's own rule: no FS  *)
(* constant appears below [SystemAdequacy]), or a fresh fixed-layer        *)
(* parameter.  A total function needs neither, and the places that really  *)
(* are finite -- the durable home map [fr_D], the history -- stay [gmap].  *)
(* When the [state_interp] conjunct lands, [fs_blocks] moves down to       *)
(* VirtioModel.v verbatim (it is iris-free and uses only [disk_read]).     *)
(* ---------------------------------------------------------------------- *)

Definition fs_blocks (dk : Z -> bv 8) : Z -> list (bv 8) :=
  fun b => disk_read dk (b * Z.of_nat BSIZE) BSIZE.

Lemma fs_blocks_length (dk : Z -> bv 8) (b : Z) :
  length (fs_blocks dk b) = BSIZE.
Proof. rewrite /fs_blocks /disk_read length_fmap length_seq //. Qed.

(* a byte outside the written range reads through *)
Lemma disk_write_out (dk : Z -> bv 8) (off : Z) (bs : list (bv 8)) (a : Z) :
  a < off \/ off + Z.of_nat (length bs) <= a ->
  disk_write dk off bs a = dk a.
Proof.
  intros [Hlt|Hge]; rewrite /disk_write.
  - rewrite (proj2 (Z.leb_gt off a)); [reflexivity|lia].
  - destruct (off <=? a) eqn:Hle; [|reflexivity].
    rewrite (lookup_ge_None_2 bs (Z.to_nat (a - off))); [reflexivity|].
    apply Z.leb_le in Hle. lia.
Qed.

(* THE TWO FACTS THE DMA COMPLETION'S MECHANICAL TIE UPDATE NEEDS (C2): a
   one-block write moves exactly that block of the view. *)
Lemma fs_blocks_write_eq (dk : Z -> bv 8) (b : Z) (bs : list (bv 8)) :
  length bs = BSIZE ->
  fs_blocks (disk_write dk (b * Z.of_nat BSIZE) bs) b = bs.
Proof.
  intros Hlen. rewrite /fs_blocks.
  pose proof (disk_read_write dk (b * Z.of_nat BSIZE) bs) as H.
  rewrite Hlen in H. exact H.
Qed.

Lemma fs_blocks_write_ne (dk : Z -> bv 8) (b c : Z) (bs : list (bv 8)) :
  length bs = BSIZE -> c <> b ->
  fs_blocks (disk_write dk (b * Z.of_nat BSIZE) bs) c = fs_blocks dk c.
Proof.
  intros Hlen Hne. rewrite /fs_blocks /disk_read.
  apply list_fmap_ext. intros j x Hx.
  apply lookup_seq in Hx as [-> Hjlt].
  apply disk_write_out. rewrite Hlen /BSIZE. rewrite /BSIZE in Hjlt.
  destruct (Z.lt_total c b) as [Hlt|[->|Hgt]]; [| congruence |]; [left|right]; lia.
Qed.

(* -- SUB-BLOCK (SECTOR) WRITES (claude-notes/projects/sector-atomic-disk.md).
      A 512-byte sector write lands inside ONE block and splices its content;
      the two facts below are what every torn-write argument reduces to. -- *)

Lemma fs_blocks_lookup (dk : Z -> bv 8) (b : Z) (k : nat) :
  (k < BSIZE)%nat ->
  fs_blocks dk b !! k = Some (dk (b * Z.of_nat BSIZE + Z.of_nat k)).
Proof.
  intro Hk. rewrite /fs_blocks /disk_read list_lookup_fmap.
  rewrite (lookup_seq_lt 0 BSIZE k Hk). reflexivity.
Qed.

(* a write of [bs] at byte offset [o] INSIDE block [b] leaves every other
   block alone *)
Lemma fs_blocks_sub_ne (dk : Z -> bv 8) (b c : Z) (o : nat) (bs : list (bv 8)) :
  (o + length bs <= BSIZE)%nat -> c <> b ->
  fs_blocks (disk_write dk (b * Z.of_nat BSIZE + Z.of_nat o) bs) c
  = fs_blocks dk c.
Proof.
  intros Hfit Hne. rewrite /fs_blocks /disk_read.
  apply list_fmap_ext. intros j x Hx.
  apply lookup_seq in Hx as [-> Hjlt].
  apply disk_write_out.
  rewrite /BSIZE in Hjlt. rewrite /BSIZE in Hfit. rewrite /BSIZE.
  destruct (Z.lt_total c b) as [Hlt|[->|Hgt]]; [| congruence |]; [left|right]; lia.
Qed.

(* ...and splices the block it does write *)
Lemma fs_blocks_splice (dk : Z -> bv 8) (b : Z) (o : nat) (bs : list (bv 8)) :
  (o + length bs <= BSIZE)%nat ->
  fs_blocks (disk_write dk (b * Z.of_nat BSIZE + Z.of_nat o) bs) b
  = take o (fs_blocks dk b) ++ bs ++ drop (o + length bs) (fs_blocks dk b).
Proof.
  intro Hfit. pose proof (fs_blocks_length dk b) as HL.
  assert (Hto : (o <= length (fs_blocks dk b))%nat) by lia.
  assert (Hlt : length (take o (fs_blocks dk b)) = o)
    by exact (length_take_le _ _ Hto).
  apply list_eq. intro k.
  destruct (decide (k < BSIZE)%nat) as [Hk|Hk]; last first.
  { assert (H1 : (length (fs_blocks
                    (disk_write dk (b * Z.of_nat BSIZE + Z.of_nat o) bs) b)
                  <= k)%nat) by (rewrite fs_blocks_length; lia).
    assert (H2 : (length (take o (fs_blocks dk b)
                    ++ bs ++ drop (o + length bs) (fs_blocks dk b)) <= k)%nat).
    { rewrite !length_app Hlt length_drop HL. lia. }
    rewrite (lookup_ge_None_2 _ _ H1) (lookup_ge_None_2 _ _ H2). reflexivity. }
  rewrite (fs_blocks_lookup _ b k Hk).
  destruct (decide (k < o)%nat) as [Hbef|Hge].
  - (* before the write *)
    assert (Hk1 : (k < length (take o (fs_blocks dk b)))%nat) by lia.
    rewrite (lookup_app_l _ _ _ Hk1) (lookup_take _ _ _ Hbef)
            (fs_blocks_lookup _ b k Hk).
    f_equal. apply disk_write_out. lia.
  - assert (Hk1 : (length (take o (fs_blocks dk b)) <= k)%nat) by lia.
    rewrite (lookup_app_r _ _ _ Hk1) Hlt.
    destruct (decide (k < o + length bs)%nat) as [Hin|Hout].
    + (* inside the write *)
      assert (Hk2 : (k - o < length bs)%nat) by lia.
      destruct (lookup_lt_is_Some_2 bs (k - o) Hk2) as [x Hx].
      rewrite (lookup_app_l _ _ _ Hk2) Hx. f_equal.
      assert (Hoff : b * Z.of_nat BSIZE + Z.of_nat o
                     <= b * Z.of_nat BSIZE + Z.of_nat k) by lia.
      assert (Hidx : Z.to_nat (b * Z.of_nat BSIZE + Z.of_nat k
                               - (b * Z.of_nat BSIZE + Z.of_nat o))
                     = (k - o)%nat) by lia.
      apply (disk_write_in _ _ _ _ x Hoff). rewrite Hidx. exact Hx.
    + (* after the write *)
      assert (Hk2 : (length bs <= k - o)%nat) by lia.
      assert (Hkk : (o + length bs + (k - o - length bs))%nat = k) by lia.
      rewrite (lookup_app_r _ _ _ Hk2) lookup_drop Hkk
              (fs_blocks_lookup _ b k Hk).
      f_equal. apply disk_write_out. lia.
Qed.

(* the two sectors of an xv6 block *)
Lemma bsize_two_sectors : BSIZE = (2 * virtio_sector_bytes)%nat.
Proof. reflexivity. Qed.

(* SECTOR 0 of a block: the first 512 bytes become [bs]... *)
Lemma fs_blocks_sector0 (dk : Z -> bv 8) (b : Z) (bs : list (bv 8)) :
  length bs = virtio_sector_bytes ->
  take virtio_sector_bytes
    (fs_blocks (disk_write dk (b * Z.of_nat BSIZE) bs) b) = bs.
Proof.
  intro Hlen.
  assert (Hfit : (0 + length bs <= BSIZE)%nat)
    by (rewrite Hlen bsize_two_sectors; lia).
  pose proof (fs_blocks_splice dk b 0 bs Hfit) as Hsp.
  rewrite Nat2Z.inj_0 Z.add_0_r in Hsp.
  rewrite Hsp take_0. cbn [app].
  exact (take_app_length' bs _ virtio_sector_bytes (eq_sym Hlen)).
Qed.

(* ...and SECTOR 1 of a block leaves the first 512 bytes ALONE.  This is the
   torn-header case: recovery reads sector 0 only ([hdr_dec_sector0]), so a
   write that lands only sector 1 is invisible to it. *)
Lemma fs_blocks_sector1 (dk : Z -> bv 8) (b : Z) (bs : list (bv 8)) :
  length bs = virtio_sector_bytes ->
  take virtio_sector_bytes
    (fs_blocks (disk_write dk (b * Z.of_nat BSIZE + virtio_sector_size) bs) b)
  = take virtio_sector_bytes (fs_blocks dk b).
Proof.
  intro Hlen.
  assert (Hfit : (virtio_sector_bytes + length bs <= BSIZE)%nat)
    by (rewrite Hlen bsize_two_sectors; lia).
  pose proof (fs_blocks_splice dk b virtio_sector_bytes bs Hfit) as Hsp.
  rewrite -virtio_sector_size_bytes in Hsp.
  rewrite Hsp.
  assert (Hto : (virtio_sector_bytes <= length (fs_blocks dk b))%nat)
    by (rewrite fs_blocks_length bsize_two_sectors; lia).
  assert (Hle : (virtio_sector_bytes
                 <= length (take virtio_sector_bytes (fs_blocks dk b)))%nat)
    by (rewrite (length_take_le _ _ Hto); lia).
  rewrite (take_app_le _ _ _ Hle) take_take Nat.min_id. reflexivity.
Qed.

(* The FULL header decode ([le_word], [hdr_dec]) and its bridge lemmas live
   in [LogDefs] (re-exported above): the widened mirror's header READING
   ([LogDefs.lm_hdr]) needs them below the FS layer.                        *)

(* ---------------------------------------------------------------------- *)
(* 1b''. THE HEADER FITS IN ONE SECTOR                                     *)
(*    (claude-notes/projects/sector-atomic-disk.md §0).                     *)
(*                                                                          *)
(* [struct logheader] is [int n; int block[LOGBLOCKS];] = 4 + 4*30 = 124     *)
(* bytes, and a well-formed header ([hdr_wf]) has [n <= LOGBLOCKS], so the   *)
(* decoder reads bytes [0, 124) ONLY -- entirely inside SECTOR 0 of the      *)
(* header block.  That is the one fact the whole sector-tearing campaign     *)
(* rests on: a torn header write is harmless in either order, because        *)
(* sector 0 landing IS the commit and sector 1 landing changes nothing       *)
(* recovery reads.                                                          *)
(* ---------------------------------------------------------------------- *)

(* one decoded word only reads bytes [4*i, 4*i+4) *)
Lemma le_word_take (bs : list (bv 8)) (i k : nat) :
  (4 * i + 4 <= k)%nat -> le_word (take k bs) i = le_word bs i.
Proof.
  intro Hk. rewrite /le_word !take_drop_commute take_take.
  rewrite (Nat.min_l (4 * i + 4) k) //.
Qed.

(* the DECODED COUNT reads the first word only, so it survives any truncation
   that keeps four bytes *)
Lemma hdr_dec_fst_take (bs : list (bv 8)) (k : nat) :
  (4 <= k)%nat -> (hdr_dec (take k bs)).1 = (hdr_dec bs).1.
Proof.
  intro Hk. rewrite /hdr_dec /=.
  assert (H0 : le_word (take k bs) 0 = le_word bs 0)
    by (apply le_word_take; lia).
  by rewrite H0.
Qed.

(* THE DECODER READS A PREFIX.  [4 * S n] bytes is all of it. *)
Lemma hdr_dec_take (bs : list (bv 8)) (k : nat) :
  (4 * S (hdr_dec bs).1 <= k)%nat -> hdr_dec (take k bs) = hdr_dec bs.
Proof.
  intro Hk. rewrite /hdr_dec /=.
  assert (H0 : le_word (take k bs) 0 = le_word bs 0)
    by (apply le_word_take; lia).
  rewrite H0. f_equal. apply list_fmap_ext. intros j x Hx.
  apply lookup_seq in Hx as [-> Hjlt].
  apply le_word_take. rewrite /hdr_dec /= in Hk. lia.
Qed.

(* ...and under [hdr_wf]'s bound that prefix is inside SECTOR 0 *)
Lemma hdr_dec_sector0 (bs : list (bv 8)) :
  ((hdr_dec bs).1 <= LOGBLOCKS)%nat ->
  hdr_dec (take virtio_sector_bytes bs) = hdr_dec bs.
Proof.
  intro Hn. apply hdr_dec_take. rewrite /LOGBLOCKS in Hn.
  rewrite /virtio_sector_bytes. lia.
Qed.

(* the tight form: 4 + 4*LOGBLOCKS = 124 bytes *)
Lemma hdr_dec_hdr_bytes (bs : list (bv 8)) :
  ((hdr_dec bs).1 <= LOGBLOCKS)%nat ->
  hdr_dec (take (4 * S LOGBLOCKS)%nat bs) = hdr_dec bs.
Proof. intro Hn. apply hdr_dec_take. lia. Qed.

(* THE FORM EVERY COROLLARY BELOW USES: two block contents that agree on
   sector 0 decode to the same header.  Bytes [512, 1024) are dead to the
   decoder. *)
Lemma hdr_dec_sector0_eq (bs bs' : list (bv 8)) :
  ((hdr_dec bs).1 <= LOGBLOCKS)%nat ->
  take virtio_sector_bytes bs' = take virtio_sector_bytes bs ->
  hdr_dec bs' = hdr_dec bs.
Proof.
  intros Hn Heq.
  assert (Hn' : ((hdr_dec bs').1 <= LOGBLOCKS)%nat).
  { rewrite -(hdr_dec_fst_take bs' virtio_sector_bytes);
      [|rewrite /virtio_sector_bytes; lia].
    rewrite Heq (hdr_dec_fst_take bs virtio_sector_bytes);
      [exact Hn | rewrite /virtio_sector_bytes; lia]. }
  rewrite -(hdr_dec_sector0 bs' Hn') Heq. by apply hdr_dec_sector0.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1b'. THE HEADER WELL-FORMEDNESS INVARIANT (durable-disk stage B).       *)
(*                                                                         *)
(* [hdr_dec] is junk-tolerant and UNBOUNDED: a garbage header names any    *)
(* 32-bit [n], and recovery of such a header would read log slots beyond   *)
(* the region -- beyond the durable extent, where no fragment pins the     *)
(* bytes -- so "two images agreeing on the durable bytes carry the same    *)
(* record" ([P_fs_rec_agree]) would be FALSE.  The cure is an invariant    *)
(* riding [fs_rec_wf]: the ON-DISK header's decoded write set is bounded   *)
(* by the region, duplicate-free, and names covered HOME blocks only.      *)
(* Every header the steady-state permits write satisfies it (swap/clear    *)
(* write n = 0; commit writes its own decoded [(n, W)] under the batch's   *)
(* recorded facts, [LogInv.log_batch]'s three pure rows; logfill and       *)
(* install leave the header alone), and the recovery-side permit takes     *)
(* the write's share of it as a premise ([hdr_wf_wr_out] is the form a     *)
(* recovery home write discharges it in).                                  *)
(* ---------------------------------------------------------------------- *)

Definition hdr_wf (P : Z -> list (bv 8)) (cov : gset Z) (logstart : Z)
    : Prop :=
  ((hdr_dec (P (log_hdr_bno logstart))).1 <= LOGBLOCKS)%nat
  /\ NoDup (hdr_dec (P (log_hdr_bno logstart))).2
  /\ (forall b : Z, b ∈ (hdr_dec (P (log_hdr_bno logstart))).2 ->
        b ∈ cov /\ b ∉ log_region_set logstart).

(* a clean header is well formed -- mkfs's disk, and every swap/clear *)
Lemma hdr_wf_zero (P : Z -> list (bv 8)) (cov : gset Z) (logstart : Z) :
  hdr_n (P (log_hdr_bno logstart)) = 0 -> hdr_wf P cov logstart.
Proof.
  intros Hn. rewrite /hdr_wf (hdr_dec_zero _ Hn) /=.
  split_and!; [lia | constructor |].
  intros b Hb. by apply elem_of_nil in Hb.
Qed.

(* the invariant reads the header block only *)
Lemma hdr_wf_ext (P P' : Z -> list (bv 8)) (cov : gset Z) (logstart : Z) :
  P' (log_hdr_bno logstart) = P (log_hdr_bno logstart) ->
  hdr_wf P cov logstart -> hdr_wf P' cov logstart.
Proof. rewrite /hdr_wf. by intros ->. Qed.

(* ...in fact it reads it only through [hdr_dec] ... *)
Lemma hdr_wf_hdr_dec (P P' : Z -> list (bv 8)) (cov : gset Z) (logstart : Z) :
  hdr_dec (P' (log_hdr_bno logstart)) = hdr_dec (P (log_hdr_bno logstart)) ->
  hdr_wf P cov logstart -> hdr_wf P' cov logstart.
Proof. rewrite /hdr_wf. by intros ->. Qed.

(* ...and so only through SECTOR 0 of it: a torn header write that lands only
   sector 1 changes nothing this invariant sees. *)
Lemma hdr_wf_sector0 (P P' : Z -> list (bv 8)) (cov : gset Z) (logstart : Z) :
  take virtio_sector_bytes (P' (log_hdr_bno logstart))
  = take virtio_sector_bytes (P (log_hdr_bno logstart)) ->
  hdr_wf P cov logstart -> hdr_wf P' cov logstart.
Proof.
  intros Heq Hwf. eapply hdr_wf_hdr_dec; [|exact Hwf].
  apply hdr_dec_sector0_eq; [exact (proj1 Hwf) | exact Heq].
Qed.

(* ...so a whole-block write ANYWHERE ELSE preserves it.  This is the form
   a recovery home write discharges [fs_recover_permit]'s premise in: the
   block it writes came out of the header it read, and the invariant it
   learned there says that block is not the header. *)
Lemma hdr_wf_wr_out (cov : gset Z) (logstart b : Z) (bs : list (bv 8))
    (dk : Z -> bv 8) :
  length bs = BSIZE ->
  b <> log_hdr_bno logstart ->
  hdr_wf (fs_blocks dk) cov logstart ->
  hdr_wf (fs_blocks (disk_write dk (b * Z.of_nat BSIZE)%Z bs)) cov logstart.
Proof.
  intros Hlen Hb. apply hdr_wf_ext.
  apply fs_blocks_write_ne; [exact Hlen | by apply not_eq_sym].
Qed.

(* ---------------------------------------------------------------------- *)
(* 1c. The recovery relation.                                              *)
(*                                                                         *)
(* Stated in LogDefs' own geometry vocabulary ([log_hdr_bno],              *)
(* [log_slot_bno], [log_region_set]), so the log proofs and this file       *)
(* cannot drift apart on where the log lives.                              *)
(* ---------------------------------------------------------------------- *)

(* the HOME blocks: the covered range minus the log's own storage *)
Definition fs_home_set (cov : gset Z) (logstart : Z) : gset Z :=
  cov ∖ log_region_set logstart.

(* a total block view, restricted to a finite set of block numbers *)
Definition fs_restrict (P : Z -> list (bv 8)) (s : gset Z)
    : gmap Z (list (bv 8)) :=
  set_to_map (fun b => (b, P b)) s.

Lemma fs_restrict_lookup_Some (P : Z -> list (bv 8)) (s : gset Z)
    (b : Z) (v : list (bv 8)) :
  fs_restrict P s !! b = Some v <-> b ∈ s /\ v = P b.
Proof.
  rewrite /fs_restrict lookup_set_to_map; last by intros y y' _ _ ?.
  split.
  - intros (x & Hx & Hf). injection Hf as Hb Hv. subst. done.
  - intros [Hb ->]. exists b. done.
Qed.

Lemma fs_restrict_dom (P : Z -> list (bv 8)) (s : gset Z) :
  dom (fs_restrict P s) = s.
Proof.
  apply set_eq. intros b. rewrite elem_of_dom. split.
  - intros [v Hv]. by apply fs_restrict_lookup_Some in Hv as [? _].
  - intros Hb. eexists. apply fs_restrict_lookup_Some. done.
Qed.

(* INSTALLING the on-disk log over the home map: entry [i] of the write set
   takes its content from log slot [i].  A [foldr] over the INDEX list
   rather than over [W] itself, because the content's block number
   ([log_slot_bno logstart i]) is a function of the index.  The step is a
   NAMED function (not an inline lambda) so that every lemma below unifies
   against the same head rather than against a fresh beta-redex. *)
Definition fs_install_step (P : Z -> list (bv 8)) (logstart : Z) (W : list Z)
    (i : nat) (m : gmap Z (list (bv 8))) : gmap Z (list (bv 8)) :=
  match W !! i with
  | Some b => <[ b := P (log_slot_bno logstart i) ]> m
  | None => m
  end.

Lemma fs_install_step_Some (P : Z -> list (bv 8)) (logstart : Z) (W : list Z)
    (i : nat) (b : Z) (m : gmap Z (list (bv 8))) :
  W !! i = Some b ->
  fs_install_step P logstart W i m = <[ b := P (log_slot_bno logstart i) ]> m.
Proof. rewrite /fs_install_step. by intros ->. Qed.

Lemma fs_install_step_None (P : Z -> list (bv 8)) (logstart : Z) (W : list Z)
    (i : nat) (m : gmap Z (list (bv 8))) :
  W !! i = None -> fs_install_step P logstart W i m = m.
Proof. rewrite /fs_install_step. by intros ->. Qed.

Definition fs_install (P : Z -> list (bv 8)) (logstart : Z) (W : list Z)
    (D : gmap Z (list (bv 8))) : gmap Z (list (bv 8)) :=
  foldr (fs_install_step P logstart W) D (seq 0 (length W)).

Lemma fs_install_nil (P : Z -> list (bv 8)) (logstart : Z)
    (D : gmap Z (list (bv 8))) :
  fs_install P logstart [] D = D.
Proof. reflexivity. Qed.

(* THE RECOVERY RELATION.  [D] is what a reboot would find, read off the
   physical disk [P] alone: the header block decides whether the log is
   live, and the whole thing is a FUNCTION of [P] (see [fs_recovery_det]). *)
Definition fs_recovery (P : Z -> list (bv 8)) (D : gmap Z (list (bv 8)))
    (cov : gset Z) (logstart : Z) : Prop :=
  D = fs_install P logstart (hdr_dec (P (log_hdr_bno logstart))).2
        (fs_restrict P (fs_home_set cov logstart)).

Lemma fs_recovery_det (P : Z -> list (bv 8)) D1 D2 cov logstart :
  fs_recovery P D1 cov logstart -> fs_recovery P D2 cov logstart -> D1 = D2.
Proof. intros -> ->. reflexivity. Qed.

Lemma fs_recovery_total (P : Z -> list (bv 8)) cov logstart :
  exists D, fs_recovery P D cov logstart.
Proof. eexists. reflexivity. Qed.

(* THE CLEAN-IMAGE COROLLARY (stage 2's [initlog] precondition, and what a
   freshly mkfs'ed disk satisfies): at [n = 0] recovery is the identity on
   the home blocks. *)
Lemma fs_recovery_clean (P : Z -> list (bv 8)) D cov logstart :
  hdr_n (P (log_hdr_bno logstart)) = 0 ->
  fs_recovery P D cov logstart <->
  D = fs_restrict P (fs_home_set cov logstart).
Proof.
  intros Hn. rewrite /fs_recovery (hdr_dec_zero _ Hn) /= fs_install_nil //.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1c'. THE MIRROR's MEANING (durable-disk stage E2).                       *)
(*                                                                          *)
(* [RiscvPtsto.log_mirror] is the SHAPE; this is what makes a recorded       *)
(* picture true of a disk: POINTWISE, TOTAL agreement with the block view.   *)
(* It is the bridge the WAL write kinds pass to each other, and the reason   *)
(* it must exist at all is that a crash permit is a STATELESS view shift:    *)
(* no single [bwrite] can re-derive "the on-disk header is clean" or "the    *)
(* log slots hold the logged values" or "home block b holds its slot's       *)
(* content" -- those are facts the PREVIOUS writes established.  Total       *)
(* agreement (homes included) is what lets a ∅-mask permit know the          *)
(* committed state BY VALUE (crash.md, "The split crash predicate"): the     *)
(* WAL's own writes are the only writes to the durable extent, so every      *)
(* permit re-establishes the picture at the post-write image.                *)
(* ---------------------------------------------------------------------- *)

(* SCOPED TO THE DURABLE EXTENT, deliberately: two disks that agree on the
   durable bytes must carry the same record ([P_fs_rec_agree] below), so the
   picture may not pin a block no fragment owns.                            *)
Definition log_mirror_ok (M : log_mirror) (P : Z -> list (bv 8))
    (cov : gset Z) (ls : Z) : Prop :=
  forall b : Z, b ∈ cov ∪ log_region_set ls -> lm_view M b = P b.

(* the mirror of a given disk -- what a swap installs and what every WAL
   fupd re-establishes at the post-write image *)
Definition mirror_of (P : Z -> list (bv 8)) : log_mirror := MkLogMirror P.

Lemma mirror_of_ok (P : Z -> list (bv 8)) (cov : gset Z) (ls : Z) :
  log_mirror_ok (mirror_of P) P cov ls.
Proof. intros b _. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 1c''. THE PURE CORE OF THE WAL's CRASH ARGUMENT (phase C2b/D1 stage 1).  *)
(*                                                                          *)
(* Four write kinds happen to the disk while the log runs, and each one has  *)
(* to re-establish [fs_recovery] at the POST-write image.  Every one of the  *)
(* four is proved here, ONCE, as a statement about an abstract post-image    *)
(* [P'] constrained POINTWISE:                                               *)
(*    Hhit :  P' <the written block> = <the new content>                     *)
(*    Hmiss:  forall c, c <> <the written block> -> P' c = P c               *)
(* and NOTHING else.  That shape is deliberate: at each call site the fupd    *)
(* has exactly [FsCrash.fs_blocks_write_eq] and [fs_blocks_write_ne] in       *)
(* hand, which are precisely those two facts about                            *)
(* [fs_blocks (disk_write dk …)] -- so no functional extensionality is ever    *)
(* needed to identify the post-image with a closed term.                      *)
(*                                                                            *)
(* The geometry premises are explicit for the same reason: the pure layer      *)
(* must not silently assume that a decoded (junk-tolerant!) header names        *)
(* in-range slots or home blocks.                                              *)
(* ---------------------------------------------------------------------- *)

(* --- the log region's geometry, as membership facts --- *)

Lemma log_slot_ne_hdr (ls : Z) (i : nat) :
  log_slot_bno ls i <> log_hdr_bno ls.
Proof.
  rewrite /log_slot_bno /log_hdr_bno.
  pose proof (Nat2Z.is_nonneg i). lia.
Qed.

Lemma log_slot_in_region (ls : Z) (i : nat) :
  (i < LOGBLOCKS)%nat -> log_slot_bno ls i ∈ log_region_set ls.
Proof.
  intros Hi. rewrite /log_region_set elem_of_union. left.
  rewrite elem_of_list_to_set elem_of_list_fmap. exists i.
  split; [reflexivity|]. apply elem_of_seq. lia.
Qed.

Lemma log_hdr_in_region (ls : Z) : log_hdr_bno ls ∈ log_region_set ls.
Proof.
  rewrite /log_region_set elem_of_union. right. by apply elem_of_singleton.
Qed.

Lemma log_hdr_in_ext (cov : gset Z) (ls : Z) :
  log_hdr_bno ls ∈ cov ∪ log_region_set ls.
Proof. apply elem_of_union. right. apply log_hdr_in_region. Qed.

Lemma log_slot_in_ext (cov : gset Z) (ls : Z) (i : nat) :
  (i < LOGBLOCKS)%nat -> log_slot_bno ls i ∈ cov ∪ log_region_set ls.
Proof.
  intros Hi. apply elem_of_union. right. by apply log_slot_in_region.
Qed.

Lemma fs_home_in_ext (cov : gset Z) (ls b : Z) :
  b ∈ fs_home_set cov ls -> b ∈ cov ∪ log_region_set ls.
Proof.
  rewrite /fs_home_set elem_of_difference. intros [Hc _].
  apply elem_of_union. by left.
Qed.

(* the two headers a mirror ties together: its own reading and the disk's *)
Lemma log_mirror_ok_hdr (M : log_mirror) (P : Z -> list (bv 8))
    (cov : gset Z) (ls : Z) :
  log_mirror_ok M P cov ls -> lm_hdr M ls = hdr_dec (P (log_hdr_bno ls)).
Proof.
  intros Hok. rewrite /lm_hdr (Hok _ (log_hdr_in_ext cov ls)) //.
Qed.

(* one block write moves the picture and the disk in step -- the closing
   move of every value-chained permit (stage E2') *)
Lemma log_mirror_ok_upd (M : log_mirror) (dk : Z -> bv 8)
    (cov : gset Z) (ls blk : Z) (bs : list (bv 8)) :
  length bs = BSIZE ->
  log_mirror_ok M (fs_blocks dk) cov ls ->
  log_mirror_ok (lm_upd M blk bs)
    (fs_blocks (disk_write dk (blk * Z.of_nat BSIZE)%Z bs)) cov ls.
Proof.
  intros Hlen Hok b Hb. destruct (decide (b = blk)) as [-> | Hne].
  - rewrite lm_upd_view_eq (fs_blocks_write_eq _ _ _ Hlen) //.
  - rewrite (lm_upd_view_ne _ _ _ _ Hne)
      (fs_blocks_write_ne _ _ _ _ Hlen Hne).
    exact (Hok b Hb).
Qed.


Lemma log_region_not_home (cov : gset Z) (ls b : Z) :
  b ∈ log_region_set ls -> b ∉ fs_home_set cov ls.
Proof.
  intros Hb Hc. rewrite /fs_home_set elem_of_difference in Hc. tauto.
Qed.

(* the two disequalities a HOME-block write needs *)
Lemma home_ne_slot (ls b : Z) (j : nat) :
  b ∉ log_region_set ls -> (j < LOGBLOCKS)%nat -> b <> log_slot_bno ls j.
Proof. intros Hb Hj ->. by apply Hb, log_slot_in_region. Qed.

Lemma home_ne_hdr (ls b : Z) :
  b ∉ log_region_set ls -> b <> log_hdr_bno ls.
Proof. intros Hb ->. by apply Hb, log_hdr_in_region. Qed.

(* --- [fs_restrict], pointwise --- *)

Lemma fs_restrict_lookup_None (P : Z -> list (bv 8)) (s : gset Z) (b : Z) :
  b ∉ s -> fs_restrict P s !! b = None.
Proof.
  intros Hb. destruct (fs_restrict P s !! b) as [v|] eqn:Hv; [|reflexivity].
  apply fs_restrict_lookup_Some in Hv as [Hin _]. done.
Qed.

Lemma fs_restrict_lookup (P : Z -> list (bv 8)) (s : gset Z) (b : Z) :
  fs_restrict P s !! b = (if decide (b ∈ s) then Some (P b) else None).
Proof.
  destruct (decide (b ∈ s)) as [Hb|Hb].
  - by apply fs_restrict_lookup_Some.
  - by apply fs_restrict_lookup_None.
Qed.

Lemma fs_restrict_ext (P P' : Z -> list (bv 8)) (s : gset Z) :
  (forall b, b ∈ s -> P' b = P b) -> fs_restrict P' s = fs_restrict P s.
Proof.
  intros HP. apply map_eq. intros b. rewrite !fs_restrict_lookup.
  destruct (decide (b ∈ s)) as [Hb|Hb]; [|reflexivity]. by rewrite (HP b Hb).
Qed.

(* THE MISSING RESTRICT LEMMA the log-fill / commit / clear transitions all
   need: a write OUTSIDE the restricted set does not move the restriction. *)
Lemma fs_restrict_upd_out (P P' : Z -> list (bv 8)) (s : gset Z) (b : Z) :
  b ∉ s -> (forall c, c <> b -> P' c = P c) ->
  fs_restrict P' s = fs_restrict P s.
Proof.
  intros Hb HP. apply fs_restrict_ext. intros c Hc. apply HP.
  intros ->. done.
Qed.

(* --- [fs_install], as a LOOKUP characterisation --- *)

Local Lemma fs_install_fold_miss (P : Z -> list (bv 8)) (ls : Z) (W : list Z)
    (D : gmap Z (list (bv 8))) (l : list nat) (b : Z) :
  b ∉ W -> foldr (fs_install_step P ls W) D l !! b = D !! b.
Proof.
  intros Hb. induction l as [|i l IH]; [reflexivity|]. cbn [foldr].
  destruct (W !! i) as [c|] eqn:Hi.
  - rewrite (fs_install_step_Some _ _ _ _ _ _ Hi).
    rewrite lookup_insert_ne; [exact IH|].
    intros ->. apply Hb. eapply elem_of_list_lookup_2. exact Hi.
  - rewrite (fs_install_step_None _ _ _ _ _ Hi). exact IH.
Qed.

Local Lemma fs_install_fold_hit (P : Z -> list (bv 8)) (ls : Z) (W : list Z)
    (D : gmap Z (list (bv 8))) (l : list nat) (i : nat) (b : Z) :
  NoDup W -> W !! i = Some b -> i ∈ l ->
  foldr (fs_install_step P ls W) D l !! b = Some (P (log_slot_bno ls i)).
Proof.
  intros Hnd Hi. induction l as [|j l IH]; [by rewrite elem_of_nil|].
  rewrite elem_of_cons. intros [->|Hin]; cbn [foldr].
  - rewrite (fs_install_step_Some _ _ _ _ _ _ Hi) lookup_insert //.
  - destruct (W !! j) as [c|] eqn:Hj.
    + rewrite (fs_install_step_Some _ _ _ _ _ _ Hj).
      destruct (decide (c = b)) as [->|Hne].
      * assert (Hji : j = i) by (eapply NoDup_lookup; [exact Hnd|exact Hj|exact Hi]).
        subst j. rewrite lookup_insert //.
      * rewrite lookup_insert_ne //. by apply IH.
    + rewrite (fs_install_step_None _ _ _ _ _ Hj). by apply IH.
Qed.

(* A block the write set does not name reads through from the home map. *)
Lemma fs_install_miss (P : Z -> list (bv 8)) (ls : Z) (W : list Z)
    (D : gmap Z (list (bv 8))) (b : Z) :
  b ∉ W -> fs_install P ls W D !! b = D !! b.
Proof. intros Hb. by apply fs_install_fold_miss. Qed.

(* A block the write set names at index [i] reads the log's slot [i].  NoDup
   is what makes "index [i]" well defined -- with a repeated block number the
   OUTERMOST insert (the smallest index) would win instead. *)
Lemma fs_install_hit (P : Z -> list (bv 8)) (ls : Z) (W : list Z)
    (D : gmap Z (list (bv 8))) (i : nat) (b : Z) :
  NoDup W -> W !! i = Some b ->
  fs_install P ls W D !! b = Some (P (log_slot_bno ls i)).
Proof.
  intros Hnd Hi. eapply fs_install_fold_hit; [exact Hnd|exact Hi|].
  apply elem_of_seq. pose proof (lookup_lt_Some _ _ _ Hi). lia.
Qed.

(* Installing over a map that ALREADY holds the logged values is a no-op --
   which is what makes the final header CLEAR preserve the durable state. *)
Lemma fs_install_idem (P : Z -> list (bv 8)) (ls : Z) (W : list Z)
    (D : gmap Z (list (bv 8))) :
  NoDup W ->
  (forall i b, W !! i = Some b -> D !! b = Some (P (log_slot_bno ls i))) ->
  fs_install P ls W D = D.
Proof.
  intros Hnd Hall. apply map_eq. intros b.
  destruct (decide (b ∈ W)) as [Hin|Hout].
  - apply elem_of_list_lookup_1 in Hin as [i Hi].
    rewrite (fs_install_hit P ls W D i b Hnd Hi). by rewrite (Hall i b Hi).
  - by rewrite fs_install_miss.
Qed.

(* Two congruences.  The first needs no uniqueness (only the slot contents
   move); the second lets the home map move too, at keys the write set names,
   and that is where NoDup is unavoidable. *)
Local Lemma fs_install_fold_extP (P P' : Z -> list (bv 8)) (ls : Z)
    (W : list Z) (D : gmap Z (list (bv 8))) (l : list nat) :
  (forall j, j ∈ l -> P' (log_slot_bno ls j) = P (log_slot_bno ls j)) ->
  foldr (fs_install_step P' ls W) D l = foldr (fs_install_step P ls W) D l.
Proof.
  induction l as [|j l IH]; [reflexivity|]. intros Hj.
  assert (Heq : foldr (fs_install_step P' ls W) D l
                = foldr (fs_install_step P ls W) D l).
  { apply IH. intros k Hk. apply Hj. by apply elem_of_list_further. }
  cbn [foldr]. rewrite Heq.
  destruct (W !! j) as [b|] eqn:Hb.
  - rewrite !(fs_install_step_Some _ _ _ _ _ _ Hb).
    rewrite (Hj j (elem_of_list_here _ _)) //.
  - rewrite !(fs_install_step_None _ _ _ _ _ Hb) //.
Qed.

Lemma fs_install_ext_P (P P' : Z -> list (bv 8)) (ls : Z) (W : list Z)
    (D : gmap Z (list (bv 8))) :
  (forall j, (j < length W)%nat -> P' (log_slot_bno ls j) = P (log_slot_bno ls j)) ->
  fs_install P' ls W D = fs_install P ls W D.
Proof.
  intros HP. rewrite /fs_install. apply fs_install_fold_extP.
  intros j Hj. apply elem_of_seq in Hj. apply HP. lia.
Qed.

Lemma fs_install_ext (P P' : Z -> list (bv 8)) (ls : Z) (W : list Z)
    (D D' : gmap Z (list (bv 8))) :
  NoDup W ->
  (forall j b, W !! j = Some b ->
     P' (log_slot_bno ls j) = P (log_slot_bno ls j)) ->
  (forall k, k ∉ W -> D' !! k = D !! k) ->
  fs_install P' ls W D' = fs_install P ls W D.
Proof.
  intros Hnd HP HD. apply map_eq. intros k.
  destruct (decide (k ∈ W)) as [Hin|Hout].
  - apply elem_of_list_lookup_1 in Hin as [j Hj].
    rewrite (fs_install_hit P' ls W D' j k Hnd Hj)
            (fs_install_hit P ls W D j k Hnd Hj).
    by rewrite (HP j k Hj).
  - rewrite !fs_install_miss //. by apply HD.
Qed.

(* --- THE FOUR RECOVERY TRANSITIONS --- *)

(* (1) LOG FILL -- write_log's copy of a logged block into slot [i], with the
   ON-DISK header still clean.  Recovery does not move at all: the slot is
   not a home block, and at n = 0 nothing reads the slots. *)
Lemma fs_recovery_logfill (P P' : Z -> list (bv 8))
    (D : gmap Z (list (bv 8))) (cov : gset Z) (ls : Z) (i : nat) :
  (i < LOGBLOCKS)%nat ->
  (forall c, c <> log_slot_bno ls i -> P' c = P c) ->
  hdr_n (P (log_hdr_bno ls)) = 0 ->
  fs_recovery P D cov ls ->
  fs_recovery P' D cov ls.
Proof.
  intros Hi Hmiss Hn Hrec.
  assert (Hhdr : P' (log_hdr_bno ls) = P (log_hdr_bno ls)).
  { apply Hmiss. apply not_eq_sym, log_slot_ne_hdr. }
  apply (fs_recovery_clean P' D cov ls); [by rewrite Hhdr|].
  apply (fs_recovery_clean P D cov ls Hn) in Hrec. rewrite Hrec.
  symmetry. apply (fs_restrict_upd_out P P' _ (log_slot_bno ls i));
    [|exact Hmiss].
  by apply log_region_not_home, log_slot_in_region.
Qed.

(* (2) COMMIT -- write_head storing a header that decodes to (n, W), n > 0.
   THE commit point: the durable state jumps, and the new one is computable
   from the PRE-write image (the header block is neither a home block nor a
   slot), which is exactly what lets the committer identify it with the
   batch's logged view. *)
Lemma fs_recovery_commit (P P' : Z -> list (bv 8)) (cov : gset Z) (ls : Z)
    (bs : list (bv 8)) :
  P' (log_hdr_bno ls) = bs ->
  (forall c, c <> log_hdr_bno ls -> P' c = P c) ->
  fs_recovery P' (fs_install P ls (hdr_dec bs).2
                    (fs_restrict P (fs_home_set cov ls))) cov ls.
Proof.
  intros Hhit Hmiss. rewrite /fs_recovery Hhit.
  rewrite (fs_restrict_upd_out P P' (fs_home_set cov ls) (log_hdr_bno ls));
    [|by apply log_region_not_home, log_hdr_in_region|exact Hmiss].
  rewrite (fs_install_ext_P P P' ls (hdr_dec bs).2) //.
  intros j _. apply Hmiss, log_slot_ne_hdr.
Qed.

(* (3) INSTALL -- install_trans writing home block [b] = W[i].  Recovery is
   UNCHANGED: the home map moves at [b], but the installed picture overwrites
   [b] with slot [i] anyway, and the slot did not move.  [length W <=
   LOGBLOCKS] is the geometry bound (a junk-tolerant decode could otherwise
   name a slot beyond the region, which the home-block write would then be
   allowed to alias).
   NOTE THE ABSENT HYPOTHESIS: nothing is assumed about the CONTENT written.
   Recovery re-installs [b] from slot [i] whatever is there, which is the
   WAL's whole point -- and it is what lets the install fupd
   ([fs_install_permit]) run without any picture of the home side of the
   disk. *)
Lemma fs_recovery_install (P P' : Z -> list (bv 8))
    (D : gmap Z (list (bv 8))) (cov : gset Z) (ls : Z) (i : nat) (b : Z) :
  NoDup (hdr_dec (P (log_hdr_bno ls))).2 ->
  (length (hdr_dec (P (log_hdr_bno ls))).2 <= LOGBLOCKS)%nat ->
  (hdr_dec (P (log_hdr_bno ls))).2 !! i = Some b ->
  b ∉ log_region_set ls ->
  (forall c, c <> b -> P' c = P c) ->
  fs_recovery P D cov ls ->
  fs_recovery P' D cov ls.
Proof.
  intros Hnd Hlen Hi Hb Hmiss Hrec.
  assert (Hhdr : P' (log_hdr_bno ls) = P (log_hdr_bno ls)).
  { apply Hmiss, not_eq_sym. by apply home_ne_hdr. }
  rewrite /fs_recovery Hhdr. rewrite /fs_recovery in Hrec. rewrite Hrec.
  symmetry. apply fs_install_ext; [exact Hnd| |].
  - intros j c Hj. apply Hmiss.
    apply not_eq_sym, (home_ne_slot ls b j Hb).
    pose proof (lookup_lt_Some _ _ _ Hj). lia.
  - intros k Hk. rewrite !fs_restrict_lookup.
    destruct (decide (k ∈ fs_home_set cov ls)) as [Hin|Hin]; [|reflexivity].
    rewrite Hmiss; [reflexivity|]. intros ->. apply Hk.
    eapply elem_of_list_lookup_2. exact Hi.
Qed.

(* (4) CLEAR -- write_head storing a header with n = 0 once every logged
   block has been installed.  Recovery becomes the plain home restriction. *)
Lemma fs_recovery_clear (P P' : Z -> list (bv 8)) (cov : gset Z) (ls : Z)
    (bs : list (bv 8)) :
  P' (log_hdr_bno ls) = bs ->
  hdr_n bs = 0 ->
  (forall c, c <> log_hdr_bno ls -> P' c = P c) ->
  fs_recovery P' (fs_restrict P (fs_home_set cov ls)) cov ls.
Proof.
  intros Hhit Hn Hmiss.
  apply (fs_recovery_clean P' _ cov ls); [by rewrite Hhit|].
  symmetry. apply (fs_restrict_upd_out P P' _ (log_hdr_bno ls)); [|exact Hmiss].
  by apply log_region_not_home, log_hdr_in_region.
Qed.

(* …and the form the fupd actually wants: the clear PRESERVES the durable
   state, given that the installed values are already in the home map.  This
   is the one place [fs_install_hit]/[fs_install_miss] are load-bearing. *)
Lemma fs_recovery_clear_keeps (P P' : Z -> list (bv 8))
    (D : gmap Z (list (bv 8))) (cov : gset Z) (ls : Z) (bs : list (bv 8)) :
  P' (log_hdr_bno ls) = bs ->
  hdr_n bs = 0 ->
  (forall c, c <> log_hdr_bno ls -> P' c = P c) ->
  NoDup (hdr_dec (P (log_hdr_bno ls))).2 ->
  (forall j b, (hdr_dec (P (log_hdr_bno ls))).2 !! j = Some b ->
     fs_restrict P (fs_home_set cov ls) !! b = Some (P (log_slot_bno ls j))) ->
  fs_recovery P D cov ls ->
  fs_recovery P' D cov ls.
Proof.
  intros Hhit Hn Hmiss Hnd Hinst Hrec.
  rewrite /fs_recovery in Hrec. rewrite Hrec (fs_install_idem _ _ _ _ Hnd Hinst).
  by eapply fs_recovery_clear.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1c'''. TORN WRITES (claude-notes/projects/sector-atomic-disk.md).       *)
(*                                                                          *)
(* A 512-byte sector lands atomically; a 1024-byte BLOCK does not.  Two      *)
(* consequences the WAL's crash argument needs, and nothing else:            *)
(*                                                                          *)
(*  - a header write that lands only SECTOR 1 is invisible to recovery       *)
(*    ([hdr_dec_sector0]), so [hdr_wf], [fs_recovery] and [log_mirror_ok]    *)
(*    all survive it unchanged;                                             *)
(*  - a torn write of a LOG SLOT moves the mirror's picture of that slot to  *)
(*    whatever the disk now holds -- the mirror is content-agnostic, which   *)
(*    is exactly why it can carry a half-written slot.                      *)
(* ---------------------------------------------------------------------- *)

Lemma log_slot_bno_inj (ls : Z) (i j : nat) :
  i <> j -> log_slot_bno ls i <> log_slot_bno ls j.
Proof. rewrite /log_slot_bno. lia. Qed.

(* RECOVERY reads the header block only through [hdr_dec]... *)
Lemma fs_recovery_hdr_dec (P P' : Z -> list (bv 8))
    (D : gmap Z (list (bv 8))) (cov : gset Z) (ls : Z) :
  hdr_dec (P' (log_hdr_bno ls)) = hdr_dec (P (log_hdr_bno ls)) ->
  (forall c, c <> log_hdr_bno ls -> P' c = P c) ->
  fs_recovery P D cov ls -> fs_recovery P' D cov ls.
Proof.
  intros Hhdr Hmiss Hrec. rewrite /fs_recovery Hhdr.
  assert (HPs : forall j, (j < length (hdr_dec (P (log_hdr_bno ls))).2)%nat ->
                  P' (log_slot_bno ls j) = P (log_slot_bno ls j))
    by (intros j _; apply Hmiss, log_slot_ne_hdr).
  rewrite (fs_install_ext_P P P' ls _ _ HPs).
  rewrite (fs_restrict_upd_out P P' (fs_home_set cov ls) (log_hdr_bno ls)
             (log_region_not_home cov ls _ (log_hdr_in_region ls)) Hmiss).
  exact Hrec.
Qed.

(* ...and so only through SECTOR 0 of it *)
Lemma fs_recovery_hdr_sector0 (P P' : Z -> list (bv 8))
    (D : gmap Z (list (bv 8))) (cov : gset Z) (ls : Z) :
  ((hdr_dec (P (log_hdr_bno ls))).1 <= LOGBLOCKS)%nat ->
  take virtio_sector_bytes (P' (log_hdr_bno ls))
  = take virtio_sector_bytes (P (log_hdr_bno ls)) ->
  (forall c, c <> log_hdr_bno ls -> P' c = P c) ->
  fs_recovery P D cov ls -> fs_recovery P' D cov ls.
Proof.
  intros Hn Heq Hmiss Hrec.
  eapply fs_recovery_hdr_dec; [| exact Hmiss | exact Hrec].
  by apply hdr_dec_sector0_eq.
Qed.

(* THE MIRROR under a torn header write: sector 1 changes nothing it holds. *)
Lemma log_mirror_ok_hdr_sector0 (M : log_mirror) (P P' : Z -> list (bv 8))
    (ls : Z) :
  ((hdr_dec (P (log_hdr_bno ls))).1 <= LOGBLOCKS)%nat ->
  take virtio_sector_bytes (P' (log_hdr_bno ls))
  = take virtio_sector_bytes (P (log_hdr_bno ls)) ->
  (forall c, c <> log_hdr_bno ls -> P' c = P c) ->
  log_mirror_ok M P ls -> log_mirror_ok M P' ls.
Proof.
  intros Hn Heq Hmiss [Hhdr Hslots]. split.
  - rewrite Hhdr. symmetry. by apply hdr_dec_sector0_eq.
  - intros i Hi. rewrite (Hslots i Hi) Hmiss //. apply log_slot_ne_hdr.
Qed.

(* THE SECTOR ANALOGUE OF [log_mirror_ok_out]: a write that lands anywhere
   inside log SLOT [j] -- a whole block, one sector, or a torn half of one --
   moves the mirror's picture of that slot to whatever the disk now holds and
   leaves every other row alone.  Content-agnostic on purpose: the mirror is
   what carries a half-written slot across the rest of the commit. *)
Lemma log_mirror_ok_sector (M : log_mirror) (P P' : Z -> list (bv 8))
    (ls : Z) (j : nat) :
  (j < LOGBLOCKS)%nat ->
  (forall c, c <> log_slot_bno ls j -> P' c = P c) ->
  log_mirror_ok M P ls ->
  log_mirror_ok (MkLogMirror (lm_hdr M)
                   (fun k => if decide (k = j)
                             then P' (log_slot_bno ls j) else lm_slots M k))
                P' ls.
Proof.
  intros Hj Hmiss [Hhdr Hslots]. split.
  - cbn [lm_hdr]. rewrite Hhdr Hmiss //.
    by apply not_eq_sym, log_slot_ne_hdr.
  - cbn [lm_slots]. intros i Hi. destruct (decide (i = j)) as [->|Hne].
    + reflexivity.
    + rewrite (Hslots i Hi) Hmiss //. by apply log_slot_bno_inj.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1d. The record the escrow is over, and its well-formedness.             *)
(* ---------------------------------------------------------------------- *)

Record fs_rec := MkFsRec {
  (* the DURABLE home map: what recovery produces from the PHYSICAL disk
     right now.  The physical disk itself is no longer a field: it is the
     crash predicate's INDEX (phase C2a), which the machine layer's tie pins
     to the real [v_disk]. *)
  fr_D : gmap Z (list (bv 8));
  (* the committed HISTORY, oldest first; [fr_D] is its last element.  The
     mono-list's persistent lower bounds over this are the durability
     RECEIPTS ([fs_receipt]) sys_sync will hand out (phase D). *)
  fr_hist : list (gmap Z (list (bv 8)));
}.

Definition fs_rec_wf (r : fs_rec) (P : Z -> list (bv 8))
    (cov : gset Z) (logstart : Z) : Prop :=
  fs_recovery P (fr_D r) cov logstart /\
  last (fr_hist r) = Some (fr_D r) /\
  (* the on-disk header's invariant (1b' above): without it the record
     would read the image beyond the durable extent, and [P_fs_rec_agree]
     -- the machine-image agreement every permit runs on -- would be false *)
  hdr_wf P cov logstart /\
  (* THE [P_wf] CONJUNCT (ruling 2, crash.md "The split crash predicate"):
     the committed view is FS-well-formed.  Stated about [fr_D] ONLY --
     never about [P] -- which is what makes it invariant under every
     re-indexing ([P_fs_rec_agree]) and under every permit that preserves
     the committed view (logfill, install, the preserving clear).  Pure
     while [fs_durable_wf]'s body is the F1 placeholder; it becomes a
     separate iProp conjunct of [P_fs] when the contents layer adds
     durable ghosts. *)
  fs_durable_wf (fr_D r).

Lemma fs_rec_wf_hist_ne r P cov logstart :
  fs_rec_wf r P cov logstart -> fr_hist r <> [].
Proof. intros (_ & Hlast & _) Hnil. rewrite Hnil in Hlast. discriminate. Qed.

(* ====================================================================== *)
(* 2. THE GHOSTS.                                                         *)
(* ====================================================================== *)


(* The gname record [P_fs] is parameterized by.  It stays a PARAMETER rather
   than being read off the fixed layer, because [riscv_crash_pred] is a FIELD
   of [riscvFixedGS] and [P_fs] is what instantiates it -- naming the record
   inside itself would be circular.  Adequacy's obligation is discharged at
   [Pc := fun dk => ∃ γs, P_fs γs … dk], whose existential is exactly
   [P_fs_alloc]'s. *)
Record fs_crash_names := MkFsCrashNames {
  fcn_hist : gname;   (* the committed history, a mono-list *)
  (* THE SWAP COUNTER's gname (phase C2b/D1).  Adequacy allocates it and
     hands the AUTH to the client, so it can only be a parameter here; the
     seam equation the client carries is [fcn_swap γs = riscv_swap_name],
     exactly like [VirtioProto]'s [dn_img γ = disk_img_name]. *)
  fcn_swap : gname;
  (* The GENERATION REGISTRY and the STARTED counter, likewise as parameters
     with seam equations ([fcn_reg γs = riscv_registry_name],
     [fcn_start γs = riscv_start_name]).  They cannot be read off
     [riscvFixedGS] here: [riscv_crash_pred] is a FIELD of that record and
     [P_fs] is what instantiates it, so naming the record inside [P_fs] would
     be circular.  The CLASSES are taken as bare Section constraints below
     rather than bundled into [fsCrashG], so that resolution picks the SAME
     Σ slots the fixed record's own fields were built from -- two sibling
     class fields would be different slots whose resources cannot interact
     (the trap DiskImg.v's header records). *)
  fcn_reg   : gname;
  fcn_start : gname;
}.

Section fs_crash.
  Context `{!fsCrashG Σ, !lockG Σ}.
  (* bare constraints, deliberately not [fsCrashG] fields -- see
     [fs_crash_names] above *)
  Context `{!ghost_mapG Σ nat riscvEraGS, !mono_natG Σ,
            !ghost_varG Σ log_mirror, !diskImgG Σ}.

  (* -------------------------------------------------------------------- *)
  (* 2a. the committed-history mono-list                                   *)
  (* -------------------------------------------------------------------- *)

  Definition fs_hist_auth (γ : gname)
      (l : list (gmap Z (list (bv 8)))) : iProp Σ :=
    own γ (●ML (l : list fs_histO)).

  Definition fs_hist_lb (γ : gname)
      (l : list (gmap Z (list (bv 8)))) : iProp Σ :=
    own γ (◯ML (l : list fs_histO)).

  Global Instance fs_hist_lb_persistent γ l : Persistent (fs_hist_lb γ l).
  Proof. rewrite /fs_hist_lb. apply _. Qed.

  Lemma fs_hist_alloc (l : list (gmap Z (list (bv 8)))) :
    ⊢ |==> ∃ γ : gname, fs_hist_auth γ l ∗ fs_hist_lb γ l.
  Proof.
    iMod (own_alloc (●ML (l : list fs_histO) ⋅ ◯ML (l : list fs_histO)))
      as (γ) "[Ha Hf]".
    { apply mono_list_both_valid_L. reflexivity. }
    iModIntro. iExists γ. iFrame.
  Qed.

  Lemma fs_hist_snapshot γ l :
    fs_hist_auth γ l -∗ fs_hist_auth γ l ∗ fs_hist_lb γ l.
  Proof.
    rewrite /fs_hist_auth /fs_hist_lb -own_op -mono_list_auth_lb_op.
    iIntros "$".
  Qed.

  Lemma fs_hist_valid γ l l' :
    fs_hist_auth γ l -∗ fs_hist_lb γ l' -∗ ⌜l' `prefix_of` l⌝.
  Proof.
    rewrite /fs_hist_auth /fs_hist_lb. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro. by apply mono_list_both_valid_L in Hv.
  Qed.

  Lemma fs_hist_update γ l l' :
    l `prefix_of` l' -> fs_hist_auth γ l ==∗ fs_hist_auth γ l'.
  Proof.
    intros Hpre. rewrite /fs_hist_auth. iIntros "Ha".
    iApply (own_update with "Ha"). by apply mono_list_update.
  Qed.

  (* -------------------------------------------------------------------- *)
  (* 2b. the FS BOOT TOKEN (phase D's generation swap)                     *)
  (*                                                                       *)
  (* One-shot and per-era: the era boot bundle will carry it, and the arm  *)
  (* of [P_fs] that is CHECKED OUT holds it.  A later generation swaps ITS *)
  (* token in using the recorded pure picture -- abandonment, not          *)
  (* revocation, exactly the crash layer's own pattern.  In C1 this is a   *)
  (* DEFINITION plus its exclusivity; the protocol is phase D's.           *)
  (* -------------------------------------------------------------------- *)

  Definition fs_boot_tok (γg : gname) : iProp Σ := lock_tok_excl γg.

  Lemma fs_boot_tok_alloc : ⊢ |==> ∃ γg : gname, fs_boot_tok γg.
  Proof. rewrite /fs_boot_tok. iApply lock_tok_excl_alloc. Qed.

  Lemma fs_boot_tok_excl γg : fs_boot_tok γg -∗ fs_boot_tok γg -∗ False.
  Proof. rewrite /fs_boot_tok. iApply lock_tok_excl_exclusive. Qed.

  Global Instance fs_boot_tok_timeless γg : Timeless (fs_boot_tok γg).
  Proof. rewrite /fs_boot_tok. apply _. Qed.

  (* -------------------------------------------------------------------- *)
  (* 2c. the tie's CLIENT-SIDE half and the receipts                       *)
  (* -------------------------------------------------------------------- *)

  (* A DURABILITY RECEIPT: persistent evidence that [D] was, at some point,
     the committed state.  (The lower bound records the whole prefix, so a
     receipt also pins everything committed before it -- which is what makes
     two receipts comparable, phase D's sys_sync.) *)
  Definition fs_receipt (γs : fs_crash_names)
      (D : gmap Z (list (bv 8))) : iProp Σ :=
    (∃ l : list (gmap Z (list (bv 8))), fs_hist_lb (fcn_hist γs) (l ++ [D]))%I.

  Global Instance fs_receipt_persistent γs D : Persistent (fs_receipt γs D).
  Proof. rewrite /fs_receipt. apply _. Qed.

  (* ==================================================================== *)
  (* 3. [P_fs] -- THE CRASH PREDICATE.                                     *)
  (* ==================================================================== *)

  (* ==================================================================== *)
  (* THE GENERATION ARM (phase C2b/D1): AT REST, or CHECKED OUT by an era.  *)
  (*                                                                        *)
  (* The counter [c] is the whole identification mechanism.  [c = 0] is at   *)
  (* rest (no era has ever taken custody); [c = S g''] means generation      *)
  (* [g''] holds custody, and the arm then carries that era's registry       *)
  (* element, its started certificate, and HALF of its log-region mirror --  *)
  (* the other half being era-side, in the log layer.                        *)
  (*                                                                        *)
  (* THE SQUEEZE.  A WAL write's fupd arrives with its own swap receipt      *)
  (* [swap_lb (S g)] (so [S g <= c], which both refutes the at-rest arm and  *)
  (* gives [g <= g'']) and, threaded in by the DMA completion, the           *)
  (* started-generations auth at [g + 1] (so [S g'' <= g + 1], i.e.          *)
  (* [g'' <= g]).  Hence [g'' = g]; [era_registered] agreement at the shared *)
  (* key gives [E'' = E]; and the mirror gname is identified, so the two     *)
  (* halves meet.  Retiring an arm needs NO identification -- only the       *)
  (* upper bound -- which is why a fresh era can always swap.                *)
  (* ==================================================================== *)

  (* the registry element and the started certificate, at the PARAMETER
     gnames.  Both persistent, as their fixed-layer twins are. *)
  Definition fs_era_reg (γs : fs_crash_names) (g : nat) (E : riscvEraGS)
      : iProp Σ := (g ↪[fcn_reg γs]□ E)%I.
  Definition fs_started (γs : fs_crash_names) (g : nat) : iProp Σ :=
    mono_nat_lb_own (fcn_start γs) (S g).

  Global Instance fs_era_reg_persistent γs g E : Persistent (fs_era_reg γs g E).
  Proof. rewrite /fs_era_reg. apply _. Qed.
  Global Instance fs_started_persistent γs g : Persistent (fs_started γs g).
  Proof. rewrite /fs_started. apply _. Qed.

  Definition fs_custody (γs : fs_crash_names) (cov : gset Z) (ls : Z)
      (dk : Z -> bv 8) (g'' : nat) : iProp Σ :=
    (∃ (E'' : riscvEraGS) (M : log_mirror),
       fs_era_reg γs g'' E'' ∗ fs_started γs g'' ∗
       ghost_var (era_mirror_name E'') (1/2) M ∗
       ⌜log_mirror_ok M (fs_blocks dk) cov ls⌝)%I.

  Definition fs_arm (γs : fs_crash_names) (cov : gset Z) (ls : Z)
      (dk : Z -> bv 8) : iProp Σ :=
    (∃ c : nat,
       mono_nat_auth_own (fcn_swap γs) 1 c ∗
       (⌜c = 0%nat⌝ ∨ ∃ g'' : nat, ⌜c = S g''⌝ ∗ fs_custody γs cov ls dk g''))%I.

  (* the at-rest arm, as adequacy mints it *)
  Lemma fs_arm_at_rest γs cov ls dk :
    mono_nat_auth_own (fcn_swap γs) 1 0%nat ⊢ fs_arm γs cov ls dk.
  Proof.
    iIntros "Ha". rewrite /fs_arm. iExists 0%nat. iFrame "Ha". by iLeft.
  Qed.

  (* the upper bound RETIREMENT needs, and it is all it needs: whatever arm is
     there, its generation is at most the ambient one.  No identification --
     which is exactly why a fresh era can always swap, including after a
     crash that stranded the previous era's mirror half. *)
  Local Lemma fs_custody_started γs cov ls dk g'' :
    fs_custody γs cov ls dk g'' -∗
    fs_started γs g'' ∗ fs_custody γs cov ls dk g''.
  Proof.
    rewrite /fs_custody. iIntros "H".
    iDestruct "H" as (E M) "(#Hr & #Hs & Hm & %Hok)".
    iSplitR; [iExact "Hs"|].
    iExists E, M. iFrame "Hr Hs Hm". iPureIntro. exact Hok.
  Qed.

  Local Lemma fs_arm_le γs cov ls dk (g n c : nat) :
    n = (g + 1)%nat ->
    mono_nat_auth_own (fcn_start γs) 1 n -∗
    (⌜c = 0%nat⌝ ∨ ∃ g'' : nat, ⌜c = S g''⌝ ∗ fs_custody γs cov ls dk g'') -∗
    ⌜(c <= S g)%nat⌝ ∗ mono_nat_auth_own (fcn_start γs) 1 n ∗
    (⌜c = 0%nat⌝ ∨ ∃ g'' : nat, ⌜c = S g''⌝ ∗ fs_custody γs cov ls dk g'').
  Proof.
    intros ->. iIntros "Hsa Hd".
    iDestruct "Hd" as "[%Hc0 | Hc]".
    { iFrame "Hsa". iSplitR; [iPureIntro; lia|]. by iLeft. }
    iDestruct "Hc" as (g'') "[%Hc Hcust]".
    iDestruct (fs_custody_started with "Hcust") as "[#Hst Hcust]".
    rewrite /fs_started.
    iDestruct (mono_nat_lb_own_valid with "Hsa Hst") as %[_ Hle].
    iFrame "Hsa". iSplitR; [iPureIntro; lia|].
    iRight. iExists g''. iSplitR; [done|]. iExact "Hcust".
  Qed.

  (* ==================================================================== *)
  (* THE SWAP: retire whatever arm is there, install THIS era's custody.    *)
  (* It rides a write fupd (initlog's final write_head), so it takes the    *)
  (* started auth the completion threaded in and hands it straight back.    *)
  (* ==================================================================== *)
  (* TWO IMAGES, and that is what a boot swap needs: the arm comes in at the
     PRE-write image and goes back out at the POST-write one.  Retirement
     drops the incoming custody wholesale -- the only thing read out of it is
     its generation ([fs_custody_started], which does not mention the image) --
     so nothing about the two has to agree.  The old one-image statement is
     the [dk = dk'] instance. *)
  Lemma fs_arm_swap (γs : fs_crash_names) (cov : gset Z) (ls : Z)
      (dk dk' : Z -> bv 8)
      (g : nat) (E : riscvEraGS) (n : nat) (M : log_mirror) :
    n = (g + 1)%nat ->
    log_mirror_ok M (fs_blocks dk') cov ls ->
    fs_era_reg γs g E -∗ fs_started γs g -∗
    mono_nat_auth_own (fcn_start γs) 1 n -∗
    ghost_var (era_mirror_name E) (1/2) M -∗
    fs_arm γs cov ls dk ==∗
      fs_arm γs cov ls dk' ∗ mono_nat_auth_own (fcn_start γs) 1 n ∗
      mono_nat_lb_own (fcn_swap γs) (S g).
  Proof.
    intros Hn Hok. iIntros "#Hreg #Hst Hsa Hmir Harm".
    rewrite {1}/fs_arm. iDestruct "Harm" as (c) "[Hc Hrest]".
    iDestruct (fs_arm_le γs cov ls dk g n c Hn with "Hsa Hrest")
      as "(%Hle & Hsa & _)".
    iMod (mono_nat_own_update (S g) with "Hc") as "[Hc #Hlb]"; [lia|].
    iModIntro. iFrame "Hsa Hlb".
    rewrite /fs_arm. iExists (S g). iFrame "Hc". iRight.
    iExists g. iSplitR; [done|].
    rewrite /fs_custody. iExists E, M. iFrame "Hreg Hst Hmir".
    iPureIntro. exact Hok.
  Qed.

  (* ==================================================================== *)
  (* THE ACCESSOR every WAL write's fupd runs on: the SQUEEZE, then the     *)
  (* mirror's two halves meet, then the arm re-closes at the POST-write     *)
  (* image with the updated picture.                                       *)
  (* ==================================================================== *)
  Lemma fs_arm_acc (γs : fs_crash_names) (cov : gset Z) (ls : Z)
      (dk : Z -> bv 8)
      (g : nat) (E : riscvEraGS) (n : nat) (M0 : log_mirror) :
    n = (g + 1)%nat ->
    fs_era_reg γs g E -∗ mono_nat_lb_own (fcn_swap γs) (S g) -∗
    mono_nat_auth_own (fcn_start γs) 1 n -∗
    ghost_var (era_mirror_name E) (1/2) M0 -∗
    fs_arm γs cov ls dk -∗
      ⌜log_mirror_ok M0 (fs_blocks dk) cov ls⌝ ∗
      mono_nat_auth_own (fcn_start γs) 1 n ∗
      (∀ (dk' : Z -> bv 8) (M' : log_mirror),
         ⌜log_mirror_ok M' (fs_blocks dk') cov ls⌝ ==∗
           fs_arm γs cov ls dk' ∗ ghost_var (era_mirror_name E) (1/2) M').
  Proof.
    intros Hn. iIntros "#Hreg #Hswlb Hsa Hmir Harm".
    rewrite {1}/fs_arm. iDestruct "Harm" as (c) "[Hc Hrest]".
    (* ABOVE: the arm's generation is at most the ambient one *)
    iDestruct (fs_arm_le γs cov ls dk g n c Hn with "Hsa Hrest")
      as "(%Hup & Hsa & Hrest)".
    (* BELOW: our own swap receipt says it is at least ours *)
    iDestruct (mono_nat_lb_own_valid with "Hc Hswlb") as %[_ Hlow].
    (* so the at-rest arm is refuted and the generations coincide *)
    destruct c as [|c']; [exfalso; lia|].
    iDestruct "Hrest" as "[%Hc0 | Hc2]"; [discriminate|].
    iDestruct "Hc2" as (g'') "[%Hceq Hcust]".
    assert (Hgg : g'' = g) by lia. subst g''.
    rewrite /fs_custody. iDestruct "Hcust" as (E'' M) "(#Hreg2 & #Hst2 & Hmir2 & %Hok)".
    (* the registry pins the era record, hence the mirror's gname *)
    rewrite /fs_era_reg.
    iDestruct (ghost_map_elem_agree with "Hreg Hreg2") as %<-.
    iDestruct (ghost_var_agree with "Hmir Hmir2") as %<-.
    iFrame "Hsa". iSplitR; [iPureIntro; exact Hok|].
    iIntros (dk' M') "%Hok'".
    iMod (ghost_var_update_halves M' with "Hmir Hmir2") as "[Hmir Hmir2]".
    iModIntro. iFrame "Hmir".
    assert (Hcg : c' = g) by lia. subst c'.
    rewrite /fs_arm. iExists (S g). iFrame "Hc". iRight.
    iExists g. iSplitR; [done|].
    rewrite /fs_custody. iExists E, M'. iFrame "Hreg Hst2 Hmir2".
    iPureIntro. exact Hok'.
  Qed.

  (* THE CRASH PREDICATE, i.e. the intended value of
     [RiscvPtsto.riscv_crash_pred] (the adequacy [Pc] parameter).  It is a
     PREDICATE ON THE DISK IMAGE [dk], and the machine layer's tie
     ([RiscvPtsto.disk_tie], whose other half is [state_interp]'s fixed
     conjunct) is what guarantees that [dk] is the REAL disk -- so nothing
     here has to own a ghost about it.  Read it as: there is a pure record
     [r] such that
       - the committed history is [fr_hist r] (its lower bounds are the
         receipts already handed out), and
       - [r] is WELL FORMED AT [dk]: recovery of the physical disk's block
         view is the last committed state.
     Everything a client ever learns at a crash comes out of the second
     conjunct; the index is what makes it a statement about the REAL disk
     rather than about a ghost. *)
  Definition P_fs (γs : fs_crash_names) (cov : gset Z) (logstart : Z)
      (dk : Z -> bv 8) : iProp Σ :=
    (∃ r : fs_rec,
       fs_hist_auth (fcn_hist γs) (fr_hist r) ∗
       ⌜fs_rec_wf r (fs_blocks dk) cov logstart⌝ ∗
       fs_arm γs cov logstart dk)%I.

  (* THE CRASH PREDICATE AS ADEQUACY FIXES IT, at RAW gnames.  Adequacy
     allocates the swap counter, the generation registry and the started
     counter inside its own proof, so a client-chosen [Pc] can only name them
     if they are PASSED to it -- which is what [HPc]'s three arguments are.
     [γs] stays existential because the history gname is allocated under the
     update, and the three seam equations are all any WAL fupd needs (they are
     exactly what [fs_arm_acc] reads).  Stated HERE, in the section that must
     stay [riscvFixedGS]-free, because this IS the value the fixed record's
     [riscv_crash_pred] field is built from. *)
  Definition P_fs_rec_named (γsw γreg γst : gname) (cov : gset Z) (ls : Z)
      (dk : Z -> bv 8) : iProp Σ :=
    (∃ γs : fs_crash_names,
       ⌜fcn_swap γs = γsw /\ fcn_reg γs = γreg /\ fcn_start γs = γst⌝ ∗
       P_fs γs cov ls dk)%I.

  (* THE EXTENT: every block the record reads -- the covered blocks and the
     log region -- lies inside the durable disk's [N] bytes.  A pure fact
     about the geometry, invariant under every write. *)
  Definition fs_extent (cov : gset Z) (ls : Z) (N : nat) : Prop :=
    forall b : Z, b ∈ cov ∪ log_region_set ls ->
      0 <= b /\ (b + 1) * Z.of_nat BSIZE <= Z.of_nat N.

  (* THE CRASH PREDICATE, AS THE OWNER OF THE DURABLE DISK
     (claude-notes/design/crash.md, "The durable disk: ONE fixed gname").
     The record above is about an image [dk]; THIS is what pins [dk] to the
     real disk: the fragments of the fixed-layer map over all of [0, N),
     which only the machine's auth can disagree with.  No thread that can
     die ever owns one of them; a DMA completion lends the auth for the
     instant, and [fs_permit_of_rec] below is how the record's own view
     shift runs under that loan. *)
  Definition P_fs_named (γd : gname) (N : nat) (γsw γreg γst : gname)
      (cov : gset Z) (ls : Z) : iProp Σ :=
    (∃ dk : Z -> bv 8,
       disk_img_bytes γd 0 (disk_read dk 0 N) ∗
       ⌜fs_extent cov ls N⌝ ∗
       P_fs_rec_named γsw γreg γst cov ls dk)%I.

  (* the record reads the image only on the extent: two images that agree
     on the durable bytes carry the same record *)
  Lemma fs_blocks_agree (dk dk' : Z -> bv 8) (N : nat) (b : Z) :
    disk_read dk 0 N = disk_read dk' 0 N ->
    0 <= b -> (b + 1) * Z.of_nat BSIZE <= Z.of_nat N ->
    fs_blocks dk b = fs_blocks dk' b.
  Proof.
    intros Heq Hb0 HbN. rewrite /fs_blocks.
    apply list_eq. intro j. rewrite /disk_read !list_lookup_fmap.
    destruct (decide (j < BSIZE)%nat) as [Hj | Hj].
    - rewrite (lookup_seq_lt _ _ _ Hj). cbn. f_equal.
      apply (disk_read_agree dk dk' N Heq). unfold BSIZE in *. lia.
    - assert (Hge : (BSIZE <= j)%nat) by lia.
      rewrite (lookup_seq_ge 0%nat BSIZE j Hge). reflexivity.
  Qed.

  Lemma fs_restrict_agree (dk dk' : Z -> bv 8) (N : nat) (s : gset Z)
      (cov : gset Z) (ls : Z) :
    disk_read dk 0 N = disk_read dk' 0 N ->
    fs_extent cov ls N ->
    s ⊆ cov ∪ log_region_set ls ->
    fs_restrict (fs_blocks dk) s = fs_restrict (fs_blocks dk') s.
  Proof.
    intros Heq Hext Hs. apply fs_restrict_ext. intros b Hb.
    destruct (Hext b (Hs b Hb)) as [Hb0 HbN].
    exact (fs_blocks_agree dk dk' N b Heq Hb0 HbN).
  Qed.

  Lemma P_fs_rec_agree (γsw γreg γst : gname) (cov : gset Z) (ls : Z)
      (N : nat) (dk dk' : Z -> bv 8) :
    disk_read dk 0 N = disk_read dk' 0 N ->
    fs_extent cov ls N ->
    P_fs_rec_named γsw γreg γst cov ls dk -∗ P_fs_rec_named γsw γreg γst cov ls dk'.
  Proof.
    intros Heq Hext.
    assert (Hblk : forall b, b ∈ cov ∪ log_region_set ls ->
                     fs_blocks dk b = fs_blocks dk' b).
    { intros b Hb. destruct (Hext b Hb) as [Hb0 HbN].
      exact (fs_blocks_agree dk dk' N b Heq Hb0 HbN). }
    assert (Hlog : forall b, b ∈ log_region_set ls -> fs_blocks dk b = fs_blocks dk' b).
    { intros b Hb. apply Hblk. apply elem_of_union. by right. }
    assert (Hhdr : log_hdr_bno ls ∈ log_region_set ls).
    { rewrite /log_region_set. apply elem_of_union. right.
      apply elem_of_singleton. reflexivity. }
    assert (Hslot : forall i, (i < LOGBLOCKS)%nat -> log_slot_bno ls i ∈ log_region_set ls).
    { intros i Hi. rewrite /log_region_set. apply elem_of_union. left.
      apply elem_of_list_to_set. apply elem_of_list_fmap. exists i.
      split; [reflexivity |]. apply elem_of_seq. lia. }
    rewrite /P_fs_rec_named. iIntros "H". iDestruct "H" as (γs) "[%Hseq H]".
    iExists γs. iSplitR; [iPureIntro; exact Hseq|].
    rewrite /P_fs. iDestruct "H" as (r) "(Hh & %Hwf & Harm)".
    iExists r. iFrame "Hh". iSplitR.
    { iPureIntro. rewrite /fs_rec_wf in Hwf *.
      destruct Hwf as (Hrec & Hlast & Hhwf & Hdwf).
      pose proof Hhwf as (Hlen & _ & _).
      assert (Hhdreq : fs_blocks dk' (log_hdr_bno ls)
                       = fs_blocks dk (log_hdr_bno ls))
        by (symmetry; exact (Hlog _ Hhdr)).
      split_and!.
      - rewrite /fs_recovery in Hrec *.
        rewrite -(fs_restrict_agree dk dk' N (fs_home_set cov ls) cov ls Heq Hext);
          [| rewrite /fs_home_set; intros x Hx; apply elem_of_union; left;
             exact (proj1 (proj1 (elem_of_difference _ _ _) Hx)) ].
        rewrite Hhdreq.
        rewrite Hrec. apply fs_install_ext_P.
        intros i Hi. rewrite hdr_dec_length in Hi.
        apply Hlog, Hslot. lia.
      - exact Hlast.
      - exact (hdr_wf_ext _ _ _ _ Hhdreq Hhwf).
      - exact Hdwf. }
    rewrite /fs_arm. iDestruct "Harm" as (c) "[Hsw Harm]". iExists c. iFrame "Hsw".
    iDestruct "Harm" as "[$ | Harm]". iRight.
    iDestruct "Harm" as (g'') "[%Hc Hc]". iExists g''. iSplitR; [done|].
    rewrite /fs_custody. iDestruct "Hc" as (E M) "(Hr & Hs & Hm & %Hok)".
    iExists E, M. iFrame "Hr Hs Hm". iPureIntro.
    rewrite /log_mirror_ok in Hok *. intros b Hb.
    rewrite (Hok b Hb). exact (Hblk b Hb).
  Qed.

  (* -------------------------------------------------------------------- *)
  (* 3a. what [P_fs] SAYS                                                   *)
  (* -------------------------------------------------------------------- *)

  (* THE HEADLINE.  At the disk image the machine layer's tie pins, the crash
     predicate says the REAL disk recovers to the last committed state.  This
     is the fact a crash-time client (recovery, sys_sync) consumes. *)
  Lemma P_fs_recovers γs cov logstart dk :
    P_fs γs cov logstart dk -∗
      ⌜exists (D : gmap Z (list (bv 8)))
              (h : list (gmap Z (list (bv 8)))),
         fs_recovery (fs_blocks dk) D cov logstart /\
         h <> [] /\ last h = Some D⌝.
  Proof.
    rewrite /P_fs.
    iIntros "Hp". iDestruct "Hp" as (r) "(_ & %Hwf & _)".
    iPureIntro. exists (fr_D r), (fr_hist r).
    destruct Hwf as (Hrec & Hlast & _).
    split_and!; [exact Hrec | | exact Hlast].
    intros Hnil. rewrite Hnil in Hlast. discriminate.
  Qed.

  (* a receipt is honest: what it names really was committed *)
  Lemma P_fs_receipt_committed γs cov logstart dk D :
    P_fs γs cov logstart dk -∗ fs_receipt γs D -∗
      ⌜exists r : fs_rec,
         fs_rec_wf r (fs_blocks dk) cov logstart /\ D ∈ fr_hist r⌝.
  Proof.
    rewrite /P_fs /fs_receipt.
    iIntros "Hp Hr". iDestruct "Hp" as (r) "(Hauth & %Hwf & _)".
    iDestruct "Hr" as (l) "Hlb".
    iDestruct (fs_hist_valid with "Hauth Hlb") as %[k Hk].
    iPureIntro. exists r. split; [exact Hwf|].
    rewrite Hk -app_assoc elem_of_app elem_of_app.
    right. left. apply elem_of_list_singleton. reflexivity.
  Qed.

  (* -------------------------------------------------------------------- *)
  (* 3b. ALLOCATION -- mkfs's obligation, discharged                        *)
  (* -------------------------------------------------------------------- *)

  (* [P_fs] holds INITIALLY, from nothing but the pure fact that the pristine
     disk recovers to [D0].  This IS the shape of adequacy's [HPc] premise
     ([RiscvAdequacy.riscv_system_adequacy]): a build-from-nothing entailment
     UNDER AN UPDATE, because a crash predicate that owns ghosts is never
     provable from nothing.  The client instantiates
     [Pc := fun dk => ∃ γs, P_fs γs cov logstart dk] and discharges the
     obligation with this lemma. *)
  Lemma P_fs_alloc (γsw γreg γst : gname) (dk0 : Z -> bv 8)
      (D0 : gmap Z (list (bv 8))) (cov : gset Z) (logstart : Z) :
    fs_recovery (fs_blocks dk0) D0 cov logstart ->
    hdr_wf (fs_blocks dk0) cov logstart ->
    mono_nat_auth_own γsw 1 0%nat ⊢ |==> ∃ γs : fs_crash_names,
      ⌜fcn_swap γs = γsw /\ fcn_reg γs = γreg /\ fcn_start γs = γst⌝ ∗
      P_fs γs cov logstart dk0 ∗ fs_receipt γs D0.
  Proof.
    intros Hrec Hhwf. iIntros "Hsw".
    iMod (fs_hist_alloc [D0]) as (γh) "[Hauth #Hlb]".
    iModIntro. iExists (MkFsCrashNames γh γsw γreg γst).
    iSplitR; [iPureIntro; done|].
    iSplitL "Hauth Hsw".
    - rewrite /P_fs. iExists (MkFsRec D0 [D0]).
      iFrame "Hauth".
      iSplitR.
      { iPureIntro. rewrite /fs_rec_wf /=.
        split_and!;
          [exact Hrec | reflexivity | exact Hhwf
          | exact (fs_durable_wf_placeholder _) (* E4: the image discharge *)]. }
      iApply fs_arm_at_rest. iExact "Hsw".
    - rewrite /fs_receipt /=. iExists []. iExact "Hlb".
  Qed.

  (* The mkfs corollary: a freshly formatted disk has an EMPTY on-disk log,
     so its committed state is just its home blocks and no recovery
     hypothesis has to be assumed at all. *)
  Lemma P_fs_alloc_clean (γsw γreg γst : gname) (dk0 : Z -> bv 8)
      (cov : gset Z) (logstart : Z) :
    hdr_n (fs_blocks dk0 (log_hdr_bno logstart)) = 0 ->
    mono_nat_auth_own γsw 1 0%nat ⊢ |==> ∃ γs : fs_crash_names,
      ⌜fcn_swap γs = γsw /\ fcn_reg γs = γreg /\ fcn_start γs = γst⌝ ∗
      P_fs γs cov logstart dk0 ∗
      fs_receipt γs (fs_restrict (fs_blocks dk0)
                       (fs_home_set cov logstart)).
  Proof.
    intros Hn. iApply P_fs_alloc.
    - by apply (fs_recovery_clean (fs_blocks dk0) _ cov logstart Hn).
    - by apply hdr_wf_zero.
  Qed.

End fs_crash.

(* ====================================================================== *)
(* 4. THE SEAM: [riscv_crash_pred] AS [P_fs], AND THE BOOT SWAP'S PERMIT.  *)
(*                                                                        *)
(* A SEPARATE SECTION, over [riscvGS], and that is forced: [P_fs] above is *)
(* what INSTANTIATES the fixed layer's [riscv_crash_pred] field, so its    *)
(* own section must stay [riscvFixedGS]-free -- naming the record inside   *)
(* the value it is built from is circular.  Everything that RELATES the    *)
(* two lives here instead, where the record exists.                        *)
(* ====================================================================== *)
Section fs_crash_seam.
  Context `{!riscvGS Σ, !fsCrashG Σ, !lockG Σ}.

  (* The crash predicate the FS client fixes [Pc] at.  [γs] is EXISTENTIAL
     because adequacy's obligation ([RiscvAdequacy]'s [HPc]) is a
     build-from-nothing entailment: the history gname is allocated under the
     update, so it cannot appear in [Pc]'s own arguments.  The three seam
     equations are what make the record's arm identifiable from outside --
     they are all a WAL fupd needs, since [fs_arm_acc] reads only
     [fcn_swap] / [fcn_reg] / [fcn_start]. *)
  (* the record at an image, at the fixed layer's names *)
  Definition P_fs_rec (cov : gset Z) (ls : Z) (dk : Z -> bv 8) : iProp Σ :=
    P_fs_rec_named riscv_swap_name riscv_registry_name riscv_start_name cov ls dk.

  Global Instance P_fs_rec_timeless cov ls dk : Timeless (P_fs_rec cov ls dk).
  Proof.
    rewrite /P_fs_rec /P_fs_rec_named /P_fs /fs_arm /fs_custody /fs_hist_auth.
    apply _.
  Qed.

  (* the crash predicate itself: the record AND the durable disk's fragments
     at the fixed layer's name and size *)
  Definition P_fs_any (cov : gset Z) (ls : Z) : iProp Σ :=
    P_fs_named riscv_disk_name riscv_disk_size
      riscv_swap_name riscv_registry_name riscv_start_name cov ls.

  Global Instance P_fs_any_timeless cov ls : Timeless (P_fs_any cov ls).
  Proof.
    rewrite /P_fs_any /P_fs_named /P_fs_rec_named /P_fs /fs_arm /fs_custody
      /fs_hist_auth.
    apply _.
  Qed.

  (* The client's persistent handle on "the crash predicate IS my [P_fs]".
     Adequacy discharges it by conversion when it instantiates [Pc]; every
     WAL fupd consumes it to get at the record. *)
  Definition fs_crash_seam (cov : gset Z) (ls : Z) : iProp Σ :=
    (□ ((riscv_crash_pred -∗ P_fs_any cov ls) ∗
        (P_fs_any cov ls -∗ riscv_crash_pred)))%I.

  (* A PERMIT STATED ON THE RECORD ALONE: what each WAL fupd actually proves.
     [fs_permit_of_rec] turns it into the machine's [disk_write_permit] by
     doing the disk bookkeeping once -- agree the fragments against the lent
     auth (so the record's [dk] IS the machine's image), run the record's
     view shift, move the fragments and the auth to the post-write image. *)
  Definition fs_rec_permit (cov : gset Z) (ls : Z) (gd : nat) (w : disk_wr)
      (Q : iProp Σ) : iProp Σ :=
    (∀ (dk : Z -> bv 8) (n : nat),
       start_auth n -∗ ⌜n = (gd + 1)%nat⌝ -∗
       ▷ P_fs_rec cov ls dk ={∅}=∗
         ▷ P_fs_rec cov ls (wr_apply w dk) ∗ start_auth n ∗ Q)%I.

  Lemma fs_permit_of_rec (cov : gset Z) (ls : Z) (gd : nat) (w : disk_wr)
      (Q : iProp Σ) :
    fs_crash_seam cov ls -∗
    fs_rec_permit cov ls gd w Q -∗
    disk_write_permit gd w Q.
  Proof.
    iIntros "#Hseam Hrec". rewrite /disk_write_permit.
    iIntros (dk n) "Hsa %Hn Ha HP".
    iDestruct "Hseam" as "[Hfwd Hbwd]".
    iAssert (▷ P_fs_any cov ls)%I with "[HP]" as "HP"; [iNext; by iApply "Hfwd"|].
    iMod "HP". rewrite /P_fs_any /P_fs_named.
    iDestruct "HP" as (dk0) "(Hfr & %Hext & HPr)".
    (* the fragments read the machine's image: the record's [dk0] agrees
       with [dk] on the whole durable disk *)
    rewrite /disk_fixed_auth.
    iDestruct (disk_img_sized_read with "Ha Hfr") as %Hrd.
    rewrite disk_read_length in Hrd.
    iDestruct (P_fs_rec_agree _ _ _ cov ls riscv_disk_size dk0 dk
                 (eq_sym Hrd) Hext with "HPr") as "HPr".
    iMod ("Hrec" $! dk n with "Hsa [//] [HPr]") as "(HPr & Hsa & HQ)";
      [iNext; iExact "HPr"|].
    (* the fragments and the auth, to the post-write image *)
    iEval (rewrite -Hrd) in "Hfr".
    iMod (disk_img_sized_write _ _ dk (wr_apply w dk) with "Ha Hfr") as "[Ha Hfr]".
    iModIntro. iFrame "Ha Hsa HQ".
    iNext. iApply "Hbwd". rewrite /P_fs_any /P_fs_named.
    iExists (wr_apply w dk). iFrame "Hfr HPr". iPureIntro. exact Hext.
  Qed.

  Global Instance fs_crash_seam_persistent cov ls :
    Persistent (fs_crash_seam cov ls).
  Proof. rewrite /fs_crash_seam. apply _. Qed.

  (* ==================================================================== *)
  (* THE BOOT SWAP'S PERMIT (phase C2b/D1 stage 3): what [initlog] curries  *)
  (* into its final [write_head].                                          *)
  (*                                                                       *)
  (* THE SWAP RE-BASES THE DURABLE STATE, it does not preserve it -- and    *)
  (* that is the honest boot semantics, not a weakening.  Every LATER WAL   *)
  (* fupd learns the PRE-write image's log region out of the custody arm's  *)
  (* [log_mirror_ok M (fs_blocks dk) ls]; the swap is the one fupd that has  *)
  (* no custody yet, so it cannot know what the on-disk header said.        *)
  (* ([initlog]'s clean-image precondition is about the block it READ, and   *)
  (* no curryable fact ties that to this fupd's universally quantified       *)
  (* [dk].)  So the record's [fr_D] moves to what the CLEARED disk recovers  *)
  (* to and the history is EXTENDED by it -- a prefix extension, so every    *)
  (* receipt handed out before the crash stays valid.                        *)
  (*                                                                        *)
  (* The whole mirror VARIABLE goes in (not a half): the swap sets its value *)
  (* to the post-write picture -- free, [mirror_of_ok] -- splits it there,   *)
  (* hands one half to the arm and returns the other in [Q].  The clean      *)
  (* header of the returned half comes from the write ITSELF                 *)
  (* ([fs_blocks_write_eq] then [hdr_dec_zero]), which is why no fact about  *)
  (* the pre-image is needed anywhere.                                       *)
  (* ==================================================================== *)
  Lemma fs_swap_permit_rec `{GEN : GenId} (cov : gset Z) (ls : Z)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_n bs = 0 ->
    era_registered gen_id riscv_eraGS -∗
    gen_started gen_id -∗
    (∃ M0 : log_mirror, ghost_var mirror_name 1 M0) -∗
    fs_rec_permit cov ls gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_at ls (0%nat, []) ∗ swap_lb (S gen_id)).
  Proof.
    intros Hlen Hn0. iIntros "#Hreg #Hst Hmir".
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    (* the index, in the block view's spelling *)
    assert (Hidx : (1024 * log_hdr_bno ls)%Z
                   = (log_hdr_bno ls * Z.of_nat BSIZE)%Z)
      by (rewrite /BSIZE; lia).
    cbn [wr_apply fst snd]. rewrite Hidx.
    set (dk' := disk_write dk (log_hdr_bno ls * Z.of_nat BSIZE)%Z bs).
    (* the two facts the pure transition wants, straight off the write *)
    assert (Hhit : fs_blocks dk' (log_hdr_bno ls) = bs)
      by (apply fs_blocks_write_eq, Hlen).
    assert (Hmiss : forall c, c <> log_hdr_bno ls -> fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc; apply fs_blocks_write_ne; [exact Hlen | exact Hc]).
    (* through the seam, and the record is timeless *)
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm)".
    (* THE NEW DURABLE STATE, and the history extension *)
    set (D' := fs_restrict (fs_blocks dk) (fs_home_set cov ls)).
    iMod (fs_hist_update (fcn_hist γs) (fr_hist r) (fr_hist r ++ [D'])
            with "Hhist") as "Hhist"; [by eexists|].
    (* the mirror: to the POST image's picture, then split *)
    iDestruct "Hmir" as (M0) "Hmir".
    iMod (ghost_var_update (mirror_of (fs_blocks dk')) with "Hmir") as "Hmir".
    iEval (rewrite -Qp.half_half) in "Hmir".
    iDestruct (ghost_var_split with "Hmir") as "[Hm1 Hm2]".
    (* the era's certificates, at the record's own gnames *)
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (fs_started γs gen_id) as "#Hst2".
    { rewrite /fs_started Hstn. iExact "Hst". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iMod (fs_arm_swap γs cov ls dk dk' gen_id riscv_eraGS n
            (mirror_of (fs_blocks dk')) Hn1 (mirror_of_ok _ _ _)
            with "Hreg2 Hst2 Hsa Hm2 Harm") as "(Harm & Hsa & #Hswlb)".
    iModIntro.
    iSplitL "Hhist Harm".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists (MkFsRec D' (fr_hist r ++ [D'])).
      iFrame "Hhist". iSplitR; [| iExact "Harm"].
      iPureIntro. rewrite /fs_rec_wf /=. split_and!.
      - exact (fs_recovery_clear (fs_blocks dk) (fs_blocks dk') cov ls bs
                 Hhit Hn0 Hmiss).
      - rewrite last_snoc. reflexivity.
      - apply hdr_wf_zero. rewrite Hhit. exact Hn0.
      - exact (fs_durable_wf_placeholder _). (* RE-BASE; gated on H/F1 *) }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    iSplitL "Hm1".
    { rewrite /log_mirror_at /log_mirror_half. iExists (mirror_of (fs_blocks dk')).
      iFrame "Hm1". iPureIntro.
      rewrite /lm_hdr /mirror_of /= Hhit. exact (hdr_dec_zero bs Hn0). }
    rewrite /swap_lb -Hsw. iExact "Hswlb".
  Qed.

  Lemma fs_swap_permit `{GEN : GenId} (cov : gset Z) (ls : Z)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_n bs = 0 ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    gen_started gen_id -∗
    (∃ M0 : log_mirror, ghost_var mirror_name 1 M0) -∗
    disk_write_permit gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_at ls (0%nat, []) ∗ swap_lb (S gen_id)).
  Proof.
    intros P0 P1. iIntros "#Hseam H0 H1 H2".
    iApply (fs_permit_of_rec with "Hseam").
    iApply (fs_swap_permit_rec with "H0 H1 H2"); try assumption.
  Qed.

  (* ==================================================================== *)
  (* THE THREE WAL DURABILITY FUPDS (phase C2b/D1 stage 4).                *)
  (*                                                                       *)
  (* Each is [fs_swap_permit]'s sibling and runs the same five steps: open  *)
  (* the seam, strip the (timeless) record inside the [={∅}=∗], run         *)
  (* [fs_arm_acc] at [(gen_id, riscv_eraGS)] -- which is where the era's    *)
  (* half of the log-region mirror MEETS the custody arm's, and therefore   *)
  (* the only place a STATELESS view shift can learn what the previous      *)
  (* writes put on the disk -- move [fr_D] with the matching pure           *)
  (* transition, and re-close the arm at the post-write image.              *)
  (*                                                                        *)
  (* WHAT EACH ONE READS OUT OF THE MIRROR, and nothing more:                *)
  (*   log fill : the header is CLEAN, so recovery does not look at the      *)
  (*              slots at all and the write is invisible to it.             *)
  (*   commit   : nothing -- the new durable state is COMPUTABLE from the     *)
  (*              pre-write image, which is what makes the jump provable      *)
  (*              without knowing anything about the disk.                    *)
  (*   install  : the header is the [(n, W)] the commit wrote, so the block   *)
  (*              being overwritten is a LOGGED one and recovery re-installs  *)
  (*              it from the slot regardless of what is written -- the       *)
  (*              content of a home write is genuinely irrelevant here        *)
  (*              ([fs_recovery_install] does not use it).                    *)
  (* ==================================================================== *)

  (* A durability receipt at the record's own gnames, with [γs] existential
     for the same reason [P_fs_any] has it: adequacy allocates the history
     gname under the update, so no client-visible constant can name it. *)
  Definition fs_receipt_any (D : gmap Z (list (bv 8))) : iProp Σ :=
    (∃ γs : fs_crash_names,
       ⌜fcn_swap γs = riscv_swap_name /\ fcn_reg γs = riscv_registry_name /\
        fcn_start γs = riscv_start_name⌝ ∗ fs_receipt γs D)%I.

  Global Instance fs_receipt_any_persistent D : Persistent (fs_receipt_any D).
  Proof. rewrite /fs_receipt_any. apply _. Qed.

  (* ---- (1) LOG FILL: write_log copying a logged block into slot [i]. ---- *)
  Lemma fs_logfill_permit_rec `{GEN : GenId} (cov : gset Z) (ls : Z) (i : nat)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    (i < LOGBLOCKS)%nat ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_at ls (0%nat, []) -∗
    fs_rec_permit cov ls gen_id (Some ((1024 * log_slot_bno ls i)%Z, bs))
      (log_mirror_at ls (0%nat, [])).
  Proof.
    intros Hlen Hi. iIntros "#Hreg #Hswlb Hmir".
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    assert (Hidx : (1024 * log_slot_bno ls i)%Z
                   = (log_slot_bno ls i * Z.of_nat BSIZE)%Z)
      by (rewrite /BSIZE; lia).
    cbn [wr_apply fst snd]. rewrite Hidx.
    set (dk' := disk_write dk (log_slot_bno ls i * Z.of_nat BSIZE)%Z bs).
    assert (Hmiss : forall c, c <> log_slot_bno ls i ->
                      fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc; apply fs_blocks_write_ne; [exact Hlen | exact Hc]).
    (* through the seam; the record is timeless, so the [▷] strips *)
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm)".
    rewrite /log_mirror_at /log_mirror_half.
    iDestruct "Hmir" as (M0) "[Hmir %HM0]".
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    (* THE ONE FACT READ OUT OF THE MIRROR: the on-disk header is clean *)
    assert (Hdk0 : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (0%nat, []))
      by (rewrite -(Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)); exact HM0).
    assert (Hn0 : hdr_n (fs_blocks dk (log_hdr_bno ls)) = 0)
      by (rewrite -hdr_dec_n Hdk0 //).
    assert (Hhdr' : fs_blocks dk' (log_hdr_bno ls) = fs_blocks dk (log_hdr_bno ls))
      by (apply Hmiss, not_eq_sym, log_slot_ne_hdr).
    iMod ("Hclose" $! dk' (mirror_of (fs_blocks dk'))
            with "[%]") as "[Harm Hmir]"; [exact (mirror_of_ok _ _ _)|].
    iModIntro.
    iSplitL "Hhist Harm".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists r. iFrame "Hhist". iSplitR; [| iExact "Harm"].
      iPureIntro. destruct Hwf as (Hrec & Hlast & Hhwf & Hdwf). split_and!.
      - exact (fs_recovery_logfill (fs_blocks dk) (fs_blocks dk') (fr_D r) cov ls i
               Hi Hmiss Hn0 Hrec).
      - exact Hlast.
      - exact (hdr_wf_ext _ _ _ _ Hhdr' Hhwf).
      - exact Hdwf. (* the committed view is untouched *) }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    rewrite /log_mirror_at /log_mirror_half.
    iExists (mirror_of (fs_blocks dk')). iFrame "Hmir". iPureIntro.
    rewrite /lm_hdr /mirror_of /= Hhdr' Hdk0 //.
  Qed.

  Lemma fs_logfill_permit `{GEN : GenId} (cov : gset Z) (ls : Z) (i : nat)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    (i < LOGBLOCKS)%nat ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_at ls (0%nat, []) -∗
    disk_write_permit gen_id (Some ((1024 * log_slot_bno ls i)%Z, bs))
      (log_mirror_at ls (0%nat, [])).
  Proof.
    intros P0 P1. iIntros "#Hseam H0 H1 H2".
    iApply (fs_permit_of_rec with "Hseam").
    iApply (fs_logfill_permit_rec with "H0 H1 H2"); try assumption.
  Qed.

  (* ---- (2) COMMIT: write_head storing a header that decodes to (n, W). ---- *)
  (* THE commit point.  [Q] carries the mirror half forward at the NEW header
     picture -- which is what the install fupds then read -- plus a durability
     receipt.  The receipt cannot NAME its state: the new durable state is
     [fs_install] over [fs_restrict (fs_blocks dk) …], and the home part of
     the physical disk is not something the era holds any picture of (the
     mirror is the LOG REGION's).  Naming it is phase D's sys_sync work, which
     needs a CURRENT-state witness rather than a mono-list lower bound. *)
  Lemma fs_commit_permit_rec `{GEN : GenId} (cov : gset Z) (ls : Z)
      (h : nat * list Z) (nn : nat) (Ws : list Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_dec bs = (nn, Ws) ->
    (* the batch's recorded facts ([LogInv.log_batch]'s three pure rows),
       here because the header this permit writes must satisfy [hdr_wf] *)
    (nn <= LOGBLOCKS)%nat ->
    NoDup Ws ->
    (forall b : Z, b ∈ Ws -> b ∈ cov /\ b ∉ log_region_set ls) ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_at ls h -∗
    fs_rec_permit cov ls gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_at ls (nn, Ws) ∗ (∃ D : gmap Z (list (bv 8)), fs_receipt_any D)).
  Proof.
    intros Hlen Hdec Hnn Hnd Hin. iIntros "#Hreg #Hswlb Hmir".
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    assert (Hidx : (1024 * log_hdr_bno ls)%Z
                   = (log_hdr_bno ls * Z.of_nat BSIZE)%Z)
      by (rewrite /BSIZE; lia).
    cbn [wr_apply fst snd]. rewrite Hidx.
    set (dk' := disk_write dk (log_hdr_bno ls * Z.of_nat BSIZE)%Z bs).
    assert (Hhit : fs_blocks dk' (log_hdr_bno ls) = bs)
      by (apply fs_blocks_write_eq, Hlen).
    assert (Hmiss : forall c, c <> log_hdr_bno ls ->
                      fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc; apply fs_blocks_write_ne; [exact Hlen | exact Hc]).
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm)".
    rewrite /log_mirror_at /log_mirror_half.
    iDestruct "Hmir" as (M0) "[Hmir %HM0]".
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    (* THE NEW DURABLE STATE, computable from the PRE-write image *)
    set (D' := fs_install (fs_blocks dk) ls (hdr_dec bs).2
                 (fs_restrict (fs_blocks dk) (fs_home_set cov ls))).
    iMod (fs_hist_update (fcn_hist γs) (fr_hist r) (fr_hist r ++ [D'])
            with "Hhist") as "Hhist"; [by eexists|].
    iDestruct (fs_hist_snapshot with "Hhist") as "[Hhist #Hlb]".
    iMod ("Hclose" $! dk' (mirror_of (fs_blocks dk'))
            with "[%]") as "[Harm Hmir]"; [exact (mirror_of_ok _ _ _)|].
    iModIntro.
    iSplitL "Hhist Harm".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists (MkFsRec D' (fr_hist r ++ [D'])).
      iFrame "Hhist". iSplitR; [| iExact "Harm"].
      iPureIntro. rewrite /fs_rec_wf /=. split_and!.
      - exact (fs_recovery_commit (fs_blocks dk) (fs_blocks dk') cov ls bs
                 Hhit Hmiss).
      - rewrite last_snoc. reflexivity.
      - rewrite /hdr_wf Hhit Hdec /=.
        split_and!; [exact Hnn | exact Hnd | exact Hin].
      - exact (fs_durable_wf_placeholder _).
        (* the COMPAT arm; [fs_commit_permit_named] below takes the real
           preservation premise, and stage G re-points ProofEndOp at it *) }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    iSplitL "Hmir".
    { rewrite /log_mirror_at /log_mirror_half.
      iExists (mirror_of (fs_blocks dk')). iFrame "Hmir". iPureIntro.
      rewrite /lm_hdr /mirror_of /= Hhit Hdec //. }
    iExists D'. rewrite /fs_receipt_any. iExists γs.
    iSplitR; [iPureIntro; done|].
    rewrite /fs_receipt. iExists (fr_hist r). iExact "Hlb".
  Qed.

  Lemma fs_commit_permit `{GEN : GenId} (cov : gset Z) (ls : Z)
      (h : nat * list Z) (nn : nat) (Ws : list Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_dec bs = (nn, Ws) ->
    (nn <= LOGBLOCKS)%nat ->
    NoDup Ws ->
    (forall b : Z, b ∈ Ws -> b ∈ cov /\ b ∉ log_region_set ls) ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_at ls h -∗
    disk_write_permit gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_at ls (nn, Ws) ∗ (∃ D : gmap Z (list (bv 8)), fs_receipt_any D)).
  Proof.
    intros P0 P1 P2 P3 P4. iIntros "#Hseam H0 H1 H2".
    iApply (fs_permit_of_rec with "Hseam").
    iApply (fs_commit_permit_rec with "H0 H1 H2"); try assumption.
  Qed.

  (* ---- (3) INSTALL: install_trans writing home block [b] = W[i]. ---- *)
  (* Recovery does not move, and the CONTENT written is irrelevant: the
     decoded header still names [b] at index [i], so recovery overwrites it
     from slot [i] either way.  That is the WAL's whole point, and it is why
     this permit needs no picture of the home side of the disk. *)
  Lemma fs_install_permit_rec `{GEN : GenId} (cov : gset Z) (ls : Z)
      (nn : nat) (Ws : list Z) (i : nat) (b : Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    NoDup Ws ->
    (length Ws <= LOGBLOCKS)%nat ->
    Ws !! i = Some b ->
    b ∉ log_region_set ls ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    (* THE ONE [▷] AMONG THE FOUR, and it is the install site's shape that
       forces it: install_trans threads its resource through the loop as the
       [▷ R] its own [bwrite]s hand back (SpecInstallTrans's generator), and
       there is no step between the return and the next entry's permit.  The
       later strips inside the [={∅}=∗] below because the mirror half is
       timeless -- which is exactly the argument that made the permit a fupd
       in the first place. *)
    ▷ log_mirror_at ls (nn, Ws) -∗
    fs_rec_permit cov ls gen_id (Some ((1024 * b)%Z, bs))
      (log_mirror_at ls (nn, Ws)).
  Proof.
    intros Hlen Hnd Hwlen Hi Hb. iIntros "#Hreg #Hswlb Hmir".
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    assert (Hidx : (1024 * b)%Z = (b * Z.of_nat BSIZE)%Z)
      by (rewrite /BSIZE; lia).
    cbn [wr_apply fst snd]. rewrite Hidx.
    set (dk' := disk_write dk (b * Z.of_nat BSIZE)%Z bs).
    assert (Hhit : fs_blocks dk' b = bs) by (apply fs_blocks_write_eq, Hlen).
    assert (Hmiss : forall c, c <> b -> fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc; apply fs_blocks_write_ne; [exact Hlen | exact Hc]).
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm)".
    rewrite /log_mirror_at /log_mirror_half.
    iMod "Hmir" as (M0) "[Hmir %HM0]".
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    (* THE FACT READ OUT OF THE MIRROR: the on-disk header IS the (n, W) the
       commit wrote, so the decoded write set is [Ws] *)
    assert (Hhdr : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (nn, Ws))
      by (rewrite -(Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)); exact HM0).
    (* the header survives a home write: [b] is not in the log region *)
    assert (Hhdr' : fs_blocks dk' (log_hdr_bno ls) = fs_blocks dk (log_hdr_bno ls))
      by (apply Hmiss, not_eq_sym; by apply home_ne_hdr).
    iMod ("Hclose" $! dk' (mirror_of (fs_blocks dk'))
            with "[%]") as "[Harm Hmir]"; [exact (mirror_of_ok _ _ _)|].
    iModIntro.
    iSplitL "Hhist Harm".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists r. iFrame "Hhist". iSplitR; [| iExact "Harm"].
      iPureIntro. destruct Hwf as (Hrec & Hlast & Hhwf & Hdwf). split_and!.
      - apply (fs_recovery_install (fs_blocks dk) (fs_blocks dk') (fr_D r) cov ls
               i b); rewrite ?Hhdr /=; assumption.
      - exact Hlast.
      - refine (hdr_wf_ext _ _ _ _ _ Hhwf).
        apply Hmiss, not_eq_sym. by apply home_ne_hdr.
      - exact Hdwf. (* the committed view is untouched *) }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    rewrite /log_mirror_at /log_mirror_half.
    iExists (mirror_of (fs_blocks dk')). iFrame "Hmir". iPureIntro.
    rewrite /lm_hdr /mirror_of /= Hhdr' Hhdr //.
  Qed.

  Lemma fs_install_permit `{GEN : GenId} (cov : gset Z) (ls : Z)
      (nn : nat) (Ws : list Z) (i : nat) (b : Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    NoDup Ws ->
    (length Ws <= LOGBLOCKS)%nat ->
    Ws !! i = Some b ->
    b ∉ log_region_set ls ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    (* THE ONE [▷] AMONG THE FOUR, and it is the install site's shape that
       forces it: install_trans threads its resource through the loop as the
       [▷ R] its own [bwrite]s hand back (SpecInstallTrans's generator), and
       there is no step between the return and the next entry's permit.  The
       later strips inside the [={∅}=∗] below because the mirror half is
       timeless -- which is exactly the argument that made the permit a fupd
       in the first place. *)
    ▷ log_mirror_at ls (nn, Ws) -∗
    disk_write_permit gen_id (Some ((1024 * b)%Z, bs))
      (log_mirror_at ls (nn, Ws)).
  Proof.
    intros P0 P1 P2 P3 P4. iIntros "#Hseam H0 H1 H2".
    iApply (fs_permit_of_rec with "Hseam").
    iApply (fs_install_permit_rec cov ls nn Ws i b bs with "H0 H1 H2");
      try assumption.
  Qed.

  (* the era's mirror half at an UNRECORDED picture: all a re-basing or
     clearing write needs, and all a swap at an unknown image can hand back *)
  Definition log_mirror_any : iProp Σ :=
    (∃ M : log_mirror, log_mirror_half M)%I.

  Global Instance log_mirror_any_timeless : Timeless log_mirror_any.
  Proof. rewrite /log_mirror_any /log_mirror_half. apply _. Qed.

  Lemma log_mirror_any_intro (ls : Z) (h : nat * list Z) :
    log_mirror_at ls h -∗ log_mirror_any.
  Proof.
    iIntros "H". rewrite /log_mirror_any /log_mirror_at.
    iDestruct "H" as (M) "[H _]". iExists M. iExact "H".
  Qed.

  (* ---- (4) CLEAR: write_head storing an n = 0 header at the end of a
     commit (and at the end of recovery). ---- *)
  (* THE CLEAR RE-BASES THE DURABLE STATE onto the current home content and
     EXTENDS the history by it, exactly as [fs_swap_permit] does -- it does
     not claim to PRESERVE [fr_D].  The preserving form
     ([fs_recovery_clear_keeps]) needs "every logged home block already holds
     its slot's content", i.e. a picture of the HOME side of the physical
     disk, and the era's custody records only the LOG REGION.  Supplying it
     would mean a home shadow in [log_mirror] (a partial [Z -> option (list
     (bv 8))] the install fupd extends); that is recorded as the residual of
     phase C2b/D1 stage 4 and is not built here.  Re-basing is sound in any
     case -- the record's [fr_D] is what the disk NOW recovers to -- and a
     receipt handed out before the clear stays valid, since the history only
     ever grows. *)
  Lemma fs_clear_permit_rec `{GEN : GenId} (cov : gset Z) (ls : Z)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_n bs = 0 ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_any -∗
    fs_rec_permit cov ls gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_at ls (0%nat, [])).
  Proof.
    intros Hlen Hn0. iIntros "#Hreg #Hswlb Hmir".
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    assert (Hidx : (1024 * log_hdr_bno ls)%Z
                   = (log_hdr_bno ls * Z.of_nat BSIZE)%Z)
      by (rewrite /BSIZE; lia).
    cbn [wr_apply fst snd]. rewrite Hidx.
    set (dk' := disk_write dk (log_hdr_bno ls * Z.of_nat BSIZE)%Z bs).
    assert (Hhit : fs_blocks dk' (log_hdr_bno ls) = bs)
      by (apply fs_blocks_write_eq, Hlen).
    assert (Hmiss : forall c, c <> log_hdr_bno ls ->
                      fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc; apply fs_blocks_write_ne; [exact Hlen | exact Hc]).
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm)".
    rewrite /log_mirror_any /log_mirror_half. iDestruct "Hmir" as (M0) "Hmir".
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    set (D' := fs_restrict (fs_blocks dk) (fs_home_set cov ls)).
    iMod (fs_hist_update (fcn_hist γs) (fr_hist r) (fr_hist r ++ [D'])
            with "Hhist") as "Hhist"; [by eexists|].
    iMod ("Hclose" $! dk' (mirror_of (fs_blocks dk'))
            with "[%]") as "[Harm Hmir]"; [exact (mirror_of_ok _ _ _)|].
    iModIntro.
    iSplitL "Hhist Harm".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists (MkFsRec D' (fr_hist r ++ [D'])).
      iFrame "Hhist". iSplitR; [| iExact "Harm"].
      iPureIntro. rewrite /fs_rec_wf /=. split_and!.
      - exact (fs_recovery_clear (fs_blocks dk) (fs_blocks dk') cov ls bs
                 Hhit Hn0 Hmiss).
      - rewrite last_snoc. reflexivity.
      - apply hdr_wf_zero. rewrite Hhit. exact Hn0.
      - exact (fs_durable_wf_placeholder _). (* RE-BASE; gated on H/F1 *) }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    rewrite /log_mirror_at /log_mirror_half.
    iExists (mirror_of (fs_blocks dk')). iFrame "Hmir". iPureIntro.
    rewrite /lm_hdr /mirror_of /= Hhit. exact (hdr_dec_zero bs Hn0).
  Qed.

  Lemma fs_clear_permit `{GEN : GenId} (cov : gset Z) (ls : Z)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_n bs = 0 ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_any -∗
    disk_write_permit gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_at ls (0%nat, [])).
  Proof.
    intros P0 P1. iIntros "#Hseam H0 H1 H2".
    iApply (fs_permit_of_rec with "Hseam").
    iApply (fs_clear_permit_rec with "H0 H1 H2"); try assumption.
  Qed.

  (* ==================================================================== *)
  (* (4') THE VALUE-CHAINED PRIMITIVES (durable-disk stage E2'/E3).         *)
  (*                                                                        *)
  (* The at-form permits above expose only the header READING; these expose  *)
  (* the mirror's VALUE: the caller passes its half at a NAMED [M0] and gets *)
  (* it back at [lm_upd M0 <written block> bs], so a committer can CHAIN its *)
  (* knowledge of the whole durable picture across a commit cycle.  That is  *)
  (* what lets                                                               *)
  (*   - the commit NAME its new committed view (and take the client's       *)
  (*     preservation premise -- ruling 2.5's fupd, pure while [P_wf] is);   *)
  (*   - the clear PRESERVE [fr_D] (stage E3): after the installs the        *)
  (*     chained value satisfies "home = slot" BY COMPUTATION, which is      *)
  (*     [fs_recovery_clear_keeps]'s missing premise.                        *)
  (* Stage G re-points ProofEndOp from the at-forms to these.                *)
  (* ==================================================================== *)

  Lemma fs_logfill_permit_v_rec `{GEN : GenId} (cov : gset Z) (ls : Z)
      (i : nat) (M0 : log_mirror) (bs : list (bv 8)) :
    length bs = BSIZE ->
    (i < LOGBLOCKS)%nat ->
    lm_hdr M0 ls = (0%nat, []) ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_half M0 -∗
    fs_rec_permit cov ls gen_id (Some ((1024 * log_slot_bno ls i)%Z, bs))
      (log_mirror_half (lm_upd M0 (log_slot_bno ls i) bs)).
  Proof.
    intros Hlen Hi HM0. iIntros "#Hreg #Hswlb Hmir".
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    assert (Hidx : (1024 * log_slot_bno ls i)%Z
                   = (log_slot_bno ls i * Z.of_nat BSIZE)%Z)
      by (rewrite /BSIZE; lia).
    cbn [wr_apply fst snd]. rewrite Hidx.
    set (dk' := disk_write dk (log_slot_bno ls i * Z.of_nat BSIZE)%Z bs).
    assert (Hmiss : forall c, c <> log_slot_bno ls i ->
                      fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc; apply fs_blocks_write_ne; [exact Hlen | exact Hc]).
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm)".
    rewrite /log_mirror_half.
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    assert (Hdk0 : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (0%nat, []))
      by (rewrite -(Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)); exact HM0).
    assert (Hn0 : hdr_n (fs_blocks dk (log_hdr_bno ls)) = 0)
      by (rewrite -hdr_dec_n Hdk0 //).
    iMod ("Hclose" $! dk' (lm_upd M0 (log_slot_bno ls i) bs)
            with "[%]") as "[Harm Hmir]";
      [exact (log_mirror_ok_upd M0 dk cov ls _ bs Hlen Hok)|].
    iModIntro.
    iSplitL "Hhist Harm".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists r. iFrame "Hhist". iSplitR; [| iExact "Harm"].
      iPureIntro. destruct Hwf as (Hrec & Hlast & Hhwf & Hdwf). split_and!.
      - exact (fs_recovery_logfill (fs_blocks dk) (fs_blocks dk') (fr_D r) cov ls i
               Hi Hmiss Hn0 Hrec).
      - exact Hlast.
      - refine (hdr_wf_ext _ _ _ _ _ Hhwf).
        apply Hmiss, not_eq_sym, log_slot_ne_hdr.
      - exact Hdwf. }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    rewrite /log_mirror_half. iExact "Hmir".
  Qed.

  Lemma fs_logfill_permit_v `{GEN : GenId} (cov : gset Z) (ls : Z)
      (i : nat) (M0 : log_mirror) (bs : list (bv 8)) :
    length bs = BSIZE ->
    (i < LOGBLOCKS)%nat ->
    lm_hdr M0 ls = (0%nat, []) ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_half M0 -∗
    disk_write_permit gen_id (Some ((1024 * log_slot_bno ls i)%Z, bs))
      (log_mirror_half (lm_upd M0 (log_slot_bno ls i) bs)).
  Proof.
    intros P0 P1 P2. iIntros "#Hseam H0 H1 H2".
    iApply (fs_permit_of_rec with "Hseam").
    iApply (fs_logfill_permit_v_rec with "H0 H1 H2"); assumption.
  Qed.

  Lemma fs_install_permit_v_rec `{GEN : GenId} (cov : gset Z) (ls : Z)
      (nn : nat) (Ws : list Z) (i : nat) (b : Z) (M0 : log_mirror)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    NoDup Ws ->
    (length Ws <= LOGBLOCKS)%nat ->
    Ws !! i = Some b ->
    b ∉ log_region_set ls ->
    lm_hdr M0 ls = (nn, Ws) ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    ▷ log_mirror_half M0 -∗
    fs_rec_permit cov ls gen_id (Some ((1024 * b)%Z, bs))
      (log_mirror_half (lm_upd M0 b bs)).
  Proof.
    intros Hlen Hnd Hwlen Hi Hb HM0. iIntros "#Hreg #Hswlb Hmir".
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    assert (Hidx : (1024 * b)%Z = (b * Z.of_nat BSIZE)%Z)
      by (rewrite /BSIZE; lia).
    cbn [wr_apply fst snd]. rewrite Hidx.
    set (dk' := disk_write dk (b * Z.of_nat BSIZE)%Z bs).
    assert (Hmiss : forall c, c <> b -> fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc; apply fs_blocks_write_ne; [exact Hlen | exact Hc]).
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm)".
    rewrite /log_mirror_half. iMod "Hmir".
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    assert (Hhdr : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (nn, Ws))
      by (rewrite -(Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)); exact HM0).
    iMod ("Hclose" $! dk' (lm_upd M0 b bs)
            with "[%]") as "[Harm Hmir]";
      [exact (log_mirror_ok_upd M0 dk cov ls _ bs Hlen Hok)|].
    iModIntro.
    iSplitL "Hhist Harm".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists r. iFrame "Hhist". iSplitR; [| iExact "Harm"].
      iPureIntro. destruct Hwf as (Hrec & Hlast & Hhwf & Hdwf). split_and!.
      - apply (fs_recovery_install (fs_blocks dk) (fs_blocks dk') (fr_D r) cov ls
               i b); rewrite ?Hhdr /=; assumption.
      - exact Hlast.
      - refine (hdr_wf_ext _ _ _ _ _ Hhwf).
        apply Hmiss, not_eq_sym. by apply home_ne_hdr.
      - exact Hdwf. }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    rewrite /log_mirror_half. iExact "Hmir".
  Qed.

  Lemma fs_install_permit_v `{GEN : GenId} (cov : gset Z) (ls : Z)
      (nn : nat) (Ws : list Z) (i : nat) (b : Z) (M0 : log_mirror)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    NoDup Ws ->
    (length Ws <= LOGBLOCKS)%nat ->
    Ws !! i = Some b ->
    b ∉ log_region_set ls ->
    lm_hdr M0 ls = (nn, Ws) ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    ▷ log_mirror_half M0 -∗
    disk_write_permit gen_id (Some ((1024 * b)%Z, bs))
      (log_mirror_half (lm_upd M0 b bs)).
  Proof.
    intros P0 P1 P2 P3 P4 P5. iIntros "#Hseam H0 H1 H2".
    iApply (fs_permit_of_rec with "Hseam").
    iApply (fs_install_permit_v_rec cov ls nn Ws i b M0 bs with "H0 H1 H2");
      assumption.
  Qed.

  (* ---- (4'b) THE NAMING COMMIT: the new committed view, as a TERM in the
     committer's own picture.  [fs_commit_permit]'s existential receipt
     becomes a receipt AT the named state, and the client's preservation
     premise (ruling 2.5) enters here -- pure while [P_wf] is, upgraded to
     the fupd when the contents layer adds durable ghosts.  The pre-image's
     log must be CLEAN per the committer's picture: that is what identifies
     the invariant's [fr_D] with [fs_restrict (lm_view M0) homes], the
     state the premise is stated at. ---- *)
  Lemma fs_commit_permit_named_rec `{GEN : GenId} (cov : gset Z) (ls : Z)
      (M0 : log_mirror) (nn : nat) (Ws : list Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_dec bs = (nn, Ws) ->
    (nn <= LOGBLOCKS)%nat ->
    NoDup Ws ->
    (forall b : Z, b ∈ Ws -> b ∈ cov /\ b ∉ log_region_set ls) ->
    lm_hdr M0 ls = (0%nat, []) ->
    (* THE CLIENT'S PRESERVATION PREMISE (stage G supplies it for real;
       the F1 placeholder makes it trivial today) *)
    (fs_durable_wf (fs_restrict (lm_view M0) (fs_home_set cov ls)) ->
     fs_durable_wf (fs_install (lm_view M0) ls Ws
                      (fs_restrict (lm_view M0) (fs_home_set cov ls)))) ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_half M0 -∗
    fs_rec_permit cov ls gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_half (lm_upd M0 (log_hdr_bno ls) bs) ∗
       fs_receipt_any (fs_install (lm_view M0) ls Ws
                         (fs_restrict (lm_view M0) (fs_home_set cov ls)))).
  Proof.
    intros Hlen Hdec Hnn Hnd Hin HM0 Hcli. iIntros "#Hreg #Hswlb Hmir".
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    assert (Hidx : (1024 * log_hdr_bno ls)%Z
                   = (log_hdr_bno ls * Z.of_nat BSIZE)%Z)
      by (rewrite /BSIZE; lia).
    cbn [wr_apply fst snd]. rewrite Hidx.
    set (dk' := disk_write dk (log_hdr_bno ls * Z.of_nat BSIZE)%Z bs).
    assert (Hhit : fs_blocks dk' (log_hdr_bno ls) = bs)
      by (apply fs_blocks_write_eq, Hlen).
    assert (Hmiss : forall c, c <> log_hdr_bno ls ->
                      fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc; apply fs_blocks_write_ne; [exact Hlen | exact Hc]).
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm)".
    rewrite /log_mirror_half.
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    (* the two views agree on the durable extent, so both the restriction
       and the install are the SAME MAP in either spelling *)
    assert (Hres : fs_restrict (fs_blocks dk) (fs_home_set cov ls)
                   = fs_restrict (lm_view M0) (fs_home_set cov ls)).
    { apply fs_restrict_ext. intros b Hb.
      symmetry. exact (Hok b (fs_home_in_ext cov ls b Hb)). }
    set (D' := fs_install (lm_view M0) ls Ws
                 (fs_restrict (lm_view M0) (fs_home_set cov ls))).
    assert (HD' : fs_install (fs_blocks dk) ls (hdr_dec bs).2
                    (fs_restrict (fs_blocks dk) (fs_home_set cov ls)) = D').
    { rewrite Hdec /= Hres. apply fs_install_ext_P.
      intros j Hj. symmetry.
      apply (Hok (log_slot_bno ls j)), log_slot_in_ext.
      pose proof (hdr_dec_length bs) as Hl. rewrite Hdec /= in Hl. lia. }
    (* the invariant's committed view IS the premise's: the pre-image's log
       is clean per the picture, so recovery is the home restriction *)
    destruct Hwf as (Hrec & Hlast & Hhwf & Hdwf).
    assert (Hdk0 : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (0%nat, []))
      by (rewrite -(Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)); exact HM0).
    assert (Hn0 : hdr_n (fs_blocks dk (log_hdr_bno ls)) = 0)
      by (rewrite -hdr_dec_n Hdk0 //).
    assert (HfrD : fr_D r = fs_restrict (lm_view M0) (fs_home_set cov ls))
      by (rewrite -Hres; exact (proj1 (fs_recovery_clean _ _ _ _ Hn0) Hrec)).
    (* the new record, its history extension, and the NAMED receipt *)
    iMod (fs_hist_update (fcn_hist γs) (fr_hist r) (fr_hist r ++ [D'])
            with "Hhist") as "Hhist"; [by eexists|].
    iDestruct (fs_hist_snapshot with "Hhist") as "[Hhist #Hlb]".
    iMod ("Hclose" $! dk' (lm_upd M0 (log_hdr_bno ls) bs)
            with "[%]") as "[Harm Hmir]";
      [exact (log_mirror_ok_upd M0 dk cov ls _ bs Hlen Hok)|].
    iModIntro.
    iSplitL "Hhist Harm".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists (MkFsRec D' (fr_hist r ++ [D'])).
      iFrame "Hhist". iSplitR; [| iExact "Harm"].
      iPureIntro. rewrite /fs_rec_wf /=. split_and!.
      - rewrite -HD'.
        exact (fs_recovery_commit (fs_blocks dk) (fs_blocks dk') cov ls bs
                 Hhit Hmiss).
      - rewrite last_snoc. reflexivity.
      - rewrite /hdr_wf Hhit Hdec /=.
        split_and!; [exact Hnn | exact Hnd | exact Hin].
      - apply Hcli. rewrite -HfrD. exact Hdwf. }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    iSplitL "Hmir"; [rewrite /log_mirror_half; iExact "Hmir"|].
    rewrite /fs_receipt_any. iExists γs.
    iSplitR; [iPureIntro; done|].
    rewrite /fs_receipt. iExists (fr_hist r). iExact "Hlb".
  Qed.

  Lemma fs_commit_permit_named `{GEN : GenId} (cov : gset Z) (ls : Z)
      (M0 : log_mirror) (nn : nat) (Ws : list Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_dec bs = (nn, Ws) ->
    (nn <= LOGBLOCKS)%nat ->
    NoDup Ws ->
    (forall b : Z, b ∈ Ws -> b ∈ cov /\ b ∉ log_region_set ls) ->
    lm_hdr M0 ls = (0%nat, []) ->
    (fs_durable_wf (fs_restrict (lm_view M0) (fs_home_set cov ls)) ->
     fs_durable_wf (fs_install (lm_view M0) ls Ws
                      (fs_restrict (lm_view M0) (fs_home_set cov ls)))) ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_half M0 -∗
    disk_write_permit gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_half (lm_upd M0 (log_hdr_bno ls) bs) ∗
       fs_receipt_any (fs_install (lm_view M0) ls Ws
                         (fs_restrict (lm_view M0) (fs_home_set cov ls)))).
  Proof.
    intros P0 P1 P2 P3 P4 P5 P6. iIntros "#Hseam H0 H1 H2".
    iApply (fs_permit_of_rec with "Hseam").
    iApply (fs_commit_permit_named_rec cov ls M0 nn Ws bs with "H0 H1 H2");
      assumption.
  Qed.

  (* ---- (4'c) THE PRESERVING CLEAR (stage E3): [fr_D] does NOT move.  The
     caught-up premise is a pure fact about the committer's own picture --
     after the installs the chained value has "home = slot" at every entry
     BY COMPUTATION -- and it is exactly [fs_recovery_clear_keeps]'s missing
     home-side picture.  No history extension: the committed state is the
     same one. ---- *)
  Lemma fs_clear_permit_keep_rec `{GEN : GenId} (cov : gset Z) (ls : Z)
      (M0 : log_mirror) (nn : nat) (Ws : list Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_n bs = 0 ->
    lm_hdr M0 ls = (nn, Ws) ->
    (forall (j : nat) (b : Z), Ws !! j = Some b ->
       lm_view M0 b = lm_view M0 (log_slot_bno ls j)) ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_half M0 -∗
    fs_rec_permit cov ls gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_half (lm_upd M0 (log_hdr_bno ls) bs)).
  Proof.
    intros Hlen Hn0 HM0 Hcaught. iIntros "#Hreg #Hswlb Hmir".
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    assert (Hidx : (1024 * log_hdr_bno ls)%Z
                   = (log_hdr_bno ls * Z.of_nat BSIZE)%Z)
      by (rewrite /BSIZE; lia).
    cbn [wr_apply fst snd]. rewrite Hidx.
    set (dk' := disk_write dk (log_hdr_bno ls * Z.of_nat BSIZE)%Z bs).
    assert (Hhit : fs_blocks dk' (log_hdr_bno ls) = bs)
      by (apply fs_blocks_write_eq, Hlen).
    assert (Hmiss : forall c, c <> log_hdr_bno ls ->
                      fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc; apply fs_blocks_write_ne; [exact Hlen | exact Hc]).
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm)".
    rewrite /log_mirror_half.
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    destruct Hwf as (Hrec & Hlast & Hhwf & Hdwf).
    pose proof Hhwf as (Hbound & Hnd & Hhome).
    assert (Hdkh : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (nn, Ws))
      by (rewrite -(Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)); exact HM0).
    iMod ("Hclose" $! dk' (lm_upd M0 (log_hdr_bno ls) bs)
            with "[%]") as "[Harm Hmir]";
      [exact (log_mirror_ok_upd M0 dk cov ls _ bs Hlen Hok)|].
    iModIntro.
    iSplitL "Hhist Harm".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists r. iFrame "Hhist". iSplitR; [| iExact "Harm"].
      iPureIntro. rewrite /fs_rec_wf /=. split_and!.
      - refine (fs_recovery_clear_keeps (fs_blocks dk) (fs_blocks dk')
                  (fr_D r) cov ls bs Hhit Hn0 Hmiss Hnd _ Hrec).
        intros j b Hjb. rewrite Hdkh /= in Hjb.
        assert (Hbc : b ∈ cov /\ b ∉ log_region_set ls).
        { apply Hhome. rewrite Hdkh /=.
          exact (elem_of_list_lookup_2 _ _ _ Hjb). }
        assert (Hbhome : b ∈ fs_home_set cov ls)
          by (rewrite /fs_home_set elem_of_difference; tauto).
        apply fs_restrict_lookup_Some. split; [exact Hbhome|].
        assert (Hjlt : (j < LOGBLOCKS)%nat).
        { apply lookup_lt_Some in Hjb.
          pose proof (hdr_dec_length (fs_blocks dk (log_hdr_bno ls))) as Hl.
          rewrite Hdkh /= in Hl Hbound. lia. }
        rewrite -(Hok b (fs_home_in_ext cov ls b Hbhome)).
        rewrite -(Hok (log_slot_bno ls j) (log_slot_in_ext cov ls j Hjlt)).
        symmetry. exact (Hcaught j b Hjb).
      - exact Hlast.
      - apply hdr_wf_zero. rewrite Hhit. exact Hn0.
      - exact Hdwf. (* THE POINT: the committed view does not move *) }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    rewrite /log_mirror_half. iExact "Hmir".
  Qed.

  Lemma fs_clear_permit_keep `{GEN : GenId} (cov : gset Z) (ls : Z)
      (M0 : log_mirror) (nn : nat) (Ws : list Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_n bs = 0 ->
    lm_hdr M0 ls = (nn, Ws) ->
    (forall (j : nat) (b : Z), Ws !! j = Some b ->
       lm_view M0 b = lm_view M0 (log_slot_bno ls j)) ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_half M0 -∗
    disk_write_permit gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_half (lm_upd M0 (log_hdr_bno ls) bs)).
  Proof.
    intros P0 P1 P2 P3. iIntros "#Hseam H0 H1 H2".
    iApply (fs_permit_of_rec with "Hseam").
    iApply (fs_clear_permit_keep_rec cov ls M0 nn Ws bs with "H0 H1 H2");
      assumption.
  Qed.

  (* ==================================================================== *)
  (* (5) THE RECOVERY-SIDE PERMIT FAMILY (phase D2).                       *)
  (*                                                                       *)
  (* RECOVERY'S WRITES CANNOT CLAIM TO PRESERVE [fr_D], AND THAT IS FORCED  *)
  (* BY THE SEAM, not by laziness.  install_trans's home writes at boot run  *)
  (* BEFORE the header write that the boot swap rides, so at each of them    *)
  (* the era either has no custody yet or has custody taken at an image it   *)
  (* knows nothing about: a swap installs the mirror at [mirror_of           *)
  (* (fs_blocks dk) ls] for the fupd's UNIVERSALLY QUANTIFIED [dk], so the   *)
  (* header picture it records is opaque to the client, and [Q] -- fixed at  *)
  (* permit-creation time -- cannot name it.  The only way for the era to    *)
  (* learn the ON-DISK header is to have WRITTEN it (that is what            *)
  (* [fs_commit_permit] does for the steady state); recovery has only READ   *)
  (* it, and a read's permit carries no data (its [disk_wr] is [None]).      *)
  (* Closing that gap means making a READ's [Q] a FUNCTION of the delivered  *)
  (* bytes -- a machine-layer interface change (saved predicates in          *)
  (* [PermInv], a read-data equation at the completion in [WpUart]); see     *)
  (* claude-notes/projects/fs-log.md, phase D2's finding.                    *)
  (*                                                                        *)
  (* So the honest recovery-side permit RE-BASES: it takes custody (or keeps *)
  (* it), sets [fr_D] to whatever the POST-write image recovers to -- always  *)
  (* possible, since [fs_recovery] is a TOTAL FUNCTION of the image           *)
  (* ([fs_recovery_total]) -- and EXTENDS the history by it.  Sound, and it   *)
  (* costs nothing that is cashed later: every receipt handed out before      *)
  (* stays valid (the history only grows), and the state recovery actually    *)
  (* leaves behind is pinned by the FINAL header write anyway                 *)
  (* ([fs_boot_head_permit] below), which is the same clear the steady state  *)
  (* uses.  What is NOT provable this way is the WAL's completeness claim     *)
  (* ("the state after recovery IS the last committed one"); that needs the   *)
  (* read-data interface above.                                              *)
  (*                                                                        *)
  (* ONE PERMIT COVERS EVERY RECOVERY WRITE, and it has to: install_trans     *)
  (* takes its permits as a UNIFORM GENERATOR over the entries               *)
  (* ([SpecInstallTrans]'s [□ ∀ i w bs', …]), so the first entry -- the one   *)
  (* that performs the swap -- cannot have a different contract from the      *)
  (* rest.  [fs_era_custody] is the disjunction that makes it uniform: the    *)
  (* era holds either the whole mirror variable (no custody taken yet) or its *)
  (* half plus the swap receipt (custody taken).  [fs_recover_permit]         *)
  (* consumes and re-establishes it, swapping on first use.                   *)
  (* ==================================================================== *)

  (* THE UNIFORM RECOVERY-SIDE RESOURCE: before the swap the era owns the
     whole mirror variable (the boot mint), after it the half plus the swap
     receipt.  Timeless, so a permit strips it inside its own [={∅}=∗]. *)
  Definition fs_era_custody `{GEN : GenId} : iProp Σ :=
    (log_mirror_full ∨ (log_mirror_any ∗ swap_lb (S gen_id)))%I.

  Global Instance fs_era_custody_timeless `{GEN : GenId} :
    Timeless fs_era_custody.
  Proof.
    rewrite /fs_era_custody /log_mirror_full /log_mirror_any /log_mirror_half.
    apply _.
  Qed.

  Lemma fs_era_custody_boot `{GEN : GenId} :
    log_mirror_full -∗ fs_era_custody.
  Proof. iIntros "H". rewrite /fs_era_custody. by iLeft. Qed.

  (* ---- (5a) THE RE-BASING WRITE, at any write identity that DOES NOT
     CORRUPT THE HEADER's invariant.  The premise is the one fact stage B's
     [hdr_wf] forces on this family: a re-based record is well formed only
     if the post-write header still is, and a recovery write cannot claim
     that for free -- its block came out of the header it read, and the
     invariant it learned there ([hdr_wf]'s home-blocks conjunct, delivered
     by the read permit) is exactly what discharges [hdr_wf_wr_out]. ---- *)
  Lemma fs_recover_permit_rec `{GEN : GenId} (cov : gset Z) (ls : Z) (w : disk_wr) :
    (forall dk : Z -> bv 8,
       hdr_wf (fs_blocks dk) cov ls ->
       hdr_wf (fs_blocks (wr_apply w dk)) cov ls) ->
    era_registered gen_id riscv_eraGS -∗
    gen_started gen_id -∗
    ▷ fs_era_custody -∗
    fs_rec_permit cov ls gen_id w fs_era_custody.
  Proof.
    intros Hsafe. iIntros "#Hreg #Hst Hcust".
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    set (dk' := wr_apply w dk).
    (* through the seam; the record is timeless, so the [▷] strips *)
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm)".
    pose proof Hwf as (_ & _ & Hhwf & _).
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    (* THE NEW DURABLE STATE: whatever the POST-write image recovers to *)
    set (D' := fs_install (fs_blocks dk') ls
                 (hdr_dec (fs_blocks dk' (log_hdr_bno ls))).2
                 (fs_restrict (fs_blocks dk') (fs_home_set cov ls))).
    iMod (fs_hist_update (fcn_hist γs) (fr_hist r) (fr_hist r ++ [D'])
            with "Hhist") as "Hhist"; [by eexists|].
    (* the arm: SWAP on first use, ACCESS afterwards -- either way it comes
       back at the post-write image, with this era's custody installed *)
    iMod "Hcust".
    iAssert (|==> fs_arm γs cov ls dk' ∗ mono_nat_auth_own (fcn_start γs) 1 n ∗
                  log_mirror_any ∗ swap_lb (S gen_id))%I
      with "[Hcust Hsa Harm]" as ">(Harm & Hsa & Hmir & #Hswlb)".
    { rewrite /fs_era_custody. iDestruct "Hcust" as "[Hfull | [Hany #Hswlb]]".
      - (* THE SWAP: retirement needs no identification, so it always goes *)
        rewrite /log_mirror_full. iDestruct "Hfull" as (M0) "Hmir".
        iMod (ghost_var_update (mirror_of (fs_blocks dk')) with "Hmir")
          as "Hmir".
        iEval (rewrite -Qp.half_half) in "Hmir".
        iDestruct (ghost_var_split with "Hmir") as "[Hm1 Hm2]".
        iAssert (fs_started γs gen_id) as "#Hst2".
        { rewrite /fs_started Hstn. iExact "Hst". }
        iMod (fs_arm_swap γs cov ls dk dk' gen_id riscv_eraGS n
                (mirror_of (fs_blocks dk')) Hn1 (mirror_of_ok _ _ _)
                with "Hreg2 Hst2 Hsa Hm2 Harm") as "(Harm & Hsa & #Hswlb)".
        iModIntro. iFrame "Harm Hsa".
        iSplitL "Hm1".
        { rewrite /log_mirror_any /log_mirror_half.
          iExists (mirror_of (fs_blocks dk')). iExact "Hm1". }
        rewrite /swap_lb -Hsw. iExact "Hswlb".
      - (* THE ACCESS: the squeeze, then re-close at the post-write image *)
        rewrite /log_mirror_any /log_mirror_half.
        iDestruct "Hany" as (M0) "Hmir".
        iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
        { rewrite Hsw. iExact "Hswlb". }
        iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                     with "Hreg2 Hswlb2 Hsa Hmir Harm")
          as "(_ & Hsa & Hclose)".
        iMod ("Hclose" $! dk' (mirror_of (fs_blocks dk'))
                with "[%]") as "[Harm Hmir]"; [exact (mirror_of_ok _ _ _)|].
        iModIntro. iFrame "Harm Hsa Hswlb".
        iExists (mirror_of (fs_blocks dk')). iExact "Hmir". }
    iModIntro.
    iSplitL "Hhist Harm".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists (MkFsRec D' (fr_hist r ++ [D'])).
      iFrame "Hhist". iSplitR; [| iExact "Harm"].
      iPureIntro. rewrite /fs_rec_wf /=. split_and!.
      - rewrite /fs_recovery. reflexivity.
      - rewrite last_snoc. reflexivity.
      - exact (Hsafe dk Hhwf).
      - exact (fs_durable_wf_placeholder _). (* RE-BASE; gated on H/F1 *) }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    rewrite /fs_era_custody. iRight. iFrame "Hmir Hswlb".
  Qed.

  Lemma fs_recover_permit `{GEN : GenId} (cov : gset Z) (ls : Z) (w : disk_wr) :
    (forall dk : Z -> bv 8,
       hdr_wf (fs_blocks dk) cov ls ->
       hdr_wf (fs_blocks (wr_apply w dk)) cov ls) ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    gen_started gen_id -∗
    ▷ fs_era_custody -∗
    disk_write_permit gen_id w fs_era_custody.
  Proof.
    intros Hsafe. iIntros "#Hseam H0 H1 H2".
    iApply (fs_permit_of_rec with "Hseam").
    iApply (fs_recover_permit_rec cov ls w Hsafe with "H0 H1 H2").
  Qed.

  (* ---- (5b) THE BOOT'S FINAL HEADER WRITE, uniform in whether the era
     already took custody. ---- *)
  (* [initlog]'s closing [write_head] writes an n = 0 header whether or not
     recovery installed anything, so its permit must accept both arms of
     [fs_era_custody]: at [n = 0] no install ran and the era still holds the
     whole mirror variable (this IS [fs_swap_permit]); at [n > 0] the first
     install already swapped and the era holds the half (this is
     [fs_clear_permit], with the swap receipt merely carried through).  Both
     land the same [Q], which is what makes [initlog]'s postcondition -- and
     therefore [log_ctx] -- independent of [n]. *)
  Lemma fs_boot_head_permit `{GEN : GenId} (cov : gset Z) (ls : Z)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_n bs = 0 ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    gen_started gen_id -∗
    fs_era_custody -∗
    disk_write_permit gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_at ls (0%nat, []) ∗ swap_lb (S gen_id)).
  Proof.
    intros Hlen Hn0. iIntros "#Hseam #Hreg #Hst Hcust".
    rewrite /fs_era_custody. iDestruct "Hcust" as "[Hfull | [Hany #Hswlb]]".
    { iApply (fs_swap_permit cov ls bs Hlen Hn0 with "Hseam Hreg Hst Hfull"). }
    iPoseProof (fs_clear_permit cov ls bs Hlen Hn0
                  with "Hseam Hreg Hswlb Hany") as "Hp".
    rewrite /disk_write_permit. iIntros (dk n) "Hsa %Hn1 Ha HP".
    iMod ("Hp" $! dk n with "Hsa [%] Ha HP") as "(Ha & HP & Hsa & Hmir)";
      [exact Hn1|].
    iModIntro. iFrame "Ha HP Hsa Hmir Hswlb".
  Qed.

End fs_crash_seam.
