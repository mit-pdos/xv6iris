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
From Stdlib Require Import ZArith Lia List FunctionalExtensionality.
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
Require Export FsWf.  (* [dv_of_D]: the committed view as a total reading *)
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
Require Import FsDurSnap.   (* [P_dur] -- the DURABLE SNAPSHOT, which is
                               [P_fs]'s durable conjunct since lane CE
                               (durable-fs-plan.md sections 1 and 3).  IMPORTED,
                               not merely required: [diskImgG]/[fsLinkG]/
                               [fsTopG] are capacity classes used as Context
                               binders below and are inert otherwise
                               (durable-notes.md).                            *)
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

(* -- SUB-BLOCK (SECTOR) WRITES (claude-notes/completed/sector-atomic-disk.md).
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
(*    (claude-notes/completed/sector-atomic-disk.md §0).                     *)
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
(* recorded facts, [LogInv.log_state]'s three pure rows; logfill and       *)
(* install leave the header alone), and the recovery-side permit takes     *)
(* the write's share of it as a premise ([hdr_wf_wr_out] is the form a     *)
(* recovery home write discharges it in).                                  *)
(* ---------------------------------------------------------------------- *)

(* AND BLOCK 1 IS IN THE ROW (durable-disk lane E-blk1, plan section 5's
   "one small fact the mint needs").  [LogInv.log_state] keeps "the write set
   never names block 1" true in the era -- off [SbPark]'s park, not off any
   premise -- and the header is what has to carry it ACROSS a power cycle,
   since the boot mint reads a header nobody in this era wrote.  It rides the
   third clause's own conjunction, LAST, so [hdr_wf]'s top-level arity does
   not move and no [destruct Hwf as (_ & _ & _)] anywhere changes.  What
   consumes it is [fs_recovery_sb_raw] below. *)
Definition hdr_wf (P : Z -> list (bv 8)) (cov : gset Z) (logstart : Z)
    : Prop :=
  ((hdr_dec (P (log_hdr_bno logstart))).1 <= LOGBLOCKS)%nat
  /\ NoDup (hdr_dec (P (log_hdr_bno logstart))).2
  /\ (forall b : Z, b ∈ (hdr_dec (P (log_hdr_bno logstart))).2 ->
        b ∈ cov /\ b ∉ log_region_set logstart /\ b <> FsImg.SB_BNO).

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

(* ...so a whole-block write ANYWHERE ELSE preserves it: the block it writes
   came out of the header it read, and the invariant it learned there says
   that block is not the header. *)
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

(* ...and the SECTOR form of the same fact (sector-atomic-disk.md §6e): a
   landing anywhere inside a block that is not the header leaves the header
   invariant alone, which is what each half of a recovery home write owes. *)
Lemma hdr_wf_sub_out (cov : gset Z) (logstart b : Z) (o : nat)
    (sbs : list (bv 8)) (dk : Z -> bv 8) :
  (o + length sbs <= BSIZE)%nat ->
  b <> log_hdr_bno logstart ->
  hdr_wf (fs_blocks dk) cov logstart ->
  hdr_wf (fs_blocks (disk_write dk (b * Z.of_nat BSIZE + Z.of_nat o)%Z sbs))
    cov logstart.
Proof.
  intros Hfit Hb. apply hdr_wf_ext.
  exact (fs_blocks_sub_ne dk b (log_hdr_bno logstart) o sbs Hfit
           (not_eq_sym Hb)).
Qed.

(* ---------------------------------------------------------------------- *)
(* 1c. The recovery relation.                                              *)
(*                                                                         *)
(* Stated in LogDefs' own geometry vocabulary ([log_hdr_bno],              *)
(* [log_slot_bno], [log_region_set]), so the log proofs and this file       *)
(* cannot drift apart on where the log lives.                              *)
(* ---------------------------------------------------------------------- *)

(* the HOME blocks ([LogDefs.fs_home_set], re-exported: the covered range
   minus the log's own storage) *)

(* [fs_restrict] MOVED DOWN to LogDefs (durable-disk 1d): the LOG has to
   name the committed view it parks the client's payload at, and it may not
   import this file.  Re-exported through [Require Export LogDefs] above. *)

(* the pointwise theory of [fs_restrict] moved DOWN to LogDefs with it *)

(* INSTALLING the on-disk log over the home map: entry [i] of the write set
   takes its content from log slot [i].  A [foldr] over the INDEX list
   rather than over [W] itself, because the content's block number
   ([log_slot_bno logstart i]) is a function of the index.  The step is a
   NAMED function (not an inline lambda) so that every lemma below unifies
   against the same head rather than against a fresh beta-redex. *)
(* [fs_install_step] and [fs_install] MOVED DOWN to LogDefs, with
   [fs_restrict], for the same reason.  Their theory stays here. *)

Lemma fs_install_step_Some (P : Z -> list (bv 8)) (logstart : Z) (W : list Z)
    (i : nat) (b : Z) (m : gmap Z (list (bv 8))) :
  W !! i = Some b ->
  fs_install_step P logstart W i m = <[ b := P (log_slot_bno logstart i) ]> m.
Proof. rewrite /fs_install_step. by intros ->. Qed.

Lemma fs_install_step_None (P : Z -> list (bv 8)) (logstart : Z) (W : list Z)
    (i : nat) (m : gmap Z (list (bv 8))) :
  W !! i = None -> fs_install_step P logstart W i m = m.
Proof. rewrite /fs_install_step. by intros ->. Qed.



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

(* ...and the reading of it a HOME-SET membership gives, which is what the
   value-chained header permits use to say that their caller's off-header
   view covers every home block (durable-disk flip-B). *)
Lemma home_set_ne_hdr (cov : gset Z) (ls b : Z) :
  b ∈ fs_home_set cov ls -> b <> log_hdr_bno ls.
Proof.
  rewrite /fs_home_set elem_of_difference. intros [_ Hb]. by apply home_ne_hdr.
Qed.

(* ...and the same reading with the region left standing, which is what
   row (b)'s MAINTENANCE wants: every write the commit cycle makes lands in
   the log region (a slot, or the header), so it is off the row's domain. *)
Lemma home_set_not_region (cov : gset Z) (ls b : Z) :
  b ∈ fs_home_set cov ls -> b ∉ log_region_set ls.
Proof. rewrite /fs_home_set elem_of_difference. tauto. Qed.

(* --- [fs_restrict], pointwise --- *)


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

(* ---------------------------------------------------------------------- *)
(* 1c''. WHAT RECOVERY LEAVES ALONE (durable-disk lanes E-clauses/E-blk1,   *)
(*       section 5's "one small fact the mint needs").                       *)
(*                                                                          *)
(* [fsinit] calls [readsb] BEFORE [initlog], so the superblock record the    *)
(* whole file-system configuration is built from ([IcacheRef.icfg_nib],      *)
(* [icfg_ist], the region geometry) is decoded from the RAW disk, while the  *)
(* snapshot the boot mint reads describes the RECOVERED view [D].  The two   *)
(* agree at a home block exactly when the on-disk log's write set does not   *)
(* name it, and that is all recovery does: [fs_install] touches the blocks   *)
(* the header names and nothing else ([fs_install_miss]).                     *)
(*                                                                          *)
(* THE PREMISE IS CLOSED (durable-disk lane E-blk1).  "The write set never   *)
(* names block 1" is now a MAINTAINED row and not a hypothesis: it rides     *)
(* [LogInv.log_state] through the era -- re-established at every append by   *)
(* [SbPark.sb_parked_bno_ne], since the park holds block 1's run at fraction *)
(* 1 inside [log_ctx] and [log_write]'s byte-range update holds the caller's *)
(* window at fraction 1 -- and it rides [hdr_wf] across the power cycle,     *)
(* [fs_commit_L_sector0_rec] (the only permit that writes a NONZERO header)  *)
(* taking it as one premise that [ProofEndOp] discharges off that same row.  *)
(* NO caller of [wp_log_write_*] pays anything for it.                       *)
(*                                                                          *)
(* This lemma keeps its GENERAL statement -- a home block the header does    *)
(* not name reads through -- and [fs_recovery_sb_raw] just below is the      *)
(* block 1 instance the mint uses.                                           *)
(* ---------------------------------------------------------------------- *)

Lemma fs_recovery_untouched (P : Z -> list (bv 8)) D (cov : gset Z)
    (logstart b : Z) :
  fs_recovery P D cov logstart ->
  b ∈ fs_home_set cov logstart ->
  b ∉ (hdr_dec (P (log_hdr_bno logstart))).2 ->
  D !! b = Some (P b).
Proof.
  intros -> Hhome Hout.
  rewrite /fs_recovery (fs_install_miss P logstart _ _ b Hout).
  apply fs_restrict_lookup_Some. split; [exact Hhome | reflexivity].
Qed.

(* ...AND AT BLOCK 1, WITH NOTHING LEFT TO ASSUME (durable-disk lane
   E-blk1).  The hypothesis above is now a clause of [hdr_wf], so recovery
   provably leaves the superblock alone: what [fsinit]'s [readsb] pulls off
   the RAW disk before [initlog] runs is the very block the committed view
   [D] holds.  The home-membership premise is the image's own geometry
   ([FsCollectImg.img_sb_home] discharges it: block 1 is covered metadata and
   sits below the log). *)
Lemma fs_recovery_sb_raw (P : Z -> list (bv 8)) (D : gmap Z (list (bv 8)))
    (cov : gset Z) (logstart : Z) :
  fs_recovery P D cov logstart ->
  hdr_wf P cov logstart ->
  FsImg.SB_BNO ∈ fs_home_set cov logstart ->
  D !! FsImg.SB_BNO = Some (P FsImg.SB_BNO).
Proof.
  intros Hrec Hwf Hhome.
  apply (fs_recovery_untouched P D cov logstart FsImg.SB_BNO Hrec Hhome).
  intros Hmem. exact (proj2 (proj2 (proj2 (proj2 Hwf) _ Hmem)) eq_refl).
Qed.

(* THE MINT'S READING OF IT (plan section 5).  The era's file-system instance
   is cloned from the snapshot, which describes [D]; the file-system
   CONFIGURATION ([IcacheRef.icfg_nib], the region geometry) is decoded from
   the record [readsb] parsed off the raw disk.  Those are one record: the
   snapshot's two superblock clauses ([FsDurSnap.sk_sb], [sk_parse]) read at
   [D]'s block 1, which the lemma above identifies with the raw one. *)
Lemma fs_recovery_sb_parse (P : Z -> list (bv 8)) (D : gmap Z (list (bv 8)))
    (cov : gset Z) (logstart : Z) (S : fs_state_rec) :
  fs_recovery P D cov logstart ->
  hdr_wf P cov logstart ->
  FsImg.SB_BNO ∈ fs_home_set cov logstart ->
  snap_bytes S D ->
  P FsImg.SB_BNO = fss_sbb S /\
  FsImg.fs_parse_sb (fun _ => P FsImg.SB_BNO) = Some (fss_sb S).
Proof.
  intros Hrec Hwf Hhome Hb.
  assert (Heq : Some (P FsImg.SB_BNO) = Some (fss_sbb S)).
  { rewrite -(sk_sb Hb). symmetry.
    exact (fs_recovery_sb_raw P D cov logstart Hrec Hwf Hhome). }
  apply (inj Some) in Heq.
  split; [exact Heq |]. rewrite Heq. exact (sk_parse Hb).
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

(* ---------------------------------------------------------------------- *)
(* THE COMMIT'S WHOLE ARITHMETIC (durable-disk 1b).                         *)
(*                                                                          *)
(* INSTALLING THE BATCH OVER THE HOME RESTRICTION OF THE PRE-COMMIT IMAGE    *)
(* LANDS EXACTLY ON THE LOGGED VIEW [L].  The two hypotheses are the log's   *)
(* own rows and nothing else:                                               *)
(*                                                                          *)
(*  - OFF the batch, the logged view IS the physical home block -- this is   *)
(*    [LogInv.log_mirror_tie_body], row (b), read through the caller's       *)
(*    off-header view [V];                                                   *)
(*  - AT the batch, the logged value of an entry's home block is the         *)
(*    content that entry's log SLOT holds -- which is the copy loop's own    *)
(*    ghost step composed with the slot row the committer chains.            *)
(*                                                                          *)
(* Because the two together pin [L] at every home block, no separate domain  *)
(* hypothesis about [L] is needed: they ARE the domain fact on [home], in    *)
(* the only two pieces it splits into.                                       *)
(* ---------------------------------------------------------------------- *)
Lemma fs_install_is_logged (V : Z -> list (bv 8)) (L : gmap Z (list (bv 8)))
    (cov : gset Z) (ls : Z) (Ws : list Z) :
  NoDup Ws ->
  (forall b : Z, b ∈ Ws -> b ∈ fs_home_set cov ls) ->
  (forall b : Z, b ∈ fs_home_set cov ls -> b ∉ Ws -> L !! b = Some (V b)) ->
  (forall (i : nat) (b : Z), Ws !! i = Some b ->
     L !! b = Some (V (log_slot_bno ls i))) ->
  fs_install V ls Ws (fs_restrict V (fs_home_set cov ls))
  = fs_restrict (dv_of_D L) (fs_home_set cov ls).
Proof.
  intros Hnd Hin Hmiss Hhit. apply map_eq. intros b.
  destruct (decide (b ∈ fs_home_set cov ls)) as [Hb|Hb].
  - assert (Hrb : fs_restrict (dv_of_D L) (fs_home_set cov ls) !! b
                  = Some (dv_of_D L b))
      by (apply fs_restrict_lookup_Some; done).
    rewrite Hrb.
    destruct (decide (b ∈ Ws)) as [Hbw|Hbw].
    + apply elem_of_list_lookup_1 in Hbw as [i Hi].
      rewrite (fs_install_hit V ls Ws (fs_restrict V (fs_home_set cov ls))
                 i b Hnd Hi).
      rewrite /dv_of_D (Hhit i b Hi) //.
    + rewrite (fs_install_miss V ls Ws (fs_restrict V (fs_home_set cov ls))
                 b Hbw).
      assert (Hrv : fs_restrict V (fs_home_set cov ls) !! b = Some (V b))
        by (apply fs_restrict_lookup_Some; done).
      rewrite Hrv /dv_of_D (Hmiss b Hb Hbw) //.
  - assert (Hbw : b ∉ Ws) by (intros Hc; exact (Hb (Hin b Hc))).
    rewrite (fs_install_miss V ls Ws (fs_restrict V (fs_home_set cov ls))
               b Hbw).
    rewrite (fs_restrict_lookup_None V (fs_home_set cov ls) b Hb).
    rewrite (fs_restrict_lookup_None (dv_of_D L) (fs_home_set cov ls) b Hb) //.
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
   ([fs_install_v_seq_permit]) run without any picture of the home side of
   the disk. *)
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
(* 1c'''. TORN WRITES (claude-notes/completed/sector-atomic-disk.md).       *)
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

(* -- THE MIRROR UNDER A TORN WRITE (sector-atomic-disk.md stage 3) --------
   The widened mirror ([LogDefs.lm_view], durable-disk stage E2) pins the
   durable extent BLOCK BY BLOCK, so a write that lands anywhere inside block
   [blk] -- a whole block, one 512-byte sector, or a torn half of one -- moves
   exactly that block's row to whatever the disk now holds and leaves every
   other row alone.  Content-agnostic on purpose: this is what carries a
   half-written block across the rest of a commit. *)
Lemma log_mirror_ok_upd_pt (M : log_mirror) (P P' : Z -> list (bv 8))
    (cov : gset Z) (ls blk : Z) :
  (forall c, c <> blk -> P' c = P c) ->
  log_mirror_ok M P cov ls ->
  log_mirror_ok (lm_upd M blk (P' blk)) P' cov ls.
Proof.
  intros Hmiss Hok b Hb. destruct (decide (b = blk)) as [-> | Hne].
  - by rewrite lm_upd_view_eq.
  - rewrite (lm_upd_view_ne _ _ _ _ Hne) (Hmiss b Hne). exact (Hok b Hb).
Qed.

(* ...and the form a SECTOR write arrives in: [bs] at byte offset [o] INSIDE
   block [blk].  [fs_blocks_sub_ne] is the "every other block" half; the
   written block's new row is left as the disk's own reading of it, because a
   torn row has no shorter name ([fs_blocks_splice] spells it out when a
   caller needs the bytes). *)
Lemma log_mirror_ok_upd_sector (M : log_mirror) (dk : Z -> bv 8)
    (cov : gset Z) (ls blk : Z) (o : nat) (bs : list (bv 8)) :
  (o + length bs <= BSIZE)%nat ->
  log_mirror_ok M (fs_blocks dk) cov ls ->
  log_mirror_ok
    (lm_upd M blk
       (fs_blocks (disk_write dk (blk * Z.of_nat BSIZE + Z.of_nat o) bs) blk))
    (fs_blocks (disk_write dk (blk * Z.of_nat BSIZE + Z.of_nat o) bs)) cov ls.
Proof.
  intros Hfit Hok.
  apply (log_mirror_ok_upd_pt _ (fs_blocks dk)); [| exact Hok].
  intros c Hc. exact (fs_blocks_sub_ne dk blk c o bs Hfit Hc).
Qed.

(* THE HEADER's READING IS A SECTOR-0 READING (sector-atomic-disk.md §0): the
   decoder reads bytes [0, 124) only, so two pictures of the header block that
   agree on sector 0 carry the same [lm_hdr]. *)
Lemma lm_hdr_sector0 (M M' : log_mirror) (ls : Z) :
  ((lm_hdr M ls).1 <= LOGBLOCKS)%nat ->
  take virtio_sector_bytes (lm_view M' (log_hdr_bno ls))
  = take virtio_sector_bytes (lm_view M (log_hdr_bno ls)) ->
  lm_hdr M' ls = lm_hdr M ls.
Proof. rewrite /lm_hdr. intros Hn Heq. by apply hdr_dec_sector0_eq. Qed.

(* THE COMMIT IS ATOMIC, at the mirror: a write that lands only in SECTOR 1 of
   the header block moves the picture of that block but NOT its reading, in
   either landing order. *)
Lemma lm_hdr_upd_sector1 (M : log_mirror) (dk : Z -> bv 8)
    (cov : gset Z) (ls : Z) (bs : list (bv 8)) :
  ((lm_hdr M ls).1 <= LOGBLOCKS)%nat ->
  length bs = virtio_sector_bytes ->
  log_mirror_ok M (fs_blocks dk) cov ls ->
  lm_hdr (lm_upd M (log_hdr_bno ls)
            (fs_blocks (disk_write dk
               (log_hdr_bno ls * Z.of_nat BSIZE + virtio_sector_size) bs)
               (log_hdr_bno ls))) ls
  = lm_hdr M ls.
Proof.
  intros Hn Hlen Hok. apply (lm_hdr_sector0 M _ ls Hn).
  rewrite lm_upd_view_eq (fs_blocks_sector1 dk (log_hdr_bno ls) bs Hlen).
  by rewrite (Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)).
Qed.


(* ---------------------------------------------------------------------- *)
(* 1c'''. THE TWO SECTORS OF AN XV6 BLOCK WRITE                            *)
(*        (claude-notes/completed/sector-atomic-disk.md §6e).                *)
(*                                                                          *)
(* A [BSIZE]-byte block write is exactly two 512-byte landings, and the WAL  *)
(* owes one view shift per landing, chained ([RiscvPtsto.disk_seq_permit]).  *)
(* These are the geometry facts every one of those chains runs on: what the  *)
(* two sectors ARE as [disk_wr]s in the block view's own spelling, and what  *)
(* the mirror's picture of the written block is after each one.             *)
(* ---------------------------------------------------------------------- *)

Lemma wr_nsectors_block (off : Z) (bs : list (bv 8)) :
  length bs = BSIZE -> wr_nsectors (Some (off, bs)) = 2%nat.
Proof.
  intro Hlen. rewrite /wr_nsectors /= Hlen /sector_count /BSIZE
    /virtio_sector_bytes. reflexivity.
Qed.

Lemma wr_sector_blk0 (blk : Z) (bs : list (bv 8)) :
  wr_sector (Some ((1024 * blk)%Z, bs)) 0
  = Some ((blk * Z.of_nat BSIZE + Z.of_nat 0)%Z, take virtio_sector_bytes bs).
Proof.
  cbn [wr_sector fst snd].
  assert (Ho : (1024 * blk + virtio_sector_size * Z.of_nat 0)%Z
               = (blk * Z.of_nat BSIZE + Z.of_nat 0)%Z)
    by (rewrite /BSIZE /virtio_sector_size; lia).
  assert (Hb : take virtio_sector_bytes (drop (virtio_sector_bytes * 0)%nat bs)
               = take virtio_sector_bytes bs)
    by (rewrite Nat.mul_0_r drop_0; reflexivity).
  rewrite Ho Hb. reflexivity.
Qed.

Lemma wr_sector_blk1 (blk : Z) (bs : list (bv 8)) :
  wr_sector (Some ((1024 * blk)%Z, bs)) 1
  = Some ((blk * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z,
          take virtio_sector_bytes (drop virtio_sector_bytes bs)).
Proof.
  cbn [wr_sector fst snd].
  assert (Ho : (1024 * blk + virtio_sector_size * Z.of_nat 1)%Z
               = (blk * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z)
    by (rewrite /BSIZE /virtio_sector_size /virtio_sector_bytes; lia).
  assert (Hb : take virtio_sector_bytes (drop (virtio_sector_bytes * 1)%nat bs)
               = take virtio_sector_bytes (drop virtio_sector_bytes bs))
    by (rewrite Nat.mul_1_r; reflexivity).
  rewrite Ho Hb. reflexivity.
Qed.

(* the two slices reassemble the block *)
Lemma sector_split (bs : list (bv 8)) :
  length bs = BSIZE ->
  take virtio_sector_bytes bs ++ take virtio_sector_bytes (drop virtio_sector_bytes bs)
  = bs.
Proof.
  intro Hlen.
  rewrite (take_ge (drop virtio_sector_bytes bs));
    [apply take_drop | rewrite length_drop Hlen bsize_two_sectors; lia].
Qed.

Lemma sector0_len (bs : list (bv 8)) :
  length bs = BSIZE -> length (take virtio_sector_bytes bs) = virtio_sector_bytes.
Proof.
  intro Hlen. rewrite length_take Hlen bsize_two_sectors. lia.
Qed.

Lemma sector1_len (bs : list (bv 8)) :
  length bs = BSIZE ->
  length (take virtio_sector_bytes (drop virtio_sector_bytes bs))
  = virtio_sector_bytes.
Proof.
  intro Hlen. rewrite length_take length_drop Hlen bsize_two_sectors. lia.
Qed.

(* ---- THE BLOCK PICTURE ONE LANDING LEAVES BEHIND (durable-disk flip-B).
   The at-form permits never had to name it -- their receipt exposes the
   header READING, which a non-header landing does not move -- but a
   VALUE-chained permit does: its receipt is the half at a closed term, so
   the half-written block needs a name.  Two names, one per sector, and the
   two composition lemmas that say both landing orders end at [bs]. ---- *)

Definition blk_sec0 (old bs : list (bv 8)) : list (bv 8) :=
  take virtio_sector_bytes bs ++ drop virtio_sector_bytes old.

Definition blk_sec1 (old bs : list (bv 8)) : list (bv 8) :=
  take virtio_sector_bytes old ++ drop virtio_sector_bytes bs.

Lemma blk_sec0_len (old bs : list (bv 8)) :
  length old = BSIZE -> length bs = BSIZE -> length (blk_sec0 old bs) = BSIZE.
Proof.
  intros Ho Hb. rewrite /blk_sec0 length_app length_take length_drop Ho Hb.
  rewrite bsize_two_sectors. lia.
Qed.

Lemma blk_sec1_len (old bs : list (bv 8)) :
  length old = BSIZE -> length bs = BSIZE -> length (blk_sec1 old bs) = BSIZE.
Proof.
  intros Ho Hb. rewrite /blk_sec1 length_app length_take length_drop Ho Hb.
  rewrite bsize_two_sectors. lia.
Qed.

(* the header's READING is a sector-0 reading, so sector 1's landing leaves
   the first 512 bytes -- and therefore the decode -- exactly where it was *)
Lemma blk_sec1_take0 (old bs : list (bv 8)) :
  (virtio_sector_bytes <= length old)%nat ->
  take virtio_sector_bytes (blk_sec1 old bs) = take virtio_sector_bytes old.
Proof.
  intro Ho. rewrite /blk_sec1.
  assert (Hl : length (take virtio_sector_bytes old) = virtio_sector_bytes)
    by (rewrite length_take; lia).
  rewrite take_app_le; [| lia]. rewrite take_take Nat.min_id //.
Qed.

Lemma blk_sec0_take0 (old bs : list (bv 8)) :
  length bs = BSIZE ->
  take virtio_sector_bytes (blk_sec0 old bs) = take virtio_sector_bytes bs.
Proof.
  intro Hb. rewrite /blk_sec0.
  assert (Hl : length (take virtio_sector_bytes bs) = virtio_sector_bytes)
    by exact (sector0_len bs Hb).
  rewrite take_app_le; [| lia]. rewrite take_take Nat.min_id //.
Qed.

(* SECTOR 0 THEN SECTOR 1 *)
Lemma blk_sec_01 (old bs : list (bv 8)) :
  length bs = BSIZE -> blk_sec1 (blk_sec0 old bs) bs = bs.
Proof.
  intro Hb. rewrite /blk_sec1 (blk_sec0_take0 old bs Hb). apply take_drop.
Qed.

(* ...AND SECTOR 1 THEN SECTOR 0, at the same picture -- which is what lets
   ONE receipt serve both branches of the sequential permit. *)
Lemma blk_sec_10 (old bs : list (bv 8)) :
  length old = BSIZE -> blk_sec0 (blk_sec1 old bs) bs = bs.
Proof.
  intro Ho. rewrite /blk_sec0 /blk_sec1.
  assert (Hl : length (take virtio_sector_bytes old) = virtio_sector_bytes)
    by (rewrite length_take Ho bsize_two_sectors; lia).
  rewrite drop_app_length'; [| exact (eq_sym Hl)]. apply take_drop.
Qed.

(* ...and the two landings, physically: what [fs_blocks] holds at the written
   block afterwards, as a function of the PRE-image's row alone. *)
Lemma fs_blocks_blk_sec0 (dk : Z -> bv 8) (blk : Z) (bs : list (bv 8)) :
  length bs = BSIZE ->
  fs_blocks (disk_write dk (blk * Z.of_nat BSIZE + Z.of_nat 0)%Z
               (take virtio_sector_bytes bs)) blk
  = blk_sec0 (fs_blocks dk blk) bs.
Proof.
  intro Hlen.
  assert (Hs0 : length (take virtio_sector_bytes bs) = virtio_sector_bytes)
    by exact (sector0_len bs Hlen).
  assert (Hfit : (0 + length (take virtio_sector_bytes bs) <= BSIZE)%nat)
    by (rewrite Hs0 bsize_two_sectors; lia).
  rewrite (fs_blocks_splice dk blk 0 (take virtio_sector_bytes bs) Hfit).
  rewrite /blk_sec0 take_0 /= Hs0 //.
Qed.

Lemma fs_blocks_blk_sec1 (dk : Z -> bv 8) (blk : Z) (bs : list (bv 8)) :
  length bs = BSIZE ->
  fs_blocks (disk_write dk (blk * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z
               (take virtio_sector_bytes (drop virtio_sector_bytes bs))) blk
  = blk_sec1 (fs_blocks dk blk) bs.
Proof.
  intro Hlen.
  assert (Hs1 : length (take virtio_sector_bytes (drop virtio_sector_bytes bs))
                = virtio_sector_bytes)
    by exact (sector1_len bs Hlen).
  assert (Hfit : (virtio_sector_bytes
                  + length (take virtio_sector_bytes (drop virtio_sector_bytes bs))
                  <= BSIZE)%nat)
    by (rewrite Hs1 bsize_two_sectors; lia).
  rewrite (fs_blocks_splice dk blk virtio_sector_bytes _ Hfit).
  rewrite /blk_sec1 Hs1.
  rewrite (take_ge (drop virtio_sector_bytes bs));
    [| rewrite length_drop Hlen bsize_two_sectors; lia].
  rewrite (drop_ge (fs_blocks dk blk));
    [| rewrite fs_blocks_length bsize_two_sectors; lia].
  rewrite app_nil_r //.
Qed.

(* ---- THE PICTURE UNDER A TORN BLOCK WRITE, in either landing order.  ONE
   value comes out of both, and that is what lets a value-chained permit's
   two branches share a single receipt (the at-forms got this for free: the
   header READING they expose does not move at a non-header block). ---- *)

Lemma lm_hdr_upd_ne (M : log_mirror) (ls blk : Z) (bs : list (bv 8)) :
  blk <> log_hdr_bno ls -> lm_hdr (lm_upd M blk bs) ls = lm_hdr M ls.
Proof.
  intro Hne.
  rewrite /lm_hdr
    (lm_upd_view_ne M blk (log_hdr_bno ls) bs (not_eq_sym Hne)) //.
Qed.

(* the HEADER's own row, moved by its SECOND sector: the picture changes and
   the reading does not -- "the commit is atomic", at the chained value *)
Lemma lm_hdr_upd_hdr_sec1 (M : log_mirror) (ls : Z) (bs : list (bv 8)) :
  ((lm_hdr M ls).1 <= LOGBLOCKS)%nat ->
  (virtio_sector_bytes <= length (lm_view M (log_hdr_bno ls)))%nat ->
  lm_hdr (lm_upd M (log_hdr_bno ls)
            (blk_sec1 (lm_view M (log_hdr_bno ls)) bs)) ls
  = lm_hdr M ls.
Proof.
  intros Hn Ho. rewrite /lm_hdr lm_upd_view_eq.
  apply (hdr_dec_sector0_eq (lm_view M (log_hdr_bno ls))); [exact Hn|].
  exact (blk_sec1_take0 _ bs Ho).
Qed.

Lemma lm_upd_sec_01 (M : log_mirror) (blk : Z) (bs : list (bv 8)) :
  length bs = BSIZE ->
  lm_upd (lm_upd M blk (blk_sec0 (lm_view M blk) bs)) blk
    (blk_sec1 (lm_view (lm_upd M blk (blk_sec0 (lm_view M blk) bs)) blk) bs)
  = lm_upd M blk bs.
Proof. intro Hb. rewrite lm_upd_view_eq (blk_sec_01 _ bs Hb) lm_upd_idem //. Qed.

Lemma lm_upd_sec_10 (M : log_mirror) (blk : Z) (bs : list (bv 8)) :
  length (lm_view M blk) = BSIZE ->
  lm_upd (lm_upd M blk (blk_sec1 (lm_view M blk) bs)) blk
    (blk_sec0 (lm_view (lm_upd M blk (blk_sec1 (lm_view M blk) bs)) blk) bs)
  = lm_upd M blk bs.
Proof. intro Ho. rewrite lm_upd_view_eq (blk_sec_10 _ bs Ho) lm_upd_idem //. Qed.

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
  hdr_wf P cov logstart.
(* THE [P_wf] CONJUNCT IS NO LONGER HERE, AND IT IS NO LONGER PURE
   (durable-disk 1d).  It used to be [FsWf.fs_durable_wf (fr_D r)] -- a
   whole-state pure sweep, with body [True].  Ruling 3
   (claude-notes/design/fs-state.md) has no whole-state pure predicate at
   all: the durable file system is a family of nested SEPARATION-LOGIC
   predicates over its OWN ghost names, so the conjunct is an [iProp] and it
   lives in [P_fs] as [FsDurSnap.P_dur (fr_D r)].  What survives here is
   exactly what the WAL layer proves for itself: recovery, the history's
   last element and the on-disk header's invariant. *)

Lemma fs_rec_wf_hist_ne r P cov logstart :
  fs_rec_wf r P cov logstart -> fr_hist r <> [].
Proof. intros (_ & Hlast & _) Hnil. rewrite Hnil in Hlast. discriminate. Qed.


(* ---------------------------------------------------------------------- *)
(* 1d''. THE RECORD, UNDER ONE 512-BYTE LANDING.                           *)
(*                                                                          *)
(* The §3 table of sector-atomic-disk.md, as three pure lemmas: what a       *)
(* single sector of a WAL write does to [fs_rec_wf].  Each is content- and   *)
(* offset-AGNOSTIC inside the block it lands in, which is exactly why the    *)
(* same lemma serves both sectors and both landing orders.                   *)
(* ---------------------------------------------------------------------- *)

(* LOG FILL.  The on-disk header is clean, so recovery never reads slot [i]  *)
(* and the landing -- half a slot or all of it -- is invisible to it.        *)
Lemma fs_rec_wf_logfill_sector (cov : gset Z) (ls : Z) (i : nat)
    (M : log_mirror) (o : nat) (sbs : list (bv 8))
    (r : fs_rec) (dk : Z -> bv 8) :
  (i < LOGBLOCKS)%nat ->
  (o + length sbs <= BSIZE)%nat ->
  lm_hdr M ls = (0%nat, []) ->
  log_mirror_ok M (fs_blocks dk) cov ls ->
  fs_rec_wf r (fs_blocks dk) cov ls ->
  fs_rec_wf r (fs_blocks (disk_write dk
     (log_slot_bno ls i * Z.of_nat BSIZE + Z.of_nat o)%Z sbs)) cov ls.
Proof.
  intros Hi Hfit HM Hok (Hrec & Hlast & Hhwf).
  assert (Hmiss : forall c, c <> log_slot_bno ls i ->
            fs_blocks (disk_write dk
               (log_slot_bno ls i * Z.of_nat BSIZE + Z.of_nat o)%Z sbs) c
            = fs_blocks dk c)
    by (intros c Hc; exact (fs_blocks_sub_ne dk _ c o sbs Hfit Hc)).
  assert (Hdk0 : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (0%nat, []))
    by (rewrite -(Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)); exact HM).
  assert (Hn0 : hdr_n (fs_blocks dk (log_hdr_bno ls)) = 0)
    by (rewrite -hdr_dec_n Hdk0 //).
  rewrite /fs_rec_wf. split_and!.
  - exact (fs_recovery_logfill (fs_blocks dk) _ (fr_D r) cov ls i Hi Hmiss Hn0 Hrec).
  - exact Hlast.
  - refine (hdr_wf_ext _ _ _ _ _ Hhwf).
    apply Hmiss, not_eq_sym, log_slot_ne_hdr.
Qed.

(* INSTALL.  The header names [b] at index [i], so recovery re-installs it
   from slot [i] whatever the landing left there. *)
Lemma fs_rec_wf_install_sector (cov : gset Z) (ls : Z) (nn : nat) (Ws : list Z)
    (i : nat) (b : Z) (M : log_mirror) (o : nat) (sbs : list (bv 8))
    (r : fs_rec) (dk : Z -> bv 8) :
  NoDup Ws -> (length Ws <= LOGBLOCKS)%nat -> Ws !! i = Some b ->
  b ∉ log_region_set ls ->
  (o + length sbs <= BSIZE)%nat ->
  lm_hdr M ls = (nn, Ws) ->
  log_mirror_ok M (fs_blocks dk) cov ls ->
  fs_rec_wf r (fs_blocks dk) cov ls ->
  fs_rec_wf r (fs_blocks (disk_write dk
     (b * Z.of_nat BSIZE + Z.of_nat o)%Z sbs)) cov ls.
Proof.
  intros Hnd Hwlen Hi Hb Hfit HM Hok (Hrec & Hlast & Hhwf).
  assert (Hmiss : forall c, c <> b ->
            fs_blocks (disk_write dk (b * Z.of_nat BSIZE + Z.of_nat o)%Z sbs) c
            = fs_blocks dk c)
    by (intros c Hc; exact (fs_blocks_sub_ne dk b c o sbs Hfit Hc)).
  assert (Hhdr : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (nn, Ws))
    by (rewrite -(Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)); exact HM).
  rewrite /fs_rec_wf. split_and!.
  - apply (fs_recovery_install (fs_blocks dk) _ (fr_D r) cov ls i b);
      rewrite ?Hhdr /=; assumption.
  - exact Hlast.
  - refine (hdr_wf_ext _ _ _ _ _ Hhwf).
    apply Hmiss, not_eq_sym. by apply home_ne_hdr.
Qed.

(* THE HEADER's SECOND SECTOR -- "the commit is atomic".  Nothing recovery
   reads changes, in either landing order and for every header write kind
   (commit, clear, boot swap): the decoder reads bytes [0, 124) only, and the
   [hdr_wf] bound it needs to say so comes out of the record itself. *)
Lemma fs_rec_wf_hdr_sector1 (cov : gset Z) (ls : Z) (sbs : list (bv 8))
    (r : fs_rec) (dk : Z -> bv 8) :
  length sbs = virtio_sector_bytes ->
  fs_rec_wf r (fs_blocks dk) cov ls ->
  fs_rec_wf r (fs_blocks (disk_write dk
     (log_hdr_bno ls * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z sbs))
     cov ls.
Proof.
  intros Hlen (Hrec & Hlast & Hhwf).
  rewrite -virtio_sector_size_bytes.
  assert (Hfit : (virtio_sector_bytes + length sbs <= BSIZE)%nat)
    by (rewrite Hlen bsize_two_sectors; lia).
  assert (Hmiss : forall c, c <> log_hdr_bno ls ->
            fs_blocks (disk_write dk
               (log_hdr_bno ls * Z.of_nat BSIZE + virtio_sector_size)%Z sbs) c
            = fs_blocks dk c).
  { intros c Hc. rewrite virtio_sector_size_bytes.
    exact (fs_blocks_sub_ne dk _ c virtio_sector_bytes sbs Hfit Hc). }
  assert (Hsec : take virtio_sector_bytes
            (fs_blocks (disk_write dk
               (log_hdr_bno ls * Z.of_nat BSIZE + virtio_sector_size)%Z sbs)
               (log_hdr_bno ls))
          = take virtio_sector_bytes (fs_blocks dk (log_hdr_bno ls)))
    by exact (fs_blocks_sector1 dk (log_hdr_bno ls) sbs Hlen).
  rewrite /fs_rec_wf. split_and!.
  - exact (fs_recovery_hdr_sector0 (fs_blocks dk) _ (fr_D r) cov ls
             (proj1 Hhwf) Hsec Hmiss Hrec).
  - exact Hlast.
  - exact (hdr_wf_sector0 (fs_blocks dk) _ cov ls Hsec Hhwf).
Qed.

(* ...and the reading the header's FIRST sector leaves behind, which is what
   every header-write kind's sector-0 shift is stated at: the block content
   the landing produces decodes exactly as the whole image would. *)
Lemma hdr_dec_blk_sector0 (dk : Z -> bv 8) (ls : Z) (bs : list (bv 8)) :
  length bs = BSIZE ->
  ((hdr_dec bs).1 <= LOGBLOCKS)%nat ->
  hdr_dec (fs_blocks (disk_write dk
     (log_hdr_bno ls * Z.of_nat BSIZE + Z.of_nat 0)%Z
     (take virtio_sector_bytes bs)) (log_hdr_bno ls))
  = hdr_dec bs.
Proof.
  intros Hlen Hn.
  assert (Hs : take virtio_sector_bytes
            (fs_blocks (disk_write dk
               (log_hdr_bno ls * Z.of_nat BSIZE + Z.of_nat 0)%Z
               (take virtio_sector_bytes bs)) (log_hdr_bno ls))
          = take virtio_sector_bytes bs).
  { rewrite Nat2Z.inj_0 Z.add_0_r.
    exact (fs_blocks_sector0 dk (log_hdr_bno ls) (take virtio_sector_bytes bs)
             (sector0_len bs Hlen)). }
  exact (hdr_dec_sector0_eq bs _ Hn Hs).
Qed.

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
  (* THE DURABLE BYTE VIEW's gname is NOT here (durable-disk 2c-pre): it is
     [RiscvPtsto.riscv_dview_name], a FIXED-layer field, and it reaches
     every definition below as the [gamma_v] PARAMETER this section threads
     -- for the same reason [fcn_swap] / [fcn_reg] / [fcn_start] are
     parameters, and with the same seam equation.  It had to move: the FS's
     durable instance [Gamma_D] is stated over [Phi_D a v := a -> v at
     gamma_D] and a CLIENT (the log's parked payload, the commit debt) must
     name it, which a gname bound existentially inside [P_fs] can never
     be. *)
}.

Section fs_crash.
  Context `{!fsCrashG Σ, !lockG Σ}.
  (* bare constraints, deliberately not [fsCrashG] fields -- see
     [fs_crash_names] above *)
  Context `{!ghost_mapG Σ nat riscvEraGS, !mono_natG Σ,
            !ghost_varG Σ log_mirror, !diskImgG Σ}.
  (* THE DURABLE SNAPSHOT's two remaining classes (lane CE).  [P_dur] is a
     function of the committed map alone -- its gname family is existential
     -- so carrying it costs [P_fs] no argument; what it does cost is these
     two capacity constraints, which every consumer already has out of
     [Xv6Cameras.xv6G]. *)
  Context `{!fsLinkG Σ, !fsTopG Σ}.

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
  (* ==================================================================== *)
  (* 2c. THE FS LAYER'S HALF OF THE CRASH PREDICATE                        *)
  (*     (durable-fs-plan.md sections 1 and 3)                             *)
  (* ==================================================================== *)

  (* It is the DURABLE SNAPSHOT [FsDurSnap.P_dur (fr_D r)], a function of
     the committed map alone.  The [gamma_v] parameter this section threads
     (instantiated at [RiscvPtsto.riscv_dview_name] by the seam section
     below) is no longer read by anything here; it survives only so that the
     ~90 files that name [fs_crash_seam] keep their statements, and its
     deletion is a separate sweep of [Pc]'s arity. *)

  Definition P_fs (γs : fs_crash_names) (γv : gname)
      (Γd : fs_dur_names) (cov : gset Z)
      (logstart : Z) (dk : Z -> bv 8) : iProp Σ :=
    (∃ r : fs_rec,
       fs_hist_auth (fcn_hist γs) (fr_hist r) ∗
       ⌜fs_rec_wf r (fs_blocks dk) cov logstart⌝ ∗
       fs_arm γs cov logstart dk ∗
       (* ---- THE DURABLE SNAPSHOT (lane CE, plan sections 1 and 3) -------
          ONE copy of the file-system predicate over its OWN, existentially
          quantified ghost names, describing the committed map [fr_D r] --
          never updated: at each group commit the WAL drops it and allocates
          a fresh one ([FsDurSnap.dsnap_step_of]).  It is indexed by
          [fr_D r] alone, so a permit that does not move the committed view
          frames it untouched and the COMMIT is the one write that advances
          it -- exactly ruling 2's "commit is the only write kind that moves
          [D]".  It is not a statement about [dk]: it is invariant under
          every re-indexing ([P_fs_rec_agree]), for the reason the old pure
          conjunct was.  ARITY-FREE: [P_dur] is a function of the map, so
          the [gamma_v] parameter this section threads is untouched. *)
       P_dur (fr_D r))%I.

  (* THE CRASH PREDICATE AS ADEQUACY FIXES IT, at RAW gnames.  Adequacy
     allocates the swap counter, the generation registry and the started
     counter inside its own proof, so a client-chosen [Pc] can only name them
     if they are PASSED to it -- which is what [HPc]'s three arguments are.
     [γs] stays existential because the history gname is allocated under the
     update, and the three seam equations are all any WAL fupd needs (they are
     exactly what [fs_arm_acc] reads).  Stated HERE, in the section that must
     stay [riscvFixedGS]-free, because this IS the value the fixed record's
     [riscv_crash_pred] field is built from. *)
  Definition P_fs_rec_named (γsw γreg γst γv : gname) (Γd : fs_dur_names)
      (cov : gset Z) (ls : Z)
      (dk : Z -> bv 8) : iProp Σ :=
    (∃ γs : fs_crash_names,
       ⌜fcn_swap γs = γsw /\ fcn_reg γs = γreg /\ fcn_start γs = γst⌝ ∗
       P_fs γs γv Γd cov ls dk)%I.

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
  Definition P_fs_named (γd : gname) (N : nat) (γsw γreg γst γv : gname)
      (Γd : fs_dur_names)
      (cov : gset Z) (ls : Z) : iProp Σ :=
    (∃ dk : Z -> bv 8,
       disk_img_bytes γd 0 (disk_read dk 0 N) ∗
       ⌜fs_extent cov ls N⌝ ∗
       P_fs_rec_named γsw γreg γst γv Γd cov ls dk)%I.

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

  Lemma P_fs_rec_agree (γsw γreg γst γv : gname) (Γd : fs_dur_names)
      (cov : gset Z) (ls : Z)
      (N : nat) (dk dk' : Z -> bv 8) :
    disk_read dk 0 N = disk_read dk' 0 N ->
    fs_extent cov ls N ->
    P_fs_rec_named γsw γreg γst γv Γd cov ls dk -∗ P_fs_rec_named γsw γreg γst γv Γd cov ls dk'.
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
    rewrite /P_fs. iDestruct "H" as (r) "(Hh & %Hwf & Harm & Hdur)".
    iExists r. iFrame "Hh". iSplitR.
    { iPureIntro. rewrite /fs_rec_wf in Hwf *.
      destruct Hwf as (Hrec & Hlast & Hhwf).
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
      - exact (hdr_wf_ext _ _ _ _ Hhdreq Hhwf). }
    (* the snapshot's side is not about [dk]: it is at [fr_D r] *)
    iFrame "Hdur".
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
  Lemma P_fs_recovers γs γv Γd cov logstart dk :
    P_fs γs γv Γd cov logstart dk -∗
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
  Lemma P_fs_receipt_committed γs γv Γd cov logstart dk D :
    P_fs γs γv Γd cov logstart dk -∗ fs_receipt γs D -∗
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

  (* ==================================================================== *)
  (*  THE COMMIT'S RECEIPT (lane CE, plan section 3's "Commit").            *)
  (* ==================================================================== *)

  (* WHAT THE DURABLE CONJUNCT IS WORTH, as one citable sentence: the REAL
     disk recovers to a committed map [D], and [D] IS a file system.  Every
     commit re-establishes it at the map its own receipt names -- the
     permit's conclusion is [fs_receipt_any (fs_restrict (dv_of_D L)
     (fs_home_set cov ls))], i.e. "[D'] = the logged view [L] on the home
     maps", and [fs_commit_L_sector0_rec] allocates the snapshot at exactly
     that [D'].  So this lemma read after a commit says: what the machine
     would recover to is the file system the batch just made.

     PURE and NON-DESTRUCTIVE: the tie inside [P_dur] is a [⌜ ⌝], so
     reading it costs nothing ([FsDurSnap.P_dur_tie_keep]).

     THE STATE IS DETERMINED BY THE MAP, which is why the existential [S]
     here (and inside [LogSnapLaw.snap_law_ok], where the WAL cannot name
     the file system's own abstract state) loses nothing: any two states
     that fit the same committed bytes have the same record, entry array and
     block map at every inum ([FsDurSnap.snap_bytes_node_inj]), the same
     superblock ([snap_bytes_sb_inj]) and the same used bits
     ([snap_bytes_used_agree]). *)
  Lemma fs_commit_receipt γs γv Γd cov ls dk :
    P_fs γs γv Γd cov ls dk -∗
      ∃ (D : gmap Z (list (bv 8))) (S : fs_state_rec),
        ⌜fs_recovery (fs_blocks dk) D cov ls⌝ ∗ ⌜snap_ok S D⌝ ∗
        P_fs γs γv Γd cov ls dk.
  Proof.
    rewrite /P_fs. iIntros "Hp". iDestruct "Hp" as (r) "(Hh & %Hwf & Harm & Hdur)".
    iDestruct (P_dur_tie_keep with "Hdur") as (S Hok) "Hdur".
    iExists (fr_D r), S. iSplitR; [iPureIntro; exact (proj1 Hwf) |].
    iSplitR; [iPureIntro; exact Hok |].
    iExists r. iFrame "Hh Harm Hdur". iPureIntro. exact Hwf.
  Qed.

  (* ...and the ACCESSOR the boot mint (plan section 5, stage 4) takes: the
     snapshot itself, lent out of the crash predicate with the record's own
     recovery fact beside it, and a wand that puts it back.  This is the
     channel through which an era re-founds its file system from the
     previous era's committed state instead of from a decode of [fs.img]. *)
  Lemma P_fs_dur_acc γs γv Γd cov ls dk :
    P_fs γs γv Γd cov ls dk -∗
      ∃ D : gmap Z (list (bv 8)),
        ⌜fs_recovery (fs_blocks dk) D cov ls⌝ ∗ P_dur D ∗
        (P_dur D -∗ P_fs γs γv Γd cov ls dk).
  Proof.
    rewrite /P_fs. iIntros "Hp". iDestruct "Hp" as (r) "(Hh & %Hwf & Harm & Hdur)".
    iExists (fr_D r). iSplitR; [iPureIntro; exact (proj1 Hwf) |].
    iFrame "Hdur". iIntros "Hdur". iExists r. iFrame "Hh Harm Hdur".
    iPureIntro. exact Hwf.
  Qed.

  (* -------------------------------------------------------------------- *)
  (* 3a'. THE PURE PROJECTION (stage H0, claude-notes/projects/             *)
  (*      durable-disk.md): what a holder of the DURABLE AUTH -- and only    *)
  (*      adequacy's own proof ever holds it, inside [state_interp] -- can   *)
  (*      read off the crash predicate WITHOUT consuming it.                 *)
  (*                                                                         *)
  (*      The era boot entailment cannot do this itself: it never holds the   *)
  (*      fixed auth, so it can never identify [P_fs_named]'s existential     *)
  (*      image with the machine's real [v_disk].  [wp_power_loop]'s PowerOn  *)
  (*      arm DOES hold it, so it runs the one agreement here and hands the   *)
  (*      resulting PURE fact to the client -- which is the mechanism that    *)
  (*      replaces the assumed per-era image hypothesis (stage I).           *)
  (* -------------------------------------------------------------------- *)

  (* the predicate is timeless, exactly as [P_fs_any] is (that one IS this
     one, at the fixed layer's names): every conjunct is a [ghost_map] /
     [mono_nat] / [own] over a discrete cmra *)
  Global Instance P_fs_named_timeless γd N γsw γreg γst γv Γd cov ls :
    Timeless (P_fs_named γd N γsw γreg γst γv Γd cov ls).
  Proof.
    rewrite /P_fs_named /P_fs_rec_named /P_fs /fs_arm /fs_custody /fs_hist_auth.
    apply _.
  Qed.

  (* the record's own [fs_rec_wf] conjuncts, read off at its committed view
     [fr_D], AND (lane CE) the durable snapshot's tie beside them: what the
     physical disk recovers to IS a file system.  That third conjunct is the
     durability claim itself, and it is what makes [SystemAdequacy]'s trace
     corollary say something about file-system consistency rather than only
     about the log's header.  PURE throughout, hence non-destructive: the
     record and the snapshot are handed back ([FsDurSnap.P_dur_tie] spends
     nothing, the tie being a [⌜ ⌝]).  LAST, so no destructuring moves. *)
  Lemma P_fs_rec_named_wf (γsw γreg γst γv : gname) (Γd : fs_dur_names)
      (cov : gset Z) (ls : Z)
      (dk : Z -> bv 8) :
    P_fs_rec_named γsw γreg γst γv Γd cov ls dk -∗
      ⌜exists D : gmap Z (list (bv 8)),
         fs_recovery (fs_blocks dk) D cov ls /\
         hdr_wf (fs_blocks dk) cov ls /\
         exists S : fs_state_rec, snap_ok S D⌝.
  Proof.
    rewrite /P_fs_rec_named /P_fs.
    iIntros "H". iDestruct "H" as (γs) "[_ H]".
    iDestruct "H" as (r) "(_ & %Hwf & _ & Hdur)".
    iDestruct (P_dur_tie with "Hdur") as (S) "%Hok".
    iPureIntro. destruct Hwf as (Hrec & _ & Hhdr).
    exists (fr_D r). split_and!; [assumption | assumption |].
    exists S. exact Hok.
  Qed.

  (* THE PROJECTION ITSELF.  Non-destructive in every resource: the auth is
     borrowed only to run [disk_img_sized_read] -- which re-indexes the record
     at the machine's own [dk], exactly as [fs_permit_of_rec] does -- and both
     it and the predicate are handed straight back.  The [▷] strips under the
     [◇] because the predicate is timeless. *)
  Lemma P_fs_project (γd : gname) (N : nat) (γsw γreg γst γv : gname)
      (Γd : fs_dur_names)
      (cov : gset Z) (ls : Z) (dk : Z -> bv 8) :
    disk_img_auth_sized γd N dk -∗
    ▷ P_fs_named γd N γsw γreg γst γv Γd cov ls -∗
    ◇ (disk_img_auth_sized γd N dk ∗
       ▷ P_fs_named γd N γsw γreg γst γv Γd cov ls ∗
       ⌜fs_extent cov ls N /\
        exists D : gmap Z (list (bv 8)),
          fs_recovery (fs_blocks dk) D cov ls /\
          hdr_wf (fs_blocks dk) cov ls /\
          exists S : fs_state_rec, snap_ok S D⌝).
  Proof.
    iIntros "Ha HP". iMod "HP".
    rewrite /P_fs_named. iDestruct "HP" as (dk0) "(Hfr & %Hext & HPr)".
    (* the fragments read the machine's image: the record's [dk0] agrees
       with [dk] on the whole durable disk *)
    iDestruct (disk_img_sized_read with "Ha Hfr") as %Hrd.
    rewrite disk_read_length in Hrd.
    (* re-index the record at [dk], read the pure fact off it there, and
       re-index back -- the agreement runs in both directions, and nothing
       else moves *)
    iDestruct (P_fs_rec_agree γsw γreg γst γv Γd cov ls N dk0 dk
                 (eq_sym Hrd) Hext with "HPr") as "HPr".
    iDestruct (P_fs_rec_named_wf with "HPr") as %Hwf.
    iDestruct (P_fs_rec_agree γsw γreg γst γv Γd cov ls N dk dk0
                 Hrd Hext with "HPr") as "HPr".
    iModIntro. iSplitL "Ha"; [iExact "Ha"|].
    iSplitL "Hfr HPr".
    { iNext. iExists dk0. iFrame "Hfr HPr". iPureIntro. exact Hext. }
    iPureIntro. split; [exact Hext | exact Hwf].
  Qed.

  (* -------------------------------------------------------------------- *)
  (* 3a''. CUSTODY AT BIRTH (durable-disk 1a).                              *)
  (*                                                                        *)
  (*   The projection above reads a PURE fact off the record without moving  *)
  (*   anything.  This is its twin on the resource side, and it is what      *)
  (*   makes every boot-path write a value-chained one: the era's mirror     *)
  (*   variable has just been allocated at [mirror_of (fs_blocks dk)] for    *)
  (*   the MACHINE'S OWN [dk], and [RiscvAdequacy]'s PowerOn arm holds both  *)
  (*   the durable auth and the crash invariant -- so this is the one place  *)
  (*   in the system where the custody arm can be installed ALREADY TRUE of  *)
  (*   the physical disk.  A born-true value alone would not do: a later     *)
  (*   permit's image is universally quantified, so the ok-tie has to be     *)
  (*   carried from birth, which is exactly what taking custody here does.   *)
  (*                                                                        *)
  (*   Everything but the mirror variable is LENT.  The durable auth is      *)
  (*   borrowed only to re-index the record at [dk] (the same move           *)
  (*   [P_fs_project] makes, and for the same reason: [P_fs_named] closes    *)
  (*   its image existentially, so nothing inside an era can identify it     *)
  (*   with the real disk); the started auth rides [fs_arm_swap] and comes   *)
  (*   straight back.  The era then boots WITH custody, its own half and the *)
  (*   swap receipt -- so no write ever re-bases [fr_D] and [initlog] /      *)
  (*   [install_trans]'s recovering arms move no exposed ghost state.        *)
  (* -------------------------------------------------------------------- *)
  Lemma P_fs_swap (γd : gname) (N : nat) (γsw γreg γst γv : gname)
      (Γd : fs_dur_names)
      (cov : gset Z) (ls : Z) (dk : Z -> bv 8)
      (E : riscvEraGS) (gen : nat) :
    gen ↪[γreg]□ E -∗
    mono_nat_lb_own γst (S gen) -∗
    mono_nat_auth_own γst 1 (gen + 1)%nat -∗
    disk_img_auth_sized γd N dk -∗
    ghost_var (era_mirror_name E) 1 (mirror_of (fs_blocks dk)) -∗
    ▷ P_fs_named γd N γsw γreg γst γv Γd cov ls ==∗
      ◇ (mono_nat_auth_own γst 1 (gen + 1)%nat ∗
         disk_img_auth_sized γd N dk ∗
         ▷ P_fs_named γd N γsw γreg γst γv Γd cov ls ∗
         ghost_var (era_mirror_name E) (1/2) (mirror_of (fs_blocks dk)) ∗
         mono_nat_lb_own γsw (S gen)).
  Proof.
    iIntros "#Hreg #Hst Hsa Ha HM HP". iMod "HP".
    rewrite /P_fs_named. iDestruct "HP" as (dk0) "(Hfr & %Hext & HPr)".
    (* the record's image agrees with the machine's on the whole durable
       disk, which is the only thing the auth is borrowed for *)
    iDestruct (disk_img_sized_read with "Ha Hfr") as %Hrd.
    rewrite disk_read_length in Hrd.
    iDestruct (P_fs_rec_agree γsw γreg γst γv Γd cov ls N dk0 dk
                 (eq_sym Hrd) Hext with "HPr") as "HPr".
    rewrite /P_fs_rec_named. iDestruct "HPr" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite /P_fs. iDestruct "HPfs" as (r) "(Hh & %Hwf & Harm & Hdur)".
    (* the two halves: one stays with the era, one goes into the arm *)
    iEval (rewrite -Qp.half_half) in "HM".
    iDestruct (ghost_var_split with "HM") as "[HMe HMc]".
    iAssert (fs_era_reg γs gen E) as "#Hreg'".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (fs_started γs gen) as "#Hst'".
    { rewrite /fs_started Hstn. iExact "Hst". }
    iEval (rewrite -Hstn) in "Hsa".
    iMod (fs_arm_swap γs cov ls dk dk gen E (gen + 1)%nat
            (mirror_of (fs_blocks dk)) eq_refl (mirror_of_ok _ _ _)
            with "Hreg' Hst' Hsa HMc Harm") as "(Harm & Hsa & #Hswlb)".
    iEval (rewrite Hstn) in "Hsa".
    iEval (rewrite Hsw) in "Hswlb".
    (* repack at [dk], then re-index back to the record's own image *)
    iAssert (P_fs_rec_named γsw γreg γst γv Γd cov ls dk)
      with "[Hh Harm Hdur]" as "HPr".
    { rewrite /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists r. iFrame "Hh". iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hdur". iExact "Harm". }
    iDestruct (P_fs_rec_agree γsw γreg γst γv Γd cov ls N dk dk0
                 Hrd Hext with "HPr") as "HPr".
    iModIntro. iModIntro. iFrame "Hsa Ha HMe Hswlb".
    iNext. iExists dk0. iFrame "Hfr HPr". iPureIntro. exact Hext.
  Qed.

  (* THE SILVER LINING (durable-disk 1a): with the era's mirror born true,
     the era knows the committed view BY VALUE -- [fr_D] is a closed term in
     the mirror alone, with no disk in it.  That term is stage 1d's payload
     index [D0], and this is the equation that says the record's [fr_D] is
     it (the record's [fs_rec_wf] gives [fs_recovery] at the physical disk,
     and [fs_recovery_det] then pins the value). *)
  Lemma fs_recovery_of_mirror (M : log_mirror) (dk : Z -> bv 8)
      (cov : gset Z) (ls : Z) :
    lm_view M = fs_blocks dk ->
    fs_recovery (fs_blocks dk)
      (fs_install (lm_view M) ls (lm_hdr M ls).2
         (fs_restrict (lm_view M) (fs_home_set cov ls))) cov ls.
  Proof. intros HM. rewrite /fs_recovery /lm_hdr HM //. Qed.

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
  (* ...AND IT MINTS THE DURABLE SNAPSHOT (lane CE, plan section 3).  The one
     thing the snapshot needs is the PURE tie [snap_ok S D0] -- it owns no
     resource anybody else has ([FsDurSnap.P_dur_alloc] is a
     build-from-nothing update) -- so this lemma gains exactly one pure
     premise, discharged at era 0 by the image's own theorem
     ([FsDurImg.img_snap_ok], through [FsDurImg.img_boot_P_fs_dur]).  The
     [gamma_v] map adequacy still mints EMPTY is no longer read here; it is
     dropped affinely, and lane CE item 3 deletes the field. *)
  Lemma P_fs_alloc (γsw γreg γst γv : gname) (Γd : fs_dur_names) (dk0 : Z -> bv 8)
      (D0 : gmap Z (list (bv 8))) (cov : gset Z) (logstart : Z) :
    fs_recovery (fs_blocks dk0) D0 cov logstart ->
    hdr_wf (fs_blocks dk0) cov logstart ->
    (* the snapshot's own premise: the committed map IS a file system *)
    (exists S : fs_state_rec, snap_ok S D0) ->
    mono_nat_auth_own γsw 1 0%nat ∗
    ghost_map_auth γv 1 (∅ : gmap Z (bv 8)) ⊢ |==> ∃ γs : fs_crash_names,
      ⌜fcn_swap γs = γsw /\ fcn_reg γs = γreg /\ fcn_start γs = γst⌝ ∗
      P_fs γs γv Γd cov logstart dk0 ∗ fs_receipt γs D0.
  Proof.
    intros Hrec Hhwf [S Hsnap]. iIntros "[Hsw Hva]".
    iMod (fs_hist_alloc [D0]) as (γh) "[Hauth #Hlb]".
    (* THE DURABLE FILE SYSTEM IS BORN HERE (lane CE): one copy of the
       predicate over fresh names, at the committed map. *)
    iMod (P_dur_alloc S D0 Hsnap) as "Hdur".
    iModIntro. iExists (MkFsCrashNames γh γsw γreg γst).
    iSplitR; [iPureIntro; done|].
    iSplitL "Hauth Hsw Hdur".
    - rewrite /P_fs. iExists (MkFsRec D0 [D0]).
      iFrame "Hauth".
      iSplitR.
      { iPureIntro. rewrite /fs_rec_wf /=.
        split_and!; [exact Hrec | reflexivity | exact Hhwf]. }
      iSplitR "Hdur"; [| iExact "Hdur"].
      iApply fs_arm_at_rest. iExact "Hsw".
    - rewrite /fs_receipt /=. iExists []. iExact "Hlb".
  Qed.

  (* The mkfs corollary: a freshly formatted disk has an EMPTY on-disk log,
     so its committed state is just its home blocks and no recovery
     hypothesis has to be assumed at all. *)
  Lemma P_fs_alloc_clean (γsw γreg γst γv : gname) (Γd : fs_dur_names) (dk0 : Z -> bv 8)
      (cov : gset Z) (logstart : Z) :
    hdr_n (fs_blocks dk0 (log_hdr_bno logstart)) = 0 ->
    (exists S : fs_state_rec,
       snap_ok S (fs_restrict (fs_blocks dk0) (fs_home_set cov logstart))) ->
    mono_nat_auth_own γsw 1 0%nat ∗
    ghost_map_auth γv 1 (∅ : gmap Z (bv 8)) ⊢ |==> ∃ γs : fs_crash_names,
      ⌜fcn_swap γs = γsw /\ fcn_reg γs = γreg /\ fcn_start γs = γst⌝ ∗
      P_fs γs γv Γd cov logstart dk0 ∗
      fs_receipt γs (fs_restrict (fs_blocks dk0)
                       (fs_home_set cov logstart)).
  Proof.
    intros Hn Hsnap. iApply P_fs_alloc.
    - by apply (fs_recovery_clean (fs_blocks dk0) _ cov logstart Hn).
    - by apply hdr_wf_zero.
    - exact Hsnap.
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
  (* the durable snapshot's two classes (lane CE); [diskImgG] rides
     [riscvGS] already.  Every consumer has them out of [Xv6G.xv6G]. *)
  Context `{!fsLinkG Σ, !fsTopG Σ}.

  (* The crash predicate the FS client fixes [Pc] at.  [γs] is EXISTENTIAL
     because adequacy's obligation ([RiscvAdequacy]'s [HPc]) is a
     build-from-nothing entailment: the history gname is allocated under the
     update, so it cannot appear in [Pc]'s own arguments.  The three seam
     equations are what make the record's arm identifiable from outside --
     they are all a WAL fupd needs, since [fs_arm_acc] reads only
     [fcn_swap] / [fcn_reg] / [fcn_start]. *)
  (* the record at an image, at the fixed layer's names *)
  Definition P_fs_rec (cov : gset Z) (ls : Z) (dk : Z -> bv 8) : iProp Σ :=
    P_fs_rec_named riscv_swap_name riscv_registry_name riscv_start_name
      riscv_dview_name riscv_fsdur cov ls dk.

  Global Instance P_fs_rec_timeless cov ls dk : Timeless (P_fs_rec cov ls dk).
  Proof.
    rewrite /P_fs_rec /P_fs_rec_named /P_fs /fs_arm /fs_custody /fs_hist_auth.
    apply _.
  Qed.

  (* the crash predicate itself: the record AND the durable disk's fragments
     at the fixed layer's name and size *)
  Definition P_fs_any (cov : gset Z) (ls : Z) : iProp Σ :=
    P_fs_named riscv_disk_name riscv_disk_size
      riscv_swap_name riscv_registry_name riscv_start_name riscv_dview_name
      riscv_fsdur cov ls.

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
    iDestruct (P_fs_rec_agree _ _ _ _ _ cov ls riscv_disk_size dk0 dk
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

  (* A durability receipt at the record's own gnames, with [γs] existential
     for the same reason [P_fs_any] has it: adequacy allocates the history
     gname under the update, so no client-visible constant can name it. *)
  Definition fs_receipt_any (D : gmap Z (list (bv 8))) : iProp Σ :=
    (∃ γs : fs_crash_names,
       ⌜fcn_swap γs = riscv_swap_name /\ fcn_reg γs = riscv_registry_name /\
        fcn_start γs = riscv_start_name⌝ ∗ fs_receipt γs D)%I.

  Global Instance fs_receipt_any_persistent D : Persistent (fs_receipt_any D).
  Proof. rewrite /fs_receipt_any. apply _. Qed.

  (* ==================================================================== *)
  (* (6) THE SEQUENTIAL PERMITS' SHARED PIECE (sector-atomic-disk.md §6e). *)
  (*                                                                      *)
  (* A 512-byte SECTOR lands atomically and a 1024-byte BLOCK does not, so *)
  (* every WAL write owes ONE object that unfolds a landing at a time      *)
  (* ([RiscvPtsto.disk_seq_permit]): a conjunction over the two orders the *)
  (* device may choose, each order a chain of two record-level view shifts *)
  (* ending in the completion's identity permit.  What makes the chain go  *)
  (* is that the mirror half travels INSIDE the residual -- the receipt of *)
  (* the first landing is the permit for the second -- which is exactly    *)
  (* what an independent permit per sector could not do (a crash permit is *)
  (* a stateless view shift with no input slot).                           *)
  (*                                                                      *)
  (* BOTH ORDERS END AT THE SAME PICTURE ([lm_upd_idem]), so ONE receipt   *)
  (* serves both branches and every call site's postcondition is the one   *)
  (* it had before the write became torn.                                  *)
  (* ==================================================================== *)

  (* the residual is whatever the caller can make of the receipt *)
  Lemma fs_rec_permit_mono (cov : gset Z) (ls : Z) (gd : nat) (w : disk_wr)
      (R R' : iProp Σ) :
    (R -∗ R') -∗ fs_rec_permit cov ls gd w R -∗ fs_rec_permit cov ls gd w R'.
  Proof.
    iIntros "HR Hp". rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn HP".
    iMod ("Hp" $! dk n with "Hsa [//] HP") as "(HP & Hsa & HR0)".
    iModIntro. iFrame "HP Hsa". by iApply "HR".
  Qed.

  (* ==================================================================== *)
  (* (7) THE VALUE-CHAINED SEQUENTIAL PERMITS (durable-disk flip-B).       *)
  (*                                                                      *)
  (* THE ONLY WRITE PERMITS LEFT, and that is the point.  The earlier      *)
  (* at-forms exposed the header READING only, which is all a caller needs *)
  (* in order to keep writing -- and exactly what a DEPOSIT could not use  *)
  (* (row (b) needs the post-commit picture's VALUE, and the at-form left  *)
  (* it existential).  Here the caller hands its half at a NAMED [M0] and  *)
  (* gets it back at a closed term, so a committer carries a picture of    *)
  (* the whole durable disk across the fills, the commit, the installs and *)
  (* the clear -- and so does a BOOT, since durable-disk 1a gives the era  *)
  (* custody at birth and the recovering install runs these same permits.  *)
  (*                                                                      *)
  (* The one thing the at-forms never had to name is the HALF-WRITTEN      *)
  (* block: a torn landing moves the picture at the block it lands in and  *)
  (* a value receipt has to say to what.  [blk_sec0] / [blk_sec1] are      *)
  (* those two rows, [lm_upd_sec_01] / [lm_upd_sec_10] are why one receipt *)
  (* still serves both landing orders, and the length side condition the   *)
  (* second composition needs travels INSIDE the first landing's receipt   *)
  (* (the picture agrees with the disk on the extent, so its rows are      *)
  (* [BSIZE] long) rather than as a premise nobody upstream could give.    *)
  (* ==================================================================== *)

  (* ---- (7a) ONE LANDING, at a named picture.  The caller's pure
     obligation is its row of the §3 table; what is new is that the receipt
     is the half at a TERM. ---- *)
  Lemma fs_v_sector0_rec `{GEN : GenId} (cov : gset Z) (ls : Z) (blk : Z)
      (bs : list (bv 8)) (M0 : log_mirror) :
    length bs = BSIZE ->
    blk ∈ cov ∪ log_region_set ls ->
    (forall (r : fs_rec) (dk : Z -> bv 8),
       log_mirror_ok M0 (fs_blocks dk) cov ls ->
       fs_rec_wf r (fs_blocks dk) cov ls ->
       fs_rec_wf r (fs_blocks (disk_write dk
          (blk * Z.of_nat BSIZE + Z.of_nat 0)%Z (take virtio_sector_bytes bs)))
          cov ls) ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    ▷ log_mirror_half M0 -∗
    fs_rec_permit cov ls gen_id
      (Some ((blk * Z.of_nat BSIZE + Z.of_nat 0)%Z, take virtio_sector_bytes bs))
      (log_mirror_half (lm_upd M0 blk (blk_sec0 (lm_view M0 blk) bs))
       ∗ ⌜length (lm_view M0 blk) = BSIZE⌝).
  Proof.
    intros Hlen Hext Hwf. iIntros "#Hreg #Hswlb Hmir".
    assert (Hfit : (0 + length (take virtio_sector_bytes bs) <= BSIZE)%nat)
      by (rewrite (sector0_len bs Hlen) bsize_two_sectors; lia).
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    cbn [wr_apply fst snd].
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwfr & Harm & Hdur)".
    rewrite /log_mirror_half. iMod "Hmir".
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    pose proof (Hok blk Hext) as Hrow.
    assert (Hlold : length (lm_view M0 blk) = BSIZE)
      by (rewrite Hrow; apply fs_blocks_length).
    assert (Hnew : fs_blocks (disk_write dk
                     (blk * Z.of_nat BSIZE + Z.of_nat 0)%Z
                     (take virtio_sector_bytes bs)) blk
                   = blk_sec0 (lm_view M0 blk) bs)
      by (rewrite Hrow; exact (fs_blocks_blk_sec0 dk blk bs Hlen)).
    iMod ("Hclose" $! (disk_write dk (blk * Z.of_nat BSIZE + Z.of_nat 0)%Z
                        (take virtio_sector_bytes bs))
            (lm_upd M0 blk (blk_sec0 (lm_view M0 blk) bs)) with "[%]")
      as "[Harm Hmir]".
    { rewrite -Hnew.
      exact (log_mirror_ok_upd_sector M0 dk cov ls blk 0
               (take virtio_sector_bytes bs) Hfit Hok). }
    iModIntro.
    iSplitL "Hhist Harm Hdur".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists r. iFrame "Hhist".
      (* [P_wf]'s side is at [fr_D r], which this write does not move *)
      iSplitR; [| iFrame "Hdur"; iExact "Harm"].
      iPureIntro. exact (Hwf r dk Hok Hwfr). }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    iSplitL "Hmir"; [rewrite /log_mirror_half; iExact "Hmir"|].
    iPureIntro. exact Hlold.
  Qed.

  Lemma fs_v_sector1_rec `{GEN : GenId} (cov : gset Z) (ls : Z) (blk : Z)
      (bs : list (bv 8)) (M0 : log_mirror) :
    length bs = BSIZE ->
    blk ∈ cov ∪ log_region_set ls ->
    (forall (r : fs_rec) (dk : Z -> bv 8),
       log_mirror_ok M0 (fs_blocks dk) cov ls ->
       fs_rec_wf r (fs_blocks dk) cov ls ->
       fs_rec_wf r (fs_blocks (disk_write dk
          (blk * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z
          (take virtio_sector_bytes (drop virtio_sector_bytes bs)))) cov ls) ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    ▷ log_mirror_half M0 -∗
    fs_rec_permit cov ls gen_id
      (Some ((blk * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z,
             take virtio_sector_bytes (drop virtio_sector_bytes bs)))
      (log_mirror_half (lm_upd M0 blk (blk_sec1 (lm_view M0 blk) bs))
       ∗ ⌜length (lm_view M0 blk) = BSIZE⌝).
  Proof.
    intros Hlen Hext Hwf. iIntros "#Hreg #Hswlb Hmir".
    assert (Hfit : (virtio_sector_bytes
                    + length (take virtio_sector_bytes
                                (drop virtio_sector_bytes bs)) <= BSIZE)%nat)
      by (rewrite (sector1_len bs Hlen) bsize_two_sectors; lia).
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    cbn [wr_apply fst snd].
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwfr & Harm & Hdur)".
    rewrite /log_mirror_half. iMod "Hmir".
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    pose proof (Hok blk Hext) as Hrow.
    assert (Hlold : length (lm_view M0 blk) = BSIZE)
      by (rewrite Hrow; apply fs_blocks_length).
    assert (Hnew : fs_blocks (disk_write dk
                     (blk * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z
                     (take virtio_sector_bytes (drop virtio_sector_bytes bs))) blk
                   = blk_sec1 (lm_view M0 blk) bs)
      by (rewrite Hrow; exact (fs_blocks_blk_sec1 dk blk bs Hlen)).
    iMod ("Hclose" $! (disk_write dk
                        (blk * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z
                        (take virtio_sector_bytes (drop virtio_sector_bytes bs)))
            (lm_upd M0 blk (blk_sec1 (lm_view M0 blk) bs)) with "[%]")
      as "[Harm Hmir]".
    { rewrite -Hnew.
      exact (log_mirror_ok_upd_sector M0 dk cov ls blk virtio_sector_bytes
               (take virtio_sector_bytes (drop virtio_sector_bytes bs)) Hfit Hok). }
    iModIntro.
    iSplitL "Hhist Harm Hdur".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists r. iFrame "Hhist".
      (* [P_wf]'s side is at [fr_D r], which this write does not move *)
      iSplitR; [| iFrame "Hdur"; iExact "Harm"].
      iPureIntro. exact (Hwf r dk Hok Hwfr). }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    iSplitL "Hmir"; [rewrite /log_mirror_half; iExact "Hmir"|].
    iPureIntro. exact Hlold.
  Qed.

  (* ---- (7b) THE COMMIT POINT, AT THE LOGGED VIEW (durable-disk 1b).
     The new committed view is a TERM the caller can read -- and the term is
     [L] on the home set, NOT install arithmetic: the install is the log's
     own business and stays inside this lemma ([fs_install_is_logged]).
     THERE IS NO CLIENT PURE PREMISE.  What used to be [fs_commit_pres] --
     "the state this write jumps to is still a well-formed file system",
     quantified over a picture no caller of end_op could name -- is gone;
     what replaces it is the log's own two rows, both of which the committer
     proves for itself:

       [Htie]  row (b) at the commit ([LogInv.log_mirror_tie_body], read
               through [Hoff] at the caller's off-header view [V]), and
       [Hslot] the entries' slot contents, i.e. the copy loop's ghost step
               composed with the chained slot picture.

     The premises about the picture are stated at [V], the caller's
     OFF-HEADER view, because both landing orders reach this shift and only
     one of them has already moved the header row: a statement mentioning
     [lm_view M0] at the header could not serve both branches with ONE
     receipt. ---- *)
  Lemma fs_commit_L_sector0_rec `{GEN : GenId} (cov : gset Z) (ls : Z)
      (M0 : log_mirror) (V : Z -> list (bv 8)) (L : gmap Z (list (bv 8)))
      (nn : nat) (Ws : list Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_dec bs = (nn, Ws) ->
    (nn <= LOGBLOCKS)%nat ->
    NoDup Ws ->
    (forall b : Z, b ∈ Ws -> b ∈ cov /\ b ∉ log_region_set ls) ->
    (* AND THE BLOCK 1 CLAUSE (durable-disk lane E-blk1).  The only permit
       that writes a NONZERO header is the one that has to carry [hdr_wf]'s
       new clause, and the committer discharges it off [LogInv.log_state]'s
       write-set row ([ProofEndOp.eo_hdr_ne_sb]) -- the same row the era
       keeps true at every [log_write]. *)
    (forall b : Z, b ∈ Ws -> b <> FsImg.SB_BNO) ->
    lm_hdr M0 ls = (0%nat, []) ->
    (forall b : Z, b <> log_hdr_bno ls -> lm_view M0 b = V b) ->
    (* ROW (b) at the commit *)
    (forall b : Z, b ∈ fs_home_set cov ls -> b ∉ Ws -> L !! b = Some (V b)) ->
    (* the batch's own entries: home block = its slot's logged content *)
    (forall (i : nat) (b : Z), Ws !! i = Some b ->
       L !! b = Some (V (log_slot_bno ls i))) ->
    (* THE SNAPSHOT'S PREMISE (lane CE, plan section 3's "Commit").  The one
       thing the new durable instance needs, and the ONLY new premise the
       commit takes: the view this write jumps to IS a file system.  It is
       PURE, it is what [LogSnapLaw.snap_law] concludes at the quiescent
       era, and the committer reads it off [LogInv.log_ctx_snap_law_of_ops]
       BEFORE it releases the log lock -- which is where the transaction
       authority the law needs lives.  Nothing resource-shaped crosses. *)
    (exists S' : fs_state_rec,
       snap_ok S' (fs_restrict (dv_of_D L) (fs_home_set cov ls))) ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    ▷ log_mirror_half M0 -∗
    fs_rec_permit cov ls gen_id
      (Some ((log_hdr_bno ls * Z.of_nat BSIZE + Z.of_nat 0)%Z,
             take virtio_sector_bytes bs))
      (log_mirror_half (lm_upd M0 (log_hdr_bno ls)
          (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs))
       ∗ fs_receipt_any (fs_restrict (dv_of_D L) (fs_home_set cov ls))
       ∗ ⌜length (lm_view M0 (log_hdr_bno ls)) = BSIZE⌝).
  Proof.
    intros Hlen Hdec Hnn Hnd Hin Hinsb HM0 Hoff Htie Hslot [Sn Hsnap].
    iIntros "#Hreg #Hswlb Hmir".
    assert (Hbound : ((hdr_dec bs).1 <= LOGBLOCKS)%nat) by (rewrite Hdec /=; lia).
    assert (Hfit : (0 + length (take virtio_sector_bytes bs) <= BSIZE)%nat)
      by (rewrite (sector0_len bs Hlen) bsize_two_sectors; lia).
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    cbn [wr_apply fst snd].
    set (dk' := disk_write dk (log_hdr_bno ls * Z.of_nat BSIZE + Z.of_nat 0)%Z
                  (take virtio_sector_bytes bs)).
    assert (Hdec' : hdr_dec (fs_blocks dk' (log_hdr_bno ls)) = (nn, Ws))
      by (unfold dk'; rewrite (hdr_dec_blk_sector0 dk ls bs Hlen Hbound); exact Hdec).
    assert (Hmiss : forall c, c <> log_hdr_bno ls -> fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc;
          exact (fs_blocks_sub_ne dk _ c 0 (take virtio_sector_bytes bs) Hfit Hc)).
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm & Hdur)".
    rewrite /log_mirror_half. iMod "Hmir".
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    pose proof (Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)) as Hrow.
    assert (Hlold : length (lm_view M0 (log_hdr_bno ls)) = BSIZE)
      by (rewrite Hrow; apply fs_blocks_length).
    assert (Hnew : fs_blocks dk' (log_hdr_bno ls)
                   = blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs)
      by (unfold dk'; rewrite Hrow;
          exact (fs_blocks_blk_sec0 dk (log_hdr_bno ls) bs Hlen)).
    (* the disk, the picture and [V] are ONE map off the header block *)
    assert (Hres : fs_restrict (fs_blocks dk) (fs_home_set cov ls)
                   = fs_restrict V (fs_home_set cov ls)).
    { apply fs_restrict_ext. intros b Hb.
      rewrite -(Hok b (fs_home_in_ext cov ls b Hb)).
      apply Hoff. exact (home_set_ne_hdr cov ls b Hb). }
    (* THE COMMITTED VIEW, BY NAME: the logged view on the home set.  The
       install arithmetic is discharged here and never leaves this file. *)
    assert (Hlogd : fs_install V ls Ws (fs_restrict V (fs_home_set cov ls))
                    = fs_restrict (dv_of_D L) (fs_home_set cov ls)).
    { apply (fs_install_is_logged V L cov ls Ws Hnd);
        [ intros b Hb; rewrite /fs_home_set;
          apply elem_of_difference; exact (Hin b Hb)
        | exact Htie | exact Hslot ]. }
    set (D' := fs_restrict (dv_of_D L) (fs_home_set cov ls)).
    assert (HD' : fs_install (fs_blocks dk) ls
                    (hdr_dec (fs_blocks dk' (log_hdr_bno ls))).2
                    (fs_restrict (fs_blocks dk) (fs_home_set cov ls)) = D').
    { rewrite Hdec' /= Hres /D' -Hlogd. apply fs_install_ext_P. intros j Hj.
      assert (Hjlt : (j < LOGBLOCKS)%nat).
      { pose proof (hdr_dec_length bs) as Hl. rewrite Hdec /= in Hl. lia. }
      rewrite -(Hok (log_slot_bno ls j) (log_slot_in_ext cov ls j Hjlt)).
      apply Hoff. apply log_slot_ne_hdr. }
    destruct Hwf as (Hrec & Hlast & Hhwf).
    assert (Hdk0 : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (0%nat, []))
      by (rewrite -Hrow; exact HM0).
    assert (Hn0 : hdr_n (fs_blocks dk (log_hdr_bno ls)) = 0)
      by (rewrite -hdr_dec_n Hdk0 //).
    assert (HfrD : fr_D r = fs_restrict V (fs_home_set cov ls))
      by (rewrite -Hres; exact (proj1 (fs_recovery_clean _ _ _ _ Hn0) Hrec)).
    (* ---- THE SNAPSHOT STEPS.  This is the one write kind that moves the
       committed view, so it is the one place the durable instance moves:
       the old copy is DROPPED (affine) and a fresh one allocated at [D'] --
       a [D'] the caller can NAME (it is [L] on the home set, computed just
       above).  The allocator runs INSIDE the permit, under this basic
       update, off the caller's pure tie alone; nothing resource-shaped is
       asked of anybody, which is why the refutation of plan section 8
       (deposited client fupds that MOVE durable resources) does not bite.
       [D'] is [fs_restrict (dv_of_D L) (fs_home_set cov ls)], exactly the
       map the premise is stated at. ---- *)
    iMod (dsnap_step_of Sn (fr_D r) D' Hsnap with "Hdur") as "Hdur".
    iMod (fs_hist_update (fcn_hist γs) (fr_hist r) (fr_hist r ++ [D'])
            with "Hhist") as "Hhist"; [by eexists|].
    iDestruct (fs_hist_snapshot with "Hhist") as "[Hhist #Hlb]".
    iMod ("Hclose" $! dk'
            (lm_upd M0 (log_hdr_bno ls)
               (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs)) with "[%]")
      as "[Harm Hmir]".
    { rewrite -Hnew. unfold dk'.
      exact (log_mirror_ok_upd_sector M0 dk cov ls (log_hdr_bno ls) 0
               (take virtio_sector_bytes bs) Hfit Hok). }
    iModIntro.
    iSplitL "Hhist Harm Hdur".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists (MkFsRec D' (fr_hist r ++ [D'])).
      iFrame "Hhist". iSplitR; [| iFrame "Hdur"; iExact "Harm"].
      iPureIntro. rewrite /fs_rec_wf /=. split_and!.
      - rewrite -HD'.
        exact (fs_recovery_commit (fs_blocks dk) (fs_blocks dk') cov ls
                 (fs_blocks dk' (log_hdr_bno ls)) eq_refl Hmiss).
      - rewrite last_snoc. reflexivity.
      - rewrite /hdr_wf Hdec' /=.
        split_and!; [exact Hnn | exact Hnd |].
        intros b Hb. destruct (Hin b Hb) as [Hbc Hbl].
        split_and!; [exact Hbc | exact Hbl | exact (Hinsb b Hb)].
      }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    iSplitL "Hmir"; [rewrite /log_mirror_half; iExact "Hmir"|].
    iSplitR "".
    { rewrite /fs_receipt_any. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /fs_receipt. iExists (fr_hist r). iExact "Hlb". }
    iPureIntro. exact Hlold.
  Qed.

  (* ---- (7c) THE PRESERVING CLEAR's FIRST SECTOR (stage E3, at a named
     picture).  [fr_D] does NOT move: the caught-up premise -- "the home
     block already holds what its log slot holds", stated at the caller's
     off-header view [V] -- is pure COMPUTATION on the chained value after
     the install pass, and it is exactly [fs_recovery_clear_keeps]'s missing
     home-side picture. ---- *)
  Lemma fs_clear_v_sector0_rec `{GEN : GenId} (cov : gset Z) (ls : Z)
      (M0 : log_mirror) (V : Z -> list (bv 8))
      (nn : nat) (Ws : list Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_n bs = 0 ->
    lm_hdr M0 ls = (nn, Ws) ->
    (forall b : Z, b <> log_hdr_bno ls -> lm_view M0 b = V b) ->
    (forall (j : nat) (b : Z), Ws !! j = Some b -> V b = V (log_slot_bno ls j)) ->
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    ▷ log_mirror_half M0 -∗
    fs_rec_permit cov ls gen_id
      (Some ((log_hdr_bno ls * Z.of_nat BSIZE + Z.of_nat 0)%Z,
             take virtio_sector_bytes bs))
      (log_mirror_half (lm_upd M0 (log_hdr_bno ls)
          (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs))
       ∗ ⌜length (lm_view M0 (log_hdr_bno ls)) = BSIZE⌝).
  Proof.
    intros Hlen Hn0 HM0 Hoff Hcaught. iIntros "#Hreg #Hswlb Hmir".
    assert (Hz : hdr_dec bs = (0%nat, [])) by exact (hdr_dec_zero bs Hn0).
    assert (Hbound : ((hdr_dec bs).1 <= LOGBLOCKS)%nat) by (rewrite Hz /=; lia).
    assert (Hfit : (0 + length (take virtio_sector_bytes bs) <= BSIZE)%nat)
      by (rewrite (sector0_len bs Hlen) bsize_two_sectors; lia).
    rewrite /fs_rec_permit. iIntros (dk n) "Hsa %Hn1 HP".
    cbn [wr_apply fst snd].
    set (dk' := disk_write dk (log_hdr_bno ls * Z.of_nat BSIZE + Z.of_nat 0)%Z
                  (take virtio_sector_bytes bs)).
    assert (Hdec' : hdr_dec (fs_blocks dk' (log_hdr_bno ls)) = (0%nat, []))
      by (unfold dk'; rewrite (hdr_dec_blk_sector0 dk ls bs Hlen Hbound); exact Hz).
    assert (Hn0' : hdr_n (fs_blocks dk' (log_hdr_bno ls)) = 0)
      by (rewrite -hdr_dec_n Hdec' //).
    assert (Hmiss : forall c, c <> log_hdr_bno ls -> fs_blocks dk' c = fs_blocks dk c)
      by (intros c Hc;
          exact (fs_blocks_sub_ne dk _ c 0 (take virtio_sector_bytes bs) Hfit Hc)).
    iMod "HP". rewrite /P_fs_rec /P_fs_rec_named.
    iDestruct "HP" as (γs) "[%Hseq HPfs]".
    destruct Hseq as (Hsw & Hrg & Hstn).
    rewrite {1}/P_fs. iDestruct "HPfs" as (r) "(Hhist & %Hwf & Harm & Hdur)".
    rewrite /log_mirror_half. iMod "Hmir".
    iAssert (fs_era_reg γs gen_id riscv_eraGS) as "#Hreg2".
    { rewrite /fs_era_reg Hrg. iExact "Hreg". }
    iAssert (mono_nat_lb_own (fcn_swap γs) (S gen_id)) as "#Hswlb2".
    { rewrite Hsw. iExact "Hswlb". }
    iAssert (mono_nat_auth_own (fcn_start γs) 1 n) with "[Hsa]" as "Hsa".
    { rewrite Hstn. iExact "Hsa". }
    iDestruct (fs_arm_acc γs cov ls dk gen_id riscv_eraGS n M0 Hn1
                 with "Hreg2 Hswlb2 Hsa Hmir Harm") as "(%Hok & Hsa & Hclose)".
    pose proof (Hok (log_hdr_bno ls) (log_hdr_in_ext cov ls)) as Hrow.
    assert (Hlold : length (lm_view M0 (log_hdr_bno ls)) = BSIZE)
      by (rewrite Hrow; apply fs_blocks_length).
    assert (Hnew : fs_blocks dk' (log_hdr_bno ls)
                   = blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs)
      by (unfold dk'; rewrite Hrow;
          exact (fs_blocks_blk_sec0 dk (log_hdr_bno ls) bs Hlen)).
    destruct Hwf as (Hrec & Hlast & Hhwf).
    pose proof Hhwf as (Hbnd & Hndw & Hhome).
    assert (Hdkh : hdr_dec (fs_blocks dk (log_hdr_bno ls)) = (nn, Ws))
      by (rewrite -Hrow; exact HM0).
    iMod ("Hclose" $! dk'
            (lm_upd M0 (log_hdr_bno ls)
               (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs)) with "[%]")
      as "[Harm Hmir]".
    { rewrite -Hnew. unfold dk'.
      exact (log_mirror_ok_upd_sector M0 dk cov ls (log_hdr_bno ls) 0
               (take virtio_sector_bytes bs) Hfit Hok). }
    iModIntro.
    iSplitL "Hhist Harm Hdur".
    { iNext. rewrite /P_fs_rec /P_fs_rec_named. iExists γs.
      iSplitR; [iPureIntro; done|].
      rewrite /P_fs. iExists r. iFrame "Hhist".
      (* [P_wf]'s side is at [fr_D r]: the preserving clear does not move it *)
      iSplitR; [| iFrame "Hdur"; iExact "Harm"].
      iPureIntro. rewrite /fs_rec_wf /=. split_and!.
      - refine (fs_recovery_clear_keeps (fs_blocks dk) (fs_blocks dk')
                  (fr_D r) cov ls (fs_blocks dk' (log_hdr_bno ls))
                  eq_refl Hn0' Hmiss _ _ Hrec).
        { exact Hndw. }
        intros j b Hjb. rewrite Hdkh /= in Hjb.
        assert (Hbc : b ∈ cov /\ b ∉ log_region_set ls /\ b <> FsImg.SB_BNO).
        { apply Hhome. rewrite Hdkh /=.
          exact (elem_of_list_lookup_2 _ _ _ Hjb). }
        assert (Hbhome : b ∈ fs_home_set cov ls)
          by (rewrite /fs_home_set elem_of_difference; tauto).
        apply fs_restrict_lookup_Some. split; [exact Hbhome|].
        assert (Hjlt : (j < LOGBLOCKS)%nat).
        { apply lookup_lt_Some in Hjb.
          pose proof (hdr_dec_length (fs_blocks dk (log_hdr_bno ls))) as Hl.
          rewrite Hdkh /= in Hl Hbnd. lia. }
        rewrite -(Hok b (fs_home_in_ext cov ls b Hbhome)).
        rewrite -(Hok (log_slot_bno ls j) (log_slot_in_ext cov ls j Hjlt)).
        rewrite (Hoff b (home_set_ne_hdr cov ls b Hbhome)).
        rewrite (Hoff (log_slot_bno ls j) (log_slot_ne_hdr ls j)).
        symmetry. exact (Hcaught j b Hjb).
      - exact Hlast.
      - apply hdr_wf_zero. exact Hn0'.
      }
    iSplitL "Hsa"; [rewrite /start_auth -Hstn; iExact "Hsa"|].
    iSplitL "Hmir"; [rewrite /log_mirror_half; iExact "Hmir"|].
    iPureIntro. exact Hlold.
  Qed.

  (* ---- (7d) LOG FILL, sequentially and by value. ---- *)
  Lemma fs_logfill_v_seq_permit `{GEN : GenId} (cov : gset Z) (ls : Z) (i : nat)
      (M0 : log_mirror) (bs : list (bv 8)) :
    length bs = BSIZE ->
    (i < LOGBLOCKS)%nat ->
    lm_hdr M0 ls = (0%nat, []) ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_half M0 -∗
    disk_seq_permit gen_id (Some ((1024 * log_slot_bno ls i)%Z, bs))
      (log_mirror_half (lm_upd M0 (log_slot_bno ls i) bs)).
  Proof.
    intros Hlen Hi HM0. iIntros "#Hseam #Hreg #Hswlb Hmir".
    assert (Hne : log_slot_bno ls i <> log_hdr_bno ls) by apply log_slot_ne_hdr.
    assert (Hext : log_slot_bno ls i ∈ cov ∪ log_region_set ls)
      by exact (log_slot_in_ext cov ls i Hi).
    assert (Hf0 : (0 + length (take virtio_sector_bytes bs) <= BSIZE)%nat)
      by (rewrite (sector0_len bs Hlen) bsize_two_sectors; lia).
    assert (Hf1 : (virtio_sector_bytes
                   + length (take virtio_sector_bytes (drop virtio_sector_bytes bs))
                   <= BSIZE)%nat)
      by (rewrite (sector1_len bs Hlen) bsize_two_sectors; lia).
    assert (Hwf0 : forall (M : log_mirror), lm_hdr M ls = (0%nat, []) ->
              forall (r : fs_rec) (dk : Z -> bv 8),
                log_mirror_ok M (fs_blocks dk) cov ls ->
                fs_rec_wf r (fs_blocks dk) cov ls ->
                fs_rec_wf r (fs_blocks (disk_write dk
                   (log_slot_bno ls i * Z.of_nat BSIZE + Z.of_nat 0)%Z
                   (take virtio_sector_bytes bs))) cov ls)
      by (intros M HM r dk Hok Hwfr;
          exact (fs_rec_wf_logfill_sector cov ls i M 0 _ r dk Hi Hf0 HM Hok Hwfr)).
    assert (Hwf1 : forall (M : log_mirror), lm_hdr M ls = (0%nat, []) ->
              forall (r : fs_rec) (dk : Z -> bv 8),
                log_mirror_ok M (fs_blocks dk) cov ls ->
                fs_rec_wf r (fs_blocks dk) cov ls ->
                fs_rec_wf r (fs_blocks (disk_write dk
                   (log_slot_bno ls i * Z.of_nat BSIZE
                    + Z.of_nat virtio_sector_bytes)%Z
                   (take virtio_sector_bytes (drop virtio_sector_bytes bs))))
                   cov ls)
      by (intros M HM r dk Hok Hwfr;
          exact (fs_rec_wf_logfill_sector cov ls i M virtio_sector_bytes _ r dk
                   Hi Hf1 HM Hok Hwfr)).
    assert (HMs0 : lm_hdr (lm_upd M0 (log_slot_bno ls i)
                     (blk_sec0 (lm_view M0 (log_slot_bno ls i)) bs)) ls
                   = (0%nat, []))
      by (rewrite (lm_hdr_upd_ne M0 ls (log_slot_bno ls i) _ Hne); exact HM0).
    assert (HMs1 : lm_hdr (lm_upd M0 (log_slot_bno ls i)
                     (blk_sec1 (lm_view M0 (log_slot_bno ls i)) bs)) ls
                   = (0%nat, []))
      by (rewrite (lm_hdr_upd_ne M0 ls (log_slot_bno ls i) _ Hne); exact HM0).
    iApply (disk_seq_permit_two gen_id _ _ (wr_nsectors_block _ bs Hlen)).
    rewrite (wr_sector_blk0 (log_slot_bno ls i) bs)
            (wr_sector_blk1 (log_slot_bno ls i) bs).
    iSplit.
    - (* SECTOR 0 FIRST *)
      iApply (fs_permit_of_rec with "Hseam").
      iApply (fs_rec_permit_mono cov ls gen_id _
                (log_mirror_half (lm_upd M0 (log_slot_bno ls i)
                    (blk_sec0 (lm_view M0 (log_slot_bno ls i)) bs))
                 ∗ ⌜length (lm_view M0 (log_slot_bno ls i)) = BSIZE⌝)%I _
                with "[] [Hmir]").
      { iIntros "[Hm _]".
        iApply (fs_permit_of_rec with "Hseam").
        iApply (fs_rec_permit_mono cov ls gen_id _
                  (log_mirror_half (lm_upd
                      (lm_upd M0 (log_slot_bno ls i)
                         (blk_sec0 (lm_view M0 (log_slot_bno ls i)) bs))
                      (log_slot_bno ls i)
                      (blk_sec1 (lm_view (lm_upd M0 (log_slot_bno ls i)
                         (blk_sec0 (lm_view M0 (log_slot_bno ls i)) bs))
                         (log_slot_bno ls i)) bs))
                   ∗ ⌜length (lm_view (lm_upd M0 (log_slot_bno ls i)
                        (blk_sec0 (lm_view M0 (log_slot_bno ls i)) bs))
                        (log_slot_bno ls i)) = BSIZE⌝)%I _
                  with "[] [Hm]").
        { iIntros "[Hm2 _]". iApply disk_write_permit_intro.
          rewrite -(lm_upd_sec_01 M0 (log_slot_bno ls i) bs Hlen).
          iExact "Hm2". }
        iApply (fs_v_sector1_rec cov ls (log_slot_bno ls i) bs _ Hlen Hext
                  (Hwf1 _ HMs0)
                  with "Hreg Hswlb [Hm]").
        iNext. iExact "Hm". }
      iApply (fs_v_sector0_rec cov ls (log_slot_bno ls i) bs M0 Hlen Hext
                (Hwf0 M0 HM0) with "Hreg Hswlb [Hmir]").
      iNext. iExact "Hmir".
    - (* SECTOR 1 FIRST *)
      iApply (fs_permit_of_rec with "Hseam").
      iApply (fs_rec_permit_mono cov ls gen_id _
                (log_mirror_half (lm_upd M0 (log_slot_bno ls i)
                    (blk_sec1 (lm_view M0 (log_slot_bno ls i)) bs))
                 ∗ ⌜length (lm_view M0 (log_slot_bno ls i)) = BSIZE⌝)%I _
                with "[] [Hmir]").
      { iIntros "[Hm %Hlold]".
        iApply (fs_permit_of_rec with "Hseam").
        iApply (fs_rec_permit_mono cov ls gen_id _
                  (log_mirror_half (lm_upd
                      (lm_upd M0 (log_slot_bno ls i)
                         (blk_sec1 (lm_view M0 (log_slot_bno ls i)) bs))
                      (log_slot_bno ls i)
                      (blk_sec0 (lm_view (lm_upd M0 (log_slot_bno ls i)
                         (blk_sec1 (lm_view M0 (log_slot_bno ls i)) bs))
                         (log_slot_bno ls i)) bs))
                   ∗ ⌜length (lm_view (lm_upd M0 (log_slot_bno ls i)
                        (blk_sec1 (lm_view M0 (log_slot_bno ls i)) bs))
                        (log_slot_bno ls i)) = BSIZE⌝)%I _
                  with "[] [Hm]").
        { iIntros "[Hm2 _]". iApply disk_write_permit_intro.
          rewrite -(lm_upd_sec_10 M0 (log_slot_bno ls i) bs Hlold).
          iExact "Hm2". }
        iApply (fs_v_sector0_rec cov ls (log_slot_bno ls i) bs _ Hlen Hext
                  (Hwf0 _ HMs1)
                  with "Hreg Hswlb [Hm]").
        iNext. iExact "Hm". }
      iApply (fs_v_sector1_rec cov ls (log_slot_bno ls i) bs M0 Hlen Hext
                (Hwf1 M0 HM0) with "Hreg Hswlb [Hmir]").
      iNext. iExact "Hmir".
  Qed.

  (* ---- (7e) INSTALL, sequentially and by value. ---- *)
  Lemma fs_install_v_seq_permit `{GEN : GenId} (cov : gset Z) (ls : Z)
      (nn : nat) (Ws : list Z) (i : nat) (b : Z) (M0 : log_mirror)
      (bs : list (bv 8)) :
    length bs = BSIZE ->
    NoDup Ws ->
    (length Ws <= LOGBLOCKS)%nat ->
    Ws !! i = Some b ->
    b ∈ cov ->
    b ∉ log_region_set ls ->
    lm_hdr M0 ls = (nn, Ws) ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    ▷ log_mirror_half M0 -∗
    disk_seq_permit gen_id (Some ((1024 * b)%Z, bs))
      (log_mirror_half (lm_upd M0 b bs)).
  Proof.
    intros Hlen Hnd Hwlen Hi Hbc Hb HM0. iIntros "#Hseam #Hreg #Hswlb Hmir".
    assert (Hne : b <> log_hdr_bno ls) by by apply home_ne_hdr.
    assert (Hext : b ∈ cov ∪ log_region_set ls)
      by (apply elem_of_union; by left).
    assert (Hf0 : (0 + length (take virtio_sector_bytes bs) <= BSIZE)%nat)
      by (rewrite (sector0_len bs Hlen) bsize_two_sectors; lia).
    assert (Hf1 : (virtio_sector_bytes
                   + length (take virtio_sector_bytes (drop virtio_sector_bytes bs))
                   <= BSIZE)%nat)
      by (rewrite (sector1_len bs Hlen) bsize_two_sectors; lia).
    assert (Hwf0 : forall (M : log_mirror), lm_hdr M ls = (nn, Ws) ->
              forall (r : fs_rec) (dk : Z -> bv 8),
                log_mirror_ok M (fs_blocks dk) cov ls ->
                fs_rec_wf r (fs_blocks dk) cov ls ->
                fs_rec_wf r (fs_blocks (disk_write dk
                   (b * Z.of_nat BSIZE + Z.of_nat 0)%Z
                   (take virtio_sector_bytes bs))) cov ls)
      by (intros M HM r dk Hok Hwfr;
          exact (fs_rec_wf_install_sector cov ls nn Ws i b M 0 _ r dk
                   Hnd Hwlen Hi Hb Hf0 HM Hok Hwfr)).
    assert (Hwf1 : forall (M : log_mirror), lm_hdr M ls = (nn, Ws) ->
              forall (r : fs_rec) (dk : Z -> bv 8),
                log_mirror_ok M (fs_blocks dk) cov ls ->
                fs_rec_wf r (fs_blocks dk) cov ls ->
                fs_rec_wf r (fs_blocks (disk_write dk
                   (b * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z
                   (take virtio_sector_bytes (drop virtio_sector_bytes bs))))
                   cov ls)
      by (intros M HM r dk Hok Hwfr;
          exact (fs_rec_wf_install_sector cov ls nn Ws i b M virtio_sector_bytes
                   _ r dk Hnd Hwlen Hi Hb Hf1 HM Hok Hwfr)).
    assert (HMs0 : lm_hdr (lm_upd M0 b (blk_sec0 (lm_view M0 b) bs)) ls
                   = (nn, Ws))
      by (rewrite (lm_hdr_upd_ne M0 ls b _ Hne); exact HM0).
    assert (HMs1 : lm_hdr (lm_upd M0 b (blk_sec1 (lm_view M0 b) bs)) ls
                   = (nn, Ws))
      by (rewrite (lm_hdr_upd_ne M0 ls b _ Hne); exact HM0).
    iApply (disk_seq_permit_two gen_id _ _ (wr_nsectors_block _ bs Hlen)).
    rewrite (wr_sector_blk0 b bs) (wr_sector_blk1 b bs).
    iSplit.
    - (* SECTOR 0 FIRST *)
      iApply (fs_permit_of_rec with "Hseam").
      iApply (fs_rec_permit_mono cov ls gen_id _
                (log_mirror_half (lm_upd M0 b (blk_sec0 (lm_view M0 b) bs))
                 ∗ ⌜length (lm_view M0 b) = BSIZE⌝)%I _ with "[] [Hmir]").
      { iIntros "[Hm _]".
        iApply (fs_permit_of_rec with "Hseam").
        iApply (fs_rec_permit_mono cov ls gen_id _
                  (log_mirror_half (lm_upd
                      (lm_upd M0 b (blk_sec0 (lm_view M0 b) bs)) b
                      (blk_sec1 (lm_view (lm_upd M0 b
                         (blk_sec0 (lm_view M0 b) bs)) b) bs))
                   ∗ ⌜length (lm_view (lm_upd M0 b
                        (blk_sec0 (lm_view M0 b) bs)) b) = BSIZE⌝)%I _
                  with "[] [Hm]").
        { iIntros "[Hm2 _]". iApply disk_write_permit_intro.
          rewrite -(lm_upd_sec_01 M0 b bs Hlen). iExact "Hm2". }
        iApply (fs_v_sector1_rec cov ls b bs _ Hlen Hext
                  (Hwf1 _ HMs0)
                  with "Hreg Hswlb [Hm]").
        iNext. iExact "Hm". }
      iApply (fs_v_sector0_rec cov ls b bs M0 Hlen Hext (Hwf0 M0 HM0)
                with "Hreg Hswlb Hmir").
    - (* SECTOR 1 FIRST *)
      iApply (fs_permit_of_rec with "Hseam").
      iApply (fs_rec_permit_mono cov ls gen_id _
                (log_mirror_half (lm_upd M0 b (blk_sec1 (lm_view M0 b) bs))
                 ∗ ⌜length (lm_view M0 b) = BSIZE⌝)%I _ with "[] [Hmir]").
      { iIntros "[Hm %Hlold]".
        iApply (fs_permit_of_rec with "Hseam").
        iApply (fs_rec_permit_mono cov ls gen_id _
                  (log_mirror_half (lm_upd
                      (lm_upd M0 b (blk_sec1 (lm_view M0 b) bs)) b
                      (blk_sec0 (lm_view (lm_upd M0 b
                         (blk_sec1 (lm_view M0 b) bs)) b) bs))
                   ∗ ⌜length (lm_view (lm_upd M0 b
                        (blk_sec1 (lm_view M0 b) bs)) b) = BSIZE⌝)%I _
                  with "[] [Hm]").
        { iIntros "[Hm2 _]". iApply disk_write_permit_intro.
          rewrite -(lm_upd_sec_10 M0 b bs Hlold). iExact "Hm2". }
        iApply (fs_v_sector0_rec cov ls b bs _ Hlen Hext
                  (Hwf0 _ HMs1)
                  with "Hreg Hswlb [Hm]").
        iNext. iExact "Hm". }
      iApply (fs_v_sector1_rec cov ls b bs M0 Hlen Hext (Hwf1 M0 HM0)
                with "Hreg Hswlb Hmir").
  Qed.

  (* ---- (7f) THE LOG'S COMMIT CONTRACT, sequentially and by value
     (durable-disk 1b).  THE POINT OF THE WHOLE campaign, and it takes NO
     client premise: the pre-image's log is clean per the caller's picture,
     so the invariant's [fr_D] IS the home restriction of [V], and the
     post-image's is the LOGGED VIEW [L] on the home set.  The write set,
     the slot contents and the install pass are the log's own arithmetic and
     do not appear in the conclusion -- what the client sees is
     [D' = L|home], which is what its debt is stated against. ---- *)
  Lemma fs_commit_L_seq_permit `{GEN : GenId} (cov : gset Z) (ls : Z)
      (M0 : log_mirror) (V : Z -> list (bv 8)) (L : gmap Z (list (bv 8)))
      (nn : nat) (Ws : list Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_dec bs = (nn, Ws) ->
    (nn <= LOGBLOCKS)%nat ->
    NoDup Ws ->
    (forall b : Z, b ∈ Ws -> b ∈ cov /\ b ∉ log_region_set ls) ->
    (* AND THE BLOCK 1 CLAUSE (durable-disk lane E-blk1).  The only permit
       that writes a NONZERO header is the one that has to carry [hdr_wf]'s
       new clause, and the committer discharges it off [LogInv.log_state]'s
       write-set row ([ProofEndOp.eo_hdr_ne_sb]) -- the same row the era
       keeps true at every [log_write]. *)
    (forall b : Z, b ∈ Ws -> b <> FsImg.SB_BNO) ->
    lm_hdr M0 ls = (0%nat, []) ->
    (forall b : Z, b <> log_hdr_bno ls -> lm_view M0 b = V b) ->
    (* ROW (b) at the commit ([LogInv.log_mirror_tie_body], through [Hoff]) *)
    (forall b : Z, b ∈ fs_home_set cov ls -> b ∉ Ws -> L !! b = Some (V b)) ->
    (* the batch's own entries: home block = its slot's logged content *)
    (forall (i : nat) (b : Z), Ws !! i = Some b ->
       L !! b = Some (V (log_slot_bno ls i))) ->
    (* THE SNAPSHOT'S PREMISE (lane CE): the view this commit jumps to IS a
       file system.  PURE, and the committer reads it off
       [LogInv.log_ctx_snap_law_of_ops] while it still holds the log lock;
       see [fs_commit_L_sector0_rec]. *)
    (exists S' : fs_state_rec,
       snap_ok S' (fs_restrict (dv_of_D L) (fs_home_set cov ls))) ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_half M0 -∗
    disk_seq_permit gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_half (lm_upd M0 (log_hdr_bno ls) bs)
       ∗ fs_receipt_any (fs_restrict (dv_of_D L) (fs_home_set cov ls))).
  Proof.
    intros Hlen Hdec Hnn Hnd Hin Hinsb HM0 Hoff Hrow Hslot Hsnap.
    iIntros "#Hseam #Hreg #Hswlb Hmir".
    assert (Hext : log_hdr_bno ls ∈ cov ∪ log_region_set ls)
      by exact (log_hdr_in_ext cov ls).
    assert (Hwfh : forall (M : log_mirror) (r : fs_rec) (dk : Z -> bv 8),
              log_mirror_ok M (fs_blocks dk) cov ls ->
              fs_rec_wf r (fs_blocks dk) cov ls ->
              fs_rec_wf r (fs_blocks (disk_write dk
                 (log_hdr_bno ls * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z
                 (take virtio_sector_bytes (drop virtio_sector_bytes bs)))) cov ls)
      by (intros M r dk _ Hwfr;
          exact (fs_rec_wf_hdr_sector1 cov ls _ r dk (sector1_len bs Hlen) Hwfr)).
    iApply (disk_seq_permit_two gen_id _ _ (wr_nsectors_block _ bs Hlen)).
    rewrite (wr_sector_blk0 (log_hdr_bno ls) bs)
            (wr_sector_blk1 (log_hdr_bno ls) bs).
    iSplit.
    - (* SECTOR 0 FIRST: the commit, then a landing recovery cannot see *)
      iApply (fs_permit_of_rec with "Hseam").
      iApply (fs_rec_permit_mono cov ls gen_id _
                (log_mirror_half (lm_upd M0 (log_hdr_bno ls)
                    (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs))
                 ∗ fs_receipt_any
                     (fs_restrict (dv_of_D L) (fs_home_set cov ls))
                 ∗ ⌜length (lm_view M0 (log_hdr_bno ls)) = BSIZE⌝)%I _
                with "[] [Hmir]").
      { iIntros "(Hm & #Hrc & _)".
        iApply (fs_permit_of_rec with "Hseam").
        iApply (fs_rec_permit_mono cov ls gen_id _
                  (log_mirror_half (lm_upd
                      (lm_upd M0 (log_hdr_bno ls)
                         (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs))
                      (log_hdr_bno ls)
                      (blk_sec1 (lm_view (lm_upd M0 (log_hdr_bno ls)
                         (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs))
                         (log_hdr_bno ls)) bs))
                   ∗ ⌜length (lm_view (lm_upd M0 (log_hdr_bno ls)
                        (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs))
                        (log_hdr_bno ls)) = BSIZE⌝)%I _
                  with "[] [Hm]").
        { iIntros "[Hm2 _]". iApply disk_write_permit_intro.
          iSplitL "Hm2".
          { rewrite -(lm_upd_sec_01 M0 (log_hdr_bno ls) bs Hlen). iExact "Hm2". }
          iExact "Hrc". }
        iApply (fs_v_sector1_rec cov ls (log_hdr_bno ls) bs _ Hlen Hext
                  (Hwfh _) with "Hreg Hswlb [Hm]").
        iNext. iExact "Hm". }
      iApply (fs_commit_L_sector0_rec cov ls M0 V L nn Ws bs Hlen Hdec Hnn Hnd
                Hin Hinsb HM0 Hoff Hrow Hslot Hsnap with "Hreg Hswlb [Hmir]").
      iNext. iExact "Hmir".
    - (* SECTOR 1 FIRST: nothing recovery reads moves, and THEN the commit *)
      iApply (fs_permit_of_rec with "Hseam").
      iApply (fs_rec_permit_mono cov ls gen_id _
                (log_mirror_half (lm_upd M0 (log_hdr_bno ls)
                    (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs))
                 ∗ ⌜length (lm_view M0 (log_hdr_bno ls)) = BSIZE⌝)%I _
                with "[] [Hmir]").
      { iIntros "[Hm %Hlold]".
        assert (HM1 : lm_hdr (lm_upd M0 (log_hdr_bno ls)
                        (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs)) ls
                      = (0%nat, [])).
        { rewrite (lm_hdr_upd_hdr_sec1 M0 ls bs); [exact HM0 | | ].
          - rewrite HM0 /=. unfold LOGBLOCKS. lia.
          - rewrite Hlold bsize_two_sectors. lia. }
        assert (HoffM1 : forall c : Z, c <> log_hdr_bno ls ->
                  lm_view (lm_upd M0 (log_hdr_bno ls)
                     (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs)) c = V c).
        { intros c Hc.
          rewrite (lm_upd_view_ne M0 (log_hdr_bno ls) c _ Hc). exact (Hoff c Hc). }
        iApply (fs_permit_of_rec with "Hseam").
        iApply (fs_rec_permit_mono cov ls gen_id _
                  (log_mirror_half (lm_upd
                      (lm_upd M0 (log_hdr_bno ls)
                         (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs))
                      (log_hdr_bno ls)
                      (blk_sec0 (lm_view (lm_upd M0 (log_hdr_bno ls)
                         (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs))
                         (log_hdr_bno ls)) bs))
                   ∗ fs_receipt_any
                       (fs_restrict (dv_of_D L) (fs_home_set cov ls))
                   ∗ ⌜length (lm_view (lm_upd M0 (log_hdr_bno ls)
                        (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs))
                        (log_hdr_bno ls)) = BSIZE⌝)%I _
                  with "[] [Hm]").
        { iIntros "(Hm2 & Hrc & _)". iApply disk_write_permit_intro.
          iSplitL "Hm2".
          { rewrite -(lm_upd_sec_10 M0 (log_hdr_bno ls) bs Hlold). iExact "Hm2". }
          iExact "Hrc". }
        iApply (fs_commit_L_sector0_rec cov ls _ V L nn Ws bs Hlen Hdec Hnn Hnd
                  Hin Hinsb HM1 HoffM1 Hrow Hslot Hsnap with "Hreg Hswlb [Hm]").
        iNext. iExact "Hm". }
      iApply (fs_v_sector1_rec cov ls (log_hdr_bno ls) bs M0 Hlen Hext
                (Hwfh M0) with "Hreg Hswlb [Hmir]").
      iNext. iExact "Hmir".
  Qed.

  (* ---- (7g) THE PRESERVING CLEAR, sequentially and by value (stage E3).
     [fr_D] does not move at all, so the steady state stops re-basing: the
     caught-up premise is COMPUTATION on the value the install chain left. ---- *)
  Lemma fs_clear_keep_seq_permit `{GEN : GenId} (cov : gset Z) (ls : Z)
      (M0 : log_mirror) (V : Z -> list (bv 8))
      (nn : nat) (Ws : list Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    hdr_n bs = 0 ->
    (nn <= LOGBLOCKS)%nat ->
    lm_hdr M0 ls = (nn, Ws) ->
    (forall b : Z, b <> log_hdr_bno ls -> lm_view M0 b = V b) ->
    (forall (j : nat) (b : Z), Ws !! j = Some b -> V b = V (log_slot_bno ls j)) ->
    fs_crash_seam cov ls -∗
    era_registered gen_id riscv_eraGS -∗
    swap_lb (S gen_id) -∗
    log_mirror_half M0 -∗
    disk_seq_permit gen_id (Some ((1024 * log_hdr_bno ls)%Z, bs))
      (log_mirror_half (lm_upd M0 (log_hdr_bno ls) bs)).
  Proof.
    intros Hlen Hn0 Hnn HM0 Hoff Hcaught. iIntros "#Hseam #Hreg #Hswlb Hmir".
    assert (Hext : log_hdr_bno ls ∈ cov ∪ log_region_set ls)
      by exact (log_hdr_in_ext cov ls).
    assert (Hwfh : forall (M : log_mirror) (r : fs_rec) (dk : Z -> bv 8),
              log_mirror_ok M (fs_blocks dk) cov ls ->
              fs_rec_wf r (fs_blocks dk) cov ls ->
              fs_rec_wf r (fs_blocks (disk_write dk
                 (log_hdr_bno ls * Z.of_nat BSIZE + Z.of_nat virtio_sector_bytes)%Z
                 (take virtio_sector_bytes (drop virtio_sector_bytes bs)))) cov ls)
      by (intros M r dk _ Hwfr;
          exact (fs_rec_wf_hdr_sector1 cov ls _ r dk (sector1_len bs Hlen) Hwfr)).
    iApply (disk_seq_permit_two gen_id _ _ (wr_nsectors_block _ bs Hlen)).
    rewrite (wr_sector_blk0 (log_hdr_bno ls) bs)
            (wr_sector_blk1 (log_hdr_bno ls) bs).
    iSplit.
    - (* SECTOR 0 FIRST *)
      iApply (fs_permit_of_rec with "Hseam").
      iApply (fs_rec_permit_mono cov ls gen_id _
                (log_mirror_half (lm_upd M0 (log_hdr_bno ls)
                    (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs))
                 ∗ ⌜length (lm_view M0 (log_hdr_bno ls)) = BSIZE⌝)%I _
                with "[] [Hmir]").
      { iIntros "[Hm _]".
        iApply (fs_permit_of_rec with "Hseam").
        iApply (fs_rec_permit_mono cov ls gen_id _
                  (log_mirror_half (lm_upd
                      (lm_upd M0 (log_hdr_bno ls)
                         (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs))
                      (log_hdr_bno ls)
                      (blk_sec1 (lm_view (lm_upd M0 (log_hdr_bno ls)
                         (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs))
                         (log_hdr_bno ls)) bs))
                   ∗ ⌜length (lm_view (lm_upd M0 (log_hdr_bno ls)
                        (blk_sec0 (lm_view M0 (log_hdr_bno ls)) bs))
                        (log_hdr_bno ls)) = BSIZE⌝)%I _
                  with "[] [Hm]").
        { iIntros "[Hm2 _]". iApply disk_write_permit_intro.
          rewrite -(lm_upd_sec_01 M0 (log_hdr_bno ls) bs Hlen). iExact "Hm2". }
        iApply (fs_v_sector1_rec cov ls (log_hdr_bno ls) bs _ Hlen Hext
                  (Hwfh _) with "Hreg Hswlb [Hm]").
        iNext. iExact "Hm". }
      iApply (fs_clear_v_sector0_rec cov ls M0 V nn Ws bs Hlen Hn0 HM0 Hoff
                Hcaught with "Hreg Hswlb [Hmir]").
      iNext. iExact "Hmir".
    - (* SECTOR 1 FIRST *)
      iApply (fs_permit_of_rec with "Hseam").
      iApply (fs_rec_permit_mono cov ls gen_id _
                (log_mirror_half (lm_upd M0 (log_hdr_bno ls)
                    (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs))
                 ∗ ⌜length (lm_view M0 (log_hdr_bno ls)) = BSIZE⌝)%I _
                with "[] [Hmir]").
      { iIntros "[Hm %Hlold]".
        assert (HM1 : lm_hdr (lm_upd M0 (log_hdr_bno ls)
                        (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs)) ls
                      = (nn, Ws)).
        { rewrite (lm_hdr_upd_hdr_sec1 M0 ls bs); [exact HM0 | | ].
          - rewrite HM0 /=. exact Hnn.
          - rewrite Hlold bsize_two_sectors. lia. }
        assert (HoffM1 : forall c : Z, c <> log_hdr_bno ls ->
                  lm_view (lm_upd M0 (log_hdr_bno ls)
                     (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs)) c = V c).
        { intros c Hc.
          rewrite (lm_upd_view_ne M0 (log_hdr_bno ls) c _ Hc). exact (Hoff c Hc). }
        iApply (fs_permit_of_rec with "Hseam").
        iApply (fs_rec_permit_mono cov ls gen_id _
                  (log_mirror_half (lm_upd
                      (lm_upd M0 (log_hdr_bno ls)
                         (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs))
                      (log_hdr_bno ls)
                      (blk_sec0 (lm_view (lm_upd M0 (log_hdr_bno ls)
                         (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs))
                         (log_hdr_bno ls)) bs))
                   ∗ ⌜length (lm_view (lm_upd M0 (log_hdr_bno ls)
                        (blk_sec1 (lm_view M0 (log_hdr_bno ls)) bs))
                        (log_hdr_bno ls)) = BSIZE⌝)%I _
                  with "[] [Hm]").
        { iIntros "[Hm2 _]". iApply disk_write_permit_intro.
          rewrite -(lm_upd_sec_10 M0 (log_hdr_bno ls) bs Hlold). iExact "Hm2". }
        iApply (fs_clear_v_sector0_rec cov ls _ V nn Ws bs Hlen Hn0 HM1 HoffM1
                  Hcaught with "Hreg Hswlb [Hm]").
        iNext. iExact "Hm". }
      iApply (fs_v_sector1_rec cov ls (log_hdr_bno ls) bs M0 Hlen Hext
                (Hwfh M0) with "Hreg Hswlb [Hmir]").
      iNext. iExact "Hmir".
  Qed.
End fs_crash_seam.
