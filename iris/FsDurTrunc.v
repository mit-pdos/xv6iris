(* FsDurTrunc.v -- THE REFUTATION OF THE PER-WRITE ACCUMULATION OF THE
   USED-SET COUPLING.

   claude-notes/design/durable-fs-plan.md section 4(a) says of the byte half
   [FsDurSnap.snap_bytes] -- the tie the log's parked payload was to
   accumulate at every [log_write] -- that

       "This half is true EVEN MID-OPERATION, which is why it -- and not
        [snap_ok] -- is what a batch accumulates per write."

   IT IS NOT.  The USED-SET COUPLING ([FsDurSnap]'s [sk_own_used] /
   [sk_disj], the design's one sanctioned whole-map pure clause) is FALSE at
   every one of [itrunc]'s 269 [bfree] calls, and the falsity is xv6's, not
   the proof's.  This file states and proves that, at exactly the shape of
   the payload obligation lane B was to discharge at [ProofBfree]'s
   [log_write] (the supplier list of plan section 6).

   ---------------------------------------------------------------------
   THE CODE (SpecItrunc.v's own transcription):

       void itrunc(struct inode *ip) {
         for (i = 0; i < NDIRECT; i++)
           if (ip->addrs[i]) { bfree(ip->dev, ip->addrs[i]);
                               ip->addrs[i] = 0; }
         ...
         ip->size = 0;
         iupdate(ip);                          <-- the ONLY record write
       }

   [ip->addrs[i] = 0] is an IN-MEMORY store.  The inode's 64-byte record
   reaches the logged view exactly once, at the tail [iupdate].  So between
   the first [bfree] and that [iupdate] -- 269 [log_write]s of the bitmap
   block, plus whatever other transactions the batch interleaves -- the
   LOGGED BYTES hold a record that still names blocks whose bitmap bit has
   just been cleared.

   [snap_bytes S D] reads its state OFF THOSE BYTES: [sk_rec] pins
   [fn_rec n] to the record in the region block, [inode_repr]'s
   [inr_blk_dom] then FORCES [is_Some (fn_blk n !! k)] for every nonzero
   direct address, hence [fn_owns n b], and [sk_own_used] demands
   [b ∈ fss_used S] while [sk_bmap] reads [fss_used S] straight out of the
   bitmap block -- where the bit is now clear.  The two cannot both hold:
   [bfree_used_coupling_refuted] below.

   THE SAME WINDOW REFUTES [sk_disj] (not formalised here, for want of a
   second write to model): the block [itrunc] freed is immediately
   allocatable, so another process's [balloc] may hand it to a second inode
   and write THAT inode's record in the same batch, at which point two of
   [S]'s nodes name one block.  xv6 is not wrong -- a batch is committed
   atomically and [itrunc]'s [iupdate] is inside it, so no COMMITTED state
   is ever inconsistent -- but a per-write accumulation sees the window.

   ---------------------------------------------------------------------
   WHY IT CANNOT BE PATCHED INSIDE THE PAYLOAD, in the four directions that
   look available:

   - Weaken [sk_bmap] to an inclusion.  The ADOPT case
     ([FsDurSnap.snap_untouched_of_free], the whole reason the coupling was
     added) needs "owned ⊆ set bits"; [bfree] needs "set bits ⊆ owned" to
     fail.  They are the two directions of the same containment.
   - Drop [sk_own_used]/[sk_disj].  Then [snap_untouched_of_free] is gone
     and no writer can adopt: "the bit I read was clear" stops implying
     "no inode names this block", and nothing else pure does.
   - Exempt the inodes whose on-disk record is stale.  The exemption set is
     the LOCKED registry (lane A) -- a ghost value.  A pure payload cannot
     name it, and a payload that could would be back to holding the abstract
     map's authority, which [InodeRegion.ftop_inv] must keep (lane A parks
     the locked registry beside it).
   - Retag the stale node inside the writer's step.  Works for a data
     block, fails for an indirect one: re-reading the overwritten block as
     an entry array yields arbitrary addresses, and [inr_blk_dom] then
     demands [D] be defined at them.

   So the coupling has to be maintained somewhere that KNOWS which inodes
   are mid-operation, i.e. in the file system's own invariant beside the
   locked registry (plan section 4(b)'s home), not in the log's payload.
   That is a design decision above this lane.

   ---------------------------------------------------------------------
   TWO FURTHER GAPS in the payload premise as it stands
   ([SpecLogWrite.wp_log_write_au_range]'s
    [∀ D0 Dc, Psi D0 Dc ==∗ Psi D0 (<[uint bno := bs]> Dc)]), found while
   sizing the nine suppliers.  Neither is refuted here; both are recorded so
   the next attempt prices them:

   (G1) THE GEOMETRY IS NOT NAMEABLE AT A SUPPLIER.  [Dc] is universally
        quantified, so a supplier cannot read [Dc !! SB_BNO] and cannot pin
        [fss_sb S].  Without [fss_sb S = <its own superblock>] the bitmap
        writer's step is not even about the bitmap: for the payload's [S],
        [bmapstart] may be an inode-region block.  The clause has to go INTO
        the payload -- and then the payload mentions the superblock, which
        lives in [FsCfg.fs_cfg], far above [LogInv].
   (G2) THE PAYLOAD IS NOT NAMEABLE AT A SUPPLIER.  Every supplier reaches
        the payload by [iDestruct "Hlctx" as (Psi) "#Hlctxa"] -- [LogInv.log_ctx]
        is the existential closure of [log_ctx_at], which is what keeps
        [log_ctx]'s arity off ~75 files.  So a supplier can only move [Psi]
        through a LAW carried by [log_ctx_at], and that law has to state the
        concrete pure fact.  Three ways out, all with a price:
          (a) [LogInv] names the concrete predicate -- needs the superblock
              (G1) at [LogInv]'s layer;
          (b) [log_ctx_at] gains an [fs_sb] argument, [log_ctx] closes it,
              and each supplier PINS it against a persistent witness (the
              four superblock cells) -- new interface, but no arity change;
          (c) every file-system contract carries [log_ctx_at Psi_c] -- the
              ~75-file sweep the worklist's sizing notes forbid.
   (G3) A RECORD WRITER ALSO NEEDS ONE FACT ABOUT [Dc]: to identify [S]'s
        node at its inum with its own it must run [FsDurSnap.rec_in_blk_inj]
        off [sk_rec], which needs [Dc !! (inodestart + i/16) = Some bsl] --
        its own OLD block bytes.  [log_write] can supply that as one extra
        pure premise (it holds the byte authority at the ghost step and
        agrees the caller's [fsblock] against it); the premise as written
        does not.

   ---------------------------------------------------------------------
   NON-VACUITY.  The hypotheses of [bfree_used_coupling_refuted] are
   [bfree]'s OWN preconditions plus the payload's own content: a state the
   byte half admits, xv6's superblock shape ([FsImg.fs_sb_ok], which
   [FsImg.fs_sb_wf] decides on the tracked image), a live inum, and a
   nonzero direct address inside the file system's size.  Nothing is hedged
   and nothing is quantified away: the tracked image's root directory alone
   supplies the inum and the address ([FsDurImg.img_root_entries] reads its
   first data block), so the first [bfree] of any [itrunc] on a nonempty
   file is an instance.  What is NOT machine-checked here is
   [snap_bytes S_img D_img] for the tracked image -- that witness is what
   the image lane (plan section 5 / worklist lane C) owes; until it exists no
   file in the tree can exhibit a closed [snap_bytes]. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
(* for ssreflect's [rewrite /x] and [//] -- [Import] is not transitive, so
   reaching [proofmode] through [FsDurSnap] does NOT enable them *)
From iris.proofmode Require Import proofmode.
Require Import BioDefs.
Require Import BitmapEnc.
Require Import DinodeEnc.
Require Import FsImg.
Require Import FsDurSnap.

Local Open Scope Z_scope.

(* [bm_bytes n u] is a 1024-element list behind a transparent [Definition],
   so a unification that has to decide [bm_bytes BSIZE A =?= bm_bytes BSIZE B]
   delta-unfolds both and does not come back (durable-notes.md: a big-op over
   a literal-sized list is a reduct, not a value; [FsDurSnap]'s
   [snap_bytes_used_agree] meets the [injection] form of the same trap).
   Nothing below needs the body. *)
Local Opaque bm_bytes.

(* ===================================================================== *)
(*  1.  THE BITMAP BLOCK IS NEITHER THE SUPERBLOCK NOR A REGION BLOCK     *)
(*                                                                        *)
(*  The two disequalities the frame below needs, both off xv6's own        *)
(*  superblock shape.  They are stated separately because they are also    *)
(*  exactly what a bitmap writer would have to know about the PAYLOAD's    *)
(*  superblock, which is gap (G1) in the header.                          *)
(* ===================================================================== *)

Lemma sb_bmapstart_ne_SB_BNO (sb : fs_sb) :
  fs_sb_ok sb -> sb_bmapstart sb <> SB_BNO.
Proof.
  intros Hok. destruct (fs_sb_ok_meta sb Hok) as (H2 & Hlt & _).
  unfold fs_data_start in Hlt. unfold SB_BNO. lia.
Qed.

Lemma sb_bmapstart_ne_region (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < sb_ninodes sb ->
  sb_inodestart sb + i `div` 16 <> sb_bmapstart sb.
Proof.
  intros Hok Hi.
  pose proof (sbo_bmapstart sb Hok) as Hbm.
  assert (Hdiv : i `div` 16 <= sb_ninodes sb `div` 16)
    by (apply Z.div_le_mono; lia).
  lia.
Qed.

Lemma sb_region_ne_SB_BNO (sb : fs_sb) (q : Z) :
  fs_sb_ok sb -> 0 <= q -> sb_inodestart sb + q <> SB_BNO.
Proof.
  intros Hok Hq. destruct (fs_sb_ok_meta sb Hok) as (H2 & _ & _).
  unfold SB_BNO. lia.
Qed.

(* ===================================================================== *)
(*  2.  THE SUPERBLOCK AND THE NODE RIDE A WRITE THAT MISSES THEM         *)
(*                                                                        *)
(*  Two transports, both instances of the same step -- the write did not   *)
(*  touch the block this clause reads.  They turn the refutation from a    *)
(*  fact about ONE state into a fact about EVERY state the byte half       *)
(*  admits at the written map -- which is the form the payload's           *)
(*  existential needs.                                                     *)
(* ===================================================================== *)

Lemma snap_bytes_sb_transport (S S' : fs_state_rec)
    (D : gmap Z (list (bv 8))) (c : Z) (cs : list (bv 8)) :
  snap_bytes S D -> snap_bytes S' (<[c := cs]> D) -> c <> SB_BNO ->
  fss_sb S' = fss_sb S.
Proof.
  intros Hok Hok' Hc.
  assert (Hb : fss_sbb S' = fss_sbb S).
  { pose proof (sk_sb Hok') as Hs.
    rewrite lookup_insert_ne in Hs; [| exact Hc].
    rewrite (sk_sb Hok) in Hs. by injection Hs as <-. }
  pose proof (sk_parse Hok') as Hp. rewrite Hb in Hp.
  rewrite (sk_parse Hok) in Hp. by injection Hp as <-.
Qed.

(* THE NODE.  Every state the byte half admits at the written map reads the
   SAME record at [i]'s slot, because the write did not touch that slot's
   block -- so the stale record [itrunc] has not yet flushed is the record
   the payload's own existential is forced to name. *)
Lemma snap_bytes_rec_transport (S S' : fs_state_rec)
    (D : gmap Z (list (bv 8))) (c : Z) (cs : list (bv 8))
    (i : Z) (n n' : fs_node) :
  snap_bytes S D -> snap_bytes S' (<[c := cs]> D) ->
  fss_sb S' = fss_sb S ->
  c <> sb_inodestart (fss_sb S) + i `div` 16 ->
  fss_inodes S !! i = Some n -> fss_inodes S' !! i = Some n' ->
  fn_rec n' = fn_rec n.
Proof.
  intros Hok Hok' Hsb Hc Hi Hi'.
  destruct (sk_rec Hok i n Hi) as (bs & Hbs & Hin).
  destruct (sk_rec Hok' i n' Hi') as (bs' & Hbs' & Hin').
  rewrite Hsb in Hbs'.
  rewrite lookup_insert_ne in Hbs'; [| exact Hc].
  rewrite Hbs in Hbs'. injection Hbs' as <-.
  exact (rec_in_blk_inj bs _ (fn_rec n') (fn_rec n)
           (inr_rec_wf (sk_repr Hok' i n' Hi'))
           (inr_rec_wf (sk_repr Hok i n Hi)) Hin' Hin).
Qed.

(* A DIRECT slot's address is a reading of the RECORD alone, so it rides
   the record transport above. *)
Lemma fn_naddr_direct (n n' : fs_node) (k : nat) :
  (k < FS_NDIRECT)%nat -> fn_rec n' = fn_rec n ->
  fn_naddr n' k = fn_naddr n k.
Proof.
  intros Hk Hr. rewrite /fn_naddr.
  destruct (decide (k < FS_NDIRECT)%nat) as [_ | Hno]; [rewrite Hr // | lia].
Qed.

(* ===================================================================== *)
(*  3.  THE REFUTATION                                                    *)
(*                                                                        *)
(*  [bfree]'s [log_write] writes the bitmap block with one bit CLEARED.    *)
(*  The payload obligation it was to discharge is                          *)
(*                                                                        *)
(*     (exists S, snap_bytes S Dc) -> exists S', snap_bytes S' Dc'         *)
(*                                                                        *)
(*  at [Dc' = <[bmapstart := bm_bytes BSIZE (used ∖ {[b]})]> Dc].  The      *)
(*  antecedent holds -- [S] is the witness -- and the consequent is FALSE  *)
(*  whenever the freed block is still named by a record the batch has not  *)
(*  flushed, which is [itrunc]'s state at every one of its frees.          *)
(* ===================================================================== *)

Theorem bfree_used_coupling_refuted
    (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i b : Z) (n : fs_node) (k : nat) :
  (* the payload's own content, at the batch's current logged view *)
  snap_bytes S D ->
  (* xv6's superblock shape -- [FsImg.fs_sb_wf] decides it on the image *)
  fs_sb_ok (fss_sb S) ->
  (* a live inum: the inode [itrunc] is emptying *)
  0 <= i < sb_ninodes (fss_sb S) ->
  fss_inodes S !! i = Some n ->
  (* ...whose record still names [b] at a DIRECT slot, because [itrunc]
     zeroes [ip->addrs[k]] in memory and flushes only at its tail iupdate *)
  (k < FS_NDIRECT)%nat -> fn_naddr n k = b -> b <> 0 ->
  (* [b] is a data block of this file system -- bfree's own precondition *)
  0 <= b < sb_size (fss_sb S) ->
  (* THE OBLIGATION [ProofBfree]'s log_write would have to discharge *)
  ~ (exists S' : fs_state_rec,
       snap_bytes S'
         (<[sb_bmapstart (fss_sb S)
            := bm_bytes BSIZE (fss_used S ∖ {[b]})]> D)).
Proof.
  intros Hok Hsb Hirange Hi Hk Hnaddr Hb0 Hbrange (S' & Hok').
  (* FIRST, while the context is small: [set_solver] here would meet
     [bm_bytes]'s 1024-element body through the list equations the proof
     grows below, and not come back.  Stated by hand for the same reason. *)
  assert (Hnot : b ∉ fss_used S ∖ {[b]}).
  { intros Hcon. apply elem_of_difference in Hcon as [_ Hne].
    apply Hne. by apply elem_of_singleton. }
  (* the write misses the superblock and misses [i]'s region block *)
  assert (Hne1 : sb_bmapstart (fss_sb S) <> SB_BNO)
    by exact (sb_bmapstart_ne_SB_BNO _ Hsb).
  assert (Hne2 : sb_bmapstart (fss_sb S)
                 <> sb_inodestart (fss_sb S) + i `div` 16)
    by (intros Heq; exact (sb_bmapstart_ne_region _ i Hsb Hirange
                             (eq_sym Heq))).
  (* ...so both states parse the same superblock *)
  assert (Hsbe : fss_sb S' = fss_sb S)
    by exact (snap_bytes_sb_transport S S' D _ _ Hok Hok' Hne1).
  (* ...and [S'] names [i] as well.  The range fact is named rather than
     spliced: an inline [ltac:] in an argument position whose expected type
     is still an evar is elaborated before the conclusion is unified
     (durable-notes.md). *)
  assert (Hirange' : 0 <= i < sb_ninodes (fss_sb S'))
    by (rewrite Hsbe; exact Hirange).
  destruct (sk_dom Hok' i Hirange') as [n' Hi'].
  (* ...at the SAME, still-stale, record *)
  assert (Hrec : fn_rec n' = fn_rec n)
    by exact (snap_bytes_rec_transport S S' D _ _ i n n'
                Hok Hok' Hsbe Hne2 Hi Hi').
  (* hence [S'] is forced to say the freed block is still owned *)
  assert (Hna : fn_naddr n' k = b)
    by (rewrite (fn_naddr_direct n n' k Hk Hrec); exact Hnaddr).
  assert (HkM : (k < FS_MAXFILE)%nat)
    by (rewrite /FS_NDIRECT in Hk; rewrite /FS_MAXFILE; lia).
  assert (Hsome : is_Some (fn_blk n' !! k)).
  { apply (proj2 (inr_blk_dom (sk_repr Hok' i n' Hi') k HkM)).
    rewrite Hna. exact Hb0. }
  assert (Howns : fn_owns n' b)
    by (left; exists k; split; [exact Hsome | exact Hna]).
  pose proof (proj1 (sk_own_used Hok' i n' b Hi' Howns)) as Hin.
  (* ...while the block it just wrote says the bit is CLEAR *)
  assert (Hbb : bm_bytes BSIZE (fss_used S ∖ {[b]})
                = bm_bytes BSIZE (fss_used S')).
  { pose proof (sk_bmap Hok') as Hb2.
    rewrite Hsbe lookup_insert in Hb2. exact (inj Some _ _ Hb2). }
  assert (Hlt : 0 <= b < 8 * Z.of_nat BSIZE).
  { rewrite BSIZE_z_nat.
    pose proof (sbo_one_bitmap _ Hsb). lia. }
  pose proof (fs_bit_bm_bytes BSIZE (fss_used S ∖ {[b]}) b Hlt) as E.
  pose proof (fs_bit_bm_bytes BSIZE (fss_used S') b Hlt) as E'.
  rewrite Hbb in E. rewrite E' in E.
  (* [b ∉ used ∖ {[b]}] and [b ∈ fss_used S'] cannot both be read off one
     block.  The two [Decision]s are spelled out: [bool_decide_eq_true_2] on
     a goal that is not itself a [bool_decide] leaves the instance an evar
     (durable-notes.md). *)
  rewrite (@bool_decide_eq_false_2 (b ∈ fss_used S ∖ {[b]}) _ Hnot) in E.
  rewrite (@bool_decide_eq_true_2 (b ∈ fss_used S') _ Hin) in E.
  discriminate.
Qed.

(* ===================================================================== *)
(*  4.  THE SAME WINDOW REFUTES [sk_disj], AT A RECORD WRITER             *)
(*                                                                        *)
(*  The block [itrunc] freed is allocatable the instant its bit is clear,  *)
(*  so [balloc] may hand it to a second inode and that inode's [iupdate]   *)
(*  writes a record naming it -- while [itrunc]'s own record, unflushed,   *)
(*  still names it too.  Then no state the byte half admits can satisfy    *)
(*  [sk_disj], and the obligation the RECORD writers ([ProofIupdate],      *)
(*  [ProofIalloc], [ProofIput]) would have to discharge has no witness     *)
(*  either.  Independent of the bitmap: [balloc] has set the bit back, so  *)
(*  section 3's contradiction is not the one at work here.                 *)
(*                                                                        *)
(*  The two inodes are taken in DIFFERENT region blocks, which is what     *)
(*  makes the write miss the stale record; that is the case xv6 produces   *)
(*  whenever the truncating and the allocating inums are 16 apart or more, *)
(*  and it is the only one this statement needs.                          *)
(* ===================================================================== *)

Theorem record_write_disj_refuted
    (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i j b : Z) (n : fs_node) (k k' : nat)
    (dn' : dinode) (bs' : list (bv 8)) :
  snap_bytes S D ->
  fs_sb_ok (fss_sb S) ->
  (* the inode [itrunc] is emptying, with its record still naming [b] *)
  0 <= i < sb_ninodes (fss_sb S) ->
  fss_inodes S !! i = Some n ->
  (k < FS_NDIRECT)%nat -> fn_naddr n k = b -> b <> 0 ->
  (* ...and the inode that adopted [b], in another region block *)
  0 <= j < sb_ninodes (fss_sb S) ->
  i <> j -> i `div` 16 <> j `div` 16 ->
  (* the record the adopter is about to flush: well formed, naming [b] *)
  dinode_wf dn' ->
  rec_in_blk bs' (64 * (j `mod` 16)) dn' ->
  (k' < FS_NDIRECT)%nat ->
  bv_unsigned (di_addrs dn' !!! k') = b ->
  (* THE OBLIGATION the record write would have to discharge *)
  ~ (exists S'' : fs_state_rec,
       snap_bytes S''
         (<[sb_inodestart (fss_sb S) + j `div` 16 := bs']> D)).
Proof.
  intros Hok Hsb Hi0 Hi Hk Hnaddr Hb0 Hj0 Hij Hblk Hwf' Hrin' Hk' Haddr'
         (S'' & Hok').
  assert (Hq : 0 <= j `div` 16) by (apply Z.div_pos; lia).
  assert (Hne1 : sb_inodestart (fss_sb S) + j `div` 16 <> SB_BNO)
    by exact (sb_region_ne_SB_BNO _ _ Hsb Hq).
  assert (Hsbe : fss_sb S'' = fss_sb S)
    by exact (snap_bytes_sb_transport S S'' D _ _ Hok Hok' Hne1).
  assert (Hirange' : 0 <= i < sb_ninodes (fss_sb S''))
    by (rewrite Hsbe; exact Hi0).
  assert (Hjrange' : 0 <= j < sb_ninodes (fss_sb S''))
    by (rewrite Hsbe; exact Hj0).
  destruct (sk_dom Hok' i Hirange') as [ni Hni].
  destruct (sk_dom Hok' j Hjrange') as [nj Hnj].
  (* the STALE record survives: the write is in another region block *)
  assert (Hne2 : sb_inodestart (fss_sb S) + j `div` 16
                 <> sb_inodestart (fss_sb S) + i `div` 16) by lia.
  assert (Hreci : fn_rec ni = fn_rec n)
    by exact (snap_bytes_rec_transport S S'' D _ _ i n ni
                Hok Hok' Hsbe Hne2 Hi Hni).
  assert (HkM : (k < FS_MAXFILE)%nat)
    by (rewrite /FS_NDIRECT in Hk; rewrite /FS_MAXFILE; lia).
  assert (Hnai : fn_naddr ni k = b)
    by (rewrite (fn_naddr_direct n ni k Hk Hreci); exact Hnaddr).
  assert (Hsomei : is_Some (fn_blk ni !! k)).
  { apply (proj2 (inr_blk_dom (sk_repr Hok' i ni Hni) k HkM)).
    rewrite Hnai. exact Hb0. }
  assert (Howni : fn_owns ni b)
    by (left; exists k; split; [exact Hsomei | exact Hnai]).
  (* ...and the ADOPTER's freshly written record names [b] as well *)
  assert (Hrecj : fn_rec nj = dn').
  { destruct (sk_rec Hok' j nj Hnj) as (bsj & Hbsj & Hinj).
    rewrite Hsbe lookup_insert in Hbsj.
    (* [<-] would leave the direction of the substitution to Coq; name the
       equation and eliminate the destructed variable explicitly *)
    injection Hbsj as Hbe. subst bsj.
    exact (rec_in_blk_inj bs' _ (fn_rec nj) dn'
             (inr_rec_wf (sk_repr Hok' j nj Hnj)) Hwf' Hinj Hrin'). }
  assert (HkM' : (k' < FS_MAXFILE)%nat)
    by (rewrite /FS_NDIRECT in Hk'; rewrite /FS_MAXFILE; lia).
  assert (Hnaj : fn_naddr nj k' = b).
  { rewrite /fn_naddr.
    destruct (decide (k' < FS_NDIRECT)%nat) as [_ | Hno]; [| lia].
    rewrite Hrecj. exact Haddr'. }
  assert (Hsomej : is_Some (fn_blk nj !! k')).
  { apply (proj2 (inr_blk_dom (sk_repr Hok' j nj Hnj) k' HkM')).
    rewrite Hnaj. exact Hb0. }
  assert (Hownj : fn_owns nj b)
    by (left; exists k'; split; [exact Hsomej | exact Hnaj]).
  exact (Hij (sk_disj Hok' i ni j nj b Hni Hnj Howni Hownj)).
Qed.

(* ...and the same statement at the shape of the premise
   [SpecLogWrite.wp_log_write_au_range] asks a supplier for, with the
   payload spelled as the plan's [Ψ D0 Dc := ⌜∃ S, snap_bytes S Dc⌝].  Any
   STRENGTHENING of that payload -- the geometry pin of (G1), a
   normalisation of the state -- is refuted a fortiori, since the
   consequent only gets harder. *)
Corollary bfree_payload_step_false
    (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i b : Z) (n : fs_node) (k : nat) :
  snap_bytes S D ->
  fs_sb_ok (fss_sb S) ->
  0 <= i < sb_ninodes (fss_sb S) ->
  fss_inodes S !! i = Some n ->
  (k < FS_NDIRECT)%nat -> fn_naddr n k = b -> b <> 0 ->
  0 <= b < sb_size (fss_sb S) ->
  ~ ((exists S0, snap_bytes S0 D) ->
     (exists S1, snap_bytes S1
        (<[sb_bmapstart (fss_sb S)
           := bm_bytes BSIZE (fss_used S ∖ {[b]})]> D))).
Proof.
  intros Hok Hsb Hirange Hi Hk Hnaddr Hb0 Hbrange Hstep.
  apply (bfree_used_coupling_refuted S D i b n k
           Hok Hsb Hirange Hi Hk Hnaddr Hb0 Hbrange).
  apply Hstep. by exists S.
Qed.
