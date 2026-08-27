(* InodeRegion.v -- THE INODE REGION: the dinode blocks' owner, and the
   per-inum fragment that replaces the coarse whole-block premise in every
   inode-layer contract.  Design: claude-notes/design/fs-icache.md, §11-§12.

   [FsBlocks.fsblock] is the write permission for a block, and a dinode
   block holds SIXTEEN inodes -- so any contract that takes the block's
   half for the duration of a call is unsatisfiable by two lock holders in
   the same block (§11.1).  The fix is a CHANGE OF GRANULARITY: callers
   hold [dinode_at γi inum dn], an exclusive per-inum ghost_map fragment,
   and the block halves never leave this region's invariant.

   ---- WHY THERE IS NO CHECKED-OUT ARM (§12) ----------------------------

   The first design (§11.4) had iupdate checking the block's half OUT of
   the region across its log_write and parking it back after.  That escrow
   cannot state its checked-out arm: during the window the thread's own
   log_write footprint ([bio_held] + the client half) holds EVERY per-block
   exclusive resource -- [disk_block] in full, both [fs_cache] halves, the
   machinery dirty half -- so by conservation the arm has nothing to hold,
   and a checkout could never prove the arm is parked.

   So the region is ONE-ARMED, and the only moment the client half leaves
   it is log_write's own ghost step (ProofLogWrite.v's [fsblock_update], a
   single [iMod] between two instruction dispatches, at mask ⊤).
   [ireg_write_au] below is the atomic update iupdate hands to the
   generalized SpecLogWrite premise: it opens the region THERE, lets
   [fsblock_update] run against the withdrawn run, and re-parks the block
   at the new bytes while retagging the caller's [dinode_at] in the same
   opening.  [ireg_read] is ilock's side: one mask-preserving opening in
   which the caller's payload machinery half pins the region's bytes and
   the coupling turns its [dinode_at] into [ds !!! islot inum = dn] --
   which is how [SpecIlock]'s "vv = false -> ds !!! islot inum = dn"
   premise stops being expressible rather than getting discharged (§11.3).

   ---- THE COUPLING, AND ONE NEW PURE FACT ------------------------------

   The invariant holds the ghost map's authority beside the block halves,
   with a pure coupling: slot [i] of block [bi]'s parked list IS the map's
   value at inum [16*bi + i].  Re-establishing the coupling after a write
   needs to know the parked list has not moved between iupdate's bread
   (where the caller learns [ds]) and its log_write (where the region is
   opened again).  Nothing the thread holds pins the LIST -- only its
   BYTES, via the machinery half riding in the thread's own payload -- so
   the bridge is [diblk_bytes_inj]: the encoding is injective on
   well-formed lists (§12.3).  Proved here from [bv_eq_of_bytes].

   ---- WHO HOLDS A FREE INUM'S FRAGMENT (§16.3/§16.4) --------------------

   Until §16 a free inum's [dinode_at] lived in the pool row's
   free arm, i.e. behind the itable spinlock -- and ialloc, whose claim is
   serialised by the BUFFER and by nothing else, can never hold that lock.
   So the free arm's fragment moved IN HERE: [ireg_slot] below is the
   per-slot arm, and it holds the record fragment exactly when the record is
   free OR freshly claimed ([fresh_shape]), and the per-inum MARKER
   ([imark]) otherwise.  Exactly one of the two is inside the invariant at
   any time and the other is outside; the marker is what the pool's free arm
   and a marker-parked cache entry now carry.

   That gives four arm moves rather than one:

     [ireg_write_au]  an ordinary flush -- fragment stays out, marker stays
                      in; hence the [di_type dn' <> 0] premise.
     [ireg_claim_au]  ialloc -- retag a type-0 record to a [fresh_shape]
                      one with NO caller resource at all.  This is §16.4's
                      claim box: the fragment never leaves the invariant, so
                      no interleaving can strand a concurrent fill.
     the FREE          iput's [ip->type = 0; iupdate] -- absorb the fragment,
                      pay out the marker.  It lives ABOVE this file, as
                      [EscrowDeposit.ireg_free_deposit_au]: the off-lock
                      deposit is the only type-0 write the reordered kernel
                      has, and it needs the escrow beside the region.
     [ireg_withdraw]  ilock's FIRST fill of a claimed inum -- deposit the
                      marker, take the fragment.  The marker is what makes
                      that case analysis exhaustive.

   ---- AND TWO MORE, FOR THE COUNT (§20.6, fs-sysfile S5f) --------------

     [ireg_write_link_reg]   mkdir's [".."] and sys_link's [ip->nlink++]:
                          mint the TYPE REGISTER's fragments in the SAME
                          ghost step as the count that pays for them
                          (fs-state.md §6½ -- the count IS the fragment
                          count).
     [ireg_write_unlink_reg] sys_unlink's [ip->nlink--], the ONLY nlink-
                          LOWERING region write in the kernel: it CONSUMES
                          them as it lowers.  That is precisely why
                          the ordinary flush may demand [di_nlink_stable]
                          -- the one writer that would violate it does not
                          go through the ordinary flush at all.

   THE SURVIVING CLAUSES ARE (L3)/(L4)/(L5), stated in [ireg_link_ok] below
   and re-established by all six arm moves.  Since durable-disk lane G's
   slice 6b their ONE remaining payoff is [ireg_link_ok_free] ("at the
   instant an inode is freed nothing names it"), which is what makes the
   claim mover's collapse of the [wl+wdu+wdt] sum legal; the old
   [ireg_link_ok_alloc] / [ireg_link_alloc] pair ("an outstanding fragment
   means an ALLOCATED record") is gone, its readings now taken off the
   counting RA ([ireg_lnk_tok_nz], [IgetLic]'s licence (a),
   [IregLinkNz.ireg_tok_nz]).  What is still NOT stated is §20.2's (L2) and the
   [c = None] half of (L3): nothing mints an [iclaim] yet, and the free
   cannot re-establish [c = None] without consuming one -- see
   [EscrowDeposit.ireg_free_deposit_au]'s note and design §20.15.

   ---- WHAT IS DELIBERATELY NOT HERE ------------------------------------

   The boot-time allocation (building the initial map from the mkfs
   image's dinode blocks and minting every [dinode_at]) is fsinit wiring
   and lives in [IcacheBoot.v], not here.  The icache pool that HOLDS the
   fragments of uncached inodes is IcacheInv's (design §10.4).            *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants ghost_map mono_nat.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvPtsto.
Require Import RiscvModelBytes.
Require Import FsBlocks.
Require Import BlockWords.
Require Import DinodeEnc.
(* THE REGION'S BYTE UNIT IS THE RECORD (durable-disk 2b-inode-1).  What the
   region parks per slot is [FsStateInode.rec_owned_at (fs_gamma_L γfs)
   inodestart z d] -- the 64-byte run at offset [64*(z mod 16)] of block
   [inodestart + z/16] -- and NOT a whole inode block's [fsblock].  The two
   are interderivable through [rec_owned_at_diblk]'s sixteen-fold split
   ([ireg_recs_blk] below), which is the ONE place the block spelling still
   appears.
   IMPORTED BEFORE [IcacheRef] ON PURPOSE: [FsStateInode] exports
   [FsStateLink], whose [link_auth] is a DIFFERENT predicate from the
   region's ten-argument ledger of the same name, and the LAST import wins
   (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY").  The
   same holds for [FsStateDefs.byte_range] against [FsBlocks]'s; this file
   spells neither unqualified. *)
Require Import FsStateInode.
(* [fsTopG] / [top_frag] -- the era's abstract inode map.  A CAPACITY class,
   so it must be IMPORTed and not merely required (durable-notes), and it is
   imported HERE, before [IcacheRef], for the collision reason the paragraph
   above gives: [FsState] re-exports [FsStateLink]'s [link_auth] and
   [FsStateDefs]'s [byte_range], both of which have live twins below.
   [fsTopG] itself is NOT taken from here: it is an [Xv6G.xv6G] member
   (durable-disk 2b-inode-3) and arrives with the [Require Export
   Xv6Cameras] at the end of this block, which is what puts it in every
   importer's scope without carrying the [FsState*] stack's colliding
   names along. *)
Require Import FsState.
Require Import FsBytesGamma.
(* THE LINK LEDGER's algebra and its ambient gname (design §20.2).
   EXPORTED, not merely imported: [ireg_slot] parks [IcacheRef.link_auth],
   so [icacheG] and [icfg] are now part of every [ireg_inv]'s type, and a
   file that names [ireg_inv] through a bare [Require Import InodeRegion]
   would otherwise IMPLICITLY GENERALIZE a fresh [icacheG] variable
   (durable-notes' first typeclass-sweep trap).  The chain is supposed to
   carry the class; this is where it starts. *)
Require Export IcacheRef.
Require Import EscrowDefs.   (* OPTION A: region_pending / reg_half / committedA *)
(* N-4 PHASE B (E1-region): the per-inum LEND COLUMN [dv_lcol] this file
   parks inside [ireg_registry], and the three column moves §L wraps in an
   [↑iregN] open.  The vocabulary is BELOW the region on purpose (see that
   file's altitude note); only the operations are here. *)
Require Import FsTree.       (* [fname] -- the lend's entry-map key type      *)
Require Import DirViewG.     (* [dv_half] / [dv_hold] -- the lent fractions  *)
Require Import DirViewLend.
(* [logged_at] / [log_epoch_lb]: the zero-receipt parked in [ireg_slot]
   (fs-log.md §G.17).  This is what puts [logG] in the section's context,
   and hence in the context of the four files that STATE something over
   [ireg_inv] -- the enumerated sweep. *)
Require Import LogInv.
(* [add_vec_unsigned], for (L4)'s two bridge lemmas below.  Already in this
   file's transitive closure (through [IcacheRef]); named here because a
   [Require Import] in a sibling does not put its lemmas in scope. *)
Require Import SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvExtras.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE ENCODING IS INJECTIVE ON WELL-FORMED LISTS (§12.3)            *)
(* ===================================================================== *)

(* a 16-bit field is determined by its two bytes *)
Lemma half_bytes_inj (w1 w2 : bv 16) :
  half_bytes w1 = half_bytes w2 -> w1 = w2.
Proof.
  intros H.
  apply (bv_eq_of_bytes (n := 2%N) w1 w2).
  intros j Hj.
  assert (Hj2 : (j < 2)%nat) by lia.
  pose proof (half_bytes_lookup w1 j Hj2) as L1.
  pose proof (half_bytes_lookup w2 j Hj2) as L2.
  rewrite H in L1. rewrite L2 in L1.
  apply (inj Some). exact (eq_sym L1).
Qed.

(* ...and a 32-bit one by its four *)
Lemma word_bytes_inj (w1 w2 : bv 32) :
  word_bytes w1 = word_bytes w2 -> w1 = w2.
Proof.
  intros H.
  apply (bv_eq_of_bytes (n := 4%N) w1 w2).
  intros j Hj.
  assert (Hj4 : (j < 4)%nat) by lia.
  pose proof (word_bytes_lookup w1 j Hj4) as L1.
  pose proof (word_bytes_lookup w2 j Hj4) as L2.
  rewrite H in L1. rewrite L2 in L1.
  apply (inj Some). exact (eq_sym L1).
Qed.

Lemma ind_bytes_inj (e1 e2 : list (bv 32)) :
  length e1 = length e2 ->
  ind_bytes e1 = ind_bytes e2 -> e1 = e2.
Proof.
  revert e2. induction e1 as [|w1 e1 IH]; intros [|w2 e2] Hlen H;
    [reflexivity | discriminate | discriminate |].
  rewrite !ind_bytes_cons in H.
  apply app_inj_1 in H as [Hw He];
    [| rewrite !word_bytes_length; reflexivity].
  f_equal.
  - exact (word_bytes_inj _ _ Hw).
  - apply IH; [by injection Hlen | exact He].
Qed.

Lemma dinode_bytes_inj (d1 d2 : dinode) :
  dinode_wf d1 -> dinode_wf d2 ->
  dinode_bytes d1 = dinode_bytes d2 -> d1 = d2.
Proof.
  intros H1 H2 H. unfold dinode_bytes in H.
  apply app_inj_1 in H as [Hty H];
    [| rewrite !half_bytes_length; reflexivity].
  apply app_inj_1 in H as [Hmaj H];
    [| rewrite !half_bytes_length; reflexivity].
  apply app_inj_1 in H as [Hmin H];
    [| rewrite !half_bytes_length; reflexivity].
  apply app_inj_1 in H as [Hnl H];
    [| rewrite !half_bytes_length; reflexivity].
  apply app_inj_1 in H as [Hsz Had];
    [| rewrite !word_bytes_length; reflexivity].
  unfold dinode_wf in H1, H2.
  destruct d1, d2; cbn in *.
  f_equal.
  - exact (half_bytes_inj _ _ Hty).
  - exact (half_bytes_inj _ _ Hmaj).
  - exact (half_bytes_inj _ _ Hmin).
  - exact (half_bytes_inj _ _ Hnl).
  - exact (word_bytes_inj _ _ Hsz).
  - apply ind_bytes_inj; [congruence | exact Had].
Qed.

Lemma diblk_bytes_inj_aux (ds1 ds2 : list dinode) :
  length ds1 = length ds2 ->
  Forall dinode_wf ds1 -> Forall dinode_wf ds2 ->
  diblk_bytes ds1 = diblk_bytes ds2 -> ds1 = ds2.
Proof.
  revert ds2. induction ds1 as [|d1 ds1 IH]; intros [|d2 ds2] Hlen Hw1 Hw2 H;
    [reflexivity | discriminate | discriminate |].
  inversion Hw1 as [|? ? Hd1 Hds1]; subst.
  inversion Hw2 as [|? ? Hd2 Hds2]; subst.
  rewrite !diblk_bytes_cons in H.
  apply app_inj_1 in H as [Hd Hds];
    [| rewrite (dinode_bytes_length d1 Hd1) (dinode_bytes_length d2 Hd2);
       reflexivity].
  f_equal.
  - exact (dinode_bytes_inj d1 d2 Hd1 Hd2 Hd).
  - apply IH; [by injection Hlen | exact Hds1 | exact Hds2 | exact Hds].
Qed.

(* THE §12.3 OBLIGATION.  This is what lets iupdate conclude the region's
   parked list at log_write time is the one it read at bread time: its own
   payload's machinery half pinned the BYTES the whole way, and the bytes
   determine the list. *)
Lemma diblk_bytes_inj (ds1 ds2 : list dinode) :
  diblk_wf ds1 -> diblk_wf ds2 ->
  diblk_bytes ds1 = diblk_bytes ds2 -> ds1 = ds2.
Proof.
  intros [Hl1 Hw1] [Hl2 Hw2].
  apply diblk_bytes_inj_aux; [congruence | exact Hw1 | exact Hw2].
Qed.

(* ===================================================================== *)
(*  WRITING ONE RECORD IS A SPLICE OF THE BLOCK (durable-disk 2b-inode-1)  *)
(*                                                                        *)
(*  The two pure facts a RECORD-granular [log_write] owes, both about the  *)
(*  encoding alone.  [diblk_bytes_slice] is what the log's tie says the    *)
(*  writer's run WAS (the checked-out buffer's slice at [64*k]), and       *)
(*  [diblk_bytes_splice] is [wp_log_write_au_range_body]'s shape           *)
(*  obligation: the buffer a slot flush leaves differs from the block's    *)
(*  logged content EXACTLY inside that slot's window.                      *)
(* ===================================================================== *)

Lemma diblk_bytes_slice (ds : list dinode) (k : nat) :
  diblk_wf ds -> (k < 16)%nat ->
  take 64%nat (drop (64 * k)%nat (diblk_bytes ds)) = dinode_bytes (ds !!! k).
Proof.
  intros [Hlen Hall] Hk.
  assert (Hwfk : dinode_wf (ds !!! k)).
  { apply (Forall_lookup_1 _ ds k); [exact Hall |].
    apply list_lookup_lookup_total_lt. lia. }
  assert (Hlb : length (diblk_bytes ds) = 1024%nat)
    by (rewrite (diblk_bytes_length ds Hall) Hlen; reflexivity).
  assert (Hsub : length (dinode_bytes (ds !!! k)) = 64%nat)
    by exact (dinode_bytes_length _ Hwfk).
  apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j 64%nat) as [Hj | Hj].
  - rewrite lookup_take; [| lia]. rewrite lookup_drop.
    rewrite (diblk_bytes_lookup ds k j Hall ltac:(lia) Hj). reflexivity.
  - rewrite lookup_take_ge; [| lia].
    symmetry. apply lookup_ge_None_2. lia.
Qed.

Lemma diblk_bytes_splice (ds : list dinode) (k : nat) (d : dinode) :
  diblk_wf ds -> dinode_wf d -> (k < 16)%nat ->
  diblk_bytes (<[k := d]> ds)
  = blk_splice (64 * k)%nat (dinode_bytes d) (diblk_bytes ds).
Proof.
  intros Hwf Hd Hk. pose proof Hwf as [Hlen Hall].
  assert (Hlb : length (diblk_bytes ds) = 1024%nat)
    by (rewrite (diblk_bytes_length ds Hall) Hlen; reflexivity).
  assert (Hsub : length (dinode_bytes d) = 64%nat)
    by exact (dinode_bytes_length d Hd).
  apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j (64 * k)%nat) as [Hlt | Hge].
  - rewrite (blk_splice_lookup_lt (64 * k)%nat (dinode_bytes d)
               (diblk_bytes ds) j ltac:(lia) Hlt).
    exact (diblk_bytes_insert_other ds k d j Hall Hd ltac:(lia)
             ltac:(left; lia)).
  - destruct (Nat.lt_ge_cases j (64 * k + 64)%nat) as [Hmid | Hgt].
    + rewrite (blk_splice_lookup_mid (64 * k)%nat (dinode_bytes d)
                 (diblk_bytes ds) j ltac:(lia) Hge ltac:(lia)).
      replace j with (64 * k + (j - 64 * k))%nat at 1 by lia.
      exact (diblk_bytes_insert_same ds k d (j - 64 * k)%nat Hall Hd
               ltac:(lia) ltac:(lia)).
    + rewrite (blk_splice_lookup_ge (64 * k)%nat (dinode_bytes d)
                 (diblk_bytes ds) j ltac:(lia) ltac:(lia)).
      exact (diblk_bytes_insert_other ds k d j Hall Hd ltac:(lia)
               ltac:(right; lia)).
Qed.

(* the slot update a flush performs keeps the block well formed *)
Lemma diblk_wf_insert (ds : list dinode) (k : nat) (d : dinode) :
  diblk_wf ds -> dinode_wf d -> diblk_wf (<[k := d]> ds).
Proof.
  intros [Hlen Hall] Hd. split.
  - rewrite length_insert. exact Hlen.
  - apply Forall_insert; [exact Hall | exact Hd].
Qed.

(* ===================================================================== *)
(*  2.  THE inum <-> (block, slot) ARITHMETIC                             *)
(* ===================================================================== *)

(* block index [bi] (relative to inodestart) of an inum, as a nat *)
Definition ireg_bi (inum : bv 32) : nat := Z.to_nat (bv_unsigned inum / 16).

Lemma ireg_bi_iblock (inum : bv 32) (inodestart : Z) :
  IBLOCK inum inodestart = inodestart + Z.of_nat (ireg_bi inum).
Proof.
  unfold IBLOCK, ireg_bi.
  pose proof (bv_unsigned_in_range _ inum) as [Hlo _].
  rewrite Z2Nat.id; [lia |].
  apply Z.div_pos; lia.
Qed.

(* the key the coupling files an inum under IS the inum *)
Lemma ireg_key_split (inum : bv 32) :
  bv_unsigned inum
  = 16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum).
Proof.
  unfold ireg_bi, islot.
  pose proof (bv_unsigned_in_range _ inum) as [Hlo _].
  pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as Hm.
  pose proof (Z.div_pos (bv_unsigned inum) 16 Hlo ltac:(lia)) as Hd.
  rewrite !Z2Nat.id; [| lia | lia].
  pose proof (Z.div_mod (bv_unsigned inum) 16 ltac:(lia)). lia.
Qed.

Lemma ireg_bi_lt (inum : bv 32) (nib : nat) :
  bv_unsigned inum < 16 * Z.of_nat nib -> (ireg_bi inum < nib)%nat.
Proof.
  intros Hin. unfold ireg_bi.
  pose proof (bv_unsigned_in_range _ inum) as [Hlo _].
  assert (Hq : bv_unsigned inum / 16 < Z.of_nat nib)
    by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(* two slots of ONE block have distinct keys; a slot of ANOTHER block has a
   distinct key.  Both are the same fact, and it is what keeps a one-inum
   update from disturbing any other slot's coupling. *)
Lemma ireg_key_inj (j1 j2 i1 i2 : nat) :
  (i1 < 16)%nat -> (i2 < 16)%nat ->
  (16 * Z.of_nat j1 + Z.of_nat i1)%Z = (16 * Z.of_nat j2 + Z.of_nat i2)%Z ->
  j1 = j2 /\ i1 = i2.
Proof. intros H1 H2 Heq. lia. Qed.

(* ===================================================================== *)
(*  2b.  THE FRESHLY CLAIMED SHAPE (§16.4)                                *)
(* ===================================================================== *)

(* Exactly what ialloc's [memset(dip, 0, 64)] followed by
   [dip->type = type] leaves on disk: a nonzero type, a zero size, thirteen
   zero address words and a ZERO LINK COUNT.  ialloc writes NOTHING else --
   [nlink] stays 0 until the caller's own iupdate -- so this is deliberately
   the WEAKEST record shape a claim can promise, and it is still enough for
   ilock's fill to build [InodeLock.inode_ok] out of nothing at all
   ([InodeInv.bm_empty] collapses every block resource, [bm_covers_nonpos]
   and [DirView.dir_ok_size_zero] ride on the zero size).

   THE NLINK CONJUNCT (design §20.18 ruling 1, the C1 layer).  The claim box
   is the ONE record shape a caller may hold whose [nlink] nothing outside
   constrains -- and create's COMMIT is
   the first writer that has to say what that count IS: it mints the
   register's fragments against [nlink 0 -> 1], and "the record I am
   flushing over has nlink 0"
   is exactly what makes the arithmetic a fact rather than a caller's claim.
   Free at the ONE producer ([SpecIalloc.ialloc_fresh_shape], where it is
   [reflexivity] over [memset]'s zero) and free at every consumer, which
   only ever destructs it.

   Stated with a bare [replicate 13] rather than [InodeInv.bm_cells
   bm_empty] so that this file keeps its short Require list; the bridge is
   one [vm_compute] at the two sites that need it. *)
Definition fresh_shape (d : dinode) : Prop :=
  bv_unsigned (di_type d) <> 0
  /\ bv_unsigned (di_size d) = 0
  /\ di_addrs d = replicate 13 (bv_0 32)
  /\ bv_unsigned (di_nlink d) = 0.

Lemma fresh_shape_wf (d : dinode) : fresh_shape d -> dinode_wf d.
Proof.
  intros (_ & _ & Ha & _). rewrite /dinode_wf Ha length_replicate. reflexivity.
Qed.

(* the new conjunct, named so a consumer reads it off without destructuring
   four ways (and so the claim box's [nlink] has one place to be cited) *)
Lemma fresh_shape_nlink (d : dinode) :
  fresh_shape d -> bv_unsigned (di_nlink d) = 0.
Proof. intros (_ & _ & _ & Hnl). exact Hnl. Qed.

(* ---- THE BARE RECORD, AND THE NODE IT DETERMINES (durable-disk C-3c) ---

   [fresh_shape] MINUS the type clause: a record that names no block and has
   size 0.  Two of this kernel's record shapes are bare -- the claim box
   ([fresh_shape]) and the FREE record iput's deposit writes (and the mkfs
   image's, [FsCfgBoot.fs_region_bare]) -- and the second is the one the
   commit's collection needs: a bare TYPE-0 record determines its abstract
   node outright, so the region can park the era's [top_frag] TIED to the
   record it holds beside it ([ireg_top_park] below).  Without the tie a free
   inum's [top_frag] is untied and the collection can prove neither
   [FsDurSnap.sk_rec] nor [sk_links] there (FsCollect.v's supplier (D)). *)
Definition ireg_bare (d : dinode) : Prop :=
  bv_unsigned (di_size d) = 0 /\ di_addrs d = replicate 13 (bv_0 32).

Lemma fresh_shape_bare (d : dinode) : fresh_shape d -> ireg_bare d.
Proof. intros (_ & Hsz & Ha & _). split; [exact Hsz | exact Ha]. Qed.

Lemma ireg_bare_wf (d : dinode) : ireg_bare d -> dinode_wf d.
Proof. intros (_ & Ha). rewrite /dinode_wf Ha length_replicate //. Qed.

(* THE NODE A BARE RECORD DETERMINES.  [FsStateInode.fn_bare]'s three
   non-record clauses are exactly "no entries, no blocks", so a bare record
   leaves the node no freedom at all -- which is why the tie below needs no
   existential and why the collection's [FsCollect.col_bundle] legs
   ([FsStateEra.inode_bytes_era]'s two big-ops) are [emp] there. *)
Definition free_node (d : dinode) : fs_node :=
  MkNode d (replicate FsImg.FS_NINDIRECT (bv_0 32)) ∅.

Lemma free_node_rec (d : dinode) : fn_rec (free_node d) = d.
Proof. reflexivity. Qed.

(* ...AND THE CONVERSE, which is what makes the tie STATABLE without an
   existential: [fn_bare] pins the entry array and the block map outright,
   so a bare node IS [free_node] of its own record. *)
Lemma free_node_of_bare (n : fs_node) : fn_bare n -> n = free_node (fn_rec n).
Proof.
  destruct n as [r e b]. intros (_ & He & Hb & _).
  rewrite /free_node /=. cbn in He, Hb. rewrite He Hb //.
Qed.

Lemma ireg_bare_of_fn_bare (n : fs_node) : fn_bare n -> ireg_bare (fn_rec n).
Proof. intros (Ha & _ & _ & Hsz & _). split; [exact Hsz | exact Ha]. Qed.

Lemma fn_bare_free_node (d : dinode) :
  ireg_bare d -> bv_unsigned (di_nlink d) = 0 -> fn_bare (free_node d).
Proof.
  intros (Hsz & Ha) Hnl. rewrite /fn_bare /free_node /fn_size /fn_nlink /=.
  split_and!; [exact Ha | reflexivity | reflexivity | exact Hsz |].
  rewrite Hnl //.
Qed.

(* ...AND [inode_local] OF IT AT A FREE RECORD, which is what the commit's
   collection reads off the park.  Only the TYPE-0 case is stated: the
   enumeration clause [FsStateInode.inl_type] is then its own first
   disjunct, so this file needs none of [FsImg]'s type names. *)
Lemma inode_local_free_node (z : Z) (d : dinode) :
  ireg_bare d -> bv_unsigned (di_nlink d) = 0 ->
  bv_unsigned (di_type d) = 0 ->
  inode_local z (free_node d).
Proof.
  intros Hb Hnl Ht0.
  apply (inode_local_bare z (free_node d) (fn_bare_free_node d Hb Hnl)).
  left. rewrite /fn_type /free_node /=. exact Ht0.
Qed.

(* ---- THE TWO IN-TRANSITION PINS (iclaim-ledger.md §2.3/§2.4) ---------

   THE CLAIM PIN (§2.4).  A claimed slot's record IS the claim box ialloc
   wrote -- [fresh_shape], hence [di_nlink = 0] and a nonzero type.  Two
   things read it: [ireg_claim_au] refutes a STANDING claim with it (its
   caller's buffer showed [di_type = 0], and [fresh_shape]'s first conjunct
   says otherwise), which is what makes the c-mint's [c = None] side
   condition dischargeable at all; and the create_fresh_ty payout (§2.8
   item 7) withdraws the pinned shape at the fill.

   IT IS THE ARM THAT KEEPS IT TRUE, not the byte movers.  §2.4's "writes
   cannot dent the pin" is the observation that every byte-writing mover
   consumes the caller's [dinode_at] and therefore runs at the MARKED arm,
   where the slot's own clause ([ireg_marked_ok] below) says [c = None] --
   so [ireg_write_au], [EscrowDeposit.ireg_free_deposit_au] and the two link movers re-establish
   the pin vacuously and none of them grows a premise.  The one mover that
   moves a slot from the claimed (IN) arm to the marked one is
   [ireg_withdraw], and that is exactly §2.4's spend site: it CONSUMES an
   [iclaim] and retires the column. *)
(* THE SECOND CONJUNCT (iclaim-ledger.md §3.1, RULING A): a claimed box is
   NEVER frozen.  It is the ClaimL row's contradiction surface in
   [IgetLic.iname_not_frozen] -- the one licence whose refutation cannot go
   through the freeze pin's [nlink = 0] (a claim box has [nlink = 0] too, by
   [fresh_shape]) and must go through the c column instead.

   IT COSTS THE MOVERS NOTHING.  [ireg_claim_au] ESTABLISHES it: its
   [di_type (ds !!! islot inum) = 0] premise meets the freeze pin's type
   conjunct at the OLD record and forces [f = FrzOff] there
   ([ireg_frz_ok_ty0]), and the claim does not touch the f column.  Every
   byte mover runs at the MARKED arm ([c = None]) and owes nothing.  The two
   movers that DO step f -- [ireg_freeze_au]'s mint and the phase step --
   both hold the record and so also run at [c = None]; and the phase step is
   self-refuting anyway, since a standing [FrzPre] already contradicts this
   clause at [c = Some]. *)
(* THE THIRD CONJUNCT (iclaim-ledger.md §5.2(a), item 7b): the column
   carries the type [ialloc] claimed, and the pin says the box's record has
   it.  [ireg_claim_au] establishes it by construction (it mints at its own
   record's type); every other mover runs at [c = None] or at an unchanged
   record, so it carries.  Spelled [x = Excl (di_type d)] rather than as a
   match on [x] so that the landed [destruct c as [x |]] proofs do not have
   to grow an [ExclBot] arm -- at [ExclBot] the equation is False, which is
   what an invalid column deserves. *)
Definition ireg_claim_ok (c : ctyUR) (f : frzUR) (d : dinode)
  : Prop :=
  match c with
  | None   => True
  | Some x => fresh_shape d /\ f = Some (Excl FrzOff) /\
              (* THE VALUE'S FIRST FIELD IS THE BOX'S TYPE.  Since
                 durable-disk C-5 the column carries the CLAIMING
                 TRANSACTION beside it ([Xv6Cameras.ctyval]); the pin says
                 nothing about that pair -- what constrains it is
                 [ireg_cpin], the parked share, which is what refutes a
                 standing claim at a commit. *)
              match x with
              | Excl v  => v.1 = di_type d
              | ExclBot => False
              end
  end.

Lemma ireg_claim_ok_none (f : frzUR) (d : dinode) : ireg_claim_ok None f d.
Proof. exact I. Qed.

(* the two projections, so no consumer destructures the match *)
Lemma ireg_claim_ok_shape (c : ctyUR) (f : frzUR) (d : dinode) :
  c <> None -> ireg_claim_ok c f d -> fresh_shape d.
Proof.
  destruct c as [x |];
    [ intros _ [H _]; exact H
    | intros H; exfalso; exact (H eq_refl) ].
Qed.

Lemma ireg_claim_ok_off (c : ctyUR) (f : frzUR) (d : dinode) :
  c <> None -> ireg_claim_ok c f d -> f = Some (Excl FrzOff).
Proof.
  destruct c as [x |];
    [ intros _ [_ [H _]]; exact H
    | intros H; exfalso; exact (H eq_refl) ].
Qed.

(* THE PAYOUT (iclaim-ledger.md §5.2(a)): the claimed type IS the box's
   type.  This is the fact [ireg_withdraw] hands create's fill, and the
   whole reason the column carries a value. *)
Lemma ireg_claim_ok_ty (v : ctyval) (f : frzUR) (d : dinode) :
  ireg_claim_ok (Some (Excl v)) f d -> di_type d = v.1.
Proof. intros [_ [_ Hx]]. exact (eq_sym Hx). Qed.

(* ---- ilock's LICENCE INDEX (iclaim-ledger.md §5''''', RULING C') --------

   [wp_ilock_sconf] serves sixteen call sites and its fill has to discharge
   §16.4's claim-box arm at every one of them.  The index says WHICH of the
   three currencies the caller brought, and therefore which discharge the
   fill runs:

     [ClaimK ty]  ialloc's own claimant -- create's child fill, and the ONLY
                  site that can present the typed [iclaim].  SPENT, together
                  with the claim-flavoured provenance unit; the pair
                  CONVERTS into the plain unit and buys [di_type d = ty].
     [PlainK]     the twelve in-file-unit sites: the reference in the
                  caller's hand already carries [runit_plain], which the
                  claim pin's (R3) turns into [c = None] -- the box arm is
                  refuted and the unit goes straight back out.
     [ShotK ty]   the three fd sites (fileread/filewrite/filestat), which
                  can hold NO whole unit across the call (their payload is
                  behind a cancellable invariant).  The generation's own
                  persistent one-shot is what they have, and it refutes
                  ilock's UNCACHED arm outright.

   Three constructors rather than a triple disjunction for [ireg_link_pin]'s
   reason: the payout differs per arm, and a caller that presented one must
   not have to case on the other two to read its own post. *)
(* [ClaimK] NAMES THE CLAIMING TRANSACTION (durable-disk C-5): the share
   [t |->[ln_tx icfg_log]{#q} tt] that [ireg_claim_au] parked in the region
   for the length of the claim box comes back at the fill, and it has to
   come back at exactly the pair that went in -- two halves of one element
   are not the whole.  The pair rides in the c
   column's own value, so the claimant's [IcacheRef.iclaim] fragment names
   it and [ireg_wd_back]'s claim arm is what hands it back. *)
Inductive ilkc : Type :=
| ClaimK (ty : bv 16) (t : nat) (q : Qp)
| PlainK
| ShotK (ty : bv 16).

(* ---- THE REFERENCE-PROVENANCE CLAUSE (iclaim-ledger.md §5', RULING R) ---

   THE r COLUMN's PIN, and the reason item 7a exists.  §5'.2 rules that every
   icache reference carries one FLAVOURED provenance unit ([IcacheRef.runit],
   [runit_claim] / [runit_plain]) for its whole life, and that a claim box
   carries no PLAINLY-licenced reference:

       (R1)  r + rc <= n          the units COUNT the in-core references
       (R2)  di_type d = 0  ->  r = 0 /\ rc = 0
       (R3)  c <> None      ->  r = 0                     <-- THE PIN

   (R3) IS WHAT §5'.3's DISJUNCTIVE WITHDRAW READS: a caller that presents its
   own [runit_plain] forces [1 <= r] ([IcacheRef.link_runit_ge]) and (R3)'s
   contrapositive then DERIVES [c = None] -- so the fifteen non-create
   [wp_ilock_sconf] sites pay with the unit their reference already carries,
   the marked arm's [ireg_marked_ok] holds, and nothing retires.

   WHY (R1) AND (R2) ARE HERE TOO -- THE DEVIATION FROM §5'.2, RECORDED.  The
   ruling's establish route for (R3) was "the standing pin [type = 0 -> r = 0]"
   at [ireg_claim_au].  THERE IS NO SUCH STANDING CLAUSE ON THE LANE: [r] rode
   the ledger entirely unconstrained (its charter at [IcacheRef.v:296] has zero
   consumers).  It is (R2), and (R2) is only PRESERVABLE with (R1) beside it:
   the one mover that writes a zero type is [EscrowDeposit.ireg_free_deposit_au], which holds
   [ifreeze_post] and therefore [n = 0] by the freeze pin -- and (R1) turns
   that into [r = rc = 0].  So the ruling's "all units die at the free's
   count-0" is exactly (R1), stated.  The three conjuncts are ONE predicate so
   that [ireg_slot]'s pure block grows by one clause and not three.

   THE COST TO THE MOVERS, ARM BY ARM.  (R1) moves only where BOTH a unit and
   the count move, which is every count mover by construction (iget's two
   up-counts and idup mint, iput's two closes spend).  (R2) is stable at every
   type-preserving flush, vacuous at [ireg_claim_au] (a [fresh_shape] record
   has a nonzero type) and paid at [EscrowDeposit.ireg_free_deposit_au] as above.  (R3) is vacuous
   at [c = None], established at [ireg_claim_au] from (R2) at the OLD (type-0)
   record, and preserved at the plain mint by [IgetLic.iname_not_claimed] --
   the §2.6-pattern table lemma, twin of the landed [iname_not_frozen]. *)
Definition ireg_ref_ok (r rc n : nat) (c : ctyUR) (d : dinode)
  : Prop :=
  (r + rc <= n)%nat
  /\ (bv_unsigned (di_type d) = 0 -> r = 0%nat /\ rc = 0%nat)
  /\ (c <> None -> r = 0%nat).

(* the all-zero slot: what boot mints and what the free re-establishes *)
Lemma ireg_ref_ok_zero (n : nat) (c : ctyUR) (d : dinode) :
  ireg_ref_ok 0 0 n c d.
Proof. rewrite /ireg_ref_ok. split_and!; [lia | intros _; done | intros _; done]. Qed.

(* (R1) read off *)
Lemma ireg_ref_ok_le (r rc n : nat) (c : ctyUR) (d : dinode) :
  ireg_ref_ok r rc n c d -> (r + rc <= n)%nat.
Proof. intros [H _]. exact H. Qed.

(* (R1) at a count-0 slot -- [EscrowDeposit.ireg_free_deposit_au]'s payment *)
Lemma ireg_ref_ok_count0 (r rc n : nat) (c : ctyUR) (d : dinode) :
  ireg_ref_ok r rc n c d -> n = 0%nat -> r = 0%nat /\ rc = 0%nat.
Proof. intros [Hle _] Hn. rewrite Hn in Hle. split; lia. Qed.

(* (R2) read off, and its contrapositive -- an outstanding unit of EITHER
   flavour is an allocatedness witness, which is what idup's mint pays with
   (it holds its caller's own unit and needs no licence at all) *)
Lemma ireg_ref_ok_ty0 (r rc n : nat) (c : ctyUR) (d : dinode) :
  ireg_ref_ok r rc n c d -> bv_unsigned (di_type d) = 0 ->
  r = 0%nat /\ rc = 0%nat.
Proof. intros [_ [H _]]. exact H. Qed.

Lemma ireg_ref_ok_alloc (r rc n : nat) (c : ctyUR) (d : dinode) :
  ireg_ref_ok r rc n c d -> (1 <= r + rc)%nat ->
  bv_unsigned (di_type d) <> 0.
Proof.
  intros [_ [H _]] Hge H0. destruct (H H0) as [-> ->]. cbn in Hge. lia.
Qed.

(* (R3) -- THE PIN, and its contrapositive, which is the form §5'.3's
   withdraw uses *)
Lemma ireg_ref_ok_claim (r rc n : nat) (c : ctyUR) (d : dinode) :
  ireg_ref_ok r rc n c d -> c <> None -> r = 0%nat.
Proof. intros [_ [_ H]]. exact H. Qed.

Lemma ireg_ref_ok_unclaimed (r rc n : nat) (c : ctyUR)
    (d : dinode) :
  ireg_ref_ok r rc n c d -> (1 <= r)%nat -> c = None.
Proof.
  intros [_ [_ H]] Hge. destruct c as [x |]; [| reflexivity].
  rewrite (H ltac:(discriminate)) in Hge. lia.
Qed.

(* THE WITHDRAW's RETIRE: dropping the claim only makes (R3) vacuous. *)
(* ---- RULING C''s RETIRE, AS ARITHMETIC (iclaim-ledger.md §5''''') -------

   THE CONVERSION at [ireg_withdraw]'s [ClaimK] arm: the claimant's
   claim-flavoured unit is spent ([rc] drops by one), a plain one is minted
   ([r] rises by one) and the c column retires -- all against the LANDED
   (R1) [r + rc <= n], which is exactly what makes the move free.  The
   [1 <= n] that §5''''-C's [cbit] route could not produce (its own probe
   refuted it at [n = 0]) is a COROLLARY here: a claim-flavoured unit in
   hand IS [1 <= rc], and (R1) turns that into [1 <= n].  Ported verbatim
   from the 7b' executor's probe ([probe_Cprime_retire] /
   [probe_Cprime_count]). *)
Lemma ireg_ref_ok_retire (r rc n : nat) (c : ctyUR) (d : dinode) :
  ireg_ref_ok r (S rc) n c d ->
  bv_unsigned (di_type d) <> 0 ->
  ireg_ref_ok (S r) rc n None d.
Proof.
  intros [H1 [_ _]] Hnz. rewrite /ireg_ref_ok.
  split_and!;
    [ lia
    | intros H0; destruct (Hnz H0)
    | intros Hne; destruct (Hne eq_refl) ].
Qed.

Lemma ireg_ref_ok_rc_count (r rc n : nat) (c : ctyUR) (d : dinode) :
  ireg_ref_ok r rc n c d -> (1 <= rc)%nat -> (1 <= n)%nat.
Proof. intros [H1 _] Hrc. lia. Qed.

Lemma ireg_ref_ok_unclaim (r rc n : nat) (c : ctyUR) (d : dinode) :
  ireg_ref_ok r rc n c d -> ireg_ref_ok r rc n None d.
Proof.
  intros [H1 [H2 _]]. rewrite /ireg_ref_ok. split_and!;
    [exact H1 | exact H2 | intros Hne; destruct (Hne eq_refl)].
Qed.

(* PRESERVATION.  A flush that keeps the type keeps the whole clause. *)
Lemma ireg_ref_ok_stable (r rc n : nat) (c : ctyUR)
    (d d' : dinode) :
  di_type d' = di_type d ->
  ireg_ref_ok r rc n c d -> ireg_ref_ok r rc n c d'.
Proof. intros Hty [H1 [H2 H3]]. rewrite /ireg_ref_ok Hty. split_and!; assumption. Qed.

(* ...and so does a move of the COUNT alone upwards ([ireg_freeze_au] does
   not move it at all; this is the shape the phase step needs) *)
Lemma ireg_ref_ok_count (r rc n n' : nat) (c : ctyUR)
    (d : dinode) :
  (n <= n')%nat -> ireg_ref_ok r rc n c d -> ireg_ref_ok r rc n' c d.
Proof. intros Hle [H1 [H2 H3]]. rewrite /ireg_ref_ok. split_and!; [lia | exact H2 | exact H3]. Qed.

(* THE CLAIM's ESTABLISH ([ireg_claim_au]): (R3) comes from (R2) at the OLD,
   type-0 record and the new record's nonzero type makes (R2) vacuous. *)
Lemma ireg_ref_ok_claim_mint (r rc n : nat) (d d' : dinode)
    (c' : ctyUR) :
  ireg_ref_ok r rc n None d ->
  bv_unsigned (di_type d) = 0 ->
  bv_unsigned (di_type d') <> 0 ->
  ireg_ref_ok r rc n c' d'.
Proof.
  intros Hok Ht0 Hnz.
  destruct (ireg_ref_ok_ty0 r rc n None d Hok Ht0) as [-> ->].
  rewrite /ireg_ref_ok. split_and!; [lia | intros H0; destruct (Hnz H0) | intros _; reflexivity].
Qed.

(* THE MINTS ([IcacheInv]'s three up-count writes): one unit and one count,
   together.  The plain flavour owes [c = None] -- that is what
   [IgetLic.iname_not_claimed] buys at iget and what the caller's own unit
   buys at idup; the claim flavour owes nothing, since (R3) names [r]. *)
Lemma ireg_ref_ok_mint (b : bool) (r rc n : nat) (c : ctyUR)
    (d : dinode) :
  ireg_ref_ok r rc n c d ->
  bv_unsigned (di_type d) <> 0 ->
  (b = false -> c = None) ->
  ireg_ref_ok (IcacheRef.rup b r) (IcacheRef.rcup b rc) (S n) c d.
Proof.
  intros [H1 [H2 H3]] Hnz Hc. rewrite /ireg_ref_ok /IcacheRef.rup /IcacheRef.rcup.
  destruct b.
  - split_and!; [lia | intros H0; destruct (Hnz H0) | intros Hcn; exact (H3 Hcn)].
  - split_and!; [lia | intros H0; destruct (Hnz H0) |].
    intros Hcn. exfalso. exact (Hcn (Hc eq_refl)).
Qed.

(* ...AND THE SPENDS (iput's two closes): the mirror, and it owes nothing --
   both columns only ever go down. *)
Lemma ireg_ref_ok_spend (b : bool) (r rc n : nat) (c : ctyUR)
    (d : dinode) :
  ireg_ref_ok (IcacheRef.rup b r) (IcacheRef.rcup b rc) (S n) c d ->
  ireg_ref_ok r rc n c d.
Proof.
  rewrite /ireg_ref_ok /IcacheRef.rup /IcacheRef.rcup.
  intros [H1 [H2 H3]]. destruct b.
  - split_and!; [lia | intros H0; destruct (H2 H0) as [Ha Hb]; split; lia
                 | intros Hcn; exact (H3 Hcn)].
  - split_and!; [lia | intros H0; destruct (H2 H0) as [Ha Hb]; split; lia
                 | intros Hcn; pose proof (H3 Hcn); lia].
Qed.

(* the MARKED arm's pure content, widened by the claim's other half: a slot
   whose record is checked out of the region carries no claim. *)
Definition ireg_marked_ok (c : ctyUR) (d : dinode) : Prop :=
  bv_unsigned (di_type d) <> 0 /\ c = None.

(* THE FREEZE PIN (§2.3, as AMENDED by the ZZProbeIcnt probe).  Phased:
   [FrzPre] is the window before iput+0x8a's last close and pins the
   in-core count at ONE (that is §1.1's B1 payout -- the [cnt2 >= 2] arm at
   [IputFreeLockedDev.v:1034] dies on a pin read); [FrzPost] is after it and
   pins the count at ZERO.  [FrzOff] is the unfrozen state and pins nothing.

   THE RECORD CONJUNCTS, LANDED (iclaim-ledger.md §3.1, RULING A -- this
   SUPERSEDES increment I's count-only deviation, which the header used to
   record here).  §2.3's [di_nlink d = 0 /\ di_type d <> 0] are now spelled
   at BOTH phases, and they are what makes §2.6's licence table
   implementable at all: with the pin count-only there was nothing for
   [LinkedL] / [HeldL] / [RootL] to contradict (increment IIIb's wall (A)).
   The nlink conjunct is the contradiction surface for those three rows; the
   type conjunct refutes a freeze at a claim/free box and is what
   [ireg_claim_au] reads to establish [ireg_claim_ok]'s new f clause.

   THE TWO MOVERS IIIb PRICED AS BLOCKERS, PAID.  [ireg_write_link_fl]
   raises [di_nlink] off zero, so it takes a new pure premise
   [bv_unsigned (di_nlink dn) <> 0] and the pin's contrapositive
   ([ireg_frz_ok_nz]) then refutes frozen outright -- one premise, in hand at
   its one raising site.  [EscrowDeposit.ireg_free_deposit_au] writes [di_type = 0] over a frozen
   slot, which is exactly iput's own free: it now TAKES [ifreeze_post] and
   RETIRES it in the same move, so the [FrzPost] arm dissolves as the type
   goes to zero.  Every other arm mover re-establishes the pin for free
   (§3.1's cost table).

   [None] IS NOW REFUTED, not vacuous.  Boot mints [Some (Excl FrzOff)] at
   every slot ([IcacheBoot.icache_boot]) and every mover steps the column
   [Some -> Some], so "the f column is present" is a free invariant -- and it
   is what lets the licence table conclude the DESIGN's [f = Some (Excl
   FrzOff)] rather than a two-way disjunction every consumer would have to
   case on. *)
(* ---- THE FREEZE MIRROR's CLAUSE (iclaim-ledger.md §3.16, RULING A⁗) ----

   The pure half of [ireg_frzc] below: the region's mirror bit READS the f
   column.  Both directions are used, and by the same reader from opposite
   ends: (→) is what makes the mint's [false] half refute "someone else is
   already freezing this inum" (S1a), (←) is what makes the freezer's
   [ifreeze_pre] force [islot2]'s arm onto its frozen-park disjunct at
   iput+0x8a (S1b) and what kills a foreign idup at a [FrzPre] inum (2.6b).

   Re-establishing it costs nothing at any mover that does not step f, and at
   the three that do it is derivable from the old clause alone: the mint flips
   [false -> true] with both halves in hand, the [FrzPre -> FrzPost] step flips
   back, and the retire ([FrzPost -> FrzOff]) reads [b = false] off the old
   clause and keeps it. *)
(* RULING G' (iclaim-ledger.md §6''): stated at [frz_preb] rather than at the
   equation [f = Some (Excl FrzPre)], which no longer determines the column
   now that the phase carries the regime index.  The clause is exactly the
   same fact; every consumer discharges it by [reflexivity] at a concrete
   column where it used to say [discriminate]. *)
Definition ireg_frzm_ok (b : bool) (f : frzUR) : Prop :=
  b = frz_preb f.

Lemma ireg_frzm_ok_false (f : frzUR) :
  frz_preb f = false -> ireg_frzm_ok false f.
Proof. intros Hne. rewrite /ireg_frzm_ok Hne. reflexivity. Qed.

Lemma ireg_frzm_ok_true (rg : frzidx) :
  ireg_frzm_ok true (Some (Excl (FrzPre rg))).
Proof. reflexivity. Qed.

(* the one direction every DECIDER uses: at [FrzPre] the bit is up *)
Lemma ireg_frzm_ok_pre (b : bool) (f : frzUR) :
  ireg_frzm_ok b f -> frz_preb f = true -> b = true.
Proof. intros -> Hf. exact Hf. Qed.

Definition ireg_frz_ok (f : frzUR) (n : nat) (d : dinode) : Prop :=
  match f with
  | Some (Excl FrzOff)  => True
  | Some (Excl (FrzPre _))  => bv_unsigned (di_nlink d) = 0
                           /\ bv_unsigned (di_type d) <> 0
                           /\ n = 1%nat
  | Some (Excl (FrzPost _)) => bv_unsigned (di_nlink d) = 0
                           /\ bv_unsigned (di_type d) <> 0
                           /\ n = 0%nat
  | _                   => False   (* [ExclBot], and the absent column *)
  end.

(* ...AND THE ONE THE MIRROR TURNS INTO A REFUTATION (iclaim-ledger.md
   §3.16).  A mover holding the mirror's [false] half knows the column is not
   [FrzPre]; if it also holds a count fragment at ONE OR MORE -- which every
   mover at a CACHED slot does, [islot2]'s live arm being at
   [Pos.to_nat n] -- then [FrzPost]'s own pin (count zero) is refuted too and
   the column is [FrzOff], at which the pin is vacuous at any new count.
   That is the whole of the licence-free up-count A⁗ buys ([ProofIdup]'s
   OPEN(2.6b)): no [iname], no arithmetic [2 <= n]. *)
Lemma ireg_frz_ok_not_pre (f : frzUR) (n : nat) (d : dinode) :
  (1 <= n)%nat -> frz_preb f = false -> ireg_frz_ok f n d ->
  f = Some (Excl FrzOff).
Proof.
  intros Hn Hne Hok. rewrite /ireg_frz_ok in Hok.
  destruct f as [[ph |] |]; [| destruct Hok | destruct Hok].
  destruct ph as [| rg | rg]; [reflexivity | discriminate Hne |].
  destruct Hok as (_ & _ & Hz). exfalso. lia.
Qed.

(* the unfrozen state pins nothing, at any count and any record *)
Lemma ireg_frz_ok_off (n : nat) (d : dinode) :
  ireg_frz_ok (Some (Excl FrzOff)) n d.
Proof. exact I. Qed.

(* A MOVER THAT MOVES NEITHER COUNT NOR RECORD-PIN CARRIES THE CLAUSE.  The
   ordinary flush is exactly this: [di_nlink_stable]'s equation and
   [di_type_stable]'s dead left disjunct. *)
Lemma ireg_frz_ok_stable (f : frzUR) (n : nat) (d d' : dinode) :
  di_nlink d' = di_nlink d ->
  di_type d' = di_type d ->
  ireg_frz_ok f n d -> ireg_frz_ok f n d'.
Proof.
  intros Hnl Hty. rewrite /ireg_frz_ok Hnl Hty. exact id.
Qed.

(* THE TWO CONTRAPOSITIVES, and they are the whole mechanism §2.6 asks for:
   a record that is NAMED, or a record that is FREE, cannot be mid-transition
   -- so the pin re-establishes at ANY record and ANY count. *)
Lemma ireg_frz_ok_nz (f : frzUR) (n : nat) (d : dinode) :
  bv_unsigned (di_nlink d) <> 0 -> ireg_frz_ok f n d ->
  f = Some (Excl FrzOff).
Proof.
  intros Hnz Hok. rewrite /ireg_frz_ok in Hok.
  destruct f as [[ph |] |]; [| destruct Hok | destruct Hok].
  destruct ph;
    [ reflexivity
    | exfalso; exact (Hnz (proj1 Hok))
    | exfalso; exact (Hnz (proj1 Hok)) ].
Qed.

Lemma ireg_frz_ok_ty0 (f : frzUR) (n : nat) (d : dinode) :
  bv_unsigned (di_type d) = 0 -> ireg_frz_ok f n d ->
  f = Some (Excl FrzOff).
Proof.
  intros Hz Hok. rewrite /ireg_frz_ok in Hok.
  destruct f as [[ph |] |]; [| destruct Hok | destruct Hok].
  destruct ph;
    [ reflexivity
    | exfalso; exact (proj1 (proj2 Hok) Hz)
    | exfalso; exact (proj1 (proj2 Hok) Hz) ].
Qed.

(* ...and the arithmetic one, which is the count-only backstop increment II's
   not-last closer already runs on (a slot at two or more references is at
   neither phase, whatever its record says). *)
Lemma ireg_frz_ok_ge2 (f : frzUR) (n : nat) (d : dinode) :
  (2 <= n)%nat -> ireg_frz_ok f n d -> f = Some (Excl FrzOff).
Proof.
  intros Hge Hok. rewrite /ireg_frz_ok in Hok.
  destruct f as [[ph |] |]; [| destruct Hok | destruct Hok].
  destruct ph;
    [ reflexivity
    | exfalso; pose proof (proj2 (proj2 Hok)); lia
    | exfalso; pose proof (proj2 (proj2 Hok)); lia ].
Qed.

(* the packaged consequence every consumer of the three above wants next *)
Lemma ireg_frz_ok_of_off (f : frzUR) (n : nat) (d : dinode) :
  f = Some (Excl FrzOff) -> ireg_frz_ok f n d.
Proof. intros ->. exact I. Qed.

(* THE PHASE STEP (iput+0x8a's last close, §2.3 as the probe corrected it).
   The two RECORD conjuncts are the same two at both phases, so a mover that
   already holds the pin re-establishes it at the other phase by supplying
   only the new COUNT -- which is the whole reason the freeze is phased
   rather than strict.  The third premise is what keeps the unfrozen column
   unfrozen: a mover may not mint a freeze by stepping [FrzOff] onwards
   (that is [ireg_freeze_au]'s job, and it pays the record premises). *)
Lemma ireg_frz_ok_phase (ph ph' : frz) (n n' : nat) (d : dinode) :
  ireg_frz_ok (Some (Excl ph)) n d ->
  (ph = FrzOff -> ph' = FrzOff) ->
  (forall rg, ph' = FrzPre rg -> n' = 1%nat) ->
  (forall rg, ph' = FrzPost rg -> n' = 0%nat) ->
  ireg_frz_ok (Some (Excl ph')) n' d.
Proof.
  intros Hok Hoff H1 H0.
  destruct ph' as [| rg' | rg']; [exact I | |].
  - destruct ph;
      [ exfalso; discriminate (Hoff eq_refl)
      | split_and!;
          [exact (proj1 Hok) | exact (proj1 (proj2 Hok)) | exact (H1 rg' eq_refl)]
      | split_and!;
          [exact (proj1 Hok) | exact (proj1 (proj2 Hok)) | exact (H1 rg' eq_refl)] ].
  - destruct ph;
      [ exfalso; discriminate (Hoff eq_refl)
      | split_and!;
          [exact (proj1 Hok) | exact (proj1 (proj2 Hok)) | exact (H0 rg' eq_refl)]
      | split_and!;
          [exact (proj1 Hok) | exact (proj1 (proj2 Hok)) | exact (H0 rg' eq_refl)] ].
Qed.

(* TYPE STABILITY (fs-icache.md §19.6 Part 1, fs-sysfile S5d).  "A flush
   either CLEARS an inode's type or leaves it exactly where it was" -- the
   premise [ireg_write_au] gained so that §19.1(i)'s retype is refuted by
   the REGION rather than by a survey of this tree's callers.

   NAMED, not written inline, for two reasons.  (i) Every consumer spells
   it in a premise list that also has to travel through [SpecIupdate]'s
   three bodies and every proof that threads them, and a named predicate
   is what keeps that a one-token edit (durable-notes: keep a side
   condition in one named, Ltac-dischargeable predicate).  (ii) A raw
   [\/] does not even PARSE in those premise lists: a [_body] definition
   is elaborated in [bi_scope] (that is what makes the trailing bare [WP e]
   legal, RiscvPtsto.v:1470), and [bi_scope] has [∨] for [bi_or] and no
   [\/] at all -- the failure surfaces as a syntax error at the body's
   final [WP], a hundred lines below the disjunction. *)
Definition di_type_stable (dn' dn : dinode) : Prop :=
  bv_unsigned (di_type dn') = 0 \/ di_type dn' = di_type dn.

(* The two ways every caller in the tree discharges it. *)
Lemma di_type_stable_eq (dn' dn : dinode) :
  di_type dn' = di_type dn -> di_type_stable dn' dn.
Proof. intros H. right. exact H. Qed.

Lemma di_type_stable_zero (dn' dn : dinode) :
  bv_unsigned (di_type dn') = 0 -> di_type_stable dn' dn.
Proof. intros H. left. exact H. Qed.

Lemma di_type_stable_refl (dn : dinode) : di_type_stable dn dn.
Proof. right. reflexivity. Qed.

(* NLINK STABILITY (fs-icache.md §20.6's "ordinary iupdate" and "iput's
   free" rows, fs-sysfile S5f).  The link ledger's (L1) clause caps the
   count of live directory records naming an inum by that inum's [nlink],
   and (L3) says a FREE record's [nlink] is zero -- so the region can only
   re-establish both across a flush if the flush is told two things about
   the record it writes:

     the FIRST conjunct -- [nlink] does not MOVE.  Without it any holder
     of [dinode_at] could lower [nlink] under an outstanding register
     fragment; with it, "a fragment outstanding implies [nlink >= 1]" is a
     theorem of the region rather than a survey of this tree's callers.  It is an EQUALITY and not "does not fall", because
     that is what every discharge site in the tree actually has: no writer
     that goes through the ordinary flush moves [nlink] at all, so
     [di_nlink_stable_refl] / [di_nlink_stable_free] take the equation as
     input already and the two consumers below become rewrites.
     sys_unlink's decrement is the ONE writer that moves an [nlink], and it
     does not go through the ordinary flush at all -- it goes through
     [ireg_write_unlink], which pays for the drop by CONSUMING a fragment.

     the SECOND conjunct -- a flush that CLEARS the type leaves [nlink]
     at zero.  That is iput's free path, whose C-level guard is literally
     [ip->nlink == 0], and it is what lets [EscrowDeposit.ireg_free_deposit_au] derive [w = 0]
     -- i.e. "a free inode is named by no live directory record" --
     INSIDE the region, with no caller obligation at all (§20.9(c)).

   NAMED for [di_type_stable]'s two reasons verbatim: it travels through
   [SpecIupdate]'s three bodies and every contract that holds the region's
   record at a stale index, and a raw [/\] in a [_body] premise list is
   elaborated in [bi_scope].

   BOTH CONJUNCTS ARE NOW STATED (fs-sysfile S5g).  S5f landed the first
   one alone and this comment describing two, because the second was not
   dischargeable anywhere: iput's free path is its only non-vacuous
   instance, and iput's proof had lost the record it reads [ip->nlink]
   off.  §20.14's (R1) -- [IcacheEscrow.ic_open_held] made
   record-parametric -- restores it, and the second conjunct is what
   carries the C-level [ip->nlink == 0] guard into the region, where
   (L3) turns it into "a free inode is named by no live directory
   record".  It costs THREE discharge sites in the whole tree; every
   contract that merely carries the premise is untouched. *)
Definition di_nlink_stable (dn' dn : dinode) : Prop :=
  di_nlink dn' = di_nlink dn
  /\ (bv_unsigned (di_type dn') = 0 -> bv_unsigned (di_nlink dn') = 0).

(* The three ways every caller in the tree discharges it.  The first two
   are one token at an ORDINARY writer: no writer at or below iupdate moves
   [nlink] at all -- writei, itrunc, dirlink and filewrite all rebuild the
   record with [di_nlink d] verbatim -- and every one of them holds
   [inode_ok]'s nonzero type, which makes the second conjunct vacuous. *)
Lemma di_nlink_stable_eq (dn' dn : dinode) :
  di_nlink dn' = di_nlink dn ->
  bv_unsigned (di_type dn') <> 0 ->
  di_nlink_stable dn' dn.
Proof.
  intros Heq Hnz. rewrite /di_nlink_stable.
  split; [exact Heq | intros H0; exfalso; exact (Hnz H0)].
Qed.

Lemma di_nlink_stable_refl (dn : dinode) :
  bv_unsigned (di_type dn) <> 0 -> di_nlink_stable dn dn.
Proof. intros Hnz. exact (di_nlink_stable_eq dn dn eq_refl Hnz). Qed.

(* ...and the THIRD is iput's free path, the one writer that clears a type.
   There the second conjunct is the whole point and the first rides on it:
   the flushed record carries the [nlink] iput tested at +0x40 and found
   zero, so both halves come out of that one zero. *)
Lemma di_nlink_stable_free (dn' dn : dinode) :
  di_nlink dn' = di_nlink dn ->
  bv_unsigned (di_nlink dn) = 0 ->
  di_nlink_stable dn' dn.
Proof.
  intros Heq Hz. rewrite /di_nlink_stable.
  split; [exact Heq | intros _; rewrite Heq; exact Hz].
Qed.

(* (L1)'s arithmetic steps, over plain [Z] and outside every section --
   durable-notes' rule, since the goals below have a [bv 32] in context and
   [lia]'s zify hook then answers "Cannot find witness".  The ordinary
   flush needs none of them: [di_nlink_stable]'s first conjunct is an
   EQUALITY, so [ireg_write_au] carries (L1) by rewriting.  What is left
   here is the LINK/UNLINK arithmetic, where [nlink] really does move. *)
Lemma ireg_wle_zero (a : Z) (w : nat) :
  (w <= Z.to_nat a)%nat -> a = 0 -> w = 0%nat.
Proof. intros H Ha. subst a. cbn in H. lia. Qed.

Lemma ireg_wle_succ (a b : Z) (w : nat) :
  0 <= b -> (S w <= Z.to_nat a)%nat -> a = b + 1 -> (w <= Z.to_nat b)%nat.
Proof. lia. Qed.

Lemma ireg_wle_plus (a b : Z) (w : nat) :
  0 <= a -> (w <= Z.to_nat a)%nat -> b = a + 1 -> (S w <= Z.to_nat b)%nat.
Proof. lia. Qed.

(* ...and the side condition all four of them take.  Named because every
   arm move needs it and [lia] cannot see it: a [bv 16]'s non-negativity is
   a fact about the type, not arithmetic in the goal. *)
Lemma di_nlink_nonneg (d : dinode) : 0 <= bv_unsigned (di_nlink d).
Proof. exact (proj1 (bv_unsigned_in_range _ (di_nlink d))). Qed.

(* ---- THE ROOT INUM, AT THE REGION'S OWN KEY TYPE -----------------------

   THE INUM IS A LITERAL at the region's own key type, for the reason
   [ireg_link_ok]'s 32767 and [ireg_bi]'s 16 are: [InodeInv.ROOTINO] is
   [mword_of_int 1 : mword 32] and [bv_unsigned] of it is this number, but
   importing [InodeInv] would put the whole in-core inode geometry (and
   [Kernel.KernelSyms]) underneath a file 350 dependents deep.  The bridge
   is [IregLinkNz.ireg_root_ROOTINO], one [reflexivity].

   WHAT IT IS FOR.  "The root is allocated, and stays allocated" is a
   reading of the COUNTING RA, not of a maintained pure clause: the region
   parks one unspendable keep-alive token at this inum ([ireg_keep]), and
   [ireg_lnk_root_alive] / [ireg_lnk_root_min2] read the root's minimum off
   [FsStateLink.link_auth_toks_le].  Nothing else needs the constant.

   Stated OUTSIDE the section for [ireg_wle_*]'s reason (a [bv 32] in the
   section context breaks [lia]'s zify hook). *)
Definition ireg_root : Z := 1.

(* THE DIRECTORY TYPE at the region's own key type, for exactly
   [ireg_root]'s reason: [DirView.T_DIR_z] is [1], but importing [DirView]
   here would put the directory-view geometry underneath a file with ~350
   dependents for one constant.  The bridge is one [reflexivity].

   LANE G6 DELETED THE THREE CLAUSES THAT USED TO STAND HERE -- (T1)
   [0 < wd -> di_type d = T_DIR], (T1') [di_type d = T_DIR -> wl = 0] and
   [ireg_par_ok], the parent register's iff.  All three were readings of the
   OLD LINK LEDGER's columns; a dirent's own type-register fragment reveals
   its target's type directly now (fs-state.md §6½). *)
Definition ireg_dir_ty : Z := 1.

(* ...and the other two, for (L5) below, spelled the same way and for
   [ireg_dir_ty]'s reason verbatim: [DirView.T_DIR_z] and [FsImg.T_FILE_z] /
   [T_DEVICE_z] live in files this one does not import, the three values are
   equal by [reflexivity], and a consumer that speaks the tree's names
   rewrites once ([ireg_ty_names] below). *)
Definition ireg_file_ty : Z := 2.
Definition ireg_dev_ty : Z := 3.

(* (L5)'s statement, named so that the four movers and [ireg_withdraw]'s
   post all spell it once. *)
Definition ireg_ty_ok (d : dinode) : Prop :=
  bv_unsigned (di_type d) = 0 \/ bv_unsigned (di_type d) = ireg_dir_ty
  \/ bv_unsigned (di_type d) = ireg_file_ty
  \/ bv_unsigned (di_type d) = ireg_dev_ty.

(* ...and (L5) read off the TYPE WORD alone, which is what a contract
   above [SpecIalloc] can state without naming [ialloc_fresh]
   (durable-disk 2b-inode-3). *)
Definition ireg_ty_ok_w (t : mword 16) : Prop :=
  bv_unsigned t = 0 \/ bv_unsigned t = ireg_dir_ty
  \/ bv_unsigned t = ireg_file_ty \/ bv_unsigned t = ireg_dev_ty.

Lemma ireg_ty_ok_of_w (d : dinode) : ireg_ty_ok_w (di_type d) -> ireg_ty_ok d.
Proof. exact (fun H => H). Qed.

(* ---- (L4)'s ARITHMETIC, AND THE SIGNED/UNSIGNED CATCH IT EXISTS FOR ----

   xv6 117c0e7 guards both nlink-raising sites with [>= NLINK_MAX], which
   gcc compiles to [== 32767] because [nlink] is a SIGNED short and it knows
   the range.  The ledger's premise is UNSIGNED, and the two differ at
   [bv_unsigned = 65535] -- signed [-1] -- where the guard passes and the
   sixteen-bit [++] still wraps to zero.  So the guard alone does NOT close
   the increment ([ProofCreateParts.cr_nlink_guard_leaves_the_wrap] is the
   witness); what closes it is (L4), the range fact that a link count is a
   NON-NEGATIVE short, and the guard is exactly what makes (L4)
   PRESERVABLE.  That is what the kernel fix bought, and it is why (L4) is
   an INVARIANT and not a premise: no caller can name the record it is
   about (fs-sysfile.md's eleventh stop, the "no name for dp" objection).

   [ireg_nlink_bump] is stated as a CONJUNCTION on purpose: the first half
   is what [ireg_write_link] owes the ledger and the second is what it owes
   the invariant, and neither holds without the other's hypothesis -- the
   range alone would not survive the write, and the guard alone leaves the
   wrap.  One lemma, so a writer cannot take half of it. *)
Lemma ireg_nlink_step (h : mword 16) :
  bv_unsigned h <> 65535 ->
  bv_unsigned (add_vec h (mword_of_int 1 : mword 16)) = bv_unsigned h + 1.
Proof.
  intro Hne.
  pose proof (bv_unsigned_in_range _ h) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z in Hr.
  rewrite add_vec_unsigned.
  assert (H1 : bv_unsigned (mword_of_int 1 : mword 16) = 1)
    by (vm_compute; reflexivity).
  rewrite H1.
  apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z. lia.
Qed.

(* THE MACHINE'S [++], CROSSED WITH NO GUARD AT ALL.  A sixteen-bit
   increment raises the value by at most one -- true even at the wrap, which
   lands at zero.  (Lane G6 moved this pair and the one below here from
   the old link ledger's [dlc_bv_add1_le] / [_nz_eq]: they are arithmetic
   about
   [di_nlink]'s width and have nothing to do with the ledger that file
   carried.) *)
Lemma nlink_add1_le (h : mword 16) :
  bv_unsigned (add_vec h (mword_of_int 1 : mword 16)) <= bv_unsigned h + 1.
Proof.
  rewrite add_vec_unsigned.
  assert (H1 : bv_unsigned (mword_of_int 1 : mword 16) = 1)
    by (vm_compute; reflexivity).
  rewrite H1.
  pose proof (bv_unsigned_in_range _ h) as Hr.
  unfold bv_wrap. unfold bv_modulus in Hr |- *.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z
    in Hr |- *.
  apply Z.mod_le; lia.
Qed.

(* ...AND ITS EXACT FORM UNDER A NONZERO READ-BACK.  A sixteen-bit [++]
   wraps only at 65535, where it lands at ZERO -- so an increment whose
   result is known nonzero did not wrap.  The nonzero fact is the flush's
   own read-back ([IregLinkNz.ireg_tok_nz] at the bumped record). *)
Lemma nlink_add1_nz_eq (h : mword 16) :
  bv_unsigned (add_vec h (mword_of_int 1 : mword 16)) <> 0 ->
  bv_unsigned (add_vec h (mword_of_int 1 : mword 16))
  = bv_unsigned h + 1.
Proof.
  rewrite add_vec_unsigned.
  assert (H1 : bv_unsigned (mword_of_int 1 : mword 16) = 1)
    by (vm_compute; reflexivity).
  rewrite H1.
  pose proof (bv_unsigned_in_range _ h) as Hr.
  unfold bv_wrap. unfold bv_modulus in Hr |- *.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 16))%Z with 65536%Z
    in Hr |- *.
  intro Hnz.
  destruct (Z.eq_dec (bv_unsigned h) 65535) as [He | Hne].
  - exfalso. apply Hnz. rewrite He. vm_compute. reflexivity.
  - rewrite Z.mod_small; lia.
Qed.

Lemma ireg_nlink_bump (h : mword 16) :
  bv_unsigned h <= 32767 ->
  h <> (mword_of_int 32767 : mword 16) ->
  bv_unsigned (add_vec h (mword_of_int 1 : mword 16)) = bv_unsigned h + 1
  /\ bv_unsigned (add_vec h (mword_of_int 1 : mword 16)) <= 32767.
Proof.
  intros Hle Hne.
  assert (Hnz : bv_unsigned h <> 32767).
  { intro Hc. apply Hne. apply bv_eq. rewrite Hc. vm_compute. reflexivity. }
  assert (Hstep : bv_unsigned (add_vec h (mword_of_int 1 : mword 16))
                  = bv_unsigned h + 1) by (apply ireg_nlink_step; lia).
  split; [exact Hstep | rewrite Hstep; lia].
Qed.

(* THE MARKER'S KEY.  The claim box needs a per-inum EXCLUSIVE token whose
   two homes are the region invariant and a pool/entry marker; a second
   ghost name for it would have to appear in [ireg_inv] AND in
   the pool row, i.e. in [ic_escrow]'s arity, i.e. in every
   fs contract in the tree.  So it is filed in the region's OWN ghost map,
   at a key no inum can occupy: inums are [bv_unsigned]s and hence
   nonnegative, and [imark_key] lands strictly below zero.  The map's
   coupling ([ireg_couple]) speaks only about nonnegative keys, and no
   marker entry is ever updated -- only moved. *)
Definition imark_key (z : Z) : Z := -(z + 1).

Lemma imark_key_neg (z : Z) : 0 <= z -> imark_key z < 0.
Proof. rewrite /imark_key. lia. Qed.

Lemma imark_key_inj (z1 z2 : Z) : imark_key z1 = imark_key z2 -> z1 = z2.
Proof. rewrite /imark_key. lia. Qed.

Lemma imark_key_ne_slot (z : Z) (j i : nat) :
  0 <= z -> imark_key z <> (16 * Z.of_nat j + Z.of_nat i)%Z.
Proof. rewrite /imark_key. lia. Qed.

(* ===================================================================== *)
(*  3.  THE GHOST, AND WHAT A CALLER HOLDS                                *)
(* ===================================================================== *)

(* [iregG] -- one [ghost_mapG Σ Z dinode] -- is defined in
   Xv6Cameras.v; what a caller holds is below. *)

Section InodeRegion.
  (* [fsLinkG] since durable-disk 2b-inode-4: [ireg_slot] parks the link
     RA's per-inum authority.  This file binds MEMBERS, not the bundle, so
     the class goes here beside [fsTopG]; every consumer that binds
     [Xv6G.xv6G] resolves it through the bundle's own field. *)
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ, !fsTopG Σ, !fsLinkG Σ}.
  Context `{ICFG : icfg}.

  (* THE per-inum resource: this inum's on-disk record is [dn].  EXCLUSIVE
     (a full-fraction ghost_map element), keyed by the inum's value; the
     block address falls out of [IBLOCK] and never needs a second ghost.
     This is what replaces [fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
     (diblk_bytes ds)] in SpecIupdate / SpecIlock / SpecWritei /
     SpecItrunc / SpecFileread (§11.3). *)
  Definition dinode_at (γi : gname) (inum : bv 32) (dn : dinode) : iProp Σ :=
    bv_unsigned inum ↪[γi] dn.

  Global Instance dinode_at_timeless γi inum dn :
    Timeless (dinode_at γi inum dn).
  Proof. rewrite /dinode_at. apply _. Qed.

  Lemma dinode_at_excl γi inum dn1 dn2 :
    dinode_at γi inum dn1 -∗ dinode_at γi inum dn2 -∗ False.
  Proof.
    rewrite /dinode_at. iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hv).
  Qed.

  (* ...AND THE DISEQUALITY THAT READS OFF IT.  Two records held at once are
     two records: exclusivity at one key is the whole content of
     [dinode_at_excl], so a holder of both never has to argue that the
     inums differ from anything about the inodes.  create's mkdir arm is
     the first consumer -- the record it appends to the parent names the
     CHILD, and the count clause (V2) needs that record not to be the
     parent's own self record.  Pure conclusion, so [iDestruct .. as %H]
     leaves both fragments in place. *)
  Lemma dinode_at_ne γi (i1 i2 : bv 32) (dn1 dn2 : dinode) :
    dinode_at γi i1 dn1 -∗ dinode_at γi i2 dn2 -∗
      ⌜bv_unsigned i1 <> bv_unsigned i2⌝.
  Proof.
    rewrite /dinode_at. iIntros "H1 H2".
    destruct (decide (bv_unsigned i1 = bv_unsigned i2)) as [Heq | Hne].
    - rewrite Heq.
      iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
      exfalso. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hv).
    - iPureIntro. exact Hne.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE MARKER (§16.4's claim box, realised inside the region)          *)
  (* ------------------------------------------------------------------ *)

  (* The per-inum token that says "this inum's record fragment is NOT in
     the region".  EXACTLY ONE of [imark γi z] and [z ↪[γi] d] sits inside
     the region invariant at any time, and the other one is outside: with
     the fragment in, the marker is out (in a pool entry, in a parked
     unloaded payload, or in iput's hand between its free-flush and its
     park); with the fragment out (a pool bundle, an [ic_loaded], a
     holder), the marker is in.

     That is what makes ilock's fill EXHAUSTIVE.  §16.4 argues the
     exhaustiveness informally -- "out of the region and not in any
     ic_loaded forces the box" -- but that argument is a uniqueness claim
     about the whole itable and needs the itable lock, which the fill does
     not hold.  The marker turns it into a one-line ghost refutation: the
     filler HOLDS the marker, so the out-of-region arm is inconsistent and
     the fragment must still be in the region. *)
  Definition imark (γi : gname) (z : Z) : iProp Σ :=
    (∃ d : dinode, imark_key z ↪[γi] d)%I.

  Global Instance imark_timeless γi z : Timeless (imark γi z).
  Proof. rewrite /imark. apply _. Qed.

  Lemma imark_excl γi z : imark γi z -∗ imark γi z -∗ False.
  Proof.
    rewrite /imark. iIntros "(%d1 & H1) (%d2 & H2)".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hv).
  Qed.

  (* WHAT A CALLER GETS BACK FROM A FLUSH.  iupdate's postcondition is the
     retagged fragment when the flushed record is allocated, and the MARKER
     when it is free ([ProofIput]'s [ip->type = 0; iupdate(ip)] path, which
     is the one site that hands an inode back to the free pool).  Stated as
     one conditional resource so iupdate keeps ONE contract. *)
  Definition ireg_out (γi : gname) (inum : bv 32) (dn : dinode) : iProp Σ :=
    (if decide (bv_unsigned (di_type dn) = 0)
     then imark γi (bv_unsigned inum)
     else dinode_at γi inum dn)%I.

  Lemma ireg_out_alloc γi inum dn :
    bv_unsigned (di_type dn) <> 0 ->
    dinode_at γi inum dn -∗ ireg_out γi inum dn.
  Proof. intros H. rewrite /ireg_out decide_False; [by iIntros "$" | exact H]. Qed.

  Lemma ireg_out_alloc_inv γi inum dn :
    bv_unsigned (di_type dn) <> 0 ->
    ireg_out γi inum dn -∗ dinode_at γi inum dn.
  Proof. intros H. rewrite /ireg_out decide_False; [by iIntros "$" | exact H]. Qed.

  Lemma ireg_out_free_inv γi inum dn :
    bv_unsigned (di_type dn) = 0 ->
    ireg_out γi inum dn -∗ imark γi (bv_unsigned inum).
  Proof. intros H. rewrite /ireg_out decide_True; [by iIntros "$" | exact H]. Qed.

  (* ------------------------------------------------------------------ *)
  (*  The invariant                                                      *)
  (* ------------------------------------------------------------------ *)

  (* slot [i] of block [bi]'s parked list is the map's value at the inum
     that lives there *)
  Definition ireg_couple (m : gmap Z dinode) (bi : nat) (ds : list dinode)
    : Prop :=
    forall i : nat, (i < 16)%nat ->
      m !! (16 * Z.of_nat bi + Z.of_nat i)%Z = Some (ds !!! i).

  (* THE PER-SLOT ARM (§16.3's conditional conjunct, completed by §16.4).
     A FREE record's fragment lives here, which is what gives ialloc's
     claim a fragment to retag under the only lock it actually holds -- the
     BUFFER (§16.2).  A CLAIMED record's fragment lives here too, at the
     [fresh_shape] ialloc's memset+store leaves: that is the claim box, and
     it is where the first ilock fill picks the fragment up.  Everything
     else -- an allocated inum's pool bundle, an [ic_loaded], a critical
     section's checked-out record -- keeps the fragment OUTSIDE, and leaves
     the marker here in its place. *)
  (* AND A NONZERO-TYPED IN ARM IS A STANDING CLAIM (durable-disk C-5).
     The IN arm's two shapes are a FREE record and a CLAIM BOX, and the box
     is exactly the state in which the c column is [Some] -- ialloc's write
     mints the claim in the same ghost step ([ireg_claim_au]) and the fill's
     [ireg_withdraw] retires it as the slot leaves this arm.  Recording that
     here is what lets a commit read [di_type d = 0] off the arm: the parked
     share [ireg_cpin] refutes [c <> None] at an empty [ln_tx] authority,
     and the left disjunct is then all that is left ([ireg_in_quiesce]).  It
     costs no mover anything -- the claim is the only writer of this arm at
     a nonzero type. *)
  Definition ireg_in (c : ctyUR) (d : dinode) : Prop :=
    bv_unsigned (di_type d) = 0 \/ (fresh_shape d /\ c <> None).

  Lemma ireg_in_free (c : ctyUR) (d : dinode) :
    bv_unsigned (di_type d) = 0 -> ireg_in c d.
  Proof. intros H. left. exact H. Qed.

  Lemma ireg_in_shape (c : ctyUR) (d : dinode) :
    ireg_in c d -> bv_unsigned (di_type d) <> 0 -> fresh_shape d.
  Proof.
    intros [H0 | [Hf _]] Hnz; [exfalso; exact (Hnz H0) | exact Hf].
  Qed.

  (* ...and its reading at a QUIESCENT ledger: with no claim standing the
     arm's record is free.  This is [FsCollect.col_region_slot_acc]'s whole
     step from "the region holds the record" to "the record is type 0". *)
  Lemma ireg_in_quiesce (c : ctyUR) (d : dinode) :
    c = None -> ireg_in c d -> bv_unsigned (di_type d) = 0.
  Proof.
    intros -> [H0 | [_ Hc]]; [exact H0 | exfalso; exact (Hc eq_refl)].
  Qed.

  (* THE PER-INUM RECORD CLAUSES (design §20.2's (L1)/(L3)).

     (L1) [w <= di_nlink d] IS GONE with the ledger column [w] it bounded
     (lane G6, fs-state.md §6½).  Its contrapositive was the whole point --
     an outstanding ticket forced [di_nlink >= 1] at the record the REGION
     holds -- and the type register says it directly instead
     ([FsStateLink.link_auth_toks_le] at [ireg_lnk], read by
     [IregLinkNz.ireg_tok_nz]).  (L3) still forces a nonzero TYPE from
     there, so "a reference implies an allocated inode" is unchanged.

     (L3) [di_type d = 0 -> di_nlink d = 0] -- a free record's link count
     is zero, which is what made (L1) collapse to [w = 0] there:
     **a free inode is named by no live directory record**, proved inside
     the region with no caller obligation at all.

     WHY THE CLAUSES ARE STATED HERE AND NOT AT THE PAYLOAD.  [d] is the
     ON-DISK record -- [ireg_couple] pins it to the parked block's bytes on
     BOTH arms -- so (L1) can be stated whether or not the fragment is
     checked out.  Park the authority with the record instead ([ic_loaded] /
     [ipool_alloc]) and the cap is stranded at every checkout: the ordinary
     fill would have to re-establish [w <= nlink] for a claim box
     ([nlink = 0]) and could not.  §20.9(c)/(d).

     THE KNOT THAT HELD THEM BACK, AND WHAT UNTIED IT (fs-sysfile S5f/S5g).
     (L1) and (L3) stand or fall together and their joint discharge lands
     on `ProofIput`:

       * [ireg_claim_au] must re-establish (L1) at the record ialloc
         writes, whose [nlink] is ZERO ([SpecIalloc.ialloc_fresh] models
         [memset(dip,0,64)]).  So it must show [w = 0] at the slot it
         claims, and its only handle is the type-0-ness its caller read out
         of the buffer -- i.e. it needs exactly (L3), "a free record's link
         count is zero", as an invariant.  ialloc never reads [nlink] and
         cannot supply it as a premise.
       * (L3) is preserved by every writer but ONE: the flush that CLEARS a
         type, i.e. iput's free path, which must show [di_nlink = 0] of the
         record it writes.  xv6 establishes exactly that -- the free is
         guarded by [ip->nlink == 0] at iput+0x40 -- but the PROOF used to
         lose it, re-opening the payload after [acquiresleep] as a FRESH
         existential with no link back to the record the halfword was read
         off.  [ity_shot] pins the TYPE across that window and nothing
         pinned [nlink].
       * and there is no ghost way round it: the ledger's authority may
         only be lowered by a frame-preserving update, so nothing can
         "clear" [w] for a record whose fragments are outstanding
         (§19.7's rule again).

     §20.14's (R1) supplies the missing fact at its source rather than
     working round it: [IcacheEscrow.ic_open_held] is record-parametric, so
     iput's free path carries its own [dn] across the sleeplock window, and
     [di_nlink_stable]'s second conjunct -- which this file always
     documented and S5f could not state -- carries the zero into
     [EscrowDeposit.ireg_free_deposit_au].  Both clauses then land with no caller obligation
     anywhere and no signature move: the six arm moves below each
     re-establish [ireg_link_ok] from what they already have.

     WHAT IS STILL NOT HERE: §20.2's (L2) [c <> None -> fresh_shape d] and
     the [c = None] half of (L3).  Neither is blocked by this knot; both
     wait on the CLAIM being minted at all, which is §20.5/§20.7's (M1)
     work -- the free cannot re-establish [c = None] without CONSUMING an
     [iclaim] it does not hold, and until something mints one there is
     nothing for a clause to say.  The [c] component rides unconstrained
     through every mover below, exactly as it did before.

     (L4) [di_nlink d <= 32767] -- a link count is a NON-NEGATIVE short.
     The clause the mkdir arm's [dp->nlink++] turned out to need and the
     twelfth stop found missing: xv6's guard is a SIGNED test and
     [wp_iupdate_link]'s premise is an unsigned one, so the guard alone
     leaves the wrap at 65535 (= signed -1) alive.  It is stated HERE for
     (L1)'s reason and one more: the record is the region's, and no caller
     can name it.  PRESERVATION is where the whole clause is paid for, and
     every arm move but one gets it free -- [di_nlink_stable] leaves the
     count alone, [fresh_shape] and the free write a zero, and the unlink
     LOWERS it.  The exception is [ireg_write_link], which is why that
     mover, alone of the six, takes a premise about the OLD count: the
     kernel's own guard, without which (L4) is not preservable at all. *)
  (* (L5) THE TYPE IS ONE OF THE FOUR (durable-disk 2b-inode-3).  It is
     [FsStateInode.inode_local]'s [inl_type], and it has no other producer:
     2b-inode-2 recorded it as coming from [ireg_wd_ty] "on the marker
     fill", which is FALSE as landed -- [ireg_wd_ty (ClaimK ty) d] is
     [di_type d = ty] with [ty] unconstrained, and at [PlainK] it is
     [True].  So the REGION is where it has to be maintained: it is the
     record's home, the image satisfies it ([FsImg.fio_type] at a live
     inode, type 0 at a free one) and every kernel writer writes one of the
     four.  Stated as a fourth clause of THIS predicate rather than as a
     new conjunct of [ireg_slot] because the six arm moves already
     re-establish [ireg_link_ok] of their new record, so nothing
     destructures differently and no [iSplitR] moves.  It is what makes
     [ireg_withdraw] able to pay [inode_local] at the claim box. *)
  (* LANE G6 DELETED (L1) [w <= di_nlink d] with the ledger column [w] it
     bounded (fs-state.md §6½): link counts are the type register's own
     multiplicity now, and [ireg_lnk] below is where the record's [nlink] is
     tied to it. *)
  Definition ireg_link_ok (d : dinode) : Prop :=
    (bv_unsigned (di_type d) = 0 -> bv_unsigned (di_nlink d) = 0)     (* L3 *)
    /\ bv_unsigned (di_nlink d) <= 32767                              (* L4 *)
    /\ ireg_ty_ok d.                                                  (* L5 *)

  (* (L4) read off without destructuring three ways -- the one clause a
     WRITER needs and the two above do not mention. *)
  Lemma ireg_link_ok_short (d : dinode) :
    ireg_link_ok d -> bv_unsigned (di_nlink d) <= 32767.
  Proof. intros (_ & H4 & _). exact H4. Qed.

  (* (L5) read off the same way -- what a fill needs of the record it is
     about to park ([FsStateEra.inode_rec_local]'s first component). *)
  Lemma ireg_link_ok_ty (d : dinode) :
    ireg_link_ok d -> ireg_ty_ok d.
  Proof. intros (_ & _ & H5). exact H5. Qed.

  (* ...and how every WRITER re-establishes it: a flush either clears the
     type or leaves it alone ([di_type_stable], the premise
     [ireg_write_au] / [ireg_write_link] / [ireg_write_unlink] already
     take), so (L5) rides for free at all three.  The claim is the one
     mover that writes a type out of nowhere, and it takes (L5) as its own
     premise. *)
  Lemma ireg_ty_ok_stable (dn' dn : dinode) :
    di_type_stable dn' dn -> ireg_link_ok dn -> ireg_ty_ok dn'.
  Proof.
    intros [H0 | Heq] Hlok; [by left |].
    rewrite /ireg_ty_ok Heq. exact (ireg_link_ok_ty dn Hlok).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE GROUP-ABSORPTION RECEIPT (fs-log.md §G.3/§G.14/§G.16/§G.17)    *)
  (* ------------------------------------------------------------------ *)

  (* WHY IT LIVES HERE AND NOT IN THE ESCROW.  §G.4 prices create's and
     unlink's freeing [iupdate] at ZERO for a caller that observed a
     NONZERO nlink under this sleeplock inside its own op; what makes that
     sound is that the zero it may now find was written AFTER the
     observation, hence inside the observer's still-live op -- whose epoch
     is frozen, commit requiring [out = 0] -- hence at the observer's own
     epoch, so [LogInv.log_use_group] turns the witness into membership of
     THIS batch's header.  §G.3 put the receipt on the icache's parked
     payload and §G.16 gated it on a per-generation one-shot; both are dead
     (§G.17): checkout and park are DIFFERENT FUNCTIONS, so the resource
     would have to cross through every caller holding a locked inode, and
     while a slot is checked out the escrow cannot name the record at all.
     The region can, always: [ireg_slot] HOLDS the record, [dinode_at] is
     the agreeing fragment every holder already carries, and the key is the
     INUM -- stable, so there is no recycle and no gate is needed.

     [icfg_iep] / [icfg_log] / [icfg_ist] are ambient for the reason
     [icfg_iref] is (§G.17's door 1): a tie between a threaded γ and a
     record field has to be sayable where both are in scope, which a body
     existential is not, and [ireg_inv]'s arity is fixed by 30-odd fs
     contracts.  The tie is the pure premise [⌜γ = icfg_log⌝] on the three
     contracts that mix the two, true at boot by [icfg_alloc]. *)
  Definition iblk_of (z : Z) : Z := z / 16 + icfg_ist.

  (* [IBLOCK] at the region's own key: the two are the same number, and
     stating the receipt over [z] is what keeps [ireg_slot]'s arity fixed. *)
  Lemma iblk_of_IBLOCK (inum : bv 32) :
    iblk_of (bv_unsigned inum) = IBLOCK inum icfg_ist.
  Proof. reflexivity. Qed.

  (* THE ⌜v = 0⌝ DISJUNCT IS THE BOOT CORNER, not slack: the mkfs image is
     full of FREE inodes (type 0, nlink 0) for which no witness exists or
     could exist, and every one of them sits at [v = 0] -- nobody has ever
     observed a nonzero nlink there.  It is refuted at the only place it
     must be, [ireg_ep_use], from [e0 <= v] and the genesis epoch being at
     least one (ProofInitlog); so a counter that has MOVED carries a real
     witness and one that has not was never observed. *)
  Definition izrcpt (z : Z) (d : dinode) (v : nat) : iProp Σ :=
    (⌜bv_unsigned (di_nlink d) = 0⌝ →
       ⌜v = 0%nat⌝ ∨
       ∃ e : nat, logged_at icfg_log e (iblk_of z) ∗ ⌜(v <= e)%nat⌝)%I.

  (* the per-inum observation counter, its epoch bound and its receipt *)
  Definition ireg_ep (z : Z) (d : dinode) : iProp Σ :=
    (∃ v : nat,
       mono_nat_auth_own (icfg_iep z) 1 v ∗
       log_epoch_lb icfg_log v ∗
       izrcpt z d v)%I.

  (* THE OBSERVER'S TOKEN (§G.13's ruled name at §G.17's key).  Persistent,
     so it survives the whole walk from the nlink guard to the iput with no
     linearity to manage; inum-keyed, so no generation index is needed. *)
  Definition nlz_obs (z : Z) (e0 : nat) : iProp Σ :=
    mono_nat_lb_own (icfg_iep z) e0.

  Global Instance izrcpt_timeless z d v : Timeless (izrcpt z d v).
  Proof. rewrite /izrcpt. apply _. Qed.

  Global Instance ireg_ep_timeless z d : Timeless (ireg_ep z d).
  Proof. rewrite /ireg_ep /izrcpt. apply _. Qed.

  Global Instance nlz_obs_persistent z e0 : Persistent (nlz_obs z e0).
  Proof. apply _. Qed.

  Global Instance nlz_obs_timeless z e0 : Timeless (nlz_obs z e0).
  Proof. apply _. Qed.

  (* BOOT: a counter at zero carries every record, free inodes included *)
  Lemma ireg_ep_intro (z : Z) (d : dinode) :
    mono_nat_auth_own (icfg_iep z) 1 0 ==∗ ireg_ep z d.
  Proof.
    iIntros "Ha". iMod (log_epoch_lb_0 icfg_log) as "#Hlb".
    iModIntro. iExists 0%nat. iFrame "Ha Hlb".
    rewrite /izrcpt. iIntros (_). iLeft. done.
  Qed.

  (* EVERY LANDED REGION WRITER CARRIES IT FOR FREE.  [di_nlink_stable]'s
     first conjunct says nlink does not MOVE across an ordinary flush, so a
     record can only BECOME zero if it already was -- and the old receipt is
     then literally the new one, at the same [v].  The claim, the free and
     the withdrawal are the same fact by their own premises.  The deposit
     ([ireg_ep_open] below) is therefore unreachable in the landed tree and
     exists for unlink's zero-writing iupdate, the first writer that will
     lower nlink at all. *)
  Lemma ireg_ep_mono (z : Z) (d d' : dinode) :
    (bv_unsigned (di_nlink d') = 0 -> bv_unsigned (di_nlink d) = 0) ->
    ireg_ep z d -∗ ireg_ep z d'.
  Proof.
    intros Hnl. iIntros "[%v (Ha & #Hlb & Hrc)]". iExists v. iFrame "Ha Hlb".
    rewrite /izrcpt. iIntros (Hz). iApply "Hrc". iPureIntro. exact (Hnl Hz).
  Qed.

  (* THE MINT (the nlink guard's shape, §G.4/§G.17).  An observer of a
     NONZERO nlink inside an op born at [e0] -- so it holds
     [log_epoch_lb γ e0], which rides [log_opSe] since §G.13 -- raises this
     inum's counter to [max v e0] and takes the bound.  The receipt is
     re-established VACUOUSLY, which is the whole reason the raise is free. *)
  Lemma ireg_ep_mint (z : Z) (d : dinode) (γ : log_names) (e0 : nat) :
    γ = icfg_log ->
    bv_unsigned (di_nlink d) <> 0 ->
    ireg_ep z d -∗ log_epoch_lb γ e0 ==∗ ireg_ep z d ∗ nlz_obs z e0.
  Proof.
    iIntros (Hγ Hnz) "[%v (Ha & #Hlb & _)] #Hlb0". subst γ.
    assert (Hmx : (v <= Nat.max v e0)%nat) by lia.
    iMod (mono_nat_own_update (Nat.max v e0) Hmx with "Ha") as "[Ha #Hub]".
    iAssert (log_epoch_lb icfg_log (Nat.max v e0)) as "#Hlbm".
    { destruct (Nat.max_spec v e0) as [[_ ->] | [_ ->]];
        [iExact "Hlb0" | iExact "Hlb"]. }
    iModIntro. iSplitR "".
    - iExists (Nat.max v e0). iFrame "Ha Hlbm".
      rewrite /izrcpt. iIntros (Hz). by exfalso.
    - rewrite /nlz_obs. iApply (mono_nat_lb_own_le e0 with "Hub"). lia.
  Qed.

  (* THE CONSUMPTION (G-3's crz premise).  The auth turns the observer's
     lower bound and the receipt's upper one into ONE comparison through the
     exact value -- two lower bounds on one counter are incomparable, which
     is §G.14's refutation of §G.3's pairing -- and the [⌜v = 0⌝] boot
     corner dies against [1 <= e0 <= v]. *)
  Lemma ireg_ep_use (z : Z) (d : dinode) (γ : log_names) (e0 : nat) :
    γ = icfg_log ->
    bv_unsigned (di_nlink d) = 0 ->
    (1 <= e0)%nat ->
    ireg_ep z d -∗ nlz_obs z e0 -∗
    ireg_ep z d ∗
    ∃ e : nat, ⌜(e0 <= e)%nat⌝ ∗ logged_at γ e (iblk_of z).
  Proof.
    iIntros (Hγ Hz He0) "[%v (Ha & #Hlb & #Hrc)] #Hob". subst γ.
    iDestruct (mono_nat_lb_own_valid with "Ha Hob") as %[_ Hle].
    iDestruct ("Hrc" $! Hz) as "[%Hv0 | (%e & #Hlg & %Hve)]".
    { exfalso. lia. }
    iSplitR "".
    - iExists v. iFrame "Ha Hlb". rewrite /izrcpt. iIntros (_).
      iRight. iExists e. iFrame "Hlg". iPureIntro. exact Hve.
    - iExists e. iFrame "Hlg". iPureIntro. lia.
  Qed.

  (* THE DEPOSITOR'S ACCESSOR.  A zero-writer reads the inum's [v] with its
     epoch bound, hands THAT to [SpecIupdate]'s credgen -- whose post is
     [∃ e, logged_at γ e (IBLOCK …) ∗ ⌜v <= e⌝], the comparison discharged
     inside [log_write] where the [ln_ep] auth is open (§G.17 blocker 4) --
     and closes at the record it wrote. *)
  Lemma ireg_ep_open (z : Z) (d : dinode) :
    ireg_ep z d -∗
    ∃ v : nat, log_epoch_lb icfg_log v ∗
      (∀ d' : dinode, izrcpt z d' v -∗ ireg_ep z d').
  Proof.
    iIntros "[%v (Ha & #Hlb & _)]". iExists v. iFrame "Hlb".
    iIntros (d') "Hrc". iExists v. iFrame "Ha Hlb". iExact "Hrc".
  Qed.

  (* THE ROOT CLAUSE RIDES HERE, not in [ireg_body] (§20.4 wrote it at the
     body, over [m !!! ROOTINO]).  It is stated STRICT -- [w < di_nlink] --
     and strictness names [w], which lives at the SLOT and nowhere else; and
     the per-slot form costs [ireg_body]'s destructuring nothing, so no
     consumer of the body moves.  A SEPARATE conjunct beside [ireg_link_ok]
     rather than a fourth conjunct inside it, because that predicate has
     consumers all over the tree reading it by projection. *)
  (* LANE G6: the pure block carries ONE clause, [ireg_link_ok].  Through
     G5 it carried five -- (L1) and the root clause at the ledger's ternary
     sum, (T1) at the d-sum, (T1') at [wl] and [ireg_par_ok] tying the
     parent register to the tagged count -- and all five went with the
     columns (fs-state.md §6½). *)
  (* OPTION A, STAGE 1b: the gate that demarcates the binary.  The current
     (free-under-lock) binary has NO off-lock free, so no slot is ever in the
     pending-free state; the reordered binary (Stage 3) redefines this to the
     real escrow-gated content and the pending arm becomes producible.
     RETIRED: the pending arm now holds the real [region_pending] (option A),
     produced by the reordered-iput deposit and refuted/redeemed pool-locally;
     the old [offlock_enabled]=[False] placeholder is gone. *)

  (* THE ARM MOVED INSIDE THE LEDGER's [∃] (iclaim-ledger.md §2.4), and that
     is the whole mechanism of the claim pin: the MARKED sub-arm can now say
     [c = None] ([ireg_marked_ok]), which is what lets every byte-writing
     mover -- each of which refutes the IN arm with the caller's own
     [dinode_at] -- re-establish [ireg_claim_ok] for free.  [ireg_ep] stays
     outside, so the destructuring pattern is [(ledger…arm) Hep] rather than
     the old [(ledger) [Hep arm]]. *)
  (* ---- THE RECEIPT + MIRROR CONJUNCT (§3.14 as built, §3.16's A⁗) ------

     ONE conjunct of [ireg_slot], carrying the two complementary handles on
     the f column that the free path's payload disjunction needs:

       * the RECEIPT ([frzown z], §3.14): parked here at EVERY phase but
         [FrzPre], so "a thread holds the receipt" IS "this inum reads
         [FrzPre]", by [frzown_excl] alone.  Hand-vs-region EXCLUSIVITY.
       * the MIRROR ([frzm_h z b] + [ireg_frzm_ok b f], §3.16): the region's
         half of a 1/2-1/2 bool whose other half rides under the ITABLE LOCK
         ([IcacheEscrow.islot2]'s live arm / the free pool's bundle), so a
         lock holder can READ the column without opening the region and,
         crucially, the arm can SELECT on it.  Region-vs-lock BRANCH
         SELECTION.

     They are packaged as ONE conjunct on purpose: [ireg_slot]'s arity and
     [ireg_slot_intro]'s are then unchanged by A⁗, so the thirty-odd sites
     that merely thread the receipt clause through a re-park are untouched
     and only the four that OPEN it (the mint, the phase step, the retire,
     boot) move. *)
  Definition ireg_frzc (z : Z) (f : frzUR) : iProp Σ :=
    ((⌜frz_preb f = true⌝ ∨ frzown z)
     ∗ (∃ b : bool, frzm_h z b ∗ ⌜ireg_frzm_ok b f⌝))%I.

  Global Instance ireg_frzc_timeless z f : Timeless (ireg_frzc z f).
  Proof. rewrite /ireg_frzc. apply _. Qed.

  Lemma ireg_frzc_intro (z : Z) (f : frzUR) (b : bool) :
    ireg_frzm_ok b f ->
    (⌜frz_preb f = true⌝ ∨ frzown z) -∗ frzm_h z b -∗ ireg_frzc z f.
  Proof.
    intros Hok. iIntros "Hr Hb". rewrite /ireg_frzc. iFrame "Hr".
    iExists b. iFrame "Hb". iPureIntro. exact Hok.
  Qed.

  (* THE RIDE-THROUGH PAIR.  Every mover in the tree but the mint and the
     [FrzPre -> FrzPost] step leaves the column OFF [FrzPre] at both ends, and
     for those the conjunct is a two-line peel-and-repark: the receipt is on
     its [frzown] arm and the mirror's bit is DOWN, at the old column and at
     the new one alike. *)
  Lemma ireg_frzc_off_acc (z : Z) (f : frzUR) :
    frz_preb f = false ->
    ireg_frzc z f -∗ frzown z ∗ frzm_h z false.
  Proof.
    intros Hne. iIntros "[Hr Hm]".
    iSplitL "Hr"; [iDestruct "Hr" as "[%Hbad | $]"; congruence |].
    iDestruct "Hm" as (b) "[Hb %Hok]".
    destruct b; [| iExact "Hb"].
    rewrite /ireg_frzm_ok Hne in Hok. discriminate Hok.
  Qed.

  Lemma ireg_frzc_off_intro (z : Z) (f : frzUR) :
    frz_preb f = false ->
    frzown z -∗ frzm_h z false -∗ ireg_frzc z f.
  Proof.
    intros Hne. iIntros "Hr Hb".
    iApply (ireg_frzc_intro _ _ false (ireg_frzm_ok_false f Hne) with "[Hr] Hb").
    iRight. iExact "Hr".
  Qed.

  (* ---- THE FREEZE's BOOT-SHELTER CLAUSE, PHASE-INDEXED ----------------
     (iclaim-ledger.md §6'', RULING G'.)

     §2.3's last conjunct used to read [⌜f = FrzOff⌝ ∨ ireg_open ∨ ireg_boot]:
     "whoever froze this inum exhibited SOME regime".  That is enough to keep
     ireclaim's boot token out of a runtime freeze window, but NOT enough to
     give it back: the off-lock deposit could only ever return the un-indexed
     disjunction, and ireclaim -- having lent its only [ireg_boot] -- has
     nothing left to refute the left arm with.  Since the phase now REMEMBERS
     the arm ([frz]'s payload), the clause can be stated at the index, and the
     deposit's agreement with the walk's [ifreeze_post rg] token selects it. *)
  (* ---- THE CORPSE WINDOW'S PARKED SHARE (durable-disk C-6, [FsCollect.v]'s
     residue (F)) -----------------------------------------------------------

     iput's free path leaves the region slot on the MARKED sub-arm -- [imark]
     and NO record fragment -- from the eviction that hands
     [IcacheEscrow.ipool_evict_lend] its share all the way to
     [EscrowDeposit.ireg_free_deposit_au].  Across that window the inum has no
     bundle ANYWHERE, so the commit's collection cannot reach it, and nothing
     in [ireg_slot] used to distinguish the corpse from an ordinary
     checked-out inode: the f column's clause was the REGIME alone, a
     persistent [IcacheRef.ireg_open] at the runtime index, which an empty
     [LogDefs.ln_tx] authority cannot touch ([FsCollect.col_corpse_not_refuted]
     was that wall).

     THE WINDOW IS INSIDE ONE TRANSACTION -- iput runs between its caller's
     [begin_op] and [end_op] and holds a share of its token (durable-disk
     B''-tx5) -- so the freeze PARKS a positive share of it beside the regime,
     for exactly the window's length: [ireg_freeze_au] takes it at the mint,
     the [FrzPre -> FrzPost] step rides it through ([ireg_fsh_step], which
     moves the phase and not the index), and [ireg_free_deposit_au] returns it
     with the regime.  At a commit the WAL's authority for that map is empty,
     so [ireg_fsh_no_ops] reads [f = FrzOff] off the clause at EVERY slot.

     It is [ireg_cpin]'s device at the f column, and the pair sits in the
     phase's own INDEX because two halves of one element are not the whole
     -- iput's spec names [(tid, q)] and must get THAT element back,
     and an existentially-keyed share cannot be re-identified.  The index is
     where the freezer's own [IcacheRef.ifreeze_pre] / [ifreeze_post] fragment
     already re-identifies it, so no new ghost and no new column. *)
  Definition ireg_fpin (rg : frzidx) : iProp Σ :=
    (rg.2.1 ↪[ln_tx icfg_log]{#(rg.2.2)} tt)%I.

  Global Instance ireg_fpin_timeless rg : Timeless (ireg_fpin rg).
  Proof. rewrite /ireg_fpin. apply _. Qed.

  Definition ireg_fsh (f : frzUR) : iProp Σ :=
    match f with
    | Some (Excl FrzOff)       => True
    | Some (Excl (FrzPre rg))  => ireg_regime rg.1 ∗ ireg_fpin rg
    | Some (Excl (FrzPost rg)) => ireg_regime rg.1 ∗ ireg_fpin rg
    | _                        => (ireg_open ∨ ireg_boot)
    end%I.

  Global Instance ireg_fsh_timeless f : Timeless (ireg_fsh f).
  Proof. rewrite /ireg_fsh. destruct f as [[[| rg | rg] |] |]; apply _. Qed.

  Lemma ireg_fsh_off : ⊢ ireg_fsh (Some (Excl FrzOff)).
  Proof. rewrite /ireg_fsh. done. Qed.

  Lemma ireg_fsh_pre (rg : frzidx) :
    ireg_regime rg.1 -∗ ireg_fpin rg -∗ ireg_fsh (Some (Excl (FrzPre rg))).
  Proof. iIntros "H1 H2". iFrame. Qed.

  Lemma ireg_fsh_post (rg : frzidx) :
    ireg_regime rg.1 -∗ ireg_fpin rg -∗ ireg_fsh (Some (Excl (FrzPost rg))).
  Proof. iIntros "H1 H2". iFrame. Qed.

  (* RULING G's RETURN LEG, as one line: with the column pinned at [FrzPost rg]
     by the walk's own token, the parked arm IS the regime the freezer lent --
     and, since C-6, the share it lent with it. *)
  Lemma ireg_fsh_post_acc (rg : frzidx) :
    ireg_fsh (Some (Excl (FrzPost rg))) -∗ ireg_regime rg.1 ∗ ireg_fpin rg.
  Proof. iIntros "[$ $]". Qed.

  (* THE REFUTATION THE COMMIT READS (durable-disk C-6).  Both window phases
     park a positive share of an open transaction's element, so at a commit --
     where the WAL's authority for that map is empty -- no slot in the region
     can be inside a freeze window.  [ireg_cpin_no_ops]'s line, at the f
     column; [ireg_frz_ok] is what rules out the absent column and [ExclBot],
     exactly as [ireg_claim_ok] does there. *)
  Lemma ireg_fsh_no_ops (f : frzUR) (n : nat) (d : dinode) :
    ireg_frz_ok f n d ->
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ireg_fsh f -∗ ⌜f = Some (Excl FrzOff)⌝.
  Proof.
    intros Hfrz. iIntros "Ha Hp".
    destruct f as [[[| rg | rg] |] |]; [by iPureIntro | | | |].
    - iDestruct "Hp" as "[_ Hp]". rewrite /ireg_fpin.
      iDestruct (ghost_map_lookup with "Ha Hp") as %Hbad.
      rewrite lookup_empty in Hbad. discriminate.
    - iDestruct "Hp" as "[_ Hp]". rewrite /ireg_fpin.
      iDestruct (ghost_map_lookup with "Ha Hp") as %Hbad.
      rewrite lookup_empty in Hbad. discriminate.
    - exfalso. exact Hfrz.
    - exfalso. exact Hfrz.
  Qed.

  (* ...and the RIDE-THROUGH every phase step wants: a mover that does not
     change the regime index (and, at the unfrozen column, cannot leave it)
     re-parks the arm it found. *)
  (* THE REFUTATION §2.3 BUILT THE CLAUSE FOR (fs-fragments.md §7.12), at the
     index: ireclaim's exclusive boot token kills EITHER arm, so a boot
     thread that reaches a slot learns its column is unfrozen.  This is
     [IgetLic.iname_not_frozen]'s (e)/BufL row. *)
  Lemma ireg_fsh_boot_off (f : frzUR) :
    ireg_fsh f -∗ ireg_boot -∗ ⌜f = Some (Excl FrzOff)⌝.
  Proof.
    rewrite /ireg_fsh. destruct f as [[[| rg | rg] |] |].
    - iIntros "_ _". iPureIntro. reflexivity.
    - iIntros "[H _] Hb". iExFalso. iApply (ireg_regime_boot_excl with "H Hb").
    - iIntros "[H _] Hb". iExFalso. iApply (ireg_regime_boot_excl with "H Hb").
    - iIntros "H Hb". iExFalso. iDestruct "H" as "[Ho | Ho]";
        [ iApply (ireg_boot_open_excl with "Hb Ho")
        | rewrite /ireg_boot; iApply (ity_pending_excl icfg_boot with "Hb Ho") ].
    - iIntros "H Hb". iExFalso. iDestruct "H" as "[Ho | Ho]";
        [ iApply (ireg_boot_open_excl with "Hb Ho")
        | rewrite /ireg_boot; iApply (ity_pending_excl icfg_boot with "Hb Ho") ].
  Qed.

  Lemma ireg_fsh_step (ph ph' : frz) :
    (ph' = FrzOff \/ frz_reg ph' = frz_reg ph) ->
    ireg_fsh (Some (Excl ph)) -∗ ireg_fsh (Some (Excl ph')).
  Proof.
    intros [-> | Hr]; [iIntros "_"; iApply ireg_fsh_off |].
    destruct ph' as [| rg' | rg']; [iIntros "_"; iApply ireg_fsh_off | |];
      (destruct ph as [| rg | rg]; cbn in Hr; [discriminate Hr | |];
       injection Hr as ->; iIntros "H"; iExact "H").
  Qed.

  (* ---- THE LEDGER AUTHORITY, BUNDLED WITH THE r COLUMN's CLAUSE --------
     (iclaim-ledger.md §5', RULING R -- packaged exactly as A⁗ packaged the
     receipt and the mirror into [ireg_frzc], and for the same reason.)

     The rc column is EXISTENTIAL here rather than one more binder of
     [ireg_slot]'s ∃, so [ireg_slot]'s destructuring pattern and
     [ireg_slot_intro]'s arity are BOTH unchanged: the thirty-odd sites that
     merely thread the authority through a re-park see nothing, and only the
     fifteen that actually MOVE it (the link movers, the claim, the withdraw,
     the free, and [IcacheInv]'s count writes) unpack -- which is exactly the
     set that owes the clause a re-establishment anyway. *)
  (* ---- WHERE (R1)/(R2)/(R3) WILL BE PARKED, AND WHY THEY ARE NOT YET ----

     THE CONJUNCT THIS BUNDLE EXISTS TO CARRY IS

         ∗ ⌜ireg_ref_ok r rc n c d⌝

     and adding it is a ONE-LINE change here.  It is NOT in yet, and the
     reason is a finding this increment establishes rather than a choice:

       (R1) [r + rc <= n] COUPLES THE UNITS TO THE IN-CORE COUNT, and it has
       to -- §5'.2's establish route for the pin runs [ireg_claim_au] <- (R2)
       <- [EscrowDeposit.ireg_free_deposit_au] <- "the count is zero", and (R1) is the only thing
       that carries a zero count to a zero unit column.  Every alternative was
       probed and refuted: a fragment can force a column UP, never to zero, so
       no premise and no token on the free can replace it; a [FrzPost]-gated
       (R1) has to be established at [ireg_freeze_au], which has nothing to
       establish it with; and a csum-flavoured c/r cell makes [iclaim] and
       [runit_plain] collide at the FRAGMENTS but moves the same obligation
       onto [link_mint_claim]'s local update, unchanged.

       AND (R1) IS EXACTLY WHAT THE FOUR COUNT ACCESSORS IN [IcacheInv] MUST
       PAY.  [ireg_icnt_acc] / [_frz_acc] / [_lic_acc] / [_mir_acc] all hand
       out [∀ m, ... icnt_half m] -- an arbitrary new count -- so with (R1)
       parked each of them must move a unit in the same step, which is the
       mint/spend wiring of §5'.4's item 7a: the two up-count AUs, idup's, and
       iput's two closes, then [SpecIget]/[SpecIdup]/[SpecIput] and the rest
       homes.  Landing (R1) WITHOUT that wiring cannot be done: it is not that
       the proofs get harder, it is that [ireg_icnt_acc]'s contract becomes
       false.

     THE STAGING WAS: 7a-core landed the flavoured column, its per-flavour
     moves, the pure clause with every preservation lemma the movers cite,
     and [IgetLic.iname_mint_ok] -- the licence table that pays the mint's
     two side conditions.  ITEM 7a-wire (this increment) TURNS THE CONJUNCT
     ON, in the one line below, and threads the units through every
     reference's lifetime: minted at iget, copied at idup, spent at iput,
     resting in [FileInv]'s fd slot and the proc invariant's [p->cwd]. *)
  Definition ireg_rcol (z : Z) (c : ctyUR) (r : nat) (f : frzUR)
      (n : nat) (d : dinode) : iProp Σ :=
    (∃ rc : nat, link_auth z c r f rc ∗ ⌜ireg_ref_ok r rc n c d⌝)%I.

  Global Instance ireg_rcol_timeless z c r f n d :
    Timeless (ireg_rcol z c r f n d).
  Proof. rewrite /ireg_rcol. apply _. Qed.

  Lemma ireg_rcol_intro (z : Z) (c : ctyUR) (r : nat) (f : frzUR)
      (n rc : nat) (d : dinode) :
    ireg_ref_ok r rc n c d ->
    link_auth z c r f rc -∗
    ireg_rcol z c r f n d.
  Proof.
    intros Href. iIntros "Hla". rewrite /ireg_rcol. iExists rc.
    iFrame "Hla". iPureIntro. exact Href.
  Qed.

  (* the ride-through: every mover that touches NEITHER the record's type nor
     the two r columns nor c re-parks the bundle by this one line *)
  Lemma ireg_rcol_stable (z : Z) (c : ctyUR) (r : nat) (f : frzUR)
      (n : nat) (d d' : dinode) :
    di_type d' = di_type d ->
    ireg_rcol z c r f n d -∗
    ireg_rcol z c r f n d'.
  Proof.
    intros Hty. rewrite /ireg_rcol. iIntros "(%rc & Hla & %Href)".
    iExists rc. iFrame "Hla". iPureIntro.
    exact (ireg_ref_ok_stable r rc n c d d' Hty Href).
  Qed.


  (* ---- READ-THROUGHS.  Every landed READER of the ledger authority goes
     through one of these rather than unpacking: the bundle is transparent to
     a fact-extracting lemma, so the ~20 sites that only look at the ledger
     move by one token and only the ones that MOVE it peel. *)
  Lemma ireg_rcol_freeze_agree (z : Z) (c : ctyUR) (r : nat) (f : frzUR)
      (n : nat) (d : dinode) (ph : frz) :
    ireg_rcol z c r f n d -∗ ifreeze ph z -∗
    ⌜f = Some (Excl ph)⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & _) Hfz".
    iApply (link_freeze_agree with "Hla Hfz").
  Qed.

  Lemma ireg_rcol_claim_agree (z : Z) (c : ctyUR) (r : nat) (f : frzUR)
      (n : nat) (d : dinode) (ty : bv 16) (t : nat) (qt : Qp) :
    ireg_rcol z c r f n d -∗ iclaim z ty t qt -∗
    ⌜c = Some (Excl ((ty, (t, qt)) : ctyval))⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & _) Hb".
    iApply (link_claim_agree with "Hla Hb").
  Qed.

  (* ---- THE FOUR UNIT MOVES AT THE BUNDLE (item 7a-wire, §5''.3's step 3).
     Each is a two-line composition of pieces [IcacheRef] and the pure clause
     family above already prove; they are the ONLY way a count accessor may
     move the in-core count now that (R1) couples it to the two r columns. *)

  (* THE MINT.  One unit and one count, together.  The plain flavour owes
     [c = None] -- [IgetLic.iname_mint_ok] buys it at iget, the caller's own
     unit at idup ([ireg_rcol_unclaimed] below); the claim flavour owes
     nothing.  The new [r] is EXISTENTIAL because [ireg_slot] binds it that
     way, so a caller re-parks without naming it. *)
  Lemma ireg_rcol_mint (bfl : bool) (z : Z) (c : ctyUR) (r : nat)
      (f : frzUR) (n : nat) (d : dinode) :
    bv_unsigned (di_type d) <> 0 ->
    (bfl = false -> c = None) ->
    ireg_rcol z c r f n d ==∗
    (∃ r' : nat, ireg_rcol z c r' f (S n) d)
    ∗ IcacheRef.runit bfl z.
  Proof.
    intros Hnz Hc. rewrite /ireg_rcol. iIntros "(%rc & Hla & %Href)".
    iMod (IcacheRef.link_mint_runit bfl with "Hla") as "[Hla $]".
    iModIntro. iExists (IcacheRef.rup bfl r), (IcacheRef.rcup bfl rc).
    iFrame "Hla". iPureIntro.
    exact (ireg_ref_ok_mint bfl r rc n c d Href Hnz Hc).
  Qed.

  (* THE SPEND (iput's two closes).  The unit forces its OWN column up, which
     is what makes the predecessor exist; the clause comes back by
     [ireg_ref_ok_spend], which owes nothing. *)
  Lemma ireg_rcol_spend (bfl : bool) (z : Z) (c : ctyUR) (r : nat)
      (f : frzUR) (n : nat) (d : dinode) :
    ireg_rcol z c r f (S n) d -∗ IcacheRef.runit bfl z ==∗
    ∃ r' : nat, ireg_rcol z c r' f n d.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & %Href) Hu".
    iDestruct (IcacheRef.link_runit_ge with "Hla Hu") as %Hge.
    destruct bfl; cbn in Hge.
    - destruct rc as [| rc0]; [lia |].
      iMod (IcacheRef.link_spend_runit true z c r f rc0
              with "Hla Hu") as "Hla".
      iModIntro. iExists r, rc0. iFrame "Hla". iPureIntro.
      exact (ireg_ref_ok_spend true r rc0 n c d Href).
    - destruct r as [| r0]; [lia |].
      iMod (IcacheRef.link_spend_runit false z c r0 f rc
              with "Hla Hu") as "Hla".
      iModIntro. iExists r0, rc. iFrame "Hla". iPureIntro.
      exact (ireg_ref_ok_spend false r0 rc n c d Href).
  Qed.

  (* ...AND THE PIN's OWN READER (§5'.3's disjunctive withdraw): a caller
     inside the region open reads [1 <= r] off its own PLAIN unit with
     [IcacheRef.link_runit_ge] and applies [ireg_ref_ok_unclaimed] to the
     clause.  Everything is borrowed; the conclusion is pure. *)
  Lemma ireg_rcol_unclaimed (z : Z) (c : ctyUR) (r : nat) (f : frzUR)
      (n : nat) (d : dinode) :
    ireg_rcol z c r f n d -∗ IcacheRef.runit false z -∗
    ⌜c = None⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & %Href) Hu".
    iDestruct (IcacheRef.link_runit_ge with "Hla Hu") as %Hge. cbn in Hge.
    iPureIntro. exact (ireg_ref_ok_unclaimed r rc n c d Href Hge).
  Qed.

  (* ...AND ITS ALLOCATEDNESS TWIN, which is what idup's mint pays its type
     premise with: it holds its caller's own unit, at EITHER flavour, and
     needs no licence at all. *)
  Lemma ireg_rcol_alloc (bfl : bool) (z : Z) (c : ctyUR) (r : nat)
      (f : frzUR) (n : nat) (d : dinode) :
    ireg_rcol z c r f n d -∗ IcacheRef.runit bfl z -∗
    ⌜bv_unsigned (di_type d) <> 0⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & %Href) Hu".
    iDestruct (IcacheRef.link_runit_ge with "Hla Hu") as %Hge.
    iPureIntro. apply (ireg_ref_ok_alloc r rc n c d Href).
    destruct bfl; cbn in Hge; lia.
  Qed.

  (* ...AND THE TWO OF THEM FUSED, which is [ireg_rcol_mint]'s premise pair
     exactly -- the shape [IgetLic.iname_mint_ok] delivers at iget and the
     caller's OWN unit delivers at idup.  One lemma so the mover reads a
     conjunction rather than case-splitting its flavour at the seam. *)
  Lemma ireg_rcol_mint_ok (bfl : bool) (z : Z) (c : ctyUR) (r : nat)
      (f : frzUR) (n : nat) (d : dinode) :
    ireg_rcol z c r f n d -∗ IcacheRef.runit bfl z -∗
    ⌜bv_unsigned (di_type d) <> 0 /\ (bfl = false -> c = None)⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & %Href) Hu".
    iDestruct (IcacheRef.link_runit_ge with "Hla Hu") as %Hge.
    iPureIntro. split.
    - apply (ireg_ref_ok_alloc r rc n c d Href).
      destruct bfl; cbn in Hge; lia.
    - intros Hb. rewrite Hb in Hge. cbn in Hge.
      exact (ireg_ref_ok_unclaimed r rc n c d Href Hge).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE LINK-COUNTING RA's PER-INUM AUTHORITY (durable-disk 2b-inode-4) *)
  (* ------------------------------------------------------------------ *)

  (*  [fs-state.md] section 2's counting RA, filed HERE and not in the
      checked-out payload.  The authority mirrors a record FIELD
      ([di_nlink]), so 2b-inode-1's ruling (i) puts it exactly where the
      record's own bytes are: region-side, total over the slot, tied to
      [d] BY CONSTRUCTION rather than by a clause.

      TWO THINGS FORCE IT and neither is a placement preference:

      - [IgetLic]'s licence (a) reads "a directory record names this inum
        and PAYS for it" into "the target is ALLOCATED", and that reading
        is the RA's own law ([FsStateLink.link_auth_toks_le]) applied at
        the TARGET's authority.  The presenter does not hold the target,
        so with the authority in the target's payload nothing in the tree
        could reach it and [SpecIget]'s premise would have no discharge.
        Region-side it is one [inv_acc] of [iregN] -- exactly where the
        pure clause (L1) it replaces was read.
      - every move of a count is a FLUSH, which already opens the region
        to write the record; [link_mint]/[link_return] are basic updates,
        so they compose into that AU at no mask cost.

      AT THIS STAGE EVERY TOKEN IS AT HOME.  The pile is [nlink] tokens
      wide, so the family's validity is free at boot and no image sweep is
      spent; the links step hands a directory's tokens to its checked-out
      payload ([FsStateInode.ent_toks]) and leaves the region holding only
      the ROOT's keep-alive token. *)
  Definition ireg_nl (d : dinode) : nat := Z.to_nat (bv_unsigned (di_nlink d)).

  (* THE MULTIPLICITY a record's own fields fix (fs-state.md section 6.5):
     one unit per COUNTED dirent, plus the ["."] a LIVE DIRECTORY holds in
     its own bundle -- the [+1] xv6 deliberately does not count.  At
     [nlink = 0] there is no bonus WHATEVER the type is, which is what
     keeps the kernel's two TYPE writes (the claim's [0 -> ty] and the free
     deposit's [ty -> 0]) at multiplicity zero, where the register is empty
     and the value is not mentioned at all. *)
  Definition ireg_mult_at (n : nat) (ty : Z) : nat :=
    (n + if bool_decide (ty = ireg_dir_ty) && negb (bool_decide (n = 0%nat))
         then 1%nat else 0%nat)%nat.

  Definition ireg_mult (d : dinode) : nat :=
    ireg_mult_at (ireg_nl d) (bv_unsigned (di_type d)).

  Lemma ireg_mult_at_zero ty : ireg_mult_at 0%nat ty = 0%nat.
  Proof.
    rewrite /ireg_mult_at (bool_decide_eq_true_2 (0%nat = 0%nat) eq_refl)
      andb_false_r //.
  Qed.

  Lemma ireg_mult_at_ge n ty : (n <= ireg_mult_at n ty)%nat.
  Proof. rewrite /ireg_mult_at. destruct (_ && _)%bool; lia. Qed.

  Lemma ireg_mult_at_le n ty : (ireg_mult_at n ty <= S n)%nat.
  Proof. rewrite /ireg_mult_at. destruct (_ && _)%bool; lia. Qed.

  Lemma ireg_mult_at_nz n ty : ireg_mult_at n ty <> 0%nat -> n <> 0%nat.
  Proof.
    intros Hm Hz. apply Hm. rewrite Hz. exact (ireg_mult_at_zero ty).
  Qed.

  Lemma ireg_mult_zero d :
    bv_unsigned (di_nlink d) = 0 -> ireg_mult d = 0%nat.
  Proof.
    intros Hz. rewrite /ireg_mult /ireg_nl Hz Z2Nat.inj_0.
    exact (ireg_mult_at_zero _).
  Qed.

  Lemma ireg_mult_nl d : (ireg_nl d <= ireg_mult d <= S (ireg_nl d))%nat.
  Proof.
    split; [exact (ireg_mult_at_ge _ _) | exact (ireg_mult_at_le _ _)].
  Qed.

  (* HOW MANY FRAGMENTS A [nlink]-BY-ONE MOVE MOVES: one for the record
     that pays, plus -- when a DIRECTORY crosses the live boundary -- the
     ["."] the live form holds and the orphan form does not.  It is TWO at
     exactly two sites in the kernel (create's fresh-directory fill and
     rmdir's [ip->nlink--]) and ONE everywhere else. *)
  Definition ireg_dot_delta (ty : Z) (n : Z) : nat :=
    if bool_decide (ty = ireg_dir_ty) && bool_decide (n = 0)
    then 2%nat else 1%nat.

  Lemma ireg_dot_delta_not_dir (ty n : Z) :
    ty <> ireg_dir_ty -> ireg_dot_delta ty n = 1%nat.
  Proof.
    intros H. rewrite /ireg_dot_delta (bool_decide_eq_false_2 _ H) //.
  Qed.

  Lemma ireg_dot_delta_live (ty n : Z) :
    n <> 0 -> ireg_dot_delta ty n = 1%nat.
  Proof.
    intros H. rewrite /ireg_dot_delta (bool_decide_eq_false_2 (n = 0) H)
      andb_false_r //.
  Qed.

  Lemma ireg_mult_bump d d' :
    bv_unsigned (di_nlink d') = bv_unsigned (di_nlink d) + 1 ->
    bv_unsigned (di_type d') = bv_unsigned (di_type d) ->
    ireg_mult d' = (ireg_mult d
                    + ireg_dot_delta (bv_unsigned (di_type d))
                                     (bv_unsigned (di_nlink d)))%nat.
  Proof.
    intros Hnl Hty.
    pose proof (di_nlink_nonneg d) as Hnn.
    rewrite /ireg_mult /ireg_mult_at /ireg_nl /ireg_dot_delta Hty Hnl.
    repeat case_bool_decide; simpl in *; lia.
  Qed.

  Lemma ireg_mult_drop d d' :
    bv_unsigned (di_nlink d) = bv_unsigned (di_nlink d') + 1 ->
    bv_unsigned (di_type d') = bv_unsigned (di_type d) ->
    ireg_mult d = (ireg_mult d'
                   + ireg_dot_delta (bv_unsigned (di_type d'))
                                    (bv_unsigned (di_nlink d')))%nat.
  Proof.
    intros Hnl Hty.
    pose proof (di_nlink_nonneg d') as Hnn.
    rewrite /ireg_mult /ireg_mult_at /ireg_nl /ireg_dot_delta Hty Hnl.
    repeat case_bool_decide; simpl in *; lia.
  Qed.

  (* THE TIE between the record's TYPE FIELD and the register's VALUE.
     [TDir p]'s [p] is NOT read here -- the slot carries the record alone
     and cannot see the [".."] entry; what pins it is the ["."] fragment
     in the directory's own checked-out payload
     ([FsStateInode.ent_ty_ok] at [DOT]), which is rmdir's (D1). *)
  Definition ireg_reg_ok (ty : Z) (v : ity) : Prop :=
    match v with
    | TFile => ty <> ireg_dir_ty
    | TDir _ => ty = ireg_dir_ty
    end.

  Lemma ireg_reg_ok_ex (ty : Z) : exists v, ireg_reg_ok ty v.
  Proof.
    destruct (decide (ty = ireg_dir_ty)) as [H | H];
      [exists (TDir 0) | exists TFile]; exact H.
  Qed.

  Lemma ireg_reg_ok_dir ty v :
    ireg_reg_ok ty v -> ty = ireg_dir_ty -> exists p, v = TDir p.
  Proof.
    destruct v as [| p]; intros Hok Hd; [destruct (Hok Hd) | by exists p].
  Qed.

  Lemma ireg_reg_ok_file ty v :
    ireg_reg_ok ty v -> ty <> ireg_dir_ty -> v = TFile.
  Proof. destruct v as [| p]; intros Hok Hd; [done | destruct (Hd Hok)]. Qed.

  (* THE ROOT KEEP-ALIVE FRAGMENT.  [ent_tokenless] exempts the ROOT's
     [".."] -- which names the root -- so the image's [nlink = 1] at the
     root is unaccounted for by any entry, and the region parks that one
     fragment here, where nothing can ever spend it.  "The root is
     allocated" is then a reading of the RA's own law and there is no pure
     clause about the root anywhere in the slot.

     IT IS THE ONLY SOURCE [IgetLic]'s licence (f) HAS: namei's
     [iget(ROOTINO)] holds nothing at all, and every other fragment at the
     root lives in the root's own checked-out payload, which [iregN] cannot
     reach. *)
  Definition ireg_keep (γfs : fs_names) (z : Z) (v : ity) : iProp Σ :=
    (if bool_decide (z = ireg_root)
     then FsStateLink.link_tok (fs_gamma_L γfs) z v else emp)%I.

  Global Instance ireg_keep_timeless γfs z v : Timeless (ireg_keep γfs z v).
  Proof. rewrite /ireg_keep. case_bool_decide; apply _. Qed.

  (* the count-and-type-indexed form, which is what BOOT hands over: the
     region's shape at a slot is a function of the record's [nlink] and
     [di_type] alone.

     THE FRAGMENTS ARE NOT HERE.  A directory's fragments ride in its
     CHECKED-OUT PAYLOAD ([IcacheEscrow.ic_loaded]'s
     [FsStateInode.ent_toks]); what the region keeps is the per-inum
     AUTHORITY, plus the root's one keep-alive.  The authority is
     region-side because [IgetLic]'s licence (a) reads the RA's law at the
     TARGET's authority and the presenter of the licence does not hold the
     target -- see the banner above. *)
  Definition ireg_lnk_at (γfs : fs_names) (z : Z) (n : nat) (ty : Z)
    : iProp Σ :=
    (∃ v : ity, ⌜ireg_reg_ok ty v⌝
       ∗ FsStateLink.link_auth (fs_gamma_L γfs) z (ireg_mult_at n ty) v
       ∗ ireg_keep γfs z v)%I.

  Definition ireg_lnk (γfs : fs_names) (z : Z) (d : dinode) : iProp Σ :=
    ireg_lnk_at γfs z (ireg_nl d) (bv_unsigned (di_type d)).

  Lemma ireg_lnk_of_at γfs z n ty d :
    n = ireg_nl d -> ty = bv_unsigned (di_type d) ->
    ireg_lnk_at γfs z n ty -∗ ireg_lnk γfs z d.
  Proof. intros -> ->. iIntros "H"; iExact "H". Qed.

  Global Instance ireg_lnk_at_timeless γfs z n ty :
    Timeless (ireg_lnk_at γfs z n ty).
  Proof. rewrite /ireg_lnk_at. apply _. Qed.

  Global Instance ireg_lnk_timeless γfs z d : Timeless (ireg_lnk γfs z d).
  Proof. rewrite /ireg_lnk. apply _. Qed.

  (* the multiplicity is a function of the two record fields, so a mover
     that moves neither moves nothing *)
  Lemma ireg_lnk_stable γfs z d d' :
    bv_unsigned (di_nlink d') = bv_unsigned (di_nlink d) ->
    bv_unsigned (di_type d') = bv_unsigned (di_type d) ->
    ireg_lnk γfs z d -∗ ireg_lnk γfs z d'.
  Proof.
    intros Heq Hty. rewrite /ireg_lnk /ireg_nl Heq Hty.
    iIntros "H"; iExact "H".
  Qed.

  (* ...AND THE TYPE-WRITING ONE: at a record whose count is zero the
     multiplicity is zero WHATEVER the type is, so the authority is the
     empty one and the value is not mentioned -- the slot may be retyped
     freely.  That is the claim's move ([0 -> ty] at a fresh box) and the
     free deposit's ([ty -> 0] at a corpse), the only two writes of
     [di_type] in the kernel.  At the ROOT the premises are contradictory
     (the keep-alive fragment cannot stand against an empty authority),
     which is how the root's slot survives the lemma. *)
  Lemma ireg_lnk_free_retype γfs z d d' :
    bv_unsigned (di_nlink d) = 0 ->
    bv_unsigned (di_nlink d') = 0 ->
    ireg_lnk γfs z d -∗ ireg_lnk γfs z d'.
  Proof.
    intros Hz Hz'. rewrite /ireg_lnk /ireg_lnk_at /ireg_nl Hz Hz' Z2Nat.inj_0.
    rewrite !ireg_mult_at_zero.
    iIntros "(%v & _ & Ha & Hk)".
    destruct (ireg_reg_ok_ex (bv_unsigned (di_type d'))) as [v' Hok'].
    rewrite /ireg_keep. case_bool_decide as Hr.
    - iDestruct (FsStateLink.link_auth_zero_no_tok with "Ha Hk") as "[]".
    - iExists v'. iSplitR; [by iPureIntro |].
      rewrite (FsStateLink.link_auth_zero_retype _ z v v').
      iFrame "Ha".
  Qed.

  (* THE RAISING FLUSH ([ip->nlink++; iupdate]), at a record whose type
     does not move: [k] fragments come out, and they go to the [dirlink]s
     that file them in directories' [FsStateInode.ent_toks].  [k] is ONE
     everywhere except create's fresh-DIRECTORY fill, where the
     multiplicity crosses [0 -> 2] (the name in the parent, and the
     child's own ["."]). *)
  Lemma ireg_lnk_bump γfs z d d' (k : nat) :
    ireg_mult d' = (ireg_mult d + k)%nat ->
    bv_unsigned (di_type d') = bv_unsigned (di_type d) ->
    ireg_lnk γfs z d ==∗
    ireg_lnk γfs z d'
    ∗ ∃ v, ⌜ireg_reg_ok (bv_unsigned (di_type d)) v⌝
           ∗ FsStateLink.link_toks (fs_gamma_L γfs) z (link_reps k v).
  Proof.
    intros Hm Hty. rewrite /ireg_lnk /ireg_lnk_at.
    iIntros "(%v & %Hok & Ha & Hk)".
    iMod (FsStateLink.link_mint_reps _ z (ireg_mult d) k v with "Ha")
      as "[Ha Hts]".
    iModIntro.
    iSplitL "Ha Hk".
    - iExists v. iSplitR; [iPureIntro; rewrite Hty; exact Hok |].
      rewrite -/(ireg_mult d') -Hm. iFrame "Ha".
      rewrite /ireg_keep. iExact "Hk".
    - iExists v. iFrame "Hts". by iPureIntro.
  Qed.

  (* ...AND THE FILL, where the multiplicity was ZERO and the caller
     CHOOSES the value.  That is mkdir's fresh child: the register is set
     to [TDir dp] at the flush that writes [nlink = 1], which is what makes
     the parent's name record able to assert "my target's parent is ME". *)
  Lemma ireg_lnk_fill γfs z d d' (v : ity) (k : nat) :
    ireg_mult d = 0%nat ->
    ireg_mult d' = k ->
    ireg_reg_ok (bv_unsigned (di_type d')) v ->
    ireg_lnk γfs z d ==∗
    ireg_lnk γfs z d'
    ∗ FsStateLink.link_toks (fs_gamma_L γfs) z (link_reps k v).
  Proof.
    intros Hz Hm Hok'. rewrite /ireg_lnk /ireg_lnk_at.
    iIntros "(%v0 & %Hok & Ha & Hk)".
    rewrite -/(ireg_mult d) Hz.
    rewrite /ireg_keep. case_bool_decide as Hr.
    - iDestruct (FsStateLink.link_auth_zero_no_tok with "Ha Hk") as "[]".
    - rewrite (FsStateLink.link_auth_zero_retype _ z v0 v).
      iMod (FsStateLink.link_mint_reps _ z 0%nat k v with "Ha") as "[Ha $]".
      iModIntro. iExists v. iSplitR; [by iPureIntro |].
      rewrite -/(ireg_mult d') Hm Nat.add_0_l. iFrame "Ha".
  Qed.

  (* ...and the LOWERING one ([ip->nlink--; iupdate]): [k] fragments in,
     paid for by the entries that gave them up.  [k] is ONE everywhere
     except rmdir's [ip->nlink--], where the child's multiplicity crosses
     [2 -> 0] (its name in the parent, and its own ["."]). *)
  Lemma ireg_lnk_drop γfs z d d' (v : ity) (k : nat) :
    ireg_mult d = (ireg_mult d' + k)%nat ->
    bv_unsigned (di_type d') = bv_unsigned (di_type d) ->
    ireg_lnk γfs z d -∗
    FsStateLink.link_toks (fs_gamma_L γfs) z (link_reps k v) ==∗
    ireg_lnk γfs z d'.
  Proof.
    intros Hm Hty. rewrite /ireg_lnk /ireg_lnk_at.
    iIntros "(%v0 & %Hok & Ha & Hk) Hts".
    rewrite -/(ireg_mult d) Hm.
    iMod (FsStateLink.link_return_reps _ z (ireg_mult d') k v0 v
            with "Ha Hts") as "Ha".
    iModIntro. iExists v0. iSplitR; [iPureIntro; rewrite Hty; exact Hok |].
    rewrite -/(ireg_mult d'). iFrame "Ha". rewrite /ireg_keep. iExact "Hk".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE READINGS                                                       *)
  (* ------------------------------------------------------------------ *)

  (* the general one, which is what licence (a) reads: any pile of
     fragments standing at this inum bounds the record's own multiplicity
     from below. *)
  Lemma ireg_lnk_toks_le γfs z d Q :
    ireg_lnk γfs z d -∗ FsStateLink.link_toks (fs_gamma_L γfs) z Q -∗
    ⌜(size Q <= ireg_mult d)%nat⌝.
  Proof.
    rewrite /ireg_lnk /ireg_lnk_at. iIntros "(%v & _ & Ha & _) Htk".
    iDestruct (FsStateLink.link_auth_toks_le with "Ha Htk") as %[Hle _].
    by iPureIntro.
  Qed.

  (* ONE fragment says the record is LIVE: at [nlink = 0] the multiplicity
     is zero whatever the type is. *)
  Lemma ireg_lnk_tok_nz γfs z d v :
    ireg_lnk γfs z d -∗ FsStateLink.link_tok (fs_gamma_L γfs) z v -∗
    ⌜bv_unsigned (di_nlink d) <> 0⌝.
  Proof.
    iIntros "Hl Ht".
    iDestruct (ireg_lnk_toks_le γfs z d {[+ v +]} with "Hl Ht") as %Hle.
    iPureIntro. intros Hz.
    rewrite (ireg_mult_zero d Hz) gmultiset_size_singleton in Hle. lia.
  Qed.

  (* ...AND ITS VALUE IS THE RECORD'S TYPE.  The agreement half of the RA's
     law, at the region's own authority: a fragment standing at an inum
     tells the holder whether that inum is a DIRECTORY, and if it is, which
     inum the region believes is its parent. *)
  Lemma ireg_lnk_tok_ty γfs z d v :
    ireg_lnk γfs z d -∗ FsStateLink.link_tok (fs_gamma_L γfs) z v -∗
    ⌜ireg_reg_ok (bv_unsigned (di_type d)) v⌝.
  Proof.
    rewrite /ireg_lnk /ireg_lnk_at. iIntros "(%v0 & %Hok & Ha & _) Ht".
    iDestruct (FsStateLink.link_auth_tok_agree with "Ha Ht") as %[-> _].
    by iPureIntro.
  Qed.

  (* THE (D1) ENGINE: two fragments at one inum carry the SAME value, since
     the authority is a UNIFORM multiset.  rmdir reads the child's ["."]
     fragment (which is [TDir] of the child's own [".."] target) against
     the parent's NAME-record fragment (whose holder asserts [TDir] of
     ITSELF) and the two collapse. *)
  Lemma ireg_lnk_toks_agree γfs z d v v' :
    ireg_lnk γfs z d -∗ FsStateLink.link_tok (fs_gamma_L γfs) z v -∗
    FsStateLink.link_tok (fs_gamma_L γfs) z v' -∗ ⌜v = v'⌝.
  Proof.
    rewrite /ireg_lnk /ireg_lnk_at. iIntros "(%v0 & _ & Ha & _) Ht Ht'".
    iDestruct (FsStateLink.link_auth_tok_agree with "Ha Ht") as %[-> _].
    iDestruct (FsStateLink.link_auth_tok_agree with "Ha Ht'") as %[-> _].
    by iPureIntro.
  Qed.

  (* THE ROOT'S READING: the parked keep-alive cannot be spent, so the RA's
     own law says the root's count is at least one. *)
  Lemma ireg_lnk_root_alive γfs d :
    ireg_lnk γfs ireg_root d -∗ ⌜1 <= bv_unsigned (di_nlink d)⌝.
  Proof.
    rewrite /ireg_lnk /ireg_lnk_at /ireg_keep bool_decide_eq_true_2 //.
    iIntros "(%v & _ & Ha & Htk)".
    iDestruct (FsStateLink.link_auth_tok_agree with "Ha Htk") as %[_ Hle].
    iPureIntro.
    pose proof (di_nlink_nonneg d) as Hnn.
    destruct (decide (bv_unsigned (di_nlink d) = 0)) as [Hz | Hnz]; [| lia].
    exfalso. rewrite -/(ireg_mult d) (ireg_mult_zero d Hz) in Hle. lia.
  Qed.

  (* ...AND THE ROOT'S MINIMUM AT A HELD PILE.  The keep-alive is a fragment
     the caller's pile does not include, so [k] fragments in hand put the
     root's own count at [k] -- hence a directory whose count is ONE and
     which two held fragments stand at is not the root, which is
     S7-unlink's dir arm's (D1) step 2.  Vacuous elsewhere: at any other
     inum [ireg_keep] is [emp] and the implication has no antecedent. *)
  Lemma ireg_lnk_root_le γfs z d (k : nat) (v : ity) :
    ireg_lnk γfs z d -∗
    FsStateLink.link_toks (fs_gamma_L γfs) z (link_reps k v) -∗
    ⌜z = ireg_root -> Z.of_nat k <= bv_unsigned (di_nlink d)⌝.
  Proof.
    rewrite /ireg_lnk /ireg_lnk_at /ireg_keep.
    case_bool_decide as Hz; last first.
    { iIntros "_ _". iPureIntro. intro Hc. exfalso. exact (Hz Hc). }
    iIntros "(%v0 & _ & Ha & Hkeep) Htk".
    iAssert (FsStateLink.link_toks (fs_gamma_L γfs) z
               ({[+ v0 +]} ⊎ link_reps k v))%I with "[Hkeep Htk]" as "Htks".
    { rewrite FsStateLink.link_toks_split. iFrame "Hkeep Htk". }
    iDestruct (FsStateLink.link_auth_toks_le with "Ha Htks") as %[Hle _].
    iPureIntro. intros _.
    rewrite gmultiset_size_disj_union gmultiset_size_singleton
      link_reps_size in Hle.
    rewrite -/(ireg_mult d) in Hle.
    pose proof (ireg_mult_nl d) as [Hlo Hhi].
    pose proof (di_nlink_nonneg d) as Hnn.
    rewrite /ireg_nl in Hhi.
    lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE ERA's ABSTRACT VALUE, PARKED WITH THE RECORD (durable-disk C-3c) *)
  (*                                                                      *)
  (*  Every inum of the region owns exactly one [FsState.top_frag].  While  *)
  (*  the record's fragment is region-side -- a FREE record, a claim box,   *)
  (*  a PENDING slot -- the abstract value parks HERE, beside it, instead   *)
  (*  of in the pool's marker arm where it used to ride UNTIED.  That is    *)
  (*  the whole of supplier (D): the commit's collection needs a whole      *)
  (*  [FsStateEra.inode_owned_era] at every inum of the abstract map, and   *)
  (*  a free inum's is the region's [z |->[γi] d] together with THIS        *)
  (*  fragment -- but only if the two describe the same node.               *)
  (*                                                                        *)
  (*  THE TIE IS GUARDED BY THE TYPE, and that is what keeps it free at      *)
  (*  every mover.  At a TYPE-0 record the node is [free_node d] outright    *)
  (*  (the record is bare, so nothing is left to choose); at a claim box     *)
  (*  the fragment rides UNTIED exactly as it did in the pool, so            *)
  (*  [ireg_claim_au] -- which retags the record 0 -> [fresh_shape] -- owes  *)
  (*  nothing and moves no resource, and the fill's own                      *)
  (*  [ireg_top_retag] (ProofIlock) is unchanged.                            *)
  (*                                                                        *)
  (*  WHERE IT ENTERS AND LEAVES.  In: boot ([IcacheBoot]) at every free     *)
  (*  inum of the image, and [EscrowDeposit.ireg_free_deposit_au] -- iput's  *)
  (*  type-0 write -- which takes the freed payload's fragment out of the    *)
  (*  escrow the freer minted ([EscrowInode.escA_body]'s EMPTY arm) and      *)
  (*  retags it at the corpse's bare record.  Out: [ireg_withdraw], the ONE  *)
  (*  exit from the IN arm.                                                  *)
  Definition ireg_top_park (γfs : fs_names) (z : Z) (d : dinode) : iProp Σ :=
    (∃ n : fs_node,
       ⌜bv_unsigned (di_type d) = 0 -> ireg_bare d /\ n = free_node d⌝ ∗
       top_frag (fs_gamma_L γfs) z n)%I.

  Global Instance ireg_top_park_timeless γfs z d :
    Timeless (ireg_top_park γfs z d).
  Proof. rewrite /ireg_top_park /top_frag. apply _. Qed.

  (* the UNTIED park, which is all a nonzero-type record owes *)
  Lemma ireg_top_park_nz γfs z d (n : fs_node) :
    bv_unsigned (di_type d) <> 0 ->
    top_frag (fs_gamma_L γfs) z n -∗ ireg_top_park γfs z d.
  Proof.
    intros Hnz. iIntros "Hf". iExists n. iFrame "Hf".
    iPureIntro. intros H0. exfalso. exact (Hnz H0).
  Qed.

  (* ...and the TIED one, at the free record the deposit and boot write *)
  Lemma ireg_top_park_free γfs z d :
    ireg_bare d ->
    top_frag (fs_gamma_L γfs) z (free_node d) -∗ ireg_top_park γfs z d.
  Proof.
    intros Hb. iIntros "Hf". iExists (free_node d). iFrame "Hf".
    iPureIntro. intros _. split; [exact Hb | reflexivity].
  Qed.

  (* the park travels across a mover that writes a NONZERO type: the tie's
     obligation is on its vacuous side at both records, so the fragment rides
     through untouched.  That is every mover but the free deposit
     ([ireg_write_au], the two link writes and [ireg_claim_au] all write a
     record with a type). *)
  Lemma ireg_top_park_retype γfs z d d' :
    bv_unsigned (di_type d') <> 0 ->
    ireg_top_park γfs z d -∗ ireg_top_park γfs z d'.
  Proof.
    intros Hnz. iIntros "(%n & _ & Hf)".
    iApply (ireg_top_park_nz γfs z d' n Hnz with "Hf").
  Qed.

  (* WHAT THE COLLECTION READS OFF IT (FsCollect's supplier (D)): at a free
     record the park IS the node, so the fragment can be handed out at
     [free_node d] with no existential left. *)
  Lemma ireg_top_park_open γfs z d :
    bv_unsigned (di_type d) = 0 ->
    ireg_top_park γfs z d -∗
      ⌜ireg_bare d⌝ ∗ top_frag (fs_gamma_L γfs) z (free_node d).
  Proof.
    intros H0. iIntros "(%n & %Hn & Hf)".
    destruct (Hn H0) as [Hb ->]. iFrame "Hf". iPureIntro. exact Hb.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE CLAIM BOX'S PARKED TRANSACTION SHARE (durable-disk C-5)          *)
  (*  -- [FsCollect.v]'s residue (E), closed.                             *)
  (*                                                                      *)
  (*  ialloc retags a FREE record to a [fresh_shape] one and the region    *)
  (*  keeps the fragment on its IN arm until the claimant's first ilock    *)
  (*  fills the box.  In that window the record has a NONZERO type, so     *)
  (*  [ireg_top_park]'s tie is on its vacuous side and the commit's        *)
  (*  collection can read neither [FsDurSnap.sk_rec] nor [sk_links] at the *)
  (*  inum ([FsCollect.col_claim_box_untied]).  The window is inside ONE   *)
  (*  transaction -- ialloc runs between its caller's [begin_op] and       *)
  (*  [end_op] -- and this is what PROVES it: the claim parks a POSITIVE   *)
  (*  share of that transaction's [LogDefs.ln_tx] element, so an empty     *)
  (*  authority refutes [c <> None] outright ([ireg_cpin_no_ops]) and the  *)
  (*  IN arm's own clause then yields [di_type d = 0]                      *)
  (*  ([ireg_in_quiesce]).  It is [IcacheEscrow.ic_pin_tx]'s device at the *)
  (*  region's own key: the c column is keyed by the INUM, the claimant    *)
  (*  holds the exclusive fragment at that key, and                        *)
  (*  [IcacheRef.link_claim_agree] re-identifies [(t, q)] at the fill --   *)
  (*  which is why [Xv6Cameras.ctyval] carries the pair as FIELDS and not  *)
  (*  existentially: two halves of one element are not the whole.          *)
  Definition ireg_cpin (c : ctyUR) : iProp Σ :=
    match c with
    | Some (Excl v) => (v.2.1 ↪[ln_tx icfg_log]{#(v.2.2)} tt)%I
    | _             => emp%I
    end.

  Global Instance ireg_cpin_timeless c : Timeless (ireg_cpin c).
  Proof. rewrite /ireg_cpin. destruct c as [[v |] |]; apply _. Qed.

  Lemma ireg_cpin_none : ⊢ ireg_cpin None.
  Proof. rewrite /ireg_cpin. done. Qed.

  Lemma ireg_cpin_some (v : ctyval) :
    v.2.1 ↪[ln_tx icfg_log]{#(v.2.2)} tt -∗ ireg_cpin (Some (Excl v)).
  Proof. iIntros "H". iExact "H". Qed.

  Lemma ireg_cpin_open (v : ctyval) :
    ireg_cpin (Some (Excl v)) -∗ v.2.1 ↪[ln_tx icfg_log]{#(v.2.2)} tt.
  Proof. iIntros "H". iExact "H". Qed.

  (* THE REFUTATION THE COMMIT READS.  A standing claim holds a positive
     share of an open transaction's element, so at a commit -- where the
     WAL's authority for that map is empty -- no claim can be standing.
     [IcacheEscrow.ic_pin_tx_no_ops]'s line, at the c column; the
     [ExclBot] arm is refuted by the slot's own claim pin, which is why the
     lemma takes it. *)
  Lemma ireg_cpin_no_ops (c : ctyUR) (f : frzUR) (d : dinode) :
    ireg_claim_ok c f d ->
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) -∗
    ireg_cpin c -∗ ⌜c = None⌝.
  Proof.
    intros Hclm. iIntros "Ha Hp". destruct c as [[v |] |].
    - rewrite /ireg_cpin.
      iDestruct (ghost_map_lookup with "Ha Hp") as %Hbad.
      rewrite lookup_empty in Hbad. discriminate.
    - exfalso. exact (proj2 (proj2 Hclm)).
    - done.
  Qed.

  (* THE SHELTER AND THE PIN, AS ONE CONJUNCT, in [ireg_fsh]'s own position
     (durable-notes, "REPLACING ONE CONJUNCT OF A BIG PAYLOAD BY ANOTHER"):
     the thirty-odd sites that merely thread the slot's f-shelter through a
     re-park are byte-stable, and only the movers that CHANGE the c column
     (the claim and the withdrawal) split it. *)
  Definition ireg_shp (c : ctyUR) (f : frzUR) : iProp Σ :=
    (ireg_fsh f ∗ ireg_cpin c)%I.

  Global Instance ireg_shp_timeless c f : Timeless (ireg_shp c f).
  Proof. rewrite /ireg_shp. apply _. Qed.

  Lemma ireg_shp_intro (c : ctyUR) (f : frzUR) :
    ireg_fsh f -∗ ireg_cpin c -∗ ireg_shp c f.
  Proof. iIntros "H1 H2". iFrame. Qed.

  Lemma ireg_shp_split (c : ctyUR) (f : frzUR) :
    ireg_shp c f -∗ ireg_fsh f ∗ ireg_cpin c.
  Proof. iIntros "[$ $]". Qed.

  (* the ride-through every mover that touches NEITHER column wants *)
  Lemma ireg_shp_none (f : frzUR) : ireg_fsh f -∗ ireg_shp None f.
  Proof. iIntros "H". iApply (ireg_shp_intro None f with "H").
         iApply ireg_cpin_none. Qed.

  Definition ireg_slot (γfs : fs_names) (γi : gname) (z : Z) (d : dinode)
    : iProp Σ :=
    ((∃ (r : nat) (c : ctyUR) (f : frzUR) (n : nat),
        ireg_rcol z c r f n d
        ∗ ⌜ireg_link_ok d⌝
        (* THE BOOT-SHELTER CLAUSE (fs-fragments.md §7.12): a claimed slot
           (c = Some) must exhibit the SEALED regime [ireg_open].  A holder of
           the exclusive [ireg_boot] token refutes that, so ireclaim proves
           every slot it reaches is unclaimed.  DISJUNCTIVE, not an
           implication, so it stays timeless ([ireg_slot_timeless]); both arms
           are timeless AND persistent. *)
        ∗ (⌜c = None⌝ ∨ ireg_open)
        (* THE COUNT COUPLING's REGION HALF (§2.2).  The other half rides
           under the itable lock -- [islot2]'s cached arm at
           [Pos.to_nat n], [islot_empty] at 0 (increment 3) -- so every
           count move needs BOTH and therefore an [↑iregN] open, which is
           the probe's structural mask verdict. *)
        ∗ icnt_half z n
        (* the two in-transition pins (§2.3/§2.4), stated over the record
           and the count this slot is carrying *)
        ∗ ⌜ireg_claim_ok c f d⌝
        ∗ ⌜ireg_frz_ok f n d⌝
        (* THE FREEZE's BOOT-SHELTER CLAUSE (§2.3's last conjunct), the
           f-column twin of the [c] clause above: a RUNTIME freezer
           exhibits the persistent [ireg_open]; ireclaim, the only boot
           freezer, PARKS its exclusive [ireg_boot] here for the freeze's
           duration and takes it back at the deposit.  Disjunctive rather
           than an implication so the slot stays timeless. *)
        ∗ ireg_shp c f
        (* THE FREEZE RECEIPT's CLAUSE (iclaim-ledger.md §3.14 as built).
           The region parks [IcacheRef.frzown z] at EVERY phase except
           [FrzPre]; the mint ([ireg_freeze_au]) hands it to the freezer and
           the [FrzPre -> FrzPost] step takes it back.  So "the receipt is
           in a thread's hand" IS "this inum's column reads [FrzPre]", by
           [frzown_excl] alone.
           WHY IT EXISTS.  A‴ has the free path's freeze token travel with
           the PAYLOAD (checked out at ilock, parked at iput+0x70, out again
           at +0x8a), which makes the parked arm's token conjunct a
           disjunction the +0x8a opener has to resolve -- and the walk has
           nothing to resolve it with, because the token IS the thing it
           parked.  With the receipt the walk parks THIS instead and keeps
           [ifreeze_pre] in hand, so the arm's other disjunct dies on
           [ifreeze_excl] with no region open at all.  Disjunctive rather
           than an implication so the slot stays timeless, exactly like the
           two shelter clauses above.
           A⁗ (§3.16) ADDED THE MIRROR beside it, inside the same conjunct:
           see [ireg_frzc]. *)
        ∗ ireg_frzc z f
     (* OPTION A (walk reg-fold): the per-inum registry element rides INSIDE
        the arm, coupled to pending-ness.  A NON-pending slot (in/marked)
        carries the whole [reg_full]; the PENDING arm carries a [reg_half]
        alongside [region_pending] (whose own [reg_half] is the partner).  So
        "non-pending ⟹ reg_full" is STRUCTURAL: the off-lock deposit, which
        fires at a marked slot, finds [reg_full] to split, and [ireg_claim_au]
        recombines the pending arm's two halves back to [reg_full] with no
        registry lookup.  The registry conjunct in [ireg_body] is now the bare
        [icfg_reg] auth. *)
        ∗ ((((⌜ireg_in c d⌝ ∗ z ↪[γi] d ∗ ireg_top_park γfs z d)
             ∨ (⌜ireg_marked_ok c d⌝ ∗ imark γi z))
            ∗ (∃ ge gr, reg_full z ge gr))
           ∨ (⌜bv_unsigned (di_type d) = 0⌝ ∗ z ↪[γi] d
              ∗ (∃ ge gr, reg_half z ge gr) ∗ region_pending z
              ∗ ireg_top_park γfs z d)))
     ∗ ireg_ep z d
     (* LAST, and that position is deliberate: an existing destructuring
        pattern's final name binds to [ireg_ep ∗ ireg_lnk], so only the
        sites that USE [ireg_ep] have to split (durable-notes, "WHEN A NEW
        CONJUNCT GOES INTO A PREDICATE FORTY PROOFS DESTRUCTURE"). *)
     ∗ ireg_lnk γfs z d)%I.

  Global Instance ireg_slot_timeless γfs γi z d :
    Timeless (ireg_slot γfs γi z d).
  Proof. rewrite /ireg_slot. apply _. Qed.

  (* the ledger's authority at one slot, held apart from the arm.  Both the
     ordinary flush and the free re-park the arm unchanged in SHAPE and
     move only the record, so every arm move below is stated by giving the
     new record and the new authority separately. *)
  Lemma ireg_slot_intro γfs γi z d c r f n :
    ireg_link_ok d ->
    ireg_claim_ok c f d ->
    ireg_frz_ok f n d ->
    ireg_rcol z c r f n d -∗
    ireg_ep z d -∗
    ireg_lnk γfs z d -∗
    (⌜c = None⌝ ∨ ireg_open) -∗
    icnt_half z n -∗
    ireg_shp c f -∗
    ireg_frzc z f -∗
    ((((⌜ireg_in c d⌝ ∗ z ↪[γi] d ∗ ireg_top_park γfs z d)
       ∨ (⌜ireg_marked_ok c d⌝ ∗ imark γi z))
      ∗ (∃ ge gr, reg_full z ge gr))
     ∨ (⌜bv_unsigned (di_type d) = 0⌝ ∗ z ↪[γi] d
        ∗ (∃ ge gr, reg_half z ge gr) ∗ region_pending z
        ∗ ireg_top_park γfs z d)) -∗
    ireg_slot γfs γi z d.
  Proof.
    intros Hok Hclm Hfrz.
    iIntros "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm".
    rewrite /ireg_slot.
    iFrame "Hep Hlnk".
    iExists r, c, f, n. iSplitL "Hla"; [iExact "Hla" |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hdisj"; [iExact "Hdisj" |].
    iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitR; [iPureIntro; exact Hclm |].
    iSplitR; [iPureIntro; exact Hfrz |].
    iSplitL "Hfdisj"; [iExact "Hfdisj" |].
    iSplitL "Hfrcp"; [iExact "Hfrcp" | iExact "Harm"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE REGION'S BYTE UNIT: SIXTEEN RECORD RUNS, NOT ONE BLOCK          *)
  (*  (durable-disk 2b-inode-1)                                           *)
  (*                                                                      *)
  (*  [ireg_blk] used to hold [fsblock (fs_bytes γfs) (inodestart + bi)    *)
  (*  (diblk_bytes ds)] -- the WHOLE block's exclusive byte run.  It now   *)
  (*  holds the sixteen 64-byte RECORD runs that block is made of, each    *)
  (*  spelled at the abstract view record the file-system predicates use   *)
  (*  ([FsStateInode.rec_owned_at] over [FsBytesGamma.fs_gamma_L], which   *)
  (*  is [rec_owned]'s geometry-free reading -- fs-state.md §7's B5).      *)
  (*                                                                      *)
  (*  WHY IT IS THE SAME RESOURCE AND WHY THAT MATTERS.                    *)
  (*  [FsStateInode.rec_owned_at_diblk] is the sixteen-fold split of one   *)
  (*  inode block's byte run at exactly the region's own slot indexing     *)
  (*  ([16*bi + k], [ds !!! k]), so [ireg_recs_blk] below is an [⊣⊢] and   *)
  (*  every reader that wants the block spelling (the three that agree     *)
  (*  bread bytes against the region, [ireg_read] / [ireg_read_blk] /      *)
  (*  [ireg_withdraw]) gathers it in one line.  What the change buys is    *)
  (*  the WRITER's side: a mover can surrender ONE record's run to         *)
  (*  [SpecLogWrite.wp_log_write_au_range] instead of the whole block,     *)
  (*  which is what B1 needs (two inodes of one block are checked out at   *)
  (*  once in mknod itself) and what [SpecLogWrite.lw_au_rec] is shaped    *)
  (*  for.                                                                 *)
  (* ------------------------------------------------------------------ *)
  (* THE RECORD RUN AT THE REGION'S OWN SPELLING OF ITS ADDRESS.
     [rec_owned_at Γ istart z] is "offset [64*(z mod 16)] of block
     [istart + z/16]"; a mover states its window as [DinodeEnc]'s
     [IBLOCK]/[islot] pair, which is what [SpecLogWrite.lw_au_rec] and the
     bio handle both name.  The two are the same numbers -- this is
     [FsStateInode.rec_owned_sb]'s arithmetic, read at an inum that is
     already a [bv 32] so no wrap premise is needed. *)
  Lemma rec_owned_at_IBLOCK (Γ : fs_view_names Σ) (inodestart : Z)
      (inum : bv 32) (dn : dinode) :
    rec_owned_at Γ inodestart (bv_unsigned inum) dn
    ⊣⊢ FsStateDefs.byte_range Γ (IBLOCK inum inodestart)
          (Z.of_nat (64 * islot inum)) (dinode_bytes dn).
  Proof.
    pose proof (bv_unsigned_in_range _ inum) as [Hlo _].
    pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as [Hm0 _].
    assert (Hblk : IBLOCK inum inodestart
                   = inodestart + bv_unsigned inum `div` 16)
      by (rewrite /IBLOCK; lia).
    assert (Hoff : Z.of_nat (64 * islot inum)
                   = 64 * (bv_unsigned inum `mod` 16)).
    { rewrite /islot Nat2Z.inj_mul Z2Nat.id; [reflexivity | lia]. }
    rewrite /rec_owned_at Hblk Hoff //.
  Qed.

  Definition ireg_recs (γfs : fs_names) (inodestart : Z)
      (bi : nat) (ds : list dinode) : iProp Σ :=
    ([∗ list] i ∈ seq 0 16,
       rec_owned_at (fs_gamma_L γfs) inodestart
                    (16 * Z.of_nat bi + Z.of_nat i)%Z (ds !!! i))%I.

  Global Instance ireg_recs_timeless γfs inodestart bi ds :
    Timeless (ireg_recs γfs inodestart bi ds).
  Proof. rewrite /ireg_recs. apply _. Qed.

  (* THE GATHER, and the only place [diblk_bytes] meets the region's bytes.
     [diblk_wf] is what makes the sixteen runs add up to 1024 bytes. *)
  Lemma ireg_recs_blk (γfs : fs_names) (inodestart : Z) (bi : nat)
      (ds : list dinode) :
    diblk_wf ds ->
    ireg_recs γfs inodestart bi ds
    ⊣⊢ fsblock (fs_bytes γfs) (inodestart + Z.of_nat bi) (diblk_bytes ds).
  Proof.
    intros Hwf. rewrite /ireg_recs.
    rewrite -(rec_owned_at_diblk (fs_gamma_L γfs) inodestart (Z.of_nat bi)
                ds Hwf).
    rewrite -gamma_blk_owned /blk_owned.
    (* the only thing the block spelling adds is its WIDTH, and
       [diblk_wf] is what supplies it *)
    assert (Hlb : length (diblk_bytes ds) = BioDefs.BSIZE)
      by exact (diblk_bytes_length_16 ds Hwf).
    iSplit; [iIntros "H"; iFrame "H"; iPureIntro; exact Hlb
            | iIntros "[_ H]"; iExact "H"].
  Qed.

  Lemma ireg_recs_to_blk (γfs : fs_names) (inodestart : Z) (bi : nat)
      (ds : list dinode) :
    diblk_wf ds ->
    ireg_recs γfs inodestart bi ds -∗
    fsblock (fs_bytes γfs) (inodestart + Z.of_nat bi) (diblk_bytes ds).
  Proof.
    intros Hwf. rewrite (ireg_recs_blk γfs inodestart bi ds Hwf).
    iIntros "H". iExact "H".
  Qed.

  Lemma ireg_recs_of_blk (γfs : fs_names) (inodestart : Z) (bi : nat)
      (ds : list dinode) :
    diblk_wf ds ->
    fsblock (fs_bytes γfs) (inodestart + Z.of_nat bi) (diblk_bytes ds) -∗
    ireg_recs γfs inodestart bi ds.
  Proof.
    intros Hwf. rewrite (ireg_recs_blk γfs inodestart bi ds Hwf).
    iIntros "H". iExact "H".
  Qed.

  (* ONE SLOT'S RUN OUT, with the fifteen others re-buildable at the
     retagged list -- [ireg_slots_acc_upd]'s byte-side twin, and what a
     record-granular mover surrenders to [SpecLogWrite.lw_au_rec]. *)
  Lemma ireg_recs_acc_upd (γfs : fs_names) (inodestart : Z) (bi : nat)
      (ds : list dinode) (i : nat) :
    (i < 16)%nat -> length ds = 16%nat ->
    ireg_recs γfs inodestart bi ds -∗
      rec_owned_at (fs_gamma_L γfs) inodestart
                   (16 * Z.of_nat bi + Z.of_nat i)%Z (ds !!! i) ∗
      (∀ d' : dinode,
         rec_owned_at (fs_gamma_L γfs) inodestart
                      (16 * Z.of_nat bi + Z.of_nat i)%Z d' -∗
         ireg_recs γfs inodestart bi (<[i := d']> ds)).
  Proof.
    intros Hi Hlen. rewrite /ireg_recs. iIntros "Hs".
    iDestruct (big_sepL_delete _ (seq 0 16) i i
                 ltac:(apply lookup_seq; split; [lia | exact Hi]) with "Hs")
      as "[Hone Hrest]".
    iFrame "Hone". iIntros (d') "Hone".
    iApply (big_sepL_delete _ (seq 0 16) i i
              ltac:(apply lookup_seq; split; [lia | exact Hi])).
    iSplitL "Hone".
    { rewrite list_lookup_total_insert; [iExact "Hone" | lia]. }
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = i)) as [->|Hne]; [iExact "H" |].
    apply lookup_seq in Hjx as [Hx _].
    rewrite list_lookup_total_insert_ne; [iExact "H" | lia].
  Qed.

  Definition ireg_blk (γi : gname) (γfs : fs_names) (inodestart : Z)
      (m : gmap Z dinode) (bi : nat) : iProp Σ :=
    (∃ ds : list dinode,
       ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗
       ireg_recs γfs inodestart bi ds ∗
       [∗ list] i ∈ seq 0 16,
         ireg_slot γfs γi (16 * Z.of_nat bi + Z.of_nat i)%Z (ds !!! i))%I.

  (* OPTION A (walk reg-fold): the registry conjunct in [ireg_body] is the
     bare [icfg_reg] auth (plus coverage).  Every inum's [reg_full]/[reg_half]
     fragment rides INSIDE its slot arm (see [ireg_slot]), coupled to
     pending-ness, so "non-pending ⟹ reg_full" is structural.  The auth is used
     only by the off-lock deposit (to rebind an inum's escrow-name pair) and by
     boot (to allocate); every other accessor threads it opaquely. *)
  (* N-4 PHASE B (E1-region, namei-pinned-lookup.md §11.5): the LEND COLUMN
     rides here too, one per inum.  This conjunct -- not [ireg_slot] -- is
     the lend's home for one reason: every region accessor threads
     [ireg_registry] OPAQUELY (it appears in exactly two constructions,
     boot's and the off-lock deposit's, and in thirty-odd re-parks only as
     the name "Hreg"), so hosting the column here moves NO [ireg_slot]
     lemma, no [ireg_slot_intro] arity and no accessor's destructuring
     pattern.  [dv_lcol] is all-[own], so [ireg_registry_timeless] and every
     [">"] strip above it survive verbatim.

     THE FAMILY IS INDEXED AT [icfg_nib], NOT at the region's [nib]
     parameter, and that is load-bearing: it is what lets the three
     operations state their addressing side-condition as the pure clause
     the lend's OWN tokens carry ([DirViewLend.dvl_dom], also at
     [icfg_nib]) and take NO premise relating the two.  Several mover
     sites -- [ProofIlock]'s fill among them -- hold [ireg_inv] at a [nib]
     that is never tied to [icfg_nib] by their contract, so a premise
     [nib = icfg_nib] would have been unpayable there.  Boot builds the
     family at [icfg_nib] because [ireg_alloc] is called at it. *)
  (* N-5.2A (§13 D-52c): the column is now a PAIR -- the directory-contents
     lend and the file-contents lend of the same inum, side by side.  Bundling
     them here rather than adding a second conjunct to [ireg_registry] is what
     keeps [ireg_registry]'s text, [ireg_registry_from_map]'s arity and
     [EscrowDeposit]'s rebind byte-identical: the two ghosts are independent
     (their four registry key families are disjoint by residue,
     [DirViewLend] §0), so nothing relates the two halves and the pair is
     purely a packaging choice. *)
  Definition ireg_lcols (z : Z) : iProp Σ :=
    (dv_lcol z ∗ fv_lcol z)%I.

  Definition ireg_lends : iProp Σ :=
    ([∗ list] k ∈ seq 0 (16 * icfg_nib), ireg_lcols (Z.of_nat k))%I.

  Global Instance ireg_lcols_timeless z : Timeless (ireg_lcols z).
  Proof. rewrite /ireg_lcols. apply _. Qed.

  Definition ireg_registry (nib : nat) : iProp Σ :=
    (∃ mr : gmap Z (gname * gname),
       ⌜∀ z : Z, (0 <= z < 16 * Z.of_nat nib)%Z -> is_Some (mr !! z)⌝ ∗
       ghost_map_auth icfg_reg 1 mr ∗ ireg_lends)%I.

  Global Instance ireg_lends_timeless : Timeless ireg_lends.
  Proof. rewrite /ireg_lends. apply _. Qed.
  Global Instance ireg_registry_timeless nib : Timeless (ireg_registry nib).
  Proof. rewrite /ireg_registry. apply _. Qed.

  (* Boot assembles the registry from the EMPTY [icfg_reg] auth ([icfg_alloc]'s
     new hand-out): it bulk-inserts a fully-covering map and calls this to wrap
     the raw elements as [reg_full]s.  Parametric over the map so the caller
     (IcacheBoot, where [region_inums] lives) supplies the domain; [reg_full]
     stays local to this file.  The lend column comes in beside it, in the
     NONE state at every inum ([DirViewLend.dv_lcol_boot]). *)
  Lemma ireg_registry_from_map (mr : gmap Z (gname * gname)) (nib : nat) :
    (forall z : Z, (0 <= z < 16 * Z.of_nat nib)%Z -> is_Some (mr !! z)) ->
    ghost_map_auth icfg_reg 1 mr -∗
    ireg_lends -∗
    ireg_registry nib.
  Proof.
    iIntros (Hcov) "Ha Hl". iExists mr. iSplitR; [done |]. iFrame.
  Qed.

  (* ONE INUM'S COLUMN, out of the family and back.  [big_sepL_delete] at
     the index [Z.to_nat z], which is the only place the region's flat
     [seq]-indexing meets the lend's [Z] keying. *)
  Lemma ireg_lends_acc (z : Z) :
    dvl_dom z ->
    ireg_lends -∗ ireg_lcols z ∗ (ireg_lcols z -∗ ireg_lends).
  Proof.
    rewrite /dvl_dom. intros Hz. rewrite /ireg_lends. iIntros "Hs".
    assert (Hi : seq 0 (16 * icfg_nib) !! Z.to_nat z = Some (Z.to_nat z)).
    { apply lookup_seq. split; [lia | lia]. }
    assert (Hid : Z.of_nat (Z.to_nat z) = z) by lia.
    iDestruct (big_sepL_delete _ _ (Z.to_nat z) (Z.to_nat z) Hi with "Hs")
      as "[Hone Hrest]".
    rewrite Hid. iFrame "Hone". iIntros "Hone".
    iApply (big_sepL_delete _ _ (Z.to_nat z) (Z.to_nat z) Hi).
    rewrite Hid. iFrame.
  Qed.

  Definition ireg_body (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) : iProp Σ :=
    (∃ m : gmap Z dinode,
       ghost_map_auth γi 1 m ∗
       ([∗ list] bi ∈ seq 0 nib, ireg_blk γi γfs inodestart m bi) ∗
       ireg_registry nib)%I.

  Definition iregN : namespace := nroot .@ "ireg".

  (* THE BYTE VIEW'S ROW, AS THE REGION SEES IT (durable-disk 1c-flip
     step 3).  [ireg_blk] above now holds the EXCLUSIVE byte run
     [fsblock (fs_bytes γfs)] instead of the cache's parked half, so the
     auth-free half/half agreement every reader used to close by
     entailment is gone: a reader opens [fs_bytes_inv] instead, and to do
     that it needs the invariant AND the fact that its block is one of the
     home blocks the invariant covers.

     THE HOME SET IS BOUND HERE, NOT A PARAMETER OF [ireg_inv], AND THAT
     IS A DELIBERATE DEVIATION from the flip's ruling (2) -- see
     claude-notes/projects/durable-disk.md item 1c.  Measured before
     deviating: [ireg_inv] appears in the STATEMENT of 203 definitions
     across 74 files, nearly all of them syscall-level contracts
     ([wp_sys_open_sconf_body], [SpecKexec.fs_fabric],
     [FsSyscalls.fs_world_all]) that have no business naming the block
     layer's home set and no way to obtain one; IcacheRef.v's own header
     already records that "[ireg_inv], whose arity is fixed by 30-odd fs
     contracts" is why the icfg class exists.  Threading a [gset Z]
     through all of them is the leak fs-state.md §0 forbids.

     NOTHING IS WEAKENED BY BINDING IT HERE.  The set is a [gset Z], not
     a ghost name (the ghost names ARE explicit: [fs_bytes γfs] and
     [fs_cache γfs]); the coverage clause pins everything the region can
     ever need of it -- every one of the region's own blocks is in it --
     and no consumer of the region ever mentions a home block that is not
     one of those.  A second invariant at [logN] over the same [fs_bytes
     γfs] cannot exist anyway: its body demands the byte map's AUTH, of
     which there is one. *)
  Notation ireg_bytes := fs_bytes_any (only parsing).

  (* ------------------------------------------------------------------ *)
  (*  THE ERA'S TOP MAP: WHERE ITS AUTHORITY LIVES (durable-disk         *)
  (*  2b-inode-3)                                                        *)
  (* ------------------------------------------------------------------ *)

  (* A CHECKED-OUT HOLDER CARRIES [FsState.top_frag] -- the era's abstract
     value of its inode, inside [FsStateEra.inode_owned_era] -- and a
     [ghost_map] element cannot be RETAGGED without its authority.  Every
     write in this kernel moves the node (a record write, a data block, a
     truncation), so a payload that could not retag would be immutable and
     no walk could re-park at its new value.  The authority therefore needs
     a home that a walk can reach at ANY instant.

     IT IS ITS OWN INVARIANT, NOT A CONJUNCT OF [ireg_body], for two
     reasons.  (i) A mover that has [iregN] OPEN -- every region write is
     one -- must still be able to retag; a conjunct inside the region's own
     body is unreachable there.  (ii) [ireg_body] is destructured at twenty
     accessors in this file and none of them has any business seeing the
     abstract map.  The handle rides in [ireg_inv] because that is the
     ambient FS credential every contract in the cone already carries
     (durable-notes: put a new ambient credential in the bundle the cone
     already threads).

     THE BODY IS UNTIED, AND SAYS SO.  Nothing here relates [I] to the
     bytes: stage 2c moves the whole [fs_view Γ_L] body into the log's
     parked payload, where the tie is the design's, and this invariant is
     retired with it.  What it provides in the meantime is exactly the
     UPDATE right the fragments need, which is sound at any [I]. *)
  Definition ftopN : namespace := nroot .@ "ftop".

  (* ------------------------------------------------------------------ *)
  (*  THE LOCKED REGISTRY (durable-disk lane A, plan section 4b)         *)
  (* ------------------------------------------------------------------ *)

  (* THE INVARIANT'S POINT, in one sentence: every inode the abstract map
     names is WELL-FORMED, except the ones some open transaction has said
     it is in the middle of writing.

     A transaction says so by ARMING: it hands its own transaction token
     over (it is parked here, [ftop_body]'s big-op) and takes back a
     receipt naming the inums whose row it has suspended.  It gets the
     token back by DISARMING, which is where it re-proves the row -- and
     that is free at the natural place, because a walk that re-packs its
     payload has [FsStateEra.inode_owned_era]'s [inode_local] in hand
     anyway.  So at a COMMIT, where no transaction is open at all, no
     token can be parked, no inum can be armed, and the row is
     [FsDurSnap.snap_local] of the whole map ([ireg_clean_acc]).

     WHY THE REGISTRY IS KEYED BY AN ARM ID.  An arm has to prove its key is
     not already taken, or the ghost map cannot grow.  Keyed by INUM that is
     exactly the fact nobody can produce -- "no other walk holds this inode"
     is the inode LOCK's property, and the lock is invisible here.  Keyed by
     TRANSACTION it costs the arming walk its WHOLE token, and a walk that
     has parked a SHARE of the same token elsewhere -- which is exactly what
     a transactional [ilock] does -- can then never arm at all.  So a walk
     arms BY SHARE and never by the whole token.  Keyed by an ARM ID
     it is free: the ghost step SEES the registry's own map, so
     [fresh (dom A)] is a key nobody holds, and the arm may then park ANY
     share.

     WHAT THE PARKED SHARE STILL BUYS is the one thing the commit reads off
     the registry: every entry holds a POSITIVE share of its transaction's
     [ln_tx] element, so an EMPTY [ln_tx] authority refutes every entry
     ([ireg_clean_acc]), which is all [IregClean.ireg_snap_local_acc] wants.
     And because the entry RECORDS the share, [ireg_release] hands back
     exactly what [ireg_arm] took, so a walk can recombine its token for
     [end_op].  The price is that a receipt carries a SET of inums rather
     than one, which costs the arming walk one more ghost step
     ([ireg_arm_more]) and nothing else. *)

  (* what an arm parks: its transaction's element, at the arm's own share *)
  Definition ireg_parked (e : ireg_arm_ent) : iProp Σ :=
    (e.1.1 ↪[ln_tx icfg_log]{#(e.1.2)} tt)%I.

  Global Instance ireg_parked_timeless e : Timeless (ireg_parked e).
  Proof. rewrite /ireg_parked. apply _. Qed.

  (* "arm [k] belongs to transaction [t], parked [q] of [t]'s token, and has
     suspended the row of every inum in [S]" -- the receipt.  It is the
     WHOLE registry element, hence exclusive, and it names its own set AND
     its own share, so no lemma below has to guess either. *)
  Definition ireg_armed (k t : nat) (q : Qp) (S : gset Z) : iProp Σ :=
    k ↪[icfg_lk] (t, q, S).

  Global Instance ireg_armed_timeless k t q S : Timeless (ireg_armed k t q S).
  Proof. rewrite /ireg_armed. apply _. Qed.

  (* THE ROW, as a pure statement about the two maps: an inum no armed
     transaction names is well-formed at the map's own value for it. *)
  Definition ftop_clean (I : gmap Z fs_node) (A : gmap nat ireg_arm_ent) : Prop :=
    forall (i : Z) (n : fs_node),
      I !! i = Some n ->
      (forall (k t : nat) (q : Qp) (S : gset Z),
         A !! k = Some (t, q, S) -> i ∉ S) ->
      inode_local i n.

  Definition ftop_body (γfs : fs_names) : iProp Σ :=
    (∃ (I : gmap Z fs_node) (A : gmap nat ireg_arm_ent),
       ghost_map_auth (fs_top γfs) 1 I ∗
       ghost_map_auth icfg_lk 1 A ∗
       (* the arming transactions' tokens, parked at each arm's own share:
          this is what makes "no transaction is open" imply "nothing is
          armed" *)
       ([∗ map] e ∈ A, ireg_parked e) ∗
       ⌜ftop_clean I A⌝)%I.

  Definition ftop_inv (γfs : fs_names) : iProp Σ :=
    inv ftopN (ftop_body γfs).

  Global Instance ftop_inv_persistent γfs : Persistent (ftop_inv γfs).
  Proof. apply _. Qed.

  Global Instance ftop_body_timeless γfs : Timeless (ftop_body γfs).
  Proof. rewrite /ftop_body. apply _. Qed.

  (* the empty registry's row is just "every inode is well-formed", which is
     what the boot image gives *)
  Lemma ftop_clean_empty (I : gmap Z fs_node) :
    (forall i n, I !! i = Some n -> inode_local i n) ->
    ftop_clean I ∅.
  Proof. intros Hl i n Hi _. exact (Hl i n Hi). Qed.

  Lemma ftop_alloc (E : coPset) (γfs : fs_names) (I : gmap Z fs_node) :
    (forall i n, I !! i = Some n -> inode_local i n) ->
    ghost_map_auth (fs_top γfs) 1 I -∗
    ghost_map_auth icfg_lk 1 (∅ : gmap nat ireg_arm_ent) ={E}=∗ ftop_inv γfs.
  Proof.
    iIntros (Hloc) "Ha Hlk".
    iMod (inv_alloc ftopN E (ftop_body γfs) with "[Ha Hlk]") as "#Hi".
    { iNext. rewrite /ftop_body. iExists I, ∅. iFrame "Ha Hlk".
      rewrite big_sepM_empty. iSplitR; [done|].
      iPureIntro. exact (ftop_clean_empty I Hloc). }
    iModIntro. iExact "Hi".
  Qed.

  (* ---- THE ARM: a transaction suspends its first inum's row ---------- *)

  (* ANY SHARE of the transaction's element goes in and the receipt comes
     out.  The key needs no freshness ARGUMENT: the ghost step sees the
     registry's map, so [fresh (dom A)] is free (see the header above). *)
  Lemma ireg_arm (E : coPset) (γfs : fs_names) (i : Z) (t : nat) (q : Qp) :
    ↑ftopN ⊆ E ->
    ftop_inv γfs -∗ t ↪[ln_tx icfg_log]{#q} tt ={E}=∗
      ∃ k : nat, ireg_armed k t q {[i]}.
  Proof.
    iIntros (HE) "#Hi Ht".
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb". iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    set (k := fresh (dom A)).
    assert (Hfree : A !! k = None).
    { apply not_elem_of_dom. exact (is_fresh (dom A)). }
    iMod (ghost_map_insert k (t, q, {[i]}) Hfree with "Hla") as "[Hla Hrec]".
    iMod ("Hclose" with "[Hta Hla Hpark Ht]") as "_".
    { iNext. rewrite /ftop_body. iExists I, (<[k := (t, q, {[i]})]> A).
      iFrame "Hta Hla".
      iSplitL "Hpark Ht".
      { rewrite big_sepM_insert; [| exact Hfree].
        rewrite /ireg_parked. cbn [fst snd]. iFrame "Ht Hpark". }
      iPureIntro. intros j m Hj Hun. apply (Hcl j m Hj).
      intros k' t' q' S' Hk'. apply (Hun k' t' q' S').
      rewrite lookup_insert_ne; [exact Hk' |].
      intros ->. rewrite Hfree in Hk'. discriminate. }
    iModIntro. iExists k. iExact "Hrec".
  Qed.

  (* ...and the WHOLE-token reading, for a walk that has parked nothing
     elsewhere: it is [ireg_arm] at [q = 1], and [ireg_release_tx] undoes
     it.  [create] is the one walk in this kernel that arms, and this is the
     form it takes until a transactional [ilock] starts parking shares. *)
  Lemma ireg_arm_tx (E : coPset) (γfs : fs_names) (i : Z) :
    ↑ftopN ⊆ E ->
    ftop_inv γfs -∗ log_tx icfg_log ={E}=∗
      ∃ k t : nat, ireg_armed k t 1%Qp {[i]}.
  Proof.
    iIntros (HE) "#Hi Htx". rewrite /log_tx. iDestruct "Htx" as (t) "Ht".
    iMod (ireg_arm E γfs i t 1%Qp HE with "Hi Ht") as (k) "Hrec".
    iModIntro. iExists k, t. iExact "Hrec".
  Qed.

  (* ---- ...AND ONE MORE INUM UNDER THE SAME TRANSACTION --------------- *)

  Lemma ireg_arm_more (E : coPset) (γfs : fs_names) (k t : nat) (q : Qp)
      (S : gset Z) (i : Z) :
    ↑ftopN ⊆ E ->
    ftop_inv γfs -∗ ireg_armed k t q S ={E}=∗ ireg_armed k t q ({[i]} ∪ S).
  Proof.
    iIntros (HE) "#Hi Hrec". rewrite /ireg_armed.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb". iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hla Hrec") as %HAt.
    iMod (ghost_map_update (t, q, {[i]} ∪ S) with "Hla Hrec") as "[Hla Hrec]".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, (<[k := (t, q, {[i]} ∪ S)]> A).
      iFrame "Hta Hla".
      iSplitL "Hpark".
      { rewrite (big_sepM_delete _ (<[k := (t, q, {[i]} ∪ S)]> A) k
                   (t, q, {[i]} ∪ S)); [| by rewrite lookup_insert].
        rewrite (big_sepM_delete _ A k (t, q, S)); [| exact HAt].
        iDestruct "Hpark" as "[Ht Hrest]".
        rewrite /ireg_parked. cbn [fst snd]. iFrame "Ht".
        rewrite delete_insert_delete. iExact "Hrest". }
      iPureIntro. intros j m Hj Hun. apply (Hcl j m Hj).
      intros k' t' q' S' Hk'. destruct (decide (k' = k)) as [->|Hne].
      - rewrite HAt in Hk'. injection Hk' as <- <- <-.
        (* the inline [ltac:] is the recorded trap: the expected type is an
           evar at elaboration time, so the rewrite has nothing to match *)
        assert (Hlk : <[k := (t, q, {[i]} ∪ S)]> A !! k
                      = Some (t, q, {[i]} ∪ S)) by apply lookup_insert.
        specialize (Hun k t q ({[i]} ∪ S) Hlk).
        set_unfold in Hun. intros Hin. apply Hun. right. exact Hin.
      - apply (Hun k' t' q' S').
        rewrite lookup_insert_ne; [exact Hk' | exact (not_eq_sym Hne)]. }
    iModIntro. iExact "Hrec".
  Qed.

  (* ---- THE DISARM: the row comes back, one inum at a time ------------ *)

  (* The walk presents its fragment at the node it is releasing and the
     WELL-FORMEDNESS of that node -- which is free where a payload is
     re-packed ([FsStateEra.inode_owned_era] carries it). *)
  Lemma ireg_disarm (E : coPset) (γfs : fs_names) (k t : nat) (q : Qp)
      (S : gset Z) (i : Z) (n : fs_node) :
    ↑ftopN ⊆ E ->
    inode_local i n ->
    ftop_inv γfs -∗ ireg_armed k t q S -∗ top_frag (fs_gamma_L γfs) i n ={E}=∗
      ireg_armed k t q (S ∖ {[i]}) ∗ top_frag (fs_gamma_L γfs) i n.
  Proof.
    iIntros (HE Hloc) "#Hi Hrec Hfr". rewrite /ireg_armed.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb". iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hla Hrec") as %HAt.
    rewrite /top_frag /fs_gamma_L /=.
    iDestruct (ghost_map_lookup with "Hta Hfr") as %HIi.
    iMod (ghost_map_update (t, q, S ∖ {[i]}) with "Hla Hrec") as "[Hla Hrec]".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, (<[k := (t, q, S ∖ {[i]})]> A).
      iFrame "Hta Hla".
      iSplitL "Hpark".
      { rewrite (big_sepM_delete _ (<[k := (t, q, S ∖ {[i]})]> A) k
                   (t, q, S ∖ {[i]})); [| by rewrite lookup_insert].
        rewrite (big_sepM_delete _ A k (t, q, S)); [| exact HAt].
        iDestruct "Hpark" as "[Ht Hrest]".
        rewrite /ireg_parked. cbn [fst snd]. iFrame "Ht".
        rewrite delete_insert_delete. iExact "Hrest". }
      iPureIntro. intros j m Hj Hun.
      destruct (decide (j = i)) as [->|Hne].
      { rewrite HIi in Hj. injection Hj as <-. exact Hloc. }
      apply (Hcl j m Hj). intros k' t' q' S' Hk'.
      destruct (decide (k' = k)) as [->|Hnt].
      - rewrite HAt in Hk'. injection Hk' as <- <- <-.
        assert (Hlk : <[k := (t, q, S ∖ {[i]})]> A !! k
                      = Some (t, q, S ∖ {[i]})) by apply lookup_insert.
        specialize (Hun k t q (S ∖ {[i]}) Hlk).
        intros Hin. apply Hun. set_unfold. split; [exact Hin | exact Hne].
      - apply (Hun k' t' q' S').
        rewrite lookup_insert_ne; [exact Hk' | exact (not_eq_sym Hnt)]. }
    iModIntro. iFrame "Hrec Hfr".
  Qed.

  (* ...and when nothing is left armed, the transaction's token comes home *)
  Lemma ireg_release (E : coPset) (γfs : fs_names) (k t : nat) (q : Qp) :
    ↑ftopN ⊆ E ->
    ftop_inv γfs -∗ ireg_armed k t q ∅ ={E}=∗ t ↪[ln_tx icfg_log]{#q} tt.
  Proof.
    iIntros (HE) "#Hi Hrec". rewrite /ireg_armed.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb". iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hla Hrec") as %HAt.
    rewrite (big_sepM_delete _ A k (t, q, ∅)); [| exact HAt].
    iDestruct "Hpark" as "[Ht Hpark]".
    rewrite /ireg_parked. cbn [fst snd].
    iMod (ghost_map_delete with "Hla Hrec") as "Hla".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, (delete k A).
      iFrame "Hta Hla Hpark".
      iPureIntro. intros j m Hj Hun. apply (Hcl j m Hj).
      intros k' t' q' S' Hk'. destruct (decide (k' = k)) as [->|Hne].
      - rewrite HAt in Hk'. injection Hk' as <- <- <-. apply not_elem_of_empty.
      - apply (Hun k' t' q' S').
        rewrite lookup_delete_ne; [exact Hk' | exact (not_eq_sym Hne)]. }
    iModIntro. iExact "Ht".
  Qed.

  (* ...and the WHOLE-token reading, [ireg_arm_tx]'s undo *)
  Lemma ireg_release_tx (E : coPset) (γfs : fs_names) (k t : nat) :
    ↑ftopN ⊆ E ->
    ftop_inv γfs -∗ ireg_armed k t 1%Qp ∅ ={E}=∗ log_tx icfg_log.
  Proof.
    iIntros (HE) "#Hi Hrec".
    iMod (ireg_release E γfs k t 1%Qp HE with "Hi Hrec") as "Ht".
    iModIntro. rewrite /log_tx. iExists t. iExact "Ht".
  Qed.

  (* ---- THE COMMIT'S READING (lane A item 5) -------------------------- *)

  (* No open transaction means no armed inum means the whole abstract map is
     well-formed -- [FsDurSnap.snap_local] of any state whose inodes are
     [I].  The committer holds the log's own transaction AUTHORITY (it is a
     conjunct of [LogInv.log_res], and [LogInv.log_tx_empty_of_ops] is what
     turns "the ledger is empty" into "the authority is empty"), so the
     reading costs it nothing but this accessor. *)
  Lemma ireg_clean_acc (E : coPset) (γfs : fs_names) :
    ↑ftopN ⊆ E ->
    ftop_inv γfs -∗
    ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) ={E, E ∖ ↑ftopN}=∗
      ∃ I : gmap Z fs_node,
        ghost_map_auth (fs_top γfs) 1 I ∗
        ⌜forall i n, I !! i = Some n -> inode_local i n⌝ ∗
        ghost_map_auth (ln_tx icfg_log) 1 (∅ : gmap nat unit) ∗
        (ghost_map_auth (fs_top γfs) 1 I ={E ∖ ↑ftopN, E}=∗ True).
  Proof.
    iIntros (HE) "#Hi Htxa".
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb". iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    (* nothing is armed: an entry would park a token the empty authority
       cannot account for *)
    iAssert (⌜A = ∅⌝)%I as %HA.
    { destruct (decide (A = ∅)) as [->|Hne]; [done |].
      apply map_choose in Hne as (k & e & HAk).
      iDestruct (big_sepM_lookup _ _ k e HAk with "Hpark") as "Ht".
      rewrite /ireg_parked.
      iDestruct (ghost_map_lookup with "Htxa Ht") as %Hbad.
      rewrite lookup_empty in Hbad. discriminate. }
    subst A.
    iModIntro. iExists I. iFrame "Hta Htxa".
    iSplitR.
    { iPureIntro. intros i n Hi. apply (Hcl i n Hi).
      intros k' t' q' S' Hk'. rewrite lookup_empty in Hk'. discriminate. }
    iIntros "Hta". iApply "Hclose". iNext. rewrite /ftop_body.
    iExists I, ∅. iFrame "Hta Hla". rewrite big_sepM_empty.
    iSplitR; [done |]. iPureIntro. exact Hcl.
  Qed.

  (* THE REGION AT POWERON, BEFORE RECOVERY HAS RUN (durable-disk lane
     E-except).  Its byte row is the bare [FsBlocks.fs_bytes_row]: the
     era's mint runs at PowerOn, when the byte view's exception set may
     still be nonempty, so nothing minted there can carry the seal.  This
     is the form [IcacheBoot.ireg_alloc] produces and the form the ONE
     pre-recovery reader of the region -- boot's [userinit] running
     [namei("/")] through [iget] -- takes; that reader's own crossing is
     licensed by the [BufL] row's carried seal, not by this bundle. *)
  Definition ireg_reg (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) : iProp Σ :=
    (inv iregN (ireg_body γi γfs inodestart nib) ∗
     fs_bytes_row γfs ∗ ftop_inv γfs)%I.

  (* ...AND THE REGION EVERY OTHER CONSUMER TAKES: the same three rows with
     the byte row SEALED.  fsinit builds it out of [ireg_reg] and the seal
     [initlog] made, and it is what [FsReady.fs_ready] carries, so not one
     [ilock]/[ialloc]/[iput]/[iupdate] site had to learn about the window. *)
  Definition ireg_inv (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) : iProp Σ :=
    (inv iregN (ireg_body γi γfs inodestart nib) ∗
     ireg_bytes γfs ∗ ftop_inv γfs)%I.

  Global Instance ireg_reg_persistent γi γfs inodestart nib :
    Persistent (ireg_reg γi γfs inodestart nib).
  Proof. apply _. Qed.

  Global Instance ireg_inv_persistent γi γfs inodestart nib :
    Persistent (ireg_inv γi γfs inodestart nib).
  Proof. apply _. Qed.

  Lemma ireg_inv_reg γi γfs inodestart nib :
    ireg_inv γi γfs inodestart nib -∗ ireg_reg γi γfs inodestart nib.
  Proof.
    iIntros "($ & Hb & $)". iApply (fs_bytes_any_row with "Hb").
  Qed.

  Lemma ireg_inv_of γi γfs inodestart nib :
    ireg_reg γi γfs inodestart nib -∗ exc_sealed (fs_exc γfs) -∗
    ireg_inv γi γfs inodestart nib.
  Proof. iIntros "($ & Hb & $) Hs". iFrame. Qed.

  Lemma ireg_inv_bytes γi γfs inodestart nib :
    ireg_inv γi γfs inodestart nib -∗ fs_bytes_any γfs.
  Proof. iIntros "(_ & $ & _)". Qed.

  Lemma ireg_inv_ftop γi γfs inodestart nib :
    ireg_inv γi γfs inodestart nib -∗ ftop_inv γfs.
  Proof. iIntros "(_ & _ & $)". Qed.

  (* THE RETAG, ALONE.  A walk that has already moved the region's record
     proxy (iupdate did it, at the region's own AU) and only owes the
     abstract value takes this one; it opens nothing but [ftopN].

     IT NOW CARRIES THE ROW (durable-disk lane A, plan section 4b): the new
     node has to be well-formed, because the map the walk is moving is the
     one a commit reads.  A walk whose write leaves the inode HALF-BUILT --
     create's mkdir child between its [nlink = 1] and its two dot entries,
     itrunc between the cleared pointers and the zeroed size -- takes
     [ireg_top_retag_armed] instead, having suspended the row first
     ([ireg_arm]).  The obligation is free at every other site: they
     re-establish exactly these facts to re-pack their payload anyway, and
     [FsStateEra.inode_local_of_ok_rec] is the one line that assembles
     them. *)
  Lemma ireg_top_retag (E : coPset) (γfs : fs_names) (i : Z)
      (n n' : fs_node) :
    ↑ftopN ⊆ E ->
    inode_local i n' ->
    ftop_inv γfs -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗ top_frag (fs_gamma_L γfs) i n'.
  Proof.
    iIntros (HE Hloc) "#Hi Hf".
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb". iDestruct "Hb" as (I A) "(Ha & Hla & Hpark & %Hcl)".
    rewrite /top_frag /fs_gamma_L /=.
    iMod (ghost_map_update n' with "Ha Hf") as "[Ha Hf]".
    iMod ("Hclose" with "[Ha Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[i := n']> I), A.
      iFrame "Ha Hla Hpark". iPureIntro.
      intros j m Hj Hun. destruct (decide (j = i)) as [->|Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl j m Hj Hun). }
    iModIntro. iExact "Hf".
  Qed.

  (* ...and the SUSPENDED form: the walk holds a receipt naming this inum,
     so the row says nothing about it and the new node may be anything. *)
  Lemma ireg_top_retag_armed (E : coPset) (γfs : fs_names) (k t : nat)
      (q : Qp) (S : gset Z) (i : Z) (n n' : fs_node) :
    ↑ftopN ⊆ E ->
    i ∈ S ->
    ftop_inv γfs -∗ ireg_armed k t q S -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗
      ireg_armed k t q S ∗ top_frag (fs_gamma_L γfs) i n'.
  Proof.
    iIntros (HE Hin) "#Hi Hrec Hf". rewrite /ireg_armed.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as ">Hb". iDestruct "Hb" as (I A) "(Ha & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hla Hrec") as %HAt.
    rewrite /top_frag /fs_gamma_L /=.
    iMod (ghost_map_update n' with "Ha Hf") as "[Ha Hf]".
    iMod ("Hclose" with "[Ha Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[i := n']> I), A.
      iFrame "Ha Hla Hpark". iPureIntro.
      intros j m Hj Hun. destruct (decide (j = i)) as [->|Hne].
      - (* this inum IS armed, so the row's own hypothesis is refuted *)
        exfalso. exact (Hun k t q S HAt Hin).
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl j m Hj Hun). }
    iModIntro. iFrame "Hrec Hf".
  Qed.

  (* [logN], [iregN] and [ftopN] are pairwise distinct namespaces, so a
     reader that has one open may still open the others. *)
  Lemma logN_iregN_disj : (↑logN : coPset) ## ↑iregN.
  Proof. solve_ndisj. Qed.

  Lemma logN_ftopN_disj : (↑logN : coPset) ## ↑ftopN.
  Proof. solve_ndisj. Qed.

  Lemma iregN_ftopN_disj : (↑iregN : coPset) ## ↑ftopN.
  Proof. solve_ndisj. Qed.


  Global Instance ireg_blk_timeless γi γfs inodestart m bi :
    Timeless (ireg_blk γi γfs inodestart m bi).
  Proof. rewrite /ireg_blk. apply _. Qed.

  Global Instance ireg_body_timeless γi γfs inodestart nib :
    Timeless (ireg_body γi γfs inodestart nib).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  The block accessor (writer form)                                   *)
  (* ------------------------------------------------------------------ *)

  (* a block's conjunct only reads the map at its OWN sixteen keys *)
  Lemma ireg_blk_mono (γi : gname) (γfs : fs_names) (inodestart : Z)
      (m m' : gmap Z dinode) (bi : nat) :
    (forall i : nat, (i < 16)%nat ->
       m' !! (16 * Z.of_nat bi + Z.of_nat i)%Z
       = m !! (16 * Z.of_nat bi + Z.of_nat i)%Z) ->
    ireg_blk γi γfs inodestart m bi -∗ ireg_blk γi γfs inodestart m' bi.
  Proof.
    intros Hag. rewrite /ireg_blk.
    iIntros "(%ds & %Hwf & %Hcp & Hfsb & Hsl)".
    iExists ds. iFrame "Hfsb Hsl". iSplitR; [done |].
    iPureIntro. intros i Hi. rewrite (Hag i Hi). exact (Hcp i Hi).
  Qed.

  (* the big-op's slot [bi], with the rest re-buildable at a map that
     changed only at [bi]'s keys -- IcacheInv.live_pool_acc_upd's shape *)
  Lemma ireg_blks_acc_upd (γi : gname) (γfs : fs_names) (inodestart : Z)
      (m : gmap Z dinode) (nib bi : nat) :
    (bi < nib)%nat ->
    ([∗ list] j ∈ seq 0 nib, ireg_blk γi γfs inodestart m j) -∗
      ireg_blk γi γfs inodestart m bi ∗
      (∀ m' : gmap Z dinode,
         ⌜forall (j i : nat), j <> bi -> (i < 16)%nat ->
            m' !! (16 * Z.of_nat j + Z.of_nat i)%Z
            = m !! (16 * Z.of_nat j + Z.of_nat i)%Z⌝ -∗
         ireg_blk γi γfs inodestart m' bi -∗
         [∗ list] j ∈ seq 0 nib, ireg_blk γi γfs inodestart m' j).
  Proof.
    intros Hbi. iIntros "Hs".
    iDestruct (big_sepL_delete _ (seq 0 nib) bi bi
                 ltac:(apply lookup_seq; split; [lia | exact Hbi]) with "Hs")
      as "[Hblk Hrest]".
    iFrame "Hblk". iIntros (m') "%Hag Hblk".
    iApply (big_sepL_delete _ (seq 0 nib) bi bi
              ltac:(apply lookup_seq; split; [lia | exact Hbi])).
    iFrame "Hblk".
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = bi)) as [->|Hne]; [iExact "H" |].
    apply lookup_seq in Hjx as [Hx _].
    iApply (ireg_blk_mono with "H").
    intros i Hi. apply Hag; [lia | exact Hi].
  Qed.

  (* ONE SLOT OF ONE BLOCK, with the fifteen others re-buildable at the
     retagged list.  Every arm move below (the claim, the flush, the free,
     the withdrawal) goes through exactly this accessor. *)
  Lemma ireg_slots_acc_upd (γfs : fs_names) (γi : gname) (bi : nat)
      (ds : list dinode) (i : nat) :
    (i < 16)%nat -> length ds = 16%nat ->
    ([∗ list] j ∈ seq 0 16,
       ireg_slot γfs γi (16 * Z.of_nat bi + Z.of_nat j)%Z (ds !!! j)) -∗
      ireg_slot γfs γi (16 * Z.of_nat bi + Z.of_nat i)%Z (ds !!! i) ∗
      (∀ d' : dinode,
         ireg_slot γfs γi (16 * Z.of_nat bi + Z.of_nat i)%Z d' -∗
         [∗ list] j ∈ seq 0 16,
           ireg_slot γfs γi (16 * Z.of_nat bi + Z.of_nat j)%Z
                     ((<[i := d']> ds) !!! j)).
  Proof.
    intros Hi Hlen. iIntros "Hs".
    iDestruct (big_sepL_delete _ (seq 0 16) i i
                 ltac:(apply lookup_seq; split; [lia | exact Hi]) with "Hs")
      as "[Hone Hrest]".
    iFrame "Hone". iIntros (d') "Hone".
    iApply (big_sepL_delete _ (seq 0 16) i i
              ltac:(apply lookup_seq; split; [lia | exact Hi])).
    iSplitL "Hone".
    { rewrite list_lookup_total_insert; [iExact "Hone" | lia]. }
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = i)) as [->|Hne]; [iExact "H" |].
    apply lookup_seq in Hjx as [Hx _].
    rewrite list_lookup_total_insert_ne; [iExact "H" | lia].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  ilock's READ (§12.2): one mask-preserving opening                  *)
  (* ------------------------------------------------------------------ *)

  (* The caller is between bread and brelse, so its handle's payload
     carries the block's machinery half at the returned bytes [bsl]; that
     half against the region's client half pins [bsl] to the parked list's
     bytes, and the coupling against [dinode_at] names the caller's slot.
     Everything goes back; only pure facts come out. *)
  Lemma ireg_read (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (b : Z) (bsl : list (bv 8)) :
    ↑iregN ⊆ E ->
    (* THE FLIP'S ONE ADDITION (durable-disk 1c-flip step 3): the region
       holds the block's EXCLUSIVE byte run, not a cache half, so pinning
       the caller's bread bytes is an OPEN of the byte view's invariant
       rather than an auth-free agreement. *)
    ↑logN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    b = IBLOCK inum inodestart ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    (b ↪[fs_cache γfs]{#(1/2)} bsl) ={E}=∗
    ⌜exists ds : list dinode,
       diblk_wf ds /\ bsl = diblk_bytes ds /\ ds !!! islot inum = dn⌝ ∗
    dinode_at γi inum dn ∗ (b ↪[fs_cache γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE HEl Hin Hb) "#Hinv Hdn Hhalf".
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iDestruct "Hrb" as "[Hrb0 #Hseal]".
    iDestruct "Hrb0" as (home Xv) "#Hbinv".
    assert (HlogI : (↑logN : coPset) ⊆ E ∖ ↑iregN)
      by (apply subseteq_difference_r; [apply logN_iregN_disj | exact HEl]).
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hrec & Hsl)".
    (* the sixteen record runs, gathered into the block spelling
       [fs_bytes_agree] takes (durable-disk 2b-inode-1) *)
    iDestruct (ireg_recs_to_blk γfs inodestart (ireg_bi inum) ds Hwf
                with "Hrec") as "Hfsb".
    rewrite -(ireg_bi_iblock inum inodestart) -Hb.
    iMod (fs_bytes_agree (E ∖ ↑iregN) (fs_bytes γfs) (fs_cache γfs)
            (fs_exc γfs) home Xv b (diblk_bytes ds) bsl HlogI
            with "Hbinv Hseal Hfsb Hhalf") as "(%Hbytes & Hfsb & Hhalf)".
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hslot : ds !!! islot inum = dn).
    { pose proof (islot_lt inum) as Hsl.
      specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Hsl Hback]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Hsl]"); [done |].
      iExists ds. rewrite (ireg_bi_iblock inum inodestart) in Hb.
      rewrite Hb. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb";
        [iApply (ireg_recs_of_blk γfs inodestart (ireg_bi inum) ds Hwf
                   with "Hfsb") | iExact "Hsl"]. }
    iModIntro. iFrame "Hdn Hhalf". iPureIntro.
    exists ds. auto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE OBSERVATION, AT THE INVARIANT (fs-log.md §G.4/§G.17)           *)
  (* ------------------------------------------------------------------ *)

  (* THE MINT, at the shape of the nlink guard both walkers already execute
     (namex +0xce, create +0x2a).  The observer holds this inum's fragment
     -- so the region's record IS the one it read -- and its own op's epoch
     bound, which rides [log_opSe] since §G.13.  What comes back is
     persistent and inum-keyed, so it travels the whole walk down to the
     [iput] with nothing to manage.

     No sleeplock is involved and none is needed: the fragment is what pins
     the record, and [ireg_inv] is an ordinary invariant. *)
  Lemma ireg_obs_mint (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (γ : log_names) (e0 : nat) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    γ = icfg_log ->
    bv_unsigned (di_nlink dn) <> 0 ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    log_epoch_lb γ e0 ={E}=∗
    dinode_at γi inum dn ∗ nlz_obs (bv_unsigned inum) e0.
  Proof.
    iIntros (HE Hin Hγ Hnz) "#Hinv Hdn #Hlb0". subst γ.
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iEval (rewrite Hdeq) in "Hep".
    iMod (ireg_ep_mint (bv_unsigned inum) dn icfg_log e0 eq_refl Hnz
            with "Hep Hlb0") as "[Hep #Hobs]".
    iEval (rewrite -Hdeq) in "Hep".
    iMod ("Hclose" with "[Ha Hreg Hfsb Hla Hep Hlnk Harm Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Hla Hep Hlnk Harm Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hla Hep Hlnk Harm Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                cl rl fz cn Hlok Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn". iExact "Hobs".
  Qed.

  (* THE CONSUMPTION -- G-3's [crz] premise, produced.  The holder sees a
     ZERO nlink at an inum it observed NONZERO at [e0] inside its own
     still-open op; out comes a log witness for this inum's block at an
     epoch no earlier than [e0], which is exactly what
     [LogInv.log_use_group] spends to conclude "the block is in THIS
     batch's header", i.e. that the freeing iupdate absorbs.

     [1 <= e0] is the genesis-epoch premise: the log starts at epoch one
     (ProofInitlog), so every op's birth epoch is at least one and the
     [⌜v = 0⌝] boot corner cannot survive [e0 <= v]. *)
  Lemma ireg_obs_use (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (γ : log_names) (e0 : nat) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    γ = icfg_log ->
    bv_unsigned (di_nlink dn) = 0 ->
    (1 <= e0)%nat ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    nlz_obs (bv_unsigned inum) e0 ={E}=∗
    dinode_at γi inum dn ∗
    ∃ e : nat, ⌜(e0 <= e)%nat⌝ ∗ logged_at γ e (IBLOCK inum icfg_ist).
  Proof.
    iIntros (HE Hin Hγ Hz He0) "#Hinv Hdn #Hobs". subst γ.
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iEval (rewrite Hdeq) in "Hep".
    iDestruct (ireg_ep_use (bv_unsigned inum) dn icfg_log e0 eq_refl Hz He0
                 with "Hep Hobs") as "[Hep #Hwit]".
    iEval (rewrite -Hdeq) in "Hep".
    iMod ("Hclose" with "[Ha Hreg Hfsb Hla Hep Hlnk Harm Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Hla Hep Hlnk Harm Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hla Hep Hlnk Harm Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                cl rl fz cn Hlok Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn". iExact "Hwit".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE FRAGMENT-FREE BLOCK READ -- ialloc's and ireclaim's side        *)
  (* ------------------------------------------------------------------ *)

  (* [ireg_read] above needs a [dinode_at] because it is answering "which
     record is MINE"; a SCAN does not ask that.  ialloc and ireclaim bread
     a dinode block and read the type/nlink halfwords of records they hold
     no fragment for -- all they need is that the bytes bread returned
     DECODE, i.e. that they are [diblk_bytes] of a well-formed list.  That
     follows from the caller's machinery half alone (it pins the region's
     parked bytes), so no fragment is involved and the opening is
     mask-preserving.

     Stated on the block INDEX rather than on an inum, because the scan
     names blocks and its sixteen records share one opening.             *)
  Lemma ireg_read_blk (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (bi : nat) (bsl : list (bv 8)) :
    ↑iregN ⊆ E ->
    (* see [ireg_read] (durable-disk 1c-flip step 3) *)
    ↑logN ⊆ E ->
    (bi < nib)%nat ->
    ireg_inv γi γfs inodestart nib -∗
    ((inodestart + Z.of_nat bi) ↪[fs_cache γfs]{#(1/2)} bsl) ={E}=∗
    ⌜exists ds : list dinode, diblk_wf ds /\ bsl = diblk_bytes ds⌝ ∗
    ((inodestart + Z.of_nat bi) ↪[fs_cache γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE HEl Hbi) "#Hinv Hhalf".
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iDestruct "Hrb" as "[Hrb0 #Hseal]".
    iDestruct "Hrb0" as (home Xv) "#Hbinv".
    assert (HlogI : (↑logN : coPset) ⊆ E ∖ ↑iregN)
      by (apply subseteq_difference_r; [apply logN_iregN_disj | exact HEl]).
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib bi Hbi with "Hblks")
      as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hrec & Hsl)".
    iDestruct (ireg_recs_to_blk γfs inodestart bi ds Hwf with "Hrec")
      as "Hfsb".
    iMod (fs_bytes_agree (E ∖ ↑iregN) (fs_bytes γfs) (fs_cache γfs)
            (fs_exc γfs) home Xv (inodestart + Z.of_nat bi) (diblk_bytes ds)
            bsl HlogI with "Hbinv Hseal Hfsb Hhalf")
      as "(%Hbytes & Hfsb & Hhalf)".
    iMod ("Hclose" with "[Ha Hreg Hfsb Hsl Hback]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Hsl]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb";
        [iApply (ireg_recs_of_blk γfs inodestart bi ds Hwf with "Hfsb")
        | iExact "Hsl"]. }
    iModIntro. iFrame "Hhalf". iPureIntro. exists ds. split; [exact Hwf | exact Hbytes].
  Qed.

  (* The scan's per-record consequence: the slot the arithmetic lands on
     is a well-formed dinode of the decoded list, and the coupling names
     the region's map value there.  (Pure, and stated so a caller that has
     just run [ireg_read_blk] can name the record it is about to test.) *)
  Lemma ireg_blk_slot (ds : list dinode) (i : nat) :
    diblk_wf ds -> (i < 16)%nat -> dinode_wf (ds !!! i).
  Proof.
    intros [Hlen Hall] Hi.
    assert (Hl : ds !! i = Some (ds !!! i))
      by (apply list_lookup_lookup_total_lt; lia).
    exact (Forall_lookup_1 _ _ _ _ Hall Hl).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE FOUR ARM MOVES (§12.2 for the first, §16.3/§16.4 for the rest)  *)
  (* ------------------------------------------------------------------ *)

  (* Exactly the shape SpecLogWrite's generalized byte-run premise takes:
     the fupd opens the region and surrenders the block's client half at
     whatever the parked bytes are; log_write's own [fsblock_update]
     agreement (against the machinery half in the caller's handle) is what
     delivers [bsl' = diblk_bytes ds], and [diblk_bytes_inj] then pins the
     parked LIST to the [ds] the caller learned at its bread.  The closing
     wand takes the half back at the flushed bytes, retags the caller's
     [dinode_at] against the authority, and re-couples the block.

     THE TYPE PREMISE (§16.4).  Since §16.3 a FREE record's fragment lives
     in the invariant, so an unconditional payout would be wrong for a
     type-0 [dn']: the slot's arm has to flip and the marker has to come
     out.  That is [EscrowDeposit.ireg_free_deposit_au] below; this lemma keeps the arm where it
     is and therefore demands an allocated [dn'].  Every ordinary caller
     has it from [InodeLock.inode_ok].

     THE TYPE-STABILITY PREMISE (fs-icache.md §19.6 Part 1, fs-sysfile S5d).
     Before it, the only constraint on the flushed record's type was the
     nonzero-ness above, so ANY holder of [dinode_at γi inum dn] could
     RETYPE the inode and re-establish the invariant -- i.e. no-writer-
     retypes-an-allocated-inode was a fact about this tree's callers and
     not a theorem of the model, which is what §19.1(i) refuted.  With the
     disjunction below it IS a theorem of the region: a flush either clears
     the type (iput's [ip->type = 0], the LEFT disjunct -- and that route
     actually leaves through [EscrowDeposit.ireg_free_deposit_au], so here the left disjunct is
     dead against [Hnz] and only records the shape) or leaves it exactly
     where it was.  The premise only TRAVELS: the proof body does not move,
     and every caller in the tree discharges it today ([ProofWritei] and
     [ProofItrunc] from their own [wi_dinode]/size-only updates,
     [ProofCreate] from [ProofCreateParts.cr_setf], [ProofIput]'s free path
     at the left disjunct). *)
  Lemma ireg_write_au (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (bsl : list (bv 8)) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    di_nlink_stable dn' dn ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    (* EXACTLY [SpecLogWrite.lw_au_rec]'s premise (durable-disk 2b-inode-1):
       the region surrenders THIS RECORD's 64-byte run at [64 * islot inum]
       of its inode block and takes it back at the flushed record's bytes.
       [bsl] is the checked-out buffer's logged content, and it appears
       ONLY in the wand's ignored equality: the log's tie is what tells a
       whole-block writer which bytes it had, and a record writer does not
       need to be told -- the run IS the fact.  Keeping the premise makes
       this fupd literally [lw_au_rec]'s left-hand side, so a caller plugs
       it in with one [iApply]. *)
    |={E, E ∖ ↑iregN}=> ∃ rec_old : list (bv 8),
      ⌜length rec_old = 64%nat⌝ ∗
      FsStateDefs.byte_range (fs_gamma_L γfs) (IBLOCK inum inodestart)
        (Z.of_nat (64 * islot inum)) rec_old ∗
      (⌜rec_old = take 64%nat (drop (64 * islot inum)%nat bsl)⌝ -∗
       FsStateDefs.byte_range (fs_gamma_L γfs) (IBLOCK inum inodestart)
         (Z.of_nat (64 * islot inum)) (dinode_bytes dn')
       ={E ∖ ↑iregN, E}=∗ dinode_at γi inum dn').
  Proof.
    iIntros (HE Hin Hdn' Hnz Hstab Hnl) "#Hinv Hdn".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp0 & >Hrec & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    (* THE COUPLING NAMES THE REGION'S RECORD AT THIS SLOT, and the caller's
       own fragment is what reads it off the authority.  This is what
       [diblk_bytes_inj] used to do through the block's bytes; at record
       granularity the ghost map says it directly. *)
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    assert (Hdnwf : dinode_wf dn)
      by (rewrite -Hdeq; exact (ireg_blk_slot ds (islot inum) Hwf Hsl)).
    assert (Hwfi : diblk_wf (<[islot inum := dn']> ds))
      by exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn').
    (* THIS SLOT'S RUN OUT of the sixteen, with the other fifteen
       re-buildable at the retagged list *)
    iDestruct (ireg_recs_acc_upd γfs inodestart (ireg_bi inum) ds (islot inum)
                 Hsl Hlen16 with "Hrec") as "[Hrun Hrecback]".
    iEval (rewrite Hkey Hdeq) in "Hrun".
    iEval (rewrite (rec_owned_at_IBLOCK (fs_gamma_L γfs) inodestart inum dn))
      in "Hrun".
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    (* THE ARM IS THE OUT ONE: the region cannot also hold this inum's
       fragment, because the caller does ([dinode_at_excl]). *)
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(_ & Hpz & _)"; iExFalso; iApply (dinode_at_excl with "Hpz Hdn")].
    iDestruct "Harm" as "[[%Hin1 [Hfr Hpk]] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite Hdeq in Hlok. rewrite Hdeq in Hclm. rewrite Hdeq in Hfrz.
    iModIntro. iExists (dinode_bytes dn).
    iSplitR; [iPureIntro; exact (dinode_bytes_length dn Hdnwf) |].
    iFrame "Hrun".
    iIntros (_) "Hrun".
    (* (L1) RIDES ON [di_nlink_stable]'s first conjunct: [nlink] does not
       move across an ordinary flush, so the cap the ledger already had is
       the SAME cap -- one rewrite, no arithmetic.  (L3) is vacuous -- an
       ordinary flush writes a nonzero type, which is [Hnz], and the
       clearing flush leaves through [EscrowDeposit.ireg_free_deposit_au]. *)
    assert (Hlok' : ireg_link_ok dn').
    { rewrite /ireg_link_ok (proj1 Hnl).
      split_and!;
        [ intros H0; exfalso; exact (Hnz H0)
        | exact (ireg_link_ok_short dn Hlok)
        | exact (ireg_ty_ok_stable dn' dn Hstab Hlok) ]. }
    (* THE CLAIM PIN IS VACUOUS HERE (iclaim-ledger.md §2.4). *)
    assert (Hclm' : ireg_claim_ok cl fz dn')
      by (rewrite (proj2 Ht2); exact I).
    (* (T1) RIDES ON [di_type_stable] PLUS [Hnz]. *)
    assert (Hty' : di_type dn' = di_type dn)
      by (destruct Hstab as [H0 | Heq]; [exfalso; exact (Hnz H0) | exact Heq]).
    (* THE FREEZE PIN IS FREE HERE (iclaim-ledger.md §3.1's cost table). *)
    assert (Hfrz' : ireg_frz_ok fz cn dn')
      by exact (ireg_frz_ok_stable fz cn dn dn' (proj1 Hnl) Hty' Hfrz).
    (* THE RECEIPT TRAVELS FOR FREE (fs-log.md §G.17). *)
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { rewrite Hdeq (proj1 Hnl). intros H0. exact H0. }
    (* ...AND SO DOES THE LINK AUTHORITY (durable-disk 2b-inode-4): an
       ordinary flush leaves the COUNT alone, which is exactly
       [di_nlink_stable]'s first conjunct. *)
    assert (Hlnkeq : bv_unsigned (di_nlink dn')
                     = bv_unsigned (di_nlink (ds !!! islot inum)))
      by (rewrite Hdeq (proj1 Hnl); reflexivity).
    assert (Htyeq : bv_unsigned (di_type dn')
                    = bv_unsigned (di_type (ds !!! islot inum)))
      by (rewrite Hdeq Hty'; reflexivity).
    iDestruct (ireg_lnk_stable γfs (bv_unsigned inum) (ds !!! islot inum) dn'
                 Hlnkeq Htyeq with "Hlnk") as "Hlnk".
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    (* the flushed record's run goes back where it came from *)
    iEval (rewrite -(rec_owned_at_IBLOCK (fs_gamma_L γfs) inodestart inum dn'))
      in "Hrun".
    iEval (rewrite -Hkey) in "Hrun".
    iDestruct ("Hrecback" $! dn' with "Hrun") as "Hrec".
    iMod ("Hclose" with "[Ha Hreg Hrec Hmk Hla Hep Hlnk Hslback Hback Hrf Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hrec Hmk Hla Hep Hlnk Hslback Hrf Hcnt Hfdisj Hfrcp]").
      { (* other blocks' keys never collide with this inum's *)
        intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact Hwfi |].
      iSplitR.
      { iPureIntro. intros i Hi.
        destruct (decide (i = islot inum)) as [->|Hne].
        - rewrite /m' -(ireg_key_split inum) lookup_insert.
          rewrite list_lookup_total_insert; [done | lia].
        - rewrite /m' lookup_insert_ne; last first.
          { rewrite (ireg_key_split inum). intros Hc.
            destruct (ireg_key_inj (ireg_bi inum) (ireg_bi inum)
                        (islot inum) i Hsl Hi Hc) as [_ Hi'].
            exact (Hne (eq_sym Hi')). }
          rewrite list_lookup_total_insert_ne; [| by apply not_eq_sym].
          exact (Hcp0 i Hi). }
      iSplitL "Hrec"; [iExact "Hrec" |].
      iApply ("Hslback" $! dn' with "[Hmk Hla Hep Hlnk Hrf Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      (* RULING R: an ordinary flush keeps the type, so the r column's clause
         is CARRIED across the record move exactly as (T1) and the freeze pin
         are -- one line, no premise on the mover. *)
      iEval (rewrite Hdeq) in "Hla".
      iDestruct (ireg_rcol_stable (bv_unsigned inum) cl rl fz cn dn dn' Hty' with "Hla") as "Hla".
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) dn' cl rl fz cn Hlok' Hclm' Hfrz'
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp").
      iLeft. iSplitR "Hrf"; [iRight; iSplitR; [iPureIntro; split; [exact Hnz | exact (proj2 Ht2)] | iExact "Hmk"] | iExact "Hrf"]. }
    iModIntro. iExact "Hdn".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  ialloc's CLAIM (§16.3/§16.4)                                        *)
  (* ------------------------------------------------------------------ *)

  (* The mirror of [ireg_write_au] with the fragment sourced FROM the
     invariant rather than supplied to it, and it needs NO caller resource
     at all: the buffer the caller is holding IS the serialiser (§16.2), so
     the only premise is the type-0 record the caller decoded out of it.
     The claim leaves the retagged fragment INSIDE the region, at the
     [fresh_shape] arm -- that is §16.4's claim box, and it is why the
     payout is trivial: nothing crosses to ialloc's caller, so no
     interleaving can strand a concurrent ilock's fill (§16.4's killing
     trace).  The FIRST fill of an entry for this inum picks the fragment up
     again with [ireg_withdraw].

     A claim against an ALREADY-CLAIMED slot is refuted PURELY: a claimed
     slot's record has [fresh_shape], hence a nonzero type, and the coupling
     says that record IS the one the caller's buffer decoded. *)
  Lemma ireg_claim_au (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn' : dinode)
      (dsc : list dinode) (t : nat) (qt : Qp) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    (* [dsc] is what the CALLER's buffer decoded to; the claim reads its
       slot's type off it and the log's tie is what identifies that record
       with the one the region parks (durable-disk 2b-inode-1). *)
    diblk_wf dsc ->
    bv_unsigned (di_type (dsc !!! islot inum)) = 0 ->
    fresh_shape dn' ->
    (* (L5), the ONE clause a claim cannot ride in on (durable-disk
       2b-inode-3): the claim box's type comes out of nowhere -- it is
       [ialloc]'s [ty] argument -- so the enumeration is the one thing the
       region cannot re-establish from the record it is replacing.  Every
       caller writes a literal ([T_FILE]/[T_DIR]/[T_DEVICE], out of
       create's [type] argument), so it is discharged where the literal
       is. *)
    ireg_ty_ok dn' ->
    (* OPTION A: the pending arm is refuted from [ireg_body]'s own registry
       ([Hreg], carried out of the open below): read this inum's [reg_full] and
       collide it with the arm's [reg_half] (fraction overflow).  No premise. *)
    ireg_inv γi γfs inodestart nib -∗
    (* THE SEALED REGIME, and it is what the landed boot clause costs the
       c-mint (iclaim-ledger.md §2.4): a claimed slot must exhibit
       [ireg_open], so every RUNTIME claimant carries it -- persistent, so
       it is borrowed and never spent.  A holder of [ireg_boot] therefore
       still proves every slot unclaimed ([IregLinkNz.ireg_boot_no_claim]),
       which is the whole point of the clause. *)
    ireg_open -∗
    (* THE CLAIMING TRANSACTION'S SHARE (durable-disk C-5, [FsCollect.v]'s
       residue (E)).  The claim box stands from here to the claimant's own
       fill, and the whole of that window is inside ONE transaction; the
       share parked here is what PROVES it, so a commit -- at which the
       WAL's [LogDefs.ln_tx] authority is empty -- can refute the box and
       read [di_type d = 0] off the region's IN arm.  It comes back at
       [ireg_withdraw]'s [ireg_wd_back], at the very [(t, qt)] the receipt
       [IcacheRef.iclaim] names. *)
    t ↪[ln_tx icfg_log]{#qt} tt -∗
    (* [SpecLogWrite.lw_au_rec]'s premise: ONE RECORD's run out and back. *)
    |={E, E ∖ ↑iregN}=> ∃ rec_old : list (bv 8),
      ⌜length rec_old = 64%nat⌝ ∗
      FsStateDefs.byte_range (fs_gamma_L γfs) (IBLOCK inum inodestart)
        (Z.of_nat (64 * islot inum)) rec_old ∗
      (⌜rec_old = take 64%nat
                    (drop (64 * islot inum)%nat (diblk_bytes dsc))⌝ -∗
       FsStateDefs.byte_range (fs_gamma_L γfs) (IBLOCK inum inodestart)
         (Z.of_nat (64 * islot inum)) (dinode_bytes dn')
       (* THE CLAIM (§2.4): the c column goes [None -> Some] in the same
          ghost step that writes the box, and the exclusive fragment is
          ialloc's receipt.  It is spent at create's fill
          ([ireg_withdraw]). *)
       ={E ∖ ↑iregN, E}=∗ iclaim (bv_unsigned inum) (di_type dn') t qt).
  Proof.
    iIntros (HE Hin Hwfc Ht0c Hfr Htyc) "#Hinv #Hopen Htx".
    pose proof (islot_lt inum) as Hsl.
    pose proof (fresh_shape_wf dn' Hfr) as Hdn'.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp0 & >Hrec & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    assert (Hwfi : diblk_wf (<[islot inum := dn']> ds))
      by exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn').
    assert (Hdrwf : dinode_wf (ds !!! islot inum))
      by exact (ireg_blk_slot ds (islot inum) Hwf Hsl).
    iDestruct (ireg_recs_acc_upd γfs inodestart (ireg_bi inum) ds (islot inum)
                 Hsl Hlen16 with "Hrec") as "[Hrun Hrecback]".
    iEval (rewrite Hkey) in "Hrun".
    iEval (rewrite (rec_owned_at_IBLOCK (fs_gamma_L γfs) inodestart inum
                      (ds !!! islot inum))) in "Hrun".
    iModIntro. iExists (dinode_bytes (ds !!! islot inum)).
    iSplitR; [iPureIntro; exact (dinode_bytes_length _ Hdrwf) |].
    iFrame "Hrun".
    (* THE TIE, AT RECORD GRANULARITY.  The log says the run the claimant
       surrendered IS the slot's slice of the checked-out buffer, the
       buffer decodes to [dsc], and the encoding is injective on records --
       so the region's parked record at this slot IS the one whose type the
       caller read as zero.  [diblk_bytes_inj] did this through the whole
       block; [diblk_bytes_slice] + [dinode_bytes_inj] do it through the
       one record. *)
    iIntros (Hbytes) "Hrun".
    assert (Ht0 : bv_unsigned (di_type (ds !!! islot inum)) = 0).
    { assert (Hslc : dinode_bytes (ds !!! islot inum)
                     = dinode_bytes (dsc !!! islot inum)).
      { rewrite Hbytes (diblk_bytes_slice dsc (islot inum) Hwfc Hsl).
        reflexivity. }
      rewrite (dinode_bytes_inj _ _ Hdrwf
                 (ireg_blk_slot dsc (islot inum) Hwfc Hsl) Hslc).
      exact Ht0c. }
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    (* OPTION A (walk registry-split): the claimed slot's fragment [Hfrg]
       reaches the tail from EITHER the live IN arm (unchanged) OR the type=0
       PENDING arm.  A pending arm no longer collides by fractions -- the
       deposit split this inum's registry element to [reg_half] -- so the claim
       COORDINATES with [region_pending] instead: it recombines the arm's
       [reg_half] with the registry's [reg_half] back into the [reg_full] the
       tail re-parks, dropping the (persistent) [committedA].  A pending arm
       whose registry element is still [reg_full] is impossible (fraction 3/2)
       and refuted, exactly as before -- so the registry disjunct is what
       discriminates a genuine deposit from a spurious one, and
       [ireg_claim_au]'s interface (and postcondition) is unchanged. *)
    (* ...AND THE ERA'S ABSTRACT VALUE COMES OUT WITH IT (durable-disk C-3c).
       BOTH arms that hold the fragment hold the park beside it, so the claim
       carries it across UNTOUCHED: the new record is [fresh_shape], hence
       nonzero-typed, and the park's tie is guarded by [di_type = 0] -- so no
       resource moves at the claim and no [ftopN] open is needed here.  It is
       the fill ([ireg_withdraw] then ProofIlock's [ireg_top_retag]) that
       re-ties the fragment at the node it parks. *)
    iAssert ((bv_unsigned inum ↪[γi] (ds !!! islot inum))
             ∗ (∃ ge gr, reg_full (bv_unsigned inum) ge gr)
             ∗ (∃ n : fs_node, top_frag (fs_gamma_L γfs) (bv_unsigned inum) n))%I
      with "[Harm]" as "(Hfrg & Hrf & Htp)".
    { iDestruct "Harm" as "[[Harm Hrf] | Hpend]".
      - (* non-pending: fragment from the IN arm + the arm's own reg_full;
           a type-0 record refutes the marked sub-arm ([Ht2 Ht0]). *)
        iDestruct "Harm" as "[[_ [Hfrg Hpk]] | [%Ht2 _]]".
        + iDestruct "Hpk" as (n0) "[_ Hn0]".
          iFrame "Hfrg Hrf". iExists n0. iExact "Hn0".
        + iExFalso. iPureIntro. exact (proj1 Ht2 Ht0).
      - (* PENDING: recombine the arm's structural [reg_half] with
           [region_pending]'s half back into [reg_full] -- the coordinate, now
           entirely from the slot's own arm (no registry lookup). *)
        iDestruct "Hpend" as "(_ & Hfrg & Hrh1 & Hrp & Hpk)".
        iDestruct "Hrh1" as (ge1 gr1) "Hrh1".
        iDestruct "Hrp" as (ge2 gr2) "[Hrh2 _]".
        iDestruct (reg_half_agree with "Hrh1 Hrh2") as %[-> ->].
        iDestruct (reg_join with "Hrh1 Hrh2") as "Hrf".
        iDestruct "Hpk" as (n0) "[_ Hn0]".
        iFrame "Hfrg". iSplitL "Hrf"; [iExists ge2, gr2; iExact "Hrf" |].
        iExists n0. iExact "Hn0". }
    (* (L3)/(L4)/(L5) AT THE CLAIM BOX: the record ialloc writes is
       [fresh_shape], so its type is NONZERO and its count ZERO. *)
    assert (Hlok' : ireg_link_ok dn').
    { split_and!;
        [ intros H0; exfalso; exact (proj1 Hfr H0)
        | rewrite (fresh_shape_nlink dn' Hfr); lia
        | exact Htyc ]. }
    (* THE ROOT IS NOT CLAIMABLE (§20.4's (f) row, fs-fragments §3.6).  The
       claim would write a [fresh_shape] record, whose count is ZERO, so the
       strict clause could not be re-established at the root -- and it does
       not have to be: the caller's buffer showed [di_type = 0] at the OLD
       record, (L3) turns that into [di_nlink = 0], and the old clause
       refutes the root there outright.  **ialloc can never claim the root**,
       proved inside the region with no premise on the mover. *)
    (* A STANDING CLAIM IS REFUTED BY THE PIN (iclaim-ledger.md §2.4), which
       is what makes [link_mint_claim]'s [c = None] side condition
       dischargeable: [ireg_claim_ok] says a claimed slot's record is
       [fresh_shape], hence has a NONZERO type, and the caller's buffer
       showed [di_type = 0] at exactly that record. *)
    assert (Hcl0 : cl = None).
    { destruct cl as [x |]; [| reflexivity].
      exfalso. exact (proj1 (proj1 Hclm) Ht0). }
    subst cl.
    (* THE CLAIM BOX IS NOT FROZEN, AND THE FREEZE PIN IS WHAT PROVES IT
       (iclaim-ledger.md §3.1, RULING A).  The caller's buffer showed
       [di_type = 0] at this slot's record, and the pin's type conjunct says a
       frozen slot's record has a NONZERO type -- so the column reads
       [FrzOff] here, with no premise on the mover and no token in the
       claimant's hand.  That is the fact [ireg_claim_ok]'s new conjunct
       records, and it is the ClaimL row of [IgetLic.iname_not_frozen]. *)
    assert (Hfz0 : fz = Some (Excl FrzOff))
      by exact (ireg_frz_ok_ty0 fz cn (ds !!! islot inum) Ht0 Hfrz).
    (* RULING R's PIN, ESTABLISHED HERE (iclaim-ledger.md §5'.2).  The r
       column's clause is unpacked, the claim is minted through it, and
       [ireg_ref_ok_claim_mint] carries it: (R2) at the OLD, type-0 record
       gives [r = rc = 0], so (R3) holds at the box the claim creates, and
       (R2) itself goes vacuous there because a [fresh_shape] record has a
       nonzero type.  THIS is the step §5'.2 mislocated as a "standing pin" --
       it is (R2), stated by this increment, and it is established at exactly
       the site the ruling names. *)
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    iMod (link_mint_claim _ _ _ _ (di_type dn') t qt with "Hla")
      as "[Hla Hcl]".
    (* RULING R's PIN, ESTABLISHED (§5'.2, landed by 7a-wire): (R2) at the
       OLD, type-0 record collapses both r columns, so (R3) holds at the box
       the claim creates and (R2) itself goes vacuous there against
       [fresh_shape]'s nonzero type.  Both facts are already in hand at this
       line ([Ht0] is the mover's own premise, [Hfr] its other). *)
    iDestruct (ireg_rcol_intro (bv_unsigned inum)
                 (Some (Excl ((di_type dn', (t, qt)) : ctyval))) rl fz cn rcl dn'
                 (ireg_ref_ok_claim_mint rl rcl cn (ds !!! islot inum) dn'
                    (Some (Excl ((di_type dn', (t, qt)) : ctyval)))
                    Href Ht0 (proj1 Hfr))
                 with "Hla") as "Hla".
    (* the new pin: the claim box IS the [fresh_shape] record just written,
       and the column it is written at is the unfrozen one *)
    assert (Hclm' : ireg_claim_ok
                      (Some (Excl ((di_type dn', (t, qt)) : ctyval))) fz dn')
      by (split_and!; [exact Hfr | exact Hfz0 | reflexivity]).
    (* THE SHARE GOES INTO THE SLOT (durable-disk C-5): the f-shelter and the
       claim pin travel as one conjunct ([ireg_shp]), so the claim splits it,
       parks the transaction's share on the c side and re-joins. *)
    iDestruct (ireg_shp_split with "Hfdisj") as "[Hfsh _]".
    iDestruct (ireg_shp_intro
                 (Some (Excl ((di_type dn', (t, qt)) : ctyval))) fz
                 with "Hfsh [Htx]") as "Hfdisj".
    { iApply (ireg_cpin_some ((di_type dn', (t, qt)) : ctyval)). iExact "Htx". }
    assert (Hfrz' : ireg_frz_ok fz cn dn')
      by exact (ireg_frz_ok_of_off fz cn dn' Hfz0).
    (* the claimed slot's old record is type-0, so (L3) already gives it
       [nlink = 0] and the receipt carries unconditionally *)
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { intros _. exact (proj1 Hlok Ht0). }
    (* the link authority does not move either: the claimed slot's OLD
       record is type-0, so (L3) pins its count at zero, and the box
       [ialloc] writes is [fresh_shape], whose count is zero too. *)
    assert (Hlnkeq : bv_unsigned (di_nlink dn')
                     = bv_unsigned (di_nlink (ds !!! islot inum)))
      by (rewrite (fresh_shape_nlink dn' Hfr) (proj1 Hlok Ht0);
          reflexivity).
    iDestruct (ireg_lnk_free_retype γfs (bv_unsigned inum)
                 (ds !!! islot inum) dn'
                 (proj1 Hlok Ht0) (fresh_shape_nlink dn' Hfr)
                 with "Hlnk") as "Hlnk".
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hfrg") as %Hm.
    iMod (ghost_map_update dn' with "Ha Hfrg") as "[Ha Hfrg]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iEval (rewrite -(rec_owned_at_IBLOCK (fs_gamma_L γfs) inodestart inum dn'))
      in "Hrun".
    iEval (rewrite -Hkey) in "Hrun".
    iDestruct ("Hrecback" $! dn' with "Hrun") as "Hrecb".
    iMod ("Hclose" with "[Ha Hreg Hrecb Hfrg Htp Hla Hep Hlnk Hslback Hback Hrf Hcnt Hfdisj Hfrcp]") as "_"; last first.
    { iModIntro. iExact "Hcl". }
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hrecb Hfrg Htp Hla Hep Hlnk Hslback Hrf Hcnt Hfdisj Hfrcp]").
      { intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact Hwfi |].
      iSplitR.
      { iPureIntro. intros i Hi.
        destruct (decide (i = islot inum)) as [->|Hne].
        - rewrite /m' -(ireg_key_split inum) lookup_insert.
          rewrite list_lookup_total_insert; [done | lia].
        - rewrite /m' lookup_insert_ne; last first.
          { rewrite (ireg_key_split inum). intros Hc.
            destruct (ireg_key_inj (ireg_bi inum) (ireg_bi inum)
                        (islot inum) i Hsl Hi Hc) as [_ Hi'].
            exact (Hne (eq_sym Hi')). }
          rewrite list_lookup_total_insert_ne; [| by apply not_eq_sym].
          exact (Hcp0 i Hi). }
      iSplitL "Hrecb"; [iExact "Hrecb" |].
      iApply ("Hslback" $! dn' with "[Hfrg Htp Hla Hep Hlnk Hrf Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) dn'
                (Some (Excl ((di_type dn', (t, qt)) : ctyval)))
                rl fz cn Hlok' Hclm' Hfrz'
                with "Hla Hep Hlnk [] Hcnt Hfdisj Hfrcp").
      { iRight. iExact "Hopen". }
      iLeft. iSplitR "Hrf";
        [iLeft; iSplitR;
           [iPureIntro; right; split; [exact Hfr | discriminate] |];
         iSplitL "Hfrg"; [iExact "Hfrg" |];
         iDestruct "Htp" as (n0) "Hn0";
         iApply (ireg_top_park_nz γfs (bv_unsigned inum) dn' n0
                   (proj1 Hfr) with "Hn0")
        | iExact "Hrf"]. }
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  iput's FREEZE -- the f column's mint (iclaim-ledger.md §1.4/§2.3)   *)
  (* ------------------------------------------------------------------ *)

  (* WHERE IT FIRES.  In [ip_free_entry]'s span, on the [nlink == 0] arm at
     iput+0x50, still under the FIRST itable-lock hold -- which is where
     [Mt !! k = Some (q, 1)] is a live fact and where §2.2's [icnt] SLOT half
     therefore reads ONE.  Between this mint and the deposit's retire the
     freeze-pin is the walk's working capital: §1.1's B1 payout reads it at
     iput+0x82 and gets [cnt2 = 1] with no arithmetic side condition, and
     +0x8a steps the phase [FrzPre -> FrzPost] fragment-side, inside the
     region open it already takes for the count.

     WHY IT IS A SWAP AND NOT AN ALLOCATION, i.e. why the caller brings
     [ifreeze FrzOff] rather than nothing.  The mint must be EXCLUSIVE -- two
     threads must not both hold a freeze at one inum -- and a [None -> Some]
     allocation cannot be: nothing a RUNTIME freezer holds refutes a standing
     [FrzPre] (the boot arm's [ireg_boot] does, by [ity_pending_excl]; the
     persistent [ireg_open] does not), and the region has no other handle on
     it.  With the unfrozen state spelled as [FrzOff] the right to freeze IS
     the exclusive fragment, it rides under the itable lock beside the count
     half, and double-freeze dies on [Excl] alone -- see [Xv6Cameras.frz]'s
     header for the same argument from the algebra's side.

     THE BOOT-SHELTER SIDE (§2.3's last conjunct) is the caller's
     [ireg_open ∨ ireg_boot]: a runtime freezer hands in the persistent
     sealed regime, ireclaim PARKS its exclusive boot token for the window
     and takes it back at the deposit. *)
  (* THE RECORD PREMISES (iclaim-ledger.md §3.1, RULING A's mover table, last
     row).  The pin is a RECORD fact now, so its mint has to establish it:
     the freezer hands in the record it is freezing -- BORROWED, exactly like
     the block half beside it, and handed straight back -- together with the
     two facts the pin spells.  All three are in the walk's hand at
     [ip_free_entry]: the inode is locked, so [dinode_at] is checked out to
     iput; [nlink = 0] is the C-level [ip->nlink == 0] test it has just taken;
     and [type <> 0] is [InodeLock.inode_ok]'s own conjunct on a live locked
     inode.
     The fragment also does a SECOND job, and it is what pays for the claim
     clause: it refutes both non-marked arms ([dinode_at_excl]), so the slot
     is at [c = None] and the new [ireg_claim_ok] conjunct is vacuous at the
     phase this mover writes. *)
  Lemma ireg_freeze_au (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) (rg : frzidx) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bv_unsigned (di_nlink dn) = 0 ->
    bv_unsigned (di_type dn) <> 0 ->
    ireg_inv γi γfs inodestart nib -∗
    ireg_regime rg.1 -∗
    (* THE WINDOW'S PARKED SHARE (durable-disk C-6, residue (F)): the freezer
       lends a positive share of its own open transaction's [LogDefs.ln_tx]
       element for the length of the freeze, and [EscrowDeposit.
       ireg_free_deposit_au] hands it back beside the regime.  It is what
       makes the corpse window -- the MARKED slot between iput's eviction and
       its off-lock deposit, at which the inum has no bundle anywhere --
       unreachable at a commit ([ireg_fsh_no_ops]).  The pair rides in [rg],
       not existentially, so the deposit returns EXACTLY the element the
       freezer parked -- two halves of one element are not the whole. *)
    ireg_fpin rg -∗
    dinode_at γi inum dn -∗
    ifreeze FrzOff (bv_unsigned inum) -∗
    icnt_half (bv_unsigned inum) 1%nat -∗
    (* THE MIRROR's LOCK HALF (iclaim-ledger.md §3.16, RULING A⁗).  The mint
       is one of exactly two sites in the tree that hold BOTH the itable lock
       and the region open, which is precisely what [frzm_update] demands --
       so the flip cannot happen anywhere else.  The caller peels this half
       off [IcacheEscrow.islot2]'s live arm (which it has just decided onto
       its LEFT/[false] disjunct from its own live mass, ZZProbeFrz P1') and
       gets it back at [true], to re-park under the FROZEN disjunct together
       with the two live slices it is about to stop needing. *)
    frzm_h (bv_unsigned inum) false ={E}=∗
    dinode_at γi inum dn ∗
    ifreeze_pre rg (bv_unsigned inum) ∗ icnt_half (bv_unsigned inum) 1%nat ∗
    (* THE FREEZE RECEIPT (iclaim-ledger.md §3.14 as built): the token the
       free path parks in the payload's token slot at iput+0x70 while it
       keeps [ifreeze_pre] in its own hand.  Returned to the region by the
       [FrzPre -> FrzPost] step at +0x8a. *)
    frzown (bv_unsigned inum) ∗
    (* ...and the mirror's lock half, UP (ZZProbeFrz P6: one bupd) *)
    frzm_h (bv_unsigned inum) true.
  Proof.
    iIntros (HE Hin Hnl0 Hty0) "#Hinv Hsh Hfpin Hdn Hoff Hhalf Hmir".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    (* THE FRAGMENT PUTS THIS OPEN ON THE MARKED ARM, and that is where the
       claim clause is paid: [ireg_marked_ok] says [cl = None]. *)
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(_ & Hpz & _)"; iExFalso; iApply (dinode_at_excl with "Hpz Hdn")].
    iDestruct "Harm" as "[[%Hin1 [Hfr Hpk]] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    (* ...and it pins the region's record at this slot to the caller's, which
       is what carries the two record premises into the pin *)
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    (* the OFF token pins the column -- this is the exclusivity *)
    iDestruct (ireg_rcol_freeze_agree with "Hla Hoff") as %->.
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    (* ...and the two halves pin the count the new pin will carry *)
    iDestruct (icnt_agree with "Hcnt Hhalf") as %->.
    iMod (link_freeze_step _ _ _ FrzOff (FrzPre rg) with "Hla Hoff")
      as "[Hla Hpre]".
    (* THE MINT ESTABLISHES THE PIN, all three conjuncts from what the
       freezer handed in (§3.1's last mover row). *)
    assert (Hfrz' : ireg_frz_ok (Some (Excl (FrzPre rg))) 1%nat
                      (ds !!! islot inum)).
    { rewrite Hdeq. split_and!; [exact Hnl0 | exact Hty0 | reflexivity]. }
    (* the claim clause at the NEW phase: the marked arm says [cl = None] *)
    assert (Hclm' : ireg_claim_ok cl (Some (Excl (FrzPre rg))) (ds !!! islot inum))
      by (rewrite (proj2 Ht2); exact I).
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    (* THE RECEIPT COMES OUT HERE (iclaim-ledger.md §3.14 as built): the old
       column is [FrzOff], so the slot's clause is on its [frzown] arm, and
       the NEW column is [FrzPre], at which the clause's own LEFT arm is
       free.  So the mint hands the receipt to the freezer at no cost, and
       "the freezer holds it" is from now on equivalent to "this inum reads
       [FrzPre]" ([frzown_excl]). *)
    iDestruct "Hfrcp" as "[[%Hbad | Hrcpt] Hmr]"; [discriminate Hbad |].
    (* THE MIRROR FLIPS HERE (ZZProbeFrz P6).  The old column is [FrzOff], so
       the region's clause pins its bit DOWN; both halves are in hand at this
       one instant, so [frzm_update] fires and both come out UP -- the
       region's re-parked at the new [FrzPre] column (where [ireg_frzm_ok] is
       [ireg_frzm_ok_true]) and the caller's handed back for the frozen-park
       disjunct of [islot2]'s live arm. *)
    iDestruct "Hmr" as (b0) "[Hmr %Hmok]".
    iDestruct (frzm_agree with "Hmr Hmir") as %<-.
    assert (Hb0 : b0 = false) by exact Hmok.
    subst b0.
    iMod (frzm_update (bv_unsigned inum) false true with "Hmr Hmir")
      as "[Hmr Hmir]".
    iMod ("Hclose" with "[Ha Hreg Hfsb Hmk Hrf Hla Hep Hlnk Hslback Hback Hcnt Hsh Hfpin Hmr Hfdisj]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Hmk Hrf Hla Hep Hlnk Hslback Hcnt Hsh Hfpin Hmr Hfdisj]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hmk Hrf Hla Hep Hlnk Hcnt Hsh Hfpin Hmr Hfdisj]").
      rewrite Hkey.
      (* RULING R: the freeze moves the f column only -- neither r column,
         neither the count nor the record -- so the clause rides verbatim. *)
      iDestruct (ireg_rcol_intro (bv_unsigned inum) cl rl
                   (Some (Excl (FrzPre rg))) 1%nat rcl (ds !!! islot inum) Href
                   with "Hla") as "Hla".
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                cl rl (Some (Excl (FrzPre rg))) 1%nat Hlok Hclm' Hfrz'
                with "Hla Hep Hlnk Hdisj Hcnt [Hsh Hfpin Hfdisj] [Hmr]").
      (* the c side of the shelter conjunct rides through untouched
         (durable-disk C-5): the freeze moves the f column only.  The f side
         is the regime the freezer lent TOGETHER WITH the window's share
         (durable-disk C-6). *)
      { iApply (ireg_shp_intro cl (Some (Excl (FrzPre rg)))
                  with "[Hsh Hfpin] [Hfdisj]").
        - iApply (ireg_fsh_pre rg with "Hsh Hfpin").
        - iDestruct (ireg_shp_split with "Hfdisj") as "[_ $]". }
      { iApply (ireg_frzc_intro _ _ true (ireg_frzm_ok_true rg) with "[] Hmr").
        iLeft. iPureIntro. reflexivity. }
      iLeft. iSplitR "Hrf"; [iRight; iSplitR; [iPureIntro; exact Ht2 | iExact "Hmk"] | iExact "Hrf"]. }
    iModIntro. rewrite /ifreeze_pre. iFrame "Hdn Hpre Hhalf Hrcpt Hmir".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE MIRROR, READ THROUGH THE REGION (iclaim-ledger.md §3.16, A⁗)    *)
  (* ------------------------------------------------------------------ *)

  (* A holder of the f column's token and of a mirror half learns, in ONE
     region open and with nothing moved, that the two agree.  It is the
     BRANCH DECIDER at both of the free path's ends:

       * at iput+0x82 the walk holds [ifreeze_pre] and peels [islot2]'s live
         arm.  Its frozen-park disjunct's LEFT alternative is a [false] half,
         and this lemma turns that into [False] -- so the arm is on the park
         and the mint's two live slices come home (S1b);
       * at the mint (+0x50) the walk has ALREADY decided the arm LEFT out of
         its own live mass, with no open at all (ZZProbeFrz P1'), and this is
         what then refutes the payload slot's [frzown] arm (S1a) -- through
         [ireg_frzc]'s own two conjuncts, at the [false] bit.

     Nothing moves, so no phase premise and no shelter clause: the slot goes
     back exactly as it came out. *)
  Lemma ireg_frzm_read (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (ph : frz) (b : bool) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    ifreeze ph (bv_unsigned inum) -∗
    frzm_h (bv_unsigned inum) b ={E}=∗
      ⌜b = frz_ispre ph⌝ ∗
      ifreeze ph (bv_unsigned inum) ∗ frzm_h (bv_unsigned inum) b.
  Proof.
    iIntros (HE Hin) "#Hinv Hfz Hmir".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iDestruct (ireg_rcol_freeze_agree with "Hla Hfz") as %->.
    iDestruct "Hfrcp" as "[Hrc Hmr]".
    iDestruct "Hmr" as (b0) "[Hmr %Hmok]".
    iDestruct (frzm_agree with "Hmr Hmir") as %<-.
    assert (Hiff : b0 = frz_ispre ph) by exact Hmok.
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hlnk Hslback Hback Hcnt Hfdisj Hrc Hmr]")
      as "_".
    { iNext. iExists mrg. iFrame "Ha Hreg".
      iApply ("Hback" $! mrg with "[%] [Hfsb Harm Hla Hep Hlnk Hslback Hcnt Hfdisj Hrc Hmr]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hlnk Hcnt Hfdisj Hrc Hmr]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                cl rl (Some (Excl ph)) cn Hlok Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj [Hrc Hmr] Harm").
      iApply (ireg_frzc_intro _ _ b0 Hmok with "Hrc Hmr"). }
    iModIntro. iFrame "Hfz Hmir". iPureIntro. exact Hiff.
  Qed.

  (* THE PAYLOAD-SLOT DECIDER (ZZProbeFrz P2, S1a): a thread holding the
     mirror's [false] half knows this inum's column is not [FrzPre], so the
     region's own RECEIPT clause is on its [frzown] arm -- and a second
     receipt, wherever it came from, is one [Excl] too many.

     THIS IS WHAT LETS ip_free_entry's WINDOW-ENTERING READ (+0x3a) TAKE THE
     PAYLOAD's TOKEN.  The parked arm's tail is a disjunction since §3.14
     (DEVIATION 1) and A⁗ widened it further; its FROZEN alternative is the
     receipt, and at REF-1 the walk decides [islot2]'s own frozen park LEFT
     out of its live mass ([IcacheInv.live_whole_share_absurd]) and then feeds
     the resulting [false] half to this lemma.  Out comes [ifreeze_off], which
     is exactly what the mint at +0x50 consumes. *)
  Lemma ireg_frzown_off_absurd (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    frzm_h (bv_unsigned inum) false -∗
    frzown (bv_unsigned inum) ={E}=∗ False.
  Proof.
    iIntros (HE Hin) "#Hinv Hmir Hrc".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iDestruct "Hfrcp" as "[Hrc' Hmr]".
    iDestruct "Hmr" as (b0) "[Hmr %Hmok]".
    iDestruct (frzm_agree with "Hmr Hmir") as %->.
    iDestruct "Hrc'" as "[%Hpre | Hrc']".
    { rewrite /ireg_frzm_ok Hpre in Hmok. discriminate Hmok. }
    iExFalso. iApply (frzown_excl with "Hrc Hrc'").
  Qed.

  (* ...AND B1's PIN READ (iclaim-ledger.md §3.16, the +0x82 re-acquire).

     The freezer re-takes the itable lock at iput+0x82 and [islot2]'s live arm
     hands it [icnt_half z (Pos.to_nat cnt2)] -- about the map AS IT IS NOW,
     the REF-1 fact the caller supplied being about the map before the release
     (that is B1's whole wall).  With the freeze STANDING, the region's own
     pin settles it in one open: [ireg_frz_ok] at [FrzPre] says the in-core
     count is ONE, so [cnt2 = 1] and the non-last-close arm is REFUTED rather
     than admitted.  Nothing moves; the slot goes back as it came out. *)
  Lemma ireg_frz_pin_read (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (ph : frz) (n : nat) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    ifreeze ph (bv_unsigned inum) -∗
    icnt_half (bv_unsigned inum) n ={E}=∗
      (∃ d : dinode, ⌜ireg_frz_ok (Some (Excl ph)) n d⌝) ∗
      ifreeze ph (bv_unsigned inum) ∗ icnt_half (bv_unsigned inum) n.
  Proof.
    iIntros (HE Hin) "#Hinv Hfz Hcnth".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iDestruct (ireg_rcol_freeze_agree with "Hla Hfz") as %->.
    iDestruct (icnt_agree with "Hcnt Hcnth") as %->.
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hlnk Hslback Hback Hcnt Hfdisj Hfrcp]")
      as "_".
    { iNext. iExists mrg. iFrame "Ha Hreg".
      iApply ("Hback" $! mrg with "[%] [Hfsb Harm Hla Hep Hlnk Hslback Hcnt Hfdisj Hfrcp]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hlnk Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                cl rl (Some (Excl ph)) n Hlok Hclm Hfrz
                with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hfz Hcnth".
    iExists (ds !!! islot inum). iPureIntro. exact Hfrz.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  ilock's WITHDRAWAL (§16.4's [icb_withdraw])                          *)
  (* ------------------------------------------------------------------ *)

  (* The FIRST fill of an entry whose parked payload is a MARKER and whose
     buffer shows a nonzero type.  It is [ireg_read]'s opening -- the
     caller's machinery half pins the region's bytes -- with one arm move on
     top: the marker goes in, the claimed fragment comes out, and the map
     does not change at all.

     EXHAUSTIVENESS, which is what §16.4 needed the box for: the marker the
     caller holds refutes the OUT arm outright, so a nonzero type at this
     slot forces the claimed arm and delivers [fresh_shape] -- out of which
     [InodeLock.inode_ok] is constructible from nothing.  No itable lock and
     no entry-uniqueness argument is involved. *)
  (* ---- THE WITHDRAW's PREMISE, INDEXED (iclaim-ledger.md §5'.3) --------

     RULING R makes the withdraw's licence a DISJUNCTION -- create's fill
     presents the typed claim and spends it; every other fill presents the
     PLAIN provenance unit its own reference carries, borrowed and returned.
     Spelled as an INDEX rather than a [∨] for [ireg_link_pin]'s reason: the
     payout differs on the two arms (only the claimant learns the type, only
     the borrower gets its unit back), and a caller that presented one arm
     must not have to case on the other to read its own post.

     [ClaimK ty] is §5.2(a)'s claim arm; [PlainK] is §5'.3's plain arm, and
     the plain arm's [c = None] is DERIVED, not assumed -- the unit collides
     [1 <= r] against the claim pin's [c <> None -> r = 0].

     ---- RULING C' (iclaim-ledger.md §5''''): THE INDEX GOES 3-VALUED -----

     The landed [option (bv 16)] is RESHAPED into [ilkc], because the fd
     layer's three [wp_ilock_sconf] sites can present NEITHER arm: their
     inode payload lives behind a cancellable invariant that no syscall may
     hold open across the call, so no whole unit and no claim reaches them.
     What they DO hold, persistently and for free, is the generation's own
     one-shot [IcacheRef.ity_shot g ty] (FileInvDefs.inode_pay carries it) --
     and a one-shot in hand says the generation has ALREADY been filled, so
     it refutes the uncached arm outright ([IcacheRef.ity_pending_shot_excl]
     at ilock's peel) and the fill never runs.  That is [ShotK].

     AND THE CLAIM ARM BECOMES A CONVERSION.  Under C' the claimant's own
     reference carries the CLAIM-flavoured unit ([runit_claim], minted by
     ialloc's [ClaimL] iget) rather than a plain one, and the withdraw takes
     BOTH it and the [iclaim]: it spends the [rc] column, mints the [r]
     column and retires [c], all in the one region open it already takes,
     and hands back [runit_plain] -- so the child reference leaves create's
     fill unit-carrying exactly as every other reference does, and the
     [1 <= n] the retire's arithmetic needs comes FREE off the LANDED (R1)
     [r + rc <= n].  (§5'''' RULING C's cbit inequality is refuted by
     machine-checked counterexample; this is its replacement.) *)
  Definition ireg_wd_lic (o : ilkc) (g : gname) (z : Z) : iProp Σ :=
    match o with
    | ClaimK ty t q => (iclaim z ty t q ∗ IcacheRef.runit_claim z)%I
    | PlainK        => IcacheRef.runit_plain z
    | ShotK ty      => IcacheRef.ity_shot g ty
    end.

  (* what comes BACK: the claim arm's pair CONVERTS into the plain unit, the
     plain unit is BORROWED and returned verbatim, and the one-shot is
     persistent so returning it costs nothing. *)
  (* ...AND THE CLAIM ARM CARRIES THE PARKED TRANSACTION SHARE BESIDE IT
     (durable-disk C-5).  The claim box parked [q] of transaction [t]'s
     [LogDefs.ln_tx] element for the length of the window ([ireg_cpin]) and
     the withdrawal is that window's EXIT, so the share comes home here --
     at the [(t, q)] the claimant's own [IcacheRef.iclaim] names, which is
     what makes it rejoinable with the residue create kept.  It rides
     INSIDE this payout rather than beside it (durable-notes, "REPLACING ONE
     CONJUNCT OF A BIG PAYLOAD BY ANOTHER"): the fifteen [PlainK]/[ShotK]
     call sites of [SpecIlock] are then byte-stable, and only create's
     [ClaimK] fill -- the one site that can be in the window at all --
     splits the pair. *)
  Definition ireg_wd_back (o : ilkc) (g : gname) (z : Z) : iProp Σ :=
    match o with
    | ClaimK _ t q => (IcacheRef.runit_plain z
                       ∗ t ↪[ln_tx icfg_log]{#q} tt)%I
    | PlainK       => IcacheRef.runit_plain z
    | ShotK ty     => IcacheRef.ity_shot g ty
    end.

  (* THE CLAIM PACKAGE's ELIM (SIMP-2, ghost-simplification.md §5.1).
     [IcacheRef.inode_claimed] -- what [SpecIalloc] now hands back as ONE
     row -- unpacks in a single destruct into the reference the caller
     keeps and, beside it, EXACTLY [ireg_wd_lic (ClaimK ty)]: the licence
     create's fill presents to [wp_ilock_sconf].  So the receipt's three
     rows travel bundled and arrive already in the shape ilock asks for;
     nothing is proved here that the ClaimK arm did not already state.
     (The extra [lockG] binder is [IcacheRef.inode_ref]'s, not this
     lemma's: the reference's liveness slice is stated over the icache
     lock's ghost theory, and this section does not carry it.) *)
  Lemma inode_claimed_to_ClaimK `{!lockG Σ} ty k q dev inum t qt g :
    IcacheRef.inode_claimed ty k q dev inum t qt ⊢
    IcacheRef.inode_ref k q dev inum ∗
    ireg_wd_lic (ClaimK ty t qt) g (bv_unsigned inum).
  Proof.
    rewrite /IcacheRef.inode_claimed /ireg_wd_lic.
    iIntros "($ & H2 & H3)". iFrame.
  Qed.

  (* ...and what the claim arm BUYS, which is the whole point of item 7 *)
  Definition ireg_wd_ty (o : ilkc) (d : dinode) : Prop :=
    match o with ClaimK ty _ _ => di_type d = ty | _ => True end.

  (* THE WITHDRAW's OWN INDEX RESTRICTION.  [ShotK] never reaches this
     mover: its one-shot kills ilock's uncached arm five hundred lines
     earlier, so the fill -- and therefore the withdrawal -- does not run.
     Stated as a premise rather than as a [False] arm of [ireg_wd_lic] so
     that ONE definition serves both this lemma and [SpecIlock]'s clause. *)
  Definition ilk_fills (o : ilkc) : Prop :=
    match o with ShotK _ => False | _ => True end.

  (* THE POST, PER INDEX, at [SpecIlock]'s [filled] indicator.  [ClaimK]'s
     arm is where create's [create_fresh_ty] comes from: the claim box is
     the ONLY shape a claimed inum can be in, so the fill is forced and both
     the indicator and the type equation are theorems, not assumptions. *)
  Definition ilk_post (o : ilkc) (filled : bool) (d : dinode) : Prop :=
    match o with
    | ClaimK ty _ _ => filled = true /\ di_type d = ty
    | PlainK        => True
    | ShotK _       => filled = false
    end.

  (* the fill arm's payout, assembled: an index that CAN fill and that has
     just been through the withdraw has both halves of its post. *)
  Lemma ilk_post_fill (o : ilkc) (d : dinode) :
    ilk_fills o -> ireg_wd_ty o d -> ilk_post o true d.
  Proof.
    destruct o as [ty tt0 qq0 | | ty]; cbn.
    - intros _ H. split; [reflexivity | exact H].
    - intros _ _. exact I.
    - intros [] _.
  Qed.

  Lemma ireg_withdraw (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (ds : list dinode)
      (b : Z) (bsl : list (bv 8)) (o : ilkc) (gy : gname) :
    ↑iregN ⊆ E ->
    (* see [ireg_read] -- the byte view's open replaces the half/half
       agreement (durable-disk 1c-flip step 3) *)
    ↑logN ⊆ E ->
    (* [ShotK] never reaches the fill -- see [ilk_fills]. *)
    ilk_fills o ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    b = IBLOCK inum inodestart ->
    diblk_wf ds ->
    bsl = diblk_bytes ds ->
    bv_unsigned (di_type (ds !!! islot inum)) <> 0 ->
    ireg_inv γi γfs inodestart nib -∗
    imark γi (bv_unsigned inum) -∗
    (* THE CLAIM, SPENT (iclaim-ledger.md §2.4: "c retires Some -> None
       there").  The withdrawal is the ONE mover that carries a claimed slot
       from the region's IN arm to the MARKED one, so it is the one place the
       c column HAS to be retired: the marked arm's clause says [c = None]
       (that is what lets every byte-writing mover re-establish the claim pin
       for free), and the retire is not frame-preserving while the
       claimant's fragment is outstanding.  The premise is landed one
       increment early for that reason -- §2.8 item 7 owns its discharge in
       [ProofIlock], where create's [iclaim] arrives from [ireg_claim_au].

       UNDER RULING C' THE CLAIM ARM IS A CONVERSION and the pair it takes
       is [iclaim ∗ runit_claim]: see [ireg_wd_lic]. *)
    ireg_wd_lic o gy (bv_unsigned inum) -∗
    (b ↪[fs_cache γfs]{#(1/2)} bsl) ={E}=∗
    (* THE TYPED PAYOUT (iclaim-ledger.md §5.2(a), item 7b): the claim was
       minted at the type [ialloc] wrote, the claim pin says the box's record
       still has it, and the spend hands the equation to create's fill.  That
       is [create_fresh_ty]'s [di_type dnc = ty], sourced. *)
    ⌜fresh_shape (ds !!! islot inum)⌝ ∗
    ⌜ireg_wd_ty o (ds !!! islot inum)⌝ ∗
    (* (L5) LEAVES WITH THE RECORD (durable-disk 2b-inode-3).  The claim
       box's fill has to park [FsStateInode.inode_local] of a node whose
       record is this one, and the type enumeration is the one clause that
       has no other source (see (L5)'s note at [ireg_link_ok]).  Free here:
       the mover has the slot open and reads it off. *)
    ⌜ireg_ty_ok (ds !!! islot inum)⌝ ∗
    ireg_wd_back o gy (bv_unsigned inum) ∗
    dinode_at γi inum (ds !!! islot inum) ∗
    (b ↪[fs_cache γfs]{#(1/2)} bsl) ∗
    (* THE ERA's ABSTRACT VALUE LEAVES WITH THE RECORD (durable-disk C-3c),
       and this is the ONE exit from the region's IN arm.  It comes out
       UNTIED -- the box is [fresh_shape], so [ireg_top_park]'s tie is on its
       vacuous side -- which is exactly the shape the fill used to take off
       the pool's marker arm, so ProofIlock's [ireg_top_retag] is unchanged. *)
    (∃ n : fs_node, top_frag (fs_gamma_L γfs) (bv_unsigned inum) n).
  Proof.
    iIntros (HE HEl Hfills Hin Hb Hwf Hbsl Hnz) "#Hinv Hmk Hcl Hhalf".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iDestruct "Hrb" as "[Hrb0 #Hseal]".
    iDestruct "Hrb0" as (home Xv) "#Hbinv".
    assert (HlogI : (↑logN : coPset) ⊆ E ∖ ↑iregN)
      by (apply subseteq_difference_r; [apply logN_iregN_disj | exact HEl]).
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds0) "(>%Hwf0 & >%Hcp0 & >Hrec & >Hsls)".
    iDestruct (ireg_recs_to_blk γfs inodestart (ireg_bi inum) ds0 Hwf0
                with "Hrec") as "Hfsb".
    rewrite -(ireg_bi_iblock inum inodestart) -Hb.
    iMod (fs_bytes_agree (E ∖ ↑iregN) (fs_bytes γfs) (fs_cache γfs)
            (fs_exc γfs) home Xv b (diblk_bytes ds0) bsl HlogI
            with "Hbinv Hseal Hfsb Hhalf") as "(%Hbytes & Hfsb & Hhalf)".
    assert (Hds0 : ds0 = ds).
    { apply (diblk_bytes_inj ds0 ds Hwf0 Hwf). rewrite -Hbytes -Hbsl. reflexivity. }
    subst ds0.
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    (* the marker in the caller's hand refutes the OUT arm *)
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(%Ht0p & _ & _)"; exfalso; exact (Hnz Ht0p)].
    iDestruct "Harm" as "[[%Hin1 [Hfr Hpk]] | [%Ht2 Hmk']]"; last first.
    { iExFalso. iApply (imark_excl with "Hmk Hmk'"). }
    assert (Hfresh : fresh_shape (ds !!! islot inum))
      by exact (ireg_in_shape cl (ds !!! islot inum) Hin1 Hnz).
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    (* THE RETIRE.  [link_spend_claim] pins [cl = Some (Excl tt)] off the
       fragment and drops the column; the slot is re-parked at [None], which
       is what the MARKED arm the withdrawal moves it to demands. *)
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    (* THE THREE ARMS, DISCHARGED IN ONE STEP (§5'.3, RESHAPED BY RULING
       C').  [ClaimK] is the CONVERSION: the [iclaim] fragment pins the
       column to [Some (Excl ty)] and the claim pin's third conjunct names
       the record's type; the claim-flavoured unit forces [1 <= rc]
       ([IcacheRef.link_rc_ge]), so the [rc] column can be spent, an [r]
       unit minted in its place and the c column retired -- three ledger
       moves in the one open, and (R1) carries across them by
       [ireg_ref_ok_retire] with no count fact needed from the caller.
       [PlainK]: the borrowed plain unit forces [1 <= r]
       ([IcacheRef.link_runit_ge] at the plain flavour) and the pin's
       contrapositive ([ireg_ref_ok_unclaimed]) DERIVES [c = None] --
       nothing retires, nothing is spent, and the unit goes straight back
       out.  [ShotK] does not reach this mover ([ilk_fills]). *)
    iDestruct (ireg_shp_split with "Hfdisj") as "[Hfsh Hcpin]".
    iAssert (|==> ∃ rl' rcl' : nat,
                  link_auth (bv_unsigned inum) None rl' fz rcl'
                  ∗ ⌜ireg_ref_ok rl' rcl' cn None (ds !!! islot inum)⌝
                  ∗ ⌜ireg_wd_ty o (ds !!! islot inum)⌝
                  ∗ ireg_wd_back o gy (bv_unsigned inum))%I
      with "[Hla Hcl Hcpin]"
      as ">(%rl' & %rcl' & Hla & %Href' & %Hty & Hwback)".
    { destruct o as [tyc tc qc | | tys];
        rewrite /ireg_wd_lic /ireg_wd_ty /ireg_wd_back.
      - iDestruct "Hcl" as "[Hcl Hru]".
        iDestruct (link_claim_agree with "Hla Hcl") as %Hcl.
        assert (Htyc : di_type (ds !!! islot inum) = tyc)
          by (rewrite Hcl in Hclm;
              exact (ireg_claim_ok_ty ((tyc, (tc, qc)) : ctyval) fz _ Hclm)).
        (* THE PARKED SHARE, IDENTIFIED.  The claimant's own fragment pins
           the column, hence the pair the region parked, so what comes out
           is the very element create handed ialloc. *)
        iEval (rewrite Hcl /ireg_cpin /=) in "Hcpin".
        iDestruct (IcacheRef.link_rc_ge with "Hla Hru") as %Hrcge.
        destruct rcl as [| rcl0]; [exfalso; lia |].
        iMod (IcacheRef.link_spend_refc with "Hla Hru") as "Hla".
        iMod (IcacheRef.link_mint_ref with "Hla") as "[Hla Hplain]".
        iMod (link_spend_claim with "Hla Hcl") as "Hla".
        iModIntro. iExists (S rl), rcl0. iFrame "Hla".
        iSplitR;
          [iPureIntro;
           exact (ireg_ref_ok_retire rl rcl0 cn cl (ds !!! islot inum)
                    Href Hnz) |].
        iSplitR; [iPureIntro; exact Htyc |].
        rewrite /IcacheRef.runit_plain. iFrame "Hplain Hcpin".
      - iDestruct (IcacheRef.link_runit_ge false with "Hla Hcl") as %Hge.
        assert (Hc0 : cl = None)
          by exact (ireg_ref_ok_unclaimed rl rcl cn cl (ds !!! islot inum)
                      Href Hge).
        rewrite Hc0. iModIntro. iExists rl, rcl. iFrame "Hla".
        iSplitR;
          [iPureIntro;
           exact (ireg_ref_ok_unclaim rl rcl cn cl (ds !!! islot inum) Href) |].
        iSplitR; [iPureIntro; exact I |]. iFrame "Hcl".
      - destruct Hfills. }
    (* RULING R: the retire makes (R3) vacuous, and RULING C''s conversion
       moves the two r columns in step -- [Href'] above is the pin that
       carries it.  The record does not move either way. *)
    iDestruct (ireg_rcol_intro (bv_unsigned inum) None rl' fz cn
                 rcl' (ds !!! islot inum) Href'
                 with "Hla") as "Hla".
    assert (Hclm0 : ireg_claim_ok None fz (ds !!! islot inum))
      by exact (ireg_claim_ok_none _ _).
    iDestruct (ireg_shp_none fz with "Hfsh") as "Hfdisj".
    iMod ("Hclose" with "[Ha Hreg Hfsb Hmk Hla Hep Hlnk Hslback Hback Hrf Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Hmk Hla Hep Hlnk Hslback Hrf Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      rewrite (ireg_bi_iblock inum inodestart) in Hb.
      rewrite Hb. iSplitL "Hfsb";
        [iApply (ireg_recs_of_blk γfs inodestart (ireg_bi inum) ds Hwf
                   with "Hfsb") |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hmk Hla Hep Hlnk Hrf Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) (ds !!! islot inum)
                None rl' fz cn Hlok Hclm0 Hfrz
                with "Hla Hep Hlnk [] Hcnt Hfdisj Hfrcp").
      { iLeft. iPureIntro. reflexivity. }
      iLeft. iSplitR "Hrf"; [iRight; iSplitR; [iPureIntro; split; [exact Hnz | reflexivity] | iExact "Hmk"] | iExact "Hrf"]. }
    iModIntro. iSplitR; [iPureIntro; exact Hfresh |].
    iSplitR; [iPureIntro; exact Hty |].
    iSplitR;
      [iPureIntro; exact (ireg_link_ok_ty (ds !!! islot inum) Hlok) |].
    (* the park leaves with the record, untied (the box is [fresh_shape]) *)
    iDestruct "Hpk" as (n0) "[_ Hn0]".
    iFrame "Hwback Hfr Hhalf". iExists n0. iExact "Hn0".
  Qed.

  (* ---- A CLAIM BOX HAS NO RECORD OUT (iclaim-ledger.md §5''''' step 2) --

     THE FACT [wp_ilock_sconf]'s [ClaimK] arm needs, and the reason its post
     can pin [filled = true] rather than leave it a hypothesis: while an
     [iclaim] is outstanding NOBODY holds the inum's [dinode_at].

     It is structural, not arithmetic.  A claimed column ([c <> None])
     refutes the MARKED arm outright -- [ireg_marked_ok] says [c = None] --
     so the slot must be on the IN arm or the PENDING one, and both of those
     park the record fragment [z ↪[γi] d] INSIDE the invariant; a second
     full-fraction element at the same key is invalid ([dinode_at_excl]).

     WHAT IT BUYS.  ilock has three ways to reach its continuation without
     running §16.4's box fill: the CACHED arm (the entry was loaded by an
     earlier ilock), the pool's ALLOCATED bundle, and the box itself.  The
     first two both hand the caller an [ic_loaded] / a pool bundle built
     around a [dinode_at], so this lemma kills them and the claimant's fill
     is FORCED.  That is exactly the "no free-and-reclaim since my claim"
     carrier fs-icache.md §20.7 asked for -- supplied by the c column, and
     it is what sources [create_fresh_ty]'s type equation. *)
  Lemma ireg_claim_no_out (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (ty : bv 16) (t : nat) (qt : Qp) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    iclaim (bv_unsigned inum) ty t qt ={E}=∗
    False.
  Proof.
    iIntros (HE Hin) "#Hinv Hdn Hcl".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf0 & >%Hcp0 & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf0 as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    iDestruct (link_claim_agree with "Hla Hcl") as %Hcl.
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]".
    - iDestruct "Harm" as "[[%Hin1 [Hfr Hpk]] | [%Ht2 Hmk']]".
      + iDestruct (dinode_at_excl with "Hdn Hfr") as %[].
      + (* the MARKED arm demands [c = None]; the fragment says otherwise *)
        exfalso. destruct Ht2 as [_ Hc0]. rewrite Hc0 in Hcl. discriminate.
    - iDestruct "Hpend" as "(%Ht0p & Hfr & _ & _)".
      iDestruct (dinode_at_excl with "Hdn Hfr") as %[].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE TWO NLINK-MOVING WRITES (design §20.6)                          *)
  (* ------------------------------------------------------------------ *)

  (* [dp->nlink++; iupdate(dp)] -- mkdir's [".."] and sys_link's
     [ip->nlink++].  It is [ireg_write_au] with the ledger moving in the
     same ghost step as the count that pays for it: (L1) grows on BOTH
     sides at once, which is what keeps the cap an inequality nobody has to
     re-argue.  The fragment travels to the [dirlink] that deposits it in
     the directory's payload.

     LANE G6 DELETED THE FLAVOUR INDEX (V1's [fl], widened by V5' to
     [option (option Z)]) with the ledger it selected: it chose which of
     [ilink]/[ilinkd]/[ilinkdp]+[iparent] the mint paid out and carried
     three type premises for the choice.  The type register's fragments are
     one shape, so the mover pays out one pile and takes none of them.

     WHAT V4'S DEAD PREMISE SAID: a PLAIN mint must show its record is
     NOT a directory, which is (T1')'s preservation -- and a walk-level
     fact at all three plain-minting sites (create's non-dir child,
     sys_link's file target).

     THE ONE UNIT OF PAYMENT IS THE SAME UNIT on all flavours -- the
     increment premise, the guard and (L4) are shared, and the sum
     [wl + wdu + wdt] rises by exactly one either way, which is what
     makes the index a flavour rather than a second currency. *)
  (* ---- RULING A-prime's PIN, INDEXED BY WHICH ARM IS PAID -------------

     §3.9 states the freeze-pin price as a disjunction, and a disjunction is
     the wrong SHAPE for a borrowed-and-returned premise: the mover hands
     back what it was given, but a caller that presented the TOKEN could not
     tell the returned [⌜…⌝ ∨ ifreeze_off] apart from the pure arm and would
     have to drop it -- which is exactly the resource sys_link needs at its
     re-park.  So the arm is a parameter, and then in-and-out are the same
     proposition at the same [pin]: [true] is the token, [false] the pure
     fact.  Every disjunction in §3.9's text reads off this by [destruct
     pin]. *)
  Definition ireg_link_pin (pin : bool) (z : Z) (d : dinode) : iProp Σ :=
    (if pin then ifreeze_off z else ⌜bv_unsigned (di_nlink d) <> 0⌝)%I.

  (* ---- RULING A-prime's PIN READER (iclaim-ledger.md §3.9) ------------

     The two routes to "this slot is not frozen", as ONE lemma so that
     [ireg_write_link_fl] below stays a single linear walk.  The PURE arm is
     RULING A's contrapositive ([ireg_frz_ok_nz]: both freeze phases carry
     [di_nlink = 0], so a named record refutes them).  The TOKEN arm reads
     the column straight off the ledger by exclusivity
     ([IcacheRef.link_freeze_agree]), exactly as [ireg_freeze_au] does at its
     own mint.  Both the authority and the premise come back out: the reader
     spends nothing, which is what lets a checked-out holder hand its
     [ifreeze_off] into an [iupdate] and still have it at [iunlock]. *)
  Lemma ireg_link_pin_read (pin : bool) (z : Z) (c : ctyUR) (r : nat)
      (f : frzUR) (n : nat) (d : dinode) :
    ireg_frz_ok f n d ->
    ireg_rcol z c r f n d -∗
    ireg_link_pin pin z d -∗
    ireg_rcol z c r f n d ∗
    ireg_link_pin pin z d ∗
    ⌜f = Some (Excl FrzOff)⌝.
  Proof.
    intros Hfrz. iIntros "Hla Hpin". rewrite /ireg_link_pin. destruct pin.
    - iDestruct (ireg_rcol_freeze_agree with "Hla Hpin") as %Hfzo.
      iFrame "Hla Hpin". iPureIntro. exact Hfzo.
    - iDestruct "Hpin" as "%Hnlnz".
      iFrame "Hla". iSplitR; [iPureIntro; exact Hnlnz |].
      iPureIntro. exact (ireg_frz_ok_nz f n d Hnlnz Hfrz).
  Qed.

  (* [oty] is the TYPE REGISTER's value the caller CHOOSES, and it is
     available exactly where the register is empty -- create's fresh-child
     fill, which is where mkdir sets the child's value to [TDir dp] so that
     the parent's name record can assert "my target's parent is me".  At
     [None] the mover keeps whatever value the region holds and hands it
     back existentially (lane G5). *)
  Lemma ireg_write_link_reg (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (bsl : list (bv 8)) (pin : bool)
      (oty : option ity) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    (* THE INCREMENT, AT THE MACHINE'S OWN WIDTH (the twelfth stop).  The
       caller supplies what its [sh] actually gives it -- the sixteen-bit
       [++] -- together with the kernel's own NLINK_MAX guard, and the
       Z-level equation the ledger needs is derived HERE, under (L4).
       A CALLER CANNOT STATE THE Z FORM: at [di_nlink dn = 65535] it is
       FALSE, and nothing outside this region bounds the count above -- so
       the old premise was suppliable only where the count was already
       known ([fresh_shape]'s zero) and was unprovable at the one site that
       raises a real directory's count.  Both new premises are walk-level
       facts at every raising site: the store's own value, and the
       branch xv6 117c0e7 added. *)
    di_nlink dn' = add_vec (di_nlink dn : mword 16) (mword_of_int 1) ->
    di_nlink dn <> (mword_of_int 32767 : mword 16) ->
    (* THE FREEZE PIN'S PRICE, AND IT IS THE ONLY ONE IN THE TABLE
       (iclaim-ledger.md §3.1, RULING A).  This mover RAISES [nlink] off
       zero, so with the pin's [di_nlink = 0] conjunct landed it would have
       to re-establish the pin at a record that violates it.  It does not
       have to: the premise says the PRE-record is already named, and the
       pin's contrapositive ([ireg_frz_ok_nz]) then refutes both phases
       outright -- a slot mid-free is a slot nothing names, and nothing links
       to it.  A walk-level fact at its one raising site (mkdir's [dp], whose
       count is at least one because it is a live directory the caller has
       locked). *)
    (* ...and the premise itself moved from the pure list to the resource
       one at RULING A-prime; see below, just after [dinode_at]. *)
    (* THE FILL'S PREMISE (lane G5, [ireg_lnk_fill]).  A caller may CHOOSE
       the register's value only where the register is empty, i.e. at a
       record whose multiplicity is zero -- create's fresh child, the one
       site in the kernel that installs a value.  LAST in the pure list, so
       no landed caller's argument positions move (durable-notes.md). *)
    (forall v : ity, oty = Some v ->
       ireg_mult dn = 0%nat /\ ireg_reg_ok (bv_unsigned (di_type dn')) v) ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    (* THE FREEZE PIN'S PRICE, IN ITS RULING A-prime FORM (iclaim-ledger.md
       §3.9).  RULING A priced this as the pure left disjunct alone and IIIc
       proved that row FALSE at two of the mover's three sites: create's
       FRESH CHILD (whose pre-record's count is pinned at zero by
       [fresh_shape]) and sys_link's [ip->nlink++] (no guard, no fragment in
       hand -- namei's licence is borrowed and returned at the iget).  Every
       cheaper route was refuted there: no record fact and no count fact
       separates a fresh claim box from a mid-free box (that is §0's B1/B2
       debt restated), and all five licence rows fail at [nlink = 0].

       The honest supply is the TOKEN, and A-custody already says where it
       lives: on the payload's custody path, i.e. in the checked-out
       holder's hand.  Both failing sites hold their inode LOCKED, so both
       have it -- [SpecIlock]'s post hands it over
       ([IcacheEscrow.ic_payload]) and [SpecIunlock]'s precondition takes it
       back.  mkdir's [dp->nlink++] and every future caller with a live
       record keep the pure arm for free.

       BORROWED AND RETURNED: the mover only READS the column through it
       ([IcacheRef.link_freeze_agree]), so it goes back out below untouched
       and a holder's ilock/iunlock pair is undisturbed. *)
    ireg_link_pin pin (bv_unsigned inum) dn -∗
    (* [SpecLogWrite.lw_au_rec]'s premise, as [ireg_write_au]'s is
       (durable-disk 2b-inode-1): one RECORD's 64-byte run out and back. *)
    |={E, E ∖ ↑iregN}=> ∃ rec_old : list (bv 8),
      ⌜length rec_old = 64%nat⌝ ∗
      FsStateDefs.byte_range (fs_gamma_L γfs) (IBLOCK inum inodestart)
        (Z.of_nat (64 * islot inum)) rec_old ∗
      (⌜rec_old = take 64%nat (drop (64 * islot inum)%nat bsl)⌝ -∗
       FsStateDefs.byte_range (fs_gamma_L γfs) (IBLOCK inum inodestart)
         (Z.of_nat (64 * islot inum)) (dinode_bytes dn')
       ={E ∖ ↑iregN, E}=∗
       dinode_at γi inum dn'
       (* THE COUNTING RA's OWN UNIT (durable-disk 2b-inode-5): the raised
          count mints one [FsStateLink.link_tok] at this inum, and it goes
          OUT -- to the [dirlink] that files it in a directory's
          [FsStateInode.ent_toks] inside that directory's checked-out
          payload.  The region keeps only the AUTHORITY. *)
       ∗ (∃ v : ity,
            ⌜ireg_reg_ok (bv_unsigned (di_type dn')) v
             /\ (forall w, oty = Some w -> v = w)⌝
            ∗ FsStateLink.link_toks (fs_gamma_L γfs) (bv_unsigned inum)
                (link_reps (ireg_dot_delta (bv_unsigned (di_type dn))
                              (bv_unsigned (di_nlink dn))) v)) ∗
       ireg_link_pin pin (bv_unsigned inum) dn).
  Proof.
    iIntros (HE Hin Hdn' Hnz Hstab Hbump Hgrd Hup)
            "#Hinv Hdn Hpin".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp0 & >Hrec & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    (* the coupling names the region's record at this slot -- what
       [diblk_bytes_inj] used to do through the block's bytes *)
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    assert (Hdnwf : dinode_wf dn)
      by (rewrite -Hdeq; exact (ireg_blk_slot ds (islot inum) Hwf Hsl)).
    assert (Hwfi : diblk_wf (<[islot inum := dn']> ds))
      by exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn').
    iDestruct (ireg_recs_acc_upd γfs inodestart (ireg_bi inum) ds (islot inum)
                 Hsl Hlen16 with "Hrec") as "[Hrun Hrecback]".
    iEval (rewrite Hkey Hdeq) in "Hrun".
    iEval (rewrite (rec_owned_at_IBLOCK (fs_gamma_L γfs) inodestart inum dn))
      in "Hrun".
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(_ & Hpz & _)"; iExFalso; iApply (dinode_at_excl with "Hpz Hdn")].
    iDestruct "Harm" as "[[%Hin1 [Hfr Hpk]] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite Hdeq in Hlok. rewrite Hdeq in Hclm. rewrite Hdeq in Hfrz.
    iModIntro. iExists (dinode_bytes dn).
    iSplitR; [iPureIntro; exact (dinode_bytes_length dn Hdnwf) |].
    iFrame "Hrun".
    iIntros (_) "Hrun".
    (* THE FREEZE IS REFUTED BEFORE ANYTHING ELSE HAPPENS (§3.1).  The new
       premise says the pre-record is NAMED; the pin says a mid-transition
       record is not; so the column reads [FrzOff] and the pin at the raised
       record is vacuous whatever [nlink] the mint writes. *)
    (* THE PIN'S TWO ROUTES TO THE SAME CONCLUSION (§3.9) -- see
       [ireg_link_pin_read] above.  Both the auth and the premise come back. *)
    iEval (rewrite Hdeq) in "Hla".
    iEval (rewrite Hdeq) in "Hlnk".
    iDestruct (ireg_link_pin_read pin (bv_unsigned inum) cl rl
                 fz cn dn Hfrz with "Hla Hpin") as "(Hla & Hpin & %Hfz0)".
    (* RULING R: the w columns move here, the r columns and the type do not,
       so the clause rides on [ireg_ref_ok_stable] and this mover -- like
       every other byte mover -- owes it nothing. *)
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    (* (L4) IS OPEN HERE AND NOWHERE ELSE, so this is where the machine's
       [++] becomes the ledger's [+1].  The same lemma hands back the
       clause's own PRESERVATION, and it is one lemma so that a writer
       cannot take the arithmetic without re-establishing the invariant
       that made it true. *)
    destruct (ireg_nlink_bump (di_nlink dn) (ireg_link_ok_short dn Hlok) Hgrd)
      as [Hstep Hshort].
    assert (Hnl : bv_unsigned (di_nlink dn') = bv_unsigned (di_nlink dn) + 1)
      by (rewrite Hbump; exact Hstep).
    assert (Hsh' : bv_unsigned (di_nlink dn') <= 32767)
      by (rewrite Hbump; exact Hshort).
    (* the type does not move ([ireg_write_au]'s step, verbatim): the LEFT
       disjunct of [di_type_stable] is dead against [Hnz]. *)
    assert (Hty' : di_type dn' = di_type dn)
      by (destruct Hstab as [H0 | Heq]; [exfalso; exact (Hnz H0) | exact Heq]).
    (* (L3)/(L4)/(L5) at the raised record: the type does not move and the
       count is bounded by the guard the caller supplied. *)
    assert (Hlok' : ireg_link_ok dn').
    { split_and!.
      - intros H0. exfalso. exact (Hnz H0).
      - exact Hsh'.
      - exact (ireg_ty_ok_stable dn' dn Hstab Hlok). }
    (* THE CLAIM PIN IS VACUOUS HERE (iclaim-ledger.md §2.4).  The caller's
       own [dinode_at] put this open on the MARKED arm, whose clause says
       [cl = None] -- so a byte-writing mover owes the pin nothing, and its
       premise list does not move. *)
    assert (Hclm' : ireg_claim_ok cl fz dn')
      by (rewrite (proj2 Ht2); exact I).
    assert (Hfrz' : ireg_frz_ok fz cn dn')
      by exact (ireg_frz_ok_of_off fz cn dn' Hfz0).

    (* nlink GROWS here, so the receipt's antecedent is absurd at [dn'] *)
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { intros H0. exfalso. pose proof (di_nlink_nonneg dn). lia. }
    (* THE RA's OWN STEP (durable-disk 2b-inode-4): the raised count is
       one [link_mint] on the region's per-inum authority, and the minted
       token joins the slot's pile.  A basic update, so it composes into
       this AU at no mask cost. *)
    assert (Htyeq : bv_unsigned (di_type dn') = bv_unsigned (di_type dn))
      by (destruct Hstab as [H0 | Heq];
          [exfalso; exact (Hnz H0) | rewrite Heq; reflexivity]).
    assert (Hmb : ireg_mult dn'
                  = (ireg_mult dn
                     + ireg_dot_delta (bv_unsigned (di_type dn))
                         (bv_unsigned (di_nlink dn)))%nat)
      by exact (ireg_mult_bump dn dn' Hnl Htyeq).
    iAssert (|==> ireg_lnk γfs (bv_unsigned inum) dn'
             ∗ ∃ v : ity,
                 ⌜ireg_reg_ok (bv_unsigned (di_type dn')) v
                  /\ (forall w, oty = Some w -> v = w)⌝
                 ∗ FsStateLink.link_toks (fs_gamma_L γfs) (bv_unsigned inum)
                     (link_reps (ireg_dot_delta (bv_unsigned (di_type dn))
                                   (bv_unsigned (di_nlink dn))) v))%I
      with "[Hlnk]" as ">[Hlnk Htok]".
    { destruct oty as [v |].
      - destruct (Hup v eq_refl) as [Hz0 Hokv].
        iMod (ireg_lnk_fill γfs (bv_unsigned inum) dn dn' v
                (ireg_dot_delta (bv_unsigned (di_type dn))
                   (bv_unsigned (di_nlink dn))) Hz0
                ltac:(rewrite Hmb Hz0; lia) Hokv with "Hlnk") as "[$ Hts]".
        iModIntro. iExists v. iFrame "Hts". iPureIntro. split; [exact Hokv |].
        intros w Hw. by injection Hw.
      - iMod (ireg_lnk_bump γfs (bv_unsigned inum) dn dn'
                (ireg_dot_delta (bv_unsigned (di_type dn))
                   (bv_unsigned (di_nlink dn))) Hmb Htyeq with "Hlnk")
          as "[$ (%v & %Hokv & Hts)]".
        iModIntro. iExists v. iFrame "Hts". iPureIntro.
        split; [rewrite Htyeq; exact Hokv | intros w Hw; discriminate]. }
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iEval (rewrite -(rec_owned_at_IBLOCK (fs_gamma_L γfs) inodestart inum dn'))
      in "Hrun".
    iEval (rewrite -Hkey) in "Hrun".
    iDestruct ("Hrecback" $! dn' with "Hrun") as "Hrec".
    iMod ("Hclose" with "[Ha Hreg Hrec Hmk Hla Hep Hlnk Hslback Hback Hrf Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hrec Hmk Hla Hep Hlnk Hslback Hrf Hcnt Hfdisj Hfrcp]").
      { intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact Hwfi |].
      iSplitR.
      { iPureIntro. intros i Hi.
        destruct (decide (i = islot inum)) as [->|Hne].
        - rewrite /m' -(ireg_key_split inum) lookup_insert.
          rewrite list_lookup_total_insert; [done | lia].
        - rewrite /m' lookup_insert_ne; last first.
          { rewrite (ireg_key_split inum). intros Hc.
            destruct (ireg_key_inj (ireg_bi inum) (ireg_bi inum)
                        (islot inum) i Hsl Hi Hc) as [_ Hi'].
            exact (Hne (eq_sym Hi')). }
          rewrite list_lookup_total_insert_ne; [| by apply not_eq_sym].
          exact (Hcp0 i Hi). }
      iSplitL "Hrec"; [iExact "Hrec" |].
      iApply ("Hslback" $! dn' with "[Hmk Hla Hep Hlnk Hrf Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iDestruct (ireg_rcol_intro (bv_unsigned inum) cl rl
                   fz cn rcl dn'
                   (ireg_ref_ok_stable rl rcl cn cl dn dn' Hty' Href)
                   with "Hla") as "Hla".
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) dn' cl rl fz cn Hlok' Hclm' Hfrz' with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp").
      iLeft. iSplitR "Hrf"; [iRight; iSplitR; [iPureIntro; split; [exact Hnz | exact (proj2 Ht2)] | iExact "Hmk"] | iExact "Hrf"]. }
    (* ...and the pin premise goes back out, unspent (§3.9's
       borrowed-and-returned). *)
    iModIntro. iFrame "Hdn Htok Hpin".
  Qed.

  (* THE THREE INSTANCE WRAPPERS ARE GONE (durable-disk lane G, slice 6e).
     [ireg_write_link] (fl = None), [ireg_write_link_d] (Some None) and
     [ireg_write_link_p] (Some (Some pv)) each pinned one flavour of the
     mover above.  None of them ever had a caller: [ProofIupdate] applies
     [ireg_write_link_reg] directly.
     carries.  The prose elsewhere in the tree that still says
     "[ireg_write_link]" means this file's flavour-indexed mover. *)

  (* [ip->nlink--; iupdate(ip)] -- sys_unlink's decrement, and THE ONLY
     nlink-LOWERING region write in the kernel (design §20.6).  It is the
     dual of [ireg_write_link_reg]: the drop is paid for by CONSUMING the
     register's fragments, so no fragment is ever left stranded above the
     count that backs it.

     This is exactly why [ireg_write_au] may demand [di_nlink_stable]: the
     one writer that would violate it does not go through the ordinary
     flush at all.

     LANE G6 DELETED THE FLAVOUR INDEX with the ledger it selected: the
     pile of type-register fragments below is the whole of what the drop
     spends. *)
  Lemma ireg_write_unlink_reg (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (bsl : list (bv 8)) (uty : ity) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    bv_unsigned (di_nlink dn) = bv_unsigned (di_nlink dn') + 1 ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    (* THE COUNTING RA's OWN UNIT, COMING BACK (durable-disk 2b-inode-5).
       This is the one flush in the kernel that LOWERS a count, so it is
       the one that returns a [FsStateLink.link_tok] to the region's
       authority -- the token the directory entry whose removal this
       decrement pays for gave up out of its own
       [FsStateInode.ent_toks]. *)
    (* ...AND IT IS A PILE, not a single unit: at rmdir's [ip->nlink--] the
       child's multiplicity crosses [2 -> 0], so the ["."] the live form
       held comes back beside the name's ([ireg_dot_delta]).  The value is
       the caller's; the RA's agreement law forces it to be the region's. *)
    FsStateLink.link_toks (fs_gamma_L γfs) (bv_unsigned inum)
      (link_reps (ireg_dot_delta (bv_unsigned (di_type dn'))
                    (bv_unsigned (di_nlink dn'))) uty) -∗
    (* the RECORD-GRANULAR form (durable-disk 2b-inode-1), with the
       observation counter [v] riding beside the run exactly as it did
       beside the block. *)
    |={E, E ∖ ↑iregN}=> ∃ (rec_old : list (bv 8)) (v : nat),
      ⌜length rec_old = 64%nat⌝ ∗
      FsStateDefs.byte_range (fs_gamma_L γfs) (IBLOCK inum inodestart)
        (Z.of_nat (64 * islot inum)) rec_old ∗
      (* THE DEPOSIT (fs-log.md §G.17).  This is the ONLY writer in the
         kernel that LOWERS nlink, hence the only one that can park a fresh
         zero, hence the only one that owes the receipt.  It hands the
         caller this inum's observation counter [v] with its epoch bound
         and takes back the receipt at the record it is about to write --
         which unlink builds out of [SpecIupdate]'s credgen post,
         [∃ e, logged_at γ e (IBLOCK …) ∗ ⌜v <= e⌝], the comparison having
         been cashed inside [log_write] against the [ln_ep] auth (§G.17
         blocker 4).  Every other region writer carries the receipt for
         free, by [ireg_ep_mono]. *)
      log_epoch_lb icfg_log v ∗
      (⌜rec_old = take 64%nat (drop (64 * islot inum)%nat bsl)⌝ -∗
       izrcpt (bv_unsigned inum) dn' v -∗
       FsStateDefs.byte_range (fs_gamma_L γfs) (IBLOCK inum inodestart)
         (Z.of_nat (64 * islot inum)) (dinode_bytes dn')
       ={E ∖ ↑iregN, E}=∗ dinode_at γi inum dn').
  Proof.
    iIntros (HE Hin Hdn' Hnz Hstab Hnl) "#Hinv Hdn Htok".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp0 & >Hrec & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    (* the coupling names the region's record at this slot -- what
       [diblk_bytes_inj] used to do through the block's bytes *)
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    assert (Hdnwf : dinode_wf dn)
      by (rewrite -Hdeq; exact (ireg_blk_slot ds (islot inum) Hwf Hsl)).
    assert (Hwfi : diblk_wf (<[islot inum := dn']> ds))
      by exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn').
    iDestruct (ireg_recs_acc_upd γfs inodestart (ireg_bi inum) ds (islot inum)
                 Hsl Hlen16 with "Hrec") as "[Hrun Hrecback]".
    iEval (rewrite Hkey Hdeq) in "Hrun".
    iEval (rewrite (rec_owned_at_IBLOCK (fs_gamma_L γfs) inodestart inum dn))
      in "Hrun".
    (* THE SLOT COMES OUT BEFORE THE MASK CLOSES, which is what lets the
       counter's value be handed to the caller in the same fupd. *)
    iDestruct (ireg_slots_acc_upd γfs γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%rl & %cl & %fz & %cn & Hla & %Hlok & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) [Hep Hlnk]]".
    iEval (rewrite Hdeq) in "Hep".
    iDestruct (ireg_ep_open with "Hep") as (v) "[#Hvlb Hepback]".
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(_ & Hpz & _)"; iExFalso; iApply (dinode_at_excl with "Hpz Hdn")].
    iDestruct "Harm" as "[[%Hin1 [Hfr Hpk]] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite Hdeq in Hlok. rewrite Hdeq in Hclm. rewrite Hdeq in Hfrz.
    iModIntro. iExists (dinode_bytes dn), v.
    iSplitR; [iPureIntro; exact (dinode_bytes_length dn Hdnwf) |].
    iFrame "Hrun Hvlb".
    iIntros (_) "Hrc Hrun".
    iDestruct ("Hepback" $! dn' with "Hrc") as "Hep".
    (* THE FREEZE PIN IS FREE HERE (§3.1's cost table): the drop's own
       premise reads [old = new + 1] over the nonnegative Z, so the
       PRE-record's count is already off zero and the pin's contrapositive
       refutes both phases with no premise added. *)
    assert (Hnlnz : bv_unsigned (di_nlink dn) <> 0).
    { pose proof (di_nlink_nonneg dn'). lia. }
    assert (Hfz0 : fz = Some (Excl FrzOff))
      by exact (ireg_frz_ok_nz fz cn dn Hnlnz Hfrz).
    (* RULING R: an unlink moves the w columns only -- the r columns and the
       type stay, so the clause rides on [ireg_ref_ok_stable]. *)
    iEval (rewrite Hdeq) in "Hla".
    iEval (rewrite Hdeq) in "Hlnk".
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    (* the type does not move: [di_type_stable]'s LEFT disjunct is dead
       against [Hnz], so (T1) travels to the written record. *)
    assert (Hty' : di_type dn' = di_type dn)
      by (destruct Hstab as [H0 | Heq]; [exfalso; exact (Hnz H0) | exact Heq]).
    (* (L3)/(L4)/(L5) at the lowered record.  (L4) falls out of the unlink
       for free, and that asymmetry is the whole reason only the raising
       mover takes a premise: [Hnl] reads [old = new + 1], so the new count
       is BELOW a count the invariant already bounded. *)
    assert (Hlok' : ireg_link_ok dn').
    { split_and!.
      - intros H0. exfalso. exact (Hnz H0).
      - pose proof (ireg_link_ok_short _ Hlok). lia.
      - exact (ireg_ty_ok_stable dn' dn Hstab Hlok). }
    (* THE ROOT CLAUSE FALLS ON BOTH SIDES AT ONCE TOO, and THIS is the mover
       the chartered form ([1 <= di_nlink] alone) could not survive: it would
       need [2 <= di_nlink dn] and have only [1 <= di_nlink dn].  Strictness
       supplies the missing one from the ledger instead of from the walk --
       the root's slack is exactly the entry it does not have in a parent,
       and [dp->nlink--] can only ever spend a subdirectory's [".."].  No
       premise, and nothing for [sys_unlink]'s ["."]/[".."] guard to
       supply. *)
    (* THE CLAIM PIN IS VACUOUS HERE (iclaim-ledger.md §2.4): the caller's
       own [dinode_at] put this open on the MARKED arm, whose clause says
       [cl = None]. *)
    assert (Hclm' : ireg_claim_ok cl fz dn')
      by (rewrite (proj2 Ht2); exact I).
    assert (Hfrz' : ireg_frz_ok fz cn dn')
      by exact (ireg_frz_ok_of_off fz cn dn' Hfz0).
    (* THE RA's OWN STEP (durable-disk 2b-inode-5), the dual of the link
       mover's: the lowered count is one [link_return], paid for by the
       token the caller brought back out of its directory's [ent_toks]. *)
    assert (Htyeq : bv_unsigned (di_type dn') = bv_unsigned (di_type dn))
      by (destruct Hstab as [H0 | Heq];
          [exfalso; exact (Hnz H0) | rewrite Heq; reflexivity]).
    iMod (ireg_lnk_drop γfs (bv_unsigned inum) dn dn' uty
            (ireg_dot_delta (bv_unsigned (di_type dn'))
               (bv_unsigned (di_nlink dn')))
            (ireg_mult_drop dn dn' Hnl Htyeq) Htyeq
            with "Hlnk Htok")
      as "Hlnk".

    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iEval (rewrite -(rec_owned_at_IBLOCK (fs_gamma_L γfs) inodestart inum dn'))
      in "Hrun".
    iEval (rewrite -Hkey) in "Hrun".
    iDestruct ("Hrecback" $! dn' with "Hrun") as "Hrec".
    iMod ("Hclose" with "[Ha Hreg Hrec Hmk Hla Hep Hlnk Hslback Hback Hrf Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hrec Hmk Hla Hep Hlnk Hslback Hrf Hcnt Hfdisj Hfrcp]").
      { intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact Hwfi |].
      iSplitR.
      { iPureIntro. intros i Hi.
        destruct (decide (i = islot inum)) as [->|Hne].
        - rewrite /m' -(ireg_key_split inum) lookup_insert.
          rewrite list_lookup_total_insert; [done | lia].
        - rewrite /m' lookup_insert_ne; last first.
          { rewrite (ireg_key_split inum). intros Hc.
            destruct (ireg_key_inj (ireg_bi inum) (ireg_bi inum)
                        (islot inum) i Hsl Hi Hc) as [_ Hi'].
            exact (Hne (eq_sym Hi')). }
          rewrite list_lookup_total_insert_ne; [| by apply not_eq_sym].
          exact (Hcp0 i Hi). }
      iSplitL "Hrec"; [iExact "Hrec" |].
      iApply ("Hslback" $! dn' with "[Hmk Hla Hep Hlnk Hrf Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iDestruct (ireg_rcol_intro (bv_unsigned inum) cl rl
                   fz cn rcl dn'
                   (ireg_ref_ok_stable rl rcl cn cl dn dn' Hty' Href)
                   with "Hla") as "Hla".
      iApply (ireg_slot_intro γfs γi (bv_unsigned inum) dn' cl rl fz cn Hlok' Hclm' Hfrz' with "Hla Hep Hlnk Hdisj Hcnt Hfdisj Hfrcp").
      iLeft. iSplitR "Hrf"; [iRight; iSplitR; [iPureIntro; split; [exact Hnz | exact (proj2 Ht2)] | iExact "Hmk"] | iExact "Hrf"]. }
    iModIntro. iExact "Hdn".
  Qed.

  (* ...AND ITS THREE INSTANCE WRAPPERS ARE GONE TOO (slice 6e), for
     [ireg_write_link]'s reason: [ireg_write_unlink] / [_d] / [_p] pinned
     one flavour apiece of the mover above and never had a caller.
     [ProofIupdate] applies [ireg_write_unlink_fl] directly. *)

  (* §20.8's ORPHAN COLOUR AND ITS FREE MINT ARE GONE (lane G6).
     [ireg_link_grey] minted one [IcacheRef.igrey] out of nothing, for
     create's [fail:] after a successful [dirlink(ip, "..")] and for
     sys_unlink's orphan re-park: the old ledger demanded a ticket for every
     live record and grey was the only honest colour at an orphaned [".."].
     The type register does not: an orphan's [".."] is TOKENLESS
     ([FsStateInode.ent_tokenless]), so both walks re-park with nothing owed
     and the [g] column -- with the permanent cost §20.18 ruling 2 recorded
     for it -- is deleted. *)

  (* ==================================================================== *)
  (*  §L.  THE LEND'S OPERATIONS (N-4 PHASE B, E1-region)                  *)
  (* ==================================================================== *)

  (*  Each one is [DirViewLend]'s column move with an [↑iregN] open around
      it, and nothing else.  The [ireg_inv] argument is a PERSISTENT handle
      that every calling context -- every byte-write mover, every escrow
      arm, the pinned walk -- already holds as a premise, so not one spec's
      text moves.  NO operation takes an inum-range premise and none
      relates the region's [nib] to [icfg_nib]: the addressing bound is the
      pure clause the lend's own tokens carry ([DirViewLend.dvl_dom]) and
      the column family is indexed at [icfg_nib] to match (see
      [ireg_lends]).  The mint, whose caller holds no lend token yet, is the
      one exception and states [dvl_dom] outright.                         *)

  (* the shared plumbing: open the region, hand the caller this inum's
     column, take it back, close.  Stated as a bupd-transformer so the three
     operations below are one line each. *)
  Lemma ireg_lcols_use (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z) (Q : iProp Σ) :
    ↑iregN ⊆ E ->
    dvl_dom z ->
    ireg_inv γi γfs inodestart nib -∗
    (ireg_lcols z ==∗ ireg_lcols z ∗ Q) ={E}=∗ Q.
  Proof.
    iIntros (HE Hz) "#Hinv Hmove".
    iDestruct "Hinv" as "[#Hiinv [#Hrb #Hftopi]]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    iDestruct "Hreg" as (mr) "(%Hcov & Hauth & Hlends)".
    iDestruct (ireg_lends_acc z Hz with "Hlends") as "[Hcol Hback]".
    iMod ("Hmove" with "Hcol") as "[Hcol HQ]".
    iDestruct ("Hback" with "Hcol") as "Hlends".
    iMod ("Hclose" with "[Ha Hblks Hauth Hlends]") as "_".
    { iNext. iExists m. iFrame "Ha Hblks".
      iExists mr. iSplitR; [done |]. iFrame. }
    iModIntro. iExact "HQ".
  Qed.

  (* ...and the two single-column forms the operations below actually use.
     Each frames the OTHER ghost's column straight through, which is the
     whole content of "the two lends are independent". *)
  Lemma ireg_lcol_use (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z) (Q : iProp Σ) :
    ↑iregN ⊆ E ->
    dvl_dom z ->
    ireg_inv γi γfs inodestart nib -∗
    (dv_lcol z ==∗ dv_lcol z ∗ Q) ={E}=∗ Q.
  Proof.
    iIntros (HE Hz) "#Hinv Hmove".
    iApply (ireg_lcols_use E γi γfs inodestart nib z with "Hinv");
      [exact HE | exact Hz |].
    iIntros "[Hd Hf]". iMod ("Hmove" with "Hd") as "[Hd $]".
    iModIntro. rewrite /ireg_lcols. iFrame.
  Qed.

  Lemma ireg_fcol_use (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z) (Q : iProp Σ) :
    ↑iregN ⊆ E ->
    dvl_dom z ->
    ireg_inv γi γfs inodestart nib -∗
    (fv_lcol z ==∗ fv_lcol z ∗ Q) ={E}=∗ Q.
  Proof.
    iIntros (HE Hz) "#Hinv Hmove".
    iApply (ireg_lcols_use E γi γfs inodestart nib z with "Hinv");
      [exact HE | exact Hz |].
    iIntros "[Hd Hf]". iMod ("Hmove" with "Hf") as "[Hf $]".
    iModIntro. rewrite /ireg_lcols. iFrame.
  Qed.

  (* THE WRITER'S TOTAL MOVE: [DirViewG.dv_set] at the ride.  On the whole
     arm it IS [dv_set] and the region is never opened; on the ¾ arm it
     gathers the escrowed ¼, sets, and cancels on the way out.  Total, with
     no premise beyond the ride and the ambient region handle -- which is
     what let the sixteen mover sites swap [dv_set] for it one line at a
     time. *)
  Lemma dv_set_rt (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z) (e e' : gmap fname Z) :
    ↑iregN ⊆ E ->
    ireg_inv γi γfs inodestart nib -∗ dv_ride z e ={E}=∗ dv_ride z e'.
  Proof.
    iIntros (HE) "#Hinv H". rewrite {1}/dv_ride.
    iDestruct "H" as "[Hw|[H34 Hm]]".
    - iMod (dv_set with "Hw") as "Hw". iModIntro. by iApply dv_ride_of_hold.
    - iDestruct "Hm" as "[%Hdom Hm']".
      iAssert (dv_lentm z e)%I with "[Hm']" as "Hm".
      { rewrite /dv_lentm. iSplitR; [by iPureIntro |]. iExact "Hm'". }
      iApply (ireg_lcol_use E γi γfs inodestart nib z with "Hinv");
        [exact HE | exact Hdom |].
      iIntros "Hcol".
      iMod (dv_col_set z e e' with "H34 Hm Hcol") as "[$ Hw]".
      iModIntro. by iApply dv_ride_of_hold.
  Qed.

  (* THE CLIENT'S MOVE, fired inside an [SpecNameiTr.nx_hop] fupd: the hop
     lends the directory's contents at whatever fraction its custody
     carries, and agreement against the ESCROWED ¼ is what forces the lent
     value to be the pinned one.  On the cancelled arm the client takes the
     persistent receipt instead. *)
  Lemma dv_pin_redeem (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z) (e : gmap fname Z)
      (dqv : dfrac) (ents : gmap fname Z) :
    ↑iregN ⊆ E ->
    ireg_inv γi γfs inodestart nib -∗
    dv_pin z e -∗ dv_half z dqv ents ={E}=∗
      dv_half z dqv ents ∗
      ((⌜ents = e⌝ ∗ dv_pin_spent z e) ∨ dv_cancelled z e).
  Proof.
    iIntros (HE) "#Hinv Hpin Hdv".
    iDestruct "Hpin" as "[%Hdom Hpin']".
    iAssert (dv_pin z e)%I with "[Hpin']" as "Hpin".
    { rewrite /dv_pin. iSplitR; [by iPureIntro |]. iExact "Hpin'". }
    iApply (ireg_lcol_use E γi γfs inodestart nib z with "Hinv");
      [exact HE | exact Hdom |].
    iIntros "Hcol".
    iMod (dv_col_redeem z e ents dqv with "Hpin Hdv Hcol") as "[$ $]".
    by iModIntro.
  Qed.

  (* ==================================================================== *)
  (*  §LF.  THE fview LEND'S OPERATIONS (N-5.2A, §13 D-52c)                *)
  (* ==================================================================== *)

  (*  §L's, at the file-contents column.  Same signatures, same [ireg_inv]
      argument, same absence of an inum-range premise (the bound is
      [DirViewLend.dvl_dom], carried by the fview tokens too), same totality
      of the writer's move.  The fview lend's consumer is the kexec walk
      (N-5.2B).                                                             *)

  Lemma fv_set_rt (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z) (b b' : list (bv 8)) :
    ↑iregN ⊆ E ->
    ireg_inv γi γfs inodestart nib -∗ fv_ride z b ={E}=∗ fv_ride z b'.
  Proof.
    iIntros (HE) "#Hinv H". rewrite {1}/fv_ride.
    iDestruct "H" as "[Hw|[H34 Hm]]".
    - iMod (fv_set with "Hw") as "Hw". iModIntro. by iApply fv_ride_of_hold.
    - iDestruct "Hm" as "[%Hdom Hm']".
      iAssert (fv_lentm z b)%I with "[Hm']" as "Hm".
      { rewrite /fv_lentm. iSplitR; [by iPureIntro |]. iExact "Hm'". }
      iApply (ireg_fcol_use E γi γfs inodestart nib z with "Hinv");
        [exact HE | exact Hdom |].
      iIntros "Hcol".
      iMod (fv_col_set z b b' with "H34 Hm Hcol") as "[$ Hw]".
      iModIntro. by iApply fv_ride_of_hold.
  Qed.

  Lemma fv_pin_redeem (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z) (b : list (bv 8))
      (dqv : dfrac) (bs : list (bv 8)) :
    ↑iregN ⊆ E ->
    ireg_inv γi γfs inodestart nib -∗
    fv_pin z b -∗ fv_half z dqv bs ={E}=∗
      fv_half z dqv bs ∗
      ((⌜bs = b⌝ ∗ fv_pin_spent z b) ∨ fv_cancelled z b).
  Proof.
    iIntros (HE) "#Hinv Hpin Hfv".
    iDestruct "Hpin" as "[%Hdom Hpin']".
    iAssert (fv_pin z b)%I with "[Hpin']" as "Hpin".
    { rewrite /fv_pin. iSplitR; [by iPureIntro |]. iExact "Hpin'". }
    iApply (ireg_fcol_use E γi γfs inodestart nib z with "Hinv");
      [exact HE | exact Hdom |].
    iIntros "Hcol".
    iMod (fv_col_redeem z b bs dqv with "Hpin Hfv Hcol") as "[$ $]".
    by iModIntro.
  Qed.

  (* ==================================================================== *)
  (*  §LW.  THE COMBINED MOVERS (N-5.2A, §13 D-52b)                        *)
  (* ==================================================================== *)

  (*  EVERY BYTE-WRITE RE-PACK MOVES BOTH GHOSTS.  A directory write changes
      the garbage [fv_of] reads off the same bytes, and a file write changes
      the garbage [dv_of] reads off them; neither ghost is type-guarded, so
      the honest statement at every mover site is "both, at the new record's
      own readings".  These two wrappers are what keep such a site ONE line
      after the sweep -- the dv-only forms stay for Phase B's byte-stability
      and are what these are built out of.                                 *)

  Lemma dvw_set_rt (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z)
      (e e' : gmap fname Z) (b b' : list (bv 8)) :
    ↑iregN ⊆ E ->
    ireg_inv γi γfs inodestart nib -∗
    dv_ride z e -∗ fv_ride z b ={E}=∗ dv_ride z e' ∗ fv_ride z b'.
  Proof.
    iIntros (HE) "#Hinv Hd Hf".
    iMod (dv_set_rt E γi γfs inodestart nib z e e' HE with "Hinv Hd") as "$".
    by iMod (fv_set_rt E γi γfs inodestart nib z b b' HE with "Hinv Hf") as "$".
  Qed.

  (* ...and the size-preserving form, for the re-packs whose record move
     leaves [di_size] alone ([DirViewLend.dv_ride_size] and its twin, taken
     together): there BOTH readings are unchanged and no fupd is needed at
     all -- the resource is simply re-typed. *)
  Lemma dvw_ride_size (z : Z) (dn1 dn2 : dinode) (data : nat -> list (bv 8)) :
    di_size dn1 = di_size dn2 ->
    dv_ride z (dv_of dn1 data) -∗ fv_ride z (fv_of dn1 data) -∗
    dv_ride z (dv_of dn2 data) ∗ fv_ride z (fv_of dn2 data).
  Proof.
    intros Hs. iIntros "Hd Hf".
    iSplitL "Hd"; [iApply (dv_ride_size z dn1 dn2 data Hs with "Hd")
                  | iApply (fv_ride_size z dn1 dn2 data Hs with "Hf")].
  Qed.

End InodeRegion.
