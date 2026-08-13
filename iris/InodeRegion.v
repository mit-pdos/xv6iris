(* InodeRegion.v -- THE INODE REGION: the dinode blocks' owner, and the
   per-inum fragment that replaces the coarse [fsblock] premise in every
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
   exclusive resource -- [disk_block] in full, both [fs_L] halves, the
   machinery dirty half -- so by conservation the arm has nothing to hold,
   and a checkout could never prove the arm is parked.

   So the region is ONE-ARMED, and the only moment the client half leaves
   it is log_write's own ghost step (ProofLogWrite.v's [fsblock_update], a
   single [iMod] between two instruction dispatches, at mask ⊤).
   [ireg_write_au] below is the atomic update iupdate hands to the
   generalized SpecLogWrite premise: it opens the region THERE, lets
   [fsblock_update] run against the withdrawn half, and re-parks the block
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

   Until §16 a free inum's [dinode_at] lived in [IcacheEscrow.ipool_shape]'s
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
     [ireg_free_au]   iput's [ip->type = 0; iupdate] -- absorb the fragment,
                      pay out the marker.
     [ireg_withdraw]  ilock's FIRST fill of a claimed inum -- deposit the
                      marker, take the fragment.  The marker is what makes
                      that case analysis exhaustive.

   ---- AND TWO MORE, FOR THE LINK LEDGER (§20.6, fs-sysfile S5f) ---------

     [ireg_write_link]    mkdir's [".."] and sys_link's [ip->nlink++]:
                          mint one [ilink] in the SAME ghost step as the
                          count that pays for it, so the ledger's (L1) cap
                          grows on both sides at once.
     [ireg_write_unlink]  sys_unlink's [ip->nlink--], the ONLY nlink-
                          LOWERING region write in the kernel: it CONSUMES
                          one [ilink] as it lowers.  That is precisely why
                          the ordinary flush may demand [di_nlink_stable]
                          -- the one writer that would violate it does not
                          go through the ordinary flush at all.

   THE LEDGER'S CLAUSES ARE (L1) AND (L3), stated in [ireg_link_ok] below
   and re-established by all six arm moves.  Their payoff is two lines:
   [ireg_link_ok_alloc] ("an outstanding fragment means an ALLOCATED
   record") and [ireg_free_au]'s own [w = 0] ("at the instant an inode is
   freed nothing names it").  [ireg_link_alloc] at the end of the file is
   the accessor that cashes the first for a caller holding the inum's
   dinode block.  What is still NOT stated is §20.2's (L2) and the
   [c = None] half of (L3): nothing mints an [iclaim] yet, and the free
   cannot re-establish [c = None] without consuming one -- see
   [ireg_free_au]'s note and design §20.15.

   ---- WHAT IS DELIBERATELY NOT HERE ------------------------------------

   The boot-time allocation (building the initial map from the mkfs
   image's dinode blocks and minting every [dinode_at]) is fsinit wiring
   and lives in [IcacheBoot.v], not here.  The icache pool that HOLDS the
   fragments of uncached inodes is IcacheInv's (design §10.4).            *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl.
From iris.base_logic.lib Require Import invariants ghost_map mono_nat.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvPtsto.
Require Import RiscvModelBytes.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import BlockWords.
Require Import DinodeEnc.
(* THE LINK LEDGER's algebra and its ambient gname (design §20.2).
   EXPORTED, not merely imported: [ireg_slot] parks [IcacheRef.link_auth],
   so [icacheG] and [icfg] are now part of every [ireg_inv]'s type, and a
   file that names [ireg_inv] through a bare [Require Import InodeRegion]
   would otherwise IMPLICITLY GENERALIZE a fresh [icacheG] variable
   (durable-notes' first typeclass-sweep trap).  The chain is supposed to
   carry the class; this is where it starts. *)
Require Export IcacheRef.
(* [logged_at] / [log_epoch_lb]: the zero-receipt parked in [ireg_slot]
   (fs-log.md §G.17).  This is what puts [logG] in the section's context,
   and hence in the context of the four files that STATE something over
   [ireg_inv] -- the enumerated sweep. *)
Require Import LogInv.
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
   [dip->type = type] leaves on disk: a nonzero type, a zero size and
   thirteen zero address words.  ialloc writes NOTHING else -- in
   particular [nlink] stays 0 until the caller's own iupdate -- so this is
   deliberately the WEAKEST record shape a claim can promise, and it is
   still enough for ilock's fill to build [InodeLock.inode_ok] out of
   nothing at all ([InodeInv.bm_empty] collapses every block resource,
   [bm_covers_nonpos] and [DirView.dir_ok_size_zero] ride on the zero
   size).

   Stated with a bare [replicate 13] rather than [InodeInv.bm_cells
   bm_empty] so that this file keeps its short Require list; the bridge is
   one [vm_compute] at the two sites that need it. *)
Definition fresh_shape (d : dinode) : Prop :=
  bv_unsigned (di_type d) <> 0
  /\ bv_unsigned (di_size d) = 0
  /\ di_addrs d = replicate 13 (bv_0 32).

Lemma fresh_shape_wf (d : dinode) : fresh_shape d -> dinode_wf d.
Proof.
  intros (_ & _ & Ha). rewrite /dinode_wf Ha length_replicate. reflexivity.
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

     the FIRST conjunct -- [nlink] does not FALL.  Without it any holder
     of [dinode_at] could lower [nlink] under an outstanding [ilink] and
     (L1) would break; with it, "a fragment outstanding implies
     [nlink >= 1]" is a theorem of the region rather than a survey of this
     tree's callers.  sys_unlink's decrement is the ONE writer that lowers
     an [nlink], and it does not go through the ordinary flush at all --
     it goes through [ireg_write_unlink], which pays for the drop by
     CONSUMING a fragment.

     the SECOND conjunct -- a flush that CLEARS the type leaves [nlink]
     at zero.  That is iput's free path, whose C-level guard is literally
     [ip->nlink == 0], and it is what lets [ireg_free_au] derive [w = 0]
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
  bv_unsigned (di_nlink dn) <= bv_unsigned (di_nlink dn')
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
  intros Heq Hnz. rewrite /di_nlink_stable Heq.
  split; [lia | intros H0; exfalso; exact (Hnz H0)].
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
  intros Heq Hz. rewrite /di_nlink_stable Heq Hz.
  split; [lia | intros _; reflexivity].
Qed.

(* (L1)'s two arithmetic steps, over plain [Z] and outside every section --
   durable-notes' rule, since the goals below have a [bv 32] in context and
   [lia]'s zify hook then answers "Cannot find witness". *)
Lemma ireg_wle_mono (a b : Z) (w : nat) :
  0 <= a -> (w <= Z.to_nat a)%nat -> a <= b -> (w <= Z.to_nat b)%nat.
Proof. lia. Qed.

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

(* THE MARKER'S KEY.  The claim box needs a per-inum EXCLUSIVE token whose
   two homes are the region invariant and a pool/entry marker; a second
   ghost name for it would have to appear in [ireg_inv] AND in
   [IcacheEscrow.ipool_shape], i.e. in [ic_escrow]'s arity, i.e. in every
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

Class iregG (Σ : gFunctors) := IregG {
  ireg_inG :: ghost_mapG Σ Z dinode;
}.
Definition iregΣ : gFunctors := #[ghost_mapΣ Z dinode].
Global Instance subG_iregΣ {Σ} : subG iregΣ Σ -> iregG Σ.
Proof. solve_inG. Qed.

Section InodeRegion.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ}.
  Context `{ICFG : icfg}.

  (* THE per-inum resource: this inum's on-disk record is [dn].  EXCLUSIVE
     (a full-fraction ghost_map element), keyed by the inum's value; the
     block address falls out of [IBLOCK] and never needs a second ghost.
     This is what replaces [fsblock γfs (IBLOCK inum inodestart)
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
  Definition ireg_in (d : dinode) : Prop :=
    bv_unsigned (di_type d) = 0 \/ fresh_shape d.

  (* THE LINK LEDGER's PER-INUM CLAUSES (design §20.2's (L1)/(L3)).

     (L1) [w <= di_nlink d] -- at most one live directory record per unit
     of [nlink].  Its contrapositive is the whole point: an outstanding
     [ilink z] forces [di_nlink >= 1] at the record the REGION holds, and
     (L3) then forces a nonzero TYPE.  "A reference implies an allocated
     inode" stops being a fact about this tree's callers.

     (L3) [di_type d = 0 -> di_nlink d = 0] -- a free record's link count
     is zero, which is what makes (L1) collapse to [w = 0] there:
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
     [ireg_free_au].  Both clauses then land with no caller obligation
     anywhere and no signature move: the six arm moves below each
     re-establish [ireg_link_ok] from what they already have.

     WHAT IS STILL NOT HERE: §20.2's (L2) [c <> None -> fresh_shape d] and
     the [c = None] half of (L3).  Neither is blocked by this knot; both
     wait on the CLAIM being minted at all, which is §20.5/§20.7's (M1)
     work -- the free cannot re-establish [c = None] without CONSUMING an
     [iclaim] it does not hold, and until something mints one there is
     nothing for a clause to say.  The [c] component rides unconstrained
     through every mover below, exactly as it did before. *)
  Definition ireg_link_ok (d : dinode) (w : nat) : Prop :=
    (w <= Z.to_nat (bv_unsigned (di_nlink d)))%nat                    (* L1 *)
    /\ (bv_unsigned (di_type d) = 0 -> bv_unsigned (di_nlink d) = 0). (* L3 *)

  (* (L1)'s contrapositive, and the reason the ledger exists: a record with
     an outstanding fragment is ALLOCATED.  Pure, so that every arm move
     and every consumer reads it off the clause the same way. *)
  Lemma ireg_link_ok_alloc (d : dinode) (w : nat) :
    ireg_link_ok d w -> (1 <= w)%nat -> bv_unsigned (di_type d) <> 0.
  Proof.
    intros [Hle Hz] Hw H0. specialize (Hz H0).
    rewrite Hz in Hle. cbn in Hle. lia.
  Qed.

  (* ...and (L3)+(L1) at a FREE record: nothing names it. *)
  Lemma ireg_link_ok_free (d : dinode) (w : nat) :
    ireg_link_ok d w -> bv_unsigned (di_type d) = 0 -> w = 0%nat.
  Proof.
    intros [Hle Hz] H0. specialize (Hz H0). rewrite Hz in Hle. cbn in Hle. lia.
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
     first conjunct says nlink never FALLS across an ordinary flush, so a
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

  Definition ireg_slot (γi : gname) (z : Z) (d : dinode) : iProp Σ :=
    ((∃ (w g r : nat) (c : option (excl unit)),
        link_auth z w g c r ∗ ⌜ireg_link_ok d w⌝)
     ∗ ireg_ep z d
     ∗ ((⌜ireg_in d⌝ ∗ z ↪[γi] d)
        ∨ (⌜bv_unsigned (di_type d) <> 0⌝ ∗ imark γi z)))%I.

  Global Instance ireg_slot_timeless γi z d : Timeless (ireg_slot γi z d).
  Proof. rewrite /ireg_slot. apply _. Qed.

  (* the ledger's authority at one slot, held apart from the arm.  Both the
     ordinary flush and the free re-park the arm unchanged in SHAPE and
     move only the record, so every arm move below is stated by giving the
     new record and the new authority separately. *)
  Lemma ireg_slot_intro γi z d w g c r :
    ireg_link_ok d w ->
    link_auth z w g c r -∗
    ireg_ep z d -∗
    ((⌜ireg_in d⌝ ∗ z ↪[γi] d)
     ∨ (⌜bv_unsigned (di_type d) <> 0⌝ ∗ imark γi z)) -∗
    ireg_slot γi z d.
  Proof.
    intros Hok. iIntros "Hla Hep Harm". rewrite /ireg_slot. iFrame "Hep Harm".
    iExists w, g, r, c. iSplitL "Hla"; [iExact "Hla" |].
    iPureIntro. exact Hok.
  Qed.

  Definition ireg_blk (γi : gname) (γfs : fs_names) (inodestart : Z)
      (m : gmap Z dinode) (bi : nat) : iProp Σ :=
    (∃ ds : list dinode,
       ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗
       fsblock γfs (inodestart + Z.of_nat bi) (diblk_bytes ds) ∗
       [∗ list] i ∈ seq 0 16,
         ireg_slot γi (16 * Z.of_nat bi + Z.of_nat i)%Z (ds !!! i))%I.

  Definition ireg_body (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) : iProp Σ :=
    (∃ m : gmap Z dinode,
       ghost_map_auth γi 1 m ∗
       [∗ list] bi ∈ seq 0 nib, ireg_blk γi γfs inodestart m bi)%I.

  Definition iregN : namespace := nroot .@ "ireg".

  Definition ireg_inv (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) : iProp Σ :=
    inv iregN (ireg_body γi γfs inodestart nib).

  Global Instance ireg_inv_persistent γi γfs inodestart nib :
    Persistent (ireg_inv γi γfs inodestart nib).
  Proof. apply _. Qed.

  Global Instance ireg_blk_timeless γi γfs inodestart m bi :
    Timeless (ireg_blk γi γfs inodestart m bi).
  Proof. rewrite /ireg_blk /fsblock. apply _. Qed.

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
     changed only at [bi]'s keys -- IcacheInv.islots_acc_upd's shape *)
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
  Lemma ireg_slots_acc_upd (γi : gname) (bi : nat) (ds : list dinode)
      (i : nat) :
    (i < 16)%nat -> length ds = 16%nat ->
    ([∗ list] j ∈ seq 0 16,
       ireg_slot γi (16 * Z.of_nat bi + Z.of_nat j)%Z (ds !!! j)) -∗
      ireg_slot γi (16 * Z.of_nat bi + Z.of_nat i)%Z (ds !!! i) ∗
      (∀ d' : dinode,
         ireg_slot γi (16 * Z.of_nat bi + Z.of_nat i)%Z d' -∗
         [∗ list] j ∈ seq 0 16,
           ireg_slot γi (16 * Z.of_nat bi + Z.of_nat j)%Z
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
    bv_unsigned inum < 16 * Z.of_nat nib ->
    b = IBLOCK inum inodestart ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    (b ↪[fs_L γfs]{#(1/2)} bsl) ={E}=∗
    ⌜exists ds : list dinode,
       diblk_wf ds /\ bsl = diblk_bytes ds /\ ds !!! islot inum = dn⌝ ∗
    dinode_at γi inum dn ∗ (b ↪[fs_L γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE Hin Hb) "#Hinv Hdn Hhalf".
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & Hsl)".
    rewrite /fsblock -(ireg_bi_iblock inum inodestart) -Hb.
    iDestruct (ghost_map_elem_agree with "Hhalf Hfsb") as %Hbytes.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hslot : ds !!! islot inum = dn).
    { pose proof (islot_lt inum) as Hsl.
      specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    iMod ("Hclose" with "[Ha Hfsb Hsl Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb Hsl]"); [done |].
      iExists ds. rewrite /fsblock (ireg_bi_iblock inum inodestart) in Hb.
      rewrite Hb. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" | iExact "Hsl"]. }
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
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
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
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) [Hep Harm]]".
    iEval (rewrite Hdeq) in "Hep".
    iMod (ireg_ep_mint (bv_unsigned inum) dn icfg_log e0 eq_refl Hnz
            with "Hep Hlb0") as "[Hep #Hobs]".
    iEval (rewrite -Hdeq) in "Hep".
    iMod ("Hclose" with "[Ha Hfsb Hla Hep Harm Hslback Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb Hla Hep Harm Hslback]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hla Hep Harm]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl gl cl rl Hlok with "Hla Hep"). iExact "Harm". }
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
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
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
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) [Hep Harm]]".
    iEval (rewrite Hdeq) in "Hep".
    iDestruct (ireg_ep_use (bv_unsigned inum) dn icfg_log e0 eq_refl Hz He0
                 with "Hep Hobs") as "[Hep #Hwit]".
    iEval (rewrite -Hdeq) in "Hep".
    iMod ("Hclose" with "[Ha Hfsb Hla Hep Harm Hslback Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb Hla Hep Harm Hslback]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hla Hep Harm]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl gl cl rl Hlok with "Hla Hep"). iExact "Harm". }
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
    (bi < nib)%nat ->
    ireg_inv γi γfs inodestart nib -∗
    ((inodestart + Z.of_nat bi) ↪[fs_L γfs]{#(1/2)} bsl) ={E}=∗
    ⌜exists ds : list dinode, diblk_wf ds /\ bsl = diblk_bytes ds⌝ ∗
    ((inodestart + Z.of_nat bi) ↪[fs_L γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE Hbi) "#Hinv Hhalf".
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib bi Hbi with "Hblks")
      as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & Hsl)".
    iDestruct (ghost_map_elem_agree with "Hhalf Hfsb") as %Hbytes.
    iMod ("Hclose" with "[Ha Hfsb Hsl Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb Hsl]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" | iExact "Hsl"]. }
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

  (* Exactly the shape SpecLogWrite's generalized fsblock premise takes:
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
     out.  That is [ireg_free_au] below; this lemma keeps the arm where it
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
     actually leaves through [ireg_free_au], so here the left disjunct is
     dead against [Hnz] and only records the shape) or leaves it exactly
     where it was.  The premise only TRAVELS: the proof body does not move,
     and every caller in the tree discharges it today ([ProofWritei] and
     [ProofItrunc] from their own [wi_dinode]/size-only updates,
     [ProofCreate] from [ProofCreateParts.cr_setf], [ProofIput]'s free path
     at the left disjunct). *)
  Lemma ireg_write_au (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    di_nlink_stable dn' dn ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock γfs (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock γfs (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ dinode_at γi inum dn').
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hnl) "#Hinv Hdn".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds0) "(>%Hwf0 & >%Hcp0 & >Hfsb & >Hsls)".
    iModIntro.
    rewrite (ireg_bi_iblock inum inodestart).
    iExists (diblk_bytes ds0).
    iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    (* the parked list IS the caller's: bytes equal, both wf, encode inj *)
    assert (Hds0 : ds0 = ds) by exact (diblk_bytes_inj ds0 ds Hwf0 Hwf Hbytes).
    subst ds0.
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) [Hep Harm]]".
    (* THE ARM IS THE OUT ONE: the region cannot also hold this inum's
       fragment, because the caller does ([dinode_at_excl]). *)
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    (* retag the caller's fragment against the authority *)
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    (* the region's record at this slot IS the caller's, by the coupling --
       which is what lets (L1) be carried from [dn] to [dn'] *)
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    rewrite Hdeq in Hlok.
    (* (L1) RIDES ON [di_nlink_stable]'s first conjunct: [nlink] does not
       fall across an ordinary flush, so the cap the ledger already had is
       still a cap.  (L3) is vacuous -- an ordinary flush writes a nonzero
       type, which is [Hnz], and the clearing flush leaves through
       [ireg_free_au] instead. *)
    assert (Hlok' : ireg_link_ok dn' wl).
    { split.
      - exact (ireg_wle_mono (bv_unsigned (di_nlink dn))
                 (bv_unsigned (di_nlink dn')) wl
                 (di_nlink_nonneg dn) (proj1 Hlok) (proj1 Hnl)).
      - intros H0. exfalso. exact (Hnz H0). }
    (* THE RECEIPT TRAVELS FOR FREE (fs-log.md §G.17): [Hnl]'s first
       conjunct says nlink never FALLS across an ordinary flush, so a zero
       at [dn'] was already a zero at [dn] and the old receipt IS the new
       one, at the same [v]. *)
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { rewrite Hdeq. intros H0. pose proof (proj1 Hnl).
      pose proof (di_nlink_nonneg dn). lia. }
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    (* re-park the block at the flushed bytes, re-coupled at m' *)
    iMod ("Hclose" with "[Ha Hfsb' Hmk Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hmk Hla Hep Hslback]").
      { (* other blocks' keys never collide with this inum's *)
        intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn') |].
      iSplitR.
      { iPureIntro. intros i Hi.
        destruct Hwf as [Hlen _].
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
      iSplitL "Hfsb'"; [iExact "Hfsb'" |].
      iApply ("Hslback" $! dn' with "[Hmk Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl gl cl rl Hlok'
                with "Hla Hep").
      iRight. iSplitR; [iPureIntro; exact Hnz | iExact "Hmk"]. }
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
      (ds : list dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    bv_unsigned (di_type (ds !!! islot inum)) = 0 ->
    fresh_shape dn' ->
    ireg_inv γi γfs inodestart nib -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock γfs (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock γfs (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ True).
  Proof.
    iIntros (HE Hin Hwf Ht0 Hfr) "#Hinv".
    pose proof (islot_lt inum) as Hsl.
    pose proof (fresh_shape_wf dn' Hfr) as Hdn'.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds0) "(>%Hwf0 & >%Hcp0 & >Hfsb & >Hsls)".
    iModIntro.
    rewrite (ireg_bi_iblock inum inodestart).
    iExists (diblk_bytes ds0).
    iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    assert (Hds0 : ds0 = ds) by exact (diblk_bytes_inj ds0 ds Hwf0 Hwf Hbytes).
    subst ds0.
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) [Hep Harm]]".
    (* the OUT arm claims a nonzero type; the caller's buffer says zero *)
    iDestruct "Harm" as "[[%Hin1 Hfrg] | [%Ht2 Hmk]]"; last first.
    { iExFalso. iPureIntro. exact (Ht2 Ht0). }
    (* (L3) AT THE CLAIMED SLOT: the record the caller's buffer showed
       type-0 has [nlink = 0], so (L1) collapses to [w = 0] -- i.e. no live
       directory record names the inum ialloc is about to claim -- and the
       fresh record's own (L1) is then free whatever [nlink] it carries.
       THIS is the step §20.13 called the knot: it needs (L3) as an
       invariant, and (L3) is what iput's free had to establish. *)
    assert (Hw0 : wl = 0%nat)
      by exact (ireg_link_ok_free (ds !!! islot inum) wl Hlok Ht0).
    assert (Hlok' : ireg_link_ok dn' wl).
    { subst wl. split; [lia | intros H0; exfalso; exact (proj1 Hfr H0)]. }
    (* the claimed slot's old record is type-0, so (L3) already gives it
       [nlink = 0] and the receipt carries unconditionally *)
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { intros _. exact (proj2 Hlok Ht0). }
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hfrg") as %Hm.
    iMod (ghost_map_update dn' with "Ha Hfrg") as "[Ha Hfrg]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hfsb' Hfrg Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hfrg Hla Hep Hslback]").
      { intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn') |].
      iSplitR.
      { iPureIntro. intros i Hi.
        destruct Hwf as [Hlen _].
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
      iSplitL "Hfsb'"; [iExact "Hfsb'" |].
      iApply ("Hslback" $! dn' with "[Hfrg Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl gl cl rl Hlok'
                with "Hla Hep").
      iLeft. iSplitR; [iPureIntro; right; exact Hfr | iExact "Hfrg"]. }
    iModIntro. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  iput's FREE (§16.3's dual)                                          *)
  (* ------------------------------------------------------------------ *)

  (* [ip->type = 0; iupdate(ip)] -- the one place an inode goes back to the
     free pool.  The caller's fragment is ABSORBED into the invariant and
     what comes out is the MARKER, which is exactly what iput's last close
     re-parks (and what [IcacheEscrow.ipool_shape]'s free arm now is).

     THE NLINK PREMISE, AND WHAT IT PROVES (design §20.6's iput row -- the
     user's premise (3), proved).  [di_nlink_stable dn' dn]'s SECOND
     conjunct fires here, because the flushed record's type IS zero: so
     [di_nlink dn' = 0], and the FIRST conjunct then pins [di_nlink dn = 0]
     too.  (L1) at the old record therefore collapses to [w = 0]: **at the
     instant an inode is freed, no live directory record names it, and no
     [ilink] fragment for it exists anywhere in the system.**  Proved
     inside the region, with no caller obligation beyond the one iput's own
     C-level [ip->nlink == 0] test already supplies (§20.9(c)).

     WHAT THIS LEMMA DOES *NOT* DO, and why (fs-sysfile S5f/S5g).  §20.5 wants
     the free to re-establish "[c = None] at a type-0 record", which is the
     clause that would make [ireg_claim_au]'s [iclaim] payout mintable.  It
     cannot: setting an exclusive claim slot back to [None] is not a
     frame-preserving update while the claimant's fragment is outstanding,
     so the free would have to CONSUME [iclaim inum] -- and iput holds no
     such token.  §20.7's own text records the same fact from the other
     end ("[ireg_free_au]'s new [c = None] premise has no discharge in
     [ProofIput] today") and prices (M1) as the carrier.  So the claim
     component exists in the algebra and the ledger carries it, but no
     clause constrains it and nothing mints it yet.

     AND (M1) IS NOT ONE CLAUSE ANYWHERE (fs-sysfile S5g, design §20.15).
     It needs [r <= 1] -- the ABSENCE of other references -- which no
     [nat]-counter authority yields from the presence of one fragment; and
     iput's free runs AFTER its [release] at +0x5c, so any count fact would
     have to cross the lock.  §20.2's "the whole §14 machine is unnecessary
     here" is true of the [w] half, which the free reads off the AUTHORITY
     above, and false of the [r] half.  Stage E is unpriced again. *)
  Lemma ireg_free_au (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') = 0 ->
    di_nlink_stable dn' dn ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock γfs (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock γfs (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ imark γi (bv_unsigned inum)).
  Proof.
    iIntros (HE Hin Hwf Hdn' Hz Hnl) "#Hinv Hdn".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds0) "(>%Hwf0 & >%Hcp0 & >Hfsb & >Hsls)".
    iModIntro.
    rewrite (ireg_bi_iblock inum inodestart).
    iExists (diblk_bytes ds0).
    iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    assert (Hds0 : ds0 = ds) by exact (diblk_bytes_inj ds0 ds Hwf0 Hwf Hbytes).
    subst ds0.
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) [Hep Harm]]".
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    rewrite Hdeq in Hlok.
    (* THE FREE IS WHERE THE LEDGER CERTIFIES "UNNAMED" (design §20.6's iput
       row; the user's premise (3), proved).  [di_nlink_stable]'s SECOND
       conjunct fires here because the flushed record's type IS zero -- and
       it is the one iput carries across its sleeplock window now that
       [ic_open_held] is record-parametric (§20.14's (R1)).  It gives
       [di_nlink dn' = 0]; the first conjunct then pins [di_nlink dn = 0]
       too; and (L1) at the OLD record collapses to [w = 0]:

         at the instant an inode is freed, no live directory record names
         it, and no [ilink] fragment for it exists anywhere in the system.

       Proved inside the region, with no caller obligation beyond iput's own
       C-level [ip->nlink == 0] test (§20.9(c)). *)
    assert (Hnl0' : bv_unsigned (di_nlink dn') = 0) by exact (proj2 Hnl Hz).
    assert (Hnl0 : bv_unsigned (di_nlink dn) = 0).
    { pose proof (proj1 Hnl) as H1. pose proof (di_nlink_nonneg dn) as H2. lia. }
    assert (Hw0 : wl = 0%nat)
      by exact (ireg_wle_zero (bv_unsigned (di_nlink dn)) wl (proj1 Hlok) Hnl0).
    assert (Hlok' : ireg_link_ok dn' wl).
    { subst wl. split; [lia | intros _; exact Hnl0']. }
    (* the free writes a zero over a zero: [Hnl0] above IS the receipt's
       antecedent already discharged at the old record (fs-log.md §G.17) *)
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { intros _. rewrite Hdeq. exact Hnl0. }
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hfsb' Hdn Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hdn Hla Hep Hslback]").
      { intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn') |].
      iSplitR.
      { iPureIntro. intros i Hi.
        destruct Hwf as [Hlen _].
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
      iSplitL "Hfsb'"; [iExact "Hfsb'" |].
      iApply ("Hslback" $! dn' with "[Hdn Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl gl cl rl Hlok'
                with "Hla Hep").
      iLeft. iSplitR; [iPureIntro; left; exact Hz | iExact "Hdn"]. }
    iModIntro. iExact "Hmk".
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
  Lemma ireg_withdraw (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (ds : list dinode)
      (b : Z) (bsl : list (bv 8)) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    b = IBLOCK inum inodestart ->
    diblk_wf ds ->
    bsl = diblk_bytes ds ->
    bv_unsigned (di_type (ds !!! islot inum)) <> 0 ->
    ireg_inv γi γfs inodestart nib -∗
    imark γi (bv_unsigned inum) -∗
    (b ↪[fs_L γfs]{#(1/2)} bsl) ={E}=∗
    ⌜fresh_shape (ds !!! islot inum)⌝ ∗
    dinode_at γi inum (ds !!! islot inum) ∗
    (b ↪[fs_L γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE Hin Hb Hwf Hbsl Hnz) "#Hinv Hmk Hhalf".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds0) "(>%Hwf0 & >%Hcp0 & >Hfsb & >Hsls)".
    rewrite /fsblock -(ireg_bi_iblock inum inodestart) -Hb.
    iDestruct (ghost_map_elem_agree with "Hhalf Hfsb") as %Hbytes.
    assert (Hds0 : ds0 = ds).
    { apply (diblk_bytes_inj ds0 ds Hwf0 Hwf). rewrite -Hbytes -Hbsl. reflexivity. }
    subst ds0.
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) [Hep Harm]]".
    (* the marker in the caller's hand refutes the OUT arm *)
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk']]"; last first.
    { iExFalso. iApply (imark_excl with "Hmk Hmk'"). }
    assert (Hfresh : fresh_shape (ds !!! islot inum))
      by (destruct Hin1 as [H0 | Hf]; [exfalso; exact (Hnz H0) | exact Hf]).
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hfsb Hmk Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb Hmk Hla Hep Hslback]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      rewrite /fsblock (ireg_bi_iblock inum inodestart) in Hb.
      rewrite Hb. iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hmk Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl gl cl rl Hlok with "Hla Hep").
      iRight. iSplitR; [iPureIntro; exact Hnz | iExact "Hmk"]. }
    iModIntro. iFrame "Hfr Hhalf". iPureIntro. exact Hfresh.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE TWO NLINK-MOVING WRITES (design §20.6)                          *)
  (* ------------------------------------------------------------------ *)

  (* [dp->nlink++; iupdate(dp)] -- mkdir's [".."] and sys_link's
     [ip->nlink++].  It is [ireg_write_au] with the ledger moving in the
     same ghost step as the count that pays for it: (L1) grows on BOTH
     sides at once, which is what keeps the cap an inequality nobody has to
     re-argue.  The fragment travels to the [dirlink] that deposits it in
     the directory's payload. *)
  Lemma ireg_write_link (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    bv_unsigned (di_nlink dn') = bv_unsigned (di_nlink dn) + 1 ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock γfs (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock γfs (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗
       dinode_at γi inum dn' ∗ ilink (bv_unsigned inum)).
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hnl) "#Hinv Hdn".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds0) "(>%Hwf0 & >%Hcp0 & >Hfsb & >Hsls)".
    iModIntro.
    rewrite (ireg_bi_iblock inum inodestart).
    iExists (diblk_bytes ds0).
    iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    assert (Hds0 : ds0 = ds) by exact (diblk_bytes_inj ds0 ds Hwf0 Hwf Hbytes).
    subst ds0.
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) [Hep Harm]]".
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    rewrite Hdeq in Hlok.
    (* (L1) GROWS ON BOTH SIDES AT ONCE: the count that pays for the new
       fragment is written in the same ghost step that mints it. *)
    assert (Hlok' : ireg_link_ok dn' (S wl)).
    { split.
      - exact (ireg_wle_plus (bv_unsigned (di_nlink dn))
                 (bv_unsigned (di_nlink dn')) wl
                 (di_nlink_nonneg dn) (proj1 Hlok) Hnl).
      - intros H0. exfalso. exact (Hnz H0). }
    (* nlink GROWS here, so the receipt's antecedent is absurd at [dn'] *)
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { intros H0. exfalso. pose proof (di_nlink_nonneg dn). lia. }
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    iMod (link_mint_link with "Hla") as "[Hla Hfrag]".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hfsb' Hmk Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hmk Hla Hep Hslback]").
      { intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn') |].
      iSplitR.
      { iPureIntro. intros i Hi.
        destruct Hwf as [Hlen _].
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
      iSplitL "Hfsb'"; [iExact "Hfsb'" |].
      iApply ("Hslback" $! dn' with "[Hmk Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' (S wl) gl cl rl Hlok'
                with "Hla Hep").
      iRight. iSplitR; [iPureIntro; exact Hnz | iExact "Hmk"]. }
    iModIntro. iFrame "Hdn Hfrag".
  Qed.

  (* [ip->nlink--; iupdate(ip)] -- sys_unlink's decrement, and THE ONLY
     nlink-LOWERING region write in the kernel (design §20.6).  It is the
     dual of [ireg_write_link]: the drop is paid for by CONSUMING one
     [ilink], so (L1) falls on both sides at once and no fragment is ever
     left stranded above the count that backs it.

     This is exactly why [ireg_write_au] may demand [di_nlink_stable]: the
     one writer that would violate it does not go through the ordinary
     flush at all. *)
  Lemma ireg_write_unlink (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    bv_unsigned (di_nlink dn) = bv_unsigned (di_nlink dn') + 1 ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ilink (bv_unsigned inum) -∗
    |={E, E ∖ ↑iregN}=> ∃ (bsl' : list (bv 8)) (v : nat),
      fsblock γfs (IBLOCK inum inodestart) bsl' ∗
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
      (⌜bsl' = diblk_bytes ds⌝ -∗
       izrcpt (bv_unsigned inum) dn' v -∗
       fsblock γfs (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ dinode_at γi inum dn').
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hnl) "#Hinv Hdn Hfrag".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds0) "(>%Hwf0 & >%Hcp0 & >Hfsb & >Hsls)".
    (* THE SLOT COMES OUT BEFORE THE MASK CLOSES, which is what lets the
       counter's value be handed to the caller in the same fupd. *)
    assert (Hlen0 : length ds0 = 16%nat) by (destruct Hwf0 as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds0 (islot inum) Hsl Hlen0
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) [Hep Harm]]".
    iDestruct (ireg_ep_open with "Hep") as (v) "[#Hvlb Hepback]".
    iModIntro.
    rewrite (ireg_bi_iblock inum inodestart).
    iExists (diblk_bytes ds0), v.
    iFrame "Hfsb Hvlb".
    iIntros (Hbytes) "Hrc Hfsb'".
    assert (Hds0 : ds0 = ds) by exact (diblk_bytes_inj ds0 ds Hwf0 Hwf Hbytes).
    subst ds0.
    iDestruct ("Hepback" $! dn' with "Hrc") as "Hep".
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    (* the caller's fragment forces [w >= 1], so the drop has something to
       spend and the authority is a successor *)
    iDestruct (link_w_ge with "Hla Hfrag") as %Hw1.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    rewrite Hdeq in Hlok.
    destruct wl as [| wl0]; [exfalso; lia |].
    (* ...and (L1) FALLS on both sides at once, which is what keeps a
       fragment from ever outliving the count that backs it. *)
    assert (Hlok' : ireg_link_ok dn' wl0).
    { split.
      - exact (ireg_wle_succ (bv_unsigned (di_nlink dn))
                 (bv_unsigned (di_nlink dn')) wl0
                 (di_nlink_nonneg dn') (proj1 Hlok) Hnl).
      - intros H0. exfalso. exact (Hnz H0). }
    iMod (link_spend_link with "Hla Hfrag") as "Hla".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hfsb' Hmk Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hmk Hla Hep Hslback]").
      { intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn') |].
      iSplitR.
      { iPureIntro. intros i Hi.
        destruct Hwf as [Hlen _].
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
      iSplitL "Hfsb'"; [iExact "Hfsb'" |].
      iApply ("Hslback" $! dn' with "[Hmk Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl0 gl cl rl Hlok'
                with "Hla Hep").
      iRight. iSplitR; [iPureIntro; exact Hnz | iExact "Hmk"]. }
    iModIntro. iExact "Hdn".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  §20.2's PAYOFF: A NAMED INUM IS AN ALLOCATED INUM                   *)
  (* ------------------------------------------------------------------ *)

  (* [ilink z] ==> [w >= 1] ([link_w_ge]) ==> (L1) [di_nlink >= 1] ==> (L3,
     contrapositive) [di_type <> 0] -- ALLOCATED.  [ireg_link_ok_alloc] is
     that chain, pure; this is its ACCESSOR, and its shape is forced.

     The fact is about a record the caller does NOT hold a fragment for --
     that is the whole point, since the fragment for a named inum is
     wherever that inum's owner put it -- so the caller cannot name the
     record through [dinode_at].  The one thing that CAN name it is the
     dinode block's machinery half, which pins the region's parked bytes:
     [ireg_read_blk]'s credential.  So the caller is between a [bread] and
     a [brelse] of the inum's own block, decodes the list, and learns the
     type of the slot the arithmetic lands on.

     Mask-preserving: nothing moves but the reading, and the fragment goes
     straight back (§20.4's "borrowed, not consumed" -- a licence that a
     directory's payload owns has to return at its holder's iunlock). *)
  Lemma ireg_link_alloc (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32)
      (b : Z) (bsl : list (bv 8)) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    b = IBLOCK inum inodestart ->
    ireg_inv γi γfs inodestart nib -∗
    ilink (bv_unsigned inum) -∗
    (b ↪[fs_L γfs]{#(1/2)} bsl) ={E}=∗
    ⌜exists ds : list dinode,
       diblk_wf ds /\ bsl = diblk_bytes ds /\
       bv_unsigned (di_type (ds !!! islot inum)) <> 0⌝ ∗
    ilink (bv_unsigned inum) ∗
    (b ↪[fs_L γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE Hin Hb) "#Hinv Hfrag Hhalf".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    rewrite /fsblock -(ireg_bi_iblock inum inodestart) -Hb.
    iDestruct (ghost_map_elem_agree with "Hhalf Hfsb") as %Hbytes.
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) [Hep Harm]]".
    iDestruct (link_w_ge with "Hla Hfrag") as %Hw1.
    assert (Hnz : bv_unsigned (di_type (ds !!! islot inum)) <> 0)
      by exact (ireg_link_ok_alloc (ds !!! islot inum) wl Hlok Hw1).
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hfsb Harm Hla Hep Hslback Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      rewrite /fsblock (ireg_bi_iblock inum inodestart) in Hb.
      rewrite Hb. iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl gl cl rl Hlok with "Hla Hep"). iExact "Harm". }
    iModIntro. iFrame "Hfrag Hhalf". iPureIntro.
    exists ds. split; [exact Hwf | split; [exact Hbytes | exact Hnz]].
  Qed.

End InodeRegion.
