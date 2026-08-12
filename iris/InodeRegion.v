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

   THE LEDGER'S CLAUSES ARE NOT YET STATED; see [ireg_link_ok] below for the
   single missing fact and where it has to come from.  The [di_nlink_stable]
   premises and the two moves above land AHEAD of it deliberately, so that
   stating the clauses costs no signature anywhere.

   ---- WHAT IS DELIBERATELY NOT HERE ------------------------------------

   The boot-time allocation (building the initial map from the mkfs
   image's dinode blocks and minting every [dinode_at]) is fsinit wiring
   and lives in [IcacheBoot.v], not here.  The icache pool that HOLDS the
   fragments of uncached inodes is IcacheInv's (design §10.4).            *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl.
From iris.base_logic.lib Require Import invariants ghost_map.
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
   elaborated in [bi_scope]. *)
Definition di_nlink_stable (dn' dn : dinode) : Prop :=
  bv_unsigned (di_nlink dn) <= bv_unsigned (di_nlink dn').

(* The two ways every caller in the tree discharges it, and both are one
   token: no writer at or below iupdate moves [nlink] at all -- writei,
   itrunc, dirlink, filewrite and iput's free path all rebuild the record
   with [di_nlink d] verbatim. *)
Lemma di_nlink_stable_eq (dn' dn : dinode) :
  di_nlink dn' = di_nlink dn -> di_nlink_stable dn' dn.
Proof. intros Heq. rewrite /di_nlink_stable Heq. lia. Qed.

Lemma di_nlink_stable_refl (dn : dinode) : di_nlink_stable dn dn.
Proof. apply di_nlink_stable_eq. reflexivity. Qed.

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
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ}.
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

     THE CLAUSES ARE NOT YET STATED, AND THE REASON IS ONE KNOT, NOT A
     SHORTCUT (fs-sysfile S5f; §20 did not price it).  (L1) and (L3) stand
     or fall together, and their joint discharge lands on `ProofIput`:

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
         guarded by [ip->nlink == 0] at iput+0x40 -- but the PROOF loses it:
         [ProofIput] reads that halfword off the record [dn] it holds
         BEFORE the window, and re-opens the payload after [acquiresleep] as
         a FRESH existential [dn2] (ProofIput.v:1938) with no link back.
         [ity_shot] pins the TYPE across the window and nothing pins
         [nlink].
       * and there is no third way in: the ledger's authority may only be
         lowered by a frame-preserving update, so nothing can "clear" [w]
         for a record whose fragments are outstanding.  §19.7's rule again.

     So the authority is PARKED here -- which is the placement §20.9(c)/(d)
     argues for and the half that costs an interface -- and the clauses
     wait on the one missing fact.  The predicate is named and applied at
     every site that will have to re-establish it, so landing (L1)+(L3) is
     a change to THIS definition plus one obligation in each of the six
     movers, and to no signature anywhere.  See the S5f ledger entry in
     claude-notes/projects/fs-sysfile.md for the two candidate repairs. *)
  Definition ireg_link_ok (d : dinode) (w : nat) : Prop := True.

  Definition ireg_slot (γi : gname) (z : Z) (d : dinode) : iProp Σ :=
    ((∃ (w g r : nat) (c : option (excl unit)),
        link_auth z w g c r ∗ ⌜ireg_link_ok d w⌝)
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
    ((⌜ireg_in d⌝ ∗ z ↪[γi] d)
     ∨ (⌜bv_unsigned (di_type d) <> 0⌝ ∗ imark γi z)) -∗
    ireg_slot γi z d.
  Proof.
    intros Hok. iIntros "Hla Harm". rewrite /ireg_slot. iFrame "Harm".
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
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) Harm]".
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
    assert (Hlok' : ireg_link_ok dn' wl) by exact I.
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    (* re-park the block at the flushed bytes, re-coupled at m' *)
    iMod ("Hclose" with "[Ha Hfsb' Hmk Hla Hslback Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hmk Hla Hslback]").
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
      iApply ("Hslback" $! dn' with "[Hmk Hla]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl gl cl rl Hlok'
                with "Hla").
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
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) Harm]".
    (* the OUT arm claims a nonzero type; the caller's buffer says zero *)
    iDestruct "Harm" as "[[%Hin1 Hfrg] | [%Ht2 Hmk]]"; last first.
    { iExFalso. iPureIntro. exact (Ht2 Ht0). }
    (* (L3) AT THE CLAIMED SLOT: the record the caller's buffer showed
       type-0 has [nlink = 0], so (L1) collapses to [w = 0] -- i.e. no live
       directory record names the inum ialloc is about to claim -- and the
       fresh record's own (L1) is then free whatever [nlink] it carries. *)
    assert (Hlok' : ireg_link_ok dn' wl) by exact I.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hfrg") as %Hm.
    iMod (ghost_map_update dn' with "Ha Hfrg") as "[Ha Hfrg]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hfsb' Hfrg Hla Hslback Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hfrg Hla Hslback]").
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
      iApply ("Hslback" $! dn' with "[Hfrg Hla]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl gl cl rl Hlok'
                with "Hla").
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

     WHAT THIS LEMMA DOES *NOT* DO, and why (fs-sysfile S5f).  §20.5 wants
     the free to re-establish "[c = None] at a type-0 record", which is the
     clause that would make [ireg_claim_au]'s [iclaim] payout mintable.  It
     cannot: setting an exclusive claim slot back to [None] is not a
     frame-preserving update while the claimant's fragment is outstanding,
     so the free would have to CONSUME [iclaim inum] -- and iput holds no
     such token.  §20.7's own text records the same fact from the other
     end ("[ireg_free_au]'s new [c = None] premise has no discharge in
     [ProofIput] today") and prices (M1) as the carrier.  So the claim
     component exists in the algebra and the ledger carries it, but no
     clause constrains it and nothing mints it yet. *)
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
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) Harm]".
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hlok' : ireg_link_ok dn' wl) by exact I.
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hfsb' Hdn Hla Hslback Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hdn Hla Hslback]").
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
      iApply ("Hslback" $! dn' with "[Hdn Hla]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl gl cl rl Hlok'
                with "Hla").
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
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) Harm]".
    (* the marker in the caller's hand refutes the OUT arm *)
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk']]"; last first.
    { iExFalso. iApply (imark_excl with "Hmk Hmk'"). }
    assert (Hfresh : fresh_shape (ds !!! islot inum))
      by (destruct Hin1 as [H0 | Hf]; [exfalso; exact (Hnz H0) | exact Hf]).
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hfsb Hmk Hla Hslback Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb Hmk Hla Hslback]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      rewrite /fsblock (ireg_bi_iblock inum inodestart) in Hb.
      rewrite Hb. iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hmk Hla]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl gl cl rl Hlok with "Hla").
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
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) Harm]".
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hlok' : ireg_link_ok dn' (S wl)) by exact I.
    iMod (link_mint_link with "Hla") as "[Hla Hfrag]".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hfsb' Hmk Hla Hslback Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hmk Hla Hslback]").
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
      iApply ("Hslback" $! dn' with "[Hmk Hla]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' (S wl) gl cl rl Hlok'
                with "Hla").
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
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock γfs (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
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
    iDestruct "Hslot" as "[(%wl & %gl & %rl & %cl & Hla & %Hlok) Harm]".
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    (* the caller's fragment forces [w >= 1], so the drop has something to
       spend and the authority is a successor *)
    iDestruct (link_w_ge with "Hla Hfrag") as %Hw1.
    destruct wl as [| wl0]; [exfalso; lia |].
    assert (Hlok' : ireg_link_ok dn' wl0) by exact I.
    iMod (link_spend_link with "Hla Hfrag") as "Hla".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hfsb' Hmk Hla Hslback Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hmk Hla Hslback]").
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
      iApply ("Hslback" $! dn' with "[Hmk Hla]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl0 gl cl rl Hlok'
                with "Hla").
      iRight. iSplitR; [iPureIntro; exact Hnz | iExact "Hmk"]. }
    iModIntro. iExact "Hdn".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE DERIVED CHAIN IS NOT HERE YET (§20.2's payoff)                  *)
  (* ------------------------------------------------------------------ *)

  (* [ilink z] ==> [w >= 1] ==> (L1) [di_nlink >= 1] ==> (L3,
     contrapositive) [di_type <> 0] -- ALLOCATED -- is the one line §20.2
     calls the payoff, and [link_w_ge] above already supplies its first
     step.  The remaining two are (L1) and (L3), which [ireg_link_ok] does
     not yet state; see the note there for the single missing fact and
     where it has to come from.  The consumer shape it will take is
     [ireg_read_blk]'s (a scan holding the dinode block's machinery half),
     because that is the only place a caller can NAME the record whose
     type it wants to know. *)

End InodeRegion.
