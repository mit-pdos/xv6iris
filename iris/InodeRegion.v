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
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants ghost_map mono_nat.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvPtsto.
Require Import RiscvModelBytes.
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
   is the ONE record shape a caller may hold whose [nlink] the ledger has
   never constrained from outside -- the fragment sits inside the region at
   this arm and (L1) is discharged there from (L3) -- and create's COMMIT is
   the first writer that has to say what that count IS: it mints one [ilink]
   against [nlink 0 -> 1], and "the record I am flushing over has nlink 0"
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
   so [ireg_write_au], [ireg_free_au] and the two link movers re-establish
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
  | Some x => fresh_shape d /\ f = Some (Excl FrzOff) /\ x = Excl (di_type d)
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
Lemma ireg_claim_ok_ty (ty : bv 16) (f : frzUR) (d : dinode) :
  ireg_claim_ok (Some (Excl ty)) f d -> di_type d = ty.
Proof. intros [_ [_ Hx]]. injection Hx as Heq. exact (eq_sym Heq). Qed.

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
Inductive ilkc : Type :=
| ClaimK (ty : bv 16)
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
   the one mover that writes a zero type is [ireg_free_au], which holds
   [ifreeze_post] and therefore [n = 0] by the freeze pin -- and (R1) turns
   that into [r = rc = 0].  So the ruling's "all units die at the free's
   count-0" is exactly (R1), stated.  The three conjuncts are ONE predicate so
   that [ireg_slot]'s pure block grows by one clause and not three.

   THE COST TO THE MOVERS, ARM BY ARM.  (R1) moves only where BOTH a unit and
   the count move, which is every count mover by construction (iget's two
   up-counts and idup mint, iput's two closes spend).  (R2) is stable at every
   type-preserving flush, vacuous at [ireg_claim_au] (a [fresh_shape] record
   has a nonzero type) and paid at [ireg_free_au] as above.  (R3) is vacuous
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

(* (R1) at a count-0 slot -- [ireg_free_au]'s payment *)
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
   its one raising site.  [ireg_free_au] writes [di_type = 0] over a frozen
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

Lemma ireg_frzm_ok_true (rg : bool) :
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
     of [dinode_at] could lower [nlink] under an outstanding [ilink] and
     (L1) would break; with it, "a fragment outstanding implies
     [nlink >= 1]" is a theorem of the region rather than a survey of this
     tree's callers.  It is an EQUALITY and not "does not fall", because
     that is what every discharge site in the tree actually has: no writer
     that goes through the ordinary flush moves [nlink] at all, so
     [di_nlink_stable_refl] / [di_nlink_stable_free] take the equation as
     input already and the two consumers below become rewrites.
     sys_unlink's decrement is the ONE writer that moves an [nlink], and it
     does not go through the ordinary flush at all -- it goes through
     [ireg_write_unlink], which pays for the drop by CONSUMING a fragment.

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

(* ---- (L4-ROOT), THE ROOT CLAUSE (design fs-icache.md §20.4) -------------

   §20.4 charters [ireg_body] gaining "the root's link count is at least
   one", because that is what refutes SpecIget's licence (f) -- the arm
   [⌜bv_unsigned z = ROOTINO⌝], which namex's absolute walk uses at +0x4c and
   which nothing else can refute at a record whose count is ZERO (a claim
   box, or iput's freeing flush).  fs-fragments.md §3.6's row (f) is the
   customer.

   THE CHARTERED FORM IS NOT PRESERVABLE, AND THE ARITHMETIC SAYS WHY.
   Take the clause as [1 <= di_nlink] alone and run it past
   [ireg_write_unlink], the kernel's one nlink-LOWERING region write.  That
   mover knows [di_nlink dn = di_nlink dn' + 1] and, from the [ilink] it
   spends, [1 <= w]; at the root it would have to show [1 <= di_nlink dn'],
   i.e. [2 <= di_nlink dn], and the old clause gives only [1 <= di_nlink dn].
   The gap is real and no premise on the MOVER closes it honestly: the mover
   cannot see that xv6 never unlinks the root, and the walk that does
   ([sys_unlink] refusing ["."] and [".."]) is three contracts away.

   WHAT IS PRESERVABLE IS (L1) MADE STRICT AT THE ROOT: [w < di_nlink].  The
   root's slack is exactly one and it is structural, not a coincidence of
   reachability --

     [dir_links] files ONE ledger unit per live NON-SELF record, so the
     root's own ["."] and [".."] (both naming the root) are filed by
     nobody, while every subdirectory's [".."] is filed against the root and
     is paid for by the [dp->nlink++] create runs at +0x128.  So the root's
     count is one MORE than the number of records that can ever name it: the
     mkfs image's [nlink = 1] is the entry the root does not have in a
     parent, and no [dirlink] can ever mint a fragment against it.

   Strictness turns every mover into arithmetic that closes on its own
   premises, with NO new premise on any of the six and no obligation
   threaded to any caller:

     [ireg_write_link]   [w -> S w] and [nlink -> nlink + 1]: strict is
                         monotone under a simultaneous bump.
     [ireg_write_unlink] [S w -> w] and [nlink -> nlink - 1]: the SAME step
                         downwards -- and this is the mover the chartered
                         form could not survive.
     [ireg_write_au]     [nlink] does not move ([di_nlink_stable]) and [w]
                         does not either.
     [ireg_claim_au]     REFUTED at the root: the caller's buffer shows
                         [di_type = 0], (L3) forces [di_nlink = 0], and
                         [w < 0] is absurd.  ialloc can never claim the root.
     [ireg_free_au]      REFUTED at the root by the same two steps from its
                         own [di_nlink dn = 0].  iput can never free the root.
     [ireg_withdraw]     record, count and authority all unchanged.

   The chartered form is the PROJECTION [ireg_root_ok_alive], and licence
   (f)'s refutation is [ireg_root_ok_ne] (pure) / [ireg_root_ne] (the
   accessor, below).

   THE INUM IS A LITERAL at the region's own key type, for the reason
   [ireg_link_ok]'s 32767 and [ireg_bi]'s 16 are: [InodeInv.ROOTINO] is
   [mword_of_int 1 : mword 32] and [bv_unsigned] of it is this number, but
   importing [InodeInv] would put the whole in-core inode geometry (and
   [Kernel.KernelSyms]) underneath a file 350 dependents deep.  The bridge
   is [IregLinkNz.ireg_root_ROOTINO], one [reflexivity].

   Stated OUTSIDE the section for [ireg_wle_*]'s reason (a [bv 32] in the
   section context breaks [lia]'s zify hook), which is also why the four
   arithmetic steps below are over plain [Z]. *)
Definition ireg_root : Z := 1.

Lemma ireg_wlt_pos (a : Z) (w : nat) : (w < Z.to_nat a)%nat -> 1 <= a.
Proof. lia. Qed.

Lemma ireg_wlt_zero (a : Z) (w : nat) : (w < Z.to_nat a)%nat -> a <> 0.
Proof. lia. Qed.

Lemma ireg_wlt_intro (a : Z) : 1 <= a -> (0 < Z.to_nat a)%nat.
Proof. lia. Qed.

Lemma ireg_wlt_succ (a b : Z) (w : nat) :
  (S w < Z.to_nat a)%nat -> a = b + 1 -> (w < Z.to_nat b)%nat.
Proof. lia. Qed.

Lemma ireg_wlt_plus (a b : Z) (w : nat) :
  (w < Z.to_nat a)%nat -> b = a + 1 -> (S w < Z.to_nat b)%nat.
Proof. lia. Qed.

(* the clause itself: (L1) STRICT, and only at the root.  Every other slot
   reads it as a tautology, which is why the five constructors below are all
   a mover ever needs. *)
Definition ireg_root_ok (z : Z) (d : dinode) (w : nat) : Prop :=
  z = ireg_root -> (w < Z.to_nat (bv_unsigned (di_nlink d)))%nat.

(* §20.4's CHARTERED READING, recovered.  This is the whole point of the
   clause and the only form a consumer outside this file should need. *)
Lemma ireg_root_ok_alive (z : Z) (d : dinode) (w : nat) :
  ireg_root_ok z d w -> z = ireg_root -> 1 <= bv_unsigned (di_nlink d).
Proof. intros H Hz. exact (ireg_wlt_pos _ w (H Hz)). Qed.

(* ...AND LICENCE (f)'s REFUTATION, pure (fs-fragments.md §3.6, row (f)).
   A record whose count is zero -- a claim box ([fresh_shape]) or the record
   iput's free path flushes -- is NOT the root. *)
Lemma ireg_root_ok_ne (z : Z) (d : dinode) (w : nat) :
  ireg_root_ok z d w -> bv_unsigned (di_nlink d) = 0 -> z <> ireg_root.
Proof. intros H H0 Hz. exact (ireg_wlt_zero _ w (H Hz) H0). Qed.

(* the vacuous constructor: at any other inum the clause says nothing *)
Lemma ireg_root_ok_nonroot (z : Z) (d : dinode) (w : nat) :
  z <> ireg_root -> ireg_root_ok z d w.
Proof. intros Hne Hz. exfalso. exact (Hne Hz). Qed.

(* BOOT: at the empty ledger the strict clause IS the chartered one, which
   is why the image obligation ([IcacheBoot.image_root_alive]) can be stated
   in §20.4's own words. *)
Lemma ireg_root_ok_zero (z : Z) (d : dinode) :
  (z = ireg_root -> 1 <= bv_unsigned (di_nlink d)) -> ireg_root_ok z d 0.
Proof. intros H Hz. exact (ireg_wlt_intro _ (H Hz)). Qed.

(* the ordinary flush: neither side moves *)
Lemma ireg_root_ok_stable (z : Z) (d d' : dinode) (w : nat) :
  di_nlink d' = di_nlink d -> ireg_root_ok z d w -> ireg_root_ok z d' w.
Proof. intros Heq H Hz. rewrite Heq. exact (H Hz). Qed.

(* the two nlink-moving writes, where BOTH sides move by one at once *)
Lemma ireg_root_ok_bump (z : Z) (d d' : dinode) (w : nat) :
  bv_unsigned (di_nlink d') = bv_unsigned (di_nlink d) + 1 ->
  ireg_root_ok z d w -> ireg_root_ok z d' (S w).
Proof. intros Hnl H Hz. exact (ireg_wlt_plus _ _ w (H Hz) Hnl). Qed.

Lemma ireg_root_ok_drop (z : Z) (d d' : dinode) (w : nat) :
  bv_unsigned (di_nlink d) = bv_unsigned (di_nlink d') + 1 ->
  ireg_root_ok z d (S w) -> ireg_root_ok z d' w.
Proof. intros Hnl H Hz. exact (ireg_wlt_succ _ _ w (H Hz) Hnl). Qed.

(* ---- (T1), THE COUNT-FACT CARRIER's CLAUSE (S7-unlink FINDING 3, V1) ----

   THE LEDGER'S [w] IS A PAIR [(wl, wd)] SINCE V1 ([Xv6Cameras.linkElemUR]),
   and (L1) is the SUM: [wl + wd <= di_nlink].  [wd] counts the paid records
   whose holder ALSO knows the target is a DIRECTORY -- the fragment is
   [IcacheRef.ilinkd] -- and (T1) is what makes that knowledge true:

     [0 < wd  ->  di_type d = T_DIR].

   WHY IT IS A SEPARATE CONJUNCT AND NOT A FOURTH CLAUSE OF [ireg_link_ok].
   The root clause's reason, verbatim (the comment at [ireg_slot]): that
   predicate has consumers all over the tree reading it BY PROJECTION
   ([ireg_link_ok_alloc] / [_short] / [_free] and eleven destructurings in
   this file), and a fourth conjunct moves every one of them.  Stated
   beside, the widening costs the six movers an arithmetic rewrite
   ([ireg_link_ok] and [ireg_root_ok] are applied at [wl + wd] and are
   THEMSELVES UNCHANGED) plus one extra pure obligation apiece, and costs
   every consumer outside this file nothing at all.

   THE TYPE IS A LITERAL at the region's own key type, for exactly
   [ireg_root]'s reason: [DirView.T_DIR_z] is [1], but importing [DirView]
   here would put the directory-view geometry underneath a file with ~350
   dependents for one constant.  The bridge is
   [IregDirBit.ireg_dir_ty_T_DIR_z], one [reflexivity], and the ACCESSOR
   that hands the fact to a caller lives in that leaf too.

   PRESERVATION, mover by mover -- and it is cheaper than the root clause's
   because [di_type] moves in only two places:

     [ireg_write_au]      [di_type_stable] plus the nonzero-type premise
                          give [di_type dn' = di_type dn]: (T1) rides across.
     [ireg_write_link]    the same two premises; [wd] does not move on the
                          PLAIN flavour, and on the d flavour the mover's own
                          new premise IS (T1) at the written record.
     [ireg_write_unlink]  the same two premises; the spent flavour lowers
                          whichever component it was filed in, and lowering
                          [wd] only weakens the antecedent.
     [ireg_claim_au]      REFUTED into vacuity: (L3) at the type-0 record
                          forces the SUM to zero, hence [wd = 0].
     [ireg_free_au]       the same, from its own [di_nlink dn = 0].
     [ireg_withdraw]      record, counts and authority all unchanged. *)
Definition ireg_dir_ty : Z := 1.

Definition ireg_dir_ok (d : dinode) (wd : nat) : Prop :=
  (0 < wd)%nat -> bv_unsigned (di_type d) = ireg_dir_ty.

(* the vacuous constructor -- the claim, the free and the whole boot image *)
Lemma ireg_dir_ok_zero (d : dinode) : ireg_dir_ok d 0.
Proof. intros H. exfalso. lia. Qed.

(* the CHARTERED READING, and the only form a consumer outside this file
   should need ([IregDirBit.ireg_dirbit_ty] is its accessor) *)
Lemma ireg_dir_ok_ty (d : dinode) (wd : nat) :
  ireg_dir_ok d wd -> (0 < wd)%nat -> bv_unsigned (di_type d) = ireg_dir_ty.
Proof. intros H Hw. exact (H Hw). Qed.

(* the type does not move: (T1) rides any flush that keeps it *)
Lemma ireg_dir_ok_stable (d d' : dinode) (wd : nat) :
  di_type d' = di_type d -> ireg_dir_ok d wd -> ireg_dir_ok d' wd.
Proof. intros Heq H Hw. rewrite Heq. exact (H Hw). Qed.

(* the d-flavoured mint's own constructor: the writer KNOWS the type *)
Lemma ireg_dir_ok_intro (d : dinode) (wd : nat) :
  bv_unsigned (di_type d) = ireg_dir_ty -> ireg_dir_ok d wd.
Proof. intros H _. exact H. Qed.

(* ...and the antecedent only weakens downwards, which is what a d-flavoured
   SPEND needs at the record it lowers *)
Lemma ireg_dir_ok_le (d : dinode) (wd wd' : nat) :
  (wd' <= wd)%nat -> ireg_dir_ok d wd -> ireg_dir_ok d wd'.
Proof. intros Hle H Hw. apply H. lia. Qed.

(* ---- (T1'), THE PLAIN-UNIT REFUSAL AT DIRECTORIES (V4) ----------------

   The MIRROR of (T1), on the OTHER component: a record whose type is
   T_DIR is never paid for by a PLAIN unit --

     [di_type d = ireg_dir_ty  ->  wl = 0].

   (T1) lets a holder of a d-flavoured unit READ "directory"; (T1') lets
   a holder of a PLAIN unit REFUTE it ([IregDirBit.ireg_link_not_dir] is
   the accessor), which is the missing half of S7-unlink's T_DIR arm:
   the flavour of the record it zeroes is existential, the FILE arm
   refutes [b = true] through (T1), and this clause is what refutes
   [b = false].  SEPARATE CONJUNCT beside [ireg_dir_ok], same discipline
   and same reasons.

   TRUE OF EVERY MINT after V4's flip: the only walk that raises a
   DIRECTORY's count is create's mkdir arm ([dp->nlink++] pays for the
   child's [".."] and is minted d-flavoured since the flip; the child
   mint at +0xc4 is d-flavoured exactly when the child is a directory),
   and sys_link refuses T_DIR targets.  Preservation, mover by mover, is
   in each mover's own header; the one PREMISE it costs is
   [ireg_write_link_fl]'s at [fl = None] -- a plain mint must show its
   record is NOT a directory, which every plain-minting site knows. *)
Definition ireg_dir_wl0 (d : dinode) (wl : nat) : Prop :=
  bv_unsigned (di_type d) = ireg_dir_ty -> wl = 0%nat.

(* the zero constructor -- boot, the claim, the free, and the tagged
   mint's collapsed pre-state *)
Lemma ireg_dir_wl0_zero (d : dinode) : ireg_dir_wl0 d 0.
Proof. intros _. reflexivity. Qed.

(* the type does not move: the clause rides any flush that keeps it *)
Lemma ireg_dir_wl0_stable (d d' : dinode) (wl : nat) :
  di_type d' = di_type d -> ireg_dir_wl0 d wl -> ireg_dir_wl0 d' wl.
Proof. intros Heq H Hty. apply H. rewrite -Heq. exact Hty. Qed.

(* the vacuous constructor: a NON-directory owes nothing, which is what
   the plain mint's new premise buys *)
Lemma ireg_dir_wl0_intro (d : dinode) (wl : nat) :
  bv_unsigned (di_type d) <> ireg_dir_ty -> ireg_dir_wl0 d wl.
Proof. intros Hne Hty. exfalso. exact (Hne Hty). Qed.

(* ...and the antecedent's conclusion only strengthens downwards, which
   is what a plain SPEND needs at the record it lowers *)
Lemma ireg_dir_wl0_le (d : dinode) (wl wl' : nat) :
  (wl' <= wl)%nat -> ireg_dir_wl0 d wl -> ireg_dir_wl0 d wl'.
Proof. intros Hle H Hty. pose proof (H Hty). lia. Qed.

(* ---- [ireg_par_ok], THE PARENT REGISTER'S CLAUSE (V5') ----------------

   The register [p] and the TAGGED count [wdt] move together and only
   together: [wdt] is at most one (a record has one parent), the register
   is set EXACTLY when the tagged unit is outstanding, and when set it is
   set at the FULL fraction (the two outstanding halves -- [ilinkdp] and
   [iparent] -- are its complement).  The iff is what makes the tagged
   mint legal with no memory: at a reclaimed inum the pre-record's
   [nlink = 0] collapses the counts, [wdt = 0] forces [p = None], and the
   alloc is frame-preserving (V5' Correction 1).

   The [(wdu, wdt)] SPLIT is what makes this clause syntactically
   preservable: untagged movers touch [wdu] only and the clause never
   moves; tagged movers move [wdt] and [p] together (V5''s "why the
   split is forced"). *)
Definition ireg_par_ok (wdt : nat)
    (p : option (dfrac_agreeR (leibnizO Z))) : Prop :=
  (wdt <= 1)%nat /\ (p = None <-> wdt = 0%nat) /\
  (p = None \/ exists pv : Z, p = Some (lreg pv)).

Lemma ireg_par_ok_none : ireg_par_ok 0 None.
Proof. split_and!; [lia | split; reflexivity | left; reflexivity]. Qed.

Lemma ireg_par_ok_some (pv : Z) : ireg_par_ok 1 (Some (lreg pv)).
Proof.
  split_and!; [lia | split; discriminate | right; exists pv; reflexivity].
Qed.

Lemma ireg_par_ok_wdt0 (wdt : nat)
    (p : option (dfrac_agreeR (leibnizO Z))) :
  ireg_par_ok wdt p -> wdt = 0%nat -> p = None.
Proof. intros (_ & Hiff & _) H0. exact (proj2 Hiff H0). Qed.

Lemma ireg_par_ok_full (wdt : nat)
    (p : option (dfrac_agreeR (leibnizO Z))) :
  ireg_par_ok wdt p -> (1 <= wdt)%nat ->
  wdt = 1%nat /\ exists pv : Z, p = Some (lreg pv).
Proof.
  intros (Hle & Hiff & Hor) H1. split; [lia |].
  destruct Hor as [Hn | Hp]; [| exact Hp].
  exfalso. pose proof (proj1 Hiff Hn). lia.
Qed.

(* (L1)'s SUM at a record nothing names: both components collapse.  Stated
   over plain [nat] outside every section for [ireg_wle_*]'s reason -- the
   goals it is used in have a [bv 32] in context, where [lia]'s zify hook
   answers "Cannot find witness". *)
Lemma ireg_sum_zero (a b : nat) : (a + b = 0)%nat -> a = 0%nat /\ b = 0%nat.
Proof. lia. Qed.

(* ...and the TERNARY form the V5' split needs at the claim and the free *)
Lemma ireg_sum_zero3 (a b c : nat) :
  (a + b + c = 0)%nat -> a = 0%nat /\ b = 0%nat /\ c = 0%nat.
Proof. lia. Qed.

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

(* [iregG] -- one [ghost_mapG Σ Z dinode] -- is defined in
   Xv6Cameras.v; what a caller holds is below. *)

Section InodeRegion.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ, !icacheG Σ,
            !logG Σ}.
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
  Definition ireg_link_ok (d : dinode) (w : nat) : Prop :=
    (w <= Z.to_nat (bv_unsigned (di_nlink d)))%nat                    (* L1 *)
    /\ (bv_unsigned (di_type d) = 0 -> bv_unsigned (di_nlink d) = 0)  (* L3 *)
    /\ bv_unsigned (di_nlink d) <= 32767.                             (* L4 *)

  (* (L1)'s contrapositive, and the reason the ledger exists: a record with
     an outstanding fragment is ALLOCATED.  Pure, so that every arm move
     and every consumer reads it off the clause the same way. *)
  Lemma ireg_link_ok_alloc (d : dinode) (w : nat) :
    ireg_link_ok d w -> (1 <= w)%nat -> bv_unsigned (di_type d) <> 0.
  Proof.
    intros [Hle [Hz _]] Hw H0. specialize (Hz H0).
    rewrite Hz in Hle. cbn in Hle. lia.
  Qed.

  (* (L4) read off without destructuring three ways -- the one clause a
     WRITER needs and the two above do not mention. *)
  Lemma ireg_link_ok_short (d : dinode) (w : nat) :
    ireg_link_ok d w -> bv_unsigned (di_nlink d) <= 32767.
  Proof. intros [_ [_ H4]]. exact H4. Qed.

  (* ...and (L3)+(L1) at a FREE record: nothing names it. *)
  Lemma ireg_link_ok_free (d : dinode) (w : nat) :
    ireg_link_ok d w -> bv_unsigned (di_type d) = 0 -> w = 0%nat.
  Proof.
    intros [Hle [Hz _]] H0. specialize (Hz H0). rewrite Hz in Hle. cbn in Hle.
    lia.
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
  (* THE LEDGER'S [w] IS THE PAIR [(wl, wd)] SINCE V1, and (L1) and the root
     clause are both applied AT THE SUM -- which is why neither predicate
     moved and why no consumer of either outside this file did.  (T1) is the
     third pure conjunct, beside them for their own reason. *)
  (* SINCE THE FUSED V4+V5' INCREMENT the pure block carries FIVE clauses:
     (L1) and the root clause at the ternary sum, (T1) at the d-SUM
     [wdu + wdt], (T1') at [wl], and [ireg_par_ok] tying the register to
     the tagged count.  Separate conjuncts throughout -- each mover
     re-establishes exactly the ones its components move. *)
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
  Definition ireg_fsh (f : frzUR) : iProp Σ :=
    match f with
    | Some (Excl FrzOff)       => True
    | Some (Excl (FrzPre rg))  => ireg_regime rg
    | Some (Excl (FrzPost rg)) => ireg_regime rg
    | _                        => (ireg_open ∨ ireg_boot)
    end%I.

  Global Instance ireg_fsh_timeless f : Timeless (ireg_fsh f).
  Proof. rewrite /ireg_fsh. destruct f as [[[| rg | rg] |] |]; apply _. Qed.

  Lemma ireg_fsh_off : ⊢ ireg_fsh (Some (Excl FrzOff)).
  Proof. rewrite /ireg_fsh. done. Qed.

  Lemma ireg_fsh_pre (rg : bool) :
    ireg_regime rg -∗ ireg_fsh (Some (Excl (FrzPre rg))).
  Proof. iIntros "H". iExact "H". Qed.

  Lemma ireg_fsh_post (rg : bool) :
    ireg_regime rg -∗ ireg_fsh (Some (Excl (FrzPost rg))).
  Proof. iIntros "H". iExact "H". Qed.

  (* RULING G's RETURN LEG, as one line: with the column pinned at [FrzPost rg]
     by the walk's own token, the parked arm IS the regime the freezer lent. *)
  Lemma ireg_fsh_post_acc (rg : bool) :
    ireg_fsh (Some (Excl (FrzPost rg))) -∗ ireg_regime rg.
  Proof. iIntros "H". iExact "H". Qed.

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
    - iIntros "H Hb". iExFalso. iApply (ireg_regime_boot_excl with "H Hb").
    - iIntros "H Hb". iExFalso. iApply (ireg_regime_boot_excl with "H Hb").
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
       <- [ireg_free_au] <- "the count is zero", and (R1) is the only thing
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
  Definition ireg_rcol (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR)
      (n : nat) (d : dinode) : iProp Σ :=
    (∃ rc : nat, link_auth z wl wdu wdt g c r p f rc
                 ∗ ⌜ireg_ref_ok r rc n c d⌝)%I.

  Global Instance ireg_rcol_timeless z wl wdu wdt g c r p f n d :
    Timeless (ireg_rcol z wl wdu wdt g c r p f n d).
  Proof. rewrite /ireg_rcol. apply _. Qed.

  Lemma ireg_rcol_intro (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR)
      (n rc : nat) (d : dinode) :
    ireg_ref_ok r rc n c d ->
    link_auth z wl wdu wdt g c r p f rc -∗
    ireg_rcol z wl wdu wdt g c r p f n d.
  Proof.
    intros Href. iIntros "Hla". rewrite /ireg_rcol. iExists rc.
    iFrame "Hla". iPureIntro. exact Href.
  Qed.

  (* the ride-through: every mover that touches NEITHER the record's type nor
     the two r columns nor c re-parks the bundle by this one line *)
  Lemma ireg_rcol_stable (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR)
      (n : nat) (d d' : dinode) :
    di_type d' = di_type d ->
    ireg_rcol z wl wdu wdt g c r p f n d -∗
    ireg_rcol z wl wdu wdt g c r p f n d'.
  Proof.
    intros Hty. rewrite /ireg_rcol. iIntros "(%rc & Hla & %Href)".
    iExists rc. iFrame "Hla". iPureIntro.
    exact (ireg_ref_ok_stable r rc n c d d' Hty Href).
  Qed.


  (* ---- READ-THROUGHS.  Every landed READER of the ledger authority goes
     through one of these rather than unpacking: the bundle is transparent to
     a fact-extracting lemma, so the ~20 sites that only look at the ledger
     move by one token and only the ones that MOVE it peel. *)
  Lemma ireg_rcol_freeze_agree (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) (ph : frz) :
    ireg_rcol z wl wdu wdt g c r p f n d -∗ ifreeze ph z -∗
    ⌜f = Some (Excl ph)⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & _) Hfz".
    iApply (link_freeze_agree with "Hla Hfz").
  Qed.

  Lemma ireg_rcol_w_ge (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) :
    ireg_rcol z wl wdu wdt g c r p f n d -∗ ilink z -∗ ⌜(1 <= wl)%nat⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & _) Hb".
    iApply (link_w_ge with "Hla Hb").
  Qed.

  Lemma ireg_rcol_wd_ge (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) :
    ireg_rcol z wl wdu wdt g c r p f n d -∗ ilinkd z -∗ ⌜(1 <= wdu)%nat⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & _) Hb".
    iApply (link_wd_ge with "Hla Hb").
  Qed.

  Lemma ireg_rcol_wdt_ge (z : Z) (wl wdu wdt g : nat) (c : ctyUR)
      (r : nat) (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) (pv : Z) :
    ireg_rcol z wl wdu wdt g c r p f n d -∗ ilinkdp z pv -∗
    ⌜(1 <= wdt)%nat /\ Some (lreg_half pv) ≼ p⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & _) Hb".
    iApply (link_wdt_ge with "Hla Hb").
  Qed.

  Lemma ireg_rcol_wsum_ge (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) (fl : option (option Z)) :
    ireg_rcol z wl wdu wdt g c r p f n d -∗ ilink_fl fl z -∗
    ⌜(1 <= wl + wdu + wdt)%nat⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & _) Hb".
    iApply (link_wsum_ge with "Hla Hb").
  Qed.

  Lemma ireg_rcol_claim_agree (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) (ty : bv 16) :
    ireg_rcol z wl wdu wdt g c r p f n d -∗ iclaim z ty -∗
    ⌜c = Some (Excl ty)⌝.
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
  Lemma ireg_rcol_mint (bfl : bool) (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) :
    bv_unsigned (di_type d) <> 0 ->
    (bfl = false -> c = None) ->
    ireg_rcol z wl wdu wdt g c r p f n d ==∗
    (∃ r' : nat, ireg_rcol z wl wdu wdt g c r' p f (S n) d)
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
  Lemma ireg_rcol_spend (bfl : bool) (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) :
    ireg_rcol z wl wdu wdt g c r p f (S n) d -∗ IcacheRef.runit bfl z ==∗
    ∃ r' : nat, ireg_rcol z wl wdu wdt g c r' p f n d.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & %Href) Hu".
    iDestruct (IcacheRef.link_runit_ge with "Hla Hu") as %Hge.
    destruct bfl; cbn in Hge.
    - destruct rc as [| rc0]; [lia |].
      iMod (IcacheRef.link_spend_runit true z wl wdu wdt g c r p f rc0
              with "Hla Hu") as "Hla".
      iModIntro. iExists r, rc0. iFrame "Hla". iPureIntro.
      exact (ireg_ref_ok_spend true r rc0 n c d Href).
    - destruct r as [| r0]; [lia |].
      iMod (IcacheRef.link_spend_runit false z wl wdu wdt g c r0 p f rc
              with "Hla Hu") as "Hla".
      iModIntro. iExists r0, rc. iFrame "Hla". iPureIntro.
      exact (ireg_ref_ok_spend false r0 rc n c d Href).
  Qed.

  (* ...AND THE PIN's OWN READER (§5'.3's disjunctive withdraw): a caller
     inside the region open reads [1 <= r] off its own PLAIN unit with
     [IcacheRef.link_runit_ge] and applies [ireg_ref_ok_unclaimed] to the
     clause.  Everything is borrowed; the conclusion is pure. *)
  Lemma ireg_rcol_unclaimed (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) :
    ireg_rcol z wl wdu wdt g c r p f n d -∗ IcacheRef.runit false z -∗
    ⌜c = None⌝.
  Proof.
    rewrite /ireg_rcol. iIntros "(%rc & Hla & %Href) Hu".
    iDestruct (IcacheRef.link_runit_ge with "Hla Hu") as %Hge. cbn in Hge.
    iPureIntro. exact (ireg_ref_ok_unclaimed r rc n c d Href Hge).
  Qed.

  (* ...AND ITS ALLOCATEDNESS TWIN, which is what idup's mint pays its type
     premise with: it holds its caller's own unit, at EITHER flavour, and
     needs no licence at all. *)
  Lemma ireg_rcol_alloc (bfl : bool) (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) :
    ireg_rcol z wl wdu wdt g c r p f n d -∗ IcacheRef.runit bfl z -∗
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
  Lemma ireg_rcol_mint_ok (bfl : bool) (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat)
      (d : dinode) :
    ireg_rcol z wl wdu wdt g c r p f n d -∗ IcacheRef.runit bfl z -∗
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

  Definition ireg_slot (γi : gname) (z : Z) (d : dinode) : iProp Σ :=
    ((∃ (wl wdu wdt g r : nat) (c : ctyUR)
        (p : option (dfrac_agreeR (leibnizO Z))) (f : frzUR) (n : nat),
        ireg_rcol z wl wdu wdt g c r p f n d
        ∗ ⌜ireg_link_ok d (wl + wdu + wdt)⌝
        ∗ ⌜ireg_root_ok z d (wl + wdu + wdt)⌝
        ∗ ⌜ireg_dir_ok d (wdu + wdt)⌝
        ∗ ⌜ireg_dir_wl0 d wl⌝
        ∗ ⌜ireg_par_ok wdt p⌝
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
        ∗ ireg_fsh f
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
        ∗ ((((⌜ireg_in d⌝ ∗ z ↪[γi] d)
             ∨ (⌜ireg_marked_ok c d⌝ ∗ imark γi z))
            ∗ (∃ ge gr, reg_full z ge gr))
           ∨ (⌜bv_unsigned (di_type d) = 0⌝ ∗ z ↪[γi] d
              ∗ (∃ ge gr, reg_half z ge gr) ∗ region_pending z)))
     ∗ ireg_ep z d)%I.

  Global Instance ireg_slot_timeless γi z d : Timeless (ireg_slot γi z d).
  Proof. rewrite /ireg_slot. apply _. Qed.

  (* the ledger's authority at one slot, held apart from the arm.  Both the
     ordinary flush and the free re-park the arm unchanged in SHAPE and
     move only the record, so every arm move below is stated by giving the
     new record and the new authority separately. *)
  Lemma ireg_slot_intro γi z d wl wdu wdt g c r p f n :
    ireg_link_ok d (wl + wdu + wdt) ->
    ireg_root_ok z d (wl + wdu + wdt) ->
    ireg_dir_ok d (wdu + wdt) ->
    ireg_dir_wl0 d wl ->
    ireg_par_ok wdt p ->
    ireg_claim_ok c f d ->
    ireg_frz_ok f n d ->
    ireg_rcol z wl wdu wdt g c r p f n d -∗
    ireg_ep z d -∗
    (⌜c = None⌝ ∨ ireg_open) -∗
    icnt_half z n -∗
    ireg_fsh f -∗
    ireg_frzc z f -∗
    ((((⌜ireg_in d⌝ ∗ z ↪[γi] d)
       ∨ (⌜ireg_marked_ok c d⌝ ∗ imark γi z))
      ∗ (∃ ge gr, reg_full z ge gr))
     ∨ (⌜bv_unsigned (di_type d) = 0⌝ ∗ z ↪[γi] d
        ∗ (∃ ge gr, reg_half z ge gr) ∗ region_pending z)) -∗
    ireg_slot γi z d.
  Proof.
    intros Hok Hrt Hdir Hwl0 Hpar Hclm Hfrz.
    iIntros "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm".
    rewrite /ireg_slot.
    iFrame "Hep".
    iExists wl, wdu, wdt, g, r, c, p, f, n. iSplitL "Hla"; [iExact "Hla" |].
    iSplitR; [iPureIntro; exact Hok |].
    iSplitR; [iPureIntro; exact Hrt |].
    iSplitR; [iPureIntro; exact Hdir |].
    iSplitR; [iPureIntro; exact Hwl0 |].
    iSplitR; [iPureIntro; exact Hpar |].
    iSplitL "Hdisj"; [iExact "Hdisj" |].
    iSplitL "Hcnt"; [iExact "Hcnt" |].
    iSplitR; [iPureIntro; exact Hclm |].
    iSplitR; [iPureIntro; exact Hfrz |].
    iSplitL "Hfdisj"; [iExact "Hfdisj" |].
    iSplitL "Hfrcp"; [iExact "Hfrcp" | iExact "Harm"].
  Qed.

  Definition ireg_blk (γi : gname) (γfs : fs_names) (inodestart : Z)
      (m : gmap Z dinode) (bi : nat) : iProp Σ :=
    (∃ ds : list dinode,
       ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗
       fsblock (fs_bytes γfs) (inodestart + Z.of_nat bi) (diblk_bytes ds) ∗
       [∗ list] i ∈ seq 0 16,
         ireg_slot γi (16 * Z.of_nat bi + Z.of_nat i)%Z (ds !!! i))%I.

  (* OPTION A (option 1, in-body): the per-inum registry, held INSIDE the
     region invariant so [ireg_claim_au] refutes the pending arm from the open
     it already does -- no [ireg_reg_inv] premise, no syscall-cone re-spec.
     Every inum's whole [reg_full] rides here; boot registers all of them.
     Timeless body, so the accessors' [>] strip is unaffected; carried through
     UNCHANGED by every accessor except [ireg_claim_au] (reads a copy to
     refute) and, at walk time, the deposit (splits [reg_full]->[reg_half]). *)
  (* OPTION A (walk reg-fold): the registry conjunct in [ireg_body] is now the
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

  Definition ireg_inv (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) : iProp Σ :=
    (inv iregN (ireg_body γi γfs inodestart nib) ∗
     ireg_bytes γfs)%I.

  Global Instance ireg_inv_persistent γi γfs inodestart nib :
    Persistent (ireg_inv γi γfs inodestart nib).
  Proof. apply _. Qed.

  Lemma ireg_inv_bytes γi γfs inodestart nib :
    ireg_inv γi γfs inodestart nib -∗ fs_bytes_any γfs.
  Proof. iIntros "[_ $]". Qed.

  (* [logN] and [iregN] are distinct namespaces, so a reader that has
     [iregN] open may still open the byte view. *)
  Lemma logN_iregN_disj : (↑logN : coPset) ## ↑iregN.
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
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iDestruct "Hrb" as (home) "#Hbinv".
    assert (HlogI : (↑logN : coPset) ⊆ E ∖ ↑iregN)
      by (apply subseteq_difference_r; [apply logN_iregN_disj | exact HEl]).
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & Hsl)".
    rewrite -(ireg_bi_iblock inum inodestart) -Hb.
    iMod (fs_bytes_agree (E ∖ ↑iregN) (fs_bytes γfs) (fs_cache γfs) home
            b (diblk_bytes ds) bsl HlogI with "Hbinv Hfsb Hhalf")
      as "(%Hbytes & Hfsb & Hhalf)".
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
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
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
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iEval (rewrite Hdeq) in "Hep".
    iMod (ireg_ep_mint (bv_unsigned inum) dn icfg_log e0 eq_refl Hnz
            with "Hep Hlb0") as "[Hep #Hobs]".
    iEval (rewrite -Hdeq) in "Hep".
    iMod ("Hclose" with "[Ha Hreg Hfsb Hla Hep Harm Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Hla Hep Harm Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hla Hep Harm Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
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
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
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
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iEval (rewrite Hdeq) in "Hep".
    iDestruct (ireg_ep_use (bv_unsigned inum) dn icfg_log e0 eq_refl Hz He0
                 with "Hep Hobs") as "[Hep #Hwit]".
    iEval (rewrite -Hdeq) in "Hep".
    iMod ("Hclose" with "[Ha Hreg Hfsb Hla Hep Harm Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Hla Hep Harm Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hla Hep Harm Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
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
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iDestruct "Hrb" as (home) "#Hbinv".
    assert (HlogI : (↑logN : coPset) ⊆ E ∖ ↑iregN)
      by (apply subseteq_difference_r; [apply logN_iregN_disj | exact HEl]).
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib bi Hbi with "Hblks")
      as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & Hsl)".
    iMod (fs_bytes_agree (E ∖ ↑iregN) (fs_bytes γfs) (fs_cache γfs) home
            (inodestart + Z.of_nat bi) (diblk_bytes ds) bsl HlogI
            with "Hbinv Hfsb Hhalf") as "(%Hbytes & Hfsb & Hhalf)".
    iMod ("Hclose" with "[Ha Hreg Hfsb Hsl Hback]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
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
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ dinode_at γi inum dn').
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hnl) "#Hinv Hdn".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
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
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    (* THE ARM IS THE OUT ONE: the region cannot also hold this inum's
       fragment, because the caller does ([dinode_at_excl]). *)
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(_ & Hpz & _)"; iExFalso; iApply (dinode_at_excl with "Hpz Hdn")].
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
    rewrite Hdeq in Hlok. rewrite Hdeq in Hrt. rewrite Hdeq in Hdir.
    rewrite Hdeq in Hwl0. rewrite Hdeq in Hclm. rewrite Hdeq in Hfrz.
    (* (L1) RIDES ON [di_nlink_stable]'s first conjunct: [nlink] does not
       move across an ordinary flush, so the cap the ledger already had is
       the SAME cap -- one rewrite, no arithmetic.  (L3) is vacuous -- an
       ordinary flush writes a nonzero type, which is [Hnz], and the
       clearing flush leaves through [ireg_free_au] instead. *)
    assert (Hlok' : ireg_link_ok dn' (wl + wdu + wdt)).
    { rewrite /ireg_link_ok (proj1 Hnl).
      split_and!;
        [ exact (proj1 Hlok)
        | intros H0; exfalso; exact (Hnz H0)
        | exact (ireg_link_ok_short dn _ Hlok) ]. }
    (* THE ROOT CLAUSE RIDES ON THE SAME EQUALITY: an ordinary flush moves
       neither the count nor the ledger, so the strict cap is the SAME cap.
       This is the mover [ireg_write_au] may demand [di_nlink_stable] for
       (its comment above), read once more at the root. *)
    assert (Hrt' : ireg_root_ok (bv_unsigned inum) dn' (wl + wdu + wdt))
      by exact (ireg_root_ok_stable _ dn dn' _ (proj1 Hnl) Hrt).
    (* THE CLAIM PIN IS VACUOUS HERE (iclaim-ledger.md §2.4).  The caller's
       own [dinode_at] put this open on the MARKED arm, whose clause says
       [cl = None] -- so a byte-writing mover owes the pin nothing, and its
       premise list does not move. *)
    assert (Hclm' : ireg_claim_ok cl fz dn')
      by (rewrite (proj2 Ht2); exact I).

    (* (T1) RIDES ON [di_type_stable] PLUS [Hnz]: the ordinary flush's LEFT
       disjunct (the type going to zero) is dead here, so the type is
       literally the same halfword and the clause is carried, not re-proved.
       [wd] does not move at all. *)
    assert (Hty' : di_type dn' = di_type dn)
      by (destruct Hstab as [H0 | Heq]; [exfalso; exact (Hnz H0) | exact Heq]).
    assert (Hdir' : ireg_dir_ok dn' (wdu + wdt))
      by exact (ireg_dir_ok_stable dn dn' (wdu + wdt) Hty' Hdir).
    assert (Hwl0' : ireg_dir_wl0 dn' wl)
      by exact (ireg_dir_wl0_stable dn dn' wl Hty' Hwl0).
    (* THE FREEZE PIN IS FREE HERE (iclaim-ledger.md §3.1's cost table, row
       one): the ordinary flush moves neither of the record fields the pin
       reads -- [di_nlink_stable]'s first conjunct is the [nlink] equation
       and [Hty'] is the [type] one -- so the clause is CARRIED, not
       re-proved, at whichever phase the column happens to be in. *)
    assert (Hfrz' : ireg_frz_ok fz cn dn')
      by exact (ireg_frz_ok_stable fz cn dn dn' (proj1 Hnl) Hty' Hfrz).
    (* THE RECEIPT TRAVELS FOR FREE (fs-log.md §G.17): [Hnl]'s first
       conjunct says nlink does not move across an ordinary flush, so a zero
       at [dn'] is the same zero at [dn] and the old receipt IS the new one,
       at the same [v]. *)
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { rewrite Hdeq (proj1 Hnl). intros H0. exact H0. }
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    (* re-park the block at the flushed bytes, re-coupled at m' *)
    iMod ("Hclose" with "[Ha Hreg Hfsb' Hmk Hla Hep Hslback Hback Hrf Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hmk Hla Hep Hslback Hrf Hcnt Hfdisj Hfrcp]").
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
      iApply ("Hslback" $! dn' with "[Hmk Hla Hep Hrf Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      (* RULING R: an ordinary flush keeps the type, so the r column's clause
         is CARRIED across the record move exactly as (T1) and the freeze pin
         are -- one line, no premise on the mover. *)
      iEval (rewrite Hdeq) in "Hla".
      iDestruct (ireg_rcol_stable (bv_unsigned inum) wl wdu wdt gl cl rl pl fz
                   cn dn dn' Hty' with "Hla") as "Hla".
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl wdu wdt gl cl rl pl fz cn
                Hlok' Hrt' Hdir' Hwl0' Hpar Hclm' Hfrz'
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp").
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
      (ds : list dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    bv_unsigned (di_type (ds !!! islot inum)) = 0 ->
    fresh_shape dn' ->
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
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       (* THE CLAIM (§2.4): the c column goes [None -> Some] in the same
          ghost step that writes the box, and the exclusive fragment is
          ialloc's receipt.  It is spent at create's fill
          ([ireg_withdraw]). *)
       ={E ∖ ↑iregN, E}=∗ iclaim (bv_unsigned inum) (di_type dn')).
  Proof.
    iIntros (HE Hin Hwf Ht0 Hfr) "#Hinv #Hopen".
    pose proof (islot_lt inum) as Hsl.
    pose proof (fresh_shape_wf dn' Hfr) as Hdn'.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
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
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
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
    iAssert ((bv_unsigned inum ↪[γi] (ds !!! islot inum))
             ∗ (∃ ge gr, reg_full (bv_unsigned inum) ge gr))%I
      with "[Harm]" as "[Hfrg Hrf]".
    { iDestruct "Harm" as "[[Harm Hrf] | Hpend]".
      - (* non-pending: fragment from the IN arm + the arm's own reg_full;
           a type-0 record refutes the marked sub-arm ([Ht2 Ht0]). *)
        iDestruct "Harm" as "[[_ Hfrg] | [%Ht2 _]]".
        + iFrame "Hfrg Hrf".
        + iExFalso. iPureIntro. exact (proj1 Ht2 Ht0).
      - (* PENDING: recombine the arm's structural [reg_half] with
           [region_pending]'s half back into [reg_full] -- the coordinate, now
           entirely from the slot's own arm (no registry lookup). *)
        iDestruct "Hpend" as "(_ & Hfrg & Hrh1 & Hrp)".
        iDestruct "Hrh1" as (ge1 gr1) "Hrh1".
        iDestruct "Hrp" as (ge2 gr2) "[Hrh2 _]".
        iDestruct (reg_half_agree with "Hrh1 Hrh2") as %[-> ->].
        iDestruct (reg_join with "Hrh1 Hrh2") as "Hrf".
        iFrame "Hfrg". iExists ge2, gr2. iExact "Hrf". }
    (* (L3) AT THE CLAIMED SLOT: the record the caller's buffer showed
       type-0 has [nlink = 0], so (L1) collapses to [w = 0] -- i.e. no live
       directory record names the inum ialloc is about to claim -- and the
       fresh record's own (L1) is then free whatever [nlink] it carries.
       THIS is the step §20.13 called the knot: it needs (L3) as an
       invariant, and (L3) is what iput's free had to establish. *)
    assert (Hw0 : (wl + wdu + wdt = 0)%nat)
      by exact (ireg_link_ok_free (ds !!! islot inum) _ Hlok Ht0).
    (* ...AND THE SUM COLLAPSING IS WHAT MAKES (T1) VACUOUS AT THE CLAIM: a
       type-0 record has no paid record of EITHER flavour naming it, so the
       claim box ialloc writes starts at [wd = 0] and owes nothing. *)
    destruct (ireg_sum_zero3 wl wdu wdt Hw0) as (Hz1 & Hz2 & Hz3).
    assert (Hlok' : ireg_link_ok dn' (wl + wdu + wdt)).
    { rewrite Hz1 Hz2 Hz3. split_and!;
        [ lia
        | intros H0; exfalso; exact (proj1 Hfr H0)
        | rewrite (fresh_shape_nlink dn' Hfr); lia ]. }
    assert (Hdir' : ireg_dir_ok dn' (wdu + wdt))
      by (rewrite Hz2 Hz3; exact (ireg_dir_ok_zero dn')).
    assert (Hwl0' : ireg_dir_wl0 dn' wl)
      by (rewrite Hz1; exact (ireg_dir_wl0_zero dn')).
    (* THE ROOT IS NOT CLAIMABLE (§20.4's (f) row, fs-fragments §3.6).  The
       claim would write a [fresh_shape] record, whose count is ZERO, so the
       strict clause could not be re-established at the root -- and it does
       not have to be: the caller's buffer showed [di_type = 0] at the OLD
       record, (L3) turns that into [di_nlink = 0], and the old clause
       refutes the root there outright.  **ialloc can never claim the root**,
       proved inside the region with no premise on the mover. *)
    assert (Hnr : bv_unsigned inum <> ireg_root)
      by exact (ireg_root_ok_ne _ (ds !!! islot inum) _ Hrt
                  (proj1 (proj2 Hlok) Ht0)).
    assert (Hrt' : ireg_root_ok (bv_unsigned inum) dn' (wl + wdu + wdt))
      by exact (ireg_root_ok_nonroot _ dn' _ Hnr).
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
    iMod (link_mint_claim _ _ _ _ _ _ _ _ _ (di_type dn') with "Hla") as "[Hla Hcl]".
    (* RULING R's PIN, ESTABLISHED (§5'.2, landed by 7a-wire): (R2) at the
       OLD, type-0 record collapses both r columns, so (R3) holds at the box
       the claim creates and (R2) itself goes vacuous there against
       [fresh_shape]'s nonzero type.  Both facts are already in hand at this
       line ([Ht0] is the mover's own premise, [Hfr] its other). *)
    iDestruct (ireg_rcol_intro (bv_unsigned inum) wl wdu wdt gl
                 (Some (Excl (di_type dn'))) rl pl fz cn rcl dn'
                 (ireg_ref_ok_claim_mint rl rcl cn (ds !!! islot inum) dn'
                    (Some (Excl (di_type dn'))) Href Ht0 (proj1 Hfr))
                 with "Hla") as "Hla".
    (* the new pin: the claim box IS the [fresh_shape] record just written,
       and the column it is written at is the unfrozen one *)
    assert (Hclm' : ireg_claim_ok (Some (Excl (di_type dn'))) fz dn')
      by (split_and!; [exact Hfr | exact Hfz0 | reflexivity]).
    assert (Hfrz' : ireg_frz_ok fz cn dn')
      by exact (ireg_frz_ok_of_off fz cn dn' Hfz0).
    (* the claimed slot's old record is type-0, so (L3) already gives it
       [nlink = 0] and the receipt carries unconditionally *)
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { intros _. exact (proj1 (proj2 Hlok) Ht0). }
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hfrg") as %Hm.
    iMod (ghost_map_update dn' with "Ha Hfrg") as "[Ha Hfrg]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hreg Hfsb' Hfrg Hla Hep Hslback Hback Hrf Hcnt Hfdisj Hfrcp]") as "_"; last first.
    { iModIntro. iExact "Hcl". }
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hfrg Hla Hep Hslback Hrf Hcnt Hfdisj Hfrcp]").
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
      iApply ("Hslback" $! dn' with "[Hfrg Hla Hep Hrf Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl wdu wdt gl
                (Some (Excl (di_type dn'))) rl pl fz cn
                Hlok' Hrt' Hdir' Hwl0' Hpar Hclm' Hfrz'
                with "Hla Hep [] Hcnt Hfdisj Hfrcp").
      { iRight. iExact "Hopen". }
      iLeft. iSplitR "Hrf"; [iLeft; iSplitR; [iPureIntro; right; exact Hfr | iExact "Hfrg"] | iExact "Hrf"]. }
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
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) (rg : bool) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bv_unsigned (di_nlink dn) = 0 ->
    bv_unsigned (di_type dn) <> 0 ->
    ireg_inv γi γfs inodestart nib -∗
    ireg_regime rg -∗
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
    iIntros (HE Hin Hnl0 Hty0) "#Hinv Hsh Hdn Hoff Hhalf Hmir".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    (* THE FRAGMENT PUTS THIS OPEN ON THE MARKED ARM, and that is where the
       claim clause is paid: [ireg_marked_ok] says [cl = None]. *)
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(_ & Hpz & _)"; iExFalso; iApply (dinode_at_excl with "Hpz Hdn")].
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
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
    iMod (link_freeze_step _ _ _ _ _ _ _ _ FrzOff (FrzPre rg) with "Hla Hoff")
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
    iMod ("Hclose" with "[Ha Hreg Hfsb Hmk Hrf Hla Hep Hslback Hback Hcnt Hsh Hmr]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Hmk Hrf Hla Hep Hslback Hcnt Hsh Hmr]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hmk Hrf Hla Hep Hcnt Hsh Hmr]").
      rewrite Hkey.
      (* RULING R: the freeze moves the f column only -- neither r column,
         neither the count nor the record -- so the clause rides verbatim. *)
      iDestruct (ireg_rcol_intro (bv_unsigned inum) wl wdu wdt gl cl rl pl
                   (Some (Excl (FrzPre rg))) 1%nat rcl (ds !!! islot inum) Href
                   with "Hla") as "Hla".
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl (Some (Excl (FrzPre rg))) 1%nat
                Hlok Hrt Hdir Hwl0 Hpar Hclm' Hfrz'
                with "Hla Hep Hdisj Hcnt [Hsh] [Hmr]").
      { iApply (ireg_fsh_pre rg with "Hsh"). }
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
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (ireg_rcol_freeze_agree with "Hla Hfz") as %->.
    iDestruct "Hfrcp" as "[Hrc Hmr]".
    iDestruct "Hmr" as (b0) "[Hmr %Hmok]".
    iDestruct (frzm_agree with "Hmr Hmir") as %<-.
    assert (Hiff : b0 = frz_ispre ph) by exact Hmok.
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hrc Hmr]")
      as "_".
    { iNext. iExists mrg. iFrame "Ha Hreg".
      iApply ("Hback" $! mrg with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hrc Hmr]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hrc Hmr]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl (Some (Excl ph)) cn
                Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj [Hrc Hmr] Harm").
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
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
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
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (mrg) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart mrg nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (ireg_rcol_freeze_agree with "Hla Hfz") as %->.
    iDestruct (icnt_agree with "Hcnt Hcnth") as %->.
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hfrcp]")
      as "_".
    { iNext. iExists mrg. iFrame "Ha Hreg".
      iApply ("Hback" $! mrg with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hfrcp]");
        [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl (Some (Excl ph)) n
                Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hfz Hcnth".
    iExists (ds !!! islot inum). iPureIntro. exact Hfrz.
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
      (ds : list dinode) (rg : bool) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') = 0 ->
    di_nlink_stable dn' dn ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    (* THE FREEZE, RETIRED IN THE SAME MOVE (iclaim-ledger.md §3.1, RULING
       A's mover table).  This is the one mover that writes a type-0 record
       over a slot the pin constrains, so with the pin's type conjunct landed
       it can no longer re-park an untouched f column: it takes the
       [FrzPost] token the walk is holding and steps the column back to
       [FrzOff], so the pin's post arm DISSOLVES exactly as the type goes to
       zero.  The token comes back as [ifreeze_off], which is what the pool
       bundle wants ([IcacheEscrow]'s free arm).
       IT IS THE DEPOSIT'S PRIVATE MOVER NOW.  [SpecIupdate] narrowed to
       [di_type dn' <> 0] (§3.1), which deletes generic iupdate's free
       branch; the only type-0 write left in the reordered kernel is the
       off-lock ifree, and that goes through [EscrowDeposit] -- where the
       token is in hand. *)
    ifreeze_post rg (bv_unsigned inum) -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ imark γi (bv_unsigned inum)
                          ∗ ifreeze_off (bv_unsigned inum)).
  Proof.
    iIntros (HE Hin Hwf Hdn' Hz Hnl) "#Hinv Hdn Hfz".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
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
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(_ & Hpz & _)"; iExFalso; iApply (dinode_at_excl with "Hpz Hdn")].
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    rewrite Hdeq in Hlok. rewrite Hdeq in Hrt.
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
    { rewrite -(proj1 Hnl). exact Hnl0'. }
    assert (Hw0 : (wl + wdu + wdt = 0)%nat)
      by exact (ireg_wle_zero (bv_unsigned (di_nlink dn)) _ (proj1 Hlok) Hnl0).
    (* ...at BOTH flavours, which is the widened form of the same sentence:
       at the instant an inode is freed no live directory record names it,
       whatever its namer knew about its type. *)
    destruct (ireg_sum_zero3 wl wdu wdt Hw0) as (Hz1 & Hz2 & Hz3).
    assert (Hlok' : ireg_link_ok dn' (wl + wdu + wdt)).
    { rewrite Hz1 Hz2 Hz3.
      split_and!; [lia | intros _; exact Hnl0' | rewrite Hnl0'; lia]. }
    assert (Hdir' : ireg_dir_ok dn' (wdu + wdt))
      by (rewrite Hz2 Hz3; exact (ireg_dir_ok_zero dn')).
    assert (Hwl0' : ireg_dir_wl0 dn' wl)
      by (rewrite Hz1; exact (ireg_dir_wl0_zero dn')).
    (* THE ROOT IS NOT FREEABLE, and it is the SAME two steps as the claim's
       (§20.4's (f) row).  [Hnl0] is the count iput tested at +0x40 and found
       zero; the old clause refutes the root at any such record.  So the free
       does not have to re-establish a strict cap over a zero -- **iput can
       never free the root** -- and again no premise on the mover, no
       obligation on the walk. *)
    assert (Hnr : bv_unsigned inum <> ireg_root)
      by exact (ireg_root_ok_ne _ dn _ Hrt Hnl0).
    assert (Hrt' : ireg_root_ok (bv_unsigned inum) dn' (wl + wdu + wdt))
      by exact (ireg_root_ok_nonroot _ dn' _ Hnr).
    (* THE CLAIM PIN IS VACUOUS HERE (iclaim-ledger.md §2.4): the caller's
       own [dinode_at] put this open on the MARKED arm, whose clause says
       [cl = None]. *)
    assert (Hclm' : ireg_claim_ok cl (Some (Excl FrzOff)) dn')
      by (rewrite (proj2 Ht2); exact I).
    (* THE RETIRE (§3.1).  The token pins the column at [FrzPost] and the
       step hands it back at [FrzOff]; the pin at the type-0 record it is
       about to park is then vacuous, which is the whole reason the mover
       takes the token rather than a premise. *)
    iDestruct (ireg_rcol_freeze_agree with "Hla Hfz") as %->.
    (* RULING R's (R2), PAID AT THE ONE MOVER THAT WRITES A ZERO TYPE
       (iclaim-ledger.md §5'.2's "all units die at the free's count-0",
       stated).  The walk's [FrzPost] token pins the in-core count at ZERO
       through the freeze pin, and (R1) -- [r + rc <= n] -- turns that into
       [r = rc = 0].  So the clause at the type-0 record the free is about to
       park is the all-zero one, and the mover owes NOTHING new: no premise,
       no token beyond the [ifreeze_post] it already takes.  This is the
       eviction-accounting tripwire §5'.4 flagged, and it closes on the pin
       the ledger already carried. *)
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    assert (Hcn0 : cn = 0%nat) by exact (proj2 (proj2 Hfrz)).
    (* ...and the pay-off line: the walk's [FrzPost] token pins the in-core
       count at ZERO ([Hcn0]) and (R1) collapses both r columns, so the
       clause at the type-0 record this mover parks is [ireg_ref_ok_zero]. *)
    destruct (ireg_ref_ok_count0 rl rcl cn cl (ds !!! islot inum) Href Hcn0)
      as [Hrl0 Hrcl0].
    assert (Href0 : forall d0 : dinode, ireg_ref_ok rl rcl cn cl d0)
      by (intros d0; rewrite Hrl0 Hrcl0; exact (ireg_ref_ok_zero cn cl d0)).
    iMod (link_freeze_step _ _ _ _ _ _ _ _ (FrzPost rg) FrzOff with "Hla Hfz")
      as "[Hla Hoff]".
    assert (Hfrz' : ireg_frz_ok (Some (Excl FrzOff)) cn dn')
      by exact (ireg_frz_ok_off cn dn').
    (* the free writes a zero over a zero: [Hnl0] above IS the receipt's
       antecedent already discharged at the old record (fs-log.md §G.17) *)
    assert (Hzm : bv_unsigned (di_nlink dn') = 0 ->
                  bv_unsigned (di_nlink (ds !!! islot inum)) = 0).
    { intros _. rewrite Hdeq. exact Hnl0. }
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    (* THE RECEIPT RIDES THROUGH: neither the old column ([FrzPost]) nor the
       new one ([FrzOff]) is [FrzPre], so the slot's clause is on its
       [frzown] arm both sides and the deposit never touches it. *)
    iDestruct (ireg_frzc_off_acc (bv_unsigned inum) (Some (Excl (FrzPost rg)))
                 ltac:(reflexivity) with "Hfrcp") as "[Hrcpt Hmr]".
    iMod ("Hclose" with "[Ha Hreg Hfsb' Hdn Hla Hep Hslback Hback Hrf Hcnt Hrcpt Hmr]") as "_".
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hdn Hla Hep Hslback Hrf Hcnt Hrcpt Hmr]").
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
      iApply ("Hslback" $! dn' with "[Hdn Hla Hep Hrf Hcnt Hrcpt Hmr]").
      rewrite Hkey.
      iDestruct (ireg_rcol_intro (bv_unsigned inum) wl wdu wdt gl cl rl pl
                   (Some (Excl FrzOff)) cn rcl dn' (Href0 dn')
                   with "Hla") as "Hla".
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl wdu wdt gl cl rl pl
                (Some (Excl FrzOff)) cn
                Hlok' Hrt' Hdir' Hwl0' Hpar Hclm' Hfrz'
                with "Hla Hep Hdisj Hcnt [] [Hrcpt Hmr]").
      { iApply ireg_fsh_off. }
      { iApply (ireg_frzc_off_intro (bv_unsigned inum) (Some (Excl FrzOff))
                  ltac:(reflexivity) with "Hrcpt Hmr"). }
      iLeft. iSplitR "Hrf"; [iLeft; iSplitR; [iPureIntro; left; exact Hz | iExact "Hdn"] | iExact "Hrf"]. }
    iModIntro. rewrite /ifreeze_off. iFrame "Hmk Hoff".
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
    | ClaimK ty => (iclaim z ty ∗ IcacheRef.runit_claim z)%I
    | PlainK    => IcacheRef.runit_plain z
    | ShotK ty  => IcacheRef.ity_shot g ty
    end.

  (* what comes BACK: the claim arm's pair CONVERTS into the plain unit, the
     plain unit is BORROWED and returned verbatim, and the one-shot is
     persistent so returning it costs nothing. *)
  Definition ireg_wd_back (o : ilkc) (g : gname) (z : Z) : iProp Σ :=
    match o with
    | ClaimK _ => IcacheRef.runit_plain z
    | PlainK   => IcacheRef.runit_plain z
    | ShotK ty => IcacheRef.ity_shot g ty
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
  Lemma inode_claimed_to_ClaimK `{!lockG Σ} ty k q dev inum g :
    IcacheRef.inode_claimed ty k q dev inum ⊢
    IcacheRef.inode_ref k q dev inum ∗
    ireg_wd_lic (ClaimK ty) g (bv_unsigned inum).
  Proof.
    rewrite /IcacheRef.inode_claimed /ireg_wd_lic.
    iIntros "($ & H2 & H3)". iFrame.
  Qed.

  (* ...and what the claim arm BUYS, which is the whole point of item 7 *)
  Definition ireg_wd_ty (o : ilkc) (d : dinode) : Prop :=
    match o with ClaimK ty => di_type d = ty | _ => True end.

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
    | ClaimK ty => filled = true /\ di_type d = ty
    | PlainK    => True
    | ShotK _   => filled = false
    end.

  (* the fill arm's payout, assembled: an index that CAN fill and that has
     just been through the withdraw has both halves of its post. *)
  Lemma ilk_post_fill (o : ilkc) (d : dinode) :
    ilk_fills o -> ireg_wd_ty o d -> ilk_post o true d.
  Proof.
    destruct o as [ty | | ty]; cbn.
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
    ireg_wd_back o gy (bv_unsigned inum) ∗
    dinode_at γi inum (ds !!! islot inum) ∗
    (b ↪[fs_cache γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE HEl Hfills Hin Hb Hwf Hbsl Hnz) "#Hinv Hmk Hcl Hhalf".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iDestruct "Hrb" as (home) "#Hbinv".
    assert (HlogI : (↑logN : coPset) ⊆ E ∖ ↑iregN)
      by (apply subseteq_difference_r; [apply logN_iregN_disj | exact HEl]).
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds0) "(>%Hwf0 & >%Hcp0 & >Hfsb & >Hsls)".
    rewrite -(ireg_bi_iblock inum inodestart) -Hb.
    iMod (fs_bytes_agree (E ∖ ↑iregN) (fs_bytes γfs) (fs_cache γfs) home
            b (diblk_bytes ds0) bsl HlogI with "Hbinv Hfsb Hhalf")
      as "(%Hbytes & Hfsb & Hhalf)".
    assert (Hds0 : ds0 = ds).
    { apply (diblk_bytes_inj ds0 ds Hwf0 Hwf). rewrite -Hbytes -Hbsl. reflexivity. }
    subst ds0.
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    (* the marker in the caller's hand refutes the OUT arm *)
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(%Ht0p & _ & _)"; exfalso; exact (Hnz Ht0p)].
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk']]"; last first.
    { iExFalso. iApply (imark_excl with "Hmk Hmk'"). }
    assert (Hfresh : fresh_shape (ds !!! islot inum))
      by (destruct Hin1 as [H0 | Hf]; [exfalso; exact (Hnz H0) | exact Hf]).
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
    iAssert (|==> ∃ rl' rcl' : nat,
                  link_auth (bv_unsigned inum) wl wdu wdt gl None rl' pl fz rcl'
                  ∗ ⌜ireg_ref_ok rl' rcl' cn None (ds !!! islot inum)⌝
                  ∗ ⌜ireg_wd_ty o (ds !!! islot inum)⌝
                  ∗ ireg_wd_back o gy (bv_unsigned inum))%I
      with "[Hla Hcl]" as ">(%rl' & %rcl' & Hla & %Href' & %Hty & Hwback)".
    { destruct o as [tyc | | tys];
        rewrite /ireg_wd_lic /ireg_wd_ty /ireg_wd_back.
      - iDestruct "Hcl" as "[Hcl Hru]".
        iDestruct (link_claim_agree with "Hla Hcl") as %Hcl.
        assert (Htyc : di_type (ds !!! islot inum) = tyc)
          by (rewrite Hcl in Hclm; exact (ireg_claim_ok_ty tyc fz _ Hclm)).
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
        rewrite /IcacheRef.runit_plain. iExact "Hplain".
      - iDestruct (IcacheRef.link_runit_ge false with "Hla Hcl") as %Hge.
        assert (Hc0 : cl = None)
          by exact (ireg_ref_ok_unclaimed rl rcl cn cl (ds !!! islot inum)
                      Href Hge).
        rewrite Hc0. iModIntro. iExists rl, rcl. iFrame "Hla".
        iSplitR;
          [iPureIntro;
           exact (ireg_ref_ok_unclaim rl rcl cn cl (ds !!! islot inum) Href) |].
        iSplitR; [iPureIntro; exact I | iExact "Hcl"].
      - destruct Hfills. }
    (* RULING R: the retire makes (R3) vacuous, and RULING C''s conversion
       moves the two r columns in step -- [Href'] above is the pin that
       carries it.  The record does not move either way. *)
    iDestruct (ireg_rcol_intro (bv_unsigned inum) wl wdu wdt gl None rl' pl fz cn
                 rcl' (ds !!! islot inum) Href'
                 with "Hla") as "Hla".
    assert (Hclm0 : ireg_claim_ok None fz (ds !!! islot inum))
      by exact (ireg_claim_ok_none _ _).
    iMod ("Hclose" with "[Ha Hreg Hfsb Hmk Hla Hep Hslback Hback Hrf Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Hmk Hla Hep Hslback Hrf Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      rewrite (ireg_bi_iblock inum inodestart) in Hb.
      rewrite Hb. iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Hmk Hla Hep Hrf Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl None rl' pl fz cn Hlok Hrt Hdir Hwl0 Hpar Hclm0 Hfrz
                with "Hla Hep [] Hcnt Hfdisj Hfrcp").
      { iLeft. iPureIntro. reflexivity. }
      iLeft. iSplitR "Hrf"; [iRight; iSplitR; [iPureIntro; split; [exact Hnz | reflexivity] | iExact "Hmk"] | iExact "Hrf"]. }
    iModIntro. iSplitR; [iPureIntro; exact Hfresh |].
    iSplitR; [iPureIntro; exact Hty |].
    iFrame "Hwback Hfr Hhalf".
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
      (ty : bv 16) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    iclaim (bv_unsigned inum) ty ={E}=∗
    False.
  Proof.
    iIntros (HE Hin) "#Hinv Hdn Hcl".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf0 & >%Hcp0 & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf0 as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    iDestruct (link_claim_agree with "Hla Hcl") as %Hcl.
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]".
    - iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk']]".
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

     FLAVOUR-INDEXED SINCE V1 (R6's [filled]-retrofit precedent), AND THE
     INDEX WIDENED BY V5' to [option (option Z)]: [None] is the landed
     mover verbatim -- same premises up to the one V4 adds, same payout,
     and [ireg_write_link] below is that instance; [Some None] mints the
     UNTAGGED [ilinkd] (V1's [Some tt]) and takes (T1) at the record it
     writes; [Some (Some pv)] is the TAGGED mint -- create's +0xc4, the
     one per-directory parent-record unit -- which allocates the parent
     REGISTER at [pv] and pays out BOTH halves ([ilinkdp] and [iparent]).
     Its legality premise is the pre-record's [nlink = 0] (the fresh
     child), which collapses every count and forces [p = None] through
     [ireg_par_ok] -- nothing is remembered from any earlier episode
     (V5' Correction 1).

     V4's PREMISE AT [fl = None]: a PLAIN mint must show its record is
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
  Lemma ireg_link_pin_read (pin : bool) (z : Z) (wl wdu wdt g : nat)
      (c : ctyUR) (r : nat)
      (p : option (dfrac_agreeR (leibnizO Z)))
      (f : frzUR) (n : nat) (d : dinode) :
    ireg_frz_ok f n d ->
    ireg_rcol z wl wdu wdt g c r p f n d -∗
    ireg_link_pin pin z d -∗
    ireg_rcol z wl wdu wdt g c r p f n d ∗
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

  Lemma ireg_write_link_fl (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) (fl : option (option Z)) (pin : bool) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
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
    (* (T1)'s MINT PREMISE, and it is what BOTH d flavours buy: the writer
       has just read the record and knows it is a directory.  Vacuous at
       [fl = None], where every landed caller stands. *)
    (forall od : option Z,
       fl = Some od -> bv_unsigned (di_type dn') = ireg_dir_ty) ->
    (* (T1')'s MINT PREMISE (V4): the mirror at the PLAIN flavour. *)
    (fl = None -> bv_unsigned (di_type dn') <> ireg_dir_ty) ->
    (* THE TAGGED MINT'S LEGALITY (V5'): the pre-record is the fresh
       child's, so its count is zero -- which is what collapses [wdt] and
       frees the register.  [fresh_shape_nlink] at the one caller. *)
    (forall pv : Z,
       fl = Some (Some pv) -> bv_unsigned (di_nlink dn) = 0) ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    (* THE FREEZE PIN'S PRICE, IN ITS RULING A-prime FORM (iclaim-ledger.md
       §3.9).  RULING A priced this as the pure left disjunct alone and IIIc
       proved that row FALSE at two of the mover's three sites: create's
       FRESH CHILD (whose pre-record's count is pinned at zero by
       [fresh_shape]) and sys_link's [ip->nlink++] (no guard, no [ilink] in
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
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗
       dinode_at γi inum dn' ∗ ilink_fl fl (bv_unsigned inum) ∗
       ireg_link_pin pin (bv_unsigned inum) dn).
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hbump Hgrd Hfl Hnfl Hflp)
            "#Hinv Hdn Hpin".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
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
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(_ & Hpz & _)"; iExFalso; iApply (dinode_at_excl with "Hpz Hdn")].
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    rewrite Hdeq in Hlok. rewrite Hdeq in Hrt. rewrite Hdeq in Hdir.
    rewrite Hdeq in Hwl0. rewrite Hdeq in Hclm. rewrite Hdeq in Hfrz.
    (* THE FREEZE IS REFUTED BEFORE ANYTHING ELSE HAPPENS (§3.1).  The new
       premise says the pre-record is NAMED; the pin says a mid-transition
       record is not; so the column reads [FrzOff] and the pin at the raised
       record is vacuous whatever [nlink] the mint writes. *)
    (* THE PIN'S TWO ROUTES TO THE SAME CONCLUSION (§3.9) -- see
       [ireg_link_pin_read] above.  Both the auth and the premise come back. *)
    iEval (rewrite Hdeq) in "Hla".
    iDestruct (ireg_link_pin_read pin (bv_unsigned inum) wl wdu wdt gl cl rl pl
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
    destruct (ireg_nlink_bump (di_nlink dn) (ireg_link_ok_short dn _ Hlok) Hgrd)
      as [Hstep Hshort].
    assert (Hnl : bv_unsigned (di_nlink dn') = bv_unsigned (di_nlink dn) + 1)
      by (rewrite Hbump; exact Hstep).
    assert (Hsh' : bv_unsigned (di_nlink dn') <= 32767)
      by (rewrite Hbump; exact Hshort).
    (* the type does not move ([ireg_write_au]'s step, verbatim): the LEFT
       disjunct of [di_type_stable] is dead against [Hnz]. *)
    assert (Hty' : di_type dn' = di_type dn)
      by (destruct Hstab as [H0 | Heq]; [exfalso; exact (Hnz H0) | exact Heq]).
    (* THE ONE GHOST STEP, FLAVOUR-INDEXED.  Whichever component the new
       fragment is filed in, the SUM rises by exactly one -- that is
       [Hsum], and it is the only thing (L1) and the root clause below
       read.  (T1) at the new d-sum is the d flavours' own obligation and
       rides at [None]; (T1') is the mirror -- [Hnfl] at [None], and at
       the d flavours [wl] does not move while the type premise keeps the
       clause's OLD reading usable; [ireg_par_ok] moves only on the
       TAGGED arm, where the collapsed counts free the register. *)
    iAssert (|==> ∃ (wl' wdu' wdt' : nat)
               (p' : option (dfrac_agreeR (leibnizO Z))),
               ⌜(wl' + wdu' + wdt')%nat = S (wl + wdu + wdt)⌝ ∗
               ⌜ireg_dir_ok dn' (wdu' + wdt')⌝ ∗
               ⌜ireg_dir_wl0 dn' wl'⌝ ∗
               ⌜ireg_par_ok wdt' p'⌝ ∗
               link_auth (bv_unsigned inum) wl' wdu' wdt' gl cl rl p' fz rcl ∗
               ilink_fl fl (bv_unsigned inum))%I
      with "[Hla]" as ">(%wl' & %wdu' & %wdt' & %p' & %Hsum & %Hdir' & %Hwl0' & %Hpar' & Hla & Hfrag)".
    { destruct fl as [[pv |] |].
      - (* the TAGGED mint: the fresh child's zero count collapses the
           slot and frees the register *)
        assert (Hnl0 : bv_unsigned (di_nlink dn) = 0)
          by exact (Hflp pv eq_refl).
        assert (Hw0 : (wl + wdu + wdt = 0)%nat)
          by exact (ireg_wle_zero (bv_unsigned (di_nlink dn)) _
                      (proj1 Hlok) Hnl0).
        destruct (ireg_sum_zero3 wl wdu wdt Hw0) as (Hz1 & Hz2 & Hz3).
        assert (Hp0 : pl = None) by exact (ireg_par_ok_wdt0 wdt pl Hpar Hz3).
        subst wl wdu wdt pl.
        iMod (link_mint_linkdp with "Hla") as "[Hla [Hdp Hip]]".
        iModIntro. iExists 0%nat, 0%nat, 1%nat, (Some (lreg pv)).
        iSplitR; [iPureIntro; lia |].
        iSplitR; [iPureIntro;
                  exact (ireg_dir_ok_intro dn' 1 (Hfl (Some pv) eq_refl)) |].
        iSplitR; [iPureIntro; exact (ireg_dir_wl0_zero dn') |].
        iSplitR; [iPureIntro; exact (ireg_par_ok_some pv) |].
        iSplitL "Hla"; [iExact "Hla" |].
        cbn. iSplitL "Hdp"; [iExact "Hdp" | iExact "Hip"].
      - (* the UNTAGGED d mint *)
        iMod (link_mint_linkd with "Hla") as "[Hla Hfrag]".
        iModIntro. iExists wl, (S wdu), wdt, pl. iFrame "Hla Hfrag".
        iPureIntro. split_and!; [lia | | | exact Hpar].
        + exact (ireg_dir_ok_intro dn' (S wdu + wdt) (Hfl None eq_refl)).
        + (* [wl] does not move, and the new record IS a directory, so the
             clause must say [wl = 0] -- which the OLD clause gives at the
             OLD record through the unchanged type *)
          intros Hty.
          apply Hwl0. rewrite -Hty'. exact Hty.
      - (* the PLAIN mint: (T1') is [Hnfl]'s vacuity, (T1) rides *)
        iMod (link_mint_link with "Hla") as "[Hla Hfrag]".
        iModIntro. iExists (S wl), wdu, wdt, pl. iFrame "Hla Hfrag".
        iPureIntro. split_and!; [lia | | | exact Hpar].
        + exact (ireg_dir_ok_stable dn dn' (wdu + wdt) Hty' Hdir).
        + exact (ireg_dir_wl0_intro dn' (S wl) (Hnfl eq_refl)). }
    (* (L1) GROWS ON BOTH SIDES AT ONCE: the count that pays for the new
       fragment is written in the same ghost step that mints it. *)
    assert (Hlok' : ireg_link_ok dn' (wl' + wdu' + wdt')).
    { rewrite Hsum. split_and!.
      - exact (ireg_wle_plus (bv_unsigned (di_nlink dn))
                 (bv_unsigned (di_nlink dn')) _
                 (di_nlink_nonneg dn) (proj1 Hlok) Hnl).
      - intros H0. exfalso. exact (Hnz H0).
      - exact Hsh'. }
    (* ...AND SO DOES THE ROOT'S STRICT CAP, for the same reason and in the
       same ghost step: [w] and [nlink] rise together, so a strict
       inequality is preserved with nothing to prove about WHICH inum this
       is.  mkdir's [dp->nlink++] at the root is exactly this case. *)
    assert (Hrt' : ireg_root_ok (bv_unsigned inum) dn' (wl' + wdu' + wdt')).
    { rewrite Hsum. exact (ireg_root_ok_bump _ dn dn' _ Hnl Hrt). }
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
    iDestruct (ireg_ep_mono (bv_unsigned inum) (ds !!! islot inum) dn' Hzm
                 with "Hep") as "Hep".
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hreg Hfsb' Hmk Hla Hep Hslback Hback Hrf Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hmk Hla Hep Hslback Hrf Hcnt Hfdisj Hfrcp]").
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
      iApply ("Hslback" $! dn' with "[Hmk Hla Hep Hrf Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iDestruct (ireg_rcol_intro (bv_unsigned inum) wl' wdu' wdt' gl cl rl p'
                   fz cn rcl dn'
                   (ireg_ref_ok_stable rl rcl cn cl dn dn' Hty' Href)
                   with "Hla") as "Hla".
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl' wdu' wdt' gl cl rl
                p' fz cn Hlok' Hrt' Hdir' Hwl0' Hpar' Hclm' Hfrz' with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp").
      iLeft. iSplitR "Hrf"; [iRight; iSplitR; [iPureIntro; split; [exact Hnz | exact (proj2 Ht2)] | iExact "Hmk"] | iExact "Hrf"]. }
    (* ...and the pin premise goes back out, unspent (§3.9's
       borrowed-and-returned). *)
    iModIntro. iFrame "Hdn Hfrag Hpin".
  Qed.

  (* THE PLAIN INSTANCE -- the landed mover, statement for statement.  Kept
     as its own lemma so that [ProofIupdate]'s and every future caller's
     shape is unchanged by the widening (the [wp_bmap_gen]/[wp_balloc_gen]
     pattern, applied one layer down). *)
  Lemma ireg_write_link (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    di_nlink dn' = add_vec (di_nlink dn : mword 16) (mword_of_int 1) ->
    di_nlink dn <> (mword_of_int 32767 : mword 16) ->
    (* V4's (T1') premise: a PLAIN mint's record is not a directory *)
    bv_unsigned (di_type dn') <> ireg_dir_ty ->
    (* §3.1's freeze-pin premise, relayed *)
    bv_unsigned (di_nlink dn) <> 0 ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗
       dinode_at γi inum dn' ∗ ilink (bv_unsigned inum)).
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hbump Hgrd Hnd Hnl0) "#Hinv Hdn".
    (* the relay pays RULING A-prime's PURE arm and drops the returned
       premise: this instance keeps its pure signature. *)
    iMod (ireg_write_link_fl E γi γfs inodestart nib inum dn dn' ds None false
            HE Hin Hwf Hdn' Hnz Hstab Hbump Hgrd
            ltac:(intros od Hc; discriminate Hc)
            ltac:(intros _; exact Hnd)
            ltac:(intros pv Hc; discriminate Hc)
            with "Hinv Hdn []") as (bsl') "[Hfsb Hwand]";
      [rewrite /ireg_link_pin; iPureIntro; exact Hnl0 |].
    iModIntro. iExists bsl'. iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    iMod ("Hwand" with "[//] Hfsb'") as "(Hdn & Hfr & _)".
    iModIntro. iSplitL "Hdn"; [iExact "Hdn" | iExact "Hfr"].
  Qed.

  (* ...and the d-FLAVOURED TWIN, whose mint premise is (T1) at the record
     the flush writes.  V1 lands it with NO caller: create's [dp->nlink++]
     at +0xc4 is where it will be established (V2), and this is the mover
     that establishment goes through. *)
  Lemma ireg_write_link_d (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    di_nlink dn' = add_vec (di_nlink dn : mword 16) (mword_of_int 1) ->
    di_nlink dn <> (mword_of_int 32767 : mword 16) ->
    bv_unsigned (di_type dn') = ireg_dir_ty ->
    (* §3.1's freeze-pin premise, relayed *)
    bv_unsigned (di_nlink dn) <> 0 ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗
       dinode_at γi inum dn' ∗ ilinkd (bv_unsigned inum)).
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hbump Hgrd Hty Hnl0) "#Hinv Hdn".
    iMod (ireg_write_link_fl E γi γfs inodestart nib inum dn dn' ds
            (Some None) false HE Hin Hwf Hdn' Hnz Hstab Hbump Hgrd
            ltac:(intros od _; exact Hty)
            ltac:(intros Hc; discriminate Hc)
            ltac:(intros pv Hc; discriminate Hc)
            with "Hinv Hdn []") as (bsl') "[Hfsb Hwand]";
      [rewrite /ireg_link_pin; iPureIntro; exact Hnl0 |].
    iModIntro. iExists bsl'. iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    iMod ("Hwand" with "[//] Hfsb'") as "(Hdn & Hfr & _)".
    iModIntro. iSplitL "Hdn"; [iExact "Hdn" | iExact "Hfr"].
  Qed.

  (* ...AND THE TAGGED INSTANCE (V5') -- create's +0xc4 child mint on the
     mkdir arm, the ONE producer of a parent-record unit.  The pre-record
     is the fresh child's ([fresh_shape_nlink]'s zero), which is both what
     makes the machine increment free to state and what frees the
     register.  It pays out the payment unit AND the payload half; the
     caller deposits the first in dp's payload at the name record and the
     second in the child's own payload as the [".."]-tie. *)
  Lemma ireg_write_link_p (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) (pv : Z) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    di_nlink dn' = add_vec (di_nlink dn : mword 16) (mword_of_int 1) ->
    di_nlink dn <> (mword_of_int 32767 : mword 16) ->
    bv_unsigned (di_type dn') = ireg_dir_ty ->
    bv_unsigned (di_nlink dn) = 0 ->
    (* NO LONGER VACUOUS (iclaim-ledger.md §3.9, RULING A-prime).  IIIc left
       this lemma carrying BOTH [Hnl0 : di_nlink dn = 0] (the fresh child's,
       from [fresh_shape_nlink]) and RULING A's [di_nlink dn <> 0] -- two
       contradictory premises, so the tagged mint was provable by refutation
       and said nothing.  A-prime deletes the second and pays the pin with
       the holder's freeze token instead, which is exactly the resource
       create is holding at +0xc4 (its [ilock(ip)] two instructions earlier
       handed it over).  Borrowed and returned. *)
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ifreeze_off (bv_unsigned inum) -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗
       dinode_at γi inum dn'
       ∗ ilinkdp (bv_unsigned inum) pv ∗ iparent (bv_unsigned inum) pv
       (* the token back, unspent *)
       ∗ ifreeze_off (bv_unsigned inum)).
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hbump Hgrd Hty Hnl0) "#Hinv Hdn Hoff".
    iMod (ireg_write_link_fl E γi γfs inodestart nib inum dn dn' ds
            (Some (Some pv)) true HE Hin Hwf Hdn' Hnz Hstab Hbump Hgrd
            ltac:(intros od _; exact Hty)
            ltac:(intros Hc; discriminate Hc)
            ltac:(intros pv' _; exact Hnl0)
            with "Hinv Hdn [Hoff]") as (bsl') "[Hfsb Hwand]";
      [rewrite /ireg_link_pin; iExact "Hoff" |].
    iModIntro. iExists bsl'. iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    iAssert (⌜bsl' = diblk_bytes ds⌝)%I as "Hb"; [iPureIntro; exact Hbytes |].
    iMod ("Hwand" with "Hb Hfsb'") as "(Hdn & Hfr & Hpin)".
    cbn. iDestruct "Hfr" as "[Hdp Hip]".
    (* at [pin = true] the premise that comes back IS the token *)
    iEval (rewrite /ireg_link_pin) in "Hpin". iRename "Hpin" into "Hoff".
    iModIntro.
    iSplitL "Hdn"; [iExact "Hdn" |].
    iSplitL "Hdp"; [iExact "Hdp" |].
    iSplitL "Hip"; [iExact "Hip" | iExact "Hoff"].
  Qed.

  (* [ip->nlink--; iupdate(ip)] -- sys_unlink's decrement, and THE ONLY
     nlink-LOWERING region write in the kernel (design §20.6).  It is the
     dual of [ireg_write_link]: the drop is paid for by CONSUMING one
     [ilink], so (L1) falls on both sides at once and no fragment is ever
     left stranded above the count that backs it.

     This is exactly why [ireg_write_au] may demand [di_nlink_stable]: the
     one writer that would violate it does not go through the ordinary
     flush at all.

     FLAVOUR-INDEXED SINCE V1, exactly as its dual: [fl = None] consumes
     [ilink] and is the landed mover verbatim ([ireg_write_unlink] below is
     that instance); [fl = Some tt] consumes [ilinkd].  The drop is ONE unit
     of the SUM either way, and no premise is added on EITHER arm -- the d
     flavour's (T1) obligation is DISCHARGED here rather than taken, because
     lowering [wd] only weakens the clause's antecedent
     ([ireg_dir_ok_le]). *)
  Lemma ireg_write_unlink_fl (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) (fl : option (option Z)) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    bv_unsigned (di_nlink dn) = bv_unsigned (di_nlink dn') + 1 ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ilink_fl fl (bv_unsigned inum) -∗
    |={E, E ∖ ↑iregN}=> ∃ (bsl' : list (bv 8)) (v : nat),
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
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
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ dinode_at γi inum dn').
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hnl) "#Hinv Hdn Hfrag".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
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
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (ireg_ep_open with "Hep") as (v) "[#Hvlb Hepback]".
    iModIntro.
    rewrite (ireg_bi_iblock inum inodestart).
    iExists (diblk_bytes ds0), v.
    iFrame "Hfsb Hvlb".
    iIntros (Hbytes) "Hrc Hfsb'".
    assert (Hds0 : ds0 = ds) by exact (diblk_bytes_inj ds0 ds Hwf0 Hwf Hbytes).
    subst ds0.
    iDestruct ("Hepback" $! dn' with "Hrc") as "Hep".
    iDestruct "Harm" as "[[Harm Hrf] | Hpend]"; [|iDestruct "Hpend" as "(_ & Hpz & _)"; iExFalso; iApply (dinode_at_excl with "Hpz Hdn")].
    iDestruct "Harm" as "[[%Hin1 Hfr] | [%Ht2 Hmk]]".
    { iExFalso.
      iApply (dinode_at_excl γi inum (ds !!! islot inum) dn with "Hfr Hdn"). }
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp0 (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    rewrite Hdeq in Hlok. rewrite Hdeq in Hrt. rewrite Hdeq in Hdir.
    rewrite Hdeq in Hwl0. rewrite Hdeq in Hclm. rewrite Hdeq in Hfrz.
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
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    (* the type does not move: [di_type_stable]'s LEFT disjunct is dead
       against [Hnz], so (T1) travels to the written record. *)
    assert (Hty' : di_type dn' = di_type dn)
      by (destruct Hstab as [H0 | Heq]; [exfalso; exact (Hnz H0) | exact Heq]).
    (* THE ONE GHOST STEP, FLAVOUR-INDEXED.  The caller's fragment forces
       ITS OWN component up by one, so the SUM is a successor whichever
       flavour was handed in -- [Hsum] -- and that successor is all (L1) and
       the root clause read.  (T1) at the new [wd'] is FREE on both arms:
       [None] does not move [wd] at all, and [Some tt] lowers it, which only
       weakens the antecedent. *)
    iAssert (|==> ∃ (wl' wdu' wdt' : nat)
               (p' : option (dfrac_agreeR (leibnizO Z))),
               ⌜S (wl' + wdu' + wdt')%nat = (wl + wdu + wdt)%nat⌝ ∗
               ⌜ireg_dir_ok dn' (wdu' + wdt')⌝ ∗
               ⌜ireg_dir_wl0 dn' wl'⌝ ∗
               ⌜ireg_par_ok wdt' p'⌝ ∗
               link_auth (bv_unsigned inum) wl' wdu' wdt' gl cl rl p' fz rcl)%I
      with "[Hla Hfrag]" as ">(%wl' & %wdu' & %wdt' & %p' & %Hsum & %Hdir' & %Hwl0' & %Hpar' & Hla)".
    { destruct fl as [[pv |] |]; cbn.
      - (* the TAGGED spend: both halves in, register reset (V5') *)
        iDestruct "Hfrag" as "[Hdp Hip]".
        iDestruct (link_wdt_ge with "Hla Hdp") as %[Hw1 _].
        destruct (ireg_par_ok_full wdt pl Hpar Hw1) as [Hwdt1 [pv0 Hpl]].
        (* the register's value IS the fragment's: half ≼ full agrees *)
        iDestruct (link_par_incl with "Hla Hip") as %Hinc.
        assert (Hpveq : pv0 = pv).
        { rewrite Hpl in Hinc.
          apply Some_included in Hinc.
          destruct Hinc as [Heqv | Hincl].
          - rewrite /lreg_half /lreg /to_frac_agree in Heqv.
            apply (inj2 to_dfrac_agree) in Heqv as [Hd _].
            apply leibniz_equiv in Hd. injection Hd as Hq.
            exfalso. vm_compute in Hq. discriminate Hq.
          - rewrite /lreg_half /lreg in Hincl.
            apply frac_agree_included_L in Hincl as [_ Ha].
            exact (eq_sym Ha). }
        subst pv0 wdt pl.
        iMod (link_spend_linkdp with "Hla Hdp Hip") as "Hla".
        iModIntro. iExists wl, wdu, 0%nat, None. iFrame "Hla". iPureIntro.
        split_and!; [lia | | | exact ireg_par_ok_none].
        + exact (ireg_dir_ok_stable dn dn' (wdu + 0)
                   Hty' (ireg_dir_ok_le dn (wdu + 1) (wdu + 0)
                           ltac:(lia) Hdir)).
        + exact (ireg_dir_wl0_stable dn dn' wl Hty' Hwl0).
      - (* the UNTAGGED d spend *)
        iDestruct (link_wd_ge with "Hla Hfrag") as %Hw1.
        destruct wdu as [| wdu0]; [exfalso; lia |].
        iMod (link_spend_linkd with "Hla Hfrag") as "Hla".
        iModIntro. iExists wl, wdu0, wdt, pl. iFrame "Hla". iPureIntro.
        split_and!; [lia | | | exact Hpar].
        + exact (ireg_dir_ok_stable dn dn' (wdu0 + wdt) Hty'
                   (ireg_dir_ok_le dn (S wdu0 + wdt) (wdu0 + wdt)
                      ltac:(lia) Hdir)).
        + exact (ireg_dir_wl0_stable dn dn' wl Hty' Hwl0).
      - (* the PLAIN spend: (T1') only strengthens downwards *)
        iDestruct (link_w_ge with "Hla Hfrag") as %Hw1.
        destruct wl as [| wl0]; [exfalso; lia |].
        iMod (link_spend_link with "Hla Hfrag") as "Hla".
        iModIntro. iExists wl0, wdu, wdt, pl. iFrame "Hla". iPureIntro.
        split_and!; [lia | | | exact Hpar].
        + exact (ireg_dir_ok_stable dn dn' (wdu + wdt) Hty' Hdir).
        + exact (ireg_dir_wl0_stable dn dn' wl0 Hty'
                   (ireg_dir_wl0_le dn (S wl0) wl0 ltac:(lia) Hwl0)). }
    (* ...and (L1) FALLS on both sides at once, which is what keeps a
       fragment from ever outliving the count that backs it. *)
    assert (Hle : (S (wl' + wdu' + wdt')
                   <= Z.to_nat (bv_unsigned (di_nlink dn)))%nat)
      by (rewrite -Hsum in Hlok; exact (proj1 Hlok)).
    assert (Hlok' : ireg_link_ok dn' (wl' + wdu' + wdt')).
    { split_and!.
      - exact (ireg_wle_succ (bv_unsigned (di_nlink dn))
                 (bv_unsigned (di_nlink dn')) _
                 (di_nlink_nonneg dn') Hle Hnl).
      - intros H0. exfalso. exact (Hnz H0).
      (* (L4) FALLS OUT OF THE UNLINK FOR FREE, and that asymmetry is the
         whole reason only the raising mover takes a premise: [Hnl] here
         reads [old = new + 1], so the new count is BELOW a count the
         invariant already bounded. *)
      - pose proof (ireg_link_ok_short _ _ Hlok). lia. }
    (* THE ROOT CLAUSE FALLS ON BOTH SIDES AT ONCE TOO, and THIS is the mover
       the chartered form ([1 <= di_nlink] alone) could not survive: it would
       need [2 <= di_nlink dn] and have only [1 <= di_nlink dn].  Strictness
       supplies the missing one from the ledger instead of from the walk --
       the root's slack is exactly the entry it does not have in a parent,
       and [dp->nlink--] can only ever spend a subdirectory's [".."].  No
       premise, and nothing for [sys_unlink]'s ["."]/[".."] guard to
       supply. *)
    assert (Hrt0 : ireg_root_ok (bv_unsigned inum) dn (S (wl' + wdu' + wdt')))
      by (rewrite Hsum; exact Hrt).
    assert (Hrt' : ireg_root_ok (bv_unsigned inum) dn' (wl' + wdu' + wdt'))
      by exact (ireg_root_ok_drop _ dn dn' _ Hnl Hrt0).
    (* THE CLAIM PIN IS VACUOUS HERE (iclaim-ledger.md §2.4): the caller's
       own [dinode_at] put this open on the MARKED arm, whose clause says
       [cl = None]. *)
    assert (Hclm' : ireg_claim_ok cl fz dn')
      by (rewrite (proj2 Ht2); exact I).
    assert (Hfrz' : ireg_frz_ok fz cn dn')
      by exact (ireg_frz_ok_of_off fz cn dn' Hfz0).

    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    iMod ("Hclose" with "[Ha Hreg Hfsb' Hmk Hla Hep Hslback Hback Hrf Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m'. iFrame "Ha Hreg".
      iApply ("Hback" $! m' with "[%] [Hfsb' Hmk Hla Hep Hslback Hrf Hcnt Hfdisj Hfrcp]").
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
      iApply ("Hslback" $! dn' with "[Hmk Hla Hep Hrf Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iDestruct (ireg_rcol_intro (bv_unsigned inum) wl' wdu' wdt' gl cl rl p'
                   fz cn rcl dn'
                   (ireg_ref_ok_stable rl rcl cn cl dn dn' Hty' Href)
                   with "Hla") as "Hla".
      iApply (ireg_slot_intro γi (bv_unsigned inum) dn' wl' wdu' wdt' gl cl rl
                p' fz cn Hlok' Hrt' Hdir' Hwl0' Hpar' Hclm' Hfrz' with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp").
      iLeft. iSplitR "Hrf"; [iRight; iSplitR; [iPureIntro; split; [exact Hnz | exact (proj2 Ht2)] | iExact "Hmk"] | iExact "Hrf"]. }
    iModIntro. iExact "Hdn".
  Qed.

  (* THE PLAIN INSTANCE -- the landed mover, statement for statement, so
     [ProofIupdate] and [DirLinks]' prose both keep their referent. *)
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
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
      log_epoch_lb icfg_log v ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       izrcpt (bv_unsigned inum) dn' v -∗
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ dinode_at γi inum dn').
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hnl) "#Hinv Hdn Hfrag".
    iApply (ireg_write_unlink_fl E γi γfs inodestart nib inum dn dn' ds None
              HE Hin Hwf Hdn' Hnz Hstab Hnl with "Hinv Hdn Hfrag").
  Qed.

  (* ...and the d-FLAVOURED TWIN.  No caller in V1: it is what V3's walk
     spends, and it exists now so the flavour is not one-way. *)
  Lemma ireg_write_unlink_d (E : coPset) (γi : gname) (γfs : fs_names)
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
    ilinkd (bv_unsigned inum) -∗
    |={E, E ∖ ↑iregN}=> ∃ (bsl' : list (bv 8)) (v : nat),
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
      log_epoch_lb icfg_log v ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       izrcpt (bv_unsigned inum) dn' v -∗
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ dinode_at γi inum dn').
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hnl) "#Hinv Hdn Hfrag".
    iApply (ireg_write_unlink_fl E γi γfs inodestart nib inum dn dn' ds
              (Some None) HE Hin Hwf Hdn' Hnz Hstab Hnl
              with "Hinv Hdn Hfrag").
  Qed.

  (* ...AND THE TAGGED INSTANCE (V5') -- the spend of a parent-record
     unit, and the REGISTER RESET.  Consumes BOTH halves at fraction one,
     so after this flush the inum's register is [None] and a later
     [ireg_write_link_p] at a reclaimed inum is legal with no memory of
     this episode (Correction 1).  Its two callers-to-be: sys_unlink's
     [ip->nlink--] on the T_DIR arm, and create's T_DIR [fail:] flush. *)
  Lemma ireg_write_unlink_p (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) (pv : Z) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    bv_unsigned (di_type dn') <> 0 ->
    di_type_stable dn' dn ->
    bv_unsigned (di_nlink dn) = bv_unsigned (di_nlink dn') + 1 ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    ilinkdp (bv_unsigned inum) pv -∗
    iparent (bv_unsigned inum) pv -∗
    |={E, E ∖ ↑iregN}=> ∃ (bsl' : list (bv 8)) (v : nat),
      fsblock (fs_bytes γfs) (IBLOCK inum inodestart) bsl' ∗
      log_epoch_lb icfg_log v ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       izrcpt (bv_unsigned inum) dn' v -∗
       fsblock (fs_bytes γfs) (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ dinode_at γi inum dn').
  Proof.
    iIntros (HE Hin Hwf Hdn' Hnz Hstab Hnl) "#Hinv Hdn Hdp Hip".
    iApply (ireg_write_unlink_fl E γi γfs inodestart nib inum dn dn' ds
              (Some (Some pv)) HE Hin Hwf Hdn' Hnz Hstab Hnl
              with "Hinv Hdn [Hdp Hip]").
    cbn. iFrame "Hdp Hip".
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
    (* see [ireg_read] (durable-disk 1c-flip step 3) *)
    ↑logN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    b = IBLOCK inum inodestart ->
    ireg_inv γi γfs inodestart nib -∗
    ilink (bv_unsigned inum) -∗
    (b ↪[fs_cache γfs]{#(1/2)} bsl) ={E}=∗
    ⌜exists ds : list dinode,
       diblk_wf ds /\ bsl = diblk_bytes ds /\
       bv_unsigned (di_type (ds !!! islot inum)) <> 0⌝ ∗
    ilink (bv_unsigned inum) ∗
    (b ↪[fs_cache γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE HEl Hin Hb) "#Hinv Hfrag Hhalf".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iDestruct "Hrb" as (home) "#Hbinv".
    assert (HlogI : (↑logN : coPset) ⊆ E ∖ ↑iregN)
      by (apply subseteq_difference_r; [apply logN_iregN_disj | exact HEl]).
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    rewrite -(ireg_bi_iblock inum inodestart) -Hb.
    iMod (fs_bytes_agree (E ∖ ↑iregN) (fs_bytes γfs) (fs_cache γfs) home
            b (diblk_bytes ds) bsl HlogI with "Hbinv Hfsb Hhalf")
      as "(%Hbytes & Hfsb & Hhalf)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    iDestruct (ireg_rcol_w_ge with "Hla Hfrag") as %Hw1.
    assert (Hws : (1 <= wl + wdu + wdt)%nat) by lia.
    assert (Hnz : bv_unsigned (di_type (ds !!! islot inum)) <> 0)
      by exact (ireg_link_ok_alloc (ds !!! islot inum) _ Hlok Hws).
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      rewrite (ireg_bi_iblock inum inodestart) in Hb.
      rewrite Hb. iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hfrag Hhalf". iPureIntro.
    exists ds. split; [exact Hwf | split; [exact Hbytes | exact Hnz]].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  §20.4's LICENCE (f), REFUTED AT A RECORD THE CALLER NAMES           *)
  (* ------------------------------------------------------------------ *)

  (* fs-fragments.md §3.6's row (f), landed.  The enumeration at a claim box
     asks what licence a foreign [iget] could have held, and (f) is the bare
     [⌜bv_unsigned z = ROOTINO⌝] -- an arm no resource refutes, because it
     names no resource.  The root clause refutes it ARITHMETICALLY: the root
     has a link, and the record in question has none.

     The caller is in iput's free-path position (or holding any claim box's
     record): it has [dinode_at γi inum dn] and it has read [nlink dn = 0] --
     off its own [ip->nlink == 0] test, or off [fresh_shape_nlink].  Out
     comes the one fact the enumeration is missing, and the fragment goes
     back untouched.

     Mask-preserving and record-preserving: nothing in the region moves, so
     this may be fired at any point in a caller's proof, exactly as
     [ireg_link_alloc] and [IregLinkNz.ireg_link_nz] may.  [ireg_root] is the
     region's own spelling of the inum; [IregLinkNz.ireg_root_ROOTINO] is the
     one-[reflexivity] bridge to [InodeInv.ROOTINO]. *)
  Lemma ireg_root_ne (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    bv_unsigned (di_nlink dn) = 0 ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn ={E}=∗
    ⌜bv_unsigned inum <> ireg_root⌝ ∗ dinode_at γi inum dn.
  Proof.
    iIntros (HE Hin Hz) "#Hinv Hdn".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hdeq : ds !!! islot inum = dn).
    { pose proof (Hcp (islot inum) Hsl) as Hc.
      rewrite -ireg_key_split in Hc. congruence. }
    rewrite Hdeq in Hrt.
    assert (Hne : bv_unsigned inum <> ireg_root)
      by exact (ireg_root_ok_ne _ dn _ Hrt Hz).
    rewrite -Hdeq in Hrt.
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt gl cl rl pl fz cn Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iFrame "Hdn". iPureIntro. exact Hne.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  §20.8's ORPHAN COLOUR: THE FREE MINT                                *)
  (*     design: fs-icache.md §20.18 ruling 2                             *)
  (* ------------------------------------------------------------------ *)

  (* [ireg_link_alloc]'s shape with the BLOCK HALF removed: it reads
     nothing, so it needs no [fs_cache] credential and no [ds], and it takes no
     fragment in.  Mask-preserving, like every other ledger move (§20.2:
     the update is purely ghost, so it threads through no contract and a
     caller may fire it at any point in its own proof).

     WHAT IT IS FOR.  create's [fail:] after a successful [dirlink(ip,
     "..")] sets [ip->nlink = 0] at +0x12e while the [".."] record it wrote
     is still live on disk -- §20.8's orphaned [".."], the one record in
     xv6 whose target's link count does not account for it.  The payload
     that record sits in demands a ticket for [dp], and the only honest
     colour at that instant is grey.  There is nothing to convert FROM:
     the [ilink dp] that would have paid for it is minted at [dp->nlink++]
     (+0x128), which on this trace never ran.

     WHY IT IS SOUND, AND THE PERMANENT CONSEQUENCE.  [g] is constrained by
     no clause of [ireg_link_ok] and [igrey] concludes nothing, so the mint
     is a frame-preserving update at any slot and the fragment it pays out
     is not evidence of anything.  The price -- taken DELIBERATELY, and
     recorded rather than allowed to happen as a side effect -- is that [g]
     can never again carry information: §20.16.3's guarded claim discipline,
     and any later revival keyed on the orphan colour, are foreclosed from
     here on.  §20.16.3's actual wall is [ireg_withdraw]'s and is untouched,
     so nothing that stands today falls; what is given up is a repair route.
     [IcacheRef.link_mint_grey] carries the same record at the algebra. *)
  Lemma ireg_link_grey (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    ireg_inv γi γfs inodestart nib ={E}=∗ igrey (bv_unsigned inum).
  Proof.
    iIntros (HE Hin) "#Hinv".
    pose proof (islot_lt inum) as Hsl.
    assert (Hkey : (16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum))%Z
                   = bv_unsigned inum) by (symmetry; apply ireg_key_split).
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
    iMod (inv_acc E iregN with "Hiinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks & >Hreg)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γi γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb & >Hsls)".
    assert (Hlen16 : length ds = 16%nat) by (destruct Hwf as [Hl _]; exact Hl).
    iDestruct (ireg_slots_acc_upd γi (ireg_bi inum) ds (islot inum) Hsl Hlen16
                with "Hsls") as "[Hslot Hslback]".
    iEval (rewrite Hkey) in "Hslot".
    iDestruct "Hslot" as "[(%wl & %wdu & %wdt & %gl & %rl & %cl & %pl & %fz & %cn & Hla & %Hlok & %Hrt & %Hdir & %Hwl0 & %Hpar & #Hdisj & Hcnt & %Hclm & %Hfrz & Hfdisj & Hfrcp & Harm) Hep]".
    (* the ONE ghost step: [g] moves, and no clause of [ireg_link_ok]
       mentions it, so the slot is re-parked at the SAME record *)
    iDestruct "Hla" as (rcl) "[Hla %Href]".
    iMod (link_mint_grey with "Hla") as "[Hla Hfrag]".
    (* RULING R: [g] moves, the r columns and the record do not. *)
    iDestruct (ireg_rcol_intro (bv_unsigned inum) wl wdu wdt (S gl) cl rl pl fz
                 cn rcl (ds !!! islot inum) Href with "Hla") as "Hla".
    assert (Hins : <[islot inum := ds !!! islot inum]> ds = ds).
    { apply list_insert_id, list_lookup_lookup_total_lt. lia. }
    iMod ("Hclose" with "[Ha Hreg Hfsb Harm Hla Hep Hslback Hback Hcnt Hfdisj Hfrcp]") as "_".
    { iNext. iExists m. iFrame "Ha Hreg".
      iApply ("Hback" $! m with "[%] [Hfsb Harm Hla Hep Hslback Hcnt Hfdisj Hfrcp]"); [done |].
      iExists ds. iSplitR; [done |]. iSplitR; [done |].
      iSplitL "Hfsb"; [iExact "Hfsb" |].
      iEval (rewrite -Hins).
      iApply ("Hslback" $! (ds !!! islot inum) with "[Harm Hla Hep Hcnt Hfdisj Hfrcp]").
      rewrite Hkey.
      iApply (ireg_slot_intro γi (bv_unsigned inum) (ds !!! islot inum)
                wl wdu wdt (S gl) cl rl pl fz cn Hlok Hrt Hdir Hwl0 Hpar Hclm Hfrz
                with "Hla Hep Hdisj Hcnt Hfdisj Hfrcp Harm"). }
    iModIntro. iExact "Hfrag".
  Qed.

  (* ==================================================================== *)
  (*  §L.  THE LEND'S THREE OPERATIONS (N-4 PHASE B, E1-region)            *)
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
    iDestruct "Hinv" as "[#Hiinv #Hrb]".
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

  (* THE MINT.  Whoever holds a directory's whole contents element and this
     inum's licence cuts a lend out of it: ¾ stays on the custody chain
     (with the ride's marker), ¼ goes into the column, and the caller walks
     away with a pin.  The licence is spent into the column, so no inum is
     ever lent twice.  (No call site at this stage -- N-5.1's boot stocking
     is the mint's consumer; [IcacheBoot.ireg_alloc] hands the licences to
     [FsCfgBoot], which currently drops them.) *)
  Lemma dv_lend_mint (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z) (e : gmap fname Z) :
    ↑iregN ⊆ E ->
    dvl_dom z ->
    ireg_inv γi γfs inodestart nib -∗ dv_lic z -∗ dv_hold z e ={E}=∗
      (dv_half z (DfracOwn (3/4)) e ∗ dv_lentm z e) ∗ dv_pin z e.
  Proof.
    iIntros (HE Hdom) "#Hinv Hlic Hw".
    iApply (ireg_lcol_use E γi γfs inodestart nib z with "Hinv");
      [exact HE | exact Hdom |].
    iIntros "Hcol".
    iMod (dv_col_mint z e Hdom with "Hlic Hw Hcol") as "[$ $]".
    by iModIntro.
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
  (*  §LF.  THE fview LEND'S THREE OPERATIONS (N-5.2A, §13 D-52c)          *)
  (* ==================================================================== *)

  (*  §L's three, at the file-contents column.  Same signatures, same
      [ireg_inv] argument, same absence of an inum-range premise (the bound
      is [DirViewLend.dvl_dom], carried by the fview tokens too), same
      totality of the writer's move.  The fview lend's consumer is the kexec
      walk (N-5.2B); the mint's is [FsCfgBoot]'s stocking, at inum 7.       *)

  Lemma fv_lend_mint (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z) (b : list (bv 8)) :
    ↑iregN ⊆ E ->
    dvl_dom z ->
    ireg_inv γi γfs inodestart nib -∗ fv_lic z -∗ fv_hold z b ={E}=∗
      (fv_half z (DfracOwn (3/4)) b ∗ fv_lentm z b) ∗ fv_pin z b.
  Proof.
    iIntros (HE Hdom) "#Hinv Hlic Hw".
    iApply (ireg_fcol_use E γi γfs inodestart nib z with "Hinv");
      [exact HE | exact Hdom |].
    iIntros "Hcol".
    iMod (fv_col_mint z b Hdom with "Hlic Hw Hcol") as "[$ $]".
    by iModIntro.
  Qed.

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
