(* FsBlocks.v -- the block layer's two content maps, and the log layer's
   instantiation of the bio layer's client view (bio_view).

   Design: claude-notes/design/fs-log.md, section "The ghost state".

   THERE ARE TWO CONTENT MAPS, and which one a resource is a share of is
   the whole distinction between "what the buffer cache believes" and
   "what the file system owns".

   - [fs_cache] -- the bio-side block CACHE map C, keyed by BLOCK number,
     values whole-block byte lists.  Its AUTH lives in the log lock's
     resource ([LogInv.log_state]), which is the freeze: during commit the
     committer owns the auth outright, so C cannot move and "log slot i
     holds C(W[i])" carries from write_log through install_trans.  Each
     covered block's element is split half/half: the MACHINERY half rides
     inside the bio layer (pool -> escrow -> handle) as the payloads
     [fs_mclean]/[fs_mdirty] below, and the PARKED half is [fs_chalf].
     Two halves agree with no auth in sight; UPDATING needs the auth plus
     both halves, so log_write (under log.lock) and the committer are the
     only writers of C.

   - the LOGGED VIEW L, keyed by BYTE ADDRESS -- section [FsBytes] at the
     bottom of this file.  [byte_range] / [fsblock] are runs of FULL,
     therefore EXCLUSIVE, ghost_map elements, which is what lets the layer
     above own a SUB-BLOCK object and why bio may hold no share of this
     map at all.  The two maps are tied inside [fs_bytes_inv] (namespace
     [logN]), which is also where the home blocks' PARKED cache halves
     live.

   - [fs_dirty]: is the block in the current pinned write set
     (logged-uncommitted-or-uninstalled)?  Half in the payload, half (plus
     the auth) in the log lock's resource, recording exactly the membership
     of lh.block[].  Flipped false->true by log_write, true->false by
     install_trans at its bunpin.

   The bio payloads: clean = cache-half + dirty-half-at-false; dirty =
   cache-half + dirty-half-at-true.  Bio moves them opaquely; only holders
   of the cache auth convert.

   THERE IS NO PER-BLOCK OWNERSHIP TOKEN.  There used to be one ([fs_own]
   / [blk_own], a unit-valued ghost map at FULL fraction), because the
   client resource was the block-keyed HALF [fs_chalf] -- two holders of a
   half at one key are perfectly consistent, so no amount of [fs_chalf]
   reasoning said a block was unowned.  The byte view below is EXCLUSIVE,
   so [fsblock_excl] does that job directly and the token was pure
   duplication: the inode block map's injectivity, bfree's "freeing a free
   block" panic refutation and the icache escrow's block tokens are all
   readings of "two owners of one block's bytes is [False]".  The one thing
   the token could say that [fsblock] cannot -- naming a block whose
   CONTENT nobody has committed to -- is what [FsStateBitmap.free_bitmap_at]
   says instead, existentially, for exactly the free pool's members
   (fs-state.md section 2). *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_map.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvPtsto.
Require Import DiskPtsto.
Require Import BioDefs.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
Local Open Scope Z_scope.


Record fs_names := MkFsNames {
  fs_cache : gname;   (* the bio-side block CACHE map C *)
  fs_dirty : gname;   (* the pinned-set flag *)
  (* THE LOGGED VIEW L, keyed by BYTE ADDRESS (durable-disk 1c-flip).  The
     FS-facing view: its elements are FULL, hence EXCLUSIVE, and every home
     block's owner above the log holds [fsblock fs_bytes b bs] where it used
     to hold the cache's parked half [fs_chalf].  Tied to [fs_cache] inside
     [fs_bytes_inv] (section [FsBytes] below), which is also where the home
     blocks' parked cache halves now live. *)
  fs_bytes : gname;
  (* THE TWO FILE-SYSTEM-STATE GHOSTS (durable-disk 2b-A / B3).  Both are
     bare [gname]s here on purpose: this file is the BLOCK layer and must not
     name [FsStateInode.fs_node] or [FsStateLink.linkUR].  They are ALLOCATED
     one level up, in [FsBoot.fs_boot_ghosts], and passed to [fs_alloc] --
     the standing rule that a ghost name is a parameter, not a new
     config-class dependency.  [FsBytesGamma.fs_gamma_L] reads them as the
     era's [Γ_L.γlink] / [Γ_L.γtop]. *)
  fs_link : gname;   (* the link-counting family ([FsStateLink.linkUR])   *)
  fs_top  : gname;   (* the top-level abstract map ([Z -> fs_node])       *)
  (* THE BYTE VIEW'S EXCEPTION SET (durable-disk lane E-except).  LAST, so
     no positional [MkFsNames] moves.  See section [FsExc] below and the
     banner at [fs_bytes_body]. *)
  fs_exc  : gname;
}.

Section FsBlocks.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ}.

  (* the FS layer's points-to for a block's logical content (the client
     half of the logged view) *)
  Definition fs_chalf (γ : fs_names) (bno : Z) (bs : list (bv 8)) : iProp Σ :=
    bno ↪[fs_cache γ]{#(1/2)} bs.

  (* the machinery halves: the bio payloads *)
  Definition fs_mclean (γ : fs_names) (bno : Z) (bs : list (bv 8)) : iProp Σ :=
    (bno ↪[fs_cache γ]{#(1/2)} bs ∗ bno ↪[fs_dirty γ]{#(1/2)} false)%I.

  Definition fs_mdirty (γ : fs_names) (bno : Z) (bs : list (bv 8)) : iProp Σ :=
    (bno ↪[fs_cache γ]{#(1/2)} bs ∗ bno ↪[fs_dirty γ]{#(1/2)} true)%I.

  Global Instance fs_mclean_timeless γ b bs : Timeless (fs_mclean γ b bs).
  Proof. apply _. Qed.
  Global Instance fs_mdirty_timeless γ b bs : Timeless (fs_mdirty γ b bs).
  Proof. apply _. Qed.

  (* the bio_view the log layer runs the buffer cache at *)
  Definition fs_view (γ : fs_names) (gd : disk_names)
      (dev : SailStdpp.Values.mword 32) (cov : gset Z) : bio_view Σ :=
    MkBioView gd dev cov (fs_mclean γ) (fs_mdirty γ)
      (fun b bs => fs_mclean_timeless γ b bs)
      (fun b bs => fs_mdirty_timeless γ b bs).

  (* what a caller of bread learns on contact: its own fs_chalf half against
     the handle's machinery half pins the returned bytes.  Stated for both
     payload polarities. *)
  Lemma fs_chalf_mclean_agree γ bno bs bs' :
    fs_chalf γ bno bs -∗ fs_mclean γ bno bs' -∗ ⌜bs' = bs⌝.
  Proof.
    iIntros "Hc [Hm _]".
    iDestruct (ghost_map_elem_agree with "Hm Hc") as %Heq. done.
  Qed.

  Lemma fs_chalf_mdirty_agree γ bno bs bs' :
    fs_chalf γ bno bs -∗ fs_mdirty γ bno bs' -∗ ⌜bs' = bs⌝.
  Proof.
    iIntros "Hc [Hm _]".
    iDestruct (ghost_map_elem_agree with "Hm Hc") as %Heq. done.
  Qed.

  (* the logged-view update (log_write's ghost step): auth + both halves.
     The auth is the log lock's (stage 2); nothing else can move L. *)
  Lemma fs_chalf_update γ (L : gmap Z (list (bv 8))) bno bs bs_new bs' :
    ghost_map_auth (fs_cache γ) 1 L -∗
    fs_chalf γ bno bs -∗
    (bno ↪[fs_cache γ]{#(1/2)} bs') ==∗
    ⌜bs' = bs /\ L !! bno = Some bs⌝ ∗
    ghost_map_auth (fs_cache γ) 1 (<[bno := bs_new]> L) ∗
    fs_chalf γ bno bs_new ∗
    (bno ↪[fs_cache γ]{#(1/2)} bs_new).
  Proof.
    iIntros "Ha Hc Hm".
    iDestruct (ghost_map_elem_agree with "Hc Hm") as %->.
    iCombine "Hc Hm" as "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hlk.
    iMod (ghost_map_update bs_new with "Ha He") as "[Ha He]".
    iDestruct "He" as "[Hc Hm]".
    iModIntro. iFrame. done.
  Qed.

  (* the dirty-flag flip (log_write: false -> true; install's bunpin step:
     true -> false): auth + both halves, exactly the same shape. *)
  Lemma fs_dirty_flip γ (D : gmap Z bool) bno (b b' bnew : bool) :
    ghost_map_auth (fs_dirty γ) 1 D -∗
    (bno ↪[fs_dirty γ]{#(1/2)} b) -∗
    (bno ↪[fs_dirty γ]{#(1/2)} b') ==∗
    ⌜b' = b /\ D !! bno = Some b⌝ ∗
    ghost_map_auth (fs_dirty γ) 1 (<[bno := bnew]> D) ∗
    (bno ↪[fs_dirty γ]{#(1/2)} bnew) ∗
    (bno ↪[fs_dirty γ]{#(1/2)} bnew).
  Proof.
    iIntros "Ha Hc Hm".
    iDestruct (ghost_map_elem_agree with "Hc Hm") as %->.
    iCombine "Hc Hm" as "He".
    iDestruct (ghost_map_lookup with "Ha He") as %Hlk.
    iMod (ghost_map_update bnew with "Ha He") as "[Ha He]".
    iDestruct "He" as "[Hc Hm]".
    iModIntro. iFrame. done.
  Qed.

End FsBlocks.

(* ===================================================================== *)
(*  THE LOGGED VIEW L, KEYED BY BYTE ADDRESS  (durable-disk 1c)          *)
(*                                                                       *)
(*  Design of record: claude-notes/design/fs-state.md §0/§1/§5.  The     *)
(*  FS-facing view of a block's content is no longer the HALF of a       *)
(*  block-keyed element -- it is a run of FULL, byte-keyed ghost_map     *)
(*  elements, one per byte address [b*BSIZE + off + k].  Full elements   *)
(*  are EXCLUSIVE, which is what lets the layer above own a SUB-BLOCK    *)
(*  object (an inode record, a directory entry) and what makes           *)
(*  [free_bitmap]'s "a block nobody else can own" argument run.          *)
(*                                                                      *)
(*  The price of exclusivity is that bio can no longer hold a share of   *)
(*  this map: the buffer cache's belief about a block rides in the       *)
(*  block-keyed CACHE map ([fs_cache], the payloads' [fs_chalf]) and the *)
(*  two are tied inside the log-layer invariant [fs_bytes_inv] below.    *)
(*  A [bread] client turns "the payload says the buffer holds [bsm]"     *)
(*  into "[bsm] is what my byte elements say" by OPENING that invariant; *)
(*  the old auth-free half/half agreement is gone.                       *)
(*                                                                      *)
(*  Everything here is stated over BARE GHOST NAMES (the standing rule:  *)
(*  ghost names are parameters).                                        *)
(*                                                                      *)
(*  TYPING.  The byte map is a [ghost_map Z (bv 8)], and this tree has   *)
(*  exactly ONE source of that instance -- [DiskImg.diskImgG], reached   *)
(*  through [RiscvPtsto.riscvF_diskGS] (see DiskImg.v's header).  A      *)
(*  second field in [fsLogG] would be a second, non-interacting Sigma    *)
(*  slot and would break the disk image's own auth/fragment pairing, so  *)
(*  the logged view rides the same class at its own gname.               *)
(* ===================================================================== *)

(* [BSIZE] at Z.  Stated at Z and never at nat: a nat equality against a
   four-digit literal materialises a unary chain (durable-notes). *)
Definition BSZ : Z := 1024.

Lemma BSZ_BSIZE : Z.of_nat BSIZE = BSZ.
Proof. vm_compute. reflexivity. Qed.

(* two distinct blocks' byte ranges do not meet *)
Lemma blk_range_disj (b b' a : Z) :
  b * BSZ <= a < b * BSZ + BSZ ->
  b' * BSZ <= a < b' * BSZ + BSZ ->
  b = b'.
Proof. unfold BSZ. lia. Qed.

(* ===================================================================== *)
(*  THE SUB-RANGE SPLICE (durable-disk 2b-0)                             *)
(*                                                                       *)
(*  A writer above the log owns a SUB-RANGE of a block -- an inode        *)
(*  record's 64 bytes, a directory entry's 16 -- and log_writes the WHOLE *)
(*  buffer it is a piece of.  [blk_splice off sub bs] is the whole-block  *)
(*  content its stores produce: [bs] with [sub] written at [off] and      *)
(*  every other byte untouched.  It is the shape the writer's own stores  *)
(*  have anyway, which is why the side condition is stated with it        *)
(*  rather than with a pointwise "agrees outside [off, off+|sub|)":       *)
(*  a caller discharges it by [reflexivity] on the term it just built.    *)
(*                                                                       *)
(*  ALL LIST REASONING HERE IS AT THE [take]/[drop]/[++] LEVEL and never  *)
(*  at the element level: the lists are 1024 long and the block layer's   *)
(*  rule is that nothing ever computes one (durable-notes).              *)
(* ===================================================================== *)

Definition blk_splice (off : nat) (sub bs : list (bv 8)) : list (bv 8) :=
  take off bs ++ sub ++ drop (off + length sub) bs.

Lemma blk_splice_length (off : nat) (sub bs : list (bv 8)) :
  (off + length sub <= length bs)%nat ->
  length (blk_splice off sub bs) = length bs.
Proof.
  intros H. rewrite /blk_splice !length_app length_take length_drop. lia.
Qed.

(* the whole-block instance: splicing a full-width run at 0 IS the run *)
Lemma blk_splice_whole (sub bs : list (bv 8)) :
  length sub = length bs -> blk_splice 0 sub bs = sub.
Proof.
  intros H. rewrite /blk_splice take_0 app_nil_l /=.
  rewrite drop_ge; [| lia]. by rewrite app_nil_r.
Qed.

Lemma blk_splice_lookup_lt (off : nat) (sub bs : list (bv 8)) (j : nat) :
  (off <= length bs)%nat -> (j < off)%nat ->
  blk_splice off sub bs !! j = bs !! j.
Proof.
  intros Hb Hj. rewrite /blk_splice lookup_app_l.
  - by apply lookup_take.
  - rewrite length_take. lia.
Qed.

Lemma blk_splice_lookup_mid (off : nat) (sub bs : list (bv 8)) (j : nat) :
  (off <= length bs)%nat -> (off <= j)%nat -> (j < off + length sub)%nat ->
  blk_splice off sub bs !! j = sub !! (j - off)%nat.
Proof.
  intros Hb H1 H2. rewrite /blk_splice.
  rewrite lookup_app_r; [| rewrite length_take; lia].
  rewrite length_take_le; [| lia].
  rewrite lookup_app_l; [done | lia].
Qed.

Lemma blk_splice_lookup_ge (off : nat) (sub bs : list (bv 8)) (j : nat) :
  (off <= length bs)%nat -> (off + length sub <= j)%nat ->
  blk_splice off sub bs !! j = bs !! j.
Proof.
  intros Hb Hj. rewrite /blk_splice.
  rewrite lookup_app_r; [| rewrite length_take; lia].
  rewrite length_take_le; [| lia].
  rewrite lookup_app_r; [| lia].
  rewrite lookup_drop. f_equal. lia.
Qed.

Definition logN : namespace := nroot .@ "fslogbytes".

(* ---------------------------------------------------------------------- *)
(*  [logN] IS A FAMILY, NOT ONE INVARIANT (durable-disk lane E-blk1).      *)
(*                                                                        *)
(*  The cache/byte tie below lives at [fsbN = logN .@ "b"] and block 1's   *)
(*  park at [SbPark.sbN = logN .@ "sb"] -- SIBLINGS, because the commit    *)
(*  holds the byte view open while the collection reads block 1, so they   *)
(*  must be independently openable.                                       *)
(*                                                                        *)
(*  WHY THE PARK LIVES UNDER [logN] AT ALL.  [SpecLogWrite]'s byte-range   *)
(*  atomic update runs at the CALLER's mask [Efs], about which the         *)
(*  contract says one thing only: [↑logN ⊆ Efs].  That window -- between   *)
(*  firing the update and closing it -- is the ONE moment at which         *)
(*  [log_write] holds the caller's run at fraction 1, hence the one moment *)
(*  at which "this is not block 1" is provable at all                      *)
(*  ([SbPark.sb_parked_bno_ne], read into [LogInv.log_state]'s write-set   *)
(*  row by [ProofLogWrite]).  Making the park a CHILD of [logN] is what    *)
(*  buys that mask with no new premise at any of log_write's ~20 call      *)
(*  sites; the alternative -- one more [↑sbN ⊆ Efs] premise on every       *)
(*  [wp_log_write_*] -- would land on all of them.                        *)
(*                                                                        *)
(*  Every [↑logN ⊆ E] premise in the tree is UNCHANGED by the split        *)
(*  ([logN]'s own value did not move); only the [inv_acc]s inside this     *)
(*  file and the committer's own open name [fsbN] instead.                *)
(* ---------------------------------------------------------------------- *)
Definition fsbN : namespace := logN .@ "b".

Lemma fsbN_logN : (↑fsbN : coPset) ⊆ ↑logN.
Proof. apply nclose_subseteq. Qed.

Lemma fsbN_sub (E : coPset) : (↑logN : coPset) ⊆ E -> (↑fsbN : coPset) ⊆ E.
Proof. intros HE. etrans; [apply fsbN_logN | exact HE]. Qed.

(* the mask side condition every reader at the top mask discharges.  Proved
   ONCE, here, in an empty context: [set_solver] inside a syscall-altitude
   proof walks the whole context (durable-notes), and every call site of
   [fs_bytes_agree] below is at [⊤] or at [⊤] minus one namespace. *)
Lemma logN_top : (↑logN : coPset) ⊆ ⊤.
Proof. set_solver. Qed.

Lemma fsbN_top : (↑fsbN : coPset) ⊆ ⊤.
Proof. exact (fsbN_sub ⊤ logN_top). Qed.

Section FsBytes.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  1.  The points-to run                                              *)
  (* ------------------------------------------------------------------ *)

  (* [bs] resides at byte offset [off] of block [b], at FULL ownership. *)
  Definition byte_range (gL : gname) (b off : Z) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] k ↦ v ∈ bs, (b * BSZ + off + Z.of_nat k) ↪[gL] v)%I.

  (* the whole-block form: every current consumer of the old block half
     spells this. *)
  Definition fsblock (gL : gname) (b : Z) (bs : list (bv 8)) : iProp Σ :=
    (⌜length bs = BSIZE⌝ ∗ byte_range gL b 0 bs)%I.

  (* ---- THE SAME TWO SHAPES AT A SHARE (durable-fs-plan.md sections 4, 6;
         lane B''-blk) ------------------------------------------------------

     [FsStateDefs] fraction-indexed the ABSTRACT byte points-to; this is the
     CONCRETE twin, and it is what lets a share cross the bridge
     [FsBytesGamma.gamma_blk_owned_q] -- which since the era-vocabulary
     unification's stage 3 happens in [InodeInv.blk_res_q_run] /
     [ind_blk_q_nz] and nowhere else on the inode path.  The
     unsuffixed names above are the [DfracOwn 1] READINGS and their text has
     not moved -- [k ↪[γ] v] IS [k ↪[γ]{DfracOwn 1} v], so each [_1]
     equation below is [reflexivity] and the ~34 files spelling [fsblock]
     are untouched by the index. *)
  Definition byte_range_q (gL : gname) (dq : dfrac) (b off : Z)
      (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] k ↦ v ∈ bs, (b * BSZ + off + Z.of_nat k) ↪[gL]{dq} v)%I.

  Definition fsblock_q (gL : gname) (dq : dfrac) (b : Z) (bs : list (bv 8))
    : iProp Σ :=
    (⌜length bs = BSIZE⌝ ∗ byte_range_q gL dq b 0 bs)%I.

  Lemma byte_range_1 gL b off bs :
    byte_range gL b off bs = byte_range_q gL (DfracOwn 1) b off bs.
  Proof. reflexivity. Qed.

  Lemma fsblock_1 gL b bs : fsblock gL b bs = fsblock_q gL (DfracOwn 1) b bs.
  Proof. reflexivity. Qed.

  (* THE CROSSING AS A WAND, WHICH IS WHAT A PROOF NEEDS.  The equation
     above holds by conversion, but both heads are [Typeclasses Opaque]
     (they have to be -- a 1024-element [big_sepL] behind a [Definition] is
     an [iFrame] hang), so neither [iFrame] nor [IntoWand] will cross it and
     a rewrite inside the proofmode is fiddly.  A caller that has just
     learned its share IS 1 -- an ALLOCATING bmap arm, where balloc hands
     over a full run -- crosses with one [iDestruct]. *)
  Lemma fsblock_q_1_of gL dq b bs :
    dq = DfracOwn 1 -> fsblock_q gL dq b bs -∗ fsblock gL b bs.
  Proof. intros ->. rewrite fsblock_1. iIntros "H". iExact "H". Qed.

  Lemma fsblock_q_1_to gL dq b bs :
    dq = DfracOwn 1 -> fsblock gL b bs -∗ fsblock_q gL dq b bs.
  Proof. intros ->. rewrite fsblock_1. iIntros "H". iExact "H". Qed.

  Global Instance byte_range_timeless gL b off bs :
    Timeless (byte_range gL b off bs).
  Proof. apply _. Qed.
  Global Instance fsblock_timeless gL b bs : Timeless (fsblock gL b bs).
  Proof. apply _. Qed.
  Global Instance byte_range_q_timeless gL dq b off bs :
    Timeless (byte_range_q gL dq b off bs).
  Proof. apply _. Qed.
  Global Instance fsblock_q_timeless gL dq b bs : Timeless (fsblock_q gL dq b bs).
  Proof. apply _. Qed.

  Lemma fsblock_length gL b bs : fsblock gL b bs -∗ ⌜length bs = BSIZE⌝.
  Proof. iIntros "[% _]". done. Qed.

  Lemma fsblock_q_length gL dq b bs :
    fsblock_q gL dq b bs -∗ ⌜length bs = BSIZE⌝.
  Proof. iIntros "[% _]". done. Qed.

  Lemma BSIZE_pos : (0 < BSIZE)%nat.
  Proof. apply Nat2Z.inj_lt. rewrite BSZ_BSIZE. unfold BSZ. lia. Qed.

  (* THE POINT OF THE RE-KEYING.  Two owners of one block's bytes is a
     contradiction -- the old block-keyed HALF was consistent with itself,
     which is exactly why a separate ownership token had to exist.  It is
     the ONE exclusivity law the file-system design invokes, used as
     [l ↦ _ ∗ l ↦ _ ⊢ False] is used: to learn that two owned things are
     different objects (fs-state.md section 0). *)
  Lemma fsblock_excl gL b bs bs' :
    fsblock gL b bs -∗ fsblock gL b bs' -∗ False.
  Proof.
    iIntros "[%Hl Hr] [%Hl' Hr']".
    assert (Hs : is_Some (bs !! 0%nat)).
    { apply lookup_lt_is_Some. rewrite Hl. exact BSIZE_pos. }
    destruct Hs as [v Hv].
    assert (Hs' : is_Some (bs' !! 0%nat)).
    { apply lookup_lt_is_Some. rewrite Hl'. exact BSIZE_pos. }
    destruct Hs' as [v' Hv'].
    rewrite /byte_range.
    iDestruct (big_sepL_lookup _ _ 0%nat v Hv with "Hr") as "H1".
    iDestruct (big_sepL_lookup _ _ 0%nat v' Hv' with "Hr'") as "H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hval _].
    exfalso. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hval).
  Qed.

  (* ---- the fraction-aware readings of the same law -------------------- *)

  (* the general form: two runs at one address bound their shares.  The
     concrete twin of [FsStateDefs.byte_range_q_valid]. *)
  Lemma byte_range_q_valid gL dq1 dq2 b off bs bs' :
    (0 < length bs)%nat -> (0 < length bs')%nat ->
    byte_range_q gL dq1 b off bs -∗ byte_range_q gL dq2 b off bs' -∗
    ⌜✓ (dq1 ⋅ dq2)⌝.
  Proof.
    intros Hl Hl'. iIntros "H H'".
    destruct (lookup_lt_is_Some_2 bs 0%nat Hl) as [v Hv].
    destruct (lookup_lt_is_Some_2 bs' 0%nat Hl') as [v' Hv'].
    rewrite /byte_range_q.
    iDestruct (big_sepL_lookup _ _ 0%nat v Hv with "H") as "H1".
    iDestruct (big_sepL_lookup _ _ 0%nat v' Hv' with "H'") as "H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hval _].
    done.
  Qed.

  Lemma fsblock_q_excl gL dq1 dq2 b bs bs' :
    ~ ✓ (dq1 ⋅ dq2) ->
    fsblock_q gL dq1 b bs -∗ fsblock_q gL dq2 b bs' -∗ False.
  Proof.
    intros Hnv. iIntros "[%Hl H] [%Hl' H']".
    iDestruct (byte_range_q_valid gL dq1 dq2 b 0 bs bs'
                 ltac:(rewrite Hl; exact BSIZE_pos)
                 ltac:(rewrite Hl'; exact BSIZE_pos) with "H H'") as %Hv.
    done.
  Qed.

  Lemma fsblock_q_ne gL dq1 dq2 b1 b2 bs1 bs2 :
    ~ ✓ (dq1 ⋅ dq2) ->
    fsblock_q gL dq1 b1 bs1 -∗ fsblock_q gL dq2 b2 bs2 -∗ ⌜b1 <> b2⌝.
  Proof.
    intros Hnv. iIntros "H1 H2".
    destruct (decide (b1 = b2)) as [->|Hne]; [| done].
    iExFalso. iApply (fsblock_q_excl gL dq1 dq2 _ _ _ Hnv with "H1 H2").
  Qed.

  (* THE TWO SPECIALISATIONS THE DESIGN NAMES (plan section 4), concretely.
     [_full]: a full owner excludes ANY other share -- the resource reading
     of "a read-locker cannot write", since [SpecLogWrite]'s byte-range AU
     needs fraction 1.  [_34]: two three-quarter owners cannot alias, which
     is why a reader's share is a QUARTER. *)
  (* the two arithmetic facts, restated here because the BLOCK layer sits
     BELOW [FsStateDefs] and must not import it (its twins there are
     [FsStateDefs.dfrac_full_nvalid] / [dfrac_34_nvalid]). *)
  Lemma blk_dfrac_full_nvalid (dq : dfrac) : ~ ✓ (DfracOwn 1 ⋅ dq).
  Proof. intros Hv. exact (exclusive_l (DfracOwn 1) dq Hv). Qed.

  Lemma blk_dfrac_34_nvalid : ~ ✓ (DfracOwn (3/4) ⋅ DfracOwn (3/4)).
  Proof.
    rewrite dfrac_op_own. intros Hv%dfrac_valid_own.
    apply (Qp.lt_nge 1 (3/4 + 3/4)%Qp); [| exact Hv].
    apply Qp.lt_sum. exists (1/2)%Qp. compute_done.
  Qed.

  Lemma fsblock_ne_full gL dq b1 b2 bs1 bs2 :
    fsblock gL b1 bs1 -∗ fsblock_q gL dq b2 bs2 -∗ ⌜b1 <> b2⌝.
  Proof.
    rewrite fsblock_1.
    iApply (fsblock_q_ne gL (DfracOwn 1) dq b1 b2 bs1 bs2
              (blk_dfrac_full_nvalid _)).
  Qed.

  (* ...AND THE FORM A SUB-BLOCK WRITER'S REFUTATION NEEDS (durable-disk
     lane E-blk1).  [SpecLogWrite]'s byte-range atomic update surrenders a
     RUN INSIDE a block, not the whole block, so the park's whole-block
     owner has to be played against a window: at [off < BSIZE] the two runs
     share the byte at [b * BSZ + off], and both are at fraction 1.  This is
     [fsblock_ne_full] one granularity down, and it is what makes "block 1
     is never logged" a resource fact rather than a premise. *)
  Lemma fsblock_byte_range_ne gL (b1 b2 : Z) (off : nat)
      (bs sub : list (bv 8)) :
    (off < BSIZE)%nat -> (0 < length sub)%nat ->
    fsblock gL b1 bs -∗ byte_range gL b2 (Z.of_nat off) sub -∗ ⌜b1 <> b2⌝.
  Proof.
    intros Hoff Hpos. iIntros "[%Hlen Hr1] Hr2".
    destruct (decide (b1 = b2)) as [->|Hne]; [| done].
    destruct (lookup_lt_is_Some_2 bs off ltac:(rewrite Hlen; exact Hoff))
      as [v Hv].
    destruct (lookup_lt_is_Some_2 sub 0%nat Hpos) as [w Hw].
    rewrite /byte_range.
    iDestruct (big_sepL_lookup _ _ off v Hv with "Hr1") as "H1".
    iDestruct (big_sepL_lookup _ _ 0%nat w Hw with "Hr2") as "H2".
    assert (Haddr : (b2 * BSZ + 0 + Z.of_nat off)%Z
                    = (b2 * BSZ + Z.of_nat off + Z.of_nat 0)%Z) by lia.
    iEval (rewrite Haddr) in "H1".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hval _].
    exfalso. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hval).
  Qed.

  Lemma fsblock_ne_34 gL b1 b2 bs1 bs2 :
    fsblock_q gL (DfracOwn (3/4)) b1 bs1 -∗
    fsblock_q gL (DfracOwn (3/4)) b2 bs2 -∗ ⌜b1 <> b2⌝.
  Proof.
    iApply (fsblock_q_ne gL (DfracOwn (3/4)) (DfracOwn (3/4)) b1 b2 bs1 bs2
              blk_dfrac_34_nvalid).
  Qed.

  (* ---- SPLITTING: how the quarter is handed out and taken back -------- *)

  Lemma byte_range_q_split gL (q1 q2 : Qp) b off bs :
    byte_range_q gL (DfracOwn (q1 + q2)) b off bs
    ⊣⊢ byte_range_q gL (DfracOwn q1) b off bs
        ∗ byte_range_q gL (DfracOwn q2) b off bs.
  Proof.
    rewrite /byte_range_q -big_sepL_sep.
    apply big_sepL_proper. intros k v _.
    apply (ghost_map_elem_fractional _ gL v q1 q2).
  Qed.

  Lemma fsblock_q_split gL (q1 q2 : Qp) b bs :
    fsblock_q gL (DfracOwn (q1 + q2)) b bs
    ⊣⊢ fsblock_q gL (DfracOwn q1) b bs ∗ fsblock_q gL (DfracOwn q2) b bs.
  Proof.
    rewrite /fsblock_q byte_range_q_split.
    iSplit.
    - iIntros "[%Hl [H1 H2]]". iSplitL "H1"; by iFrame.
    - iIntros "[[%Hl H1] [_ H2]]". by iFrame.
  Qed.

  Lemma fsblock_split_34 gL b bs :
    fsblock gL b bs
    ⊣⊢ fsblock_q gL (DfracOwn (3/4)) b bs ∗ fsblock_q gL (DfracOwn (1/4)) b bs.
  Proof.
    rewrite fsblock_1 -(fsblock_q_split gL (3/4) (1/4)).
    rewrite Qp.three_quarter_quarter //.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2.  The run as a map, so the ghost_map big-op lemmas apply         *)
  (* ------------------------------------------------------------------ *)

  Lemma big_sepM_map_seqZ (Phi : Z -> bv 8 -> iProp Σ) (start : Z)
      (xs : list (bv 8)) :
    ([∗ map] a ↦ v ∈ (map_seqZ start xs : gmap Z (bv 8)), Phi a v)
    ⊣⊢ ([∗ list] k ↦ v ∈ xs, Phi (start + Z.of_nat k) v).
  Proof.
    revert start. induction xs as [|x xs IH]; intros start.
    - simpl. rewrite big_sepM_empty //.
    - rewrite map_seqZ_cons big_sepM_insert; [| apply map_seqZ_cons_disjoint].
      rewrite IH big_sepL_cons.
      assert (Hz : start + Z.of_nat 0 = start) by lia. rewrite Hz.
      f_equiv. apply big_sepL_proper. intros k y _.
      assert (Hs : Z.succ start + Z.of_nat k = start + Z.of_nat (S k)) by lia.
      rewrite Hs //.
  Qed.

  Lemma byte_range_map (gL : gname) (b off : Z) (bs : list (bv 8)) :
    byte_range gL b off bs ⊣⊢
      ([∗ map] a ↦ v ∈ (map_seqZ (b * BSZ + off) bs : gmap Z (bv 8)),
         a ↪[gL] v).
  Proof. rewrite /byte_range big_sepM_map_seqZ //. Qed.

  (* two runs pinned to the same authority at the same start and length
     are the same run *)
  Lemma map_seqZ_inj (xs ys : list (bv 8)) (start : Z) (L : gmap Z (bv 8)) :
    length xs = length ys ->
    (map_seqZ start xs : gmap Z (bv 8)) ⊆ L ->
    (map_seqZ start ys : gmap Z (bv 8)) ⊆ L ->
    xs = ys.
  Proof.
    intros Hlen H1 H2. apply list_eq. intros k.
    destruct (xs !! k) as [x|] eqn:Hx.
    - assert (Hy : is_Some (ys !! k)).
      { apply lookup_lt_is_Some. rewrite -Hlen.
        apply lookup_lt_is_Some. by exists x. }
      destruct Hy as [y Hy]. rewrite Hy. f_equal.
      apply (lookup_map_seqZ_Some_inv start) in Hx.
      apply (lookup_map_seqZ_Some_inv start) in Hy.
      pose proof (map_subseteq_spec (map_seqZ start xs : gmap Z (bv 8)) L) as [Hs1 _].
      pose proof (map_subseteq_spec (map_seqZ start ys : gmap Z (bv 8)) L) as [Hs2 _].
      specialize (Hs1 H1 _ _ Hx). specialize (Hs2 H2 _ _ Hy). congruence.
    - symmetry. apply lookup_ge_None. rewrite -Hlen.
      by apply lookup_ge_None.
  Qed.

  (* ...AND THE SUB-RANGE READING OF IT (durable-disk 2b-0).  A run pinned
     to the authority INSIDE a longer run's span is that run's slice --
     which is how the sub-block writer learns what the other 960 bytes of
     its block are without ever holding them: the cache entry is [L] read
     at the block's whole range ([bytes_tie]), and the writer's own run is
     [L] read at its own. *)
  Lemma map_seqZ_slice (xs ys : list (bv 8)) (start : Z) (o : nat)
      (L : gmap Z (bv 8)) :
    (o + length ys <= length xs)%nat ->
    (map_seqZ start xs : gmap Z (bv 8)) ⊆ L ->
    (map_seqZ (start + Z.of_nat o) ys : gmap Z (bv 8)) ⊆ L ->
    ys = take (length ys) (drop o xs).
  Proof.
    intros Hle H1 H2. apply list_eq. intros k.
    destruct (decide (k < length ys)%nat) as [Hk|Hk].
    - destruct (lookup_lt_is_Some_2 ys k Hk) as [y Hy].
      rewrite Hy. symmetry.
      rewrite lookup_take; [| exact Hk]. rewrite lookup_drop.
      assert (Hxs : is_Some (xs !! (o + k)%nat))
        by (apply lookup_lt_is_Some; lia).
      destruct Hxs as [x Hx]. rewrite Hx. f_equal.
      apply (lookup_map_seqZ_Some_inv (start + Z.of_nat o)) in Hy.
      apply (lookup_map_seqZ_Some_inv start) in Hx.
      pose proof (lookup_weaken _ _ _ _ Hy H2) as HL1.
      pose proof (lookup_weaken _ _ _ _ Hx H1) as HL2.
      assert (Heq : start + Z.of_nat o + Z.of_nat k
                    = start + Z.of_nat (o + k)%nat) by lia.
      rewrite Heq in HL1. congruence.
    - rewrite (lookup_ge_None_2 ys k); [| lia].
      symmetry. apply lookup_ge_None_2.
      rewrite length_take length_drop. lia.
  Qed.

  Lemma byte_range_q_map (gL : gname) (dq : dfrac) (b off : Z)
      (bs : list (bv 8)) :
    byte_range_q gL dq b off bs ⊣⊢
      ([∗ map] a ↦ v ∈ (map_seqZ (b * BSZ + off) bs : gmap Z (bv 8)),
         a ↪[gL]{dq} v).
  Proof. rewrite /byte_range_q big_sepM_map_seqZ //. Qed.

  (* what the auth says about an owned run *)
  Lemma byte_range_lookup gL (L : gmap Z (bv 8)) b off bs :
    ghost_map_auth gL 1 L -∗ byte_range gL b off bs -∗
    ⌜(map_seqZ (b * BSZ + off) bs : gmap Z (bv 8)) ⊆ L⌝.
  Proof.
    iIntros "Ha Hr". rewrite byte_range_map.
    iApply (ghost_map_lookup_big with "Ha Hr").
  Qed.

  (* AGREEMENT NEEDS NO SHARE (plan section 4: "the bytes at every record
     slot and data block by AGREEMENT -- any fraction suffices").  This is
     the one law a read-locker at a QUARTER runs, and every reading below
     that a share must survive goes through it. *)
  (* [ghost_map_lookup_big] is stated at fraction 1 only in iris 4.4.0, so
     this is its own three-line proof at a share ([ghost_map_lookup] itself
     takes a [dfrac] -- the big-op version simply was not generalised). *)
  Lemma byte_range_q_lookup gL dq (L : gmap Z (bv 8)) b off bs :
    ghost_map_auth gL 1 L -∗ byte_range_q gL dq b off bs -∗
    ⌜(map_seqZ (b * BSZ + off) bs : gmap Z (bv 8)) ⊆ L⌝.
  Proof.
    iIntros "Ha Hr". rewrite byte_range_q_map.
    rewrite map_subseteq_spec. iIntros (k v Hk).
    iDestruct (ghost_map_lookup with "Ha [Hr]") as %->; [| done].
    rewrite big_sepM_lookup; done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3.  THE UPDATE, AT BYTE-RANGE GRANULARITY                          *)
  (*                                                                     *)
  (*  Stated at [off]/[bs]/[bs'] rather than at whole blocks so that     *)
  (*  stage 2's sub-block owners (an inode record, a dirent) use it      *)
  (*  without the log moving again.  It is the pure ghost step: the auth *)
  (*  plus the FULL elements of the bytes that change.                   *)
  (* ------------------------------------------------------------------ *)

  Lemma byte_range_update_at gL (L : gmap Z (bv 8)) (start : Z)
      (bs bs' : list (bv 8)) :
    length bs' = length bs ->
    ghost_map_auth gL 1 L -∗
    ([∗ list] k ↦ v ∈ bs, (start + Z.of_nat k) ↪[gL] v) ==∗
    ghost_map_auth gL 1 ((map_seqZ start bs' : gmap Z (bv 8)) ∪ L) ∗
    ([∗ list] k ↦ v ∈ bs', (start + Z.of_nat k) ↪[gL] v).
  Proof.
    revert bs' start L. induction bs as [|x bs IH]; intros bs' start L Hlen.
    - destruct bs'; [| simpl in Hlen; lia].
      iIntros "Ha _". simpl. rewrite left_id_L. by iFrame.
    - destruct bs' as [|x' bs']; [simpl in Hlen; lia |].
      simpl in Hlen.
      iIntros "Ha Hr". rewrite big_sepL_cons.
      iDestruct "Hr" as "[Hhd Htl]".
      assert (Hz : start + Z.of_nat 0 = start) by lia.
      rewrite Hz.
      iMod (ghost_map_update x' with "Ha Hhd") as "[Ha Hhd]".
      iAssert ([∗ list] k ↦ v ∈ bs, (Z.succ start + Z.of_nat k) ↪[gL] v)%I
        with "[Htl]" as "Htl".
      { iApply (big_sepL_proper with "Htl"). intros k y _.
        assert (Hs : start + Z.of_nat (S k) = Z.succ start + Z.of_nat k) by lia.
        rewrite Hs //. }
      iMod (IH bs' (Z.succ start) (<[start := x']> L) ltac:(lia) with "Ha Htl")
        as "[Ha Htl]".
      iModIntro.
      rewrite map_seqZ_cons.
      rewrite -(insert_union_l (map_seqZ (Z.succ start) bs') L start x').
      rewrite (insert_union_r (map_seqZ (Z.succ start) bs') L start x');
        [| apply map_seqZ_cons_disjoint].
      iFrame "Ha".
      rewrite big_sepL_cons Hz. iFrame "Hhd".
      iApply (big_sepL_proper with "Htl"). intros k y _.
      assert (Hs : Z.succ start + Z.of_nat k = start + Z.of_nat (S k)) by lia.
      rewrite Hs //.
  Qed.

  Lemma byte_range_update gL (L : gmap Z (bv 8)) b off bs bs' :
    length bs' = length bs ->
    ghost_map_auth gL 1 L -∗ byte_range gL b off bs ==∗
    ghost_map_auth gL 1 ((map_seqZ (b * BSZ + off) bs' : gmap Z (bv 8)) ∪ L) ∗
    byte_range gL b off bs'.
  Proof.
    intros Hlen. rewrite /byte_range.
    iIntros "Ha Hr".
    iApply (byte_range_update_at gL L (b * BSZ + off) bs bs' Hlen with "Ha Hr").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3b.  THE EXCEPTION SET, AND THE SEAL  (durable-disk lane E-except) *)
  (*                                                                     *)
  (*  THE ONE WINDOW IN WHICH THE TWO CONTENT MAPS DISAGREE is the       *)
  (*  recovery window: at PowerOn on a DIRTY log header the era's byte   *)
  (*  view [L] is minted at the COMMITTED view [FsCrash.fr_D] -- the raw *)
  (*  home blocks with the on-disk log's batch installed -- while the    *)
  (*  cache map [C] and the physical disk still read the CRASHED bytes.  *)
  (*  So [bytes_tie] is false at exactly the home blocks the on-disk     *)
  (*  header's write set names, and true everywhere else.  That set is   *)
  (*  the EXCEPTION SET.  (Plan section 5; [BioInv.pool_blk], the        *)
  (*  mirror row and [SpecInitlog]'s [lm_view] row all stay true --      *)
  (*  the cache and the disk agree throughout, which is why the          *)
  (*  exception lands here and nowhere else.)                            *)
  (*                                                                     *)
  (*  IT IS OWNED BY THE WAL, ONE-KEY GHOST MAP, AND THE HANDLE IS ALSO  *)
  (*  THE SEAL.  [exc_auth] sits inside the byte view's own invariant;   *)
  (*  [exc_own] is the WAL's exclusive handle on it -- minted at PowerOn  *)
  (*  at the header's write set, threaded through [SpecFsinit] into      *)
  (*  [SpecInitlog], SHRUNK one block at a time by the recovering        *)
  (*  [install_trans] (each home [bwrite] lands the logged value in the  *)
  (*  cache, which restores the tie AT THAT BLOCK), and spent EMPTY at   *)
  (*  the end of recovery, where [exc_seal] PERSISTS the element at [∅]. *)
  (*  A discarded ghost-map element can never move again, so             *)
  (*  [exc_sealed] is a permanent certificate that the exception set is  *)
  (*  empty -- "recovery is done".  It rides [LogInv.log_ctx], hence     *)
  (*  [fs_bytes_any] (below), hence every runtime reader of the tie for  *)
  (*  free: only [initlog]/[install_trans] and [fsinit]'s own pre-       *)
  (*  recovery [readsb] ever run with a nonempty exception set, and      *)
  (*  those three take [exc_own] and a [b ∉ X] premise instead.          *)
  (*                                                                     *)
  (*  WHAT [L] HOLDS ON THE EXCEPTION SET is the LOGGED value, and the   *)
  (*  invariant records it as a FUNCTION [Xv] fixed at allocation (the   *)
  (*  log region is not written during recovery, so it does not move).   *)
  (*  That is what lets the recovering install restore the tie without   *)
  (*  owning the byte run: it writes [Xv b] into the cache and the       *)
  (*  invariant already knows [L] reads [Xv b] there.                    *)
  (* ------------------------------------------------------------------ *)

  (* the authority, inside [fs_bytes_body] *)
  Definition exc_auth (gX : gname) (X : gset Z) : iProp Σ :=
    ghost_map_auth gX 1 ({[ tt := X ]} : gmap unit (gset Z)).

  (* the WAL's exclusive handle *)
  Definition exc_own (gX : gname) (X : gset Z) : iProp Σ :=
    (tt ↪[gX] X)%I.

  (* the PERSISTENT seal: the element, discarded at [∅] *)
  Definition exc_sealed (gX : gname) : iProp Σ :=
    (tt ↪[gX]□ (∅ : gset Z))%I.

  Global Instance exc_auth_timeless gX X : Timeless (exc_auth gX X).
  Proof. apply _. Qed.
  Global Instance exc_own_timeless gX X : Timeless (exc_own gX X).
  Proof. apply _. Qed.
  Global Instance exc_sealed_persistent gX : Persistent (exc_sealed gX).
  Proof. apply _. Qed.
  Global Instance exc_sealed_timeless gX : Timeless (exc_sealed gX).
  Proof. apply _. Qed.

  Lemma exc_alloc (X : gset Z) :
    ⊢ |==> ∃ gX : gname, exc_auth gX X ∗ exc_own gX X.
  Proof.
    iMod (ghost_map_alloc ({[ tt := X ]} : gmap unit (gset Z)))
      as (gX) "[Ha Hf]".
    rewrite big_sepM_singleton. iModIntro. iExists gX. iFrame.
  Qed.

  Lemma exc_agree gX X X' :
    exc_auth gX X -∗ exc_own gX X' -∗ ⌜X = X'⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (ghost_map_lookup with "Ha Hf") as %Hlk.
    rewrite lookup_singleton in Hlk. iPureIntro. congruence.
  Qed.

  (* THE SEAL, READ: a discarded element at [∅] against the authority. *)
  Lemma exc_sealed_empty gX X :
    exc_auth gX X -∗ exc_sealed gX -∗ ⌜X = ∅⌝.
  Proof.
    iIntros "Ha Hs".
    iDestruct (ghost_map_lookup with "Ha Hs") as %Hlk.
    rewrite lookup_singleton in Hlk. iPureIntro. congruence.
  Qed.

  Lemma exc_update gX X X' :
    exc_auth gX X -∗ exc_own gX X ==∗ exc_auth gX X' ∗ exc_own gX X'.
  Proof.
    iIntros "Ha Hf".
    iMod (ghost_map_update X' with "Ha Hf") as "[Ha Hf]".
    rewrite insert_singleton. by iFrame.
  Qed.

  (* ...AND THE SEAL, MADE.  Spending the handle at [∅] persists it. *)
  Lemma exc_seal gX :
    exc_own gX ∅ ==∗ exc_sealed gX.
  Proof. iIntros "Hf". by iMod (ghost_map_elem_persist with "Hf") as "$". Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  THE LOG-LAYER INVARIANT: the cache map against the byte view   *)
  (* ------------------------------------------------------------------ *)

  (* [L] resides exactly the byte range of the covered (home) blocks. *)
  Definition bytes_dom (L : gmap Z (bv 8)) (home : gset Z) : Prop :=
    forall a, is_Some (L !! a)
              <-> exists b, b ∈ home /\ b * BSZ <= a < b * BSZ + BSZ.

  (* every cache entry reads off [L] *)
  Definition bytes_tie (L : gmap Z (bv 8)) (C : gmap Z (list (bv 8))) : Prop :=
    forall b bs, C !! b = Some bs ->
                 (map_seqZ (b * BSZ) bs : gmap Z (bv 8)) ⊆ L.

  (* ...EXCEPTED ON [X] (section 3b): every cache entry OUTSIDE the
     exception set reads off [L].  [bytes_tie] is the [X = ∅] instance. *)
  Definition bytes_tie_exc (L : gmap Z (bv 8)) (C : gmap Z (list (bv 8)))
      (X : gset Z) : Prop :=
    forall b bs, C !! b = Some bs -> b ∉ X ->
                 (map_seqZ (b * BSZ) bs : gmap Z (bv 8)) ⊆ L.

  Lemma bytes_tie_exc_empty L C : bytes_tie_exc L C ∅ <-> bytes_tie L C.
  Proof.
    split.
    - intros H b bs Hb. apply (H b bs Hb). set_solver.
    - intros H b bs Hb _. exact (H b bs Hb).
  Qed.

  (* ON [X], [L] holds the LOGGED value, named by the invariant's own
     function [Xv].  This is what the recovering install reads the tie
     back off when its bwrite lands. *)
  Definition bytes_exc_val (L : gmap Z (bv 8)) (Xv : Z -> list (bv 8))
      (X : gset Z) : Prop :=
    forall b, b ∈ X -> (map_seqZ (b * BSZ) (Xv b) : gmap Z (bv 8)) ⊆ L.

  (* THE BODY.  [gL] is the byte view's name, [gc] the cache's.  The
     invariant holds the byte AUTH and, per home block, the cache
     element's OTHER half -- the half the FS client used to hold.  That
     placement is what keeps [log_state] (the spinlock resource) holding
     the cache auth OUTRIGHT, so the freeze-by-auth during commit, and
     every proof that rides it (write_head, install_trans, end_op's
     write_log), is untouched by the re-keying.

     TIMELESS, and it has to be: [log_write] opens it inside the same
     ghost step that fires the client's atomic update, with no program
     step left to absorb a later. *)
  (* THE EXCEPTION SET RIDES INSIDE (lane E-except): [X] is existential --
     no consumer names it -- and its authority is what the WAL's handle
     [exc_own] moves against.  The two pure rows about it go LAST, after
     [bytes_dom], so every [destruct] of this body that predates the
     window keeps its pattern's prefix. *)
  Definition fs_bytes_body (gL gc gX : gname) (home : gset Z)
      (Xv : Z -> list (bv 8)) : iProp Σ :=
    (∃ (L : gmap Z (bv 8)) (C : gmap Z (list (bv 8))) (X : gset Z),
       ghost_map_auth gL 1 L ∗
       ([∗ map] b ↦ bs ∈ C, b ↪[gc]{#(1/2)} bs) ∗
       exc_auth gX X ∗
       ⌜dom C = home⌝ ∗
       ⌜forall b bs, C !! b = Some bs -> length bs = BSIZE⌝ ∗
       ⌜bytes_tie_exc L C X⌝ ∗ ⌜bytes_dom L home⌝ ∗
       ⌜X ⊆ home⌝ ∗ ⌜bytes_exc_val L Xv X⌝)%I.

  Global Instance fs_bytes_body_timeless gL gc gX home Xv :
    Timeless (fs_bytes_body gL gc gX home Xv).
  Proof. apply _. Qed.

  Definition fs_bytes_inv (gL gc gX : gname) (home : gset Z)
      (Xv : Z -> list (bv 8)) : iProp Σ :=
    inv fsbN (fs_bytes_body gL gc gX home Xv).

  Global Instance fs_bytes_inv_persistent gL gc gX home Xv :
    Persistent (fs_bytes_inv gL gc gX home Xv).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  5.  What a bread client gets: C(b) IS L's bytes at b               *)
  (* ------------------------------------------------------------------ *)

  (* HOLDING THE RUN IS BEING A HOME BLOCK, so neither crossing takes a
     membership premise.  [bytes_dom] says [L] resides EXACTLY the home
     blocks' byte range, and a [fsblock] at [b] resides [b]'s first byte in
     [L]; two block ranges that share a byte are one block
     ([blk_range_disj]).  Deriving it here rather than threading it is what
     keeps every reader above -- the inode region's, the bitmap's, bmap's,
     readi's, writei's -- free of a [gset Z] premise it has no way to
     discharge (bmap holds no covered-ness fact at all). *)
  (* THE lemma the inode layer needs: two owned blocks are distinct.  It is
     [l ↦ _ ∗ l ↦ _ ⊢ False] read as a disequality, exactly as fs-state.md
     section 0 rules -- never a maintained clause. *)
  Lemma fsblock_ne gL b1 b2 bs1 bs2 :
    fsblock gL b1 bs1 -∗ fsblock gL b2 bs2 -∗ ⌜b1 <> b2⌝.
  Proof.
    iIntros "H1 H2". destruct (decide (b1 = b2)) as [->|Hne]; [| done].
    iExFalso. iApply (fsblock_excl with "H1 H2").
  Qed.

  (* AT SUB-BLOCK GRANULARITY (durable-disk 2b-0): owning ANY nonempty run
     inside block [b]'s width is being a home block.  [fsblock_home] is the
     whole-block instance and nothing that uses it moves. *)
  Lemma byte_range_home (gL : gname) (L : gmap Z (bv 8)) (home : gset Z)
      (b : Z) (off : nat) (bs : list (bv 8)) :
    bytes_dom L home ->
    (off < BSIZE)%nat -> (0 < length bs)%nat ->
    ghost_map_auth gL 1 L -∗ byte_range gL b (Z.of_nat off) bs -∗ ⌜b ∈ home⌝.
  Proof.
    iIntros (Hdm Hoff Hpos) "Ha Hr".
    iDestruct (byte_range_lookup with "Ha Hr") as %Hsub.
    assert (Hfst : is_Some ((map_seqZ (b * BSZ + Z.of_nat off) bs
                               : gmap Z (bv 8)) !! (b * BSZ + Z.of_nat off))).
    { apply lookup_map_seqZ_is_Some. lia. }
    destruct Hfst as [v Hv].
    assert (HL : L !! (b * BSZ + Z.of_nat off) = Some v)
      by exact (lookup_weaken _ _ _ _ Hv Hsub).
    destruct (proj1 (Hdm (b * BSZ + Z.of_nat off)) (mk_is_Some _ _ HL))
      as (b' & Hb' & Hr').
    iPureIntro.
    assert (Hoz : Z.of_nat off < BSZ).
    { rewrite -BSZ_BSIZE. apply Nat2Z.inj_lt. exact Hoff. }
    rewrite (blk_range_disj b b' (b * BSZ + Z.of_nat off)
               ltac:(lia) Hr'). exact Hb'.
  Qed.

  Lemma fsblock_home (gL : gname) (L : gmap Z (bv 8)) (home : gset Z)
      (b : Z) (bs : list (bv 8)) :
    bytes_dom L home ->
    ghost_map_auth gL 1 L -∗ fsblock gL b bs -∗ ⌜b ∈ home⌝.
  Proof.
    iIntros (Hdm) "Ha [%Hlb Hr]".
    iApply (byte_range_home gL L home b 0%nat bs Hdm
              BSIZE_pos ltac:(rewrite Hlb; exact BSIZE_pos) with "Ha Hr").
  Qed.

  (* HOLDING THE RUN IS BEING A HOME BLOCK, as a fupd at the row rather
     than at the raw auth: what the bitmap's allocator hands its caller is
     the fresh block's byte run, and [b ∈ home] -- i.e. [b] is covered and
     outside the log's own storage, the two facts bread and log_write
     demand of a block number -- is a CONSEQUENCE of holding it, not a
     clause anybody maintains. *)
  Lemma fsblock_home_open (E : coPset) gL gc gX home Xv b bs :
    ↑logN ⊆ E ->
    fs_bytes_inv gL gc gX home Xv -∗
    fsblock gL b bs ={E}=∗ ⌜b ∈ home⌝ ∗ fsblock gL b bs.
  Proof.
    iIntros (HE) "#Hinv Hfb".
    iMod (inv_acc E fsbN with "Hinv") as "[Hbody Hclose]"; [exact (fsbN_sub E HE) |].
    iDestruct "Hbody" as (L C X)
      ">(Ha & HC & Hxa & %Hdom & %Hlens & %Htie & %Hdm & %Hxs & %Hxv)".
    iDestruct (fsblock_home gL L home b bs Hdm with "Ha Hfb") as %Hb.
    iMod ("Hclose" with "[Ha HC Hxa]") as "_".
    { iApply bi.later_intro. iExists L, C, X. by iFrame. }
    iModIntro. by iFrame.
  Qed.

  (* THE BREAD CLIENT'S CROSSING, AT THE SEAL (lane E-except).  Every
     runtime reader of the tie runs THIS form: the persistent seal says
     the exception set is empty, so the tie holds at every home block and
     no reader carries a membership premise.  The pre-recovery form, which
     takes the WAL's handle and [b ∉ X] instead, is [fs_bytes_agree_exc]
     just below; it has exactly two callers ([fsinit]'s [readsb] and the
     recovering install's own step). *)
  Lemma fs_bytes_agree (E : coPset) gL gc gX home Xv b bs bsm :
    ↑logN ⊆ E ->
    fs_bytes_inv gL gc gX home Xv -∗
    exc_sealed gX -∗
    fsblock gL b bs -∗
    (b ↪[gc]{#(1/2)} bsm) ={E}=∗
      ⌜bsm = bs⌝ ∗ fsblock gL b bs ∗ (b ↪[gc]{#(1/2)} bsm).
  Proof.
    iIntros (HE) "#Hinv #Hseal Hfb Hm".
    iMod (inv_acc E fsbN with "Hinv") as "[Hbody Hclose]"; [exact (fsbN_sub E HE) |].
    iDestruct "Hbody" as (L C X)
      ">(Ha & HC & Hxa & %Hdom & %Hlens & %Htie & %Hdm & %Hxs & %Hxv)".
    iDestruct (exc_sealed_empty with "Hxa Hseal") as %->.
    iDestruct (fsblock_home gL L home b bs Hdm with "Ha Hfb") as %Hb.
    assert (Hin : is_Some (C !! b)).
    { apply elem_of_dom. rewrite Hdom. exact Hb. }
    destruct Hin as [bsi Hbsi].
    iDestruct (big_sepM_lookup_acc _ _ b bsi Hbsi with "HC") as "[Hi Hback]".
    iDestruct (ghost_map_elem_agree with "Hm Hi") as %->.
    iDestruct "Hfb" as "[%Hlb Hr]".
    iDestruct (byte_range_lookup with "Ha Hr") as %Hsub.
    rewrite Z.add_0_r in Hsub.
    assert (Hbe : bs = bsi).
    { apply (map_seqZ_inj bs bsi (b * BSZ) L); [| exact Hsub |].
      - rewrite Hlb (Hlens b bsi Hbsi) //.
      - exact (Htie b bsi Hbsi ltac:(set_solver)). }
    iMod ("Hclose" with "[Ha Hback Hi Hxa]") as "_".
    { iApply bi.later_intro. iExists L, C, ∅. iFrame "Ha Hxa". iSplitL; [by iApply "Hback" |].
      iPureIntro. auto 10. }
    iModIntro. iFrame "Hm". rewrite /fsblock. iFrame "Hr".
    iSplit; [iPureIntro; congruence | done].
  Qed.

  (* ...AND THE SAME CROSSING INSIDE THE RECOVERY WINDOW: the WAL's handle
     names the exception set and the caller says its block is outside it.
     The handle comes back untouched. *)
  Lemma fs_bytes_agree_exc (E : coPset) gL gc gX home Xv (X : gset Z)
      b bs bsm :
    ↑logN ⊆ E -> b ∉ X ->
    fs_bytes_inv gL gc gX home Xv -∗
    exc_own gX X -∗
    fsblock gL b bs -∗
    (b ↪[gc]{#(1/2)} bsm) ={E}=∗
      ⌜bsm = bs⌝ ∗ exc_own gX X ∗ fsblock gL b bs ∗ (b ↪[gc]{#(1/2)} bsm).
  Proof.
    iIntros (HE Hnin) "#Hinv Hxo Hfb Hm".
    iMod (inv_acc E fsbN with "Hinv") as "[Hbody Hclose]"; [exact (fsbN_sub E HE) |].
    iDestruct "Hbody" as (L C X0)
      ">(Ha & HC & Hxa & %Hdom & %Hlens & %Htie & %Hdm & %Hxs & %Hxv)".
    iDestruct (exc_agree with "Hxa Hxo") as %->.
    iDestruct (fsblock_home gL L home b bs Hdm with "Ha Hfb") as %Hb.
    assert (Hin : is_Some (C !! b)).
    { apply elem_of_dom. rewrite Hdom. exact Hb. }
    destruct Hin as [bsi Hbsi].
    iDestruct (big_sepM_lookup_acc _ _ b bsi Hbsi with "HC") as "[Hi Hback]".
    iDestruct (ghost_map_elem_agree with "Hm Hi") as %->.
    iDestruct "Hfb" as "[%Hlb Hr]".
    iDestruct (byte_range_lookup with "Ha Hr") as %Hsub.
    rewrite Z.add_0_r in Hsub.
    assert (Hbe : bs = bsi).
    { apply (map_seqZ_inj bs bsi (b * BSZ) L); [| exact Hsub |].
      - rewrite Hlb (Hlens b bsi Hbsi) //.
      - exact (Htie b bsi Hbsi Hnin). }
    iMod ("Hclose" with "[Ha Hback Hi Hxa]") as "_".
    { iApply bi.later_intro. iExists L, C, X. iFrame "Ha Hxa". iSplitL; [by iApply "Hback" |].
      iPureIntro. auto 10. }
    iModIntro. iFrame "Hm Hxo". rewrite /fsblock. iFrame "Hr".
    iSplit; [iPureIntro; congruence | done].
  Qed.

  (* ---- THE SAME TWO CROSSINGS AT A SHARE (lane B''-blk) -------------- *)

  (* Holding ANY nonempty run inside block [b]'s width is being a home
     block, and that reading is an AGREEMENT against the byte auth, so it
     survives any share.  This is what makes a read-locker's quarter enough
     to bread its own data block. *)
  Lemma byte_range_q_home (gL : gname) (dq : dfrac) (L : gmap Z (bv 8))
      (home : gset Z) (b : Z) (off : nat) (bs : list (bv 8)) :
    bytes_dom L home ->
    (off < BSIZE)%nat -> (0 < length bs)%nat ->
    ghost_map_auth gL 1 L -∗ byte_range_q gL dq b (Z.of_nat off) bs -∗
    ⌜b ∈ home⌝.
  Proof.
    iIntros (Hdm Hoff Hpos) "Ha Hr".
    iDestruct (byte_range_q_lookup with "Ha Hr") as %Hsub.
    assert (Hfst : is_Some ((map_seqZ (b * BSZ + Z.of_nat off) bs
                               : gmap Z (bv 8)) !! (b * BSZ + Z.of_nat off))).
    { apply lookup_map_seqZ_is_Some. lia. }
    destruct Hfst as [v Hv].
    assert (HL : L !! (b * BSZ + Z.of_nat off) = Some v)
      by exact (lookup_weaken _ _ _ _ Hv Hsub).
    destruct (proj1 (Hdm (b * BSZ + Z.of_nat off)) (mk_is_Some _ _ HL))
      as (b' & Hb' & Hr').
    iPureIntro.
    assert (Hoz : Z.of_nat off < BSZ).
    { rewrite -BSZ_BSIZE. apply Nat2Z.inj_lt. exact Hoff. }
    rewrite (blk_range_disj b b' (b * BSZ + Z.of_nat off)
               ltac:(lia) Hr'). exact Hb'.
  Qed.

  Lemma fsblock_q_home (gL : gname) (dq : dfrac) (L : gmap Z (bv 8))
      (home : gset Z) (b : Z) (bs : list (bv 8)) :
    bytes_dom L home ->
    ghost_map_auth gL 1 L -∗ fsblock_q gL dq b bs -∗ ⌜b ∈ home⌝.
  Proof.
    iIntros (Hdm) "Ha [%Hlb Hr]".
    iApply (byte_range_q_home gL dq L home b 0%nat bs Hdm
              BSIZE_pos ltac:(rewrite Hlb; exact BSIZE_pos) with "Ha Hr").
  Qed.

  Lemma fsblock_q_home_open (E : coPset) gL dq gc gX home Xv b bs :
    ↑logN ⊆ E ->
    fs_bytes_inv gL gc gX home Xv -∗
    fsblock_q gL dq b bs ={E}=∗ ⌜b ∈ home⌝ ∗ fsblock_q gL dq b bs.
  Proof.
    iIntros (HE) "#Hinv Hfb".
    iMod (inv_acc E fsbN with "Hinv") as "[Hbody Hclose]"; [exact (fsbN_sub E HE) |].
    iDestruct "Hbody" as (L C X)
      ">(Ha & HC & Hxa & %Hdom & %Hlens & %Htie & %Hdm & %Hxs & %Hxv)".
    iDestruct (fsblock_q_home gL dq L home b bs Hdm with "Ha Hfb") as %Hb.
    iMod ("Hclose" with "[Ha HC Hxa]") as "_".
    { iApply bi.later_intro. iExists L, C, X. by iFrame. }
    iModIntro. by iFrame.
  Qed.

  (* THE BREAD CLIENT'S CROSSING AT A SHARE.  [fs_bytes_agree] verbatim with
     [fsblock_q] in place of [fsblock]: every step of it is a lookup against
     the byte auth or the cache half, and neither is a share of the byte
     run, so the quarter goes through unchanged. *)
  Lemma fs_bytes_agree_q (E : coPset) gL dq gc gX home Xv b bs bsm :
    ↑logN ⊆ E ->
    fs_bytes_inv gL gc gX home Xv -∗
    exc_sealed gX -∗
    fsblock_q gL dq b bs -∗
    (b ↪[gc]{#(1/2)} bsm) ={E}=∗
      ⌜bsm = bs⌝ ∗ fsblock_q gL dq b bs ∗ (b ↪[gc]{#(1/2)} bsm).
  Proof.
    iIntros (HE) "#Hinv #Hseal Hfb Hm".
    iMod (inv_acc E fsbN with "Hinv") as "[Hbody Hclose]"; [exact (fsbN_sub E HE) |].
    iDestruct "Hbody" as (L C X)
      ">(Ha & HC & Hxa & %Hdom & %Hlens & %Htie & %Hdm & %Hxs & %Hxv)".
    iDestruct (exc_sealed_empty with "Hxa Hseal") as %->.
    iDestruct (fsblock_q_home gL dq L home b bs Hdm with "Ha Hfb") as %Hb.
    assert (Hin : is_Some (C !! b)).
    { apply elem_of_dom. rewrite Hdom. exact Hb. }
    destruct Hin as [bsi Hbsi].
    iDestruct (big_sepM_lookup_acc _ _ b bsi Hbsi with "HC") as "[Hi Hback]".
    iDestruct (ghost_map_elem_agree with "Hm Hi") as %->.
    iDestruct "Hfb" as "[%Hlb Hr]".
    iDestruct (byte_range_q_lookup with "Ha Hr") as %Hsub.
    rewrite Z.add_0_r in Hsub.
    assert (Hbe : bs = bsi).
    { apply (map_seqZ_inj bs bsi (b * BSZ) L); [| exact Hsub |].
      - rewrite Hlb (Hlens b bsi Hbsi) //.
      - exact (Htie b bsi Hbsi ltac:(set_solver)). }
    iMod ("Hclose" with "[Ha Hback Hi Hxa]") as "_".
    { iApply bi.later_intro. iExists L, C, ∅. iFrame "Ha Hxa". iSplitL; [by iApply "Hback" |].
      iPureIntro. auto 10. }
    iModIntro. iFrame "Hm". rewrite /fsblock_q. iFrame "Hr".
    iSplit; [iPureIntro; congruence | done].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  6.  log_write's ghost step, AT BYTE-RANGE GRANULARITY              *)
  (*                                                                     *)
  (*  The writer presents ONLY the sub-range it owns ([sub_old] at        *)
  (*  [off]) plus the handle's cache half; the log presents the cache     *)
  (*  auth (it holds log.lock); the invariant supplies the cache          *)
  (*  element's other half and the byte auth.  THE OTHER 960 BYTES ARE    *)
  (*  LEARNED, NEVER PRESENTED: the cache entry is [L] read at the        *)
  (*  block's whole range ([bytes_tie]) and the writer's run is [L] read  *)
  (*  at its own, so [map_seqZ_slice] identifies the writer's bytes with  *)
  (*  the slice of the checked-out buffer -- which is what makes an       *)
  (*  inode record's 64 bytes (or a dirent's 16) enough to log_write the  *)
  (*  whole block.  The new cache content is the SPLICE, i.e. exactly     *)
  (*  what the writer's own stores produced.                             *)
  (*                                                                     *)
  (*  [length sub_new = length sub_old] is GUARDED by the block's width   *)
  (*  because the width is not known until the invariant is open; the     *)
  (*  whole-block corollary below is what that guard buys (it has no      *)
  (*  [length bsm] premise to give).                                      *)
  (* ------------------------------------------------------------------ *)

  Lemma byte_range_log_update (E : coPset) gL gc gX home Xv
      (C : gmap Z (list (bv 8)))
      (b : Z) (off : nat) (sub_old sub_new bs_old : list (bv 8)) :
    ↑logN ⊆ E ->
    (off + length sub_old <= BSIZE)%nat ->
    (0 < length sub_old)%nat ->
    (length bs_old = BSIZE -> length sub_new = length sub_old) ->
    fs_bytes_inv gL gc gX home Xv -∗
    exc_sealed gX -∗
    ghost_map_auth gc 1 C -∗
    byte_range gL b (Z.of_nat off) sub_old -∗
    (b ↪[gc]{#(1/2)} bs_old) ={E}=∗
      ⌜C !! b = Some bs_old /\ length bs_old = BSIZE /\
        sub_old = take (length sub_old) (drop off bs_old)⌝ ∗
      ghost_map_auth gc 1 (<[b := blk_splice off sub_new bs_old]> C) ∗
      byte_range gL b (Z.of_nat off) sub_new ∗
      (b ↪[gc]{#(1/2)} blk_splice off sub_new bs_old).
  Proof.
    iIntros (HE Hoff Hpos Hshape) "#Hinv #Hseal Hca Hr Hm".
    iMod (inv_acc E fsbN with "Hinv") as "[Hbody Hclose]"; [exact (fsbN_sub E HE) |].
    iDestruct "Hbody" as (L C0 X)
      ">(Ha & HC & Hxa & %Hdom & %Hlens & %Htie0 & %Hdm & %Hxs & %Hxv)".
    iDestruct (exc_sealed_empty with "Hxa Hseal") as %->.
    assert (Htie : bytes_tie L C0)
      by (apply bytes_tie_exc_empty; exact Htie0).
    iDestruct (byte_range_home gL L home b off sub_old Hdm
                 ltac:(lia) Hpos with "Ha Hr") as %Hb.
    assert (Hin : is_Some (C0 !! b)).
    { apply elem_of_dom. rewrite Hdom. exact Hb. }
    destruct Hin as [bsi Hbsi].
    iDestruct (big_sepM_insert_acc _ _ b bsi Hbsi with "HC") as "[Hi Hback]".
    iDestruct (ghost_map_elem_agree with "Hm Hi") as %Hbso.
    subst bsi.
    assert (Hlbo : length bs_old = BSIZE) by exact (Hlens b bs_old Hbsi).
    specialize (Hshape Hlbo).
    iDestruct (byte_range_lookup with "Ha Hr") as %Hsub.
    (* THE 960 BYTES, LEARNED *)
    assert (Hslice : sub_old = take (length sub_old) (drop off bs_old)).
    { apply (map_seqZ_slice bs_old sub_old (b * BSZ) off L);
        [rewrite Hlbo; lia | exact (Htie b bs_old Hbsi) | exact Hsub]. }
    assert (Hlsp : length (blk_splice off sub_new bs_old) = BSIZE).
    { rewrite blk_splice_length; [exact Hlbo | rewrite Hshape Hlbo; lia]. }
    (* the cache element moves: both halves plus the log's auth *)
    iCombine "Hm Hi" as "He".
    iDestruct (ghost_map_lookup with "Hca He") as %Hclk.
    iMod (ghost_map_update (blk_splice off sub_new bs_old) with "Hca He")
      as "[Hca He]".
    iDestruct "He" as "[Hm Hi]".
    (* the byte view moves ON EXACTLY THE WRITER'S BYTES *)
    iMod (byte_range_update gL L b (Z.of_nat off) sub_old sub_new
            Hshape with "Ha Hr") as "[Ha Hr]".
    (* the new keys are the old ones: same start, same length *)
    assert (Hdomeq : dom (map_seqZ (b * BSZ + Z.of_nat off) sub_new
                            : gmap Z (bv 8))
                     = dom (map_seqZ (b * BSZ + Z.of_nat off) sub_old
                              : gmap Z (bv 8))).
    { apply set_eq. intros a.
      rewrite !elem_of_dom !lookup_map_seqZ_is_Some. rewrite Hshape. done. }
    assert (Hnew_sub : dom (map_seqZ (b * BSZ + Z.of_nat off) sub_new
                              : gmap Z (bv 8)) ⊆ dom L).
    { rewrite Hdomeq. apply subseteq_dom. exact Hsub. }
    assert (Hoz : Z.of_nat off + Z.of_nat (length sub_old) <= BSZ).
    { rewrite -BSZ_BSIZE -Nat2Z.inj_add. apply Nat2Z.inj_le. lia. }
    assert (Hrange : forall a,
              is_Some ((map_seqZ (b * BSZ + Z.of_nat off) sub_new
                          : gmap Z (bv 8)) !! a) ->
              b * BSZ <= a < b * BSZ + BSZ).
    { intros a Hs. apply lookup_map_seqZ_is_Some in Hs.
      rewrite Hshape in Hs. lia. }
    (* the spliced block still reads off the moved authority *)
    assert (Htieb : (map_seqZ (b * BSZ) (blk_splice off sub_new bs_old)
                       : gmap Z (bv 8))
                    ⊆ (map_seqZ (b * BSZ + Z.of_nat off) sub_new
                         : gmap Z (bv 8)) ∪ L).
    { apply map_subseteq_spec. intros a v Hav.
      apply lookup_map_seqZ_Some in Hav as [Hge Hlk].
      destruct (decide (off <= Z.to_nat (a - b * BSZ)
                        /\ Z.to_nat (a - b * BSZ) < off + length sub_new)%nat)
        as [[Hj1 Hj2] | Hjout].
      - (* inside the writer's own run: the left map has it *)
        rewrite blk_splice_lookup_mid in Hlk; [| lia | lia | lia].
        apply lookup_union_Some_raw. left.
        apply lookup_map_seqZ_Some. split; [lia |].
        replace (Z.to_nat (a - (b * BSZ + Z.of_nat off)))
          with (Z.to_nat (a - b * BSZ) - off)%nat by lia.
        exact Hlk.
      - (* outside it: the byte is the checked-out buffer's, hence [L]'s *)
        assert (Hbsl : bs_old !! Z.to_nat (a - b * BSZ) = Some v).
        { destruct (decide (Z.to_nat (a - b * BSZ) < off)%nat) as [Hlt | Hge2].
          - rewrite blk_splice_lookup_lt in Hlk; [exact Hlk | lia | lia].
          - rewrite blk_splice_lookup_ge in Hlk; [exact Hlk | lia | lia]. }
        apply lookup_union_Some_raw. right. split.
        + apply eq_None_not_Some. intros Hs.
          apply lookup_map_seqZ_is_Some in Hs. lia.
        + pose proof (map_subseteq_spec
                        (map_seqZ (b * BSZ) bs_old : gmap Z (bv 8)) L) as [Hs _].
          apply (Hs (Htie b bs_old Hbsi) a v).
          apply lookup_map_seqZ_Some. split; [lia | exact Hbsl]. }
    iMod ("Hclose" with "[Ha Hback Hi Hxa]") as "_".
    { iApply bi.later_intro.
      iExists ((map_seqZ (b * BSZ + Z.of_nat off) sub_new : gmap Z (bv 8)) ∪ L),
              (<[b := blk_splice off sub_new bs_old]> C0), ∅.
      iFrame "Ha Hxa".
      iSplitL.
      { iApply ("Hback" with "Hi"). }
      iPureIntro.
      split; [| split; [| split; [| split; [| split]]]].
      - rewrite dom_insert_L Hdom.
        assert (Hbh : b ∈ home) by exact Hb. set_solver.
      - intros b' bs' Hb'.
        destruct (decide (b' = b)) as [->|Hne].
        + rewrite lookup_insert in Hb'. congruence.
        + rewrite lookup_insert_ne in Hb'; [| done]. exact (Hlens b' bs' Hb').
      - intros b' bs' Hb' _.
        destruct (decide (b' = b)) as [->|Hne].
        + rewrite lookup_insert in Hb'. injection Hb' as <-. exact Htieb.
        + rewrite lookup_insert_ne in Hb'; [| done].
          apply map_subseteq_spec. intros a v Hav.
          apply lookup_union_Some_raw. right. split.
          * apply eq_None_not_Some. intros Hs.
            pose proof (Hrange a Hs) as Hrg.
            apply lookup_map_seqZ_Some in Hav as [Hge Hlk].
            assert (Hlt : a < b' * BSZ + BSZ).
            { apply lookup_lt_Some in Hlk.
              rewrite (Hlens b' bs' Hb') in Hlk.
              revert Hlk. rewrite -BSZ_BSIZE. lia. }
            exact (Hne (blk_range_disj b' b a (conj Hge Hlt) Hrg)).
          * pose proof (map_subseteq_spec
                          (map_seqZ (b' * BSZ) bs' : gmap Z (bv 8)) L) as [Hs _].
            exact (Hs (Htie b' bs' Hb') a v Hav).
      - intros a. rewrite -Hdm. split.
        + intros [v Hv]. apply lookup_union_Some_raw in Hv as [Hv | [_ Hv]].
          * apply elem_of_dom. apply Hnew_sub. apply elem_of_dom. by exists v.
          * by exists v.
        + intros Hs. apply lookup_union_is_Some. by right.
      - set_solver.
      - intros b'' Hb''. set_solver. }
    iModIntro. iFrame "Hca Hm Hr". iPureIntro. auto.
  Qed.

  (* THE WHOLE-BLOCK COROLLARY, at its old statement so that nothing which
     uses it moves: the writer that happens to own the entire run presents
     it at [off = 0], and the splice of a full-width run IS that run. *)
  Lemma fsblock_update (E : coPset) gL gc gX home Xv (C : gmap Z (list (bv 8)))
      (b : Z) (bs bs_new bsm : list (bv 8)) :
    ↑logN ⊆ E -> length bs_new = BSIZE ->
    fs_bytes_inv gL gc gX home Xv -∗
    exc_sealed gX -∗
    ghost_map_auth gc 1 C -∗
    fsblock gL b bs -∗
    (b ↪[gc]{#(1/2)} bsm) ={E}=∗
      ⌜bsm = bs /\ C !! b = Some bs⌝ ∗
      ghost_map_auth gc 1 (<[b := bs_new]> C) ∗
      fsblock gL b bs_new ∗
      (b ↪[gc]{#(1/2)} bs_new).
  Proof.
    iIntros (HE Hlnew) "#Hinv #Hseal Hca Hfb Hm".
    iDestruct "Hfb" as "[%Hlb Hr]".
    iMod (byte_range_log_update E gL gc gX home Xv C b 0%nat bs bs_new bsm HE
            ltac:(rewrite Hlb; lia) ltac:(rewrite Hlb; exact BSIZE_pos)
            ltac:(intros Hbm; rewrite Hlnew Hlb //)
            with "Hinv Hseal Hca Hr Hm")
      as "((%Hclk & %Hlbm & %Hslice) & Hca & Hr & Hm)".
    (* the buffer's parked bytes ARE the writer's run: [take BSIZE] of a
       block-wide list is the list *)
    assert (Hbe : bsm = bs).
    { rewrite Hslice drop_0 Hlb. symmetry. apply take_ge. lia. }
    assert (Hsp : blk_splice 0 bs_new bsm = bs_new).
    { apply blk_splice_whole. rewrite Hlnew Hlbm //. }
    iEval (rewrite Hsp) in "Hca". iEval (rewrite Hsp) in "Hm".
    iModIntro. rewrite /fsblock.
    iSplitR; [iPureIntro; split; [exact Hbe | rewrite -Hbe; exact Hclk] |].
    iFrame "Hca Hm Hr". iPureIntro. exact Hlnew.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  6b.  THE RECOVERING INSTALL'S GHOST STEP (lane E-except)           *)
  (*                                                                     *)
  (*  The one step that SHRINKS the exception set, and the reason the     *)
  (*  window can be carried at all: the byte view does NOT move (it was   *)
  (*  minted at the committed view, so it already reads the logged value  *)
  (*  at [b]); what moves is the CACHE map, from the crashed bytes to     *)
  (*  [Xv b] -- exactly what the home [bwrite] just put on the disk --    *)
  (*  and that is what makes the tie true at [b] again.  So this step     *)
  (*  needs NO byte run: the file system already owns [b]'s, at the value *)
  (*  the install is landing.  That is the whole content of exit (1).     *)
  (* ------------------------------------------------------------------ *)
  Lemma fsblock_install_exc (E : coPset) gL gc gX home Xv
      (C : gmap Z (list (bv 8))) (X : gset Z) (b : Z) (bsm : list (bv 8)) :
    ↑logN ⊆ E -> b ∈ X -> length (Xv b) = BSIZE ->
    fs_bytes_inv gL gc gX home Xv -∗
    exc_own gX X -∗
    ghost_map_auth gc 1 C -∗
    (b ↪[gc]{#(1/2)} bsm) ={E}=∗
      ⌜C !! b = Some bsm⌝ ∗
      exc_own gX (X ∖ {[b]}) ∗
      ghost_map_auth gc 1 (<[b := Xv b]> C) ∗
      (b ↪[gc]{#(1/2)} Xv b).
  Proof.
    iIntros (HE Hb HlXv) "#Hinv Hxo Hca Hm".
    iMod (inv_acc E fsbN with "Hinv") as "[Hbody Hclose]"; [exact (fsbN_sub E HE) |].
    iDestruct "Hbody" as (L C0 X0)
      ">(Ha & HC & Hxa & %Hdom & %Hlens & %Htie & %Hdm & %Hxs & %Hxv)".
    iDestruct (exc_agree with "Hxa Hxo") as %->.
    assert (Hbh : b ∈ home) by (apply Hxs; exact Hb).
    assert (Hin : is_Some (C0 !! b)).
    { apply elem_of_dom. rewrite Hdom. exact Hbh. }
    destruct Hin as [bsi Hbsi].
    iDestruct (big_sepM_insert_acc _ _ b bsi Hbsi with "HC") as "[Hi Hback]".
    iDestruct (ghost_map_elem_agree with "Hm Hi") as %Hbso.
    subst bsi.
    iCombine "Hm Hi" as "He".
    iDestruct (ghost_map_lookup with "Hca He") as %Hclk.
    iMod (ghost_map_update (Xv b) with "Hca He") as "[Hca He]".
    iDestruct "He" as "[Hm Hi]".
    iMod (exc_update gX X (X ∖ {[b]}) with "Hxa Hxo") as "[Hxa Hxo]".
    iMod ("Hclose" with "[Ha Hback Hi Hxa]") as "_".
    { iApply bi.later_intro. iExists L, (<[b := Xv b]> C0), (X ∖ {[b]}).
      iFrame "Ha Hxa".
      iSplitL. { iApply ("Hback" with "Hi"). }
      iPureIntro. split; [| split; [| split; [| split; [| split]]]].
      - rewrite dom_insert_L Hdom. set_solver.
      - intros b' bs' Hb'.
        destruct (decide (b' = b)) as [->|Hne].
        + rewrite lookup_insert in Hb'. injection Hb' as <-. exact HlXv.
        + rewrite lookup_insert_ne in Hb'; [| done]. exact (Hlens b' bs' Hb').
      - intros b' bs' Hb' Hnin.
        destruct (decide (b' = b)) as [->|Hne].
        + rewrite lookup_insert in Hb'. injection Hb' as <-. exact (Hxv b Hb).
        + rewrite lookup_insert_ne in Hb'; [| done].
          apply (Htie b' bs' Hb'). set_solver.
      - exact Hdm.
      - set_solver.
      - intros b'' Hb''. apply Hxv. set_solver. }
    iModIntro. iFrame "Hxo Hca Hm". iPureIntro. exact Hclk.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  7.  THE MINT                                                       *)
  (*                                                                     *)
  (*  The byte view is born from the cache map: one FULL byte run per     *)
  (*  home block, and the cache elements' spare halves are swallowed by   *)
  (*  the invariant on the way in.  This is what the boot-time            *)
  (*  distribution calls once, in place of handing every FS client a      *)
  (*  block half.                                                        *)
  (* ------------------------------------------------------------------ *)

  Lemma byte_map_grow (gL : gname) (C : gmap Z (list (bv 8)))
      (L0 : gmap Z (bv 8)) (h0 : gset Z) :
    (forall b bs, C !! b = Some bs -> length bs = BSIZE) ->
    (forall b, b ∈ dom C -> b ∉ h0) ->
    bytes_dom L0 h0 ->
    ghost_map_auth gL 1 L0 ==∗
    ∃ L : gmap Z (bv 8),
      ⌜bytes_dom L (h0 ∪ dom C)⌝ ∗ ⌜bytes_tie L C⌝ ∗
      ghost_map_auth gL 1 L ∗ ([∗ map] b ↦ bs ∈ C, fsblock gL b bs).
  Proof.
    revert L0 h0.
    induction C as [|b bs C' Hb IH] using map_ind;
      intros L0 h0 Hlen Hfresh Hdm.
    - iIntros "Ha". iModIntro. iExists L0.
      rewrite dom_empty_L right_id_L big_sepM_empty.
      iFrame "Ha". iPureIntro. split; [exact Hdm |].
      intros b' bs' Hb'. rewrite lookup_empty in Hb'. done.
    - iIntros "Ha".
      iMod (IH L0 h0 with "Ha") as (L') "(%Hdm' & %Htie' & Ha & HC)".
      { intros b' bs' Hb'. apply (Hlen b' bs').
        rewrite lookup_insert_ne; [done |]. congruence. }
      { intros b' Hb'. apply Hfresh. rewrite dom_insert_L. set_solver. }
      { exact Hdm. }
      (* the new block's byte run is fresh *)
      assert (Hbnot : b ∉ h0 ∪ dom C').
      { intros Hin. apply elem_of_union in Hin as [Hin | Hin].
        - apply (Hfresh b); [| exact Hin]. rewrite dom_insert_L. set_solver.
        - apply elem_of_dom in Hin as [x Hx]. congruence. }
      assert (Hlb : length bs = BSIZE).
      { apply (Hlen b bs). by rewrite lookup_insert. }
      assert (Hdisj : (map_seqZ (b * BSZ) bs : gmap Z (bv 8)) ##ₘ L').
      { apply map_disjoint_spec. intros a v1 v2 H1 H2.
        assert (Hr1 : b * BSZ <= a < b * BSZ + BSZ).
        { assert (Hs1 : is_Some ((map_seqZ (b * BSZ) bs : gmap Z (bv 8)) !! a))
            by (by exists v1).
          apply lookup_map_seqZ_is_Some in Hs1.
          rewrite Hlb BSZ_BSIZE in Hs1. exact Hs1. }
        assert (Hs : is_Some (L' !! a)) by (by exists v2).
        apply Hdm' in Hs as (b'' & Hb'' & Hr2).
        apply Hbnot. rewrite (blk_range_disj b b'' a Hr1 Hr2). exact Hb''. }
      iMod (ghost_map_insert_big
              (map_seqZ (b * BSZ) bs : gmap Z (bv 8)) Hdisj with "Ha")
        as "[Ha Hnew]".
      iModIntro.
      iExists ((map_seqZ (b * BSZ) bs : gmap Z (bv 8)) ∪ L').
      iSplitR.
      { iPureIntro. intros a. split.
        - intros Hs. apply lookup_union_is_Some in Hs as [Hs | Hs].
          + exists b. split.
            * rewrite dom_insert_L. set_solver.
            * apply lookup_map_seqZ_is_Some in Hs.
              rewrite Hlb BSZ_BSIZE in Hs. exact Hs.
          + apply Hdm' in Hs as (b'' & Hb'' & Hr).
            exists b''. split; [| exact Hr].
            rewrite dom_insert_L. set_solver.
        - intros (b'' & Hb'' & Hr). apply lookup_union_is_Some.
          rewrite dom_insert_L in Hb''.
          destruct (decide (b'' = b)) as [->|Hne].
          + left. apply lookup_map_seqZ_is_Some.
            rewrite Hlb BSZ_BSIZE. exact Hr.
          + right. apply Hdm'. exists b''. split; [| exact Hr]. set_solver. }
      iSplitR.
      { iPureIntro. intros b' bs' Hb'.
        destruct (decide (b' = b)) as [->|Hne].
        - rewrite lookup_insert in Hb'. injection Hb' as <-.
          apply map_union_subseteq_l.
        - rewrite lookup_insert_ne in Hb'; [| done].
          etrans; [exact (Htie' b' bs' Hb') |].
          by apply map_union_subseteq_r. }
      iFrame "Ha".
      rewrite big_sepM_insert; [| exact Hb].
      iSplitL "Hnew".
      { rewrite /fsblock /byte_range.
        iSplitR; [iPureIntro; exact Hlb |].
        rewrite big_sepM_map_seqZ.
        iApply (big_sepL_proper with "Hnew"). intros k y _.
        assert (Hz : b * BSZ + Z.of_nat k = b * BSZ + 0 + Z.of_nat k) by lia.
        rewrite Hz //. }
      iExact "HC".
  Qed.

  (* THE MINT, AT A VALUE FUNCTION AND AN EXCEPTION SET (lane E-except).
     [C] is the cache map the era boots on -- the RAW covered blocks --
     and [Bv] is what the BYTE view is minted at: the committed view
     [FsCrash.fr_D], which differs from [C] exactly on the pending set
     [X].  Outside [X] the two agree, which is the fourth premise and is
     what makes the tie true there at birth; on [X] the invariant records
     [Bv] as its own [Xv], which is what the recovering install reads the
     tie back off block by block.  At a CLEAN header [X = ∅], [Bv] is the
     raw content and this is the old statement. *)
  Lemma fs_bytes_alloc (E : coPset) (gc : gname) (C : gmap Z (list (bv 8)))
      (Bv : Z -> list (bv 8)) (X : gset Z) :
    (forall b bs, C !! b = Some bs -> length bs = BSIZE) ->
    (forall b, b ∈ dom C -> length (Bv b) = BSIZE) ->
    X ⊆ dom C ->
    (forall b bs, C !! b = Some bs -> b ∉ X -> Bv b = bs) ->
    ([∗ map] b ↦ bs ∈ C, b ↪[gc]{#(1/2)} bs) ={E}=∗
      ∃ gL gX : gname,
        fs_bytes_inv gL gc gX (dom C) Bv ∗
        exc_own gX X ∗
        ([∗ map] b ↦ bs ∈ C, fsblock gL b (Bv b)).
  Proof.
    iIntros (Hlen HlB HXsub Hagr) "HC".
    (* the byte view's own value map: [C]'s domain, [Bv]'s values *)
    set (B := map_imap (fun (k : Z) (_ : list (bv 8)) => Some (Bv k)) C).
    assert (HBlk : forall b, B !! b = (fun _ => Bv b) <$> (C !! b)).
    { intros b. subst B. rewrite map_lookup_imap.
      destruct (C !! b) as [x|]; done. }
    assert (HBdom : dom B = dom C).
    { apply set_eq. intros b. rewrite !elem_of_dom HBlk.
      destruct (C !! b); split; intros [? ?]; try done; by eexists. }
    assert (HBlen : forall b bs, B !! b = Some bs -> length bs = BSIZE).
    { intros b bs Hb. rewrite HBlk in Hb.
      destruct (C !! b) as [x|] eqn:Hc; [| done].
      cbn in Hb. injection Hb as <-. apply HlB, elem_of_dom. by exists x. }
    iMod (ghost_map_alloc_empty (K := Z) (V := bv 8)) as (gL) "Ha".
    iMod (byte_map_grow gL B ∅ ∅ HBlen with "Ha")
      as (L) "(%Hdm & %Htie & Ha & Hfb)".
    { intros b' _. set_solver. }
    { intros a. split.
      - intros [v Hv]. rewrite lookup_empty in Hv. done.
      - intros (b' & Hb' & _). set_solver. }
    rewrite left_id_L HBdom in Hdm.
    iMod (exc_alloc X) as (gX) "[Hxa Hxo]".
    iMod (inv_alloc fsbN E (fs_bytes_body gL gc gX (dom C) Bv)
            with "[Ha HC Hxa]") as "#Hinv".
    { iApply bi.later_intro. iExists L, C, X. iFrame "Ha HC Hxa". iPureIntro.
      split; [done |]. split; [exact Hlen |].
      split; [| split; [exact Hdm | split; [exact HXsub |]]].
      - intros b bs Hb Hnin.
        rewrite -(Hagr b bs Hb Hnin).
        apply (Htie b (Bv b)). rewrite HBlk Hb //.
      - intros b Hb.
        apply (Htie b (Bv b)). rewrite HBlk.
        destruct (proj1 (elem_of_dom C b) (HXsub b Hb)) as [x Hx].
        rewrite Hx //. }
    iModIntro. iExists gL, gX. iFrame "Hinv Hxo".
    rewrite (big_sepM_dom (fun b => fsblock gL b (Bv b)) C) -HBdom
            -(big_sepM_dom (fun b => fsblock gL b (Bv b)) B).
    iApply (big_sepM_mono with "Hfb"). intros b bs Hb.
    rewrite HBlk in Hb. destruct (C !! b) as [x|] eqn:Hc; [| done].
    cbn in Hb. injection Hb as <-. done.
  Qed.

End FsBytes.

(* SEALED AGAINST TYPECLASS RESOLUTION, AND IT HAS TO BE.  [fsblock] is a
   1024-element [big_sepL] under two [Definition]s, and [iFrame] resolves
   its [Frame] instances up to delta: point a bare [iFrame] at a goal
   holding [fsblock gL b (bitmap_bytes used)] and it unfolds through
   [byte_range] into the whole run and does not come back -- measured, as a
   [BitmapInv.bitmap_res_close] that ran past ten minutes with no error
   (durable-notes: a per-file build over five minutes is a bug).  Sealing
   the two heads leaves [rewrite /fsblock] and the declared [Timeless]
   instances working and makes [iFrame] treat a block run as one atom,
   which is what every consumer above the log wants of it. *)
Global Typeclasses Opaque byte_range fsblock byte_range_q fsblock_q.

(* ===================================================================== *)
(*  THE ERA'S MINT  (durable-disk 1c-flip, step 1)                        *)
(*                                                                       *)
(*  One lemma allocates every ghost the block layer owns and splits its   *)
(*  per-block output along the HOME/LOG-REGION line, because that line is *)
(*  where the two views part company:                                    *)
(*                                                                       *)
(*    - a HOME block ([b] in [home]) belongs to the file system, so its   *)
(*      client resource is the EXCLUSIVE byte run [fsblock fs_bytes];     *)
(*      its parked cache half is swallowed by [fs_bytes_inv] on the way   *)
(*      in and no mortal ever holds one again;                           *)
(*    - a LOG-REGION block is the log's OWN storage, which is not in the  *)
(*      file system's byte view at all ([home] is [cov] minus             *)
(*      [log_region_set]), so it keeps the parked cache half [fs_chalf]   *)
(*      that [log_state] parks.                                          *)
(*                                                                       *)
(*  The machinery halves and the log side's dirty halves are per-block    *)
(*  over the WHOLE map and are handed out undivided -- they know nothing  *)
(*  about the split.                                                     *)
(* ===================================================================== *)

Section FsMint.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ}.

  (* THE ROW EVERY BREAD CLIENT ABOVE THE LOG CARRIES.  The home set is
     bound because no consumer needs to name it: holding the block's byte
     run IS being a home block ([fsblock_home]), and the byte map's AUTH --
     of which there is exactly one -- is inside the invariant, so two
     invariants at [logN] over one [fs_bytes γ] cannot disagree about it.
     What a consumer needs is only that SOME such invariant exists, which
     is what this says.  Three carriers hand it out and every client of the
     block layer holds one of them: [LogInv.log_ctx], [BitmapInv.bitmap_inv]
     and [InodeRegion.ireg_inv]. *)
  (* THE ROW AT A NAMED HOME SET.  [Xv] is bound: it is the invariant's own
     bookkeeping for the recovery window and no consumer above the WAL
     names it. *)
  Definition fs_bytes_at (γ : fs_names) (home : gset Z) : iProp Σ :=
    (∃ Xv : Z -> list (bv 8),
       fs_bytes_inv (fs_bytes γ) (fs_cache γ) (fs_exc γ) home Xv)%I.

  Global Instance fs_bytes_at_persistent γ home :
    Persistent (fs_bytes_at γ home).
  Proof. apply _. Qed.

  (* THE ROW ITSELF, minted at PowerOn: it says only that SOME byte-view
     invariant over [γ] exists.  The three carriers hand this out. *)
  Definition fs_bytes_row (γ : fs_names) : iProp Σ :=
    (∃ home : gset Z, fs_bytes_at γ home)%I.

  Global Instance fs_bytes_row_persistent γ : Persistent (fs_bytes_row γ).
  Proof. apply _. Qed.

  (* ...AND THE ROW A RUNTIME READER NEEDS (lane E-except): the row plus
     the SEAL.  It is what [LogInv.log_ctx] carries, so every client of
     the log layer gets it for free and not one crossing site above the
     WAL changed.  [BitmapInv.bitmap_inv] and [InodeRegion.ireg_inv] are
     minted at PowerOn, BEFORE recovery has run, so they carry only
     [fs_bytes_row]; their own crossings take [exc_sealed] explicitly and
     their callers read it off [log_ctx]. *)
  Definition fs_bytes_any (γ : fs_names) : iProp Σ :=
    (fs_bytes_row γ ∗ exc_sealed (fs_exc γ))%I.

  Global Instance fs_bytes_any_persistent γ : Persistent (fs_bytes_any γ).
  Proof. apply _. Qed.

  Lemma fs_bytes_any_row γ : fs_bytes_any γ -∗ fs_bytes_row γ.
  Proof. iIntros "[$ _]". Qed.

  Lemma fs_bytes_any_seal γ : fs_bytes_any γ -∗ exc_sealed (fs_exc γ).
  Proof. iIntros "[_ $]". Qed.

  Lemma fs_bytes_any_of γ :
    fs_bytes_row γ -∗ exc_sealed (fs_exc γ) -∗ fs_bytes_any γ.
  Proof. iIntros "H1 H2". iFrame. Qed.

  (* ...and the same pair at a NAMED home set, which is what
     [BitmapInv.bitmap_inv] carries (it already names [cov]/[logstart]). *)
  Definition fs_bytes_any_at (γ : fs_names) (home : gset Z) : iProp Σ :=
    (fs_bytes_at γ home ∗ exc_sealed (fs_exc γ))%I.

  Global Instance fs_bytes_any_at_persistent γ home :
    Persistent (fs_bytes_any_at γ home).
  Proof. apply _. Qed.

  Lemma fs_bytes_any_at_any γ home :
    fs_bytes_any_at γ home -∗ fs_bytes_any γ.
  Proof.
    iIntros "[Hat $]". rewrite /fs_bytes_row. iExists home. iExact "Hat".
  Qed.

  (* the bread client's crossing, at that row: what used to be an auth-free
     half/half entailment is this fupd (durable-disk 1c-flip step 3) *)
  Lemma fs_bytes_agree_any (E : coPset) (γ : fs_names) (b : Z)
      (bs bsm : list (bv 8)) :
    ↑logN ⊆ E ->
    fs_bytes_any γ -∗
    fsblock (fs_bytes γ) b bs -∗
    (b ↪[fs_cache γ]{#(1/2)} bsm) ={E}=∗
      ⌜bsm = bs⌝ ∗ fsblock (fs_bytes γ) b bs ∗
      (b ↪[fs_cache γ]{#(1/2)} bsm).
  Proof.
    iIntros (HE) "[Hrow #Hseal] Hfb Hm".
    iDestruct "Hrow" as (home Xv) "#Hinv".
    iApply (fs_bytes_agree E (fs_bytes γ) (fs_cache γ) (fs_exc γ) home Xv
              b bs bsm HE with "Hinv Hseal Hfb Hm").
  Qed.

  (* THE SAME CROSSING AT A SHARE (lane B''-blk).  This is [readi]'s tie
     between the buffer bread handed it and the bytes its own [inode_blocks]
     names, and it is an AGREEMENT, so a read-locker holding a QUARTER of
     the run runs it exactly as a full owner does (plan section 4). *)
  Lemma fs_bytes_agree_any_q (E : coPset) (γ : fs_names) (dq : dfrac) (b : Z)
      (bs bsm : list (bv 8)) :
    ↑logN ⊆ E ->
    fs_bytes_any γ -∗
    fsblock_q (fs_bytes γ) dq b bs -∗
    (b ↪[fs_cache γ]{#(1/2)} bsm) ={E}=∗
      ⌜bsm = bs⌝ ∗ fsblock_q (fs_bytes γ) dq b bs ∗
      (b ↪[fs_cache γ]{#(1/2)} bsm).
  Proof.
    iIntros (HE) "[Hrow #Hseal] Hfb Hm".
    iDestruct "Hrow" as (home Xv) "#Hinv".
    iApply (fs_bytes_agree_q E (fs_bytes γ) dq (fs_cache γ) (fs_exc γ) home Xv
              b bs bsm HE with "Hinv Hseal Hfb Hm").
  Qed.

  (* the two halves of a map along a decidable predicate on the key *)
  Lemma fs_split_filter {V : Type} (m : gmap Z V) (S : gset Z)
      (Phi : Z -> V -> iProp Σ) :
    ([∗ map] k ↦ v ∈ m, Phi k v)
      ⊢ ([∗ map] k ↦ v ∈ filter (fun kv => kv.1 ∈ S) m, Phi k v)
        ∗ ([∗ map] k ↦ v ∈ filter (fun kv => kv.1 ∉ S) m, Phi k v).
  Proof.
    rewrite -big_sepM_union; [| apply map_disjoint_filter_complement].
    rewrite map_filter_union_complement //.
  Qed.

  Lemma fs_filter_dom {V : Type} (m : gmap Z V) (S : gset Z) :
    S ⊆ dom m -> dom (filter (fun kv => kv.1 ∈ S) m) = S.
  Proof.
    intros Hsub. apply set_eq. intros b. rewrite elem_of_dom. split.
    - intros [v Hv]. apply map_lookup_filter_Some in Hv as [_ Hin]. exact Hin.
    - intros Hin. destruct (proj1 (elem_of_dom m b) (Hsub b Hin)) as [v Hv].
      exists v. apply map_lookup_filter_Some. split; [exact Hv | exact Hin].
  Qed.

  (* THE GHOST STEP the era runs once.  [L0] is the mkfs image's covered
     content map, [home] the covered range minus the log's own storage.
     All FOUR client-side pieces come out explicitly: an affine [iFrame]
     dropping one of them compiles and strands initlog. *)
  (* THE ERA'S BYTE VIEW IS MINTED AT [Dv], NOT AT THE CACHE (lane
     E-except).  [Dv] is the COMMITTED view [FsCrash.fr_D]: the raw home
     blocks with the on-disk log's batch installed.  [X] is the set where
     the two differ -- the pending home blocks -- and it comes out as the
     WAL's handle [exc_own].  At a clean header [X = ∅] and [Dv] IS the
     raw content, which is the pre-E-except statement. *)
  Lemma fs_alloc (E : coPset) (γlk γtp : gname)
      (L0 : gmap Z (list (bv 8))) (home : gset Z)
      (Dv : Z -> list (bv 8)) (X : gset Z) :
    (forall b bs, L0 !! b = Some bs -> length bs = BSIZE) ->
    home ⊆ dom L0 ->
    (forall b, b ∈ home -> length (Dv b) = BSIZE) ->
    X ⊆ home ->
    (forall b bs, L0 !! b = Some bs -> b ∈ home -> b ∉ X -> Dv b = bs) ->
    ⊢ |={E}=> ∃ γ : fs_names,
      (* the two ghosts the caller allocated, named back to it *)
      ⌜fs_link γ = γlk⌝ ∗ ⌜fs_top γ = γtp⌝ ∗
      ghost_map_auth (fs_cache γ) 1 L0 ∗
      ghost_map_auth (fs_dirty γ) 1 ((fun _ => false) <$> L0) ∗
      fs_bytes_inv (fs_bytes γ) (fs_cache γ) (fs_exc γ) home Dv ∗
      exc_own (fs_exc γ) X ∗
      ([∗ map] bno ↦ bs ∈ L0,
         fs_mclean γ bno bs ∗ (bno ↪[fs_dirty γ]{#(1/2)} false)) ∗
      ([∗ map] bno ↦ bs ∈ filter (fun kv => kv.1 ∈ home) L0,
         fsblock (fs_bytes γ) bno (Dv bno)) ∗
      ([∗ map] bno ↦ bs ∈ filter (fun kv => kv.1 ∉ home) L0,
         fs_chalf γ bno bs).
  Proof.
    iIntros (Hlen Hsub HlD HXsub Hagr).
    iMod (ghost_map_alloc L0) as (γC) "[HaC HC]".
    iMod (ghost_map_alloc ((fun _ => false) <$> L0)) as (γD) "[HaD HD]".
    rewrite !big_sepM_fmap.
    (* peel each block's cache element into its two halves *)
    iAssert ([∗ map] bno ↦ bs ∈ L0,
               (bno ↪[γC]{#(1/2)} bs) ∗ (bno ↪[γC]{#(1/2)} bs))%I
      with "[HC]" as "HC".
    { iApply (big_sepM_mono with "HC"). intros bno bs _.
      iIntros "H". iDestruct "H" as "[$ $]". }
    rewrite big_sepM_sep. iDestruct "HC" as "[HCm HCp]".
    (* the parked halves split along [home]: the home ones are swallowed
       by the byte invariant, the log region's stay parked as [fs_chalf] *)
    iDestruct (fs_split_filter L0 home (fun bno bs => bno ↪[γC]{#(1/2)} bs)%I
                 with "HCp") as "[HCh HCl]".
    iMod (fs_bytes_alloc E γC (filter (fun kv => kv.1 ∈ home) L0) Dv X
            with "HCh") as (γL γX) "(#Hinv & Hxo & Hfb)".
    { intros b bs Hb. apply map_lookup_filter_Some in Hb as [Hb _].
      exact (Hlen b bs Hb). }
    { intros b Hb. apply HlD. rewrite (fs_filter_dom L0 home Hsub) in Hb.
      exact Hb. }
    { rewrite (fs_filter_dom L0 home Hsub). exact HXsub. }
    { intros b bs Hb Hnin. apply map_lookup_filter_Some in Hb as [Hb Hin].
      exact (Hagr b bs Hb Hin Hnin). }
    rewrite (fs_filter_dom L0 home Hsub).
    iModIntro. iExists (MkFsNames γC γD γL γlk γtp γX).
    iSplitR; [done |]. iSplitR; [done |].
    rewrite /fs_chalf /fs_mclean /=.
    iFrame "HaC HaD Hinv Hxo Hfb HCl".
    iAssert ([∗ map] bno ↦ bs ∈ L0,
               (bno ↪[γD]{#(1/2)} false) ∗ (bno ↪[γD]{#(1/2)} false))%I
      with "[HD]" as "HD".
    { iApply (big_sepM_mono with "HD"). intros bno bs _.
      iIntros "H". iDestruct "H" as "[$ $]". }
    rewrite big_sepM_sep. iDestruct "HD" as "[HD1 HD2]".
    iCombine "HCm HD1" as "H". rewrite -big_sepM_sep.
    iCombine "H HD2" as "H". rewrite -big_sepM_sep.
    iApply (big_sepM_mono with "H").
    intros bno bs _. iIntros "[[HC HD1] HD2]". iFrame.
  Qed.

End FsMint.
