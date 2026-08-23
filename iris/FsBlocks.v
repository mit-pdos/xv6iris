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
From iris.algebra Require Import auth gmap frac.
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

(* the mask side condition every reader at the top mask discharges.  Proved
   ONCE, here, in an empty context: [set_solver] inside a syscall-altitude
   proof walks the whole context (durable-notes), and every call site of
   [fs_bytes_agree] below is at [⊤] or at [⊤] minus one namespace. *)
Lemma logN_top : (↑logN : coPset) ⊆ ⊤.
Proof. set_solver. Qed.

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

  Global Instance byte_range_timeless gL b off bs :
    Timeless (byte_range gL b off bs).
  Proof. apply _. Qed.
  Global Instance fsblock_timeless gL b bs : Timeless (fsblock gL b bs).
  Proof. apply _. Qed.

  Lemma fsblock_length gL b bs : fsblock gL b bs -∗ ⌜length bs = BSIZE⌝.
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

  (* what the auth says about an owned run *)
  Lemma byte_range_lookup gL (L : gmap Z (bv 8)) b off bs :
    ghost_map_auth gL 1 L -∗ byte_range gL b off bs -∗
    ⌜(map_seqZ (b * BSZ + off) bs : gmap Z (bv 8)) ⊆ L⌝.
  Proof.
    iIntros "Ha Hr". rewrite byte_range_map.
    iApply (ghost_map_lookup_big with "Ha Hr").
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

  (* WHAT A CLIENT OF THE BYTE VIEW LEARNS WHEN THE AUTH IS LENT TO IT
     (durable-disk 1d', item 4).  The commit's payload law takes the byte
     AUTHORITY as an input so that the client can agree the ELEMENTS it owns
     against it and read off the real logged view; this is the tie that
     makes that reading total on the home set -- [Lb] resides exactly the
     home blocks' byte range, and every home block's cache entry is a
     whole block whose bytes are [Lb]'s.  Together the two pin [Lb] to the
     byte flattening of [L] on [home], which is what the client needs to
     identify [LogDefs.lm_logged L] with what its own elements say. *)
  Definition bytes_home_at (Lb : gmap Z (bv 8)) (L : gmap Z (list (bv 8)))
      (home : gset Z) : Prop :=
    bytes_dom Lb home /\
    forall b : Z, b ∈ home -> exists bs : list (bv 8),
      L !! b = Some bs /\ length bs = BSIZE /\
      (map_seqZ (b * BSZ) bs : gmap Z (bv 8)) ⊆ Lb.

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
  Definition fs_bytes_body (gL gc : gname) (home : gset Z) : iProp Σ :=
    (∃ (L : gmap Z (bv 8)) (C : gmap Z (list (bv 8))),
       ghost_map_auth gL 1 L ∗
       ([∗ map] b ↦ bs ∈ C, b ↪[gc]{#(1/2)} bs) ∗
       ⌜dom C = home⌝ ∗
       ⌜forall b bs, C !! b = Some bs -> length bs = BSIZE⌝ ∗
       ⌜bytes_tie L C⌝ ∗ ⌜bytes_dom L home⌝)%I.

  Global Instance fs_bytes_body_timeless gL gc home :
    Timeless (fs_bytes_body gL gc home).
  Proof. apply _. Qed.

  Definition fs_bytes_inv (gL gc : gname) (home : gset Z) : iProp Σ :=
    inv logN (fs_bytes_body gL gc home).

  Global Instance fs_bytes_inv_persistent gL gc home :
    Persistent (fs_bytes_inv gL gc home).
  Proof. apply _. Qed.

  (* ...AND HOW THE HOLDER OF THE CACHE AUTH READS IT OFF THE INVARIANT'S
     BODY.  The parked halves are the invariant's; the auth is the log
     lock's; agreement between them is what turns the body's own [bytes_tie]
     (stated over the PARKED map [C]) into the tie the client wants, stated
     over the map the log actually holds.  Pure conclusion, so nothing is
     consumed. *)
  Lemma fs_bytes_home_of (gc : gname) (L C : gmap Z (list (bv 8)))
      (Lb : gmap Z (bv 8)) (home : gset Z) :
    dom C = home ->
    (forall b bs, C !! b = Some bs -> length bs = BSIZE) ->
    bytes_tie Lb C -> bytes_dom Lb home ->
    ghost_map_auth gc 1 L -∗
    ([∗ map] b ↦ bs ∈ C, b ↪[gc]{#(1/2)} bs) -∗
    ⌜bytes_home_at Lb L home⌝.
  Proof.
    iIntros (Hdom Hlens Htie Hdm) "Hca HC".
    iAssert (⌜forall (b : Z) (bs : list (bv 8)), C !! b = Some bs ->
               L !! b = Some bs⌝)%I as %Hagr.
    { iIntros (b bs Hb).
      iDestruct (big_sepM_lookup _ _ b bs Hb with "HC") as "Hi".
      iApply (ghost_map_lookup with "Hca Hi"). }
    iPureIntro. split; [exact Hdm|].
    intros b Hb.
    assert (Hin : is_Some (C !! b)) by (apply elem_of_dom; rewrite Hdom; exact Hb).
    destruct Hin as [bs Hbs].
    exists bs. split_and!.
    - exact (Hagr b bs Hbs).
    - exact (Hlens b bs Hbs).
    - exact (Htie b bs Hbs).
  Qed.

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
  Lemma fsblock_home_open (E : coPset) gL gc home b bs :
    ↑logN ⊆ E ->
    fs_bytes_inv gL gc home -∗
    fsblock gL b bs ={E}=∗ ⌜b ∈ home⌝ ∗ fsblock gL b bs.
  Proof.
    iIntros (HE) "#Hinv Hfb".
    iMod (inv_acc E logN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (L C) ">(Ha & HC & %Hdom & %Hlens & %Htie & %Hdm)".
    iDestruct (fsblock_home gL L home b bs Hdm with "Ha Hfb") as %Hb.
    iMod ("Hclose" with "[Ha HC]") as "_".
    { iNext. iExists L, C. by iFrame. }
    iModIntro. by iFrame.
  Qed.

  Lemma fs_bytes_agree (E : coPset) gL gc home b bs bsm :
    ↑logN ⊆ E ->
    fs_bytes_inv gL gc home -∗
    fsblock gL b bs -∗
    (b ↪[gc]{#(1/2)} bsm) ={E}=∗
      ⌜bsm = bs⌝ ∗ fsblock gL b bs ∗ (b ↪[gc]{#(1/2)} bsm).
  Proof.
    iIntros (HE) "#Hinv Hfb Hm".
    iMod (inv_acc E logN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (L C) ">(Ha & HC & %Hdom & %Hlens & %Htie & %Hdm)".
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
      - exact (Htie b bsi Hbsi). }
    iMod ("Hclose" with "[Ha Hback Hi]") as "_".
    { iNext. iExists L, C. iFrame "Ha". iSplitL; [by iApply "Hback" |].
      iPureIntro. auto. }
    iModIntro. iFrame "Hm". rewrite /fsblock. iFrame "Hr".
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

  Lemma byte_range_log_update (E : coPset) gL gc home (C : gmap Z (list (bv 8)))
      (b : Z) (off : nat) (sub_old sub_new bs_old : list (bv 8)) :
    ↑logN ⊆ E ->
    (off + length sub_old <= BSIZE)%nat ->
    (0 < length sub_old)%nat ->
    (length bs_old = BSIZE -> length sub_new = length sub_old) ->
    fs_bytes_inv gL gc home -∗
    ghost_map_auth gc 1 C -∗
    byte_range gL b (Z.of_nat off) sub_old -∗
    (b ↪[gc]{#(1/2)} bs_old) ={E}=∗
      ⌜C !! b = Some bs_old /\ length bs_old = BSIZE /\
        sub_old = take (length sub_old) (drop off bs_old)⌝ ∗
      ghost_map_auth gc 1 (<[b := blk_splice off sub_new bs_old]> C) ∗
      byte_range gL b (Z.of_nat off) sub_new ∗
      (b ↪[gc]{#(1/2)} blk_splice off sub_new bs_old).
  Proof.
    iIntros (HE Hoff Hpos Hshape) "#Hinv Hca Hr Hm".
    iMod (inv_acc E logN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (L C0) ">(Ha & HC & %Hdom & %Hlens & %Htie & %Hdm)".
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
    iMod ("Hclose" with "[Ha Hback Hi]") as "_".
    { iNext.
      iExists ((map_seqZ (b * BSZ + Z.of_nat off) sub_new : gmap Z (bv 8)) ∪ L),
              (<[b := blk_splice off sub_new bs_old]> C0).
      iFrame "Ha".
      iSplitL.
      { iApply ("Hback" with "Hi"). }
      iPureIntro. split; [| split; [| split]].
      - rewrite dom_insert_L Hdom.
        assert (Hbh : b ∈ home) by exact Hb. set_solver.
      - intros b' bs' Hb'.
        destruct (decide (b' = b)) as [->|Hne].
        + rewrite lookup_insert in Hb'. congruence.
        + rewrite lookup_insert_ne in Hb'; [| done]. exact (Hlens b' bs' Hb').
      - intros b' bs' Hb'.
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
        + intros Hs. apply lookup_union_is_Some. by right. }
    iModIntro. iFrame "Hca Hm Hr". iPureIntro. auto.
  Qed.

  (* THE WHOLE-BLOCK COROLLARY, at its old statement so that nothing which
     uses it moves: the writer that happens to own the entire run presents
     it at [off = 0], and the splice of a full-width run IS that run. *)
  Lemma fsblock_update (E : coPset) gL gc home (C : gmap Z (list (bv 8)))
      (b : Z) (bs bs_new bsm : list (bv 8)) :
    ↑logN ⊆ E -> length bs_new = BSIZE ->
    fs_bytes_inv gL gc home -∗
    ghost_map_auth gc 1 C -∗
    fsblock gL b bs -∗
    (b ↪[gc]{#(1/2)} bsm) ={E}=∗
      ⌜bsm = bs /\ C !! b = Some bs⌝ ∗
      ghost_map_auth gc 1 (<[b := bs_new]> C) ∗
      fsblock gL b bs_new ∗
      (b ↪[gc]{#(1/2)} bs_new).
  Proof.
    iIntros (HE Hlnew) "#Hinv Hca Hfb Hm".
    iDestruct "Hfb" as "[%Hlb Hr]".
    iMod (byte_range_log_update E gL gc home C b 0%nat bs bs_new bsm HE
            ltac:(rewrite Hlb; lia) ltac:(rewrite Hlb; exact BSIZE_pos)
            ltac:(intros Hbm; rewrite Hlnew Hlb //)
            with "Hinv Hca Hr Hm")
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

  Lemma fs_bytes_alloc (E : coPset) (gc : gname) (C : gmap Z (list (bv 8))) :
    (forall b bs, C !! b = Some bs -> length bs = BSIZE) ->
    ([∗ map] b ↦ bs ∈ C, b ↪[gc]{#(1/2)} bs) ={E}=∗
      ∃ gL : gname,
        fs_bytes_inv gL gc (dom C) ∗
        ([∗ map] b ↦ bs ∈ C, fsblock gL b bs).
  Proof.
    iIntros (Hlen) "HC".
    iMod (ghost_map_alloc_empty (K := Z) (V := bv 8)) as (gL) "Ha".
    iMod (byte_map_grow gL C ∅ ∅ Hlen with "Ha") as (L) "(%Hdm & %Htie & Ha & Hfb)".
    { intros b' _. set_solver. }
    { intros a. split.
      - intros [v Hv]. rewrite lookup_empty in Hv. done.
      - intros (b' & Hb' & _). set_solver. }
    rewrite left_id_L in Hdm.
    iMod (inv_alloc logN E (fs_bytes_body gL gc (dom C)) with "[Ha HC]") as "#Hinv".
    { iNext. iExists L, C. iFrame "Ha HC". iPureIntro. auto. }
    iModIntro. iExists gL. iFrame "Hinv Hfb".
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
Global Typeclasses Opaque byte_range fsblock.

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
  Definition fs_bytes_any (γ : fs_names) : iProp Σ :=
    (∃ home : gset Z, fs_bytes_inv (fs_bytes γ) (fs_cache γ) home)%I.

  Global Instance fs_bytes_any_persistent γ : Persistent (fs_bytes_any γ).
  Proof. apply _. Qed.

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
    iIntros (HE) "Hrow Hfb Hm". iDestruct "Hrow" as (home) "#Hinv".
    iApply (fs_bytes_agree E (fs_bytes γ) (fs_cache γ) home b bs bsm HE
              with "Hinv Hfb Hm").
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
  Lemma fs_alloc (E : coPset) (γlk γtp : gname)
      (L0 : gmap Z (list (bv 8))) (home : gset Z) :
    (forall b bs, L0 !! b = Some bs -> length bs = BSIZE) ->
    home ⊆ dom L0 ->
    ⊢ |={E}=> ∃ γ : fs_names,
      (* the two ghosts the caller allocated, named back to it *)
      ⌜fs_link γ = γlk⌝ ∗ ⌜fs_top γ = γtp⌝ ∗
      ghost_map_auth (fs_cache γ) 1 L0 ∗
      ghost_map_auth (fs_dirty γ) 1 ((fun _ => false) <$> L0) ∗
      fs_bytes_inv (fs_bytes γ) (fs_cache γ) home ∗
      ([∗ map] bno ↦ bs ∈ L0,
         fs_mclean γ bno bs ∗ (bno ↪[fs_dirty γ]{#(1/2)} false)) ∗
      ([∗ map] bno ↦ bs ∈ filter (fun kv => kv.1 ∈ home) L0,
         fsblock (fs_bytes γ) bno bs) ∗
      ([∗ map] bno ↦ bs ∈ filter (fun kv => kv.1 ∉ home) L0,
         fs_chalf γ bno bs).
  Proof.
    iIntros (Hlen Hsub).
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
    iMod (fs_bytes_alloc E γC (filter (fun kv => kv.1 ∈ home) L0)
            with "HCh") as (γL) "[#Hinv Hfb]".
    { intros b bs Hb. apply map_lookup_filter_Some in Hb as [Hb _].
      exact (Hlen b bs Hb). }
    rewrite (fs_filter_dom L0 home Hsub).
    iModIntro. iExists (MkFsNames γC γD γL γlk γtp).
    iSplitR; [done |]. iSplitR; [done |].
    rewrite /fs_chalf /fs_mclean /=.
    iFrame "HaC HaD Hinv Hfb HCl".
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
