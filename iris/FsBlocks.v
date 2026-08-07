(* FsBlocks.v -- the log layer's LOGGED-VIEW ghost over the FS block range,
   and its instantiation of the bio layer's client view (bio_view).

   Design: claude-notes/design/fs-log.md.  Two ghost maps over block
   numbers, each entry split half/half:

   - γL (the logged view L): D overlaid with every log_write of the current
     open batch.  [fsblock] is the CLIENT half -- the FS layer's points-to
     for logical block content; the machinery half rides inside the bio
     layer as the payload below.  Two halves agree with no auth in sight
     (that is bread's postcondition); UPDATING needs the auth, which lives
     in the log lock's resource (LogInv.v, stage 2) -- so log_write (under
     log.lock) and the committer (who checks the auth out) are the only
     writers of L.  That freeze-by-auth is what carries "log slot i holds
     L(W[i])" from write_log through install_trans.

   - γdirty: is the block in the current pinned write set
     (logged-uncommitted-or-uninstalled)?  Half in the payload, half (plus
     the auth) in the log lock's resource, recording exactly the membership
     of lh.block[].  Flipped false->true by log_write, true->false by
     install_trans at its bunpin.

   The bio payloads: clean = L-half + dirty-half-at-false; dirty = L-half +
   dirty-half-at-true.  Bio moves them opaquely; only holders of the log
   auth convert.

   - γown (the EXCLUSIVE per-block ownership token, [blk_own]): a third
     ghost map, unit-valued, whose elements are FULL-fraction and therefore
     incompatible with themselves.  It exists because [fsblock] cannot do
     that job: it is a HALF, so two owners each holding a half of one key
     is perfectly consistent, and the layer above (the inode block map)
     needs "two file indices never name one disk block" -- [blk_own_ne].
     The AUTHORITY over this map belongs to the bitmap/free-block
     invariant, which is not designed yet; until it is, nothing holds the
     auth and nothing needs it.  Only the elements' exclusivity is
     load-bearing, and that holds with no auth in sight. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvPtsto.
Require Import DiskPtsto.
Require Import BioInv.
Local Open Scope Z_scope.

Class fsLogG (Σ : gFunctors) := FsLogG {
  fsL_inG :: ghost_mapG Σ Z (list (bv 8));
  fsdirty_inG :: ghost_mapG Σ Z bool;
  fsown_inG :: ghost_mapG Σ Z unit;
}.
Definition fsLogΣ : gFunctors :=
  #[ghost_mapΣ Z (list (bv 8)); ghost_mapΣ Z bool; ghost_mapΣ Z unit].
Global Instance subG_fsLogΣ {Σ} : subG fsLogΣ Σ -> fsLogG Σ.
Proof. solve_inG. Qed.

Record fs_names := MkFsNames {
  fs_L     : gname;   (* the logged view *)
  fs_dirty : gname;   (* the pinned-set flag *)
  fs_own   : gname;   (* the exclusive per-block ownership token *)
}.

Section FsBlocks.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ}.

  (* the FS layer's points-to for a block's logical content (the client
     half of the logged view) *)
  Definition fsblock (γ : fs_names) (bno : Z) (bs : list (bv 8)) : iProp Σ :=
    bno ↪[fs_L γ]{#(1/2)} bs.

  (* EXCLUSIVE ownership of a block.  Unlike [fsblock] (a half, so two
     holders of one key are consistent) this token is a FULL-fraction
     ghost_map element: nobody else can hold one at the same block.  The
     inode layer's block-map injectivity is [blk_own_ne] below. *)
  Definition blk_own (γ : fs_names) (bno : Z) : iProp Σ :=
    bno ↪[fs_own γ] tt.

  Global Instance blk_own_timeless γ b : Timeless (blk_own γ b).
  Proof. rewrite /blk_own. apply _. Qed.

  (* two full-fraction elements at ONE key are incompatible: their dfracs
     compose to [DfracOwn 1 ⋅ DfracOwn 1], which is not valid. *)
  Lemma blk_own_excl γ b :
    blk_own γ b -∗ blk_own γ b -∗ False.
  Proof.
    rewrite /blk_own. iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hv).
  Qed.

  (* THE lemma the inode layer needs: two owned blocks are distinct. *)
  Lemma blk_own_ne γ b1 b2 :
    blk_own γ b1 -∗ blk_own γ b2 -∗ ⌜b1 <> b2⌝.
  Proof.
    iIntros "H1 H2". destruct (decide (b1 = b2)) as [->|Hne]; [| done].
    iExFalso. iApply (blk_own_excl with "H1 H2").
  Qed.

  (* the machinery halves: the bio payloads *)
  Definition fs_mclean (γ : fs_names) (bno : Z) (bs : list (bv 8)) : iProp Σ :=
    (bno ↪[fs_L γ]{#(1/2)} bs ∗ bno ↪[fs_dirty γ]{#(1/2)} false)%I.

  Definition fs_mdirty (γ : fs_names) (bno : Z) (bs : list (bv 8)) : iProp Σ :=
    (bno ↪[fs_L γ]{#(1/2)} bs ∗ bno ↪[fs_dirty γ]{#(1/2)} true)%I.

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

  (* what a caller of bread learns on contact: its own fsblock half against
     the handle's machinery half pins the returned bytes.  Stated for both
     payload polarities. *)
  Lemma fsblock_mclean_agree γ bno bs bs' :
    fsblock γ bno bs -∗ fs_mclean γ bno bs' -∗ ⌜bs' = bs⌝.
  Proof.
    iIntros "Hc [Hm _]".
    iDestruct (ghost_map_elem_agree with "Hm Hc") as %Heq. done.
  Qed.

  Lemma fsblock_mdirty_agree γ bno bs bs' :
    fsblock γ bno bs -∗ fs_mdirty γ bno bs' -∗ ⌜bs' = bs⌝.
  Proof.
    iIntros "Hc [Hm _]".
    iDestruct (ghost_map_elem_agree with "Hm Hc") as %Heq. done.
  Qed.

  (* the logged-view update (log_write's ghost step): auth + both halves.
     The auth is the log lock's (stage 2); nothing else can move L. *)
  Lemma fsblock_update γ (L : gmap Z (list (bv 8))) bno bs bs_new bs' :
    ghost_map_auth (fs_L γ) 1 L -∗
    fsblock γ bno bs -∗
    (bno ↪[fs_L γ]{#(1/2)} bs') ==∗
    ⌜bs' = bs /\ L !! bno = Some bs⌝ ∗
    ghost_map_auth (fs_L γ) 1 (<[bno := bs_new]> L) ∗
    fsblock γ bno bs_new ∗
    (bno ↪[fs_L γ]{#(1/2)} bs_new).
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

  (* allocation, from an initial content map (the mkfs image's covered
     range): the two auths, and PER BLOCK all four client-side pieces --
     the fsblock client half, the machinery-clean payload (which pairs
     with the boot-side [disk_block]s to form [bio_init]'s pool bundles),
     the LOG-SIDE dirty half (which stocks [log_batch]'s all-false
     big-op), and the exclusive [blk_own] token (which the allocator layer
     above will hand out and take back).  All four, explicitly: an affine
     iFrame dropping one of them compiles and strands initlog -- or, for
     [blk_own], strands the block permanently, since no auth exists to
     re-mint it.
     The ownership map's AUTH is deliberately dropped here: its authority
     belongs to the bitmap/free-block invariant, which does not exist yet,
     and the elements' exclusivity needs no auth. *)
  Lemma fs_alloc (L0 : gmap Z (list (bv 8))) :
    ⊢ |==> ∃ γ : fs_names,
      ghost_map_auth (fs_L γ) 1 L0 ∗
      ghost_map_auth (fs_dirty γ) 1 ((fun _ => false) <$> L0) ∗
      [∗ map] bno ↦ bs ∈ L0,
        fsblock γ bno bs ∗ fs_mclean γ bno bs ∗
        (bno ↪[fs_dirty γ]{#(1/2)} false) ∗ blk_own γ bno.
  Proof.
    iMod (ghost_map_alloc L0) as (γL) "[HaL HL]".
    iMod (ghost_map_alloc ((fun _ => false) <$> L0)) as (γD) "[HaD HD]".
    iMod (ghost_map_alloc ((fun _ => tt) <$> L0)) as (γO) "[_ HO]".
    iModIntro. iExists (MkFsNames γL γD γO). iFrame "HaL HaD".
    rewrite !big_sepM_fmap.
    iCombine "HL HD" as "H". rewrite -big_sepM_sep.
    iCombine "H HO" as "H". rewrite -big_sepM_sep.
    iApply (big_sepM_mono with "H").
    intros bno bs Hbs. iIntros "[[HL HD] HO]".
    iDestruct "HL" as "[HL1 HL2]".
    iDestruct "HD" as "[HD1 HD2]".
    rewrite /fsblock /fs_mclean /blk_own. iFrame.
  Qed.

End FsBlocks.
