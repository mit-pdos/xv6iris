(* ====================================================================== *)
(* DiskPtsto.v -- the disk points-to.                                      *)
(*                                                                         *)
(* The virtio disk's image is a total function [v_disk : Z -> bv 8].  The  *)
(* driver-facing resource for it is a byte-granularity ghost map: the      *)
(* AUTH rides in [RiscvPtsto.era_interp]'s image conjunct, at the ERA's    *)
(* image gname (claude-notes/design/fs-log.md, stage 4),                   *)
(* tied to the image by [VirtioModel.disk_view] -- the exact analogue of   *)
(* [mem_view]: a fragment exists only for offsets somebody minted, and the *)
(* model's disk stays                                                      *)
(* total underneath.  [disk_bytes]/[disk_block] are the derived forms the  *)
(* function specs use ([virtio_disk_rw] moves a whole 1024-byte block).   *)
(*                                                                         *)
(* This file also owns the OTHER driver-protocol ghosts, so a single       *)
(* [disk_names] record travels through [dev_inv] (mirroring [uart_names]): *)
(*   dn_img  -- the disk image map above.  ALWAYS [disk_img_name] (the     *)
(*              AMBIENT ERA's image gname): the map is minted by the power *)
(*              thread at boot, before this record exists, so [dn_img] is  *)
(*              CONSTRUCTED at it rather than allocated.  It stays a FIELD *)
(*              so every client statement ([disk_bytes γ …]) keeps its     *)
(*              spelling;                                                  *)
(*   dn_slot -- ghost_map nat vslot: the auth covers every in-flight       *)
(*              request; the FRAGMENT for position [p] is the publisher's  *)
(*              RECEIPT, and presenting it is what licenses the reclaim;   *)
(*   dn_nc   -- mono_nat over the completed count: an interrupt handler's  *)
(*              used-index read mints a persistent lower bound that        *)
(*              survives to its later per-slot reads;                      *)
(*   dn_np   -- ghost_var nat over the published count: the OTHER half     *)
(*              lives in the vdisk_lock's resource, so only a lock holder  *)
(*              can publish, and a lock holder KNOWS the published index.  *)
(*                                                                         *)
(* Design rationale: claude-notes/design/virtio-driver.md.                 *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_map ghost_var mono_nat.
From iris.algebra.lib Require Import dfrac_agree.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import VirtioModel.
Require Import VirtioQueue.
Require Import DiskImg.
Require Import RiscvPtsto.  (* [riscvFixedGS]: the sole owner of [mono_natG], and it carries [diskImgG] *)

Local Open Scope Z_scope.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)


Record disk_names := DiskNames {
  dn_img   : gname;
  dn_slot  : gname;
  dn_nc    : gname;
  dn_np    : gname;
  dn_claim : gname;
  dn_cfg   : gname;
  (* THE COMPLETION ORDER (tools/vtest/README.md finding 5).  A ghost_map
     from a request's POSITION in the available ring to the USED INDEX its
     completion was reported at.  The two are different numbers now that the
     device answers requests in whatever order it finishes them, and the
     interrupt handler -- which walks used indices -- needs the inverse
     direction to name the position it is looking at.  Its elements are
     minted PERSISTENT at the completion: they are pure identification, never
     ownership, and two of them at one position agree. *)
  dn_ord   : gname;
  (* THE HANDLER'S READ WATERMARK ([disk.used_idx] in virtio_disk_intr).  A
     [ghost_var nat]: the invariant holds one half at [vp_nr], the disk lock's
     resource the other.  It is the credential that says the record being
     reclaimed is the one at the watermark -- which is what keeps the unread
     used records a contiguous run, and hence what says a completion can
     never overwrite one the driver still owes a look (finding 5). *)
  dn_nr    : gname;
  (* THE STAGED HEAD, between the ring store and the index bump.  A
     [ghost_var (option (bv 16))]: the invariant holds one half and couples
     it to the cell at the publish position, the publisher the other.  See
     [Xv6Cameras.disk_stage_inG] for why the gap exists at all. *)
  dn_stage : gname;
  (* the CRASH-PERMIT channel's ghost-map name (PermInv.v): the auth lives in
     [PermInv.perm_inv (dn_perm γ)], allocated per era beside [disk_inv], and
     its ELEMENTS ([PermInv.perm_tok]) ride the timeless request slots. *)
  dn_perm  : gname;
}.

(* ---------------------------------------------------------------------- *)
(* the disk view and the points-to                                         *)
(* ---------------------------------------------------------------------- *)

(* [disk_view] itself lives in [VirtioModel.v]: the auth it ties is the
   ERA one in [RiscvPtsto.era_interp] (claude-notes/design/crash.md),
   which is below this file, so the predicate has to be stated in the
   iris-free model.  [disk_read_cons] and the whole byte-level points-to
   algebra likewise live in [DiskImg.v], at a bare gname: the power thread
   mints an era's fragments before any [disk_names] record exists.  The
   [disk_names]-keyed forms below are those, verbatim, at [dn_img γ]. *)

Section DiskPtsto.
  (* [riscvFixedGS] rather than [!diskImgG Σ]: it CARRIES [diskImgG]
     ([riscvF_diskGS]), so naming both would be the same double path this
     file just removed for [mono_natG].  It also supplies the [mono_natG]
     the disk's [nc] counter needs. *)
  Context `{!diskGhostG Σ, !riscvFixedGS Σ}.

  (* -- the frozen live configuration ------------------------------------ *)

  (* [virtio_disk_init] freezes the configuration it programmed into this
     persistent fact.  A driver holding it and the copy the device invariant
     exports (from any accessor) learns [v_cfg v = the config it programmed],
     hence the three queue-page addresses.

     BEFORE the freeze the SAME cell is the boot chain's CONFIG TRACKER: the
     not-live arm of [virtio_proto] holds [disk_cfg_is γ (DfracOwn (1/2))
     (v_cfg v)] and the driver holds the other half, so a boot chain that
     programs the queue from inside the device invariant keeps deterministic
     knowledge of the configuration it has written so far (the device never
     touches [v_cfg], so the pair is stable across device steps), and the two
     halves recombine to the exclusive fraction exactly at the live flip,
     which is what [disk_cfg_set] consumes.  One cell serves both roles: a
     separate ghost_var over the same object would be redundant. *)
  Definition disk_cfg_is (γ : disk_names) (dq : dfrac) (c : virtio_cfg)
    : iProp Σ := own (dn_cfg γ) (to_dfrac_agree dq (c : leibnizO virtio_cfg)).

  Definition disk_cfg (γ : disk_names) (c : virtio_cfg) : iProp Σ :=
    disk_cfg_is γ DfracDiscarded c.

  Global Instance disk_cfg_persistent γ c : Persistent (disk_cfg γ c).
  Proof. rewrite /disk_cfg /disk_cfg_is. apply _. Qed.
  Global Instance disk_cfg_timeless γ c : Timeless (disk_cfg γ c).
  Proof. rewrite /disk_cfg /disk_cfg_is. apply _. Qed.
  Global Instance disk_cfg_is_timeless γ dq c : Timeless (disk_cfg_is γ dq c).
  Proof. rewrite /disk_cfg_is. apply _. Qed.

  Lemma disk_cfg_agree (γ : disk_names) (c c' : virtio_cfg) :
    disk_cfg γ c -∗ disk_cfg γ c' -∗ ⌜c = c'⌝.
  Proof.
    iIntros "Ha Hb". rewrite /disk_cfg /disk_cfg_is.
    by iDestruct (own_valid_2 with "Ha Hb") as %[_ ?]%dfrac_agree_op_valid_L.
  Qed.

  (* the tracker form: any two views of the cell agree on the value.  This is
     what makes the boot chain's half deterministic knowledge -- it is the one
     lemma [virtio_disk_init]'s caller uses to identify the configuration it
     was handed with the one the invariant currently holds. *)
  Lemma disk_cfg_is_agree (γ : disk_names) (dq dq' : dfrac) (c c' : virtio_cfg) :
    disk_cfg_is γ dq c -∗ disk_cfg_is γ dq' c' -∗ ⌜c = c'⌝.
  Proof.
    iIntros "Ha Hb". rewrite /disk_cfg_is.
    by iDestruct (own_valid_2 with "Ha Hb") as %[_ ?]%dfrac_agree_op_valid_L.
  Qed.

  (* the exclusive fraction splits into the invariant's half and the driver's,
     and rejoins for [disk_cfg_set] at the live flip *)
  Lemma disk_cfg_is_split (γ : disk_names) (c : virtio_cfg) :
    disk_cfg_is γ (DfracOwn 1) c -∗
    disk_cfg_is γ (DfracOwn (1/2)) c ∗ disk_cfg_is γ (DfracOwn (1/2)) c.
  Proof.
    iIntros "H". rewrite /disk_cfg_is.
    iEval (rewrite -Qp.half_half -dfrac_op_own dfrac_agree_op own_op) in "H".
    iDestruct "H" as "[$ $]".
  Qed.

  Lemma disk_cfg_is_join (γ : disk_names) (c c' : virtio_cfg) :
    disk_cfg_is γ (DfracOwn (1/2)) c -∗ disk_cfg_is γ (DfracOwn (1/2)) c' -∗
    disk_cfg_is γ (DfracOwn 1) c.
  Proof.
    iIntros "Ha Hb".
    iDestruct (disk_cfg_is_agree with "Ha Hb") as %<-.
    rewrite /disk_cfg_is.
    iEval (rewrite -Qp.half_half -dfrac_op_own dfrac_agree_op own_op).
    iFrame "Ha Hb".
  Qed.

  Lemma disk_cfg_alloc (c : virtio_cfg) :
    ⊢ |==> ∃ g : gname, own g (to_dfrac_agree (DfracOwn 1) (c : leibnizO virtio_cfg)).
  Proof. iApply own_alloc. done. Qed.

  (* set the value (full fraction is exclusive) and then freeze it *)
  Lemma disk_cfg_set (γ : disk_names) (c c' : virtio_cfg) :
    disk_cfg_is γ (DfracOwn 1) c ==∗ disk_cfg γ c'.
  Proof.
    iIntros "H". rewrite /disk_cfg_is /disk_cfg /disk_cfg_is.
    iMod (own_update _ _ (to_dfrac_agree (DfracOwn 1) (c' : leibnizO virtio_cfg))
            with "H") as "H".
    { apply cmra_update_exclusive. done. }
    iApply (own_update with "H"). apply dfrac_agree_persist.
  Qed.

  (* MOVE the tracker without freezing it: the pre-flip half of [disk_cfg_set].
     Every configuration write [virtio_disk_init] performs before the queue
     goes live steps the tracker this way -- the two halves rejoin, the value
     moves, and the pair splits again -- so the driver keeps deterministic
     knowledge of what it has programmed while the state itself lives under
     [disk_inv].  The freeze happens exactly once, at the live flip. *)
  Lemma disk_cfg_is_move (γ : disk_names) (c c' : virtio_cfg) :
    disk_cfg_is γ (DfracOwn 1) c ==∗ disk_cfg_is γ (DfracOwn 1) c'.
  Proof.
    iIntros "H". rewrite /disk_cfg_is.
    iApply (own_update with "H"). apply cmra_update_exclusive. done.
  Qed.

  (* -- the disk points-to ----------------------------------------------- *)
  (*                                                                        *)
  (* Every form below is [DiskImg]'s gname-keyed one at [dn_img γ] -- the    *)
  (* era's image gname, constructed (not allocated) by                       *)
  (* [VirtioProto.disk_ghosts_alloc].  Restated here rather than aliased so  *)
  (* that no client statement changes and no implicit argument moves.        *)

  Definition disk_byte (γ : disk_names) (o : Z) (b : bv 8) : iProp Σ :=
    disk_img_byte (dn_img γ) o b.

  Definition disk_bytes (γ : disk_names) (o : Z) (bs : list (bv 8)) : iProp Σ :=
    disk_img_bytes (dn_img γ) o bs.

  (* the block form [virtio_disk_rw]'s spec moves: xv6's BSIZE = 1024 *)
  Definition disk_block (γ : disk_names) (bno : Z) (bs : list (bv 8)) : iProp Σ :=
    (⌜length bs = 1024%nat⌝ ∗ disk_bytes γ (1024 * bno) bs)%I.

  Global Instance disk_byte_timeless γ o b : Timeless (disk_byte γ o b).
  Proof. rewrite /disk_byte. apply _. Qed.
  Global Instance disk_bytes_timeless γ o bs : Timeless (disk_bytes γ o bs).
  Proof. rewrite /disk_bytes. apply _. Qed.
  Global Instance disk_block_timeless γ bno bs : Timeless (disk_block γ bno bs).
  Proof. rewrite /disk_block /disk_bytes. apply _. Qed.

  (* -- structural peeling ----------------------------------------------- *)

  Lemma disk_bytes_cons (γ : disk_names) (o : Z) (b : bv 8) (bs : list (bv 8)) :
    disk_bytes γ o (b :: bs) ⊣⊢ disk_byte γ o b ∗ disk_bytes γ (o + 1) bs.
  Proof. exact (disk_img_bytes_cons (dn_img γ) o b bs). Qed.

  (* -- agreement: fragments read the image ------------------------------ *)

  Lemma disk_bytes_read (γ : disk_names) (dmap : gmap Z (bv 8))
      (dk : Z -> bv 8) (o : Z) (bs : list (bv 8)) :
    disk_view dmap dk ->
    ghost_map_auth (dn_img γ) 1 dmap -∗ disk_bytes γ o bs -∗
    ⌜disk_read dk o (length bs) = bs⌝.
  Proof. exact (disk_img_bytes_read (dn_img γ) dmap dk o bs). Qed.

  (* -- update: an OUT completion rewrites a range ----------------------- *)

  (* the raw update: the new map holds [bs'] on the range and agrees with the
     old one everywhere else.  [disk_bytes_update] reads the [disk_view]
     transfer off these two clauses. *)
  Lemma disk_bytes_update_gen (γ : disk_names) (dmap : gmap Z (bv 8))
      (o : Z) (bs bs' : list (bv 8)) :
    length bs' = length bs ->
    ghost_map_auth (dn_img γ) 1 dmap -∗ disk_bytes γ o bs ==∗
    ∃ dmap' : gmap Z (bv 8),
      ghost_map_auth (dn_img γ) 1 dmap' ∗ disk_bytes γ o bs' ∗
      ⌜forall (j : nat) (b : bv 8), bs' !! j = Some b ->
         dmap' !! (o + Z.of_nat j)%Z = Some b⌝ ∗
      ⌜forall x : Z,
         (forall j : nat, (j < length bs')%nat -> (x ≠ o + Z.of_nat j)%Z) ->
         dmap' !! x = dmap !! x⌝.
  Proof. exact (disk_img_bytes_update_gen (dn_img γ) dmap o bs bs'). Qed.

  Lemma disk_bytes_update (γ : disk_names) (dmap : gmap Z (bv 8))
      (o : Z) (bs bs' : list (bv 8)) :
    length bs' = length bs ->
    ghost_map_auth (dn_img γ) 1 dmap -∗ disk_bytes γ o bs ==∗
    ∃ dmap' : gmap Z (bv 8),
      ghost_map_auth (dn_img γ) 1 dmap' ∗ disk_bytes γ o bs' ∗
      ⌜forall dk : Z -> bv 8,
         disk_view dmap dk -> disk_view dmap' (disk_write dk o bs')⌝.
  Proof. exact (disk_img_bytes_update (dn_img γ) dmap o bs bs'). Qed.

  (* -- minting: fragments for untouched offsets ------------------------- *)

  Lemma disk_bytes_mint (γ : disk_names) (dmap : gmap Z (bv 8))
      (dk : Z -> bv 8) (o : Z) (n : nat) :
    disk_view dmap dk ->
    (forall j : nat, (j < n)%nat -> dmap !! (o + Z.of_nat j) = None) ->
    ghost_map_auth (dn_img γ) 1 dmap ==∗
    ∃ dmap' : gmap Z (bv 8),
      ghost_map_auth (dn_img γ) 1 dmap' ∗
      disk_bytes γ o (disk_read dk o n) ∗
      ⌜disk_view dmap' dk⌝.
  Proof. exact (disk_img_bytes_mint (dn_img γ) dmap dk o n). Qed.

End DiskPtsto.
