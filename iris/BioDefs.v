(* BioDefs.v -- the names, ghost functors, slot fragments, and client view
   shared at the boundary of the bio ownership layer.

   This is deliberately separate from [BioInv]: the log layer constructs a
   view and owns the pool of available bio reference slots, so it should not
   serialize behind the buffer cache's escrow, lock resource, and
   initialization proofs.  [BioInv] re-exports this file to preserve the
   existing API. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac numbers.
From iris.base_logic.lib Require Import own.
Require Import SailStdpp.Values.
Require Import DiskPtsto.
Require Import Riscv.rv64d_types.
Require Export Xv6Cameras.  (* the cameras this file states its theory over *)
Local Open Scope Z_scope.

(* xv6's file-system block size.  Keep this at the bottom of the dependency
   graph: both the bio client view and pure inode byte indexing need it. *)
Definition BSIZE : nat := 1024%nat.
Definition BSLOTS : nat := 1024%nat.

(* THE SUPPLY SPLITS ONCE, AT BOOT, AND THE TWO SHARES NEVER MIX.
   [BSLOTS_PROC] is the proc layer's: three units per process slot, parked in
   [ProcDefs.proc_dormant] so that a slot which has never run still owns what
   its first syscall will need.  [BSLOTS_FS] is everything else -- the file
   system's own working supply, which is what [bio_init] hands back.
   Spelled as literals here because [BioDefs] sits below [ProcGeom] and must
   not name [NPROC]; [SpecProcinit] carries the equation [BSLOTS_PROC =
   NPROC * 3] where both are in scope. *)
Definition BSLOTS_PROC : nat := 192%nat.
Definition BSLOTS_FS : nat := 832%nat.

Lemma bslots_shares : BSLOTS = (BSLOTS_PROC + BSLOTS_FS)%nat.
Proof. reflexivity. Qed.

Record bio_names := MkBioNames {
  bn_lk   : gname;                (* the "bcache" spinlock               *)
  bn_auth : gname;                (* ● (gmap nat (frac * positive))      *)
  bn_slk  : nat -> gname * gname; (* buffer k's sleeplock (γl, γsl)      *)
  bn_own  : nat -> gname;         (* buffer k's checkout token           *)
  bn_mid  : nat -> gname;         (* buffer k's recycle token            *)
}.

(* ---------------------------------------------------------------------- *)
(* THE SLOT SUPPLY.  A [bslot] is the right to hold ONE buffer-cache         *)
(* reference: [bread] spends one and [brelse] returns it, and the bcache     *)
(* invariant parks [bslots n] against each buffer's refcount.  So the whole  *)
(* theory is a credit ledger over [authUR natUR], and the fragments are      *)
(* additive ([bslots_op]).                                                   *)
(*                                                                          *)
(* THE GHOST NAME IS CANONICAL ([Xv6Cameras.bioslot_name]), not a field of   *)
(* [bio_names] -- see that class's note.  Everything here therefore states   *)
(* at a bare count, which is what lets the per-process allowance live in     *)
(* [ProcDefs.proc_dormant] beside [fd_slots]/[iref_slots] without dragging   *)
(* a file-system ghost name below the file system.                          *)
(* ---------------------------------------------------------------------- *)
Section BioSlots.
  Context `{!bioslotG Σ}.

  Definition bslots (n : nat) : iProp Σ := own bioslot_name (◯ n).
  Definition bslot : iProp Σ := bslots 1.
  Definition bslots_auth : iProp Σ := own bioslot_name (● BSLOTS).

  Lemma bslots_op a b : bslots (a + b) ⊣⊢ bslots a ∗ bslots b.
  Proof.
    rewrite /bslots.
    assert (Hop : (◯ (a + b)%nat : bioslotUR) = ◯ a ⋅ ◯ b)
      by (rewrite -auth_frag_op; reflexivity).
    rewrite Hop own_op. reflexivity.
  Qed.

  Lemma bslots_split a b : bslots (a + b) -∗ bslots a ∗ bslots b.
  Proof. rewrite bslots_op. iIntros "$". Qed.
  Lemma bslots_combine a b : bslots a -∗ bslots b -∗ bslots (a + b).
  Proof. iIntros "Ha Hb". rewrite bslots_op. iFrame. Qed.

  Lemma bslots_bound n : bslots_auth -∗ bslots n -∗ ⌜(n <= BSLOTS)%nat⌝.
  Proof.
    rewrite /bslots_auth /bslots. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro. by apply nat_included in Hincl.
  Qed.

  (* the consequence every increment needs: a slot-backed count is far below
     what an int can hold (fd_slots_no_overflow's mirror). *)
  Lemma bslots_no_overflow (n : positive) :
    bslots_auth -∗ bslots (Pos.to_nat n) -∗
    ⌜(Z.pos n < 2 ^ 31)%Z /\ (Z.pos (Pos.succ n) < 2 ^ 31)%Z⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (bslots_bound with "Ha Hf") as %Hle.
    iPureIntro.
    assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (EB : BSLOTS = 1024%nat) by (vm_compute; reflexivity).
    rewrite EB in Hle.
    assert (Hz : (Z.pos n <= 1024)%Z) by (rewrite -positive_nat_Z; lia).
    rewrite E31. lia.
  Qed.
End BioSlots.

(* the supply, minted once at boot -- the shape [IrefSlots.iref_slots_alloc]
   and [FdSlots.fd_slots_alloc] already use.  [bio_init] no longer allocates
   it (it cannot: the name is fixed before the invariant exists), so it takes
   the authority as a premise and the caller keeps the fragments. *)
Lemma bslots_alloc `{!bioslotGpreS Σ} :
  ⊢ |==> ∃ _ : bioslotG Σ, bslots_auth ∗ bslots BSLOTS_PROC ∗ bslots BSLOTS_FS.
Proof.
  iMod (own_alloc ((● BSLOTS ⋅ ◯ BSLOTS) : bioslotUR)) as (γ) "[Ha Hf]".
  { apply auth_both_valid_discrete. split; [done | done]. }
  iModIntro. iExists (BioSlotG Σ _ γ). iFrame "Ha".
  rewrite /bslots.
  assert (Hsh : (◯ BSLOTS : bioslotUR) = ◯ BSLOTS_PROC ⋅ ◯ BSLOTS_FS)
    by (rewrite -auth_frag_op; reflexivity).
  rewrite Hsh own_op. by iFrame.
Qed.

(* THE CLIENT VIEW the whole bio layer is parametric over: the disk ghost the
   covered blocks' [disk_block] fragments live at, the ONE covered device,
   the covered block-number range, and the two opaque content payloads.
   The log layer instantiates the payloads with its logged-view ghost halves;
   bio itself never opens them.  [bv_cov] must not contain 0 (binit leaves
   every buffer's blockno cell at 0) -- [BioInv.bio_init] takes that premise. *)
Record bio_view (Σ : gFunctors) := MkBioView {
  bv_gd    : disk_names;
  bv_dev   : SailStdpp.Values.mword 32;
  bv_cov   : gset Z;
  bv_clean : Z -> list (bv 8) -> iProp Σ;
  bv_dirty : Z -> list (bv 8) -> iProp Σ;
  (* The payloads ride an escrow opened inside atomic updates, so no step is
     available to absorb a later. *)
  bv_clean_tl : forall b bs, Timeless (bv_clean b bs);
  bv_dirty_tl : forall b bs, Timeless (bv_dirty b bs);
}.
Arguments bv_gd {Σ} _.
Arguments bv_dev {Σ} _.
Arguments bv_cov {Σ} _.
Arguments bv_clean {Σ} _.
Arguments bv_dirty {Σ} _.
Arguments bv_clean_tl {Σ} _ _ _.
Arguments bv_dirty_tl {Σ} _ _ _.
Arguments MkBioView {Σ} _ _ _ _ _ _ _.

Global Instance bio_view_clean_timeless {Σ} (V : bio_view Σ) b bs :
  Timeless (bv_clean V b bs) := bv_clean_tl V b bs.
Global Instance bio_view_dirty_timeless {Σ} (V : bio_view Σ) b bs :
  Timeless (bv_dirty V b bs) := bv_dirty_tl V b bs.
