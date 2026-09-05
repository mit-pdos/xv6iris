(*  AppDur.v -- THE APPLICATION'S DURABLE INSTANCE: its claim about the
    committed abstract state, beside the snapshot, tied by half an
    authority.

    Design of record: claude-notes/projects/app-instances.md sections 0-3
    and 7 (round C, "the durable instance").

    THE TIE (section 2).  Owner's rule: nothing application-specific inside
    a kernel file-system predicate.  The kernel's durable snapshot
    [FsDurSnap.fs_snap] keeps the KERNEL half of its abstract map's
    authority; the application's durable claim is a SEPARATE conjunct of
    the crash slot, holding the GUEST half at the same gname beside the
    claim about the map's view.  Agreement ([ghost_map_auth_agree]) is the
    identification: no binder is shared with the snapshot's own record.

    THREE CROSSINGS, ONE TRANSPORT ([AppInv.app_xfer_raw]).  At the COMMIT
    the file system's law ([FsCollectAll.fs_snap_law_build]) mints a fresh
    snapshot and hands its guest half here, where the running claim is
    copied onto it ([app_dur_raw_clone]).  At POWER-ON the clone
    ([FsCrash.P_fs_swap]) does the same off the crash slot's own guest.  At
    the BOOT the lent guest meets the clone's kernel half, agreement pins
    the founded map, and the claim goes straight into the era's running
    invariant ([app_dur_raw_agree], then [AppInv.app_inv_alloc]).

    RAW FIRST, PINNED SECOND.  [app_dur_raw] takes the predicate as an
    argument so the system theorem can state the crash slot under
    [riscvGpreS], before any era's record exists ([SystemAdequacy]'s
    composite [Pc]); [app_guest] is the same thing at the era's ambient
    record, and it is the ONE value of the WAL's opaque guest index
    ([FsCrash.fs_crash_seam_at], [LogSnapLaw.snap_law_at]) that the tree
    ever supplies.

    UNDER A LATER.  The transport yields [▷ A], so every producer packs the
    guest [▷]-shaped ([app_dur_raw_pack]); the crash slot at [SystemAdequacy]
    stores it later-free because the slot itself sits under the machine's
    own [▷]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import Xv6Cameras.      (* [fsTopG]: the top map's ghost class *)
Require Import FsNode.          (* [fs_node] *)
Require Import FsAbsDefs.       (* [aview], [abs_view] *)
Require Import AppCfg.          (* [appcfg]: [app_pred] *)
Require Import AppInv.          (* [app_xfer_raw]: the transport *)

Local Open Scope Z_scope.

Section AppDurRaw.
  Context `{!fsTopG Σ}.

  (* THE DURABLE CLAIM at a predicate and a snapshot map name [gt]: the
     guest half of the map's authority beside the claim at the map's view,
     at SOME instance of the application's names -- the one the transport
     minted. *)
  Definition app_dur_raw {N : Type} (A : N -> aview -> iProp Σ)
      (gt : gname) : iProp Σ :=
    (∃ (r : N) (I : gmap Z fs_node),
       ghost_map_auth gt (1/2) I ∗ A r (abs_view I))%I.

  (* OPENING A LATER-SHAPED GUEST: the half is timeless and comes out; the
     claim stays under its later.  [N] need not be inhabited, which is why
     the existential is pulled through the later with the [◇]. *)
  Lemma app_dur_raw_open {N} (A : N -> aview -> iProp Σ) (gt : gname) :
    ▷ app_dur_raw A gt -∗
      ◇ ∃ (r : N) (I : gmap Z fs_node),
          ghost_map_auth gt (1/2) I ∗ ▷ A r (abs_view I).
  Proof.
    iIntros "H". rewrite /app_dur_raw.
    iPoseProof (bi.later_exist_except_0 with "H") as "H".
    iMod "H" as (r) "H".
    iDestruct "H" as (I) "[>Hh Hp]".
    iModIntro. iExists r, I. iFrame "Hh Hp".
  Qed.

  (* PACKING: the guest half beside a claim at the same map, under the
     later the transport left on the claim *)
  Lemma app_dur_raw_pack {N} (A : N -> aview -> iProp Σ) (gt : gname)
      (I : gmap Z fs_node) :
    ghost_map_auth gt (1/2) I -∗
    (∃ r : N, ▷ A r (abs_view I)) -∗
    ▷ app_dur_raw A gt.
  Proof.
    iIntros "Hh Hp". iDestruct "Hp" as (r) "Hp".
    iNext. rewrite /app_dur_raw. iExists r, I. iFrame "Hh Hp".
  Qed.

  (* THE CLONE (the commit and the PowerOn arm): run the transport on a
     claim, keep the original, and pack the copy onto a fresh guest half at
     the same map *)
  Lemma app_dur_raw_clone {N} (A : N -> aview -> iProp Σ) (gt : gname)
      (I : gmap Z fs_node) (r : N) :
    app_xfer_raw A -∗
    ghost_map_auth gt (1/2) I -∗
    ▷ A r (abs_view I) ==∗
      ▷ A r (abs_view I) ∗ ▷ app_dur_raw A gt.
  Proof.
    iIntros "#Hx Hh Hp". rewrite /app_xfer_raw.
    iMod ("Hx" with "Hp") as "[Hp Hnew]".
    iModIntro. iFrame "Hp". iApply (app_dur_raw_pack with "Hh Hnew").
  Qed.

  (* AGREEMENT (the boot, and the PowerOn arm): a guest against a kernel
     fraction of the same map pins the guest's map, and the claim comes out
     at the kernel's map, under its later; both fractions come back *)
  Lemma app_dur_raw_agree {N} (A : N -> aview -> iProp Σ) (gt : gname)
      (q : Qp) (I : gmap Z fs_node) :
    ghost_map_auth gt q I -∗
    ▷ app_dur_raw A gt -∗
      ◇ (ghost_map_auth gt q I ∗ ghost_map_auth gt (1/2) I ∗
         ∃ r : N, ▷ A r (abs_view I)).
  Proof.
    iIntros "Hk Hg".
    iMod (app_dur_raw_open with "Hg") as (r I') "[Hh Hp]".
    iDestruct (ghost_map_auth_agree with "Hk Hh") as %<-.
    iModIntro. iFrame "Hk Hh". iExists r. iExact "Hp".
  Qed.
End AppDurRaw.

Section AppDur.
  Context `{!fsTopG Σ}.
  Context `{APP : appcfg Σ}.

  (* THE GUEST, at the era's record: the one value the WAL's opaque index
     [G : gname -> iProp Σ] ever takes ([FsCollectAll.fs_snap_law_build]) *)
  Definition app_guest (gt : gname) : iProp Σ := app_dur_raw app_pred gt.
End AppDur.
