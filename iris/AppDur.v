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

    THREE CROSSINGS.  At the COMMIT the file system's law
    ([FsCollectAll.fs_snap_law_build]) mints a fresh snapshot and hands its
    guest half here, where the MERGE ([AppInv.app_merge_raw], SY3-K2) turns
    the running claim into a wand from the old guest to the new one
    ([app_dur_raw_merge]), applied at the header write.  At POWER-ON the clone
    ([FsCrash.P_fs_swap]) runs the TRANSPORT ([AppInv.app_xfer_raw]) on
    the crash slot's own guest (the shape [app_dur_raw_clone] states).  At
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
    own [▷].

    THE DURABLE-COPY PREDICATE [Okc] (sync SY3-A3b, design/sync.md §4.5
    "The copy predicate").  The guest's record satisfies a pure predicate
    the application chooses ([App.app_okc]; [True] for every application
    but the union, whose is "the role field says durable copy"), because a
    claim that cannot tell a durable copy from a running one by its ghost
    state alone has to learn it somewhere: every producer of a guest -- the
    merge's new copy, the PowerOn transport's re-based copy, era 0's
    founding -- proves it, and the merge's wand receives it of the old
    copy.  [appcfg] does not carry it, so the crash seam at the era's guest
    and the merge package are closed over it TOGETHER ([app_dur_laws]). *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import Xv6Cameras.      (* [fsTopG]: the top map's ghost class *)
Require Import FsNode.          (* [fs_node] *)
Require Import FsAbsDefs.       (* [aview], [abs_view] *)
Require Import AppCfg.          (* [appcfg]: [app_pred] *)
Require Import AppInv.          (* [app_xfer_raw]: the transport; [app_merge_raw]: the merge *)
Require Import RiscvPtsto.      (* [riscvFixedGS]/[start_auth]: the merge's loan *)
Require RiscvLang.              (* [GenId]: the package's era *)
Require FsCrash.                (* [fs_crash_seam_at]: the seam at the guest, packaged
                                   with the merge ([app_dur_laws], sync SY3-A3b) *)

Local Open Scope Z_scope.

Section AppDurRaw.
  Context `{!fsTopG Σ}.

  (* THE DURABLE CLAIM at a predicate, a durable-copy predicate and a
     snapshot map name [gt]: the guest half of the map's authority beside
     the claim at the map's view, at SOME instance of the application's
     names satisfying [Okc] -- the one the transport or the merge minted. *)
  Definition app_dur_raw {N : Type} (A : N -> aview -> iProp Σ)
      (Okc : N -> Prop) (gt : gname) : iProp Σ :=
    (∃ (r : N) (I : gmap Z fs_node),
       ⌜Okc r⌝ ∗ ghost_map_auth_frac gt (1/2) I ∗ A r (abs_view I))%I.

  (* OPENING A LATER-SHAPED GUEST: the half and the record's predicate are
     timeless and come out; the claim stays under its later.  [N] need not
     be inhabited, which is why the existential is pulled through the later
     with the [◇]. *)
  Lemma app_dur_raw_open {N} (A : N -> aview -> iProp Σ) (Okc : N -> Prop)
      (gt : gname) :
    ▷ app_dur_raw A Okc gt -∗
      ◇ ∃ (r : N) (I : gmap Z fs_node),
          ⌜Okc r⌝ ∗ ghost_map_auth_frac gt (1/2) I ∗ ▷ A r (abs_view I).
  Proof using .
    iIntros "H". rewrite /app_dur_raw.
    iPoseProof (bi.later_exist_except_0 with "H") as "H".
    iMod "H" as (r) "H".
    iDestruct "H" as (I) "(>%Hr & >Hh & Hp)".
    iModIntro. iExists r, I. iFrame "Hh Hp". by iPureIntro.
  Qed.

  (* PACKING: the guest half beside a claim at the same map, under the
     later the transport left on the claim, at a record satisfying [Okc] *)
  Lemma app_dur_raw_pack {N} (A : N -> aview -> iProp Σ) (Okc : N -> Prop)
      (gt : gname) (I : gmap Z fs_node) :
    ghost_map_auth_frac gt (1/2) I -∗
    (∃ r : N, ⌜Okc r⌝ ∗ ▷ A r (abs_view I)) -∗
    ▷ app_dur_raw A Okc gt.
  Proof using .
    iIntros "Hh Hp". iDestruct "Hp" as (r) "[%Hr Hp]".
    iNext. rewrite /app_dur_raw. iExists r, I. iFrame "Hh Hp". by iPureIntro.
  Qed.

  (* AGREEMENT: a guest against a kernel fraction of the same map pins the
     guest's map, and the claim comes out at the kernel's map, under its
     later, with its record's predicate; both fractions come back *)
  Lemma app_dur_raw_agree {N} (A : N -> aview -> iProp Σ) (Okc : N -> Prop)
      (gt : gname) (q : Qp) (I : gmap Z fs_node) :
    ghost_map_auth_frac gt q I -∗
    ▷ app_dur_raw A Okc gt -∗
      ◇ (ghost_map_auth_frac gt q I ∗ ghost_map_auth_frac gt (1/2) I ∗
         ∃ r : N, ⌜Okc r⌝ ∗ ▷ A r (abs_view I)).
  Proof using .
    iIntros "Hk Hg".
    iMod (app_dur_raw_open with "Hg") as (r I') "(%Hr & Hh & Hp)".
    iDestruct (ghost_map_auth_agree with "Hk Hh") as %<-.
    iModIntro. iFrame "Hk Hh". iExists r. iFrame "Hp". by iPureIntro.
  Qed.
End AppDurRaw.

(* THE MERGE'S GUEST FORM needs the fixed record's class: its wand is lent
   the machine's started auth (sync SY3-A1) *)
Section AppDurMerge.
  Context `{!fsTopG Σ, !riscvFixedGS Σ}.

  (* THE MERGE (the commit, SY3-K2): run the merge on the running claim,
     keep the original, and hand out the guest-level wand the WAL applies
     to the old guest at the header write ([FsDurSnap.dur_merge]).  The
     fresh guest half goes INTO the wand beside the merge's own; the old
     guest's half is dropped with it, its claim and its record's durable-
     copy predicate go to the merge.  The token [T] (sync K3-3) goes in
     with the running claim and comes back on either arm of the additive
     pair; the started auth the wand is lent (SY3-A1) passes straight
     through to the application's own wand. *)
  Lemma app_dur_raw_merge {N} (A : N -> aview -> iProp Σ) (Ok Okc : N -> Prop)
      (T : iProp Σ) (gd : nat) (gt : gname) (I : gmap Z fs_node) (r : N) :
    (* the running record satisfies the era's record predicate *)
    Ok r ->
    app_merge_raw A Ok Okc T gd -∗
    ghost_map_auth_frac gt (1/2) I -∗
    ▷ A r (abs_view I) -∗
    T ==∗
      ▷ A r (abs_view I) ∗
      ((∀ (gt_o : gname) (n : nat), ⌜n = (gd + 1)%nat⌝ -∗ start_auth n -∗
          ▷ app_dur_raw A Okc gt_o ==∗ ▷ app_dur_raw A Okc gt ∗ T ∗ start_auth n)
       ∧ T).
  Proof using .
    intros HOk. iIntros "#Hm Hh Hp HT". rewrite /app_merge_raw.
    iMod ("Hm" with "[//] Hp HT") as "[Hp Hw]".
    iDestruct "Hw" as (r') "(_ & %Hr' & Hw)".
    iModIntro. iFrame "Hp". iSplit; [| iDestruct "Hw" as "[_ HT]"; iExact "HT"].
    iDestruct "Hw" as "[Hw _]".
    iIntros (gt_o n Hn) "Hsa Hold".
    iMod ("Hw" $! n with "[//] Hsa [Hold]") as "(Hnew & HT & Hsa)".
    { iNext. iEval (rewrite /app_dur_raw) in "Hold".
      iDestruct "Hold" as (r_o I_o) "(%Hro & _ & Hold)".
      iExists r_o, (abs_view I_o). iFrame "Hold". by iPureIntro. }
    iModIntro. iFrame "HT Hsa".
    iApply (app_dur_raw_pack with "Hh"). iExists r'. iFrame "Hnew". by iPureIntro.
  Qed.
End AppDurMerge.

Section AppDur.
  Context `{!fsTopG Σ}.
  Context `{APP : appcfg Σ}.

  (* THE GUEST, at the era's record and a durable-copy predicate: the one
     value the WAL's opaque index [G : gname -> iProp Σ] ever takes
     ([FsCollectAll.fs_snap_law_build]) *)
  Definition app_guest (Okc : app_names -> Prop) (gt : gname) : iProp Σ :=
    app_dur_raw app_pred Okc gt.
End AppDur.

(* THE ERA'S DURABLE SIDE, AS ONE PACKAGE (sync SY3-A3b): the crash seam at
   the era's guest and the merge package ([AppInv.app_merge]), closed over
   ONE durable-copy predicate -- which [appcfg] does not carry, and which
   the two must agree on: the merge's wand reads [Okc] of the old copy the
   seam hands the header write.  What the boot builds (at the application's
   [App.app_okc]) and carries on fsinit's kit, where the commit's law and
   the hooked law are built out of it. *)
Section AppDurLaws.
  Context `{!riscvGS Σ, !fsCrashG Σ, !lockG Σ, !fsLinkG Σ, !fsTopG Σ}.
  Context `{GEN : RiscvLang.GenId}.
  Context `{APP : appcfg Σ}.

  Definition app_dur_laws (cov : gset Z) (ls : Z) : iProp Σ :=
    (∃ Okc : app_names -> Prop,
       FsCrash.fs_crash_seam_at (app_guest Okc) cov ls ∗ app_merge Okc)%I.

  Global Instance app_dur_laws_persistent cov ls : Persistent (app_dur_laws cov ls).
  Proof using . rewrite /app_dur_laws. apply _. Qed.
End AppDurLaws.
