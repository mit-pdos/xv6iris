(*  AppCfg.v -- THE APPLICATION'S PREDICATE ON THE ABSTRACT FILE-SYSTEM
    STATE, as a class record and nothing else.

    Design of record: claude-notes/design/applications.md section 1.  An
    application proven on top of xv6 claims something of the node map
    between taints -- [app_pred I], an iProp over the RAW node map, so that
    the claim can OWN resources (per-node fragments, receipts, the
    application's own ghosts; the owner's 2026-09-05 correction: a pure
    left arm is bogus).  It is the one field here, and the record is
    carried exactly as [IcacheRef.icfg] and [FsCfg.fscfg] are: a field of
    [FileInvDefs.fileG] ([file_app]), threaded EXPLICITLY through the boot
    kits ([FsCfgKits.fs_kit_fsinit_ghost], [FsCfgBoot.fs_boot_supply]) and
    the era mint ([FsCfgSnap.fs_cfg_alloc_snap]), and AMBIENT everywhere
    else -- [FsAbsInv.fsabs_ok] names it through the class, and every file
    that binds [fileG] sees it through [file_app].

    WHY ITS OWN RECORD, AND NOT A FIELD OF [fscfg].  [fscfg] is pure data
    (gnames, gsets, block numbers) with no [Σ] in sight, which is what lets
    it be minted by a fupd that has not built the era's [fileG] yet; an
    [iProp Σ] field would put [Σ] on it and on every consumer that only
    wanted a gname.  The application's predicate is a PROOF-side choice
    made once per theorem ([SystemAdequacy.xv6_boot_era] builds
    [MkAppcfg A] for the mint), so it gets a record of its own, parametric
    in [Σ], below [fscfg] in the tree.

    IT IS PER-ERA, EXACTLY AS [icfg] IS: a class assumption of each section,
    instantiated by each era's boot chain.  Nothing about the predicate is
    assumed timeless or persistent (applications.md section 2: the body
    keeps it under the invariant's later, and the dischargers move it
    without stripping).  The GENERIC application's is [fun _ => True]. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris.base_logic Require Import iprop.
Require Import FsNode.        (* [fs_node]: the predicate's domain *)

Class appcfg (Σ : gFunctors) := MkAppcfg {
  (* THE APPLICATION'S PREDICATE ON THE ABSTRACT FILE-SYSTEM STATE
     (claude-notes/design/applications.md section 1): an iProp over the raw
     node map, carried exactly as [icfg]/[fscfg] are -- a field of
     [fileG], threaded explicitly through the kits and the era mint,
     ambient everywhere else.  The GENERIC application's is
     [fun _ => True]. *)
  app_pred : gmap Z fs_node -> iProp Σ;
}.
(* the boot builds the record at a predicate whose [Σ] is already fixed
   ([SystemAdequacy.xv6_boot_era]: [MkAppcfg A]); [Σ] is implicit there
   exactly as it is on [App.MkApp] *)
Arguments MkAppcfg {Σ} _.
