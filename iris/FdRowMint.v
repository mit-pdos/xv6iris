(* ===================================================================== *)
(* FdRowMint.v -- THE ERA-0 MIRROR MINT, at the userinit park.             *)
(*                                                                         *)
(* Design of record: claude-notes/design/fd-row-pilot.md, section 6 item 3 *)
(* (the era-0 mint at the userinit park -- allocate [γm], kernel half      *)
(* into the enriched residue, user half + seed facts into init's entry     *)
(* deposit).  Prover plan: the FD-ROW PILOT section of                     *)
(* claude-notes/projects/fs-syscall-specs.md, stage P3.                    *)
(*                                                                         *)
(* WHAT THIS FILE IS.  [FdRowPilot.era0_seed_boot] already says that the   *)
(* mirror VALUE the era boots at is a seed: cwd at ROOTINO, sixteen        *)
(* closed rows, a console-less root directory, read off the checked image  *)
(* through [FsInitPin]'s era-0 facts.  What is missing between that pure   *)
(* fact and init's program proof is the GHOST and its two HOMES.  This     *)
(* file is exactly that:                                                   *)
(*                                                                         *)
(*   [mirror_entry γm u]  -- INIT'S ENTRY PACKAGE: the mirror's USER half  *)
(*     beside the seed facts.  This is what the process carries into its   *)
(*     first enriched syscall: the half is the deposit the arm's right     *)
(*     disjunct takes ([UexecRetFs.uexec_ret_fs_F]) and the seed is        *)
(*     [FdRowPilot.pilot_console_pure]'s first premise, so the package IS  *)
(*     the pilot's hypothesis set, packed.                                 *)
(*                                                                         *)
(*   [mirror_tied γm γfd Γ cw u] -- THE ENRICHED LOOP'S RESIDUE: the       *)
(*     mirror's KERNEL half held BESIDE THE REAL GHOSTS, at the reading    *)
(*     those ghosts carry.  Faithfulness is therefore DEFINITIONAL at the  *)
(*     residue's index rather than asserted: the fd leg IS                 *)
(*     [FdSlots.fd_frags]'s list, the av leg IS [FsAbs.astate]'s view, and *)
(*     the loop's obligation (stage P4) is to RE-INDEX the pair as the     *)
(*     real ghosts move, which is what [mirror_tied_round] is shaped for.  *)
(*                                                                         *)
(*   [mirror_era0_mint] / [mirror_era0_mint_tied] -- THE MINT: from the    *)
(*     era-0 boot state, allocate [γm] and place both halves.              *)
(*                                                                         *)
(* THE SOLO SCOPING, WHERE IT ACTUALLY BITES (design section 5, OWNER-     *)
(* RULED YES 2026-08-31).  The av leg is a faithful reading of the SHARED  *)
(* abstract state only while init is the sole process.  In this file that  *)
(* ruling costs exactly one thing: [mirror_tied] holds [astate Γ (um_av    *)
(* u)] -- the EXCLUSIVE authority -- rather than a share or an             *)
(* observation.  A residue that owns the whole authority across a          *)
(* process's excursion is only inhabitable in a quiescent, single-process  *)
(* era, and that is the honest statement of the scoping: it is a           *)
(* condition on who can HOLD the residue, not a hedge inside it.  The      *)
(* post-fork row weakens this one conjunct to existential observations     *)
(* backed by persistent certificates and changes nothing else (design      *)
(* section 5, non-goal section 7).                                         *)
(*                                                                         *)
(* WHAT IS *NOT* CLAIMED HERE.  The mirror is a FRESH ghost: minting it at *)
(* the seed asserts nothing about the kernel by itself.  The tie to the    *)
(* real state is the [mirror_tied] conjuncts, and those are premises of    *)
(* the tied mint, discharged at the boot instant by the sites named in     *)
(* section 5's ask -- never assumed as a "gap" the way durable-notes'      *)
(* "A GAP PREMISE CAN BE UNSATISFIABLE" warns about.  Each of the three is *)
(* an ordinary inhabited resource with a named producer:                   *)
(* [fd_frags γ fdt0] from [ProcInv]'s slot-open mint, [astate Γ (abs_view  *)
(* (fss_inodes S))] from the snapshot boot mint (the authority             *)
(* [FsInitPin] section 6's live corollaries stand on), and the cwd         *)
(* equation from userinit's own [namei("/")].                              *)
(*                                                                         *)
(* NOTHING IS SEALED IN THIS FILE, and it introduces no [Axiom]: every     *)
(* statement below is proven.                                              *)
(*                                                                         *)
(* THE LEAF RULE ([FsImgCheck.v]'s header).  [FdRowPilot] requires         *)
(* [FsInitPin]/[FsImgCheck], so the PILOT CONE is an image-check consumer  *)
(* and must end in a leaf.  This file requires [FdRowPilot] and is that    *)
(* leaf: nothing may require FdRowMint.                                    *)
(* ===================================================================== *)

(* Require block: FdRowPilot.v's, VERBATIM (durable-notes: trimmed imports
   have OOM'd the build), plus this file's own two lines at the end. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var.

(* the ghost classes first, so the file-system stack's names win over the
   block layer's twins (durable-notes, AND WHERE THAT IMPORT COLLIDES,
   PUT IT EARLY) -- FsInitPin.v's own block, kept verbatim *)
Require Import Xv6Cameras.
Require Import FsState.

Require Import BioDefs.
Require Import DinodeEnc.
Require Import DirView.
Require Import InodeInv.
Require Import FsTree.
Require Import IcacheEscrow.
Require Import FsCrash.
Require Import FsDurSnap.
Require Import FsDurSyscall.
Require Import FsCfgBoot.
Require Import FsDurImg.
Require Import SystemAdequacy.
Require Import FsImgDisk.
Require Import FsImgCheck.
Require Import FsImg.
Require Import FsAbs.
Require Import FsInitPin.       (* [era0_D], [era0_root_row], [img_astep_root] *)

(* ...the machine layer the walk-shaped corollary is stated on... *)
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import UserHeap.
Require Import UsysMemOk.
Require Import UexecRet.

(* ...and the pilot's own vocabulary *)
Require Import ProcGeom.
Require Import FdSlots.
Require Import ConsoleInv.      (* [CONSOLE], [NDEV_max] *)
Require Import PathElems.
Require Import SpecSysMknodAU.  (* [dev_arg], [mknod_parent_elems],
                                   [delta_create] + its row algebra *)
Require Import SpecSysOpenAU.   (* [om_arg] / [om_readable] / [om_writable] *)
Require Import TsoCtx.
Require Import FsFdMirror.
Require Import UexecRetFs.

(* ...the mint's own two: the seed and its boot instantiation, and the
   slot type the park's family is indexed by. *)
Require Import UexecSlot.       (* [uvis] -- the park's family index *)
Require Import FdRowPilot.      (* [era0_seed], [era0_seed_boot] *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE ERA-0 MIRROR VALUE                                            *)
(* ===================================================================== *)

(* The value the era boots at, named once so every statement below indexes
   at the same term.  Its three legs are design section 5's three facts:

     [fdt0]                   allocproc births sixteen closed descriptors
                              ([FdSlots.fdst_map0] at the ghost; see
                              [fd_frags_fdt0] below)
     [abs_view (fss_inodes S)] the founded abstract view -- the snapshot
                              mint founds the era's map AT [fss_inodes S]
                              on the nose ([FsInitPin]'s header, "WHY THE
                              SNAPSHOT STATE IS THE RIGHT PLACE TO STAND")
     [ROOTINO]                userinit's [p->cwd = namei("/")]            *)
Definition era0_u (S : fs_state_rec) : umirror :=
  MkUmirror fdt0 (abs_view (fss_inodes S)) FsImg.ROOTINO.

Lemma era0_u_fdt (S : fs_state_rec) : um_fdt (era0_u S) = fdt0.
Proof. reflexivity. Qed.

Lemma era0_u_av (S : fs_state_rec) :
  um_av (era0_u S) = abs_view (fss_inodes S).
Proof. reflexivity. Qed.

Lemma era0_u_cwd (S : fs_state_rec) : um_cwd (era0_u S) = FsImg.ROOTINO.
Proof. reflexivity. Qed.

(* the seed facts at that value: [FdRowPilot.era0_seed_boot], restated at
   the name so no consumer has to spell the record *)
Lemma era0_u_seed (S : fs_state_rec) :
  snap_ok S era0_D -> era0_seed (era0_u S).
Proof. exact (era0_seed_boot S). Qed.

(* ===================================================================== *)
(*  2.  THE THREE LEGS, EACH AT ITS OWN GHOST                             *)
(*                                                                        *)
(*  Only the fd leg has a producer worth a lemma here; the av leg's is     *)
(*  [FsInitPin]'s era-0 facts (already cited through [era0_u_seed]) and    *)
(*  the cwd leg's is userinit's own call.                                  *)
(* ===================================================================== *)

Section MirrorLegs.
  Context {Σ : gFunctors}.
  Context `{!fdslotG Σ}.

  (* DESIGN SECTION 5 FACT 1, AT ITS GHOST.  [ProcInv]'s slot-open mint
     runs [FdSlots.fd_st_alloc NOFILE] and reads the fragment side with
     [fd_frags_of_closed], i.e. it produces [fd_frags γ (replicate NOFILE
     FdClosed)] -- and [fdt0] IS that list, by definition.  So the mirror's
     fd leg is not a new reading of anything: it is the bundle allocproc
     already builds, at the value it already has.

     THE ONE PLACE THIS COSTS SOMETHING, and it is section 5's ask: the
     mint is closed into [fd_frags_any] on the next line of that same
     proof ([ProcInv.v:2408]) and travels to the userinit park as
     [fd_frags_any] ([SpecAllocproc]'s post, [ParkCap.park_token_park]),
     so the VALUE is gone by the time the mirror wants it.  It cannot be
     recovered: [fd_frags_any] gives the length and nothing else.  It has
     to be CARRIED, which FdSlots' own header already prices as "a change
     of parameter at the holder, not a re-plumb". *)
  Lemma fd_frags_fdt0 (γ : gname) :
    ([∗ list] fd ∈ seq 0 NOFILE, fd_st γ fd FdClosed) -∗ fd_frags γ fdt0.
  Proof.
    iIntros "H". rewrite /fdt0. iApply (fd_frags_of_closed with "H").
  Qed.

  (* ...and the converse direction the ask has to give up: the existential
     bundle pins the LENGTH and nothing about the rows, so no mirror leg
     can be read off it. *)
  Lemma fd_frags_any_len (γ : gname) :
    fd_frags_any γ -∗ ∃ sts : list fdstate,
      fd_frags γ sts ∗ ⌜length sts = NOFILE⌝.
  Proof.
    rewrite /fd_frags_any. iIntros "H". iDestruct "H" as (sts) "H".
    iDestruct (fd_frags_len with "H") as %Hlen.
    iExists sts. by iFrame.
  Qed.

End MirrorLegs.

(* ===================================================================== *)
(*  3.  THE TWO HOMES                                                     *)
(* ===================================================================== *)

Section MirrorHomes.
  Context {Σ : gFunctors}.
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ umirror}.
  Context `{!fdslotG Σ}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ---- 3a.  INIT'S ENTRY PACKAGE ------------------------------------ *)

  (* the user half beside the seed facts.  The half is what the enriched
     arm's right disjunct takes as its deposit; the seed is what forces
     the pilot's chain.  Nothing else is in it -- deliberately: the entry
     package must be constructible at the park, where no fs walk has
     happened yet.

     THE PURE CONJUNCT GOES LAST (durable-notes): a consumer destructures
     the resource first, and stage P5's walk will destructure this one at
     every enriched call. *)
  Definition mirror_entry (γm : gname) (u : umirror) : iProp Σ :=
    (mcur γm u ∗ ⌜era0_seed u⌝)%I.

  Lemma mirror_entry_open (γm : gname) (u : umirror) :
    mirror_entry γm u -∗ mcur γm u ∗ ⌜era0_seed u⌝.
  Proof. rewrite /mirror_entry. iIntros "[H %Hs]". by iFrame. Qed.

  Lemma mirror_entry_intro (γm : gname) (u : umirror) :
    era0_seed u -> mcur γm u -∗ mirror_entry γm u.
  Proof. rewrite /mirror_entry. iIntros (Hs) "H". by iFrame. Qed.

  (* the deposit alone, for a call that does not re-read the seed *)
  Lemma mirror_entry_deposit (γm : gname) (u : umirror) :
    mirror_entry γm u -∗ mcur γm u.
  Proof. rewrite /mirror_entry. iIntros "[$ _]". Qed.

  (* ---- 3b.  THE ENRICHED LOOP'S RESIDUE ------------------------------ *)

  (* THE KERNEL HALF, BESIDE THE REAL GHOSTS, INDEXED AT THEIR READING.

     The point of the shape is that faithfulness is not a conjunct that
     could quietly be false: the fd leg is spelled [fd_frags γfd (um_fdt
     u)] and the av leg [astate Γ (um_av u)], so a residue at [u] IS a
     residue whose mirror agrees with the ghosts, and the only way to move
     the ghosts is to move [u] with them ([mirror_tied_round]).

     [cw] is the process's own cwd inum -- a parameter rather than a
     conjunct against a ghost, because the kernel's [p->cwd] is an INODE
     POINTER and the pointer-to-inum reading lives in the icache layer.
     At the mint it is ROOTINO by userinit's [namei("/")]; keeping it
     abstract here is what lets stage P4 discharge the pointer reading at
     the altitude that owns it, without this file guessing at it. *)
  Definition mirror_tied (γm γfd : gname) Γ (cw : Z) (u : umirror)
      : iProp Σ :=
    (mcur γm u ∗ fd_frags γfd (um_fdt u) ∗ astate Γ (um_av u)
     ∗ ⌜um_cwd u = cw⌝)%I.

  Lemma mirror_tied_open (γm γfd : gname) Γ (cw : Z) (u : umirror) :
    mirror_tied γm γfd Γ cw u -∗
    mcur γm u ∗ fd_frags γfd (um_fdt u) ∗ astate Γ (um_av u)
    ∗ ⌜um_cwd u = cw⌝.
  Proof. rewrite /mirror_tied. iIntros "H". iExact "H". Qed.

  Lemma mirror_tied_close (γm γfd : gname) Γ (cw : Z) (u : umirror) :
    um_cwd u = cw ->
    mcur γm u -∗ fd_frags γfd (um_fdt u) -∗ astate Γ (um_av u) -∗
    mirror_tied γm γfd Γ cw u.
  Proof. rewrite /mirror_tied. iIntros (Hcw) "Hm Hfd Hav". by iFrame. Qed.

  (* THE ANTI-DRIFT RECEIPT.  A deposited half and the residue cannot
     disagree: [mcur] is a two-halves [ghost_var], so the residue's index
     is the deposit's mirror on the nose.  This is what makes the arm's
     [ufs_step] tie meaningful -- the loop steps the mirror the PROCESS
     deposited, not some other one. *)
  Lemma mirror_tied_agree (γm γfd : gname) Γ (cw : Z) (u ud : umirror) :
    mirror_tied γm γfd Γ cw u -∗ mcur γm ud -∗ ⌜ud = u⌝.
  Proof.
    rewrite /mirror_tied. iIntros "(Hm & _ & _ & _) Hd".
    iDestruct (mcur_agree with "Hd Hm") as %->. done.
  Qed.

  (* the two readings a syscall's own proof wants off the residue *)
  Lemma mirror_tied_fdlen (γm γfd : gname) Γ (cw : Z) (u : umirror) :
    mirror_tied γm γfd Γ cw u -∗ ⌜length (um_fdt u) = NOFILE⌝.
  Proof.
    rewrite /mirror_tied. iIntros "(_ & Hfd & _ & _)".
    by iDestruct (fd_frags_len with "Hfd") as %H.
  Qed.

  (* a client-held share of an inum agrees with the MIRROR's row.  This is
     [FsAbs.astate_nview] read through the residue, and it is the move
     that lets stage P4 justify open's observed [anode] -- the arm's
     [um_av u !! i = Some a] conjunct -- from the receipts the AU dispatch
     already hands out. *)
  Lemma mirror_tied_row (γm γfd : gname) Γ (cw : Z) (u : umirror)
      (q : Qp) (i : Z) (a : anode) :
    mirror_tied γm γfd Γ cw u -∗ nview Γ q i a -∗ ⌜um_av u !! i = Some a⌝.
  Proof.
    rewrite /mirror_tied. iIntros "(_ & _ & Hav & _) Hn".
    by iDestruct (astate_nview with "Hav Hn") as %H.
  Qed.

  (* THE LOOP'S ROUND, GHOST-WISE (stage P4's skeleton).  The loop joins
     the residue with the process's deposit, lets the syscall move the
     REAL ghosts -- that move is the caller's wand, and it is exactly what
     the landed AU receipts supply -- and re-indexes both halves at the new
     reading.

     What is deliberately NOT here is the [ufs_step] tie: that is a
     statement about the ROW, established from the dispatcher's post, and
     it is stage P4's to supply.  What IS here is that the ghost move is
     always available and that the two halves cannot drift apart while it
     happens.  The [⌜ud = u⌝] receipt comes out first, so a caller that
     needs it before committing the update can take this lemma's
     [mirror_tied_agree] half instead. *)
  Lemma mirror_tied_round (γm γfd : gname) Γ (cw : Z) (u ud u' : umirror) :
    um_cwd u' = cw ->
    mirror_tied γm γfd Γ cw u -∗
    mcur γm ud -∗
    (fd_frags γfd (um_fdt u) -∗ astate Γ (um_av u) ==∗
       fd_frags γfd (um_fdt u') ∗ astate Γ (um_av u')) -∗
    |==> ⌜ud = u⌝ ∗ mirror_tied γm γfd Γ cw u' ∗ mcur γm u'.
  Proof.
    iIntros (Hcw) "Hres Hd Hmove".
    iDestruct (mirror_tied_agree with "Hres Hd") as %Heq.
    iEval (rewrite /mirror_tied) in "Hres".
    iDestruct "Hres" as "(Hm & Hfd & Hav & _)".
    iMod ("Hmove" with "Hfd Hav") as "[Hfd Hav]".
    iMod (mcur_update γm u ud u' with "Hm Hd") as "[Hk Hu]".
    iModIntro. iSplitR; [iPureIntro; exact Heq |].
    iFrame "Hu". rewrite /mirror_tied. iFrame "Hk Hfd Hav".
    iPureIntro. exact Hcw.
  Qed.

  (* ...and the degenerate round the QUIET rows take: a syscall outside
     [uenr_dom] moves neither leg, so the residue and the deposit come
     back untouched and no update fires. *)
  Lemma mirror_tied_quiet (γm γfd : gname) Γ (cw : Z) (u ud : umirror) :
    mirror_tied γm γfd Γ cw u -∗ mcur γm ud -∗
    ⌜ud = u⌝ ∗ mirror_tied γm γfd Γ cw u ∗ mcur γm u.
  Proof.
    iIntros "Hres Hd".
    iDestruct (mirror_tied_agree with "Hres Hd") as %Heq. subst ud.
    iSplitR; [iPureIntro; reflexivity |].
    iSplitL "Hres"; [iExact "Hres" | iExact "Hd"].
  Qed.

End MirrorHomes.

(* THE TWO HOMES ARE SEALED, exactly as [UexecRetFs] seals [uslot_fs] /
   [uvb_fs] and for the same reason (durable-notes: [iFrame] RESOLVES ITS
   INSTANCES UP TO DELTA).  [mirror_tied]'s body carries [fd_frags], which
   is a [big_sepL] over a sixteen-row list behind two [Definition]s -- a
   fine abstraction and a bad frame target.  Consumers go through the
   openers above, or [rewrite /mirror_tied]. *)
Global Typeclasses Opaque mirror_entry mirror_tied.

(* ===================================================================== *)
(*  4.  THE MINT                                                          *)
(* ===================================================================== *)

Section MirrorMint.
  Context {Σ : gFunctors}.
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ umirror}.
  Context `{!fdslotG Σ}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* ---- 4a.  THE MINT, BARE ------------------------------------------- *)

  (* Allocate the pair at the era-0 value and hand out both halves: the
     kernel's (which the caller parks in the enriched loop's residue) and
     init's entry package.

     The ONLY premise is the era-0 boot state itself -- [snap_ok S era0_D],
     [SystemAdequacy.fsimg_snap_ok]'s own shape, the one equation about the
     initial machine [SystemAdequacy]'s header allows.  That is the
     solo-scoping ruling cashed out: the mint's av-leg faithfulness
     premise is the boot state, with no multi-process story anywhere in
     it. *)
  Theorem mirror_era0_mint (S : fs_state_rec) :
    snap_ok S era0_D ->
    ⊢ |==> ∃ γm : gname, mcur γm (era0_u S) ∗ mirror_entry γm (era0_u S).
  Proof.
    intros HS.
    iMod (mcur_alloc (era0_u S)) as (γm) "[Hk Hu]".
    iModIntro. iExists γm. iFrame "Hk".
    iApply (mirror_entry_intro γm (era0_u S) (era0_u_seed S HS) with "Hu").
  Qed.

  (* ---- 4b.  THE MINT, TIED ------------------------------------------- *)

  (* THE STATEMENT OF RECORD FOR STAGE P3.  The same mint, with the kernel
     half landed in the loop's residue BESIDE the real ghosts rather than
     bare -- i.e. with the mirror's faithfulness established, not merely
     declared, at the boot instant.

     Each premise names its producer:
       [fd_frags γfd fdt0]  -- allocproc's fresh table, at the value
         [ProcInv]'s slot-open mint gives it ([fd_frags_fdt0]); section 5's
         ask is that this value reach the park unclosed.
       [astate Γ (abs_view (fss_inodes S))] -- the founded authority, the
         snapshot mint's own ([FsInitPin] section 6's live corollaries
         stand on exactly this resource at exactly this index, and are
         "consumed AT THE BOOT INSTANT" in the same sense).
       [snap_ok S era0_D] -- the era-0 premise, as in 4a.

     The cwd leg lands at ROOTINO, which is userinit's [namei("/")] read at
     the mirror; the residue's [cw] parameter is what a later era (or a
     process whose cwd has moved) would instantiate differently. *)
  Theorem mirror_era0_mint_tied (γfd : gname) Γ (S : fs_state_rec) :
    snap_ok S era0_D ->
    fd_frags γfd fdt0 -∗
    astate Γ (abs_view (fss_inodes S)) -∗
    |==> ∃ γm : gname,
      mirror_tied γm γfd Γ FsImg.ROOTINO (era0_u S)
      ∗ mirror_entry γm (era0_u S).
  Proof.
    intros HS. iIntros "Hfd Hav".
    iMod (mcur_alloc (era0_u S)) as (γm) "[Hk Hu]".
    iModIntro. iExists γm.
    iSplitR "Hu".
    - rewrite /mirror_tied era0_u_fdt era0_u_av. iFrame "Hk Hfd Hav".
      iPureIntro. exact (era0_u_cwd S).
    - iApply (mirror_entry_intro γm (era0_u S) (era0_u_seed S HS) with "Hu").
  Qed.

  (* ---- 4c.  THE LIVE-VIEW READINGS AT THE MINT ----------------------- *)

  (* [FsInitPin] section 6's route (a), for the mirror's own two facts: a
     consumer holding the founded authority reads them off it and hands it
     straight back (nothing is spent -- they are facts about the map the
     authority carries).

     These are what make the mint's seed CHECKABLE at the boot instant
     rather than only at the pure level: the residue itself witnesses that
     the root is a console-less directory, which is the fact that forces
     init's FIRST open to -1 in [FdRowPilot.pilot_console_pure]. *)
  Lemma astate_era0_console_miss Γ (S : fs_state_rec) :
    snap_ok S era0_D ->
    astate Γ (abs_view (fss_inodes S)) -∗
      astate Γ (abs_view (fss_inodes S))
      ∗ ⌜um_resolve (era0_u S) console_str = None⌝.
  Proof.
    intros HS. iIntros "Hst". iFrame "Hst". iPureIntro.
    apply era0_resolve_console_miss. exact (era0_u_seed S HS).
  Qed.

  (* ...and the same fact read off the RESIDUE, which is the form stage P4
     applies (the loop holds the residue, not a bare authority). *)
  Lemma mirror_tied_era0_console_miss (γm γfd : gname) Γ (cw : Z)
      (S : fs_state_rec) :
    snap_ok S era0_D ->
    mirror_tied γm γfd Γ cw (era0_u S) -∗
      mirror_tied γm γfd Γ cw (era0_u S)
      ∗ ⌜um_resolve (era0_u S) console_str = None⌝.
  Proof.
    intros HS. iIntros "Hres". iSplitL "Hres"; [iExact "Hres" |].
    iPureIntro. apply era0_resolve_console_miss. exact (era0_u_seed S HS).
  Qed.

End MirrorMint.

(* ===================================================================== *)
(*  5.  THE PARK ARM, IN PARALLEL FORM                                    *)
(*                                                                        *)
(*  The mint's landing site is [ProofUserinit]'s MINT SITE #1 -- the       *)
(*  [iAssert (∀ W : uvis, uslot W)] that feeds [ParkCap.park_token_park].  *)
(*  That file is upstream's and is not touched here; what this section     *)
(*  supplies is the parallel form of the enriched arm, so the diff below   *)
(*  is a splice of proven lemmas rather than a new proof obligation.       *)
(* ===================================================================== *)

Section MirrorPark.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ umirror}.
  Context `{!fdslotG Σ}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* THE ARM IS CONSERVATIVE AT THE PARK.  Whatever the park is handed
     today -- the generic family, or sync's/echo's through
     [UexecCond.cond_entry_slot] -- lifts to the enriched family for free,
     by [UexecRetFs.uslot_uslot_fs].  So the enriched mint arm never has to
     PROVE anything new about the child in order to park it: the
     enrichment is opt-in per call, and a child that never takes the right
     disjunct is the child upstream already parks.

     This is the receipt that prices design section 6 item 3's diff: the
     one line that changes type at the park site is discharged by this
     lemma. *)
  Lemma mirror_park_family_of_gen (γm : gname) :
    (∀ W : uvis, uslot W) -∗ (∀ W : uvis, uslot_fs γm W).
  Proof.
    iIntros "Hfam" (W).
    iSpecialize ("Hfam" $! W).
    iApply (uslot_uslot_fs with "Hfam").
  Qed.

  (* ...and the [□] form, which is what the site actually has: userinit's
     [Hjslot] is built from the PERSISTENT [UG.uexec_wp_gen] through
     [UexecCond.cond_entry_slot], so the family there is boxable as it
     stands.  The boxed form is what lets stage P5's enriched walk take
     the family at ITS key while the park keeps one for the generic keys. *)
  Lemma mirror_park_family_of_gen_box (γm : gname) :
    □ (∀ W : uvis, uslot W) -∗ □ (∀ W : uvis, uslot_fs γm W).
  Proof.
    iIntros "#Hfam !>" (W).
    iApply (mirror_park_family_of_gen γm with "Hfam").
  Qed.

  (* THE WHOLE ARM, as one sentence: from the era-0 ghosts and whatever
     family the park would have received, the enriched park receives the
     enriched family, the loop receives the tied residue, and init receives
     its entry package.  This is design section 6 item 3, proven. *)
  Theorem mirror_era0_park_arm (γfd : gname) Γ (S : fs_state_rec) :
    snap_ok S era0_D ->
    (∀ W : uvis, uslot W) -∗
    fd_frags γfd fdt0 -∗
    astate Γ (abs_view (fss_inodes S)) -∗
    |==> ∃ γm : gname,
      (∀ W : uvis, uslot_fs γm W)
      ∗ mirror_tied γm γfd Γ FsImg.ROOTINO (era0_u S)
      ∗ mirror_entry γm (era0_u S).
  Proof.
    intros HS. iIntros "Hfam Hfd Hav".
    iMod (mirror_era0_mint_tied γfd Γ S HS with "Hfd Hav")
      as (γm) "[Hres Hentry]".
    iModIntro. iExists γm.
    iSplitR "Hres Hentry";
      [iApply (mirror_park_family_of_gen γm with "Hfam") |].
    iSplitL "Hres"; [iExact "Hres" | iExact "Hentry"].
  Qed.

End MirrorPark.

(* ===================================================================== *)
(*  6.  THE DIFF-SHAPED ASK, RE-MEASURED AGAINST THE CURRENT TEXT         *)
(*                                                                        *)
(*  (2026-08-31, PILOT-CONVERGENCE lane, after upstream's [fd_frags_any]   *)
(*  retirement -- commits c83604c8b / 8091053d1 / 34c2d83f2 / 544c08005 /  *)
(*  e185c293a.)  COMPILED, not proposed: the (2a) splice below was applied *)
(*  to a scratch twin of ProofUserinit.v and built GREEN on the mirror,    *)
(*  and (2b)'s two obstacles are the twin's own error messages.           *)
(* ===================================================================== *)
(*                                                                        *)
(*  UPSTREAM FILE: iris/ProofUserinit.v, MINT SITE #1.  THE SITE TODAY,    *)
(*  verbatim (ProofUserinit.v:773-780 -- it moved under the ctx threading  *)
(*  and the retirement, and the [fdt0] argument is NEW):                   *)
(*                                                                        *)
(*    iAssert (forall W : uvis, uslot W)%I as "Hjslot".                    *)
(*    { iPoseProof UG.uexec_wp_gen as "#Hgen".                             *)
(*      iIntros (W). iApply (UexecCond.cond_entry_slot W with "Hgen"). }   *)
(*    iMod (park_token_park N rest (MkUstate (upd_cwd V ipv) M) fdt0       *)
(*            Hwf Hrest with [Htoken Htext Hwire Htramp Hmk Hstack Henv    *)
(*            Hown Hfrag Hjslot, and the bracketed five]) as [Hpctx].      *)
(*                                                                        *)
(*  THE ASK SPLITS IN TWO, and the split is the news.  (2a) is ONE line    *)
(*  and it compiles; (2b) is not three lines and is not independent of     *)
(*  design section 6 item 1.                                               *)
(*                                                                        *)
(*  ---- (2a) THE MINT.  COMPILED (scratch twin, EC2-green). ----          *)
(*                                                                        *)
(*    iAssert (forall W : uvis, uslot W)%I as "Hjslot".                    *)
(*    { iPoseProof UG.uexec_wp_gen as "#Hgen".                             *)
(*      iIntros (W). iApply (UexecCond.cond_entry_slot W with "Hgen"). }   *)
(*    iMod (FdRowMint.mirror_era0_mint Sfs Hsnap)                          *)
(*      as (gm) "[Hkhalf Hentry]".                                         *)
(*    iMod (park_token_park N rest (MkUstate (upd_cwd V ipv) M) fdt0       *)
(*            Hwf Hrest with [the same eleven, unchanged]) as "Hpctx".     *)
(*                                                                        *)
(*  ONE inserted [iMod], nothing deleted, THE PARK CALL UNTOUCHED, and the *)
(*  ~270 remaining lines of the walk unaffected -- the two minted halves   *)
(*  sit unused in the affine context.  What that one line still costs, all *)
(*  of it OUTSIDE the site:                                                *)
(*                                                                        *)
(*   (i)  THE GHOST CLASS.  [ghost_varG Sigma umirror] is not in           *)
(*        ProofUserinit's context (riscvGS / xv6G / bioslotG / fileG /     *)
(*        fdslotG / irefslotG / pavG) and has to be added there and in the *)
(*        adequacy [Sigma].  The mint's other classes are FREE: [fsTopG]   *)
(*        and [fsLinkG] are MEMBERS of [Xv6G.xv6G] (Xv6G.v:81 and its      *)
(*        neighbour), and [fdslotG] is already a binder.                   *)
(*                                                                        *)
(*   (ii) THE PURE PREMISE (input (C)) REACHES THE CONTRACT, not just the  *)
(*        proof.  [snap_ok S era0_D] is nowhere in ProofUserinit -- the    *)
(*        file has no fs-abstraction vocabulary at all -- so it arrives as *)
(*        a parameter, and that WIDENS [wp_userinit_sconf]'s type, which   *)
(*        is a field of the Module Type [SpecUserinit.USERINIT]            *)
(*        ([wp_userinit_sconf_body], SpecUserinit.v:135,272-281).  The     *)
(*        twin measured this exactly: with the ascription in place the     *)
(*        build stops at -- Signature components for field                 *)
(*        wp_userinit_sconf do not match -- and with the ascription        *)
(*        dropped the file is green.                                       *)
(*        So the ask reaches the userinit CONTRACT and its callers         *)
(*        (LinkUserinit, the boot chain) -- cheap, but not local.          *)
(*                                                                        *)
(*   (iii) THE CONE.  [Require Import FdRowMint] inside ProofUserinit is a *)
(*        CYCLE: FdRowMint -> FdRowPilot -> FsImgCheck -> SystemAdequacy   *)
(*        -> BootChain -> LinkMain -> LinkUserinit -> ProofUserinit.  The  *)
(*        mint's statements have to be SPLIT into a file below the boot    *)
(*        chain first.  The split is clean: sections 1-5 need the image    *)
(*        check for exactly three things ([era0_u_seed] through            *)
(*        [FdRowPilot.era0_seed_boot], and the two console-miss            *)
(*        corollaries); the homes, the mint and the park arm do not.  The  *)
(*        twin compiles only because a scratch file may sit above the      *)
(*        whole tree.                                                      *)
(*                                                                        *)
(*  ---- (2b) THE PARK AT THE ENRICHED FAMILY.  NOT THREE LINES. ----      *)
(*                                                                        *)
(*  The previous version of this section said the park's family argument   *)
(*  keeps its name and position and changes only its type.  Measured, that *)
(*  is the expensive half, and it is not independent of the arm ruling:    *)
(*                                                                        *)
(*   (i)  THE FAMILY'S TYPE IS INSIDE A FIXPOINT.  Splicing               *)
(*        [iDestruct (mirror_park_family_of_gen gm with "Hjslot")] and     *)
(*        passing the result gets, verbatim (twin 2):                      *)
(*          iSpecialize: cannot instantiate                                *)
(*            ((forall W : uvis, uslot W) -* park_child ... ==* ...)       *)
(*          with (forall W : uvis, UexecRetFs.uslot_fs gm W)               *)
(*        and [park_token_park] cannot merely be re-typed: [uslot          *)
(*        (uvis_of U' sts)] sits inside [ParkCap.park_pkg], i.e. inside    *)
(*        the [park_token] FIXPOINT (ParkCap.v:134).  Parking an enriched  *)
(*        family is a generalisation of the park CHANNEL over the slot     *)
(*        family -- the same shape upstream ask (4) asks of the ENGINE,    *)
(*        and worth asking for in the same breath.                         *)
(*                                                                        *)
(*   (ii) AND IT WOULD BE PREMATURE.  What the resume hands the loop is    *)
(*        what the LOOP must consume; while upstream's loop is the plain   *)
(*        one, the honest park is the plain family, and the process lifts  *)
(*        at its own walk through the proven [uslot_uslot_fs].  The park's *)
(*        type change becomes right exactly when the enriched arm (design  *)
(*        section 6 item 1) and the enriched loop (stage P4) land.         *)
(*                                                                        *)
(*   (iii) THE TIED MINT CANNOT FIRE HERE AT ALL, and the reason is        *)
(*        LINEARITY rather than a missing hypothesis.  [mirror_tied] holds *)
(*        [fd_frags gfd (um_fdt u)], and at era 0 that IS                  *)
(*        [fd_frags (pv_fdg V) fdt0] -- the very resource the site hands   *)
(*        to [park_token_park].  One bundle, two would-be owners: the park *)
(*        package captures it in its resume closer (ParkCap.v:284-299) and *)
(*        holds it across the whole parked period.  Input (B), the founded *)
(*        [astate], is absent too (ProofUserinit names no [astate]         *)
(*        anywhere), but the linearity is the fatal one -- no plumbing     *)
(*        gives the residue a bundle the park is already holding.  THE FIX *)
(*        IS NOT PLUMBING: the tie belongs where the fragments actually    *)
(*        are during a trap, beside [UsertrapRes.ut_own] inside the loop's *)
(*        excursion -- stage P4's territory, which is where               *)
(*        [mirror_tied_round] was already aimed.  THE PARK MINTS THE       *)
(*        GHOST; THE LOOP ESTABLISHES THE TIE.                             *)
(*                                                                        *)
(*  ---- WHAT UPSTREAM'S RETIREMENT ALREADY ANSWERED ----                  *)
(*                                                                        *)
(*  Input (A) is DONE, and answered BY BUILDING rather than by promising.  *)
(*  [ProcInv]'s slot-open mint now concludes at the value, [SpecAllocproc] *)
(*  carries it through its post ([fd_frags (pv_fdg (us_V U)) fdt0],        *)
(*  SpecAllocproc.v:195), [ParkCap.park_token_park] takes a NAMED table    *)
(*  (ParkCap.v:224 and 247) and [ProofUserinit] parks at [fdt0]            *)
(*  (ProofUserinit.v:776).  A fresh process's descriptor table is          *)
(*  therefore stateable end to end -- exactly what [fd_frags_any_len]      *)
(*  above records as unrecoverable from the existential form.  The AS-     *)
(*  LANDED FINDING in the worklist -- allocproc's fresh table is minted at *)
(*  its VALUE and existentially closed one line later -- is CLOSED.        *)
(* ===================================================================== *)
