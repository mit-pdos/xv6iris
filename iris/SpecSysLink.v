(* SpecSysLink.v -- the public interface of sys_link(), stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

     uint64 sys_link(void) {
       char name[DIRSIZ], new[MAXPATH], old[MAXPATH];
       struct inode *dp, *ip;

       if (argstr(0, old, MAXPATH) < 0 || argstr(1, new, MAXPATH) < 0)
         return -1;

       begin_op();
       if ((ip = namei(old)) == 0) { end_op(); return -1; }

       ilock(ip);
       if (ip->type == T_DIR) { iunlockput(ip); end_op(); return -1; }
       if (ip->nlink >= NLINK_MAX) { iunlockput(ip); end_op(); return -1; }

       ip->nlink++;
       iupdate(ip);
       iunlock(ip);

       if ((dp = nameiparent(new, name)) == 0) goto bad;
       ilock(dp);
       // dp may have been unlinked while we resolved it
       if (dp->nlink == 0) { iunlockput(dp); goto bad; }
       if (dp->dev != ip->dev || dirlink(dp, name, ip->inum) < 0) {
         iunlockput(dp); goto bad;
       }
       iunlockput(dp);
       iput(ip);
       end_op();
       return 0;

      bad:
       ilock(ip);
       ip->nlink--;
       iupdate(ip);
       iunlockput(ip);
       end_op();
       return -1;
     }

   @ KernelSyms.sys_link, 292 bytes / 101 instructions (CodeSysLink.v).
   A THIRTY-EIGHT slot frame ([c.addi16sp sp,-304] at +0x00), carved:

     slot  1  (sp+296)  ra
     slot  2  (sp+288)  s0, the frame pointer (= the ENTRY sp)
     slot  3  (sp+280)  s1 = ip     -- saved LATE, at +0x30
     slot  4  (sp+272)  s2 = dp     -- saved LATER STILL, at +0x5c
     slots 5..6         [char name[DIRSIZ]] -- [addi a1,s0,-48]
     slots 7..22        [char new[MAXPATH]] -- [addi a1,s0,-176]
     slots 23..38       [char old[MAXPATH]] -- [addi a1,s0,-304]

   THE TWO REGISTER SAVES ARE SHRINK-WRAPPED.  [c.sdsp s1] runs only after
   BOTH argstr calls succeed and [c.sdsp s2] only after the type and
   NLINK_MAX guards pass, and each exit restores exactly what its own path
   saved -- so the two argstr-failure arms neither save nor restore either
   register, which is sound because neither is written on those paths.
   Nothing about the three buffers reaches this contract: they are carved
   out of [stack_own] with [StackBytes.slotsn_bytes_own].

   ==== WHAT THIS CONTRACT IS ABOUT =====================================

   sys_link is the first SYSCALL-level consumer of the CREDITED iupdate
   pair ([SpecIupdate.wp_iupdate_link] / [wp_iupdate_unlink]) and of the
   kernel's NLINK_MAX guard arm, so its walk is where the whole link
   contract layer is exercised end to end.  Two facts about that, because
   they are what the walk is:

   * THE LINK FRAGMENT IS MINTED AND SETTLED INSIDE THIS FUNCTION.  The
     [ip->nlink++; iupdate(ip)] at +0x5e..+0x66 mints one
     [FsStateLink.link_tok] at [ip] against the count that pays for it; on
     the success path the [dirlink] at +0x9c lets the caller DEPOSIT it into
     the parent's [IcacheEscrow.dlinks], caller-side --
     design/fs-icache.md 20.18 ruling 1 keeps every link resource OUT of
     [SpecDirlink]; on every route to [bad:] the [ip->nlink--; iupdate(ip)]
     at +0xfa..+0x106 CONSUMES it back.  Nothing else crosses this
     interface in either direction.
   * THE ORPHAN GUARD IS WHAT MAKES THE DEPOSIT LEGAL.  The [lh a5,74(s2)]
     / [c.beqz] at +0x84..+0x88 -- create's re-check, given to sys_link at
     f60ff58 -- refuses to [dirlink] into a parent a concurrent rmdir has
     orphaned, which would strand the fragment above in a directory whose
     [itrunc] discards records without dropping counts.  Its arm is ARM E2,
     a plain [iunlockput(dp); goto bad;], so nothing about it reaches this
     contract except that the [-1] disjunct now has one more way to happen.
   * THE NLINK_MAX GUARD IS WHAT MAKES THE MINT LEGAL.  [wp_iupdate_link]'s premise
     [di_nlink dn0 <> mword_of_int 32767] is exactly the [beq a4,a5] at
     +0x58 falling through; the [lui a4,0x8 / addi a4,a4,-1] pair at
     +0x54/+0x56 is 32767,
     and the test is [==] rather than [>=] because [nlink] is a signed
     short and NLINK_MAX is SHRT_MAX.  The SIGNED/UNSIGNED gap the twelfth
     stop recorded is closed by [InodeRegion]'s (L4) range clause, which is
     where the increment premise is discharged.

   ==== THE REFERENCE LEDGER CLOSES AT THREE ON EVERY ARM ===============

   [iref_slots 3] goes in and comes back out unchanged, and three -- one
   more than sys_chdir's two -- is forced by the SECOND resolve: when
   nameiparent runs, [ip] is already held.

   * namei takes two units and hands ONE back on success (the second pays
     for the reference it returns), so the walk's peak is [ip] plus the
     walker's own two;
   * nameiparent does the same for [dp];
   * every arm releases what it made -- [iunlockput(ip)] on the type and
     NLINK_MAX arms and at [bad:], [iunlockput(dp)] + [iput(ip)] on the
     success arm -- and the two argstr arms make no reference at all.

   ==== THE LOG LEDGER IS THE SET FORM, AND IT HAS TO BE ================

   begin_op mints [LogInv.log_op g MAXOPBLOCKS] = ten units and end_op
   retires whatever is left, so nothing log-shaped crosses this interface.
   sys_link runs TWO unbounded-depth walks inside one transaction, so the
   COUNTED namei/nameiparent contracts are hopeless here for sys_chdir's
   reason squared: [(L + 1) * iput_units] demands twelve of the ten at a
   three-component path, twice over.  The SET form prices each walk at
   [SpecNamex.walk_need L <= 4] and spends at most one.

   Note that the two [argstr] calls run BEFORE [begin_op] -- unlike
   sys_chdir, where the string fetch is inside the transaction -- so the
   two argstr-failure arms carry no log resource at all.

   ==== WHAT ITS CALLER MUST HOLD ======================================

   [eb = true] is namei's premise, inherited verbatim.  The
   [trap_csrs_ext] / [cpu_claim_ext] complement is threaded anyway,
   uniformly with begin_op / iupdate / iput / iunlockput / end_op, and is
   [emp] there.

   THE CROSSING IS THE LITERAL [true]: this function sleeps in every one of
   its eleven distinct callees, so it may return on a hart other than the
   one it was called on.

   THE BITMAP IS AN INVARIANT ([BitmapInv.bitmap_inv], inside [fs_ready]):
   [dirlink]'s writei can ALLOCATE and the two walks' iunlockputs can FREE,
   and the contract says nothing about either.

   DETERMINISM: none is claimed, and none is available.  Which of the
   eight arms runs is a function of the FILE SYSTEM and of the user's two
   strings, and no caller of this contract knows any of that.  The
   postcondition is the honest disjunction on the returned a0. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import SpecPrintk.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRefDefs.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecDirlink.    (* [ic_sleeplocks], [ireg_blocks_ok] *)
(* THE APPLICATION'S SIDE (round E2, lane E2-L).  [FsTree] for the entry
   name, [FsBytesGamma] for the live Gamma the commits are indexed by,
   [AppInv] for [app_step]/[appE] and the parked license the [_unit]s pay
   with, [SpecSysUnlinkAU] for [utgt_commit_at] -- link's failure arm's
   count-down IS unlink's target step ([FsAbsDelta.delta_link_untgt] is
   [delta_unl_tgt] on the nose), so it is REUSED and not cloned -- and
   [FsAbsDelta] (which [SpecSysUnlinkAU] re-exports) for the three deltas.
   [FsAbsDefs] LAST, by FsAbs's own rule. *)
Require Import FsTree.          (* [fname]                                  *)
Require Import FsBytesGamma.    (* [fs_gamma_L], [fs_view_names], [gamma_top] *)
Require Import AppInv.          (* [app_step], [appN]/[appE], [app_step_acc] *)
Require Import SpecSysUnlinkAU. (* [utgt_commit_at] + [FsAbsDelta] re-export *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbsDefs.       (* LAST (FsAbs's own rule)                  *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* sys_link's own frame is 304 bytes -- THIRTY-EIGHT slots
   ([c.addi16sp sp,-304] at +0x00).  Its deepest callee is namei (106);
   nameiparent wants 104, dirlink 100, iunlockput 64, argstr 60, iput 60,
   end_op 58, ilock 44, iupdate 44, begin_op 26, iunlock 26. *)
Notation K_sys_link := (154%nat) (only parsing).
(* THE REFERENCE ALLOWANCE.  Three, and the third one is nameiparent's:
   see the header's reference ledger. *)
Definition sys_link_slots : nat := 3%nat.

(* sys_link's result, as the honest disjunction on a0.  BOTH values come
   out of the same [c.mv a0,a5] at +0x11a, whose a5 each arm set to its own
   literal: 0 at +0xb4 on the success arm, -1 at every failure. *)
Definition sys_link_ret (r : mword 64) : Prop :=
  r = (mword_of_int (-1) : mword 64) \/ r = (zero_reg : mword 64).

(* ===================================================================== *)
(*  THE APPLICATION'S SIDE OF sys_link (round E2, lane E2-L)              *)
(* ===================================================================== *)

(* Owner ruling Q-c (2026-09-05): "strengthen in place -- we have a single
   kernel proof".  There is no parallel AU twin of sys_link; this contract
   IS the one the dispatcher runs, so it grows the commits rather than
   being copied beside one (app-round-e2.md section 4's recommendation, and
   the R10 waiver that goes with it).

   THE DELTA IS THREE INSTANTS, and that is a machine fact -- the same
   stance [SpecSysUnlinkAU]'s header takes for unlink's two:

     instant 1 -- THE TARGET'S COUNT ([ip->nlink++; iupdate(ip)] at
        +0x5e..+0x66, BEFORE the entry exists).  [FsAbsDelta.delta_link_tgt]
        at the row the machine reads under [ip->lock].  Between it and
        instant 2 the [iunlock(ip)] at +0x6c really releases the record and
        a concurrent observer sees the raised count with no name for it.
     instant 2 -- THE PARENT'S ENTRY ([dirlink(dp, name, ip->inum)] at
        +0x9c).  [delta_link_ent]: the parent gains [nm |-> t]; link is for
        files and devices only, so no count moves.
     instant 3 -- THE UNDO, on every route to [bad:] ([ip->nlink--;
        iupdate(ip)] at +0xfa..+0x106).  [delta_link_untgt] IS
        [delta_unl_tgt], so ITS COMMIT IS [SpecSysUnlinkAU.utgt_commit_at],
        REUSED VERBATIM rather than cloned.

   [FsAbsDelta.delta_link_split] is the machine-checked composition and
   [delta_link_untgt_tgt] is the fact that instant 3 restores the pre-view
   exactly, in BOTH arms of the target row.

   THE TARGET'S ROW IS A PARAMETER, not a lookup (lane E2-D's one
   deviation): sys_link has NO [ip->nlink == 0] guard -- ProofSysLink.v's
   "THE IIIc WALL" records that the count fact is genuinely unavailable
   there -- so the target may be an unlinked-but-open file with no row at
   all, and the bump RESURRECTS it.  [arow_at] is the side condition, one
   insert either way. *)

(* THE TARGET IS NEVER A DIRECTORY: ARM C's [ip->type == T_DIR] test at
   +0x4c refused it before the bump, which is also why [delta_link_ent]
   moves no count ([FsAbsDelta.acre_bump]'s reading of a non-dir child). *)
Definition link_tgt_ok (c : absnode) : Prop :=
  match c with ADir _ => False | _ => True end.

Lemma link_tgt_ok_not_dir (n : fs_node) :
  fn_is_dir n = false -> link_tgt_ok (an_node (abs_row n)).
Proof.
  intros Hd. rewrite /link_tgt_ok.
  destruct (an_node (abs_row n)) as [bs | ents | ma mi] eqn:He;
    [exact I | | exact I].
  exfalso. destruct (abs_row_dir_inv n ents He) as [Hc _].
  rewrite Hd in Hc. discriminate.
Qed.

Section SysLinkAbs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  The two NEW commits (the third is unlink's, reused)                *)
  (* ------------------------------------------------------------------ *)

  (* INSTANT 1 -- the target row, two-phase at the raw map
     ([FsAbsCreateFire.acre_commit_at_gen]'s mold: phase 1 observes the
     pre-state, phase 2 witnesses the delta applied and pays the receipt).
     [is_Some (I !! t)] is what lets the generic discharger pay the step
     off the parked license ([AppInv.app_step_acc]) although the VIEW may
     have no row at [t]: the target's inum is a region row, and the fire
     reads that off [ghost_map_lookup] at the instant. *)
  Definition ltgt_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> anode -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (t : Z) (a : anode),
       ⌜arow_at (abs_view I) t a⌝ -∗
       ⌜link_tgt_ok (an_node a)⌝ -∗
       ⌜is_Some (I !! t)⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         (* THE CALLER'S STEP (app-instances.md section 7): its claim about
            the pre-view survives the delta, at the RAW insert the mover
            performs ([AppInv.app_step]; the delta is its reading) *)
         app_step t I (delta_link_tgt t a (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_link_tgt t a (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗ Φ (abs_view I) t a))%I.

  (* INSTANT 2 -- the parent row, [uent_commit_at]'s shape at
     [delta_link_ent].  The parent is a LIVE directory (the orphan guard at
     +0x84 refused an [nlink = 0] parent, so the row is in the view) and
     the name is ABSENT ([dirlink]'s own [dirlookup] guard). *)
  Definition lent_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d t : Z) (nm : fname)
       (ents : gmap fname Z) (nl : nat),
       ⌜abs_view I !! d = Some (MkAnode (ADir ents) nl)⌝ -∗
       ⌜ents !! nm = None⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         app_step d I (delta_link_ent d nm t (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_link_ent d nm t (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗ Φ (abs_view I) d nm t))%I.

  (* ------------------------------------------------------------------ *)
  (*  Satisfiability: the [_unit] dischargers                            *)
  (* ------------------------------------------------------------------ *)

  Lemma link_appN_appE : ↑appN ⊆ appE.
  Proof. rewrite /appE. done. Qed.

  Lemma ltgt_commit_at_unit (γfs : fs_names) E :
    ↑appN ⊆ E ->
    app_inv γfs -∗ ltgt_commit_at (fs_gamma_L γfs) E (fun _ _ _ => True%I).
  Proof.
    iIntros (HE) "#Hai". rewrite /ltgt_commit_at.
    iIntros (I t a) "%Hrow %Hok %Hsome Ha".
    iMod (app_step_acc E γfs t I _ HE Hsome with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma lent_commit_at_unit (γfs : fs_names) E :
    ↑appN ⊆ E ->
    app_inv γfs -∗ lent_commit_at (fs_gamma_L γfs) E (fun _ _ _ _ => True%I).
  Proof.
    iIntros (HE) "#Hai". rewrite /lent_commit_at.
    iIntros (I d t nm ents nl) "%Hd %Hnm Ha".
    iMod (app_step_acc E γfs d I _ HE
            (abs_view_lookup_is_Some I d _ Hd) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The bundle, and the three receipts                                 *)
  (* ------------------------------------------------------------------ *)

  Definition link_commits Γ
      (Ftgt : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Funt : pfam Σ (aview -> Z -> iProp Σ)) : iProp Σ :=
    (pf_at (ltgt_commit_at Γ appE) Ftgt ∗ pf_at (lent_commit_at Γ appE) Fent
     ∗ pf_at (utgt_commit_at Γ appE) Funt)%I.

  (* the whole bundle at the trivial families -- what the dispatcher hands
     down ([FsAbsInvFire.fsabs_link_pre] is this beside [app_inv]) *)
  Lemma link_commits_unit (γfs : fs_names) :
    app_inv γfs -∗
    link_commits (fs_gamma_L γfs) (pfam_triv (fun _ _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)) (pfam_triv (fun _ _ => True%I)).
  Proof.
    iIntros "#Hai". rewrite /link_commits.
    iSplitR.
    { iApply pf_at_triv.
      iApply (ltgt_commit_at_unit γfs appE link_appN_appE with "Hai"). }
    iSplitR.
    { iApply pf_at_triv.
      iApply (lent_commit_at_unit γfs appE link_appN_appE with "Hai"). }
    iApply pf_at_triv.
    iApply (utgt_commit_at_unit γfs appE link_appN_appE with "Hai").
  Qed.

  (* each receipt with its instant's pure facts restated beside the
     caller's own [Φ] *)
  Definition ltgt_fired (Ftgt : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (t : Z) : iProp Σ :=
    (∃ (av : aview) (a : anode),
       ⌜arow_at av t a⌝ ∗ ⌜link_tgt_ok (an_node a)⌝ ∗ Ftgt.(pf_recv) av t a)%I.

  Definition lent_fired (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (d : Z) (nm : fname) (t : Z) : iProp Σ :=
    (∃ (av : aview) (ents : gmap fname Z) (nl : nat),
       ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗ ⌜ents !! nm = None⌝
       ∗ Fent.(pf_recv) av d nm t)%I.

  (* THE UNDO'S ROW IS AN EXISTENTIAL, and that is a machine fact too: the
     [iunlock(ip)] at +0x6c releases the record, so the one the [bad:] arm
     re-[ilock]s at +0xf6 need not be the one instant 1 bumped -- another
     hart may have linked or unlinked it in between.  What the arm DOES
     know is that the row is present at a live count (the walk's own
     [FsStateLink.link_tok] pays for one link: [IregLinkNz.ireg_tok_nz]),
     which is exactly [utgt_commit_at]'s premise. *)
  Definition luntgt_fired (Funt : pfam Σ (aview -> Z -> iProp Σ))
      (t : Z) : iProp Σ :=
    (∃ (av : aview) (a : anode), ⌜av !! t = Some a⌝ ∗ Funt.(pf_recv) av t)%I.

  (* ------------------------------------------------------------------ *)
  (*  THE POST ARMS, keyed on the returned a0                            *)
  (* ------------------------------------------------------------------ *)

  (* ret 0  -- ARM G: the target's count went up and the parent gained the
                name.  [t] is the target's inum, [d] the parent's, [nm] the
                new path's last element.  The undo commit comes home.
     ret -1 -- the honest fold of the landed blanket disjunction:
                (i)  NOTHING fs-visible happened: the whole bundle back --
                     ARM A (either argstr), ARM B (namei(old) missed),
                     ARM C (the target is a directory), ARM D (NLINK_MAX);
                (ii) the DO-THEN-UNDO PAIR -- every route to [bad:]: ARM E
                     (nameiparent missed), ARM E2 (the orphan guard), ARM F
                     (dirlink refused).  Both target receipts, the parent
                     leg's commit back unspent. *)
  Definition link_arms Γ
      (Ftgt : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Funt : pfam Σ (aview -> Z -> iProp Σ))
      (r : mword 64) : iProp Σ :=
    ((⌜r = (zero_reg : mword 64)⌝ ∗
        ∃ (t d : Z) (nm : fname),
          ltgt_fired Ftgt t ∗ lent_fired Fent d nm t
          ∗ pf_at (utgt_commit_at Γ appE) Funt)
     ∨ (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
          (link_commits Γ Ftgt Fent Funt
           ∨ (∃ t : Z, ltgt_fired Ftgt t ∗ luntgt_fired Funt t
                       ∗ pf_at (lent_commit_at Γ appE) Fent))))%I.

  (* ...and the three introduction forms the walk's ten exits use *)
  Lemma link_arms_none Γ Ftgt Fent Funt (r : mword 64) :
    r = (mword_of_int (-1) : mword 64) ->
    link_commits Γ Ftgt Fent Funt -∗ link_arms Γ Ftgt Fent Funt r.
  Proof.
    intros ->. rewrite /link_arms. iIntros "H". iRight.
    iSplitR; [done |]. by iLeft.
  Qed.

  Lemma link_arms_undone Γ Ftgt Fent Funt (r : mword 64) (t : Z) :
    r = (mword_of_int (-1) : mword 64) ->
    ltgt_fired Ftgt t -∗ luntgt_fired Funt t -∗
    pf_at (lent_commit_at Γ appE) Fent -∗ link_arms Γ Ftgt Fent Funt r.
  Proof.
    intros ->. rewrite /link_arms. iIntros "H1 H2 H3". iRight.
    iSplitR; [done |]. iRight. iExists t. iFrame "H1 H2 H3".
  Qed.

  Lemma link_arms_ok Γ Ftgt Fent Funt (r : mword 64)
      (t d : Z) (nm : fname) :
    r = (zero_reg : mword 64) ->
    ltgt_fired Ftgt t -∗ lent_fired Fent d nm t -∗
    pf_at (utgt_commit_at Γ appE) Funt -∗ link_arms Γ Ftgt Fent Funt r.
  Proof.
    intros ->. rewrite /link_arms. iIntros "H1 H2 H3". iLeft.
    iSplitR; [done |]. iExists t, d, nm. iFrame "H1 H2 H3".
  Qed.

  (* the landed blanket [sys_link_ret] is IMPLIED by the arms, which is
     what lets the dispatcher keep reading the old fact *)
  Lemma link_arms_ret Γ Ftgt Fent Funt (r : mword 64) :
    link_arms Γ Ftgt Fent Funt r -∗ ⌜sys_link_ret r⌝.
  Proof.
    rewrite /link_arms /sys_link_ret.
    iIntros "[[-> _] | [-> _]]"; iPureIntro; [by right | by left].
  Qed.

End SysLinkAbs.

(* the arms are a disjunction with existentials inside: sealed, as
   [SpecSysMkdir.mkdir_arms] is, so an [iFrame] at syscall altitude does
   not search through them *)
Global Typeclasses Opaque link_arms.

Definition wp_sys_link_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γf : gname)      (* ftable, kalloc, printk   *)
    (gs : list gname) (j : nat) (gl : gname)     (* the running process      *)
   (* disk fabric + lock *)
    (pd pav pu : mword 64)
    (dqb dqs dqbs : dfrac)
    (v0 v1 : mword 64)                        (* syscall arguments 0 and 1  *)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (* ---- the application's four families (round E2, lane E2-L) ---- *)
    (Ftgt : pfam Σ (aview -> Z -> anode -> iProp Σ))
    (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
    (Funt : pfam Σ (aview -> Z -> iProp Σ)) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_link in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_link <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  (* ---- the block-layer geometry ---- *)
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (* mkfs's [ushort] geometry, create's premise verbatim and for the same
     reason: it is what makes the [lw a2,4(s1)] at +0x96 -- which SIGN
     extends the 32-bit [ip->inum] cell -- agree with [SpecDirlink]'s
     ZERO-extended halfword argument. *)
  16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
  (* ---- dirlink's out-of-blocks arm calls printk, not panic ---- *)
  printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  (* namei's own premise, inherited: the walker runs with the base enabled *)
  eb = true ->
  (* the two argstr calls read syscall arguments 0 and 1 out of the
     trapframe page [proc_priv] carries *)
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v0 ->
  pv_tf (us_V U) !! tf_arg_idx 1 = Some v1 ->
  sie_cap_gpr KT1 m K b pj -∗
  (* ENTERED WITH NO LOCK HELD, and that is why there is no [locks_below]
     premise here: the depth is pinned at ZERO, so [CpuOwn.cpu_own_zero_empty]
     DERIVES [lks = ∅] and every order goal the eleven callees raise is
     [locks_below ∅ _]. *)
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, THREADED.  [emp] at [eb = true] -- which this
     contract's own premise forces -- so no caller gains an obligation. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  printk_env fsc_printk fsc_uart fsc_disk -∗
  (* ---- the block layer ---- *)
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  fs_crash_seam fsc_cov fsc_logst -∗
  gen_cert -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
  bslots 3 -∗
  (* ---- the inode cache, and the region the two flushes write ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B; §6′ RULING G).
     Persistent, borrowed and never spent; it rides the SAME channel
     [ireg_inv] does.  It is here because this contract reaches iput, whose
     free path FREEZES the inode, and §2.3's boot-shelter clause makes a
     freezer exhibit the regime it freezes under.  A runtime caller hands
     [SpecIput] the LEFT arm of its borrowed disjunction and discards what
     comes back; only ireclaim, which freezes before the seal is fired,
     lends [ireg_boot] instead. *)
  ireg_open -∗
  (* ---- the three superblock cells dirlink's writei / bmap / balloc read ---- *)
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  (* argstr's page-table side, and the two walks' (iget's ipool arm allocates) *)
  kalloc_env fsc_kalloc None -∗
  (* the running-thread bundle *)
  procs_inv gs -∗
  (* ---- the process, and the reference allowance the two walks need ---- *)
  iref_slots sys_link_slots -∗
  proc_priv γf pj pid U -∗
  (* ---- THE APPLICATION'S SIDE: the three commits link's legs fire at
     their three instants (round E2, lane E2-L).  The dispatcher passes the
     [_unit] dischargers ([FsAbsInvFire.fsabs_link_pre]) exactly as it does
     for unlink. ---- *)
  link_commits (fs_gamma_L fsc_fs) Ftgt Fent Funt -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: sys_link parks in every
     one of its eleven distinct callees, so it can return on another hart
     whatever SIE was doing.
     Vacuous at [true], so consuming it costs the caller nothing. *)
  wp_next true pj (fun (CID : CpuId) =>
  (* THE IMAGE DOES NOT MOVE.  This syscall only READS user memory (argstr,
     through fetchstr and copyinstr); the pages it faults in on the way were
     already in the block's view, as lazy pages reading 0, so vmfault does
     not move it either.  Only the DESCRIPTOR grows, and the block comes
     back at the image it was handed. *)
  ∀ (mf : regfile) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      (* the page table may have GROWN: the two fetchstrs fault user pages
         in.  [uptd_ext_sz] is argstr's own report, composed across the pair by
         [ProcPtOwn.uptd_ext_sz_trans]. *)
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
      (* NO ORDERING on the free pool: dirlink both ALLOCATES (balloc, under
         its writei) and the two walks FREE (itrunc, under an iunlockput of
         a link-count-zero inode).  See the header. *)
      (* the allowance, whole: see the header's reference ledger *)
      iref_slots sys_link_slots -∗
      (* the process block, at the same everything but the page table *)
      proc_priv γf pj pid (us_upt U P') -∗
      ⌜sys_link_ret (mf !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
      (* ...and the legs' receipts, keyed on that answer *)
      link_arms (fs_gamma_L fsc_fs) Ftgt Fent Funt
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSLINK.
  Parameter wp_sys_link_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (dqb dqs dqbs : dfrac)
      (v0 v1 : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (Ftgt : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Fent : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Funt : pfam Σ (aview -> Z -> iProp Σ)),
      wp_sys_link_sconf_body γf gs j gl pd pav pu

 dqb dqs dqbs v0 v1 pid U
                             m K eb b lks Ftgt Fent Funt.
End SYSLINK.
