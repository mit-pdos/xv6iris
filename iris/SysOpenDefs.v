(* SysOpenDefs.v -- the OPEN family's STATEMENT LEAF: the omode readings,
   the two abstract-state commits sys_open fires, the walk package, the two
   caller BUNDLES and the descriptor-success tail.  Definitions and small
   structural lemmas only -- no arms, no frame, no [Module Type].
   sys_open's ONE contract is [SpecSysOpen]'s [SYSOPEN], which requires this
   file and states its arms over these pieces.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-5
   ("ONE CONTRACT PER SYSCALL"; section 7's TWO open rows -- the no-CREATE
   row's empty delta column is CORRECTED below, see THE ONE DELTA).  The
   abstract vocabulary is FsAbs.v; the molds are SysMknodDefs.v (the
   family conventions) and SpecSysMknod.v (the one-contract shape) -- this
   file states the walk premise at the ERA HOPS and the commits at the
   RAW-MAP [_at] shape, which is what [FsAbsMknodFire]'s header shows is
   the only dischargeable one against [InodeRegion.ftop_body] -- plus
   FsAbsReadFire.v (the single-phase whole-[anode] observation) and the
   write side (the delta vocabulary).

   THE DRIVING CONSUMER is xv6's init.c: [open("console", O_RDWR)], called
   twice in init's preamble -- the PLAIN (no-O_CREATE) arm opening a
   DEVICE.

   ==== WHO ELSE TAKES THESE PIECES ====================================

   The pieces here are shared vocabulary, which is why they live below the
   contract rather than inside it:

   - [om_arg] and the four bit readings: ProofSysOpenBits.v,
     ProofSysOpenShared.v, ProofSysOpenStores.v, SpecSysOpen.v.
   - [namei_walk_pre_era] / [namei_walk_dead_era]: SpecKexec.v,
     SpecSysExec.v, SpecSysChdir.v, ProofKexecA.v -- the [∀ pl] shape every
     full-path era walk that does NOT name its path states its premise at.
     open's own bundles left it for [FsAbsEra.ex_start] at the path
     argument 0 names; what still consumes the [∀ pl] form here is the
     generic supplier's bridge ([open_au_plain_at_of_all]), and the death
     receipt [namei_walk_dead_era] is unchanged (it always took its [pl]).
   - [aopen_commit_at] / [atrunc_commit_at]: FsAbsOpenFire.v (the fire
     lemmas), FsAbsInvFire.v (the trivial-family dischargers),
     SpecKexec.v, SpecSysExec.v, SpecSysChdir.v.
   - [open_fd_ok]: SpecSysOpen.v's own create arms, and SpecSysDup.v's
     success arm is cut from it.

   ==== THE TWO BUNDLES ================================================

   [open_au_pre_plain] and [open_au_pre_create] are what a caller hands in
   AT THE PATH IT PASSED, and [open_au_plain_at]/[open_au_create_at] are
   the same two under the reading of trapframe argument 0
   ([ArgPath.arg_path_of], sys_exec's guard) -- one on each side of the
   O_CREATE key.  [SpecSysOpen.open_in] is the [if] that picks between the
   guarded pair, and the contract carries only that.

   - PLAIN ([om_create vom = false], the init arm): the walk premise covers
     the FULL path -- open resolves the whole path via namei, not
     nameiparent -- and the terminal node is observed by a single-phase
     read-only commit.  NOTHING MUTATES at the abstract layer on this
     surface EXCEPT the one conditional delta below.
   - O_CREATE: create's surface at [ty = T_FILE] -- the walk premise is
     [FsAbsEraMknod]'s parent-prefix one-shot VERBATIM, the success commit
     is [FsAbsMknodFire.acre_commit_at] at the child [AFile []]
     ([SysMknodDefs.delta_create] reused, type-parameterized as it was
     built to be), and the exists-lookup rides [dlookup_commit_at].  The
     EXISTS arm does not fail: xv6's open(O_CREATE) on an existing FILE or
     DEVICE opens it ([SpecCreate]'s ARM F-OK: [ty = T_FILE] and
     [di_type dn = T_FILE \/ di_type dn = T_DEVICE] -- the +0x4c / +0x5c
     tests; a found DIRECTORY is ARM F-BAD and fails).

   ==== THE WALK PREMISE (the mknod era lesson, applied at authoring) ===

   Both walk premises are [FsAbsEra.ex_start] / [ep_start] AT THE PATH
   ARGUMENT 0 NAMES -- one-shot fupds firing [FsAbs.ax_hop] at the ERA
   LEND [FsAbsEra.elend] -- the only trace walks that exist fire that
   family, and only that lend lets a hop's consumer read the authority's
   row ([elend_astate]).  The START INUM IS QUANTIFIED with only the
   SLASH->ROOTINO tie, exactly as [npar_walk_pre_era]: an absolute fetch
   pins the start to [FsImg.ROOTINO], a relative one starts at the cwd
   inode, whose inum no landed reading exposes -- so the premise shape is
   consumable by BOTH the absolute era walks and the relative-start arm.
   NO ESCAPE DISJUNCT rides the success arms: init's own path is the
   RELATIVE "console", so an absolute-only escape would gut the driving
   consumer.  ([SpecSysMknod] carries no escape either, for the same
   reason.)

   ==== THE ONE DELTA (correcting doc section 7's no-CREATE row) ========

   The no-CREATE surface has exactly ONE delta: [(omode & O_TRUNC) &&
   ip->type == T_FILE] runs itrunc, a real mutation the doc's row elides.
   It fires ONLY on the file success arm -- devices are excluded by the
   type test itself (even with O_TRUNC set), directories never reach it
   (the O_RDONLY guard), and every failure arm returns before it runs.

   [delta_trunc] is MINTED, in [FsAbsDelta.delta_write]'s total-function
   mold, because the write delta cannot express truncation: [blk_splice]
   never shrinks ([delta_write_no_shrink] below is the machine-checked
   justification for the mint).  The commit [atrunc_commit_at] is the
   two-phase [_at] mold at that delta.  The file+O_TRUNC arm's receipt
   carries the OBSERVED-ROW TIE: the trunc fired at a state whose row at
   [i] still held the observed bytes -- priced on the machine, not free:
   the observation and itrunc happen inside ONE ilock hold (ilock ...
   tests ... filealloc/fdalloc ... itrunc ... iunlock; filealloc's ftable
   lock is a spinlock, nothing sleeps holding the inode unlocked), and the
   prover's payload custody ([IcacheEscrow.ic_loaded]'s whole [top_frag])
   pins the authority's row across the window.  On the CREATE-fresh arm the
   child is [AFile []] and itrunc's delta is the IDENTITY
   ([delta_trunc_nil]), so the caller's own piece fires there and its
   receipt comes back at the empty byte list.

   AND THE PIECE IS OWED ONLY WHEN THE CODE TRUNCATES.  The mode half of
   the C test is decided before the walk runs, so the bundles carry the
   commit under [open_trunc_piece], the guard [if om_trunc vom then ...
   else emp] -- the same shape [SpecSysOpen.open_in] gives [om_create vom].
   An open without O_TRUNC hands in nothing for it, and the arms give
   nothing back.

   ==== WHAT IT DELIBERATELY DOES NOT SAY ==============================

   NOTHING ABOUT DURABILITY (doc section 5's discipline; the only delta on
   either surface is O_TRUNC's and create's, both instances of SNAPSHOT
   like every other).  NOTHING about the OFFSET CELL: the new descriptor's
   [f->off = 0] lives in [fcontent] behind [file_ref] with no
   client-facing carrier.  NOTHING about user memory (the fetched path is
   existential, SpecFetchstr's stance).  NOTHING about create's
   intermediate states (the armed child is observable at nlink 1 before
   the parent's entry lands; SysMknodDefs's honesty stance inherited
   wholesale, [cre_pre]'s freshness shape included).  The agreement seeds
   ([_pinned]) are here so that a stable derivation is assembly rather
   than proof.

   ==== INIT'S INSTANTIATION (the driving consumer), in two lines ======

   [open("console", O_RDWR)]: [vom = 2] -- [om_rdwr_modes] +
   [om_rdwr_plain] put it on the PLAIN side of the key at [rb = wb = true]
   -- and the fetched path is the RELATIVE "console", exercising the
   quantified start at init's cwd (the root); the DEVICE arm lands at
   [ma = 1] (CONSOLE) and the receipt types fd 0 / fd 1 as
   [FdOpen true true (FdDevice 1)] beside [fd_frees = 0 :: _] / [1 :: _].

   BINDERS: one instance path per scope -- [fileG] is bound and
   [icacheG]/[icfg] resolve only through its fields (the SpecCreate
   header's argument, inherited); the FsAbs carriers resolve their
   [fsTopG]/[fsLinkG] through [xv6G]'s fields; [GenId] is bound because
   [open_fd_ok] carries [proc_priv].  The live Γ is
   [FsBytesGamma.fs_gamma_L fsc_fs]; its gname tie to [ftop_body]'s
   authority is definitional ([FsAbs.ftop_gamma_top]). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import DiskInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import IrefSlots.
Require Import FileInvDefs.               (* [is_ftable], [fnode] *)
Require Import ProcInv.
Require Import SpecFdalloc.     (* [fd_frees] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require Import FsTree.          (* [fname] *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ *)
Require FsImg.                  (* [FsImg.ROOTINO : Z] -- Require, NOT
                                   Import: [FsImg]'s [fs_sb] field readers
                                   would shadow the superblock CELL
                                   ADDRESSES the frame below threads *)
Require Import SysMknodDefs.  (* [delta_create], [cre_pre],
                                   [npar_elems], [abs_view_insert] *)
Require Import SysWriteDefs.  (* the splice algebra it re-exports, which
                                   the mint justification below is cut from *)
Require Import FsAbsEra.        (* [elend]: the era lend the hops fire;
                                   [ex_start]/[ep_start]: the walk one-shot
                                   AT ONE PATH, which the two bundles are
                                   stated over *)
Require Import ArgPath.         (* [arg_path_of]: the reading of trapframe
                                   argument 0, shared with sys_exec *)
Require Import FsAbsEraMknod.   (* [npar_walk_pre_era], [npar_walk_dead_era]
                                   -- the parent-prefix one-shot, REUSED *)
Require Import FsAbsMknodFire.  (* [acre_commit_at], [dlookup_commit_at],
                                   [mkf_auth_nview] *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbs.           (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE OMODE READINGS AND THE TRUNC DELTA (PURE)                     *)
(* ===================================================================== *)

(* the mode-flag reading of syscall argument 1: argint keeps the low int,
   and the C's bit tests read that int's bits -- O_WRONLY = 1, O_RDWR = 2,
   O_CREATE = 0x200 (bit 9), O_TRUNC = 0x400 (bit 10) *)
Definition om_arg (v : mword 64) : Z := (bv_unsigned v) mod (2 ^ 32).

Definition om_wronly (v : mword 64) : bool := Z.testbit (om_arg v) 0.
Definition om_rdwr (v : mword 64) : bool := Z.testbit (om_arg v) 1.
Definition om_create (v : mword 64) : bool := Z.testbit (om_arg v) 9.
Definition om_trunc (v : mword 64) : bool := Z.testbit (om_arg v) 10.

(* the two mode booleans the walk stores into the new file, read straight
   off the C: [f->readable = !(omode & O_WRONLY)],
   [f->writable = (omode & O_WRONLY) || (omode & O_RDWR)] *)
Definition om_readable (v : mword 64) : bool := negb (om_wronly v).
Definition om_writable (v : mword 64) : bool := om_wronly v || om_rdwr v.

Lemma om_arg_range (v : mword 64) : 0 <= om_arg v < 2 ^ 32.
Proof. apply Z.mod_pos_bound. lia. Qed.

(* the dir arm's key is the WHOLE-int equality [omode = O_RDONLY = 0];
   under it the stored modes are read-only-read-write-not -- which is what
   makes the dir arm consistent with the landed
   writable-fd-is-not-a-directory theorem *)
Lemma om_rdonly_modes (v : mword 64) :
  om_arg v = 0 -> om_readable v = true /\ om_writable v = false.
Proof.
  rewrite /om_readable /om_writable /om_wronly /om_rdwr.
  intros ->. done.
Qed.

(* init's omode, decoded (the header's two-line instantiation) *)
Lemma om_rdwr_modes (v : mword 64) :
  om_arg v = 2 -> om_readable v = true /\ om_writable v = true.
Proof.
  rewrite /om_readable /om_writable /om_wronly /om_rdwr.
  intros ->. done.
Qed.

Lemma om_rdwr_plain (v : mword 64) :
  om_arg v = 2 -> om_create v = false /\ om_trunc v = false.
Proof. rewrite /om_create /om_trunc. intros ->. done. Qed.

(* THE MINT JUSTIFICATION (header, THE ONE DELTA): the write delta cannot
   express truncation -- a splice never shrinks the file -- so the trunc
   delta below is a NEW total function in [delta_write]'s mold, not a
   reuse refused. *)
Lemma delta_write_no_shrink `{XI : CurCtx} (av : aview) (i : Z) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  (off <= length bs0)%nat ->
  exists bs1,
    delta_write i off new av !! i = Some (MkAnode (AFile bs1) nl)
    /\ (length bs0 <= length bs1)%nat.
Proof.
  intros Hi Hoff. exists (blk_splice off new bs0). split.
  - exact (delta_write_lookup av i off new bs0 nl Hi).
  - rewrite (blk_splice_length_grow off new bs0 Hoff). lia.
Qed.

Require Export FsAbsDelta.   (* [delta_trunc] + its row algebra (hoisted 2026-09-04) *)

(* ===================================================================== *)
(*  2.  THE COMMITS, THE WALK PACKAGE, THE FD STORY, AND THE ARMS         *)
(* ===================================================================== *)

Section OpenDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  (* [GenId], because the arms carry [proc_priv] (SpecSysOpen's note) *)
  Context `{GEN : GenId}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  2a.  The observation commit (single-phase, read-only, at the map)   *)
  (* ------------------------------------------------------------------ *)

  (* THE TERMINAL OBSERVATION, [dlookup_commit_at]'s single-phase
     read-only mold at the WHOLE [anode]: open without O_CREATE mutates
     nothing, so the caller hands the very same authority back and no row
     obligation arises.  Fired once, inside the opened node's lock
     window; agreement against caller-held [nview] shares happens here.
     [E] for reuse; the machine contract instantiates the floor [∅]. *)
  (* NO [`{XI : CurCtx}].  Nothing here reads the hart context -- the piece
     is a ghost-map borrow and a fupd -- and the binder is not free: it makes
     every form stated over this piece CONTEXT-INDEXED, up through
     [SpecSysExec.sys_exec_au_pre] to [UexecSG]'s class instance and hence
     to [UexecRet.uslot], and then two proofs at two contexts hold slots that
     print identically and do not match. *)
  Definition aopen_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> anode -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (i : Z) (a : anode),
       ⌜arow_at (abs_view I) i a⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗ Φ (abs_view I) i a)%I.

  (* satisfiability: the seal cannot be vacuously blocked on the caller *)
  Lemma aopen_commit_at_unit `{XI : CurCtx} Γ E :
    ⊢ aopen_commit_at Γ E (fun _ _ _ => True%I).
  Proof.
    rewrite /aopen_commit_at. iIntros (I i a) "%Hi Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  (* THE STABLE SEED: a caller-held [nview] share turns "some state" into
     "a state whose row at MY inum is MY value" -- discharged here once
     so the follow-on stable derivation is assembly. *)
  Lemma aopen_commit_at_pinned `{XI : CurCtx} Γ E (q : Qp) (jpin : Z) (b : anode)
      (Φ : aview -> Z -> anode -> iProp Σ) :
    nview Γ q jpin b -∗
    (∀ (av : aview) (i : Z) (a : anode),
       ⌜av !! jpin = Some b⌝ -∗ nview Γ q jpin b -∗ Φ av i a) -∗
    aopen_commit_at Γ E Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /aopen_commit_at.
    iIntros (I i a) "%Hi Ha".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
    iModIntro. iFrame "Ha".
    iApply ("HΦ" $! (abs_view I) i a with "[%] Hn"). done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b.  The trunc commit (two-phase, at the map)                       *)
  (* ------------------------------------------------------------------ *)

  (* [acre_commit_at]'s two-phase mold at [delta_trunc]: phase 1 lends
     the pre-state (the row IS a file, at the bytes the receipt names);
     phase 2 is quantified over the post map and constrained by its
     READING alone, so the caller witnesses exactly "the row is empty
     now" and nothing about the record the mover chose. *)
  Definition atrunc_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (i : Z) (bs0 : list (bv 8)) (nl : nat),
       ⌜arow_at (abs_view I) i (MkAnode (AFile bs0) nl)⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         (* THE CALLER'S STEP (app-instances.md section 7): its claim about
            the pre-view survives the delta, at the RAW insert the mover
            performs ([AppInv.app_step]; the delta is its reading) *)
         app_step i I (delta_trunc i (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_trunc i (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗ Φ (abs_view I) i bs0))%I.

  (* satisfiability, at the live Γ: a write-kind shape owes the caller's
     step, which a client that answers for no abstract state pays out of
     the SUPPLY ([AppInv.app_step_acc]) *)
  Lemma atrunc_commit_at_unit (γfs : fs_names) E :
    app_sup -∗ atrunc_commit_at (fs_gamma_L γfs) E (fun _ _ _ => True%I).
  Proof.
    iIntros "#Hsup". rewrite /atrunc_commit_at. iIntros (I i bs0 nl) "%Hpre Ha".
    iDestruct (app_step_acc i I (delta_trunc i (abs_view I))
                 with "Hsup") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma atrunc_commit_at_pinned (γfs : fs_names) E (q : Qp) (jpin : Z) (b : anode)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ) :
    app_sup -∗
    nview (fs_gamma_L γfs) q jpin b -∗
    (∀ (av : aview) (i : Z) (bs : list (bv 8)),
       ⌜av !! jpin = Some b⌝ -∗ nview (fs_gamma_L γfs) q jpin b -∗ Φ av i bs) -∗
    atrunc_commit_at (fs_gamma_L γfs) E Φ.
  Proof.
    iIntros "#Hsup Hn HΦ". rewrite /atrunc_commit_at.
    iIntros (I i bs0 nl) "%Hpre Ha".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
    iDestruct (app_step_acc i I (delta_trunc i (abs_view I))
                 with "Hsup") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    iFrame "Ha'".
    iApply ("HΦ" $! (abs_view I) i bs0 with "[%] Hn"). done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b'.  THE TRUNC PIECE IS OWED ONLY WHEN THE CODE TRUNCATES          *)
  (* ------------------------------------------------------------------ *)

  (* sys_open truncates iff [(omode & O_TRUNC) && ip->type == T_FILE], and
     the mode half of that test is decided by the caller's own omode before
     the walk runs.  So the trunc commit rides the guard [om_trunc vom],
     exactly as [SpecSysOpen.open_in] rides [om_create vom]: an open without
     O_TRUNC owes NOTHING here, and the kernel promises more by demanding
     less.  (The type half is not the caller's to decide, which is why the
     guard is the mode bit alone and the FILE arm is where the receipt
     appears.)

     Written as an [if] rather than as a hypothesis so the parameter lists
     of the bundles, the arms and the receipts stay the length they have:
     [Ft] is still named at [om_trunc vom = false], and what it is worth
     there is [emp].

     THE COMMIT IS NOT KEYED AT THE OPENED INUM, and that is forced rather
     than chosen.  The bundle is handed in BEFORE [argstr] runs: the walk
     sits under [∀ pl, ⌜arg_path_of M pv pl⌝ -∗ …] and the commits sit
     OUTSIDE that wand (the note at [open_au_plain_at] says why -- argstr
     can fail, and then no [pl] satisfies the reading, so a failure-fold
     consumer must get the commits back on the nose).  So no inum exists to
     name at supply time, and an [i]-indexed [atrunc_commit_at] would have
     to be handed in as [∀ i, …], which is the obligation the unguarded
     shape already has.  The walk's terminal cursor is no tie either: the
     O_CREATE FRESH arm fires this piece at the child CREATE just made
     ([SpecSysOpen.open_post_ok_create]), which went through no hop.  The
     guard is what a constraining application needs anyway -- with the bit
     clear it owes nothing, so [FsConsPin.file_pin_trunc]'s [i <> ino] is
     never demanded of it. *)
  Definition open_trunc_piece Γ (vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    (if om_trunc vom then pf_at (atrunc_commit_at Γ appE) Ft else emp)%I.

  (* the two readings, so no consumer destructs the [if] by hand *)
  Lemma open_trunc_piece_true Γ (vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    om_trunc vom = true ->
    open_trunc_piece Γ vom Ft ⊣⊢ pf_at (atrunc_commit_at Γ appE) Ft.
  Proof. intros Hv. rewrite /open_trunc_piece Hv. reflexivity. Qed.

  Lemma open_trunc_piece_false Γ (vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    om_trunc vom = false -> open_trunc_piece Γ vom Ft ⊣⊢ emp.
  Proof. intros Hv. rewrite /open_trunc_piece Hv. reflexivity. Qed.

  (* ...and the free one: at [om_trunc vom = false] nothing is owed, so the
     piece is available out of thin air.  This is the whole content of the
     tightening for a caller like init, whose [open("console", O_RDWR)] has
     the bit clear ([om_arg_two_flags]). *)
  Lemma open_trunc_piece_none Γ (vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    om_trunc vom = false -> ⊢ open_trunc_piece Γ vom Ft.
  Proof. intros Hv. rewrite /open_trunc_piece Hv. done. Qed.

  (* ------------------------------------------------------------------ *)
  (*  2c.  The walk package (full path; the era hops; quantified start)   *)
  (* ------------------------------------------------------------------ *)

  (* ONE SHOT, instantiated by the walk at the string argstr fetched and
     at the inum it starts from -- [npar_walk_pre_era]'s shape over the
     FULL element list (open resolves via namei, not nameiparent).  The
     start is namex's rule ([FsAbsStart.um_start_of]): an absolute fetch
     pins [FsImg.ROOTINO], a relative one starts at [cw], the calling
     process's cwd inum -- the contract passes its block's [pv_cwi]
     (header, THE WALK PREMISE; lane C3). *)
  (* NO [`{XI : CurCtx}] -- see [aopen_commit_at]. *)
  Definition namei_walk_pre_era (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ) : iProp Σ :=
    (∀ (pl : list (bv 8)) (r : Z),
       ⌜r = um_start_of cw pl⌝ ={⊤}=∗
       P 0%nat r
       ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (path_elems pl)
           0%nat)%I.

  (* the walk's death receipt, the era refund shape verbatim: either hop
     [k] never fired (non-directory cursor, or namex's nlink guard) and
     the cursor comes back with hops from [k], or it fired and missed and
     the miss receipt comes back with hops from [S k] *)
  (* NO [`{XI : CurCtx}] -- see [aopen_commit_at] and [namei_walk_pre_era]
     above: the body is the era refund, and nothing in it reads a context.
     The binder has to be absent rather than merely unused, because the
     failure fold this appears in is what open's and chdir's RECEIPTS carry
     ([SpecSysOpen.open_receipt_plain], [SpecSysChdir.chdir_receipt]), and a
     receipt is read at a U-mode key where there is no context to resolve. *)
  Definition namei_walk_dead_era (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) : iProp Σ :=
    (∃ (k : nat) (d : Z),
       ⌜(k < length (path_elems pl))%nat⌝ ∗
       ((P k d
         ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (path_elems pl)
             k)
        ∨ (Pmiss k d
           ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss
               (path_elems pl) (S k))))%I.

  (* ------------------------------------------------------------------ *)
  (*  2d.  The AU bundles                                                 *)
  (* ------------------------------------------------------------------ *)

  (* Everything the PLAIN caller hands in, AT THE PATH IT PASSED, at the
     mask floor [∅].  Each one-shot piece arrives as its AU CONJOINED with
     its own refund (the REFUNDS ruling); the pair is [PieceFam.pfam], the
     receipt beside the refund, so the list stays the length it had.  The
     walk's cursor pair [P]/[Pmiss] stays BARE: a sequenced piece carries
     its refund as its cursor and owes no second one.

     THE WALK IS AT ONE PATH ([FsAbsEra.ex_start] at [pl]), not at every
     path: [namei_walk_pre_era]'s body instantiated there, which is a
     rename ([FsAbsOpenFire.opf_start_of_open] is the one-line bridge, and
     [open_au_pre_plain_of_all] below is this bundle's).  A caller whose
     cursor is PINNED -- a pin is sound at ONE path -- can hand this in;
     the [∀ pl] form it could not.  The guard that says WHICH path is the
     syscall tier's ([open_au_plain_at] below, [ArgPath.arg_path_of] at
     trapframe argument 0), exactly as sys_exec's is. *)
  Definition open_au_pre_plain Γ (γfs : fs_names) (cw : Z)
      (pl : list (bv 8)) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    (ex_start γfs cw P Pmiss pl
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ open_trunc_piece Γ vom Ft)%I.

  (* ...and the O_CREATE caller: the parent-prefix one-shot REUSED from
     the mknod era file at that same path ([FsAbsEra.ep_start]), create's
     fused delta at the child [AFile []], the exists observation, and
     open's own two commits *)
  Definition open_au_pre_create Γ (γfs : fs_names) (cw : Z)
      (pl : list (bv 8)) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    (ep_start γfs cw P Pmiss pl
     ∗ pf_at (acre_commit_at Γ appE (AFile [])) Fok
     ∗ pf_at (dlookup_commit_at Γ appE) Fex
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ open_trunc_piece Γ vom Ft
     (* ...and create's CHILD legs (round E2, lane E2-C) *)
     ∗ cre_child_unfired Γ (AFile []) Farm Fun)%I.

  (* ------------------------------------------------------------------ *)
  (*  2d'.  THE SYSCALL TIER: the same bundle under the reading of the    *)
  (*  caller's argument 0.                                                *)
  (*                                                                      *)
  (*  sys_open [argstr]s trapframe argument 0 and walks THAT string, so    *)
  (*  the WALK PIECE is owed at whatever the image holds there:            *)
  (*  [∀ pl, ⌜arg_path_of M pv pl⌝ -∗ ex_start … pl], which is             *)
  (*  [SpecSysExec.sys_exec_au_pre]'s first conjunct one syscall over.     *)
  (*  It is ONE walk, not a family of them -- the wand is linear and the   *)
  (*  reading is a function of [(M, pv)] ([ArgPath.arg_path_of_uniq]) --   *)
  (*  so a caller that knows its own image pays at exactly one path, and   *)
  (*  a caller that knows nothing about it still supplies the wand from    *)
  (*  the ∀-shaped walk premise in one line ([_of_all] below).             *)
  (*                                                                      *)
  (*  THE COMMITS STAY OUTSIDE THE WAND, and that is forced rather than    *)
  (*  chosen.  argstr can fail (a bad pointer, a string past MAXPATH), and *)
  (*  then NO [pl] satisfies the reading at all -- an image with no NUL    *)
  (*  at or after [pv] has no reading -- so a consumer of the failure      *)
  (*  fold's "nothing happened" arm could never open a whole-bundle wand   *)
  (*  to get its commits back.  It needs them back on the nose             *)
  (*  ([SpecSysMknod.mknod_stable_fail]'s first arm is exactly that        *)
  (*  consumer), and here they are.  Only the walk is path-shaped anyway:  *)
  (*  a commit is keyed by an inum and a view, never by a string.          *)
  (* ------------------------------------------------------------------ *)
  Definition open_au_plain_at Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    ((∀ pl : list (bv 8), ⌜arg_path_of M pv pl⌝ -∗ ex_start γfs cw P Pmiss pl)
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ open_trunc_piece Γ vom Ft)%I.

  Definition open_au_create_at Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    ((∀ pl : list (bv 8), ⌜arg_path_of M pv pl⌝ -∗ ep_start γfs cw P Pmiss pl)
     ∗ pf_at (acre_commit_at Γ appE (AFile [])) Fok
     ∗ pf_at (dlookup_commit_at Γ appE) Fex
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ open_trunc_piece Γ vom Ft
     ∗ cre_child_unfired Γ (AFile []) Farm Fun)%I.

  (* ...and the INSTANCE: at the path the syscall actually read, the walk
     wand fires and the bundle is the one-path one above.  This is the step
     sys_open's proof takes once argstr has answered. *)
  Lemma open_au_plain_at_inst Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8))
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    arg_path_of M pv pl ->
    open_au_plain_at Γ γfs cw M pv vom P Pmiss Fo Ft -∗
    open_au_pre_plain Γ γfs cw pl vom P Pmiss Fo Ft.
  Proof.
    iIntros (Hpl) "(Hw & Ho & Ht)". rewrite /open_au_pre_plain. iFrame "Ho Ht".
    iApply ("Hw" $! pl with "[%]"). exact Hpl.
  Qed.

  Lemma open_au_create_at_inst Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64) (pl : list (bv 8))
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    arg_path_of M pv pl ->
    open_au_create_at Γ γfs cw M pv vom P Pmiss Farm Fun Fok Fex Fo Ft -∗
    open_au_pre_create Γ γfs cw pl vom P Pmiss Farm Fun Fok Fex Fo Ft.
  Proof.
    iIntros (Hpl) "(Hw & Hok & Hex & Ho & Ht & Hch)".
    rewrite /open_au_pre_create. iFrame "Hok Hex Ho Ht Hch".
    iApply ("Hw" $! pl with "[%]"). exact Hpl.
  Qed.

  (* THE GENERIC SUPPLIER'S ONE LINE.  A family that tracks nothing owes
     the walk at EVERY string ([namei_walk_pre_era] / [npar_walk_pre_era],
     what [FsAbsInvFire] discharges), and that form INSTANTIATES to the
     one-path bundle -- the direction that matters, since the bundle is
     the weaker thing to supply. *)
  Lemma open_au_plain_at_of_all Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    namei_walk_pre_era γfs cw P Pmiss -∗
    pf_at (aopen_commit_at Γ appE) Fo -∗
    open_trunc_piece Γ vom Ft -∗
    open_au_plain_at Γ γfs cw M pv vom P Pmiss Fo Ft.
  Proof.
    iIntros "Hw Ho Ht". rewrite /open_au_plain_at. iFrame "Ho Ht".
    iIntros (pl) "_". rewrite /ex_start /namei_walk_pre_era. iIntros (r Hr).
    iMod ("Hw" $! pl r with "[%]") as "[$ $]"; [exact Hr | done].
  Qed.

  Lemma open_au_create_at_of_all Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    npar_walk_pre_era γfs cw P Pmiss -∗
    pf_at (acre_commit_at Γ appE (AFile [])) Fok -∗
    pf_at (dlookup_commit_at Γ appE) Fex -∗
    pf_at (aopen_commit_at Γ appE) Fo -∗
    open_trunc_piece Γ vom Ft -∗
    cre_child_unfired Γ (AFile []) Farm Fun -∗
    open_au_create_at Γ γfs cw M pv vom P Pmiss Farm Fun Fok Fex Fo Ft.
  Proof.
    iIntros "Hw Hok Hex Ho Ht Hch". rewrite /open_au_create_at.
    iFrame "Hok Hex Ho Ht Hch".
    iIntros (pl) "_". rewrite /ep_start /npar_walk_pre_era. iIntros (r Hr).
    iMod ("Hw" $! pl r with "[%]") as "[$ $]"; [exact Hr | done].
  Qed.

  Lemma open_au_pre_plain_of_all Γ (γfs : fs_names) (cw : Z)
      (pl : list (bv 8)) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    namei_walk_pre_era γfs cw P Pmiss -∗
    pf_at (aopen_commit_at Γ appE) Fo -∗
    open_trunc_piece Γ vom Ft -∗
    open_au_pre_plain Γ γfs cw pl vom P Pmiss Fo Ft.
  Proof.
    iIntros "Hw Ho Ht". rewrite /open_au_pre_plain. iFrame "Ho Ht".
    rewrite /ex_start /namei_walk_pre_era. iIntros (r Hr).
    iMod ("Hw" $! pl r with "[%]") as "[$ $]"; [exact Hr | done].
  Qed.

  Lemma open_au_pre_create_of_all Γ (γfs : fs_names) (cw : Z)
      (pl : list (bv 8)) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    npar_walk_pre_era γfs cw P Pmiss -∗
    pf_at (acre_commit_at Γ appE (AFile [])) Fok -∗
    pf_at (dlookup_commit_at Γ appE) Fex -∗
    pf_at (aopen_commit_at Γ appE) Fo -∗
    open_trunc_piece Γ vom Ft -∗
    cre_child_unfired Γ (AFile []) Farm Fun -∗
    open_au_pre_create Γ γfs cw pl vom P Pmiss Farm Fun Fok Fex Fo Ft.
  Proof.
    iIntros "Hw Hok Hex Ho Ht Hch". rewrite /open_au_pre_create.
    iFrame "Hok Hex Ho Ht Hch".
    rewrite /ep_start /npar_walk_pre_era. iIntros (r Hr).
    iMod ("Hw" $! pl r with "[%]") as "[$ $]"; [exact Hr | done].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2e.  The descriptor story                                           *)
  (* ------------------------------------------------------------------ *)

  (* the sharpened success post implies the landed bundle shape *)
  Lemma open_fd_frags_any `{XI : CurCtx} (γ : gname) (sts : list fdstate) :
    fd_frags γ sts ⊢ fd_frags_any γ.
  Proof. rewrite /fd_frags_any. iIntros "H". by iExists sts. Qed.

  (* THE SUCCESS ARMS' SHARED TAIL, [SpecSysOpen.sys_open_post]'s success
     arm with the bundle SHARPENED: the LEAST free descriptor now names
     the new file (a0 = that descriptor; which file-table slot is
     existential, the table is not the caller's to name), the block comes
     back with the cell written ([us_ofile]), and the fragment bundle
     comes back at an EXPLICIT state list whose row at [fd] is the NEW
     descriptor's type -- [proc_priv_settle]'s payout, re-packed through
     [fd_frags_acc]. *)
  Definition open_fd_ok `{XI : CurCtx} (γf : gname) (p : mword 64) (pid : mword 32)
      (UW : ustate) (rb wb : bool) (t : fdtype) (sts : list fdstate)
      (r : mword 64) : iProp Σ :=
    (∃ (fd : nat) (l : list nat) (k : nat),
       ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
        /\ fd_frees (pv_ofile (us_V UW)) = fd :: l
        (* ...AND THE SLOT WAS CLOSED -- [SpecSysOpen.sys_open_post]'s
           conjunct, verbatim: fdalloc hands its authority back at
           [FdClosed], and [UserFd.ufd_open]'s insert needs the key free *)
        /\ sts !! fd = Some FdClosed⌝ ∗
       proc_priv γf p pid (us_ofile UW fd (fnode k)) ∗
       (* the caller's OWN table with exactly ONE row moved -- the landed
          success row's shape, at the arm's typed row *)
       fd_frags (pv_fdg (us_V UW)) (<[fd := FdOpen rb wb t]> sts))%I.

  (* ------------------------------------------------------------------ *)
  (*  2e'.  The descriptor story, SPLIT: the kernel's half and the        *)
  (*  process's.                                                          *)
  (*                                                                      *)
  (*  [open_fd_ok] above bundles three things: the [struct proc] cell      *)
  (*  fdalloc wrote ([proc_priv] at [us_ofile]), the descriptor-state      *)
  (*  fragments at the moved table ([fd_frags]) -- both KERNEL-owned, and  *)
  (*  neither nameable by a process at its own key -- and one PURE fact,   *)
  (*  which is the only part of open's success a process can state:        *)
  (*  WHICH descriptor came back, that it was closed before, and that the  *)
  (*  table it resumes at is the caller's with that one row retyped.       *)
  (*                                                                      *)
  (*  So the pure fact is named on its own ([open_fd_rcpt], read at the    *)
  (*  RESUME view [fdv'] rather than at an existential insert), and         *)
  (*  [open_fd_ok_split] below reads the bundle as the kernel's half at     *)
  (*  that view beside it.  [open_fd_ok] itself keeps the shape its five    *)
  (*  producers prove, and the split is a consequence of it.                *)
  (* ------------------------------------------------------------------ *)

  (* THE RECEIPT: what open's success is worth to the PROCESS.  It sharpens
     [UsysMemOk.usys_fd_ok]'s open row -- which says a descriptor became
     open at SOME type and mode -- by naming the mode bits (the caller's own
     omode) and the type (the node the walk reached), and it is the reason
     the arm's [t] is worth carrying: a program that opens the console
     learns its descriptor is [FdDevice], not merely open. *)
  Definition open_fd_rcpt (rb wb : bool) (t : fdtype) (sts : list fdstate)
      (r : mword 64) (fdv' : list fdstate) : Prop :=
    exists fd : nat,
      r = (mword_of_int (Z.of_nat fd) : mword 64)
      /\ sts !! fd = Some FdClosed
      /\ fdv' = <[fd := FdOpen rb wb t]> sts.

  (* ...AND THE SPLIT ITSELF: [open_fd_ok] read as the KERNEL'S HALF -- the
     block with the [ofile] cell written and the descriptor fragments -- at
     the view [fdv'] the process resumes at, BESIDE the pure receipt about
     that view.  One direction is what every consumer wants
     ([SpecSysOpen.open_arms_split]); the arms keep both halves, so nothing
     is given up by reading them this way. *)
  Lemma open_fd_ok_split `{XI : CurCtx} (γf : gname) (p : mword 64)
      (pid : mword 32) (UW : ustate) (rb wb : bool) (t : fdtype)
      (sts : list fdstate) (r : mword 64) :
    open_fd_ok γf p pid UW rb wb t sts r ⊢
      ∃ (fd : nat) (l : list nat) (k : nat) (fdv' : list fdstate),
        (* the kernel's row, AT THE SPLIT'S OWN [fd]: which descriptor
           fdalloc took, that the caller's table had it closed, and what the
           resume view is.  It is [open_fd_rcpt]'s content spelled at that
           [fd] rather than at an existential one, because the dispatcher
           reads [SpecFdalloc.fd_frees_below] at the same descriptor the
           free list's head names ([ProofSyscall]'s open arm). *)
        ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
         /\ fd_frees (pv_ofile (us_V UW)) = fd :: l
         /\ sts !! fd = Some FdClosed
         /\ fdv' = <[fd := FdOpen rb wb t]> sts⌝
        ∗ ⌜open_fd_rcpt rb wb t sts r fdv'⌝
        ∗ proc_priv γf p pid (us_ofile UW fd (fnode k))
        ∗ fd_frags (pv_fdg (us_V UW)) fdv'.
  Proof.
    rewrite /open_fd_ok /open_fd_rcpt.
    iIntros "H". iDestruct "H" as (fd l k) "((%Hr & %Hfl & %Hcl) & Hp & Hb)".
    iExists fd, l, k, (<[fd := FdOpen rb wb t]> sts).
    iSplitR; [ iPureIntro;
               split_and!; [ exact Hr | exact Hfl | exact Hcl | reflexivity ] | ].
    iSplitR; [ iPureIntro; exists fd;
               split_and!; [ exact Hr | exact Hcl | reflexivity ] | ].
    iFrame "Hp Hb".
  Qed.

End OpenDefs.

(* big-op bodies behind definitions: seal them, or an [iFrame] near a
   consumer resolves instances through the whole hop family
   (durable-notes; optimization.md, "a big-op body is the predictor").
   The three commits are match-free single wands and stay transparent,
   as the family's do. *)
Global Typeclasses Opaque namei_walk_pre_era namei_walk_dead_era
  open_au_pre_plain open_au_pre_create
  open_au_plain_at open_au_create_at open_fd_ok.
