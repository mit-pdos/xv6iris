(* SpecSysOpenAU.v -- the OPEN family's STATEMENT LEAF: the omode readings,
   the two abstract-state commits sys_open fires, the walk package, the two
   caller BUNDLES and the descriptor-success tail.  Definitions and small
   structural lemmas only -- no arms, no frame, no [Module Type].
   sys_open's ONE contract is [SpecSysOpen]'s [SYSOPEN], which requires this
   file and states its arms over these pieces.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-5
   ("ONE CONTRACT PER SYSCALL"; section 7's TWO open rows -- the no-CREATE
   row's empty delta column is CORRECTED below, see THE ONE DELTA).  The
   abstract vocabulary is FsAbs.v; the molds are SpecSysMknodAU.v (the
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

   - [om_arg] and the four bit readings: FdRowPilot.v, UkInitFs.v,
     FsFdMirror.v, ProofSysOpenAUBits.v.
   - [open_walk_pre_era] / [open_walk_dead_era]: SpecKexecAU.v,
     SpecSysExecAU.v, SpecSysChdir.v, ProofKexecAUA.v -- every full-path
     era walk states its premise at this shape.
   - [aopen_commit_at] / [atrunc_commit_at]: FsAbsOpenFire.v (the fire
     lemmas), FsAbsInvFire.v (the trivial-family dischargers),
     SpecKexecAU.v, SpecSysExecAU.v, SpecSysChdir.v.
   - [open_fd_ok]: SpecSysOpen.v's own create arms, and SpecSysDup.v's
     success arm is cut from it.

   ==== THE TWO BUNDLES ================================================

   [open_au_pre_plain] and [open_au_pre_create] are what a caller hands in
   on each side of the O_CREATE key; [SpecSysOpen.open_in] is the [if] that
   picks between them, and the contract carries only that.

   - PLAIN ([om_create vom = false], the init arm): the walk premise covers
     the FULL path -- open resolves the whole path via namei, not
     nameiparent -- and the terminal node is observed by a single-phase
     read-only commit.  NOTHING MUTATES at the abstract layer on this
     surface EXCEPT the one conditional delta below.
   - O_CREATE: create's surface at [ty = T_FILE] -- the walk premise is
     [FsAbsEraMknod]'s parent-prefix one-shot VERBATIM, the success commit
     is [FsAbsMknodFire.acre_commit_at] at the child [AFile []]
     ([SpecSysMknodAU.delta_create] reused, type-parameterized as it was
     built to be), and the exists-lookup rides [dlookup_commit_at].  The
     EXISTS arm does not fail: xv6's open(O_CREATE) on an existing FILE or
     DEVICE opens it ([SpecCreate]'s ARM F-OK: [ty = T_FILE] and
     [di_type dn = T_FILE \/ di_type dn = T_DEVICE] -- the +0x4c / +0x5c
     tests; a found DIRECTORY is ARM F-BAD and fails).

   ==== THE WALK PREMISE (the mknod era lesson, applied at authoring) ===

   Both walk premises are one-shot fupds firing [FsAbs.ax_hop] at the ERA
   LEND [FsAbsEra.elend] -- the only trace walks that exist fire that
   family, and only that lend lets a hop's consumer read the authority's
   row ([elend_astate]).  The START INUM IS QUANTIFIED with only the
   SLASH->ROOTINO tie, exactly as [mknod_walk_pre_era]: an absolute fetch
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
   pins the authority's row across the window.  On the CREATE-fresh arm
   the child is [AFile []] and itrunc's delta is the IDENTITY
   ([delta_trunc_nil]); the commit is REFUNDED there rather than fired
   vacuously.

   ==== WHAT IT DELIBERATELY DOES NOT SAY ==============================

   NOTHING ABOUT DURABILITY (doc section 5's discipline; the only delta on
   either surface is O_TRUNC's and create's, both instances of SNAPSHOT
   like every other).  NOTHING about the OFFSET CELL: the new descriptor's
   [f->off = 0] lives in [fcontent] behind [file_ref] with no
   client-facing carrier.  NOTHING about user memory (the fetched path is
   existential, SpecFetchstr's stance).  NOTHING about create's
   intermediate states (the armed child is observable at nlink 1 before
   the parent's entry lands; SpecSysMknodAU's honesty stance inherited
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
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskInv.
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
Require Import FileInv.               (* [is_ftable], [fnode] *)
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecPrintk.      (* [printk_env], [printk_gen_contract] *)
Require Import SpecDirlink.     (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import SpecFdalloc.     (* [fd_frees] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require Import FsTree.          (* [fname] *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ *)
Require FsImg.                  (* [FsImg.ROOTINO : Z] -- Require, NOT
                                   Import: [FsImg]'s [fs_sb] field readers
                                   would shadow the superblock CELL
                                   ADDRESSES the frame below threads *)
Require Import SpecSysMknodAU.  (* [delta_create], [cre_pre],
                                   [mknod_parent_elems], [abs_view_insert] *)
Require Import SpecSysWriteAU.  (* the splice algebra it re-exports, which
                                   the mint justification below is cut from *)
Require Import FsAbsEra.        (* [elend]: the era lend the hops fire *)
Require Import FsAbsEraMknod.   (* [mknod_walk_pre_era], [mknod_walk_dead_era]
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
Definition om_arg `{XI : CurCtx} (v : mword 64) : Z := (bv_unsigned v) mod (2 ^ 32).

Definition om_wronly `{XI : CurCtx} (v : mword 64) : bool := Z.testbit (om_arg v) 0.
Definition om_rdwr `{XI : CurCtx} (v : mword 64) : bool := Z.testbit (om_arg v) 1.
Definition om_create `{XI : CurCtx} (v : mword 64) : bool := Z.testbit (om_arg v) 9.
Definition om_trunc `{XI : CurCtx} (v : mword 64) : bool := Z.testbit (om_arg v) 10.

(* the two mode booleans the walk stores into the new file, read straight
   off the C: [f->readable = !(omode & O_WRONLY)],
   [f->writable = (omode & O_WRONLY) || (omode & O_RDWR)] *)
Definition om_readable `{XI : CurCtx} (v : mword 64) : bool := negb (om_wronly v).
Definition om_writable `{XI : CurCtx} (v : mword 64) : bool := om_wronly v || om_rdwr v.

Lemma om_arg_range `{XI : CurCtx} (v : mword 64) : 0 <= om_arg v < 2 ^ 32.
Proof. apply Z.mod_pos_bound. lia. Qed.

(* the dir arm's key is the WHOLE-int equality [omode = O_RDONLY = 0];
   under it the stored modes are read-only-read-write-not -- which is what
   makes the dir arm consistent with the landed
   writable-fd-is-not-a-directory theorem *)
Lemma om_rdonly_modes `{XI : CurCtx} (v : mword 64) :
  om_arg v = 0 -> om_readable v = true /\ om_writable v = false.
Proof.
  rewrite /om_readable /om_writable /om_wronly /om_rdwr.
  intros ->. done.
Qed.

(* init's omode, decoded (the header's two-line instantiation) *)
Lemma om_rdwr_modes `{XI : CurCtx} (v : mword 64) :
  om_arg v = 2 -> om_readable v = true /\ om_writable v = true.
Proof.
  rewrite /om_readable /om_writable /om_wronly /om_rdwr.
  intros ->. done.
Qed.

Lemma om_rdwr_plain `{XI : CurCtx} (v : mword 64) :
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

Section SysOpenAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
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
     [SpecSysExecAU.sys_exec_au_pre] to [UexecSG]'s class instance and hence
     to [UexecRet.uslot], and then two proofs at two contexts hold slots that
     print identically and do not match. *)
  Definition aopen_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> anode -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (i : Z) (a : anode),
       ⌜arow_at (abs_view I) i a⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗ Φ (abs_view I) i a)%I.

  (* the astate-shaped reading, for a client that reasons abstractly --
     the read-only direction holds (a client that can serve the
     authority form can serve this one by unfolding [astate]); the reverse
     does not (nothing ties the returned authority to the borrowed map),
     which is why the CONTRACT carries the [_at] form *)
  Definition aopen_commit `{XI : CurCtx} Γ (E : coPset)
      (Φ : aview -> Z -> anode -> iProp Σ) : iProp Σ :=
    (∀ (av : aview) (i : Z) (a : anode),
       ⌜arow_at av i a⌝ -∗
       astate_q Γ (1/2) av ={E}=∗ astate_q Γ (1/2) av ∗ Φ av i a)%I.

  Lemma aopen_commit_at_weaken `{XI : CurCtx} Γ E Φ :
    aopen_commit_at Γ E Φ ⊢ aopen_commit Γ E Φ.
  Proof.
    iIntros "Hcm". rewrite /aopen_commit.
    iIntros (av i a) "%Hi Hst".
    iDestruct (astate_q_elim with "Hst") as (I) "[Ha %Hav]". subst av.
    iMod ("Hcm" $! I i a with "[//] Ha") as "[Ha HΦ]".
    iModIntro. iFrame "HΦ". iApply astate_q_intro. iExact "Ha".
  Qed.

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
  Definition atrunc_commit_at `{XI : CurCtx} Γ (E : coPset)
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
     step, which a client that knows nothing pays out of the parked license
     ([AppInv.app_step_acc], inside the commit's own fupd) *)
  Lemma atrunc_commit_at_unit `{XI : CurCtx} (γfs : fs_names) E :
    ↑appN ⊆ E ->
    app_inv γfs -∗ atrunc_commit_at (fs_gamma_L γfs) E (fun _ _ _ => True%I).
  Proof.
    iIntros (HE) "#Hai". rewrite /atrunc_commit_at. iIntros (I i bs0 nl) "%Hpre Ha".
    iMod (app_step_acc_view E γfs i I (delta_trunc i (abs_view I)) HE
            (delta_trunc_absent (abs_view I) i) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma atrunc_commit_at_pinned `{XI : CurCtx} (γfs : fs_names) E (q : Qp) (jpin : Z) (b : anode)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    nview (fs_gamma_L γfs) q jpin b -∗
    (∀ (av : aview) (i : Z) (bs : list (bv 8)),
       ⌜av !! jpin = Some b⌝ -∗ nview (fs_gamma_L γfs) q jpin b -∗ Φ av i bs) -∗
    atrunc_commit_at (fs_gamma_L γfs) E Φ.
  Proof.
    iIntros (HE) "#Hai Hn HΦ". rewrite /atrunc_commit_at.
    iIntros (I i bs0 nl) "%Hpre Ha".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
    iMod (app_step_acc_view E γfs i I (delta_trunc i (abs_view I)) HE
            (delta_trunc_absent (abs_view I) i) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    iFrame "Ha'".
    iApply ("HΦ" $! (abs_view I) i bs0 with "[%] Hn"). done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2c.  The walk package (full path; the era hops; quantified start)   *)
  (* ------------------------------------------------------------------ *)

  (* ONE SHOT, instantiated by the walk at the string argstr fetched and
     at the inum it starts from -- [mknod_walk_pre_era]'s shape over the
     FULL element list (open resolves via namei, not nameiparent).  The
     start is namex's rule ([FsAbsStart.um_start_of]): an absolute fetch
     pins [FsImg.ROOTINO], a relative one starts at [cw], the calling
     process's cwd inum -- the contract passes its block's [pv_cwi]
     (header, THE WALK PREMISE; lane C3). *)
  (* NO [`{XI : CurCtx}] -- see [aopen_commit_at]. *)
  Definition open_walk_pre_era (γfs : fs_names) (cw : Z)
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
  Definition open_walk_dead_era `{XI : CurCtx} (γfs : fs_names)
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

  (* Everything the PLAIN caller hands in, at the mask floor [∅].  Each
     one-shot piece arrives as its AU CONJOINED with its own refund (the
     REFUNDS ruling); the pair is [PieceFam.pfam], the receipt beside the
     refund, so the list stays the length it had.  The walk's cursor pair
     [P]/[Pmiss] stays BARE: a sequenced piece carries its refund as its
     cursor and owes no second one. *)
  Definition open_au_pre_plain `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    (open_walk_pre_era γfs cw P Pmiss
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ pf_at (atrunc_commit_at Γ appE) Ft)%I.

  (* ...and the O_CREATE caller: the parent-prefix one-shot REUSED from
     the mknod era file, create's fused delta at the child [AFile []],
     the exists observation, and open's own two commits *)
  Definition open_au_pre_create `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    (mknod_walk_pre_era γfs cw P Pmiss
     ∗ pf_at (acre_commit_at Γ appE (AFile [])) Fok
     ∗ pf_at (dlookup_commit_at Γ appE) Fex
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ pf_at (atrunc_commit_at Γ appE) Ft
     (* ...and create's CHILD legs (round E2, lane E2-C) *)
     ∗ cre_child_unfired Γ (AFile []) Farm Fun)%I.

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

End SysOpenAU.

(* big-op bodies behind definitions: seal them, or an [iFrame] near a
   consumer resolves instances through the whole hop family
   (durable-notes; optimization.md, "a big-op body is the predictor").
   The three commits are match-free single wands and stay transparent,
   as the family's do. *)
Global Typeclasses Opaque open_walk_pre_era open_walk_dead_era
  open_au_pre_plain open_au_pre_create open_fd_ok.
