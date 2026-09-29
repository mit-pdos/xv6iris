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
Require Import FsAbsEra.        (* [elend]: the era lend the hops fire;
                                   [ex_start]/[ep_start]: the walk one-shot
                                   AT ONE PATH, which the two bundles are
                                   stated over *)
Require Import ArgPath.         (* [arg_path_of]: the reading of trapframe
                                   argument 0, shared with sys_exec *)
Require Import SysMknodDefs.     (* [npar_elems]: the PARENT prefix (TL-3K) *)
Require Import FsAbsMknodFire.  (* [acre_commit_at], [dlookup_commit_at],
                                   [mkf_auth_nview] *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbs.           (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import CtxIdDefs.

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
       ghost_map_auth_frac (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ∗ Φ (abs_view I) i a)%I.

  (* satisfiability: the seal cannot be vacuously blocked on the caller *)
  Lemma aopen_commit_at_unit `{XI : CurCtx} Γ E :
    ⊢ aopen_commit_at Γ E (fun _ _ _ => True%I).
  Proof using .
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
  Proof using .
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
       ghost_map_auth_frac (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ∗
         (* THE CALLER'S STEP (app-instances.md section 7): its claim about
            the pre-view survives the delta, at the RAW insert the mover
            performs ([AppInv.app_step]; the delta is its reading) *)
         app_step i I (delta_trunc i (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_trunc i (abs_view I)⌝ -∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ∗ Φ (abs_view I) i bs0))%I.

  (* satisfiability, at the live Γ: a write-kind shape owes the caller's
     step, which a client that answers for no abstract state pays out of
     the SUPPLY ([AppInv.app_step_acc]) *)
  Lemma atrunc_commit_at_unit (γfs : fs_names) E :
    app_sup -∗ atrunc_commit_at (fs_gamma_L γfs) E (fun _ _ _ => True%I).
  Proof using .
    iIntros "#Hsup". rewrite /atrunc_commit_at. iIntros (I i bs0 nl) "%Hpre Ha".
    iDestruct (app_step_acc i I (delta_trunc i (abs_view I))
                 with "Hsup") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  (* ...and at a PERSISTENT post the supplier already holds: what an
     application pays out of its taint, whose receipt is the taint again
     ([PinnedOpen.pobs_dead_trunc_piece]) *)
  Lemma atrunc_commit_at_unit_pers (γfs : fs_names) E (T : iProp Σ)
      `{!Persistent T} :
    app_sup -∗ T -∗ atrunc_commit_at (fs_gamma_L γfs) E (fun _ _ _ => T).
  Proof using .
    iIntros "#Hsup #HT". rewrite /atrunc_commit_at. iIntros (I i bs0 nl) "%Hpre Ha".
    iDestruct (app_step_acc i I (delta_trunc i (abs_view I))
                 with "Hsup") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha' HT".
  Qed.

  Lemma atrunc_commit_at_pinned (γfs : fs_names) E (q : Qp) (jpin : Z) (b : anode)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ) :
    app_sup -∗
    nview (fs_gamma_L γfs) q jpin b -∗
    (∀ (av : aview) (i : Z) (bs : list (bv 8)),
       ⌜av !! jpin = Some b⌝ -∗ nview (fs_gamma_L γfs) q jpin b -∗ Φ av i bs) -∗
    atrunc_commit_at (fs_gamma_L γfs) E Φ.
  Proof using .
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
  (*  2b'.  THE KEYED TRUNC PIECE AND ITS PERMIT (lanes F-OPEN-2 and      *)
  (*  F-OPEN-3, seam 1)                                                   *)
  (*                                                                      *)
  (*  The commit used to be NOT keyed at the                              *)
  (*  opened inum because no inum exists to name at SUPPLY time.  That is  *)
  (*  true of the supply and false of the FIRE, and lane F-OPEN priced     *)
  (*  the difference: a constraining application -- one whose claim is     *)
  (*  about a PARTICULAR file -- cannot step a truncate at an inum it      *)
  (*  cannot identify, because the row the call reached might be one its   *)
  (*  own claim pins (in the file application's case one of the four       *)
  (*  era-0 binaries, whose rows [FileFsPure.file_fs_pure] holds).  So     *)
  (*  the piece has to arrive KEYED, on [FsAbsCreateFire.aunarm_of_arm]'s  *)
  (*  mould: a PERMIT naming the inum goes in, the commit AT THAT INUM     *)
  (*  comes out, and whatever the application parked in the permit rides   *)
  (*  into the fire.                                                      *)
  (*                                                                      *)
  (*  [atrunc_commit_i] is [atrunc_commit_at] with [i] an INDEX rather     *)
  (*  than quantified inside, [atrunc_of_permit] is the keyed family, and  *)
  (*  the two bridges below say the keyed shape is WEAKER than the landed  *)
  (*  one in the direction that matters (a caller that answers at every    *)
  (*  row answers at the permitted one, so every generic supplier is a     *)
  (*  restatement and the permit goes unread).                            *)
  (*                                                                      *)
  (*  THE BUNDLES CARRY IT (lane F-OPEN-3).  Keying alone was necessary   *)
  (*  and not sufficient: the EXISTS arm also needs the permit to tie its  *)
  (*  inum to the WALK'S TERMINAL IDENTIFICATION, which is what            *)
  (*  [trunc_permit_of] adds -- the tie beside the DISJUNCTION the kernel  *)
  (*  pays from whichever of create's two arms ran.  The plain surface     *)
  (*  carries the same piece at the TERMINAL permit ([trunc_term_at] /     *)
  (*  [trunc_term_arg], lane TRUNC-PERMIT): its walk's terminal cursor,    *)
  (*  so an application whose walk cannot reach a terminal refutes the    *)
  (*  permit instead of stepping a truncate at every file row.  Every     *)
  (*  generic caller still supplies the piece through                     *)
  (*  [open_trunc_piece_of_all] in one line.                              *)
  (* ------------------------------------------------------------------ *)

  Definition atrunc_commit_i Γ (E : coPset) (i : Z)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (bs0 : list (bv 8)) (nl : nat),
       ⌜arow_at (abs_view I) i (MkAnode (AFile bs0) nl)⌝ -∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth_frac (γtop Γ) (1/2) I ∗
         app_step i I (delta_trunc i (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_trunc i (abs_view I)⌝ -∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth_frac (γtop Γ) (1/2) I' ∗ Φ (abs_view I) i bs0))%I.

  (* the two readings, in both directions: the indexed family at every
     index IS the landed one *)
  Lemma atrunc_commit_i_of_at Γ (E : coPset) (i : Z)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ) :
    atrunc_commit_at Γ E Φ -∗ atrunc_commit_i Γ E i Φ.
  Proof using .
    rewrite /atrunc_commit_at /atrunc_commit_i.
    iIntros "H" (I bs0 nl) "%Hpre Hka".
    iApply ("H" $! I i bs0 nl with "[%] Hka"). exact Hpre.
  Qed.

  Lemma atrunc_commit_at_of_i Γ (E : coPset)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ) :
    (∀ i : Z, atrunc_commit_i Γ E i Φ) -∗ atrunc_commit_at Γ E Φ.
  Proof using .
    rewrite /atrunc_commit_at /atrunc_commit_i.
    iIntros "H" (I i bs0 nl) "%Hpre Hka".
    iApply ("H" $! i I bs0 nl with "[%] Hka"). exact Hpre.
  Qed.

  (* THE KEYED PIECE, on [aunarm_of_arm]'s mould *)
  Definition atrunc_of_permit Γ (E : coPset) (Kt : Z -> iProp Σ)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (∀ i : Z, Kt i -∗ atrunc_commit_i Γ E i Φ)%I.

  (* THE BRIDGE every generic supplier takes, and the whole content of
     "the permit is unread at a trivial family": a caller that can answer
     at EVERY file row can answer at the permitted one, and drops the
     permit ([aunarm_of_arm_of_all]'s twin). *)
  Lemma atrunc_of_permit_of_all Γ (E : coPset) (Kt : Z -> iProp Σ)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ) :
    atrunc_commit_at Γ E Φ -∗ atrunc_of_permit Γ E Kt Φ.
  Proof using .
    iIntros "H". rewrite /atrunc_of_permit. iIntros (i) "_".
    iApply (atrunc_commit_i_of_at with "H").
  Qed.

  (* satisfiability at the live Γ, so the keyed shape cannot be vacuously
     blocked on the caller either *)
  Lemma atrunc_of_permit_unit (γfs : fs_names) E (Kt : Z -> iProp Σ) :
    app_sup -∗ atrunc_of_permit (fs_gamma_L γfs) E Kt (fun _ _ _ => True%I).
  Proof using .
    iIntros "#Hsup".
    iApply (atrunc_of_permit_of_all with "[]").
    iApply (atrunc_commit_at_unit γfs E with "Hsup").
  Qed.

  (* THE CREATE'S OWN RECEIPT, AS A PERMIT: what the FRESH arm holds when
     it fires the truncate.  [FsAbsCreateFire.cre_acre_fired] already
     carries the create's pre-state facts beside the caller's receipt, so
     this is that pair with the parent and the name existentially closed --
     the truncate is keyed by the CHILD's inum and by nothing else. *)
  Definition trunc_permit_cre
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) (i : Z)
      : iProp Σ :=
    (∃ (d : Z) (nm : fname), cre_acre_fired Fok d nm i (AFile []))%I.

  (* ------------------------------------------------------------------ *)
  (*  THE PERMIT ITSELF (lane F-OPEN-3).                                  *)
  (*                                                                      *)
  (*  THE PLAIN SURFACE PAYS ITS WALK'S TERMINAL CURSOR (lane              *)
  (*  TRUNC-PERMIT).  Its walk's terminal IS the inum the truncate         *)
  (*  reaches, and the cursor there is the one thing a constraining        *)
  (*  application can refute: at a name its claim says is absent the walk  *)
  (*  dies at its first hop and the terminal cursor is the taint           *)
  (*  ([PinnedObs.pobs_dead_term]), so the application pays the step out   *)
  (*  of the taint alone -- where a trivial permit asked it for an         *)
  (*  [AppInv.app_step] at EVERY file row, which a claim pinning rows      *)
  (*  cannot give.  The cursor is SPENT into the permit exactly as the     *)
  (*  parent cursor is below: a truncating plain open's arms report it     *)
  (*  inside the kept piece's refund where the truncate did not fire       *)
  (*  ([cre_ft_kept]) and not at all where it did; an application that     *)
  (*  wants it back threads it through its own [Ft] receipt               *)
  (*  ([SpecSysOpen.cur_kept], [SpecSysOpen.plain_trunc_kept]).           *)
  (*                                                                      *)
  (*  THE O_CREATE SURFACE PAYS TWO THINGS, and both are what the kernel   *)
  (*  HOLDS at the [itrunc] and the caller could not name at supply time:  *)
  (*                                                                      *)
  (*  (1) THE WALK'S TIE.  [d] and [nm] are quantified inside every one    *)
  (*  of create's own receipts ([dlookup_commit_at] most of all), so the   *)
  (*  sentence "the found node is the one my path names" is precisely      *)
  (*  what those receipts cannot say.  The tie is the pair of facts                   *)
  (*  [SysMknodDefs.npar_cur] already carries at the syscall tier -- the   *)
  (*  last element of the path argument 0 reads IS [nm], and the walk's    *)
  (*  terminal directory is [d] -- guarded by the reading exactly as the   *)
  (*  parent cursor is ([trunc_tie_arg]); at the ONE-PATH tier the guard   *)
  (*  is discharged and the two facts stand bare ([trunc_tie_at]).  The    *)
  (*  cursor is SPENT, not read: [P] is an arbitrary (possibly linear)     *)
  (*  predicate, so the arms of a TRUNCATING create do not report the      *)
  (*  terminal cursor -- see [SpecSysOpen.cur_kept].                       *)
  (*                                                                      *)
  (*  (2) THE DISJUNCTION create's two arms pay from.  On the FRESH run    *)
  (*  the child was made and the create leg fired, so the kernel hands     *)
  (*  the create's own fired receipt ([cre_acre_fired], which is           *)
  (*  [trunc_permit_cre]'s body at a named [d]/[nm]).  On the EXISTS run   *)
  (*  create's [dirlookup] FOUND the name, so the ARM NEVER FIRED and the  *)
  (*  kernel still holds its piece: it hands the exists observation's      *)
  (*  fired receipt BESIDE THAT UNFIRED ARM PIECE.  A constraining         *)
  (*  application parks its claim in the arm ([pf_at] is a CONJUNCTION,    *)
  (*  so the piece's refund carries it) and reads it back here.           *)
  (* ------------------------------------------------------------------ *)

  (* THE PLAIN SURFACE'S PERMIT: the walk's terminal cursor, bare at the
     ONE-PATH tier... *)
  Definition trunc_term_at (pl : list (bv 8)) (P : nat -> Z -> iProp Σ)
      (i : Z) : iProp Σ :=
    P (length (path_elems pl)) i.

  (* ...and under the reading of argument 0 at the SYSCALL tier
     ([SysMknodDefs.npar_cur]'s shape over the FULL element list) *)
  Definition trunc_term_arg (M : gmap Z (bv 8)) (pv : mword 64)
      (P : nat -> Z -> iProp Σ) (i : Z) : iProp Σ :=
    (∀ pl : list (bv 8), ⌜arg_path_of M pv pl⌝ -∗ P (length (path_elems pl)) i)%I.

  Lemma trunc_term_arg_of_at (M : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (P : nat -> Z -> iProp Σ) (i : Z) :
    arg_path_of M pv pl ->
    trunc_term_at pl P i -∗ trunc_term_arg M pv P i.
  Proof using .
    intros Hpl. rewrite /trunc_term_at /trunc_term_arg.
    iIntros "HP" (pl') "%Hpl'".
    rewrite (arg_path_of_uniq M pv pl' pl Hpl' Hpl). iExact "HP".
  Qed.

  Lemma trunc_term_at_of_arg (M : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (P : nat -> Z -> iProp Σ) (i : Z) :
    arg_path_of M pv pl ->
    trunc_term_arg M pv P i -∗ trunc_term_at pl P i.
  Proof using .
    intros Hpl. rewrite /trunc_term_at /trunc_term_arg.
    iIntros "H". iApply ("H" $! pl with "[%]"). exact Hpl.
  Qed.

  (* the tie at the ONE-PATH tier: the two pure-and-cursor facts bare *)
  Definition trunc_tie_at (pl : list (bv 8)) (P : nat -> Z -> iProp Σ)
      (d : Z) (nm : fname) : iProp Σ :=
    (⌜list_basics.list.last (path_elems pl) = Some nm⌝
     ∗ P (length (npar_elems pl)) d)%I.

  (* ...and at the SYSCALL tier, under the reading of argument 0 *)
  Definition trunc_tie_arg (M : gmap Z (bv 8)) (pv : mword 64)
      (P : nat -> Z -> iProp Σ) (d : Z) (nm : fname) : iProp Σ :=
    ((∀ pl : list (bv 8), ⌜arg_path_of M pv pl⌝ -∗
        ⌜list_basics.list.last (path_elems pl) = Some nm⌝)
     ∗ npar_cur M pv P d)%I.

  (* the reading is a function of [(M, pv)], so the two ties are one at
     the path the syscall read ([ArgPath.arg_path_of_uniq]) *)
  Lemma trunc_tie_arg_of_at (M : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (P : nat -> Z -> iProp Σ) (d : Z) (nm : fname) :
    arg_path_of M pv pl ->
    trunc_tie_at pl P d nm -∗ trunc_tie_arg M pv P d nm.
  Proof using .
    intros Hpl. iIntros "[%Hlast HP]". rewrite /trunc_tie_arg. iSplitR.
    - iIntros (pl') "%Hpl'".
      rewrite (arg_path_of_uniq M pv pl' pl Hpl' Hpl). by iPureIntro.
    - iApply (npar_cur_intro M pv pl P d Hpl with "HP").
  Qed.

  (* ...and back: the guarded tie, at the path the reading answers *)
  Lemma trunc_tie_at_of_arg (M : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (P : nat -> Z -> iProp Σ) (d : Z) (nm : fname) :
    arg_path_of M pv pl ->
    trunc_tie_arg M pv P d nm -∗ trunc_tie_at pl P d nm.
  Proof using .
    intros Hpl. rewrite /trunc_tie_arg /trunc_tie_at.
    iIntros "[Hl HP]". iSplitL "Hl".
    - iApply ("Hl" $! pl with "[%]"). exact Hpl.
    - iApply (npar_cur_elim M pv pl P d Hpl with "HP").
  Qed.

  Definition trunc_permit_of Γ (T : Z -> fname -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (i : Z) : iProp Σ :=
    (∃ (d : Z) (nm : fname),
       T d nm ∗
       (cre_acre_fired Fok d nm i (AFile [])
        ∨ (cre_ex_fired Fex d nm i
           ∗ pf_at (aarm_commit_at Γ appE (AFile [])) Farm)))%I.

  (* the permit moves with its tie, contravariantly: a piece keyed by the
     WEAKER permit answers the stronger one *)
  Lemma trunc_permit_of_mono Γ (T T' : Z -> fname -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (i : Z) :
    □ (∀ (d : Z) (nm : fname), T d nm -∗ T' d nm) -∗
    trunc_permit_of Γ T Farm Fok Fex i -∗ trunc_permit_of Γ T' Farm Fok Fex i.
  Proof using .
    iIntros "#Hmv H". rewrite /trunc_permit_of.
    iDestruct "H" as (d nm) "[HT Hrest]". iExists d, nm.
    iSplitL "HT"; [ iApply ("Hmv" with "HT") | iExact "Hrest" ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE EXISTS BRANCH ALONE (lane F-OPEN-6).                            *)
  (*                                                                      *)
  (*  [trunc_permit_of] is a DISJUNCTION, and a piece keyed by it refunds  *)
  (*  a permit whose branch the arm that paid it does not say.  That is    *)
  (*  the whole of F-OPEN-5's residue: a found DEVICE is reported on the   *)
  (*  EXISTS run only, and there create's [dirlookup] found the name and   *)
  (*  the arm NEVER FIRED -- so what was paid is the right disjunct, and   *)
  (*  an application that parks a claim in the arm reads it back and       *)
  (*  contradicts the device.  The left disjunct is unreachable there and  *)
  (*  unrefutable in the logic, so the ARM SAYS WHICH BRANCH IT PAID.      *)
  (*                                                                      *)
  (*  The FRESH run needs no twin: [sys_open] type-checks the inode        *)
  (*  [create] returned, STILL LOCKED (xv6's [sysfile.c]: [create] returns *)
  (*  the inode locked and the [ip->type] test runs before [iunlock]), so  *)
  (*  the observation on that run IS the created child's own type and the  *)
  (*  arm reports [FdInode] with no device sub-arm at all --               *)
  (*  [SpecSysOpen.open_post_ok_create]'s FRESH arm carries [cre_pre av d  *)
  (*  nm ents nl i (AFile [])] and nothing else is needed.                 *)
  (* ------------------------------------------------------------------ *)

  Definition trunc_permit_ex Γ (T : Z -> fname -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (i : Z) : iProp Σ :=
    (∃ (d : Z) (nm : fname),
       T d nm ∗ cre_ex_fired Fex d nm i
       ∗ pf_at (aarm_commit_at Γ appE (AFile [])) Farm)%I.

  (* ...and it IS a permit: the branch-specific one answers the piece the
     caller keyed at the disjunction *)
  Lemma trunc_permit_of_ex Γ (T : Z -> fname -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (i : Z) :
    trunc_permit_ex Γ T Farm Fex i -∗ trunc_permit_of Γ T Farm Fok Fex i.
  Proof using .
    iIntros "H". rewrite /trunc_permit_ex /trunc_permit_of.
    iDestruct "H" as (d nm) "(HT & Hex & Harm)". iExists d, nm.
    iFrame "HT". iRight. iFrame "Hex Harm".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b''.  THE TRUNC PIECE IS OWED ONLY WHEN THE CODE TRUNCATES         *)
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

     THE COMMIT IS NOT KEYED AT THE OPENED INUM AT SUPPLY TIME, and that
     is forced rather than chosen.  The bundle is handed in BEFORE [argstr]
     runs: the walk sits under [∀ pl, ⌜arg_path_of M pv pl⌝ -∗ …] and the
     commits sit OUTSIDE that wand (the note at [open_au_plain_at] says
     why -- argstr can fail, and then no [pl] satisfies the reading, so a
     failure-fold consumer must get the commits back on the nose).  So no
     inum exists to name when the piece is handed in, and what names it
     later is the PERMIT below, paid by the kernel where it holds what
     pays it.  The guard is what a constraining application needs anyway
     -- with the bit clear it owes nothing, so [FsConsPin.file_pin_trunc]'s
     [i <> ino] is never demanded of it. *)
  (* THE PIECE IS KEYED BY A PERMIT (lane F-OPEN-3).  [Kt] is what the
     kernel pays at the [itrunc] to name the inum the call reached; a
     caller that answers at every row ignores it
     ([open_trunc_piece_of_all]), and the create surface's caller reads
     its own claim off it ([trunc_permit_of] below). *)
  Definition open_trunc_piece Γ (vom : mword 64) (Kt : Z -> iProp Σ)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    (if om_trunc vom then pf_at (atrunc_of_permit Γ appE Kt) Ft else emp)%I.

  (* the two readings, so no consumer destructs the [if] by hand *)
  Lemma open_trunc_piece_true Γ (vom : mword 64) (Kt : Z -> iProp Σ)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    om_trunc vom = true ->
    open_trunc_piece Γ vom Kt Ft ⊣⊢ pf_at (atrunc_of_permit Γ appE Kt) Ft.
  Proof using . intros Hv. rewrite /open_trunc_piece Hv. reflexivity. Qed.

  Lemma open_trunc_piece_false Γ (vom : mword 64) (Kt : Z -> iProp Σ)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    om_trunc vom = false -> open_trunc_piece Γ vom Kt Ft ⊣⊢ emp.
  Proof using . intros Hv. rewrite /open_trunc_piece Hv. reflexivity. Qed.

  (* ...and the free one: at [om_trunc vom = false] nothing is owed, so the
     piece is available out of thin air.  This is the whole content of the
     tightening for a caller like init, whose [open("console", O_RDWR)] has
     the bit clear ([om_arg_two_flags]). *)
  Lemma open_trunc_piece_none Γ (vom : mword 64) (Kt : Z -> iProp Σ)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    om_trunc vom = false -> ⊢ open_trunc_piece Γ vom Kt Ft.
  Proof using . intros Hv. rewrite /open_trunc_piece Hv. done. Qed.

  (* THE GENERIC SUPPLIER'S ONE LINE: a caller that can answer at EVERY
     file row answers at the permitted one and never reads the permit
     ([atrunc_of_permit_of_all]). *)
  Lemma open_trunc_piece_of_all Γ (vom : mword 64) (Kt : Z -> iProp Σ)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    pf_at (atrunc_commit_at Γ appE) Ft -∗ open_trunc_piece Γ vom Kt Ft.
  Proof using .
    iIntros "H". rewrite /open_trunc_piece. destruct (om_trunc vom); [| done].
    iApply (pf_at_mono with "[] H"). iIntros "H".
    iApply (atrunc_of_permit_of_all with "H").
  Qed.

  (* THE PERMIT MOVES CONTRAVARIANTLY: a piece that answers the STRONGER
     permit answers the weaker one, which is how the syscall-tier bundle
     instantiates to the one-path bundle ([open_au_create_at_inst]). *)
  Lemma open_trunc_piece_mono Γ (vom : mword 64) (Kt Kt' : Z -> iProp Σ)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    □ (∀ i : Z, Kt' i -∗ Kt i) -∗
    open_trunc_piece Γ vom Kt Ft -∗ open_trunc_piece Γ vom Kt' Ft.
  Proof using .
    iIntros "#Hmv H". rewrite /open_trunc_piece.
    destruct (om_trunc vom); [| done].
    iApply (pf_at_mono with "[] H"). iIntros "H".
    rewrite /atrunc_of_permit. iIntros (i) "Hk".
    iApply ("H" with "[Hk]"). iApply ("Hmv" with "Hk").
  Qed.

  (* THE TWO TIERS' PIECES, as the syscall-tier bundle's instance needs
     them in BOTH directions: the one-path piece answers the guarded
     permit at the path the reading names, and back. *)
  Lemma open_trunc_piece_arg_to_at Γ (vom : mword 64)
      (M : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8))
      (P : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    arg_path_of M pv pl ->
    open_trunc_piece Γ vom
      (trunc_permit_of Γ (trunc_tie_arg M pv P) Farm Fok Fex) Ft -∗
    open_trunc_piece Γ vom
      (trunc_permit_of Γ (trunc_tie_at pl P) Farm Fok Fex) Ft.
  Proof using .
    intros Hpl. iIntros "H".
    iApply (open_trunc_piece_mono with "[] H"). iIntros "!>" (i) "Hk".
    iApply (trunc_permit_of_mono Γ (trunc_tie_at pl P) (trunc_tie_arg M pv P)
              Farm Fok Fex i with "[] Hk").
    iIntros "!>" (d nm) "HT".
    iApply (trunc_tie_arg_of_at M pv pl P d nm Hpl with "HT").
  Qed.

  Lemma open_trunc_piece_at_to_arg Γ (vom : mword 64)
      (M : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8))
      (P : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    arg_path_of M pv pl ->
    open_trunc_piece Γ vom
      (trunc_permit_of Γ (trunc_tie_at pl P) Farm Fok Fex) Ft -∗
    open_trunc_piece Γ vom
      (trunc_permit_of Γ (trunc_tie_arg M pv P) Farm Fok Fex) Ft.
  Proof using .
    intros Hpl. iIntros "H".
    iApply (open_trunc_piece_mono with "[] H"). iIntros "!>" (i) "Hk".
    iApply (trunc_permit_of_mono Γ (trunc_tie_arg M pv P) (trunc_tie_at pl P)
              Farm Fok Fex i with "[] Hk").
    iIntros "!>" (d nm) "HT".
    iApply (trunc_tie_at_of_arg M pv pl P d nm Hpl with "HT").
  Qed.

  (* ...and the PLAIN surface's pair, one permit over *)
  Lemma open_trunc_piece_term_arg_to_at Γ (vom : mword 64)
      (M : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8))
      (P : nat -> Z -> iProp Σ)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    arg_path_of M pv pl ->
    open_trunc_piece Γ vom (trunc_term_arg M pv P) Ft -∗
    open_trunc_piece Γ vom (trunc_term_at pl P) Ft.
  Proof using .
    intros Hpl. iIntros "H".
    iApply (open_trunc_piece_mono with "[] H"). iIntros "!>" (i) "Hk".
    iApply (trunc_term_arg_of_at M pv pl P i Hpl with "Hk").
  Qed.

  Lemma open_trunc_piece_term_at_to_arg Γ (vom : mword 64)
      (M : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8))
      (P : nat -> Z -> iProp Σ)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    arg_path_of M pv pl ->
    open_trunc_piece Γ vom (trunc_term_at pl P) Ft -∗
    open_trunc_piece Γ vom (trunc_term_arg M pv P) Ft.
  Proof using .
    intros Hpl. iIntros "H".
    iApply (open_trunc_piece_mono with "[] H"). iIntros "!>" (i) "Hk".
    iApply (trunc_term_at_of_arg M pv pl P i Hpl with "Hk").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE PIECE ONCE THE INUM IS KNOWN.  Between the point the call has   *)
  (*  an inode in hand and the [itrunc] the piece travels KEYED at that   *)
  (*  inum: the permit is paid ONCE, where what pays it is still in hand  *)
  (*  (the walk's terminal cursor on the plain surface, create's own      *)
  (*  payout on the O_CREATE one), and every block below                  *)
  (*  carries [atrunc_commit_i].  A caller whose truncate never fires     *)
  (*  gets this back and eliminates to its own refund, which is where the *)
  (*  investment it parked in the permit comes home ([pf_at] is a         *)
  (*  CONJUNCTION: the supplier proves the commit and the refund from the *)
  (*  same permit).                                                      *)
  (* ------------------------------------------------------------------ *)
  Definition open_trunc_at Γ (vom : mword 64) (i : Z)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    (if om_trunc vom then pf_at (atrunc_commit_i Γ appE i) Ft else emp)%I.

  (* ...AND THE PERMIT IS RECOVERABLE FROM IT.  A [pf_at] is a CONJUNCTION,
     so keying the piece spends the permit on the COMMIT side only and the
     refund side may keep it: this is the family the keyed piece travels
     at, and it is what makes an open that fails PAST a fired create hand
     the caller back what it parked in the permit ([SpecSysOpen]'s arm (a)
     -- [itrunc] runs after fdalloc, so that arm is reachable and its
     investment must come home).  Both surfaces travel at it: the name
     is create's, which keyed first. *)
  Definition cre_ft_kept (Kt : Z -> iProp Σ) (i : Z)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ) :=
    MkPfam Ft.(pf_recv) (Ft.(pf_refund) ∗ Kt i)%I.

  Lemma open_trunc_at_true Γ (vom : mword 64) (i : Z)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    om_trunc vom = true ->
    open_trunc_at Γ vom i Ft ⊣⊢ pf_at (atrunc_commit_i Γ appE i) Ft.
  Proof using . intros Hv. rewrite /open_trunc_at Hv. reflexivity. Qed.

  Lemma open_trunc_at_false Γ (vom : mword 64) (i : Z)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    om_trunc vom = false -> open_trunc_at Γ vom i Ft ⊣⊢ emp.
  Proof using . intros Hv. rewrite /open_trunc_at Hv. reflexivity. Qed.

  Lemma open_trunc_at_none Γ (vom : mword 64) (i : Z)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    om_trunc vom = false -> ⊢ open_trunc_at Γ vom i Ft.
  Proof using . intros Hv. rewrite /open_trunc_at Hv. done. Qed.

  (* PAYING THE PERMIT: the piece keyed at one inum. *)
  Lemma open_trunc_at_of_permit Γ (vom : mword 64) (Kt : Z -> iProp Σ)
      (i : Z) (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    open_trunc_piece Γ vom Kt Ft -∗
    (if om_trunc vom then Kt i else emp) -∗
    open_trunc_at Γ vom i (cre_ft_kept Kt i Ft).
  Proof using .
    iIntros "H Hk". rewrite /open_trunc_piece /open_trunc_at.
    destruct (om_trunc vom); [| done].
    rewrite /pf_at /atrunc_of_permit /cre_ft_kept. cbn [pf_recv pf_refund].
    iSplit.
    - iDestruct "H" as "[H _]". iApply ("H" with "Hk").
    - iDestruct "H" as "[_ H]". iFrame "H Hk".
  Qed.

  (* ...AND PAYING IT WITH A STRONGER PERMIT, so the piece REFUNDS the
     stronger one (lane F-OPEN-6).  [pf_at] is a CONJUNCTION, so the
     payment is available on both sides: the commit spends it through the
     weakening and the refund keeps it as it was handed in.  This is what
     lets the EXISTS arm say which branch of [trunc_permit_of] it paid
     while the caller still hands in one piece keyed at the disjunction. *)
  Lemma open_trunc_at_of_permit_at Γ (vom : mword 64) (Kt Kt' : Z -> iProp Σ)
      (i : Z) (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    (Kt' i -∗ Kt i) -∗
    open_trunc_piece Γ vom Kt Ft -∗
    (if om_trunc vom then Kt' i else emp) -∗
    open_trunc_at Γ vom i (cre_ft_kept Kt' i Ft).
  Proof using .
    iIntros "Hmv H Hk". rewrite /open_trunc_piece /open_trunc_at.
    destruct (om_trunc vom); [| done].
    rewrite /pf_at /atrunc_of_permit /cre_ft_kept. cbn [pf_recv pf_refund].
    iSplit.
    - iDestruct "H" as "[H _]". iApply "H". iApply ("Hmv" with "Hk").
    - iDestruct "H" as "[_ H]". iFrame "H Hk".
  Qed.

  (* the keyed piece is MONOTONE IN THE PERMIT IT REFUNDS, which is how a
     consumer that does not care which branch was paid reads the
     branch-specific piece as the disjunctive one *)
  Lemma open_trunc_at_kept_mono Γ (vom : mword 64) (Kt Kt' : Z -> iProp Σ)
      (i : Z) (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    (Kt' i -∗ Kt i) -∗
    open_trunc_at Γ vom i (cre_ft_kept Kt' i Ft) -∗
    open_trunc_at Γ vom i (cre_ft_kept Kt i Ft).
  Proof using .
    iIntros "Hmv H". rewrite /open_trunc_at.
    destruct (om_trunc vom); [| done].
    rewrite /pf_at /cre_ft_kept. cbn [pf_recv pf_refund].
    iSplit.
    - iDestruct "H" as "[H _]". iExact "H".
    - iDestruct "H" as "[_ [$ Hk]]". iApply ("Hmv" with "Hk").
  Qed.

  (* THE KEPT PIECE, READ: a consumer that does not fire the commit may
     drop the permit its refund carries... *)
  Lemma open_trunc_at_kept_forget Γ (vom : mword 64) (Kt : Z -> iProp Σ)
      (i : Z) (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    open_trunc_at Γ vom i (cre_ft_kept Kt i Ft) -∗ open_trunc_at Γ vom i Ft.
  Proof using .
    iIntros "H". rewrite /open_trunc_at. destruct (om_trunc vom); [| done].
    rewrite /pf_at /cre_ft_kept. cbn [pf_recv pf_refund].
    iSplit; [iDestruct "H" as "[$ _]" | iDestruct "H" as "[_ [$ _]]"].
  Qed.

  (* ...and a keyed piece takes a permit onto its refund side for nothing:
     how the create surface enters the blocks the plain surface states at
     its own kept family ([ProofSysOpenCreArm.socr_key_plain]) *)
  Lemma open_trunc_at_kept_intro Γ (vom : mword 64) (Kt : Z -> iProp Σ)
      (i : Z) (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    open_trunc_at Γ vom i Ft -∗
    (if om_trunc vom then Kt i else emp) -∗
    open_trunc_at Γ vom i (cre_ft_kept Kt i Ft).
  Proof using .
    iIntros "H Hk". rewrite /open_trunc_at. destruct (om_trunc vom); [| done].
    rewrite /pf_at /cre_ft_kept. cbn [pf_recv pf_refund].
    iSplit; [iDestruct "H" as "[$ _]" | iDestruct "H" as "[_ H]"; iFrame "H Hk"].
  Qed.


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
     (* THE TRUNCATE'S PERMIT is the walk's own terminal cursor (lane
        TRUNC-PERMIT): paid where the kernel holds it, at the join *)
     ∗ open_trunc_piece Γ vom (trunc_term_at pl P) Ft)%I.

  (* ...and the O_CREATE caller: the parent-prefix one-shot REUSED from
     the mknod era file at that same path ([FsAbsEra.ep_start]), create's
     fused delta at the child [AFile []], the exists observation, and
     open's own two commits *)
  Definition open_au_pre_create Γ (γfs : fs_names) (cw : Z)
      (pl : list (bv 8)) (Nm : fname -> Prop) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    (ep_start γfs cw P Pmiss pl
     (* THE PARENT CURSOR rides the commit (lane TL-3K, WALL A fix (i)) *)
     (* ...AND THE NAME PREDICATE (RULING NM, the thread's open half):
        create files exactly the name argument 0's last element spells, so
        the caller's claim is asked to absorb a create there and nowhere
        else.  [SpecSysMknod.mknod_au_pre]'s [Nm], one syscall over. *)
     ∗ pf_at (acre_commit_at_nm Γ appE (AFile []) Nm
                (P (length (npar_elems pl))) Farm) Fok
     ∗ pf_at (dlookup_commit_at Γ appE) Fex
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     (* THE TRUNCATE'S PERMIT is create's own payout at this path (lane
        F-OPEN-3): the walk's tie beside whichever of the two arms ran *)
     ∗ open_trunc_piece Γ vom
         (trunc_permit_of Γ (trunc_tie_at pl P) Farm Fok Fex) Ft
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
     ∗ open_trunc_piece Γ vom (trunc_term_arg M pv P) Ft)%I.

  Definition open_au_create_at Γ (γfs : fs_names) (cw : Z)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) : iProp Σ :=
    ((∀ pl : list (bv 8), ⌜arg_path_of M pv pl⌝ -∗ ep_start γfs cw P Pmiss pl)
     (* the name UNDER THE SAME GUARD the cursor carries
        ([FsAbsCreateNm.npar_nm]): whatever argument 0 reads *)
     ∗ pf_at (acre_commit_at_nm Γ appE (AFile []) (npar_nm M pv)
                (npar_cur M pv P) Farm) Fok
     ∗ pf_at (dlookup_commit_at Γ appE) Fex
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ open_trunc_piece Γ vom
         (trunc_permit_of Γ (trunc_tie_arg M pv P) Farm Fok Fex) Ft
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
  Proof using .
    iIntros (Hpl) "(Hw & Ho & Ht)". rewrite /open_au_pre_plain. iFrame "Ho".
    iSplitL "Hw". { iApply ("Hw" $! pl with "[%]"). exact Hpl. }
    (* the permit at this path: the cursor stands bare once the reading
       has answered *)
    iApply (open_trunc_piece_term_arg_to_at Γ vom M pv pl P Ft Hpl with "Ht").
  Qed.

  (* THE CURSOR'S TWO READINGS, as one move (lane TL-3K);
     [SpecSysMknod.mknod_acre_inst]'s twin at the file child. *)
  Lemma open_acre_inst Γ (M : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (P : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    arg_path_of M pv pl ->
    pf_at (acre_commit_at_nm Γ appE (AFile []) (npar_nm M pv)
             (npar_cur M pv P) Farm) Fok -∗
    pf_at (acre_commit_at_nm Γ appE (AFile []) (npar_nm M pv)
             (P (length (npar_elems pl))) Farm) Fok.
  Proof using .
    intros Hpl. iIntros "Hok".
    rewrite /acre_commit_at_nm. iApply (pf_at_mono with "[] Hok").
    iIntros "Hok". rewrite /acre_commit_at_gen_nm.
    iIntros (I d i nm ents nl) "%Hpre %Hnm %HNm Harm HPd Ha".
    iDestruct (npar_cur_intro M pv pl P d Hpl with "HPd") as "HPd".
    iMod ("Hok" $! I d i nm ents nl with "[//] [//] [//] Harm HPd Ha")
      as "(Ha & HPd & Hstep & Hph2)".
    iDestruct (npar_cur_elim M pv pl P d Hpl with "HPd") as "HPd".
    iModIntro. by iFrame "Ha HPd Hstep Hph2".
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
    open_au_pre_create Γ γfs cw pl (npar_nm M pv) vom P Pmiss
      Farm Fun Fok Fex Fo Ft.
  Proof using .
    iIntros (Hpl) "(Hw & Hok & Hex & Ho & Ht & Hch)".
    rewrite /open_au_pre_create.
    iSplitL "Hw".
    { iApply ("Hw" $! pl with "[%]"). exact Hpl. }
    iFrame "Hex Ho Hch".
    iSplitR "Ht".
    { iApply (open_acre_inst Γ M pv pl P Farm Fok Hpl with "Hok"). }
    (* THE PERMIT, at this path: the tie's two facts stand bare once the
       reading has answered ([trunc_tie_arg_of_at]) *)
    iApply (open_trunc_piece_arg_to_at Γ vom M pv pl P Farm Fok Fex Ft Hpl
              with "Ht").
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
    open_trunc_piece Γ vom (trunc_term_arg M pv P) Ft -∗
    open_au_plain_at Γ γfs cw M pv vom P Pmiss Fo Ft.
  Proof using .
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
    pf_at (acre_commit_at Γ appE (AFile []) (npar_cur M pv P) Farm) Fok -∗
    pf_at (dlookup_commit_at Γ appE) Fex -∗
    pf_at (aopen_commit_at Γ appE) Fo -∗
    open_trunc_piece Γ vom
      (trunc_permit_of Γ (trunc_tie_arg M pv P) Farm Fok Fex) Ft -∗
    cre_child_unfired Γ (AFile []) Farm Fun -∗
    open_au_create_at Γ γfs cw M pv vom P Pmiss Farm Fun Fok Fex Fo Ft.
  Proof using .
    iIntros "Hw Hok Hex Ho Ht Hch". rewrite /open_au_create_at.
    iFrame "Hex Ho Ht Hch".
    iSplitR "Hok".
    { iIntros (pl) "_". rewrite /ep_start /npar_walk_pre_era. iIntros (r Hr).
      iMod ("Hw" $! pl r with "[%]") as "[$ $]"; [exact Hr | done]. }
    (* a provider that answers at EVERY name answers at the guarded ones *)
    iApply (pf_at_mono with "[] Hok"). iIntros "Hok".
    iApply (acre_commit_at_nm_of Γ appE (AFile []) (npar_nm M pv)
              (npar_cur M pv P) Farm Fok.(pf_recv) with "Hok").
  Qed.

  Lemma open_au_pre_plain_of_all Γ (γfs : fs_names) (cw : Z)
      (pl : list (bv 8)) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    namei_walk_pre_era γfs cw P Pmiss -∗
    pf_at (aopen_commit_at Γ appE) Fo -∗
    open_trunc_piece Γ vom (trunc_term_at pl P) Ft -∗
    open_au_pre_plain Γ γfs cw pl vom P Pmiss Fo Ft.
  Proof using .
    iIntros "Hw Ho Ht". rewrite /open_au_pre_plain. iFrame "Ho Ht".
    rewrite /ex_start /namei_walk_pre_era. iIntros (r Hr).
    iMod ("Hw" $! pl r with "[%]") as "[$ $]"; [exact Hr | done].
  Qed.

  Lemma open_au_pre_create_of_all Γ (γfs : fs_names) (cw : Z)
      (pl : list (bv 8)) (Nm : fname -> Prop) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ)) :
    npar_walk_pre_era γfs cw P Pmiss -∗
    pf_at (acre_commit_at Γ appE (AFile [])
             (P (length (npar_elems pl))) Farm) Fok -∗
    pf_at (dlookup_commit_at Γ appE) Fex -∗
    pf_at (aopen_commit_at Γ appE) Fo -∗
    open_trunc_piece Γ vom
      (trunc_permit_of Γ (trunc_tie_at pl P) Farm Fok Fex) Ft -∗
    cre_child_unfired Γ (AFile []) Farm Fun -∗
    open_au_pre_create Γ γfs cw pl Nm vom P Pmiss Farm Fun Fok Fex Fo Ft.
  Proof using .
    iIntros "Hw Hok Hex Ho Ht Hch". rewrite /open_au_pre_create.
    iFrame "Hex Ho Ht Hch".
    iSplitR "Hok".
    { rewrite /ep_start /npar_walk_pre_era. iIntros (r Hr).
      iMod ("Hw" $! pl r with "[%]") as "[$ $]"; [exact Hr | done]. }
    iApply (pf_at_mono with "[] Hok"). iIntros "Hok".
    iApply (acre_commit_at_nm_of Γ appE (AFile []) Nm
              (P (length (npar_elems pl))) Farm Fok.(pf_recv) with "Hok").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2e.  The descriptor story                                           *)
  (* ------------------------------------------------------------------ *)

  (* the sharpened success post implies the landed bundle shape *)
  Lemma open_fd_frags_any `{XI : CurCtx} (γ : gname) (sts : list fdstate) :
    fd_frags γ sts ⊢ fd_frags_any γ.
  Proof using . rewrite /fd_frags_any. iIntros "H". by iExists sts. Qed.

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
  Proof using .
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

(* ...and the truncate's permit family with them (lane F-OPEN-3): every
   one of these is a guard over a [pf_at], so an [iFrame] that sees
   through them resolves instances through the whole create surface --
   optimization.md's rule, and the measured cost of not doing it here was
   a twenty-minute [ProofSysOpenCreArm]. *)
Global Typeclasses Opaque open_trunc_piece open_trunc_at cre_ft_kept
  trunc_permit_of trunc_permit_ex trunc_tie_at trunc_tie_arg
  trunc_permit_cre trunc_term_at trunc_term_arg.
