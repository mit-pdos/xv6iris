(* SpecSysOpenAU.v -- sys_open's ATOMIC-UPDATE contract, stated over the
   campaign's abstract state.  A STATEMENT FILE: definitions, structural
   lemmas, and a [Module Type] seal -- no walk, no proof against the
   machine.

   Design of record: claude-notes/design/fs-syscall-specs.md sections 0-5
   (v3; section 7's TWO open rows -- the no-CREATE row's empty delta
   column is CORRECTED below, see THE ONE DELTA) and lane W of
   claude-notes/projects/fs-syscall-specs.md.  The abstract vocabulary is
   FsAbs.v (lane A, landed); the molds are SpecSysMknodAU.v (the family
   conventions) READ THROUGH ITS TWO PROVER FINDINGS -- this file states
   the walk premise at the ERA HOPS and the commits at the RAW-MAP [_at]
   shape FROM THE START (SpecSysMknodAUEra / FsAbsMknodFire: the frozen
   dv_half walk-pre made the original unsealable, and the astate-shaped
   commits proved non-give-backable against [InodeRegion.ftop_body]) --
   plus SpecSysReadAU.v (the single-phase whole-[anode] observation) and
   SpecSysWriteAU.v (the delta vocabulary, the exclusion-by-premise
   pattern).

   THE DRIVING CONSUMER is xv6's init.c: [open("console", O_RDWR)],
   called twice in init's preamble -- the PLAIN (no-O_CREATE) arm opening
   a DEVICE.  That arm is this file's primary surface; the O_CREATE arm
   and the file/dir arms complete it in the family mold.

   ==== WHAT THIS CONTRACT IS ==========================================

   A PARALLEL FORM beside [SpecSysOpen.wp_sys_open_sconf] (R10: the
   landed contract does not move).  Same calling convention, same ambient
   premises, same threaded resources -- INCLUDING the landed descriptor
   story verbatim: the LEAST free descriptor ([SpecFdalloc.fd_frees]),
   the fd-state fragment bundle ([FdSlots.fd_frags_any]) in, and the
   retype at [ProcInv.proc_priv_settle].  What is NEW: the caller hands
   in commit steps fired at the syscall's linearization instants against
   the ONE abstract state, the postcondition ties the returned a0 to the
   values OBSERVED at those instants, and the success arm SHARPENS the
   landed bundle return to [fd_frags] at an EXPLICIT state list whose row
   at the new descriptor is typed -- [FdOpen rb wb (FdDevice ma)] on the
   device arm, [FdOpen rb wb (FdInode i)] on the file/dir/create arms
   ([FdSlots]: [FdDevice] carries its major, [FdInode] its inum, the two
   mode booleans ride [FdOpen]).  [proc_priv_settle]'s payout IS the
   typed row; [open_fd_frags_any] ties the sharpened post back to the
   landed shape.

   TWO SEALED FORMS, keyed by the O_CREATE bit AS A PREMISE (the
   exclusion-by-premise pattern: omode is the caller's own trapframe
   argument, so the split costs a caller nothing):

   - [wp_sys_open_au_plain]  ([om_create vom = false], the init arm):
     the walk premise covers the FULL path -- open resolves the whole
     path via namei, not nameiparent -- and the terminal node is observed
     by a single-phase read-only commit.  NOTHING MUTATES at the abstract
     layer on this surface EXCEPT the one conditional delta below.
   - [wp_sys_open_au_create] ([om_create vom = true]): create's surface
     at [ty = T_FILE] -- the walk premise is [FsAbsEraMknod]'s parent-
     prefix one-shot VERBATIM, the success commit is
     [FsAbsMknodFire.acre_commit_at] at the child [AFile []]
     ([SpecSysMknodAU.delta_create] reused, type-parameterized as it was
     built to be), and the exists-lookup rides [dlookup_commit_at].  The
     EXISTS arm does not fail: xv6's open(O_CREATE) on an existing FILE
     or DEVICE opens it ([SpecCreate]'s ARM F-OK: [ty = T_FILE] and
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
   consumable by BOTH the absolute era walks landed today and the
   relative-start arm the concurrent walk lane is building.  NO ESCAPE
   DISJUNCT rides the success arms (contrast [SpecSysMknodAUEra]'s
   ret-0 escape): init's own path is the RELATIVE "console", so an
   absolute-only escape would gut the driving consumer -- the relative
   walk consumption is instead RECORDED as the prover's dependency
   (item 1 below), and when that lane lands nothing here moves.

   ==== THE ONE DELTA (correcting doc section 7's no-CREATE row) ========

   The no-CREATE surface has exactly ONE delta: [(omode & O_TRUNC) &&
   ip->type == T_FILE] runs itrunc, a real mutation the doc's row elides.
   It fires ONLY on the file success arm -- devices are excluded by the
   type test itself (even with O_TRUNC set), directories never reach it
   (the O_RDONLY guard), and every failure arm returns before it runs.

   [delta_trunc] is MINTED, in [SpecSysWriteAU.delta_write]'s total-
   function mold, because the write delta cannot express truncation:
   [blk_splice] never shrinks ([delta_write_no_shrink] below is the
   machine-checked justification for the mint).  The commit
   [atrunc_commit_at] is the two-phase [_at] mold at that delta.  The
   file+O_TRUNC arm's receipt carries the OBSERVED-ROW TIE: the trunc
   fired at a state whose row at [i] still held the observed bytes --
   priced on the machine, not free: the observation and itrunc happen
   inside ONE ilock hold (ilock ... tests ... filealloc/fdalloc ...
   itrunc ... iunlock; filealloc's ftable lock is a spinlock, nothing
   sleeps holding the inode unlocked), and the prover's payload custody
   ([IcacheEscrow.ic_loaded]'s whole [top_frag]) pins the authority's row
   across the window.  On the CREATE-fresh arm the child is [AFile []]
   and itrunc's delta is the IDENTITY ([delta_trunc_nil]); the commit is
   REFUNDED there rather than fired vacuously.

   ==== THE ARMS, AGAINST SpecSysOpen's EIGHT ==========================

   ret = fd (the least free descriptor, [fd_frees]'s head, a0 = its
   zero-extension) -- plain form, keyed by the observed [anode]:
     DEVICE  the row is [ADev ma mi], [0 <= ma <= NDEV_max] ASSERTED
             (the +0x?? [lhu]+[bltu] single unsigned compare: NDEV_max =
             NDEV - 1 = 9 is the landed spelling, ConsoleInv), fragment
             typed [FdDevice ma], trunc commit refunded.
     FILE    the row is [AFile bs0]; fragment [FdInode i]; the trunc
             receipt iff [om_trunc vom] (above), the commit back
             otherwise.
     DIR     ONLY at [om_arg vom = 0] -- the C compares the WHOLE omode
             int against O_RDONLY, not a bit -- so the fragment is
             [FdOpen true false (FdInode i)]: the landed contract's
             writable-fd-is-not-a-directory theorem ([SpecSysOpen]'s
             header: [FileInvDefs.inode_pay_alloc] demands
             [wr = true -> ty <> T_DIR], and the +0xf6 test is where it
             is paid) holds here BY THE ARM'S OWN KEY ([om_rdonly_modes]).
   ret = fd, create form: FRESH (the fused delta fired at the entry
   write; [cre_pre] restated purely; unfired commits refunded) or
   EXISTS-OPENS (the exists observation fired, then the terminal
   observation on the FOUND node -- an [AFile] or [ADev] split, never
   [ADir], per F-OK).
   ret = -1 -- the honest fold of the landed blanket, residue returned
   per arm; the value does not say which arm fired (DETERMINISM: none,
   the landed stance):
     (i)   nothing fs-visible happened (argstr failed): the whole AU
           bundle comes back unspent;
     (ii)  the walk died at hop [k]: the era refund shape, both/all
           commits back;
     (iii) the walk completed and open failed past it.  PLAIN: the
           observation HAS fired (every post-walk failure -- the
           dir-with-write-mode test, the bad major, the two table-full
           arms -- sits inside the child's lock window, so the fire
           point always exists) and its receipt is delivered; the trunc
           commit back.  CREATE: three-way -- (a) create SUCCEEDED FRESH
           and open failed past it (table full): the delta STANDS and
           [Φok] is delivered -- the fs mutation of a failed open is
           real and this spec says so; (b) the name existed: [Φex]
           delivered (found DIR = ARM F-BAD, found DEVICE with a bad
           major, or table full past a good found node), the terminal
           observation fired OR refunded (the F-BAD instant is inside
           create, where forcing the fire would charge the create-AU
           carry; mknod's precedent); (c) nothing observed (the nlink
           guard, out of inodes, dirlink failure, the empty-final-name
           path "/"): everything back.

   ==== WHAT IT DELIBERATELY DOES NOT SAY ==============================

   NOTHING ABOUT DURABILITY (doc section 5's discipline; the only delta
   on either surface is O_TRUNC's and create's, both instances of
   SNAPSHOT like every other).  NOTHING about the OFFSET CELL: the new
   descriptor's [f->off = 0] lives in [fcontent] behind [file_ref] with
   no client-facing carrier (lane A item (iv), the offset seam -- this
   contract is that seam's THIRD consumer).  NOTHING about user memory
   (the fetched path is existential, SpecFetchstr's stance).  NOTHING
   about create's intermediate states (the minted orphan is observable;
   SpecSysMknodAU's honesty stance inherited wholesale, [cre_pre]'s
   freshness shape included).  And NO STABLE COROLLARY -- deliberately
   ABSENT rather than sealed vacuous: the mknod prover showed the
   frozen-shape stable forms are underivable as stated (the era/_at
   stable story is a dedicated follow-on), and this family does not
   author vacuous statements.  The agreement seeds ([_pinned]) are
   provided so that follow-on is assembly, not proof.

   ==== WHAT THE PROVER OWES ===========================================

   1. THE WALK CONSUMPTION.  Plain form: the era NAMEI walk
      ([SpecNameiEra.wp_namei_era]) fired at [open_walk_pre_era]'s
      one-shot -- ABSOLUTE fetches only today; the RELATIVE start is the
      concurrent walk lane's deliverable and this contract's recorded
      dependency (the premise shape already quantifies the start, so
      nothing here moves when it lands).  Create form: a create-AU carry
      at [ty = T_FILE] -- [SpecCreateAU] is T_DEVICE-pinned (its header,
      difference (2)), so the prover owes the general-[ty] (or a
      T_FILE-pinned sibling) carry; the walk side is
      [SpecNparWrapEra] + [FsAbsNparMknod.np_pre_of_mknod] as for mknod.
   2. THE TERMINAL FIRE: [aopen_commit_at] fired inside the child's lock
      window off the firing function's own [top_frag] (no walk lend
      involved) -- [FsAbsMknodFire.mkf_dlookup_fire]'s pattern with the
      row read whole; a mkf-style fire lemma is a short leaf in that
      file's mold.
   3. THE TRUNC FIRE: [atrunc_commit_at]'s two phases around itrunc's
      record update inside its transaction ([ftopN] critical section,
      [inode_local] give-back), the reading bridge (the truncated record
      reads [AFile []] -- the zero-size [fn_file_bytes] -- through
      [SpecSysMknodAU.abs_view_insert]), and the observed-row tie via
      the lock-hold custody (header, THE ONE DELTA).
   4. THE FD BOOKKEEPING: sys_open's landed proof already runs
      [proc_priv_settle]; restate its payout through
      [FdSlots.fd_frags_acc] to the explicit-[sts] post
      ([open_fd_ok]'s shape), and relay [fd_frees]'s head fact.
   5. THE MODE-BIT TIES: the machine's andi/branch tests against the
      [om_*] readings (bits 0/1/9/10 of the argint'd low int), and the
      whole-int O_RDONLY equality at the dir test.
   6. THE MAJOR BOUND: the [lhu]+[bltu] single unsigned compare to
      [0 <= ma <= NDEV_max] (a negative short zero-extends past 9;
      [SpecSysOpen]'s header prices it as ONE branch).
   7. THE F-OK BRIDGE: [SpecCreate]'s found-arm facts into the
      exists-opens sub-arms' [AFile]/[ADev] split (a found [ADir] is
      refuted by F-OK's type disjunction).

   ==== OPEN QUESTIONS FOR THE OWNER ===================================

   1. The -1 fold's observation asymmetry: the PLAIN form REQUIRES the
      fired receipt on every post-walk failure (the lock window always
      exists), the CREATE form's (b) allows a refund (the F-BAD instant
      is inside create).  Tighten (b) to fired-only at the cost of a
      fatter create-AU carry, or relax the plain form to match?
   2. The trunc receipt's observed-row tie (⌜av' !! i = the observed
      row⌝) is priced on the lock-hold custody argument.  If the prover
      finds it heavy, the fallback is a fully existential pre-row --
      say now or at the walk?
   3. The fresh+O_TRUNC arm REFUNDS the trunc commit (identity delta,
      [delta_trunc_nil]) rather than firing it vacuously -- confirm.
   4. The commit mask floor [∅]: mknod's ruling inherited; confirm no
      first consumer needs its own invariant open at an instant.

   ==== INIT'S INSTANTIATION (the driving consumer), in two lines ======

   [open("console", O_RDWR)]: [vom = 2] -- [om_rdwr_modes] +
   [om_rdwr_plain] put it on the PLAIN form at [rb = wb = true] -- and
   the fetched path is the RELATIVE "console", exercising the quantified
   start at init's cwd (the root); the DEVICE arm lands at [ma = 1]
   (CONSOLE) and the receipt types fd 0 / fd 1 as
   [FdOpen true true (FdDevice 1)] beside [fd_frees = 0 :: _] / [1 :: _].

   BINDERS: one instance path per scope -- [fileG] is bound and
   [icacheG]/[icfg] resolve only through its fields (the SpecCreate
   header's argument, inherited); the FsAbs carriers resolve their
   [fsTopG]/[fsLinkG] through [xv6G]'s fields; [GenId] is bound because
   the arms carry [proc_priv] (SpecSysOpen's own section note).  The
   live Γ is [FsBytesGamma.fs_gamma_L fsc_fs]; its gname tie to
   [ftop_body]'s authority is definitional ([FsAbs.ftop_gamma_top]). *)
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
Require Import IcacheRef.
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
Require Import SpecCreate.      (* [create_slots]; the F-OK facts *)
Require Import ConsoleInv.      (* [NDEV_max] *)
Require Import SpecSysOpen.     (* the landed contract this file states a
                                   parallel form beside; [K_sys_open],
                                   [sys_open_slots] *)
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
Require Import SpecSysWriteAU.  (* [delta_write] + the splice algebra the
                                   mint justification below is cut from *)
Require Import FsAbsEra.        (* [elend]: the era lend the hops fire *)
Require Import FsAbsEraMknod.   (* [mknod_walk_pre_era], [mknod_walk_dead_era]
                                   -- the parent-prefix one-shot, REUSED *)
Require Import FsAbsMknodFire.  (* [acre_commit_at], [dlookup_commit_at],
                                   [mkf_auth_nview] *)
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

(* THE DELTA: the file's bytes become empty; nlink untouched.  Total on
   purpose -- applied where the row is not an [AFile] it is the identity;
   the side condition lives in the commit's premise, not in the function
   (the family rule). *)
Definition delta_trunc `{XI : CurCtx} (i : Z) (av : aview) : aview :=
  match av !! i with
  | Some a =>
      match an_node a with
      | AFile _ => <[i := MkAnode (AFile []) (an_nlink a)]> av
      | _ => av
      end
  | None => av
  end.

(* the delta's row algebra *)
Lemma delta_trunc_file `{XI : CurCtx} (av : aview) (i : Z) (bs0 : list (bv 8))
    (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  delta_trunc i av = <[i := MkAnode (AFile []) nl]> av.
Proof. intros Hi. rewrite /delta_trunc Hi //=. Qed.

Lemma delta_trunc_lookup `{XI : CurCtx} (av : aview) (i : Z) (bs0 : list (bv 8))
    (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  delta_trunc i av !! i = Some (MkAnode (AFile []) nl).
Proof.
  intros Hi. rewrite (delta_trunc_file av i bs0 nl Hi) lookup_insert //.
Qed.

Lemma delta_trunc_other `{XI : CurCtx} (av : aview) (i j : Z) :
  j <> i -> delta_trunc i av !! j = av !! j.
Proof.
  intros Hj. rewrite /delta_trunc.
  destruct (av !! i) as [a |]; [| done].
  destruct (an_node a) as [bs | ents | ma mi]; [| done | done].
  rewrite lookup_insert_ne //.
Qed.

(* truncating an EMPTY file is the identity -- why the CREATE-fresh arm
   refunds the trunc commit instead of firing it vacuously (header) *)
Lemma delta_trunc_nil `{XI : CurCtx} (av : aview) (i : Z) (nl : nat) :
  av !! i = Some (MkAnode (AFile []) nl) -> delta_trunc i av = av.
Proof.
  intros Hi. rewrite (delta_trunc_file av i [] nl Hi).
  by rewrite (insert_id av i (MkAnode (AFile []) nl) Hi).
Qed.

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
  Definition aopen_commit_at `{XI : CurCtx} Γ (E : coPset)
      (Φ : aview -> Z -> anode -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (i : Z) (a : anode),
       ⌜abs_view I !! i = Some a⌝ -∗
       ghost_map_auth (γtop Γ) 1 I ={E}=∗
       ghost_map_auth (γtop Γ) 1 I ∗ Φ (abs_view I) i a)%I.

  (* the astate-shaped reading, for a client that reasons abstractly --
     the read-only direction holds ([FsAbsMknodFire]'s
     [dlookup_commit_at_weaken] argument, verbatim); the reverse does not
     (nothing ties the returned authority to the borrowed map), which is
     why the CONTRACT carries the [_at] form *)
  Definition aopen_commit `{XI : CurCtx} Γ (E : coPset)
      (Φ : aview -> Z -> anode -> iProp Σ) : iProp Σ :=
    (∀ (av : aview) (i : Z) (a : anode),
       ⌜av !! i = Some a⌝ -∗
       astate Γ av ={E}=∗ astate Γ av ∗ Φ av i a)%I.

  Lemma aopen_commit_at_weaken `{XI : CurCtx} Γ E Φ :
    aopen_commit_at Γ E Φ ⊢ aopen_commit Γ E Φ.
  Proof.
    iIntros "Hcm". rewrite /aopen_commit.
    iIntros (av i a) "%Hi Hst".
    iDestruct (astate_elim with "Hst") as (I) "[Ha %Hav]". subst av.
    iMod ("Hcm" $! I i a with "[//] Ha") as "[Ha HΦ]".
    iModIntro. iFrame "HΦ". iApply astate_intro. iExact "Ha".
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
       ⌜abs_view I !! i = Some (MkAnode (AFile bs0) nl)⌝ -∗
       ghost_map_auth (γtop Γ) 1 I ={E}=∗
       ghost_map_auth (γtop Γ) 1 I ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_trunc i (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) 1 I' ={E}=∗
            ghost_map_auth (γtop Γ) 1 I' ∗ Φ (abs_view I) i bs0))%I.

  Lemma atrunc_commit_at_unit `{XI : CurCtx} Γ E :
    ⊢ atrunc_commit_at Γ E (fun _ _ _ => True%I).
  Proof.
    rewrite /atrunc_commit_at. iIntros (I i bs0 nl) "%Hpre Ha".
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma atrunc_commit_at_pinned `{XI : CurCtx} Γ E (q : Qp) (jpin : Z) (b : anode)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ) :
    nview Γ q jpin b -∗
    (∀ (av : aview) (i : Z) (bs : list (bv 8)),
       ⌜av !! jpin = Some b⌝ -∗ nview Γ q jpin b -∗ Φ av i bs) -∗
    atrunc_commit_at Γ E Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /atrunc_commit_at.
    iIntros (I i bs0 nl) "%Hpre Ha".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
    iModIntro. iFrame "Ha". iIntros (I') "%Heq Ha'". iModIntro.
    iFrame "Ha'".
    iApply ("HΦ" $! (abs_view I) i bs0 with "[%] Hn"). done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2c.  The walk package (full path; the era hops; quantified start)   *)
  (* ------------------------------------------------------------------ *)

  (* ONE SHOT, instantiated by the walk at the string argstr fetched and
     at the inum it starts from -- [mknod_walk_pre_era]'s shape over the
     FULL element list (open resolves via namei, not nameiparent).  The
     start is QUANTIFIED with only the SLASH tie: an absolute fetch pins
     [FsImg.ROOTINO], a relative one starts at the cwd inode (header,
     THE WALK PREMISE). *)
  Definition open_walk_pre_era `{XI : CurCtx} (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ) : iProp Σ :=
    (∀ (pl : list (bv 8)) (r : Z),
       ⌜pl !! 0%nat = Some SLASH -> r = FsImg.ROOTINO⌝ ={⊤}=∗
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

  (* everything the PLAIN caller hands in, at the mask floor [∅] *)
  Definition open_au_pre_plain `{XI : CurCtx} Γ (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (open_walk_pre_era γfs P Pmiss
     ∗ aopen_commit_at Γ ∅ Φo
     ∗ atrunc_commit_at Γ ∅ Φt)%I.

  (* ...and the O_CREATE caller: the parent-prefix one-shot REUSED from
     the mknod era file, create's fused delta at the child [AFile []],
     the exists observation, and open's own two commits *)
  Definition open_au_pre_create `{XI : CurCtx} Γ (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (mknod_walk_pre_era γfs P Pmiss
     ∗ acre_commit_at Γ ∅ (AFile []) Φok
     ∗ dlookup_commit_at Γ ∅ Φex
     ∗ aopen_commit_at Γ ∅ Φo
     ∗ atrunc_commit_at Γ ∅ Φt)%I.

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
      (UW : ustate) (rb wb : bool) (t : fdtype) (r : mword 64) : iProp Σ :=
    (∃ (fd : nat) (l : list nat) (k : nat) (sts : list fdstate),
       ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
        /\ fd_frees (pv_ofile (us_V UW)) = fd :: l⌝ ∗
       ⌜sts !! fd = Some (FdOpen rb wb t)⌝ ∗
       proc_priv γf p pid (us_ofile UW fd (fnode k)) ∗
       fd_frags (pv_fdg (us_V UW)) sts)%I.

  (* ------------------------------------------------------------------ *)
  (*  2f.  The PLAIN arms                                                 *)
  (* ------------------------------------------------------------------ *)

  (* ret = fd: the walk completed at [i] (cursor over the FULL path), the
     terminal observation fired, and the arm is keyed by the observed
     [anode] (header, THE ARMS) *)
  Definition open_post_ok_plain `{XI : CurCtx} Γ (γf : gname) (p : mword 64)
      (pid : mword 32) (vom : mword 64)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (UW : ustate) (r : mword 64) : iProp Σ :=
    (∃ (pl : list (bv 8)) (av : aview) (i : Z),
       P (length (path_elems pl)) i ∗
       ((* DEVICE (the init arm): the major is in range, the fragment is
           [FdDevice ma], and O_TRUNC never applies *)
        (∃ (ma mi : Z) (nl : nat),
           ⌜av !! i = Some (MkAnode (ADev ma mi) nl)⌝ ∗
           ⌜0 <= ma <= NDEV_max⌝ ∗
           Φo av i (MkAnode (ADev ma mi) nl) ∗
           atrunc_commit_at Γ ∅ Φt ∗
           open_fd_ok γf p pid UW (om_readable vom) (om_writable vom)
             (FdDevice ma) r)
        ∨ (* FILE: the ONE delta of this surface, iff O_TRUNC -- the trunc
             fired at a state still holding the OBSERVED row (the
             lock-hold tie, header) *)
        (∃ (bs0 : list (bv 8)) (nl : nat),
           ⌜av !! i = Some (MkAnode (AFile bs0) nl)⌝ ∗
           Φo av i (MkAnode (AFile bs0) nl) ∗
           (if om_trunc vom
            then ∃ av' : aview,
                   ⌜av' !! i = Some (MkAnode (AFile bs0) nl)⌝ ∗
                   Φt av' i bs0
            else atrunc_commit_at Γ ∅ Φt) ∗
           open_fd_ok γf p pid UW (om_readable vom) (om_writable vom)
             (FdInode i) r)
        ∨ (* DIRECTORY, at O_RDONLY exactly: the arm's own key is what
             pays the writable-fd-is-not-a-directory theorem here
             ([om_rdonly_modes]) *)
        (∃ (ents : gmap fname Z) (nl : nat),
           ⌜av !! i = Some (MkAnode (ADir ents) nl)⌝ ∗
           ⌜om_arg vom = 0⌝ ∗
           Φo av i (MkAnode (ADir ents) nl) ∗
           atrunc_commit_at Γ ∅ Φt ∗
           open_fd_ok γf p pid UW true false (FdInode i) r)))%I.

  (* ret -1: the header's three-way fold, residue returned per arm.  The
     third disjunct's observation is FIRED, not optional: every post-walk
     failure sits inside the child's lock window. *)
  Definition open_post_fail_plain `{XI : CurCtx} Γ (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (open_au_pre_plain Γ γfs P Pmiss Φo Φt
     ∨ (∃ pl : list (bv 8),
          (open_walk_dead_era γfs P Pmiss pl
             ∗ aopen_commit_at Γ ∅ Φo
             ∗ atrunc_commit_at Γ ∅ Φt)
          ∨ (∃ i : Z,
               P (length (path_elems pl)) i
               ∗ (∃ (av : aview) (a : anode),
                    ⌜av !! i = Some a⌝ ∗ Φo av i a)
               ∗ atrunc_commit_at Γ ∅ Φt)))%I.

  (* the armed disjunction the continuation receives, keyed on a0, with
     the landed post's fd-side bundle folded in per arm ([fd_frags_any]
     back untouched on failure -- no arm that installed a descriptor can
     fail after doing so -- and [fd_slot] back on every arm) *)
  Definition open_arms_plain `{XI : CurCtx} Γ (γfs : fs_names) (γf : gname)
      (p : mword 64) (pid : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (UW : ustate) (r : mword 64) : iProp Σ :=
    (((⌜r = (mword_of_int (-1) : mword 64)⌝
       ∗ proc_priv γf p pid UW
       ∗ fd_frags_any (pv_fdg (us_V UW))
       ∗ open_post_fail_plain Γ γfs P Pmiss Φo Φt)
      ∨ open_post_ok_plain Γ γf p pid vom P Φo Φt UW r)
     ∗ fd_slot)%I.

  (* ------------------------------------------------------------------ *)
  (*  2g.  The O_CREATE arms                                              *)
  (* ------------------------------------------------------------------ *)

  (* ret = fd: FRESH (the fused delta fired at the entry write; the
     terminal observation and the trunc commit refunded -- the child is
     [AFile []] and itrunc's delta is the identity) or EXISTS-OPENS (the
     exists observation fired at the parent, then the terminal
     observation on the FOUND node -- [AFile] or [ADev] only, per
     SpecCreate's F-OK) *)
  Definition open_post_ok_create `{XI : CurCtx} Γ (γf : gname) (p : mword 64)
      (pid : mword 32) (vom : mword 64)
      (P : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (UW : ustate) (r : mword 64) : iProp Σ :=
    (∃ (pl : list (bv 8)) (d i : Z) (nm : fname),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       P (length (mknod_parent_elems pl)) d ∗
       ((* FRESH *)
        (∃ (av : aview) (ents : gmap fname Z) (nl : nat),
           ⌜cre_pre av d nm ents nl i (AFile [])⌝ ∗
           ⌜0 < i < 16 * Z.of_nat icfg_nib⌝ ∗
           Φok av d nm i ∗
           dlookup_commit_at Γ ∅ Φex ∗
           aopen_commit_at Γ ∅ Φo ∗
           atrunc_commit_at Γ ∅ Φt ∗
           open_fd_ok γf p pid UW (om_readable vom) (om_writable vom)
             (FdInode i) r)
        ∨ (* EXISTS-OPENS *)
        (∃ (avx : aview) (entsx : gmap fname Z) (nlx : nat),
           ⌜avx !! d = Some (MkAnode (ADir entsx) nlx)⌝ ∗
           ⌜entsx !! nm = Some i⌝ ∗
           Φex avx d nm i ∗
           acre_commit_at Γ ∅ (AFile []) Φok ∗
           (∃ (av : aview) (nl : nat),
              ((* the found node is a FILE *)
               (∃ bs0 : list (bv 8),
                  ⌜av !! i = Some (MkAnode (AFile bs0) nl)⌝ ∗
                  Φo av i (MkAnode (AFile bs0) nl) ∗
                  (if om_trunc vom
                   then ∃ av' : aview,
                          ⌜av' !! i = Some (MkAnode (AFile bs0) nl)⌝ ∗
                          Φt av' i bs0
                   else atrunc_commit_at Γ ∅ Φt) ∗
                  open_fd_ok γf p pid UW (om_readable vom)
                    (om_writable vom) (FdInode i) r)
               ∨ (* ...or a DEVICE (F-OK admits it; the major test still
                    stands between it and the fd) *)
               (∃ ma mi : Z,
                  ⌜av !! i = Some (MkAnode (ADev ma mi) nl)⌝ ∗
                  ⌜0 <= ma <= NDEV_max⌝ ∗
                  Φo av i (MkAnode (ADev ma mi) nl) ∗
                  atrunc_commit_at Γ ∅ Φt ∗
                  open_fd_ok γf p pid UW (om_readable vom)
                    (om_writable vom) (FdDevice ma) r))))))%I.

  (* ret -1: the fold.  Note arm (a): a FRESH create that succeeded
     before open's table-full failure leaves its delta STANDING, and the
     receipt is delivered -- the fs mutation of a failed open is real. *)
  Definition open_post_fail_create `{XI : CurCtx} Γ (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (open_au_pre_create Γ γfs P Pmiss Φok Φex Φo Φt
     ∨ (∃ pl : list (bv 8),
          (mknod_walk_dead_era γfs P Pmiss pl
             ∗ acre_commit_at Γ ∅ (AFile []) Φok
             ∗ dlookup_commit_at Γ ∅ Φex
             ∗ aopen_commit_at Γ ∅ Φo
             ∗ atrunc_commit_at Γ ∅ Φt)
          ∨ (∃ d : Z,
               P (length (mknod_parent_elems pl)) d
               ∗ atrunc_commit_at Γ ∅ Φt
               ∗ ((* (a) create succeeded FRESH; open failed past it *)
                  (∃ (av : aview) (i : Z) (nm : fname)
                     (ents : gmap fname Z) (nl : nat),
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜cre_pre av d nm ents nl i (AFile [])⌝ ∗
                     ⌜0 < i < 16 * Z.of_nat icfg_nib⌝ ∗
                     Φok av d nm i
                     ∗ dlookup_commit_at Γ ∅ Φex
                     ∗ aopen_commit_at Γ ∅ Φo)
                  ∨ (* (b) the name existed: found DIR (F-BAD), a bad
                       found-device major, or table full past a good
                       found node; -1 does not say which *)
                  (∃ (av : aview) (i : Z) (nm : fname)
                     (ents : gmap fname Z) (nl : nat),
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
                     ⌜ents !! nm = Some i⌝ ∗
                     Φex av d nm i
                     ∗ acre_commit_at Γ ∅ (AFile []) Φok
                     ∗ (aopen_commit_at Γ ∅ Φo
                        ∨ (∃ (av' : aview) (a : anode),
                             ⌜av' !! i = Some a⌝ ∗ Φo av' i a)))
                  ∨ (* (c) nothing observed: the nlink guard, out of
                       inodes, dirlink failure, "/" *)
                  (acre_commit_at Γ ∅ (AFile []) Φok
                   ∗ dlookup_commit_at Γ ∅ Φex
                   ∗ aopen_commit_at Γ ∅ Φo)))))%I.

  Definition open_arms_create `{XI : CurCtx} Γ (γfs : fs_names) (γf : gname)
      (p : mword 64) (pid : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (UW : ustate) (r : mword 64) : iProp Σ :=
    (((⌜r = (mword_of_int (-1) : mword 64)⌝
       ∗ proc_priv γf p pid UW
       ∗ fd_frags_any (pv_fdg (us_V UW))
       ∗ open_post_fail_create Γ γfs P Pmiss Φok Φex Φo Φt)
      ∨ open_post_ok_create Γ γf p pid vom P Φok Φex Φo Φt UW r)
     ∗ fd_slot)%I.

End SysOpenAU.

(* big-op bodies behind definitions: seal them, or an [iFrame] near a
   consumer resolves instances through the whole hop family
   (durable-notes; optimization.md, "a big-op body is the predictor").
   The three commits are match-free single wands and stay transparent,
   as the family's do. *)
Global Typeclasses Opaque open_walk_pre_era open_walk_dead_era
  open_au_pre_plain open_au_pre_create open_fd_ok
  open_post_ok_plain open_post_fail_plain open_arms_plain
  open_post_ok_create open_post_fail_create open_arms_create.

(* ===================================================================== *)
(*  3.  THE MACHINE CONTRACT: SpecSysOpen's frame + the AU                *)
(* ===================================================================== *)

(* THE SHARED FRAME: [SpecSysOpen.wp_sys_open_sconf_body]'s premises and
   threaded resources VERBATIM (R10 -- the landed contract's calling
   convention, not a new one), abstracted over the AU-side extras: the
   caller's bundle [EXTRA] and the armed post [ARMS] on the final ustate
   and the returned a0 -- which REPLACES the landed [sys_open_post]
   (each arm carries the same descriptor story, so the landed post is
   implied through [open_fd_frags_any]).  Both sealed forms below are
   this frame at their own bundle and arms. *)
Definition wp_sys_open_au_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} `{XI : CurCtx}
    (γfl γf : gname)   (* ftable lock + ghost, kalloc, printk *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (ns : nat)                                          (* the iref ledger     *)
    (dqb dqs dqbs dqn : dfrac)
    (v vom : mword 64)                       (* syscall arguments 0 and 1   *)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (EXTRA : iProp Σ) (ARMS : ustate -> mword 64 -> iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_open in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_open <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  bitmap_geom_ok fsc_cov fsc_logst fsc_bmapstart fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  1 < fsc_ninodes ->
  fsc_ninodes <= 16 * Z.of_nat icfg_nib ->
  fsc_ninodes < 2 ^ 31 ->
  16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
  printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
  (sys_open_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  eb = true ->
  pv_tf (us_V U) !! tf_arg_idx 0 = Some v ->
  pv_tf (us_V U) !! tf_arg_idx 1 = Some vom ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  printk_env fsc_printk fsc_uart fsc_disk -∗
  is_ftable γfl γf -∗
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  fs_crash_seam fsc_cov fsc_logst -∗
  gen_cert -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string <{ disk_res fsc_disk pd pav pu }> -∗
  bslots 3 -∗
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  ireg_open -∗
  sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  kalloc_env fsc_kalloc None -∗
  procs_inv gs -∗
  iref_slots ns -∗
  fd_slot -∗
  proc_priv γf pj pid U -∗
  fd_frags_any (pv_fdg (us_V U)) -∗
  (* ---- THE AU SIDE (the one addition to the landed premise list) ---- *)
  EXTRA -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (ns' : nat) (P' : uptd) (M' : gmap Z (bv 8)),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext (pv_upt (us_V U)) P'⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      bslots 3 -∗
      sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      ⌜ns' = ns⌝ -∗
      iref_slots ns' -∗
      (* the armed post on the final process state and the returned a0
         (implies the landed [sys_open_post]) *)
      ARMS (upd_usM (us_upt U P') M')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE PLAIN FORM (the init arm).  The abstract state is read at the LIVE
   Γ, [fs_gamma_L fsc_fs]; the mode readings are of the caller's own
   argument word, so the receipts speak about the omode IT passed.  The
   O_CREATE bit is excluded BY PREMISE (header: two sealed forms). *)
Definition wp_sys_open_au_plain_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} `{XI : CurCtx}
    (γfl γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v vom : mword 64)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φo : aview -> Z -> anode -> iProp Σ)
    (Φt : aview -> Z -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  om_create vom = false ->
  wp_sys_open_au_frame γfl γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v vom pid U m K eb b lks
    (open_au_pre_plain Γfs fsc_fs P Pmiss Φo Φt)
    (open_arms_plain Γfs fsc_fs γf (proc_addr j) pid vom P Pmiss Φo Φt).

(* THE O_CREATE FORM: create's surface at the child [AFile []]. *)
Definition wp_sys_open_au_create_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} `{XI : CurCtx}
    (γfl γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v vom : mword 64)
    (pid : mword 32) (U : ustate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
    (Φo : aview -> Z -> anode -> iProp Σ)
    (Φt : aview -> Z -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  om_create vom = true ->
  wp_sys_open_au_frame γfl γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v vom pid U m K eb b lks
    (open_au_pre_create Γfs fsc_fs P Pmiss Φok Φex Φo Φt)
    (open_arms_create Γfs fsc_fs γf (proc_addr j) pid vom P Pmiss
       Φok Φex Φo Φt).

(* ===================================================================== *)
(*  4.  THE SEAL                                                          *)
(* ===================================================================== *)

(* NO STABLE COROLLARY IS SEALED -- deliberately (header: WHAT IT
   DELIBERATELY DOES NOT SAY).  The mknod prover showed the frozen-shape
   stable forms are underivable as stated; the era/_at stable story is a
   dedicated follow-on, and this family does not author vacuous
   statements.  The [_pinned] seeds above are its raw material. *)
Module Type SYSOPEN_AU.
  Parameter wp_sys_open_au_plain :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γfl γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v vom : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ),
      wp_sys_open_au_plain_body γfl γf gs j gl pd pav pu ns
        dqb dqs dqbs dqn v vom pid U m K eb b lks P Pmiss Φo Φt.

  Parameter wp_sys_open_au_create :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γfl γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v vom : mword 64)
      (pid : mword 32) (U : ustate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ),
      wp_sys_open_au_create_body γfl γf gs j gl pd pav pu ns
        dqb dqs dqbs dqn v vom pid U m K eb b lks P Pmiss Φok Φex Φo Φt.
End SYSOPEN_AU.
