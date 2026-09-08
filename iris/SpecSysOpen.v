(* SpecSysOpen.v -- THE contract of sys_open(), stated independently of its
   proof.  Requires only the definitional layer, its callees' SPECS, the
   abstract-state vocabulary and the family's statement leaf
   ([SpecSysOpenAU]) -- never a whole-function proof file -- so every
   function proof can be checked in parallel.

     uint64 sys_open(void) {
       char path[MAXPATH];
       int fd, omode;
       struct file *f;
       struct inode *ip;
       int n;

       argint(1, &omode);
       if ((n = argstr(0, path, MAXPATH)) < 0) return -1;

       begin_op();

       if (omode & O_CREATE) {
         ip = create(path, T_FILE, 0, 0);
         if (ip == 0) { end_op(); return -1; }
       } else {
         if ((ip = namei(path)) == 0) { end_op(); return -1; }
         ilock(ip);
         if (ip->type == T_DIR && omode != O_RDONLY) {
           iunlockput(ip); end_op(); return -1;
         }
       }

       if (ip->type == T_DEVICE && (ip->major < 0 || ip->major >= NDEV)) {
         iunlockput(ip); end_op(); return -1;
       }

       if ((f = filealloc()) == 0 || (fd = fdalloc(f)) < 0) {
         if (f) fileclose(f);
         iunlockput(ip); end_op(); return -1;
       }

       if (ip->type == T_DEVICE) { f->type = FD_DEVICE; f->major = ip->major; }
       else                      { f->type = FD_INODE;  f->off = 0; }
       f->ip = ip;
       f->readable = !(omode & O_WRONLY);
       f->writable = (omode & O_WRONLY) || (omode & O_RDWR);

       if ((omode & O_TRUNC) && ip->type == T_FILE) itrunc(ip);

       iunlock(ip);
       end_op();
       return fd;
     }

   @ KernelSyms.sys_open, 342 bytes (CodeSysOpen.v).  A TWENTY-FOUR slot
   frame ([addi sp,sp,-192] at +0x00, [addi s0,sp,192] at +0x06), carved --
   numbering slots from the top, [pa_stk sp0 n] = sp0 - 8n:

     slot  1  (s0-8)    ra
     slot  2  (s0-16)   s0, the frame pointer (= the ENTRY sp)
     slot  3  (s0-24)   s1 = ip  -- saved LATE, at +0x28
     slot  4  (s0-32)   s2 = f   -- saved LATER, at +0x5e
     slot  5  (s0-40)   s3 = fd  -- saved LATER STILL, at +0x68
     slot  6  (s0-48)   dead
     slots 7..22        [char path[MAXPATH]] -- [addi a1,s0,-176]
     slot 23            [int omode] in its UPPER word, [s0-180]
     slot 24            dead (the frame's bottom)

   THE THREE REGISTER SAVES ARE SHRINK-WRAPPED, AND THAT MAKES THE FRAME
   CARVE ARM-DEPENDENT -- unlike sys_chdir's and sys_link's, where one
   [*_frame_join] serves every exit.  The prologue pushes only ra and s0;
   [c.sdsp s1,168] is at +0x28, AFTER the [argstr < 0] branch, [sd s2,160]
   at +0x5e after the T_DEVICE test, [sd s3,152] at +0x68 after filealloc
   succeeded.  The epilogue at +0xca restores only ra/s0, and every arm
   reloads exactly the subset it saved (+0xd8/+0x10a/+0x116 reload s1;
   +0x12e reloads s1+s2; +0x126 reloads s3 then falls into +0x12e; the
   success tail +0xc4 reloads all three).  ARM 0 never owns slot 5 at all.
   Nothing about [path] reaches this contract: it is carved out of
   [stack_own] with [StackBytes.slotsn_bytes_own].

   ==== ONE CONTRACT ====================================================

   [Module Type SYSOPEN] is sys_open's only seal.  Its body is the
   whole-function FRAME below plus ONE caller INPUT ([open_in]) and ONE
   armed OUTPUT ([open_arms]), BOTH KEYED THE WAY THE CODE KEYS: on
   [SpecSysOpenAU.om_create vom], the O_CREATE bit of the caller's own
   omode argument, which the machine tests with the [andi a5,a5,512] /
   [c.beqz] pair at +0x36.  On the [false] side the input is
   [open_au_pre_plain] and the output [open_arms_plain]; on the [true] side
   [open_au_pre_create] and [open_arms_create].  The two arm families are
   stated below in full.

   THE LANDED RETURN BLANKET [sys_open_post] IS A CONSEQUENCE, not a
   conjunct ([open_arms_landed], via [open_arms_plain_landed] /
   [open_arms_create_landed]).  It could not be a conjunct: unlike
   sys_write's blanket, which is a pure [Prop], [sys_open_post] CARRIES
   [proc_priv], the descriptor-state bundle and [fd_slot], and every arm
   already carries those -- conjoining it would demand them twice.

   THE TWO ARM STATEMENTS, [wp_sys_open_plain_body] and
   [wp_sys_open_create_body], are the one body at a DECIDED key: each takes
   [om_create vom = false] / [= true] as a premise and is otherwise
   [wp_sys_open_body] with the [if] reduced.  They are not sealed, not
   client-facing, and each has exactly ONE proof (ProofSysOpenAU.v's plain
   walk, ProofSysOpenAUFull.v's create walk); the seal's own lemma is the
   three-line [destruct] over them.  So there is one proof per arm and one
   contract for the syscall.

   ==== WHAT THE CALLER HANDS IN =======================================

   [SpecSysOpenAU]'s two bundles -- see that file's header for the walk
   premise's era shape, the two commits, and the ONE delta the no-O_CREATE
   surface has (O_TRUNC's).  The caller's predicates are the walk cursor
   [P]/[Pmiss], create's child legs [Φarm]/[Φun], create's two receipts
   [Φok]/[Φex], the terminal observation [Φo] and the trunc receipt [Φt];
   the plain side ignores the create four, which is what its bundle and
   arms say by not mentioning them.

   ==== WHAT THIS CONTRACT IS ABOUT =====================================

   sys_open is the tree's FIRST WRITER of [f->ip] and [f->off], and the only
   syscall that PUBLISHES a file payload out of an inode reference.  Two
   facts about that, because they are what the walk is:

   * THE [+1] INODE REFERENCE NEVER LEAVES.  create / namei hand back a
     reference, and instead of an [iput] the walk PARKS it in [f->ip] with
     [FileInvDefs.inode_pay_alloc]: the shed reference, the generation it
     names and that generation's [ity_shot] become the FD_INODE payload at
     fraction one.  That is the same ledger sentence as sys_chdir's
     [p->cwd], one descriptor further along -- which is why the success arm
     ends one iref unit short and the allowance below is spend-at-most
     rather than conserved.
   * THE WRITABLE-FD-IS-NOT-A-DIRECTORY WITNESS IS THE THEOREM OF THIS
     WALK.  [inode_pay_alloc] demands [wr = true -> ty <> T_DIR], and both
     arms discharge it FROM THE CODE: the O_CREATE arm passes T_FILE (and
     create's ok arm reports [di_type dn ∈ {T_FILE, T_DEVICE}]), while the
     else arm's test at +0xf6 forces [omode = O_RDONLY = 0] on any T_DIR
     inode, whence [f->writable = (omode & 1) || (omode & 3) = 0].  This is
     where filewrite's [DirView.dir_ok] obligation -- five frames up -- is
     actually paid.  In the arms below it holds BY THE DIR ARM'S OWN KEY
     ([om_rdonly_modes]).

   THE [major] BOUNDS CHECK IS ONE UNSIGNED TEST, NOT TWO.  The C is
   [ip->major < 0 || ip->major >= NDEV]; gcc emitted [lhu] + [bltu 9 <u a4].
   A negative [short] zero-extends to [>= 0x8000 > 9], so the single
   unsigned compare decides both disjuncts and the walk has ONE branch to
   price, not a short-circuit pair.  [NDEV_max = NDEV - 1 = 9] is the
   landed spelling (ConsoleInv).

   ==== THE ARMS ========================================================

   ret = fd (the least free descriptor, [fd_frees]'s head, a0 = its
   zero-extension) -- PLAIN side, keyed by the observed [anode]:
     DEVICE  the row is [ADev ma mi], [0 <= ma <= NDEV_max] ASSERTED,
             fragment typed [FdDevice ma], trunc commit refunded.
     FILE    the row is [AFile bs0]; fragment [FdInode i]; the trunc
             receipt iff [om_trunc vom], the commit back otherwise.
     DIR     ONLY at [om_arg vom = 0] -- the C compares the WHOLE omode
             int against O_RDONLY, not a bit -- so the fragment is
             [FdOpen true false (FdInode i)].
   ret = fd, CREATE side: FRESH (the fused delta fired at the entry write;
   [cre_pre] restated purely; unfired commits refunded) or EXISTS-OPENS
   (the exists observation fired, then the terminal observation on the
   FOUND node -- an [AFile] or [ADev] split, never [ADir], per F-OK).
   ret = -1 -- residue returned per arm; the value does not say which arm
   fired (DETERMINISM: none is claimed and none is available):
     (i)   nothing fs-visible happened (argstr failed): the whole bundle
           comes back unspent;
     (ii)  the walk died at hop [k]: the era refund shape, both/all
           commits back;
     (iii) the walk completed and open failed past it.  PLAIN: the
           observation HAS fired (every post-walk failure -- the
           dir-with-write-mode test, the bad major, the two table-full
           arms -- sits inside the child's lock window, so the fire point
           always exists) and its receipt is delivered; the trunc commit
           back.  CREATE: three-way -- (a) create SUCCEEDED FRESH and open
           failed past it (table full): the delta STANDS and [Φok] is
           delivered -- the fs mutation of a failed open is real and this
           spec says so; (b) the name existed: [Φex] delivered (found DIR
           = ARM F-BAD, found DEVICE with a bad major, or table full past
           a good found node), the terminal observation fired OR refunded
           (the F-BAD instant is inside create, where forcing the fire
           would charge the create-AU carry; mknod's precedent);
           (c) nothing observed (the nlink guard, out of inodes, dirlink
           failure, the empty-final-name path "/"): everything back.

   The success arms additionally TYPE the new descriptor's row --
   [FdOpen rb wb (FdDevice ma)] on the device arm, [FdOpen rb wb
   (FdInode i γo)] on the file/dir/create arms -- where the blanket leaves
   the type existential; [proc_priv_settle]'s payout IS the typed row.

   ==== THE REFERENCE LEDGER, AND WHY IT IS THREE ======================

   [create_slots] -- three, create's own -- goes in, and at most three come
   out spent.  The O_CREATE arm IS create, so its allowance is create's
   verbatim; the else arm's namei takes two and hands one back, and the
   third pays for the reference that ends up in [f->ip].  Every failure arm
   releases what it made ([iunlockput(ip)]), and the success arm keeps
   exactly one -- parked, as above.

   ==== THE LOG LEDGER CLOSES AT THREE, AND THE FLOOR IS THE WALK =======

   begin_op mints [LogInv.log_op g MAXOPBLOCKS] = ten units and end_op
   retires whatever is left, so nothing log-shaped crosses this interface.
   The whole ledger (machine-checked in [SysOpenBudget.v]) turns on what the
   two entry arms leave AT THE JOIN: the else arm leaves nine, and the
   O_CREATE arm can offer only [SpecCreate]'s [ok = true] FLOOR, which is
   [iput_units] = three -- exactly what each of ARMs D/E/F spends on its
   [iunlockput].  Without S6-mkdir's floor the create arm reaches the join
   with a bare [u' <= u] whose corner is zero: the floor is not a
   convenience for this walk, it is the walk ([so_create_nofloor_busts]).
   The COUNTED namei contract busts it at [L = 3] and leaves one where the
   join needs three ([so_counted_namei_busts]), so the SET form is forced
   here for sys_chdir's reason at a longer tail.

   The O_TRUNC tail is payable out of create's three with no credit, because
   [it_entry false u = S (S u)]: freeing a file's blocks costs two, every
   [bfree] hitting the one bitmap block and the tail flush the one inode
   block ([so_trunc_closes]).  sys_open could not supply a credit in any
   case -- create's post reports [Sb ⊆ Sb'] and never a membership.

   ==== THE FILE-TABLE LEDGER: ONE UNIT IN, ONE UNIT OUT ===============

   One [fd_slot] is the syscall's allowance.  filealloc CONSUMES it (the new
   reference has to live somewhere); fdalloc hands one back when it installs
   the descriptor (the descriptor's own unit); filealloc's failure arm hands
   it straight back, and ARM F-FAIL's [fileclose] hands it back after
   fdalloc refused.  So every one of the eight arms returns exactly one.

   ARM F-FAIL's extra [fileclose(f)] IS FREE, and that is
   [SpecFileclose.fileclose_env_none]'s doing: the file it closes is still
   FD_NONE ([SpecFilealloc]'s post pins the type), and fileclose's
   environment at FD_NONE is [emp].  pipealloc's reason, reused -- which is
   why no [fclose_names] and no closing environment appear below.

   ==== WHAT ITS CALLER MUST HOLD ======================================

   [eb = true] is create's and namei's premise, inherited verbatim.  The
   [trap_csrs_ext] / [cpu_claim_ext] complement is threaded anyway, and is
   [emp] there.

   THE CROSSING IS THE LITERAL [true]: this function sleeps in create, in
   namei, in ilock, in itrunc, in begin_op and in end_op, so it may return
   on a hart other than the one it was called on.

   THE BITMAP IS AN INVARIANT ([BitmapInv.bitmap_inv], inside [fs_ready]):
   create's dirlink can ALLOCATE and both the failure arms' iunlockputs and
   the O_TRUNC tail can FREE, and the contract says nothing about either.

   THE IMAGE DOES NOT MOVE.  This syscall only READS user memory (argstr,
   through fetchstr and copyinstr); the pages it faults in on the way were
   already in the block's view, as lazy pages reading 0, so vmfault does not
   move it either.  Only the DESCRIPTOR grows, and the block comes back at
   the image it was handed -- which is why the continuation's binders are
   [(mf, ns', P')] and the page-table report is the SIZED one
   ([uptd_ext_sz]).

   ==== NOTHING ABOUT DURABILITY =======================================

   No durable clause of any kind appears below (design/fs-syscall-specs.md
   section 5).  NO STABLE COROLLARY is sealed either: the era/[_at] stable
   story is a dedicated follow-on, and the agreement seeds
   ([SpecSysOpenAU]'s [_pinned] lemmas) are its raw material.

   BINDERS: one instance path per scope -- [fileG] is bound and
   [icacheG]/[icfg] resolve only through its fields (the SpecCreate
   header's argument, inherited); the FsAbs carriers resolve their
   [fsTopG]/[fsLinkG] through [xv6G]'s fields; [GenId] is bound because the
   arms carry [proc_priv].  The live Γ is [FsBytesGamma.fs_gamma_L fsc_fs];
   its gname tie to [ftop_body]'s authority is definitional
   ([FsAbs.ftop_gamma_top]). *)
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
Require Import VcGen.           (* [trunc32_unsigned], for the mode-bit tie *)
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
Require Import FileInv.               (* [is_ftable], [fnode] *)
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import ProcInv.
Require Import SpecPrintk.      (* [printk_env], [printk_gen_contract] *)
Require Import SpecDirlink.     (* [ic_sleeplocks], [ireg_blocks_ok] *)
Require Import SpecFdalloc.     (* [fd_frees] *)
Require Import SpecCreate.      (* [create_slots], the create arms and their
                                   T_FILE readings *)
Require Import ConsoleInv.      (* [NDEV_max] *)
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
Require Import FsAbsEraMknod.   (* [mknod_walk_pre_era], [mknod_walk_dead_era]
                                   -- the parent-prefix one-shot, REUSED *)
Require Import FsAbsMknodFire.  (* [acre_commit_at], [dlookup_commit_at] *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import SpecSysOpenAU.   (* THE STATEMENT LEAF: the omode readings,
                                   the two commits, the walk package, the
                                   two bundles, [open_fd_ok] *)
Require Import FsAbs.           (* LAST (FsAbs's own rule) *)
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* sys_open's own frame is 192 bytes -- TWENTY-FOUR slots ([addi sp,sp,-192]
   at +0x00) -- over its deepest callee, create (114).  Every other callee
   fits under that: namei 106, fileclose [8 + K_iput] = 68, iunlockput 64,
   argstr 60, end_op 58, itrunc 50, ilock 44, begin_op 26, iunlock 26,
   argint 18, filealloc 14, fdalloc 14. *)
Notation K_sys_open := (148%nat) (only parsing).
(* THE REFERENCE ALLOWANCE.  create's own, and for create's own reason; see
   the header's reference ledger. *)
Definition sys_open_slots : nat := create_slots.

(* ===================================================================== *)
(* THE TWO MODE FLAGS, AS FUNCTIONS OF omode.  These are xv6's own two      *)
(* lines, read at the argument rather than at the stored bytes:            *)
(*                                                                        *)
(*     f->readable = !(omode & O_WRONLY);                                  *)
(*     f->writable = (omode & O_WRONLY) || (omode & O_RDWR);               *)
(*                                                                        *)
(* with O_WRONLY = 0x001 and O_RDWR = 0x002 -- so READABLE is "bit 0       *)
(* clear" and WRITABLE is "bit 0 or bit 1 set", which is what the two      *)
(* [mod]s below say.  The post used to bind both booleans existentially;   *)
(* naming them here is what lets a caller of open KNOW whether the         *)
(* descriptor it just got back can be read or written, rather than only    *)
(* that it is open.                                                       *)
(* ===================================================================== *)
Definition so_rd_of (om : mword 32) : bool :=
  bool_decide (bv_unsigned om `mod` 2 = 0).
Definition so_wr_of (om : mword 32) : bool :=
  negb (bool_decide (bv_unsigned om `mod` 4 = 0)).

Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)
Section SpecSysOpen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{!ufdG Σ}.
  (* [GenId], for [ProcInv.proc_priv]'s own index: the private block now
     carries [FirstTok.first_tok], whose boot arm names [gen_cert].  The
     definitions below mention the block, so the section has to bind it. *)
  Context `{GEN : GenId}.

  (* sys_open's result, keyed by the returned a0, over the process state [W]
     the syscall ends with -- i.e. the incoming [V] with argstr's page-table
     growth already folded in (the continuation below does that with
     [upd_upt], so this predicate is purely about the DESCRIPTORS).

     Both arms hand the fd unit back: see the header's file-table ledger. *)
  (* THE BUNDLE MOVED INSIDE THE DISJUNCTION, and that is the whole of the
     sharpening.  It used to sit outside as [fd_frags_any], shared by every
     arm -- which is the only way to write it when the arms cannot say
     different things about the table.  They can now: the failure arms hand
     [sts] back on the nose, and the success arm hands back [sts] with ONE
     row replaced.

     THE MODE IS PINNED TO THE FLAGS; ONLY THE TYPE IS EXISTENTIAL.
     [f->readable] and [f->writable] are functions of the omode argument --
     xv6's own two lines, [so_rd_of] and [so_wr_of] above -- so a caller
     that passed [O_RDONLY] learns its descriptor READS and one that passed
     [O_WRONLY] learns its descriptor WRITES.  That is the difference
     between knowing a descriptor is open and knowing what it is for.

     THE TYPE STAYS EXISTENTIAL, and honestly so: it is [FdDevice] exactly
     when the path resolved to a T_DEVICE inode, which is a fact about the
     PATH WALK and not about the descriptor table.
     [SpecSysOpenAU.open_fd_ok] names it, because the AU frame observes the
     inode. *)
  Definition sys_open_post `{XI : CurCtx} (γf : gname) (p : mword 64) (pid : mword 32)
      (UW : ustate) (sts : list fdstate)
      (* the omode argument, as [argint] read it -- what the two mode bits
         are functions OF *)
      (om : mword 32)
      (r : mword 64) : iProp Σ :=
    ((* FAILURE, on any of the seven arms.  The descriptor array is EXACTLY
        as it came in: no arm that installed a descriptor can fail after
        doing so -- fdalloc is the last thing that can refuse.  The bundle
        comes back at the caller's own [sts]. *)
     (⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ proc_priv γf p pid UW ∗
        fd_frags (pv_fdg (us_V UW)) sts)
     ∨
     (* SUCCESS.  The LEAST free descriptor now names the new file, and the
        returned a0 is that descriptor.  Which file slot it is is
        existential: the file table is not the caller's to name.  The
        descriptor fdalloc opened is retyped from [FdClosed] to the new
        file's type ([ProcInv.proc_priv_settle]), and that ONE row is the
        only one that moves. *)
     (∃ (fd : nat) (l : list nat) (k : nat) (t : fdtype),
       ⌜r = (mword_of_int (Z.of_nat fd) : mword 64) /\
        fd_frees (pv_ofile (us_V UW)) = fd :: l /\
        (* ...AND THE SLOT WAS CLOSED.  fdalloc handed its authority back at
           [FdClosed] and the caller's own bundle yields the matching
           fragment, so this is one [FdSlots.fd_st_agree] inside the proof
           -- it is EXPOSED here because no caller can re-derive it, and
           without it the row licenses an open() that retypes a descriptor
           its caller is already holding.  [UserFd.ufd_open] is what needs
           it: minting a handle for the returned descriptor is an insert,
           and an insert needs the key free. *)
        sts !! fd = Some FdClosed⌝ ∗
       proc_priv γf p pid (us_ofile UW fd (fnode k)) ∗
       fd_frags (pv_fdg (us_V UW))
         (<[fd := FdOpen (so_rd_of om) (so_wr_of om) t]> sts)))
    ∗ fd_slot.

  (* THE LANDED SHAPE, DERIVED.  Callers that do not yet name their table --
     the dispatch arm, until [ProofSyscall.sysc_arm_pre] is indexed too --
     want the post as it used to be: the descriptor disjunction with the
     bundle beside it.  Forgetting the row is sound and one-directional,
     which is exactly the asymmetry [fd_frags_any] always had; keeping the
     weakening HERE, as a named lemma, means there is one place to delete
     when the last caller is updated. *)
  Lemma sys_open_post_any `{XI : CurCtx} (γf : gname) (p : mword 64)
      (pid : mword 32) (UW : ustate) (sts : list fdstate) (om : mword 32)
      (r : mword 64) :
    sys_open_post γf p pid UW sts om r ⊢
    ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ proc_priv γf p pid UW
      ∨ ∃ (fd : nat) (l : list nat) (k : nat),
          ⌜r = (mword_of_int (Z.of_nat fd) : mword 64) /\
           fd_frees (pv_ofile (us_V UW)) = fd :: l⌝ ∗
          proc_priv γf p pid (us_ofile UW fd (fnode k)))
     ∗ fd_frags_any (pv_fdg (us_V UW)) ∗ fd_slot).
  Proof.
    rewrite /sys_open_post /fd_frags_any.
    iIntros "[[(%Hr & Hp & Hb) | (%fd & %l & %k & %t & %Hpu & Hp & Hb)] Hfd]".
    - iFrame "Hfd". iSplitR "Hb"; [| by iExists sts].
      iLeft. by iFrame "Hp".
    - iFrame "Hfd". iSplitR "Hb";
        [| by iExists (<[fd := FdOpen (so_rd_of om) (so_wr_of om) t]> sts)].
      iRight. iExists fd, l, k. iFrame "Hp". iPureIntro.
      destruct Hpu as (Hr1 & Hfl1 & _). exact (conj Hr1 Hfl1).
  Qed.

End SpecSysOpen.

(* ===================================================================== *)
(*  THE ARMS.  Two families, one per side of the O_CREATE key.            *)
(* ===================================================================== *)

Section SysOpenArms.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  (* [GenId], because the arms carry [proc_priv] *)
  Context `{GEN : GenId}.
  Implicit Types Γ : fs_view_names Σ.

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
      (sts : list fdstate) (UW : ustate) (r : mword 64) : iProp Σ :=
    (∃ (pl : list (bv 8)) (av : aview) (i : Z),
       P (length (path_elems pl)) i ∗
       ((* DEVICE (the init arm): the major is in range, the fragment is
           [FdDevice ma], and O_TRUNC never applies *)
        (∃ (ma mi : Z) (nl : nat),
           ⌜arow_at av i (MkAnode (ADev ma mi) nl)⌝ ∗
           ⌜0 <= ma <= NDEV_max⌝ ∗
           Φo av i (MkAnode (ADev ma mi) nl) ∗
           atrunc_commit_at Γ appE Φt ∗
           open_fd_ok γf p pid UW (om_readable vom) (om_writable vom)
             (FdDevice ma) sts r)
        ∨ (* FILE: the ONE delta of this surface, iff O_TRUNC -- the trunc
             fired at a state still holding the OBSERVED row (the
             lock-hold tie, header) *)
        (∃ (bs0 : list (bv 8)) (nl : nat),
           ⌜arow_at av i (MkAnode (AFile bs0) nl)⌝ ∗
           Φo av i (MkAnode (AFile bs0) nl) ∗
           (if om_trunc vom
            then ∃ av' : aview,
                   ⌜arow_at av' i (MkAnode (AFile bs0) nl)⌝ ∗
                   Φt av' i bs0
            else atrunc_commit_at Γ appE Φt) ∗
           ∃ γo : gname,
             open_fd_ok γf p pid UW (om_readable vom) (om_writable vom)
               (FdInode i γo) sts r)
        ∨ (* DIRECTORY, at O_RDONLY exactly: the arm's own key is what
             pays the writable-fd-is-not-a-directory theorem here
             ([om_rdonly_modes]) *)
        (∃ (ents : gmap fname Z) (nl : nat),
           ⌜arow_at av i (MkAnode (ADir ents) nl)⌝ ∗
           ⌜om_arg vom = 0⌝ ∗
           Φo av i (MkAnode (ADir ents) nl) ∗
           atrunc_commit_at Γ appE Φt ∗
           ∃ γo : gname,
             open_fd_ok γf p pid UW true false (FdInode i γo) sts r)))%I.

  (* ret -1: the header's three-way fold, residue returned per arm.  The
     third disjunct's observation is FIRED, not optional: every post-walk
     failure sits inside the child's lock window. *)
  Definition open_post_fail_plain `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (open_au_pre_plain Γ γfs cw P Pmiss Φo Φt
     ∨ (∃ pl : list (bv 8),
          (open_walk_dead_era γfs P Pmiss pl
             ∗ aopen_commit_at Γ appE Φo
             ∗ atrunc_commit_at Γ appE Φt)
          ∨ (∃ i : Z,
               P (length (path_elems pl)) i
               ∗ (∃ (av : aview) (a : anode),
                    ⌜arow_at av i a⌝ ∗ Φo av i a)
               ∗ atrunc_commit_at Γ appE Φt)))%I.

  (* the armed disjunction the continuation receives, keyed on a0, with
     the landed post's fd-side bundle folded in per arm (the caller's
     [sts] back on the nose on failure, one row moved on success, and
     [fd_slot] back on every arm); [open_arms_plain_landed] below is the
     tie to [SpecSysOpen.sys_open_post] *)
  Definition open_arms_plain `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z) (γf : gname)
      (p : mword 64) (pid : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (sts : list fdstate) (UW : ustate) (r : mword 64) : iProp Σ :=
    (((⌜r = (mword_of_int (-1) : mword 64)⌝
       ∗ proc_priv γf p pid UW
       (* the failure arms hand the caller's table back ON THE NOSE: no
          arm that installed a descriptor can fail after doing so *)
       ∗ fd_frags (pv_fdg (us_V UW)) sts
       ∗ open_post_fail_plain Γ γfs cw P Pmiss Φo Φt)
      ∨ open_post_ok_plain Γ γf p pid vom P Φo Φt sts UW r)
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
      (Φarm Φun : aview -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (sts : list fdstate) (UW : ustate) (r : mword 64) : iProp Σ :=
    (∃ (pl : list (bv 8)) (d i : Z) (nm : fname),
       ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
       P (length (mknod_parent_elems pl)) d ∗
       ((* FRESH *)
        (∃ (av : aview) (ents : gmap fname Z) (nl : nat),
           ⌜cre_pre av d nm ents nl i (AFile [])⌝ ∗
           ⌜0 < i < 16 * Z.of_nat icfg_nib⌝ ∗
           Φok av d nm i ∗
           dlookup_commit_at Γ appE Φex ∗
           aopen_commit_at Γ appE Φo ∗
           atrunc_commit_at Γ appE Φt ∗
           (* the child's row APPEARED at this inum; the unarm comes home
              (round E2, lane E2-C) *)
           cre_arm_fired Φarm i ∗ aunarm_commit_at Γ appE Φun ∗
           ∃ γo : gname,
             open_fd_ok γf p pid UW (om_readable vom) (om_writable vom)
               (FdInode i γo) sts r)
        ∨ (* EXISTS-OPENS *)
        (∃ (avx : aview) (entsx : gmap fname Z) (nlx : nat),
           ⌜avx !! d = Some (MkAnode (ADir entsx) nlx)⌝ ∗
           ⌜entsx !! nm = Some i⌝ ∗
           Φex avx d nm i ∗
           acre_commit_at Γ appE (AFile []) Φok ∗
           (* the name was already there: create's child legs are whole *)
           cre_child_unfired Γ (AFile []) Φarm Φun ∗
           (∃ (av : aview) (nl : nat),
              ((* the found node is a FILE *)
               (∃ bs0 : list (bv 8),
                  ⌜arow_at av i (MkAnode (AFile bs0) nl)⌝ ∗
                  Φo av i (MkAnode (AFile bs0) nl) ∗
                  (if om_trunc vom
                   then ∃ av' : aview,
                          ⌜arow_at av' i (MkAnode (AFile bs0) nl)⌝ ∗
                          Φt av' i bs0
                   else atrunc_commit_at Γ appE Φt) ∗
                  ∃ γo : gname,
                    open_fd_ok γf p pid UW (om_readable vom)
                      (om_writable vom) (FdInode i γo) sts r)
               ∨ (* ...or a DEVICE (F-OK admits it; the major test still
                    stands between it and the fd) *)
               (∃ ma mi : Z,
                  ⌜arow_at av i (MkAnode (ADev ma mi) nl)⌝ ∗
                  ⌜0 <= ma <= NDEV_max⌝ ∗
                  Φo av i (MkAnode (ADev ma mi) nl) ∗
                  atrunc_commit_at Γ appE Φt ∗
                  open_fd_ok γf p pid UW (om_readable vom)
                    (om_writable vom) (FdDevice ma) sts r))))))%I.

  (* ret -1: the fold.  Note arm (a): a FRESH create that succeeded
     before open's table-full failure leaves its delta STANDING, and the
     receipt is delivered -- the fs mutation of a failed open is real. *)
  Definition open_post_fail_create `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φarm Φun : aview -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) : iProp Σ :=
    (open_au_pre_create Γ γfs cw P Pmiss Φarm Φun Φok Φex Φo Φt
     ∨ (∃ pl : list (bv 8),
          (mknod_walk_dead_era γfs P Pmiss pl
             ∗ acre_commit_at Γ appE (AFile []) Φok
             ∗ dlookup_commit_at Γ appE Φex
             ∗ aopen_commit_at Γ appE Φo
             ∗ atrunc_commit_at Γ appE Φt
             ∗ cre_child_unfired Γ (AFile []) Φarm Φun)
          ∨ (∃ d : Z,
               P (length (mknod_parent_elems pl)) d
               ∗ atrunc_commit_at Γ appE Φt
               ∗ ((* (a) create succeeded FRESH; open failed past it *)
                  (∃ (av : aview) (i : Z) (nm : fname)
                     (ents : gmap fname Z) (nl : nat),
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜cre_pre av d nm ents nl i (AFile [])⌝ ∗
                     ⌜0 < i < 16 * Z.of_nat icfg_nib⌝ ∗
                     Φok av d nm i
                     ∗ dlookup_commit_at Γ appE Φex
                     ∗ aopen_commit_at Γ appE Φo
                     (* the child's row APPEARED and STANDS *)
                     ∗ cre_arm_fired Φarm i ∗ aunarm_commit_at Γ appE Φun)
                  ∨ (* (b) the name existed: found DIR (F-BAD), a bad
                       found-device major, or table full past a good
                       found node; -1 does not say which *)
                  (∃ (av : aview) (i : Z) (nm : fname)
                     (ents : gmap fname Z) (nl : nat),
                     ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                     ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
                     ⌜ents !! nm = Some i⌝ ∗
                     Φex av d nm i
                     ∗ acre_commit_at Γ appE (AFile []) Φok
                     (* create's child legs: whole, or the do-then-undo
                        PAIR -- the fold does not separate the two here
                        (round E2, lane E2-C) *)
                     ∗ (cre_child_unfired Γ (AFile []) Φarm Φun
                        ∨ ∃ ic : Z, cre_child_pair Φarm Φun ic)
                     ∗ (aopen_commit_at Γ appE Φo
                        ∨ (∃ (av' : aview) (a : anode),
                             ⌜arow_at av' i a⌝ ∗ Φo av' i a)))
                  ∨ (* (c) nothing observed: the nlink guard, out of
                       inodes, dirlink failure, "/" *)
                  (acre_commit_at Γ appE (AFile []) Φok
                   ∗ dlookup_commit_at Γ appE Φex
                   ∗ aopen_commit_at Γ appE Φo
                   (* the guards and "out of inodes" fired nothing; a failed
                      [dirlink] fired the do-then-undo PAIR (ruling Q-h) *)
                   ∗ (cre_child_unfired Γ (AFile []) Φarm Φun
                      ∨ ∃ ic : Z, cre_child_pair Φarm Φun ic))))))%I.

  Definition open_arms_create `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z) (γf : gname)
      (p : mword 64) (pid : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φarm Φun : aview -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (sts : list fdstate) (UW : ustate) (r : mword 64) : iProp Σ :=
    (((⌜r = (mword_of_int (-1) : mword 64)⌝
       ∗ proc_priv γf p pid UW
       ∗ fd_frags (pv_fdg (us_V UW)) sts
       ∗ open_post_fail_create Γ γfs cw P Pmiss Φarm Φun Φok Φex Φo Φt)
      ∨ open_post_ok_create Γ γf p pid vom P Φarm Φun Φok Φex Φo Φt sts UW r)
     ∗ fd_slot)%I.

  (* ------------------------------------------------------------------ *)
  (*  2h.  The tie to the landed post                                     *)
  (* ------------------------------------------------------------------ *)

  (* THE MODE READINGS ARE THE LANDED ONES.  [SpecSysOpen.so_rd_of] /
     [so_wr_of] read the two mode bits off the argint'd word ([trunc32
     vom]); this file's [om_readable]/[om_writable] read the same bits
     off [om_arg vom].  One lemma says they are one function. *)
  Lemma om_arg_trunc32 `{XI : CurCtx} (v : mword 64) :
    bv_unsigned (trunc32 v) = om_arg v.
  Proof.
    rewrite trunc32_unsigned /om_arg /bv_wrap /bv_modulus.
    change (Z.of_N (MachineWord.MachineWord.Z_idx 32)) with 32. reflexivity.
  Qed.

  Lemma om_modes_landed `{XI : CurCtx} (v : mword 64) :
    so_rd_of (trunc32 v) = om_readable v
    /\ so_wr_of (trunc32 v) = om_writable v.
  Proof.
    rewrite /so_rd_of /so_wr_of /om_readable /om_writable /om_wronly /om_rdwr
      om_arg_trunc32.
    set (x := om_arg v).
    (* both bits as Euclidean arithmetic, then the four cases by computation *)
    rewrite (Z.testbit_eqb x 0); [| lia]. rewrite (Z.testbit_eqb x 1); [| lia].
    rewrite Z.pow_0_r Z.pow_1_r Z.div_1_r.
    pose proof (Z.div_mod x 2 ltac:(lia)) as Hd2.
    pose proof (Z.div_mod x 4 ltac:(lia)) as Hd4.
    pose proof (Z.div_mod (x `div` 2) 2 ltac:(lia)) as Hd22.
    pose proof (Z.mod_pos_bound x 2 ltac:(lia)) as Hb2.
    pose proof (Z.mod_pos_bound x 4 ltac:(lia)) as Hb4.
    pose proof (Z.mod_pos_bound (x `div` 2) 2 ltac:(lia)) as Hb22.
    assert (H4 : x `mod` 4 = x `mod` 2 + 2 * ((x `div` 2) `mod` 2)) by lia.
    assert (Hm2 : x `mod` 2 = 0 \/ x `mod` 2 = 1) by lia.
    assert (Hm2' : (x `div` 2) `mod` 2 = 0 \/ (x `div` 2) `mod` 2 = 1) by lia.
    clear Hd2 Hd4 Hd22 Hb2 Hb4 Hb22.
    rewrite H4.
    destruct Hm2 as [Hm2 | Hm2], Hm2' as [Hm2' | Hm2']; rewrite Hm2 Hm2';
      split; vm_compute; reflexivity.
  Qed.

  (* THE PLAIN ARMS IMPLY THE LANDED POST.  The receipts and the walk
     package are dropped, the typed row becomes the landed existential
     [t], and the modes are read through [om_modes_landed] (the dir arm's
     [true]/[false] through [om_rdonly_modes]).  This is what lets a
     consumer of [SpecSysOpen.sys_open_post] -- the dispatch -- run on the
     AU contract unchanged. *)
  Lemma open_fd_ok_landed `{XI : CurCtx} (γf : gname) (p : mword 64) (pid : mword 32)
      (UW : ustate) (rb wb : bool) (t : fdtype) (sts : list fdstate)
      (om : mword 32) (r : mword 64) :
    so_rd_of om = rb -> so_wr_of om = wb ->
    open_fd_ok γf p pid UW rb wb t sts r ⊢
      (∃ (fd : nat) (l : list nat) (k : nat) (t : fdtype),
         ⌜r = (mword_of_int (Z.of_nat fd) : mword 64) /\
          fd_frees (pv_ofile (us_V UW)) = fd :: l /\
          sts !! fd = Some FdClosed⌝ ∗
         proc_priv γf p pid (us_ofile UW fd (fnode k)) ∗
         fd_frags (pv_fdg (us_V UW))
           (<[fd := FdOpen (so_rd_of om) (so_wr_of om) t]> sts)).
  Proof.
    intros -> ->. rewrite /open_fd_ok.
    iIntros "H". iDestruct "H" as (fd l k) "(%Hpu & Hp & Hb)".
    iExists fd, l, k, t. iFrame "Hp Hb". iPureIntro. exact Hpu.
  Qed.

  Lemma open_arms_plain_landed `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z) (γf : gname)
      (p : mword 64) (pid : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (sts : list fdstate) (UW : ustate) (r : mword 64) :
    open_arms_plain Γ γfs cw γf p pid vom P Pmiss Φo Φt sts UW r ⊢
      sys_open_post γf p pid UW sts (trunc32 vom) r.
  Proof.
    destruct (om_modes_landed vom) as [Hrd Hwr].
    rewrite /open_arms_plain /open_post_ok_plain /sys_open_post.
    iIntros "[[(%Hr & Hp & Hb & _) | H] $]".
    - iLeft. by iFrame "Hp Hb".
    - iRight.
      iDestruct "H" as (pl av i) "(_ & [H | [H | H]])".
      + iDestruct "H" as (ma mi nl) "(_ & _ & _ & _ & H)".
        iApply (open_fd_ok_landed _ _ _ _ _ _ _ _ (trunc32 vom) with "H");
          [exact Hrd | exact Hwr].
      + iDestruct "H" as (bs0 nl) "(_ & _ & _ & H)". iDestruct "H" as (γo) "H".
        iApply (open_fd_ok_landed _ _ _ _ _ _ _ _ (trunc32 vom) with "H");
          [exact Hrd | exact Hwr].
      + iDestruct "H" as (ents nl) "(_ & %Hom & _ & _ & H)". iDestruct "H" as (γo) "H".
        destruct (om_rdonly_modes vom Hom) as [Hrd0 Hwr0].
        iApply (open_fd_ok_landed _ _ _ _ _ _ _ _ (trunc32 vom) with "H");
          [by rewrite Hrd Hrd0 | by rewrite Hwr Hwr0].
  Qed.

  Lemma open_arms_create_landed `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z) (γf : gname)
      (p : mword 64) (pid : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φarm Φun : aview -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (sts : list fdstate) (UW : ustate) (r : mword 64) :
    open_arms_create Γ γfs cw γf p pid vom P Pmiss Φarm Φun Φok Φex Φo Φt sts UW r ⊢
      sys_open_post γf p pid UW sts (trunc32 vom) r.
  Proof.
    destruct (om_modes_landed vom) as [Hrd Hwr].
    rewrite /open_arms_create /open_post_ok_create /sys_open_post.
    iIntros "[[(%Hr & Hp & Hb & _) | H] $]".
    - iLeft. by iFrame "Hp Hb".
    - iRight.
      iDestruct "H" as (pl d i nm) "(_ & _ & [H | H])".
      + iDestruct "H" as (av ents nl) "(_ & _ & _ & _ & _ & _ & _ & _ & H)".
        iDestruct "H" as (γo) "H".
        iApply (open_fd_ok_landed _ _ _ _ _ _ _ _ (trunc32 vom) with "H");
          [exact Hrd | exact Hwr].
      + iDestruct "H" as (avx entsx nlx) "(_ & _ & _ & _ & _ & H)".
        iDestruct "H" as (av nl) "[H | H]".
        * iDestruct "H" as (bs0) "(_ & _ & _ & H)". iDestruct "H" as (γo) "H".
          iApply (open_fd_ok_landed _ _ _ _ _ _ _ _ (trunc32 vom) with "H");
            [exact Hrd | exact Hwr].
        * iDestruct "H" as (ma mi) "(_ & _ & _ & _ & H)".
          iApply (open_fd_ok_landed _ _ _ _ _ _ _ _ (trunc32 vom) with "H");
            [exact Hrd | exact Hwr].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE ONE INPUT AND THE ONE OUTPUT, at the key the code branches on   *)
  (* ------------------------------------------------------------------ *)

  (* [om_create vom] is the O_CREATE bit of the caller's own omode
     argument; the machine reads it with the [andi a5,a5,512] / [c.beqz]
     pair at +0x36.  A caller that knows its own omode knows which side it
     is on and owes only that side's pieces. *)
  Definition open_in `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z)
      (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φarm Φun : aview -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ) : iProp Σ :=
    if om_create vom
    then open_au_pre_create Γ γfs cw P Pmiss Φarm Φun Φok Φex Φo Φt
    else open_au_pre_plain Γ γfs cw P Pmiss Φo Φt.

  Definition open_arms `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z)
      (γf : gname) (p : mword 64) (pid : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φarm Φun : aview -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (sts : list fdstate) (UW : ustate) (r : mword 64) : iProp Σ :=
    if om_create vom
    then open_arms_create Γ γfs cw γf p pid vom P Pmiss Φarm Φun Φok Φex
           Φo Φt sts UW r
    else open_arms_plain Γ γfs cw γf p pid vom P Pmiss Φo Φt sts UW r.

  (* THE RETURN BLANKET, READ OFF THE ARMS.  It is a consequence and not a
     second conjunct: [sys_open_post] carries [proc_priv], the
     descriptor-state bundle and [fd_slot], and each arm already carries
     all three -- so conjoining it would demand them twice (sys_write can
     conjoin its blanket only because that one is a pure [Prop]).  This is
     also what lets the dispatch consume [sys_open_post] unchanged. *)
  Lemma open_arms_landed `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z)
      (γf : gname) (p : mword 64) (pid : mword 32) (vom : mword 64)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φarm Φun : aview -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (sts : list fdstate) (UW : ustate) (r : mword 64) :
    open_arms Γ γfs cw γf p pid vom P Pmiss Φarm Φun Φok Φex Φo Φt sts UW r
    ⊢ sys_open_post γf p pid UW sts (trunc32 vom) r.
  Proof.
    rewrite /open_arms. destruct (om_create vom).
    - apply open_arms_create_landed.
    - apply open_arms_plain_landed.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  create's FAILURE FOLD, READ INTO THIS FILE'S OWN ARMS               *)
  (*                                                                      *)
  (*  [SpecCreate.cre_fail_arms] at [T_FILE] IS [open_post_fail_create]'s  *)
  (*  inner three, arm for arm, and the only thing the fold adds is        *)
  (*  sys_open's own two commits, which on every one of create's failure   *)
  (*  arms are still UNFIRED (create returned 0 and sys_open has not yet   *)
  (*  touched the child).  Stated as a wand taking those two so that the   *)
  (*  consumer's prover applies it with no case analysis at all.           *)
  (*                                                                      *)
  (*  Arm (a) -- a FRESH create that succeeded and an open that failed     *)
  (*  past it -- is unreachable from the failure fold by construction,     *)
  (*  because create returning 0 is exactly what that fold is the payout   *)
  (*  of.  sys_open builds (a) from the [made = true] arm at its OWN later *)
  (*  failures.  The SUCCESS correspondence is                            *)
  (*  [SpecCreate.cre_ok_arms_file] and its two projections; nothing of it *)
  (*  belongs here, since both of open's success disjuncts end in          *)
  (*  [open_fd_ok], which create never sees.                              *)
  (* ------------------------------------------------------------------ *)
  Lemma cre_fail_to_open `{XI : CurCtx} Γ (γfs : fs_names) (cw : Z)
      (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φarm : aview -> Z -> iProp Σ)
      (Φdots : aview -> Z -> Z -> bool -> iProp Σ)
      (Φun : aview -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ)
      (pl : list (bv 8)) :
    cre_fail_arms Γ γfs (bv_unsigned T_FILE) ma mi P Pmiss
      Φarm Φdots Φun Φok Φex pl -∗
    aopen_commit_at Γ appE Φo -∗
    atrunc_commit_at Γ appE Φt -∗
    open_post_fail_create Γ γfs cw P Pmiss Φarm Φun Φok Φex Φo Φt.
  Proof.
    iIntros "Hcf Ho Ht".
    iDestruct (cre_fail_arms_file with "Hcf") as "Hcf".
    rewrite /open_post_fail_create.
    iRight. iExists pl.
    iDestruct "Hcf" as "[(Hd & Hac & Hdl & Hcl) | Hr]".
    - iLeft. iFrame "Hd Hac Hdl Ho Ht Hcl".
    - iRight. iDestruct "Hr" as (d) "(HP & Hac & Hrest & Hcl)".
      iExists d. iFrame "HP Ht".
      iDestruct "Hrest" as "[Hfired | Hdl]".
      + (* (b): the name was there and the observation fired *)
        iRight. iLeft.
        iDestruct "Hfired" as (av i nm ents nl) "(%Hl & %Hrow & %Hent & HΦ)".
        iExists av, i, nm, ents, nl.
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iSplitR; [by iPureIntro |].
        iFrame "HΦ Hac".
        iSplitL "Hcl"; [iExact "Hcl" |].
        iLeft. iExact "Ho".
      + (* (c): nothing observed *)
        iRight. iRight. iFrame "Hac Hdl Ho Hcl".
  Qed.

End SysOpenArms.

(* big-op bodies behind definitions: seal them, or an [iFrame] near a
   consumer resolves instances through the whole hop family
   (durable-notes; optimization.md, "a big-op body is the predictor"). *)
Global Typeclasses Opaque open_post_ok_plain open_post_fail_plain
  open_arms_plain open_post_ok_create open_post_fail_create
  open_arms_create open_in open_arms.

(* ===================================================================== *)
(*  THE WHOLE-FUNCTION FRAME, abstracted over the caller's bundle and the *)
(*  armed post.  There is no second body: this frame is the only one, and *)
(*  the three bodies below instantiate it.                                *)
(* ===================================================================== *)

(* Abstracted over the two AU-side extras: the caller's bundle [EXTRA] and
   the armed post [ARMS] on the final ustate and the returned a0 -- which
   REPLACES the landed [sys_open_post] (each arm carries the same
   descriptor story, so the blanket is implied; see [open_arms_landed]). *)

Definition wp_sys_open_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γfl γf : gname)   (* ftable lock + ghost, kalloc, printk *)
    (gs : list gname) (j : nat) (gl : gname)            (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (ns : nat)                                          (* the iref ledger     *)
    (dqb dqs dqbs dqn : dfrac)
    (v vom : mword 64)                       (* syscall arguments 0 and 1   *)
    (pid : mword 32) (U : ustate) (sts : list fdstate)
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
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
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
  (* the descriptor-state fragments at the caller's OWN table -- the
     landed row since 34375379c; the arms return it with one row moved *)
  fd_frags (pv_fdg (us_V U)) sts -∗
  (* ---- THE AU SIDE (the one addition to the landed premise list) ---- *)
  EXTRA -∗
  wp_next true pj (fun (CID : CpuId) =>
  (* THE IMAGE DOES NOT MOVE ([SpecSysOpen]'s note): sys_open only READS
     user memory, so the binders are [(mf, ns', P')] and the block returns
     at [us_upt U P'] -- no [M'].  [uptd_ext_sz] is argstr's own report. *)
  ∀ (mf : regfile) (ns' : nat) (P' : uptd),
      ⌜callee_saved m mf⌝ -∗
      ⌜uptd_ext_sz (pv_sz (us_V U)) (pv_upt (us_V U)) P'⌝ -∗
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
      ARMS (us_upt U P')
        (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE ONE BODY.  The abstract state is read at the LIVE Γ,
   [fs_gamma_L fsc_fs]; the mode readings are of the caller's own argument
   word, so the receipts speak about the omode IT passed.  Both the input
   and the arms are keyed on [om_create vom]. *)
Definition wp_sys_open_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γfl γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v vom : mword 64)
    (pid : mword 32) (U : ustate) (sts : list fdstate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φarm Φun : aview -> Z -> iProp Σ)
    (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
    (Φo : aview -> Z -> anode -> iProp Σ)
    (Φt : aview -> Z -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  wp_sys_open_frame γfl γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v vom pid U sts m K eb b lks
    (open_in Γfs fsc_fs (pv_cwi (us_V U)) vom P Pmiss Φarm Φun Φok Φex Φo Φt)
    (open_arms Γfs fsc_fs (pv_cwi (us_V U)) γf (proc_addr j) pid vom
       P Pmiss Φarm Φun Φok Φex Φo Φt sts).

(* ===================================================================== *)
(*  THE TWO ARM STATEMENTS.  Each is the body above at a DECIDED key --   *)
(*  the [if] reduced by the premise -- and each has exactly ONE proof.    *)
(*  Neither is sealed and neither is client-facing: the seal below is the *)
(*  three-line [destruct] over the two.                                   *)
(* ===================================================================== *)

(* THE PLAIN ARM (the init arm): [om_create vom = false], so the input is
   [open_au_pre_plain] and the output [open_arms_plain].  The create arm is
   refuted at the [c.beqz] rather than proved -- exclusion by premise, at
   the machine. *)
Definition wp_sys_open_plain_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γfl γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v vom : mword 64)
    (pid : mword 32) (U : ustate) (sts : list fdstate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φo : aview -> Z -> anode -> iProp Σ)
    (Φt : aview -> Z -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  om_create vom = false ->
  wp_sys_open_frame γfl γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v vom pid U sts m K eb b lks
    (open_au_pre_plain Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Φo Φt)
    (open_arms_plain Γfs fsc_fs (pv_cwi (us_V U)) γf (proc_addr j) pid vom
       P Pmiss Φo Φt sts).

(* THE O_CREATE ARM: create's surface at the child [AFile []]. *)
Definition wp_sys_open_create_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γfl γf : gname)
    (gs : list gname) (j : nat) (gl : gname)
    (pd pav pu : mword 64)
    (ns : nat)
    (dqb dqs dqbs dqn : dfrac)
    (v vom : mword 64)
    (pid : mword 32) (U : ustate) (sts : list fdstate)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φarm Φun : aview -> Z -> iProp Σ)
    (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
    (Φo : aview -> Z -> anode -> iProp Σ)
    (Φt : aview -> Z -> list (bv 8) -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  om_create vom = true ->
  wp_sys_open_frame γfl γf gs j gl pd pav pu ns dqb dqs dqbs dqn
    v vom pid U sts m K eb b lks
    (open_au_pre_create Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Φarm Φun Φok Φex Φo Φt)
    (open_arms_create Γfs fsc_fs (pv_cwi (us_V U)) γf (proc_addr j) pid vom P Pmiss
       Φarm Φun Φok Φex Φo Φt sts).

(* ===================================================================== *)
(*  ONE MODULE TYPE                                                       *)
(* ===================================================================== *)

(* There is no parallel statement for the walk, the commits or the arms,
   and no second proof against the code.  NO STABLE COROLLARY IS SEALED --
   deliberately: the mknod prover showed the frozen-shape stable forms are
   underivable as stated, the era/[_at] stable story is a dedicated
   follow-on, and this family does not author vacuous statements.  The
   agreement seeds ([SpecSysOpenAU]'s [_pinned] lemmas) are its raw
   material. *)
Module Type SYSOPEN.
  Parameter wp_sys_open :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γfl γf : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (pd pav pu : mword 64)
      (ns : nat)
      (dqb dqs dqbs dqn : dfrac)
      (v vom : mword 64)
      (pid : mword 32) (U : ustate) (sts : list fdstate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φarm Φun : aview -> Z -> iProp Σ)
      (Φok Φex : aview -> Z -> fname -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (Φt : aview -> Z -> list (bv 8) -> iProp Σ),
      wp_sys_open_body γfl γf gs j gl pd pav pu ns dqb dqs dqbs dqn
        v vom pid U sts m K eb b lks P Pmiss Φarm Φun Φok Φex Φo Φt.
End SYSOPEN.
