(* SpecCreate.v -- the public interface of create, the writing half's boss.

     static struct inode*
     create(char *path, short type, short major, short minor)
     {
       struct inode *ip, *dp;
       char name[DIRSIZ];

       if((dp = nameiparent(path, name)) == 0)
         return 0;

       ilock(dp);

       if((ip = dirlookup(dp, name, 0)) != 0){
         iunlockput(dp);
         ilock(ip);
         if(type == T_FILE && (ip->type == T_FILE || ip->type == T_DEVICE))
           return ip;
         iunlockput(ip);
         return 0;
       }

       if((ip = ialloc(dp->dev, type)) == 0){
         iunlockput(dp);
         return 0;
       }

       ilock(ip);
       ip->major = major;
       ip->minor = minor;
       ip->nlink = 1;
       iupdate(ip);

       if(type == T_DIR){                  // Create . and .. entries.
         if(dirlink(ip, ".", ip->inum) < 0 || dirlink(ip, "..", dp->inum) < 0)
           goto fail;
       }

       if(dirlink(dp, name, ip->inum) < 0)
         goto fail;

       if(type == T_DIR){
         dp->nlink++;                      // for ".."; now that success is
         iupdate(dp);                      // guaranteed
       }

       iunlockput(dp);
       return ip;

      fail:
       ip->nlink = 0;
       iupdate(ip);
       iunlockput(ip);
       iunlockput(dp);
       return 0;
     }

   create calls NO panic: every failure is an ordinary arm.

   ==== THE nlink GUARD, AND WHAT IT DOES TO THE DECODE BELOW (9da28f5) ====

   The `if (dp->nlink == 0)` above is upstream `9da28f5`'s second guard
   (`kernel-defects.md` D2; namex has the twin, and `ProofNamex` walks it).
   It grew create from 312 bytes to **332** and it moved every offset in the
   listing below, so:

   **THE DECODE BLOCK THAT FOLLOWS IS AT PRE-9da28f5 OFFSETS AND MUST BE
   REGENERATED BEFORE ANY WALK.**  It is kept because its FIVE structural
   findings are all still true (four dirlink call sites for three source
   calls; `dp->nlink++` last; create never stores `ip->type`; one register
   carries the answer; a0 is not reloaded before either ilock).  What moved:
   the register allocation (the answer now lives in s2, not s3) and every
   address from the prologue on.  Read `CodeCreate.v`, not this comment.

   What IS verified against the regenerated `CodeCreate.v` at this revision:

     +0x00  c.addi16sp -80                   FRAME STILL 80 BYTES / 10 SLOTS
            (0x715d), and **SEVEN** callee-saves in the prologue --
            ra 72, s0 64, s1 56, s2 48, s4 32, s5 24, s6 16.  SLOT 40 IS
            s3's AND THE PROLOGUE DOES NOT WRITE IT: the [c.sdsp s3,40(sp)]
            is at +0x8a, i.e. on the ALLOCATE HALF ONLY, and it is reloaded
            per-arm (+0xd0 C-OK, +0xdc A-FAIL, +0x144 FAIL) rather than by
            the shared epilogue, which restores the same seven.  s3 is
            therefore callee-saved on ARMS N / G / F-BAD / F-OK for the
            trivial reason that they never write it.
     +0x1c  jal nameiparent  / +0x20 mv s1,a0 (dp) / +0x22 beqz -> ARM N
     +0x26  jal ilock                        (a0 still dp)
     +0x2a  lh  a5,74(s1)                    dp->nlink                 [GUARD]
     +0x2e  c.beqz a5 -> +0x76               [ARM G, the guard's exit]
     +0x30  li a2,0 / addi a1,s0,-80 / mv a0,s1 / +0x38 jal dirlookup
     +0x62  mv a0,s2                         THE EPILOGUE FUNNEL, s2 = answer
     +0x76  mv a0,s1 / +0x78 jal iunlockput (dp) / +0x7c li s2,0
     +0x7e  c.j +0x62                        (the epilogue funnel)

   **ARM G IS A MEMBER OF THE ok = false FAMILY, AND THE CONTRACT ALREADY
   ADMITS IT** -- this is the whole reason `wp_create_sconf_body` does not
   move for the fix.  Its exit is `iunlockput(dp); return 0`, i.e. ARM N's
   payload one call later, so the failure arm's "a0 = 0 and create holds
   nothing -- every inode it touched has been iunlockput" is literally true
   of it; the slot ledger is untouched (nameiparent spends two and returns
   one, the `iunlockput` returns the second, so `ns' = ns`, well inside
   `ns - create_slots <= ns' <= ns`); `Sb` grows and `u` falls only by
   whatever flush the `iput` inside `iunlockput` runs, which is exactly what
   `Sb ⊆ Sb'` / `u' <= u` were written for.  The failure family is therefore
   **N / G / F-BAD / A-FAIL / FAIL**, five arms where the text below says
   four.  Design: `fs-icache.md` §20.17 step 1.

   The guard's DECISION is `ProofNamex`'s at +0xce/+0xd2 verbatim -- the
   halfword comes out of the `i_nlink` conjunct of `ic_loaded`'s
   `inode_meta`, and `sign_extend' 64` is injective on `mword 16`, so the
   `c.beqz` decides `di_nlink dn = 0` exactly (`ProofNamexParts.nx_nlz_eq` /
   `nx_nlz_ne`, hoisted there by stage B' precisely so both walkers can
   name them).  The FALL-THROUGH is the interesting half: it hands the walk
   `bv_unsigned (di_nlink dn) <> 0` at the SAME `dn` that `ic_loaded` names
   in its `dinode_at` and quantifies its `dlinks` over -- which is the
   raw material §20.17's step 4/5 consume.

   ==== THE DECODE (PRE-9da28f5 OFFSETS -- SEE ABOVE) =====================

   FRAME: 80 bytes ([addi sp,sp,-80] at +0x00, [addi s0,sp,80] at +0x12),
   EIGHT callee-saves (ra 72, s0 64, s1 56, s2 48, s3 40, s4 32, s5 24,
   s6 16) and the 16-byte `name[DIRSIZ]` local at sp+0 = **s0-80** (the
   [addi a1,s0,-80] at +0x1c / +0x30 / +0xae / +0xfc).  ONE epilogue and
   ONE [ret], at +0x62..+0x74.

   REGISTERS: s1 = dp, s3 = THE RETURN VALUE (every path funnels through
   [mv a0,s3] at +0x60), s2 = type until +0x80 and then ip, s4 = the
   surviving copy of type, s5 = major, s6 = minor.

     +0x14  mv s2,a1 / mv s4,a1 / mv s5,a2 / mv s6,a3
     +0x1c  addi a1,s0,-80                    a1 = &name
     +0x20  jal nameiparent                   (0x80003a2a)
     +0x24  mv s1,a0                          s1 = dp
     +0x26  beqz a0 -> +0x134                 [ARM N]
     +0x2a  jal ilock                         (a0 STILL dp -- not reloaded)
     +0x2e  li a2,0 / addi a1,s0,-80 / mv a0,s1
     +0x36  jal dirlookup                     (0x8000377c)
     +0x3a  mv s3,a0                          s3 = ip  (= 0 on the miss!)
     +0x3c  c.beqz a0 -> +0x80                [the ALLOCATE half]
     +0x3e  mv a0,s1 / +0x40 jal iunlockput   (dp)
     +0x44  mv a0,s3 / +0x46 jal ilock        (ip)
     +0x4a  li a5,2
     +0x4c  bne s2,a5 -> +0x76                [type != T_FILE]
     +0x50  lhu a5,68(s3)   ip->type
     +0x54  addiw a5,a5,-2 / slli 48 / srli 48 / li a4,1
     +0x5c  bltu a4,a5 -> +0x76               [ip->type not in {2,3}]
     +0x60  mv a0,s3 ... ret                  [ARM F-OK: the LOCKED ip]
     +0x76  mv a0,s3 / jal iunlockput / li s3,0 / j +0x60   [ARM F-BAD]
     +0x80  mv a1,s2 (type) / lw a0,0(s1) (dp->dev)
     +0x84  jal ialloc                        (0x8000306c)
     +0x88  mv s2,a0                          s2 = ip
     +0x8a  c.beqz a0 -> +0xc6                [ARM A-FAIL]
     +0x8c  jal ilock                         (a0 STILL ip)
     +0x90  sh s5,70(s2)   ip->major = major
     +0x94  sh s6,72(s2)   ip->minor = minor
     +0x98  li a5,1 / sh a5,74(s2)   ip->nlink = 1
     +0x9e  mv a0,s2 / +0xa0 jal iupdate      (0x80003128)
     +0xa4  li a4,1
     +0xa6  beq s4,a4 -> +0xce                [type == T_DIR]
     +0xaa  lw a2,4(s2) (ip->inum) / addi a1,s0,-80 / mv a0,s1
     +0xb4  jal dirlink   (dp, name, ip->inum)          [NON-DIR copy]
     +0xb8  bltz a0 -> +0x11c                 [fail:]
     +0xbc  mv a0,s1 / +0xbe jal iunlockput (dp) / mv s3,s2 / j +0x60
                                              [ARM C-OK -- the LOCKED ip]
     +0xc6  mv a0,s1 / jal iunlockput (dp) / j +0x60      [ARM A-FAIL body]
     +0xce  lw a2,4(s2) / auipc+addi a1 = 0x800075c0 (".") / mv a0,s2
     +0xdc  jal dirlink   (ip, ".", ip->inum)
     +0xe0  bltz a0 -> +0x11c
     +0xe4  lw a2,4(s1) (dp->inum) / a1 = 0x800075c8 ("..") / mv a0,s2
     +0xf0  jal dirlink   (ip, "..", dp->inum)
     +0xf4  bltz a0 -> +0x11c
     +0xf8  lw a2,4(s2) / addi a1,s0,-80 / mv a0,s1
     +0x102 jal dirlink   (dp, name, ip->inum)           [DIR copy]
     +0x106 bltz a0 -> +0x11c
     +0x10a lhu a5,74(s1) / addiw a5,a5,1 / sh a5,74(s1)  dp->nlink++
     +0x114 mv a0,s1 / +0x116 jal iupdate (dp) / +0x11a j +0xbc
     +0x11c sh zero,74(s2)   ip->nlink = 0             [fail:]
     +0x120 mv a0,s2 / +0x122 jal iupdate (ip)
     +0x126 mv a0,s2 / +0x128 jal iunlockput (ip)
     +0x12c mv a0,s1 / +0x12e jal iunlockput (dp)
     +0x132 j +0x60                           [ARM FAIL, s3 = 0]
     +0x134 mv s3,a0 (= 0) / +0x136 j +0x60   [ARM N body]

   Inode field offsets in play: dev @ +0, inum @ +4, type @ +68, major
   @ +70, minor @ +72, nlink @ +74.

   FIVE THINGS THE C SKETCH DOES NOT SHOW, all verified against the decode:

   1. **FOUR dirlink call sites for THREE source calls.**  The compiler
      DUPLICATED `dirlink(dp, name, ip->inum)` into the two arms of the
      `type == T_DIR` test (+0xb4 for the non-directory, +0x102 for the
      directory) so that the second `if(type == T_DIR)` needs no re-test.
   2. **`dp->nlink++` and `iupdate(dp)` come LAST** (+0x10a..+0x116), after
      every dirlink has succeeded -- not before the `.`/`..` links as in
      the older xv6.  So NO cleanup arm ever has to undo the parent's link
      count, and the `fail:` arm touches only the CHILD's.
   3. **create never stores `ip->type`.**  +68 is READ once (+0x50, the
      found arm) and never written: the type is installed on DISK by
      `ialloc`, and reaches memory through ilock's fill.  This is the
      whole reason [SpecIalloc.ialloc_fresh] exists -- and the reason for
      the ONE open item recorded below.
   4. **s3 carries the answer, and the two `return 0` arms at +0xc6 and
      +0x132 never re-zero it.**  They are 0 because control reached them
      only through the +0x3c `c.beqz` (dirlookup missed), whose +0x3a
      `mv s3,a0` already stored 0.  `s3 = 0` is a live invariant across
      the whole +0x80..+0x132 region.
   5. **a0 is NOT reloaded before the ilock at +0x2a nor the one at
      +0x8c**: it is the live return value of nameiparent / ialloc.

   ==== THE RETURN IS A *LOCKED* INODE ====================================

   Both success arms return with the child's SLEEPLOCK STILL HELD and its
   entry CHECKED OUT -- create is the only fs.c function that does.  So
   this contract's success payout is, verbatim, [SpecIunlock]'s /
   [SpecIunlockput]'s PRECONDITION:

     is_sleeplock .. ∗ sleeplocked_q .. pidv ∗ ic_deposit ∗
     i_dev/i_inum halves ∗ i_valid ↦ true ∗ ic_loaded ∗ ity_shot ∗
     inode_ref_short_gen k (qi + s) qi dev inum g

   i.e. exactly what sys_open must present to `iunlock(ip)` before it
   parks the inode in the file struct, and what sys_mkdir / sys_mknod
   present to `iunlockput(ip)`.  The reference is the RETAINED PARENT of
   the share the deposit holds: [IcacheRef.inode_ref_gather] re-forms the
   canonical reference the caller later spends.

   IT IS GENERATION-NAMED, AND AT THE *SAME* [g] AS THE DEPOSIT AND THE
   [ity_shot].  Erasing the name here cost nothing to the two callers that
   only [iunlockput] (they weaken it back with
   [IcacheRef.inode_ref_short_gen_forget], one line), and it BLOCKED the
   one that does not: [FileInvDefs.inode_pay_alloc] wants
   [inode_shr_held_gen v Q g] and [ity_shot g ty] AT ONE [g], and sys_open's
   O_CREATE arm has no other route to that name -- its else arm keeps the
   gen-named parent across its own [ilock], and this arm cannot, because
   the name was thrown away inside create.  The general rule: a payout
   that already names a generation in one conjunct must not erase it in
   another, because no consumer can put it back.

   ==== THE OP-WIDE SET (fs-icache.md section 18 clause 1) ================

   create is section 18's named consumer: ONE begin_op..end_op around the
   whole body lives in the CALLER (sys_open / sys_mkdir / sys_mknod), and
   create threads ONE [LogInv.log_opS] across ialloc + iupdate x3 +
   dirlink x4 (+ the writei and iupdate inside each dirlink).  The op's
   DISTINCT-BLOCK set is at most SIX, whatever the counted per-call sums
   say:

     IBLOCK(ip)   ialloc's claim, ip's iupdate, and the iupdate inside
                  each dirlink on ip
     IBLOCK(dp)   dp's nlink++ iupdate and the iupdate inside dirlink(dp)
     bmapstart    the one bitmap block (bitmap_geom_ok's 0 < size <= BPB)
     ip's block 0 the new directory's first data block ("." and "..")
     dp's block   the block holding the new entry
     dp's indirect  only when the parent is past NDIRECT blocks

   against MAXOPBLOCKS = 10.  The counted sum is far past it (4 x
   dirlink_units = 28 alone), which is exactly why the seam is SET FORM.
   The arm-by-arm ledger, and the two callee retrofits it needs, are in
   projects/fs-sysfile.md's S5a section.

   The postcondition offers [Sb ⊆ Sb'] and [u' <= u] and NO CEILING on
   [Sb' ∖ Sb]: S3l's finding is that no obligation anywhere consumes a
   ceiling (callers claim MEMBERSHIPS), and a ceiling here would have to
   name loop-carried block maps.  Budget soundness rides the counter --
   [LogInv.log_spend_step] refuses to grow [Sb] without spending.

   THE FLOOR ON [u'] IS OFFERED ONLY AT [ok = true], AND THAT GUARD IS
   FORCED.  The success arms hand back a LOCKED inode, so their caller
   must run its own [iunlockput] before [end_op] -- sys_mkdir at +0x2e and
   sys_mknod at +0x46 both do -- and [wp_iunlockput_*] wants [iput_units]
   in hand.  Nothing between create's return and that call mints a unit,
   so without this clause neither walk can reach its own [iunlockput].
   (The superseded justification here read "create's caller runs [end_op],
   which takes [log_op] at ANY count".  That describes the LAST call those
   callers make, not the one before it.)

   The failure arms owe nothing of the kind -- they hold no inode -- and
   they could not pay it: create's [fail:] tail runs TWO [iunlockput]s and
   the second, on the PARENT, is entered with neither [cru] nor [crz],
   because no route into [fail:] has logged [IBLOCK dp].  [dl16_post]'s
   membership trio is guarded on [0 < tot] and every route into [fail:]
   has [tot = 0]; SpecDirlink's own header explains why that guard is
   forced rather than inherited.  So the call spends one whatever it
   reports, and [CreateBudget.cr_budget_fail_late] -- which prices the arm
   at [ip_need <= u7 /\ u7 = 3] -- says that call can RUN, not that three
   survive it.  Two survive, and an unconditional floor would be false.

   ==== THE ONE OPEN ITEM, STATED HONESTLY ================================

   The `made = true` arm claims [di_type dn = ty].  create does not write
   the type (decode fact 3), so that identity has to arrive from ialloc's
   claim through ilock's THIRD FILL ARM -- and today's [SpecIlock]
   postcondition binds [dn] EXISTENTIALLY, so it does not.  Without it
   the mkdir path cannot even call [dirlink(ip, ".")], whose first
   premise is [di_type dn = T_DIR].  The repair (an additive
   [wp_ilock_fresh] fed by a half-fragment claim receipt out of
   [InodeRegion]) is designed and sized in projects/fs-sysfile.md's S5a
   section; this contract states the TRUE post-state and the proof stage
   inherits the retrofit.  Nothing else in this file depends on it.

   create SLEEPS everywhere, so it threads the full running-process
   bundle and takes the parking premise.  It enters and returns at
   noff 0. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
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
Require Import BitmapInv.
Require Import KernelDataInv.
Require Import SpecPrintk.
Require Import ByteBuf.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SleepLock.
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecDirlookup.
(* [iput_units]: the post's [ok = true] floor is stated at iput's own
   constant, because what the floor exists for is the caller's
   [iunlockput] of the inode create hands back. *)
Require Import SpecIput.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
(* ---- THE APPLICATION'S SIDE (round E2, lane E2-C) ---- *)
Require Import FsBytesGamma.     (* [fs_gamma_L]: the live Γ                *)
Require Import AppInv.           (* [appE]: the commit mask                 *)
Require Import FsTree.           (* [fname]: the entry names the receipts carry *)
Require Import PathElems.        (* [path_elems]: the walk's hop names       *)
Require Import DirView.          (* [T_DIR_z] -- the dots leg's guard *)
Require Import FsAbsCreateFire.  (* the legs' commits and receipts, the type
                                    literals and [create_made]              *)
Require Import SpecSysMknodAU.   (* [mknod_parent_elems]: the PARENT prefix  *)
Require Import FsAbsEra.         (* [ep_start]: the walk's deferred start    *)
Require Import FsAbsMknodFire.   (* [mknod_walk_dead_era]: the walk's death  *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbsDefs.        (* LAST (FsAbs's own rule)                 *)
Import Defs.
Require Import TsoCtx.
Require Import OffBox.   (* [off_rows] / [off_rows_dep] / [off_rows_to_dep] -- the inode's off rows (items 35/36) *)

Local Open Scope Z_scope.

(* create's own frame is 80 bytes (10 slots) -- UNCHANGED by 9da28f5's guard,
   which added instructions but no stack (the `c.addi16sp` at +0x00 is still
   0x715d = -80 and the eight callee-saves still go to 72..16).  Its deepest
   callee is nameiparent (104); dirlink wants 100, dirlookup 90, iunlockput
   64, ialloc 56, ilock and iupdate 44 each.

   104, and every one of nameiparent/dirlink/dirlookup/ialloc moved for ONE
   reason, the bmap chain SpecReadi.v documents: printk's real stack need
   (48, printk_stack) dominates bmap (64), which dominates balloc's
   out-of-blocks arm (58), which pushed bmap's callers readi 72 -> 78 and
   dirlookup 84 -> 90, and from there namex 96 -> 102, nameiparent 98 -> 104,
   dirlink 94 -> 100.  10 + 104 = 114.  Checked against SpecNameiparent.v
   (104), SpecDirlink.v (100), SpecDirlookup.v (90), SpecIunlockput.v (64),
   SpecIalloc.v (56), SpecIlock.v (44), SpecIupdate.v (44).
   [ProofCreateParts.cr_K_value] carries the same number. *)
Notation K_create := (124%nat) (only parsing).
(* THE LEDGER UNITS create must have in hand.  nameiparent takes two and
   returns one on success; dirlookup's iget takes the second on the found
   arm; ialloc takes one on the allocate half; dirlink is NET ZERO but
   wants one in hand for the iget its dirlookup may run.  Every
   iunlockput returns one.  So the peak is THREE, and a success arm keeps
   exactly one out -- the reference to the inode it returns. *)
Definition create_slots : nat := 3%nat.

(* THE WHOLE TRANSACTION.  See the header: the distinct-block set is at
   most six, and the caller's begin_op pays MAXOPBLOCKS. *)
Definition create_units : nat := MAXOPBLOCKS.

Lemma create_units_value : create_units = 10%nat.
Proof. reflexivity. Qed.

(* The two type literals ([T_FILE] / [T_DEVICE]) and the record the
   non-directory allocate arm leaves behind ([create_made]) are
   [FsAbsCreateFire]'s, re-exported here: the era walk's fires and the
   mknod vocabulary leaf read them and sit below this contract, which
   names their walk package in turn. *)

(* (L5) at the third literal type the entries pass; its two siblings are
   [FsAbsCreateFire.T_FILE_ty_ok] / [T_DEVICE_ty_ok], and this one lives
   here because [SpecDirlookup] is in scope here. *)
Lemma T_DIR_ty_ok : InodeRegion.ireg_ty_ok_w SpecDirlookup.T_DIR.
Proof. right. left. reflexivity. Qed.

(* NO STANDALONE [icacheG] / [icfg] IN ANY CONTEXT BELOW, and that is
   load-bearing rather than tidy.  [FileInvDefs.fileG] CARRIES both as
   field instances ([file_icacheG], [file_icfg]), so a context binding
   [!fileG Σ] AND [!icacheG Σ] has two [icacheG]s -- and create is the
   first function where the two MEET: [ProcInv.cwd_ref] (which create
   hands to [nameiparent]) resolves its [inode_held] through [fileG],
   while every [ic_*] here would resolve through the standalone one.  The
   two propositions then print IDENTICALLY and fail to unify, with
   durable-notes' *"iSpecialize: cannot instantiate (P -∗ Q) with P"*.
   Worse, the [Module Type] below would be UNPROVABLE while stating it,
   because a sealer must supply the statement at INDEPENDENT instances.
   [SpecKexec] already binds it this way for the same reason; keep it. *)
Section CreateSpec.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Context `{GEN : GenId}.

  (* THE LOCKED-INODE PAYOUT.  Exactly [SpecIunlock]'s / [SpecIunlockput]'s
     precondition over slot [k], with the retained parent that lets the
     caller re-form and spend the reference.  Factored out because
     sys_open, sys_mkdir and sys_mknod all consume it and none of them
     should have to re-spell it. *)
  Definition create_locked
 (pidv : mword 32)
      (k : nat) (qi s : Qp) (g : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap) : iProp Σ :=
    (∃ γil γisl : gname,
       (* r25 shapes (plan item 33): the parked ident fraction IS the
          travelling share -- create lends exactly half of the fresh
          reference to its own ilock, and sys_open's publish
          ([ProofSysOpenParts.so_publish]) parks the payload at [s + s]. *)
       ⌜qi = s⌝ ∗
       is_sleeplock_genl γil γisl (i_lock (ientry k)) "inode"%string (ic_slp fsc_ic k) (slh_tok (icfg_isl k)) ∗
       sleeplocked_q γisl s (i_lock (ientry k)) pidv ∗
       (* THE CHECKOUT IS ARMED (durable-disk B''-tx2): create returns with
          the child still write-locked, so what it hands over is the
          TRANSACTIONAL descriptor -- the escrow's arm at a half beside the
          holder's own half of the same element.  It stands exactly where a
          bare [ic_deposit fsc_ic k d] stands, at the same arguments, and it is
          why this contract's post no longer hands the
          caller a separate [LogInv.log_tx] on the success arm. *)
       (* A6.145 (tso-flip): at the checkout's EPOCH, under the caller's floor *)
       (∃ loc tlc : nat,
          ⌜(loc <= tlc)%nat⌝ ∗ IcacheRef.cred_floor loc tlc ∗
          ic_tx_dep fsc_ic k s icfg_dev inum g loc) ∗
       (* the child's off rows, FOLDED, out of create's own ilock (items 35/36) *)
       off_rows off_cfg k cur_ctx ∗
       i_dev (ientry k) ↦₄{DfracOwn (1/2)} icfg_dev ∗
       i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum ∗
       i_valid (ientry k) ↦₄ valid_word true ∗
       ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst k inum dn bm ∗
       ity_shot g (di_type dn) ∗
       (* ...AND THE INUM'S FREEZE TOKEN (iclaim-ledger.md §3.9): this bundle
          is a CHECKED-OUT entry, i.e. exactly [SpecIunlockput]'s
          precondition, and since A-prime that precondition includes
          [ifreeze_off].  create holds it (its own [ilock(ip)] handed it
          over) and hands it on to whichever of sys_open / sys_mkdir /
          sys_mknod releases the child. *)
       ifreeze_off (bv_unsigned inum) ∗
       (* A6.145: the retained parent travels FLOORED (genlo + the carrier's
          floor receipt), so the eventual forget can rebuild the credential *)
       (∃ lo tl : nat,
          ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
          inode_ref_short_genlo k (qi + s)%Qp qi icfg_dev inum g lo) ∗
       (* ...AND ITS PROVENANCE UNIT (item 7a-wire, iclaim-ledger.md §5''.3).
          This bundle IS [SpecIunlockput]'s precondition, and since item
          7a-wire that precondition includes the unit the closing iput
          spends.  create holds it -- it came out of its own iget, or out of
          [SpecIalloc]'s claim -- and hands it on to whichever of sys_open /
          sys_mkdir / sys_mknod releases the child. *)
       runit_any (bv_unsigned inum))%I.

  (* Assembled structurally, not by [iFrame]: at the syscall altitude this
     is built at (hundreds of accumulated hypotheses), even a NAMED
     [iFrame "H1 .. H10"] over these ten conjuncts measured 26-28 s per call
     site in ProofCreate.v -- [iSplitL]/[iExact] is free, the same fix as
     [IcacheEscrow.ic_mk_loaded] for the same reason (optimization.md,
     "Framing"). *)
  Lemma create_locked_mk pidv k qi s g inum dn bm
      γil γisl :
    qi = s ->
    is_sleeplock_genl γil γisl (i_lock (ientry k)) "inode"%string (ic_slp fsc_ic k) (slh_tok (icfg_isl k)) -∗
    sleeplocked_q γisl s (i_lock (ientry k)) pidv -∗
    (∃ loc tlc : nat,
       ⌜(loc <= tlc)%nat⌝ ∗ IcacheRef.cred_floor loc tlc ∗
       ic_tx_dep fsc_ic k s icfg_dev inum g loc) -∗
    off_rows off_cfg k cur_ctx -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} icfg_dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word true -∗
    ic_loaded fsc_fs fsc_ireg fsc_cov fsc_logst k inum dn bm -∗
    ity_shot g (di_type dn) -∗
    ifreeze_off (bv_unsigned inum) -∗
    (∃ lo tl : nat,
       ⌜(lo <= tl)%nat⌝ ∗ IcacheRef.cred_floor lo tl ∗
       inode_ref_short_genlo k (qi + s)%Qp qi icfg_dev inum g lo) -∗
    runit_any (bv_unsigned inum) -∗
    create_locked pidv k qi s g inum dn bm.
  Proof.
    intros Hqs.
    iIntros "Hlk Hlkd Hdep Hoffr Hdev Hinum Hvalid Hload Hshot Hfrz Href Hru".
    rewrite /create_locked. iExists γil, γisl.
    iSplitR; [iPureIntro; exact Hqs |].
    iSplitL "Hlk"; [iExact "Hlk" |]. iSplitL "Hlkd"; [iExact "Hlkd" |].
    iSplitL "Hdep"; [iExact "Hdep" |].
    iSplitL "Hoffr"; [iExact "Hoffr" |].
    iSplitL "Hdev"; [iExact "Hdev" |]. iSplitL "Hinum"; [iExact "Hinum" |].
    iSplitL "Hvalid"; [iExact "Hvalid" |]. iSplitL "Hload"; [iExact "Hload" |].
    iSplitL "Hshot"; [iExact "Hshot" |].
    iSplitL "Hfrz"; [iExact "Hfrz" |].
    iSplitL "Href"; [iExact "Href" | iExact "Hru"].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE APPLICATION'S SIDE OF create (round E2, lane E2-C; design of    *)
  (*  record applications.md section 2, the delta legs fs-syscall-specs   *)
  (*  section 4).  create performs [delta_create] as LEGS -- the ARM      *)
  (*  (the child's row appears), mkdir's DOTS, the PARENT leg, and on     *)
  (*  failure the UNARM (the row disappears; ruling Q-h: the do-then-undo *)
  (*  PAIR is the honest form) -- and each leg fires a two-phase commit   *)
  (*  the caller supplies here ([FsAbsCreateFire]).  The child's content  *)
  (*  is indexed by the requested type ([cre_c0]/[cre_child]); the        *)
  (*  receipts come back in the post, each with its instant's row facts.  *)
  (* ------------------------------------------------------------------ *)

  (* ------------------------------------------------------------------ *)
  (*  THE DOTS LEG IS GUARDED BY THE TYPE.                                *)
  (*                                                                      *)
  (*  Only a DIRECTORY gets dots: the [beq s4,a4] at +0xca is taken        *)
  (*  exactly on [type == T_DIR], and at any other type create's dots      *)
  (*  commit can never fire.  So the contract does not ask a caller at     *)
  (*  another type for one -- a caller owes nothing for a move its call    *)
  (*  cannot make, and that is the contract's honesty, not a convenience.  *)
  (*  Before the guard, mknod's and open(O_CREATE)'s provers had to         *)
  (*  MANUFACTURE a dots piece for a leg they knew was dead, and the only   *)
  (*  thing they could pay its [AppInv.app_step] from was the parked        *)
  (*  license -- which is what kept the license alive after every other     *)
  (*  fire moved to the deposit or the supply.                              *)
  (*                                                                      *)
  (*  It is ONE definition rather than the implication spelled at each of   *)
  (*  its five occurrences (the bundle, and the unfired-return position in  *)
  (*  each arm) so that a proof that merely PASSES the leg on -- which is   *)
  (*  almost all of them -- treats it as one atom.                          *)
  (* ------------------------------------------------------------------ *)
  Definition cre_dots_leg (Γ : fs_view_names Σ) (tyz : Z)
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ)) : iProp Σ :=
    (⌜tyz = T_DIR_z⌝ -∗ pf_at (adots_commit_at Γ appE) Fdots)%I.

  (* a caller that HAS the piece owes the leg *)
  Lemma cre_dots_leg_of (Γ : fs_view_names Σ) (tyz : Z)
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ)) :
    pf_at (adots_commit_at Γ appE) Fdots -∗ cre_dots_leg Γ tyz Fdots.
  Proof. iIntros "H" (_). iExact "H". Qed.

  (* ...and create reads the piece back out where the branch is taken *)
  Lemma cre_dots_leg_at (Γ : fs_view_names Σ) (tyz : Z)
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ)) :
    tyz = T_DIR_z ->
    cre_dots_leg Γ tyz Fdots -∗ pf_at (adots_commit_at Γ appE) Fdots.
  Proof. intros Hty. iIntros "H". iApply ("H" $! Hty). Qed.

  (* THE POINT: at any other type the leg is free *)
  Lemma cre_dots_leg_nodir (Γ : fs_view_names Σ) (tyz : Z)
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ)) :
    tyz <> T_DIR_z -> ⊢ cre_dots_leg Γ tyz Fdots.
  Proof. intros Hne. iIntros (Hty). exfalso. exact (Hne Hty). Qed.

  (* the four commits, at the child's type-indexed content *)
  Definition cre_commits (Γ : fs_view_names Σ) (tyz ma mi : Z)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
      (Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) : iProp Σ :=
    (pf_at (aarm_commit_at Γ appE (cre_c0 tyz ma mi)) Farm
     ∗ cre_dots_leg Γ tyz Fdots
     ∗ pf_at (aunarm_commit_at Γ appE) Fun
     ∗ pf_at (acre_commit_at_gen Γ appE (cre_child tyz ma mi)) Fok)%I.

  (* SATISFIABILITY, and the discharger every caller of the landed create
     hands down: the GENERIC application asks nothing of create's legs, so
     every commit is its own unit and the whole bundle is paid off the
     SUPPLY ([AppInv.app_step_acc], through [FsAbsCreateFire]'s four
     [_unit]s).  It sits here rather than in [FsAbsInvFire]'s
     [fsabs_*] family because [ProofSysMkdir], one of its consumers, is
     BELOW that file in the cone. *)
  Lemma cre_commits_unit (γfs : fs_names) (tyz ma mi : Z) :
    app_sup -∗
    cre_commits (fs_gamma_L γfs) tyz ma mi (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I))
      (pfam_triv (fun _ _ => True%I)) (pfam_triv (fun _ _ _ _ => True%I)).
  Proof.
    iIntros "#Hsup". rewrite /cre_commits.
    iSplitR.
    { iApply pf_at_triv.
      iApply (aarm_commit_at_unit γfs appE _ with "Hsup"). }
    iSplitR.
    { iApply cre_dots_leg_of. iApply pf_at_triv.
      iApply (adots_commit_at_unit γfs appE with "Hsup"). }
    iSplitR.
    { iApply pf_at_triv.
      iApply (aunarm_commit_at_unit γfs appE with "Hsup"). }
    iApply pf_at_triv.
    iApply (acre_commit_at_gen_unit γfs appE _ with "Hsup").
  Qed.

  (* ARM C-OK / F-OK, keyed on [made].  Both success arms ran nameiparent,
     so both return the WALK CURSOR at the parent index and tie the name to
     the path's last element; what differs is which instant fired.  A FRESH
     child had its arm, [its dots -- a directory --] and its parent leg
     fired, the unarm and the exists observation come home unfired; a FOUND
     node moved nothing, so the observation fired and every commit comes
     home. *)
  Definition cre_ok_arms (Γ : fs_view_names Σ) (tyz ma mi : Z)
      (P : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
      (Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (pl : list (bv 8)) (made : bool) (i : Z) : iProp Σ :=
    (∃ (d : Z) (nm : fname),
       ⌜list_basics.last (path_elems pl) = Some nm⌝
       ∗ P (length (mknod_parent_elems pl)) d
       ∗ (if made
          then cre_arm_fired Farm i
               ∗ (cre_dots_fired Fdots i d true ∨ cre_dots_leg Γ tyz Fdots)
               ∗ cre_acre_fired Fok d nm i (cre_child tyz ma mi d i)
               ∗ pf_at (aunarm_commit_at Γ appE) Fun
               ∗ pf_at (dlookup_commit_at Γ appE) Fex
          else cre_ex_fired Fex d nm i
               ∗ cre_commits Γ tyz ma mi Farm Fdots Fun Fok))%I.

  (* ARM N: the walk died before create saw a parent, so the death receipt
     comes home and every commit is whole.  ARMS G / F-BAD / A-FAIL / FAIL
     and mkdir's three [fail:] entries: the walk REACHED the parent, so the
     cursor comes home; the exists observation fired (F-BAD read the name)
     or comes home; and the child's legs are whole, or the do-then-undo PAIR
     fired -- the arm, [the dots, both or the first alone,] the unarm -- with
     the parent leg always coming home. *)
  Definition cre_fail_arms (Γ : fs_view_names Σ) (γfs : fs_names)
      (tyz ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
      (Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (pl : list (bv 8)) : iProp Σ :=
    ((mknod_walk_dead_era γfs P Pmiss pl
        ∗ pf_at (dlookup_commit_at Γ appE) Fex
        ∗ cre_commits Γ tyz ma mi Farm Fdots Fun Fok)
     ∨ (∃ d : Z,
          P (length (mknod_parent_elems pl)) d
          ∗ ((∃ (nm : fname) (i : Z),
                ⌜list_basics.last (path_elems pl) = Some nm⌝
                ∗ cre_ex_fired Fex d nm i)
             ∨ pf_at (dlookup_commit_at Γ appE) Fex)
          ∗ pf_at (acre_commit_at_gen Γ appE (cre_child tyz ma mi)) Fok
          ∗ ((pf_at (aarm_commit_at Γ appE (cre_c0 tyz ma mi)) Farm
                ∗ cre_dots_leg Γ tyz Fdots
                ∗ pf_at (aunarm_commit_at Γ appE) Fun)
             ∨ (∃ i : Z,
                  cre_arm_fired Farm i
                  ∗ ((∃ full : bool, cre_dots_fired Fdots i d full)
                     ∨ cre_dots_leg Γ tyz Fdots)
                  ∗ cre_unarm_fired Fun i))))%I.

  (* ------------------------------------------------------------------ *)
  (*  THE POST'S PURE SUCCESS READING, AND THE TWO PINNED SPECIALISATIONS *)
  (* ------------------------------------------------------------------ *)

  (* [ARM C-OK]: this inode was just allocated.  The type is ialloc's, the
     three halfword stores are create's, and on the NON-directory arm the
     record is exactly [create_made]; on the directory arm the size is 32
     and block 0 holds "." and "..".
     [ARM F-OK]: the name was already there, and the two tests at +0x4c /
     +0x5c passed -- which is where [ty = T_FILE] comes from, and it is what
     lets a caller at any OTHER type read [ok = true -> made = true] off the
     post. *)
  Definition cre_ok_pure (ty major minor : mword 16) (made : bool)
      (dn : dinode) : Prop :=
    if made
    then di_type dn = ty
         /\ di_major dn = major
         /\ di_minor dn = minor
         /\ bv_unsigned (di_nlink dn) = 1
         /\ (ty <> SpecDirlookup.T_DIR -> dn = create_made ty major minor)
    else ty = T_FILE
         /\ (di_type dn = T_FILE \/ di_type dn = T_DEVICE).

  (* create returns a FRESH inode at every type but [T_FILE]. *)
  Lemma cre_made_of_ne_file (ty major minor : mword 16) (made : bool)
      (dn : dinode) :
    ty <> T_FILE -> cre_ok_pure ty major minor made dn -> made = true.
  Proof.
    intros Hne Hp. destruct made; [reflexivity |].
    destruct Hp as [Hty _]. exfalso. exact (Hne Hty).
  Qed.

  (* mknod's reading: the device type forces the fresh arm and the record. *)
  Lemma cre_ok_pure_dev (major minor : mword 16) (made : bool) (dn : dinode) :
    cre_ok_pure T_DEVICE major minor made dn ->
    made = true /\ dn = create_made T_DEVICE major minor.
  Proof.
    intros Hp.
    assert (Hm : made = true).
    { eapply cre_made_of_ne_file; [| exact Hp].
      intros Hc. by vm_compute in Hc. }
    subst made. split; [reflexivity |].
    destruct Hp as (_ & _ & _ & _ & Hrec). apply Hrec.
    intros Hc. by vm_compute in Hc.
  Qed.

  (* sys_open's reading: both arms survive, keyed on [made]. *)
  Lemma cre_ok_pure_file (major minor : mword 16) (made : bool) (dn : dinode) :
    cre_ok_pure T_FILE major minor made dn ->
    if made then dn = create_made T_FILE major minor
    else di_type dn = T_FILE \/ di_type dn = T_DEVICE.
  Proof.
    intros Hp. destruct made.
    - destruct Hp as (_ & _ & _ & _ & Hrec). apply Hrec.
      intros Hc. by vm_compute in Hc.
    - exact (proj2 Hp).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE INPUT BUNDLE AT THE TRIVIAL FAMILIES                           *)
  (* ------------------------------------------------------------------ *)

  (* The whole of what a caller hands create, for a caller that tracks
     nothing: every hop says yes, every cursor is [True], and each commit
     is its own unit paid off [AppInv.app_sup].  It sits here rather than
     in [FsAbsInvFire]'s [fsabs_*] family because [ProofSysMkdir], one of
     its consumers, is BELOW that file in the cone. *)
  Lemma cre_start_unit (γfs : fs_names) (cw : Z) (pl : list (bv 8)) :
    ⊢ ep_start γfs cw (fun _ _ => True%I) (fun _ _ => True%I) pl.
  Proof. iApply ep_start_triv. Qed.

  (* the exists observation at the trivial pair -- the shape the bundles
     take it in, so no caller assembles the conjunction by hand *)
  Lemma cre_dlookup_unit (Γ : fs_view_names Σ) :
    ⊢ pf_at (dlookup_commit_at Γ appE) (pfam_triv (fun _ _ _ _ => True%I)).
  Proof.
    iApply pf_at_triv. iApply dlookup_commit_at_unit.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE BUNDLE, ASSEMBLED AT A PINNED TYPE                              *)
  (*                                                                      *)
  (*  A type-pinned caller holds the child's content as a CONSTANT and    *)
  (*  OWES NO DOTS LEG AT ALL -- at a device or a file the [beq s4,a4] at  *)
  (*  +0xca is never taken, and [cre_dots_leg] is guarded on exactly that  *)
  (*  test, so these two produce it out of the type inequality and take    *)
  (*  no dots piece from anyone.                                          *)
  (* ------------------------------------------------------------------ *)

  Lemma cre_commits_of_dev (Γ : fs_view_names Σ) (ma mi : Z)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok -∗
    cre_child_unfired Γ (ADev ma mi) Farm Fun -∗
    cre_commits Γ (bv_unsigned T_DEVICE) ma mi Farm (pfam_triv (fun _ _ _ _ => True%I)) Fun Fok.
  Proof.
    rewrite /cre_commits /cre_child_unfired (cre_c0_dev ma mi).
    iIntros "Hac [Ha Hu]".
    iDestruct (cre_dots_leg_nodir Γ (bv_unsigned T_DEVICE)
                 (pfam_triv (fun _ _ _ _ => True%I))
                 ltac:(rewrite T_DEVICE_value /T_DIR_z; lia)) as "Hd".
    iFrame "Ha Hd Hu".
    (* THE MOVER RIDES THE PAIR: [acre_commit_at_gen_ext] is stated on the
       AU side alone, and [refund_mono] lifts it over the conjunction. *)
    iApply (pf_at_mono with "[] Hac"). iIntros "Hac".
    iApply (acre_commit_at_gen_ext Γ appE (fun _ _ => ADev ma mi)
              (cre_child (bv_unsigned T_DEVICE) ma mi) Fok.(pf_recv)
              (fun d i => eq_sym (cre_child_dev ma mi d i)) with "Hac").
  Qed.

  Lemma cre_commits_of_file (Γ : fs_view_names Σ) (ma mi : Z)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    pf_at (acre_commit_at Γ appE (AFile [])) Fok -∗
    cre_child_unfired Γ (AFile []) Farm Fun -∗
    cre_commits Γ (bv_unsigned T_FILE) ma mi Farm (pfam_triv (fun _ _ _ _ => True%I)) Fun Fok.
  Proof.
    rewrite /cre_commits /cre_child_unfired (cre_c0_file ma mi).
    iIntros "Hac [Ha Hu]".
    iDestruct (cre_dots_leg_nodir Γ (bv_unsigned T_FILE)
                 (pfam_triv (fun _ _ _ _ => True%I))
                 ltac:(rewrite T_FILE_value /T_DIR_z; lia)) as "Hd".
    iFrame "Ha Hd Hu".
    iApply (pf_at_mono with "[] Hac"). iIntros "Hac".
    iApply (acre_commit_at_gen_ext Γ appE (fun _ _ => AFile [])
              (cre_child (bv_unsigned T_FILE) ma mi) Fok.(pf_recv)
              (fun d i => eq_sym (cre_child_file ma mi d i)) with "Hac").
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE TWO PINNED READINGS OF THE ARMS                                 *)
  (*                                                                      *)
  (*  A type-pinned caller does not want the [made] key or the general    *)
  (*  child index: at [T_DEVICE] the found arm is unreachable and the     *)
  (*  child is the device; at [T_FILE] both arms live and the child is    *)
  (*  the empty file.  Each reading is a LEMMA over the one contract, so  *)
  (*  a drift in the arms breaks a proof rather than a prover.            *)
  (* ------------------------------------------------------------------ *)

  (* sys_mknod's success payout.  [cre_made_of_ne_file] is what hands the
     caller the [made = true] this is stated at. *)
  Lemma cre_ok_arms_dev (Γ : fs_view_names Σ) (ma mi : Z)
      (P : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
      (Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (pl : list (bv 8)) (i : Z) :
    cre_ok_arms Γ (bv_unsigned T_DEVICE) ma mi P Farm Fdots Fun Fok Fex pl
      true i ⊢
      ∃ (av : aview) (d : Z) (nm : fname) (ents : gmap fname Z) (nl : nat),
        ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
        ⌜cre_pre av d nm ents nl i (ADev ma mi)⌝ ∗
        P (length (mknod_parent_elems pl)) d ∗
        pf_at (dlookup_commit_at Γ appE) Fex ∗
        Fok.(pf_recv) av d nm i ∗
        cre_arm_fired Farm i ∗ pf_at (aunarm_commit_at Γ appE) Fun.
  Proof.
    rewrite /cre_ok_arms. iIntros "H".
    iDestruct "H" as (d nm) "(%Hlast & HP & Harm & _ & Hacre & Hun & Hdl)".
    rewrite /cre_acre_fired.
    iDestruct "Hacre" as (av ents nl) "(%Hpre & HΦ)".
    iExists av, d, nm, ents, nl.
    iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; exact Hpre |].
    iFrame "HP Hdl HΦ Harm Hun".
  Qed.

  (* ...and its failure fold. *)
  Lemma cre_fail_arms_dev (Γ : fs_view_names Σ) (γfs : fs_names) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
      (Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (pl : list (bv 8)) :
    cre_fail_arms Γ γfs (bv_unsigned T_DEVICE) ma mi P Pmiss
      Farm Fdots Fun Fok Fex pl ⊢
      ((mknod_walk_dead_era γfs P Pmiss pl
          ∗ pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok
          ∗ pf_at (dlookup_commit_at Γ appE) Fex
          ∗ cre_child_unfired Γ (ADev ma mi) Farm Fun)
       ∨ (∃ d : Z,
            P (length (mknod_parent_elems pl)) d
            ∗ pf_at (acre_commit_at Γ appE (ADev ma mi)) Fok
            ∗ ((∃ (av : aview) (i : Z) (nm : fname) (ents : gmap fname Z)
                  (nl : nat),
                  ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                  ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
                  ⌜ents !! nm = Some i⌝ ∗
                  Fex.(pf_recv) av d nm i)
               ∨ pf_at (dlookup_commit_at Γ appE) Fex)
            ∗ (cre_child_unfired Γ (ADev ma mi) Farm Fun
               ∨ ∃ i : Z, cre_child_pair Farm Fun i))).
  Proof.
    rewrite /cre_fail_arms /cre_commits /cre_child_unfired /cre_child_pair.
    iIntros "[(Hd & Hdl & Harm & _ & Hun & Hac) | Hr]".
    - iLeft. iFrame "Hd Hdl". iSplitL "Hac"; [iExact "Hac" |].
      iSplitL "Harm"; [iExact "Harm" | iExact "Hun"].
    - iRight. iDestruct "Hr" as (d) "(HP & Hex & Hac & Hlegs)".
      iExists d. iFrame "HP". iSplitL "Hac"; [iExact "Hac" |].
      iSplitL "Hex".
      { iDestruct "Hex" as "[Hf | Hdl]"; [| by iRight].
        iLeft. iDestruct "Hf" as (nm i) "(%Hlast & Hf)".
        rewrite /cre_ex_fired. iDestruct "Hf" as (av ents nl) "(%Hrow & %Hent & HΦ)".
        iExists av, i, nm, ents, nl.
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iSplitR; [by iPureIntro |]. iExact "HΦ". }
      iDestruct "Hlegs" as "[(Ha & _ & Hu) | Hpair]".
      + iLeft. iSplitL "Ha"; [iExact "Ha" | iExact "Hu"].
      + iRight. iDestruct "Hpair" as (i) "(Ha & _ & Hu)".
        iExists i. iFrame "Ha Hu".
  Qed.

  (* sys_open's O_CREATE success payout: both arms survive the pin, keyed on
     [made], with the cursor and the name tie SHARED (both ran
     nameiparent). *)
  Lemma cre_ok_arms_file (Γ : fs_view_names Σ) (ma mi : Z)
      (P : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
      (Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (pl : list (bv 8)) (made : bool) (i : Z) :
    cre_ok_arms Γ (bv_unsigned T_FILE) ma mi P Farm Fdots Fun Fok Fex pl
      made i ⊢
      ∃ (d : Z) (nm : fname),
        ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
        P (length (mknod_parent_elems pl)) d ∗
        ((∃ (av : aview) (ents : gmap fname Z) (nl : nat),
            ⌜cre_pre av d nm ents nl i (AFile [])⌝ ∗
            Fok.(pf_recv) av d nm i ∗
            pf_at (dlookup_commit_at Γ appE) Fex ∗
            cre_arm_fired Farm i ∗ pf_at (aunarm_commit_at Γ appE) Fun)
         ∨ (∃ (av : aview) (ents : gmap fname Z) (nl : nat),
            ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
            ⌜ents !! nm = Some i⌝ ∗
            Fex.(pf_recv) av d nm i ∗
            pf_at (acre_commit_at Γ appE (AFile [])) Fok ∗
            cre_child_unfired Γ (AFile []) Farm Fun)).
  Proof.
    rewrite /cre_ok_arms /cre_commits /cre_child_unfired. iIntros "H".
    iDestruct "H" as (d nm) "(%Hlast & HP & Hrest)".
    iExists d, nm. iSplitR; [by iPureIntro |]. iFrame "HP".
    destruct made.
    - iDestruct "Hrest" as "(Harm & _ & Hacre & Hun & Hdl)".
      rewrite /cre_acre_fired.
      iDestruct "Hacre" as (av ents nl) "(%Hpre & HΦ)".
      iLeft. iExists av, ents, nl.
      iSplitR; [iPureIntro; exact Hpre |]. iFrame "HΦ Hdl Harm Hun".
    - iDestruct "Hrest" as "(Hex & Ha & _ & Hu & Hac)".
      rewrite /cre_ex_fired.
      iDestruct "Hex" as (av ents nl) "(%Hrow & %Hent & HΦ)".
      iRight. iExists av, ents, nl.
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitL "HΦ"; [iExact "HΦ" |].
      iSplitL "Hac"; [iExact "Hac" |].
      iSplitL "Ha"; [iExact "Ha" | iExact "Hu"].
  Qed.

  (* ...and the two PROJECTIONS sys_open's prover takes, so it destructs
     [made] once and frames. *)
  Lemma cre_ok_file_fresh (Γ : fs_view_names Σ) (ma mi : Z)
      (P : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
      (Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (pl : list (bv 8)) (i : Z) :
    cre_ok_arms Γ (bv_unsigned T_FILE) ma mi P Farm Fdots Fun Fok Fex pl
      true i ⊢
      ∃ (d : Z) (nm : fname) (av : aview) (ents : gmap fname Z) (nl : nat),
        ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
        ⌜cre_pre av d nm ents nl i (AFile [])⌝ ∗
        P (length (mknod_parent_elems pl)) d ∗
        Fok.(pf_recv) av d nm i ∗
        pf_at (dlookup_commit_at Γ appE) Fex ∗
        cre_arm_fired Farm i ∗ pf_at (aunarm_commit_at Γ appE) Fun.
  Proof.
    rewrite /cre_ok_arms /cre_acre_fired. iIntros "H".
    iDestruct "H" as (d nm) "(%Hl & HP & Ha & _ & Hac & Hu & Hdl)".
    iDestruct "Hac" as (av ents nl) "(%Hpre & HΦ)".
    rewrite (cre_child_file ma mi d i) in Hpre.
    iExists d, nm, av, ents, nl.
    iSplitR; [by iPureIntro |]. iSplitR; [iPureIntro; exact Hpre |].
    iFrame "HP HΦ Hdl Ha Hu".
  Qed.

  Lemma cre_ok_file_exists (Γ : fs_view_names Σ) (ma mi : Z)
      (P : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
      (Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (pl : list (bv 8)) (i : Z) :
    cre_ok_arms Γ (bv_unsigned T_FILE) ma mi P Farm Fdots Fun Fok Fex pl
      false i ⊢
      ∃ (d : Z) (nm : fname) (av : aview) (ents : gmap fname Z) (nl : nat),
        ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
        ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
        ⌜ents !! nm = Some i⌝ ∗
        P (length (mknod_parent_elems pl)) d ∗
        Fex.(pf_recv) av d nm i ∗
        pf_at (acre_commit_at Γ appE (AFile [])) Fok ∗
        cre_child_unfired Γ (AFile []) Farm Fun.
  Proof.
    rewrite /cre_ok_arms /cre_ex_fired /cre_commits /cre_child_unfired
            (cre_c0_file ma mi).
    iIntros "H".
    iDestruct "H" as (d nm) "(%Hl & HP & Hex & Ha & _ & Hu & Hac)".
    iDestruct "Hex" as (av ents nl) "(%Hrow & %Hent & HΦ)".
    iExists d, nm, av, ents, nl.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitL "HP"; [iExact "HP" |]. iSplitL "HΦ"; [iExact "HΦ" |].
    iSplitL "Hac".
    { rewrite /acre_commit_at.
      iApply (pf_at_mono with "[] Hac"). iIntros "Hac".
      iApply (acre_commit_at_gen_ext Γ appE
                (cre_child (bv_unsigned T_FILE) ma mi) (fun _ _ => AFile [])
                Fok.(pf_recv) (fun d0 i0 => cre_child_file ma mi d0 i0)
                with "Hac"). }
    iSplitL "Ha"; [iExact "Ha" | iExact "Hu"].
  Qed.

  (* ...and its failure fold, which sys_open folds into its own create arms. *)
  Lemma cre_fail_arms_file (Γ : fs_view_names Σ) (γfs : fs_names) (ma mi : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
      (Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (pl : list (bv 8)) :
    cre_fail_arms Γ γfs (bv_unsigned T_FILE) ma mi P Pmiss
      Farm Fdots Fun Fok Fex pl ⊢
      ((mknod_walk_dead_era γfs P Pmiss pl
          ∗ pf_at (acre_commit_at Γ appE (AFile [])) Fok
          ∗ pf_at (dlookup_commit_at Γ appE) Fex
          ∗ cre_child_unfired Γ (AFile []) Farm Fun)
       ∨ (∃ d : Z,
            P (length (mknod_parent_elems pl)) d
            ∗ pf_at (acre_commit_at Γ appE (AFile [])) Fok
            ∗ ((∃ (av : aview) (i : Z) (nm : fname) (ents : gmap fname Z)
                  (nl : nat),
                  ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
                  ⌜av !! d = Some (MkAnode (ADir ents) nl)⌝ ∗
                  ⌜ents !! nm = Some i⌝ ∗
                  Fex.(pf_recv) av d nm i)
               ∨ pf_at (dlookup_commit_at Γ appE) Fex)
            ∗ (cre_child_unfired Γ (AFile []) Farm Fun
               ∨ ∃ i : Z, cre_child_pair Farm Fun i))).
  Proof.
    rewrite /cre_fail_arms /cre_commits /cre_child_unfired /cre_child_pair.
    iIntros "[(Hd & Hdl & Harm & _ & Hun & Hac) | Hr]".
    - iLeft. iFrame "Hd Hdl". iSplitL "Hac"; [iExact "Hac" |].
      iSplitL "Harm"; [iExact "Harm" | iExact "Hun"].
    - iRight. iDestruct "Hr" as (d) "(HP & Hex & Hac & Hlegs)".
      iExists d. iFrame "HP". iSplitL "Hac"; [iExact "Hac" |].
      iSplitL "Hex".
      { iDestruct "Hex" as "[Hf | Hdl]"; [| by iRight].
        iLeft. iDestruct "Hf" as (nm i) "(%Hlast & Hf)".
        rewrite /cre_ex_fired. iDestruct "Hf" as (av ents nl) "(%Hrow & %Hent & HΦ)".
        iExists av, i, nm, ents, nl.
        iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
        iSplitR; [by iPureIntro |]. iExact "HΦ". }
      iDestruct "Hlegs" as "[(Ha & _ & Hu) | Hpair]".
      + iLeft. iSplitL "Ha"; [iExact "Ha" | iExact "Hu"].
      + iRight. iDestruct "Hpair" as (i) "(Ha & _ & Hu)".
        iExists i. iFrame "Ha Hu".
  Qed.
End CreateSpec.

(* the two arm bodies are disjunctions with existentials inside, over a
   walk family: sealed, so an [iFrame] at syscall altitude does not search
   through them *)
Global Typeclasses Opaque cre_ok_arms cre_fail_arms.

Definition wp_create_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
 (γf : gname)           (* kalloc, ftable, printk *)
    (plen : nat) (pfun : nat -> bv 8)                 (* the PATH buffer     *)
    (ty major minor : mword 16)                       (* a1, a2, a3          *)
    (U : ustate)                                    (* the running process *)
    (u : nat) (Sb : gset Z)                           (* THE OP-WIDE LEDGER  *)
    (ns : nat)                                        (* the iref ledger     *)
    (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (* ---- THE APPLICATION'S SIDE: the walk's cursor pair, the four legs'
       receipts and the exists observation's ---- *)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Farm : pfam Σ (aview -> Z -> iProp Σ))
    (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
    (Fun : pfam Σ (aview -> Z -> iProp Σ))
    (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
    (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :=
  let pcE : mword 64 := mword_of_int KernelSyms.create in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let Γfs := fs_gamma_L fsc_fs in
  let tyz := bv_unsigned ty in
  let ma := bv_unsigned major in
  let mi := bv_unsigned minor in
  (K_create <= K)%nat ->
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
  InodeInv.ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (* ---- namex's path buffer ---- *)
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* ---- ialloc's three geometry premises, and its live type premise ---- *)
  1 < fsc_ninodes ->
  fsc_ninodes <= 16 * Z.of_nat icfg_nib ->
  fsc_ninodes < 2 ^ 31 ->
  (* ...and mkfs's own [ushort] geometry beside them, carried as a premise
     rather than as a slot widening (D0-a): it is what makes the
     [lw a2,4(s3)] at +0xb6 agree with dirlink's ZERO-extended halfword
     argument.  BOTH of create's proof halves consume it ([cr_alloc_half],
     [cr_fail_half]) and nothing below the seal supplies it, so the seal
     is where it has to stand. *)
  16 * Z.of_nat icfg_nib <= 2 ^ 16 ->
  bv_unsigned ty <> 0 ->
  (* durable-disk 2b-inode-3: ialloc's claim box owes the region (L5) --
     the type it writes is one of the four the enumeration admits.  Stated
     on the type WORD so this file needs no [SpecIalloc] import; all three
     entries pass a literal. *)
  InodeRegion.ireg_ty_ok_w ty ->
  (* ---- ialloc's no-inodes arm calls printk, not panic ---- *)
  printk_gen_contract (kt := KT1) fsc_printk fsc_uart fsc_disk ->
  (* ---- THE TWO LEDGERS (see the header) ---- *)
  (create_units <= u)%nat ->
  (create_slots <= ns)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* a1/a2/a3 = type / major / minor, sign-extended by the RV64 ABI: the
     [bne s2,2] at +0x4c and the [beq s4,1] at +0xa6 compare the whole
     64-bit register, while the three [sh]s at +0x90/+0x94/+0x9a store
     exactly the low sixteen bits. *)
  m !!! Regidx (mword_of_int 11 : mword 5) = (sign_extend' 64 ty : mword 64) ->
  m !!! Regidx (mword_of_int 12 : mword 5) = (sign_extend' 64 major : mword 64) ->
  m !!! Regidx (mword_of_int 13 : mword 5) = (sign_extend' 64 minor : mword 64) ->
  (* PARKING PREMISE (hart-generic scheduler protocol) *)
  eb = true ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is pcE -∗
  (* the two persistent credentials ialloc's printk arm needs, and the
     rodata image the "." / ".." literals live in *)
  kernel_data -∗
  printk_env fsc_printk fsc_uart fsc_disk -∗
  bio_ctx fsc_bio (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) -∗
  log_ctx icfg_log fsc_bio fsc_fs fsc_cov fsc_logst icfg_dev -∗
  kalloc_env fsc_kalloc None -∗
  (* ---- THE ICACHE, THE ITABLE AND THE INODE REGION ---- *)
  is_itable2 fsc_itlock fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst icfg_nib icfg_dev -∗
  itable_inv -∗
  ic_escrows fsc_ic fsc_fs fsc_ireg fsc_cov fsc_logst -∗
  ic_sleeplocks fsc_ic -∗
  ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B).  Persistent,
     borrowed, never spent.  create is the only function in the tree that
     runs [ialloc], and [SpecIalloc] now takes this because
     [InodeRegion.ireg_claim_au] -- the one mover that mints a [c] column --
     does.  It rides the SAME channel [ireg_inv] does, from the syscall
     dispatch's [sysc_fs_env] down; its producer is the boot chain's
     ([IcacheRefDefs.ity_shoot] on fsinit's [ireg_boot]), terminating at the
     EXISTING [LinkForkretNF.wp_forkret_nf_ax] IOU. *)
  ireg_open -∗
  (* ---- the four superblock cells ---- *)
  sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  (* ---- THE RUNNING PROCESS, WHOLE ----
     create needs the pid quarter (every sleeplock records it), the p->cwd
     CELL and the cwd REFERENCE (namex's starting point) -- which is
     [ProcInv.proc_priv_cwd_pid]'s exact payout, and the reason the block
     is taken whole rather than in pieces.  create copies nothing to or
     from user memory, so nothing else in the block is touched and the
     block comes back at the SAME [V]. *)
  proc_priv γf pj pidv U -∗
  (* ---- the caller's NUL-terminated path buffer (a kernel buffer: every
     caller ran argstr into its own frame) ---- *)
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
  (* ---- the running-thread bundle and the disk fabric ---- *)
  procs_inv γs -∗
  dev_inv fsc_uart fsc_disk -∗
  disk_geom fsc_disk pd pav pu -∗
  is_lock fsc_dlock d_lock "virtio_disk"%string (disk_res_at fsc_disk pd pav pu) -∗
  bslots 3 -∗
  iref_slots ns -∗
  (* ---- THE OP-WIDE RESERVATION, IN SET FORM (section 18 clause 1) ---- *)
  log_opS icfg_log u Sb -∗
  (* ---- THE TRANSACTION TOKEN (durable-disk lane A, plan section 4b) ----
     create is the one function whose child is MID-BUILT across a call: a
     mkdir's child carries [nlink = 1] from +0xc4 and gets its two dot
     entries only at the interior [dirlink]s, and in between it is a
     directory with a link count and no dots -- exactly what
     [FsStateInode.inode_local] rules out.  So create SUSPENDS that inode's
     row for the window ([InodeRegion.ireg_arm]), which parks this token,
     and hands it back at the disarm.  Every other walk in the tree leaves
     its inode well-formed at each write and needs none of this.
     THE TOKEN COMES BACK ON EVERY ARM: create's caller ends the operation,
     and end_op takes the whole [LogInv.log_op]. *)
  log_tx icfg_log -∗
  (* ---- THE APPLICATION'S SIDE ----
     THE WALK: the PARENT-PREFIX one-shot at create's own path buffer
     ([FsAbsEra.ep_start]).  The syscall hands its [mknod_walk_pre_era]
     straight down ([FsAbsMknodFire.np_start_of_mknod]) and the START INUM
     is decided inside the walk: ROOTINO on an absolute fetch, the calling
     process's [pv_cwi] on a relative one.  The hop family is over the
     PARENT PREFIX, which is [SpecSysMknodAU.mknod_parent_elems]
     definitionally.
     THE EXISTS OBSERVATION: fired at create's own [dirlookup] when the name
     is already in the parent's entry map, and refunded on every arm that
     does not read it.
     THE FOUR COMMITS create's legs fire (round E2, lane E2-C), at the
     child's type-indexed content. *)
  ep_start fsc_fs (pv_cwi (us_V U)) P Pmiss pl -∗
  pf_at (dlookup_commit_at Γfs appE) Fex -∗
  cre_commits Γfs tyz ma mi Farm Fdots Fun Fok -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: create parks (ilock,
     bread, the whole fs cone), and a park moves the hart with interrupts
     off, so the crossing has nothing to do with SIE. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (ok made : bool)
    (k : nat) (qi s : Qp) (g : gname) (inum : mword 32)
    (dn : dinode) (bm : blkmap)
    (u' : nat) (Sb' : gset Z) (ns' : nat),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      pc_is ret_tgt -∗
      (* everything structural comes back untouched *)
      sb_ninodes ↦₄{dqn} (mword_of_int fsc_ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      sb_size ↦₄{dqbs} (mword_of_int fsc_size : mword 32) -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      (* NO ORDERING on the bitmap: create both ALLOCATES (balloc, under
         dirlink's writei) and FREES (itrunc, under the fail arm's
         iunlockput of a link-count-zero inode). *)
      proc_priv γf pj pidv U -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1] pfun i) -∗
      bslots 3 -∗
      (* THE LEDGER, EXACTLY.  This used to be the interval
         [ns - create_slots <= ns' <= ns] with an [ok = true -> S ns' <= ns]
         floor bolted on, and the header's ARM-G note recorded what was
         actually true underneath it: every failure arm returns the ledger
         WHOLE and every success arm keeps exactly ONE out (the reference to
         the inode it returns).  All nine of this function's continuation
         sites already computed those figures and then weakened them, so
         saying them outright costs nothing here and is what a CALLER needs:
         sys_mkdir and sys_mknod run their own [iunlockput], which hands the
         success arm's one back, and an interval cannot show that they end
         where they started.  The interval is recovered from this by [lia]
         under [create_slots <= ns]. *)
      ⌜if ok then (S ns' = ns)%nat else ns' = ns⌝ -∗
      iref_slots ns' -∗
      (* THE OP-WIDE SET GREW MONOTONICALLY AND THE COUNTER ONLY FELL, AND
         ON THE SUCCESS ARMS THE COUNTER STILL COVERS AN [iput].  No ceiling
         on [Sb' ∖ Sb] -- see the header.  The floor is GUARDED ON [ok] and
         that guard is forced, not a convenience: see the header. *)
      ⌜Sb ⊆ Sb' /\ (u' <= u)%nat /\ (ok = true -> (iput_units <= u')%nat)⌝ -∗
      log_opS icfg_log u' Sb' -∗
      (* THE TRANSACTION TOKEN GOES WITH THE ANSWER (durable-disk B''-tx2).
         No arm of create leaves an inode's row suspended (lane A), but the
         SUCCESS arms return a write-locked child, whose escrow holds half
         of the transaction's element -- so on those arms the token is
         inside [create_locked]'s [IcacheEscrow.ic_tx_dep] and there is
         nothing to hand back beside it.  On the failure arms nothing is
         locked and the whole token comes home. *)
      (if ok
       then (* BOTH SUCCESS ARMS RETURN A LOCKED INODE *)
         ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ientry k
          /\ (k < NINODE)%nat
          /\ 0 < bv_unsigned inum < 16 * Z.of_nat icfg_nib
          /\ cre_ok_pure ty major minor made dn⌝ ∗
         create_locked pidv k qi s g inum dn bm ∗
         (* ...the walk cursor, the legs' receipts and the observation *)
         cre_ok_arms Γfs tyz ma mi P Farm Fdots Fun Fok Fex pl made
           (bv_unsigned inum)
       else (* ARMS N / F-BAD / A-FAIL / FAIL: a0 = 0 and create holds
               nothing -- every inode it touched has been iunlockput. *)
         ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
          = (mword_of_int 0 : mword 64)⌝ ∗ log_tx icfg_log ∗
         (* the walk died, or the cursor comes home with the observation
            fired or not and the legs whole or the do-then-undo pair
            (ruling Q-h) *)
         cre_fail_arms Γfs fsc_fs tyz ma mi P Pmiss Farm Fdots Fun Fok Fex pl) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CREATE.
  Parameter wp_create_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γs : list gname) (j : nat) (γl : gname)
      (pd pav pu : mword 64)
 (γf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (ty major minor : mword 16)
      (U : ustate)
      (u : nat) (Sb : gset Z)
      (ns : nat)
      (pidv : mword 32) (dqb dqs dqbs dqn : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
      (Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)),
      wp_create_sconf_body γs j γl pd pav pu
 γf
 plen pfun ty major minor
                           U u Sb ns pidv dqb dqs dqbs dqn m K eb b lks
                           P Pmiss Farm Fdots Fun Fok Fex.
End CREATE.
