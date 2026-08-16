(* LinkSysOpen.v -- instantiates the sys_open proof against its thirteen
   callees' proofs.  Sealed, so this is the only place the fourteen ever meet.

   NOTHING NEW ENTERS THE CONE.  Every one of the thirteen is already linked:
   argint by LinkSysExit.v; argstr, begin_op, iunlockput and end_op by
   LinkSysChdir.v; namei and ilock likewise; create by LinkSysMkdir.v;
   iunlock, itrunc, filealloc, fdalloc and fileclose by LinkSysLink.v /
   LinkSysPipe.v / LinkSysClose.v.  So the assumption set is LinkSysMkdir.v's
   -- the standing platform five plus funext, plus [create_fresh_ty], which
   comes in through create's ialloc and through nothing else.

   THE THREE THINGS THE COMPOSITION RESTS ON, all recorded at the point of
   use in SpecSysOpen.v's header and machine-checked in SysOpenBudget.v:

   - THE LOG LEDGER CLOSES AT THREE, AND THE FLOOR IS THE WALK.  The two
     entry arms meet at +0x4a with different counts -- the else arm leaves
     nine, the O_CREATE arm can offer only [SpecCreate]'s [ok = true] floor,
     which is [iput_units] = three -- and three is EXACTLY what each of ARMs
     D/E/F spends on its [iunlockput] ([so_join_exact]).  Without S6-mkdir's
     floor the create arm arrives with a bare [u' <= u] whose corner is zero
     and the first [iunlockput] past the join is unpayable
     ([so_create_nofloor_busts]).  The COUNTED namei contract busts the same
     ledger at [L = 3] ([so_counted_namei_busts]), so the SET form is forced.
   - THE [+1] INODE REFERENCE NEVER LEAVES.  Instead of an [iput] the success
     arm PARKS it in [f->ip] as [FileInvDefs.inode_pay], which is why the
     reference ledger is spend-at-most rather than conserved and why the
     success arm ends one unit short.  sys_chdir's [p->cwd] sentence, one
     descriptor further along.
   - THE WRITABLE-FD-IS-NOT-A-DIRECTORY WITNESS is discharged FROM THE CODE
     on both arms ([so_pay_witness]): the O_CREATE arm passes T_FILE, the
     else arm's test at +0xf6 forces [omode = O_RDONLY] on any T_DIR inode.
     This is where filewrite's [DirView.dir_ok] obligation is actually paid.

   The file-table ledger is one unit in, one unit out on every one of the
   eight arms; ARM F-FAIL's extra [fileclose] is free because the file it
   closes is still FD_NONE ([SpecFileclose.fileclose_env_none]).

   panic is NOT a module here.  Every panic sys_open can reach is inside a
   callee; the [kernel_data] / [panic_env] the contract takes are threaded
   down to the callees' own arms. *)
Require Import LinkArgint LinkArgstr LinkBeginOp LinkCreate LinkNamei
        LinkIlock LinkIunlock LinkIunlockput LinkEndOp LinkFileclose
        LinkItrunc LinkFilealloc LinkFdalloc
        ProofSysOpen.

Module SysOpen := SysOpenProof Argint Argstr BeginOp Create Namei Ilock
                              Iunlock Iunlockput EndOp Fileclose Itrunc
                              Filealloc Fdalloc.
