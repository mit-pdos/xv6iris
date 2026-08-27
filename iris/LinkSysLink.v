(* LinkSysLink.v -- instantiates the sys_link proof against its eleven
   callees' proofs.  Sealed, so this is the only place the twelve ever meet.

   NOTHING NEW ENTERS THE CONE.  All eleven are already linked: argstr,
   begin_op, iunlockput and end_op by LinkSysChdir.v; namei, ilock, iunlock
   and iput likewise; nameiparent, iupdate and dirlink by LinkCreate.v.  So
   the assumption set is exactly LinkSysChdir.v's -- the standing platform
   five plus funext.

   THE TWO THINGS THE COMPOSITION RESTS ON, both recorded at the point of
   use in SpecSysLink.v's header and machine-checked in SysLinkBudget.v:

   - the LINK FRAGMENT is minted and settled inside this function.  The
     [ip->nlink++; iupdate(ip)] at +0x5e..+0x66 mints one
     [FsStateLink.link_tok] at [ip] against the count that pays for it; the
     success arm DEPOSITS it into the parent's [IcacheEscrow.dlinks] at the
     dirlink, caller-side; every route to [bad:] CONSUMES it back at the
     [ip->nlink--].  Nothing else crosses this interface.
   - dirlink's FOUND arm is payable only through [SpecDirlink]'s separate
     found-arm clause.  sys_link cannot refute that arm the way create does
     -- it never looks the name up before linking it -- and seven from the
     nine its two walks and its mint can leave is two, against an
     [iput_units] of three ([SysLinkBudget.sl_found_counted_busts_by_one]).

   The reference ledger closes at THREE, one more than sys_chdir's two,
   because nameiparent runs with [ip] already held. *)
Require Import LinkArgstr LinkBeginOp LinkNamei LinkNameiparent LinkIlock
        LinkIunlock LinkIupdate LinkDirlink LinkIput LinkIunlockput LinkEndOp
        ProofSysLink.

Module SysLink := SysLinkProof Argstr BeginOp Namei Nameiparent Ilock Iunlock
                              Iupdate Dirlink Iput Iunlockput EndOp.
