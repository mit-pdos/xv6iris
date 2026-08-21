(* LinkSysUnlink.v -- instantiates the sys_unlink proof against its twelve
   callees' proofs.  Sealed, so this is the only place the thirteen ever
   meet.

   THIS FILE RETIRED THE TREE'S LAST STUB AXIOM.  While the walk was being
   built it supplied [SpecSysUnlink.SYSUNLINK] with an [Axiom] at the REAL
   shape -- visible to [Print Assumptions] and to
   [tools/proof_coverage.py]'s textual scan, unlike a bare [Declare Module]
   (claude-notes/design/spec-modules.md, "An ASSUMED callee: Module Type +
   an Axiom in the link").  The walk is landed and sealed, so the axiom is
   gone and sysfile.c is 16/16.

   NOTHING NEW ENTERS THE CONE.  All twelve are already linked elsewhere:
   argstr, begin_op, iunlockput and end_op by LinkSysChdir.v; ilock and
   nameiparent likewise; namecmp, dirlookup, readi, writei, memset and
   iupdate by LinkCreate.v and LinkSysOpen.v.  So the assumption set is the
   standing platform five plus [functional_extensionality_dep].

   WHAT THE COMPOSITION RESTS ON, recorded at the point of use in
   SpecSysUnlink.v's header and machine-checked in SysUnlinkBudget.v:

   - the LEDGER FRAGMENTS are released and settled inside this function.
     The zeroing's [writei] releases the removed record's ticket
     caller-side ([DirLinks.dir_links_unlink]); the FILE arm spends it at
     [ip->nlink--], and the T_DIR arm spends the child's [".."] ticket at
     [dp->nlink--] and the TAGGED parent-record unit -- both halves of the
     child's parent register -- at [ip->nlink--], which RESETS the register
     before the inum can be reclaimed.  Nothing colour-shaped crosses this
     interface.
   - the two facts the T_DIR arm needs about the shape of the filesystem --
     (D1) the child's [".."] names the parent, and (D2) a directory holding
     a live subdirectory entry has at least two links -- are DERIVED inside
     the walk, from the ledger's own parent register and its (T1')/lower
     count clauses.  They are not premises and they are not axioms; the
     campaign record is claude-notes/projects/fs-fragments-campaign.md,
     V4 and V5'. *)
From Stdlib Require Import ZArith List.
(* the whole-function memset spec [MEMSET] is [MemsetArray]
   (LinkMemsetArray), not [LinkMemset.Memset] -- the latter is the
   [MEMSET_PARTS] block layer.  LinkBalloc.v and LinkIalloc.v carry the
   same note for the same reason. *)
Require Import LinkArgstr LinkBeginOp LinkNameiparent LinkIlock LinkNamecmp
        LinkDirlookup LinkMemsetArray LinkReadi LinkWritei LinkIupdate
        LinkIunlockput LinkEndOp LinkPanic
        ProofSysUnlink.

Module SysUnlink := SysUnlinkProof Argstr BeginOp Nameiparent Ilock Namecmp
                                   Dirlookup MemsetArray Readi Writei Iupdate
                                   Iunlockput EndOp Panic.
