(* LinkSysUnlinkAU.v -- instantiates the sys_unlink AU proof against its
   twelve callees' proofs, so [SpecSysUnlinkAU.SYSUNLINK_AU] is an
   unconditional theorem about the machine.

   [LinkSysUnlink.v]'s shape with ONE substitution: nameiparent enters at
   the ERA trace contract ([LinkNparWrapEra.NparWrap], the walk that fires
   the parent-prefix hop family) rather than at
   [LinkNameiparent.Nameiparent].  Nothing else changes and NOTHING NEW
   ENTERS THE CONE: every one of the twelve is already linked elsewhere,
   and the era nameiparent is [LinkNparWrapEra]'s, whose own assumption set
   is byte-identical to [LinkNamexEra]'s (the two platform axioms plus
   funext).

   THE AU IS A PARALLEL FORM, NOT A REPLACEMENT (R10): [LinkSysUnlink.v]
   and its [SysUnlink] stand untouched beside this, exactly as
   [LinkSysMknodAU] stands beside [LinkSysMknod]. *)
From Stdlib Require Import ZArith List.
(* the whole-function memset spec [MEMSET] is [MemsetArray]
   (LinkMemsetArray), not [LinkMemset.Memset] -- the latter is the
   [MEMSET_PARTS] block layer.  LinkSysUnlink.v carries the same note. *)
Require Import LinkArgstr LinkBeginOp LinkNparWrapEra LinkIlock LinkNamecmp
        LinkDirlookup LinkMemsetArray LinkReadi LinkWritei LinkIupdate
        LinkIunlockput LinkEndOp LinkPanic
        ProofSysUnlinkAU.

Module SysUnlinkAU := SysUnlinkAUProof Argstr BeginOp NparWrap Ilock Namecmp
                                       Dirlookup MemsetArray Readi Writei
                                       Iupdate Iunlockput EndOp Panic.
