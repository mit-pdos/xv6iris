(* LinkSysUnlink.v -- instantiates the sys_unlink proof against its twelve
   callees' proofs, so [SpecSysUnlink.SYSUNLINK] is an unconditional
   theorem about the machine.

   nameiparent enters at the ERA trace contract
   ([LinkNparWrapEra.NparWrap], the walk that fires the parent-prefix hop
   family).  NOTHING NEW ENTERS THE CONE: every one of the twelve is
   already linked elsewhere, and the era nameiparent is
   [LinkNparWrapEra]'s, whose own assumption set is byte-identical to
   [LinkNamexEra]'s (the two platform axioms plus funext).

   THIS IS THE ONLY LINK: sys_unlink has one contract and one proof. *)
From Stdlib Require Import ZArith List.
(* the whole-function memset spec [MEMSET] is [MemsetArray]
   (LinkMemsetArray), not [LinkMemset.Memset] -- the latter is the
   [MEMSET_PARTS] block layer. *)
Require Import LinkArgstr LinkBeginOp LinkNparWrapEra LinkIlock LinkNamecmp
        LinkDirlookup LinkMemsetArray LinkReadi LinkWritei LinkIupdate
        LinkIunlockput LinkEndOp LinkPanic
        ProofSysUnlink.

Module SysUnlink := SysUnlinkProof Argstr BeginOp NparWrap Ilock Namecmp
                                   Dirlookup MemsetArray Readi Writei
                                   Iupdate Iunlockput EndOp Panic.
