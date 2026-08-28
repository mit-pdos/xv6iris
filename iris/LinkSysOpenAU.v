(* LinkSysOpenAU.v -- the sys_open ATOMIC-UPDATE proof (PLAIN ARM) composed
   with its callees'.

   [LinkSysOpen.v]'s cone with TWO differences and no others:

   - namei arrives at the ERA trace contract ([LinkNameiEra.NameiEra])
     instead of the landed one.  [LinkNameiEra]'s header records that this
     cone's assumption set is the walk's -- the standing platform axioms
     plus funext -- so nothing new enters here.
   - create does NOT arrive at all.  The plain form excludes O_CREATE by
     premise, so the create arm is refuted at the [c.beqz] rather than
     proved, and the walk has twelve callees where the landed one has
     thirteen.  When the O_CREATE arm lands it brings a create-AU argument
     back (at [ty = T_FILE]; [SpecCreateAU] is T_DEVICE-pinned, see
     [SpecSysOpenAUPlain]'s header).

   Every remaining callee is already linked by [LinkSysOpen.v], and the era
   walk by [LinkSysMknodAU.v]'s cone, so this composition assumes nothing
   the landed sys_open does not. *)
Require Import LinkArgint LinkArgstr LinkBeginOp LinkNameiEra
        LinkIlock LinkIunlock LinkIunlockput LinkEndOp LinkFileclose
        LinkItrunc LinkFilealloc LinkFdalloc
        ProofSysOpenAU.

Module SysOpenAU := SysOpenAUPlainProof Argint Argstr BeginOp NameiEra Ilock
                                        Iunlock Iunlockput EndOp Fileclose
                                        Itrunc Filealloc Fdalloc.
