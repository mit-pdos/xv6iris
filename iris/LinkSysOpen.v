(* LinkSysOpen.v -- the sys_open proof composed with its callees'.

   THIRTEEN arguments.  Twelve are the plain arm's ([LinkArgint] through
   [LinkFdalloc]); the thirteenth is create, which only the O_CREATE arm
   calls, at the T_FILE carry ([LinkCreateAUF.CreateAUF]) rather than the
   landed [SpecCreate] one.  namei arrives at the ERA trace contract
   ([LinkNameiEra.NameiEra]); [LinkNameiEra]'s header records that this
   cone's assumption set is the walk's -- the standing platform axioms plus
   funext -- and [LinkCreateAUF]'s that ITS cone's assumption count is
   [LinkCreateAU]'s exactly, so this composition assumes nothing new.

   The module this builds seals [SpecSysOpen.SYSOPEN]: its one parameter
   [wp_sys_open], keyed on [om_create vom], with the plain arm re-exported
   from [ProofSysOpenAU.SysOpenPlainProof] (see [ProofSysOpenAUFull]'s
   header) and the create arm proved beside it. *)
Require Import LinkArgint LinkArgstr LinkBeginOp LinkNameiEra
        LinkIlock LinkIunlock LinkIunlockput LinkEndOp LinkFileclose
        LinkItrunc LinkFilealloc LinkFdalloc LinkCreateAUF
        ProofSysOpenAUFull.

Module SysOpen := SysOpenProof Argint Argstr BeginOp NameiEra Ilock
                               Iunlock Iunlockput EndOp Fileclose
                               Itrunc Filealloc Fdalloc CreateAUF.
