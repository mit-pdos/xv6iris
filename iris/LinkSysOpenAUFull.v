(* LinkSysOpenAUFull.v -- the WHOLE sys_open ATOMIC-UPDATE proof (both
   arms) composed with its callees'.

   [LinkSysOpenAU.v]'s cone with ONE addition and no other difference:
   create arrives, at the T_FILE carry ([LinkCreateAUF.CreateAUF]) rather
   than the landed [SpecCreate] one.  [LinkCreateAUF]'s header records
   that ITS cone's assumption count is [LinkCreateAU]'s exactly, and every
   other callee here is already linked by [LinkSysOpenAU.v], so this
   composition assumes nothing the landed sys_open and the plain AU arm do
   not.

   The module this builds seals [SpecSysOpenAU.SYSOPEN_AU] WHOLE -- both
   [wp_sys_open_au_plain] (re-exported from the landed
   [ProofSysOpenAU.SysOpenAUPlainProof]; see [ProofSysOpenAUFull]'s
   header) and [wp_sys_open_au_create]. *)
Require Import LinkArgint LinkArgstr LinkBeginOp LinkNameiEra
        LinkIlock LinkIunlock LinkIunlockput LinkEndOp LinkFileclose
        LinkItrunc LinkFilealloc LinkFdalloc LinkCreateAUF
        ProofSysOpenAUFull.
Require Import TsoCtx.

Module SysOpenAUFull := SysOpenAUProof Argint Argstr BeginOp NameiEra Ilock
                                       Iunlock Iunlockput EndOp Fileclose
                                       Itrunc Filealloc Fdalloc CreateAUF.
