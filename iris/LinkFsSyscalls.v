(* LinkFsSyscalls.v -- instantiates F3's friendly wrappers against the two
   sealed syscall contracts they repackage.

   The wrappers in FsSyscalls.v are FUNCTORS over [SYSMKDIR] / [SYSCHDIR],
   F2's [FsLookupTree] pattern: the tree layer never enters a Link cone, so
   FsSyscalls.v itself compiles against the definitional layer alone and can
   be checked in parallel with every proof file.  This is the one place the
   packaging meets the proofs, and it exists so that [Print Assumptions] can
   be run on a CLOSED term:

     Print Assumptions FsMkdir.wp_sys_mkdir_friendly.
       -> the five platform axioms + funext (LinkSysMkdir.v's own set,
          unchanged)
     Print Assumptions FsChdir.wp_sys_chdir_friendly.
       -> the five platform axioms + funext (LinkSysChdir.v's set, unchanged)

   THE LIFT ADDS NOTHING TO EITHER SET, which is F2's bar and this cone's
   only quantitative claim: the friendly layer is a repackaging, not a new
   assumption.  (What it does NOT add is a tree delta either -- see
   FsSyscalls.v's header, stops S1-S3.) *)
Require Import LinkSysMkdir LinkSysChdir FsSyscalls.

Module FsMkdir := FsSysMkdir SysMkdir.
Module FsChdir := FsSysChdir SysChdir.
