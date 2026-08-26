(* ====================================================================== *)
(*  OFF THE BUILD (durable-disk lane E-unpin).  This file's row in          *)
(*  iris/_CoqProject is commented out: it is part of the era-0             *)
(*  pinned-/init story, whose premises were                                *)
(*  [FsCfgBoot.fs_cfg_alloc]'s [dv_pin ROOTINO ...] / [fv_pin 7 ...] --    *)
(*  image-CONTENT facts, false at any era after a crash, now removed from  *)
(*  the boot chain (era 0 included).  The source is KEPT, unedited below,  *)
(*  to be PORTED by the file-system behaviour project onto its abstract    *)
(*  state; the handoff banner at the top of                                *)
(*  claude-notes/projects/namei-pinned-lookup.md is the owner's ruling and *)
(*  the full list of files taken off the build.                            *)
(* ====================================================================== *)
(* LinkNameiPinned.v -- the PINNED walk's two functors at their proven
   module, i.e. where the pinned namei stops having a parameter.

   [DirViewPin.NameiPinnedProof] (the pinned walk over an arbitrary expected
   chain) and [NameiInitPinned.NameiInitPinnedProof] (that walk at boot's one
   chain, [("init", 7)]) both functor over [SpecNameiTr.NAMEI_TR].  N-3 landed
   [LinkNameiTr.NameiTr] : NAMEI_TR with no axiom of its own, so applying them
   here leaves no module parameter and no new assumption: both theorems sit at
   the tree's standing baseline -- the five platform reservation externs and
   functional extensionality.

   THIS IS THE ONLY FILE THAT MAY APPLY THEM.  Doing it in [DirViewPin.v] or
   [NameiInitPinned.v] instead is what put the whole namex link cone (336
   files, 57 [Link*.v]) into every client of those files -- [SpecKexecPinned.v]
   among them, a [Spec*.v] that does not use the closed form at all. *)
Require Import DirViewPin.
Require Import NameiInitPinned.
Require Import LinkNameiTr.

Module NameiPinned := DirViewPin.NameiPinnedProof LinkNameiTr.NameiTr.

Module InitPinned :=
  NameiInitPinned.NameiInitPinnedProof LinkNameiTr.NameiTr.
