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
