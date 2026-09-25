/-
**THE APPLICATION'S DURABLE INSTANCE** -- a port of Rocq `AppDur.v`
(`/shared/xv6rocq/iris/AppDur.v`): the application's claim about the committed
abstract state, beside the snapshot, tied by HALF an authority.  Crash batch
C-1, agent CG; user ruling D37 (the generic application slot, as Rocq).

THE TIE (Rocq's header).  The kernel's durable snapshot (`Xv6/FsDurSnap.lean`,
`fsSnap`) keeps the KERNEL half of its abstract map's authority; the
application's durable claim is a SEPARATE conjunct of the crash slot, holding
the GUEST half at the same gname beside its claim about the map's view.
Agreement is the identification.

THREE CROSSINGS, ONE TRANSPORT (`Xv6/AppInv.lean`'s `appXferRaw`): at the
COMMIT the file system's law mints a fresh snapshot and hands its guest half
here, where the running claim is copied onto it (`appDurRaw_clone`); at
POWER-ON the clone (`Xv6/FsCrash.lean`, `pFs_swap`) does the same off the crash
slot's own guest; at the BOOT the lent guest meets the clone's kernel half.

RAW FIRST, PINNED SECOND.  `appDurRaw` takes the predicate as an argument, so
the system theorem can state the crash slot before any era's record exists;
`appGuest` is the same thing at the application's own predicate, the ONE value
of the WAL's opaque guest index (`fsCrashSeamAt`, `snapLawAt`) the tree ever
supplies.

## DEVIATIONS from Rocq

1. Rocq's `ghost_map_auth gt (1/2) I` is
   `gt ↪●MAP{DFrac.own (1 : Qp).half} I` (`snapGuest`'s spelling,
   `Xv6/FsDurSnap.lean` deviation 3); `abs_view` is `absView`, `app_pred` is
   `Appcfg.appPred`.
2. `appDurRaw_open` pulls the two existentials through the later separately
   (`later_exists_except0`, then `later_exists` over the inhabited node map),
   where Rocq's one `bi.later_exist_except_0` plus `iDestruct` does both.

## NOT PORTED (crash brief D36; uses checked over `/shared/xv6rocq/iris/*.v`)

* `app_dur_raw_agree` -- no use outside AppDur.v.
-/
import Xv6.AppInv

namespace Xv6

open Iris Iris.BI Iris.ProofMode Std MachCSL

set_option linter.unusedSectionVars false

section AppDurRaw
variable {GF : BundledGFunctors} [FsTopG GF]

/-- THE DURABLE CLAIM at a predicate and a snapshot map name `gt`: the guest
half of the map's authority beside the claim at the map's view, at SOME
instance of the application's names (Rocq `app_dur_raw`). -/
def appDurRaw {N : Type} (A : N → Aview → IProp GF) (gt : GName) : IProp GF :=
  iprop(∃ (r : N) (I : RegMapF FsNode),
    (gt ↪●MAP{DFrac.own (1 : Qp).half} I) ∗ A r (absView I))

/-- OPENING A LATER-SHAPED GUEST: the half is timeless and comes out, the claim
stays under its later (Rocq `app_dur_raw_open`). -/
theorem appDurRaw_open {N : Type} (A : N → Aview → IProp GF) (gt : GName) :
    ▷ appDurRaw A gt ⊢
      ◇ ∃ (r : N) (I : RegMapF FsNode),
        (gt ↪●MAP{DFrac.own (1 : Qp).half} I) ∗ ▷ A r (absView I) := by
  unfold appDurRaw
  iintro H
  imod later_exists_except0 $$ H with ⟨%r, H⟩
  ihave ⟨%I, H⟩ := (later_exists (α := RegMapF FsNode)).2 $$ H
  icases later_sep.1 $$ H with ⟨>Hh, Hp⟩
  imodintro
  iexists r, I
  iframe Hh Hp

/-- PACKING: the guest half beside a claim at the same map, under the later the
transport left on the claim (Rocq `app_dur_raw_pack`). -/
theorem appDurRaw_pack {N : Type} (A : N → Aview → IProp GF) (gt : GName)
    (I : RegMapF FsNode) :
    (gt ↪●MAP{DFrac.own (1 : Qp).half} I) ⊢
      (∃ r : N, ▷ A r (absView I)) -∗ ▷ appDurRaw A gt := by
  iintro Hh ⟨%r, Hp⟩
  inext
  unfold appDurRaw
  iexists r, I
  iframe Hh Hp

/-- THE CLONE (the commit and the PowerOn arm): run the transport on a claim,
keep the original, and pack the copy onto a fresh guest half at the same map
(Rocq `app_dur_raw_clone`). -/
theorem appDurRaw_clone {N : Type} (A : N → Aview → IProp GF) (gt : GName)
    (I : RegMapF FsNode) (r : N) :
    appXferRaw A ⊢ (gt ↪●MAP{DFrac.own (1 : Qp).half} I) -∗ ▷ A r (absView I) ==∗
      ▷ A r (absView I) ∗ ▷ appDurRaw A gt := by
  iintro #Hx Hh Hp
  unfold appXferRaw
  imod Hx $$ %r %(absView I) Hp with ⟨Hp, Hnew⟩
  imodintro
  iframe Hp
  iapply appDurRaw_pack A gt I $$ Hh Hnew

end AppDurRaw

section AppDur
variable {GF : BundledGFunctors} [FsTopG GF] [Appcfg GF]

/-- THE GUEST, at the application's own predicate: the one value the WAL's
opaque index `G : GName → IProp` ever takes (Rocq `app_guest`). -/
def appGuest (gt : GName) : IProp GF := appDurRaw appPred gt

end AppDur

end Xv6
