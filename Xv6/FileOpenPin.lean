/-
**THE PIN, AT THE DEED'S OWN INUM** -- §5a of Rocq `FileOpen.v`
(`iris/FileOpen.v`, pinned 1900b8a43) and the first lemma of
its section `FileOpenMiss`: the pure pins a read-only open at the line's
file `N` hands `PinnedObs`' walk.

* `f_pin_walks` / `f_pin_resolves`: at a PRESENT entry `s[N]? = some (i, bs)`
  the one-element path `[N]` walks `[ROOTINO; i]` and resolves to `AFile bs`
  at every view the claim admits (`fOk v s`);
* `f_pin_misses`: at an ABSENT class name the first hop misses.

## DEVIATIONS from Rocq

1. Inums `Nat`, maps as `Xv6/AppFilePure.lean` deviations 1-2.
2. The section binders are dropped: the three lemmas are pure.
-/
import Xv6.AppFilePure
import Xv6.PinnedObs

namespace Xv6

/-- Rocq `f_pin_walks`. -/
theorem fPin_walks (i : Nat) (bs : List (BitVec 8)) (N : Fname) (s : Dst) (cw : Nat)
    (pl : List (BitVec 8)) (hs : s[N]? = some (i, bs)) (hel : pathElems pl = [N])
    (hst : umStartOf cw pl = ROOTINO) :
    pinWalksAt (fun v : Aview => fOk v s) cw pl [ROOTINO, i] i := by
  unfold pinWalksAt
  rw [hel]
  refine ⟨by simpa using hst, by simp, ?_⟩
  intro v hv
  have hp := fOk_pin v s N i bs hv hs
  exact Arun.cons _ _ _ _ _ (by simpa using hp.1) (Arun.nil _)

/-- Rocq `f_pin_resolves`. -/
theorem fPin_resolves (i : Nat) (bs : List (BitVec 8)) (N : Fname) (s : Dst) (cw : Nat)
    (pl : List (BitVec 8)) (hs : s[N]? = some (i, bs)) (hel : pathElems pl = [N])
    (hst : umStartOf cw pl = ROOTINO) :
    pinResolvesAbs (fun v : Aview => fOk v s) cw pl [ROOTINO, i] i (.AFile bs) := by
  refine ⟨fPin_walks i bs N s cw pl hs hel hst, ?_⟩
  intro v hv
  exact ⟨1, (fOk_pin v s N i bs hv hs).2⟩

/-- Rocq `f_pin_misses`: the pin an ABSENT class name gives the walk. -/
theorem fPin_misses (N : Fname) (s : Dst) (cw : Nat) (pl : List (BitVec 8))
    (hN : uname N) (hs : s[N]? = none) (hel : pathElems pl = [N])
    (hst : umStartOf cw pl = ROOTINO) :
    pinMissesAt (fun v : Aview => fOk v s) cw pl ROOTINO := by
  refine ⟨hst, ?_⟩
  intro v nm hp hnm
  rw [hel] at hnm
  simp at hnm
  subst hnm
  exact fOk_absent v s N hp hN hs

end Xv6
