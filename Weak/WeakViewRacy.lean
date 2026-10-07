/-
Weak: **the `wp_wracy_load` experiment** (PROTOTYPE) — a persistent `wsLb` floor alone drives
the racy-load exclusion; no exact fragment of the hart's weak state is needed at racy sites.

Rocq: `iris/WeakViewRacy.v` @ xxvzwolszwmp.

Rocq header (abridged, Rocq vocabulary): admissibility is ANTITONE in the hart's state —
`wbyte_ok` depends on `wm_ws` only through `readable … ws vpre a t` (excluding writes in
`Nat.max vpre (coh ws a)`), so a LARGER `ws` excludes MORE timestamps.  Racy clients want to
shrink the admissible set, which is driven by knowing the hart's view is AT LEAST something:
exactly a lower bound.  `WeakKpt.wbyte_ok_ge` already takes `tc <= w_vrNew (wm_ws s)` as a bare
inequality, so the single persistent `ws_lb` of `WeakViewMono` serves both the owned and the
racy layer.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention (name map below).
2. STATEMENT SHAPES: Rocq `P -∗ Q ==∗ R` is `P ∗ Q ⊢ |==> R`, `P -∗ Q -∗ ⌜φ⌝` is
   `P ∗ Q ⊢ ⌜φ⌝` (the `WeakViewMono` convention); the camera context `weakViewG Σ` is
   `[WeakViewG GF]`.
3. `wbyteOkGeFromLb`, `wadmNotStaleFromLb`, `wracyExclusionAfterStep` take
   `ak.akIfetch = false` (resp. `rak.akIfetch = false`), inherited from the Lean
   `WeakKpt.wbyteOkGe` (O2/D2: a fetch reads through the i-cache view `itv`, which the data-view
   cover does not bound — `WeakKpt` header deviation 2).  The premise sits just before the
   cover premise, as in `wbyteOkGe`.
4. `rn : N` with `N.to_nat rn` is `rn : Nat` (the Lean `wadm`); `Arch.pa` is `PAddr`;
   `is_Some (log_byte …)` is `(logByte …).isSome = true`; `acc_addr` is `WeakInterp.accAddr`.

**Name map** (Rocq → Lean): `ws_lb_survives_step`→`wsLbSurvivesStep`,
`wbyte_ok_ge_from_lb`→`wbyteOkGeFromLb`, `wadm_not_stale_from_lb`→`wadmNotStaleFromLb`,
`wracy_exclusion_after_step`→`wracyExclusionAfterStep`.

**Dropped:** none.
-/
import Weak.WeakViewMono
import Weak.WeakRacy
import Weak.WeakKpt

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp

section racyLb

variable {GF : BundledGFunctors} [WeakViewG GF]

/-! ## 1. The floor is never rebased. -/

theorem wsLbSurvivesStep (γ : WviewNames) (w w' w0 : Wstate) (hle : wsLe w w') :
    wsAuth (GF := GF) γ w ∗ wsLb γ w0 ⊢ |==> (wsAuth γ w' ∗ wsLb γ w0 ∗ ⌜wsLe w0 w'⌝) := by
  iintro ⟨Ha, #Hlb⟩
  ihave %hle0 := wsLbValid γ w w0 $$ [Ha]
  · isplitl [Ha]
    · iexact Ha
    · iexact Hlb
  imod wsUpdate γ w w' hle $$ Ha with Ha
  imodintro
  isplitl [Ha]
  · iexact Ha
  isplitl []
  · iexact Hlb
  ipureintro
  exact wsLeTrans hle0 hle

/-! ## 2. The exclusion, driven by the floor alone. -/

theorem wbyteOkGeFromLb (γ : WviewNames) (s : Wmstate) (w0 : Wstate) (ak : AkInfo) (a : Int)
    (t tc : Nat) (b : BitVec 8) :
    1 ≤ tc →
    ak.akIfetch = false →
    tc ≤ w0.wVrNew →
    (logByte (wimg s) s.wmLog tc a).isSome = true →
    wbyteOk s ak a t b →
    wsAuth (GF := GF) γ s.wmWs ∗ wsLb γ w0 ⊢ ⌜tc ≤ t⌝ := by
  intro htc1 hif htc0 hlog hok
  iintro H
  ihave %hle := wsLbValid γ s.wmWs w0 $$ H
  ipureintro
  obtain ⟨_, _, _, hvr, _⟩ := hle
  exact wbyteOkGe s ak a t tc b htc1 hif (Nat.le_trans htc0 hvr) hlog hok

/-! ## 3. The same, at the rule's actual oracle surface. -/

theorem wadmNotStaleFromLb (γ : WviewNames) (s : Wmstate) (w0 : Wstate) (rak : AkInfo)
    (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (tc j : Nat) :
    j < rn →
    1 ≤ tc →
    rak.akIfetch = false →
    tc ≤ w0.wVrNew →
    (logByte (wimg s) s.wmLog tc (WeakInterp.accAddr ra j)).isSome = true →
    wadm s rak ra rn w →
    wsAuth (GF := GF) γ s.wmWs ∗ wsLb γ w0 ⊢
      ⌜∃ t, tc ≤ t ∧ wbyteOk s rak (WeakInterp.accAddr ra j) t (nthByte w j)⌝ := by
  intro hj htc1 hif htc0 hlog hadm
  obtain ⟨t, hok⟩ := hadm j hj
  iintro H
  ihave %hge := wbyteOkGeFromLb γ s w0 rak _ t tc _ htc1 hif htc0 hlog hok $$ H
  ipureintro
  exact ⟨t, hge, hok⟩

/-! ## 4. THE POINT, in one statement. -/

theorem wracyExclusionAfterStep (γ : WviewNames) (s s' : Wmstate) (w0 : Wstate) (rak : AkInfo)
    (ra : PAddr) (rn : Nat) (w : BitVec (8 * rn)) (tc j : Nat) :
    wsLe s.wmWs s'.wmWs →
    j < rn →
    1 ≤ tc →
    rak.akIfetch = false →
    tc ≤ w0.wVrNew →
    (logByte (wimg s') s'.wmLog tc (WeakInterp.accAddr ra j)).isSome = true →
    wadm s' rak ra rn w →
    wsAuth (GF := GF) γ s.wmWs ∗ wsLb γ w0 ⊢
      |==> (wsAuth γ s'.wmWs ∗
        ⌜∃ t, tc ≤ t ∧ wbyteOk s' rak (WeakInterp.accAddr ra j) t (nthByte w j)⌝) := by
  intro hstep hj htc1 hif htc0 hlog hadm
  iintro ⟨Ha, #Hlb⟩
  imod wsLbSurvivesStep γ s.wmWs s'.wmWs w0 hstep $$ [Ha] with ⟨Ha, -, -⟩
  · isplitl [Ha]
    · iexact Ha
    · iexact Hlb
  ihave %hfresh := wadmNotStaleFromLb γ s' w0 rak ra rn w tc j hj htc1 hif htc0 hlog hadm $$ [Ha]
  · isplitl [Ha]
    · iexact Ha
    · iexact Hlb
  imodintro
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    exact hfresh

end racyLb

end Weak
