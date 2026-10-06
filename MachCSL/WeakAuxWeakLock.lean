/-
MachCSL: the EXCLUSIVE-AUTH spinlock ghost state of the Rocq `WpLock.v` (its section
"The lock's ghost state" and "the four state transitions"), for the weak-memory port.

Rocq: `iris/WpLock.v` @ xxvzwolszwmp, lines 40-210 (`lock_state`, `lockUR`, `lockG`,
`lock_auth`, `lock_frag`, `locked`, `locked_pre`, the ghost laws and the four transitions).

WHY A SHIM.  The Lean SC lock kit (`MachCSL.Lock`, the TSO port) replaced Rocq's
`excl_auth (leibnizO lock_state)` by a half/half ghost variable carrying the acquire position
(`lockHalf`) and a context-indexed `locked`, so the Rocq camera the weak files consume
(`WeakLock`, `AxCondM4`, `AxLeafS5`, `AxRelease3/4`, `AxSpinRow3`, `AxSpinCtl3` use `locked` /
`locked_pre` / `lock_auth` / `lock_frag`) has no Lean counterpart.  This file is that camera,
Rocq-literal, under names that do not collide with `MachCSL.Lock`'s.

**Deviations from Rocq.**

1. NAMES.  `lock_state` is `MachCSL.LockState` (the same `Option (CPU × Bool)`, already in
   `MachCSL.Resources`).  `lockG` is the class `LockExG GF` (field `lockInG : ElemG GF LockExRF`,
   the `Weak/AxGhost.lean` deviation 3 precedent); `lockUR` is `LockExUR` =
   `Auth (Option (Excl (DiscreteO LockState)))` (iris-lean's `ExclAuthUR`; `leibnizO` is
   `DiscreteO`).  `locked` / `locked_pre` are `lockedEx` / `lockedPreEx` (`MachCSL.locked` and
   `MachCSL.lockedPre` are the TSO kit's, a different predicate).
2. STATEMENT SHAPES (the `Weak/WeakStore.lean` deviation 3 convention): Rocq `A -∗ B -∗ C` is
   `A ⊢ B -∗ C`, `A -∗ B ==∗ C` is `A ⊢ B -∗ |==> C`.
3. `lockExAlloc` and `lockKeepPure` (Lean-only): `lockExAlloc` is the `own_alloc (●E None ⋅ ◯E None)` that Rocq inlines in
   `WeakLock.wlock_alloc` / `wplock_alloc`.

**Rocq → Lean name map.**  `lock_state` `LockState`, `lockUR` `LockExUR`, `lockG` `LockExG`,
`lock_inG` `LockExG.lockInG`, `lock_auth` `lockAuth`, `lock_frag` `lockFrag`, `locked`
`lockedEx`, `locked_pre` `lockedPreEx`, `lock_auth_timeless` `lockAuth_timeless`,
`lock_frag_timeless` `lockFrag_timeless`, `lock_frag_agree` `lockFragAgree`,
`lock_frag_exclusive` `lockFragExclusive`, `locked_exclusive` `lockedExExclusive`,
`locked_state` `lockedExState`, `locked_pre_state` `lockedPreExState`, `lock_state_update`
`lockStateUpdate`, `lock_take` `lockTake`, `lock_setcpu` `lockSetcpu`, `lock_clrcpu`
`lockClrcpu`, `lock_give` `lockGive`.

**Not ported** (no weak file uses them): `lockΣ`, `subG_lockΣ` (no `gFunctors` lists),
`lk_cpu_val*`, `locked_cpu_eq`, `lock_tok_excl*`, and the rest of `WpLock.v` (the SC lock
library proper, whose Lean counterpart is `MachCSL.Lock`/`MachCSL.WpLock`).
-/
import MachCSL.Resources
import Iris.Algebra.Lib.ExclAuth
import Iris.Instances.IProp
import Iris.ProofMode

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Iris.OFE

/-- The lock state as an OFE (Rocq `leibnizO lock_state`). -/
abbrev LockExO : Type := DiscreteO LockState

/-- Rocq `lockUR := excl_authUR (leibnizO lock_state)`. -/
abbrev LockExUR : Type := Auth (Option (Excl LockExO))

abbrev LockExRF : COFE.OFunctorPre := constOF LockExUR

/-- Rocq `lockG`. -/
class LockExG (GF : BundledGFunctors) where
  lockInG : ElemG GF LockExRF

attribute [reducible, instance] LockExG.lockInG

section lockEx

variable {GF : BundledGFunctors} [LockExG GF]

/-- The authority on the lock's state; lives in the invariant. -/
def lockAuth (γ : GName) (st : LockState) : IProp GF :=
  iOwn (F := LockExRF) γ (ExclAuth.auth (⟨st⟩ : LockExO))

/-- The state fragment; the free one lives in the invariant, a held one is the holder's token. -/
def lockFrag (γ : GName) (st : LockState) : IProp GF :=
  iOwn (F := LockExRF) γ (ExclAuth.frag (⟨st⟩ : LockExO))

/-- THE holder token: hart `i` holds the lock and `lk->cpu` is set. -/
def lockedEx (γ : GName) (i : CPU) : IProp GF := lockFrag γ (some (i, true))

/-- The same, in the window where `lk->cpu` is still 0. -/
def lockedPreEx (γ : GName) (i : CPU) : IProp GF := lockFrag γ (some (i, false))

instance lockAuth_timeless (γ : GName) (st : LockState) : Timeless (lockAuth (GF := GF) γ st) := by
  unfold lockAuth; infer_instance

instance lockFrag_timeless (γ : GName) (st : LockState) : Timeless (lockFrag (GF := GF) γ st) := by
  unfold lockFrag; infer_instance

/-- The fragment agrees with the authority. -/
theorem lockFragAgree (γ : GName) (st st' : LockState) :
    lockAuth (GF := GF) γ st ⊢ lockFrag γ st' -∗ ⌜st = st'⌝ := by
  unfold lockAuth lockFrag
  iintro Ha Hf
  icases iOwn_cmraValid_op $$ [$Ha $Hf] with %hv
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree hv)

/-- The state fragment is exclusive. -/
theorem lockFragExclusive (γ : GName) (st st' : LockState) :
    lockFrag (GF := GF) γ st ⊢ lockFrag γ st' -∗ False := by
  unfold lockFrag
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %hv
  exact (ExclAuth.frag_op_valid.mp hv).elim

theorem lockedExExclusive (γ : GName) (i j : CPU) :
    lockedEx (GF := GF) γ i ⊢ lockedEx γ j -∗ False :=
  lockFragExclusive γ _ _

/-- THE holder law. -/
theorem lockedExState (γ : GName) (st : LockState) (i : CPU) :
    lockAuth (GF := GF) γ st ⊢ lockedEx γ i -∗ ⌜st = some (i, true)⌝ :=
  lockFragAgree γ st _

theorem lockedPreExState (γ : GName) (st : LockState) (i : CPU) :
    lockAuth (GF := GF) γ st ⊢ lockedPreEx γ i -∗ ⌜st = some (i, false)⌝ :=
  lockFragAgree γ st _

theorem lockStateUpdate (γ : GName) (st st' : LockState) :
    lockAuth (GF := GF) γ st ⊢ lockFrag γ st -∗ |==> (lockAuth γ st' ∗ lockFrag γ st') := by
  unfold lockAuth lockFrag
  apply wand_intro
  exact iOwn_op.mpr.trans ((iOwn_update ExclAuth.update).trans (bupd_mono iOwn_op.mp))

/-- acquire's `amoswap`: a free lock becomes "held by `i`, cpu not yet written". -/
theorem lockTake (γ : GName) (i : CPU) :
    lockAuth (GF := GF) γ none ⊢ lockFrag γ none -∗
      |==> (lockAuth γ (some (i, false)) ∗ lockedPreEx γ i) :=
  lockStateUpdate γ none (some (i, false))

/-- A pure consequence of `P ∗ Q` that keeps both (Lean-only; `Weak.keepPure`'s twin). -/
theorem lockKeepPure {PROP : Type _} [BI PROP] {P Q : PROP} {φ : Prop} (h : P ⊢ Q -∗ ⌜φ⌝) :
    P ⊢ Q -∗ ⌜φ⌝ ∗ P ∗ Q :=
  wand_intro ((and_intro (wand_elim h) .rfl).trans
    (persistent_and_affinely_sep_left_mp.trans (sep_mono_left affinely_elim)))

/-- acquire's `lk->cpu = mycpu()`: the holder gets THE token. -/
theorem lockSetcpu (γ : GName) (st : LockState) (i : CPU) :
    lockAuth (GF := GF) γ st ⊢ lockedPreEx γ i -∗
      |==> (⌜st = some (i, false)⌝ ∗ lockAuth γ (some (i, true)) ∗ lockedEx γ i) := by
  iintro Ha Hf
  icases lockKeepPure (lockedPreExState γ st i) $$ Ha Hf with ⟨%hst, Ha, Hf⟩
  subst hst
  unfold lockedPreEx lockedEx
  imod lockStateUpdate γ (some (i, false)) (some (i, true)) $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  isplitr
  · ipureintro; rfl
  · iframe Ha Hf

/-- release's `lk->cpu = 0`: back into the window. -/
theorem lockClrcpu (γ : GName) (st : LockState) (i : CPU) :
    lockAuth (GF := GF) γ st ⊢ lockedEx γ i -∗
      |==> (⌜st = some (i, true)⌝ ∗ lockAuth γ (some (i, false)) ∗ lockedPreEx γ i) := by
  iintro Ha Hf
  icases lockKeepPure (lockedExState γ st i) $$ Ha Hf with ⟨%hst, Ha, Hf⟩
  subst hst
  unfold lockedPreEx lockedEx
  imod lockStateUpdate γ (some (i, true)) (some (i, false)) $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  isplitr
  · ipureintro; rfl
  · iframe Ha Hf

/-- release's word clear: the lock goes free again. -/
theorem lockGive (γ : GName) (st : LockState) (i : CPU) :
    lockAuth (GF := GF) γ st ⊢ lockedPreEx γ i -∗
      |==> (⌜st = some (i, false)⌝ ∗ lockAuth γ none ∗ lockFrag γ none) := by
  iintro Ha Hf
  icases lockKeepPure (lockedPreExState γ st i) $$ Ha Hf with ⟨%hst, Ha, Hf⟩
  subst hst
  unfold lockedPreEx
  imod lockStateUpdate γ (some (i, false)) none $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  isplitr
  · ipureintro; rfl
  · iframe Ha Hf

/-- ALLOCATION of a free lock's ghost state (Rocq inlines it). -/
theorem lockExAlloc : ⊢ |==> ∃ γ : GName, lockAuth (GF := GF) γ none ∗ lockFrag γ none := by
  unfold lockAuth lockFrag
  exact (iOwn_alloc (F := LockExRF)
    ((ExclAuth.auth (⟨none⟩ : LockExO)) • ExclAuth.frag (⟨none⟩ : LockExO))
    ExclAuth.valid).trans (bupd_mono (exists_mono fun _ => iOwn_op.mp))

end lockEx

end MachCSL
