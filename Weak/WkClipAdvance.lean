/-
Weak: **the ADVANCING install cut** (STEP-0 prototype for the user page tables).

Rocq: `iris/WkClipAdvance.v` @ xxvzwolszwmp.

The Rocq header, in substance.  A user leaf slot is OVERWRITTEN by software (`mappages`,
`uvmunmap`'s `*pte = 0`, `uvmalloc`), so there is no single canonical word every message is an
A/D variant of.  The proposed shape is "every message AT OR ABOVE THE LATEST INSTALL writes a
variant of the CURRENT word" -- exactly `WeakKpt` §1's CLIPPED layer (`wlogVariantsFrom T0`,
`wfreshFrom T0`, `wwinInstall log T0`) with the cut `T0` ADVANCING at every software store.
This file tests the pure log-level core, with the existing vocabulary UNCHANGED:

1. `wclipReinstall` -- THE RE-INSTALL RULE: appending an arbitrary 8-byte window write
   `wwriteMsg tid k la 8 w'` to ANY log re-establishes all three clipped conjuncts at the
   fresh cut `log.length + 1` (the appended message's timestamp; the timestamp of index `i`
   is `i + 1`), with `w'` as the canonical word.  The old history drops out because the
   closure at that cut only quantifies over the appended message.
2. `wclipUnmapCollapse` (+ `_ext` under a further window-disjoint extension) -- at the
   `uvmunmap` word `0`, via the existing `wadmVariantFrom` verbatim: every admissible read of
   the window is `pteSetAD 0 a d`.
3. `pteSetAdZeroInvalid` -- A/D variants of the zero word are eff-invalid PTEs
   (`WeakWalkEff.wpteInvalid`, the spelling the walk's fault arm consumes); the SC projection
   `pteSetAdZeroPteInvalid` follows by `wpteInvalidPteInvalid`.
4. `wclipUnmapFaults` -- the headline: after a software store of the zero word, every
   admissible read of the slot is an invalid PTE.

VERDICT (Rocq): the clipped layer supports an advancing cut with NOTHING added.

**Deviations from Rocq.**

1. Vocabulary as `Weak/WeakKpt.lean` deviation 1 (`S (length log)` ↦ `log.length + 1`,
   `wm_log σ` ↦ `σ.wmLog`, `w_vrNew (wm_ws σ)` ↦ `σ.wmWs.wVrNew`, `pa_z` ↦ `paZ`,
   `wwrite_msg` ↦ `wwriteMsg`, `pte_set_ad` ↦ `MachCSL.pteSetAD`, `mword_of_int 0` ↦ `0#64`,
   `bv (8 * 8)` ↦ `BitVec (8 * 8)`; the `(w' : mword 64)` casts are definitional and vanish).
2. O2 (`WeakKpt` deviation 2): `wadmVariantFrom` takes `rak.akIfetch = false`, so
   `wclipUnmapCollapse`, `wclipUnmapCollapseExt` and `wclipUnmapFaults` carry that premise
   (just before the cover premise), as the absorption theorem does.
3. `wpteInvalidBit0`: Rocq's `Z.testbit (bv_unsigned w) 0 = false` ↦ `w.getLsbD 0 = false`.
   The Lean model's `pte_is_invalid` tests `V == 0` with a plain `if` (Rocq: an `or_boolM`
   chain), so the proof is the `if` reduction, not `exec_eff_or_boolM_nil`.
   `pteSetAdZeroInvalid` is closed by the `V`-bit fact of the concrete zero variants
   (`bv1_cases` + `decide`) instead of `pte_set_ad_testbit` (not in the Lean tree).
4. `pte_set_ad_refl` ↦ `MachCSL.pteAD_refl` (reused).
5. Rocq's `Print Assumptions` commands are not declarations.

**Rocq → Lean name map.**  `wreinstall_install` `wreinstallInstall`; `wreinstall_variants`
`wreinstallVariants`; `wreinstall_fresh` `wreinstallFresh`; `wclip_reinstall`
`wclipReinstall`; `wclip_unmap_collapse` `wclipUnmapCollapse`; `wclip_unmap_collapse_ext`
`wclipUnmapCollapseExt`; `wpte_invalid_bit0` `wpteInvalidBit0`; `pte_set_ad_zero_invalid`
`pteSetAdZeroInvalid`; `pte_set_ad_zero_pte_invalid` `pteSetAdZeroPteInvalid`;
`wclip_unmap_faults` `wclipUnmapFaults`.  (None is a duplicated Rocq name.)

**Dropped:** nothing -- all 10 Rocq lemmas are ported.
-/
import Weak.WeakKpt
import MachCSL.PteClass

namespace Weak

open MachCSL MachCSL.Stdpp
open Sail
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The re-install rule -/

/-- The appended message is the one at the new cut, and it writes every byte of the window. -/
theorem wreinstallInstall (tid : Option Nat) (kcls : WmClass) (la : PAddr)
    (log : List Wmsg) (w' : BitVec (8 * 8)) :
    wwinInstall (log ++ [wwriteMsg tid kcls la 8 w']) (log.length + 1) la := by
  refine ⟨by omega, wwriteMsg tid kcls la 8 w', ?_, ?_⟩
  · rw [Nat.add_sub_cancel, lookup_app_r (Nat.le_refl _), Nat.sub_self]
    rfl
  · intro j hj
    rw [wwriteMsgByte tid kcls la 8 w' j hj]
    rfl

/-- THE POINT OF THE WHOLE FILE: the closure at the fresh cut sees ONLY the appended message,
so the arbitrary new word `w'` is a legitimate canonical word. -/
theorem wreinstallVariants (tid : Option Nat) (kcls : WmClass) (la : PAddr)
    (log : List Wmsg) (w' : BitVec (8 * 8)) :
    wlogVariantsFrom (log.length + 1) (log ++ [wwriteMsg tid kcls la 8 w']) (paZ la) w' := by
  intro i m hi hge
  have hlen : i < log.length + 1 := by
    have := lookup_lt_Some hi
    simpa using this
  have hieq : i = log.length := by omega
  subst hieq
  rw [lookup_app_r (Nat.le_refl _), Nat.sub_self] at hi
  injection hi with hi
  subst hi
  exact wmsgVariantWrite tid kcls la w' (paZ la) w' rfl (pteAD_refl w')

/-- The CAS discipline at the fresh cut is VACUOUS: nothing lies strictly above the install. -/
theorem wreinstallFresh (tid : Option Nat) (kcls : WmClass) (la : PAddr)
    (log : List Wmsg) (w' : BitVec (8 * 8)) (img : Image) :
    wfreshFrom (log.length + 1) img (log ++ [wwriteMsg tid kcls la 8 w']) (paZ la) := by
  intro i m b hi hgt _
  exfalso
  have := lookup_lt_Some hi
  simp at this
  omega

/-- THE RE-INSTALL RULE, packaged (`wlogWf log` and `accWf la 8` are carried, not consumed). -/
theorem wclipReinstall (tid : Option Nat) (kcls : WmClass) (la : PAddr)
    (log : List Wmsg) (w' : BitVec (8 * 8)) :
    wlogWf log →
    accWf la 8 →
    wwinInstall (log ++ [wwriteMsg tid kcls la 8 w']) (log.length + 1) la ∧
    wlogVariantsFrom (log.length + 1) (log ++ [wwriteMsg tid kcls la 8 w']) (paZ la) w' ∧
    (∀ img : Image,
       wfreshFrom (log.length + 1) img (log ++ [wwriteMsg tid kcls la 8 w']) (paZ la)) := by
  intro _ _
  exact ⟨wreinstallInstall tid kcls la log w', wreinstallVariants tid kcls la log w',
    fun img => wreinstallFresh tid kcls la log w' img⟩

/-! ## 2. The collapse at the new cut, at the `uvmunmap` word -/

theorem wclipUnmapCollapse (σ : Wmstate) (rak : AkInfo) (la : PAddr)
    (log : List Wmsg) (tid : Option Nat) (kcls : WmClass)
    (z w : BitVec (8 * 8)) :
    z = 0#64 →
    σ.wmLog = log ++ [wwriteMsg tid kcls la 8 z] →
    rak.akIfetch = false →
    log.length + 1 ≤ σ.wmWs.wVrNew →
    wadm σ rak la 8 w →
    ∃ a d : BitVec 1, w = pteSetAD 0#64 a d := by
  intro hz hlog hif hcov hadm
  obtain ⟨a, d, hw⟩ := wadmVariantFrom σ rak la z (log.length + 1) w
    (by rw [hlog]; exact wreinstallVariants tid kcls la log z)
    (by rw [hlog]; exact wreinstallInstall tid kcls la log z)
    hif hcov hadm
  exact ⟨a, d, by rw [hw, hz]⟩

/-- ... and the same under any further extension of the log that does not write the window. -/
theorem wclipUnmapCollapseExt (σ : Wmstate) (rak : AkInfo) (la : PAddr)
    (log rest : List Wmsg) (tid : Option Nat) (kcls : WmClass)
    (z w : BitVec (8 * 8)) :
    z = 0#64 →
    σ.wmLog = (log ++ [wwriteMsg tid kcls la 8 z]) ++ rest →
    (∀ (i : Nat) (m : Wmsg),
       σ.wmLog[i]? = some m → log.length + 1 ≤ i →
       ∀ j : Nat, j < 8 → msgByte m (WeakInterp.accAddr la j) = none) →
    rak.akIfetch = false →
    log.length + 1 ≤ σ.wmWs.wVrNew →
    wadm σ rak la 8 w →
    ∃ a d : BitVec 1, w = pteSetAD 0#64 a d := by
  intro hz hlog hno hif hcov hadm
  have hlen0 : (log ++ [wwriteMsg tid kcls la 8 z]).length = log.length + 1 := by simp
  have hpref : (log ++ [wwriteMsg tid kcls la 8 z]) <+: σ.wmLog := by
    rw [hlog]; exact ⟨rest, rfl⟩
  have hvar : wlogVariantsFrom (log.length + 1) σ.wmLog (paZ la) z := by
    refine wlogVariantsFromExt (log.length + 1) _ σ.wmLog (paZ la) z
      (wreinstallVariants tid kcls la log z) hpref ?_
    intro i m hi hge j hj
    exact hno i m hi (by omega) j hj
  have hinst : wwinInstall σ.wmLog (log.length + 1) la :=
    wwinInstallPrefix _ σ.wmLog (log.length + 1) la (wreinstallInstall tid kcls la log z) hpref
  obtain ⟨a, d, hw⟩ := wadmVariantFrom σ rak la z (log.length + 1) w hvar hinst hif hcov hadm
  exact ⟨a, d, by rw [hw, hz]⟩

/-! ## 3. A/D variants of the zero word still fault -/

/-- A word with `V` clear is eff-invalid: the first test fires, nothing is read, the trace is
empty (deviation 3). -/
theorem wpteInvalidBit0 (w : BitVec 64) :
    w.getLsbD 0 = false → wpteInvalid w := by
  intro hb s
  have hv : _get_PTE_Flags_V (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) = 0#1 := by
    simp only [Mk_PTE_Flags, _get_PTE_Flags_V, Sail.BitVec.extractLsb, BitVec.extractLsb]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 := by omega
    subst this
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero, Nat.zero_add]
    simpa using hb
  unfold pte_is_invalid
  rw [hv]
  exact execEffReturnM true s

/-- THE UNMAPPED-SLOT FAULT FACT: every A/D variant of the zero word is an invalid PTE. -/
theorem pteSetAdZeroInvalid (a d : BitVec 1) :
    wpteInvalid (pteSetAD 0#64 a d) := by
  apply wpteInvalidBit0
  rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;> decide

/-- The SC projection, free. -/
theorem pteSetAdZeroPteInvalid (a d : BitVec 1) :
    pteInvalid (pteSetAD 0#64 a d) :=
  wpteInvalidPteInvalid _ (pteSetAdZeroInvalid a d)

/-! ## 4. The headline, end to end -/

theorem wclipUnmapFaults (σ : Wmstate) (rak : AkInfo) (la : PAddr)
    (log : List Wmsg) (tid : Option Nat) (kcls : WmClass)
    (z w : BitVec (8 * 8)) :
    z = 0#64 →
    σ.wmLog = log ++ [wwriteMsg tid kcls la 8 z] →
    rak.akIfetch = false →
    log.length + 1 ≤ σ.wmWs.wVrNew →
    wadm σ rak la 8 w →
    wpteInvalid w := by
  intro hz hlog hif hcov hadm
  obtain ⟨a, d, hw⟩ := wclipUnmapCollapse σ rak la log tid kcls z w hz hlog hif hcov hadm
  rw [hw]
  exact pteSetAdZeroInvalid a d

end Weak
