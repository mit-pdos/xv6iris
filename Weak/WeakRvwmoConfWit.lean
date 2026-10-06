/-
Weak: **the `hemit` non-vacuity witness** (route B, B0b-1).

Rocq: `iris/WeakRvwmoConfWit.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE GAP.  `WeakRvwmoConf.hartConf` is the per-hart row-emittability relation the whole conformance
bundle (`WeakRvwmoSupply.gdexecQconf`) is built on, and B0b-1 landed it with only the EMPTY row
witnessed (`hartConfNil`).  An empty-row witness proves nothing about the relation's shape.

THE WITNESS.  A REAL single-instruction emission of the real xv6 kernel: the `sw &started` store of
`main` -- the instruction `WeakEvStarted`'s end-to-end certification measures -- at the machine
monad node it is emitted from (`WeakEvStarted.evX2`, the residual after the fetch and the 179
silent nodes behind it), with its REQUEST (`evReqw`) read off that node by total projection
(`evStoreReq`) and inverted by `WeakEvLift.ewriteReqAtInv`.  The row is ONE label, the axiomatic
`LStore` of the flag word at `&started`; the emission is the one block `HEone` builds: an EMPTY
administrative run and the realizing step.

WHAT IS AND IS NOT CONCRETE.  The monad, the request, the address, the stored value, the access
kind and the emitted class are all the real machine's (the Lean kernel image, `WeakEvStarted`
deviation 7).  The register file `rs`, the instruction channel `ib`, the CPU and the device
fabric `d0` are UNIVERSALLY QUANTIFIED: the `memWrite` arm of `WeakEvInst.pnodeStep` reads none of
them (the operand lists are a function of `ib`, and `projLbl` drops them).

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below); `regstate` ↦ `RegFile`, `oib32` ↦ `Ibch`
   (`ib_bits ib` ↦ `ib.ibBits`), `dev_state` ↦ `DevStates`, `agent` ↦ `Nat`, `pa_z` ↦ `paZ`,
   `WeakLock.lock_one` ↦ `lockOne`, `ev_x2.2` ↦ `evX2.2`.
2. The request facts are used ONLY through `WeakEvStarted`'s fact theorems (`evStoreReq`,
   `evStoreRam`, `evStoreVal`, `evStorePlain`, `evStorePa`): `evReqw` is an `Option.get`, not a
   literal (`WeakEvStarted` deviation 7).  The wlabel's address is stated, as in Rocq, at
   `paZ evFlag`; the step's own label is at `paZ evReqw.pa`, bridged by `evStorePa`.
3. `hartConfNonempty`'s witnesses: CPU `⟨0, _⟩`, `evRs0`, `ibNone`, and Rocq's `dev0_state` ↦ the
   all-default fabric `⟨fun _ => default⟩` (Lean has no closed `dev0_state`; any fabric works,
   the theorem `evHartConf` is universal in it).
4. §4's `Print Assumptions` are dropped (the lint's axiom/sorry ban is the audit).

**Rocq → Lean name map.**  `ev_p0` `evP0`, `ev_p1` `evP1`, `ev_wl` `evWl`, `ev_row` `evRow`,
`ev_em` `evEm`, `ev_pstep` `evPstep`, `ev_realizes` `evRealizes`, `ev_hart_conf` `evHartConf`,
`ev_em_devfree` `evEmDevfree`, `hart_conf_nonempty` `hartConfNonempty`.

**Dropped:** nothing (Rocq 10 declarations; Lean 10).
-/
import Weak.WeakEvStarted
import Weak.WeakRvwmoSupply

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! ## 1. The objects -/

/-- The hart, sitting at the store node of `sw &started` (`fn = none`: no fence parked). -/
noncomputable def evP0 (cpu : CPU) (rs : RegFile) (ib : Ibch) : Pexv6 :=
  .PHart cpu evX2.2 rs none ib

/-- … and where it lands, named through the projection's own resume function. -/
noncomputable def evP1 (cpu : CPU) (rs : RegFile) (ib : Ibch) : Pexv6 :=
  .PHart cpu (ewriteResume evX2.2) rs none ib

/-- THE WLABEL the step emits: plain, at `&started`, four bytes of `lockOne`. -/
def evWl (ib : Ibch) : Wlabel :=
  .LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne)
    (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits))

/-- THE ROW: its axiomatic image, ONE graph label. -/
def evRow : List Lbl :=
  [.LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne) .WCplain]

/-- THE EMISSION: one tagged item, no administrative items. -/
noncomputable def evEm (cpu : CPU) (rs : RegFile) (ib : Ibch) : Hemission :=
  ⟨[(evWl ib, some 0)], evP1 cpu rs ib⟩

/-! ## 2. The step -/

theorem evPstep (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : DevStates) :
    pstepEv (evP0 cpu rs ib) d0 (evWl ib) (evP1 cpu rs ib) d0 := by
  obtain ⟨K, Hm, Hres⟩ := ewriteReqAtInv 4 64 evX2.2 evReqw evStoreReq
  simp only [pstepEv, evP0, evP1]
  rw [Hres, Hm]
  refine ⟨?_, none, none, none, ?_, ?_, Or.inl ?_⟩
  any_goals trivial
  simp only [pstepNode, pnodeStep, evStoreRam, Bool.false_eq_true, if_false]
  split
  · rename_i v hv
    rw [evStoreVal] at hv
    cases hv
    refine ⟨by decide, Or.inl ⟨by rw [evStorePlain], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    any_goals trivial
    rw [evStorePlain, evStorePa]
    rfl
  · rename_i hv
    rw [evStoreVal] at hv
    exact absurd hv (by simp)

/-- THE PROJECTION: the wlabel's axiomatic image IS the row's label, at class `WCplain`. -/
theorem evRealizes (cpu : CPU) (rs : RegFile) (ib : Ibch) :
    hlblRealizes (evP0 cpu rs ib) wsInit
      (.LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne) .WCplain) (evWl ib) := by
  obtain ⟨K, Hm, _⟩ := ewriteReqAtInv 4 64 evX2.2 evReqw evStoreReq
  refine ⟨trivial, trivial, trivial, ?_⟩
  simp only [evWl, pclsEv, evP0, projLbl]
  rw [Hm]
  simp only [pnodeWclass, evStorePlain]
  rfl

/-! ## 3. The witness -/

theorem evHartConf (i : Nat) (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : DevStates) :
    hartConf i evRow (evP0 cpu rs ib) (fun _ => d0) (evEm cpu rs ib) :=
  hemit.HEone (dv := fun _ => d0) 0 wsInit
    (.LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne) .WCplain) []
    (evP0 cpu rs ib) [] (evP0 cpu rs ib) d0 (evWl ib) (evP1 cpu rs ib) [] (evP1 cpu rs ib)
    (.ARnil _ _) (evRealizes cpu rs ib) (evPstep cpu rs ib d0) (.HEnil _ _ _)

/-- … and the emission is FABRIC-QUIET, so it is a `gdexecQconf` block. -/
theorem evEmDevfree (cpu : CPU) (rs : RegFile) (ib : Ibch) : emDevfree (evEm cpu rs ib) := by
  simp [emDevfree, emLabels, evEm, evWl]

/-- THE POINT: `hartConf` IS INHABITED AT A NONEMPTY ROW, by a real memory event. -/
theorem hartConfNonempty :
    ∃ (i : Nat) (row : List Lbl) (p0 : Pexv6) (d0 : DevStates) (em : Hemission),
      row ≠ [] ∧ hartConf i row p0 (fun _ => d0) em ∧ emDevfree em :=
  ⟨0, evRow, evP0 ⟨0, by decide⟩ evRs0 ibNone, ⟨fun _ => default⟩,
    evEm ⟨0, by decide⟩ evRs0 ibNone,
    by simp [evRow], evHartConf _ _ _ _ _, evEmDevfree _ _ _⟩

end Weak
