/-
Weak: **W11-F [OWN.102] increment 2 — the walk pcs are EVEN, and the cycle obligations `fetchOkRF` /
`dataOkRF` from the realization interfaces at every reached NON-pin walk state**.  Lean-only, no Rocq
twin.

* `CapF2.walkEven` — at every non-pin state the walk policy reaches from a walk-certifying pin row of
  `pinsW9a`, `pc % 2 = 0`: a reflection check over B5's generated table (`PinWalkTab.walkRows`,
  `decide +kernel`, the `PinCycRun.walkNw` pattern).  This is the `hev` premise of
  `PinDataOk.fetchOkRFiiOf` / `PinDataOk.dkFetchOk` (inventory A14, `PROGRESS-W11F.md`).
* `CapF2.walkBounds` — `0 ≤ pc` and `pc + 2 < 2 ^ 64` there (from `walkText`), `fetchOkRFiOf`'s.
* `CapF2.cycFactsAt` — at such a state, from the three realization interfaces at its pc
  (`PinFetchPa.fetchRealized`, `PinDataOk.fetchOkRealized`, `PinDataOk.dataRealized`) and the
  emission facts `kFetchText` / admin fetch items: `fetchOkRF ∧ dataOkRF` — every per-pc input of
  the three interface lemmas (`walkText`, `walkDec`, `walkNw`, `execCyOfWalk`,
  `PinCycRunFetch.fetchCyR1Of`, `walkEven`) is discharged here, so the only run inputs left are the
  interfaces themselves.

**Open (inventory A15).**  `PinCycRun.cycWalk` / `cycRunOfHartConf*` take `fetchOkRF` / `dataOkRF` at
EVERY `preach` state, pin states included, but use them only at non-pin states (after `pstep own s =
some l`, `l ≠ []`); the table facts the interface lemmas need hold only there.  Closing that needs a
guarded restatement of `cycWalk`'s two premises (an edit of the merged `Weak/PinCycRunAsm.lean` and its
four restatements) — not done here.

Spec: FAITHFUL (proof organisation; the table is re-checked by the kernel through the merged
definitions).  Every name is file-qualified (`CapF2.*`).
-/
import Weak.PinCycRunTab
import Weak.PinCycRunFetch
import Weak.PinDataOkIF4

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Wlabel KernelPinsDef
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)
open PinWalkTab
open SailCycleOrderK PinCycRun PinDataflow

/-! # 1. Even walk pcs, by the table -/

/-- The per-state check: a non-pin state's pc is even. -/
def CapF2.evOk (own : Bool) (s : PState) : Bool :=
  match pstep own s with
  | some (_ :: _) => decide (s.psPc % 2 = 0)
  | _ => true

/-- The per-row check. -/
def CapF2.evRowOk (r : WRow) : Bool := r.wSts.all (CapF2.evOk r.wOwn)

theorem CapF2.evRowsOk0 : walkRows0.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk1 : walkRows1.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk2 : walkRows2.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk3 : walkRows3.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk4 : walkRows4.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk5 : walkRows5.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk6 : walkRows6.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk7 : walkRows7.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk8 : walkRows8.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk9 : walkRows9.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk10 : walkRows10.all CapF2.evRowOk = true := by decide +kernel
theorem CapF2.evRowsOk11 : walkRows11.all CapF2.evRowOk = true := by decide +kernel

theorem CapF2.evRowsOk : walkRows.all CapF2.evRowOk = true := by
  simp only [walkRows, List.all_append, CapF2.evRowsOk0, CapF2.evRowsOk1, CapF2.evRowsOk2,
    CapF2.evRowsOk3, CapF2.evRowsOk4, CapF2.evRowsOk5, CapF2.evRowsOk6, CapF2.evRowsOk7,
    CapF2.evRowsOk8, CapF2.evRowsOk9, CapF2.evRowsOk10, CapF2.evRowsOk11, Bool.and_self]

/-- **EVERY REACHED NON-PIN WALK STATE HAS AN EVEN PC** (header). -/
theorem CapF2.walkEven (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState) :
    (pc, w) ∈ pinsW9a → walkOwn w = some own → preach own (pinStart pc) x n →
    pstep own x = some l → l ≠ [] → x.psPc % 2 = 0 := by
  intro hm hw hx hp hne
  have hin : (pc, own) ∈ walkRows.map (fun r => (r.wPc, r.wOwn)) := by
    rw [walkRowsCover]
    exact List.mem_filterMap.2 ⟨(pc, w), hm, by simp [hw]⟩
  obtain ⟨r, hr, he⟩ := List.mem_map.1 hin
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hrow := List.all_eq_true.mp walkRowsOk r hr
  unfold rowOk at hrow
  rw [Bool.and_eq_true] at hrow
  obtain ⟨h0, h1⟩ := hrow
  obtain ⟨y, hy, hey⟩ := List.any_eq_true.mp h0
  have hst : pinStart r.wPc ∈ r.wSts := by
    rw [WeakRvwmoPinBridge3.pstateEqbEq _ _ hey]; exact hy
  have hall := List.all_eq_true.mp h1
  have hx' := PinWalkTab.closedReach r.wOwn r.wSts
    (fun s hs => (Bool.and_eq_true _ _ ▸ hall s hs).2) _ x n hx hst
  have hev := List.all_eq_true.mp (List.all_eq_true.mp CapF2.evRowsOk r hr) x hx'
  unfold CapF2.evOk at hev
  rw [hp] at hev
  cases l with
  | nil => exact absurd rfl hne
  | cons a l => exact of_decide_eq_true hev

/-- The pc bounds `fetchOkRFiOf` needs, at a reached non-pin walk state (from `walkText`). -/
theorem CapF2.walkBounds (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState) :
    (pc, w) ∈ pinsW9a → walkOwn w = some own → preach own (pinStart pc) x n →
    pstep own x = some l → l ≠ [] → 0 ≤ x.psPc ∧ x.psPc + 2 < 2 ^ 64 := by
  intro hm hw hx hp hne
  have ht := walkText pc w own x n l hm hw hx hp hne
  unfold textLo textHi at ht
  omega

/-! # 2. The cycle obligations from the interfaces -/

/-- **`fetchOkRF ∧ dataOkRF` FROM THE REALIZATION INTERFACES** (header), at a reached non-pin walk
state: every per-pc premise of `fetchOkRFiOf` / `fetchOkRFiiOf` / `dataOkRFOf` discharged from the
table and the merged per-instruction facts. -/
theorem CapF2.cycFactsAt (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState)
    (hm : (pc, w) ∈ pinsW9a) (hw : walkOwn w = some own) (hx : preach own (pinStart pc) x n)
    (hp : pstep own x = some l) (hne : l ≠ [])
    (p0 : Pexv6) (d0 : Efab) (em : Hemission) (hft : kFetchText em)
    (hfeN : ∀ a tvs t, (LIFetch a tvs, t) ∈ em.emItems → t = none)
    (hfr : PinFetchPa.fetchRealized p0 d0 em x.psPc)
    (hfo : PinDataOk.fetchOkRealized p0 d0 em x.psPc)
    (hdr : PinDataOk.dataRealized p0 d0 em x.psPc) :
    fetchOkRF p0 d0 em x.psPc ∧ dataOkRF p0 d0 em x.psPc := by
  have ht := walkText pc w own x n l hm hw hx hp hne
  have hev := CapF2.walkEven pc w own x n l hm hw hx hp hne
  obtain ⟨h0, hlt⟩ := CapF2.walkBounds pc w own x n l hm hw hx hp hne
  obtain ⟨a, hdec, -⟩ := walkDec pc w own x n l hm hw hx hp hne
  have hnw := walkNw pc w own x n l hm hw hx hp hne
  have hexec := execCyOfWalk pc w own x n l hm hw hx hp hne
  have hr1 := PinCycRunFetch.fetchCyR1Of x.psPc
  have hfi := PinFetchPa.fetchOkRFiOf p0 d0 em x.psPc h0 hlt hfr
  have hfii := PinDataOk.fetchOkRFiiOf p0 d0 em x.psPc ht hev a hdec hr1 hexec hnw hft hfeN hfi hfo
  have hf : fetchOkRF p0 d0 em x.psPc := ⟨hfi, hfii⟩
  exact ⟨hf, PinDataOk.dataOkRFOf p0 d0 em x.psPc ht a hdec hr1 hexec hnw hft hfeN hf hdr⟩

end Weak
