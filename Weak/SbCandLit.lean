/-
Weak: **allocproc route P, increment P-W1 — the litmus members are `SbCand` RUNS**
(`notes/weak-allocproc-plan-review-R45.md` §5 row P-W1).  Lean-only, no Rocq twin.  A LEAF.

`Weak/LitmusSBAcqP.lean` exhibits route-P members as abstract issue/landing POSITIONS (`SBAcqP.FifoCore`,
`ReadsGF`, `CoGF`, `GateWr`).  This file promotes them to runs of the buffered candidate
`Weak/SbCand.lean`, with GF's labels VERBATIM (every timestamp the member's log position = GF's write
index, every value GF's), under EVERY lawful landing policy — in particular `SbPol.epoch` (the primary
one, [OWN.113]) and `SbPol.fifo`:

* **`SbCandLit.l1MemberSb`** — Litmus 1 (`SBAcq.l1`, R44's F44-1 shape: both release stores buffered
  past the hart's next `amoswap.w.aq` and failed spin).  The interleaving is `SBAcqP.ord1P`'s
  (`SbCandLit.o1Items`), the per-hart traces are GF's program rows (`SbCandLit.l1Trace`), the final
  log is GF's writes in gmo order (`SbCandLit.l1Log`: member co = GF co), all buffers drained
  (`SbCandLit.l1Drained`).
* **`SbCandLit.l4xMemberSb`** — F-R45-1's companion with the [OWN.112] exemption (`SBAcqP.l4x`:
  `e_B` = `ilock+0xe` reads the landed top); same four facts against `SBAcqP.ord4X`.

Every step is checked by `SbCand.runOkB` (`decide +kernel`): reads are TOP reads, landings take the
oldest entry, AMOs pass `SbCand.amoOk` (in Litmus 1 the acquire `amoswap` overtakes the pending
release store of the SAME epoch — the release's `fence rw,w` precedes the store, not the AMO).
-/
import Weak.SbCand
import Weak.LitmusSBAcqP

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-- Macro steps from an interleaving by event ids: GF's label at each event, then the landings of the
listed plain stores (each the oldest entry of its hart). -/
def SbCandLit.toSteps (G : Gexec) (o : List (Geid × List Geid)) : List (Estep × List Nat) :=
  o.map (fun p => (⟨p.1.1, (gxLbl G p.1).getD (LFence false false false false)⟩, p.2.map Prod.fst))

/-- The same interleaving as `SBAcqP` items. -/
def SbCandLit.toItems (o : List (Geid × List Geid)) : List SBAcqP.Item :=
  o.flatMap (fun p => (false, p.1) :: p.2.map (fun w => (true, w)))

/-- The message GF's write event `e` appends. -/
def SbCandLit.msgOf (G : Gexec) (e : Geid) : Option Wmsg :=
  (gxLbl G e).bind (fun l => (lbWr l).map (fun bv => ⟨bv.1, bv.2, some e.1, lbCls l⟩))

def SbCandLit.σ0 (img : Image) : SbCand.CandS := ⟨⟨img, [], fun _ => wsInit⟩, fun _ => []⟩

theorem SbCandLit.σ0Init (img : Image) : SbCand.initS (SbCandLit.σ0 img) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- Per agent `i`, the labels of the trace. -/
def SbCandLit.traceOf (steps : List (Estep × List Nat)) (i : Nat) : List Lbl :=
  ((steps.map Prod.fst).filter (fun s => s.esAg = i)).map Estep.esLb

/-! # 1. Litmus 1 -/

def SbCandLit.o1 : List (Geid × List Geid) :=
  [((0, 0), []), ((1, 0), []), ((0, 1), []), ((1, 1), []), ((0, 2), []), ((1, 2), []),
   ((0, 3), []), ((1, 3), []), ((0, 4), []), ((1, 4), []), ((0, 5), []), ((1, 5), [(0, 2), (1, 2)])]

def SbCandLit.steps1 : List (Estep × List Nat) := SbCandLit.toSteps SBAcq.l1.gdG SbCandLit.o1

theorem SbCandLit.o1Items : SbCandLit.toItems SbCandLit.o1 = SBAcqP.ord1P := by decide +kernel

theorem SbCandLit.l1RunB :
    SbCand.runOkB (SbCandLit.σ0 SBAcq.l1.gdG.gxImg) SbCandLit.steps1 = true := by decide +kernel

/-- **LITMUS 1 IS AN `SbCand` RUN under every lawful landing policy** (epoch, FIFO, …). -/
theorem SbCandLit.l1MemberSb (pol : SbPol) :
    SbCand.execWfP pol ⟨SbCand.statesOf (SbCandLit.σ0 SBAcq.l1.gdG.gxImg) SbCandLit.steps1,
      SbCandLit.steps1.map Prod.fst⟩ :=
  SbCand.runOfB pol _ _ (SbCandLit.σ0Init _) SbCandLit.l1RunB

theorem SbCandLit.l1MemberEpoch :
    SbCand.execWfP SbPol.epoch ⟨SbCand.statesOf (SbCandLit.σ0 SBAcq.l1.gdG.gxImg) SbCandLit.steps1,
      SbCandLit.steps1.map Prod.fst⟩ := SbCandLit.l1MemberSb SbPol.epoch

theorem SbCandLit.l1MemberFifo :
    SbCand.execWfP SbPol.fifo ⟨SbCand.statesOf (SbCandLit.σ0 SBAcq.l1.gdG.gxImg) SbCandLit.steps1,
      SbCandLit.steps1.map Prod.fst⟩ := SbCandLit.l1MemberSb SbPol.fifo

/-- The per-hart traces are GF's program rows, labels verbatim. -/
theorem SbCandLit.l1Trace :
    SbCandLit.traceOf SbCandLit.steps1 0 = (SBAcq.l1Prog 1 2)[0]! ∧
    SbCandLit.traceOf SbCandLit.steps1 1 = (SBAcq.l1Prog 1 2)[1]! ∧
    (SbCandLit.steps1.map Prod.fst).all (fun s => decide (s.esAg < 2)) = true := by
  decide +kernel

/-- The final log is GF's writes in gmo order (the member's co is GF's, total). -/
theorem SbCandLit.l1Log :
    (SbCand.statesOf (SbCandLit.σ0 SBAcq.l1.gdG.gxImg) SbCandLit.steps1).getLast?.map (·.ms.msLog) =
      some ((gwrites SBAcq.l1.gdG).filterMap (SbCandLit.msgOf SBAcq.l1.gdG)) ∧
    (gwrites SBAcq.l1.gdG).length = 8 := by
  decide +kernel

theorem SbCandLit.l1Drained :
    (SbCand.statesOf (SbCandLit.σ0 SBAcq.l1.gdG.gxImg) SbCandLit.steps1).getLast?.map
      (fun σ => (σ.sb 0, σ.sb 1)) = some ([], []) := by
  decide +kernel

/-! # 2. F-R45-1 with the [OWN.112] exemption -/

def SbCandLit.o4 : List (Geid × List Geid) :=
  [((0, 0), []), ((0, 1), []), ((0, 2), []), ((1, 0), []), ((1, 1), [(0, 2)]), ((2, 0), []),
   ((2, 1), []), ((2, 2), []), ((0, 3), []), ((0, 4), []), ((0, 5), [(0, 5)])]

def SbCandLit.steps4 : List (Estep × List Nat) := SbCandLit.toSteps SBAcqP.l4x.gdG SbCandLit.o4

theorem SbCandLit.o4Items : SbCandLit.toItems SbCandLit.o4 = SBAcqP.ord4X := by decide +kernel

theorem SbCandLit.l4xRunB :
    SbCand.runOkB (SbCandLit.σ0 SBAcqP.l4x.gdG.gxImg) SbCandLit.steps4 = true := by decide +kernel

/-- **THE EXEMPT F-R45-1 MEMBER IS AN `SbCand` RUN under every lawful landing policy.** -/
theorem SbCandLit.l4xMemberSb (pol : SbPol) :
    SbCand.execWfP pol ⟨SbCand.statesOf (SbCandLit.σ0 SBAcqP.l4x.gdG.gxImg) SbCandLit.steps4,
      SbCandLit.steps4.map Prod.fst⟩ :=
  SbCand.runOfB pol _ _ (SbCandLit.σ0Init _) SbCandLit.l4xRunB

theorem SbCandLit.l4xTrace :
    SbCandLit.traceOf SbCandLit.steps4 0 = (SBAcqP.l4Prog 0 SBAcqP.b2)[0]! ∧
    SbCandLit.traceOf SbCandLit.steps4 1 = (SBAcqP.l4Prog 0 SBAcqP.b2)[1]! ∧
    SbCandLit.traceOf SbCandLit.steps4 2 = (SBAcqP.l4Prog 0 SBAcqP.b2)[2]! ∧
    (SbCandLit.steps4.map Prod.fst).all (fun s => decide (s.esAg < 3)) = true := by
  decide +kernel

theorem SbCandLit.l4xLog :
    (SbCand.statesOf (SbCandLit.σ0 SBAcqP.l4x.gdG.gxImg) SbCandLit.steps4).getLast?.map
      (·.ms.msLog) = some ((gwrites SBAcqP.l4x.gdG).filterMap (SbCandLit.msgOf SBAcqP.l4x.gdG)) ∧
    (gwrites SBAcqP.l4x.gdG).length = 5 := by
  decide +kernel

theorem SbCandLit.l4xDrained :
    (SbCand.statesOf (SbCandLit.σ0 SBAcqP.l4x.gdG.gxImg) SbCandLit.steps4).getLast?.map
      (fun σ => (σ.sb 0, σ.sb 1, σ.sb 2)) = some ([], [], []) := by
  decide +kernel

end Weak
