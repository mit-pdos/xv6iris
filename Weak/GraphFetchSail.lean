/-
Weak: **[OWN.86] = Q-P1-FENCEI (b′) — the Sail characterisation of the restated fence.i sites**
(plan `notes/weak-allocproc-plan.md` rev 52, §C W5d-G G6; `PROGRESS-W5dG63b.md` §(1), option (b′)
RULED; D40 [OWN.15]).  Lean-only, no Rocq twin.

`emFenceI em f` (`Weak/GraphFetch.lean`, the trusted fetch text's fence.i sites) reads the
EMISSION-WIDE latest own cycle label (`LInstr`/`LIFetch`) before an `LFence false×4` item.  This
file proves that this criterion identifies EXACTLY Sail's `fence.i` barriers, from W-SCO's
`sailCycleOrder_holds` (`Weak/SailCycleOrderCycle.lean`):

* `GraphFetchSail.nodeFenceZero` — a Sail node step labelled `LFence false×4` is a
  `Barrier_RISCV_i` barrier (`ebarLabel`; every other barrier kind has a non-zero `ebarNow`) or an
  SFENCE.VMA announce (`annLabel`, the Q7 marker): nothing else carries that label;
* `GraphFetchSail.plicNotCyc` — a PLIC wire step (`pstepPlic`, a disjunct of the hart's own
  `pstepHart`) is labelled `LDev`, NOT a cycle label: wherever it lands it moves neither the latest
  cycle label nor the criterion;
* `GraphFetchSail.lastCycOwn` — `sailCycleOrder`'s `lastCyc` IS `GraphFetch.lastCycL` of the hart's
  own label list (`GraphFetchSail.ownLbls`), the label list of its emission;
* **`GraphFetchSail.fenceISiteIff`** — along every `pfRunST` run from a booted pf configuration
  (`wbootFacts σ0`), at a hart step labelled `LFence false×4` out of a Sail node, the latest own
  cycle label is `LInstr` IFF the node is `.barrier .Barrier_RISCV_i`;
* `GraphFetchSail.emFenceISail` / `GraphFetchSail.emMarkerNotSite` — the same in `emFenceI`'s
  vocabulary, for an emission item whose prefix's labels are the hart's own labels of the run:
  a `fence.i` barrier's item IS a site, an `sfence.vma` marker's item's prefix fails the criterion.

Spec marks.  Zifencei: "FENCE.I ... subsequent instruction fetches ... see ... previous data
stores"; one `fence.i` is one instruction.  Sail: `execute FENCEI` is the one `Barrier_RISCV_i`
after its own announce; interrupts are taken at the step boundary; the PLIC wire is asynchronous
and part of no instruction.  RVWMO / riscv.cat / PMAs: silent (no fetch model).  The restated
`emFenceI` is therefore FAITHFUL on every Sail emission (this file); it is STRONGER than the old
block-local text only on non-Sail LTS emissions, which no Sail-boot bundle has.  No new trusted
text here: proof organisation.  Lean-only helpers are file-qualified (`GraphFetchSail.*`).
-/
import Weak.GraphFetch
import Weak.SailCycleOrderCycle

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open TsoShadow

/-- A Sail node step labelled `LFence false×4` is a `fence.i` barrier or an SFENCE.VMA announce
(the Q7 marker). -/
theorem GraphFetchSail.nodeFenceZero (o : Outcome Register RegisterType) (k : o.ret → SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : DevStates) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pnodeStep (.impure (.ok o) k) rs ib d (.LFence false false false false) m' ors fn' d' oib obar →
    o = .barrier .Barrier_RISCV_i ∨ ∃ n w, o = .instrAnnounce n w ∧ sfAnnB n w = true := by
  intro h
  cases o with
  | regRead r => obtain ⟨h1, _⟩ := h; cases h1
  | regWrite r v =>
    obtain ⟨h1, _⟩ := h
    revert h1
    generalize erwOf (depsOfIb ib.ibBits) ib.ibRds r = e
    cases e <;> intro h1 <;> cases h1
  | memRead n va req =>
    simp only [pnodeStep] at h
    split at h
    · obtain ⟨_, _, h1, _⟩ := h; cases h1
    · rcases h with ⟨_, _, _, _, _, h1, _⟩ | ⟨_, ⟨_, _, _, _, _, h1, _⟩ | ⟨_, _, _, _, _, h1, _⟩⟩ <;>
        cases h1
  | memWrite n va req =>
    simp only [pnodeStep] at h
    split at h
    · split at h
      · obtain ⟨_, h1, _⟩ := h; cases h1
      · exact h.elim
    · split at h
      · rcases h with ⟨_, ⟨_, h1, _⟩ | ⟨_, ⟨h1, _⟩ | ⟨h1, _⟩⟩⟩ <;> cases h1
      · exact h.elim
  | readRam => exact h.elim
  | writeRam => exact h.elim
  | barrier b =>
    obtain ⟨h1, _⟩ := h
    left
    cases b <;> first | rfl | (simp [ebarLabel, ebarNow] at h1)
  | cacheOp => obtain ⟨h1, _⟩ := h; cases h1
  | tlbi => obtain ⟨h1, _⟩ := h; cases h1
  | translationStart => obtain ⟨h1, _⟩ := h; cases h1
  | translationEnd => obtain ⟨h1, _⟩ := h; cases h1
  | takeException => obtain ⟨h1, _⟩ := h; cases h1
  | returnException => obtain ⟨h1, _⟩ := h; cases h1
  | cycleCount => obtain ⟨h1, _⟩ := h; cases h1
  | getCycleCount => obtain ⟨h1, _⟩ := h; cases h1
  | message => obtain ⟨h1, _⟩ := h; cases h1
  | choose p => obtain ⟨_, h1, _⟩ := h; cases h1
  | branchAnnounce => obtain ⟨h1, _⟩ := h; cases h1
  | instrAnnounce n w =>
    obtain ⟨h1, _⟩ := h
    right
    refine ⟨n, w, rfl, ?_⟩
    unfold annLabel at h1
    cases hs : sfAnnB n w with
    | true => rfl
    | false => rw [hs] at h1; cases h1

/-- A PLIC wire step is labelled `LDev`: not a cycle label. -/
theorem GraphFetchSail.plicNotCyc (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
    (d' : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepPlic cpu m rs fn ib d l m' ors fn' d' oib obar → GraphFetch.lbCyc l = false := by
  rintro ⟨_, _, _, _, rfl, _⟩
  rfl

/-- The hart's own labels of a step list (the label list of its emission). -/
def GraphFetchSail.ownLbls (i : Nat) (st : List (Nat × Wlabel)) : List Wlabel :=
  (st.filter (fun y => y.1 == i)).map Prod.snd

/-- `sailCycleOrder`'s `lastCyc` is `GraphFetch.lastCycL` of the hart's own labels. -/
theorem GraphFetchSail.lastCycOwn (i : Nat) (st : List (Nat × Wlabel)) :
    SrvwmoXv6Adequacy.lastCyc i st = GraphFetch.lastCycL (GraphFetchSail.ownLbls i st) := by
  unfold SrvwmoXv6Adequacy.lastCyc GraphFetchSail.ownLbls GraphFetch.lastCycL
  rw [List.filter_map, List.filter_filter, List.getLast?_map]
  congr 2
  apply List.filter_congr
  intro y _
  obtain ⟨j, l⟩ := y
  cases l <;> simp [SrvwmoXv6Adequacy.lbCyc, GraphFetch.lbCyc]

/-- **THE SAIL CHARACTERISATION** ([OWN.86], from W-SCO `sailCycleOrder_holds`): along every run
from a booted pf configuration, at a hart step labelled `LFence false×4` out of a Sail node, the
hart's latest own cycle label is `LInstr` IFF the node is a `fence.i` barrier. -/
theorem GraphFetchSail.fenceISiteIff
    (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) (σ0 : WGState)
    (hb : wbootFacts σ0) (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab)
    (hrun : pfRunST pstepEv pclsEv fok TsoShadow.cohSrc
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st c)
    (cpu : CPU) (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
    (ib : Ibch) (ws : Wstate) (pr : GSet Nat)
    (hag : c.pcAgs[cpu.val]? = some ⟨.PHart cpu (.impure (.ok o) k) rs none ib, ws, pr⟩)
    (d : Efab) (p' : Pexv6) (d' : Efab)
    (hstep : pstepEv (.PHart cpu (.impure (.ok o) k) rs none ib) d
      (.LFence false false false false) p' d') :
    GraphFetch.lastCycL (GraphFetchSail.ownLbls (hartAgent cpu) st) = some .LInstr ↔
      o = .barrier .Barrier_RISCV_i := by
  obtain ⟨hfi, hsf⟩ := sailCycleOrder_holds fok σ0 hb st c hrun cpu o k rs ib ws pr hag
  rw [← GraphFetchSail.lastCycOwn]
  obtain ⟨m', ors, fn', dd, oib, obar, hn, -⟩ :=
    PfStepTso.nodeOf cpu _ rs none ib d _ p' d' hstep (fun _ _ _ _ _ h => by cases h) rfl
  refine ⟨fun hl => ?_, hfi⟩
  rcases GraphFetchSail.nodeFenceZero o k rs ib _ m' ors fn' dd oib obar hn with h | ⟨n, w, ho, hs⟩
  · exact h
  · obtain ⟨base, tvs, hf⟩ := hsf n w ho hs
    rw [hl] at hf
    cases hf

/-- In `emFenceI`'s vocabulary: an emission item `(LFence false×4, some f)` whose prefix's labels
are the hart's own labels of the run, taken by a `fence.i` barrier node, is a site. -/
theorem GraphFetchSail.emFenceISail
    (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) (σ0 : WGState)
    (hb : wbootFacts σ0) (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab)
    (hrun : pfRunST pstepEv pclsEv fok TsoShadow.cohSrc
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st c)
    (cpu : CPU) (k : Unit → SailM Unit) (rs : RegFile) (ib : Ibch) (ws : Wstate) (pr : GSet Nat)
    (hag : c.pcAgs[cpu.val]? =
      some ⟨.PHart cpu (.impure (.ok (.barrier .Barrier_RISCV_i)) k) rs none ib, ws, pr⟩)
    (em : Hemission) (f : Nat) (pre rest : List Eitem)
    (he : em.emItems = pre ++ (Wlabel.LFence false false false false, some f) :: rest)
    (hown : pre.map Prod.fst = GraphFetchSail.ownLbls (hartAgent cpu) st) :
    emFenceI em f := by
  obtain ⟨hfi, -⟩ := sailCycleOrder_holds fok σ0 hb st c hrun cpu (.barrier .Barrier_RISCV_i) k rs ib ws pr hag
  refine GraphFetch.emFenceIOfPre em f pre rest he ?_
  rw [hown, ← GraphFetchSail.lastCycOwn]
  exact hfi rfl

/-- ... and an `sfence.vma` marker's item (an SFENCE.VMA announce node) fails the criterion at its
own prefix: the latest own cycle label there is the instruction's fetch. -/
theorem GraphFetchSail.emMarkerNotSite
    (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop) (σ0 : WGState)
    (hb : wbootFacts σ0) (st : List (Nat × Wlabel)) (c : Wpcfg Pexv6 Efab)
    (hrun : pfRunST pstepEv pclsEv fok TsoShadow.cohSrc
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st c)
    (cpu : CPU) (n : Nat) (w : BitVec n) (k : Unit → SailM Unit) (rs : RegFile) (ib : Ibch)
    (ws : Wstate) (pr : GSet Nat)
    (hag : c.pcAgs[cpu.val]? =
      some ⟨.PHart cpu (.impure (.ok (.instrAnnounce n w)) k) rs none ib, ws, pr⟩)
    (hsf : sfAnnB n w = true) (pre : List Eitem)
    (hown : pre.map Prod.fst = GraphFetchSail.ownLbls (hartAgent cpu) st) :
    GraphFetch.lastCycL (pre.map Prod.fst) ≠ some .LInstr := by
  obtain ⟨-, hs⟩ := sailCycleOrder_holds fok σ0 hb st c hrun cpu (.instrAnnounce n w) k rs ib ws pr hag
  obtain ⟨base, tvs, hf⟩ := hs n w rfl hsf
  rw [hown, ← GraphFetchSail.lastCycOwn, hf]
  intro h
  cases h

end Weak
