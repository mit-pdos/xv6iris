/-
Weak/Prom: **`amoSplitFused` for emission v2** (S1M-proof, plan rev 7 §1 M10 (4); NA-5).  The generic theorems of
`Weak/Prom/AmoSplit.lean` instantiated with the Sail program half `pstepV2` (Emit.lean) and its canonical fused
program `fuseStep pstepV2` (each `LAmoLd`, silent steps, `LAmoSt` of a hart = one `LRmw` step).

What is PROVED about `pstepV2` here (by unfolding Emit.lean, no premise):
* `pstepV2_fab` — every step whose label is not `LDev` leaves the fabric alone and does not read it (MMIO is the
  only arm that touches `DevStates`, M12);
* `pstepV2_amoSrcs` — the sources an AMO half carries are register-only (`depsAddr`/`depsVsrc` are `dsrcOfNum`
  lists, WeakDeps.lean:345–434).

What is a NAMED SCOPE PREMISE (`amoTightV2 ps`, a fact about the Sail model's `execute_AMO`, not about a program):
after an `LAmoLd`, a hart reachable from `ps` takes only `LSilent` steps until an `LAmoSt` with the same address
sources.  Sail's `execute_AMO` (InstsEnd.lean, zaamo_insts.sail:100–140) does `mem_write_ea`, `mem_read`, `rX_bits
rs2` (a register read: `LSilent`), a pure computation, `mem_write_value`; the decoded bits (hence `depsAddr`) do not
change within the instruction.  It FAILS for `amocas` (a failed compare writes `rd` and skips the write; the
optional write-back is a boundary event after `LRegW rd`), and it fails for a run in which `mem_write_value` traps
after the read (NOT checked here whether Sail's PMP/PMA checks can let the read of an `Atomic` access pass and fail
its write).  The Sail runner (MachSail.lean) STOPs on `amocas` and on traps, so the corpus runs are inside the
premise; discharging it is a proof about `execute_AMO`'s monadic code (not attempted).

Theorems:
* `amoSplitFused` — (⇒) every valid run of machine v2 over `pstepV2` that ends with no hart between its halves
  has a valid run over `fuseStep pstepV2` with THE SAME final configuration and `TrRel`-related traces; (⇐) every
  valid run over `fuseStep pstepV2` is a valid run over `pstepV2` with the same final configuration (no premise).
* `amoSplitFused_any` — (⇒) without the closedness side condition (`splitToFused`'s general form).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.AmoSplit
import Weak.Prom.Emit

namespace Weak.Prom.AS

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Weak (Image Dsrc)
open Weak.Prom
open PLabel

/-! ## 1. `pstepV2` is fabric-free off MMIO -/

/-- Not a device label. -/
def notDev (l : PLabel) : Prop := ∀ kd b vs sa sv, l ≠ LDev kd b vs sa sv

theorem hnodeStep_fab {h h' : HState} {d d' : DevStates} {l : PLabel} (hs : hnodeStep h d l h' d')
    (hl : notDev l) : d' = d ∧ ∀ d2, hnodeStep h d2 l h' d2 := by
  unfold hnodeStep at hs
  split at hs
  · rename_i x heq
    exact ⟨hs.1, fun d2 => by unfold hnodeStep; rw [heq]; exact ⟨rfl, hs.2⟩⟩
  · exact hs.elim
  · rename_i o k heq
    cases o
    all_goals dsimp only at hs
    all_goals first
      | exact ⟨hs.1, fun d2 => by unfold hnodeStep; rw [heq]; exact ⟨rfl, hs.2⟩⟩
      | exact ⟨hs.2.1, fun d2 => by unfold hnodeStep; rw [heq]; exact ⟨hs.1, rfl, hs.2.2⟩⟩
      | (obtain ⟨c, h1, h2, h3⟩ := hs
         exact ⟨h2, fun d2 => by unfold hnodeStep; rw [heq]; exact ⟨c, h1, rfl, h3⟩⟩)
      | exact hs.elim
      | skip
    · -- memRead
      split at hs
      · obtain ⟨w, _, hl', _⟩ := hs
        exact absurd hl' (hl _ _ _ _ _)
      · rename_i hdev
        refine ⟨hs.1, fun d2 => ?_⟩
        unfold hnodeStep
        rw [heq]
        dsimp only
        rw [if_neg hdev]
        first | exact ⟨rfl, hs.2⟩ | exact ⟨trivial, hs.2⟩
    · -- memWrite
      split at hs
      · rename_i v hv
        split at hs
        · exact absurd hs.2.1 (hl _ _ _ _ _)
        · rename_i hdev
          refine ⟨hs.1, fun d2 => ?_⟩
          unfold hnodeStep
          rw [heq]
          dsimp only
          rw [hv]
          dsimp only
          rw [if_neg hdev]
          first | exact ⟨rfl, hs.2⟩ | exact ⟨trivial, hs.2⟩
      · exact hs.elim

theorem pstepV2_fab {h h' : HState} {d d' : DevStates} {l : PLabel} (hs : pstepV2 h d l h' d') (hl : notDev l) :
    d' = d ∧ ∀ d2, pstepV2 h d2 l h' d2 := by
  obtain ⟨hcpu, hs⟩ := hs
  unfold hstep at hs
  split at hs
  · rename_i heq
    refine ⟨hs.2.1, fun _ => ⟨hcpu, ?_⟩⟩
    unfold hstep
    rw [heq]
    exact ⟨hs.1, rfl, hs.2.2⟩
  · rename_i heq
    obtain ⟨hd, hall⟩ := hnodeStep_fab hs hl
    refine ⟨hd, fun d2 => ⟨hcpu, ?_⟩⟩
    unfold hstep
    rw [heq]
    exact hall d2

/-! ## 2. The sources of an AMO half are register-only -/

theorem regOnly_dsrcOfNum (n : Int) : regOnly (Weak.dsrcOfNum n) := by
  unfold Weak.dsrcOfNum
  split
  · intro x hx
    simp at hx
    subst hx
    intro h
    cases h
  · intro x hx
    cases hx

theorem regOnly_nil : regOnly [] := fun _ h => by cases h

theorem regOnly_depsAddr (r : Weak.OpRoles) : regOnly (Weak.depsAddr r) := by
  unfold Weak.depsAddr
  split
  all_goals first | exact regOnly_dsrcOfNum _ | exact regOnly_nil

theorem regOnly_depsVsrc (r : Weak.OpRoles) : regOnly (Weak.depsVsrc r) := by
  unfold Weak.depsVsrc
  split
  all_goals first | exact regOnly_dsrcOfNum _ | exact regOnly_nil

/-- The sources an AMO half carries are register-only. -/
def amoSrcsOk : PLabel → Prop
  | LAmoLd _ _ _ asrc => regOnly asrc
  | LAmoSt _ _ _ asrc vsrc => regOnly asrc ∧ regOnly vsrc
  | _ => True

theorem barLabel_ok (b : barrier_kind) : amoSrcsOk (barLabel b) := by
  unfold barLabel
  split
  · trivial
  · split <;> trivial

theorem hnodeStep_amoSrcs {h h' : HState} {d d' : DevStates} {l : PLabel} (hs : hnodeStep h d l h' d') :
    amoSrcsOk l := by
  unfold hnodeStep at hs
  split at hs
  · rcases hs.2 with ⟨_, _, _, rfl, _⟩ | ⟨b, old, _, _, _, _, _, rfl, _⟩ | ⟨k, w, _, _, _, _, rfl, _⟩ |
      ⟨tick, _, _, rfl, _⟩
    · trivial
    · exact ⟨regOnly_depsAddr _, regOnly_nil⟩
    · trivial
    · trivial
  · exact hs.elim
  · rename_i o k heq
    cases o
    all_goals dsimp only at hs
    all_goals first
      | (rw [hs.1]; first | trivial | exact barLabel_ok _)
      | (obtain ⟨c, rfl, _⟩ := hs; trivial)
      | exact hs.elim
      | skip
    · -- regRead
      obtain ⟨_, hs⟩ := hs
      split at hs <;> (rw [hs.1]; trivial)
    · -- regWrite
      obtain ⟨_, _, hs⟩ := hs
      split at hs
      · rw [hs]; trivial
      · split at hs <;> (rw [hs]; trivial)
    · -- memRead
      split at hs
      · obtain ⟨w, _, rfl, _⟩ := hs; trivial
      · obtain ⟨_, _, hs⟩ := hs
        split at hs
        · obtain ⟨w, tvs, _, rfl, _⟩ := hs; trivial
        · split at hs
          · obtain ⟨w, tvs, _, _, _, _, _, hs⟩ := hs
            split at hs
            · rw [hs.1]; trivial
            · rw [hs.1]; exact regOnly_depsAddr _
          · obtain ⟨tvs, _, _, _, rfl, _⟩ := hs; trivial
    · -- memWrite
      split at hs
      · split at hs
        · rw [hs.2.1]; trivial
        · obtain ⟨_, hs⟩ := hs
          unfold ramWrite at hs
          dsimp only at hs
          obtain ⟨_, hs⟩ := hs
          split at hs
          · split at hs
            · rcases hs with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> trivial
            · rw [hs.1]; exact ⟨regOnly_depsAddr _, regOnly_depsVsrc _⟩
          · obtain ⟨c, _, _, _, rfl, _⟩ := hs; trivial
      · exact hs.elim

theorem pstepV2_amoSrcs {h h' : HState} {d d' : DevStates} {l : PLabel} (hs : pstepV2 h d l h' d') :
    amoSrcsOk l := by
  obtain ⟨_, hs⟩ := hs
  unfold hstep at hs
  split at hs
  · rw [hs.1]; trivial
  · exact hnodeStep_amoSrcs hs

/-! ## 3. The scope premise and the instance of `SplitOk` -/

/-- The states of the harts `ps` can reach (any labels, any fabric). -/
def v2Inv (ps : List HState) (h : HState) : Prop := ∃ h0 ∈ ps, reachH h0 h

theorem reachH_snoc {h0 h h' : HState} {d d' : DevStates} {l : PLabel} (hr : reachH h0 h)
    (hs : pstepV2 h d l h' d') : reachH h0 h' := by
  induction hr with
  | refl => exact .step _ _ _ d d' l hs (.refl _)
  | step _ _ _ d1 d1' l1 h1 _ ih => exact .step _ _ _ d1 d1' l1 h1 (ih hs)

/-- **THE SCOPE PREMISE `amoTightV2 ps`** (Sail's `execute_AMO`, zaamo_insts.sail; see the header): after a read
half, a hart reachable from `ps` takes only `LSilent` steps until a write half with the read's address sources.
A fact about the Sail model's AMO sequencing, stated over reachable states as `translationOff` is; FALSE for
`amocas` (no write after a failed compare) — `amocas` is out of this premise's scope, as it is a STOP of the Sail
runner. -/
def amoTightV2 (ps : List HState) : Prop :=
  ∀ h, v2Inv ps h → ∀ d aq base tvs asrc h1 d1, pstepV2 h d (LAmoLd aq base tvs asrc) h1 d1 →
    ∀ hk, silentRun pstepV2 h1 hk → ∀ d l h' d', pstepV2 hk d l h' d' →
      l = LSilent ∨ ∃ rl b data vsrc, l = LAmoSt rl b data asrc vsrc

theorem splitOk_v2 {ps : List HState} (htight : amoTightV2 ps) :
    SplitOk pstepV2 (fuseStep pstepV2) (v2Inv ps) := by
  refine splitOk_fuse (fun h d l h' d' ⟨h0, hm, hr⟩ hs => ⟨h0, hm, reachH_snoc hr hs⟩) ?_ ?_
  · intro h d l h' d' _ hs hl
    refine pstepV2_fab hs ?_
    rcases hl with rfl | ⟨aq, base, tvs, asrc, rfl⟩ <;> (intro _ _ _ _ _ he; cases he)
  · intro h d aq base tvs asrc h1 d1 hI hs
    refine ⟨pstepV2_amoSrcs hs, fun hk hsr d l h' d' hs' => ?_⟩
    rcases htight h hI _ aq base tvs asrc h1 d1 hs hk hsr d l h' d' hs' with h0 | ⟨rl, b, data, vsrc, rfl⟩
    · exact .inl h0
    · exact .inr ⟨rl, b, data, vsrc, rfl, (pstepV2_amoSrcs hs').2⟩

/-! ## 4. `amoSplitFused` for emission v2 -/

/-- A fused run keeps every AMO slot empty (no fused label is a half). -/
theorem fused_rmw_none {P D : Type} {pstepS : P → D → PLabel → P → D → Prop} :
    ∀ {c c' : PCfg P D} {es : List PEvt}, pmSteps (fuseStep pstepS) c es c' →
      (∀ (k : Nat) (ag : PAgent P), c.pcAgs[k]? = some ag → ag.paWs.wRmw = none) →
      ∀ (k : Nat) (ag : PAgent P), c'.pcAgs[k]? = some ag → ag.paWs.wRmw = none := by
  intro c c' es hr
  induction hr with
  | refl => exact id
  | step c0 c1 c2 e es hs _ ih =>
    intro hc
    apply ih
    intro k ag hk
    cases hs with
    | promise i ag0 m hag _ _ =>
      simp only at hk
      rcases getElem?_set_of hk with ⟨hkj, hb, _⟩ | ⟨_, hk'⟩
      · subst hkj hb; exact hc _ ag0 hag
      · exact hc k ag hk'
    | state j ag0 l ots st' d' ws' prom' hag hp hm =>
      simp only at hk
      rcases getElem?_set_of hk with ⟨hkj, hb, _⟩ | ⟨_, hk'⟩
      · subst hkj hb
        have hl : isHalf l = false := by
          cases hp with
          | plain _ _ _ _ hl => exact hl
          | amo => rfl
        exact memStep_rmw_none hm hl (hc _ ag0 hag)
      · exact hc k ag hk'

theorem fused_closed {P D : Type} {pstepS : P → D → PLabel → P → D → Prop} {Inv : P → Prop} {img : Image}
    {d0 : D} {ps : List P} {evs : List PEvt} {cfg : PCfg P D} (hv : validRun (fuseStep pstepS) img d0 ps evs cfg) :
    closedS pstepS Inv cfg := by
  intro k ag hk
  left
  refine fused_rmw_none hv.1 (fun k ag hk => ?_) k ag hk
  simp only [pmInit, List.getElem?_map, Option.map_eq_some_iff] at hk
  obtain ⟨p, _, rfl⟩ := hk
  rfl

/-- **`amoSplitFused` (plan M10 (4)), emission v2.**  Under the Sail AMO-sequencing premise `amoTightV2 ps`:
(⇒) every valid run of machine v2 over the Sail emission `pstepV2` that ends with no hart between its AMO halves
(`closedS`) is matched by a valid run over the fused program `fuseStep pstepV2` with THE SAME final configuration
and per-hart traces related by `TrRel` (each `LRmw` ↦ `LAmoLd`, `LSilent`*, `LAmoSt`); (⇐) every valid run over
`fuseStep pstepV2` is a valid run over `pstepV2` with the same final configuration, traces related by `TrRel`. -/
theorem amoSplitFused {img : Image} {d0 : DevStates} {ps : List HState} (htight : amoTightV2 ps) :
    (∀ evs cfg, validRun pstepV2 img d0 ps evs cfg → closedS pstepV2 (v2Inv ps) cfg →
      ∃ evsF, validRun (fuseStep pstepV2) img d0 ps evsF cfg ∧ ∀ h, TrRel (traceOf h evsF) (traceOf h evs)) ∧
    (∀ evsF cfg, validRun (fuseStep pstepV2) img d0 ps evsF cfg →
      ∃ evs, validRun pstepV2 img d0 ps evs cfg ∧ ∀ h, TrRel (traceOf h evsF) (traceOf h evs)) :=
  ⟨fun _ _ hv hcl => splitToFused_closed (splitOk_v2 htight) (fun p hp => ⟨p, hp, .refl p⟩) hv hcl,
   fun _ _ hv => fusedToSplit (fuseOk_fuse pstepV2) (fun _ _ => trivial) hv⟩

/-- **The behaviours agree**: a configuration is the final configuration of a valid fused run iff it is the final
configuration of a valid Sail-emission run with no hart between its AMO halves. -/
theorem amoSplitFused_behavior {img : Image} {d0 : DevStates} {ps : List HState} (htight : amoTightV2 ps)
    (cfg : PCfg HState DevStates) :
    pmBehavior (fuseStep pstepV2) img d0 ps cfg ↔
      (pmBehavior pstepV2 img d0 ps cfg ∧ closedS pstepV2 (v2Inv ps) cfg) := by
  constructor
  · rintro ⟨evsF, hv⟩
    obtain ⟨evs, hv', _⟩ := (amoSplitFused htight).2 evsF cfg hv
    exact ⟨⟨evs, hv'⟩, fused_closed hv⟩
  · rintro ⟨⟨evs, hv⟩, hcl⟩
    obtain ⟨evsF, hvF, _⟩ := (amoSplitFused htight).1 evs cfg hv hcl
    exact ⟨evsF, hvF⟩

/-- `amoSplitFused` (⇒) WITHOUT the closedness side condition: `splitToFused`'s general form (a hart that ends
between its halves keeps its pre-read agent on the fused side, and its trace is `TrRelP`'s second form). -/
theorem amoSplitFused_any {img : Image} {d0 : DevStates} {ps : List HState} (htight : amoTightV2 ps)
    {evs : List PEvt} {cfg : PCfg HState DevStates} (hv : validRun pstepV2 img d0 ps evs cfg) :
    ∃ evsF cfgF, validRun (fuseStep pstepV2) img d0 ps evsF cfgF ∧ cfgF.pcImg = cfg.pcImg ∧
      cfgF.pcLog = cfg.pcLog ∧ cfgF.pcDev = cfg.pcDev ∧ cfgF.pcAgs.length = cfg.pcAgs.length ∧
      (∀ h, TrRelP (traceOf h evsF) (traceOf h evs)) ∧
      (∀ h, cfg.pcAgs.length ≤ h → traceOf h evsF = [] ∧ traceOf h evs = []) ∧
      (∀ (k : Nat) (agS : PAgent HState), cfg.pcAgs[k]? = some agS → ∃ agF, cfgF.pcAgs[k]? = some agF ∧
        ((agF = agS ∧ TrRel (traceOf k evsF) (traceOf k evs)) ∨
         (agS.paWs.wRmw ≠ none ∧ pendS pstepV2 (v2Inv ps) agS.paSt))) :=
  splitToFused (splitOk_v2 htight) (fun p hp => ⟨p, hp, .refl p⟩) hv

end Weak.Prom.AS
