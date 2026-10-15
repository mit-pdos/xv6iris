/-
Weak: **(c) [OWN.100], increment 6a — the dependency shadow's step function** (`PROGRESS-W10N2p.md`).
Lean-only, no Rocq twin.

`SilDep.wsStep ws l n`: the agent-state update of each arm of the registered promise-free step
(`wpPfStep`, WeakPromiseBridge.lean), as a function of the label and the log length `n`; the inversion
**`SilDep.stepWs`** (a pf step of agent `i` sets agent `i`'s state to `wsStep` of its old state and keeps
the other agents' list entries), and its twin **`SilDep.stepWsS`** (the silent exclusive store's update).
The shadow of increment 6c is this function folded over each step's labels.

Spec: FAITHFUL (proof organisation).
-/
import Weak.SilOrd

namespace Weak

open MachCSL MachCSL.Stdpp

/-- The agent-state update of a promise-free step with label `l` at log length `n`. -/
def SilDep.wsStep (ws : Wstate) (l : Wlabel) (n : Nat) : Wstate :=
  match l with
  | .LSilent => ws
  | .LLoad aq _ base tvs asrc => loadPostRunD ws aq (srcsView ws asrc) base (tvs.map Prod.fst)
  | .LStore rl base data asrc vsrc =>
      storePostRunD ws rl (srcsView ws asrc) (srcsView ws vsrc) base data.length (n + 1)
  | .LRmw aq rl base tvs data asrc vsrc =>
      storePostRunD (loadPostRunD ws aq (srcsView ws asrc) base (tvs.map Prod.fst))
        rl (srcsView ws asrc) (srcsView ws vsrc) base data.length (n + 1)
  | .LFence pr pw sr sw => fencePost ws pr pw sr sw
  | .LDev .. => ws
  | .LRegW rd srcs => regwPost ws rd (srcsView ws srcs)
  | .LCtrl srcs => ctrlPost ws (srcsView ws srcs)
  | .LInstr => instrPost ws
  | .LExLoad aq base tvs asrc =>
      exloadPostRunD ws aq (srcsView ws asrc) base (tvs.map Prod.fst)
  | .LExStore rl base data asrc vsrc =>
      storePostRunD ws rl (srcsView ws asrc) (srcsView ws vsrc) base data.length (n + 1)
  | .LIFetch .. => ws

/-- The silent exclusive store's update at position `q`. -/
def SilDep.silentWs (ws : Wstate) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (base : Int)
    (q : Nat) : Wstate :=
  storePostRunD (SilCand.aqRaise ws q) false (srcsView ws asrc) (srcsView ws vsrc) base data.length q

section twin

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- **THE INVERSION**: a registered pf step of agent `i` replaces agent `i`'s entry by its program
successor with state `wsStep`. -/
theorem SilDep.stepWs (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpPfStep pstep pcls i l c c' →
    ∃ (ag : Wpagent P) (st' : P), c.pcAgs[i]? = some ag ∧
      c'.pcAgs = c.pcAgs.set i ⟨st', SilDep.wsStep ag.paWs l c.pcLog.length, ag.paProm⟩ := by
  intro h
  cases h <;> exact ⟨_, _, by assumption, rfl⟩

/-- The twin inversion: a registered step, or the silent exclusive store. -/
theorem SilDep.stepWsS (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    SilPf.wpPfStepS pstep pcls i l c c' →
    ∃ (ag : Wpagent P) (st' : P), c.pcAgs[i]? = some ag ∧
      ((c'.pcAgs = c.pcAgs.set i ⟨st', SilDep.wsStep ag.paWs l c.pcLog.length, ag.paProm⟩) ∨
       (∃ (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (q : Nat),
          l = .LExStore false base data asrc vsrc ∧
          c'.pcAgs = c.pcAgs.set i ⟨st', SilDep.silentWs ag.paWs data asrc vsrc base q,
            ag.paProm⟩)) := by
  intro h
  cases h with
  | old l c c' h =>
    obtain ⟨ag, st', hlk, he⟩ := SilDep.stepWs pstep pcls i l c c' h
    exact ⟨ag, st', hlk, .inl he⟩
  | exStoreSilent cfg ag base data asrc vsrc R q st' d' hlk =>
    exact ⟨ag, st', hlk, .inr ⟨base, data, asrc, vsrc, q, rfl, rfl⟩⟩

/-- A step of agent `i` keeps every other agent's entry. -/
theorem SilDep.stepOther (i j : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    SilPf.wpPfStepS pstep pcls i l c c' → j ≠ i → c'.pcAgs[j]? = c.pcAgs[j]? := by
  intro h hj
  obtain ⟨ag, st', -, he | ⟨_, _, _, _, _, -, he⟩⟩ := SilDep.stepWsS pstep pcls i l c c' h <;>
    rw [he, List.getElem?_set_ne (Ne.symm hj)]

end twin

/-- The number of messages a label appends. -/
def SilDep.wcount (l : Wlabel) : Nat :=
  match l with
  | .LStore .. | .LRmw .. | .LExStore .. => 1
  | _ => 0

/-- The agent state and log length along a label list. -/
def SilDep.runWs (p : Wstate × Nat) (ls : List Wlabel) : Wstate × Nat :=
  ls.foldl (fun p l => (SilDep.wsStep p.1 l p.2, p.2 + SilDep.wcount l)) p

/-- A star (no appends): the agent state folded at a fixed log length. -/
def SilDep.starWs (ws : Wstate) (ls : List Wlabel) (n : Nat) : Wstate :=
  ls.foldl (fun w l => SilDep.wsStep w l n) ws

section twin2

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- A registered step appends `wcount l` messages. -/
theorem SilDep.stepLog (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpPfStep pstep pcls i l c c' → c'.pcLog.length = c.pcLog.length + SilDep.wcount l := by
  intro h
  cases h <;> simp [SilDep.wcount]

/-- **THE STAR, EXACTLY**: `SilPair.admRunRtc` with the agent's final state. -/
theorem SilDep.admRunRtcW (instr : Bool) (p : P) (d : D) (ls : List Wlabel) (p' : P) (d' : D) :
    admRunG pstep instr p d ls p' d' →
    ∀ (c : Wpcfg P D) (i : Nat) (ag : Wpagent P),
      c.pcAgs[i]? = some ag → ag.paSt = p → c.pcDev = d →
      (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
        ifetchOk c.pcImg c.pcLog 0 base tvs) →
      ∃ (c' : Wpcfg P D) (ag' : Wpagent P),
        rtc (wpPfRun pstep pcls) c c' ∧ cfgEqr c c' ∧ c'.pcDev = d' ∧
        c'.pcAgs[i]? = some ag' ∧ ag'.paSt = p' ∧
        ag'.paWs = SilDep.starWs ag.paWs ls c.pcLog.length ∧
        (∀ j, j ≠ i → c'.pcAgs[j]? = c.pcAgs[j]?) ∧
        c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' := by
  intro h
  induction h with
  | nil p d =>
    intro c i ag hlk hst hdev _
    refine ⟨c, ag, rtc_refl _, cfgEqrRefl c, hdev, hlk, hst, rfl, fun _ _ => rfl, ?_⟩
    exact (listSetLookupId (by simp [List.getElem?_map, hlk, hst])).symm
  | cons p d l p1 d1 ls p' d' hadm hps _ ih =>
    intro c i ag hlk hst hdev hf
    obtain ⟨c1, ag1, hstep, he1, hd1, hl1, hs1, -, -, hf1⟩ :=
      PfRunUnpinned.admStepPfF pstep pcls instr c i ag l p1 d1 hadm
        (fun b t hl => by subst hl; exact hf b t (List.mem_cons.2 (.inl rfl))) hlk
        (by rw [hst, hdev]; exact hps)
    obtain ⟨ag0, st0, hlk0, hset⟩ := SilDep.stepWs pstep pcls i l c c1 hstep
    rw [hlk, Option.some.injEq] at hlk0
    subst hlk0
    have hw1 : ag1.paWs = SilDep.wsStep ag.paWs l c.pcLog.length := by
      rw [hset, List.getElem?_set_self (lookup_lt_Some hlk), Option.some.injEq] at hl1
      rw [← hl1]
    have hoth1 : ∀ j, j ≠ i → c1.pcAgs[j]? = c.pcAgs[j]? := by
      intro j hj; rw [hset, List.getElem?_set_ne (Ne.symm hj)]
    obtain ⟨c2, ag2, hrun, he2, hd2, hl2, hs2, hw2, hoth2, hf2⟩ :=
      ih c1 i ag1 hl1 hs1 hd1
        (fun b t hm => by rw [he1.1, he1.2.1]; exact hf b t (List.mem_cons.2 (.inr hm)))
    refine ⟨c2, ag2, rtc_l ⟨i, l, hstep⟩ hrun, cfgEqrTrans _ _ _ he1 he2, hd2, hl2, hs2, ?_,
      fun j hj => (hoth2 j hj).trans (hoth1 j hj), ?_⟩
    · rw [hw2, hw1, he1.2.1]; rfl
    · rw [hf2, hf1, list_insert_insert]

end twin2

end Weak
