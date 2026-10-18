/-
Weak: **(c) [OWN.100], increment 6a — the dependency shadow's step function** (`PROGRESS-W10N2p.md`).
Lean-only, no Rocq twin.

`SilDep.wsStep ws l n`: the agent-state update of each arm of the registered promise-free step
(`wpPfStep`, WeakPromiseBridge.lean), as a function of the label and the log length `n`; the inversion
**`SilDep.stepWs`** (a pf step of agent `i` sets agent `i`'s state to `wsStep` of its old state and keeps
the other agents' list entries), and its twin **`SilDep.stepWsS`** (the silent exclusive store's update).
The shadow of increment 6c is this function folded over each step's labels.

6b: the shadow's block transitions (`SilDep.preW`, the write node's state of a pair block;
`SilDep.depOkL` / `SilDep.silentWsL`, the silent write's dependency bound and update read off its label;
`SilDep.pairSh`), and the labelled-run fold **`SilDep.pfRunSWs`** (a labelled pf run of one agent moves
that agent's state by `runWs` and keeps the others).

Spec: FAITHFUL (proof organisation).
-/
import Weak.SilPfBridge

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

theorem SilDep.runWsAppend (p : Wstate × Nat) (ls ls' : List Wlabel) :
    SilDep.runWs p (ls ++ ls') = SilDep.runWs (SilDep.runWs p ls) ls' := by
  unfold SilDep.runWs
  exact List.foldl_append ..

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
        c'.pcAgs.map Wpagent.paSt = (c.pcAgs.map Wpagent.paSt).set i p' ∧
        wsEqr ag.paWs ag'.paWs ∧ (instr = false → ag'.paWs.wRes = ag.paWs.wRes) := by
  intro h
  induction h with
  | nil p d =>
    intro c i ag hlk hst hdev _
    refine ⟨c, ag, rtc_refl _, cfgEqrRefl c, hdev, hlk, hst, rfl, fun _ _ => rfl, ?_,
      wsEqrRefl _, fun _ => rfl⟩
    exact (listSetLookupId (by simp [List.getElem?_map, hlk, hst])).symm
  | cons p d l p1 d1 ls p' d' hadm hps _ ih =>
    intro c i ag hlk hst hdev hf
    obtain ⟨c1, ag1, hstep, he1, hd1, hl1, hs1, hwe1, hr1, hf1⟩ :=
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
    obtain ⟨c2, ag2, hrun, he2, hd2, hl2, hs2, hw2, hoth2, hf2, hwe2, hr2⟩ :=
      ih c1 i ag1 hl1 hs1 hd1
        (fun b t hm => by rw [he1.1, he1.2.1]; exact hf b t (List.mem_cons.2 (.inr hm)))
    refine ⟨c2, ag2, rtc_l ⟨i, l, hstep⟩ hrun, cfgEqrTrans _ _ _ he1 he2, hd2, hl2, hs2, ?_,
      fun j hj => (hoth2 j hj).trans (hoth1 j hj), ?_, wsEqrTrans hwe1 hwe2,
      fun hi => (hr2 hi).trans (hr1 hi)⟩
    · rw [hw2, hw1, he1.2.1]; rfl
    · rw [hf2, hf1, list_insert_insert]

/-- A labelled pf run of agent `i` alone moves agent `i`'s state and the log length by `runWs`, and
keeps every other agent's entry. -/
theorem SilDep.pfRunSWs (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    (c c' : Wpcfg P D) (st : List (Nat × Wlabel)) :
    pfRunS pstep pcls fok c st c' →
    ∀ (i : Nat) (ag : Wpagent P), c.pcAgs[i]? = some ag → (∀ x, x ∈ st → x.1 = i) →
      ∃ ag' : Wpagent P, c'.pcAgs[i]? = some ag' ∧
        (ag'.paWs, c'.pcLog.length) = SilDep.runWs (ag.paWs, c.pcLog.length) (st.map Prod.snd) ∧
        ∀ j, j ≠ i → c'.pcAgs[j]? = c.pcAgs[j]? := by
  intro h
  induction h with
  | nil =>
    intro i ag hlk _
    exact ⟨ag, hlk, rfl, fun _ _ => rfl⟩
  | snoc c1 c2 st i' l _ hs _ ih =>
    intro i ag hlk hall
    have hi : i' = i := hall (i', l) (List.mem_append.2 (.inr (List.mem_singleton.2 rfl)))
    subst hi
    obtain ⟨ag1, hl1, hw1, ho1⟩ :=
      ih i' ag hlk (fun x hx => hall x (List.mem_append.2 (.inl hx)))
    obtain ⟨ag0, st', hlk0, hset⟩ := SilDep.stepWs pstep pcls i' l c1 c2 hs
    rw [hl1, Option.some.injEq] at hlk0
    subst hlk0
    refine ⟨⟨st', SilDep.wsStep ag1.paWs l c1.pcLog.length, ag1.paProm⟩, ?_, ?_, ?_⟩
    · rw [hset]; exact List.getElem?_set_self (lookup_lt_Some hl1)
    · rw [List.map_append, SilDep.runWsAppend, ← hw1, SilDep.stepLog pstep pcls i' l c1 c2 hs]
      rfl
    · intro j hj
      rw [hset, List.getElem?_set_ne (Ne.symm hj)]
      exact ho1 j hj

end twin2

/-! # The shadow's block transitions -/

/-- The write node's state of a pair block: the leading star `ls`, the exclusive read `l1`, the
intra-pair star `ls2`, from `w` at log length `n`. -/
def SilDep.preW (w : Wstate) (ls : List Wlabel) (l1 : Wlabel) (ls2 : List Wlabel) (n : Nat) :
    Wstate :=
  SilDep.starWs (SilDep.wsStep (SilDep.starWs w ls n) l1 n) ls2 n

/-- The silent write's dependency bound, read off its label. -/
def SilDep.depOkL (w : Wstate) (l : Wlabel) (q : Nat) : Prop :=
  match l with
  | .LExStore _ _ _ asrc vsrc => SilCand.depView w asrc vsrc ≤ q
  | _ => True

/-- The silent write's update, read off its label. -/
def SilDep.silentWsL (w : Wstate) (l : Wlabel) (q : Nat) : Wstate :=
  match l with
  | .LExStore _ base data asrc vsrc => SilDep.silentWs w data asrc vsrc base q
  | _ => w

/-- **THE SHADOW OF A PAIR BLOCK**: ordinary, the registered pair's update; silent at `q`, the
dependency bound at the write node and the silent update. -/
def SilDep.pairSh (w : Wstate) (ls : List Wlabel) (l1 : Wlabel) (ls2 : List Wlabel) (l2 : Wlabel)
    (n : Nat) (o : Option Nat) (w' : Wstate) : Prop :=
  match o with
  | none => w' = SilDep.wsStep (SilDep.preW w ls l1 ls2 n) l2 n
  | some q => SilDep.depOkL (SilDep.preW w ls l1 ls2 n) l2 q ∧
      w' = SilDep.silentWsL (SilDep.preW w ls l1 ls2 n) l2 q

/-- A label that appends nothing leaves `runWs`'s log length; a list of them folds as `starWs`. -/
theorem SilDep.runWsZero (ls : List Wlabel) :
    (∀ l, l ∈ ls → SilDep.wcount l = 0) →
    ∀ (w : Wstate) (n : Nat), SilDep.runWs (w, n) ls = (SilDep.starWs w ls n, n) := by
  induction ls with
  | nil => intro _ w n; rfl
  | cons l ls ih =>
    intro h w n
    have h0 := h l (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) (SilDep.wsStep w l n) n
    show SilDep.runWs (SilDep.wsStep w l n, n + SilDep.wcount l) ls = _
    rw [h0, Nat.add_zero, this]
    rfl

theorem SilDep.adminWcount (instr : Bool) (l : Wlabel) : lbAdmin instr l → SilDep.wcount l = 0 := by
  cases l <;> simp [lbAdmin, SilDep.wcount]

/-- The registered pair block's labels fold to the pair's shadow. -/
theorem SilDep.runWsPair (i : Nat) (w : Wstate) (n : Nat) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (asrc1 : List Dsrc) (ls2 : List Wlabel) (l2 : Wlabel) :
    (∀ l, l ∈ ls2 → lbAdmin false l) →
    (SilDep.runWs (w, n) (((i, Wlabel.LExLoad aq base tvs asrc1) ::
        (ls2.map (fun l => (i, l)) ++ [(i, l2)])).map Prod.snd)).1
      = SilDep.wsStep (SilDep.starWs (SilDep.wsStep w (.LExLoad aq base tvs asrc1) n) ls2 n) l2 n := by
  intro had
  have hm : (((i, Wlabel.LExLoad aq base tvs asrc1) ::
      (ls2.map (fun l => (i, l)) ++ [(i, l2)])).map Prod.snd)
      = (Wlabel.LExLoad aq base tvs asrc1 :: ls2) ++ [l2] := by
    simp [List.map_map, Function.comp_def]
  rw [hm, SilDep.runWsAppend,
    SilDep.runWsZero (Wlabel.LExLoad aq base tvs asrc1 :: ls2) (fun l hl => by
      rcases List.mem_cons.1 hl with rfl | hl
      · rfl
      · exact SilDep.adminWcount false l (had l hl)) w n]
  rfl

end Weak
