/-
Weak: **W11-C2′ (b-L) [OWN.82][OWN.97] — the PRIMED pf machine (the walker's write-back keeps the
release flag), a separate instance used only by the release-tag chain.**

Owner ruling [OWN.97] (PRIMED TWINS): every definition the registered M1/M2 use stays EXACTLY
unchanged.  So this file adds NOTHING to the label alphabet or to the class type.  The primed
machine `WbPrimed.wpPfStepW` is `wpPfStep` verbatim except in ONE arm: at an `LExStore` step
whose agent sits at a WRITE-BACK node (`pwb`; for the event instance `WbPrimed.pwbEv`, an
exclusive write outside an AMO-opcode instruction, i.e. the page walker's
`write_pte_conditional`, which Sail issues with the same access kind as `sc`) the post-state
KEEPS the release-pending flag `wRelp` and the publication watermark `wPub`
(`WbPrimed.exPost`).  RVWMO's FENCE orders EXPLICIT later stores (ppo rule 4); Svadu's A/D
update is an implicit access.  Labels, side conditions, program steps and the class function
are the registered ones (the class is still `pcls` at the agent's — now primed — state).

* `WbPrimed.mask` / `WbPrimed.wsEqX`: two hart states agree except on `wPub`/`wRelp`.
* The mask-commutation lemmas: no view effect reads `wPub`/`wRelp` except to compute them.
* THE SIMULATION (`WbPrimed.stepFwd`, `WbPrimed.stepBwd`, `WbPrimed.runFwd`, `WbPrimed.runBwd`):
  registered run ↔ primed run, step for step at the same labels and program states, the logs
  equal up to a positional re-tag of classes (`retagLog`), the agents' states equal except
  `wPub`/`wRelp` (`WbPrimed.cfgRel`).

Lean-only (no Rocq counterpart); every name is file-qualified (`WbPrimed.*`).
-/
import Weak.WeakRetag
import Weak.WeakEvInst

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Wlabel

/-! ## 1. Agreement except on the release bookkeeping -/

/-- Forget `wPub`/`wRelp`. -/
def WbPrimed.mask (w : Wstate) : Wstate := { w with wPub := 0, wRelp := false }

/-- Two hart states agree except on `wPub`/`wRelp`. -/
def WbPrimed.wsEqX (w1 w2 : Wstate) : Prop := WbPrimed.mask w1 = WbPrimed.mask w2

/-- Restore `ws`'s `wPub`/`wRelp` on `w`. -/
def WbPrimed.keepPR (ws w : Wstate) : Wstate := { w with wPub := ws.wPub, wRelp := ws.wRelp }

/-- The exclusive store's post-state in the primed machine. -/
def WbPrimed.exPost (b : Bool) (ws w : Wstate) : Wstate := bif b then WbPrimed.keepPR ws w else w

theorem WbPrimed.maskMask (w : Wstate) : WbPrimed.mask (WbPrimed.mask w) = WbPrimed.mask w := rfl

theorem WbPrimed.maskExPost (b : Bool) (ws w : Wstate) :
    WbPrimed.mask (WbPrimed.exPost b ws w) = WbPrimed.mask w := by
  cases b <;> rfl

theorem WbPrimed.maskFoldl {α : Type} (g : Wstate → α → Wstate)
    (hg : ∀ w x, WbPrimed.mask (g w x) = WbPrimed.mask (g (WbPrimed.mask w) x)) :
    ∀ (l : List α) (w : Wstate),
      WbPrimed.mask (l.foldl g w) = WbPrimed.mask (l.foldl g (WbPrimed.mask w)) := by
  intro l
  induction l with
  | nil => intro w; rfl
  | cons x l ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih (g w x), hg w x, ← ih (g (WbPrimed.mask w) x)]

theorem WbPrimed.maskLoadPostAt (w : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    WbPrimed.mask (loadPostAt w aq vpre a t)
      = WbPrimed.mask (loadPostAt (WbPrimed.mask w) aq vpre a t) := rfl

theorem WbPrimed.maskStorePostD (w : Wstate) (rl : Bool) (vf : Nat) (a : Int) (t : Nat) :
    WbPrimed.mask (storePostD w rl vf a t)
      = WbPrimed.mask (storePostD (WbPrimed.mask w) rl vf a t) := rfl

theorem WbPrimed.maskCtrlPost (w : Wstate) (v : Nat) :
    WbPrimed.mask (ctrlPost w v) = WbPrimed.mask (ctrlPost (WbPrimed.mask w) v) := rfl

theorem WbPrimed.srcsViewMask (w : Wstate) (l : List Dsrc) :
    srcsView (WbPrimed.mask w) l = srcsView w l := rfl

/-- A masked equation transports through `f` when `f` commutes with the mask. -/
theorem WbPrimed.maskCongr (f : Wstate → Wstate)
    (hf : ∀ w, WbPrimed.mask (f w) = WbPrimed.mask (f (WbPrimed.mask w))) (w1 w2 : Wstate) :
    WbPrimed.mask w1 = WbPrimed.mask w2 → WbPrimed.mask (f w1) = WbPrimed.mask (f w2) := by
  intro h
  rw [hf w1, hf w2, h]

theorem WbPrimed.maskBytesLoad (ws : Wstate) (aq : Bool) (vpre : Nat) (ats : List (Int × Nat))
    (w : Wstate) :
    WbPrimed.mask (ats.foldl (fun w' (x : Int × Nat) => loadPostAt w' aq vpre x.1 x.2) w)
      = WbPrimed.mask (ats.foldl (fun w' (x : Int × Nat) => loadPostAt w' aq vpre x.1 x.2)
          (WbPrimed.mask w)) :=
  WbPrimed.maskFoldl _ (fun w' x => WbPrimed.maskLoadPostAt w' aq vpre x.1 x.2) ats w

theorem WbPrimed.maskBytesStore (rl : Bool) (vf : Nat) (as_ : List Int) (t : Nat) (w : Wstate) :
    WbPrimed.mask (as_.foldl (fun w' a => storePostD w' rl vf a t) w)
      = WbPrimed.mask (as_.foldl (fun w' a => storePostD w' rl vf a t) (WbPrimed.mask w)) :=
  WbPrimed.maskFoldl _ (fun w' x => WbPrimed.maskStorePostD w' rl vf x t) as_ w

/-- The run-level read. -/
theorem WbPrimed.maskLoadPostRunD (w : Wstate) (aq : Bool) (vaddr : Nat) (base : Int)
    (ts : List Nat) :
    WbPrimed.mask (loadPostRunD w aq vaddr base ts)
      = WbPrimed.mask (loadPostRunD (WbPrimed.mask w) aq vaddr base ts) := by
  show WbPrimed.mask (ctrlPost (loadPostBytesD w aq vaddr (loadRunAts base ts)) (max vaddr w.wTbank))
    = WbPrimed.mask (ctrlPost (loadPostBytesD (WbPrimed.mask w) aq vaddr (loadRunAts base ts))
        (max vaddr w.wTbank))
  rw [WbPrimed.maskCtrlPost, WbPrimed.maskCtrlPost (loadPostBytesD (WbPrimed.mask w) _ _ _)]
  unfold loadPostBytesD
  rw [WbPrimed.maskBytesLoad w aq (loadVpreD w aq vaddr) (loadRunAts base ts) w]
  rfl

theorem WbPrimed.maskLoadPostRun (w : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    WbPrimed.mask (loadPostRun w aq base ts)
      = WbPrimed.mask (loadPostRun (WbPrimed.mask w) aq base ts) := by
  rw [← loadPostRunD0, ← loadPostRunD0]
  exact WbPrimed.maskLoadPostRunD w aq 0 base ts

/-- The run-level write. -/
theorem WbPrimed.maskStorePostRunD (w : Wstate) (rl : Bool) (va vd : Nat) (base : Int)
    (n t : Nat) :
    WbPrimed.mask (storePostRunD w rl va vd base n t)
      = WbPrimed.mask (storePostRunD (WbPrimed.mask w) rl va vd base n t) := by
  show WbPrimed.mask (ctrlPost (storePostBytesD w rl (max va vd) (storeRunAs base n) t)
      (max va w.wTbank))
    = WbPrimed.mask (ctrlPost (storePostBytesD (WbPrimed.mask w) rl (max va vd) (storeRunAs base n) t)
        (max va w.wTbank))
  rw [WbPrimed.maskCtrlPost, WbPrimed.maskCtrlPost (storePostBytesD (WbPrimed.mask w) _ _ _ _)]
  unfold storePostBytesD
  rw [WbPrimed.maskBytesStore rl (max va vd) (storeRunAs base n) t w]

theorem WbPrimed.maskFencePost (w : Wstate) (pr pw sr sw : Bool) :
    WbPrimed.mask (fencePost w pr pw sr sw)
      = WbPrimed.mask (fencePost (WbPrimed.mask w) pr pw sr sw) := rfl

theorem WbPrimed.maskRegwPost (w : Wstate) (rd v : Nat) :
    WbPrimed.mask (regwPost w rd v) = WbPrimed.mask (regwPost (WbPrimed.mask w) rd v) := rfl

theorem WbPrimed.maskInstrPost (w : Wstate) :
    WbPrimed.mask (instrPost w) = WbPrimed.mask (instrPost (WbPrimed.mask w)) := rfl

theorem WbPrimed.ldvOfMask (w : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    ldvOf (WbPrimed.mask w) aq vaddr base ts = ldvOf w aq vaddr base ts := by
  have h := WbPrimed.maskLoadPostRunD (instrPost w) aq vaddr base ts
  have h2 := WbPrimed.maskLoadPostRunD (instrPost (WbPrimed.mask w)) aq vaddr base ts
  have e : WbPrimed.mask (instrPost (WbPrimed.mask w)) = WbPrimed.mask (instrPost w) := rfl
  rw [e] at h2
  have e2 := congrArg Wstate.wLdv (h2.trans h.symm)
  exact e2

theorem WbPrimed.maskExloadPostRunD (w : Wstate) (aq : Bool) (vaddr : Nat) (base : Int)
    (ts : List Nat) :
    WbPrimed.mask (exloadPostRunD w aq vaddr base ts)
      = WbPrimed.mask (exloadPostRunD (WbPrimed.mask w) aq vaddr base ts) := by
  unfold exloadPostRunD
  rw [WbPrimed.ldvOfMask]
  have h : WbPrimed.mask (ctrlPost (loadPostBytes w aq
        (List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' 0 ts.length) ts))
        (max vaddr w.wTbank))
      = WbPrimed.mask (ctrlPost (loadPostBytes (WbPrimed.mask w) aq
        (List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' 0 ts.length) ts))
        (max vaddr w.wTbank)) := by
    rw [WbPrimed.maskCtrlPost, WbPrimed.maskCtrlPost (loadPostBytes (WbPrimed.mask w) _ _)]
    unfold loadPostBytes
    rw [WbPrimed.maskBytesLoad w aq (loadVpre w aq) _ w]
    rfl
  have e3 := congrArg (fun z => wsResSet z (some ⟨base, ts, ldvOf w aq 0 base ts⟩)) h
  exact e3

/-! ## 2. The primed machine -/

section primed

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (pwb : P → Bool)

/-- **THE PRIMED pf MACHINE**: `wpPfStep` verbatim, except that an `LExStore` step taken at a
write-back node (`pwb`) keeps `wPub`/`wRelp` (`WbPrimed.exPost`). -/
inductive WbPrimed.wpPfStepW (i : Nat) : Wlabel → Wpcfg P D → Wpcfg P D → Prop
  | PFSilent (cfg : Wpcfg P D) (ag : Wpagent P) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev .LSilent st' d' →
      WbPrimed.wpPfStepW i .LSilent cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', ag.paWs, ag.paProm⟩⟩
  | PFLoad (cfg : Wpcfg P D) (ag : Wpagent P) (aq lat : Bool) (base : Int)
      (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LLoad aq lat base tvs asrc) st' d' →
      readOkD cfg.pcImg cfg.pcLog ag.paWs aq lat base tvs (srcsView ag.paWs asrc) →
      WbPrimed.wpPfStepW i (.LLoad aq lat base tvs asrc) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st',
           loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst),
           ag.paProm⟩⟩
  | PFStore (cfg : Wpcfg P D) (ag : Wpagent P) (rl : Bool) (base : Int)
      (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (k : WmClass) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LStore rl base data asrc vsrc) st' d' →
      data ≠ [] →
      k = pcls ag.paSt (.LStore rl base data asrc vsrc) ag.paWs →
      WbPrimed.wpPfStepW i (.LStore rl base data asrc vsrc) cfg
        ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], d',
         cfg.pcAgs.set i ⟨st',
           storePostRunD ag.paWs rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc)
             base data.length (cfg.pcLog.length + 1),
           ag.paProm⟩⟩
  | PFRmw (cfg : Wpcfg P D) (ag : Wpagent P) (aq rl : Bool) (base : Int)
      (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
      (k : WmClass) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LRmw aq rl base tvs data asrc vsrc) st' d' →
      data ≠ [] →
      tvs.length = data.length →
      -- D-2r: the 0 floor, mirroring `wpstep.WPRmw`.
      readOk cfg.pcImg cfg.pcLog ag.paWs aq false base tvs →
      exclOk cfg.pcLog i base tvs (cfg.pcLog.length + 1) →
      k = pcls ag.paSt (.LRmw aq rl base tvs data asrc vsrc) ag.paWs →
      WbPrimed.wpPfStepW i (.LRmw aq rl base tvs data asrc vsrc) cfg
        ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], d',
         cfg.pcAgs.set i ⟨st',
           storePostRunD
             (loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))
             rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc)
             base data.length (cfg.pcLog.length + 1),
           ag.paProm⟩⟩
  | PFFence (cfg : Wpcfg P D) (ag : Wpagent P) (pr pw sr sw : Bool) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LFence pr pw sr sw) st' d' →
      WbPrimed.wpPfStepW i (.LFence pr pw sr sw) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', fencePost ag.paWs pr pw sr sw, ag.paProm⟩⟩
  | PFDev (cfg : Wpcfg P D) (ag : Wpagent P) {kd : IoKind} {ba : Int} {bs : List (BitVec 8)}
      {sa sv : List Dsrc} (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LDev kd ba bs sa sv) st' d' →
      WbPrimed.wpPfStepW i (.LDev kd ba bs sa sv) cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', ag.paWs, ag.paProm⟩⟩
  | PFRegW (cfg : Wpcfg P D) (ag : Wpagent P) (rd : Nat) (srcs : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LRegW rd srcs) st' d' →
      WbPrimed.wpPfStepW i (.LRegW rd srcs) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', regwPost ag.paWs rd (srcsView ag.paWs srcs), ag.paProm⟩⟩
  | PFCtrl (cfg : Wpcfg P D) (ag : Wpagent P) (srcs : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LCtrl srcs) st' d' →
      WbPrimed.wpPfStepW i (.LCtrl srcs) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', ctrlPost ag.paWs (srcsView ag.paWs srcs), ag.paProm⟩⟩
  | PFInstr (cfg : Wpcfg P D) (ag : Wpagent P) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev .LInstr st' d' →
      WbPrimed.wpPfStepW i .LInstr cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', instrPost ag.paWs, ag.paProm⟩⟩
  | PFExLoad (cfg : Wpcfg P D) (ag : Wpagent P) (aq : Bool) (base : Int)
      (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LExLoad aq base tvs asrc) st' d' →
      -- D-2r: the 0 floor, mirroring `wpstep.WPExLoad`.
      readOk cfg.pcImg cfg.pcLog ag.paWs aq false base tvs →
      WbPrimed.wpPfStepW i (.LExLoad aq base tvs asrc) cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st',
           exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst),
           ag.paProm⟩⟩
  | PFExStore (cfg : Wpcfg P D) (ag : Wpagent P) (rl : Bool) (base : Int)
      (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (k : WmClass) (R : Wresv) (st' : P)
      (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LExStore rl base data asrc vsrc) st' d' →
      data ≠ [] →
      ag.paWs.wRes = some R →
      R.rvBase = base →
      R.rvTs.length = data.length →
      exclOkTs cfg.pcLog i base R.rvTs (cfg.pcLog.length + 1) →
      k = pcls ag.paSt (.LExStore rl base data asrc vsrc) ag.paWs →
      WbPrimed.wpPfStepW i (.LExStore rl base data asrc vsrc) cfg
        ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], d',
         cfg.pcAgs.set i ⟨st',
           -- THE ONE DIFFERENCE: at a write-back node the release flag and watermark are KEPT
           WbPrimed.exPost (pwb ag.paSt) ag.paWs
             (storePostRunD ag.paWs rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc)
               base data.length (cfg.pcLog.length + 1)),
           ag.paProm⟩⟩
  /-- O2 (Lean-only, deviation 6): the twin of `wpstep.WPIFetch` — an i-cache read at
  instruction view 0, state and log unchanged. -/
  | PFIFetch (cfg : Wpcfg P D) (ag : Wpagent P) (base : Int) (tvs : List (Nat × BitVec 8))
      (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (.LIFetch base tvs) st' d' →
      ifetchOk cfg.pcImg cfg.pcLog 0 base tvs →
      WbPrimed.wpPfStepW i (.LIFetch base tvs) cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', ag.paWs, ag.paProm⟩⟩


/-- One primed step. -/
def WbPrimed.wpPfRunW (c c' : Wpcfg P D) : Prop := ∃ i l, WbPrimed.wpPfStepW pstep pcls pwb i l c c'

end primed


/-! ## 3. The simulation: registered run ↔ primed run -/

/-- Retagging depends on the class function only below the log's length. -/
theorem WbPrimed.retagLogCongr (f g : Nat → WmClass) (log : List Wmsg) :
    (∀ p, p < log.length → f p = g p) → retagLog f log = retagLog g log := by
  intro h
  apply List.ext_getElem?
  intro p
  rw [retagLogLookup, retagLogLookup]
  by_cases hp : p < log.length
  · rw [List.getElem?_eq_getElem hp]
    simp only [Option.map_some, retagMsg, h p hp]
  · rw [List.getElem?_eq_none (by omega)]
    rfl

/-- A retag survives appending one message (with its own class on each side). -/
theorem WbPrimed.retagSnoc (f : Nat → WmClass) (log : List Wmsg) (base : Int)
    (data : List (BitVec 8)) (tid : Option Nat) (k k' : WmClass) :
    ∃ g, retagLog f log ++ [⟨base, data, tid, k'⟩] = retagLog g (log ++ [⟨base, data, tid, k⟩]) := by
  refine ⟨fun p => if p = log.length then k' else f p, ?_⟩
  rw [retagLogApp]
  congr 1
  · apply WbPrimed.retagLogCongr
    intro p hp
    simp only [if_neg (Nat.ne_of_lt hp)]
  · simp [retagMsg]

/-- THE SIMULATION RELATION: same image and fabric, logs equal up to a positional re-tag of
classes, same agents' program states and promise sets, hart states equal except
`wPub`/`wRelp`. -/
def WbPrimed.cfgRel {P D : Type} (c c' : Wpcfg P D) : Prop :=
  c'.pcImg = c.pcImg ∧ c'.pcDev = c.pcDev ∧ (∃ f, c'.pcLog = retagLog f c.pcLog) ∧
  c'.pcAgs.length = c.pcAgs.length ∧
  ∀ (i : Nat) (ag : Wpagent P), c.pcAgs[i]? = some ag → ∃ ag' : Wpagent P, c'.pcAgs[i]? = some ag' ∧
    ag'.paSt = ag.paSt ∧
    ag'.paProm = ag.paProm ∧ WbPrimed.mask ag'.paWs = WbPrimed.mask ag.paWs

theorem WbPrimed.cfgRelRefl {P D : Type} (c : Wpcfg P D) : WbPrimed.cfgRel c c := by
  refine ⟨rfl, rfl, ⟨untagF c.pcLog, (retagLogUntag c.pcLog).symm⟩, rfl, ?_⟩
  intro i ag h
  exact ⟨ag, h, rfl, rfl, rfl⟩

theorem WbPrimed.cfgRelLogLength {P D : Type} {c c' : Wpcfg P D} (h : WbPrimed.cfgRel c c') :
    c'.pcLog.length = c.pcLog.length := by
  obtain ⟨-, -, ⟨f, hf⟩, -⟩ := h
  rw [hf, retagLogLength]

/-- The registered side's agents, seen from the primed side. -/
theorem WbPrimed.cfgRelInv {P D : Type} {c c' : Wpcfg P D} (h : WbPrimed.cfgRel c c') (i : Nat)
    (ag' : Wpagent P) (hlk : c'.pcAgs[i]? = some ag') :
    ∃ ag, c.pcAgs[i]? = some ag ∧ ag'.paSt = ag.paSt ∧ ag'.paProm = ag.paProm ∧
      WbPrimed.mask ag'.paWs = WbPrimed.mask ag.paWs := by
  obtain ⟨-, -, -, hlen, hags⟩ := h
  have hi : i < c.pcAgs.length := by rw [← hlen]; exact lookup_lt_Some hlk
  obtain ⟨ag, hag⟩ : ∃ ag, c.pcAgs[i]? = some ag := ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨ag'', hlk'', h1, h2, h3⟩ := hags i ag hag
  rw [hlk] at hlk''
  cases hlk''
  exact ⟨ag, hag, h1, h2, h3⟩

/-- The one update lemma every arm uses. -/
theorem WbPrimed.cfgRelSet {P D : Type} (c c' : Wpcfg P D) (i : Nat) (st : P) (w w' : Wstate)
    (pr : GSet Nat) (log log' : List Wmsg) (d : D) :
    WbPrimed.cfgRel c c' → (∃ f, log' = retagLog f log) → WbPrimed.mask w' = WbPrimed.mask w →
    WbPrimed.cfgRel ⟨c.pcImg, log, d, c.pcAgs.set i ⟨st, w, pr⟩⟩
      ⟨c'.pcImg, log', d, c'.pcAgs.set i ⟨st, w', pr⟩⟩ := by
  rintro ⟨himg, -, -, hlen, hags⟩ hlog hw
  refine ⟨himg, rfl, hlog, by simp [hlen], ?_⟩
  intro j ag hj
  rcases lookupSetCases hj with ⟨rfl, rfl⟩ | ⟨hne, hj'⟩
  · refine ⟨⟨st, w', pr⟩, list_lookup_insert ?_, rfl, rfl, hw⟩
    have := lookup_lt_Some hj
    simp only [List.length_set] at this
    omega
  · obtain ⟨ag', h1, h2, h3, h4⟩ := hags j ag hj'
    exact ⟨ag', by rw [list_lookup_insert_ne (Ne.symm hne)]; exact h1, h2, h3, h4⟩

theorem WbPrimed.srcsViewEqX {w w' : Wstate} (h : WbPrimed.mask w' = WbPrimed.mask w)
    (l : List Dsrc) : srcsView w' l = srcsView w l := by
  rw [← WbPrimed.srcsViewMask w' l, h, WbPrimed.srcsViewMask]

theorem WbPrimed.readOkDMask (img : Image) (log : List Wmsg) (w : Wstate) (aq lat : Bool)
    (base : Int) (tvs : List (Nat × BitVec 8)) (va : Nat) :
    readOkD img log (WbPrimed.mask w) aq lat base tvs va ↔ readOkD img log w aq lat base tvs va :=
  Iff.rfl

theorem WbPrimed.readOkDEqX (img : Image) (log : List Wmsg) {w w' : Wstate}
    (h : WbPrimed.mask w' = WbPrimed.mask w) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (va : Nat) :
    readOkD img log w aq lat base tvs va → readOkD img log w' aq lat base tvs va := by
  intro hr
  rw [← WbPrimed.readOkDMask, h, WbPrimed.readOkDMask]
  exact hr

theorem WbPrimed.wResEqX {w w' : Wstate} (h : WbPrimed.mask w' = WbPrimed.mask w) :
    w'.wRes = w.wRes := by
  have e := congrArg Wstate.wRes h
  exact e

section sim

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (pwb : P → Bool)

/-- **THE SIMULATION, forward**: every registered step is matched by a primed step at the same
label. -/
theorem WbPrimed.stepFwd (i : Nat) (l : Wlabel) (c c1 c' : Wpcfg P D) :
    wpPfStep pstep pcls i l c c1 → WbPrimed.cfgRel c c' →
    ∃ c1', WbPrimed.wpPfStepW pstep pcls pwb i l c' c1' ∧ WbPrimed.cfgRel c1 c1' := by
  intro h hR
  have hR0 := hR
  have hll := WbPrimed.cfgRelLogLength hR
  obtain ⟨himg, hdev, ⟨f, hlog⟩, hlen, hags⟩ := hR
  cases h with
  | PFSilent _ ag st' d' hlk hps =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, .PFSilent c' ag' st' d' hlk' (by rw [hst, hdev]; exact hps), ?_⟩
    rw [hpr]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩ hws
  | PFLoad _ ag aq lat base tvs asrc st' d' hlk hps hr =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    have hs := WbPrimed.srcsViewEqX hws asrc
    refine ⟨_, .PFLoad c' ag' aq lat base tvs asrc st' d' hlk' (by rw [hst, hdev]; exact hps)
      (by rw [himg, hlog, retagReadOkD, hs]; exact WbPrimed.readOkDEqX _ _ hws _ _ _ _ _ hr), ?_⟩
    rw [hpr, hs]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr (fun w => loadPostRunD w aq _ base _)
        (fun w => WbPrimed.maskLoadPostRunD w aq _ base _) _ _ hws)
  | PFStore _ ag rl base data asrc vsrc k st' d' hlk hps hnn hk =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    have hs := WbPrimed.srcsViewEqX hws asrc
    have hs2 := WbPrimed.srcsViewEqX hws vsrc
    refine ⟨_, .PFStore c' ag' rl base data asrc vsrc _ st' d' hlk' (by rw [hst, hdev]; exact hps)
      hnn rfl, ?_⟩
    rw [hpr, hs, hs2, hll]
    obtain ⟨g, hg⟩ := WbPrimed.retagSnoc f c.pcLog base data (some i) k
      (pcls ag'.paSt (.LStore rl base data asrc vsrc) ag'.paWs)
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨g, by rw [hlog, hg]⟩
      (WbPrimed.maskCongr (fun w => storePostRunD w rl _ _ base _ _)
        (fun w => WbPrimed.maskStorePostRunD w rl _ _ base _ _) _ _ hws)
  | PFRmw _ ag aq rl base tvs data asrc vsrc k st' d' hlk hps hnn hlen' hr he hk =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    have hs := WbPrimed.srcsViewEqX hws asrc
    have hs2 := WbPrimed.srcsViewEqX hws vsrc
    refine ⟨_, .PFRmw c' ag' aq rl base tvs data asrc vsrc _ st' d' hlk'
      (by rw [hst, hdev]; exact hps) hnn hlen'
      (by rw [himg, hlog, retagReadOk]; exact WbPrimed.readOkDEqX _ _ hws _ _ _ _ _ hr)
      (by rw [hlog, retagExclOk, retagLogLength]; exact he) rfl, ?_⟩
    rw [hpr, hs, hs2, hll]
    obtain ⟨g, hg⟩ := WbPrimed.retagSnoc f c.pcLog base data (some i) k
      (pcls ag'.paSt (.LRmw aq rl base tvs data asrc vsrc) ag'.paWs)
    refine WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨g, by rw [hlog, hg]⟩ ?_
    exact WbPrimed.maskCongr (fun w => storePostRunD w rl _ _ base _ _)
      (fun w => WbPrimed.maskStorePostRunD w rl _ _ base _ _) _ _
      (WbPrimed.maskCongr (fun w => loadPostRunD w aq _ base _)
        (fun w => WbPrimed.maskLoadPostRunD w aq _ base _) _ _ hws)
  | PFFence _ ag pr pw sr sw st' d' hlk hps =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, .PFFence c' ag' pr pw sr sw st' d' hlk' (by rw [hst, hdev]; exact hps), ?_⟩
    rw [hpr]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr (fun w => fencePost w pr pw sr sw)
        (fun w => WbPrimed.maskFencePost w pr pw sr sw) _ _ hws)
  | PFDev _ ag st' d' hlk hps =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, .PFDev c' ag' st' d' hlk' (by rw [hst, hdev]; exact hps), ?_⟩
    rw [hpr]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩ hws
  | PFRegW _ ag rd srcs st' d' hlk hps =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    have hs := WbPrimed.srcsViewEqX hws srcs
    refine ⟨_, .PFRegW c' ag' rd srcs st' d' hlk' (by rw [hst, hdev]; exact hps), ?_⟩
    rw [hpr, hs]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr (fun w => regwPost w rd _) (fun w => WbPrimed.maskRegwPost w rd _) _ _ hws)
  | PFCtrl _ ag srcs st' d' hlk hps =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    have hs := WbPrimed.srcsViewEqX hws srcs
    refine ⟨_, .PFCtrl c' ag' srcs st' d' hlk' (by rw [hst, hdev]; exact hps), ?_⟩
    rw [hpr, hs]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr (fun w => ctrlPost w _) (fun w => WbPrimed.maskCtrlPost w _) _ _ hws)
  | PFInstr _ ag st' d' hlk hps =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, .PFInstr c' ag' st' d' hlk' (by rw [hst, hdev]; exact hps), ?_⟩
    rw [hpr]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr instrPost WbPrimed.maskInstrPost _ _ hws)
  | PFExLoad _ ag aq base tvs asrc st' d' hlk hps hr =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    have hs := WbPrimed.srcsViewEqX hws asrc
    refine ⟨_, .PFExLoad c' ag' aq base tvs asrc st' d' hlk' (by rw [hst, hdev]; exact hps)
      (by rw [himg, hlog, retagReadOk]; exact WbPrimed.readOkDEqX _ _ hws _ _ _ _ _ hr), ?_⟩
    rw [hpr, hs]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr (fun w => exloadPostRunD w aq _ base _)
        (fun w => WbPrimed.maskExloadPostRunD w aq _ base _) _ _ hws)
  | PFExStore _ ag rl base data asrc vsrc k R st' d' hlk hps hnn hres hrb hrlen he hk =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    have hs := WbPrimed.srcsViewEqX hws asrc
    have hs2 := WbPrimed.srcsViewEqX hws vsrc
    refine ⟨_, .PFExStore c' ag' rl base data asrc vsrc _ R st' d' hlk'
      (by rw [hst, hdev]; exact hps) hnn (by rw [WbPrimed.wResEqX hws]; exact hres) hrb hrlen
      (by rw [hlog, retagExclOkTs, retagLogLength]; exact he) rfl, ?_⟩
    rw [hpr, hs, hs2, hll]
    obtain ⟨g, hg⟩ := WbPrimed.retagSnoc f c.pcLog base data (some i) k
      (pcls ag'.paSt (.LExStore rl base data asrc vsrc) ag'.paWs)
    refine WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨g, by rw [hlog, hg]⟩ ?_
    rw [WbPrimed.maskExPost]
    exact WbPrimed.maskCongr (fun w => storePostRunD w rl _ _ base _ _)
      (fun w => WbPrimed.maskStorePostRunD w rl _ _ base _ _) _ _ hws
  | PFIFetch _ ag base tvs st' d' hlk hps hif =>
    obtain ⟨ag', hlk', hst, hpr, hws⟩ := hags i ag hlk
    refine ⟨_, .PFIFetch c' ag' base tvs st' d' hlk' (by rw [hst, hdev]; exact hps)
      (by rw [himg, hlog, retagIfetchOk]; exact hif), ?_⟩
    rw [hpr]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩ hws

end sim


section simB

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)
variable (pwb : P → Bool)

/-- **THE SIMULATION, backward**: every primed step is matched by a registered step at the same
label. -/
theorem WbPrimed.stepBwd (i : Nat) (l : Wlabel) (c c' c1' : Wpcfg P D) :
    WbPrimed.wpPfStepW pstep pcls pwb i l c' c1' → WbPrimed.cfgRel c c' →
    ∃ c1, wpPfStep pstep pcls i l c c1 ∧ WbPrimed.cfgRel c1 c1' := by
  intro h hR
  have hR0 := hR
  have hll := WbPrimed.cfgRelLogLength hR
  have hinv := WbPrimed.cfgRelInv hR
  obtain ⟨himg, hdev, ⟨f, hlog⟩, hlen, hags⟩ := hR
  cases h with
  | PFSilent _ ag' st' d' hlk' hps =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    refine ⟨_, .PFSilent c ag st' d' hlk (by rw [← hst, ← hdev]; exact hps), ?_⟩
    rw [hpr]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩ hws
  | PFLoad _ ag' aq lat base tvs asrc st' d' hlk' hps hr =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    have hs := WbPrimed.srcsViewEqX hws asrc
    refine ⟨_, .PFLoad c ag aq lat base tvs asrc st' d' hlk (by rw [← hst, ← hdev]; exact hps)
      (by
        rw [himg, hlog, retagReadOkD, hs] at hr
        exact WbPrimed.readOkDEqX _ _ hws.symm _ _ _ _ _ hr), ?_⟩
    rw [hpr, hs]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr (fun w => loadPostRunD w aq _ base _)
        (fun w => WbPrimed.maskLoadPostRunD w aq _ base _) _ _ hws)
  | PFStore _ ag' rl base data asrc vsrc k st' d' hlk' hps hnn hk =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    have hs := WbPrimed.srcsViewEqX hws asrc
    have hs2 := WbPrimed.srcsViewEqX hws vsrc
    refine ⟨_, .PFStore c ag rl base data asrc vsrc _ st' d' hlk (by rw [← hst, ← hdev]; exact hps)
      hnn rfl, ?_⟩
    rw [hpr, hs, hs2, hll]
    obtain ⟨g, hg⟩ := WbPrimed.retagSnoc f c.pcLog base data (some i)
      (pcls ag.paSt (.LStore rl base data asrc vsrc) ag.paWs) k
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨g, by rw [hlog, hg]⟩
      (WbPrimed.maskCongr (fun w => storePostRunD w rl _ _ base _ _)
        (fun w => WbPrimed.maskStorePostRunD w rl _ _ base _ _) _ _ hws)
  | PFRmw _ ag' aq rl base tvs data asrc vsrc k st' d' hlk' hps hnn hlen' hr he hk =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    have hs := WbPrimed.srcsViewEqX hws asrc
    have hs2 := WbPrimed.srcsViewEqX hws vsrc
    refine ⟨_, .PFRmw c ag aq rl base tvs data asrc vsrc _ st' d' hlk
      (by rw [← hst, ← hdev]; exact hps) hnn hlen'
      (by
        rw [himg, hlog, retagReadOk] at hr
        exact WbPrimed.readOkDEqX _ _ hws.symm _ _ _ _ _ hr)
      (by rw [hlog, retagExclOk, retagLogLength] at he; exact he) rfl, ?_⟩
    rw [hpr, hs, hs2, hll]
    obtain ⟨g, hg⟩ := WbPrimed.retagSnoc f c.pcLog base data (some i)
      (pcls ag.paSt (.LRmw aq rl base tvs data asrc vsrc) ag.paWs) k
    refine WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨g, by rw [hlog, hg]⟩ ?_
    exact WbPrimed.maskCongr (fun w => storePostRunD w rl _ _ base _ _)
      (fun w => WbPrimed.maskStorePostRunD w rl _ _ base _ _) _ _
      (WbPrimed.maskCongr (fun w => loadPostRunD w aq _ base _)
        (fun w => WbPrimed.maskLoadPostRunD w aq _ base _) _ _ hws)
  | PFFence _ ag' pr pw sr sw st' d' hlk' hps =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    refine ⟨_, .PFFence c ag pr pw sr sw st' d' hlk (by rw [← hst, ← hdev]; exact hps), ?_⟩
    rw [hpr]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr (fun w => fencePost w pr pw sr sw)
        (fun w => WbPrimed.maskFencePost w pr pw sr sw) _ _ hws)
  | PFDev _ ag' st' d' hlk' hps =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    refine ⟨_, .PFDev c ag st' d' hlk (by rw [← hst, ← hdev]; exact hps), ?_⟩
    rw [hpr]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩ hws
  | PFRegW _ ag' rd srcs st' d' hlk' hps =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    have hs := WbPrimed.srcsViewEqX hws srcs
    refine ⟨_, .PFRegW c ag rd srcs st' d' hlk (by rw [← hst, ← hdev]; exact hps), ?_⟩
    rw [hpr, hs]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr (fun w => regwPost w rd _) (fun w => WbPrimed.maskRegwPost w rd _) _ _ hws)
  | PFCtrl _ ag' srcs st' d' hlk' hps =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    have hs := WbPrimed.srcsViewEqX hws srcs
    refine ⟨_, .PFCtrl c ag srcs st' d' hlk (by rw [← hst, ← hdev]; exact hps), ?_⟩
    rw [hpr, hs]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr (fun w => ctrlPost w _) (fun w => WbPrimed.maskCtrlPost w _) _ _ hws)
  | PFInstr _ ag' st' d' hlk' hps =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    refine ⟨_, .PFInstr c ag st' d' hlk (by rw [← hst, ← hdev]; exact hps), ?_⟩
    rw [hpr]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr instrPost WbPrimed.maskInstrPost _ _ hws)
  | PFExLoad _ ag' aq base tvs asrc st' d' hlk' hps hr =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    have hs := WbPrimed.srcsViewEqX hws asrc
    refine ⟨_, .PFExLoad c ag aq base tvs asrc st' d' hlk (by rw [← hst, ← hdev]; exact hps)
      (by
        rw [himg, hlog, retagReadOk] at hr
        exact WbPrimed.readOkDEqX _ _ hws.symm _ _ _ _ _ hr), ?_⟩
    rw [hpr, hs]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩
      (WbPrimed.maskCongr (fun w => exloadPostRunD w aq _ base _)
        (fun w => WbPrimed.maskExloadPostRunD w aq _ base _) _ _ hws)
  | PFExStore _ ag' rl base data asrc vsrc k R st' d' hlk' hps hnn hres hrb hrlen he hk =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    have hs := WbPrimed.srcsViewEqX hws asrc
    have hs2 := WbPrimed.srcsViewEqX hws vsrc
    refine ⟨_, .PFExStore c ag rl base data asrc vsrc _ R st' d' hlk
      (by rw [← hst, ← hdev]; exact hps) hnn (by rw [← WbPrimed.wResEqX hws]; exact hres) hrb hrlen
      (by rw [hlog, retagExclOkTs, retagLogLength] at he; exact he) rfl, ?_⟩
    rw [hpr, hs, hs2, hll]
    obtain ⟨g, hg⟩ := WbPrimed.retagSnoc f c.pcLog base data (some i)
      (pcls ag.paSt (.LExStore rl base data asrc vsrc) ag.paWs) k
    refine WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨g, by rw [hlog, hg]⟩ ?_
    rw [WbPrimed.maskExPost]
    exact WbPrimed.maskCongr (fun w => storePostRunD w rl _ _ base _ _)
      (fun w => WbPrimed.maskStorePostRunD w rl _ _ base _ _) _ _ hws
  | PFIFetch _ ag' base tvs st' d' hlk' hps hif =>
    obtain ⟨ag, hlk, hst, hpr, hws⟩ := hinv i ag' hlk'
    refine ⟨_, .PFIFetch c ag base tvs st' d' hlk (by rw [← hst, ← hdev]; exact hps)
      (by rw [himg, hlog, retagIfetchOk] at hif; exact hif), ?_⟩
    rw [hpr]
    exact WbPrimed.cfgRelSet c c' i st' _ _ _ _ _ d' hR0 ⟨f, hlog⟩ hws

/-- **The run-level simulation, forward.** -/
theorem WbPrimed.runFwd (c c1 c' : Wpcfg P D) :
    rtc (wpPfRun pstep pcls) c c1 → WbPrimed.cfgRel c c' →
    ∃ c1', rtc (WbPrimed.wpPfRunW pstep pcls pwb) c' c1' ∧ WbPrimed.cfgRel c1 c1' := by
  intro h
  induction h generalizing c' with
  | refl => intro hR; exact ⟨c', rtc_refl _, hR⟩
  | tail _ hs ih =>
    intro hR
    obtain ⟨cm', hrun, hRm⟩ := ih c' hR
    obtain ⟨i, l, hst⟩ := hs
    obtain ⟨c1', hst', hR1⟩ := WbPrimed.stepFwd pstep pcls pwb i l _ _ cm' hst hRm
    exact ⟨c1', rtc_r hrun ⟨i, l, hst'⟩, hR1⟩

/-- **The run-level simulation, backward.** -/
theorem WbPrimed.runBwd (c c' c1' : Wpcfg P D) :
    rtc (WbPrimed.wpPfRunW pstep pcls pwb) c' c1' → WbPrimed.cfgRel c c' →
    ∃ c1, rtc (wpPfRun pstep pcls) c c1 ∧ WbPrimed.cfgRel c1 c1' := by
  intro h
  induction h generalizing c with
  | refl => intro hR; exact ⟨c, rtc_refl _, hR⟩
  | tail _ hs ih =>
    intro hR
    obtain ⟨cm, hrun, hRm⟩ := ih c hR
    obtain ⟨i, l, hst⟩ := hs
    obtain ⟨c1, hst', hR1⟩ := WbPrimed.stepBwd pstep pcls pwb i l cm _ _ hst hRm
    exact ⟨c1, rtc_r hrun ⟨i, l, hst'⟩, hR1⟩

end simB

/-! ## 4. The event instance's write-back nodes -/

/-- The announced instruction is of the AMO major opcode (`0101111`: LR, SC, the AMOs,
AMOCAS, SSAMOSWAP) — in Sail the only instructions issuing an EXPLICIT exclusive write
(`STORECON`, `AMO`, `SSAMOSWAP`; `Write_RISCV_conditional*`).  A compressed word never matches
(its low bits are not `11`); `none` (the fetch phase, before the announce) is not one. -/
def WbPrimed.ibAmo (ib : Ibch) : Bool :=
  match ib.ibBits with
  | some w => w.toNat % 128 == 47
  | none => false

/-- **The write-back node** of the event instance: a hart whose announced instruction is not an
AMO-opcode one.  (The primed machine consults it only at an `LExStore` step, i.e. at an exclusive
write, which outside an AMO-opcode instruction is the page walker's `write_pte_conditional`.)
The disk agent has none. -/
def WbPrimed.pwbEv : Pexv6 → Bool
  | .PHart _ _ _ _ ib => !WbPrimed.ibAmo ib
  | .PDisk _ => false

/-- The primed pf step of the event instance. -/
abbrev WbPrimed.pfStepEvW (i : Nat) (l : Wlabel) (c c' : Wpcfg Pexv6 Efab) : Prop :=
  WbPrimed.wpPfStepW pstepEv pclsEv WbPrimed.pwbEv i l c c'

end Weak
