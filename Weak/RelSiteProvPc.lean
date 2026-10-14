/-
Weak: **W11-C2′ (a2) [OWN.82] — the issuing pc of every pf log message, carried by W4's
lock-step** (plan rev 52 §D Q-WCREL-2, route (a); the interface `Weak/RelSiteProv.lean`).

Independent of the (b) choice (Q-C2P-B2): nothing here reads a store's view effect.

* **The pf-side issuing-pc log** `RelSiteProvPc.recPcLog r` of a W4 run record `r`
  (`MachOfPf.PfRec`): one entry per log message, in log order — the PC of the appending agent's
  register file at the appending step (`pcOfSt`; the disk agent, which has no pc, gets `-1`,
  never a release pc).  `RelSiteProvPc.contRLog`: along a record the log grows by exactly the
  appending steps' messages, each stamped `pclsEv` at its pre-state.
* **(a3)'s step obligation** `RelSiteProvPc.relStepWCrel r`: every recorded appending step whose
  agent's pc is a release pc is stamped `.WCrel`.  `RelSiteProvPc.relPcWCrelOfSteps`: from the
  initial (empty-log) configuration it gives `RelSiteProv.relPcWCrel cN.pcLog (recPcLog r)` —
  i.e. (a3) is now a statement about ONE pf step at a time.
* **(a2) the lock-step** `RelSiteProvPc.simRelPc`: at every `SimRel`-related pair, each pf hart's
  pc IS the MachCSL hart's `PC` (W4's register-file equality); `RelSiteProvPc.simRunAt`: every
  recorded step of a run W4 simulates has a REACHABLE MachCSL configuration related to its
  pre-configuration; `RelSiteProvPc.recPcLockstep` composes them: the issuing pc this file
  records for a hart's store IS the `PC` the MachCSL hart has where W4 simulates that store — the
  pc a MachCSL provenance ghost ((a1), `RelSiteProv.relProvExport`) records at that store event
  (one MachCSL store per pf append, in order: `rmem`'s `R-log` keeps `σ.log` and the pf log the
  same length).

Lean-only (no Rocq counterpart); every name is file-qualified (`RelSiteProvPc.*`).
-/
import Weak.MachOfPf
import Weak.RelSiteProv

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open MachOfPf
open Wlabel

namespace RelSiteProvPc

/-! ## 1. The issuing-pc log of a run record -/

/-- The labels whose `wpPfStep` arm appends a log message. -/
def lbAppends : Wlabel → Bool
  | .LStore .. | .LRmw .. | .LExStore .. => true
  | _ => false

/-- The issuing pc of a program state: a hart's `PC`; the disk agent has none (`-1`). -/
def pcOfSt : Pexv6 → Int
  | .PHart _ _ rs _ _ => ((rs .PC).toNat : Int)
  | .PDisk _ => -1

/-- The pc of a recorded step, if it appends a message. -/
def recPc (x : PfRec) : Option Int :=
  if lbAppends x.lb then some ((x.pre.pcAgs[x.ag]?).elim (-1) (fun ag => pcOfSt ag.paSt))
  else none

/-- **The issuing-pc log**: one entry per appended message, in log order. -/
def recPcLog (r : List PfRec) : List Int := r.filterMap recPc

theorem recPcLogCons (x : PfRec) (r : List PfRec) :
    recPcLog (x :: r) = (match recPc x with | some p => p :: recPcLog r | none => recPcLog r) := by
  simp only [recPcLog, List.filterMap_cons]
  cases recPc x <;> rfl

/-- A promise-free step's log effect: an appending label appends ONE message, authored by the
agent and stamped by `pcls` at the agent's pre-state; any other label leaves the log alone. -/
theorem stepLog {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (i : Nat) (l : Wlabel) (c c' : Wpcfg P D)
    (h : wpPfStep pstep pcls i l c c') :
    (lbAppends l = false → c'.pcLog = c.pcLog) ∧
    (lbAppends l = true → ∃ (ag : Wpagent P) (m : Wmsg), c.pcAgs[i]? = some ag ∧
      c'.pcLog = c.pcLog ++ [m] ∧ m.wmAk = pcls ag.paSt l ag.paWs) := by
  cases h with
  | PFStore _ ag _ _ _ _ _ k _ _ hlk _ _ hk =>
    exact ⟨(fun h => by cases h), fun _ => ⟨ag, _, hlk, rfl, hk⟩⟩
  | PFRmw _ ag _ _ _ _ _ _ _ k _ _ hlk _ _ _ _ _ hk =>
    exact ⟨(fun h => by cases h), fun _ => ⟨ag, _, hlk, rfl, hk⟩⟩
  | PFExStore _ ag _ _ _ _ _ k _ _ _ hlk _ _ _ _ _ _ hk =>
    exact ⟨(fun h => by cases h), fun _ => ⟨ag, _, hlk, rfl, hk⟩⟩
  | PFSilent => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFLoad => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFFence => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFDev => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFRegW => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFCtrl => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFInstr => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFExLoad => exact ⟨fun _ => rfl, fun h => by cases h⟩
  | PFIFetch => exact ⟨fun _ => rfl, fun h => by cases h⟩

/-- Along a record the log only grows. -/
theorem contRPrefix {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : contRC fok fcutT c st r cN) : c.pcLog <+: cN.pcLog := by
  induction h with
  | nil => exact List.prefix_refl _
  | cons c c' st i l k r cN hs _ _ _ _ _ ih =>
    refine List.IsPrefix.trans ?_ ih
    obtain ⟨h0, h1⟩ := stepLog _ _ _ _ _ _ hs
    cases ha : lbAppends l
    · rw [h0 ha]; exact List.prefix_refl _
    · obtain ⟨_, m, _, he, _⟩ := h1 ha
      rw [he]; exact List.prefix_append _ _

/-- **The log of a record** (length): exactly one message per entry of the issuing-pc log. -/
theorem contRLogLength {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : contRC fok fcutT c st r cN) : cN.pcLog.length = c.pcLog.length + (recPcLog r).length := by
  induction h with
  | nil => simp [recPcLog]
  | cons c c' st i l k r cN hs _ _ _ _ _ ih =>
    rw [ih, recPcLogCons]
    obtain ⟨h0, h1⟩ := stepLog _ _ _ _ _ _ hs
    cases ha : lbAppends l
    · rw [h0 ha]; simp [recPc, ha]
    · obtain ⟨_, m, _, he, _⟩ := h1 ha
      rw [he]; simp [recPc, ha]; omega

/-! ## 2. (a3) as a per-step obligation -/

/-- **(a3)'s STEP OBLIGATION**: every recorded appending step whose agent's issuing pc is a
release pc is stamped `.WCrel` by the instance's class function at its pre-state. -/
def relStepWCrel (r : List PfRec) : Prop :=
  ∀ x, x ∈ r → lbAppends x.lb = true → ∀ ag, x.pre.pcAgs[x.ag]? = some ag →
    pcOfSt ag.paSt ∈ releasePcs → pclsEv ag.paSt x.lb ag.paWs = .WCrel

theorem negOneNotRelease : (-1 : Int) ∉ releasePcs := by
  simp [releasePcs]
  omega

/-- The obligation, at an offset: message `c.pcLog.length + q` of `cN` and entry `q` of the
issuing-pc log. -/
theorem relPcWCrelOff {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : contRC fok fcutT c st r cN) (hob : relStepWCrel r) :
    ∀ (q : Nat) (mq : Wmsg) (pc : Int), cN.pcLog[c.pcLog.length + q]? = some mq →
      (recPcLog r)[q]? = some pc → pc ∈ releasePcs → mq.wmAk = .WCrel := by
  induction h with
  | nil => intro q mq pc _ hp; simp [recPcLog] at hp
  | cons c c' st i l k r cN hs _ _ _ _ hr ih =>
    intro q mq pc hm hp hrel
    have hob' : relStepWCrel r := fun x hx => hob x (List.mem_cons_of_mem _ hx)
    obtain ⟨h0, h1⟩ := stepLog _ _ _ _ _ _ hs
    rw [recPcLogCons] at hp
    cases ha : lbAppends l
    · have hp' : (recPcLog r)[q]? = some pc := by simpa [recPc, ha] using hp
      exact ih hob' q mq pc (by rw [h0 ha]; exact hm) hp' hrel
    · obtain ⟨ag, m, hlk, he, hk⟩ := h1 ha
      have hpre := contRPrefix hr
      cases q with
      | zero =>
        have hpc : pc = (c.pcAgs[i]?).elim (-1) (fun ag => pcOfSt ag.paSt) := by
          simpa [recPc, ha] using hp.symm
        rw [hlk] at hpc
        simp only [Option.elim] at hpc
        have hm' : cN.pcLog[c.pcLog.length]? = some m := by
          rw [he] at hpre
          obtain ⟨tl, htl⟩ := hpre
          rw [← htl]
          simp
        rw [Nat.add_zero, hm'] at hm
        cases hm
        rw [hk]
        exact hob ⟨c, i, l, k⟩ (List.mem_cons_self) ha ag hlk (hpc ▸ hrel)
      | succ q =>
        have hp' : (recPcLog r)[q]? = some pc := by simpa [recPc, ha] using hp
        have hlen : c'.pcLog.length = c.pcLog.length + 1 := by rw [he]; simp
        exact ih hob' q mq pc (by rw [hlen, Nat.add_right_comm]; exact hm) hp' hrel

/-- **(a3) reduced to single steps**: from an empty log, the step obligation gives the pf half of
the interface, `RelSiteProv.relPcWCrel`, at the issuing-pc log. -/
theorem relPcWCrelOfSteps {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab}
    (h : contRC fok fcutT c st r cN) (h0 : c.pcLog = []) (hob : relStepWCrel r) :
    RelSiteProv.relPcWCrel cN.pcLog (recPcLog r) := by
  intro q mq pc hm hp hrel
  exact relPcWCrelOff h hob q mq pc (by rw [h0]; simpa using hm) hp hrel

/-! ## 3. (a2): W4's lock-step carries the pc -/

/-- **The lock-step, at one related pair**: each pf hart's issuing pc IS the MachCSL hart's `PC`
(`SimRel`'s register files are EQUAL). -/
theorem simRelPc {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {t : List Expr} {g : GState}
    (hR : SimRel c st t g) (cpu : CPU) :
    ∃ ag, c.pcAgs[cpu.val]? = some ag ∧ pcOfSt ag.paSt = (((g.m.regs cpu) .PC).toNat : Int) := by
  obtain ⟨-, -, ⟨H, vs, dp, dws, dpr, -, -, hharts, -, -⟩, -, -, -, -⟩ := hR
  obtain ⟨fn, ib, ws, pr, hlk, -⟩ := hharts cpu
  exact ⟨_, hlk, rfl⟩

/-- **Every recorded step is simulated from a reachable related configuration** (`simRun`'s
induction, keeping each intermediate pair). -/
theorem simRunAt {fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    {g0 : GState} {c0 : Wpcfg Pexv6 Efab} (hH : HypsC fok fcutT g0 c0) :
    ∀ {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {r : List PfRec} {cN : Wpcfg Pexv6 Efab},
      contRC fok fcutT c st r cN →
      ∀ {t : List Expr} {g : GState} {n : Nat} {κ : List Obs},
        SimRel c st t g → MRun n ([Expr.power], g0) κ (t, g) →
        pfRunST pstepEv pclsEv fok TsoShadow.cohSrc c0 st c → pairAdjacent (st ++ recLabels r) →
        ∀ x, x ∈ r → ∃ (st' : List (Nat × Wlabel)) (n' : Nat) (κ' : List Obs) (t' : List Expr)
          (g' : GState), MRun n' ([Expr.power], g0) κ' (t', g') ∧ SimRel x.pre st' t' g' := by
  intro c st r cN h
  induction h with
  | nil => intro _ _ _ _ _ _ _ _ x hx; cases hx
  | cons c c' st i l k r cN hs hf hfT hcf hk hr ih =>
    intro t g n κ hR hreach hrun hadj x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨st, n, κ, t, g, hreach, hR⟩
    · have hadj' : pairAdjacent (st ++ (i, l) :: recLabels r) := by
        simpa [recLabels] using hadj
      obtain ⟨m1, t1, g1, -, hm1, hR1⟩ := simStep hH hR hreach hrun hs hf hfT hcf hk hadj'
        (fun aq base tvs asrc hl => by subst hl; exact exclAhead fok hs hr hadj')
      exact ih hR1 (mrunTrans hreach hm1) (pfRunST.snoc c c' st i l hrun hs hf hfT)
        (by simpa using hadj') x hx

/-- **(a2), composed**: in every run W4 simulates from boot, each recorded store of hart `cpu`
has a reachable MachCSL configuration, related to the store's pre-configuration, whose hart
`cpu` has `PC` equal to the store's entry in the issuing-pc log. -/
theorem recPcLockstep (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
    {fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop}
    (σ0 : WGState) (ds : DevStates) (g0 : GState)
    (hb : wbootFacts σ0) (hds : σ0.wgdev = ds.reset) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hgd : g0.m.devs = ds)
    (hH : HypsC fok fcutT g0 (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)))
    (r : List PfRec) (cN : Wpcfg Pexv6 Efab)
    (hr : contRC fok fcutT (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) [] r cN)
    (hadj : pairAdjacent (recLabels r)) :
    ∀ x, x ∈ r → ∀ (cpu : CPU), x.ag = cpu.val → lbAppends x.lb = true →
      ∃ (st' : List (Nat × Wlabel)) (n' : Nat) (κ' : List Obs) (t' : List Expr) (g' : GState),
        MRun n' ([Expr.power], g0) κ' (t', g') ∧ SimRel x.pre st' t' g' ∧
        recPc x = some (((g'.m.regs cpu) .PC).toNat : Int) := by
  intro x hx cpu hag ha
  have hboot := powerOnRun g0 σ0 ds hb hg0 hp0 hgd
  have hR0 := simRelBoot σ0 ds hb hds
  obtain ⟨st', n', κ', t', g', hm, hR⟩ :=
    simRunAt hH hr hR0 hboot pfRunST.nil (by simpa using hadj) x hx
  obtain ⟨ag, hlk, hpc⟩ := simRelPc hR cpu
  refine ⟨st', n', κ', t', g', hm, hR, ?_⟩
  simp only [recPc, ha, if_true, hag, hlk, Option.elim, hpc]

end RelSiteProvPc

end Weak
