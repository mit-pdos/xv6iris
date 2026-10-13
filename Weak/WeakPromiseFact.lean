/-
Weak: **the front-loading factorization** (M6 W1, slice 2).

Rocq: `iris/WeakPromiseFact.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: the analog of Promising-ARM's Thm 7.1
(`promising_to_promising_pf`, PtoPF.v) for `WeakPromise`'s native full machine:
every run whose state steps are LAT-FREE factors as (all promise steps) ; (only
state steps, against the frozen log), with the SAME final configuration.
Appends happen ONLY in `WPPromise`, so a (state; promise) → (promise; state)
swap keeps every timestamp fixed, and the state step's side conditions survive
the END-EXTENSION of the log because `cfgWf` bounds every view by the OLD log
length.  THE SHAPE: the non-promise rules are repackaged ONCE as the single-
constructor relation `wpAstep i l` (side conditions in `astepOk`, effect a
`Wstate` function `f` and a promise deletion `Dl`), so the four structural
lemmas (shape, log extension, other-agent framing, own-promise-set
augmentation) have one case each.  Part (E): with a shared fabric, state steps
of distinct agents commute UNLESS BOTH TOUCH THE FABRIC; `wpAfree` is the
dev-free fragment and the per-agent decomposition is re-proved over it.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1 (`wp_astep` ↦ `wpAstep` with
   constructor `WPAStep`; `wp_promise_step` ↦ `wpPromiseStep` with `WPPromStep`;
   `wp_afree` ↦ `wpAfree` with `WPAFree`; Prop-valued inductives and
   relations keep a lowerCamel name, like `wpstep`).
2. The section variable `pstep` (and, from part (E) on, `pdev`) is an explicit
   argument of every declaration that uses it, in Rocq's order (Rocq's
   `Global Arguments` make the same choice).
3. Induction over `rtc`: Rocq's head-style `induction … as [|x y z …]` is
   `MachCSL.rtc_ind_l` (or tail induction where the motive does not care).
4. PROOFS of the three commutation lemmas (`wp_afree_astep_comm`,
   `wp_astep_afree_comm`, `wp_afree_comm`) go by inversion of both steps and
   one `List.set_comm`, rather than through `wp_astep_frame` / `list_insert_id`
   rewriting chains; statements unchanged.
5. `lat_free` is written with a wildcard arm for the constructors Rocq lists
   one by one (same truth value per constructor).  `cfg_wf_promise_step`
   keeps `pstep` as an explicit (unused-in-the-statement) argument via
   `include pstep in`, as Rocq's section abstraction gives it.
6. O2 / owner decision D4 (added with the `Weak/WeakInterp.lean` port): the
   label alphabet has the Lean-only `LIFetch base tvs` (`Weak/WeakPromise.lean`
   deviation 8).  `astepOk`'s arm is `ifetchOk img log 0 base tvs ∧ f = id ∧
   Dl = none` (the state-identity arm); `wpAstepWpstep`, `wpstepSplit`,
   `astepOkApp` (via `ifetchOkApp`), `astepOkProm`, `astepOkDel` gain the
   matching case.  `latFree (LIFetch ..)` is `True` (the wildcard arm), so
   Layer 1's lat-free fragment contains fetches.

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakPromise

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## Lat-freedom -/

/-- A state step is LAT-FREE when its label is not a latest-kind load. -/
def latFree (l : Wlabel) : Prop :=
  match l with
  | LLoad _ lat _ _ _ => lat = false
  | _ => True

theorem latFreeRmw (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
    (asrc vsrc : List Dsrc) : latFree (LRmw aq rl base tvs data asrc vsrc) := trivial

theorem latFreeRegw (rd : Nat) (srcs : List Dsrc) : latFree (LRegW rd srcs) := trivial
theorem latFreeCtrl (srcs : List Dsrc) : latFree (LCtrl srcs) := trivial
theorem latFreeInstr : latFree LInstr := trivial

section fact

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)

/-- `Wpcfg`'s eta law (definitional in Lean). -/
theorem wpcfgEta (c : Wpcfg P D) : (⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs⟩ : Wpcfg P D) = c := rfl

/-! ## Splitting `wpstep` into promise steps and state steps -/

/-- The promise step's effect on the promising agent. -/
def promAdd (T : Nat) (ag : Wpagent P) : Wpagent P := ⟨ag.paSt, ag.paWs, {T} ∪ ag.paProm⟩

/-- `WPPromise` alone. -/
inductive wpPromiseStep : Wpcfg P D → Wpcfg P D → Prop
  | WPPromStep (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (base : Int) (data : List (BitVec 8))
      (k : WmClass) :
      cfg.pcAgs[i]? = some ag →
      data ≠ [] →
      wpPromiseStep cfg
        ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], cfg.pcDev,
         cfg.pcAgs.set i (promAdd (cfg.pcLog.length + 1) ag)⟩

/-- A state step deletes at most one timestamp from its own promise set. -/
def promDel (Dl : Option Nat) (pr : GSet Nat) : GSet Nat :=
  match Dl with
  | none => pr
  | some ts => pr \ {ts}

/-- The side conditions of the non-promise rules, collected by label; `f` is the
rule's `Wstate` update and `Dl` its promise deletion, both PINNED by the label. -/
def astepOk (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P) (l : Wlabel)
    (f : Wstate → Wstate) (Dl : Option Nat) : Prop :=
  match l with
  | LSilent => f = id ∧ Dl = none
  | LLoad aq lat base tvs asrc =>
      readOkD img log ag.paWs aq lat base tvs (srcsView ag.paWs asrc) ∧
      f = (fun w => loadPostRunD w aq (srcsView w asrc) base (tvs.map Prod.fst)) ∧
      Dl = none
  | LStore rl base data asrc vsrc =>
      ∃ ts k, ts ∈ ag.paProm ∧
        log[ts - 1]? = some ⟨base, data, some i, k⟩ ∧
        fulfilOkD ag.paWs rl base data.length ts
          (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc)) ∧
        f = (fun w => storePostRunD w rl (srcsView w asrc) (srcsView w vsrc) base data.length ts) ∧
        Dl = some ts
  | LRmw aq rl base tvs data asrc vsrc =>
      ∃ ts k, tvs.length = data.length ∧ ts ∈ ag.paProm ∧
        log[ts - 1]? = some ⟨base, data, some i, k⟩ ∧
        readOk img log ag.paWs aq false base tvs ∧
        exclOk log i base tvs ts ∧
        fulfilOkD (loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))
          rl base data.length ts
          (max (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc))
            (ldvOf ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))) ∧
        f = (fun w => storePostRunD (loadPostRunD w aq (srcsView w asrc) base (tvs.map Prod.fst))
              rl (srcsView w asrc) (srcsView w vsrc) base data.length ts) ∧
        Dl = some ts
  | LFence pr pw sr sw => f = (fun w => fencePost w pr pw sr sw) ∧ Dl = none
  | LDev .. => f = id ∧ Dl = none
  | LRegW rd srcs => f = (fun w => regwPost w rd (srcsView w srcs)) ∧ Dl = none
  | LCtrl srcs => f = (fun w => ctrlPost w (srcsView w srcs)) ∧ Dl = none
  | LInstr => f = instrPost ∧ Dl = none
  | LExLoad aq base tvs asrc =>
      readOk img log ag.paWs aq false base tvs ∧
      f = (fun w => exloadPostRunD w aq (srcsView w asrc) base (tvs.map Prod.fst)) ∧
      Dl = none
  | LExStore rl base data asrc vsrc =>
      ∃ ts k R, ts ∈ ag.paProm ∧
        log[ts - 1]? = some ⟨base, data, some i, k⟩ ∧
        ag.paWs.wRes = some R ∧
        R.rvBase = base ∧ R.rvTs.length = data.length ∧
        exclOkTs log i base R.rvTs ts ∧
        fulfilOkD ag.paWs rl base data.length ts
          (max (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc))
            (max R.rvView
              (if adShapedb img log base R.rvTs data
               then max ag.paWs.wVrOld ag.paWs.wVwOld else 0))) ∧
        f = (fun w => storePostRunD w rl (srcsView w asrc) (srcsView w vsrc) base data.length ts) ∧
        Dl = some ts
  | LIFetch base tvs => ifetchOk img log 0 base tvs ∧ f = id ∧ Dl = none

/-- The non-promise rules of `wpstep`, as ONE relation indexed by the acting
agent and the label. -/
inductive wpAstep (i : Nat) (l : Wlabel) : Wpcfg P D → Wpcfg P D → Prop
  | WPAStep (cfg : Wpcfg P D) (ag : Wpagent P) (st' : P) (d' : D) (f : Wstate → Wstate)
      (Dl : Option Nat) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev l st' d' →
      astepOk cfg.pcImg cfg.pcLog i ag l f Dl →
      wpAstep i l cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', f ag.paWs, promDel Dl ag.paProm⟩⟩

def wpStateStep (c c' : Wpcfg P D) : Prop := ∃ i l, wpAstep pstep i l c c'

def wpLfStep (c c' : Wpcfg P D) : Prop := ∃ i l, latFree l ∧ wpAstep pstep i l c c'

/-- A lat-free run step: promise, or lat-free state step. -/
def wpLfRun (c c' : Wpcfg P D) : Prop := wpPromiseStep c c' ∨ wpLfStep pstep c c'

/-! ## The split is exact -/

theorem wpPromiseStepWpstep (c c' : Wpcfg P D) : wpPromiseStep c c' → wpstep pstep c c' := by
  intro h
  cases h with
  | WPPromStep i ag base data k hlk hnn => exact wpstep.WPPromise c i ag base data k hlk hnn

theorem wpAstepWpstep (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpAstep pstep i l c c' → wpstep pstep c c' := by
  intro h
  cases h with
  | WPAStep ag st' d' f Dl hlk hps hok =>
    cases l with
    | LSilent => obtain ⟨rfl, rfl⟩ := hok; exact wpstep.WPSilent c i ag st' d' hlk hps
    | LLoad aq lat base tvs asrc =>
      obtain ⟨hr, rfl, rfl⟩ := hok; exact wpstep.WPLoad c i ag aq lat base tvs asrc st' d' hlk hps hr
    | LStore rl base data asrc vsrc =>
      obtain ⟨ts, k, h1, h2, h3, rfl, rfl⟩ := hok
      exact wpstep.WPFulfil c i ag rl base data asrc vsrc k ts st' d' hlk hps h1 h2 h3
    | LRmw aq rl base tvs data asrc vsrc =>
      obtain ⟨ts, k, h1, h2, h3, h4, h5, h6, rfl, rfl⟩ := hok
      exact wpstep.WPRmw c i ag aq rl base tvs data asrc vsrc k ts st' d' hlk hps h1 h2 h3 h4 h5 h6
    | LFence pr pw sr sw =>
      obtain ⟨rfl, rfl⟩ := hok; exact wpstep.WPFence c i ag pr pw sr sw st' d' hlk hps
    | LDev => obtain ⟨rfl, rfl⟩ := hok; exact wpstep.WPDev c i ag st' d' hlk hps
    | LRegW rd srcs => obtain ⟨rfl, rfl⟩ := hok; exact wpstep.WPRegW c i ag rd srcs st' d' hlk hps
    | LCtrl srcs => obtain ⟨rfl, rfl⟩ := hok; exact wpstep.WPCtrl c i ag srcs st' d' hlk hps
    | LInstr => obtain ⟨rfl, rfl⟩ := hok; exact wpstep.WPInstr c i ag st' d' hlk hps
    | LExLoad aq base tvs asrc =>
      obtain ⟨hr, rfl, rfl⟩ := hok; exact wpstep.WPExLoad c i ag aq base tvs asrc st' d' hlk hps hr
    | LExStore rl base data asrc vsrc =>
      obtain ⟨ts, k, R, h1, h2, h3, h4, h5, h6, h7, rfl, rfl⟩ := hok
      exact wpstep.WPExStore c i ag rl base data asrc vsrc k ts R st' d' hlk hps h1 h2 h3 h4 h5 h6 h7
    | LIFetch base tvs =>
      obtain ⟨hr, rfl, rfl⟩ := hok; exact wpstep.WPIFetch c i ag base tvs st' d' hlk hps hr

theorem wpStateStepWpstep (c c' : Wpcfg P D) : wpStateStep pstep c c' → wpstep pstep c c' := by
  rintro ⟨i, l, h⟩; exact wpAstepWpstep pstep i l c c' h

theorem wpLfRunWpstep (c c' : Wpcfg P D) : wpLfRun pstep c c' → wpstep pstep c c' := by
  rintro (h | ⟨i, l, _, h⟩)
  · exact wpPromiseStepWpstep pstep c c' h
  · exact wpAstepWpstep pstep i l c c' h

theorem wpLfRunRtcWpstep (c c' : Wpcfg P D) : rtc (wpLfRun pstep) c c' → rtc (wpstep pstep) c c' :=
  rtc_subrel (fun x y h => wpLfRunWpstep pstep x y h)

theorem wpstepSplit (c c' : Wpcfg P D) :
    wpstep pstep c c' → wpPromiseStep c c' ∨ wpStateStep pstep c c' := by
  intro h
  cases h with
  | WPPromise i ag base data k hlk hnn => exact .inl (wpPromiseStep.WPPromStep c i ag base data k hlk hnn)
  | WPSilent i ag st' d' hlk hps =>
    exact .inr ⟨i, LSilent, wpAstep.WPAStep c ag st' d' id none hlk hps ⟨rfl, rfl⟩⟩
  | WPLoad i ag aq lat base tvs asrc st' d' hlk hps hr =>
    exact .inr ⟨i, _, wpAstep.WPAStep c ag st' d'
      (fun w => loadPostRunD w aq (srcsView w asrc) base (tvs.map Prod.fst)) none hlk hps
      ⟨hr, rfl, rfl⟩⟩
  | WPFulfil i ag rl base data asrc vsrc k ts st' d' hlk hps h1 h2 h3 =>
    exact .inr ⟨i, _, wpAstep.WPAStep c ag st' d'
      (fun w => storePostRunD w rl (srcsView w asrc) (srcsView w vsrc) base data.length ts)
      (some ts) hlk hps ⟨ts, k, h1, h2, h3, rfl, rfl⟩⟩
  | WPRmw i ag aq rl base tvs data asrc vsrc k ts st' d' hlk hps h1 h2 h3 h4 h5 h6 =>
    exact .inr ⟨i, _, wpAstep.WPAStep c ag st' d'
      (fun w => storePostRunD (loadPostRunD w aq (srcsView w asrc) base (tvs.map Prod.fst))
        rl (srcsView w asrc) (srcsView w vsrc) base data.length ts)
      (some ts) hlk hps ⟨ts, k, h1, h2, h3, h4, h5, h6, rfl, rfl⟩⟩
  | WPFence i ag pr pw sr sw st' d' hlk hps =>
    exact .inr ⟨i, _, wpAstep.WPAStep c ag st' d' (fun w => fencePost w pr pw sr sw) none hlk hps
      ⟨rfl, rfl⟩⟩
  | WPDev i ag st' d' hlk hps =>
    exact .inr ⟨i, LDev _ _ _ _ _, wpAstep.WPAStep c ag st' d' id none hlk hps ⟨rfl, rfl⟩⟩
  | WPRegW i ag rd srcs st' d' hlk hps =>
    exact .inr ⟨i, _, wpAstep.WPAStep c ag st' d' (fun w => regwPost w rd (srcsView w srcs)) none
      hlk hps ⟨rfl, rfl⟩⟩
  | WPCtrl i ag srcs st' d' hlk hps =>
    exact .inr ⟨i, _, wpAstep.WPAStep c ag st' d' (fun w => ctrlPost w (srcsView w srcs)) none
      hlk hps ⟨rfl, rfl⟩⟩
  | WPInstr i ag st' d' hlk hps =>
    exact .inr ⟨i, LInstr, wpAstep.WPAStep c ag st' d' instrPost none hlk hps ⟨rfl, rfl⟩⟩
  | WPExLoad i ag aq base tvs asrc st' d' hlk hps hr =>
    exact .inr ⟨i, _, wpAstep.WPAStep c ag st' d'
      (fun w => exloadPostRunD w aq (srcsView w asrc) base (tvs.map Prod.fst)) none hlk hps
      ⟨hr, rfl, rfl⟩⟩
  | WPExStore i ag rl base data asrc vsrc k ts R st' d' hlk hps h1 h2 h3 h4 h5 h6 h7 =>
    exact .inr ⟨i, _, wpAstep.WPAStep c ag st' d'
      (fun w => storePostRunD w rl (srcsView w asrc) (srcsView w vsrc) base data.length ts)
      (some ts) hlk hps ⟨ts, k, R, h1, h2, h3, h4, h5, h6, h7, rfl, rfl⟩⟩
  | WPIFetch i ag base tvs st' d' hlk hps hr =>
    exact .inr ⟨i, LIFetch base tvs, wpAstep.WPAStep c ag st' d' id none hlk hps ⟨hr, rfl, rfl⟩⟩

/-- THE LAYER-1 PROGRAM-ALPHABET RESTRICTION: the program never emits a
latest-kind load. -/
def latFreeProg : Prop :=
  ∀ (p : P) (d : D) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc)
    (p' : P) (d' : D), ¬ pstep p d (LLoad aq true base tvs asrc) p' d'

theorem latFreeProgLat (p : P) (d : D) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc) (p' : P) (d' : D) :
    latFreeProg pstep → ¬ pstep p d (LLoad aq true base tvs asrc) p' d' :=
  fun h => h p d aq base tvs asrc p' d'

theorem latFreeProgStep (c c' : Wpcfg P D) :
    latFreeProg pstep → wpstep pstep c c' → wpLfRun pstep c c' := by
  intro hlfp hstep
  rcases wpstepSplit pstep c c' hstep with hpr | ⟨i, l, hs⟩
  · exact .inl hpr
  refine .inr ⟨i, l, ?_, hs⟩
  cases hs with
  | WPAStep ag st' d' f Dl hlk hps hok =>
    cases l with
    | LLoad aq lat base tvs asrc =>
      cases lat with
      | false => rfl
      | true => exact (latFreeProgLat pstep _ _ _ _ _ _ _ _ hlfp hps).elim
    | _ => trivial

theorem latFreeProgRun (c c' : Wpcfg P D) :
    latFreeProg pstep → rtc (wpstep pstep) c c' → rtc (wpLfRun pstep) c c' := fun hlfp =>
  rtc_subrel (fun x y h => latFreeProgStep pstep x y hlfp h)

-- Well-formedness transports to the split relations.  (`pstep` is an explicit
-- argument of `cfgWfPromiseStep`, as in Rocq, although its statement does not mention it.)
include pstep in
theorem cfgWfPromiseStep (c c' : Wpcfg P D) : cfgWf c → wpPromiseStep c c' → cfgWf c' :=
  fun hwf h => cfgWfStep pstep c c' hwf (wpPromiseStepWpstep pstep c c' h)

theorem cfgWfAstep (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    cfgWf c → wpAstep pstep i l c c' → cfgWf c' :=
  fun hwf h => cfgWfStep pstep c c' hwf (wpAstepWpstep pstep i l c c' h)

theorem cfgWfLfRun (c c' : Wpcfg P D) : cfgWf c → wpLfRun pstep c c' → cfgWf c' :=
  fun hwf h => cfgWfStep pstep c c' hwf (wpLfRunWpstep pstep c c' h)

/-! ## The four structural lemmas -/

theorem wpPromiseStepInv (c c' : Wpcfg P D) :
    wpPromiseStep c c' →
    ∃ j agj base data k,
      c.pcAgs[j]? = some agj ∧ data ≠ [] ∧
      c' = ⟨c.pcImg, c.pcLog ++ [⟨base, data, some j, k⟩], c.pcDev,
             c.pcAgs.set j (promAdd (c.pcLog.length + 1) agj)⟩ := by
  intro h
  cases h with
  | WPPromStep i ag base data k hlk hnn => exact ⟨i, ag, base, data, k, hlk, hnn, rfl⟩

/-- (L1) SHAPE. -/
theorem wpAstepShape (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpAstep pstep i l c c' →
    ∃ ag ag', c.pcAgs[i]? = some ag ∧ c'.pcImg = c.pcImg ∧ c'.pcLog = c.pcLog ∧
      c'.pcAgs = c.pcAgs.set i ag' := by
  intro h
  cases h with
  | WPAStep ag st' d' f Dl hlk _ _ => exact ⟨ag, _, hlk, rfl, rfl, rfl⟩

theorem wpAstepLog (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpAstep pstep i l c c' → c'.pcLog = c.pcLog := fun h =>
  (wpAstepShape pstep i l c c' h).choose_spec.choose_spec.2.2.1

/-- Inversion for `wpAstep` in the shape a TRACE wants. -/
theorem wpAstepInv (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpAstep pstep i l c c' →
    ∃ ag st' d' f Dl,
      c.pcAgs[i]? = some ag ∧
      pstep ag.paSt c.pcDev l st' d' ∧
      astepOk c.pcImg c.pcLog i ag l f Dl ∧
      c' = ⟨c.pcImg, c.pcLog, d', c.pcAgs.set i ⟨st', f ag.paWs, promDel Dl ag.paProm⟩⟩ := by
  intro h
  cases h with
  | WPAStep ag st' d' f Dl hlk hps hok => exact ⟨ag, st', d', f, Dl, hlk, hps, hok, rfl⟩

/-- The state phase runs against a FROZEN log. -/
theorem wpStateStepLog (c c' : Wpcfg P D) :
    rtc (wpStateStep pstep) c c' → c'.pcLog = c.pcLog ∧ c'.pcImg = c.pcImg := by
  intro h
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨i, l, hs⟩ := hs
    obtain ⟨_, _, _, hi, hl, _⟩ := wpAstepShape pstep _ _ _ _ hs
    exact ⟨hl.trans ih.1, hi.trans ih.2⟩

/-- (L2, the semantic core) LOG EXTENSION. -/
theorem astepOkApp (img : Image) (log l' : List Wmsg) (i : Nat) (ag : Wpagent P) (lb : Wlabel)
    (f : Wstate → Wstate) (Dl : Option Nat) :
    wsBounded ag.paWs log.length → latFree lb →
    astepOk img log i ag lb f Dl → astepOk img (log ++ l') i ag lb f Dl := by
  intro hb hlf
  cases lb with
  | LSilent => exact id
  | LLoad aq lat base tvs asrc =>
    simp only [latFree] at hlf; subst hlf
    rintro ⟨hr, hf, hdl⟩
    exact ⟨readOkDApp img log l' _ aq base tvs _ hb (srcsViewBounded _ _ _ hb) hr, hf, hdl⟩
  | LStore rl base data asrc vsrc =>
    rintro ⟨ts, k, hin, hlog, hful, hf, hdl⟩
    exact ⟨ts, k, hin, lookup_app_l_Some hlog, hful, hf, hdl⟩
  | LRmw aq rl base tvs data asrc vsrc =>
    rintro ⟨ts, k, hlen, hin, hlog, hr, he, hful, hf, hdl⟩
    have hlt := lookup_lt_Some hlog
    exact ⟨ts, k, hlen, hin, lookup_app_l_Some hlog, readOkApp img log l' _ aq base tvs hb hr,
      exclOkApp log l' i base tvs ts (by omega) he, hful, hf, hdl⟩
  | LFence => exact id
  | LDev => exact id
  | LRegW => exact id
  | LCtrl => exact id
  | LInstr => exact id
  | LExLoad aq base tvs asrc =>
    rintro ⟨hr, hf, hdl⟩
    exact ⟨readOkApp img log l' _ aq base tvs hb hr, hf, hdl⟩
  | LExStore rl base data asrc vsrc =>
    rintro ⟨ts, k, R, hin, hlog, hres, hrb, hrlen, he, hful, hf, hdl⟩
    have hlt := lookup_lt_Some hlog
    have hrb' : ∀ (j t : Nat), R.rvTs[j]? = some t → t ≤ log.length :=
      (wsBoundedRes _ _ hb R hres).1
    refine ⟨ts, k, R, hin, lookup_app_l_Some hlog, hres, hrb, hrlen,
      exclOkTsApp log l' i base R.rvTs ts (by omega) he, ?_, hf, hdl⟩
    rw [adShapedbApp img log l' base R.rvTs data hrb']
    exact hful
  | LIFetch base tvs =>
    rintro ⟨hr, hf, hdl⟩
    exact ⟨ifetchOkApp img log l' 0 base tvs (Nat.zero_le _) hr, hf, hdl⟩

theorem wpAstepApp (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) (m : Wmsg) :
    cfgWf c → latFree l → wpAstep pstep i l c c' →
    wpAstep pstep i l ⟨c.pcImg, c.pcLog ++ [m], c.pcDev, c.pcAgs⟩
      ⟨c.pcImg, c.pcLog ++ [m], c'.pcDev, c'.pcAgs⟩ := by
  intro hwf hlf hs
  cases hs with
  | WPAStep ag st' d' f Dl hlk hps hok =>
    obtain ⟨hb, _⟩ := hwf i ag hlk
    exact wpAstep.WPAStep ⟨c.pcImg, c.pcLog ++ [m], c.pcDev, c.pcAgs⟩ ag st' d' f Dl hlk hps
      (astepOkApp c.pcImg c.pcLog [m] i ag l f Dl hb hlf hok)

/-- (L3) FRAMING. -/
theorem wpAstepFrame (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) (j : Nat) (b : Wpagent P) :
    i ≠ j → wpAstep pstep i l c c' →
    wpAstep pstep i l ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set j b⟩
      ⟨c.pcImg, c.pcLog, c'.pcDev, c'.pcAgs.set j b⟩ := by
  intro hne hs
  cases hs with
  | WPAStep ag st' d' f Dl hlk hps hok =>
    dsimp only
    rw [list_insert_commute (Ne.symm hne)]
    exact wpAstep.WPAStep ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set j b⟩ ag st' d' f Dl
      (by dsimp only; rw [list_lookup_insert_ne (Ne.symm hne)]; exact hlk) hps hok

/-- (L4) OWN PROMISE SET. -/
theorem promDelAdd (T : Nat) (Dl : Option Nat) (pr : GSet Nat) :
    T ∉ pr → (∀ ts, Dl = some ts → ts ∈ pr) → promDel Dl ({T} ∪ pr) = {T} ∪ promDel Dl pr := by
  intro hT hD
  cases Dl with
  | none => rfl
  | some ts =>
    have hts := hD ts rfl
    have hne : ts ≠ T := fun h => hT (h ▸ hts)
    simp only [promDel]
    set_solver

theorem astepOkProm (img : Image) (log : List Wmsg) (i : Nat) (ag ag' : Wpagent P) (l : Wlabel)
    (f : Wstate → Wstate) (Dl : Option Nat) :
    ag'.paWs = ag.paWs → ag.paProm ⊆ ag'.paProm →
    astepOk img log i ag l f Dl → astepOk img log i ag' l f Dl := by
  intro hws hpr
  cases l with
  | LSilent => exact id
  | LLoad => simp only [astepOk, hws]; exact id
  | LStore =>
    simp only [astepOk, hws]
    rintro ⟨ts, k, h1, h2, h3, h4, h5⟩
    exact ⟨ts, k, elemOfWeaken h1 hpr, h2, h3, h4, h5⟩
  | LRmw =>
    simp only [astepOk, hws]
    rintro ⟨ts, k, h0, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨ts, k, h0, elemOfWeaken h1 hpr, h2, h3, h4, h5, h6, h7⟩
  | LFence => exact id
  | LDev => exact id
  | LRegW => exact id
  | LCtrl => exact id
  | LInstr => exact id
  | LExLoad => simp only [astepOk, hws]; exact id
  | LExStore =>
    simp only [astepOk, hws]
    rintro ⟨ts, k, R, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨ts, k, R, elemOfWeaken h1 hpr, h2, h3, h4, h5, h6, h7, h8, h9⟩
  | LIFetch => exact id

theorem astepOkDel (img : Image) (log : List Wmsg) (i : Nat) (ag : Wpagent P) (l : Wlabel)
    (f : Wstate → Wstate) (Dl : Option Nat) (ts : Nat) :
    astepOk img log i ag l f Dl → Dl = some ts → ts ∈ ag.paProm := by
  cases l with
  | LStore =>
    rintro ⟨ts', k, h1, _, _, _, rfl⟩ h
    injection h with h; subst h; exact h1
  | LRmw =>
    rintro ⟨ts', k, _, h1, _, _, _, _, _, rfl⟩ h
    injection h with h; subst h; exact h1
  | LExStore =>
    rintro ⟨ts', k, R, h1, _, _, _, _, _, _, _, rfl⟩ h
    injection h with h; subst h; exact h1
  | LLoad => rintro ⟨_, _, rfl⟩ h; cases h
  | LExLoad => rintro ⟨_, _, rfl⟩ h; cases h
  | LSilent => rintro ⟨_, rfl⟩ h; cases h
  | LFence => rintro ⟨_, rfl⟩ h; cases h
  | LDev => rintro ⟨_, rfl⟩ h; cases h
  | LRegW => rintro ⟨_, rfl⟩ h; cases h
  | LCtrl => rintro ⟨_, rfl⟩ h; cases h
  | LInstr => rintro ⟨_, rfl⟩ h; cases h
  | LIFetch => rintro ⟨_, _, rfl⟩ h; cases h

theorem wpAstepPromAdd (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) (T : Nat) (ag ag' : Wpagent P) :
    c.pcAgs[i]? = some ag →
    c'.pcAgs[i]? = some ag' →
    T ∉ ag.paProm →
    wpAstep pstep i l c c' →
    wpAstep pstep i l ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set i (promAdd T ag)⟩
      ⟨c.pcImg, c.pcLog, c'.pcDev, c.pcAgs.set i (promAdd T ag')⟩ := by
  intro hlk0 hlk1 hT hs
  cases hs with
  | WPAStep ag0 st' d' f Dl hlk hps hok =>
    dsimp only at hlk1 ⊢
    have hlt := lookup_lt_Some hlk
    have hag : ag0 = ag := by rw [hlk] at hlk0; injection hlk0
    subst hag
    rw [list_lookup_insert hlt] at hlk1
    injection hlk1 with hag'
    subst hag'
    have hstep := wpAstep.WPAStep (pstep := pstep) (i := i) (l := l)
      ⟨c.pcImg, c.pcLog, c.pcDev, c.pcAgs.set i (promAdd T ag0)⟩ (promAdd T ag0) st' d' f Dl
      (list_lookup_insert hlt) hps
      (astepOkProm c.pcImg c.pcLog i ag0 (promAdd T ag0) l f Dl rfl unionSubseteqR hok)
    have hpd : promDel Dl ({T} ∪ ag0.paProm) = {T} ∪ promDel Dl ag0.paProm :=
      promDelAdd T Dl _ hT (fun ts h => astepOkDel c.pcImg c.pcLog i ag0 l f Dl ts hok h)
    simp only [promAdd, List.set_set, hpd] at hstep ⊢
    exact hstep

/-! ## (C) THE SWAP LEMMA -/

theorem wpSwap (i : Nat) (l : Wlabel) (c1 c2 c3 : Wpcfg P D) :
    cfgWf c1 → latFree l → wpAstep pstep i l c1 c2 → wpPromiseStep c2 c3 →
    ∃ c2', wpPromiseStep c1 c2' ∧ wpAstep pstep i l c2' c3 := by
  intro hwf hlf hs hp
  obtain ⟨ag, agn, hlk, himg, hlog, hags⟩ := wpAstepShape pstep _ _ _ _ hs
  obtain ⟨j, agj, pb, pd, pk, hlkj, hnn, rfl⟩ := wpPromiseStepInv _ _ hp
  obtain ⟨hb, hpw⟩ := hwf i ag hlk
  have hlt := lookup_lt_Some hlk
  have hT : c1.pcLog.length + 1 ∉ ag.paProm := fun hin => by
    have := (hpw _ hin).2.1; omega
  have hs2 := wpAstepApp pstep i l c1 c2 ⟨pb, pd, some j, pk⟩ hwf hlf hs
  rw [himg, hlog, hags]
  by_cases heq : i = j
  · subst heq
    rw [hags, list_lookup_insert hlt] at hlkj
    injection hlkj with hagj
    subst hagj
    refine ⟨⟨c1.pcImg, c1.pcLog ++ [⟨pb, pd, some i, pk⟩], c1.pcDev,
      c1.pcAgs.set i (promAdd (c1.pcLog.length + 1) ag)⟩,
      wpPromiseStep.WPPromStep c1 i ag pb pd pk hlk hnn, ?_⟩
    rw [List.set_set]
    have hlk2 : (⟨c1.pcImg, c1.pcLog ++ [⟨pb, pd, some i, pk⟩], c2.pcDev, c2.pcAgs⟩ :
        Wpcfg P D).pcAgs[i]? = some agn := by
      dsimp only; rw [hags, list_lookup_insert hlt]
    have hs3 := wpAstepPromAdd pstep i l
      ⟨c1.pcImg, c1.pcLog ++ [⟨pb, pd, some i, pk⟩], c1.pcDev, c1.pcAgs⟩
      ⟨c1.pcImg, c1.pcLog ++ [⟨pb, pd, some i, pk⟩], c2.pcDev, c2.pcAgs⟩
      (c1.pcLog.length + 1) ag agn hlk hlk2 hT hs2
    dsimp only at hs3
    exact hs3
  · rw [hags, list_lookup_insert_ne heq] at hlkj
    refine ⟨⟨c1.pcImg, c1.pcLog ++ [⟨pb, pd, some j, pk⟩], c1.pcDev,
      c1.pcAgs.set j (promAdd (c1.pcLog.length + 1) agj)⟩,
      wpPromiseStep.WPPromStep c1 j agj pb pd pk hlkj hnn, ?_⟩
    have hs3 := wpAstepFrame pstep i l _ _ j (promAdd (c1.pcLog.length + 1) agj) heq hs2
    dsimp only at hs3
    rw [hags] at hs3
    exact hs3

/-! ## (D) THE FACTORIZATION -/

/-- One lat-free state step bubbles to the END of a whole promise phase. -/
theorem wpSwapPromises (c2 c3 : Wpcfg P D) :
    rtc wpPromiseStep c2 c3 →
    ∀ i l c1, cfgWf c1 → latFree l → wpAstep pstep i l c1 c2 →
      ∃ c2', rtc wpPromiseStep c1 c2' ∧ wpAstep pstep i l c2' c3 := by
  intro h
  refine rtc_ind_l (fun c2 => ∀ i l c1, cfgWf c1 → latFree l → wpAstep pstep i l c1 c2 →
    ∃ c2', rtc wpPromiseStep c1 c2' ∧ wpAstep pstep i l c2' c3) c3 ?_ ?_ c2 h
  · intro i l c1 _ _ hs; exact ⟨c1, rtc_refl _, hs⟩
  · intro c2 ca hstep _ ih i l c1 hwf hlf hs
    obtain ⟨d, hpd, hsd⟩ := wpSwap pstep i l c1 c2 ca hwf hlf hs hstep
    obtain ⟨c2', hrun, hfin⟩ := ih i l d (cfgWfPromiseStep pstep _ _ hwf hpd) hlf hsd
    exact ⟨c2', rtc_l hpd hrun, hfin⟩

/-- THE MAIN THEOREM (PARM Thm 7.1's analog). -/
theorem wpFrontLoad (c0 c : Wpcfg P D) :
    cfgWf c0 → rtc (wpLfRun pstep) c0 c →
    ∃ mid, rtc wpPromiseStep c0 mid ∧ rtc (wpLfStep pstep) mid c := by
  intro hwf hrun
  refine rtc_ind_l (fun c0 => cfgWf c0 →
    ∃ mid, rtc wpPromiseStep c0 mid ∧ rtc (wpLfStep pstep) mid c) c ?_ ?_ c0 hrun hwf
  · intro _; exact ⟨c, rtc_refl _, rtc_refl _⟩
  · intro c0 c1 hstep _ ih hwf
    obtain ⟨mid, hprom, hstate⟩ := ih (cfgWfLfRun pstep _ _ hwf hstep)
    rcases hstep with hpr | ⟨i, l, hlf, hs⟩
    · exact ⟨mid, rtc_l hpr hprom, hstate⟩
    · obtain ⟨d, hprom', hsd⟩ := wpSwapPromises pstep _ _ hprom i l c0 hwf hlf hs
      exact ⟨d, hprom', rtc_l ⟨i, l, hlf, hsd⟩ hstate⟩

/-- The same, from a PROGRAM-level hypothesis. -/
theorem wpFrontLoadProg (c0 c : Wpcfg P D) :
    latFreeProg pstep → cfgWf c0 → rtc (wpstep pstep) c0 c →
    ∃ mid, rtc wpPromiseStep c0 mid ∧ rtc (wpLfStep pstep) mid c := fun hlfp hwf hrun =>
  wpFrontLoad pstep c0 c hwf (latFreeProgRun pstep c0 c hlfp hrun)

/-- The behavior-level reading (PARM `Machine.pf_exec`). -/
theorem wpBehaviorFrontLoad (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    rtc (wpLfRun pstep) (wpInit img d0 ps) c → noPromises c →
    ∃ mid,
      rtc wpPromiseStep (wpInit img d0 ps) mid ∧
      rtc (wpLfStep pstep) mid c ∧
      wpBehavior pstep img d0 ps c := by
  intro hrun hnp
  obtain ⟨mid, hprom, hstate⟩ := wpFrontLoad pstep _ _ (cfgWfInit img d0 ps) hrun
  exact ⟨mid, hprom, hstate, wpLfRunRtcWpstep pstep _ _ hrun, hnp⟩

/-- THE HEADLINE: every BEHAVIOR of a lat-free program is a promise phase
followed by a state phase. -/
theorem wpBehaviorFactor (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    latFreeProg pstep → wpBehavior pstep img d0 ps c →
    ∃ mid,
      rtc wpPromiseStep (wpInit img d0 ps) mid ∧ rtc (wpLfStep pstep) mid c ∧ noPromises c := by
  rintro hlfp ⟨hrun, hnp⟩
  obtain ⟨mid, hprom, hstate⟩ := wpFrontLoadProg pstep _ _ hlfp (cfgWfInit img d0 ps) hrun
  exact ⟨mid, hprom, hstate, hnp⟩

/-! ## (E) DEV-FREE STATE STEPS, AND WHAT STILL COMMUTES -/

-- THE FABRIC-TOUCHING MARKER, a parameter of the program alongside `pstep`.
variable (pdev : P → Wlabel → P → Bool)

def pdevOk : Prop :=
  ∀ p d l p' d', pstep p d l p' d' → pdev p l p' = false → d' = d ∧ ∀ d0, pstep p d0 l p' d0

/-- The dev-free fragment of `wpAstep i l`. -/
inductive wpAfree (i : Nat) (l : Wlabel) : Wpcfg P D → Wpcfg P D → Prop
  | WPAFree (cfg : Wpcfg P D) (ag : Wpagent P) (st' : P) (f : Wstate → Wstate) (Dl : Option Nat) :
      cfg.pcAgs[i]? = some ag →
      (∀ d, pstep ag.paSt d l st' d) →
      astepOk cfg.pcImg cfg.pcLog i ag l f Dl →
      wpAfree i l cfg
        ⟨cfg.pcImg, cfg.pcLog, cfg.pcDev, cfg.pcAgs.set i ⟨st', f ag.paWs, promDel Dl ag.paProm⟩⟩

theorem wpAfreeAstep (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpAfree pstep i l c c' → wpAstep pstep i l c c' := by
  intro h
  cases h with
  | WPAFree ag st' f Dl hlk hps hok => exact wpAstep.WPAStep c ag st' c.pcDev f Dl hlk (hps _) hok

theorem wpAfreeDev (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpAfree pstep i l c c' → c'.pcDev = c.pcDev := by
  intro h; cases h; rfl

/-- The MARKER puts a step in the fragment. -/
theorem wpAstepAfree (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    pdevOk pstep pdev → wpAstep pstep i l c c' →
    (∀ ag ag', c.pcAgs[i]? = some ag → c'.pcAgs[i]? = some ag' → pdev ag.paSt l ag'.paSt = false) →
    wpAfree pstep i l c c' := by
  intro hpok hs hm
  cases hs with
  | WPAStep ag st' d' f Dl hlk hps hok =>
    have hlt := lookup_lt_Some hlk
    have hm' : pdev ag.paSt l st' = false :=
      hm ag ⟨st', f ag.paWs, promDel Dl ag.paProm⟩ hlk (list_lookup_insert hlt)
    obtain ⟨rfl, hany⟩ := hpok _ _ _ _ _ hps hm'
    exact wpAfree.WPAFree c ag st' f Dl hlk hany hok

theorem wpAfreeShape (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpAfree pstep i l c c' →
    ∃ ag ag', c.pcAgs[i]? = some ag ∧ c'.pcImg = c.pcImg ∧ c'.pcLog = c.pcLog ∧
      c'.pcDev = c.pcDev ∧ c'.pcAgs = c.pcAgs.set i ag' := by
  intro h
  cases h with
  | WPAFree ag st' f Dl hlk _ _ => exact ⟨ag, _, hlk, rfl, rfl, rfl, rfl⟩

/-- FRAMING for the dev-free fragment (it frames the fabric as well). -/
theorem wpAfreeFrame (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) (j : Nat) (b : Wpagent P) (d : D) :
    i ≠ j → wpAfree pstep i l c c' →
    wpAfree pstep i l ⟨c.pcImg, c.pcLog, d, c.pcAgs.set j b⟩ ⟨c.pcImg, c.pcLog, d, c'.pcAgs.set j b⟩ := by
  intro hne hs
  cases hs with
  | WPAFree ag st' f Dl hlk hps hok =>
    dsimp only
    rw [list_insert_commute (Ne.symm hne)]
    exact wpAfree.WPAFree ⟨c.pcImg, c.pcLog, d, c.pcAgs.set j b⟩ ag st' f Dl
      (by dsimp only; rw [list_lookup_insert_ne (Ne.symm hne)]; exact hlk) hps hok

/-- THE KEY LEMMA, mixed form 1: a dev-free step of `i1` commutes past an
arbitrary state step of `i2 ≠ i1`. -/
theorem wpAfreeAstepComm (i1 : Nat) (l1 : Wlabel) (i2 : Nat) (l2 : Wlabel) (c1 c2 c3 : Wpcfg P D) :
    i1 ≠ i2 → wpAfree pstep i1 l1 c1 c2 → wpAstep pstep i2 l2 c2 c3 →
    ∃ c2', wpAstep pstep i2 l2 c1 c2' ∧ wpAfree pstep i1 l1 c2' c3 := by
  intro hne hs1 hs2
  cases hs1 with
  | WPAFree ag1 st1 f1 Dl1 hlk1 hps1 hok1 =>
    cases hs2 with
    | WPAStep ag2 st2 d2 f2 Dl2 hlk2 hps2 hok2 =>
      dsimp only at hlk2 hps2 hok2 ⊢
      rw [list_lookup_insert_ne hne] at hlk2
      refine ⟨⟨c1.pcImg, c1.pcLog, d2, c1.pcAgs.set i2 ⟨st2, f2 ag2.paWs, promDel Dl2 ag2.paProm⟩⟩,
        wpAstep.WPAStep c1 ag2 st2 d2 f2 Dl2 hlk2 hps2 hok2, ?_⟩
      rw [list_insert_commute (Ne.symm hne)]
      exact wpAfree.WPAFree ⟨c1.pcImg, c1.pcLog, d2,
          c1.pcAgs.set i2 ⟨st2, f2 ag2.paWs, promDel Dl2 ag2.paProm⟩⟩ ag1 st1 f1 Dl1
        (by dsimp only; rw [list_lookup_insert_ne (Ne.symm hne)]; exact hlk1) hps1 hok1

/-- THE KEY LEMMA, mixed form 2. -/
theorem wpAstepAfreeComm (i1 : Nat) (l1 : Wlabel) (i2 : Nat) (l2 : Wlabel) (c1 c2 c3 : Wpcfg P D) :
    i1 ≠ i2 → wpAstep pstep i1 l1 c1 c2 → wpAfree pstep i2 l2 c2 c3 →
    ∃ c2', wpAfree pstep i2 l2 c1 c2' ∧ wpAstep pstep i1 l1 c2' c3 := by
  intro hne hs1 hs2
  cases hs1 with
  | WPAStep ag1 st1 d1 f1 Dl1 hlk1 hps1 hok1 =>
    cases hs2 with
    | WPAFree ag2 st2 f2 Dl2 hlk2 hps2 hok2 =>
      dsimp only at hlk2 hps2 hok2 ⊢
      rw [list_lookup_insert_ne hne] at hlk2
      refine ⟨⟨c1.pcImg, c1.pcLog, c1.pcDev, c1.pcAgs.set i2 ⟨st2, f2 ag2.paWs, promDel Dl2 ag2.paProm⟩⟩,
        wpAfree.WPAFree c1 ag2 st2 f2 Dl2 hlk2 hps2 hok2, ?_⟩
      rw [list_insert_commute (Ne.symm hne)]
      exact wpAstep.WPAStep ⟨c1.pcImg, c1.pcLog, c1.pcDev,
          c1.pcAgs.set i2 ⟨st2, f2 ag2.paWs, promDel Dl2 ag2.paProm⟩⟩ ag1 st1 d1 f1 Dl1
        (by dsimp only; rw [list_lookup_insert_ne (Ne.symm hne)]; exact hlk1) hps1 hok1

/-- THE KEY LEMMA, packaged: distinct agents, at least one step dev-free. -/
theorem wpAstepComm (i1 : Nat) (l1 : Wlabel) (i2 : Nat) (l2 : Wlabel) (c1 c2 c3 : Wpcfg P D) :
    i1 ≠ i2 → wpAstep pstep i1 l1 c1 c2 → wpAstep pstep i2 l2 c2 c3 →
    wpAfree pstep i1 l1 c1 c2 ∨ wpAfree pstep i2 l2 c2 c3 →
    ∃ c2', wpAstep pstep i2 l2 c1 c2' ∧ wpAstep pstep i1 l1 c2' c3 := by
  intro hne hs1 hs2 hfr
  rcases hfr with hfr | hfr
  · obtain ⟨d, h1, h2⟩ := wpAfreeAstepComm pstep i1 l1 i2 l2 c1 c2 c3 hne hfr hs2
    exact ⟨d, h1, wpAfreeAstep pstep _ _ _ _ h2⟩
  · obtain ⟨d, h1, h2⟩ := wpAstepAfreeComm pstep i1 l1 i2 l2 c1 c2 c3 hne hs1 hfr
    exact ⟨d, wpAfreeAstep pstep _ _ _ _ h1, h2⟩

/-- Both dev-free: the fragment is closed under the swap. -/
theorem wpAfreeComm (i1 : Nat) (l1 : Wlabel) (i2 : Nat) (l2 : Wlabel) (c1 c2 c3 : Wpcfg P D) :
    i1 ≠ i2 → wpAfree pstep i1 l1 c1 c2 → wpAfree pstep i2 l2 c2 c3 →
    ∃ c2', wpAfree pstep i2 l2 c1 c2' ∧ wpAfree pstep i1 l1 c2' c3 := by
  intro hne hs1 hs2
  cases hs1 with
  | WPAFree ag1 st1 f1 Dl1 hlk1 hps1 hok1 =>
    cases hs2 with
    | WPAFree ag2 st2 f2 Dl2 hlk2 hps2 hok2 =>
      dsimp only at hlk2 hps2 hok2 ⊢
      rw [list_lookup_insert_ne hne] at hlk2
      refine ⟨⟨c1.pcImg, c1.pcLog, c1.pcDev, c1.pcAgs.set i2 ⟨st2, f2 ag2.paWs, promDel Dl2 ag2.paProm⟩⟩,
        wpAfree.WPAFree c1 ag2 st2 f2 Dl2 hlk2 hps2 hok2, ?_⟩
      rw [list_insert_commute (Ne.symm hne)]
      exact wpAfree.WPAFree ⟨c1.pcImg, c1.pcLog, c1.pcDev,
          c1.pcAgs.set i2 ⟨st2, f2 ag2.paWs, promDel Dl2 ag2.paProm⟩⟩ ag1 st1 f1 Dl1
        (by dsimp only; rw [list_lookup_insert_ne (Ne.symm hne)]; exact hlk1) hps1 hok1

/-- One agent's steps, and the steps of a SET of agents (general fragment). -/
def wpAstepOf (i : Nat) (c c' : Wpcfg P D) : Prop := ∃ l, wpAstep pstep i l c c'

/-- The frozen-log / framing facts of a whole phase. -/
theorem astepOfRtcFrozen (i : Nat) (c c' : Wpcfg P D) :
    rtc (wpAstepOf pstep i) c c' →
    c'.pcLog = c.pcLog ∧ c'.pcImg = c.pcImg ∧ c'.pcAgs.length = c.pcAgs.length ∧
    (∀ j, j ≠ i → c'.pcAgs[j]? = c.pcAgs[j]?) := by
  intro h
  induction h with
  | refl => exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  | tail _ hs ih =>
    obtain ⟨l, hs⟩ := hs
    obtain ⟨_, _, _, hi, hl, ha⟩ := wpAstepShape pstep _ _ _ _ hs
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨hl.trans h1, hi.trans h2, by rw [ha, List.length_set, h3], fun j hj => ?_⟩
    rw [ha, list_lookup_insert_ne (Ne.symm hj), h4 j hj]

def wpAstepsOf (Q : Nat → Prop) (c c' : Wpcfg P D) : Prop := ∃ i l, Q i ∧ wpAstep pstep i l c c'

def wpAstepOther (i : Nat) (c c' : Wpcfg P D) : Prop := wpAstepsOf pstep (fun j => j ≠ i) c c'

theorem wpAstepsOfMono (Q Q' : Nat → Prop) (c c' : Wpcfg P D) :
    (∀ i, Q i → Q' i) → rtc (wpAstepsOf pstep Q) c c' → rtc (wpAstepsOf pstep Q') c c' := by
  intro hQ
  exact rtc_subrel (fun x y ⟨i, l, hq, hs⟩ => ⟨i, l, hQ i hq, hs⟩)

/-- Every state step is taken by an agent that EXISTS in the list. -/
theorem wpAstepLt (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpAstep pstep i l c c' → i < c.pcAgs.length := by
  intro h
  obtain ⟨_, _, hlk, _⟩ := wpAstepShape pstep _ _ _ _ h
  exact lookup_lt_Some hlk

theorem wpAstepAgsLength (i : Nat) (l : Wlabel) (c c' : Wpcfg P D) :
    wpAstep pstep i l c c' → c'.pcAgs.length = c.pcAgs.length := by
  intro h
  obtain ⟨_, _, _, _, _, ha⟩ := wpAstepShape pstep _ _ _ _ h
  rw [ha, List.length_set]

theorem wpStateStepAgents (c c' : Wpcfg P D) :
    rtc (wpStateStep pstep) c c' →
    rtc (wpAstepsOf pstep (fun i => i < c.pcAgs.length)) c c' := by
  intro h
  refine rtc_ind_l (fun c => rtc (wpAstepsOf pstep (fun i => i < c.pcAgs.length)) c c') c'
    (rtc_refl _) ?_ c h
  intro x y hxy _ ih
  obtain ⟨i, l, hs⟩ := hxy
  refine rtc_l ⟨i, l, wpAstepLt pstep _ _ _ _ hs, hs⟩ ?_
  refine wpAstepsOfMono pstep _ _ _ _ (fun k hk => ?_) ih
  rw [wpAstepAgsLength pstep _ _ _ _ hs] at hk
  exact hk

/-! ## (E') The DEV-FREE phase decomposes per agent -/

def wpAfreeOf (i : Nat) (c c' : Wpcfg P D) : Prop := ∃ l, wpAfree pstep i l c c'

def wpAfreesOf (Q : Nat → Prop) (c c' : Wpcfg P D) : Prop := ∃ i l, Q i ∧ wpAfree pstep i l c c'

def wpFreeStep (c c' : Wpcfg P D) : Prop := ∃ i l, wpAfree pstep i l c c'

def wpAfreeOther (i : Nat) (c c' : Wpcfg P D) : Prop := wpAfreesOf pstep (fun j => j ≠ i) c c'

theorem wpAfreeOfAstepOf (i : Nat) (c c' : Wpcfg P D) :
    rtc (wpAfreeOf pstep i) c c' → rtc (wpAstepOf pstep i) c c' :=
  rtc_subrel (fun x y ⟨l, hs⟩ => ⟨l, wpAfreeAstep pstep _ _ _ _ hs⟩)

theorem wpFreeStepStateStep (c c' : Wpcfg P D) :
    rtc (wpFreeStep pstep) c c' → rtc (wpStateStep pstep) c c' :=
  rtc_subrel (fun x y ⟨i, l, hs⟩ => ⟨i, l, wpAfreeAstep pstep _ _ _ _ hs⟩)

theorem wpAfreesOfMono (Q Q' : Nat → Prop) (c c' : Wpcfg P D) :
    (∀ i, Q i → Q' i) → rtc (wpAfreesOf pstep Q) c c' → rtc (wpAfreesOf pstep Q') c c' := by
  intro hQ
  exact rtc_subrel (fun x y ⟨i, l, hq, hs⟩ => ⟨i, l, hQ i hq, hs⟩)

theorem wpFreeStepAgents (c c' : Wpcfg P D) :
    rtc (wpFreeStep pstep) c c' →
    rtc (wpAfreesOf pstep (fun i => i < c.pcAgs.length)) c c' := by
  intro h
  refine rtc_ind_l (fun c => rtc (wpAfreesOf pstep (fun i => i < c.pcAgs.length)) c c') c'
    (rtc_refl _) ?_ c h
  intro x y hxy _ ih
  obtain ⟨i, l, hs⟩ := hxy
  refine rtc_l ⟨i, l, wpAstepLt pstep _ _ _ _ (wpAfreeAstep pstep _ _ _ _ hs), hs⟩ ?_
  refine wpAfreesOfMono pstep _ _ _ _ (fun k hk => ?_) ih
  rw [wpAstepAgsLength pstep _ _ _ _ (wpAfreeAstep pstep _ _ _ _ hs)] at hk
  exact hk

theorem wpAstepCommRtc (i : Nat) (c2 c3 : Wpcfg P D) :
    rtc (wpAfreeOf pstep i) c2 c3 →
    ∀ j l c1, j ≠ i → wpAfree pstep j l c1 c2 →
      ∃ c2', rtc (wpAfreeOf pstep i) c1 c2' ∧ wpAfree pstep j l c2' c3 := by
  intro h
  refine rtc_ind_l (fun c2 => ∀ j l c1, j ≠ i → wpAfree pstep j l c1 c2 →
    ∃ c2', rtc (wpAfreeOf pstep i) c1 c2' ∧ wpAfree pstep j l c2' c3) c3 ?_ ?_ c2 h
  · intro j l c1 _ hs; exact ⟨c1, rtc_refl _, hs⟩
  · intro c2 ca hstep _ ih j l c1 hne hs
    obtain ⟨l2, hstep⟩ := hstep
    obtain ⟨d, hid, hjd⟩ := wpAfreeComm pstep j l i l2 c1 c2 ca hne hs hstep
    obtain ⟨c2', hrun, hfin⟩ := ih j l d hne hjd
    exact ⟨c2', rtc_l ⟨l2, hid⟩ hrun, hfin⟩

/-- The per-agent EXTRACTION. -/
theorem wpProjectOf (Q : Nat → Prop) (i : Nat) (c c' : Wpcfg P D) :
    rtc (wpAfreesOf pstep Q) c c' →
    ∃ mid, rtc (wpAfreeOf pstep i) c mid ∧ rtc (wpAfreesOf pstep (fun j => Q j ∧ j ≠ i)) mid c' := by
  intro h
  refine rtc_ind_l (fun c => ∃ mid, rtc (wpAfreeOf pstep i) c mid ∧
    rtc (wpAfreesOf pstep (fun j => Q j ∧ j ≠ i)) mid c') c' ⟨c', rtc_refl _, rtc_refl _⟩ ?_ c h
  intro c ca hstep _ ih
  obtain ⟨k, l, hq, hstep⟩ := hstep
  obtain ⟨mid, hi, hoth⟩ := ih
  by_cases hk : k = i
  · subst hk; exact ⟨mid, rtc_l ⟨l, hstep⟩ hi, hoth⟩
  · obtain ⟨d, hid, hkd⟩ := wpAstepCommRtc pstep i _ _ hi k l c hk hstep
    exact ⟨d, hid, rtc_l ⟨k, l, ⟨hq, hk⟩, hkd⟩ hoth⟩

theorem wpStateProject (i : Nat) (c c' : Wpcfg P D) :
    rtc (wpFreeStep pstep) c c' →
    ∃ mid, rtc (wpAfreeOf pstep i) c mid ∧ rtc (wpAfreeOther pstep i) mid c' := by
  intro hrun
  obtain ⟨mid, hi, hoth⟩ := wpProjectOf pstep (fun _ => True) i c c'
    (wpAfreesOfMono pstep _ _ _ _ (fun _ _ => trivial) (wpFreeStepAgents pstep c c' hrun))
  exact ⟨mid, hi, wpAfreesOfMono pstep _ _ _ _ (fun _ h => h.2) hoth⟩

/-- The per-agent DECOMPOSITION (PARM's `Machine.state_exec`). -/
def wpPhases : List Nat → Wpcfg P D → Wpcfg P D → Prop
  | [], c, c' => c = c'
  | i :: js', c, c' => ∃ mid, rtc (wpAfreeOf pstep i) c mid ∧ wpPhases js' mid c'

theorem wpAstepsOfNone (Q : Nat → Prop) (c c' : Wpcfg P D) :
    (∀ i, ¬ Q i) → rtc (wpAfreesOf pstep Q) c c' → c = c' := by
  intro hQ h
  cases h with
  | refl => rfl
  | tail _ hs => obtain ⟨i, _, hq, _⟩ := hs; exact (hQ i hq).elim

theorem wpStateGroup (js : List Nat) :
    ∀ Q c c', (∀ i, Q i → i ∈ js) → rtc (wpAfreesOf pstep Q) c c' → wpPhases pstep js c c' := by
  induction js with
  | nil =>
    intro Q c c' hcov hrun
    exact wpAstepsOfNone pstep Q c c' (fun k hk => by have := hcov k hk; simp at this) hrun
  | cons i js' ih =>
    intro Q c c' hcov hrun
    obtain ⟨mid, hi, hoth⟩ := wpProjectOf pstep Q i c c' hrun
    refine ⟨mid, hi, ih _ mid c' (fun k ⟨hq, hne⟩ => ?_) hoth⟩
    rcases List.mem_cons.1 (hcov k hq) with hki | hin
    · exact (hne hki).elim
    · exact hin

/-- THE DEV-FREE-PHASE FORM (the `Machine.state_exec` analog). -/
theorem wpStateExec (c c' : Wpcfg P D) :
    rtc (wpFreeStep pstep) c c' → wpPhases pstep (List.range' 0 c.pcAgs.length) c c' := by
  intro hrun
  exact wpStateGroup pstep _ (fun i => i < c.pcAgs.length) c c'
    (fun k hk => List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩) (wpFreeStepAgents pstep c c' hrun)

end fact

end Weak
