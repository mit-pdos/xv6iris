/-
Weak/Prom: **E-c — an EXPERIMENTAL machine variant: machine v2 plus a minimal A/D arm** (G4 deciding experiment
E-c, owner ruling [OWN.P13]; G4-review2.md §6 B-1′, §7; plan rev 7 M20).  Machine.lean is NOT changed; translation
stays off in the mainline.  This variant exists to test whether track (b)'s reordering lemma survives the A/D arm.

## The arm (plan M20 (2), (3), (5); quotes supervisor.adoc @ e17d92a1, ~/dev/weak-orch/promising/spec/)

* supervisor.adoc:1622–1624 "The PTE update must be atomic with respect to other accesses to the PTE, and must
  atomically perform all page-table walk checks for that leaf PTE as part of, and before, conditionally updating
  the PTE value."  Rendering: ONE fused step `VLabel.ad base tvs data` (read answers `tvs`, written bytes `data`,
  fulfil `ts`): every read byte `(t, v)` holds `v` at `t`, `t < ts`, and NO write by ANY agent (the updating hart
  included) to that byte lies in `(t, ts)` (`adReadOk`).  So every byte reads the latest write below `ts`.
  FAITHFUL (M20 (2): `exclOk` against writes by any hart in `(tr, ts)`); fusing the read and the write is FAITHFUL
  for behaviours (the pair has no view effect, so a split read can always be moved next to its write), as `LRmw`.
* M20 (2): the pre-view is ONLY the read's sources (`t < ts`); no `vcap`, `vwNew`, address/data view, rl-term; no
  COH against the hart's `coh`.  M20 (3) (rev 5 default): NO post-state effect for A and for D — `ws` unchanged;
  only the promise is consumed.
* supervisor.adoc:1625–1627 "Updates of the A bit may be performed as a result of speculation, even if the
  associated memory access ultimately is not performed architecturally."  The arm is the SAME for a speculative
  update (`WPAspec`): the program half `pstep` may emit `ad` at any point, tied to no access.  FAITHFUL.
* supervisor.adoc:1628–1630 "updates to the D bits in VS-stage and G-stage PTEs that result from an explicit store
  must be exact (i.e. non-speculative) and observed in program order by the local hart" — not enforced (M20 (3)
  rev 5 default, PA-5D off): WEAKER-or-FAITHFUL (no H extension in xv6).
* supervisor.adoc:1635–1640 "The PTE update must appear in the global memory order before the memory access that
  caused the PTE update and before any subsequent explicit memory access to that virtual page by the local hart.
  The ordering on loads and stores provided by FENCE instructions … also orders the PTE updates" — PA-5-ord, not
  enforced (plan M20 Reference: optional, unenforced): WEAKER.  M20 (1)'s contribution of a non-speculative A/D read
  to its access's pre-view (PA-1) is not modelled either: WEAKER.  Both would only RAISE views (the direction the
  NF_R self bound already absorbs); the arm here is the hard case, the write with no view effect.
* The value written (`adData`, M20 (6): `update_PTE_Bits` of the read value) is an EMISSION fact (Sail computes it);
  the abstract `pstep` chooses `data`, as for every other write label.
* MESSAGE CLASS `WCad` (M20 (5)) — `PClass.ad`.  Machine.lean's `PClass` is closed (it may not be edited), so the
  class is ENCODED as `.cmo .clean 0` with a NON-EMPTY data list: no v2 arm fulfils such a message (the only arm
  taking a `.cmo` class, `memStep.cmo`, needs `data = []`), and `cmoAt` never sees it (length 0 covers no byte).
  So `.ad` is fixed at the promise and matched only by the A/D arm, which fulfils nothing else: INERT, as M20 (5).
* FETCH: v2's fetch arm exempts an "own already-fulfilled store (a po-earlier store of the hart)" from the fetch
  view (Machine.lean `fetchView`).  An A/D write is "a gmo store outside po and ppo" (plan M20, Reference), so it is
  no such store: `ownDoneV` excludes the `.ad` class.  FAITHFUL to the reading recorded at `fetchView`.

The variant's runs (`pmStepV`, `validRunV`) are machine v2's with this label alphabet (`VLabel`) and events
(`VEvt`).  No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.NfrFetch

namespace Weak.Prom

/-- THE A/D MESSAGE CLASS `WCad` (plan M20 (5)), encoded (see the header): `.cmo .clean 0` with non-empty data. -/
def PClass.ad : PClass := .cmo .clean 0

namespace Ad

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open PLabel

/-- THE VARIANT'S LABELS: machine v2's, and the fused A/D update (plan M20: `LAdRd`/`LAdWr` as one step). -/
inductive VLabel where
  | v (l : PLabel)
  | ad (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))

/-- Timestamp `t` of `M` is an A/D message. -/
def adAt (M : List PMsg) (t : Nat) : Prop := ∃ m, M[t - 1]? = some m ∧ m.cls = PClass.ad

/-- The fetch view's own-store exemption WITHOUT A/D writes (an A/D write is not a po-earlier store). -/
def ownDoneV (log : List PMsg) (i : Nat) (prom : GSet Nat) (t : Nat) : Bool :=
  ownDone log i prom t &&
    (match log[t - 1]? with
     | some m => !(decide (m.cls = PClass.ad))
     | none => false)

/-- The variant's fetch view (Machine.lean `fetchView` with `ownDoneV`). -/
def fetchViewV (log : List PMsg) (i : Nat) (prom : GSet Nat) (base : Int) (tvs : List (Nat × BitVec 8)) : Nat :=
  bytesMax (fun _ t => if ownDoneV log i prom t then 0 else t) base tvs

/-- The variant's fetch post (Machine.lean arm `fetch` with `fetchViewV`), against log `L` and promises `prom`. -/
def fetchPostV (L : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (base : Int)
    (tvs : List (Nat × BitVec 8)) : PState :=
  { ws with
    wIfr := max ws.wIfr (bytesMax (fun _ t => t) base tvs)
    wIfv := max ws.wIfv (fetchViewV L i prom base tvs) }

/-- THE A/D READ of one byte for an update at `ts` (supervisor.adoc:1622–1624; M20 (2)): the byte holds `v` at `t`,
`t < ts` (the write's only pre-view), and no write by ANY agent to the byte lies in `(t, ts)`. -/
def adReadOk (img : Image) (log : List PMsg) (ts : Nat) (a : Int) (t : Nat) (v : BitVec 8) : Prop :=
  memByte img log t a = some v ∧ t < ts ∧ ¬ writesIn log a t (ts - 1)

section memstep

variable (img : Image) (log : List PMsg) (i : Nat)

/-- THE VARIANT'S MEMORY HALF: v2's arms except the fetch, the fetch with `fetchViewV`, and the A/D arm. -/
inductive memStepV : GSet Nat → PState → VLabel → Option Nat → PState → GSet Nat → Prop
  /-- Every non-fetch arm of machine v2, unchanged. -/
  | v2 (prom : GSet Nat) (ws : PState) (l : PLabel) (ots : Option Nat) (ws' : PState) (prom' : GSet Nat) :
      memStep img log i prom ws l ots ws' prom' → ¬ Nfr.F.isFetch l → memStepV prom ws (.v l) ots ws' prom'
  /-- Machine v2's fetch arm, the own-store exemption without A/D writes. -/
  | fetch (prom : GSet Nat) (ws : PState) (base : Int) (tvs : List (Nat × BitVec 8)) :
      bytesAll (fetchByteOk img log ws) base tvs →
      memStepV prom ws (.v (LIFetch base tvs)) none (fetchPostV log i prom ws base tvs) prom
  /-- THE A/D UPDATE (`WPAd`/`WPAspec`, M20 (2), (3), (5)): fulfils its `.ad` promise `ts`; atomic against every
  write (`adReadOk`); NO view effect, NO COH; post: the promise is consumed, nothing else. -/
  | ad (prom : GSet Nat) (ws : PState) (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
      (ts : Nat) :
      tvs.length = data.length → 0 < ts → ts ∈ prom → log[ts - 1]? = some ⟨base, data, some i, PClass.ad⟩ →
      bytesAll (adReadOk img log ts) base tvs →
      memStepV prom ws (.ad base tvs data) (some ts) ws (prom \ {ts})

end memstep

/-- The variant's events. -/
inductive VEvt where
  | prom (i : Nat) (m : PMsg)
  | st (i : Nat) (l : VLabel) (ts : Option Nat)

section machine

variable {P D : Type} (pstep : P → D → VLabel → P → D → Prop)

/-- ONE STEP of the variant (Machine.lean `pmStep` over `VLabel`). -/
inductive pmStepV : PCfg P D → VEvt → PCfg P D → Prop
  | promise (cfg : PCfg P D) (i : Nat) (ag : PAgent P) (m : PMsg) :
      cfg.pcAgs[i]? = some ag →
      (m.data ≠ [] ∨ ∃ k len, m.cls = .cmo k len ∧ 0 < len) →
      m.tid = some i →
      pmStepV cfg (.prom i m)
        ⟨cfg.pcImg, cfg.pcLog ++ [m], cfg.pcDev,
         cfg.pcAgs.set i ⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩⟩
  | state (cfg : PCfg P D) (i : Nat) (ag : PAgent P) (l : VLabel) (ots : Option Nat) (st' : P) (d' : D)
      (ws' : PState) (prom' : GSet Nat) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev l st' d' →
      memStepV cfg.pcImg cfg.pcLog i ag.paProm ag.paWs l ots ws' prom' →
      pmStepV cfg (.st i l ots) ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', ws', prom'⟩⟩

/-- Runs of the variant. -/
inductive pmStepsV : PCfg P D → List VEvt → PCfg P D → Prop
  | refl (cfg : PCfg P D) : pmStepsV cfg [] cfg
  | step (c0 c1 c2 : PCfg P D) (e : VEvt) (es : List VEvt) :
      pmStepV pstep c0 e c1 → pmStepsV c1 es c2 → pmStepsV c0 (e :: es) c2

/-- A VALID RUN of the variant (Machine.lean `validRun`). -/
def validRunV (img : Image) (d0 : D) (ps : List P) (evs : List VEvt) (cfg : PCfg P D) : Prop :=
  pmStepsV pstep (pmInit img d0 ps) evs cfg ∧ noPromises cfg

end machine

/-- The trace of agent `h` (Machine.lean `traceOf`). -/
def traceOfV (h : Nat) : List VEvt → List (VLabel × Option Nat)
  | [] => []
  | .prom _ _ :: es => traceOfV h es
  | .st i l ots :: es => if i = h then (l, ots) :: traceOfV h es else traceOfV h es

end Ad

end Weak.Prom
