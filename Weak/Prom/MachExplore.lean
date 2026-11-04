/-
Weak/Prom: **the label-level successor function of machine v2** (S0-P part (2), milestone 1; designed for
milestone 2's `explorerStep_sound`).

`succ img log i prom ws t` lists, for agent `i` with promise set `prom` and state `ws` against the memory `log`, every
state step `memStep img log i prom ws l ots ws' prom'` whose label `l` instantiates the label TEMPLATE `t` (a label
without its memory answers: a load without its per-byte timestamps/values, a store without its fulfil timestamp).
It is a plain Lean function over machine v2's own types (`PState`, `PLabel`, `GSet Nat`, `List PMsg`), and every
successor's post-state is computed by Machine.lean's own post-state functions (`loadRun`, `storeRun`, `amoPost`,
`fencePost`, …), so the milestone-2 statement is

  `explorerStep_sound : s ∈ succ img log i prom ws t → memStep img log i prom ws s.l s.ots s.ws s.prom`

and needs only the Bool transcriptions below to be equivalent to the `Prop` premises (`writesInB`, `exclOkB`,
`invalReadB`, `loadOkB`, `cohBelowB`; one lemma each), plus `ExtTreeSet.contains ↔ ∈`.  PROVED in
`Weak/Prom/MachSound.lean` (milestone 2).

## Completeness (what milestone 1 relies on; proof sketch, not yet a Lean theorem)

`succ` is also COMPLETE: every `memStep` whose label instantiates `t` is listed.  Fixed labels and writes are
enumerated outright (every `ts ∈ [1, |log|]` is tried; a fulfilled `ts` is a promise, hence `≤ |log|`).  Reads are
the only infinite-looking case: `readCands` lists answer runs, and the list is complete:
* if the log holds a cache-block message (never in the litmus corpus), every byte tries every timestamp `0 … |log|`
  (brute force; `memByte … t a = some v` forces `t ≤ |log|`);
* otherwise `invalRead` is false (it needs a `cmo` message), and for an admissible run `tvs` let
  `p₀ = max vpre (nonFwdMax ws base tvs)`.  A NON-forwarded byte `(t, v)` at `a` has `t ≤ p₀` and no write to `a`
  in `(t, max p₀ (coh a)] ⊇ (t, p₀]`, so `t` is THE latest timestamp `≤ p₀` holding byte `a` (`latestAt`); a
  forwarded byte has `t` = the forward-bank entry.  So `tvs` is in the product `byteOpts … p₀` with
  `max vpre nonFwdMax = p₀`, which `readCands` enumerates for every `p₀ ∈ [vpre, |log|]`.
Every candidate is then FILTERED by `loadOkB` (the transcription of `loadOk`), so the generator is only trusted for
completeness, never for soundness.
-/
import Weak.Prom.MachInval   -- MachFix-R-b5 (was: Weak.Prom.Machine)

namespace Weak.Prom.Mach

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel

/-! ## 1. Bool transcriptions of the `memStep` premises -/

/-- `writesIn` as a Bool: some `t ∈ (lo, hi]` writes byte `a`. -/
def writesInB (log : List PMsg) (a : Int) (lo hi : Nat) : Bool :=
  (List.range' (lo + 1) (hi - lo)).any (fun t =>
    match log[t - 1]? with
    | some m => (m.byteAt a).isSome
    | none => false)

/-- `writesInBy … (fun tid => tid ≠ some i)` as a Bool. -/
def writesInOtherB (log : List PMsg) (i : Nat) (a : Int) (lo hi : Nat) : Bool :=
  (List.range' (lo + 1) (hi - lo)).any (fun t =>
    match log[t - 1]? with
    | some m => (m.byteAt a).isSome && decide (m.tid ≠ some i)
    | none => false)

/-- `exclOk` as a Bool. -/
def exclOkB (log : List PMsg) (i : Nat) : Int → List Nat → Nat → Bool
  | _, [], _ => true
  | a, t :: r, ts => !writesInOtherB log i a t (ts - 1) && exclOkB log i (a + 1) r ts

/-- `cmoAt` as a Bool (note `t - 1` at `t = 0` is `0`, exactly as in `cmoAt`). -/
def cmoAtB (log : List PMsg) (p : CmoKind → Bool) (t : Nat) (a : Int) : Bool :=
  match log[t - 1]? with
  | some m =>
    match m.cls with
    | .cmo k len => p k && decide (m.pa ≤ a) && decide (a < m.pa + len)
    | _ => false
  | none => false

/-- `invalRead` as a Bool: `ti` ranges over `(t, |log|]` (a `cmoAt` timestamp `> t ≥ 0` is a log entry), `ti'`
over `(ti, max fl ti]`, `c` over `[0, ti)`. -/
def invalReadB (log : List PMsg) (a : Int) (t fl : Nat) : Bool :=
  (List.range' (t + 1) (log.length - t)).any (fun ti =>
    cmoAtB log isInvalK ti a && !writesInB log a ti fl &&
    !(List.range' (ti + 1) (max fl ti - ti)).any (fun ti' => cmoAtB log isInvalK ti' a) &&
    (List.range ti).all (fun c => !cmoAtB log isCleanK c a || !writesInB log a t (c - 1)))

/-- `bytesAll` as a Bool. -/
def bytesAllB (P : Int → Nat → BitVec 8 → Bool) : Int → List (Nat × BitVec 8) → Bool
  | _, [] => true
  | a, (t, v) :: r => P a t v && bytesAllB P (a + 1) r

/-- `loadOk` as a Bool. -/
def loadOkB (img : Image) (log : List PMsg) (ws : PState) (vpre : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Bool :=
  bytesAllB (fun a t v =>
      memByte img log t a == some v &&
      (!writesInB log a t
          (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a)) ||
        invalReadB log a t (max vpre (coh ws a))))
    base tvs

/-- MachFix-R-b5: `invalReadAt` as a Bool (`ti'` over `(ti, max fl ti]`, `c` over `[0, ti)`). -/
def invalReadAtB (log : List PMsg) (a : Int) (t fl ti : Nat) : Bool :=
  cmoAtB log isInvalK ti a && decide (t < ti) && !writesInB log a ti fl &&
    !(List.range' (ti + 1) (max fl ti - ti)).any (fun ti' => cmoAtB log isInvalK ti' a) &&
    (List.range ti).all (fun c => !cmoAtB log isCleanK c a || !writesInB log a t (c - 1))

/-- MachFix-R-b5: `bytesAny` as a Bool. -/
def bytesAnyB (P : Int → Nat → BitVec 8 → Bool) : Int → List (Nat × BitVec 8) → Bool
  | _, [] => false
  | a, (t, v) :: r => P a t v || bytesAnyB P (a + 1) r

/-- MachFix-R-b5: `invalCite` as a Bool (`ti` over `[0, vi]`). -/
def invalCiteB (log : List PMsg) (ws : PState) (vpre vi : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) :
    Bool :=
  bytesAllB (fun a t _ =>
      !writesInB log a t (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a)) ||
      (List.range (vi + 1)).any (fun ti => invalReadAtB log a t (max vpre (coh ws a)) ti)) base tvs &&
  (vi == 0 || bytesAnyB (fun a t _ => invalReadAtB log a t (max vpre (coh ws a)) vi) base tvs)

/-- `cohBelow` as a Bool. -/
def cohBelowB (ws : PState) : Int → Nat → Nat → Bool
  | _, 0, _ => true
  | a, n + 1, ts => decide (coh ws a < ts) && cohBelowB ws (a + 1) n ts

/-- Promise membership (`ExtTreeSet.contains`). -/
def promHas (prom : GSet Nat) (ts : Nat) : Bool := prom.contains ts

/-! ## 2. Read candidates (complete; see the header) -/

/-- Does the log hold a cache-block message? -/
def logHasCmo (log : List PMsg) : Bool :=
  log.any (fun m => match m.cls with | .cmo _ _ => true | _ => false)

/-- MachFix-R-b5: THE ABSORBED-VIEW CANDIDATES of a read: `0`, and with a cache-block message every timestamp
`1 … |log|` (`invalCite_le`); each candidate is filtered by `invalCiteB`. -/
def viCands (log : List PMsg) : List Nat :=
  if logHasCmo log then List.range (log.length + 1) else [0]

/-- MachFix-R-b5: the admissible absorbed views of an admissible read. -/
def viOpts (log : List PMsg) (ws : PState) (vpre : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) : List Nat :=
  (viCands log).filter (fun vi => invalCiteB log ws vpre vi base tvs)

/-- The latest timestamp `≤ p` at which byte `a` is held (the image at `0`, or a log entry writing `a`). -/
def latestAt (img : Image) (log : List PMsg) (a : Int) (p : Nat) : Option Nat :=
  ((List.range (p + 1)).reverse).find? (fun t => (memByte img log t a).isSome)

/-- The per-byte options at read point `p₀`: `(t, v, forwarded?)`. -/
def byteOpts (img : Image) (log : List PMsg) (ws : PState) (vpre p0 : Nat) (a : Int) :
    List (Nat × BitVec 8 × Bool) :=
  let fwd : List (Nat × BitVec 8 × Bool) :=
    match get? ws.wFwd a with
    | some (tf, _) =>
      match memByte img log tf a with
      | some v => if !writesInB log a tf (max vpre (coh ws a)) then [(tf, v, true)] else []
      | none => []
    | none => []
  let nf : List (Nat × BitVec 8 × Bool) :=
    match latestAt img log a p0 with
    | some t =>
      if fwdHit ws a t then [] else
      match memByte img log t a with
      | some v => if !writesInB log a t (max p0 (coh ws a)) then [(t, v, false)] else []
      | none => []
    | none => []
  fwd ++ nf

/-- The product of per-byte option lists, keeping the max non-forwarded timestamp. -/
def prodOpts : List (List (Nat × BitVec 8 × Bool)) → List (List (Nat × BitVec 8) × Nat)
  | [] => [([], 0)]
  | os :: rest =>
    (prodOpts rest).flatMap (fun (tl, m) =>
      os.map (fun (t, v, f) => ((t, v) :: tl, if f then m else max t m)))

/-- Brute-force per-byte options (every timestamp holding the byte), for a log with cache-block messages. -/
def bruteOpts (img : Image) (log : List PMsg) (a : Int) : List (Nat × BitVec 8 × Bool) :=
  (List.range (log.length + 1)).filterMap (fun t => (memByte img log t a).map (fun v => (t, v, false)))

/-- THE READ CANDIDATES of an `sz`-byte read at `base`, pre-view `vpre` (a superset of the admissible runs). -/
def readCands (img : Image) (log : List PMsg) (ws : PState) (vpre : Nat) (base : Int) (sz : Nat) :
    List (List (Nat × BitVec 8)) :=
  let addrs := (List.range sz).map (fun k : Nat => base + (k : Int))
  if logHasCmo log then
    (prodOpts (addrs.map (bruteOpts img log))).map (·.1)
  else
    (List.range' vpre (log.length + 1 - vpre)).flatMap (fun p0 =>
      ((prodOpts (addrs.map (byteOpts img log ws vpre p0))).filter (fun c => max vpre c.2 == p0)).map (·.1))

/-! ## 3. Label templates and the successor function -/

/-- A LABEL TEMPLATE: a label without the memory system's answers. -/
inductive Tmpl where
  /-- A label with no answer (silent, fence, FENCE.I, register write, control, boundary, SC end). -/
  | fix (l : PLabel)
  /-- `LLoad aq rl base tvs asrc` with `|tvs| = sz`. -/
  | ld (aq rl : Bool) (base : Int) (sz : Nat) (asrc : List Dsrc)
  /-- `LExLoad aq rl base tvs asrc` with `|tvs| = sz`. -/
  | lr (aq rl : Bool) (base : Int) (sz : Nat) (asrc : List Dsrc)
  /-- `LStore aq rl base data asrc vsrc` with its fulfil timestamp. -/
  | st (aq rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
  /-- `LExStore aq rl base data asrc vsrc` with its fulfil timestamp. -/
  | sc (aq rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
  /-- `LRmw aq rl base tvs (f values) asrc vsrc`: the written bytes are a function of the read bytes. -/
  | rmw (aq rl : Bool) (base : Int) (sz : Nat) (f : List (BitVec 8) → List (BitVec 8)) (asrc vsrc : List Dsrc)

/-- One successor: the concrete label, the fulfil timestamp, the post-state and promise set. -/
structure Succ where
  l : PLabel
  ots : Option Nat
  ws : PState
  prom : GSet Nat

/-- The post-state of a label with no answer (the arms `silent`, `fence`, `fenceI`, `dev`, `regW`, `ctrl`,
`instr`, `scFail`), `none` for a label that needs answers. -/
def fixPost (ws : PState) : PLabel → Option PState
  | LSilent => some ws
  | LFence pr pw sr sw => some (fencePost ws pr pw sr sw)
  | LFenceI => some (fenceIPost ws)
  | LDev _ _ _ _ _ => some ws
  | LRegW rd srcs => some { ws with wRegv := insert ws.wRegv rd (srcsView ws srcs) }
  | LCtrl srcs => some { ws with wVcap := max (srcsView ws srcs) ws.wVcap }
  | LInstr => some { ws with wLdv := 0, wRmw := none, wIfv := 0 }
  | LExFail => some { ws with wRes := none }
  | _ => none

/-- The fulfil timestamps a write of `data` at `base` with class `cls` may take: own promises holding exactly this
message, above the bytes' coherence floors and above the pre-view `pre`. -/
def writeTs (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) (base : Int) (data : List (BitVec 8))
    (cls : PClass) (pre : Nat) : List Nat :=
  (List.range' 1 log.length).filter (fun ts =>
    promHas prom ts && log[ts - 1]? == some ⟨base, data, some i, cls⟩ &&
    cohBelowB ws base data.length ts && decide (pre < ts))

/-- THE SUCCESSOR FUNCTION: every `memStep` of agent `i` whose label instantiates the template. -/
def succ (img : Image) (log : List PMsg) (i : Nat) (prom : GSet Nat) (ws : PState) : Tmpl → List Succ
  | .fix l =>
    match fixPost ws l with
    | some ws' => [⟨l, none, ws', prom⟩]
    | none => []
  | .ld aq rl base sz asrc =>
    let va := srcsView ws asrc
    let vpre := ldPre ws aq rl va
    (readCands img log ws vpre base sz).flatMap (fun tvs =>
      if loadOkB img log ws vpre base tvs then
        (viOpts log ws vpre base tvs).map (fun vi =>   -- MachFix-R-b5
          ⟨LLoad aq rl base tvs asrc, none, loadRunV ws aq rl va vi base tvs, prom⟩)
      else [])
  | .lr aq rl base sz asrc =>
    let va := srcsView ws asrc
    let vpre := ldPre ws aq rl va
    (readCands img log ws vpre base sz).flatMap (fun tvs =>
      if loadOkB img log ws vpre base tvs then
        (viOpts log ws vpre base tvs).map (fun vi =>   -- MachFix-R-b5
          ⟨LExLoad aq rl base tvs asrc, none,
            { loadRunV ws aq rl va vi base tvs with
              wRes := some ⟨base, tvs.map Prod.fst, readViewV ws aq rl va vi base tvs⟩ },
            prom⟩)
      else [])
  | .st aq rl base data asrc vsrc =>
    let va := srcsView ws asrc
    let vd := srcsView ws vsrc
    (writeTs log i prom ws base data (stClass rl) (stPreA ws aq rl va vd)).map (fun ts =>
      ⟨LStore aq rl base data asrc vsrc, some ts,
        acqPost (storeRun ws rl va (max va vd) base data.length ts) aq ts, prom \ {ts}⟩)
  | .sc aq rl base data asrc vsrc =>
    match ws.wRes with
    | none => []
    | some R =>
      let va := srcsView ws asrc
      let vd := srcsView ws vsrc
      ((writeTs log i prom ws base data .excl (max (stPreA ws aq rl va vd) R.rvView)).filter (fun ts =>
          exclOkB log i R.rvBase R.rvTs ts && R.rvTs.all (fun t => decide (t < ts)))).map (fun ts =>
        let s1 := storeRun ws rl va ts base data.length ts
        ⟨LExStore aq rl base data asrc vsrc, some ts, { acqPost s1 aq ts with wLdv := max s1.wLdv ts, wRes := none },
          prom \ {ts}⟩)
  | .rmw aq rl base sz f asrc vsrc =>
    let va := srcsView ws asrc
    let vd := srcsView ws vsrc
    let vpre := ldPre ws aq false va
    (readCands img log ws vpre base sz).flatMap (fun tvs =>
      if !loadOkB img log ws vpre base tvs then [] else
      let data := f (tvs.map Prod.snd)
      let ws1 := loadRun ws aq false va base tvs
      if tvs.length != data.length then [] else
      ((writeTs log i prom ws1 base data .excl (stPre ws1 rl va vd)).filter (fun ts =>
          exclOkB log i base (tvs.map Prod.fst) ts)).flatMap (fun ts =>
        ((viOpts log ws vpre base tvs).filter (fun vi => decide (vi < ts))).map (fun vi =>   -- MachFix-R-b5
          ⟨LRmw aq rl base tvs data asrc vsrc, some ts,
            amoPost (storeRun (loadRunV ws aq false va vi base tvs) rl va ts base data.length ts) aq ts,
            prom \ {ts}⟩)))

/-! ## 4. Promise sets of the promises-first normal form -/

/-- The promise set of agent `i` after promising every message of `log` it authored, in log order (the `promise`
arm's `{|log| + 1} ∪ prom`, iterated). -/
def promsOf (log : List PMsg) (i : Nat) : GSet Nat :=
  (List.range log.length).foldl (fun acc k =>
    match log[k]? with
    | some m => if m.tid == some i then {k + 1} ∪ acc else acc
    | none => acc) ∅

/-- No outstanding promise among the timestamps `1 … |log|` (`promWf` bounds every promise by `|log|`). -/
def promDone (log : List PMsg) (prom : GSet Nat) : Bool :=
  (List.range' 1 log.length).all (fun t => !promHas prom t)

end Weak.Prom.Mach
