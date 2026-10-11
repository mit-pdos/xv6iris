/-
Weak: **W2 SPIKE — promise-free runs into TsoMem: the (↓) risk witnesses** (allocproc plan
`notes/weak-allocproc-plan.md` §C Stage 0 "W2"; report `W2-spike.md` at the workspace root).

Lean-only (no Rocq source).  The spike's verdict is the plan's D7 STOP: on SHAPED pf runs
(`pfRunS` + `pairAdjacent` + every plain load `scaOk`, W5b's statements) the WeakMem machine
has behaviours TsoMem lacks under the plan's position-preserving log identification.  This
file proves the two hart-side witnesses and the parts of the per-label table that DO close:

* `TsoOfPf.g1Run` / `TsoOfPf.tsoAqPairTv` (G1, the `.aq` "off-by-one" is off by `top - t`):
  after an acquire exclusive pair whose read takes timestamp `t` of the lock word, WeakMem's
  load floor is `t`, TsoMem's is the pair's write timestamp `top + 1`; a later plain load of
  another byte reads a value TsoMem cannot return.
* `TsoOfPf.g2Run` / `TsoOfPf.tsoAfterLoadCoh` (G2, mixed-size coherence): the spike found that
  TsoMem stamped EVERY footprint byte's coherence floor with the load's view `tvn` (two
  overlapping loads of different footprints separated it from WeakMem).  W-COH (G2-Q (a′))
  changed TsoMem: a load stamps a byte with its source's timestamp only when the source is
  FOREIGN, and a hart's store resets its footprint's floors; `tsoAfterLoadCoh` states the new
  stamp, `g2TsoSched` gives `g2Run` a TsoMem schedule, `g2OwnSched` realizes §B(10)'s own-store
  candidate (`m0`/`w_c'`).
* `TsoOfPf.fenceRow`: every non-`fence.i` barrier's TsoMem floor is below WeakMem's `wVrNew`
  given `R`'s three view inequalities (the fence spot checks).

The program is the most permissive one (`TsoOfPf.anyStep`): W2's per-label lemma is stated for
any `pstep`, so a counterexample may pick it.  `TsoOfPf.histOf` is `R`'s per-byte history
(the log projection; latest first; image entry at timestamp 0).
-/
import Weak.PfRunShape
import Weak.WeakEvLang
import MachCSL.Lang

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D

/-! ## 0. Program, image, configuration, `R`'s history -/

/-- Any program: every label is a program step. -/
def TsoOfPf.anyStep (_ : Unit) (_ : Unit) (_ : Wlabel) (_ : Unit) (_ : Unit) : Prop := True

/-- Every write is plain-class. -/
def TsoOfPf.anyCls (_ : Unit) (_ : Wlabel) (_ : Wstate) : WmClass := .WCplain

/-- The all-zero image. -/
def TsoOfPf.img0 : Image := fun _ => some 0

/-- Two agents (0 = hart A, 1 = hart B), both at `wsInit`, empty log. -/
def TsoOfPf.cfg0 : Wpcfg Unit Unit :=
  ⟨TsoOfPf.img0, [], (), [⟨(), wsInit, ∅⟩, ⟨(), wsInit, ∅⟩]⟩

-- The witnesses' logs: G1 (`x := 1` by B, then A's AMO write to `y`), G2 (`c := 1`, `a := 1`).
def TsoOfPf.mx : Wmsg := ⟨0, [1#8], some 1, .WCplain⟩
def TsoOfPf.my : Wmsg := ⟨8, [1#8], some 0, .WCplain⟩
def TsoOfPf.g1Log : List Wmsg := [TsoOfPf.mx, TsoOfPf.my]
def TsoOfPf.mc : Wmsg := ⟨2, [1#8], some 1, .WCplain⟩
def TsoOfPf.ma : Wmsg := ⟨0, [1#8], some 1, .WCplain⟩
def TsoOfPf.g2Log : List Wmsg := [TsoOfPf.mc, TsoOfPf.ma]

/-- `R`'s per-byte history of `a`: the log's writes to `a`, latest first (timestamp = position
+ 1, author = `wmTid`), then the image byte at timestamp 0. -/
def TsoOfPf.histOf (img : Image) (log : List Wmsg) (a : Int) : Hist :=
  ((List.range log.length).filterMap (fun i =>
      (log[i]?.bind (fun m => msgByte m a)).map
        (fun v => (⟨i + 1, (log[i]?.bind Wmsg.wmTid).getD 0, v⟩ : HEnt)))).reverse ++
  ((img a).map (fun v => (⟨0, 0, v⟩ : HEnt))).toList

theorem TsoOfPf.notWritesInLe (log : List Wmsg) (a : Int) (lo hi : Nat) (h : hi ≤ lo) :
    ¬ writesIn log a lo hi := by
  rintro ⟨t, h1, h2, _⟩; omega

/-- A later write is never visible, checked on the log positions `t < t' ≤ |log|` only. -/
theorem TsoOfPf.later (img : Image) (log : List Wmsg) (i tvn : Nat) (a : Int) (t : Nat)
    (hlo : ∀ t', t < t' → t' ≤ log.length → (logByte img log t' a).isSome → ¬ scaVis log i tvn t') :
    ∀ t', t < t' → (logByte img log t' a).isSome → ¬ scaVis log i tvn t' :=
  fun t' ht hs => hlo t' ht (logByteBounded _ _ _ _ hs) hs

-- The witnesses' per-byte read obligations (`readOkD`), by evaluation.
set_option hygiene false in
local macro "tsoRd" : tactic => `(tactic| (intro j t v h; rcases j with _ | _ | j <;> simp at h <;>
  (obtain ⟨rfl, rfl⟩ := h) <;>
  exact ⟨by decide, ⟨by decide, TsoOfPf.notWritesInLe _ _ _ _ (by decide)⟩, by simp⟩))

-- The witnesses' single-copy-atomicity bytes (`scaByte`), by enumeration of log positions.
set_option hygiene false in
local macro "tsoSca" : tactic => `(tactic| (
  rcases j with _ | _ | j <;> simp at h <;> subst h
  all_goals refine ⟨(by decide), Or.inl (by decide), TsoOfPf.later _ _ _ _ _ _ ?_⟩
  all_goals intro tq h1 h2 hs hv
  all_goals (try simp [TsoOfPf.cfg0, TsoOfPf.g2Log] at h2)
  all_goals rcases (show tq = 1 ∨ tq = 2 by omega) with rfl | rfl
  all_goals simp_all [scaVis, logByte, msgByte, accAddr, TsoOfPf.cfg0, TsoOfPf.mx, TsoOfPf.my,
    TsoOfPf.mc, TsoOfPf.ma, TsoOfPf.g2Log]))

/-- TsoMem reading a two-entry history `[⟨k, B, 1⟩, ⟨0, _, 0⟩]` as agent `0 ≠ B`. -/
theorem TsoOfPf.readHi (k tvn : Nat) (h : k ≤ tvn) :
    Hist.read 0 tvn [⟨k, 1, 1#8⟩, ⟨0, 0, 0#8⟩] = some 1#8 := by
  simp [Hist.read, HEnt.visible, h]

theorem TsoOfPf.readLo (k tvn : Nat) (h : tvn < k) :
    Hist.read 0 tvn [⟨k, 1, 1#8⟩, ⟨0, 0, 0#8⟩] = some 0#8 := by
  simp [Hist.read, HEnt.visible, show ¬ k ≤ tvn by omega]

/-! ## 1. G1 — the acquire exclusive pair (TsoMem: floor `top + 1`; WeakMem: floor `t`) -/

/-- TsoMem: an acquire exclusive read followed by its write leaves the floor at the write's
timestamp `top + 1`, whatever timestamp the read's bytes carried. -/
theorem TsoOfPf.tsoAqPairTv (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (pa' : PAddr) (n' : Nat) (w' : BitVec (8 * n')) :
    ((σ.afterExcl cpu pa n w true).store cpu pa' n' w' true).tv cpu = σ.top + 1 := by
  simp [HRead.afterExcl, updCpu, MState.top]

/-- TsoMem: any exclusive read moves the read watermark to the top (a later `fence r,_`
raises the floor there; WeakMem's `wVrOld` only reaches the read's timestamps). -/
theorem TsoOfPf.tsoExclRv (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (aq : Bool) : ((σ.afterExcl cpu pa n w aq).hr cpu).rv = σ.top := by
  simp [HRead.afterExcl, updCpu]


/-- B stores `x := 1` (ts 1); A runs `amoswap.aq` on `y` (read ts 0, write ts 2), then a
plain load of `x` returning the IMAGE byte 0. -/
def TsoOfPf.g1St : List (Nat × Wlabel) :=
  [(1, .LStore false 0 [1#8] [] []), (0, .LExLoad true 8 [(0, 0#8)] []),
   (0, .LExStore false 8 [1#8] [] []), (0, .LLoad false false 0 [(0, 0#8)] [])]

theorem TsoOfPf.g1Shape : pairAdjacent TsoOfPf.g1St :=
  pairAdjacentApp [(1, .LStore false 0 [1#8] [] [])] _
    (pairAdjacentFused _ (by simp [lbFused]))
    (pairAdjacentApp _ [(0, .LLoad false false 0 [(0, 0#8)] [])]
      (pairAdjacentBlk 0 true 8 [(0, 0#8)] [] false [1#8] [] [] [] (by simp) (by simp) rfl)
      (pairAdjacentFused _ (by simp [lbFused])))

theorem TsoOfPf.g1Run :
    ∃ c, pfRunS TsoOfPf.anyStep TsoOfPf.anyCls (candKfetch 0 0) TsoOfPf.cfg0 TsoOfPf.g1St c ∧
      c.pcLog = TsoOfPf.g1Log := by
  refine ⟨_, pfRunS.snoc _ _
    [(1, .LStore false 0 [1#8] [] []), (0, .LExLoad true 8 [(0, 0#8)] []),
     (0, .LExStore false 8 [1#8] [] [])] 0 (.LLoad false false 0 [(0, 0#8)] [])
    (pfRunS.snoc _ _
      [(1, .LStore false 0 [1#8] [] []), (0, .LExLoad true 8 [(0, 0#8)] [])] 0
      (.LExStore false 8 [1#8] [] [])
      (pfRunS.snoc _ _ [(1, .LStore false 0 [1#8] [] [])] 0 (.LExLoad true 8 [(0, 0#8)] [])
        (pfRunSOne _ _ _ _ _ 1 (.LStore false 0 [1#8] [] [])
          (wpPfStep.PFStore TsoOfPf.cfg0 ⟨(), wsInit, ∅⟩ false 0 [1#8] [] [] .WCplain () ()
            rfl trivial (by simp) rfl) trivial)
        (wpPfStep.PFExLoad _ ⟨(), wsInit, ∅⟩ true 8 [(0, 0#8)] [] () () rfl trivial ?r2) trivial)
      (wpPfStep.PFExStore _ _ false 8 [1#8] [] [] .WCplain ⟨8, [0], ldvOf wsInit true 0 8 [0]⟩
        () () rfl trivial (by simp) rfl rfl rfl ?e3 rfl) trivial)
    (wpPfStep.PFLoad _ _ false false 0 [(0, 0#8)] [] () () rfl trivial ?r4) ?f4, rfl⟩
  case r2 => tsoRd
  case e3 =>
    intro j t h hw
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact notWritesInCompute _ _ _ _ (by decide) (writesInByWritesIn _ _ _ _ _ hw)
    | succ j => simp at h
  case r4 => tsoRd
  case f4 => 
    refine ⟨0, by simp [TsoOfPf.cfg0], fun j t h => ?_⟩; tsoSca

/-- TsoMem's side of G1: from `R` (history = log projection; floor after the pair = top + 1
= 2, `tsoAqPairTv` at `top = 1`), hart A's load of byte 0 at ANY admissible view reads 1. -/
theorem TsoOfPf.g1Tso (tvn : Nat) (h : TsoOfPf.g1Log.length ≤ tvn) :
    Hist.read 0 tvn (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g1Log 0) = some 1#8 := by
  have hh : TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g1Log 0 = [⟨1, 1, 1#8⟩, ⟨0, 0, 0#8⟩] := by
    decide
  rw [hh]
  exact TsoOfPf.readHi 1 tvn (by simp [TsoOfPf.g1Log] at h; omega)

/-! ## 2. G2 — mixed-size coherence floors -/

/-- TsoMem (G2-Q (a′), W-COH): a plain load by `me` stamps footprint byte `j`'s coherence
floor with its source's timestamp `t` iff the source is FOREIGN (`max (hr.coh a) t`); an
own-sourced (forwarded or below the view) or source-less byte keeps `hr.coh a`.  The per-byte
input is `srcs : LoadSrcs` (`MState.afterLoad` passes `FlatMem.loadSrcs`; W5b′'s `tsoShadow`
mirrors it from the pf log). -/
theorem TsoOfPf.tsoAfterLoadCoh (hr : HRead) (me : Agent) (pa : PAddr) (n tvn j : Nat)
    (srcs : LoadSrcs) (hn : n < 2 ^ 64) (hj : j < n) :
    (∀ tid t, srcs[j]? = some (some (tid, t)) → tid ≠ me →
      (hr.afterLoad me pa n tvn srcs).coh (pa + BitVec.ofNat 64 j) =
        max (hr.coh (pa + BitVec.ofNat 64 j)) t) ∧
    ((∀ tid t, srcs[j]? = some (some (tid, t)) → tid = me) →
      (hr.afterLoad me pa n tvn srcs).coh (pa + BitVec.ofNat 64 j) =
        hr.coh (pa + BitVec.ofNat 64 j)) := by
  simp only [HRead.afterLoad]
  rw [LoadSrcs.stamp_at srcs me pa n j hn hj]
  unfold LoadSrcs.stampAt
  refine ⟨fun tid t hs hne => by rw [hs]; simp [hne], fun hown => ?_⟩
  split
  · rename_i tid t hs
    rw [if_pos (hown tid t hs)]; simp
  · simp


/-- B stores `c := 1` (ts 1) then `a := 1` (ts 2); A loads the half-word `(a, b)` reading
`(1, 0)`, then the half-word `(b, c)` reading `(0, 0)`. -/
def TsoOfPf.g2St : List (Nat × Wlabel) :=
  [(1, .LStore false 2 [1#8] [] []), (1, .LStore false 0 [1#8] [] []),
   (0, .LLoad false false 0 [(2, 1#8), (0, 0#8)] []),
   (0, .LLoad false false 1 [(0, 0#8), (0, 0#8)] [])]

theorem TsoOfPf.g2Shape : pairAdjacent TsoOfPf.g2St :=
  pairAdjacentFused _ (by simp [TsoOfPf.g2St, lbFused])

theorem TsoOfPf.g2Run :
    ∃ c, pfRunS TsoOfPf.anyStep TsoOfPf.anyCls (candKfetch 0 0) TsoOfPf.cfg0 TsoOfPf.g2St c ∧
      c.pcLog = TsoOfPf.g2Log := by
  refine ⟨_, pfRunS.snoc _ _
    [(1, .LStore false 2 [1#8] [] []), (1, .LStore false 0 [1#8] [] []),
     (0, .LLoad false false 0 [(2, 1#8), (0, 0#8)] [])] 0
    (.LLoad false false 1 [(0, 0#8), (0, 0#8)] [])
    (pfRunS.snoc _ _ [(1, .LStore false 2 [1#8] [] []), (1, .LStore false 0 [1#8] [] [])] 0
      (.LLoad false false 0 [(2, 1#8), (0, 0#8)] [])
      (pfRunS.snoc _ _ [(1, .LStore false 2 [1#8] [] [])] 1 (.LStore false 0 [1#8] [] [])
        (pfRunSOne _ _ _ _ _ 1 (.LStore false 2 [1#8] [] [])
          (wpPfStep.PFStore TsoOfPf.cfg0 ⟨(), wsInit, ∅⟩ false 2 [1#8] [] [] .WCplain () ()
            rfl trivial (by simp) rfl) trivial)
        (wpPfStep.PFStore _ _ false 0 [1#8] [] [] .WCplain () () rfl trivial (by simp) rfl)
        trivial)
      (wpPfStep.PFLoad _ ⟨(), wsInit, ∅⟩ false false 0 [(2, 1#8), (0, 0#8)] [] () () rfl
        trivial ?r3) ?f3)
    (wpPfStep.PFLoad _ _ false false 1 [(0, 0#8), (0, 0#8)] [] () () rfl trivial ?r4) ?f4, rfl⟩
  case r3 => tsoRd
  case r4 => tsoRd
  case f3 => 
    refine ⟨2, by simp [TsoOfPf.cfg0], fun j t h => ?_⟩; tsoSca
  case f4 => 
    refine ⟨0, by simp [TsoOfPf.cfg0], fun j t h => ?_⟩; tsoSca

/-- The view facts of G2 under `R`: the first load returns byte `a = 1` only at a view
`tvn₁ ≥ 2`, and at any view `≥ 2` byte `c` reads 1.  (Before W-COH the first load stamped byte
`b`'s floor with `tvn₁`, forcing the second load to a view `≥ 2` where `c` reads 1, not the
pf run's 0; under (a′) `b`'s image source stamps nothing — `g2TsoSched`.) -/
theorem TsoOfPf.g2Tso :
    (∀ tvn, Hist.read 0 tvn (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 0) = some 1#8 → 2 ≤ tvn) ∧
    (∀ tvn, 2 ≤ tvn → Hist.read 0 tvn (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 2) = some 1#8) := by
  have ha : TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 0 = [⟨2, 1, 1#8⟩, ⟨0, 0, 0#8⟩] := by decide
  have hc : TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 2 = [⟨1, 1, 1#8⟩, ⟨0, 0, 0#8⟩] := by decide
  refine ⟨fun tvn h => ?_, fun tvn h => by rw [hc]; exact TsoOfPf.readHi 1 tvn (by omega)⟩
  rw [ha] at h
  by_cases hl : 2 ≤ tvn
  · exact hl
  · rw [TsoOfPf.readLo 2 tvn (by omega)] at h; simp at h

/-- **G2 closes under (a′)** (W-COH): `g2Run` HAS a TsoMem schedule.  Hart A (agent 0, floor
0, no fence) loads `(a, b)` at view 2 reading `(1, 0)`; only `a`'s source is foreign (B's store
at ts 2), `b`'s is the image entry at ts 0, so the second load of `(b, c)` is coherence-legal at
view 0 and reads `(0, 0)` — the pf run's values. -/
theorem TsoOfPf.g2TsoSched :
    Hist.read 0 2 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 0) = some 1#8 ∧
    Hist.read 0 2 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 1) = some 0#8 ∧
    (HRead.zero.afterLoad 0 0#64 2 2
        [Hist.readSrc 0 2 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 0),
         Hist.readSrc 0 2 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 1)]).cohOk 1#64 2 0 ∧
    Hist.read 0 0 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 1) = some 0#8 ∧
    Hist.read 0 0 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 2) = some 0#8 := by
  have ha : TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 0 = [⟨2, 1, 1#8⟩, ⟨0, 0, 0#8⟩] := by decide
  have hb : TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 1 = [⟨0, 0, 0#8⟩] := by decide
  have hc : TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2Log 2 = [⟨1, 1, 1#8⟩, ⟨0, 0, 0#8⟩] := by decide
  rw [ha, hb, hc]
  decide

/-- §B(10)'s own-store candidate: B writes `c := 1` (`w_c`, ts 1), `c := 2` (`w_c'`, ts 2);
A writes `a := 1` (`m0`, ts 3); B writes `d := 1` (`w_d`, ts 4); bytes `c = 0`, `a = 1`,
`d = 2`. -/
def TsoOfPf.mc1 : Wmsg := ⟨0, [1#8], some 1, .WCplain⟩
def TsoOfPf.mc2 : Wmsg := ⟨0, [2#8], some 1, .WCplain⟩
def TsoOfPf.m0 : Wmsg := ⟨1, [1#8], some 0, .WCplain⟩
def TsoOfPf.md : Wmsg := ⟨2, [1#8], some 1, .WCplain⟩
def TsoOfPf.g2OwnLog : List Wmsg := [TsoOfPf.mc1, TsoOfPf.mc2, TsoOfPf.m0, TsoOfPf.md]

/-- **§B(10)'s own-store counterexample, realized** (W-COH, the foreign-only stamp): after
A's store `m0` (which resets `coh a`), `r_prev = lh (a, d)` at view 4 reads `a` from its OWN
`m0` and `d` from the foreign `w_d`, stamping only `d`; so `r = lh (c, a)` is coherence-legal at
view 1 and byte `c` reads `w_c` (1), not `w_c'` (2).  Had `a`'s source been stamped (agent 9
standing for a reader to whom `m0` is foreign), `r` would be illegal at view 1. -/
theorem TsoOfPf.g2OwnSched :
    Hist.read 0 4 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 1) = some 1#8 ∧
    Hist.read 0 4 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 2) = some 1#8 ∧
    ((HRead.zero.resetCoh 1#64 1).afterLoad 0 1#64 2 4
        [Hist.readSrc 0 4 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 1),
         Hist.readSrc 0 4 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 2)]).cohOk 0#64 2 1 ∧
    Hist.read 0 1 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 0) = some 1#8 ∧
    Hist.read 0 1 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 1) = some 1#8 ∧
    ¬ ((HRead.zero.resetCoh 1#64 1).afterLoad 9 1#64 2 4
        [Hist.readSrc 0 4 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 1),
         Hist.readSrc 0 4 (TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 2)]).cohOk 0#64 2 1 := by
  have hc : TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 0 =
      [⟨2, 1, 2#8⟩, ⟨1, 1, 1#8⟩, ⟨0, 0, 0#8⟩] := by decide
  have ha : TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 1 = [⟨3, 0, 1#8⟩, ⟨0, 0, 0#8⟩] := by
    decide
  have hd : TsoOfPf.histOf TsoOfPf.img0 TsoOfPf.g2OwnLog 2 = [⟨4, 1, 1#8⟩, ⟨0, 0, 0#8⟩] := by
    decide
  rw [hc, ha, hd]
  decide

/-! ## 3. The fence spot checks -/

/-- Every barrier but `fence.i`: TsoMem's post-fence floor is below WeakMem's post-fence
`wVrNew`, given `R`'s view inequalities `tv ≤ wVrNew`, `rv ≤ wVrOld`, `ownPub ≤ wVwOld`. -/
theorem TsoOfPf.fenceRow (b : barrier_kind) (pr pw sr sw : Bool) (ws : Wstate) (tv rv pub : Nat)
    (hb : ebarNow b = some (pr, pw, sr, sw)) (h1 : tv ≤ ws.wVrNew) (h2 : rv ≤ ws.wVrOld)
    (h3 : pub ≤ ws.wVwOld) :
    MachCSL.fencePost (fenceDrains b) (fenceAcq b) tv rv pub ≤
      (Weak.fencePost ws pr pw sr sw).wVrNew := by
  cases b <;> simp only [ebarNow, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hb <;>
    (try obtain ⟨rfl, rfl, rfl, rfl⟩ := hb) <;>
    simp only [MachCSL.fencePost, Weak.fencePost, fenceDrains, fenceAcq] <;> simp <;> omega

end Weak
