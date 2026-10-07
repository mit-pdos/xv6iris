/-
Weak: **B2e-3b slice 3a — candidate extension by a solo block**.

Rocq: `iris/WeakRvwmoCert.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4e ("SLICE 3's SHAPE", sub-slice 3a).
Slice 3 certifies a run by taking a realized candidate and APPENDING, one instruction block at a
time, the hart's next event at the CURRENT log.  This file is the single-block step of that
iteration, in both of its halves:

(1) THE AXIOMATIC HALF — `candSnoc` and `snocConsistent`: appending a step to an
    sRVWMO-consistent candidate keeps it sRVWMO-consistent as soon as the appended label is
    admissible at the candidate's own last replay state.  The route is
    `WeakAxiomatic3.srvwmoRealizable` out, `WeakAxiomatic2.candReachable` back in, and
    `WeakSrvwmoLitmus.srvwmoOfWf` to re-package: consistency of a candidate is EXACTLY
    machine-reachability, so extension is a purely LOCAL side condition.
(2) THE PROGRAM HALF — `execProgOk'Snoc` (+ its exclusive-pair twin): the trace-indexed supply
    `WeakAxRealize.execProgOk'` extends by one position from ONE `hemit`-shaped block for the
    acting agent (`supplyOfQconf`'s per-position obligation for a single appended block); the
    `wRelp` bridge is `hlblRealizesRelp` / `candWsRelp`.

THE TWO ADMISSIBILITY QUESTIONS (§4).  (i) A read of the LATEST in-log write is always
admissible, modulo the byte being defined at all (`latestBytesOk`): the floor is bounded by the
log length (`candLastBounded`) and nothing above `latestTs` writes the byte.  (ii) An appended
read may name an OLDER write exactly when no message strictly between it and the agent's own
per-byte floor `cdFloor` writes that byte (`snocRdAdm`) — candidate vocabulary only.

A LEAF: nothing imports this file.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below); `S k` ↦ `k + 1`; `l !! n` ↦ `l[n]?`; `seq 0 n` ↦
   `List.range' 0 n`; `default (bv_0 8) o` ↦ `o.getD 0#8`; `is_Some o` ↦ `o.isSome`;
   `<[i := p']> l` ↦ `l.set i p'`; `bool_decide (k ≤ n)` ↦ `if k ≤ n then …`; `agent` ↦ `Nat`;
   `dev_state` ↦ `Efab` (the event instance's fabric, `WeakEvPf` deviation 9 / owner decision
   Q1); `regstate` ↦ `RegFile`, `oib32` ↦ `Ibch`; `EStep i lb` ↦ `⟨i, lb⟩`; `WMsg` ↦ the
   `Wmsg` literal.  The axiomatic label constructors are written `.LLoad`/`Lbl.LLoad`
   (no `open` of either label type).
2. O2 / STAGE C — THE PINNED PROGRAM LTS (`WeakAxRealize` deviation 4, `WeakRvwmoSupply`
   deviation 2; orchestrator ruling: the Cert chain runs at `pstepPin img pstepEv`, the LTS the
   replay needs).  The fetch is an administrative label (`projLbl (LIFetch ..) = none`), so the
   realizing wlabel is never a fetch (`WeakRvwmoCert.hlblRealizesPin`), and `hlblRealizesAx` is
   `Iff.rfl` again (Stage B's `lbFetchInert` premise of `execProgOk'Snoc` is DELETED).  The supply
   `execProgOk'` of `execProgOk'Snoc` / `execProgOk'SnocPair` (premise and conclusion), of the
   smoke `smProg0` / `smSnocProg` and of `candExtendBlockNonempty` is at the PINNED LTS
   `pstepPin c.cdImg pstepEv`, and each appended block supplies the pin of its administrative
   labels: `execProgOk'Snoc` takes `∀ l0 ∈ ls, WeakAxRealize.fetchPin c.cdImg l0` (after the
   `admRun`),
   `execProgOk'SnocPair` the same for `ls1` and `ls2` (after their `admRun`s).  The realizing
   labels' pins are free (`hlblRealizesPin`, `hlblRealizesPairPin`).
3. Rocq's `Section smoke` context (`img cpu rs ib d0`) becomes explicit parameters of each smoke
   declaration (only those it uses, as Rocq's section closing does).  `cand_extend_block_nonempty`'s
   witnesses: CPU `⟨0, _⟩`, `evRs0`, `ibNone`, and Rocq's `dev0_state` ↦ the all-default fabric
   `efInit ⟨fun _ => default⟩` (as `WeakRvwmoConfWit.hartConfNonempty`).
4. §7's `Print Assumptions` audit is dropped (the lint's axiom/sorry ban is the audit).
5. Lean-only helpers: `WeakRvwmoCert.rangeMapLookup` (the lookup of a `map` over `range' 0 n`),
   `WeakRvwmoCert.hlblRealizesPin`, `WeakRvwmoCert.hlblRealizesPairPin` (deviation 2).

**Rocq → Lean name map.**  `cand_snoc` `candSnoc`, `cd_end` `cdEnd`, `cand_last_st`
`candLastSt`, `cd_log_end` `cdLogEnd`, `cand_snoc_img` `candSnocImg`, `cand_snoc_tr`
`candSnocTr`, `cd_end_snoc` `cdEndSnoc`, `cand_snoc_tr_lt` `candSnocTrLt`, `cand_snoc_tr_end`
`candSnocTrEnd`, `replay_app_le` `replayAppLe`, `cand_snoc_stt` `candSnocStt`,
`cand_snoc_last_st` `candSnocLastSt`, `cand_snoc_log` `candSnocLog`, `cd_log_end_full`
`cdLogEndFull`, `cd_log_end_snoc` `cdLogEndSnoc`, `cand_last_img` `candLastImg`,
`cand_last_log` `candLastLog`, `srvwmo_wf` `srvwmoWf`, `srvwmo_step_ok` `srvwmoStepOk`,
`snoc_consistent` `snocConsistent`, `cand_last_bounded` `candLastBounded`,
`snoc_write_consistent` `snocWriteConsistent`, `snoc_fence_consistent` `snocFenceConsistent`,
`cd_floor` `cdFloor`, `snoc_rd_adm` `snocRdAdm`, `snoc_rd_ok` `snocRdOk`,
`snoc_read_consistent` `snocReadConsistent`, `lrd_ts` `lrdTs`, `lrd_vs` `lrdVs`,
`latest_read_lbl` `latestReadLbl`, `latest_bytes_ok` `latestBytesOk`, `lrd_ts_lookup`
`lrdTsLookup`, `lrd_vs_lookup` `lrdVsLookup`, `lrd_length` `lrdLength`, `latest_snoc_rd_adm`
`latestSnocRdAdm`, `snoc_latest_consistent` `snocLatestConsistent`, `snoc_rmw_consistent`
`snocRmwConsistent`, `snoc_rmw_latest_consistent` `snocRmwLatestConsistent`, `pst_snoc`
`pstSnoc`, `dv_snoc` `dvSnoc`, `pst_snoc_le` `pstSnocLe`, `pst_snoc_gt` `pstSnocGt`,
`dv_snoc_le` `dvSnocLe`, `dv_snoc_gt` `dvSnocGt`, `exec_prog_ok'_snoc` `execProgOk'Snoc`,
`exec_prog_ok'_snoc_pair` `execProgOk'SnocPair`, `cand_last_ws_relp` `candLastWsRelp`,
`hlbl_realizes_row_end` `hlblRealizesRowEnd`, `hlbl_realizes_pair_row_end`
`hlblRealizesPairRowEnd`, `sm_c` `smC`, `sm_lb` `smLb`, `sm_consistent` `smConsistent`,
`sm_ws` `smWs`, `sm_bytes` `smBytes`, `sm_snoc_consistent` `smSnocConsistent`, `sm_snoc_log`
`smSnocLog`, `sm_pst` `smPst`, `sm_dv` `smDv`, `sm_prog0` `smProg0`, `sm_snoc_prog`
`smSnocProg`, `sm_latest_consistent` `smLatestConsistent`, `cand_extend_block_nonempty`
`candExtendBlockNonempty`.

**Dropped:** nothing (Rocq 62 declarations; Lean 62 + 3 helpers).
-/
import Weak.WeakAxiomatic3
import Weak.WeakSrvwmoLitmus
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoConfWit

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! # 1. `candSnoc` and its log / `stt` calculus -/

def candSnoc (c : Cand) (s : Estep) : Cand := ⟨c.cdImg, c.cdTr ++ [s]⟩

/-- The position the appended step occupies, and the state / log it is admitted at. -/
def cdEnd (c : Cand) : Nat := c.cdTr.length
def candLastSt (c : Cand) : Mstate := stt (candExec c) (cdEnd c)
def cdLogEnd (c : Cand) : List Wmsg := cdLog c (cdEnd c)

theorem candSnocImg (c : Cand) (s : Estep) : (candSnoc c s).cdImg = c.cdImg := rfl

theorem candSnocTr (c : Cand) (s : Estep) : (candSnoc c s).cdTr = c.cdTr ++ [s] := rfl

theorem cdEndSnoc (c : Cand) (s : Estep) : cdEnd (candSnoc c s) = cdEnd c + 1 := by
  simp [cdEnd, candSnoc]

theorem candSnocTrLt (c : Cand) (s : Estep) (k : Nat) :
    k < cdEnd c → (candSnoc c s).cdTr[k]? = c.cdTr[k]? := by
  intro hk
  exact List.getElem?_append_left hk

theorem candSnocTrEnd (c : Cand) (s : Estep) : (candSnoc c s).cdTr[cdEnd c]? = some s := by
  simp [candSnoc, cdEnd]

/-- The replay is a fold, so a longer trace agrees on every earlier state. -/
theorem replayAppLe (σ : Mstate) (tr tr' : List Estep) (k : Nat) :
    k ≤ tr.length → (replay σ (tr ++ tr'))[k]? = (replay σ tr)[k]? := by
  induction tr generalizing σ k with
  | nil =>
    intro hk
    have : k = 0 := by simp at hk; omega
    subst this
    rw [replay0, replay0]
  | cons s0 tr ih =>
    intro hk
    cases k with
    | zero => rw [replay0, replay0]
    | succ k =>
      simp only [List.cons_append, replay, List.getElem?_cons_succ]
      exact ih _ k (by simp at hk; omega)

theorem candSnocStt (c : Cand) (s : Estep) (k : Nat) :
    k ≤ cdEnd c → stt (candExec (candSnoc c s)) k = stt (candExec c) k := by
  intro hk
  show ((replay (candInit c) (c.cdTr ++ [s]))[k]?).getD msJunk =
    ((replay (candInit c) c.cdTr)[k]?).getD msJunk
  rw [replayAppLe _ _ _ _ hk]

theorem candSnocLastSt (c : Cand) (s : Estep) :
    stt (candExec (candSnoc c s)) (cdEnd c) = candLastSt c :=
  candSnocStt c s _ (Nat.le_refl _)

theorem candSnocLog (c : Cand) (s : Estep) (k : Nat) :
    k ≤ cdEnd c → cdLog (candSnoc c s) k = cdLog c k := by
  intro hk
  show trMsgs ((c.cdTr ++ [s]).take k) = trMsgs (c.cdTr.take k)
  rw [List.take_append_of_le_length hk]

theorem cdLogEndFull (c : Cand) : cdLogEnd c = trMsgs c.cdTr := cdLogFull c

/-- THE NEW LOG = THE OLD LOG ++ THE STEP'S MESSAGES. -/
theorem cdLogEndSnoc (c : Cand) (s : Estep) :
    cdLogEnd (candSnoc c s) = cdLogEnd c ++ esMsg s := by
  rw [cdLogEndFull, cdLogEndFull]
  show trMsgs (c.cdTr ++ [s]) = _
  rw [trMsgsApp]
  simp [trMsgs]

/-- The last state's image and log, in candidate vocabulary. -/
theorem candLastImg (c : Cand) : (candLastSt c).msImg = c.cdImg :=
  candEimg c _ (Nat.le_refl _)

theorem candLastLog (c : Cand) : (candLastSt c).msLog = cdLogEnd c :=
  candElog c _ (Nat.le_refl _)

/-! # 2. Consistency is exactly reachability, and extension is local -/

theorem srvwmoWf (c : Cand) : srvwmoConsistent c → execWf (candExec c) :=
  fun hc => (srvwmoRealizable c hc).1

/-- Every step of a consistent candidate is admissible at its own replay state. -/
theorem srvwmoStepOk (c : Cand) (k : Nat) (s : Estep) :
    srvwmoConsistent c → c.cdTr[k]? = some s →
    mstepOk (stt (candExec c) k) s.esAg s.esLb := by
  intro hc hs
  exact (mstepDet _ _ _ _ (execStepAt (candExec c) k s (srvwmoWf c hc) hs)).2

/-- THE EXTENSION THEOREM.  One local side condition; nothing global is re-proved. -/
theorem snocConsistent (c : Cand) (s : Estep) :
    srvwmoConsistent c →
    mstepOk (candLastSt c) s.esAg s.esLb →
    srvwmoConsistent (candSnoc c s) := by
  intro hc hok
  apply srvwmoOfWf
  refine (candReachable _ ?_).1
  intro k s' hs'
  have hlt := lookup_lt_Some hs'
  simp only [candSnoc, List.length_append, List.length_singleton] at hlt
  by_cases hk : k < cdEnd c
  · rw [candSnocTrLt c s k hk] at hs'
    rw [candSnocStt c s k (Nat.le_of_lt hk)]
    exact srvwmoStepOk c k s' hc hs'
  · have : k = cdEnd c := by unfold cdEnd at hk ⊢; omega
    subst this
    rw [candSnocTrEnd c s] at hs'
    simp only [Option.some.injEq] at hs'
    subst hs'
    rw [candSnocLastSt]
    exact hok

/-- Boundedness of the last state — it comes free from reachability. -/
theorem candLastBounded (c : Cand) : srvwmoConsistent c → cfgBounded (candLastSt c) := by
  intro hc
  exact candBoundedUpto c (cdEnd c) (Nat.le_refl _) (fun k s _ hs => srvwmoStepOk c k s hc hs)

/-! # 3. The appended write, fence and RMW -/

/-- WRITES ARE ALWAYS APPENDABLE. -/
theorem snocWriteConsistent (c : Cand) (i : Nat) (rl : Bool) (base : Int)
    (vs : List (BitVec 8)) (kc : WmClass) :
    srvwmoConsistent c → vs ≠ [] →
    srvwmoConsistent (candSnoc c ⟨i, .LStore rl base vs kc⟩) :=
  fun hc hne => snocConsistent c _ hc hne

theorem snocFenceConsistent (c : Cand) (i : Nat) (pr pw sr sw : Bool) :
    srvwmoConsistent c →
    srvwmoConsistent (candSnoc c ⟨i, .LFence pr pw sr sw⟩) :=
  fun hc => snocConsistent c _ hc trivial

/-! # 4. The admissible read label -/

/-! ## 4.1 The candidate-side read-admissibility condition -/

/-- The agent's per-byte read floor at the end of `c`. -/
def cdFloor (c : Cand) (i : Nat) (aq : Bool) (a : Int) : Nat :=
  max (loadVpre ((candLastSt c).msWs i) aq) (coh ((candLastSt c).msWs i) a)

def snocRdAdm (c : Cand) (i : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) : Prop :=
  vs.length = ts.length ∧
  -- the named source really carries the named value ...
  (∀ (j : Nat) (t : Nat) (v : BitVec 8), ts[j]? = some t → vs[j]? = some v →
     logByte c.cdImg (cdLogEnd c) t (accAddr base j) = some v) ∧
  -- ... and nothing the agent has already observed overwrites it
  (∀ (j : Nat) (t : Nat), ts[j]? = some t →
     ¬ writesIn (cdLogEnd c) (accAddr base j) t (cdFloor c i aq (accAddr base j)))

theorem snocRdOk (c : Cand) (i : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    snocRdAdm c i aq base ts vs →
    rdOk (candLastSt c).msImg (candLastSt c).msLog ((candLastSt c).msWs i) aq base ts vs := by
  rintro ⟨hlen, hval, hcoh⟩
  rw [candLastImg, candLastLog]
  refine ⟨hlen, fun j t v hj hv => ⟨hval j t v hj hv, ?_, hcoh j t hj⟩⟩
  rw [hval j t v hj hv]
  rfl

/-- THE OLDER-SOURCE VARIANT. -/
theorem snocReadConsistent (c : Cand) (i : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    srvwmoConsistent c → snocRdAdm c i aq base ts vs →
    srvwmoConsistent (candSnoc c ⟨i, .LLoad aq base ts vs⟩) :=
  fun hc hadm => snocConsistent c _ hc (snocRdOk c i aq base ts vs hadm)

/-! ## 4.2 The latest-source read label -/

def lrdTs (c : Cand) (base : Int) (n : Nat) : List Nat :=
  (List.range' 0 n).map (fun j => latestTs (cdLogEnd c) (accAddr base j))

def lrdVs (c : Cand) (base : Int) (n : Nat) : List (BitVec 8) :=
  (List.range' 0 n).map (fun j =>
    (logByte c.cdImg (cdLogEnd c) (latestTs (cdLogEnd c) (accAddr base j)) (accAddr base j)).getD
      0#8)

def latestReadLbl (c : Cand) (aq : Bool) (base : Int) (n : Nat) : Lbl :=
  .LLoad aq base (lrdTs c base n) (lrdVs c base n)

/-- The footprint's bytes exist at all — the only hypothesis (i) needs. -/
def latestBytesOk (c : Cand) (base : Int) (n : Nat) : Prop :=
  ∀ (j : Nat), j < n →
    (logByte c.cdImg (cdLogEnd c) (latestTs (cdLogEnd c) (accAddr base j))
      (accAddr base j)).isSome

/-- (Lean-only) The lookup of a `map` over `range' 0 n`. -/
theorem WeakRvwmoCert.rangeMapLookup {α : Type} (f : Nat → α) (n j : Nat) (x : α) :
    ((List.range' 0 n).map f)[j]? = some x → j < n ∧ x = f j := by
  intro h
  obtain ⟨hl, hx⟩ := List.getElem?_eq_some_iff.1 h
  simp only [List.length_map, List.length_range'] at hl
  simp only [List.getElem_map, List.getElem_range'] at hx
  exact ⟨hl, by rw [← hx]; simp⟩

theorem lrdTsLookup (c : Cand) (base : Int) (n j t : Nat) :
    (lrdTs c base n)[j]? = some t →
    j < n ∧ t = latestTs (cdLogEnd c) (accAddr base j) :=
  WeakRvwmoCert.rangeMapLookup _ n j t

theorem lrdVsLookup (c : Cand) (base : Int) (n j : Nat) (v : BitVec 8) :
    (lrdVs c base n)[j]? = some v →
    j < n ∧
    v = (logByte c.cdImg (cdLogEnd c) (latestTs (cdLogEnd c) (accAddr base j))
          (accAddr base j)).getD 0#8 :=
  WeakRvwmoCert.rangeMapLookup _ n j v

theorem lrdLength (c : Cand) (base : Int) (n : Nat) :
    (lrdVs c base n).length = (lrdTs c base n).length := by
  simp [lrdVs, lrdTs]

/-- THE ANSWER TO (i): the latest-source label always satisfies §4.1's condition. -/
theorem latestSnocRdAdm (c : Cand) (i : Nat) (aq : Bool) (base : Int) (n : Nat) :
    srvwmoConsistent c → latestBytesOk c base n →
    snocRdAdm c i aq base (lrdTs c base n) (lrdVs c base n) := by
  intro hc hb
  have hbi := candLastBounded c hc i
  rw [candLastLog] at hbi
  refine ⟨lrdLength c base n, ?_, ?_⟩
  · intro j t v hj hv
    obtain ⟨_, rfl⟩ := lrdTsLookup c base n j t hj
    obtain ⟨hjn, rfl⟩ := lrdVsLookup c base n j v hv
    have hs := hb j hjn
    cases h : logByte c.cdImg (cdLogEnd c) (latestTs (cdLogEnd c) (accAddr base j))
        (accAddr base j) with
    | none => rw [h] at hs; cases hs
    | some w => rfl
  · intro j t hj hw
    obtain ⟨_, rfl⟩ := lrdTsLookup c base n j t hj
    apply latestTsTop (cdLogEnd c) (accAddr base j)
    refine writesInMonoHi _ _ _ _ _ ?_ hw
    unfold cdFloor
    have h1 := loadVpreBounded ((candLastSt c).msWs i) aq _ hbi
    have h2 := hbi.2.2.2.2.2.2.1 (accAddr base j)
    omega

theorem snocLatestConsistent (c : Cand) (i : Nat) (aq : Bool) (base : Int) (n : Nat) :
    srvwmoConsistent c → latestBytesOk c base n →
    srvwmoConsistent (candSnoc c ⟨i, latestReadLbl c aq base n⟩) :=
  fun hc hb => snocReadConsistent c i aq base _ _ hc (latestSnocRdAdm c i aq base n hc hb)

/-! ## 4.3 The appended RMW

ATOMICITY IS THE EXTRA DEMAND: an appended read-modify-write must name the LATEST message of
every byte. -/

theorem snocRmwConsistent (c : Cand) (i : Nat) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (kc : WmClass) :
    srvwmoConsistent c → wvs ≠ [] → wvs.length = ts.length →
    snocRdAdm c i aq base ts rvs →
    (∀ (j : Nat) (t : Nat), ts[j]? = some t →
       latest c.cdImg (cdLogEnd c) (accAddr base j) t) →
    srvwmoConsistent (candSnoc c ⟨i, .LRmw aq rl base ts rvs wvs kc⟩) := by
  intro hc hne hlen hadm hlat
  apply snocConsistent c _ hc
  refine ⟨hne, hlen, snocRdOk c i aq base ts rvs hadm, ?_⟩
  show rmwLatest (candLastSt c).msImg (candLastSt c).msLog base ts
  rw [candLastImg, candLastLog]
  exact hlat

/-- … and its latest-source instance, where atomicity is free. -/
theorem snocRmwLatestConsistent (c : Cand) (i : Nat) (aq rl : Bool) (base : Int) (n : Nat)
    (wvs : List (BitVec 8)) (kc : WmClass) :
    srvwmoConsistent c → latestBytesOk c base n →
    wvs ≠ [] → wvs.length = n →
    srvwmoConsistent
      (candSnoc c ⟨i, .LRmw aq rl base (lrdTs c base n) (lrdVs c base n) wvs kc⟩) := by
  intro hc hb hne hlen
  refine snocRmwConsistent c i aq rl base _ _ wvs kc hc hne ?_
    (latestSnocRdAdm c i aq base n hc hb) ?_
  · simp [lrdTs, hlen]
  · intro j t hj
    obtain ⟨hjn, rfl⟩ := lrdTsLookup c base n j t hj
    exact latestTsLatest _ _ _ (hb j hjn)

/-! # 5. The program side -/

/-! ## 5.1 The extended supply -/

def pstSnoc (c : Cand) (pst : Nat → List Pexv6) (i : Nat) (p' : Pexv6) : Nat → List Pexv6 :=
  fun k => if k ≤ cdEnd c then pst k else (pst (cdEnd c)).set i p'

def dvSnoc (c : Cand) (dv : Nat → Efab) (d' : Efab) : Nat → Efab :=
  fun k => if k ≤ cdEnd c then dv k else d'

theorem pstSnocLe (c : Cand) (pst : Nat → List Pexv6) (i : Nat) (p' : Pexv6) (k : Nat) :
    k ≤ cdEnd c → pstSnoc c pst i p' k = pst k := by
  intro h; simp [pstSnoc, h]

theorem pstSnocGt (c : Cand) (pst : Nat → List Pexv6) (i : Nat) (p' : Pexv6) (k : Nat) :
    cdEnd c < k → pstSnoc c pst i p' k = (pst (cdEnd c)).set i p' := by
  intro h; simp [pstSnoc, show ¬ k ≤ cdEnd c by omega]

theorem dvSnocLe (c : Cand) (dv : Nat → Efab) (d' : Efab) (k : Nat) :
    k ≤ cdEnd c → dvSnoc c dv d' k = dv k := by
  intro h; simp [dvSnoc, h]

theorem dvSnocGt (c : Cand) (dv : Nat → Efab) (d' : Efab) (k : Nat) :
    cdEnd c < k → dvSnoc c dv d' k = d' := by
  intro h; simp [dvSnoc, show ¬ k ≤ cdEnd c by omega]

/-- (Lean-only, deviation 2) The realizing wlabel is never a fetch: it is pinned to any image. -/
theorem WeakRvwmoCert.hlblRealizesPin (im : Image) (p : Pexv6) (ws : Wstate) (lb : Lbl)
    (l : Wlabel) : hlblRealizes p ws lb l → WeakAxRealize.fetchPin im l := by
  rintro ⟨-, -, -, hpr⟩
  cases l with
  | LIFetch base tvs => simp [projLbl] at hpr
  | _ => trivial

/-- (Lean-only, deviation 2) … and neither end of a fused pair is. -/
theorem WeakRvwmoCert.hlblRealizesPairPin (im : Image) (p pm : Pexv6) (ws : Wstate) (lb : Lbl)
    (l1 l2 : Wlabel) :
    hlblRealizesPair p pm ws lb l1 l2 →
      WeakAxRealize.fetchPin im l1 ∧ WeakAxRealize.fetchPin im l2 := by
  rintro ⟨_, _, _, _, _, _, _, _, rfl, rfl, -⟩
  exact ⟨trivial, trivial⟩

/-- THE PROGRAM-SIDE EXTENSION THEOREM (the `HEone` block shape).  Deviation 2: the pinned LTS;
the block's administrative labels are pinned. -/
theorem execProgOk'Snoc (c : Cand) (i : Nat) (p pa : Pexv6) (da : Efab) (ls : List Wlabel)
    (l : Wlabel) (lb : Lbl) (p' : Pexv6) (d' : Efab) (pst : Nat → List Pexv6)
    (dv : Nat → Efab) :
    execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst dv (candExec c) →
    (pst (cdEnd c))[i]? = some p →
    admRun true p (dv (cdEnd c)) ls pa da →
    (∀ l0, l0 ∈ ls → WeakAxRealize.fetchPin c.cdImg l0) →
    hlblRealizes pa ((candLastSt c).msWs i) lb l →
    pstepEv pa da l p' d' →
    execProgOk' (pstepPin c.cdImg pstepEv) pclsEv (pstSnoc c pst i p') (dvSnoc c dv d')
      (candExec (candSnoc c ⟨i, lb⟩)) := by
  intro hpo hp hrun hpin hre hst k s hs
  change (c.cdTr ++ [⟨i, lb⟩])[k]? = some s at hs
  have hlt := lookup_lt_Some hs
  simp only [List.length_append, List.length_singleton] at hlt
  by_cases hk : k < cdEnd c
  · have hs' : c.cdTr[k]? = some s := by
      rw [← candSnocTrLt c ⟨i, lb⟩ k hk]; exact hs
    obtain ⟨q, qa, qd, q', h1, h2, h3, h4⟩ := hpo k s hs'
    refine ⟨q, qa, qd, q', ?_⟩
    rw [pstSnocLe c pst i p' k (by omega), pstSnocLe c pst i p' (k + 1) (by omega),
      dvSnocLe c dv d' k (by omega), dvSnocLe c dv d' (k + 1) (by omega),
      candSnocStt c _ k (by omega)]
    exact ⟨h1, h2, h3, h4⟩
  · have : k = cdEnd c := by unfold cdEnd at hk ⊢; omega
    subst this
    have hs2 := candSnocTrEnd c ⟨i, lb⟩
    change (c.cdTr ++ [⟨i, lb⟩])[cdEnd c]? = some ⟨i, lb⟩ at hs2
    rw [hs2, Option.some.injEq] at hs
    subst hs
    refine ⟨p, pa, da, p', ?_⟩
    rw [pstSnocLe c pst i p' (cdEnd c) (Nat.le_refl _),
      pstSnocGt c pst i p' (cdEnd c + 1) (by omega),
      dvSnocLe c dv d' (cdEnd c) (Nat.le_refl _), dvSnocGt c dv d' (cdEnd c + 1) (by omega),
      candSnocLastSt]
    exact ⟨hp, rfl, admRunPin _ _ _ _ _ _ _ hrun hpin,
      Or.inl ⟨l, (hlblRealizesAx _ _ _ _ _).2 hre,
        hst, WeakRvwmoCert.hlblRealizesPin _ _ _ _ _ hre⟩⟩

/-- … and the `HEpair` block shape (a fused exclusive pair).  Deviation 2. -/
theorem execProgOk'SnocPair (c : Cand) (i : Nat) (p pa : Pexv6) (da : Efab)
    (ls1 : List Wlabel) (l1 l2 : Wlabel) (lb : Lbl) (pm : Pexv6) (dm : Efab)
    (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab) (p' : Pexv6) (d' : Efab)
    (pst : Nat → List Pexv6) (dv : Nat → Efab) :
    execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst dv (candExec c) →
    (pst (cdEnd c))[i]? = some p →
    admRun true p (dv (cdEnd c)) ls1 pa da →
    (∀ l0, l0 ∈ ls1 → WeakAxRealize.fetchPin c.cdImg l0) →
    hlblRealizesPair pa pm2 ((candLastSt c).msWs i) lb l1 l2 →
    pstepEv pa da l1 pm dm →
    admRun false pm dm ls2 pm2 dm2 →
    (∀ l0, l0 ∈ ls2 → WeakAxRealize.fetchPin c.cdImg l0) →
    pstepEv pm2 dm2 l2 p' d' →
    execProgOk' (pstepPin c.cdImg pstepEv) pclsEv (pstSnoc c pst i p') (dvSnoc c dv d')
      (candExec (candSnoc c ⟨i, lb⟩)) := by
  intro hpo hp hrun hpin1 hre hs1 hrun2 hpin2 hs2 k s hs
  change (c.cdTr ++ [⟨i, lb⟩])[k]? = some s at hs
  have hlt := lookup_lt_Some hs
  simp only [List.length_append, List.length_singleton] at hlt
  by_cases hk : k < cdEnd c
  · have hs' : c.cdTr[k]? = some s := by
      rw [← candSnocTrLt c ⟨i, lb⟩ k hk]; exact hs
    obtain ⟨q, qa, qd, q', h1, h2, h3, h4⟩ := hpo k s hs'
    refine ⟨q, qa, qd, q', ?_⟩
    rw [pstSnocLe c pst i p' k (by omega), pstSnocLe c pst i p' (k + 1) (by omega),
      dvSnocLe c dv d' k (by omega), dvSnocLe c dv d' (k + 1) (by omega),
      candSnocStt c _ k (by omega)]
    exact ⟨h1, h2, h3, h4⟩
  · have : k = cdEnd c := by unfold cdEnd at hk ⊢; omega
    subst this
    have hse := candSnocTrEnd c ⟨i, lb⟩
    change (c.cdTr ++ [⟨i, lb⟩])[cdEnd c]? = some ⟨i, lb⟩ at hse
    rw [hse, Option.some.injEq] at hs
    subst hs
    refine ⟨p, pa, da, p', ?_⟩
    rw [pstSnocLe c pst i p' (cdEnd c) (Nat.le_refl _),
      pstSnocGt c pst i p' (cdEnd c + 1) (by omega),
      dvSnocLe c dv d' (cdEnd c) (Nat.le_refl _), dvSnocGt c dv d' (cdEnd c + 1) (by omega),
      candSnocLastSt]
    have hpp := WeakRvwmoCert.hlblRealizesPairPin c.cdImg _ _ _ _ _ _ hre
    exact ⟨hp, rfl, admRunPin _ _ _ _ _ _ _ hrun hpin1,
      Or.inr ⟨pm, dm, pm2, dm2, l1, l2, (hlblRealizesPairAx _ _ _ _ _ _ _).1 hre, ⟨hs1, hpp.1⟩,
        admRunPin _ _ _ _ _ _ _ hrun2 hpin2, ⟨hs2, hpp.2⟩⟩⟩

/-! ## 5.2 The relp bridge -/

theorem candLastWsRelp (c : Cand) (i : Nat) :
    ((candLastSt c).msWs i).wRelp = (rowWs (trow i c.cdTr) (tcnt i c.cdTr)).wRelp := by
  have hte : c.cdTr.take (cdEnd c) = c.cdTr := take_ge (Nat.le_refl _)
  unfold candLastSt
  rw [candWsRelp c i (cdEnd c) (Nat.le_refl _), hte]

theorem hlblRealizesRowEnd (c : Cand) (i : Nat) (p : Pexv6) (lb : Lbl) (l : Wlabel) :
    hlblRealizes p (rowWs (trow i c.cdTr) (tcnt i c.cdTr)) lb l →
    hlblRealizes p ((candLastSt c).msWs i) lb l :=
  hlblRealizesRelp _ _ _ _ _ (candLastWsRelp c i)

theorem hlblRealizesPairRowEnd (c : Cand) (i : Nat) (p pm : Pexv6) (lb : Lbl)
    (l1 l2 : Wlabel) :
    hlblRealizesPair p pm (rowWs (trow i c.cdTr) (tcnt i c.cdTr)) lb l1 l2 →
    hlblRealizesPair p pm ((candLastSt c).msWs i) lb l1 l2 :=
  hlblRealizesPairRelp _ _ _ _ _ _ _ (candLastWsRelp c i)

/-! # 6. Smoke / non-vacuity

A CONCRETE extension, with the real machine's block: the `sw &started` store of xv6's `main`
(`WeakRvwmoConfWit`'s `ev*` objects), appended to the empty candidate over an arbitrary boot
image.  Both halves are instantiated, and the appended message is COMPUTED. -/

/-- The candidate before the block: empty trace over `img`. -/
def smC (img : Image) : Cand := ⟨img, []⟩

/-- The axiomatic label of the block (`WeakRvwmoConfWit.evRow`'s only element). -/
def smLb : Lbl := .LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne) .WCplain

theorem smConsistent (img : Image) : srvwmoConsistent (smC img) := by
  apply srvwmoOfWf
  refine (candReachable _ ?_).1
  intro k s hs
  simp [smC] at hs

theorem smWs (img : Image) : (candLastSt (smC img)).msWs 0 = wsInit := by
  unfold candLastSt
  rw [sttLookup _ _ _ (replay0 (candInit (smC img)) (smC img).cdTr)]
  rfl

theorem smBytes : WeakInterpProj.wbytes 4 lockOne ≠ [] := by
  intro h
  have hl := wbytesLength 4 lockOne
  rw [h] at hl
  simp at hl

/-- (a) THE AXIOMATIC HALF. -/
theorem smSnocConsistent (img : Image) : srvwmoConsistent (candSnoc (smC img) ⟨0, smLb⟩) :=
  snocWriteConsistent _ 0 false _ _ .WCplain (smConsistent img) smBytes

/-- … and the extended log, COMPUTED: one message, the real store's. -/
theorem smSnocLog (img : Image) :
    cdLogEnd (candSnoc (smC img) ⟨0, smLb⟩)
      = [⟨paZ evFlag, WeakInterpProj.wbytes 4 lockOne, some 0, .WCplain⟩] := by
  rw [cdLogEndSnoc]
  rfl

/-- (b) THE PROGRAM HALF. -/
noncomputable def smPst (cpu : CPU) (rs : RegFile) (ib : Ibch) : Nat → List Pexv6 :=
  fun _ => [evP0 cpu rs ib]

def smDv (d0 : Efab) : Nat → Efab := fun _ => d0

theorem smProg0 (img : Image) (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : Efab) :
    execProgOk' (pstepPin img pstepEv) pclsEv (smPst cpu rs ib) (smDv d0)
      (candExec (smC img)) := by
  intro k s hs
  change ([] : List Estep)[k]? = some s at hs
  simp at hs

theorem smSnocProg (img : Image) (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : Efab) :
    execProgOk' (pstepPin img pstepEv) pclsEv
      (pstSnoc (smC img) (smPst cpu rs ib) 0 (evP1 cpu rs ib))
      (dvSnoc (smC img) (smDv d0) d0)
      (candExec (candSnoc (smC img) ⟨0, smLb⟩)) :=
  execProgOk'Snoc (smC img) 0 (evP0 cpu rs ib) (evP0 cpu rs ib) d0 [] (evWl ib) smLb
    (evP1 cpu rs ib) d0 (smPst cpu rs ib) (smDv d0)
    (smProg0 img cpu rs ib d0) rfl (.ARnil _ _) (fun _ h => absurd h List.not_mem_nil)
    (by rw [smWs]; exact evRealizes cpu rs ib) (evPstep cpu rs ib d0)

/-- The LATEST-source read is non-vacuous too: over a TOTAL image the latest-source label of ANY
footprint is appendable, at any agent and any annotation. -/
theorem smLatestConsistent (i : Nat) (aq : Bool) (base : Int) (n : Nat) :
    srvwmoConsistent
      (candSnoc (smC (fun _ => some 0#8))
        ⟨i, latestReadLbl (smC (fun _ => some 0#8)) aq base n⟩) := by
  apply snocLatestConsistent _ _ _ _ _ (smConsistent _)
  intro j _
  have hl : cdLogEnd (smC (fun _ => some 0#8)) = [] := rfl
  rw [hl, latestTsNil]
  rfl

/-- THE POINT, with the objects hidden: the two extension theorems are JOINTLY inhabited at a
real, nonempty block. -/
theorem candExtendBlockNonempty :
    ∃ (c : Cand) (s : Estep) (pst : Nat → List Pexv6) (dv : Nat → Efab),
      c.cdTr = [] ∧
      srvwmoConsistent (candSnoc c s) ∧
      cdLogEnd (candSnoc c s) ≠ [] ∧
      execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst dv (candExec (candSnoc c s)) :=
  ⟨smC (fun _ => none), ⟨0, smLb⟩,
    pstSnoc (smC (fun _ => none)) (smPst ⟨0, by decide⟩ evRs0 ibNone) 0
      (evP1 ⟨0, by decide⟩ evRs0 ibNone),
    dvSnoc (smC (fun _ => none)) (smDv (efInit ⟨fun _ => default⟩)) (efInit ⟨fun _ => default⟩),
    rfl, smSnocConsistent _, by rw [smSnocLog]; simp, smSnocProg _ _ _ _ _⟩

end Weak
