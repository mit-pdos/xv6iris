/-
Weak: **allocproc route P — [R46.4] `blockedIsCensus`: a plain-load head that is not a census site
passes the value gate** (`notes/weak-allocproc-plan-review-R46.md` §3 "where the hunt's completeness
rests" (i), §7 [R46.4]; PROGRESS-W2-blocked.md).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing
registered imports this file.

**Spec, stated first.**  riscv.cat's load value axiom: a read returns, per byte, the gmo-latest write
among those gmo-before or po-before it.  In the gated walk (`SbOrd`) a plain-load head passes the value
gate (`SbOrd.valGate`: the member's TOP bytes are GF's) as soon as every byte's GF source is FORWARDED
(an own pending store, the youngest of the row at the byte — rule 1 + the load value axiom) or LANDED
(then it is the member-latest, `PInv.rd`).  So a BLOCKED head is a read some byte of which is sourced
by a FOREIGN write that is pending or unissued.  This file makes the "non-census loads are never
blocked" half of §HEADHOP's transport (T) explicit: it proves that a byte is landed whenever its GF
source is reached from the head's realized prefix by a chain of RVWMO ordering facts the walk
machine honours, and it NAMES the per-head classification the realization owes (`NonCensusSrc`).

  §1  structural invariants of EVERY walk state (`SbBlocked.St`, `stStAt`; no validity needed):
      pending tags below the row length and in issue order, and each entry's fence counter `fs` is
      the number of member `pw ∧ sw` fences of its row after it (`fsCnt`).
  §2  history invariants of every state of a VALID candidate (`histStAt`):
      **(EP) `EpochOk`** — no pending entry has a member `pw ∧ sw` fence between it and a LANDED write
      of its row (rule 4 as the epoch buffer enforces it: `SbPol.epochOk` at a landing, `amoOk` at an
      AMO); **(DR) `DrainOk`** — no pending entry is po-before a realized DRAINING fence (`pw ∧ sr`:
      the fence waits for an empty buffer).  (DR) is the `drainLanded` clause of [R46.6], here a
      theorem about reachable states — no `PInv`/`SbOrd` edit.
  §3  `SbBlocked.Landed` (realized, not pending) and **the chain `SbBlocked.Hb`** rooted at the head's
      realized prefix: program order, fabric order (`PInv.dvP`), a realized AMO's byte source
      (`amoSrcLanded`: atomicity puts it gmo-before the AMO's landed write), the release epoch
      (`epochLanded`, from (EP)), the draining fence (`drainLanded`, from (DR)); **`hbSound`**.
  §4  own sources: `ownPo` (an own GF source is po-before the read — rule 1), **`ownFwd`** (a pending
      own source is the youngest own entry at the byte, so the byte is forwarded with GF's value).
  §5  **`SbBlocked.blockedIsCensus`** (every byte image / own / `Hb`-landed ⇒ `srcGate` ⇒ `valGate`),
      its reachable-state form `blockedIsCensusC`, the NAMED transport input **`NonCensusSrc`**, and
      **`headOrdRdOfCensus`** (row H3 from the per-census-site table alone).

How R46 §3's informal arms map: "own source ⇒ forwarded" = `ownFwd` / the landed branch; "chained source
⇒ hop AMO realized ⇒ release landed ⇒ epoch ⇒ landed" = `Hb.root`/`po` + `Hb.amo` + `Hb.epoch`; "device
source ⇒ landed at issue" is NOT a walk fact (device-row stores are buffered like any store) — the
faithful replacement is the device's `DFence` (`LFence true true true true`, draining): `Hb.drain`, with
the `DFence` realized through program / fabric order (`Hb.po`/`Hb.fab`; finding F-W2-BC-1); "an unissued
foreign source is excluded" = an `Hb`-landed write is realized (`hbSound`), so a source the chain reaches
is never unissued — producing the chain is the realization's lock / fabric discipline (named).

Spec mark: FAITHFUL (proof organisation over riscv.cat rules 1, 4, load value, atomicity and the
fabric order as the walk honours them).  The one NAMED input, `NonCensusSrc` (the classification of
non-census heads' sources), is FAITHFUL (true of xv6 runs by the lock / custody / fabric discipline) and
WEAKER while named; it is a GF + realized-prefix statement, never a statement about the finished member
(so not circular with `noStuckP`).  Lean-only helpers `SbBlocked.*`.
-/
import Weak.SbHeadHop2
import Weak.WeakRvwmoLock
import Weak.SbOrdWalk

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. Structural invariants of every walk state -/

/-- A `pw ∧ sw` fence label (an epoch boundary of the buffer). -/
def SbBlocked.isFsw : Lbl → Bool
  | LFence _ true _ true => true
  | _ => false

/-- The number of `pw ∧ sw` fences in `rows` at positions `≥ j`. -/
def SbBlocked.fsCnt (rows : List Lbl) (j : Nat) : Nat := ((rows.drop j).filter SbBlocked.isFsw).length

theorem SbBlocked.fsCntSucc (rows : List Lbl) (j : Nat) (l : Lbl) (h : rows[j]? = some l) :
    SbBlocked.fsCnt rows j = (if SbBlocked.isFsw l then 1 else 0) + SbBlocked.fsCnt rows (j + 1) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 h
  unfold SbBlocked.fsCnt
  rw [List.drop_eq_getElem_cons hlt, hget, List.filter_cons]
  cases SbBlocked.isFsw l <;> simp <;> omega

theorem SbBlocked.fsCntLen (rows : List Lbl) (j : Nat) (hj : rows.length ≤ j) :
    SbBlocked.fsCnt rows j = 0 := by
  unfold SbBlocked.fsCnt; rw [List.drop_eq_nil_of_le hj]; rfl

theorem SbBlocked.fsCntMono1 (rows : List Lbl) (j : Nat) :
    SbBlocked.fsCnt rows (j + 1) ≤ SbBlocked.fsCnt rows j := by
  cases h : rows[j]? with
  | none =>
    have hj : rows.length ≤ j := by
      rcases Nat.lt_or_ge j rows.length with hl | hl
      · rw [List.getElem?_eq_getElem hl] at h; cases h
      · exact hl
    rw [SbBlocked.fsCntLen rows j hj, SbBlocked.fsCntLen rows (j + 1) (by omega)]
    exact Nat.le_refl 0
  | some l => rw [SbBlocked.fsCntSucc rows j l h]; omega

theorem SbBlocked.fsCntMono (rows : List Lbl) (j : Nat) :
    ∀ d, SbBlocked.fsCnt rows (j + d) ≤ SbBlocked.fsCnt rows j
  | 0 => Nat.le_refl _
  | d + 1 => Nat.le_trans (SbBlocked.fsCntMono1 rows (j + d)) (SbBlocked.fsCntMono rows j d)

theorem SbBlocked.fsCntLe (rows : List Lbl) (a b : Nat) (hab : a ≤ b) :
    SbBlocked.fsCnt rows b ≤ SbBlocked.fsCnt rows a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact SbBlocked.fsCntMono rows a d

/-- A `pw ∧ sw` fence at `kf ∈ [j, m)` makes the count drop. -/
theorem SbBlocked.fsCntGap (rows : List Lbl) (j kf m : Nat) (l : Lbl) (hl : rows[kf]? = some l)
    (hf : SbBlocked.isFsw l = true) (hj : j ≤ kf) (hm : kf < m) :
    SbBlocked.fsCnt rows m + 1 ≤ SbBlocked.fsCnt rows j := by
  have h1 := SbBlocked.fsCntLe rows j kf hj
  have h2 := SbBlocked.fsCntSucc rows kf l hl
  have h3 := SbBlocked.fsCntLe rows (kf + 1) m hm
  rw [if_pos hf] at h2
  omega

theorem SbBlocked.fsCntApp (rows : List Lbl) (l : Lbl) (j : Nat) (hj : j ≤ rows.length) :
    SbBlocked.fsCnt (rows ++ [l]) j = SbBlocked.fsCnt rows j + (if SbBlocked.isFsw l then 1 else 0) := by
  unfold SbBlocked.fsCnt
  rw [List.drop_append_of_le_length hj, List.filter_append, List.length_append]
  cases h : SbBlocked.isFsw l <;> simp [h]

/-- **THE STRUCTURAL INVARIANT** (every walk state, valid or not). -/
structure SbBlocked.St (w : WS) : Prop where
  lt : ∀ u p, p ∈ w.pend u → p.1 < (w.rows u).length
  ord : ∀ u, ((w.pend u).map Prod.fst).Pairwise (· < ·)
  fs : ∀ u p, p ∈ w.pend u → p.2.fs = SbBlocked.fsCnt (w.rows u) (p.1 + 1)

/-- Where a pending entry after an event comes from: an old entry with the same tag, or the new issue. -/
theorem SbBlocked.pendBack (w : WS) (s : Estep) (j : Nat) (p : Nat × SbEnt) :
    p ∈ (nextI w (.ev s)).pend j →
    (∃ q, q ∈ w.pend j ∧ q.1 = p.1) ∨ (j = s.esAg ∧ p.1 = (w.rows j).length) := by
  intro hp
  rw [pendEvEq] at hp
  by_cases hj : j = s.esAg
  · rw [if_pos hj] at hp
    subst hj
    rcases pendECases w s.esAg s.esLb with ⟨rl, base, vs, k, -, he⟩ | ⟨pr, sr, -, he⟩ | he <;>
      rw [he] at hp
    · rcases List.mem_append.1 hp with hp | hp
      · exact .inl ⟨p, hp, rfl⟩
      · simp only [List.mem_singleton] at hp
        exact .inr ⟨rfl, by rw [hp]⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact .inl ⟨q, hq, rfl⟩
    · exact .inl ⟨p, hp, rfl⟩
  · rw [if_neg hj] at hp
    exact .inl ⟨p, hp, rfl⟩

theorem SbBlocked.rowsBack (w : WS) (s : Estep) (j n : Nat) (hn : n < (w.rows j).length) :
    ((nextI w (.ev s)).rows j)[n]? = (w.rows j)[n]? := by
  rw [rowsEvEq]
  split
  · exact lookup_app_l hn
  · rfl

theorem SbBlocked.stEv (w : WS) (s : Estep) (h : SbBlocked.St w) : SbBlocked.St (nextI w (.ev s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j p hp
    rw [rowsEvEq]
    rcases SbBlocked.pendBack w s j p hp with ⟨q, hq, hq1⟩ | ⟨hj, hp1⟩
    · have := h.lt j q hq
      split
      · rw [List.length_append, List.length_singleton]; omega
      · omega
    · rw [if_pos hj, List.length_append, List.length_singleton]; omega
  · intro j
    rw [pendEvEq]
    by_cases hj : j = s.esAg
    · rw [if_pos hj]
      subst hj
      rcases pendECases w s.esAg s.esLb with ⟨rl, base, vs, k, -, he⟩ | ⟨pr, sr, -, he⟩ | he <;> rw [he]
      · rw [List.map_append, List.pairwise_append]
        refine ⟨h.ord _, by simp, ?_⟩
        intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
        exact h.lt _ q hq
      · rw [List.map_map]
        exact h.ord _
      · exact h.ord _
    · rw [if_neg hj]; exact h.ord j
  · intro j p hp
    rw [pendEvEq] at hp
    rw [rowsEvEq]
    by_cases hj : j = s.esAg
    · rw [if_pos hj] at hp ⊢
      subst hj
      obtain ⟨u, lb⟩ := s
      dsimp only at hp ⊢
      have hold : ∀ q, q ∈ w.pend u → SbBlocked.fsCnt (w.rows u ++ [lb]) (q.1 + 1) =
          q.2.fs + (if SbBlocked.isFsw lb then 1 else 0) := by
        intro q hq
        rw [SbBlocked.fsCntApp _ _ _ (by have := h.lt u q hq; omega), h.fs u q hq]
      cases lb with
      | LStore rl base vs k =>
        change p ∈ w.pend u ++ [((w.rows u).length, SbCand.issueEnt w.σ u rl base vs k)] at hp
        rcases List.mem_append.1 hp with hp | hp
        · rw [hold p hp]; rfl
        · simp only [List.mem_singleton] at hp
          subst hp
          rw [SbBlocked.fsCntLen _ _ (by simp)]
          rfl
      | LFence pr pw sr sw =>
        by_cases hfw : pw = true ∧ sw = true
        · obtain ⟨rfl, rfl⟩ := hfw
          have he : pendE w u (LFence pr true sr true) = (w.pend u).map (fun p => (p.1, p.2.bump)) := by
            simp [pendE]
          rw [he] at hp
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          show q.2.bump.fs = SbBlocked.fsCnt _ (q.1 + 1)
          rw [hold q hq]
          rfl
        · have he : pendE w u (LFence pr pw sr sw) = w.pend u := by
            cases pw <;> cases sw <;> simp_all [pendE]
          have hf0 : SbBlocked.isFsw (LFence pr pw sr sw) = false := by
            cases pw <;> cases sw <;> simp_all [SbBlocked.isFsw]
          rw [he] at hp
          rw [hold p hp, hf0]
          rfl
      | LLoad aq base ts vs =>
        change p ∈ w.pend u at hp
        rw [hold p hp]; rfl
      | LRmw aq rl base ts rvs wvs k =>
        change p ∈ w.pend u at hp
        rw [hold p hp]; rfl
      | LIo kd base vs =>
        change p ∈ w.pend u at hp
        rw [hold p hp]; rfl
    · rw [if_neg hj] at hp ⊢; exact h.fs j p hp

theorem SbBlocked.stLand (w : WS) (i k : Nat) (h : SbBlocked.St w) :
    SbBlocked.St (nextI w (.land i k)) := by
  cases hp : (w.pend i)[k]? with
  | none => simp only [nextI, hp]; exact h
  | some p =>
    rw [landEq i k p hp]
    refine ⟨fun j q hq => ?_, fun j => ?_, fun j q hq => ?_⟩
    · exact h.lt j q (pendLandMem i k p hp j q (by rw [landEq i k p hp]; exact hq))
    · show ((upd w.pend i ((w.pend i).eraseIdx k) j).map Prod.fst).Pairwise _
      by_cases hj : j = i
      · subst hj; rw [updEq]
        exact (h.ord j).sublist ((List.eraseIdx_sublist _ _).map _)
      · rw [updNe _ _ _ _ hj]; exact h.ord j
    · exact h.fs j q (pendLandMem i k p hp j q (by rw [landEq i k p hp]; exact hq))

/-- **THE STRUCTURAL INVARIANT HOLDS AT EVERY STATE OF EVERY CANDIDATE.** -/
theorem SbBlocked.stStAt (c : CandW) : ∀ k, SbBlocked.St (stAt c k)
  | 0 => ⟨fun _ _ h => by simp [stAt, init] at h, fun _ => by simp [stAt, init],
      fun _ _ h => by simp [stAt, init] at h⟩
  | k + 1 => by
    cases hk : c.its[k]? with
    | none =>
      show SbBlocked.St (match c.its[k]? with
        | some it => nextI (stAt c k) it
        | none => stAt c k)
      rw [hk]; exact SbBlocked.stStAt c k
    | some it =>
      rw [stAtSucc c k it hk]
      cases it with
      | ev s => exact SbBlocked.stEv _ s (SbBlocked.stStAt c k)
      | land i j => exact SbBlocked.stLand _ i j (SbBlocked.stStAt c k)

/-! # 2. History invariants of every state of a valid candidate -/

/-- **(EP)** no pending entry of row `i` has a member `pw ∧ sw` fence between it and a LANDED write
(`w.gmo` member with a write label) of row `i`. -/
def SbBlocked.EpochOk (w : WS) : Prop :=
  ∀ i p r, p ∈ w.pend i → r ∈ w.gmo → r.1 = i → p.1 < r.2 →
    (∃ l, (w.rows i)[r.2]? = some l ∧ lbIsW l = true) →
    ∀ kf l, p.1 < kf → kf < r.2 → (w.rows i)[kf]? = some l → SbBlocked.isFsw l = true → False

/-- **(DR)** no pending entry of row `i` is po-before a realized draining fence (`pw ∧ sr`) of row `i`. -/
def SbBlocked.DrainOk (w : WS) : Prop :=
  ∀ i p f pr sw, p ∈ w.pend i → p.1 < f → (w.rows i)[f]? = some (LFence pr true true sw) → False

theorem SbBlocked.amoOkOf {σ σ' : SbCand.CandS} {i : Nat} {aq rl : Bool} {base : Int} {ts : List Nat}
    {rvs wvs : List (BitVec 8)} {k : WmClass} (h : SbCand.stepE σ i (LRmw aq rl base ts rvs wvs k) σ') :
    SbCand.amoOk (σ.sb i) base ts.length := by
  cases h; assumption

theorem SbBlocked.drainOf {σ σ' : SbCand.CandS} {i : Nat} {pr pw sr sw : Bool}
    (h : SbCand.stepE σ i (LFence pr pw sr sw) σ') : SbCand.drains pw sr = true → σ.sb i = [] := by
  cases h; assumption

theorem SbBlocked.mapSndNil (l : List (Nat × SbEnt)) : l.map Prod.snd = [] → l = [] := by
  cases l with
  | nil => intro _; rfl
  | cons a l => intro h; simp at h

theorem SbBlocked.epEv (img : Image) (w : WS) (s : Estep) (hI : Inv img w) (hS : SbBlocked.St w)
    (hE : SbBlocked.EpochOk w)
    (hok : SbCand.stepE w.σ s.esAg s.esLb (SbCand.nextE w.σ s.esAg s.esLb)) :
    SbBlocked.EpochOk (nextI w (.ev s)) := by
  intro i p r hp hr hri hlt hwr kf l hk1 hk2 hkl hf
  have hgmo : (nextI w (.ev s)).gmo =
      if gmoEv s.esLb then w.gmo ++ [(s.esAg, (w.rows s.esAg).length)] else w.gmo := rfl
  have hold : r ∈ w.gmo → False := by
    intro hr0
    obtain ⟨l0, hl0, -⟩ := hI.gmoMem r hr0
    have hrlen : r.2 < (w.rows i).length := by rw [← hri]; exact lookup_lt_Some hl0
    rw [SbBlocked.rowsBack w s i r.2 hrlen] at hwr
    rw [SbBlocked.rowsBack w s i kf (by omega)] at hkl
    rcases SbBlocked.pendBack w s i p hp with ⟨q, hq, hq1⟩ | ⟨-, hp1⟩
    · exact hE i q r hq hr0 hri (by omega) hwr kf l (by omega) hk2 hkl hf
    · omega
  rw [hgmo] at hr
  by_cases hgm : gmoEv s.esLb = true
  · rw [if_pos hgm] at hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hold hr
    · simp only [List.mem_singleton] at hr
      subst hr
      dsimp only at hri hlt hk2 hwr
      subst hri
      obtain ⟨l', hl', hW⟩ := hwr
      rw [rowsEvEq, if_pos rfl, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hl'
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl'
      subst hl'
      obtain ⟨u, lb⟩ := s
      dsimp only at *
      obtain ⟨aq, rl, base, ts, rvs, wvs, k, rfl⟩ :
          ∃ aq rl base ts rvs wvs k, lb = LRmw aq rl base ts rvs wvs k := by
        rcases lb with _ | _ | _ | ⟨aq, rl, base, ts, rvs, wvs, k⟩ | _
        all_goals first
          | exact ⟨aq, rl, base, ts, rvs, wvs, k, rfl⟩
          | simp [gmoEv, isSt, lbIsW, lbIsMem] at hgm hW
      have hpe : (nextI w (.ev ⟨u, LRmw aq rl base ts rvs wvs k⟩)).pend u = w.pend u := by
        rw [pendEvEq, if_pos rfl]; rfl
      rw [hpe] at hp
      have hok' := SbBlocked.amoOkOf hok
      have hfs0 : p.2.fs = 0 := (hok' p.2 (by rw [hI.sb u]; exact List.mem_map.2 ⟨p, hp, rfl⟩)).1
      rw [SbBlocked.rowsBack _ _ u kf hk2] at hkl
      have hgap := SbBlocked.fsCntGap (w.rows u) (p.1 + 1) kf (w.rows u).length l hkl hf (by omega) hk2
      rw [← hS.fs u p hp, hfs0] at hgap
      omega
  · rw [if_neg hgm] at hr; exact hold hr

theorem SbBlocked.epLand (img : Image) (w : WS) (i0 k : Nat) (hI : Inv img w) (hS : SbBlocked.St w)
    (hE : SbBlocked.EpochOk w) (hok : SbPol.epoch.landOk (w.σ.sb i0) k) :
    SbBlocked.EpochOk (nextI w (.land i0 k)) := by
  cases hq : (w.pend i0)[k]? with
  | none => simp only [nextI, hq]; exact hE
  | some q =>
    intro i p r hp hr hri hlt hwr kf l hk1 hk2 hkl hf
    have hp0 : p ∈ w.pend i := pendLandMem i0 k q hq i p hp
    rw [landEq i0 k q hq] at hr hwr hkl
    dsimp only at hr hwr hkl
    rcases List.mem_append.1 hr with hr | hr
    · exact hE i p r hp0 hr hri hlt hwr kf l hk1 hk2 hkl hf
    · simp only [List.mem_singleton] at hr
      subst hr
      dsimp only at hri hlt hk2
      subst hri
      obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.1 hp0
      have hkk : k' < k := by
        rcases Nat.lt_trichotomy k' k with h | h | h
        · exact h
        · subst h; rw [hq] at hk'; cases hk'; omega
        · have := pairwiseLt _ k k' q.1 p.1 (hS.ord _) (by rw [List.getElem?_map, hq]; rfl)
            (by rw [List.getElem?_map, hk']; rfl) h
          omega
      have hok2 : SbPol.epochOk (w.σ.sb i0) k := hok
      have hfs := (hok2.2 k' p.2 q.2 hkk (by rw [hI.sb, List.getElem?_map, hk']; rfl)
        (by rw [hI.sb, List.getElem?_map, hq]; rfl)).1
      have hgap := SbBlocked.fsCntGap (w.rows i0) (p.1 + 1) kf (q.1 + 1) l hkl hf (by omega) (by omega)
      rw [← hS.fs i0 p hp0, ← hS.fs i0 q (List.mem_of_getElem? hq), hfs] at hgap
      omega

theorem SbBlocked.drEv (img : Image) (w : WS) (s : Estep) (hI : Inv img w) (hD : SbBlocked.DrainOk w)
    (hok : SbCand.stepE w.σ s.esAg s.esLb (SbCand.nextE w.σ s.esAg s.esLb)) :
    SbBlocked.DrainOk (nextI w (.ev s)) := by
  intro i p f pr sw hp hpf hf
  rcases rowsEvInv w s i f _ hf with hf0 | ⟨hi, hfl, hlb⟩
  · rcases SbBlocked.pendBack w s i p hp with ⟨q, hq, hq1⟩ | ⟨-, hp1⟩
    · exact hD i q f pr sw hq (by omega) hf0
    · have := lookup_lt_Some hf0; omega
  · subst hi
    have hnil : w.pend s.esAg = [] := by
      apply SbBlocked.mapSndNil
      rw [← hI.sb]
      rw [← hlb] at hok
      exact SbBlocked.drainOf hok rfl
    rcases SbBlocked.pendBack w s s.esAg p hp with ⟨q, hq, -⟩ | ⟨-, hp1⟩
    · rw [hnil] at hq; cases hq
    · omega

theorem SbBlocked.drLand (w : WS) (i0 k : Nat) (hD : SbBlocked.DrainOk w) :
    SbBlocked.DrainOk (nextI w (.land i0 k)) := by
  cases hq : (w.pend i0)[k]? with
  | none => simp only [nextI, hq]; exact hD
  | some q =>
    intro i p f pr sw hp hpf hf
    have hp0 : p ∈ w.pend i := pendLandMem i0 k q hq i p hp
    rw [landEq i0 k q hq] at hf
    exact hD i p f pr sw hp0 hpf hf

/-- **(EP) AND (DR) HOLD AT EVERY STATE OF A VALID CANDIDATE** (epoch policy). -/
theorem SbBlocked.histStAt (c : CandW) (hv : validW SbPol.epoch c) :
    ∀ k, SbBlocked.EpochOk (stAt c k) ∧ SbBlocked.DrainOk (stAt c k)
  | 0 => ⟨fun _ _ _ h => by simp [stAt, init] at h, fun _ _ _ _ _ h => by simp [stAt, init] at h⟩
  | k + 1 => by
    have ih := SbBlocked.histStAt c hv k
    cases hk : c.its[k]? with
    | none =>
      show SbBlocked.EpochOk (match c.its[k]? with
        | some it => nextI (stAt c k) it
        | none => stAt c k) ∧ SbBlocked.DrainOk (match c.its[k]? with
        | some it => nextI (stAt c k) it
        | none => stAt c k)
      rw [hk]; exact ih
    | some it =>
      rw [stAtSucc c k it hk]
      have hok := hv k it hk
      have hI := invStAt SbPol.epoch c hv k
      have hS := SbBlocked.stStAt c k
      cases it with
      | ev s => exact ⟨SbBlocked.epEv _ _ s hI hS ih.1 hok, SbBlocked.drEv _ _ s hI ih.2 hok⟩
      | land i j => exact ⟨SbBlocked.epLand _ _ i j hI hS ih.1 hok, SbBlocked.drLand _ i j ih.2⟩

/-! # 3. Landed events and the chain -/

/-- Event `s` has LANDED at `w`: realized and not pending. -/
def SbBlocked.Landed (w : WS) (s : Geid) : Prop :=
  realized w s ∧ ∀ p, p ∈ w.pend s.1 → p.1 ≠ s.2

theorem SbBlocked.relXFenceL (x : Prop) (pr pw sr sw : Bool) (l' : Lbl) :
    lblRelX x (LFence pr pw sr sw) l' → l' = LFence pr pw sr sw := by
  rintro (⟨-, h⟩ | ⟨-, h⟩)
  · exact lblReidxFence _ _ _ _ _ h
  · simp [lblReidxSub] at h

section Inv

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- The member label of a realized event, related to GF's. -/
theorem SbBlocked.memLbl (hP : PInv N img G X dev w) (e : Geid) (l : Lbl) (hr : realized w e)
    (hl : gxLbl G e = some l) : ∃ l', (w.rows e.1)[e.2]? = some l' ∧ lblRelX (X e) l l' := by
  obtain ⟨l', hl'⟩ : ∃ l', (w.rows e.1)[e.2]? = some l' := ⟨_, List.getElem?_eq_getElem hr⟩
  obtain ⟨l0, hl0, hrel⟩ := hP.pf.1 e.1 e.2 l' hl'
  have h0 : l0 = l := Option.some.inj (hl0.symm.trans hl)
  subst h0
  exact ⟨l', hl', hrel⟩

/-- A realized GF fence's member label is the same fence. -/
theorem SbBlocked.memFence (hP : PInv N img G X dev w) (e : Geid) (pr pw sr sw : Bool)
    (hr : realized w e) (hl : gxLbl G e = some (LFence pr pw sr sw)) :
    (w.rows e.1)[e.2]? = some (LFence pr pw sr sw) := by
  obtain ⟨l', hl', hrel⟩ := SbBlocked.memLbl hP e _ hr hl
  rw [hl', SbBlocked.relXFenceL _ _ _ _ _ l' hrel]

theorem SbBlocked.landedOfGmo (hP : PInv N img G X dev w) (s : Geid) (hs : s ∈ w.gmo) :
    SbBlocked.Landed w s := by
  obtain ⟨l, hl, -⟩ := hP.inv.gmoMem s hs
  refine ⟨lookup_lt_Some hl, fun p hp hp1 => ?_⟩
  apply hP.inv.pendGmo s.1 p hp
  rw [hp1]; exact hs

/-- A landed GF write of `a` is in the landed list of `a`. -/
theorem SbBlocked.landedWr (hP : PInv N img G X dev w) (s : Geid) (a : Int) (hL : SbBlocked.Landed w s)
    (hw : gwrB G a s = true) : s ∈ wrAtW w a := by
  refine Classical.byContradiction (fun hn => ?_)
  rcases unlanded hP a s hw hn with hr | ⟨k, p, hk, hp1⟩
  · exact hr hL.1
  · exact hL.2 p (List.mem_of_getElem? hk) hp1

/-- A landed GF write is in the member's gmo. -/
theorem SbBlocked.landedGmo (hP : PInv N img G X dev w) (s : Geid) (hL : SbBlocked.Landed w s)
    (hW : gisW G s = true) : s ∈ w.gmo := by
  obtain ⟨l, hl⟩ : ∃ l, gxLbl G s = some l := by
    unfold gisW at hW
    cases h : gxLbl G s with
    | none => rw [h] at hW; cases hW
    | some l => exact ⟨l, rfl⟩
  have hWl : lbIsW l = true := by unfold gisW at hW; rw [hl] at hW; exact hW
  obtain ⟨l', hl', hrel⟩ := SbBlocked.memLbl hP s l hL.1 hl
  have hW' : lbIsW l' = true := by
    rcases relXW _ l l' hrel (.inl hWl) with rfl | ⟨_, _, _, _, _, _, _, _, -, rfl, -⟩
    · exact hWl
    · rfl
  rcases hP.inv.memIn s.1 s.2 l' hl' (memOfWr _ hW') with h | h
  · exact h
  · obtain ⟨p, hp, hp1⟩ := List.mem_map.1 h
    exact absurd hp1 (hL.2 p hp)

/-- **A REALIZED AMO'S BYTE SOURCE HAS LANDED** (atomicity: the source is gmo-before the AMO's own
write of the byte, which landed at the AMO's step; the landed list is gmo-downward closed). -/
theorem SbBlocked.amoSrcLanded (hP : PInv N img G X dev w) (hc : CatH G) (A s : Geid) (aq rl : Bool)
    (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (kc : WmClass) (j t : Nat)
    (hl : gxLbl G A = some (LRmw aq rl base ts rvs wvs kc)) (hrA : realized w A)
    (htj : ts[j]? = some t) (hs : gwriteAt G t = some s) : SbBlocked.Landed w s := by
  obtain ⟨-, hwl, hrl⟩ := rmwShape hc.wf A aq rl base ts rvs wvs kc hl
  have hj : j < ts.length := lookup_lt_Some htj
  have hwe : gwritesByte G A (accAddr base j) (wvs[j]'(by omega)) :=
    ⟨_, base, wvs, j, hl, rfl, List.getElem?_eq_getElem _, rfl⟩
  have hre : greadsByte G A (accAddr base j) t (rvs[j]'(by omega)) :=
    ⟨_, base, ts, rvs, j, hl, rfl, htj, List.getElem?_eq_getElem _, rfl⟩
  have hAL : SbBlocked.Landed w A := by
    refine ⟨hrA, fun p hp hp1 => ?_⟩
    obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLbl hP A.1 p hp
    have h2 : gxLbl G (A.1, p.1) = gxLbl G A := by rw [hp1]
    rw [h2, hl] at hl'
    cases hl'
  have hAW : A ∈ wrAtW w (accAddr base j) := SbBlocked.landedWr hP A _ hAL (gwrBOf G A _ _ hc.wf hwe).1
  obtain ⟨hsrc, -⟩ := hc.lv A _ t _ hre
  cases t with
  | zero => simp [gwriteAt] at hs
  | succ n =>
    obtain ⟨s', hs', hsw, hvis⟩ := hsrc
    rw [hs] at hs'
    cases hs'
    have hlt : gpos G s < gpos G A := by
      rcases hvis with h | h
      · exact h.2.2
      · exact (rule1Lt G s A _ _ hc.ppo h (.inl ⟨_, hsw⟩) hwe).2.2
    obtain ⟨hsb, hsm⟩ := gwrBOf G s _ _ hc.wf hsw
    have hsG : s ∈ wrAtG G (accAddr base j) := List.mem_filter.2 ⟨hsm, hsb⟩
    have hsW := landedDown G w _ s A (hP.pf.2 _) hc.wf.1 hAW hsG hlt
    exact SbBlocked.landedOfGmo hP s (List.mem_filter.1 hsW).1

/-- **THE RELEASE EPOCH** (rule 4 at the buffer, (EP)): a write po-before a `pw ∧ sw` fence po-before a
LANDED write of its row has landed. -/
theorem SbBlocked.epochLanded (hP : PInv N img G X dev w) (hE : SbBlocked.EpochOk w) (r s : Geid)
    (hL : SbBlocked.Landed w r) (hrW : gisW G r = true) (h1 : s.1 = r.1) (hf : fenceSw G s.1 s.2 r.2) :
    SbBlocked.Landed w s := by
  obtain ⟨kf, pr, sr, hk1, hk2, hkl⟩ := hf
  have hrg := SbBlocked.landedGmo hP r hL hrW
  obtain ⟨lr, hlr⟩ : ∃ l, gxLbl G r = some l := by
    unfold gisW at hrW
    cases h : gxLbl G r with
    | none => rw [h] at hrW; cases hrW
    | some l => exact ⟨l, rfl⟩
  have hWl : lbIsW lr = true := by unfold gisW at hrW; rw [hlr] at hrW; exact hrW
  obtain ⟨lr', hlr', hrel⟩ := SbBlocked.memLbl hP r lr hL.1 hlr
  have hW' : lbIsW lr' = true := by
    rcases relXW _ lr lr' hrel (.inl hWl) with rfl | ⟨_, _, _, _, _, _, _, _, -, rfl, -⟩
    · exact hWl
    · rfl
  have hrl : r.2 < (w.rows s.1).length := by rw [h1]; exact hL.1
  have hkr : realized w (s.1, kf) := by show kf < (w.rows s.1).length; omega
  have hkm := SbBlocked.memFence hP (s.1, kf) pr true sr true hkr hkl
  refine ⟨by show s.2 < (w.rows s.1).length; omega, fun p hp hp1 => ?_⟩
  exact hE s.1 p r hp hrg h1.symm (by omega) ⟨lr', by rw [h1]; exact hlr', hW'⟩ kf _ (by omega) hk2
    hkm rfl

/-- **THE DRAINING FENCE** ((DR), [R46.6]'s `drainLanded`): an event po-before a REALIZED draining
fence (`pw ∧ sr`) of its row is not pending. -/
theorem SbBlocked.drainLanded (hP : PInv N img G X dev w) (hD : SbBlocked.DrainOk w) (f s : Geid)
    (pr sw : Bool) (hrf : realized w f) (hfl : gxLbl G f = some (LFence pr true true sw))
    (h1 : s.1 = f.1) (h2 : s.2 < f.2) : SbBlocked.Landed w s := by
  have hfm := SbBlocked.memFence hP f pr true true sw hrf hfl
  have hfl' : f.2 < (w.rows s.1).length := by rw [h1]; exact hrf
  refine ⟨by show s.2 < (w.rows s.1).length; omega, fun p hp hp1 => ?_⟩
  exact hD s.1 p f.2 pr sw hp (by omega) (by rw [h1]; exact hfm)

end Inv

/-- **THE CHAIN** from the head `h`'s realized prefix: `Hb G dev h false e` — `e` is realized whenever
`h` is its row's head; `Hb G dev h true e` — `e` has landed then.  Program order (`root`, `po`), the
fabric order (`fab`), landed ⇒ realized (`lr`), a realized AMO's byte source (`amo`), the release epoch
(`epoch`: a write po-before a `pw ∧ sw` fence po-before a landed write of its row), the draining fence
(`drain`: an event po-before a realized `pw ∧ sr` fence of its row — the device's `DFence`, the
driver's `fence iorw,iorw`). -/
inductive SbBlocked.Hb (G : Gexec) (dev : List Geid) (h : Geid) : Bool → Geid → Prop where
  | root (e : Geid) : e.1 = h.1 → e.2 < h.2 → SbBlocked.Hb G dev h false e
  | po (e e' : Geid) : SbBlocked.Hb G dev h false e → e'.1 = e.1 → e'.2 < e.2 →
      SbBlocked.Hb G dev h false e'
  | fab (e e' : Geid) : SbBlocked.Hb G dev h false e → before dev e' e → SbBlocked.Hb G dev h false e'
  | lr (e : Geid) : SbBlocked.Hb G dev h true e → SbBlocked.Hb G dev h false e
  | amo (A s : Geid) (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8))
      (kc : WmClass) (j t : Nat) : SbBlocked.Hb G dev h false A →
      gxLbl G A = some (LRmw aq rl base ts rvs wvs kc) → ts[j]? = some t → gwriteAt G t = some s →
      SbBlocked.Hb G dev h true s
  | epoch (r s : Geid) : SbBlocked.Hb G dev h true r → gisW G r = true → s.1 = r.1 →
      fenceSw G s.1 s.2 r.2 → SbBlocked.Hb G dev h true s
  | drain (f s : Geid) (pr sw : Bool) : SbBlocked.Hb G dev h false f →
      gxLbl G f = some (LFence pr true true sw) → s.1 = f.1 → s.2 < f.2 → SbBlocked.Hb G dev h true s

section Inv2

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- **THE CHAIN IS SOUND** at a walk state with (EP) and (DR). -/
theorem SbBlocked.hbSound (hP : PInv N img G X dev w) (hc : CatH G) (hE : SbBlocked.EpochOk w)
    (hD : SbBlocked.DrainOk w) (x : Nat) (b : Bool) (e : Geid) (hh : SbBlocked.Hb G dev (hd w x) b e) :
    (b = false → realized w e) ∧ (b = true → SbBlocked.Landed w e) := by
  induction hh with
  | root e h1 h2 =>
    refine ⟨fun _ => ?_, fun h => by cases h⟩
    show e.2 < (w.rows e.1).length
    rw [h1]; exact h2
  | po e e' _ h1 h2 ih =>
    refine ⟨fun _ => ?_, fun h => by cases h⟩
    have := ih.1 rfl
    show e'.2 < (w.rows e'.1).length
    rw [h1]; unfold realized at this; omega
  | fab e e' _ hb ih => exact ⟨fun _ => hP.dvP e' e hb (ih.1 rfl), fun h => by cases h⟩
  | lr e _ ih => exact ⟨fun _ => (ih.2 rfl).1, fun h => by cases h⟩
  | amo A s aq rl base ts rvs wvs kc j t _ hl htj hs ih =>
    exact ⟨(fun h => nomatch h), fun _ =>
      SbBlocked.amoSrcLanded hP hc A s aq rl base ts rvs wvs kc j t hl (ih.1 rfl) htj hs⟩
  | epoch r s _ hrW h1 hf ih =>
    exact ⟨(fun h => nomatch h), fun _ => SbBlocked.epochLanded hP hE r s (ih.2 rfl) hrW h1 hf⟩
  | drain f s pr sw _ hfl h1 h2 ih =>
    exact ⟨(fun h => nomatch h), fun _ => SbBlocked.drainLanded hP hD f s pr sw (ih.1 rfl) hfl h1 h2⟩

/-! # 4. Own sources -/

/-- An OWN GF source of a load byte is po-before the load (rule 1: a po-later own write of the byte
is gmo-after the load, hence not visible to it). -/
theorem SbBlocked.ownPo (hc : CatH G) (h : Geid) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) (hl : gxLbl G h = some (LLoad aq base ts vs)) (a : Int) (t : Nat)
    (v : BitVec 8) (hrd : greadsByte G h a t v) (s : Geid) (hs : gwriteAt G t = some s)
    (hsx : s.1 = h.1) : s.2 < h.2 ∧ gwritesByte G s a v := by
  obtain ⟨hsrc, -⟩ := hc.lv h a t v hrd
  cases t with
  | zero => simp [gwriteAt] at hs
  | succ n =>
    obtain ⟨s', hs', hsw, hvis⟩ := hsrc
    rw [hs] at hs'
    cases hs'
    refine ⟨?_, hsw⟩
    rcases hvis with hg | hg
    · refine Classical.byContradiction (fun hn => ?_)
      rcases Nat.lt_or_ge h.2 s.2 with hlt | hge
      · obtain ⟨ls, -, -, -, hls, -⟩ := id hsw
        have hpo : WeakRvwmoGraph.gpo G h s := SBAcq.gpoOf G h s _ ls hl hls hsx.symm hlt
        have h2 := rule1Lt G h s a v hc.ppo hpo (.inr ⟨_, v, hrd⟩) hsw
        exact gmoLtIrrefl G s (gmoLtTrans G s h s hg h2)
      · have heq : s = h := Prod.ext hsx (by omega)
        subst heq
        obtain ⟨ls, base', vs', j, hls, hwr, -⟩ := hsw
        rw [hl, Option.some.injEq] at hls
        subst hls
        cases hwr
    · exact hg.2.1

/-- The forwarded byte of a buffer whose entries after `e` do not write the byte is `e`'s. -/
theorem SbBlocked.fwdLast (a : Int) (A B : List SbEnt) (e : SbEnt) (he : (msgByte e.msg a).isSome)
    (hB : ∀ e', e' ∈ B → msgByte e'.msg a = none) :
    SbCand.fwdByte (A ++ e :: B) a = msgByte e.msg a := by
  have key : ∀ (B : List SbEnt) (o : Option (BitVec 8)), (∀ e', e' ∈ B → msgByte e'.msg a = none) →
      B.foldl (fun o e => (msgByte e.msg a).or o) o = o := by
    intro B
    induction B with
    | nil => intro o _; rfl
    | cons e' B ih =>
      intro o hB
      simp only [List.foldl_cons]
      rw [hB e' (by simp)]
      exact ih o (fun e'' h => hB e'' (by simp [h]))
  unfold SbCand.fwdByte
  rw [List.foldl_append, List.foldl_cons, key B _ hB]
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 he
  rw [hu]; rfl

/-- **A PENDING OWN SOURCE IS FORWARDED WITH GF'S VALUE**: it is the youngest own pending entry at the
byte (a younger one would be a po-later own write of the byte, gmo-after the source by rule 1 and
visible to the read — contradicting the load value axiom's maximality). -/
theorem SbBlocked.ownFwd (hP : PInv N img G X dev w) (hc : CatH G) (x : Nat) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs))
    (a : Int) (t : Nat) (v : BitVec 8) (hrd : greadsByte G (hd w x) a t v) (s : Geid)
    (hs : gwriteAt G t = some s) (hsx : s.1 = x) (p : Nat × SbEnt) (hp : p ∈ w.pend x)
    (hp1 : p.1 = s.2) : SbCand.fwdByte (w.σ.sb x) a = some v := by
  obtain ⟨hpo, hsw⟩ := SbBlocked.ownPo hc (hd w x) aq base ts vs hl a t v hrd s hs hsx
  have hsxp : s = (x, p.1) := Prod.ext hsx hp1.symm
  have hcov := pendCovers hP x p a v hp (by rw [← hsxp]; exact hsw)
  obtain ⟨A, B, hAB⟩ := List.append_of_mem hp
  have hpw := hP.ord x
  rw [hAB, List.map_append, List.map_cons, List.pairwise_append, List.pairwise_cons] at hpw
  have hB : ∀ q, q ∈ B → msgByte q.2.msg a = none := by
    intro q hq
    cases hm : msgByte q.2.msg a with
    | none => rfl
    | some u =>
      exfalso
      have hqB : q ∈ w.pend x := by rw [hAB]; simp [hq]
      have hqw := pendWritesV hP x q a u hqB hm
      have hlt : p.1 < q.1 := hpw.2.1.1 q.1 (List.mem_map.2 ⟨q, hq, rfl⟩)
      have hqr := pendRealized hP x q hqB
      obtain ⟨rl', base', vs', kc', hlq, -, -⟩ := pendLbl hP x q hqB
      obtain ⟨ls, -, -, -, hls, -⟩ := id hsw
      have hpo1 : WeakRvwmoGraph.gpo G s (x, q.1) :=
        SBAcq.gpoOf G s (x, q.1) ls _ hls hlq hsx (by rw [← hp1]; exact hlt)
      have hg := rule1Lt G s (x, q.1) a u hc.ppo hpo1 (.inl ⟨v, hsw⟩) hqw
      have hpo2 : WeakRvwmoGraph.gpo G (x, q.1) (hd w x) :=
        SBAcq.gpoOf G (x, q.1) (hd w x) _ _ hlq hl rfl hqr
      have hmax := (hc.lv _ a t v hrd).2 _ u hqw (.inr hpo2)
      have hsW := gwritesOf G s a v hc.wf hsw
      have hqW := gwritesOf G _ a u hc.wf hqw
      have hix := (gwixGposLt G s (x, q.1) hc.wf.1 hsW hqW).2 hg.2.2
      have hst := (gwriteAtInv G t s hc.wf.1 hs).2
      omega
  rw [hP.inv.sb x, hAB, List.map_append, List.map_cons,
    SbBlocked.fwdLast a _ _ p.2 hcov (fun e' he' => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he'
      exact hB q hq)]
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hcov
  rw [hu]
  have := pendWritesV hP x p a u hp hu
  rw [← hsxp] at this
  rw [gwritesByteDet G s a u v this hsw]

/-- Per byte: a LANDED GF source is not forwarded and is the member-latest (as `srcGateOfLanded`). -/
theorem SbBlocked.byteOfLanded (hP : PInv N img G X dev w) (hc : CatH G) (x : Nat) (aq : Bool)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8)) (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs))
    (a : Int) (t : Nat) (v : BitVec 8) (hrd : greadsByte G (hd w x) a t v) (hL : landedSrc G w a t) :
    SbCand.fwdByte (w.σ.sb x) a = none ∧ srcLatest G w a t := by
  have he : ¬ realized w (hd w x) := fun h => by unfold realized hd at h; simp at h
  cases hf : SbCand.fwdByte (w.σ.sb x) a with
  | none => exact ⟨rfl, hP.rd _ _ t _ hrd he hL⟩
  | some v' =>
    exfalso
    rcases fwdRel (w.pend x) a with ⟨-, h2⟩ | ⟨p, hp, -, h2, -⟩
    · rw [← hP.inv.sb x, hf] at h2; cases h2
    · rw [← hP.inv.sb x, hf] at h2
      have hpr := pendRealized hP x p hp
      unfold realized at hpr
      obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLbl hP x p hp
      have hsw : gwritesByte G (x, p.1) a v' := pendWritesV hP x p _ v' hp h2.symm
      have hsW := gwritesOf G _ _ _ hc.wf hsw
      have hsm : (x, p.1) ∈ G.gxGmo := lblGmo G _ _ hc.wf hl' rfl
      have hpo : WeakRvwmoGraph.gpo G (x, p.1) (hd w x) := SBAcq.gpoOf G _ _ _ _ hl' hl rfl hpr
      have hsNW : (x, p.1) ∉ wrAtW w a :=
        fun h' => hP.inv.pendGmo x p hp (List.mem_filter.1 h').1
      have hle := (hc.lv _ _ t v hrd).2 _ v' hsw (.inr hpo)
      rcases hL with rfl | ⟨s, hs, hsl⟩
      · have := gwixPos G _ hsW; omega
      · obtain ⟨hsG, hsix⟩ := gwriteAtInv G _ s hc.wf.1 hs
        by_cases hne : s = (x, p.1)
        · rw [hne] at hsl; exact hsNW hsl
        · have hix : gwix G (x, p.1) < gwix G s := by
            rcases Nat.lt_or_ge (gwix G (x, p.1)) (gwix G s) with h | h
            · exact h
            · exact absurd (gwixInj G _ _ hc.wf.1 hsG hsW (by omega)) hne
          have hgp := (gwixGposLt G _ _ hc.wf.1 hsW hsG).1 hix
          have hsGa : (x, p.1) ∈ wrAtG G a := List.mem_filter.2 ⟨hsm, (gwrBOf G _ _ _ hc.wf hsw).1⟩
          exact hsNW (landedDown G w _ _ s (hP.pf.2 _) hc.wf.1 hsl hsGa hgp)

/-! # 5. `blockedIsCensus` -/

/-- **THE SOURCE CLASSES OF A NON-CENSUS READ BYTE** (GF + the head's position): the image, an OWN
write, or a write the chain `Hb` lands. -/
def SbBlocked.SrcCls (G : Gexec) (dev : List Geid) (h : Geid) (t : Nat) : Prop :=
  t = 0 ∨ ∃ s, gwriteAt G t = some s ∧ (s.1 = h.1 ∨ SbBlocked.Hb G dev h true s)

/-- **A HEAD WHOSE EVERY BYTE IS IN A SOURCE CLASS PASSES THE SOURCE GATE.** -/
theorem SbBlocked.srcGateOfCls (hP : PInv N img G X dev w) (hc : CatH G) (hE : SbBlocked.EpochOk w)
    (hD : SbBlocked.DrainOk w) (x : Nat) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs))
    (hcls : ∀ a t v, greadsByte G (hd w x) a t v → SbBlocked.SrcCls G dev (hd w x) t) :
    srcGate G w x base ts vs := by
  intro j t v htj hvj
  have hrd : greadsByte G (hd w x) (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
  have landedCase : ∀ s, gwriteAt G t = some s → gwritesByte G s (accAddr base j) v →
      SbBlocked.Landed w s →
      SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
        (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧ srcLatest G w (accAddr base j) t) :=
    fun s hs hsw hL => .inr (SbBlocked.byteOfLanded hP hc x aq base ts vs hl _ t v hrd
      (.inr ⟨s, hs, SbBlocked.landedWr hP s _ hL (gwrBOf G s _ _ hc.wf hsw).1⟩))
  have srcW : ∀ s, gwriteAt G t = some s → gwritesByte G s (accAddr base j) v := by
    intro s hs
    obtain ⟨hsrc, -⟩ := hc.lv _ _ t v hrd
    cases t with
    | zero => simp [gwriteAt] at hs
    | succ n =>
      obtain ⟨s', hs', hsw, -⟩ := hsrc
      rw [hs] at hs'
      cases hs'
      exact hsw
  rcases hcls _ t v hrd with h0 | ⟨s, hs, hown | hhb⟩
  · exact .inr (SbBlocked.byteOfLanded hP hc x aq base ts vs hl _ t v hrd (.inl h0))
  · have hsx : s.1 = x := hown
    by_cases hpen : ∃ p, p ∈ w.pend x ∧ p.1 = s.2
    · obtain ⟨p, hp, hp1⟩ := hpen
      exact .inl (SbBlocked.ownFwd hP hc x aq base ts vs hl _ t v hrd s hs hsx p hp hp1)
    · obtain ⟨hpo, hsw⟩ := SbBlocked.ownPo hc (hd w x) aq base ts vs hl _ t v hrd s hs hown
      refine landedCase s hs hsw ⟨?_, fun p hp hp1 => hpen ⟨p, by rw [← hsx]; exact hp, hp1⟩⟩
      show s.2 < (w.rows s.1).length
      rw [hsx]; exact hpo
  · exact landedCase s hs (srcW s hs) ((SbBlocked.hbSound hP hc hE hD x true s hhb).2 rfl)

/-- **`blockedIsCensus` — A PLAIN-LOAD HEAD ALL OF WHOSE BYTE SOURCES ARE IN A SOURCE CLASS PASSES THE
VALUE GATE** (at a walk state with (EP) and (DR)). -/
theorem SbBlocked.blockedIsCensus (hP : PInv N img G X dev w) (hc : CatH G) (himg : G.gxImg = img)
    (hE : SbBlocked.EpochOk w) (hD : SbBlocked.DrainOk w) (x : Nat) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs))
    (hcls : ∀ a t v, greadsByte G (hd w x) a t v → SbBlocked.SrcCls G dev (hd w x) t) :
    valGate w x base ts vs :=
  valGateMono hP hc.wf hc.lv himg x aq base ts vs hl
    (SbBlocked.srcGateOfCls hP hc hE hD x aq base ts vs hl hcls)

end Inv2

/-- **… AT EVERY REACHABLE STATE** of a valid candidate (epoch policy): (EP) and (DR) are theorems
(`histStAt`). -/
theorem SbBlocked.blockedIsCensusC {N : Nat} {G : Gexec} {X : Geid → Prop} {dev : List Geid}
    (c : CandW) (hv : validW SbPol.epoch c) (hP : PInv N c.img G X dev (cur c)) (hc : CatH G)
    (himg : G.gxImg = c.img) (x : Nat) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (cur c) x) = some (LLoad aq base ts vs))
    (hcls : ∀ a t v, greadsByte G (hd (cur c) x) a t v → SbBlocked.SrcCls G dev (hd (cur c) x) t) :
    valGate (cur c) x base ts vs :=
  have hh := SbBlocked.histStAt c hv c.its.length
  SbBlocked.blockedIsCensus hP hc himg hh.1 hh.2 x aq base ts vs hl hcls

/-- **THE NAMED TRANSPORT INPUT** (the half of §HEADHOP's (T) that [R46.4] makes explicit): at walk
state `w`, every non-exempt plain-load head that is NOT a census site (`Census`: the realization of a
`SilSite.kSites` pc or a device `DRead` — the label ↔ pc map, P-W6) has every byte source in a source
class: the image, an own write, or a write reached from the head's realized prefix by `SbBlocked.Hb`.
Truth for xv6: a non-census kernel / user load reads bytes in custody — own (stack, the process's own
memory on its hart), or handed over through a lock (the releaser's stores are po-before its
`fence rw,w`; the reader's `amoswap.aq` reads that release or a later one: `Hb.amo` + `Hb.epoch`), or
DMA data (po-before the device's draining `DFence`, realized through fabric order: `Hb.drain`).
FAITHFUL; WEAKER while named. -/
def SbBlocked.NonCensusSrc (G : Gexec) (dev : List Geid) (X Census : Geid → Prop) (w : WS) : Prop :=
  ∀ x base ts vs, gxLbl G (hd w x) = some (LLoad false base ts vs) → ¬ X (hd w x) → ¬ Census (hd w x) →
    ∀ a t v, greadsByte G (hd w x) a t v → SbBlocked.SrcCls G dev (hd w x) t

/-- **ROW H3 FROM THE CENSUS TABLE ALONE**: given the named transport for non-census heads, `HeadOrdRd`
under the value gate needs the per-head table (never blocked, or the static hops) ONLY at census
sites. -/
theorem SbBlocked.headOrdRdOfCensus {N : Nat} {G : Gexec} {X : Geid → Prop} {dev : List Geid}
    (Census : Geid → Prop) (c : CandW) (hv : validW SbPol.epoch c) (hP : PInv N c.img G X dev (cur c))
    (hc : CatH G) (himg : G.gxImg = c.img)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hr2'' : ∀ s m, WeakRvwmoGraph.gpo G s m → gisIo G s = true → gisR G m = true → gmoLt G s m)
    (hNC : SbBlocked.NonCensusSrc G dev X Census (cur c))
    (hT : ∀ x base ts vs, gxLbl G (hd (cur c) x) = some (LLoad false base ts vs) → ¬ X (hd (cur c) x) →
      Census (hd (cur c) x) →
      valGate (cur c) x base ts vs ∨
        (SbHeadHop.WrHop G (hd (cur c) x) ∧ SbHeadHop2.A2At G dev (cur c) x)) :
    HeadOrdRd G X valGate dev (cur c) := by
  apply SbHeadHop2.headOrdRdOfTable hc hr1 hr2''
  intro x base ts vs hl hX
  by_cases hC : Census (hd (cur c) x)
  · exact hT x base ts vs hl hX hC
  · exact .inl (SbBlocked.blockedIsCensusC c hv hP hc himg x false base ts vs hl
      (hNC x base ts vs hl hX hC))

end Weak
