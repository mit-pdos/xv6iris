/-
Weak: **allocproc route P, increment P-W3 (2/2) — `SbOrdWalk`, THE GATED WALK and its COMPLETION**
(`notes/weak-allocproc-routeP-design.md` §3.2/§3.4; plan rev 55 row P-W3 `walkPolP`/`walkRunP`; [OWN.106]
[OWN.112] [OWN.113]).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this file.

  §1  the effect of an item on the walk machine state (`realized`, the landed lists, the tagged buffers);
  §2  **THE GATE IS SOUND**: an ENABLED landing keeps the walk invariant `SbOrd.PInv` (`pinvLand`); an
      enabled head event, with the member label its arm gives, keeps it (`pinvEv`) — the read arm `rdG`
      is a PARAMETER with its soundness `RdSound` (proved for the design's source gate from P-W2's
      `loadArm`, `srcSound`, and for the value gate from `topTs`, `valSound`); the exempt arm is P-W2's
      `rdXArm` with the exempt-value interface `SbReplay.ExValTop` (both exempt classes: its `ip->ref`
      half F-P-W2-1 and its `lk->cpu` half [OWN.124], kept NAMED);
  §3  **`walkStepP`**: every enabled genuine item extends the walk candidate (`SbWalk.validW` under the
      epoch buffer) keeping `PInv` and strictly decreasing the work measure `work`;
  §4  **`walkRunP`**: from the empty walk, given `noStuckP`'s interfaces at every reachable GATED state
      (`gatedW`: every item enabled at its state — F-W2-V-1 (a), `PROGRESS-P-W3r-e.md`), a FINISHED gated walk (every row complete, every buffer drained) — and **`memberOfRun`**: its member is a
      well-formed graph whose writes are the landed log, whose AMOs read the latest bytes, which AGREES
      with GF (`SbAgree.agreeX`, P-W2's `agreeXOfPfx`), with `agreeW4` (`nf = True`), `agreeW3` at every
      lock set, and value agreement `valEqX` given `ExValGF`.

The program layer (`SbWalk.ok`'s `progOk`: each event item realized by the emission's block, P-W2's
`lockBlk`) is NOT built here: the walk is the machine walk, the datum is P-W4/P-W6's (the gate never reads
program states; see PROGRESS).

Spec: FAITHFUL (proof organisation).  Lean-only helpers `SbOrd.*`.
-/
import Weak.SbOrd

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SbOrd

open SbWalk SbAgree SbReplay

/-! # 1. The effect of an item -/

section Eff

variable {w : WS}

theorem landEq (i k : Nat) (p : Nat × SbEnt) (hp : (w.pend i)[k]? = some p) :
    nextI w (.land i k) =
      ⟨SbCand.nextL w.σ i k, upd w.pend i ((w.pend i).eraseIdx k), w.rows, w.fw, w.gmo ++ [(i, p.1)]⟩ := by
  simp only [nextI, hp]

theorem realizedLand (i k : Nat) (p : Nat × SbEnt) (hp : (w.pend i)[k]? = some p) (r : Geid) :
    realized (nextI w (.land i k)) r ↔ realized w r := by
  rw [landEq i k p hp]; exact Iff.rfl

theorem wrAtLand (i k : Nat) (p : Nat × SbEnt) (hp : (w.pend i)[k]? = some p) (a : Int) :
    wrAtW (nextI w (.land i k)) a =
      if rwrB w.rows a (i, p.1) = true then wrAtW w a ++ [(i, p.1)] else wrAtW w a := by
  rw [landEq i k p hp]
  show (w.gmo ++ [(i, p.1)]).filter (rwrB w.rows a) = _
  rw [List.filter_append, List.filter_cons]
  split <;> simp [wrAtW, *]

theorem pendLandMem (i k : Nat) (p : Nat × SbEnt) (hp : (w.pend i)[k]? = some p) (j : Nat)
    (q : Nat × SbEnt) : q ∈ (nextI w (.land i k)).pend j → q ∈ w.pend j := by
  rw [landEq i k p hp]
  show q ∈ upd w.pend i _ j → _
  by_cases hj : j = i
  · subst hj; rw [updEq]; exact List.mem_of_mem_eraseIdx
  · rw [updNe _ _ _ _ hj]; exact id

theorem pendLandOrd (i k : Nat) (p : Nat × SbEnt) (hp : (w.pend i)[k]? = some p) (j : Nat) :
    ((w.pend j).map Prod.fst).Pairwise (· < ·) →
    (((nextI w (.land i k)).pend j).map Prod.fst).Pairwise (· < ·) := by
  intro h
  rw [landEq i k p hp]
  show ((upd w.pend i _ j).map Prod.fst).Pairwise _
  by_cases hj : j = i
  · subst hj; rw [updEq]
    exact h.sublist ((List.eraseIdx_sublist _ _).map _)
  · rw [updNe _ _ _ _ hj]; exact h

theorem rowsEvEq (s : Estep) (j : Nat) :
    (nextI w (.ev s)).rows j = if j = s.esAg then w.rows j ++ [s.esLb] else w.rows j := by
  show upd w.rows s.esAg (w.rows s.esAg ++ [s.esLb]) j = _
  by_cases hj : j = s.esAg
  · subst hj; rw [updEq, if_pos rfl]
  · rw [updNe _ _ _ _ hj, if_neg hj]

theorem realizedEv (s : Estep) (r : Geid) :
    realized (nextI w (.ev s)) r ↔ realized w r ∨ r = (s.esAg, (w.rows s.esAg).length) := by
  unfold realized
  rw [rowsEvEq s r.1]
  by_cases hj : r.1 = s.esAg
  · rw [if_pos hj, List.length_append, List.length_singleton]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact .inl h
      · exact .inr (Prod.ext hj (by rw [h, hj]))
    · rintro (h | rfl)
      · omega
      · simp
  · rw [if_neg hj]
    constructor
    · exact .inl
    · rintro (h | rfl)
      · exact h
      · exact absurd rfl hj

theorem pendEvEq (s : Estep) (j : Nat) :
    (nextI w (.ev s)).pend j = if j = s.esAg then pendE w s.esAg s.esLb else w.pend j := by
  show upd w.pend s.esAg _ j = _
  by_cases hj : j = s.esAg
  · subst hj; rw [updEq, if_pos rfl]
  · rw [updNe _ _ _ _ hj, if_neg hj]

end Eff

/-- `srcLatest` and `landedSrc` read only the landed list of the byte. -/
theorem srcLatestCongr (G : Gexec) (w w' : WS) (a : Int) (t : Nat) :
    wrAtW w' a = wrAtW w a → (srcLatest G w' a t ↔ srcLatest G w a t) := by
  intro h; unfold srcLatest; rw [h]

theorem landedCongr (G : Gexec) (w w' : WS) (a : Int) (t : Nat) :
    wrAtW w' a = wrAtW w a → (landedSrc G w' a t ↔ landedSrc G w a t) := by
  intro h; unfold landedSrc; rw [h]

theorem srcLatestTop (G : Gexec) (w' : WS) (a : Int) (t : Nat) (s : Geid) (L : List Geid) :
    wrAtW w' a = L ++ [s] → gwriteAt G t = some s → srcLatest G w' a t := by
  intro h hs; exact .inr ⟨s, hs, by rw [h]; simp⟩

theorem landedSnoc (G : Gexec) (w w' : WS) (a : Int) (t : Nat) (s : Geid) :
    wrAtW w' a = wrAtW w a ++ [s] → landedSrc G w' a t →
    (∃ i, gwriteAt G (i + 1) = some s ∧ t = i + 1) ∨ landedSrc G w a t := by
  intro h hl
  rcases hl with h0 | ⟨src, hs, hm⟩
  · exact .inr (.inl h0)
  · rw [h] at hm
    rcases List.mem_append.1 hm with hm | hm
    · exact .inr (.inr ⟨src, hs, hm⟩)
    · simp only [List.mem_singleton] at hm
      subst hm
      cases t with
      | zero => simp [gwriteAt] at hs
      | succ i => exact .inl ⟨i, hs, rfl⟩

theorem storeNoRead (G : Gexec) (s : Geid) (rl : Bool) (base : Int) (vs : List (BitVec 8)) (kc : WmClass)
    (a : Int) (t : Nat) (v : BitVec 8) :
    gxLbl G s = some (LStore rl base vs kc) → ¬ greadsByte G s a t v := by
  rintro hl ⟨l, base', ts, vs', j, hl', hrd, -⟩
  rw [hl, Option.some.injEq] at hl'
  subst hl'; cases hrd

/-! # 2. The gate is sound: the walk invariant along enabled items -/

section Sound

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- **AN ENABLED LANDING KEEPS THE WALK INVARIANT.** -/
theorem pinvLand (pol : SbPol) (hP : PInv N img G X dev w) (i k : Nat) (hg : landG pol G w i k) :
    PInv N img G X dev (nextI w (.land i k)) := by
  obtain ⟨p, hp, hok, hco⟩ := hg
  have hpm : p ∈ w.pend i := List.mem_of_getElem? hp
  obtain ⟨rl, base, vs, kc, hl, hrow, -⟩ := pendLbl hP i p hpm
  have hrows : (nextI w (.land i k)).rows = w.rows := by rw [landEq i k p hp]
  refine ⟨invLand img pol w i k hP.inv hok, ?_, exOkLand X w i k hP.ex, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · refine pfxLand img pol G X w i k hP.inv hP.pf hok (fun p' hp' b hb => ?_)
    rw [hp, Option.some.injEq] at hp'
    subst hp'
    exact (hco b hb).1
  · intro x; rw [hrows]; exact hP.len x
  · intro x hx; rw [hrows] at hx; exact hP.ag x hx
  · intro r a t v hr hnr hl'
    rw [realizedLand i k p hp] at hnr
    by_cases hb : rwrB w.rows a (i, p.1) = true
    · have hw' : wrAtW (nextI w (.land i k)) a = wrAtW w a ++ [(i, p.1)] := by
        rw [wrAtLand i k p hp, if_pos hb]
      rcases landedSnoc G w _ a t _ hw' hl' with ⟨j, hs, rfl⟩ | hold
      · exact srcLatestTop G _ a _ _ _ hw' hs
      · exfalso
        have hsl := hP.rd r a t v hr hnr hold
        have := (hco a hb).2 r t v hr hsl (fun h => by subst h; exact storeNoRead G _ _ _ _ _ a t v hl hr)
        exact hnr this
    · have hw' : wrAtW (nextI w (.land i k)) a = wrAtW w a := by
        rw [wrAtLand i k p hp, if_neg hb]
      rw [srcLatestCongr G w _ a t hw']
      exact hP.rd r a t v hr hnr ((landedCongr G w _ a t hw').1 hl')
  · intro d d' hb hd'
    rw [realizedLand i k p hp] at hd' ⊢
    exact hP.dvP d d' hb hd'
  · intro j; exact pendLandOrd i k p hp j (hP.ord j)
  · intro j q hq hfs
    rw [hrows]; exact hP.fs0 j q (pendLandMem i k p hp j q hq) hfs
  · intro j q q' hq hq' hlt hfs
    exact hP.fs2 j q q' (pendLandMem i k p hp j q hq) (pendLandMem i k p hp j q' hq') hlt hfs
  · intro j q hq; exact hP.nrl j q (pendLandMem i k p hp j q hq)

theorem pendECases (w : WS) (x : Nat) (lb : Lbl) :
    (∃ rl base vs k, lb = LStore rl base vs k ∧
      pendE w x lb = w.pend x ++ [((w.rows x).length, SbCand.issueEnt w.σ x rl base vs k)]) ∨
    (∃ pr sr, lb = LFence pr true sr true ∧
      pendE w x lb = (w.pend x).map (fun p => (p.1, p.2.bump))) ∨
    pendE w x lb = w.pend x := by
  cases lb with
  | LStore rl base vs k => exact .inl ⟨rl, base, vs, k, rfl, rfl⟩
  | LFence pr pw sr sw =>
    cases pw <;> cases sw
    · exact .inr (.inr (by simp [pendE]))
    · exact .inr (.inr (by simp [pendE]))
    · exact .inr (.inr (by simp [pendE]))
    · exact .inr (.inl ⟨pr, sr, rfl, by simp [pendE]⟩)
  | _ => exact .inr (.inr rfl)

theorem relXFence (x : Prop) (l : Lbl) (pr pw sr sw : Bool) :
    lblRelX x l (LFence pr pw sr sw) → l = LFence pr pw sr sw := by
  rintro (⟨-, h⟩ | ⟨-, h⟩) <;> cases l <;> simp_all [lblReidx, lblReidxSub]

theorem relXStore (x : Prop) (l : Lbl) (rl : Bool) (base : Int) (vs : List (BitVec 8)) (k : WmClass) :
    lblRelX x l (LStore rl base vs k) → l = LStore rl base vs k := by
  rintro (⟨-, h⟩ | ⟨-, h⟩) <;> cases l <;> simp_all [lblReidx, lblReidxSub]

theorem fenceSwMono (G : Gexec) (i lo hi hi' : Nat) : fenceSw G i lo hi → hi ≤ hi' → fenceSw G i lo hi' := by
  rintro ⟨kf, pr, sr, h1, h2, h3⟩ hle; exact ⟨kf, pr, sr, h1, by omega, h3⟩

/-- **AN ENABLED HEAD EVENT, WITH ITS ARM'S MEMBER LABEL, KEEPS THE WALK INVARIANT** — given the arm's
facts: the label related to GF's, the `SbCand` step, the fabric turn, for an AMO the co-prefix and the
readers condition at each written byte (the `wr` gate), for an exempt read an in-range word. -/
theorem pinvEv (hP : PInv N img G X dev w) (hI : ImgFacts G) (x : Nat) (hx : x < N)
    (hcnt : (w.rows x).length < (G.gxProg.getD x []).length)
    (l lb' : Lbl) (hl : gxLbl G (hd w x) = some l) (hrel : lblRelX (X (hd w x)) l lb')
    (hst : SbCand.stepE w.σ x lb' (SbCand.nextE w.σ x lb'))
    (hfab : fabOk dev w (hd w x))
    (hco : gmoEv lb' = true → ∀ b, wrsB lb' b = true → wrAtW w b ++ [hd w x] <+: wrAtG G b)
    (hdone : gmoEv lb' = true → ∀ b, wrsB lb' b = true → readersDone G w b (hd w x))
    (hex : X (hd w x) → exValL x lb') :
    PInv N img G X dev (nextI w (.ev ⟨x, lb'⟩)) := by
  have htag : ∀ q, q ∈ w.pend x → q.1 < (w.rows x).length := fun q hq => pendRealized hP x q hq
  refine ⟨invEv img w ⟨x, lb'⟩ hP.inv hst, pfxEv img G X w ⟨x, lb'⟩ l hP.inv hP.pf hl hrel hco,
    exOkEv X w ⟨x, lb'⟩ hP.ex hex, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rows bounded
    intro j
    rw [rowsEvEq]
    by_cases hj : j = x
    · subst hj; rw [if_pos rfl, List.length_append, List.length_singleton]; exact hcnt
    · rw [if_neg hj]; exact hP.len j
  · -- agents
    intro j hj
    rw [rowsEvEq] at hj
    by_cases hjx : j = x
    · subst hjx; exact hx
    · rw [if_neg hjx] at hj; exact hP.ag j hj
  · -- an unrealized read with a landed source reads the member-latest
    intro r a t v hr hnr hl'
    rw [realizedEv] at hnr
    have hwa := wrAtEv img w ⟨x, lb'⟩ a hP.inv
    by_cases hb : (gmoEv lb' && wrsB lb' a) = true
    · have hw' : wrAtW (nextI w (.ev ⟨x, lb'⟩)) a = wrAtW w a ++ [hd w x] := by
        rw [hwa, if_pos hb]; rfl
      rcases landedSnoc G w _ a t _ hw' hl' with ⟨j, hs, rfl⟩ | hold
      · exact srcLatestTop G _ a _ _ _ hw' hs
      · exfalso
        simp only [Bool.and_eq_true] at hb
        have hsl := hP.rd r a t v hr (fun h => hnr (.inl h)) hold
        exact hnr (.inl (hdone hb.1 a hb.2 r t v hr hsl (fun h => hnr (.inr h))))
    · have hw' : wrAtW (nextI w (.ev ⟨x, lb'⟩)) a = wrAtW w a := by
        rw [hwa, if_neg hb]
      rw [srcLatestCongr G w _ a t hw']
      exact hP.rd r a t v hr (fun h => hnr (.inl h)) ((landedCongr G w _ a t hw').1 hl')
  · -- fabric prefix
    intro d d' hb hd'
    rw [realizedEv] at hd' ⊢
    rcases hd' with h | h
    · exact .inl (hP.dvP d d' hb h)
    · have hin : d' ∈ dev := by obtain ⟨i, j, -, hj, -⟩ := hb; exact List.mem_of_getElem? hj
      rw [h] at hin hb
      exact .inl (hfab hin d hb)
  · -- tags in issue order
    intro j
    rw [pendEvEq]
    by_cases hj : j = x
    · subst hj
      rw [if_pos rfl]
      rcases pendECases w j lb' with ⟨rl, base, vs, k, -, hpe⟩ | ⟨pr, sr, -, hpe⟩ | hpe
      · rw [hpe, List.map_append, List.pairwise_append]
        refine ⟨hP.ord j, by simp, fun a ha b hb => ?_⟩
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
        rw [hb]; exact htag q hq
      · rw [hpe, List.map_map]
        have : (Prod.fst ∘ fun p : Nat × SbEnt => (p.1, p.2.bump)) = Prod.fst := by funext p; rfl
        rw [this]; exact hP.ord j
      · rw [hpe]; exact hP.ord j
    · rw [if_neg hj]; exact hP.ord j
  · -- fs0
    intro j q hq hfs
    rw [pendEvEq] at hq
    rw [rowsEvEq]
    by_cases hj : j = x
    · subst hj
      rw [if_pos rfl] at hq
      rw [if_pos rfl, List.length_append, List.length_singleton]
      rcases pendECases w j lb' with ⟨rl, base, vs, k, -, hpe⟩ | ⟨pr, sr, hlb, hpe⟩ | hpe
      · rw [hpe] at hq
        rcases List.mem_append.1 hq with hq | hq
        · exact fenceSwMono G j _ _ _ (hP.fs0 j q hq hfs) (by omega)
        · simp only [List.mem_singleton] at hq
          subst hq; exact absurd rfl hfs
      · rw [hpe] at hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        subst hlb
        refine ⟨(w.rows j).length, pr, sr, htag p hp, by omega, ?_⟩
        have := relXFence _ l pr true sr true hrel
        rw [← this]; exact hl
      · rw [hpe] at hq
        exact fenceSwMono G j _ _ _ (hP.fs0 j q hq hfs) (by omega)
    · rw [if_neg hj] at hq ⊢; exact hP.fs0 j q hq hfs
  · -- fs2
    intro j q q' hq hq' hlt hfs
    rw [pendEvEq] at hq hq'
    by_cases hj : j = x
    · subst hj
      rw [if_pos rfl] at hq hq'
      rcases pendECases w j lb' with ⟨rl, base, vs, k, -, hpe⟩ | ⟨pr, sr, -, hpe⟩ | hpe
      · rw [hpe] at hq hq'
        rcases List.mem_append.1 hq with hq | hq <;> rcases List.mem_append.1 hq' with hq' | hq'
        · exact hP.fs2 j q q' hq hq' hlt hfs
        · simp only [List.mem_singleton] at hq'; subst hq'
          have := htag q hq; simp only at hlt; omega
        · simp only [List.mem_singleton] at hq; subst hq
          have hfs' : q'.2.fs ≠ 0 := hfs
          exact hP.fs0 j q' hq' hfs'
        · simp only [List.mem_singleton] at hq hq'; subst hq hq'; exact absurd hlt (Nat.lt_irrefl _)
      · rw [hpe] at hq hq'
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hq'
        exact hP.fs2 j p p' hp hp' hlt (fun h => hfs (by simp [SbEnt.bump, h]))
      · rw [hpe] at hq hq'; exact hP.fs2 j q q' hq hq' hlt hfs
    · rw [if_neg hj] at hq hq'; exact hP.fs2 j q q' hq hq' hlt hfs
  · -- no `.rl` entry
    intro j q hq
    rw [pendEvEq] at hq
    by_cases hj : j = x
    · subst hj
      rw [if_pos rfl] at hq
      rcases pendECases w j lb' with ⟨rl, base, vs, k, hlb, hpe⟩ | ⟨pr, sr, -, hpe⟩ | hpe
      · rw [hpe] at hq
        rcases List.mem_append.1 hq with hq | hq
        · exact hP.nrl j q hq
        · simp only [List.mem_singleton] at hq
          subst hq hlb
          have := hI.noRl _ _ hl
          rw [relXStore _ l rl base vs k hrel] at this
          exact this
      · rw [hpe] at hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        exact hP.nrl j p hp
      · rw [hpe] at hq; exact hP.nrl j q hq
    · rw [if_neg hj] at hq; exact hP.nrl j q hq

end Sound

/-! ## 2.1 The read arms -/

/-- **A SOUND READ GATE** at a walk candidate: an enabled non-exempt load has an `SbCand` step with GF's
values (timestamps re-chosen). -/
def RdSound (G : Gexec) (rdG : RdG) (c : CandW) : Prop :=
  ∀ x aq base ts vs, gxLbl G (hd (cur c) x) = some (LLoad aq base ts vs) → rdG (cur c) x base ts vs →
    (aq = true → SbCand.noRl ((cur c).σ.sb x)) →
    ∃ ts', ts'.length = ts.length ∧
      SbCand.stepE (cur c).σ x (LLoad aq base ts' vs) (SbCand.nextE (cur c).σ x (LLoad aq base ts' vs))

theorem lblShapeLd (G : Gexec) (hwf : gwf G) (e : Geid) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) : gxLbl G e = some (LLoad aq base ts vs) → vs.length = ts.length := by
  intro hl
  unfold gxLbl at hl
  cases hr : G.gxProg[e.1]? with
  | none => rw [hr] at hl; cases hl
  | some row =>
    rw [hr] at hl
    simp only [Option.bind_some] at hl
    exact hwf.2.2 e.1 row e.2 _ hr hl

/-- The design's source gate is sound (P-W2's `loadArm`). -/
theorem srcSound (pol : SbPol) (G : Gexec) (X : Geid → Prop) (c : CandW) (hv : validW pol c)
    (hpf : pfx G X (cur c)) (hwf : gwf G) (hlv : gloadValue G) (himg : G.gxImg = c.img) :
    RdSound G (srcGate G) c :=
  fun x aq base ts vs hl hs hrl =>
    loadArm pol c G X x _ aq base ts vs hv hpf hlv himg hl (lblShapeLd G hwf _ aq base ts vs hl) hs hrl

/-- The value gate is sound (`topTs`: a top read with the gate's values). -/
theorem valSound (pol : SbPol) (G : Gexec) (c : CandW) (hv : validW pol c) (hwf : gwf G) :
    RdSound G valGate c := by
  intro x aq base ts vs hl htop hrl
  have hS : SbCand.Inv (cur c).σ := sbInvStAt pol c hv c.its.length
  obtain ⟨ts', hl', hrd, -⟩ := topTs (cur c).σ x aq base hS vs htop
  exact ⟨ts', by rw [hl', lblShapeLd G hwf _ aq base ts vs hl], .load aq base ts' vs hrd hrl⟩

/-- **THE `wr` ARM'S CO-PREFIX**: an AMO whose byte source is the member-latest lands its write
immediately after it in GF's co (atomicity). -/
theorem amoPrefix {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}
    (hP : PInv N img G X dev w) (hc : CatH G) (e : Geid) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (kc : WmClass) (hl : gxLbl G e = some (LRmw aq rl base ts rvs wvs kc))
    (he : ¬ realized w e) (j t : Nat) (htj : ts[j]? = some t)
    (hsl : srcLatest G w (accAddr base j) t) :
    wrAtW w (accAddr base j) ++ [e] <+: wrAtG G (accAddr base j) := by
  obtain ⟨-, hwl, hrl⟩ := rmwShape hc.wf e aq rl base ts rvs wvs kc hl
  have hj : j < ts.length := lookup_lt_Some htj
  have hwe : gwritesByte G e (accAddr base j) (wvs[j]'(by omega)) :=
    ⟨_, base, wvs, j, hl, rfl, List.getElem?_eq_getElem _, rfl⟩
  have hre : greadsByte G e (accAddr base j) t (rvs[j]'(by omega)) :=
    ⟨_, base, ts, rvs, j, hl, rfl, htj, List.getElem?_eq_getElem _, rfl⟩
  obtain ⟨heb, hem⟩ := gwrBOf G e _ _ hc.wf hwe
  have heG : e ∈ wrAtG G (accAddr base j) := List.mem_filter.2 ⟨hem, heb⟩
  have heW : e ∉ wrAtW w (accAddr base j) := by
    intro h
    obtain ⟨l', hl', -⟩ := hP.inv.gmoMem e (List.mem_filter.1 h).1
    exact he (lookup_lt_Some hl')
  refine Classical.byContradiction (fun hno => ?_)
  obtain ⟨n, hnG, hnW, hlt⟩ := nextUnlanded G w _ e (hP.pf.2 _) hc.wf.1 heG heW hno
  obtain ⟨hnm, hnb⟩ := List.mem_filter.1 hnG
  obtain ⟨u, hnw⟩ := gwrBTo G n _ hnb
  have hnWs := gwritesOf G n _ u hc.wf hnw
  have heWs := gwritesOf G e _ _ hc.wf hwe
  have h1 : t < gwix G n := by
    rcases hsl with ⟨rfl, -⟩ | ⟨src, hs, hlast⟩
    · exact gwixPos G n hnWs
    · have hsrcW : src ∈ wrAtW w (accAddr base j) := List.mem_of_getLast? hlast
      obtain ⟨hsrcWs, hix⟩ := gwriteAtInv G t src hc.wf.1 hs
      have hsrcm := (List.mem_filter.1 hsrcW).1
      have hsrcG : src ∈ G.gxGmo := by
        have := (hP.pf.2 (accAddr base j)).subset hsrcW
        exact (List.mem_filter.1 this).1
      have hne : src ≠ n := fun h => hnW (h ▸ hsrcW)
      have hlt2 : gpos G src < gpos G n := by
        rcases Nat.lt_or_ge (gpos G src) (gpos G n) with h | h
        · exact h
        · rcases Nat.eq_or_lt_of_le h with h | h
          · exact absurd (gposInj G _ _ hc.wf.1 hsrcG hnm h.symm) hne
          · exact absurd (landedDown G w _ n src (hP.pf.2 _) hc.wf.1 hsrcW hnG h) hnW
      rw [← hix]; exact (gwixGposLt G src n hc.wf.1 hsrcWs hnWs).2 hlt2
  have h2 : gwix G n < gwix G e := (gwixGposLt G n e hc.wf.1 hnWs heWs).2 hlt
  exact hc.atom e _ t _ hre ⟨_, hl, rfl⟩ n u hnw ⟨h1, h2⟩

/-- **THE HEAD ARMS**: an enabled head's member label — GF's label re-timed (`rd`, `wr`), the top read
(`rdX`), GF's label verbatim (stores, fences, I/O) — with everything `pinvEv` needs. -/
theorem armHd {N : Nat} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {rdG : RdG} {c : CandW}
    (hv : validW SbPol.epoch c) (hP : PInv N c.img G X dev (cur c)) (hc : CatH G)
    (himg : G.gxImg = c.img) (hrs : RdSound G rdG c)
    (hX : ∀ e l, X e → gxLbl G e = some l → ∃ base ts vs, l = LLoad false base ts vs)
    (hdef : ∀ e a t v, greadsByte G e a t v → (c.img a).isSome) (hIref : ExValTop G X (cur c))
    (x : Nat) (l : Lbl) (hl : gxLbl G (hd (cur c) x) = some l)
    (he : enbL G X rdG (cur c) (hd (cur c) x) l) :
    ∃ lb', lblRelX (X (hd (cur c) x)) l lb' ∧
      SbCand.stepE (cur c).σ x lb' (SbCand.nextE (cur c).σ x lb') ∧
      (gmoEv lb' = true → ∀ b, wrsB lb' b = true →
        wrAtW (cur c) b ++ [hd (cur c) x] <+: wrAtG G b) ∧
      (gmoEv lb' = true → ∀ b, wrsB lb' b = true → readersDone G (cur c) b (hd (cur c) x)) ∧
      (X (hd (cur c) x) → exValL x lb') := by
  have hnX : ∀ l0, gxLbl G (hd (cur c) x) = some l0 → (∀ base ts vs, l0 ≠ LLoad false base ts vs) →
      ¬ X (hd (cur c) x) := by
    intro l0 hl0 hn hx
    obtain ⟨base, ts, vs, h⟩ := hX _ l0 hx hl0
    exact hn base ts vs h
  have hnr : ¬ realized (cur c) (hd (cur c) x) := fun h => by unfold realized hd at h; simp at h
  cases l with
  | LLoad aq base ts vs =>
    rcases he with hx | ⟨hx, hrl, hg⟩
    · obtain ⟨b0', t0', v0', h⟩ := hX _ _ hx hl
      have haq : aq = false := by injection h
      subst haq
      have hlen := lblShapeLd G hc.wf _ _ _ _ _ hl
      obtain ⟨ts', vs', h1, h2, htop, hsub, hst⟩ := rdXArm SbPol.epoch c G x _ base ts vs hv hl
        (fun j hj => hdef _ _ _ _ ⟨_, base, ts, vs, j, hl, rfl, List.getElem?_eq_getElem hj,
          List.getElem?_eq_getElem (by rw [hlen]; exact hj), rfl⟩)
      refine ⟨LLoad false base ts' vs', .inr ⟨hx, hsub⟩, hst, fun _ b hb => by simp [wrsB, lbWr] at hb,
        fun _ b hb => by simp [wrsB, lbWr] at hb, fun _ => ?_⟩
      exact rdXIref G X (cur c) x base ts ts' vs vs' hIref hx hl h2 htop
    · obtain ⟨ts', h1, hst⟩ := hrs x aq base ts vs hl hg hrl
      exact ⟨LLoad aq base ts' vs, .inl ⟨hx, rfl, rfl, rfl, h1⟩, hst, fun _ b hb => by simp [wrsB, lbWr] at hb,
        fun _ b hb => by simp [wrsB, lbWr] at hb, fun h => absurd h hx⟩
  | LStore rl base vs kc =>
    have hx := hnX _ hl (fun _ _ _ h => by cases h)
    have hne : vs ≠ [] := by
      unfold gxLbl at hl
      cases hr : G.gxProg[(hd (cur c) x).1]? with
      | none => rw [hr] at hl; cases hl
      | some row =>
        rw [hr] at hl; simp only [Option.bind_some] at hl
        exact hc.wf.2.2 _ row _ _ hr hl
    exact ⟨_, .inl ⟨hx, lblReidxRefl _⟩, .issue rl base vs kc hne he, fun h => by simp [gmoEv, isSt, lbIsMem, lbIsR, lbIsW] at h,
      fun h => by simp [gmoEv, isSt, lbIsMem, lbIsR, lbIsW] at h, fun h => absurd h hx⟩
  | LFence pr pw sr sw =>
    have hx := hnX _ hl (fun _ _ _ h => by cases h)
    exact ⟨_, .inl ⟨hx, lblReidxRefl _⟩, .fence pr pw sr sw he,
      fun h => by simp [gmoEv, isSt, lbIsMem, lbIsR, lbIsW, lbIsIo] at h,
      fun h => by simp [gmoEv, isSt, lbIsMem, lbIsR, lbIsW, lbIsIo] at h, fun h => absurd h hx⟩
  | LRmw aq rl base ts rvs wvs kc =>
    have hx := hnX _ hl (fun _ _ _ h => by cases h)
    obtain ⟨hA, hB, hC, hD⟩ := he
    obtain ⟨hwne, hwl, hrl⟩ := rmwShape hc.wf _ aq rl base ts rvs wvs kc hl
    obtain ⟨ts', h1, hrd, hlat⟩ := rmwArm SbPol.epoch c G X x _ aq rl base ts rvs wvs kc hv hP.pf hc.lv
      himg hl hrl (fun j t ht => (hA j t ht).1)
    have hbyte : ∀ b, wrsB (LRmw aq rl base ts' rvs wvs kc) b = true →
        ∃ j t, ts[j]? = some t ∧ b = accAddr base j := by
      intro b hb
      obtain ⟨base0, vs0, j, v, hw, hv0, ha⟩ := (wrsBIff _ b).1 hb
      simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hj : j < ts.length := by rw [← hwl]; exact lookup_lt_Some hv0
      exact ⟨j, ts[j], List.getElem?_eq_getElem hj, ha.symm⟩
    refine ⟨LRmw aq rl base ts' rvs wvs kc, .inl ⟨hx, rfl, rfl, rfl, rfl, rfl, rfl, h1⟩,
      .rmw aq rl base ts' rvs wvs kc hwne (by rw [h1]; exact hwl) hrd hlat (by rw [h1]; exact hB) hC hD,
      fun _ b hb => ?_, fun _ b hb => ?_, fun h => absurd h hx⟩
    · obtain ⟨j, t, ht, rfl⟩ := hbyte b hb
      exact amoPrefix hP hc _ aq rl base ts rvs wvs kc hl hnr j t ht (hA j t ht).1
    · obtain ⟨j, t, ht, rfl⟩ := hbyte b hb
      exact (hA j t ht).2
  | LIo kd base vs =>
    have hx := hnX _ hl (fun _ _ _ h => by cases h)
    exact ⟨_, .inl ⟨hx, lblReidxRefl _⟩, .io kd base vs, fun _ b hb => by simp [wrsB, lbWr] at hb,
      fun _ b hb => by simp [wrsB, lbWr] at hb, fun h => absurd h hx⟩

/-! # 3. One walk step -/

def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumToLt (f g : Nat → Nat) (x0 : Nat) : ∀ n, x0 < n → g x0 < f x0 →
    (∀ y, y ≠ x0 → g y = f y) → sumTo g n < sumTo f n
  | 0, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, hlt, heq => by
    show sumTo g n + g n < sumTo f n + f n
    by_cases hn : n = x0
    · subst hn
      have : sumTo g n = sumTo f n := sumToEq f g n (fun y hy => heq y (by omega))
      omega
    · have := sumToLt f g x0 n (by omega) hlt heq
      rw [heq n hn]; omega
where
  sumToEq (f g : Nat → Nat) : ∀ n, (∀ y, y < n → g y = f y) → sumTo g n = sumTo f n
    | 0, _ => rfl
    | n + 1, h => by
      show sumTo g n + g n = sumTo f n + f n
      rw [sumToEq f g n (fun y hy => h y (by omega)), h n (by omega)]

theorem sumToZero (f : Nat → Nat) : ∀ n, sumTo f n = 0 → ∀ y, y < n → f y = 0
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h, y, hy => by
    have h' : sumTo f n + f n = 0 := h
    by_cases hyn : y = n
    · subst hyn; omega
    · exact sumToZero f n (by omega) y (by omega)

/-- **THE WORK MEASURE**: twice the GF events left per row plus the pending stores. -/
def work (N : Nat) (G : Gexec) (w : WS) : Nat :=
  sumTo (fun x => 2 * ((G.gxProg.getD x []).length - (w.rows x).length) + (w.pend x).length) N

/-- What the walk needs at every reachable candidate: the gated-read order (NAMED, row H3 — rows H1, H2,
H4, H5 are PROVED, `SbOrd.blkHead`; F-P-W3-3), the exempt-value interface (NAMED, F-P-W2-1), a sound read
gate weaker than the source gate (PROVED for `srcGate` and `valGate`: `srcIfc`, `valIfc`). -/
structure StateIfc (G : Gexec) (X : Geid → Prop) (rdG : RdG) (dev : List Geid) (c : CandW) : Prop where
  head : HeadOrdRd G X rdG dev (cur c)
  iref : ExValTop G X (cur c)
  sound : RdSound G rdG c
  mono : ∀ x aq base ts vs, gxLbl G (hd (cur c) x) = some (LLoad aq base ts vs) →
    srcGate G (cur c) x base ts vs → rdG (cur c) x base ts vs

/-- The global hypotheses of the walk (cat, the trusted residue, `gfDevWIo`, the image facts, the
device-row store order (NAMED device model, row H4), the hart-row fabric fact (`LockFacts3.hartDevIo`
on an xv6 bundle), the exempt reads are plain loads of image bytes). -/
structure WalkHyp (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) : Prop where
  cat : CatH GF.gfGd.gdG
  io : ioResidueGmo GF
  wio : gfDevWIo GF
  imgF : ImgFacts GF.gfGd.gdG
  devSt : DevStOrd GF.gfGd.gdG GF.gfDev
  hart : ∀ e, e ∈ GF.gfDev → e.1 < NCPU → gisIo GF.gfGd.gdG e = true
  len : GF.gfGd.gdG.gxProg.length = N
  imgEq : GF.gfGd.gdG.gxImg = img
  ex : ∀ e l, X e → gxLbl GF.gfGd.gdG e = some l → ∃ base ts vs, l = LLoad false base ts vs
  def' : ∀ e a t v, greadsByte GF.gfGd.gdG e a t v → (img a).isSome

theorem curSnoc (c : CandW) (it : Item) : cur (snocC c it) = nextI (cur c) it := by
  show stAt (snocC c it) (c.its ++ [it]).length = _
  rw [List.length_append, List.length_singleton]
  exact stAtSnocEnd c it

/-- The walk target an item realizes (an event of row `s.esAg`'s head, or the landing of `i`'s `k`-th
entry). -/
def itemTgt : Item → Tgt
  | .ev s => .hd s.esAg
  | .land i k => .ld i k

/-- **A GATED CANDIDATE** (F-W2-V-1 (a), PROGRESS-P-W3r-e): every item was ENABLED (`enb` under the epoch
buffer, with the read gate `rdG`) at the walk state before it — the candidates `walkRunP` builds. -/
def gatedW (G : Gexec) (X : Geid → Prop) (rdG : RdG) (dev : List Geid) (c : CandW) : Prop :=
  ∀ (k : Nat) (it : Item), c.its[k]? = some it → enb SbPol.epoch G X rdG dev (stAt c k) (itemTgt it)

theorem gatedNil (G : Gexec) (X : Geid → Prop) (rdG : RdG) (dev : List Geid) (img : Image) :
    gatedW G X rdG dev ⟨img, []⟩ := fun _ _ h => by simp at h

theorem gatedSnoc (G : Gexec) (X : Geid → Prop) (rdG : RdG) (dev : List Geid) (c : CandW) (it : Item)
    (hg : gatedW G X rdG dev c) (he : enb SbPol.epoch G X rdG dev (cur c) (itemTgt it)) :
    gatedW G X rdG dev (snocC c it) := by
  intro k it' hk
  change (c.its ++ [it])[k]? = some it' at hk
  by_cases hlt : k < c.its.length
  · rw [List.getElem?_append_left hlt] at hk
    rw [stAtSnoc c it k (Nat.le_of_lt hlt)]
    exact hg k it' hk
  · have hk' : k = c.its.length := by
      have := (List.getElem?_eq_some_iff.1 hk).1
      simp only [List.length_append, List.length_singleton] at this
      omega
    subst hk'
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hk
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    rw [stAtSnoc c it _ (Nat.le_refl _)]
    exact he

/-- **`walkStepP` — ONE GATED WALK STEP**: an enabled genuine item extends the walk (valid under the
epoch buffer), keeps the walk invariant and strictly decreases the work. -/
theorem walkStepP (GF : Gfexec) (N : Nat) (X : Geid → Prop) (rdG : RdG) (c : CandW)
    (hW : WalkHyp GF N c.img X) (hv : validW SbPol.epoch c)
    (hP : PInv N c.img GF.gfGd.gdG X GF.gfDev (cur c)) (hS : StateIfc GF.gfGd.gdG X rdG GF.gfDev c)
    (T : Tgt) (hT : validT N GF.gfGd.gdG (cur c) T)
    (he : enb SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev (cur c) T) :
    ∃ it, validW SbPol.epoch (snocC c it) ∧ PInv N c.img GF.gfGd.gdG X GF.gfDev (cur (snocC c it)) ∧
      work N GF.gfGd.gdG (cur (snocC c it)) < work N GF.gfGd.gdG (cur c) ∧ itemTgt it = T := by
  cases T with
  | ld i k =>
    obtain ⟨hi, -⟩ := hT
    obtain ⟨p, hp, hok, -⟩ := id he
    refine ⟨.land i k, validSnoc _ c _ hv hok, by rw [curSnoc]; exact pinvLand _ hP i k he, ?_, rfl⟩
    rw [curSnoc]
    refine sumToLt _ _ i N hi ?_ (fun y hy => ?_)
    · rw [landEq i k p hp]
      dsimp only
      rw [updEq, List.length_eraseIdx, if_pos (lookup_lt_Some hp)]
      have := lookup_lt_Some hp
      omega
    · rw [landEq i k p hp]
      dsimp only
      rw [updNe _ _ _ _ hy]
  | hd x =>
    obtain ⟨hx, hcnt⟩ := hT
    obtain ⟨l, hl, hfab, hen⟩ := he
    obtain ⟨lb', hrel, hst, hco, hdone, hex⟩ := armHd hv hP hW.cat hW.imgEq hS.sound hW.ex hW.def'
      hS.iref x l hl hen
    refine ⟨.ev ⟨x, lb'⟩, validSnoc _ c _ hv hst, by
      rw [curSnoc]; exact pinvEv hP hW.imgF x hx hcnt l lb' hl hrel hst hfab hco hdone hex, ?_, rfl⟩
    rw [curSnoc]
    refine sumToLt _ _ x N hx ?_ (fun y hy => ?_)
    · rw [rowsEvEq, if_pos rfl, pendEvEq, if_pos rfl, List.length_append, List.length_singleton]
      dsimp only
      have hpe : (pendE (cur c) x lb').length ≤ ((cur c).pend x).length + 1 := by
        rcases pendECases (cur c) x lb' with ⟨_, _, _, _, -, h⟩ | ⟨_, _, -, h⟩ | h <;> rw [h] <;> simp
      omega
    · rw [rowsEvEq, if_neg hy, pendEvEq, if_neg hy]

/-! # 4. The finished walk and its member -/

theorem pinvInit (N : Nat) (img : Image) (G : Gexec) (X : Geid → Prop) (dev : List Geid) :
    PInv N img G X dev (init img) where
  inv := invInit img
  pf := pfxInit G X img
  ex := exOkInit X img
  len _ := by simp [init]
  ag _ h := absurd rfl h
  rd _ _ t _ _ _ hl := by
    rcases hl with rfl | ⟨_, _, hm⟩
    · exact .inl ⟨rfl, rfl⟩
    · simp [wrAtW, init] at hm
  dvP _ _ _ h := by simp [realized, init] at h
  ord _ := List.Pairwise.nil
  fs0 _ _ h := by simp [init] at h
  fs2 _ _ _ h := by simp [init] at h
  nrl _ _ h := by simp [init] at h

/-- **`walkRunP` — THE GATED WALK RUNS TO COMPLETION**: given the global hypotheses and, at every reachable
GATED candidate (F-W2-V-1 (a): every item enabled at its state, `gatedW`), `noStuckP`'s per-state
interfaces, a FINISHED valid gated walk exists (every row complete, every buffer drained) with the walk
invariant. -/
theorem walkRunP (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (rdG : RdG)
    (hW : WalkHyp GF N img X)
    (hS : ∀ c, validW SbPol.epoch c → gatedW GF.gfGd.gdG X rdG GF.gfDev c → c.img = img →
      PInv N img GF.gfGd.gdG X GF.gfDev (cur c) → StateIfc GF.gfGd.gdG X rdG GF.gfDev c) :
    ∃ c, c.img = img ∧ validW SbPol.epoch c ∧ PInv N img GF.gfGd.gdG X GF.gfDev (cur c) ∧
      (∀ x, x < N → ((cur c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
      drained (cur c) ∧ gatedW GF.gfGd.gdG X rdG GF.gfDev c := by
  suffices H : ∀ n c, validW SbPol.epoch c → gatedW GF.gfGd.gdG X rdG GF.gfDev c → c.img = img →
      PInv N img GF.gfGd.gdG X GF.gfDev (cur c) → work N GF.gfGd.gdG (cur c) ≤ n →
      ∃ c', c'.img = img ∧ validW SbPol.epoch c' ∧ PInv N img GF.gfGd.gdG X GF.gfDev (cur c') ∧
        (∀ x, x < N → ((cur c').rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur c') ∧ gatedW GF.gfGd.gdG X rdG GF.gfDev c' by
    exact H _ ⟨img, []⟩ (fun k it h => by simp at h) (gatedNil _ X rdG _ img) rfl (pinvInit N img _ X _)
      (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro c hv hg hc hP hw
    by_cases hfin : (∀ x, x < N → ((cur c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur c)
    · exact ⟨c, hc, hv, hP, hfin.1, hfin.2, hg⟩
    · exfalso
      obtain ⟨T, hT, he⟩ := noStuckP GF N img X rdG (cur c) hW.cat hW.io hW.wio hW.imgF hW.len hP
        (hS c hv hg hc hP).mono hW.devSt hW.hart (hS c hv hg hc hP).head (nonFinal hP hfin)
      subst hc
      obtain ⟨it, -, -, hlt, -⟩ := walkStepP GF N X rdG c hW hv hP (hS c hv hg rfl hP) T hT he
      omega
  | succ n ih =>
    intro c hv hg hc hP hw
    by_cases hfin : (∀ x, x < N → ((cur c).rows x).length = (GF.gfGd.gdG.gxProg.getD x []).length) ∧
        drained (cur c)
    · exact ⟨c, hc, hv, hP, hfin.1, hfin.2, hg⟩
    · obtain ⟨T, hT, he⟩ := noStuckP GF N img X rdG (cur c) hW.cat hW.io hW.wio hW.imgF hW.len hP
        (hS c hv hg hc hP).mono hW.devSt hW.hart (hS c hv hg hc hP).head (nonFinal hP hfin)
      subst hc
      obtain ⟨it, hv', hP', hlt, hit⟩ := walkStepP GF N X rdG c hW hv hP (hS c hv hg rfl hP) T hT he
      exact ih (snocC c it) hv' (gatedSnoc _ X rdG _ c it hg (by rw [hit]; exact he)) rfl hP'
        (by omega)
where
  nonFinal {G : Gexec} {dev : List Geid} {w : WS} (hP : PInv N img G X dev w)
      (hfin : ¬ ((∀ x, x < N → (w.rows x).length = (G.gxProg.getD x []).length) ∧ drained w)) :
      (∃ x, x < N ∧ (w.rows x).length < (G.gxProg.getD x []).length) ∨ (∃ i, w.pend i ≠ []) := by
    by_cases h1 : ∀ x, x < N → (w.rows x).length = (G.gxProg.getD x []).length
    · have h2 : ¬ drained w := fun h => hfin ⟨h1, h⟩
      obtain ⟨i, hi⟩ : ∃ i, w.pend i ≠ [] :=
        Classical.byContradiction (fun hn => h2 (fun i => Classical.byContradiction (fun h => hn ⟨i, h⟩)))
      exact .inr ⟨i, hi⟩
    · obtain ⟨x, hx, hne⟩ : ∃ x, x < N ∧ (w.rows x).length ≠ (G.gxProg.getD x []).length :=
        Classical.byContradiction (fun hn => h1 (fun x hx =>
          Classical.byContradiction (fun h => hn ⟨x, hx, h⟩)))
      exact .inl ⟨x, hx, by have := hP.len x; omega⟩

/-- **THE FINISHED WALK'S MEMBER** (P-W2's `agreeXOfPfx` and the member facts, at the machine walk). -/
theorem memberOfRun (pol : SbPol) (N : Nat) (G : Gexec) (X : Geid → Prop) (dev : List Geid) (c : CandW)
    (hv : validW pol c) (hwf : gwf G) (himg : G.gxImg = c.img) (hN : G.gxProg.length = N)
    (hP : PInv N c.img G X dev (cur c))
    (hfin : ∀ x, x < N → ((cur c).rows x).length = (G.gxProg.getD x []).length)
    (hdr : drained (cur c)) :
    gwf (memberP N c) ∧ logOf (memberP N c) (logP c) ∧
    CertZ18.rmwLatest (memberP N c) (logP c) ∧ agreeX G (memberP N c) X ∧
    CertZ24.agreeW4 G (memberP N c) (fun _ => False) ∧
    (∀ L, CertZ18.agreeW3 G (memberP N c) L) ∧
    (ExValGF G X → valEqX G (memberP N c) X) := by
  have hR : RmwInv c.img (cur c) := rmwInvStAt pol c hv _
  have hagr := agreeXOfPfx N c.img G X (cur c) hP.inv hP.ag hdr hwf himg hN hfin hP.pf
  exact ⟨memberGwf N _ _ hP.inv hP.ag hdr, memberLogOf N _ _ hP.inv hP.ag,
    memberRmwLatest N _ _ hP.inv hR hP.ag hdr, hagr, agreeW4OfX _ _ X hagr,
    fun L => agreeW3OfX _ _ X L hagr, fun hG => valEqXOfAgree _ _ X hagr hG (memberExOk N _ X _ hP.ex)⟩

/-- **A COMPLETED MEMBER FOR EVERY CAT-CONSISTENT GF** (modulo `noStuckP`'s named per-state interfaces, asked
only at GATED candidates, F-W2-V-1 (a)):
the gated walk under the per-address + fence-epoch buffer runs to completion, and its member agrees with
GF (labels up to read re-timing, exempt reads up to their word; FULL co), with value agreement given the
exempt-value interface `ExValGF`. -/
theorem memberOfCat (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (rdG : RdG)
    (hW : WalkHyp GF N img X)
    (hS : ∀ c, validW SbPol.epoch c → gatedW GF.gfGd.gdG X rdG GF.gfDev c → c.img = img →
      PInv N img GF.gfGd.gdG X GF.gfDev (cur c) → StateIfc GF.gfGd.gdG X rdG GF.gfDev c) :
    ∃ c, c.img = img ∧ validW SbPol.epoch c ∧ drained (cur c) ∧
      gwf (memberP N c) ∧ logOf (memberP N c) (logP c) ∧
      CertZ18.rmwLatest (memberP N c) (logP c) ∧ agreeX GF.gfGd.gdG (memberP N c) X ∧
      CertZ24.agreeW4 GF.gfGd.gdG (memberP N c) (fun _ => False) ∧
      (∀ L, CertZ18.agreeW3 GF.gfGd.gdG (memberP N c) L) ∧
      (ExValGF GF.gfGd.gdG X → valEqX GF.gfGd.gdG (memberP N c) X) := by
  obtain ⟨c, hc, hv, hP, hfin, hdr, -⟩ := walkRunP GF N img X rdG hW hS
  subst hc
  exact ⟨c, rfl, hv, hdr, memberOfRun SbPol.epoch N _ X _ c hv hW.cat.wf hW.imgEq hW.len hP hfin hdr⟩

/-- The design's source gate meets the read-gate obligations at every invariant candidate. -/
theorem srcIfc (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (hW : WalkHyp GF N img X)
    (c : CandW) (hv : validW SbPol.epoch c) (hc : c.img = img)
    (hP : PInv N img GF.gfGd.gdG X GF.gfDev (cur c)) :
    RdSound GF.gfGd.gdG (srcGate GF.gfGd.gdG) c ∧
    (∀ x aq base ts vs, gxLbl GF.gfGd.gdG (hd (cur c) x) = some (LLoad aq base ts vs) →
      srcGate GF.gfGd.gdG (cur c) x base ts vs → srcGate GF.gfGd.gdG (cur c) x base ts vs) :=
  ⟨srcSound SbPol.epoch _ X c hv hP.pf hW.cat.wf hW.cat.lv (hW.imgEq.trans hc.symm),
    fun _ _ _ _ _ _ h => h⟩

/-- The value gate meets the read-gate obligations at every invariant candidate. -/
theorem valIfc (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (hW : WalkHyp GF N img X)
    (c : CandW) (hv : validW SbPol.epoch c)
    (hP : PInv N img GF.gfGd.gdG X GF.gfDev (cur c)) :
    RdSound GF.gfGd.gdG valGate c ∧
    (∀ x aq base ts vs, gxLbl GF.gfGd.gdG (hd (cur c) x) = some (LLoad aq base ts vs) →
      srcGate GF.gfGd.gdG (cur c) x base ts vs → valGate (cur c) x base ts vs) :=
  ⟨valSound SbPol.epoch _ c hv hW.cat.wf,
    fun x aq base ts vs hl hs => valGateMono hP hW.cat.wf hW.cat.lv hW.imgEq x aq base ts vs hl hs⟩

end SbOrd

end Weak
