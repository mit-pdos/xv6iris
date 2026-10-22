/-
Weak: **the S-R `DomAt` lift, increment I-3 — `SbProgR`, PROGRESS under the S-R gate (`noStuckR`)**
(ruling [OWN.150]; `PROGRESS-DomAt.md` §0.2; `PROGRESS-SPSR.md` §7 step 3).  Lean-only, no Rocq twin.
A leaf: nothing registered imports this file.

**Spec, stated first.**  Under the S-R gate no item waits for a READ: a landing waits for older own
entries (riscv.cat rules 1, 4) and for GF's earlier writes (S-P: co ⊆ gmo, gmo|W total); a plain load waits
only for its SOURCE to land (rfe ⊆ gmo, load value).  So the measure counts only fabric members and WRITES
(`waitedOnR`), the (E3)/(E3w) edges of `SbOrd` disappear, and the per-head table's row H3 shrinks to its
WRITE half `HeadOrdW` (a blocked plain load is gmo-before every later write / fabric member of its row —
`SbHeadHop.WrHop`'s shape, PROVED per census site from rules 11 and 4 + the census; F-6m-1 / [OWN.124]'s
`mycpu` frame spills are the known exception, which is why the `holding+0x12` read stays EXEMPT).

  §1  the measure `muR` and its target lemmas.
  §2  the named inputs: **`NoAqLd`** (image census, finding F-DomAt-1: no plain `.aq` load — in this
      alphabet `lr.aq`'s access kind; xv6 has no LR/SC) and **`HeadOrdW`** (row H3′, per state).
  §3  the blocked items: a landing (E1 rule 1/4; S-P `SpikeSP.nextW`), a fence (row H2), an AMO (E6, S-P;
      row H1), a load (rfe, the own-forwarding case), a fabric member (R3).
  §4  **`noStuckR`**: at every non-final S-R walk state some genuine item is ENABLED.

Spec: FAITHFUL (proof organisation over riscv.cat rules 1, 4, 5, load value, co ⊆ gmo; the trusted
residue (R1)/(R2)/(R2″)/(R3) as in `SbOrd`).  Lean-only helpers `SbOrdR.*`.
-/
import Weak.SbArmR

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SbOrdR

open SbWalk SbAgree SbReplay SbOrd SpikeSP SbDom

/-! # 1. The measure -/

/-- **AN EVENT AN S-R ITEM CAN WAIT ON**: a fabric member or a write (no reads: the S-R gate never waits for
one). -/
def waitedOnR (G : Gexec) (dev : List Geid) (m : Geid) : Prop := m ∈ dev ∨ gisW G m = true

open Classical in
/-- **THE S-R MEASURE**: a landing — its store's gmo position; a head — the least gmo position of an
unrealized waited-on event of its row (`|gmo|` if none). -/
noncomputable def muR (G : Gexec) (dev : List Geid) (w : WS) : Tgt → Nat
  | .hd x => minPos G G.gxGmo.length
      (G.gxGmo.filter (fun e => decide (e.1 = x ∧ ¬ realized w e ∧ waitedOnR G dev e)))
  | .ld i k =>
    match (w.pend i)[k]? with
    | some p => gpos G (i, p.1)
    | none => G.gxGmo.length

section Mu

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

theorem muRHdLe (e : Geid) : e ∈ G.gxGmo → ¬ realized w e → waitedOnR G dev e →
    muR G dev w (.hd e.1) ≤ gpos G e :=
  fun hm hr hw => minPosLe G _ _ e (List.mem_filter.2 ⟨hm, by simp [hr, hw]⟩)

theorem muRHdGt (x n : Nat) : n < G.gxGmo.length →
    (∀ e, e ∈ G.gxGmo → e.1 = x → ¬ realized w e → waitedOnR G dev e → n < gpos G e) →
    n < muR G dev w (.hd x) :=
  fun hd h => minPosGt G _ n _ hd (fun e he => by
    obtain ⟨h1, h2⟩ := List.mem_filter.1 he
    simp only [decide_eq_true_eq] at h2
    exact h e h1 h2.1 h2.2.1 h2.2.2)

theorem muRLd (i k : Nat) (p : Nat × SbEnt) : (w.pend i)[k]? = some p → muR G dev w (.ld i k) = gpos G (i, p.1) := by
  intro h; simp [muR, h]

theorem pendAgR (hP : PInvR N img G X dev w) (i : Nat) (p : Nat × SbEnt) : p ∈ w.pend i → i < N := by
  intro hp
  have := pendRealizedR hP i p hp
  exact hP.ag i (fun h => by unfold realized at this; rw [h] at this; simp at this)

theorem tgtEvR (hwf : gwf G) (hN : G.gxProg.length = N) (m : Geid) :
    m ∈ G.gxGmo → ¬ realized w m → waitedOnR G dev m →
    validT N G w (.hd m.1) ∧ muR G dev w (.hd m.1) ≤ gpos G m := by
  intro hm hr hwo
  refine ⟨?_, muRHdLe m hm hr hwo⟩
  obtain ⟨l, hl, -⟩ := (hwf.2.1 m).1 hm
  unfold gxLbl at hl
  cases hrow : G.gxProg[m.1]? with
  | none => rw [hrow] at hl; cases hl
  | some row =>
    rw [hrow] at hl
    simp only [Option.bind_some] at hl
    refine ⟨by rw [← hN]; exact lookup_lt_Some hrow, ?_⟩
    rw [List.getD_eq_getElem?_getD, hrow]
    simp only [Option.getD_some]
    unfold realized at hr
    have := lookup_lt_Some hl
    omega

theorem tgtPendR (hP : PInvR N img G X dev w) (i k : Nat) (p : Nat × SbEnt) :
    (w.pend i)[k]? = some p → validT N G w (.ld i k) ∧ muR G dev w (.ld i k) = gpos G (i, p.1) :=
  fun h => ⟨⟨pendAgR hP i p (List.mem_of_getElem? h), p, h⟩, muRLd i k p h⟩

theorem tgtER (hwf : gwf G) (hN : G.gxProg.length = N) (m : Geid) (n : Nat) :
    m ∈ G.gxGmo → ¬ realized w m → waitedOnR G dev m → gpos G m < n →
    ∃ B, validT N G w B ∧ muR G dev w B < n := by
  intro hm hr hwo hlt
  obtain ⟨hv, hle⟩ := tgtEvR hwf hN m hm hr hwo
  exact ⟨_, hv, by omega⟩

/-- A GF write that has not landed is unrealized or pending. -/
theorem unlandedR (hP : PInvR N img G X dev w) (s : Geid) :
    s ∈ gwrites G → s ∉ wrW w →
    ¬ realized w s ∨ ∃ (k : Nat) (p : Nat × SbEnt), (w.pend s.1)[k]? = some p ∧ p.1 = s.2 := by
  intro hs hn
  by_cases hr : realized w s
  · right
    obtain ⟨l', hl'⟩ : ∃ l', (w.rows s.1)[s.2]? = some l' := ⟨_, List.getElem?_eq_getElem hr⟩
    obtain ⟨l, hl, hrel⟩ := hP.pf.1 s.1 s.2 l' hl'
    have hlw : lbIsW l = true := by
      have := ((gwritesElemOf G s).1 hs).2
      unfold gisW at this; rw [show gxLbl G s = gxLbl G (s.1, s.2) from rfl, hl] at this; exact this
    have hlw' : lbIsW l' = true := by rw [relXIsW _ l l' hrel]; exact hlw
    rcases hP.inv.memIn s.1 s.2 l' hl' (memOfWr _ hlw') with h | h
    · exact absurd (List.mem_filter.2 ⟨h, by unfold rwW; rw [hl']; exact hlw'⟩) hn
    · obtain ⟨p, hp, hp1⟩ := List.mem_map.1 h
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hp
      exact ⟨k, p, hk, hp1⟩
  · exact .inl hr

/-- **AN UNLANDED GF WRITE BELOW A BOUND YIELDS A GENUINE ITEM BELOW IT.** -/
theorem tgtWR (hP : PInvR N img G X dev w) (hwf : gwf G) (hN : G.gxProg.length = N) (s : Geid) (n : Nat) :
    s ∈ gwrites G → s ∉ wrW w → gpos G s < n → ∃ B, validT N G w B ∧ muR G dev w B < n := by
  intro hs hn hlt
  have hsm := ((gwritesElemOf G s).1 hs).1
  rcases unlandedR hP s hs hn with hr | ⟨k, p, hk, hp1⟩
  · exact tgtER hwf hN s n hsm hr (.inr ((gwritesElemOf G s).1 hs).2) hlt
  · obtain ⟨hv, heq⟩ := tgtPendR hP s.1 k p hk
    refine ⟨_, hv, ?_⟩
    rw [heq, hp1]; exact hlt

/-- A head gmo-before every later waited-on event of its row: a target below the head is below its
measure. -/
theorem headBoundR (hwf : gwf G) (x : Nat) (l : Lbl) (n : Nat) :
    gxLbl G (hd w x) = some l → lbIsMem l = true →
    (∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → waitedOnR G dev m → gmoLt G (hd w x) m) →
    n < gpos G (hd w x) → n < muR G dev w (.hd x) := by
  intro hl hm hord hn
  have he := lblGmo G _ l hwf hl hm
  refine muRHdGt x n (Nat.lt_trans hn (gposLtLen G _ he)) (fun m hmG hmx hmr hwo => ?_)
  unfold realized at hmr
  by_cases heq : m.2 = (hd w x).2
  · have : m = hd w x := Prod.ext hmx heq
    subst this; exact hn
  · have hlt : (hd w x).2 < m.2 := by unfold hd at heq ⊢; rw [hmx] at hmr; omega
    exact Nat.lt_trans hn (hord m hmG hmx hlt hwo).2.2

end Mu

/-! # 2. The named inputs -/

/-- **NO PLAIN `.aq` LOAD (NAMED, image census; finding F-DomAt-1)**: GF has no `LLoad true` — in this
alphabet the access kind of `lr.aq` (`WeakRvwmoGraph.lbRcsc`'s doc); xv6's text has no LR/SC (the image half
is a census over the text walk, like `SbOrd.imgAmoAq`; the transport is the realization's). -/
def NoAqLd (G : Gexec) : Prop := ∀ e base ts vs, gxLbl G e ≠ some (LLoad true base ts vs)

/-- **ROW H3′ — THE S-R BLOCKED READ (NAMED; the only per-state residue of `noStuckR`)**: at walk state `w`,
a non-exempt plain-load head BLOCKED by the S-R read gate (a byte whose GF source has not landed, or a
forwarded byte with another value) is gmo-before every later fabric member or WRITE of its row — the write
half of `SbOrd.HeadOrdRd` (no reads: nothing waits on one). -/
def HeadOrdW (G : Gexec) (X : Geid → Prop) (dev : List Geid) (w : WS) : Prop :=
  ∀ x base ts vs, gxLbl G (hd w x) = some (LLoad false base ts vs) → ¬ X (hd w x) →
    ¬ srGate G w x false base ts vs →
    ∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → waitedOnR G dev m → gmoLt G (hd w x) m

/-! # 3. The blocked items -/

section Blk

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

theorem pendWritesR (hP : PInvR N img G X dev w) (i : Nat) (p : Nat × SbEnt) (a : Int) :
    p ∈ w.pend i → (msgByte p.2.msg a).isSome → ∃ u, gwritesByte G (i, p.1) a u := by
  intro hp hs
  obtain ⟨rl, base, vs, kc, hl, -, hm⟩ := pendLblR hP i p hp
  rw [hm] at hs
  obtain ⟨j, hj, rfl⟩ := msgByteIndex base vs _ _ a hs
  exact ⟨vs[j], _, base, vs, j, hl, rfl, List.getElem?_eq_getElem hj, rfl⟩

theorem pendWritesVR (hP : PInvR N img G X dev w) (i : Nat) (p : Nat × SbEnt) (a : Int) (u : BitVec 8) :
    p ∈ w.pend i → msgByte p.2.msg a = some u → gwritesByte G (i, p.1) a u := by
  intro hp hs
  obtain ⟨rl, base, vs, kc, hl, -, hm⟩ := pendLblR hP i p hp
  rw [hm] at hs
  obtain ⟨j, hj, rfl⟩ := msgByteIndex base vs _ _ _ (by rw [hs]; rfl)
  rw [msgByteVal] at hs
  exact ⟨_, base, vs, j, hl, rfl, hs, rfl⟩

theorem pendCoversR (hP : PInvR N img G X dev w) (i : Nat) (p : Nat × SbEnt) (a : Int) (u : BitVec 8) :
    p ∈ w.pend i → gwritesByte G (i, p.1) a u → (msgByte p.2.msg a).isSome = true := by
  intro hp hw
  obtain ⟨rl, base, vs, kc, hl, -, hm⟩ := pendLblR hP i p hp
  obtain ⟨l, base', vs', j, hl', hwr, hv, ha⟩ := hw
  rw [hl, Option.some.injEq] at hl'
  subst hl'
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
  obtain ⟨rfl, rfl⟩ := hwr
  rw [hm, ← ha, msgByteVal, hv]; rfl

theorem fwdOfCoverR (hP : PInvR N img G X dev w) (x : Nat) (q : Nat × SbEnt) (a : Int) :
    q ∈ w.pend x → (msgByte q.2.msg a).isSome = true → SbCand.fwdByte (w.σ.sb x) a ≠ none := by
  intro hq hc
  rw [hP.inv.sb x]
  rcases fwdRel (w.pend x) a with ⟨h1, -⟩ | ⟨p, -, -, h2, h3⟩
  · rw [fwdIdFold] at h1
    have := fwdFoldNone a _ none h1 q hq
    rw [hc] at this; cases this
  · rw [h2]; intro h; rw [h] at h3; cases h3

/-- A GF write of `a` that has not landed (at the byte) is unrealized or pending. -/
theorem unlandedAR (hP : PInvR N img G X dev w) (a : Int) (s : Geid) :
    gwrB G a s = true → s ∉ wrAtW w a →
    ¬ realized w s ∨ ∃ (k : Nat) (p : Nat × SbEnt), (w.pend s.1)[k]? = some p ∧ p.1 = s.2 := by
  intro hw hn
  by_cases hr : realized w s
  · right
    obtain ⟨l', hl'⟩ : ∃ l', (w.rows s.1)[s.2]? = some l' := ⟨_, List.getElem?_eq_getElem hr⟩
    obtain ⟨l, hl, hrel⟩ := hP.pf.1 s.1 s.2 l' hl'
    have hwl : wrsB l' a = true := by
      rw [wrsBEq _ l l' a hrel]; simp only [gwrB, hl] at hw; exact hw
    rcases hP.inv.memIn s.1 s.2 l' hl' (memOfWr _ (wrsBOfWr _ _ hwl)) with h | h
    · exact absurd (List.mem_filter.2 ⟨h, by simp only [rwrB, hl']; exact hwl⟩) hn
    · obtain ⟨p, hp, hp1⟩ := List.mem_map.1 h
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hp
      exact ⟨k, p, hk, hp1⟩
  · exact .inl hr

/-- A blocked write waits for GF's next unlanded write, strictly gmo-before it (S-P). -/
theorem nextTgtR (hP : PInvR N img G X dev w) (hc : CatH G) (hN : G.gxProg.length = N) (s : Geid) :
    s ∈ gwrites G → s ∉ wrW w → ¬ (wrW w ++ [s] <+: gwrites G) →
    ∃ B, validT N G w B ∧ muR G dev w B < gpos G s := by
  intro hs hsW hno
  obtain ⟨n, hnG, hnW, hlt⟩ := nextW _ w s hP.spw hc.wf.1 hs hsW hno
  exact tgtWR hP hc.wf hN n _ hnG hnW hlt

/-- **THE BLOCKED S-R LANDING** (edges (E1) rule 1 / rule 4, S-P co ⊆ gmo ∩ gmo|W): a genuine item of
strictly smaller measure — no reader edge. -/
theorem blkLandR (hP : PInvR N img G X dev w) (hc : CatH G) (hN : G.gxProg.length = N) (i k : Nat)
    (p : Nat × SbEnt) (hp : (w.pend i)[k]? = some p) (hb : ¬ landR SbPol.epoch G w i k) :
    ∃ B, validT N G w B ∧ muR G dev w B < gpos G (i, p.1) := by
  have hpm : p ∈ w.pend i := List.mem_of_getElem? hp
  obtain ⟨rl, base, vs, kc, hl, hrow, hmsg⟩ := pendLblR hP i p hpm
  have hsb : w.σ.sb i = (w.pend i).map Prod.snd := hP.inv.sb i
  by_cases hok : SbPol.epoch.landOk (w.σ.sb i) k
  · have hno : ¬ (wrW w ++ [(i, p.1)] <+: gwrites G) := fun h => hb ⟨p, hp, hok, h⟩
    have hs : (i, p.1) ∈ gwrites G :=
      (gwritesElemOf _ _).2 ⟨lblGmo _ _ _ hc.wf hl rfl, by unfold gisW; rw [hl]; rfl⟩
    have hsW : (i, p.1) ∉ wrW w := fun h => hP.inv.pendGmo i p hpm (List.mem_filter.1 h).1
    exact nextTgtR hP hc hN _ hs hsW hno
  · -- (E1): an older own entry of an earlier epoch or overlapping
    have hk : k < (w.σ.sb i).length := by
      rw [hsb, List.length_map]; exact lookup_lt_Some hp
    have hsbk : (w.σ.sb i)[k]? = some p.2 := by rw [hsb, List.getElem?_map, hp]; rfl
    obtain ⟨k', e', e, hk', h1, h2, hne⟩ : ∃ k' e' e, k' < k ∧ (w.σ.sb i)[k']? = some e' ∧
        (w.σ.sb i)[k]? = some e ∧ ¬ (e'.fs = e.fs ∧ ¬ SbEnt.overlaps e' e) := by
      refine Classical.byContradiction (fun hn => hok ⟨hk, fun k' e' e hk' h1 h2 => ?_⟩)
      exact Classical.byContradiction (fun h => hn ⟨k', e', e, hk', h1, h2, h⟩)
    rw [hsbk, Option.some.injEq] at h2
    subst h2
    obtain ⟨p', hp', rfl⟩ : ∃ p', (w.pend i)[k']? = some p' ∧ p'.2 = e' := by
      rw [hsb, List.getElem?_map] at h1
      cases hq : (w.pend i)[k']? with
      | none => rw [hq] at h1; cases h1
      | some q => rw [hq] at h1; exact ⟨q, rfl, Option.some.inj h1⟩
    have hp'm : p' ∈ w.pend i := List.mem_of_getElem? hp'
    have htag : p'.1 < p.1 :=
      pairwiseLt _ k' k _ _ (hP.ord i) (by rw [List.getElem?_map, hp']; rfl)
        (by rw [List.getElem?_map, hp]; rfl) hk'
    obtain ⟨rl', base', vs', kc', hl', -, hmsg'⟩ := pendLblR hP i p' hp'm
    have hpo : WeakRvwmoGraph.gpo G (i, p'.1) (i, p.1) := SBAcq.gpoOf G _ _ _ _ hl' hl rfl htag
    have hlt : gmoLt G (i, p'.1) (i, p.1) := by
      by_cases hfs : p'.2.fs = p.2.fs
      · have hov : SbEnt.overlaps p'.2 p.2 := Classical.byContradiction (fun h => hne ⟨hfs, h⟩)
        obtain ⟨j, hj, hs⟩ := hov
        rw [hmsg] at hj hs
        obtain ⟨u', hu'⟩ := pendWritesR hP i p' _ hp'm hs
        exact rule1Lt G _ _ _ vs[j] hc.ppo hpo (.inl ⟨u', hu'⟩)
          ⟨_, base, vs, j, hl, rfl, List.getElem?_eq_getElem hj, rfl⟩
      · obtain ⟨kf, pr, sr, hk1, hk2, hf⟩ := hP.fs2 i p p' hpm hp'm htag hfs
        exact SBAcq.fenceLt G _ _ _ _ kf pr true sr true hc.ppo hl' hl rfl hk1 hk2 hf rfl rfl
    obtain ⟨hv, heq⟩ := tgtPendR hP i k' p' hp'
    exact ⟨_, hv, by rw [heq]; exact hlt.2.2⟩

/-- **THE FABRIC-BLOCKED HEAD** (edge (Efab), the trusted (R3)). -/
theorem blkFabR (hc : CatH G) (hN : G.gxProg.length = N) (hwio : ∀ d, d ∈ dev → gmem G d)
    (hr3 : ∀ d e, gmem G d → gmem G e → before dev d e → gmoLt G d e) (x : Nat)
    (hb : ¬ fabOk dev w (hd w x)) : ∃ B, validT N G w B ∧ muR G dev w B < gpos G (hd w x) := by
  unfold fabOk at hb
  have hin : hd w x ∈ dev := Classical.byContradiction (fun h => hb (fun h' => absurd h' h))
  obtain ⟨d, hbd, hnr⟩ : ∃ d, before dev d (hd w x) ∧ ¬ realized w d := by
    refine Classical.byContradiction (fun hn => hb (fun _ d hd' => ?_))
    exact Classical.byContradiction (fun h => hn ⟨d, hd', h⟩)
  have hdm : d ∈ dev := by obtain ⟨i, -, hi, -, -⟩ := hbd; exact List.mem_of_getElem? hi
  have hlt := hr3 d _ (hwio d hdm) (hwio _ hin) hbd
  exact tgtER hc.wf hN d _ hlt.1 hnr (.inl hdm) hlt.2.2

/-- **ROW H2 (rule 4 + (R1))**: a draining fence head with a pending entry waits for the OLDEST entry,
gmo-before every later memory event of the row. -/
theorem blkFenceR (hP : PInvR N img G X dev w) (hc : CatH G) (hI : ImgFacts G)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hN : G.gxProg.length = N) (x : Nat) (pr pw sr sw : Bool)
    (hl : gxLbl G (hd w x) = some (LFence pr pw sr sw)) (hdr : SbCand.drains pw sr = true)
    (hne : w.σ.sb x ≠ []) : ∃ B, validT N G w B ∧ muR G dev w B < muR G dev w (.hd x) := by
  have hpw : pw = true := by simp [SbCand.drains] at hdr; exact hdr.1
  have hsr : sr = true := by simp [SbCand.drains] at hdr; exact hdr.2
  have hsw : sw = true := hI.fenceSw _ pr pw sr sw hl (by simp [hpw, hsr])
  obtain ⟨p0, ps, hps⟩ : ∃ p0 ps, w.pend x = p0 :: ps := by
    rw [hP.inv.sb x] at hne
    cases h : w.pend x with
    | nil => rw [h] at hne; exact absurd rfl hne
    | cons p0 ps => exact ⟨p0, ps, rfl⟩
  have hp0 : (w.pend x)[0]? = some p0 := by rw [hps]; rfl
  have hp0m : p0 ∈ w.pend x := List.mem_of_getElem? hp0
  obtain ⟨rl, base, vs, kc, hl0, -, -⟩ := pendLblR hP x p0 hp0m
  have hs0m : (x, p0.1) ∈ G.gxGmo := lblGmo G _ _ hc.wf hl0 rfl
  have hs0r := pendRealizedR hP x p0 hp0m
  obtain ⟨hv, heq⟩ := tgtPendR hP x 0 p0 hp0
  refine ⟨_, hv, ?_⟩
  rw [heq]
  refine muRHdGt x _ (gposLtLen G _ hs0m) (fun m hm hmx hmr _ => ?_)
  obtain ⟨lm, hlm, hmm⟩ := gwfGmoMem G m hc.wf hm
  unfold realized at hmr hs0r
  have hgt : (w.rows x).length < m.2 := by
    rw [hmx] at hmr
    rcases Nat.lt_or_ge (w.rows x).length m.2 with h | h
    · exact h
    · exfalso
      have : m = hd w x := Prod.ext hmx (by unfold hd; omega)
      rw [this, hl, Option.some.injEq] at hlm
      subst hlm; simp [lbIsMem, lbIsR, lbIsW, lbIsIo] at hmm
  have hpo : WeakRvwmoGraph.gpo G (x, p0.1) m :=
    SBAcq.gpoOf G _ m _ lm hl0 hlm hmx.symm (by simp only at hs0r; omega)
  by_cases hio : lbIsIo lm = true
  · exact (hr1 _ m hpo ⟨_, hl0, rfl⟩ (by unfold gisIo; rw [hl0]; rfl)
      (by unfold gisIo; rw [hlm]; exact hio)).2.2
  · have hrw : (lbIsR lm || lbIsW lm) = true := by
      cases lm <;> simp_all [lbIsMem, lbIsR, lbIsW, lbIsIo]
    refine (SBAcq.fenceLt G _ m _ lm (w.rows x).length pr pw sr sw hc.ppo hl0 hlm hmx.symm
      (by simp only at hs0r; omega) hgt hl (by simp [hpw, lbIsW]) ?_).2.2
    rw [hsr, hsw]; simpa using hrw

/-- **THE BLOCKED S-R AMO HEAD** (edges (E6) rule 1 / rule 4, S-P): a target strictly gmo-before it. -/
theorem blkAmoR (hP : PInvR N img G X dev w) (hc : CatH G) (hI : ImgFacts G) (hN : G.gxProg.length = N)
    (x : Nat) (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (kc : WmClass)
    (hl : gxLbl G (hd w x) = some (LRmw aq rl base ts rvs wvs kc))
    (hb : ¬ enbLR G X w (hd w x) (LRmw aq rl base ts rvs wvs kc)) :
    ∃ B, validT N G w B ∧ muR G dev w B < gpos G (hd w x) := by
  obtain ⟨-, hwl, -⟩ := rmwShape hc.wf _ aq rl base ts rvs wvs kc hl
  have hrl0 : rl = false := hI.noRl _ _ hl
  have hnr : SbCand.noRl (w.σ.sb x) := by
    intro e he
    rw [hP.inv.sb x] at he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact hP.nrl x p hp
  have hwr : ∀ j (hj : j < ts.length), gwritesByte G (hd w x) (accAddr base j) (wvs[j]'(by rw [hwl]; exact hj)) :=
    fun j hj => ⟨_, base, wvs, j, hl, rfl, List.getElem?_eq_getElem _, rfl⟩
  by_cases hB : SbCand.amoOk (w.σ.sb x) base ts.length
  · have hno : ¬ (wrW w ++ [hd w x] <+: gwrites G) :=
      fun h => hb ⟨hB, fun h' => by simp [hrl0] at h', fun _ => hnr, h⟩
    have hem : hd w x ∈ G.gxGmo := lblGmo _ _ _ hc.wf hl rfl
    have hs : hd w x ∈ gwrites G := (gwritesElemOf _ _).2 ⟨hem, by unfold gisW; rw [hl]; rfl⟩
    have hsW : hd w x ∉ wrW w := by
      intro h
      obtain ⟨l, hl', -⟩ := hP.inv.gmoMem _ (List.mem_filter.1 h).1
      unfold hd at hl'; simp at hl'
    exact nextTgtR hP hc hN _ hs hsW hno
  · obtain ⟨e', he', hbad⟩ : ∃ e', e' ∈ w.σ.sb x ∧ ¬ (e'.fs = 0 ∧ ¬ e'.hits base ts.length) := by
      refine Classical.byContradiction (fun hn => hB (fun e' he' => ?_))
      exact Classical.byContradiction (fun h => hn ⟨e', he', h⟩)
    rw [hP.inv.sb x] at he'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he'
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hp
    obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLblR hP x p hp
    have hpr := pendRealizedR hP x p hp
    unfold realized at hpr
    have hpo : WeakRvwmoGraph.gpo G (x, p.1) (hd w x) := SBAcq.gpoOf G _ _ _ _ hl' hl rfl hpr
    have hlt : gmoLt G (x, p.1) (hd w x) := by
      by_cases hfs : p.2.fs = 0
      · have hhit : p.2.hits base ts.length := Classical.byContradiction (fun h => hbad ⟨hfs, h⟩)
        obtain ⟨j, hj, hs⟩ := hhit
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hs
        exact rule1Lt G _ _ _ _ hc.ppo hpo (.inl ⟨u, pendWritesVR hP x p _ u hp hu⟩) (hwr j hj)
      · obtain ⟨kf, pr, sr, hk1, hk2, hf⟩ := hP.fs0 x p hp hfs
        exact SBAcq.fenceLt G _ _ _ _ kf pr true sr true hc.ppo hl' hl rfl hk1 hk2 hf rfl (by simp [lbIsW])
    obtain ⟨hv, heq⟩ := tgtPendR hP x k p hk
    exact ⟨_, hv, by rw [heq]; exact hlt.2.2⟩

/-- **THE BLOCKED S-R LOAD HEAD** (edge (E5) rfe ⊆ gmo; the own-forwarding case): if the S-R read gate fails,
a target strictly gmo-before the load. -/
theorem blkLoadR (hP : PInvR N img G X dev w) (hc : CatH G) (hN : G.gxProg.length = N) (x : Nat)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad false base ts vs)) (hns : ¬ srGate G w x false base ts vs) :
    ∃ B, validT N G w B ∧ muR G dev w B < gpos G (hd w x) := by
  obtain ⟨j, t, v, htj, hvj, hbad⟩ : ∃ j t v, ts[j]? = some t ∧ vs[j]? = some v ∧
      ¬ (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
        (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧ t ≤ (wrW w).length ∧
          (false = true → ∀ s, gwriteAt G t = some s → s.1 = x → gmoLt G s (hd w x)))) := by
    refine Classical.byContradiction (fun hn => hns (fun j t v h1 h2 => ?_))
    exact Classical.byContradiction (fun h => hn ⟨j, t, v, h1, h2, h⟩)
  have hrd : greadsByte G (hd w x) (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
  have hem : hd w x ∈ G.gxGmo := lblGmo G _ _ hc.wf hl rfl
  cases hf : SbCand.fwdByte (w.σ.sb x) (accAddr base j) with
  | none =>
    have hnl : (wrW w).length < t := by
      refine Nat.lt_of_not_le (fun h => hbad (.inr ⟨hf, h, fun h' => by cases h'⟩))
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    obtain ⟨⟨src, hs, hsw, hvis⟩, -⟩ := hc.lv _ _ _ _ hrd
    obtain ⟨hsG, hsix⟩ := gwriteAtInv G _ src hc.wf.1 hs
    have hsW : src ∉ wrW w := fun h => by
      have := wixLeOfPfx _ src hc.wf.1 hP.spw h; omega
    have hlt : gmoLt G src (hd w x) := by
      rcases hvis with h | h
      · exact h
      · exfalso
        have hsG' : src ∉ w.gmo := by
          intro hm
          refine hsW (List.mem_filter.2 ⟨hm, ?_⟩)
          obtain ⟨l', hl', -⟩ := hP.inv.gmoMem src hm
          obtain ⟨l, hlg, hrel⟩ := hP.pf.1 src.1 src.2 l' hl'
          unfold rwW; rw [hl']; show lbIsW l' = true; rw [relXIsW _ l l' hrel]
          obtain ⟨l0, b0, vs0, j0, hl0, hw0, -⟩ := hsw
          rw [show gxLbl G (src.1, src.2) = gxLbl G src from rfl, hl0, Option.some.injEq] at hlg
          subst hlg; cases l0 <;> simp_all [lbWr, lbIsW]
        exact fwdOfOwnUnlanded hP.inv hP.pf x src _ _ h.1 h.2.1 hsw hsG' hf
    exact tgtWR hP hc.wf hN src _ hsG hsW hlt.2.2
  | some v' =>
    have hv' : v' ≠ v := fun h => hbad (.inl (by rw [hf, h]))
    rcases fwdRel (w.pend x) (accAddr base j) with ⟨-, h2⟩ | ⟨p, hp, hid, h2, h3⟩
    · rw [← hP.inv.sb x, hf] at h2; cases h2
    · rw [← hP.inv.sb x, hf] at h2
      have hpr := pendRealizedR hP x p hp
      unfold realized at hpr
      obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLblR hP x p hp
      have hsw : gwritesByte G (x, p.1) (accAddr base j) v' := pendWritesVR hP x p _ v' hp h2.symm
      have hsW := gwritesOf G _ _ _ hc.wf hsw
      have hsm : (x, p.1) ∈ G.gxGmo := lblGmo G _ _ hc.wf hl' rfl
      have hpo : WeakRvwmoGraph.gpo G (x, p.1) (hd w x) := SBAcq.gpoOf G _ _ _ _ hl' hl rfl hpr
      obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := by
        cases t with
        | zero =>
          exfalso
          have := (hc.lv _ _ 0 v hrd).2 _ v' hsw (.inr hpo)
          have := gwixPos G _ hsW; omega
        | succ i => exact ⟨i, rfl⟩
      obtain ⟨⟨src, hs, hsrcw, hvis⟩, hmax⟩ := hc.lv _ _ _ _ hrd
      have hle := hmax _ v' hsw (.inr hpo)
      obtain ⟨hsrcG, hsrcIx⟩ := gwriteAtInv G _ src hc.wf.1 hs
      have hne : src ≠ (x, p.1) := by
        intro heq
        rw [heq] at hs
        have := fwdArm img G X w (hd w x) x p.1 _ _ v hP.inv hP.pf hc.lv hrd hs hid
        rw [this] at hf; exact hv' (Option.some.inj hf).symm
      have hix : gwix G (x, p.1) < gwix G src := by
        rcases Nat.lt_or_ge (gwix G (x, p.1)) (gwix G src) with h | h
        · exact h
        · exact absurd (SbOrd.gwixInj G _ _ hsrcG hsW (by omega)) hne
      have hgp := (gwixGposLt G _ _ hc.wf.1 hsW hsrcG).1 hix
      have hlt : gmoLt G src (hd w x) := by
        rcases hvis with h | h
        · exact h
        · exfalso
          have hsx : src.1 = x := h.1
          obtain ⟨hsb, hsrcm⟩ := gwrBOf G src _ _ hc.wf hsrcw
          have hsGa : (x, p.1) ∈ wrAtG G (accAddr base j) :=
            List.mem_filter.2 ⟨hsm, (gwrBOf G _ _ _ hc.wf hsw).1⟩
          have hsNW : (x, p.1) ∉ wrAtW w (accAddr base j) :=
            fun h' => hP.inv.pendGmo x p hp (List.mem_filter.1 h').1
          have hsrcNW : src ∉ wrAtW w (accAddr base j) :=
            fun h' => hsNW (landedDown G w _ _ src (hP.pf.2 _) hc.wf.1 h' hsGa hgp)
          have hsr : realized w src := by unfold realized; rw [hsx]; exact h.2.1
          rcases unlandedAR hP _ src hsb hsrcNW with h' | ⟨k, q, hq, hq1⟩
          · exact h' hsr
          · have hqm := List.mem_of_getElem? hq
            have hsrc : src = (src.1, q.1) := Prod.ext rfl hq1.symm
            have hcov : (msgByte q.2.msg (accAddr base j)).isSome = true := by
              rw [hsrc] at hsrcw; exact pendCoversR hP src.1 q _ v hqm hsrcw
            rw [hsx] at hqm
            have hmx := fwdFoldMax _ _ none p.1 (hP.ord x) hid q hqm hcov
            have hne2 : src.2 ≠ p.1 := fun h2 => hne (Prod.ext hsx h2)
            have hlt2 : src.2 < p.1 := by rw [← hq1] at hne2 ⊢; omega
            have hpo2 : WeakRvwmoGraph.gpo G src (x, p.1) := by
              obtain ⟨lsrc, hlsrc, -⟩ := gwfGmoMem G src hc.wf hsrcm
              exact SBAcq.gpoOf G _ _ _ _ hlsrc hl' hsx hlt2
            have := (rule1Lt G _ _ _ _ hc.ppo hpo2 (.inl ⟨_, hsrcw⟩) hsw).2.2
            omega
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hp
      obtain ⟨hv, heq⟩ := tgtPendR hP x k p hk
      exact ⟨_, hv, by rw [heq]; exact Nat.lt_trans hgp hlt.2.2⟩

/-- **THE BLOCKED I/O HEAD** ([OWN.152]; `SbOrd.blkIo` over `PInvR`; edge the trusted (R1)). -/
theorem blkIoR (hP : PInvR N img G X dev w) (hc : CatH G)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (x : Nat) (kd : IoKind) (base : Int) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LIo kd base vs)) (hne : w.σ.sb x ≠ []) :
    ∃ B, validT N G w B ∧ muR G dev w B < gpos G (hd w x) := by
  obtain ⟨p0, ps, hps⟩ : ∃ p0 ps, w.pend x = p0 :: ps := by
    rw [hP.inv.sb x] at hne
    cases h : w.pend x with
    | nil => rw [h] at hne; exact absurd rfl hne
    | cons p0 ps => exact ⟨p0, ps, rfl⟩
  have hp0 : (w.pend x)[0]? = some p0 := by rw [hps]; rfl
  have hp0m : p0 ∈ w.pend x := List.mem_of_getElem? hp0
  obtain ⟨rl, base0, vs0, kc, hl0, -, -⟩ := pendLblR hP x p0 hp0m
  have hs0r := pendRealizedR hP x p0 hp0m
  unfold realized at hs0r
  have hpo : WeakRvwmoGraph.gpo G (x, p0.1) (hd w x) := SBAcq.gpoOf G _ _ _ _ hl0 hl rfl hs0r
  have hlt := hr1 _ _ hpo ⟨_, hl0, rfl⟩ (by unfold gisIo; rw [hl0]; rfl) (by unfold gisIo; rw [hl]; rfl)
  obtain ⟨hv, heq⟩ := tgtPendR hP x 0 p0 hp0
  exact ⟨_, hv, by rw [heq]; exact hlt.2.2⟩

/-- **EVERY BLOCKED S-R HEAD WAITS FOR A GENUINE ITEM OF STRICTLY SMALLER MEASURE** — rows H1 (`aqOrd`),
H2 (`blkFenceR`), H4 (`ioOrd`, `stOrd`) PROVED, row H3′ the named `HeadOrdW`, `.aq` plain loads excluded by
the census `NoAqLd`. -/
theorem blkHeadR (hP : PInvR N img G X dev w) (hc : CatH G) (hI : ImgFacts G) (hNA : NoAqLd G)
    (hN : G.gxProg.length = N) (hwio : ∀ d, d ∈ dev → gmem G d)
    (hwio2 : ∀ d, d ∈ dev → gisWIo G d = true)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hr2 : ∀ s m, WeakRvwmoGraph.gpo G s m → gisIo G s = true → gisW G m = true → gmoLt G s m)
    (hr2'' : ∀ s m, WeakRvwmoGraph.gpo G s m → gisIo G s = true → gisR G m = true → gmoLt G s m)
    (hr3a : ∀ s m, gisIo G s = true → gisIo G m = true → WeakRvwmoGraph.gpo G s m → gmoLt G s m)
    (hr3 : ∀ d e, gmem G d → gmem G e → before dev d e → gmoLt G d e)
    (hR : HeadOrdW G X dev w) (hDS : DevStOrd G dev) (hDF : DevStFab G dev)
    (hHart : ∀ e, e ∈ dev → e.1 < NCPU → gisIo G e = true) (x : Nat)
    (hv : validT N G w (.hd x)) (hq : SbOrd.devQuiet w) (hb : ¬ enbR SbPol.epoch G X dev w (.hd x)) :
    ∃ B, validT N G w B ∧ muR G dev w B < muR G dev w (.hd x) := by
  obtain ⟨l, hl⟩ := lblOfValid x hv.2
  have hbound : ∀ n, lbIsMem l = true →
      (∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → waitedOnR G dev m → gmoLt G (hd w x) m) →
      n < gpos G (hd w x) → n < muR G dev w (.hd x) :=
    fun n hm hord hn => headBoundR hc.wf x l n hl hm hord hn
  have hall : (∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → gmoLt G (hd w x) m) →
      ∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → waitedOnR G dev m → gmoLt G (hd w x) m :=
    fun H m h1 h2 h3 _ => H m h1 h2 h3
  by_cases hf : fabOk dev w (hd w x)
  · have hnl : ¬ enbLR G X w (hd w x) l := fun h => hb ⟨hq, l, hl, hf, h⟩
    cases l with
    | LLoad aq base ts vs =>
      cases aq with
      | true => exact absurd hl (hNA _ base ts vs)
      | false =>
        have hX : ¬ X (hd w x) := fun hX => hnl (.inl hX)
        have hns : ¬ srGate G w x false base ts vs := fun hs => hnl (.inr ⟨hX, (fun h => by cases h), hs⟩)
        obtain ⟨B, hB, hlt⟩ := blkLoadR hP hc hN x base ts vs hl hns
        exact ⟨B, hB, hbound _ rfl (hR x base ts vs hl hX hns) hlt⟩
    | LStore rl base vs kc =>
      -- [OWN.151]: a device store issues only as GF's next write (it lands at once)
      have hrl : rl = false := by have := hI.noRl _ _ hl; simpa [lbRl] using this
      have hno : ¬ (NCPU ≤ x → wrW w ++ [hd w x] <+: gwrites G) :=
        fun h => hnl ⟨(fun h' => by rw [hrl] at h'; cases h'), h⟩
      have hx : NCPU ≤ x := Classical.byContradiction (fun h => hno (fun h' => absurd h' h))
      have hno' : ¬ (wrW w ++ [hd w x] <+: gwrites G) := fun h => hno (fun _ => h)
      have hem : hd w x ∈ G.gxGmo := lblGmo _ _ _ hc.wf hl rfl
      have hs : hd w x ∈ gwrites G := (gwritesElemOf _ _).2 ⟨hem, by unfold gisW; rw [hl]; rfl⟩
      have hsW : hd w x ∉ wrW w := by
        intro h
        obtain ⟨l', hl', -⟩ := hP.inv.gmoMem _ (List.mem_filter.1 h).1
        unfold hd at hl'; simp at hl'
      obtain ⟨B, hB, hlt⟩ := nextTgtR hP hc hN _ hs hsW hno'
      exact ⟨B, hB, hbound _ rfl (hall (stOrd hc hDS hHart x rl base vs kc hl (hDF _ rl base vs kc hx hl))) hlt⟩
    | LFence pr pw sr sw =>
      have hdr : SbCand.drains pw sr = true :=
        Classical.byContradiction (fun h => hnl (fun h' => absurd h' h))
      have hne : w.σ.sb x ≠ [] := fun h => hnl (fun _ => h)
      exact blkFenceR hP hc hI hr1 hN x pr pw sr sw hl hdr hne
    | LRmw aq rl base ts rvs wvs kc =>
      obtain ⟨B, hB, hlt⟩ := blkAmoR hP hc hI hN x aq rl base ts rvs wvs kc hl hnl
      have haq := hI.amoAq _ aq rl base ts rvs wvs kc hl
      subst haq
      exact ⟨B, hB, hbound _ rfl (hall (aqOrd hc x _ hl rfl)) hlt⟩
    | LIo kd base vs =>
      -- [OWN.152]: an I/O head waits for its row's oldest pending store ((R1))
      obtain ⟨B, hB, hlt⟩ := blkIoR hP hc hr1 x kd base vs hl hnl
      exact ⟨B, hB, hbound _ rfl (hall (ioOrd hc hr2 hr2'' hr3a x kd base vs hl)) hlt⟩
  · obtain ⟨B, hB, hlt⟩ := blkFabR hc hN hwio hr3 x hf
    have hin : hd w x ∈ dev := by
      unfold fabOk at hf
      exact Classical.byContradiction (fun h => hf (fun h' => absurd h' h))
    obtain ⟨l', hl', hm'⟩ := hwio _ hin
    rw [hl, Option.some.injEq] at hl'
    subst hl'
    refine ⟨B, hB, hbound _ hm' ?_ hlt⟩
    have hwi := hwio2 _ hin
    unfold gisWIo gisW gisIo at hwi
    rw [hl] at hwi
    cases l with
    | LIo kd base vs => exact hall (ioOrd hc hr2 hr2'' hr3a x kd base vs hl)
    | LStore rl base vs kc => exact hall (stOrd hc hDS hHart x rl base vs kc hl hin)
    | LRmw aq rl base ts rvs wvs kc =>
      have haq := hI.amoAq _ aq rl base ts rvs wvs kc hl
      subst haq
      exact hall (aqOrd hc x _ hl rfl)
    | LLoad _ _ _ _ => simp [lbIsW, lbIsIo] at hwi
    | LFence _ _ _ _ => simp [lbIsW, lbIsIo] at hwi

end Blk

/-! # 4. `noStuckR` -/

/-- A non-final S-R walk state has a genuine item. -/
theorem validOfNonFinalR {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid}
    {w : WS} (hP : PInvR N img G X dev w) :
    (∃ x, x < N ∧ (w.rows x).length < (G.gxProg.getD x []).length) ∨ (∃ i, w.pend i ≠ []) →
    ∃ T, validT N G w T := by
  rintro (⟨x, hx, hl⟩ | ⟨i, hi⟩)
  · exact ⟨.hd x, hx, hl⟩
  · obtain ⟨p, ps, hps⟩ : ∃ p ps, w.pend i = p :: ps := by
      cases h : w.pend i with
      | nil => exact absurd h hi
      | cons p ps => exact ⟨p, ps, rfl⟩
    exact ⟨.ld i 0, pendAgR hP i p (by rw [hps]; simp), p, by rw [hps]; rfl⟩

/-- **`noStuckR` — PROGRESS UNDER THE S-R GATE**: at every S-R walk state of a cat-consistent `GF` with the
walk invariant `PInvR`, if any work is left, SOME GENUINE ITEM IS ENABLED — under the per-address +
fence-epoch buffer [OWN.113], the trusted residue ((R1), (R2), (R2″) [OWN.116], (R3)), `gfDevWIo`, the
hart-row fabric fact, the image facts (rows H1/H2), the census `NoAqLd` (F-DomAt-1), the device-row store
order `DevStOrd` (row H4) and the blocked-read interface `HeadOrdW` (row H3′, NAMED: the WRITE half of
`SbOrd.HeadOrdRd`; no reader edge exists any more). -/
theorem noStuckR (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (w : WS)
    (hc : CatH GF.gfGd.gdG) (hio : ioResidueGmo GF) (hwio : gfDevWIo GF) (hI : ImgFacts GF.gfGd.gdG)
    (hNA : NoAqLd GF.gfGd.gdG)
    (hN : GF.gfGd.gdG.gxProg.length = N) (hP : PInvR N img GF.gfGd.gdG X GF.gfDev w)
    (hDS : DevStOrd GF.gfGd.gdG GF.gfDev) (hDF : DevStFab GF.gfGd.gdG GF.gfDev)
    (hHart : ∀ e, e ∈ GF.gfDev → e.1 < NCPU → gisIo GF.gfGd.gdG e = true)
    (hR : HeadOrdW GF.gfGd.gdG X GF.gfDev w) :
    ((∃ x, x < N ∧ (w.rows x).length < (GF.gfGd.gdG.gxProg.getD x []).length) ∨ (∃ i, w.pend i ≠ [])) →
    ∃ T, validT N GF.gfGd.gdG w T ∧ enbR SbPol.epoch GF.gfGd.gdG X GF.gfDev w T := by
  intro hne
  by_cases hnq : ¬ SbOrd.devQuiet w
  · -- [OWN.151]: a pending device store — its landing is the enabled item (the device unit)
    obtain ⟨i, hi, hpi⟩ : ∃ i, NCPU ≤ i ∧ w.pend i ≠ [] := by
      refine Classical.byContradiction (fun hn => hnq (fun i hi => ?_))
      exact Classical.byContradiction (fun h => hn ⟨i, hi, h⟩)
    obtain ⟨-, hlg, -⟩ := hP.du i hi hpi
    obtain ⟨p, hp, -⟩ := id hlg
    exact ⟨.ld i 0, ⟨pendAgR hP i p (List.mem_of_getElem? hp), p, hp⟩, .inr hi, hlg⟩
  have hq : SbOrd.devQuiet w := Classical.byContradiction hnq
  obtain ⟨A0, hA0⟩ := validOfNonFinalR hP hne
  have hwio' : ∀ d, d ∈ GF.gfDev → gmem GF.gfGd.gdG d :=
    fun d hd => WeakRvwmoLin2.wioGmem _ d (hwio d hd)
  have hr1 : ∀ s m, WeakRvwmoGraph.gpo GF.gfGd.gdG s m → gmem GF.gfGd.gdG s →
      gisIo GF.gfGd.gdG s = false → gisIo GF.gfGd.gdG m = true → gmoLt GF.gfGd.gdG s m :=
    fun s m hpo hgm hn hi => hio s m (.inl ⟨hpo, hgm, hn, hi⟩)
  have hr2 : ∀ s m, WeakRvwmoGraph.gpo GF.gfGd.gdG s m → gisIo GF.gfGd.gdG s = true →
      gisW GF.gfGd.gdG m = true → gmoLt GF.gfGd.gdG s m :=
    fun s m hpo hi hw => hio s m (.inr (.inl ⟨hpo, hi, hw⟩))
  have hr2'' : ∀ s m, WeakRvwmoGraph.gpo GF.gfGd.gdG s m → gisIo GF.gfGd.gdG s = true →
      gisR GF.gfGd.gdG m = true → gmoLt GF.gfGd.gdG s m :=
    fun s m hpo hi hr => hio s m (.inr (.inr (.inr (.inr (.inr ⟨hpo, hi, hr⟩)))))
  have hr3a : ∀ s m, gisIo GF.gfGd.gdG s = true → gisIo GF.gfGd.gdG m = true →
      WeakRvwmoGraph.gpo GF.gfGd.gdG s m → gmoLt GF.gfGd.gdG s m :=
    fun s m hi hj hpo => hio s m (.inr (.inr (.inr (.inl ⟨hi, hj, hpo⟩))))
  have hr3 : ∀ d e, gmem GF.gfGd.gdG d → gmem GF.gfGd.gdG e → before GF.gfDev d e →
      gmoLt GF.gfGd.gdG d e :=
    fun d e hd he hb => hio d e (.inr (.inr (.inr (.inr (.inl ⟨hd, he, hb⟩)))))
  refine SbOrd.descent (validT N GF.gfGd.gdG w) (enbR SbPol.epoch GF.gfGd.gdG X GF.gfDev w)
    (muR GF.gfGd.gdG GF.gfDev w) (fun A hv hb => ?_) A0 hA0
  cases A with
  | hd x =>
    obtain ⟨B, hB, hlt⟩ := blkHeadR hP hc hI hNA hN hwio' hwio hr1 hr2 hr2'' hr3a hr3 hR hDS hDF hHart x hv hq hb
    exact ⟨B, hB, .inr hlt⟩
  | ld i k =>
    obtain ⟨-, p, hp⟩ := hv
    obtain ⟨B, hB, hlt⟩ := blkLandR hP hc hN i k p hp (fun h => hb ⟨.inl hq, h⟩)
    exact ⟨B, hB, .inr (by rw [muRLd i k p hp]; exact hlt)⟩

end SbOrdR

end Weak
