/-
Weak: **allocproc route P, increment P-W3 (1/2) — `SbOrd`, THE GATE and PROGRESS (`noStuckP`)**
(`notes/weak-allocproc-routeP-design.md` §3.2 (the gate) and §3.4 (progress, restated per
`notes/weak-allocproc-plan-review-R45.md` §2.4); plan rev 55 row P-W3; rulings [OWN.106] (step by step,
no order premise), [OWN.112] (the two exempt `ip->ref` reads), [OWN.113] (the per-address + fence-epoch
buffer: `SbPol.epoch`)).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this file.

  §1  **THE GATE** at a walk machine state `w` (`SbWalk.WS`), over the class graph `G` with exempt reads
      `X` and fabric list `dev`: items `Tgt.hd x` (row `x`'s next GF event `hd w x`) and `Tgt.ld i k`
      (agent `i`'s `k`-th pending store).  `SbOrd.enb`: a fabric member waits until every earlier fabric
      member is realized (`fabOk`); per label (`enbL`): a plain load is EXEMPT (`X`, the `rdX` arm) or
      passes the READ GATE `rdG` (a PARAMETER: the design's source gate `srcGate` — every byte forwarded
      with GF's value or its GF source member-latest — or any weaker gate `rdG ⊇ srcGate`, e.g. the VALUE
      gate `valGate` of finding F-P-W3-1); a store issues unless `.rl` with a nonempty buffer; a fence
      waits for the drain when `pw ∧ sr`; an AMO (`wr`) needs its byte sources member-latest, every GF
      reader of them realized (`readersDone`), `amoOk`, the `.rl`/`.aq` buffer conditions; an I/O event
      always goes.  A landing (`landG`) needs `pol.landOk`, and at every byte it writes: landed list ++ it
      a GF co prefix, every GF reader of the current member-latest realized.
  §2  the walk-state invariant **`SbOrd.PInv`**: P-W2's bookkeeping `Inv`, prefix `pfx`, `exOk`, the
      rows bounded by GF's, the agent bound, and the four progress invariants — `rd` (an unrealized read
      whose GF source has landed reads the member-latest), `dvP` (realized fabric members are a prefix
      of `dev`), `ord` (pending tags in issue order), `fs0`/`fs2` (an entry's fence counter is nonzero
      / two entries' counters differ only across a `pw ∧ sw` fence of the row).
  §3  the measure `SbOrd.mu` (a landing: its store's gmo position; a head: the LEAST gmo position of
      an unrealized memory event of the row — so an edge INTO a head is free and the per-head table
      speaks only of edges OUT of blocked heads) and the abstract **`SbOrd.descent`**.
  §4  the per-head table as interfaces: **`SbOrd.HeadOrd`** — a BLOCKED memory head that is not an
      `.aq` read is gmo-before every later memory event of its row (rows H3 / H4 / H5 of R45's table;
      findings F-P-W3-1 / F-P-W3-2, `Weak/LitmusSbStuck.lean`: FALSE on xv6 shapes under the design's
      gate, so it stays NAMED); the image facts `SbOrd.ImgFacts` (G1 every AMO `.aq`, no `.rl`, every
      draining fence `sw`) — H1 (rule 5) and H2 (rule 4 + (R1)) are PROVED from them.

Spec: FAITHFUL (proof organisation over riscv.cat's rules 1, 4, 5, load value, atomicity, co ⊆ gmo, and
the trusted residue's (R1)/(R3)); the named items are listed in §4 with their marks.  Lean-only helpers
`SbOrd.*`.
-/
import Weak.SbReplay
import Weak.WeakRvwmoLin2
import Weak.LitmusSBAcq

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

namespace SbOrd

open SbWalk SbAgree SbReplay

/-! # 1. The gate -/

/-- Event `e` is realized at `w` (its row has stepped past it). -/
def realized (w : WS) (e : Geid) : Prop := e.2 < (w.rows e.1).length

instance (w : WS) (e : Geid) : Decidable (realized w e) := inferInstanceAs (Decidable (_ < _))

/-- Row `x`'s next GF event. -/
def hd (w : WS) (x : Nat) : Geid := (x, (w.rows x).length)

/-- A fabric member waits until every EARLIER fabric member is realized (fabric order). -/
def fabOk (dev : List Geid) (w : WS) (e : Geid) : Prop :=
  e ∈ dev → ∀ d, before dev d e → realized w d

/-- Every GF reader of byte `a`'s current member-latest write (other than `s`) is realized. -/
def readersDone (G : Gexec) (w : WS) (a : Int) (s : Geid) : Prop :=
  ∀ r t v, greadsByte G r a t v → srcLatest G w a t → r ≠ s → realized w r

/-- **THE DESIGN'S READ GATE** (§3.2 `rd`): every byte forwarded with GF's value, or not forwarded with
its GF source the member-latest write (P-W2's `loadArm` input). -/
def srcGate (G : Gexec) (w : WS) (x : Nat) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) : Prop :=
  ∀ j t v, ts[j]? = some t → vs[j]? = some v →
    SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
    (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧ srcLatest G w (accAddr base j) t)

/-- **THE VALUE GATE** (finding F-P-W3-1 (a)): the member's TOP bytes are GF's bytes. -/
def valGate (w : WS) (x : Nat) (base : Int) (_ts : List Nat) (vs : List (BitVec 8)) : Prop :=
  topVals w x base vs

/-- A read gate: a predicate on (state, agent, footprint, GF timestamps, GF values). -/
abbrev RdG : Type := WS → Nat → Int → List Nat → List (BitVec 8) → Prop

/-- **THE PER-LABEL GATE** of row `e.1`'s next event `e` with GF label `l`. -/
def enbL (G : Gexec) (X : Geid → Prop) (rdG : RdG) (w : WS) (e : Geid) : Lbl → Prop
  | LLoad aq base ts vs => X e ∨ (¬ X e ∧ (aq = true → SbCand.noRl (w.σ.sb e.1)) ∧ rdG w e.1 base ts vs)
  | LStore rl _ _ _ => rl = true → w.σ.sb e.1 = []
  | LFence _ pw sr _ => SbCand.drains pw sr = true → w.σ.sb e.1 = []
  | LRmw aq rl base ts _ _ _ =>
      (∀ j t, ts[j]? = some t →
        srcLatest G w (accAddr base j) t ∧ readersDone G w (accAddr base j) e) ∧
      SbCand.amoOk (w.σ.sb e.1) base ts.length ∧ (rl = true → w.σ.sb e.1 = []) ∧
      (aq = true → SbCand.noRl (w.σ.sb e.1))
  | LIo .. => True

/-- The gate's items: a row's next event, or a pending store. -/
inductive Tgt where
  | hd (x : Nat)
  | ld (i k : Nat)

/-- **THE LANDING GATE** (§3.2 `land`). -/
def landG (pol : SbPol) (G : Gexec) (w : WS) (i k : Nat) : Prop :=
  ∃ p, (w.pend i)[k]? = some p ∧ pol.landOk (w.σ.sb i) k ∧
    ∀ a, rwrB w.rows a (i, p.1) = true →
      wrAtW w a ++ [(i, p.1)] <+: wrAtG G a ∧ readersDone G w a (i, p.1)

/-- **THE GATE.** -/
def enb (pol : SbPol) (G : Gexec) (X : Geid → Prop) (rdG : RdG) (dev : List Geid) (w : WS) :
    Tgt → Prop
  | .hd x => ∃ l, gxLbl G (hd w x) = some l ∧ fabOk dev w (hd w x) ∧ enbL G X rdG w (hd w x) l
  | .ld i k => landG pol G w i k

/-- A genuine item: a row (an agent below `N`) with GF events left, or an existing pending entry. -/
def validT (N : Nat) (G : Gexec) (w : WS) : Tgt → Prop
  | .hd x => x < N ∧ (w.rows x).length < (G.gxProg.getD x []).length
  | .ld i k => i < N ∧ ∃ p, (w.pend i)[k]? = some p

/-! # 2. The walk-state invariant -/

/-- A GF read source at byte `a` (timestamp `t`) has LANDED: the image, or a landed write. -/
def landedSrc (G : Gexec) (w : WS) (a : Int) (t : Nat) : Prop :=
  t = 0 ∨ ∃ s, gwriteAt G t = some s ∧ s ∈ wrAtW w a

/-- A `pw ∧ sw` fence of row `i` strictly between positions `lo` and `hi` (GF's label). -/
def fenceSw (G : Gexec) (i lo hi : Nat) : Prop :=
  ∃ kf pr sr, lo < kf ∧ kf < hi ∧ gxLbl G (i, kf) = some (LFence pr true sr true)

/-- **THE WALK-STATE INVARIANT** of route P's gated walk. -/
structure PInv (N : Nat) (img : Image) (G : Gexec) (X : Geid → Prop) (dev : List Geid) (w : WS) :
    Prop where
  inv : Inv img w
  pf : pfx G X w
  ex : exOk X w
  len : ∀ x, (w.rows x).length ≤ (G.gxProg.getD x []).length
  ag : agOk N w
  rd : ∀ r a t v, greadsByte G r a t v → ¬ realized w r → landedSrc G w a t → srcLatest G w a t
  dvP : ∀ d d', before dev d d' → realized w d' → realized w d
  ord : ∀ i, ((w.pend i).map Prod.fst).Pairwise (· < ·)
  fs0 : ∀ i p, p ∈ w.pend i → p.2.fs ≠ 0 → fenceSw G i p.1 (w.rows i).length
  fs2 : ∀ i p p', p ∈ w.pend i → p' ∈ w.pend i → p'.1 < p.1 → p'.2.fs ≠ p.2.fs → fenceSw G i p'.1 p.1
  nrl : ∀ i p, p ∈ w.pend i → p.2.rl = false

/-! # 3. The measure and the descent -/

/-- The least of `gpos` over a list (`d` if empty). -/
def minPos (G : Gexec) (d : Nat) : List Geid → Nat
  | [] => d
  | e :: l => min (gpos G e) (minPos G d l)

theorem minPosLe (G : Gexec) (d : Nat) : ∀ (l : List Geid) (e : Geid), e ∈ l → minPos G d l ≤ gpos G e
  | [], _, h => by simp at h
  | f :: l, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (minPosLe G d l e h)

theorem minPosGt (G : Gexec) (d n : Nat) : ∀ (l : List Geid), n < d → (∀ e, e ∈ l → n < gpos G e) →
    n < minPos G d l
  | [], hd, _ => hd
  | f :: l, hd, h => Nat.lt_min.2 ⟨h f (by simp), minPosGt G d n l hd (fun e he => h e (by simp [he]))⟩

/-- **THE MEASURE**: a landing — its store's gmo position; a head — the least gmo position of an
unrealized memory event of its row (`|gmo|` if none). -/
def mu (G : Gexec) (w : WS) : Tgt → Nat
  | .hd x => minPos G G.gxGmo.length (G.gxGmo.filter (fun e => decide (e.1 = x ∧ ¬ realized w e)))
  | .ld i k =>
    match (w.pend i)[k]? with
    | some p => gpos G (i, p.1)
    | none => G.gxGmo.length

theorem muHdLe (G : Gexec) (w : WS) (e : Geid) :
    e ∈ G.gxGmo → ¬ realized w e → mu G w (.hd e.1) ≤ gpos G e :=
  fun hm hr => minPosLe G _ _ e (List.mem_filter.2 ⟨hm, by simp [hr]⟩)

theorem muHdGt (G : Gexec) (w : WS) (x n : Nat) : n < G.gxGmo.length →
    (∀ e, e ∈ G.gxGmo → e.1 = x → ¬ realized w e → n < gpos G e) → n < mu G w (.hd x) :=
  fun hd h => minPosGt G _ n _ hd (fun e he => by
    obtain ⟨h1, h2⟩ := List.mem_filter.1 he
    simp only [decide_eq_true_eq] at h2
    exact h e h1 h2.1 h2.2)

theorem muLd (G : Gexec) (w : WS) (i k : Nat) (p : Nat × SbEnt) :
    (w.pend i)[k]? = some p → mu G w (.ld i k) = gpos G (i, p.1) := by
  intro h; simp [mu, h]

/-- **THE DESCENT**: if every blocked genuine item waits for a genuine item that is enabled or has a
strictly smaller measure, some genuine item is enabled (whenever one exists). -/
theorem descent {T : Type} (valid enbT : T → Prop) (m : T → Nat)
    (h : ∀ A, valid A → ¬ enbT A → ∃ B, valid B ∧ (enbT B ∨ m B < m A)) :
    ∀ A, valid A → ∃ B, valid B ∧ enbT B := by
  suffices H : ∀ n A, m A ≤ n → valid A → ∃ B, valid B ∧ enbT B from fun A hA => H _ A (Nat.le_refl _) hA
  intro n
  induction n with
  | zero =>
    intro A hA hv
    by_cases he : enbT A
    · exact ⟨A, hv, he⟩
    · obtain ⟨B, hB, hB'⟩ := h A hv he
      rcases hB' with hB' | hB'
      · exact ⟨B, hB, hB'⟩
      · omega
  | succ n ih =>
    intro A hA hv
    by_cases he : enbT A
    · exact ⟨A, hv, he⟩
    · obtain ⟨B, hB, hB'⟩ := h A hv he
      rcases hB' with hB' | hB'
      · exact ⟨B, hB, hB'⟩
      · exact ih B (by omega) hB

/-! # 4. The per-head table: interfaces -/

/-- **THE IMAGE FACTS** the table uses, on GF's labels (NAMED: the image halves are `LockFacts.amoCensus`
(the only AMO is `acquire+0x1c`'s `amoswap.w.aq`, no `.rl`) and `LockFacts.fenceCensus` (the draining
fences are `fence iorw,iorw`); the transport label ↔ instruction is the realization's, of
`LockFacts2.lockReal` (L2)'s kind — G1 `kernelAmoAq` of R43 §4).  `amoAq` gives table row H1 (rule 5),
`fenceSw` row H2 (rule 4 + (R1)). -/
structure ImgFacts (G : Gexec) : Prop where
  amoAq : ∀ e aq rl base ts rvs wvs kc, gxLbl G e = some (LRmw aq rl base ts rvs wvs kc) → aq = true
  noRl : ∀ e l, gxLbl G e = some l → lbRl l = false
  fenceSw : ∀ e pr pw sr sw, gxLbl G e = some (LFence pr pw sr sw) → (pw && sr) = true → sw = true

/-- **THE PER-HEAD ORDER** (R45 table rows H3 / H4 / H5, NAMED): at walk state `w`, a BLOCKED memory head
that is not an `.aq` read is gmo-before every later memory event of its row.  FALSE on xv6 shapes under
the design's gate (`SbStuck.l5NoMemberP`: `holding+0x0` reading nonzero; `SbStuck.l6NoMember`: an I/O
head before a RAM read) — the lines are STOPPED (PROGRESS F-P-W3-1/2); it is the exact residue of
`noStuckP` once rows H1/H2, every landing edge and every edge into a head are proved. -/
def HeadOrd (pol : SbPol) (G : Gexec) (X : Geid → Prop) (rdG : RdG) (dev : List Geid) (w : WS) : Prop :=
  ∀ x l, gxLbl G (hd w x) = some l → lbIsMem l = true → ¬ enb pol G X rdG dev w (.hd x) →
    (lbIsR l && lbAq l) = false →
    ∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → gmoLt G (hd w x) m

/-! # 5. Basic facts -/

theorem posOfLt : ∀ (l : List Geid) (x : Geid), x ∈ l → posOf l x < l.length
  | [], _, h => by simp at h
  | y :: l, x, h => by
    unfold posOf
    by_cases hy : y = x
    · rw [if_pos hy]; simp
    · rw [if_neg hy]
      have := posOfLt l x (by rcases List.mem_cons.1 h with h | h; exact absurd h.symm hy; exact h)
      simp; omega

theorem posOfGet : ∀ (l : List Geid) (x : Geid), x ∈ l → l[posOf l x]? = some x
  | [], _, h => by simp at h
  | y :: l, x, h => by
    unfold posOf
    by_cases hy : y = x
    · rw [if_pos hy]; simp [hy]
    · rw [if_neg hy]
      simp only [List.getElem?_cons_succ]
      exact posOfGet l x (by rcases List.mem_cons.1 h with h | h; exact absurd h.symm hy; exact h)

theorem posOfApp : ∀ (l t : List Geid) (x : Geid), x ∈ l → posOf (l ++ t) x = posOf l x
  | [], _, _, h => by simp at h
  | y :: l, t, x, h => by
    show posOf (y :: (l ++ t)) x = posOf (y :: l) x
    unfold posOf
    by_cases hy : y = x
    · rw [if_pos hy, if_pos hy]
    · rw [if_neg hy, if_neg hy,
        posOfApp l t x (by rcases List.mem_cons.1 h with h | h; exact absurd h.symm hy; exact h)]

theorem posOfAppNot : ∀ (l t : List Geid) (x : Geid), x ∉ l → posOf (l ++ t) x = l.length + posOf t x
  | [], _, _, _ => by simp
  | y :: l, t, x, h => by
    have hy : ¬ y = x := fun e => h (by simp [e])
    rw [show posOf ((y :: l) ++ t) x = posOf (l ++ t) x + 1 from by simp [posOf, hy],
      posOfAppNot l t x (fun h' => h (List.mem_cons_of_mem _ h'))]
    simp; omega

theorem gposPosOf (G : Gexec) (e : Geid) :
    G.gxGmo.Nodup → e ∈ G.gxGmo → gpos G e = posOf G.gxGmo e :=
  fun hnd he => (posOfLookup _ _ e hnd (gposElemLookup G e he)).symm

theorem gposLtLen (G : Gexec) (e : Geid) : e ∈ G.gxGmo → gpos G e < G.gxGmo.length :=
  fun he => lookup_lt_Some (gposElemLookup G e he)

theorem wrAtGNodup (G : Gexec) (a : Int) : G.gxGmo.Nodup → (wrAtG G a).Nodup :=
  fun h => h.filter _

/-- In GF's write list of a byte, list order IS gmo order. -/
theorem wrAtGLt (G : Gexec) (a : Int) (x y : Geid) : G.gxGmo.Nodup → x ∈ wrAtG G a → y ∈ wrAtG G a →
    (posOf (wrAtG G a) x < posOf (wrAtG G a) y ↔ gpos G x < gpos G y) := by
  intro hnd hx hy
  obtain ⟨hxm, hxb⟩ := List.mem_filter.1 hx
  obtain ⟨hym, hyb⟩ := List.mem_filter.1 hy
  rw [gposPosOf G x hnd hxm, gposPosOf G y hnd hym]
  exact posFilter _ _ x y hnd hxm hym hxb hyb

/-- **THE LANDED LIST IS DOWNWARD CLOSED IN GMO** among GF's writes of the byte. -/
theorem landedDown (G : Gexec) (w : WS) (a : Int) (x y : Geid) :
    wrAtW w a <+: wrAtG G a → G.gxGmo.Nodup → y ∈ wrAtW w a → x ∈ wrAtG G a → gpos G x < gpos G y →
    x ∈ wrAtW w a := by
  rintro ⟨T, hT⟩ hnd hy hx hlt
  have hyG : y ∈ wrAtG G a := by rw [← hT]; exact List.mem_append_left _ hy
  have h1 := (wrAtGLt G a x y hnd hx hyG).2 hlt
  have h2 : posOf (wrAtG G a) y = posOf (wrAtW w a) y := by rw [← hT]; exact posOfApp _ _ y hy
  have h3 := posOfLt _ y hy
  have hlt' : posOf (wrAtG G a) x < (wrAtW w a).length := by omega
  have hget := posOfGet _ x hx
  rw [← hT] at hget hlt'
  rw [List.getElem?_append_left hlt'] at hget
  exact List.mem_of_getElem? hget

/-- The FIRST unlanded GF write of a byte, when a pending write `s` cannot land on top. -/
theorem nextUnlanded (G : Gexec) (w : WS) (a : Int) (s : Geid) :
    wrAtW w a <+: wrAtG G a → G.gxGmo.Nodup → s ∈ wrAtG G a → s ∉ wrAtW w a →
    ¬ (wrAtW w a ++ [s] <+: wrAtG G a) →
    ∃ n, n ∈ wrAtG G a ∧ n ∉ wrAtW w a ∧ gpos G n < gpos G s := by
  rintro ⟨T, hT⟩ hnd hs hsW hno
  cases T with
  | nil => rw [List.append_nil] at hT; rw [← hT] at hs; exact absurd hs hsW
  | cons n T' =>
    have hnG : n ∈ wrAtG G a := by rw [← hT]; simp
    have hnd' : (wrAtW w a ++ n :: T').Nodup := by rw [hT]; exact wrAtGNodup G a hnd
    have hnW : n ∉ wrAtW w a := fun h => (List.nodup_append.1 hnd').2.2 n h n (by simp) rfl
    by_cases hns : n = s
    · subst hns; exact absurd ⟨T', by rw [← hT, List.append_assoc]; rfl⟩ hno
    · refine ⟨n, hnG, hnW, (wrAtGLt G a n s hnd hnG hs).1 ?_⟩
      rw [← hT, posOfAppNot _ _ n hnW, posOfAppNot _ _ s hsW]
      have hsT : s ∈ n :: T' := by
        rw [← hT] at hs
        rcases List.mem_append.1 hs with h | h
        · exact absurd h hsW
        · exact h
      have : posOf (n :: T') n = 0 := by simp [posOf]
      have : posOf (n :: T') s = posOf T' s + 1 := by
        simp only [posOf, if_neg hns]
      omega

theorem wrsBOfWr (l : Lbl) (a : Int) : wrsB l a = true → lbIsW l = true := by
  intro h
  unfold wrsB at h
  cases l <;> simp_all [lbWr, lbIsW]

theorem wrsBEq (x : Prop) (l l' : Lbl) (a : Int) : lblRelX x l l' → wrsB l' a = wrsB l a := by
  intro h; unfold wrsB; rw [relXWr x l l' h]

theorem memOfWr (l : Lbl) : lbIsW l = true → lbIsMem l = true := by
  intro h; simp [lbIsMem, h]

section Inv

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- A pending entry's store: its member row label and GF's label are the same `LStore`. -/
theorem pendLbl (hP : PInv N img G X dev w) (i : Nat) (p : Nat × SbEnt) : p ∈ w.pend i →
    ∃ rl base vs kc, gxLbl G (i, p.1) = some (LStore rl base vs kc) ∧
      (w.rows i)[p.1]? = some (LStore rl base vs kc) ∧ p.2.msg = ⟨base, vs, some i, kc⟩ := by
  intro hp
  obtain ⟨rl, base, vs, kc, hrow, hmsg⟩ := hP.inv.pendSt i p hp
  obtain ⟨l, hl, hrel⟩ := hP.pf.1 i p.1 _ hrow
  rcases relXW _ l _ hrel (.inr rfl) with h | ⟨_, _, _, _, _, _, _, _, _, h, -⟩
  · rw [← h] at hl; exact ⟨rl, base, vs, kc, hl, hrow, hmsg⟩
  · cases h

theorem pendRealized (hP : PInv N img G X dev w) (i : Nat) (p : Nat × SbEnt) : p ∈ w.pend i →
    realized w (i, p.1) := by
  intro hp
  obtain ⟨_, _, _, _, _, hrow, _⟩ := pendLbl hP i p hp
  exact lookup_lt_Some hrow

theorem pendAg (hP : PInv N img G X dev w) (i : Nat) (p : Nat × SbEnt) : p ∈ w.pend i → i < N := by
  intro hp
  have := pendRealized hP i p hp
  exact hP.ag i (fun h => by unfold realized at this; rw [h] at this; simp at this)

/-- A GF write of `a` that has not landed is unrealized or pending. -/
theorem unlanded (hP : PInv N img G X dev w) (a : Int) (s : Geid) :
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

/-- **AN UNREALIZED EVENT IS A TARGET**: its row's head is genuine and measures at most its position. -/
theorem tgtEv (hwf : gwf G) (hN : G.gxProg.length = N) (m : Geid) :
    m ∈ G.gxGmo → ¬ realized w m → validT N G w (.hd m.1) ∧ mu G w (.hd m.1) ≤ gpos G m := by
  intro hm hr
  refine ⟨?_, muHdLe G w m hm hr⟩
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

/-- **A PENDING STORE IS A TARGET**: its landing is genuine and measures its position. -/
theorem tgtPend (hP : PInv N img G X dev w) (i k : Nat) (p : Nat × SbEnt) :
    (w.pend i)[k]? = some p → validT N G w (.ld i k) ∧ mu G w (.ld i k) = gpos G (i, p.1) :=
  fun h => ⟨⟨pendAg hP i p (List.mem_of_getElem? h), p, h⟩, muLd G w i k p h⟩

/-- **AN UNLANDED GF WRITE BELOW A BOUND YIELDS A GENUINE ITEM BELOW IT.** -/
theorem tgtW (hP : PInv N img G X dev w) (hwf : gwf G) (hN : G.gxProg.length = N) (a : Int)
    (s : Geid) (n : Nat) : gwrB G a s = true → s ∈ G.gxGmo → s ∉ wrAtW w a → gpos G s < n →
    ∃ B, validT N G w B ∧ mu G w B < n := by
  intro hw hm hn hlt
  rcases unlanded hP a s hw hn with hr | ⟨k, p, hk, hp1⟩
  · obtain ⟨hv, hle⟩ := tgtEv hwf hN s hm hr
    exact ⟨_, hv, by omega⟩
  · obtain ⟨hv, heq⟩ := tgtPend hP s.1 k p hk
    refine ⟨_, hv, ?_⟩
    rw [heq, hp1]; exact hlt

/-- An unrealized event at a gmo position below the bound. -/
theorem tgtE (hwf : gwf G) (hN : G.gxProg.length = N) (m : Geid) (n : Nat) :
    m ∈ G.gxGmo → ¬ realized w m → gpos G m < n → ∃ B, validT N G w B ∧ mu G w B < n := by
  intro hm hr hlt
  obtain ⟨hv, hle⟩ := tgtEv hwf hN m hm hr
  exact ⟨_, hv, by omega⟩

end Inv

/-! # 6. The cat facts the edges use -/

theorem pairwiseLt {α : Type} {R : α → α → Prop} : ∀ (l : List α) (i j : Nat) (a b : α),
    l.Pairwise R → l[i]? = some a → l[j]? = some b → i < j → R a b
  | [], _, _, _, _, _, h, _, _ => by simp at h
  | _ :: _, _, 0, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | x :: l, 0, j + 1, a, b, h, hi, hj, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact (List.pairwise_cons.1 h).1 b (List.mem_of_getElem? hj)
  | _ :: l, i + 1, j + 1, a, b, h, hi, hj, hij =>
    pairwiseLt l i j a b (List.pairwise_cons.1 h).2 hi hj (by omega)

/-- What progress uses of the model: well-formedness, rules 1/4/5 (`gppoCat6Gmo`), load value,
atomicity (`rvwmoCatAD`'s first four conjuncts). -/
structure CatH (G : Gexec) : Prop where
  wf : gwf G
  ppo : gppoCat6Gmo G
  lv : gloadValue G
  atom : gatomicity G

theorem rule1Lt (G : Gexec) (e1 e2 : Geid) (a : Int) (v : BitVec 8) : gppoCat6Gmo G →
    WeakRvwmoGraph.gpo G e1 e2 → gaccesses G e1 a → gwritesByte G e2 a v → gmoLt G e1 e2 :=
  fun hp hpo hacc hw => hp e1 e2 (Or.inl ⟨hpo, a, hacc, v, hw⟩)

theorem gwrBOf (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwf G → gwritesByte G e a v → gwrB G a e = true ∧ e ∈ G.gxGmo :=
  fun hwf h => let ⟨h1, _, h3⟩ := gwritesMem G e a v hwf h; ⟨h3, h1⟩

theorem gwrBTo (G : Gexec) (e : Geid) (a : Int) : gwrB G a e = true → ∃ v, gwritesByte G e a v := by
  unfold gwrB
  cases hl : gxLbl G e with
  | none => simp
  | some l =>
    intro h
    obtain ⟨base, vs, j, v, hw, hv, ha⟩ := (wrsBIff l a).1 h
    exact ⟨v, l, base, vs, j, hl, hw, hv, ha⟩

theorem lblGmo (G : Gexec) (e : Geid) (l : Lbl) : gwf G → gxLbl G e = some l → lbIsMem l = true →
    e ∈ G.gxGmo :=
  fun hwf hl hm => gwfMemGmo G e hwf ⟨l, hl, hm⟩

theorem gwritesOf (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) : gwf G → gwritesByte G e a v →
    e ∈ gwrites G :=
  fun hwf h => let ⟨h1, h2, _⟩ := gwritesMem G e a v hwf h; (gwritesElemOf G e).2 ⟨h1, h2⟩

theorem gwixPos (G : Gexec) (e : Geid) : e ∈ gwrites G → 1 ≤ gwix G e := by
  intro h; obtain ⟨i, -, hi⟩ := gwixLookup G e h; omega

theorem gwixInj (G : Gexec) (w1 w2 : Geid) : w1 ∈ gwrites G → w2 ∈ gwrites G →
    gwix G w1 = gwix G w2 → w1 = w2 := by
  intro h1 h2 he
  obtain ⟨i1, l1, e1⟩ := gwixLookup G w1 h1
  obtain ⟨i2, l2, e2⟩ := gwixLookup G w2 h2
  have : i1 = i2 := by omega
  subst this; rw [l1] at l2; exact Option.some.inj l2

theorem srcLatestUniq (G : Gexec) (w : WS) (a : Int) (t t' : Nat) : G.gxGmo.Nodup →
    srcLatest G w a t → srcLatest G w a t' → t = t' := by
  intro hnd h1 h2
  rcases h1 with ⟨rfl, h1⟩ | ⟨s1, hs1, hl1⟩ <;> rcases h2 with ⟨rfl, h2⟩ | ⟨s2, hs2, hl2⟩
  · rfl
  · rw [h1] at hl2; cases hl2
  · rw [h2] at hl1; cases hl1
  · rw [hl1, Option.some.injEq] at hl2
    subst hl2
    rw [← (gwriteAtInv G t s1 hnd hs1).2, ← (gwriteAtInv G t' s1 hnd hs2).2]

/-- An RMW's read source is co-before its own write. -/
theorem srcLtWrite {G : Gexec} (hc : CatH G) (e : Geid) (a : Int) (t : Nat) (v u : BitVec 8) :
    greadsByte G e a t v → gwritesByte G e a u → t < gwix G e := by
  intro hr hw
  have heW := gwritesOf G e a u hc.wf hw
  cases t with
  | zero => exact gwixPos G e heW
  | succ i =>
    obtain ⟨⟨src, hs, hsw, hvis⟩, -⟩ := hc.lv e a (i + 1) v hr
    have hsW := gwritesOf G src a _ hc.wf hsw
    have hlt : gmoLt G src e := by
      rcases hvis with h | h
      · exact h
      · exact rule1Lt G src e a u hc.ppo h (.inl ⟨_, hsw⟩) hw
    have := (gwixGposLt G src e hc.wf.1 hsW heW).2 hlt.2.2
    rw [(gwriteAtInv G (i + 1) src hc.wf.1 hs).2] at this
    exact this

/-- FROM-READS: a read whose source is co-before `s` (at the byte) is gmo-before `s`. -/
theorem frLtW {G : Gexec} (hc : CatH G) (r s : Geid) (a : Int) (t : Nat) (v u : BitVec 8) :
    greadsByte G r a t v → gwritesByte G s a u → t < gwix G s → r ≠ s → gmoLt G r s := by
  intro hr hw hlt hne
  have hrm := gwfMemGmo G r hc.wf (SBAcq.rdGmem G r a t v hr)
  have hsm := (gwrBOf G s a u hc.wf hw).2
  rcases gmoLtTotal G r s hc.wf.1 hrm hsm hne with h | h
  · exact h
  · have := (hc.lv r a t v hr).2 s u hw (.inl h); omega

/-! # 7. The blocked items -/

section Blk

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- A pending entry's store writes every byte its message covers (GF's label). -/
theorem pendWrites (hP : PInv N img G X dev w) (i : Nat) (p : Nat × SbEnt) (a : Int) :
    p ∈ w.pend i → (msgByte p.2.msg a).isSome → ∃ u, gwritesByte G (i, p.1) a u := by
  intro hp hs
  obtain ⟨rl, base, vs, kc, hl, -, hm⟩ := pendLbl hP i p hp
  rw [hm] at hs
  obtain ⟨j, hj, rfl⟩ := msgByteIndex base vs _ _ a hs
  exact ⟨vs[j], _, base, vs, j, hl, rfl, List.getElem?_eq_getElem hj, rfl⟩

/-- **THE BLOCKED LANDING** (edges (E1) rule 1 / rule 4 under the epoch buffer, (E2) co ⊆ gmo, (E3) fr):
it waits for a genuine item of strictly smaller measure — no census, no interface. -/
theorem blkLand (hP : PInv N img G X dev w) (hc : CatH G) (hN : G.gxProg.length = N) (i k : Nat)
    (p : Nat × SbEnt) (hp : (w.pend i)[k]? = some p) (hb : ¬ landG SbPol.epoch G w i k) :
    ∃ B, validT N G w B ∧ mu G w B < gpos G (i, p.1) := by
  have hpm : p ∈ w.pend i := List.mem_of_getElem? hp
  obtain ⟨rl, base, vs, kc, hl, hrow, hmsg⟩ := pendLbl hP i p hpm
  have hsm : (i, p.1) ∈ G.gxGmo := lblGmo G _ _ hc.wf hl rfl
  have hsb : w.σ.sb i = (w.pend i).map Prod.snd := hP.inv.sb i
  by_cases hok : SbPol.epoch.landOk (w.σ.sb i) k
  · -- the policy allows it: some written byte fails the co-prefix or the readers condition
    have hex : ∃ a, rwrB w.rows a (i, p.1) = true ∧
        ¬ (wrAtW w a ++ [(i, p.1)] <+: wrAtG G a ∧ readersDone G w a (i, p.1)) := by
      refine Classical.byContradiction (fun hn => hb ⟨p, hp, hok, fun a ha => ?_⟩)
      exact Classical.byContradiction (fun h => hn ⟨a, ha, h⟩)
    obtain ⟨a, ha, hbad⟩ := hex
    have hgw : gwrB G a (i, p.1) = true := by
      simp only [rwrB, hrow] at ha; simp only [gwrB, hl]; exact ha
    obtain ⟨u, hwu⟩ := gwrBTo G _ a hgw
    have hsG : (i, p.1) ∈ wrAtG G a := List.mem_filter.2 ⟨hsm, hgw⟩
    have hsW : (i, p.1) ∉ wrAtW w a := fun h => hP.inv.pendGmo i p hpm (List.mem_filter.1 h).1
    by_cases hpre : wrAtW w a ++ [(i, p.1)] <+: wrAtG G a
    · -- (E3): an unrealized GF reader of the current member-latest
      have hrd : ¬ readersDone G w a (i, p.1) := fun h => hbad ⟨hpre, h⟩
      obtain ⟨r, t, v, hr, hsl, hne, hnr⟩ : ∃ r t v, greadsByte G r a t v ∧ srcLatest G w a t ∧
          r ≠ (i, p.1) ∧ ¬ realized w r := by
        refine Classical.byContradiction (fun hn => hrd (fun r t v h1 h2 h3 => ?_))
        exact Classical.byContradiction (fun h4 => hn ⟨r, t, v, h1, h2, h3, h4⟩)
      have hlt : t < gwix G (i, p.1) := by
        rcases hsl with ⟨rfl, -⟩ | ⟨src, hs, hlast⟩
        · exact gwixPos G _ (gwritesOf G _ a u hc.wf hwu)
        · have hsrcW : src ∈ wrAtW w a := List.mem_of_getLast? hlast
          obtain ⟨T, hT⟩ := hpre
          have hsrcG : src ∈ wrAtG G a := by rw [← hT]; simp [hsrcW]
          have hp1 : posOf (wrAtG G a) src < posOf (wrAtG G a) (i, p.1) := by
            rw [← hT, List.append_assoc, posOfApp _ _ src hsrcW, posOfAppNot _ _ _ hsW]
            have := posOfLt _ src hsrcW
            omega
          have hg := (wrAtGLt G a src _ hc.wf.1 hsrcG hsG).1 hp1
          obtain ⟨hsrcGW, hsrcIx⟩ := gwriteAtInv G t src hc.wf.1 hs
          rw [← hsrcIx]
          exact (gwixGposLt G src _ hc.wf.1 hsrcGW (gwritesOf G _ a u hc.wf hwu)).2 hg
      have hrs := frLtW hc r (i, p.1) a t v u hr hwu hlt hne
      exact tgtE hc.wf hN r _ hrs.1 hnr hrs.2.2
    · -- (E2): the next unlanded GF write of the byte
      obtain ⟨n, hnG, hnW, hlt⟩ := nextUnlanded G w a _ (hP.pf.2 a) hc.wf.1 hsG hsW hpre
      obtain ⟨hnm, hnb⟩ := List.mem_filter.1 hnG
      exact tgtW hP hc.wf hN a n _ hnb hnm hnW hlt
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
    obtain ⟨rl', base', vs', kc', hl', -, hmsg'⟩ := pendLbl hP i p' hp'm
    have hpo : WeakRvwmoGraph.gpo G (i, p'.1) (i, p.1) := SBAcq.gpoOf G _ _ _ _ hl' hl rfl htag
    have hlt : gmoLt G (i, p'.1) (i, p.1) := by
      by_cases hfs : p'.2.fs = p.2.fs
      · -- rule 1: a common byte
        have hov : SbEnt.overlaps p'.2 p.2 := Classical.byContradiction (fun h => hne ⟨hfs, h⟩)
        obtain ⟨j, hj, hs⟩ := hov
        rw [hmsg] at hj hs
        obtain ⟨u', hu'⟩ := pendWrites hP i p' _ hp'm hs
        exact rule1Lt G _ _ _ vs[j] hc.ppo hpo (.inl ⟨u', hu'⟩)
          ⟨_, base, vs, j, hl, rfl, List.getElem?_eq_getElem hj, rfl⟩
      · -- rule 4: a `pw ∧ sw` fence between
        obtain ⟨kf, pr, sr, hk1, hk2, hf⟩ := hP.fs2 i p p' hpm hp'm htag hfs
        exact SBAcq.fenceLt G _ _ _ _ kf pr true sr true hc.ppo hl' hl rfl hk1 hk2 hf rfl rfl
    obtain ⟨hv, heq⟩ := tgtPend hP i k' p' hp'
    exact ⟨_, hv, by rw [heq]; exact hlt.2.2⟩

/-! ## 7.1 Forwarding: the youngest covering entry -/

def fwdF (a : Int) (o : Option Nat) (p : Nat × SbEnt) : Option Nat :=
  if (msgByte p.2.msg a).isSome then some p.1 else o

theorem fwdIdFold (ps : List (Nat × SbEnt)) (a : Int) : fwdId ps a = ps.foldl (fwdF a) none := rfl

theorem fwdFoldSome (a : Int) : ∀ (ps : List (Nat × SbEnt)) (r : Nat),
    ps.foldl (fwdF a) (some r) ≠ none
  | [], _ => by simp
  | q :: ps, r => by
    simp only [List.foldl_cons, fwdF]
    split
    · exact fwdFoldSome a ps _
    · exact fwdFoldSome a ps r

theorem fwdFoldNone (a : Int) : ∀ (ps : List (Nat × SbEnt)) (o : Option Nat),
    ps.foldl (fwdF a) o = none → ∀ q, q ∈ ps → (msgByte q.2.msg a).isSome = false
  | [], _, _, _, h => by simp at h
  | q0 :: ps, o, h, q, hq => by
    simp only [List.foldl_cons, fwdF] at h
    by_cases hc : (msgByte q0.2.msg a).isSome = true
    · rw [if_pos hc] at h; exact absurd h (fwdFoldSome a ps _)
    · rw [if_neg hc] at h
      rcases List.mem_cons.1 hq with rfl | hq
      · simpa using hc
      · exact fwdFoldNone a ps o h q hq

theorem fwdFoldSrc (a : Int) : ∀ (ps : List (Nat × SbEnt)) (o : Option Nat) (r : Nat),
    ps.foldl (fwdF a) o = some r → o = some r ∨ ∃ q, q ∈ ps ∧ q.1 = r
  | [], _, _, h => by simp at h; exact .inl h
  | q0 :: ps, o, r, h => by
    simp only [List.foldl_cons, fwdF] at h
    split at h
    · rcases fwdFoldSrc a ps _ r h with h' | ⟨q, hq, hq1⟩
      · exact .inr ⟨q0, by simp, Option.some.inj h'⟩
      · exact .inr ⟨q, List.mem_cons_of_mem _ hq, hq1⟩
    · rcases fwdFoldSrc a ps o r h with h' | ⟨q, hq, hq1⟩
      · exact .inl h'
      · exact .inr ⟨q, List.mem_cons_of_mem _ hq, hq1⟩

/-- The forwarding tag is the LARGEST covering tag (tags in issue order). -/
theorem fwdFoldMax (a : Int) : ∀ (ps : List (Nat × SbEnt)) (o : Option Nat) (r : Nat),
    (ps.map Prod.fst).Pairwise (· < ·) → ps.foldl (fwdF a) o = some r →
    ∀ q, q ∈ ps → (msgByte q.2.msg a).isSome = true → q.1 ≤ r
  | [], _, _, _, _, _, hq, _ => by simp at hq
  | q0 :: ps, o, r, hpw, h, q, hq, hc => by
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hpw
    simp only [List.foldl_cons, fwdF] at h
    rcases List.mem_cons.1 hq with rfl | hq
    · rw [if_pos hc] at h
      rcases fwdFoldSrc a ps _ r h with h' | ⟨q', hq', hq1⟩
      · exact Nat.le_of_eq (Option.some.inj h')
      · rw [← hq1]; exact Nat.le_of_lt (hpw.1 q'.1 ⟨q', hq', rfl⟩)
    · split at h
      · exact fwdFoldMax a ps _ r hpw.2 h q hq hc
      · exact fwdFoldMax a ps o r hpw.2 h q hq hc

/-- A covered byte IS forwarded. -/
theorem fwdOfCover (hP : PInv N img G X dev w) (x : Nat) (q : Nat × SbEnt) (a : Int) :
    q ∈ w.pend x → (msgByte q.2.msg a).isSome = true → SbCand.fwdByte (w.σ.sb x) a ≠ none := by
  intro hq hc
  rw [hP.inv.sb x]
  rcases fwdRel (w.pend x) a with ⟨h1, -⟩ | ⟨p, -, -, h2, h3⟩
  · rw [fwdIdFold] at h1
    have := fwdFoldNone a _ none h1 q hq
    rw [hc] at this; cases this
  · rw [h2]; intro h; rw [h] at h3; cases h3

/-- The pending entry's store writes exactly the bytes its message has, with their values. -/
theorem pendWritesV (hP : PInv N img G X dev w) (i : Nat) (p : Nat × SbEnt) (a : Int) (u : BitVec 8) :
    p ∈ w.pend i → msgByte p.2.msg a = some u → gwritesByte G (i, p.1) a u := by
  intro hp hs
  obtain ⟨rl, base, vs, kc, hl, -, hm⟩ := pendLbl hP i p hp
  rw [hm] at hs
  obtain ⟨j, hj, rfl⟩ := msgByteIndex base vs _ _ _ (by rw [hs]; rfl)
  rw [msgByteVal] at hs
  exact ⟨_, base, vs, j, hl, rfl, hs, rfl⟩

theorem pendCovers (hP : PInv N img G X dev w) (i : Nat) (p : Nat × SbEnt) (a : Int) (u : BitVec 8) :
    p ∈ w.pend i → gwritesByte G (i, p.1) a u → (msgByte p.2.msg a).isSome = true := by
  intro hp hw
  obtain ⟨rl, base, vs, kc, hl, -, hm⟩ := pendLbl hP i p hp
  obtain ⟨l, base', vs', j, hl', hwr, hv, ha⟩ := hw
  rw [hl, Option.some.injEq] at hl'
  subst hl'
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
  obtain ⟨rfl, rfl⟩ := hwr
  rw [hm, ← ha, msgByteVal, hv]; rfl

/-! ## 7.2 The heads -/

theorem lblOfValid (x : Nat) : (w.rows x).length < (G.gxProg.getD x []).length →
    ∃ l, gxLbl G (hd w x) = some l := by
  intro h
  unfold gxLbl hd
  cases hr : G.gxProg[x]? with
  | none => rw [List.getD_eq_getElem?_getD, hr] at h; simp at h
  | some row =>
    rw [List.getD_eq_getElem?_getD, hr] at h
    simp only [Option.getD_some] at h
    exact ⟨_, by simp only [Option.bind_some]; exact List.getElem?_eq_getElem h⟩

/-- A head gmo-before every later memory event of its row: a target below the head is below its
measure. -/
theorem headBound (hwf : gwf G) (x : Nat) (l : Lbl) (n : Nat) :
    gxLbl G (hd w x) = some l → lbIsMem l = true →
    (∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → gmoLt G (hd w x) m) →
    n < gpos G (hd w x) → n < mu G w (.hd x) := by
  intro hl hm hord hn
  have he := lblGmo G _ l hwf hl hm
  refine muHdGt G w x n (Nat.lt_trans hn (gposLtLen G _ he)) (fun m hmG hmx hmr => ?_)
  unfold realized at hmr
  by_cases heq : m.2 = (hd w x).2
  · have : m = hd w x := Prod.ext hmx heq
    subst this; exact hn
  · have hlt : (hd w x).2 < m.2 := by unfold hd at heq ⊢; rw [hmx] at hmr; omega
    exact Nat.lt_trans hn (hord m hmG hmx hlt).2.2

/-- **ROW H1 (rule 5)**: an `.aq` read head is gmo-before every later memory event of its row. -/
theorem aqOrd (hc : CatH G) (x : Nat) (l : Lbl) : gxLbl G (hd w x) = some l → (lbIsR l && lbAq l) = true →
    ∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → gmoLt G (hd w x) m := by
  intro hl hra m hm hmx hlt
  obtain ⟨lm, hlm, hmm⟩ := gwfGmoMem G m hc.wf hm
  simp only [Bool.and_eq_true] at hra
  exact SBAcq.acqLt G _ m l lm hc.ppo hl hlm (by unfold hd; exact hmx.symm) hlt hra.1 hra.2 hmm

/-- **ROW H2 (rule 4 + (R1))**: a draining fence head with a pending entry waits for the OLDEST entry,
gmo-before every later memory event of the row (the drain bit `pw`; `sr` for reads, `sw` for writes —
the image fact `fenceSw` — and the trusted (R1) for I/O). -/
theorem blkFence (hP : PInv N img G X dev w) (hc : CatH G) (hI : ImgFacts G)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hN : G.gxProg.length = N) (x : Nat) (pr pw sr sw : Bool)
    (hl : gxLbl G (hd w x) = some (LFence pr pw sr sw)) (hdr : SbCand.drains pw sr = true)
    (hne : w.σ.sb x ≠ []) : ∃ B, validT N G w B ∧ mu G w B < mu G w (.hd x) := by
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
  obtain ⟨rl, base, vs, kc, hl0, -, -⟩ := pendLbl hP x p0 hp0m
  have hs0m : (x, p0.1) ∈ G.gxGmo := lblGmo G _ _ hc.wf hl0 rfl
  have hs0r := pendRealized hP x p0 hp0m
  obtain ⟨hv, heq⟩ := tgtPend hP x 0 p0 hp0
  refine ⟨_, hv, ?_⟩
  rw [heq]
  refine muHdGt G w x _ (gposLtLen G _ hs0m) (fun m hm hmx hmr => ?_)
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

/-- The shape of an AMO label (`gwf`). -/
theorem rmwShape (hwf : gwf G) (e : Geid) (aq rl : Bool) (base : Int) (ts : List Nat)
    (rvs wvs : List (BitVec 8)) (kc : WmClass) :
    gxLbl G e = some (LRmw aq rl base ts rvs wvs kc) →
    wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length := by
  intro hl
  unfold gxLbl at hl
  cases hr : G.gxProg[e.1]? with
  | none => rw [hr] at hl; cases hl
  | some row =>
    rw [hr] at hl
    simp only [Option.bind_some] at hl
    exact hwf.2.2 e.1 row e.2 _ hr hl

/-- **THE BLOCKED AMO HEAD** (edges (E2w) co ⊆ gmo, (E3w) fr, (E6) rule 1 / rule 4, the source not yet
issued R43 R6): a target strictly gmo-before the AMO. -/
theorem blkAmo (hP : PInv N img G X dev w) (hc : CatH G) (hI : ImgFacts G) (hN : G.gxProg.length = N)
    (rdG : RdG) (x : Nat) (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8))
    (kc : WmClass) (hl : gxLbl G (hd w x) = some (LRmw aq rl base ts rvs wvs kc))
    (hb : ¬ enbL G X rdG w (hd w x) (LRmw aq rl base ts rvs wvs kc)) :
    ∃ B, validT N G w B ∧ mu G w B < gpos G (hd w x) := by
  obtain ⟨-, hwl, hrl⟩ := rmwShape hc.wf _ aq rl base ts rvs wvs kc hl
  have hrl0 : rl = false := hI.noRl _ _ hl
  have hnr : SbCand.noRl (w.σ.sb x) := by
    intro e he
    rw [hP.inv.sb x] at he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact hP.nrl x p hp
  have he : realized w (hd w x) → False := fun h => by unfold realized hd at h; simp at h
  have hem : hd w x ∈ G.gxGmo := lblGmo G _ _ hc.wf hl rfl
  have hwr : ∀ j (hj : j < ts.length), gwritesByte G (hd w x) (accAddr base j) (wvs[j]'(by omega)) :=
    fun j hj => ⟨_, base, wvs, j, hl, rfl, List.getElem?_eq_getElem _, rfl⟩
  by_cases hA : ∀ j t, ts[j]? = some t →
      srcLatest G w (accAddr base j) t ∧ readersDone G w (accAddr base j) (hd w x)
  · by_cases hB : SbCand.amoOk (w.σ.sb x) base ts.length
    · exact absurd ⟨hA, hB, ⟨fun h => by simp [hrl0] at h, fun _ => hnr⟩⟩ hb
    · -- (E6): an own pending entry of an earlier epoch (rule 4) or overlapping (rule 1)
      obtain ⟨e', he', hbad⟩ : ∃ e', e' ∈ w.σ.sb x ∧ ¬ (e'.fs = 0 ∧ ¬ e'.hits base ts.length) := by
        refine Classical.byContradiction (fun hn => hB (fun e' he' => ?_))
        exact Classical.byContradiction (fun h => hn ⟨e', he', h⟩)
      rw [hP.inv.sb x] at he'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he'
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hp
      obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLbl hP x p hp
      have hpr := pendRealized hP x p hp
      unfold realized at hpr
      have hpo : WeakRvwmoGraph.gpo G (x, p.1) (hd w x) :=
        SBAcq.gpoOf G _ _ _ _ hl' hl rfl hpr
      have hlt : gmoLt G (x, p.1) (hd w x) := by
        by_cases hfs : p.2.fs = 0
        · have hhit : p.2.hits base ts.length := Classical.byContradiction (fun h => hbad ⟨hfs, h⟩)
          obtain ⟨j, hj, hs⟩ := hhit
          obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hs
          exact rule1Lt G _ _ _ _ hc.ppo hpo (.inl ⟨u, pendWritesV hP x p _ u hp hu⟩) (hwr j hj)
        · obtain ⟨kf, pr, sr, hk1, hk2, hf⟩ := hP.fs0 x p hp hfs
          exact SBAcq.fenceLt G _ _ _ _ kf pr true sr true hc.ppo hl' hl rfl hk1 hk2 hf rfl
            (by simp [lbIsW])
      obtain ⟨hv, heq⟩ := tgtPend hP x k p hk
      exact ⟨_, hv, by rw [heq]; exact hlt.2.2⟩
  · obtain ⟨j, t, htj, hbad⟩ : ∃ j t, ts[j]? = some t ∧
        ¬ (srcLatest G w (accAddr base j) t ∧ readersDone G w (accAddr base j) (hd w x)) := by
      refine Classical.byContradiction (fun hn => hA (fun j t ht => ?_))
      exact Classical.byContradiction (fun h => hn ⟨j, t, ht, h⟩)
    have hjl : j < ts.length := lookup_lt_Some htj
    have hrd : greadsByte G (hd w x) (accAddr base j) t (rvs[j]'(by omega)) :=
      ⟨_, base, ts, rvs, j, hl, rfl, htj, List.getElem?_eq_getElem _, rfl⟩
    have hlt := srcLtWrite hc _ _ t _ _ hrd (hwr j hjl)
    by_cases hsl : srcLatest G w (accAddr base j) t
    · -- (E3w): an unrealized GF reader of the member-latest
      have hnd : ¬ readersDone G w (accAddr base j) (hd w x) := fun h => hbad ⟨hsl, h⟩
      obtain ⟨r, t', v', hr, hsl', hne, hnrr⟩ : ∃ r t' v', greadsByte G r (accAddr base j) t' v' ∧
          srcLatest G w (accAddr base j) t' ∧ r ≠ hd w x ∧ ¬ realized w r := by
        refine Classical.byContradiction (fun hn => hnd (fun r t' v' h1 h2 h3 => ?_))
        exact Classical.byContradiction (fun h4 => hn ⟨r, t', v', h1, h2, h3, h4⟩)
      have := srcLatestUniq G w _ t' t hc.wf.1 hsl' hsl
      subst this
      have hrs := frLtW hc r (hd w x) _ t' v' _ hr (hwr j hjl) hlt hne
      exact tgtE hc.wf hN r _ hrs.1 hnrr hrs.2.2
    · -- (E2w) / the source not yet issued: an unlanded source, gmo-before the AMO
      have hnl : ¬ landedSrc G w (accAddr base j) t :=
        fun h => hsl (hP.rd _ _ t _ hrd he h)
      obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := by
        cases t with
        | zero => exact absurd (.inl rfl) hnl
        | succ i => exact ⟨i, rfl⟩
      obtain ⟨⟨src, hs, hsw, hvis⟩, -⟩ := hc.lv _ _ _ _ hrd
      have hsW : src ∉ wrAtW w (accAddr base j) := fun h => hnl (.inr ⟨src, hs, h⟩)
      obtain ⟨hsb, hsm⟩ := gwrBOf G src _ _ hc.wf hsw
      have hlt' : gmoLt G src (hd w x) := by
        rcases hvis with h | h
        · exact h
        · exact rule1Lt G src _ _ _ hc.ppo h (.inl ⟨_, hsw⟩) (hwr j hjl)
      exact tgtW hP hc.wf hN _ src _ hsb hsm hsW hlt'.2.2

/-- **THE BLOCKED LOAD HEAD** (edge (E5) rfe ⊆ gmo, the source not yet issued, the own-forwarding
case): if the design's source gate fails, a target strictly gmo-before the load. -/
theorem blkLoad (hP : PInv N img G X dev w) (hc : CatH G) (hN : G.gxProg.length = N) (x : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs)) (hns : ¬ srcGate G w x base ts vs) :
    ∃ B, validT N G w B ∧ mu G w B < gpos G (hd w x) := by
  obtain ⟨j, t, v, htj, hvj, hbad⟩ : ∃ j t v, ts[j]? = some t ∧ vs[j]? = some v ∧
      ¬ (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
        (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧ srcLatest G w (accAddr base j) t)) := by
    refine Classical.byContradiction (fun hn => hns (fun j t v h1 h2 => ?_))
    exact Classical.byContradiction (fun h => hn ⟨j, t, v, h1, h2, h⟩)
  have hrd : greadsByte G (hd w x) (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
  have he : ¬ realized w (hd w x) := fun h => by unfold realized hd at h; simp at h
  have hem : hd w x ∈ G.gxGmo := lblGmo G _ _ hc.wf hl rfl
  cases hf : SbCand.fwdByte (w.σ.sb x) (accAddr base j) with
  | none =>
    have hsl : ¬ srcLatest G w (accAddr base j) t := fun h => hbad (.inr ⟨hf, h⟩)
    have hnl : ¬ landedSrc G w (accAddr base j) t := fun h => hsl (hP.rd _ _ t _ hrd he h)
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := by
      cases t with
      | zero => exact absurd (.inl rfl) hnl
      | succ i => exact ⟨i, rfl⟩
    obtain ⟨⟨src, hs, hsw, hvis⟩, -⟩ := hc.lv _ _ _ _ hrd
    have hsW : src ∉ wrAtW w (accAddr base j) := fun h => hnl (.inr ⟨src, hs, h⟩)
    obtain ⟨hsb, hsm⟩ := gwrBOf G src _ _ hc.wf hsw
    have hlt : gmoLt G src (hd w x) := by
      rcases hvis with h | h
      · exact h
      · -- an own earlier source not landed is pending, hence forwarded: impossible
        exfalso
        have hsx : src.1 = x := h.1
        have hsr : realized w src := by unfold realized; rw [hsx]; exact h.2.1
        rcases unlanded hP _ src hsb hsW with h' | ⟨k, q, hq, hq1⟩
        · exact h' hsr
        · have hqm := List.mem_of_getElem? hq
          have hsrc : src = (src.1, q.1) := Prod.ext rfl hq1.symm
          rw [hsrc] at hsw
          have := fwdOfCover hP src.1 q _ hqm (pendCovers hP src.1 q _ v hqm hsw)
          rw [hsx] at this
          exact this hf
    exact tgtW hP hc.wf hN _ src _ hsb hsm hsW hlt.2.2
  | some v' =>
    have hv' : v' ≠ v := fun h => hbad (.inl (by rw [hf, h]))
    rcases fwdRel (w.pend x) (accAddr base j) with ⟨-, h2⟩ | ⟨p, hp, hid, h2, h3⟩
    · rw [← hP.inv.sb x, hf] at h2; cases h2
    · rw [← hP.inv.sb x, hf] at h2
      have hpr := pendRealized hP x p hp
      unfold realized at hpr
      obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLbl hP x p hp
      have hsw : gwritesByte G (x, p.1) (accAddr base j) v' := pendWritesV hP x p _ v' hp h2.symm
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
        · exact absurd (gwixInj G _ _ hsrcG hsW (by omega)) hne
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
          rcases unlanded hP _ src hsb hsrcNW with h' | ⟨k, q, hq, hq1⟩
          · exact h' hsr
          · have hqm := List.mem_of_getElem? hq
            have hsrc : src = (src.1, q.1) := Prod.ext rfl hq1.symm
            have hcov : (msgByte q.2.msg (accAddr base j)).isSome = true := by
              rw [hsrc] at hsrcw; exact pendCovers hP src.1 q _ v hqm hsrcw
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
      obtain ⟨hv, heq⟩ := tgtPend hP x k p hk
      exact ⟨_, hv, by rw [heq]; exact Nat.lt_trans hgp hlt.2.2⟩

/-- **THE FABRIC-BLOCKED HEAD** (edge (Efab), the trusted (R3)): an earlier unrealized fabric member,
gmo-before it. -/
theorem blkFab (hc : CatH G) (hN : G.gxProg.length = N) (hwio : ∀ d, d ∈ dev → gmem G d)
    (hr3 : ∀ d e, gmem G d → gmem G e → before dev d e → gmoLt G d e) (x : Nat)
    (hb : ¬ fabOk dev w (hd w x)) : ∃ B, validT N G w B ∧ mu G w B < gpos G (hd w x) := by
  unfold fabOk at hb
  have hin : hd w x ∈ dev := Classical.byContradiction (fun h => hb (fun h' => absurd h' h))
  obtain ⟨d, hbd, hnr⟩ : ∃ d, before dev d (hd w x) ∧ ¬ realized w d := by
    refine Classical.byContradiction (fun hn => hb (fun _ d hd' => ?_))
    exact Classical.byContradiction (fun h => hn ⟨d, hd', h⟩)
  have hdm : d ∈ dev := by obtain ⟨i, -, hi, -, -⟩ := hbd; exact List.mem_of_getElem? hi
  have hlt := hr3 d _ (hwio d hdm) (hwio _ hin) hbd
  exact tgtE hc.wf hN d _ hlt.1 hnr hlt.2.2

/-- **EVERY BLOCKED HEAD WAITS FOR A GENUINE ITEM OF STRICTLY SMALLER MEASURE** — rows H1 (`aqOrd`) and
H2 (`blkFence`) proved, rows H3/H4/H5 the interface `HeadOrd`. -/
theorem blkHead (pol : SbPol) (hP : PInv N img G X dev w) (hc : CatH G) (hI : ImgFacts G)
    (hN : G.gxProg.length = N) (rdG : RdG) (hwio : ∀ d, d ∈ dev → gmem G d)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hr3 : ∀ d e, gmem G d → gmem G e → before dev d e → gmoLt G d e)
    (hH : HeadOrd pol G X rdG dev w) (x : Nat)
    (hmono : ∀ aq base ts vs, gxLbl G (hd w x) = some (LLoad aq base ts vs) →
      srcGate G w x base ts vs → rdG w x base ts vs)
    (hv : validT N G w (.hd x)) (hb : ¬ enb pol G X rdG dev w (.hd x)) :
    ∃ B, validT N G w B ∧ mu G w B < mu G w (.hd x) := by
  obtain ⟨l, hl⟩ := lblOfValid x hv.2
  have hord : lbIsMem l = true → ∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 →
      gmoLt G (hd w x) m := by
    intro hm
    by_cases hra : (lbIsR l && lbAq l) = true
    · exact aqOrd hc x l hl hra
    · exact hH x l hl hm hb (by simpa using hra)
  have hbound : ∀ n, lbIsMem l = true → n < gpos G (hd w x) → n < mu G w (.hd x) :=
    fun n hm hn => headBound hc.wf x l n hl hm (hord hm) hn
  by_cases hf : fabOk dev w (hd w x)
  · have hnl : ¬ enbL G X rdG w (hd w x) l := fun h => hb ⟨l, hl, hf, h⟩
    cases l with
    | LLoad aq base ts vs =>
      have hns : ¬ srcGate G w x base ts vs := by
        intro hs
        refine hnl (.inr ⟨fun hX => hnl (.inl hX), fun _ e he => ?_, hmono aq base ts vs hl hs⟩)
        rw [hP.inv.sb] at he
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
        exact hP.nrl _ p hp
      obtain ⟨B, hB, hlt⟩ := blkLoad hP hc hN x aq base ts vs hl hns
      exact ⟨B, hB, hbound _ rfl hlt⟩
    | LStore rl base vs kc =>
      exfalso
      have := hI.noRl _ _ hl
      exact hnl (fun h => by simp [lbRl] at this; rw [this] at h; cases h)
    | LFence pr pw sr sw =>
      have hdr : SbCand.drains pw sr = true :=
        Classical.byContradiction (fun h => hnl (fun h' => absurd h' h))
      have hne : w.σ.sb x ≠ [] := fun h => hnl (fun _ => h)
      exact blkFence hP hc hI hr1 hN x pr pw sr sw hl hdr hne
    | LRmw aq rl base ts rvs wvs kc =>
      obtain ⟨B, hB, hlt⟩ := blkAmo hP hc hI hN rdG x aq rl base ts rvs wvs kc hl hnl
      exact ⟨B, hB, hbound _ rfl hlt⟩
    | LIo kd base vs => exact absurd trivial hnl
  · obtain ⟨B, hB, hlt⟩ := blkFab hc hN hwio hr3 x hf
    have hin : hd w x ∈ dev := by
      unfold fabOk at hf
      exact Classical.byContradiction (fun h => hf (fun h' => absurd h' h))
    obtain ⟨l', hl', hm'⟩ := hwio _ hin
    rw [hl, Option.some.injEq] at hl'
    subst hl'
    exact ⟨B, hB, hbound _ hm' hlt⟩

end Blk

/-! # 8. `noStuckP` -/

/-- A non-final walk state has a genuine item. -/
theorem validOfNonFinal {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid}
    {w : WS} (hP : PInv N img G X dev w) :
    (∃ x, x < N ∧ (w.rows x).length < (G.gxProg.getD x []).length) ∨ (∃ i, w.pend i ≠ []) →
    ∃ T, validT N G w T := by
  rintro (⟨x, hx, hl⟩ | ⟨i, hi⟩)
  · exact ⟨.hd x, hx, hl⟩
  · obtain ⟨p, ps, hps⟩ : ∃ p ps, w.pend i = p :: ps := by
      cases h : w.pend i with
      | nil => exact absurd h hi
      | cons p ps => exact ⟨p, ps, rfl⟩
    exact ⟨.ld i 0, pendAg hP i p (by rw [hps]; simp), p, by rw [hps]; rfl⟩

/-- **`noStuckP` — PROGRESS** (design §3.4 restated per R45 §2.4, [OWN.106]): at every walk state of a
cat-consistent `GF` satisfying the walk invariant, if any work is left, SOME GENUINE ITEM IS ENABLED —
under the per-address + fence-epoch buffer [OWN.113], any read gate weaker than the design's source
gate, the trusted residue's (R1)/(R3), `gfDevWIo`, the image facts (rows H1/H2) and the per-head order
interface `HeadOrd` (rows H3/H4/H5 — FALSE in general under the design's gate, F-P-W3-1/2). -/
theorem noStuckP (GF : Gfexec) (N : Nat) (img : Image) (X : Geid → Prop) (rdG : RdG) (w : WS)
    (hc : CatH GF.gfGd.gdG) (hio : ioResidueGmo GF) (hwio : gfDevWIo GF) (hI : ImgFacts GF.gfGd.gdG)
    (hN : GF.gfGd.gdG.gxProg.length = N) (hP : PInv N img GF.gfGd.gdG X GF.gfDev w)
    (hmono : ∀ x aq base ts vs, gxLbl GF.gfGd.gdG (hd w x) = some (LLoad aq base ts vs) →
      srcGate GF.gfGd.gdG w x base ts vs → rdG w x base ts vs)
    (hH : HeadOrd SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev w) :
    ((∃ x, x < N ∧ (w.rows x).length < (GF.gfGd.gdG.gxProg.getD x []).length) ∨ (∃ i, w.pend i ≠ [])) →
    ∃ T, validT N GF.gfGd.gdG w T ∧ enb SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev w T := by
  intro hne
  obtain ⟨A0, hA0⟩ := validOfNonFinal hP hne
  have hwio' : ∀ d, d ∈ GF.gfDev → gmem GF.gfGd.gdG d :=
    fun d hd => WeakRvwmoLin2.wioGmem _ d (hwio d hd)
  have hr1 : ∀ s m, WeakRvwmoGraph.gpo GF.gfGd.gdG s m → gmem GF.gfGd.gdG s →
      gisIo GF.gfGd.gdG s = false → gisIo GF.gfGd.gdG m = true → gmoLt GF.gfGd.gdG s m :=
    fun s m hpo hgm hn hi => hio s m (.inl ⟨hpo, hgm, hn, hi⟩)
  have hr3 : ∀ d e, gmem GF.gfGd.gdG d → gmem GF.gfGd.gdG e → before GF.gfDev d e →
      gmoLt GF.gfGd.gdG d e :=
    fun d e hd he hb => hio d e (.inr (.inr (.inr (.inr ⟨hd, he, hb⟩))))
  refine descent (validT N GF.gfGd.gdG w) (enb SbPol.epoch GF.gfGd.gdG X rdG GF.gfDev w)
    (mu GF.gfGd.gdG w) (fun A hv hb => ?_) A0 hA0
  cases A with
  | hd x =>
    obtain ⟨B, hB, hlt⟩ := blkHead SbPol.epoch hP hc hI hN rdG hwio' hr1 hr3 hH x
      (hmono x) hv hb
    exact ⟨B, hB, .inr hlt⟩
  | ld i k =>
    obtain ⟨-, p, hp⟩ := hv
    obtain ⟨B, hB, hlt⟩ := blkLand hP hc hN i k p hp hb
    exact ⟨B, hB, .inr (by rw [muLd _ w i k p hp]; exact hlt)⟩

/-- The VALUE gate is admissible (weaker than the source gate at every invariant state). -/
theorem valGateMono {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}
    (hP : PInv N img G X dev w) (hwf : gwf G) (hlv : gloadValue G) (himg : G.gxImg = img)
    (x : Nat) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gxLbl G (hd w x) = some (LLoad aq base ts vs) → srcGate G w x base ts vs →
    valGate w x base ts vs := by
  intro hl hs j v hvj
  have hlen : vs.length = ts.length := by
    unfold gxLbl at hl
    cases hr : G.gxProg[(hd w x).1]? with
    | none => rw [hr] at hl; cases hl
    | some row =>
      rw [hr] at hl
      simp only [Option.bind_some] at hl
      exact hwf.2.2 _ row _ _ hr hl
  obtain ⟨t, ht⟩ : ∃ t, ts[j]? = some t :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hlen]; exact lookup_lt_Some hvj)⟩
  rcases hs j t v ht hvj with h | ⟨hn, hsl⟩
  · exact .inl h
  · refine .inr ⟨hn, ?_⟩
    rw [hP.inv.img]
    exact srcVal img G X w (hd w x) _ t v hP.inv hP.pf hlv himg
      ⟨_, base, ts, vs, j, hl, rfl, ht, hvj, rfl⟩ hsl

end SbOrd

end Weak
