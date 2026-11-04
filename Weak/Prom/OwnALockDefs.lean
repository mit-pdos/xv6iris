/-
Weak/Prom: **G4 target (1) on track (a): the SPINLOCK PROTOCOL — definitions, pure facts, resources, setup** (stage
S4a part 2; plan rev 7 §4 "Gate G4" (1a): the manual's Example 1, mm-explanatory.adoc:700–712:
`li t0, 1; again: amoswap.w.aq t0, t0, (a0); bnez t0, again; # critical section; amoswap.w.rl x0, x0, (a0)`, with
the mutual-exclusion client `ld; addi; sd` of a counter; §3 "Acquire", "Atomicity", "The deposit", "Opening").

The lock word `Lk` (4 bytes) and the counter `Ct` (8 bytes).  Every message of `M` is classified by its content
(fixed: `M` is a parameter of the adequacy, plan §3 "pre-allocated"):
* `isL` — a LOCK message: 4 bytes at `Lk`, class `excl` (an AMO's write), by hart 0 or 1; among them `isA`
  (value 1, an acquire attempt), `isR` (value 0, a release), and the rest (other values: JUNK, written only after a
  dead read, `deadInv` but not dead);
* `isC` — a COUNTER message: 8 bytes at `Ct`, class `plain`, by hart 0 or 1;
* `isDd` — DEAD: neither; no hart's text can fulfil it (`g.dd`, free mode, OwnAWp.lean).
THE LOCK-WORD CHAIN: `wrL M t` (message `t` writes byte `Lk`) and `nxtL M s u` (`u` is the first such message after
`s`).  "Two AMOs cannot read the same message, because `exclOk` makes them co-adjacent" (plan §3 "Atomicity"): the
acquiring AMO at `ts` that reads byte `Lk` from `s0` has `nxtL M s0 ts` (proved per step in OwnALock.lean from
`exclOk`, the hart's coherence floor and its own-message bag), so THE CLAIM TOKEN OF THE SLOT OF `s0` IS
`token (tk u)` FOR THE UNIQUE `u` WITH `nxtL M s0 u` — the AMO whose read source is `s0` (plan §3: "The lock
protocol gives the claim token to 'the AMO whose read source is s', and that AMO is unique, so R is taken once").
Resources (pre-allocated at adequacy start, plan R-a5):
* `cPts g M lw` — the counter's points-to (plan §3 "Points-to", track-(a) form): its latest write is `lw` (a
  counter message, or the image when `lw = 0`), and the `pend` of every later counter message is held here;
* `Rs g M s` — the lock's resource deposited at `s`: the counter's points-to with latest write `≤ s`;
* `iSlot` — the image's slot (the lock is born unlocked, holding `Rs 0`); `rSlot r` — release `r`'s slot: `pend r`
  (not yet fulfilled), or `shot r`, the author's token `tk r`, and `Rs r` or the claim token of `nxtL M r`;
* `obag` — a hart's OWN-MESSAGE BAG above its coherence floor `lo`: `pend` of its acquire messages and the token of
  its acquire and release messages (what makes "an own lock message between my read source and my write" absurd).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAFront
import Weak.Prom.OwnAMPDefs

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The addresses, the text, the test -/

/-- The lock word. -/
abbrev Lk : Int := (X : Int)
/-- The counter. -/
abbrev Ct : Int := (Y : Int)

/-- **(1a) the manual's Example 1** (mm-explanatory.adoc:700–712; the two "arbitrary unrelated" accesses before and
after are omitted), with the critical section `ld t2,(a1); addi t2,t2,1; sd t2,(a1)`; `a0 = x10 = Lk`,
`a1 = x11 = Ct`, `t0 = x5`, `t2 = x7`:
`0: li t0,1  1: amoswap.w.aq t0,t0,(a0)  2: bnez t0,1  3: ld t2,(a1)  4: addi t2,t2,1  5: sd t2,(a1)
 6: amoswap.w.rl x0,x0,(a0)`. -/
def p1a : List XI :=
  [.i (Weak.Prom.Ref.Lit.li 5 1), .i (Weak.Prom.Ref.Lit.amoswapW true false 5 5 10), .i (.br .ne 5 0 1),
   .i (Weak.Prom.Ref.Lit.ld 7 11), .i (Weak.Prom.Ref.Lit.addi 7 7 1), .i (Weak.Prom.Ref.Lit.sd 7 11),
   .i (Weak.Prom.Ref.Lit.amoswapW false true 0 0 10)]

/-- The base program of `p1a`. -/
abbrev b1a : List Instr := p1a.map XI.base

/-- The test: two harts run `p1a`; image all zero (the lock is born unlocked, the counter is 0). -/
def t1a : Test :=
  { harts := [b1a, b1a]
    regs0 := [[(10, X), (11, Y)], [(10, X), (11, Y)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

/-- The texts of the loop front end. -/
abbrev xs1a : List (List XI) := [p1a]

theorem xOf_1a : xOf xs1a b1a = some p1a := by decide

/-! ## 2. Message classes -/

/-- A lock message's shape. -/
def lmP (m : PMsg) : Prop := m.pa = Lk ∧ m.data.length = 4 ∧ m.cls = .excl ∧ (m.tid = some 0 ∨ m.tid = some 1)

/-- A counter message's shape. -/
def cmP (m : PMsg) : Prop := m.pa = Ct ∧ m.data.length = 8 ∧ m.cls = .plain ∧ (m.tid = some 0 ∨ m.tid = some 1)

instance : DecidablePred lmP := fun m => by unfold lmP; infer_instance
instance : DecidablePred cmP := fun m => by unfold cmP; infer_instance

/-- The class of the message at `t`, as a `Bool`. -/
def clsB (p : PMsg → Prop) [DecidablePred p] (M : List PMsg) (t : Nat) : Bool :=
  match msgAt M t with
  | some m => decide (p m)
  | none => false

def isL (M : List PMsg) (t : Nat) : Bool := clsB lmP M t
def isA (M : List PMsg) (t : Nat) : Bool := clsB (fun m => lmP m ∧ m.data = toBytes 1 4) M t
def isR (M : List PMsg) (t : Nat) : Bool := clsB (fun m => lmP m ∧ m.data = toBytes 0 4) M t
def isC (M : List PMsg) (t : Nat) : Bool := clsB cmP M t
def isDd (M : List PMsg) (t : Nat) : Bool := !isL M t && !isC M t
/-- Junk or dead: its `pend` goes to a `deadInv`. -/
def isJ (M : List PMsg) (t : Nat) : Bool := (isL M t && !isA M t && !isR M t) || isDd M t
/-- Authored by hart `h`. -/
def byH (M : List PMsg) (h t : Nat) : Bool := decide (tidAt M t = some h)

theorem clsB_iff {p : PMsg → Prop} [DecidablePred p] {M : List PMsg} {t : Nat} :
    clsB p M t = true ↔ ∃ m, msgAt M t = some m ∧ p m := by
  unfold clsB
  cases h : msgAt M t with
  | none => simp
  | some m => simp

theorem clsB_of {p : PMsg → Prop} [DecidablePred p] {M : List PMsg} {t : Nat} {m : PMsg}
    (h : msgAt M t = some m) : clsB p M t = decide (p m) := by
  unfold clsB; rw [h]

theorem isA_L {M : List PMsg} {t : Nat} (h : isA M t = true) : isL M t = true := by
  obtain ⟨m, hm, hp, _⟩ := clsB_iff.1 h
  exact clsB_iff.2 ⟨m, hm, hp⟩

theorem isR_L {M : List PMsg} {t : Nat} (h : isR M t = true) : isL M t = true := by
  obtain ⟨m, hm, hp, _⟩ := clsB_iff.1 h
  exact clsB_iff.2 ⟨m, hm, hp⟩

theorem isA_R {M : List PMsg} {t : Nat} (h : isA M t = true) : isR M t = false := by
  obtain ⟨m, hm, _, hd⟩ := clsB_iff.1 h
  rw [isR, clsB_of hm]
  simp only [decide_eq_false_iff_not]
  rintro ⟨_, hd'⟩
  rw [hd] at hd'; exact absurd hd' (by decide)

theorem isC_L {M : List PMsg} {t : Nat} (h : isC M t = true) : isL M t = false := by
  obtain ⟨m, hm, hp⟩ := clsB_iff.1 h
  rw [isL, clsB_of hm]
  simp only [decide_eq_false_iff_not]
  intro hl
  have := hl.1.symm.trans hp.1
  simp [Lk, Ct, X, Y] at this

theorem rng_ge {M : List PMsg} {t : Nat} (h : t ∈ rng M) : 1 ≤ t := (mem_rng.1 h).1

/-- `isA` and `byH` determine the message. -/
theorem isA_msg {M : List PMsg} {t h : Nat} (hA : isA M t = true) (hh : byH M h t = true) :
    msgAt M t = some ⟨Lk, toBytes 1 4, some h, .excl⟩ := by
  obtain ⟨m, hm, ⟨h1, _, h3, _⟩, hd⟩ := clsB_iff.1 hA
  have ht : tidAt M t = some h := of_decide_eq_true hh
  unfold tidAt at ht; rw [hm] at ht
  simp only [Option.bind_some] at ht
  rw [hm]; congr 1
  cases m; simp_all

theorem isR_msg {M : List PMsg} {t h : Nat} (hR : isR M t = true) (hh : byH M h t = true) :
    msgAt M t = some ⟨Lk, toBytes 0 4, some h, .excl⟩ := by
  obtain ⟨m, hm, ⟨h1, _, h3, _⟩, hd⟩ := clsB_iff.1 hR
  have ht : tidAt M t = some h := of_decide_eq_true hh
  unfold tidAt at ht; rw [hm] at ht
  simp only [Option.bind_some] at ht
  rw [hm]; congr 1
  cases m; simp_all

/-! ## 3. The lock-word chain -/

/-- Message `t` writes byte `a`. -/
def wrB (M : List PMsg) (a : Int) (t : Nat) : Prop := ∃ m, msgAt M t = some m ∧ (m.byteAt a).isSome = true

/-- `u` is the first message after `s` writing byte `Lk`. -/
def nxtL (M : List PMsg) (s u : Nat) : Prop := s < u ∧ wrB M Lk u ∧ ∀ v, s < v → v < u → ¬ wrB M Lk v

theorem nxtL_unique {M : List PMsg} {s u u' : Nat} (h : nxtL M s u) (h' : nxtL M s u') : u = u' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  rcases Nat.lt_trichotomy u u' with hl | he | hl
  · exact absurd h2 (h3' u h1 hl)
  · exact he
  · exact absurd h2' (h3 u' h1' hl)

/-- A lock message writes bytes `Lk .. Lk+3`. -/
theorem isL_byte {M : List PMsg} {t : Nat} {j : Nat} (hj : j < 4) (h : isL M t = true) :
    ∃ m, msgAt M t = some m ∧ (m.byteAt (Lk + j)).isSome = true := by
  obtain ⟨m, hm, h1, h2, _⟩ := clsB_iff.1 h
  refine ⟨m, hm, ?_⟩
  rw [← h1, byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl

/-- A counter message does not touch the lock word. -/
theorem isC_noL {M : List PMsg} {t : Nat} {m : PMsg} (hm : msgAt M t = some m) (h : isC M t = true) (j : Nat)
    (hj : j < 4) : m.byteAt (Lk + j) = none := by
  rw [isC, clsB_of hm] at h
  have hp := of_decide_eq_true h
  unfold PMsg.byteAt
  rw [hp.1, if_neg (by simp only [Lk, Ct, X, Y]; omega)]

/-- A lock message does not touch the counter. -/
theorem isL_noC {M : List PMsg} {t : Nat} {m : PMsg} (hm : msgAt M t = some m) (h : isL M t = true) (j : Nat)
    (hj : j < 8) : m.byteAt (Ct + j) = none := by
  rw [isL, clsB_of hm] at h
  have hp := of_decide_eq_true h
  unfold PMsg.byteAt
  rw [hp.1]
  split
  · apply List.getElem?_eq_none; rw [hp.2.1]; simp only [Lk, Ct, X, Y]; omega
  · rfl

/-- The byte an acquire / release message holds at `Lk + j`. -/
theorem isA_byte {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (h : isA M t = true) (hj : j < 4) :
    m.byteAt (Lk + j) = (toBytes 1 4)[j]? := by
  obtain ⟨m', hm', ⟨h1, _⟩, hd⟩ := clsB_iff.1 h
  rw [hm] at hm'; cases hm'
  rw [← h1, byteAt_off rfl, hd]

theorem isR_byte {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (h : isR M t = true) (hj : j < 4) :
    m.byteAt (Lk + j) = (toBytes 0 4)[j]? := by
  obtain ⟨m', hm', ⟨h1, _⟩, hd⟩ := clsB_iff.1 h
  rw [hm] at hm'; cases hm'
  rw [← h1, byteAt_off rfl, hd]

/-- Every message is a lock message (acquire, release or junk), a counter message, or dead. -/
theorem cls_cases (M : List PMsg) (t : Nat) :
    isA M t = true ∨ isR M t = true ∨ isC M t = true ∨ isJ M t = true := by
  unfold isJ isDd
  cases hA : isA M t <;> cases hR : isR M t <;> cases hC : isC M t <;> cases hL : isL M t <;> simp

/-- A lock-touching message (`wrB` at `Lk + j`) is a lock message or junk/dead. -/
theorem wrL_cls {M : List PMsg} {t j : Nat} (hj : j < 4) (h : wrB M (Lk + j) t) :
    isA M t = true ∨ isR M t = true ∨ isJ M t = true := by
  rcases cls_cases M t with h1 | h1 | h1 | h1
  · exact .inl h1
  · exact .inr (.inl h1)
  · obtain ⟨m, hm, hb⟩ := h
    rw [isC_noL hm h1 j hj] at hb; cases hb
  · exact .inr (.inr h1)

/-- The coherence contradiction: a write `v` to `Lk` above the read source `s0` and below the coherence floor. -/
theorem chain_coh {M : List PMsg} {ws : PState} {s0 v vpre : Nat} (hsv : s0 < v) (hv : v ≤ coh ws Lk)
    (hw : wrB M Lk v) (hr : ¬ writesIn M Lk s0 (max vpre (coh ws Lk))) : False := by
  obtain ⟨m, hm, hb⟩ := hw
  obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
  exact hr ⟨k + 1, hsv, by omega, m, by simpa [msgAt] using hm, hb⟩

/-- The atomicity contradiction: another hart's write to `Lk` strictly between the source and the AMO's write. -/
theorem chain_excl {M : List PMsg} {h s0 v ts : Nat} (hsv : s0 < v) (hvt : v < ts) (hw : wrB M Lk v)
    (htid : tidAt M v ≠ some h) (hx : ¬ writesInBy M (fun tid => tid ≠ some h) Lk s0 (ts - 1)) : False := by
  obtain ⟨m, hm, hb⟩ := hw
  obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
  refine hx ⟨k + 1, hsv, by omega, m, by simpa [msgAt] using hm, hb, ?_⟩
  intro he; apply htid; unfold tidAt; rw [hm]; exact he

/-! ## 4. The client's trace invariant -/

/-- A counter load entry. -/
def isCLd (e : PEv) (tvs : List (Nat × BitVec 8)) : Prop := ∃ a, e = (LLoad false false Ct tvs a, none)

/-- A counter store entry at `ts`. -/
def isCSt (e : PEv) (ts : Nat) : Prop := ∃ d a b, e = (LStore false false Ct d a b, some ts)

/-- No counter entry. -/
def noC (ev : Trace) : Prop := ∀ e ∈ ev, (∀ tvs, ¬ isCLd e tvs) ∧ (∀ ts, ¬ isCSt e ts)

/-- `lw` is THE LATEST COUNTER MESSAGE BELOW `ts` (the image when `lw = 0`). -/
def latestC (M : List PMsg) (lw ts : Nat) : Prop :=
  (lw = 0 ∨ isC M lw = true) ∧ lw < ts ∧ ∀ u, lw < u → u < ts → isC M u = false

/-- **THE MUTUAL-EXCLUSION INVARIANT of a hart** (G4 (1)): if its trace has a counter load and a counter store at
`ts`, every byte of the load was read from the latest counter message below `ts` (or the image) — no counter write
of anybody lies between the critical section's read and its write. -/
def qLk (M : List PMsg) (ev : Trace) : Prop :=
  ∀ tvs ts, (∃ e ∈ ev, isCLd e tvs) → (∃ e ∈ ev, isCSt e ts) → ∃ lw, (∀ p ∈ tvs, p.1 = lw) ∧ latestC M lw ts

def qsLk (M : List PMsg) : Nat → Trace → Prop := fun _ => qLk M

theorem qLk_noC {M : List PMsg} {ev : Trace} (h : noC ev) : qLk M ev := by
  intro tvs ts h1 _
  obtain ⟨e, he, hl⟩ := h1
  exact absurd hl ((h e he).1 tvs)

theorem noC_nil : noC [] := fun _ h => by cases h

theorem noC_snoc {ev : Trace} {e : PEv} (h : noC ev) (he : (∀ tvs, ¬ isCLd e tvs) ∧ (∀ ts, ¬ isCSt e ts)) :
    noC (ev ++ [e]) := by
  intro e' he'
  rcases List.mem_append.1 he' with h1 | h1
  · exact h e' h1
  · rw [List.mem_singleton] at h1; subst h1; exact he

/-- A lock AMO entry is no counter entry. -/
theorem rmw_nonC (aq rl : Bool) (tvs : List (Nat × BitVec 8)) (d : List (BitVec 8)) (a b : List Dsrc) (ts : Nat) :
    (∀ tv, ¬ isCLd (LRmw aq rl Lk tvs d a b, some ts) tv) ∧ (∀ t, ¬ isCSt (LRmw aq rl Lk tvs d a b, some ts) t) := by
  refine ⟨fun _ ⟨_, h⟩ => ?_, fun _ ⟨_, _, _, h⟩ => ?_⟩ <;> cases h

theorem qLk_snoc {M : List PMsg} {ev : Trace} {e : PEv} (h : qLk M ev)
    (he : (∀ tvs, ¬ isCLd e tvs) ∧ (∀ ts, ¬ isCSt e ts)) : qLk M (ev ++ [e]) := by
  intro tvs ts hh1 hh2
  obtain ⟨e1, h1, hl⟩ := hh1
  obtain ⟨e2, h2, hs⟩ := hh2
  have h1' : e1 ∈ ev := by
    rcases List.mem_append.1 h1 with h | h
    · exact h
    · rw [List.mem_singleton] at h; subst h; exact absurd hl (he.1 tvs)
  have h2' : e2 ∈ ev := by
    rcases List.mem_append.1 h2 with h | h
    · exact h
    · rw [List.mem_singleton] at h; subst h; exact absurd hs (he.2 ts)
  exact h tvs ts ⟨e1, h1', hl⟩ ⟨e2, h2', hs⟩

/-! ## 5. Bags -/

/-- Hart `h`'s acquire messages above `lo`, except `ex`. -/
def bagA (M : List PMsg) (h lo ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lo < t) && decide (t ≠ ex) && isA M t && byH M h t)

/-- Hart `h`'s lock messages (acquire or release) above `lo`, except `ex`. -/
def bagL (M : List PMsg) (h lo ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lo < t) && decide (t ≠ ex) && (isA M t || isR M t) && byH M h t)

/-- The counter's bag above `lw`. -/
def cBag (M : List PMsg) (lw : Nat) : List Nat := (rng M).filter (fun t => decide (lw < t) && isC M t)

theorem mem_bagA {M : List PMsg} {h lo ex t : Nat} :
    t ∈ bagA M h lo ex ↔ t ∈ rng M ∧ lo < t ∧ t ≠ ex ∧ isA M t = true ∧ byH M h t = true := by
  unfold bagA; simp [List.mem_filter, and_assoc]

theorem mem_bagL {M : List PMsg} {h lo ex t : Nat} :
    t ∈ bagL M h lo ex ↔ t ∈ rng M ∧ lo < t ∧ t ≠ ex ∧ (isA M t = true ∨ isR M t = true) ∧ byH M h t = true := by
  unfold bagL; simp [List.mem_filter, and_assoc]

theorem mem_cBag {M : List PMsg} {lw t : Nat} : t ∈ cBag M lw ↔ t ∈ rng M ∧ lw < t ∧ isC M t = true := by
  unfold cBag; simp [List.mem_filter]

theorem nodup_rng (M : List PMsg) : (rng M).Nodup := List.nodup_range' ..

/-! ## 6. Resources -/

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- THE COUNTER'S POINTS-TO (plan §3 "Points-to", track (a)): latest write `lw`, the `pend` of every later counter
message. -/
def cPts (g : AGN) (M : List PMsg) (lw : Nat) : IProp GF :=
  iprop(⌜lw = 0 ∨ isC M lw = true⌝ ∗ [∗list] t ∈ cBag M lw, pend g t)

/-- The lock's resource deposited at `s`. -/
def Rs (g : AGN) (M : List PMsg) (s : Nat) : IProp GF := iprop(∃ lw, ⌜lw ≤ s⌝ ∗ cPts g M lw)

/-- The claim token of the slot of `s`: the token of the first lock-word write after `s`. -/
def nxtTok (M : List PMsg) (tk : Nat → GName) (s : Nat) : IProp GF := iprop(∃ u, ⌜nxtL M s u⌝ ∗ token (tk u))

def lkN : Namespace := ndot nroot "promLock"

/-- THE IMAGE'S SLOT: the lock is born unlocked with `Rs 0`. -/
def iSlot (g : AGN) (M : List PMsg) (tk : Nat → GName) : IProp GF :=
  inv (ndot lkN 0) iprop(Rs g M 0 ∨ nxtTok M tk 0)

/-- RELEASE `r`'S SLOT (plan §3 "The deposit"): `pend r`, or `shot r` with the author's token and `Rs r` or the
claim token. -/
def rSlot (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) : IProp GF :=
  inv (ndot lkN r) iprop(pend g r ∨ (shot g r ∗ token (tk r) ∗ (Rs g M r ∨ nxtTok M tk r)))

/-- THE PROTOCOL'S PERSISTENT PART. -/
def lkCtx (g : AGN) (M : List PMsg) (tk : Nat → GName) : IProp GF :=
  iprop(doomInv g M ∗ iSlot g M tk ∗ ([∗list] r ∈ (rng M).filter (isR M), rSlot g M tk r) ∗
    ([∗list] d ∈ (rng M).filter (isJ M), deadInv g d))

/-- THE OWN-MESSAGE BAG of hart `h` above `lo` (except `ex`). -/
def obag (g : AGN) (M : List PMsg) (tk : Nat → GName) (h lo ex : Nat) : IProp GF :=
  iprop(([∗list] t ∈ bagA M h lo ex, pend g t) ∗ [∗list] t ∈ bagL M h lo ex, token (tk t))

instance (g : AGN) (M : List PMsg) (tk : Nat → GName) : Persistent (iSlot (GF := GF) g M tk) := by
  unfold iSlot; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) : Persistent (rSlot (GF := GF) g M tk r) := by
  unfold rSlot; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) : Persistent (lkCtx (GF := GF) g M tk) := by
  unfold lkCtx; infer_instance

instance (g : AGN) (M : List PMsg) (lw : Nat) : Timeless (cPts (GF := GF) g M lw) := by
  unfold cPts
  have : Timeless ([∗list] t ∈ cBag M lw, pend (GF := GF) g t) := BigSepL.bigSepL_timeless (fun _ => inferInstance)
  infer_instance

instance (g : AGN) (M : List PMsg) (s : Nat) : Timeless (Rs (GF := GF) g M s) := by unfold Rs; infer_instance

instance (M : List PMsg) (tk : Nat → GName) (s : Nat) : Timeless (nxtTok (GF := GF) M tk s) := by
  unfold nxtTok; infer_instance

end res

end Weak.Prom.OA
