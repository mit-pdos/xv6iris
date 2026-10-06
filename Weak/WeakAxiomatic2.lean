/-
Weak: **the global memory order, and `ob`-acyclicity** (W4 SLICE 2 of the M6
robustness effort).

Rocq: `iris/WeakAxiomatic2.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: slice 1 (`WeakAxiomatic`) built the
event-labelled machine, the relations, the ppo fragment and the SOUNDNESS
direction in LOCAL form (`axOrd`).  This file builds a GLOBAL MEMORY ORDER in
which every read is placed, and derives from it the global external axiom
`acyclic(ppo ∪ rf ∪ co ∪ fr)`.  DELIBERATELY DEPENDENCY-FREE.

THE HEADLINE DESIGN DECISION: slice 1's event-level `ax_external` conjecture is
FALSE for this model (a two-byte load gives a three-edge `rfe ; fr ; co` cycle,
`evRfeCoFrCyclic` below), an artefact of collapsing a multi-byte access into
one event.  So the global memory order is a total order on OPERATIONS
`Mop := (byte, event)`, and `ob` is stated there.

WHERE EACH OPERATION SITS (`opos`): a WRITE at its message's timestamp; a READ
at `max (timestamp read) (load pre-view)` — the naive "timestamp read" is wrong
(`load x (7) ; fence r,r ; load y (3)`).  Sound because `readable`'s window is
`(t, max vpre (coh a)]` (`frGmo`), complete for ppo because `ordVrNew` delivers
into `wVrNew` ≤ `loadVpre`.  Ties broken by (write before read), execution
position, byte address — making the key INJECTIVE and the order TOTAL.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakAxiomatic.lean` deviation 1.  Types: `mop` ↦ `Mop`,
   `cand` ↦ `Cand` (`Cand img tr` ↦ `⟨img, tr⟩`; `cd_img`/`cd_tr` ↦
   `cdImg`/`cdTr`).  `gmo_op` ↦ `gmoOp`, `ob_op` ↦ `obOp`, `rfe_ev` ↦ `rfeEv`,
   `es_msg` ↦ `esMsg`, `tr_msgs` ↦ `trMsgs`, `ce_w0_1` ↦ `ceW0_1` (digit
   segments keep their underscore), `ceE` kept, `ev_rfe_co_fr_cyclic` ↦
   `evRfeCoFrCyclic`.
2. THE KEY TYPE.  Rocq's `nat * nat * nat * Z` is LEFT-nested (`p.1.1.1` is
   the position); Lean's `Nat × Nat × Nat × Int` is RIGHT-nested, so `kless`
   reads `p.1`, `p.2.1`, `p.2.2.1`, `p.2.2.2` for Rocq's `p.1.1.1`, `p.1.1.2`,
   `p.1.2`, `p.2`.  Same order, same components.
3. SECTION VARIABLES.  The Rocq `Section counterexample` (`Context v`) becomes
   an explicit leading `(v : BitVec 8)` argument of every declaration that
   uses it — exactly the Rocq signature after the section closes.
4. `vm_compute` in the counterexample (on terms with the open byte `v`, so no
   closed-term decision applies) is `simp` over the definitions (`logByte`,
   `msgByte`, `trMsgs`, ...).
5. `replay` is Rocq-literal (`σ :: match tr with ...`).
6. Lean-only helper (no Rocq twin): none.

**Not ported:** nothing.  The closing §9 ("what slice 2 does not do", the
`promise_free_complete` conjecture and the view-domination sketch) is prose,
kept as the comment at the end; slice 3 (`WeakAxiomatic3`) discharges it.

**Statements checked** (by hand, against Rocq): all of them; in particular
`promiseFreeObAcyclic`, `promiseFreeGmo`, `soundRelOrd`, `candReachable`,
`scCandReachable`, `evRfeCoFrCyclic`.
-/
import Weak.WeakAxiomatic

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl Ev

/-! # 4. The global memory order -/

/-- An OPERATION: the access event `e` performs at byte `a`. -/
abbrev Mop : Type := Int × Ev

/-- The lexicographic key order: position, then (writes before reads), then
execution position, then byte address. -/
def kless (p q : Nat × Nat × Nat × Int) : Prop :=
  p.1 < q.1 ∨
  (p.1 = q.1 ∧
   (p.2.1 < q.2.1 ∨
    (p.2.1 = q.2.1 ∧
     (p.2.2.1 < q.2.2.1 ∨ (p.2.2.1 = q.2.2.1 ∧ p.2.2.2 < q.2.2.2)))))

theorem klessTrans (p q r : Nat × Nat × Nat × Int) : kless p q → kless q r → kless p r := by
  unfold kless; omega

theorem klessIrrefl (p : Nat × Nat × Nat × Int) : ¬ kless p p := by
  unfold kless; omega

theorem klessTotal (p q : Nat × Nat × Nat × Int) : kless p q ∨ p = q ∨ kless q p := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨a', b', c', d'⟩ := q
  simp only [kless, Prod.mk.injEq]
  omega

theorem tcKless {A : Type _} (R : A → A → Prop) (f : A → Nat × Nat × Nat × Int) :
    (∀ x y, R x y → kless (f x) (f y)) → ∀ x, ¬ tc R x x := by
  intro hf x hc
  have hall : ∀ y z, tc R y z → kless (f y) (f z) := by
    intro y z hyz
    induction hyz with
    | single h => exact hf _ _ h
    | tail _ h ih => exact klessTrans _ _ _ ih (hf _ _ h)
  exact klessIrrefl (f x) (hall x x hc)

/-- THE POSITION OF AN OPERATION. -/
def opos (E : Exec) (a : Int) (e : Ev) : Nat :=
  if writesb E a e then evTs E e else max (ets E a e) (evpre E e)

def ophase (E : Exec) (a : Int) (e : Ev) : Nat := if writesb E a e then 0 else 1

def okey (E : Exec) (o : Mop) : Nat × Nat × Nat × Int :=
  (opos E o.1 o.2, ophase E o.1 o.2, evIx o.2, o.1)

def gmoOp (E : Exec) : Mop → Mop → Prop := fun o1 o2 => kless (okey E o1) (okey E o2)

/-! ### The order's structural properties -/

theorem gmoOpTrans (E : Exec) (o1 o2 o3 : Mop) : gmoOp E o1 o2 → gmoOp E o2 o3 → gmoOp E o1 o3 :=
  klessTrans _ _ _

theorem gmoOpIrrefl (E : Exec) (o : Mop) : ¬ gmoOp E o o := klessIrrefl _

theorem evIxInj (e1 e2 : Ev) : evIx e1 = evIx e2 → e1 = e2 := by
  cases e1 <;> cases e2 <;> simp [evIx]

theorem okeyInj (E : Exec) (o1 o2 : Mop) : okey E o1 = okey E o2 → o1 = o2 := by
  obtain ⟨a1, e1⟩ := o1
  obtain ⟨a2, e2⟩ := o2
  simp only [okey, Prod.mk.injEq]
  rintro ⟨_, _, hix, rfl⟩
  exact ⟨rfl, evIxInj e1 e2 hix⟩

theorem gmoOpTotal (E : Exec) (o1 o2 : Mop) : gmoOp E o1 o2 ∨ o1 = o2 ∨ gmoOp E o2 o1 := by
  rcases klessTotal (okey E o1) (okey E o2) with h | h | h
  · exact .inl h
  · exact .inr (.inl (okeyInj E o1 o2 h))
  · exact .inr (.inr h)

/-! ### Reading `opos` and `ophase` off an event -/

theorem wrBDec (E : Exec) (a : Int) (e : Ev) : wrB E a e ∨ ¬ wrB E a e := by
  cases hb : writesb E a e
  · right; intro h; rw [(writesbSpec E a e).2 h] at hb; cases hb
  · left; exact (writesbSpec E a e).1 hb

theorem oposWr (E : Exec) (a : Int) (e : Ev) : wrB E a e → opos E a e = evTs E e := by
  intro h; unfold opos; rw [(writesbSpec E a e).2 h]; rfl

theorem ophaseWr (E : Exec) (a : Int) (e : Ev) : wrB E a e → ophase E a e = 0 := by
  intro h; unfold ophase; rw [(writesbSpec E a e).2 h]; rfl

theorem oposNwr (E : Exec) (a : Int) (e : Ev) :
    ¬ wrB E a e → opos E a e = max (ets E a e) (evpre E e) := by
  intro h; unfold opos; rw [writesbFalse E a e h]; rfl

theorem ophaseNwr (E : Exec) (a : Int) (e : Ev) : ¬ wrB E a e → ophase E a e = 1 := by
  intro h; unfold ophase; rw [writesbFalse E a e h]; rfl

/-- A read operation's position is at least the timestamp it read. -/
theorem oposRdGe (E : Exec) (a : Int) (k t : Nat) (v : BitVec 8) :
    ¬ wrB E a (ev_at k) → readsAt E k a t v → t ≤ opos E a (ev_at k) := by
  intro hn hr
  rw [oposNwr E a _ hn, etsRd E a k t v hn hr]; omega

/-- A `lbRdTs` hit IS a read of that byte. -/
theorem lbRdTsReads (E : Exec) (k : Nat) (s : Estep) (a : Int) (t : Nat) :
    execWf E → E.exTr[k]? = some s → lbRdTs s.esLb a = some t → ∃ v, readsAt E k a t v := by
  intro hwf hs
  unfold lbRdTs
  cases hrd : lbRd s.esLb with
  | none => simp
  | some x =>
    obtain ⟨base, ts, vs⟩ := x
    simp only
    split
    · rename_i hle
      intro hj
      have hlen := (execRdOk E k s base ts vs hwf hs hrd).1
      have hjl : (a - base).toNat < vs.length := by rw [hlen]; exact lookup_lt_Some hj
      refine ⟨vs[(a - base).toNat], s, base, ts, vs, (a - base).toNat, hs, hrd, hj,
        List.getElem?_eq_getElem hjl, ?_⟩
      unfold accAddr; omega
    · simp

/-- Positions are inside the log. -/
theorem etsLeLog (E : Exec) (a : Int) (k : Nat) :
    execWf E → k < E.exTr.length → ¬ wrB E a (ev_at k) → ets E a (ev_at k) ≤ (elog E k).length := by
  intro hwf hk hn
  unfold ets
  rw [writesbFalse E a _ hn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hs : E.exTr[k]? with
  | none => exact Nat.zero_le _
  | some s =>
    simp only
    cases ht : lbRdTs s.esLb a with
    | none => exact Nat.zero_le _
    | some t =>
      obtain ⟨v, hr⟩ := lbRdTsReads E k s a t hwf hs ht
      exact readsAtTsLe E k a t v hwf hr

theorem oposLeLog (E : Exec) (a : Int) (k : Nat) :
    execWf E → k < E.exTr.length → ¬ wrB E a (ev_at k) → opos E a (ev_at k) ≤ (elog E k).length := by
  intro hwf hk hn
  rw [oposNwr E a _ hn]
  have := etsLeLog E a k hwf hk hn
  have := evpreLeLog E k hwf (by omega)
  omega

theorem oposLeNext (E : Exec) (a : Int) (k : Nat) :
    execWf E → k < E.exTr.length → opos E a (ev_at k) ≤ (elog E (k + 1)).length := by
  intro hwf hk
  rcases wrBDec E a (ev_at k) with hw | hn
  · rw [oposWr E a _ hw]
    obtain ⟨⟨s, hs, hlw⟩, _⟩ := hw
    rw [evTsNext E k s hwf hs hlw]
    exact Nat.le_refl _
  · have := oposLeLog E a k hwf hk hn
    have := execLogLenLe E k (k + 1) hwf (by omega) (by omega)
    omega

/-- A write's position is strictly above everything the log held before it. -/
theorem oposWrGt (E : Exec) (a2 : Int) (k2 : Nat) :
    execWf E → wrB E a2 (ev_at k2) → (elog E k2).length < opos E a2 (ev_at k2) := by
  intro _ hw; rw [oposWr E a2 _ hw, evTsAt]; omega

/-! # 5. The characteristic properties of the order -/

theorem gmoOpLt (E : Exec) (a1 : Int) (e1 : Ev) (a2 : Int) (e2 : Ev) :
    opos E a1 e1 < opos E a2 e2 → gmoOp E (a1, e1) (a2, e2) := by
  intro h; left; exact h

theorem gmoOpWrRd (E : Exec) (a1 : Int) (e1 : Ev) (a2 : Int) (e2 : Ev) :
    opos E a1 e1 ≤ opos E a2 e2 → wrB E a1 e1 → ¬ wrB E a2 e2 → gmoOp E (a1, e1) (a2, e2) := by
  intro hle hw hn
  have h1 := ophaseWr E a1 e1 hw
  have h2 := ophaseNwr E a2 e2 hn
  unfold gmoOp kless okey
  simp only [h1, h2]
  omega

theorem gmoOpIx (E : Exec) (a1 : Int) (e1 : Ev) (a2 : Int) (e2 : Ev) :
    opos E a1 e1 ≤ opos E a2 e2 → ophase E a1 e1 = ophase E a2 e2 → evIx e1 < evIx e2 →
    gmoOp E (a1, e1) (a2, e2) := by
  intro hle hph hix
  unfold gmoOp kless okey
  simp only
  omega

/-- (i) WRITES AGREE WITH `gmo`, in both directions. -/
theorem coGmo (E : Exec) (a : Int) (w1 w2 : Ev) : coB E a w1 w2 → gmoOp E (a, w1) (a, w2) := by
  rintro ⟨hw1, hw2, hlt⟩
  apply gmoOpLt
  rw [oposWr E a w1 hw1, oposWr E a w2 hw2]; exact hlt

theorem gmoCo (E : Exec) (a : Int) (w1 w2 : Ev) :
    execWf E → wrB E a w1 → wrB E a w2 → gmoOp E (a, w1) (a, w2) → coB E a w1 w2 := by
  intro hwf hw1 hw2 hg
  refine ⟨hw1, hw2, ?_⟩
  unfold gmoOp kless okey at hg
  simp only [oposWr E a w1 hw1, oposWr E a w2 hw2, ophaseWr E a w1 hw1, ophaseWr E a w2 hw2] at hg
  rcases hg with hlt | ⟨heq, hlt | ⟨_, hix | ⟨_, ha⟩⟩⟩
  · exact hlt
  · omega
  · exfalso
    rw [evTsInj E w1 w2 hwf hw1.1 hw2.1 heq] at hix; omega
  · omega

/-- (ii) AN `rf` SOURCE PRECEDES ITS READER. -/
theorem rfGmo (E : Exec) (a : Int) (w r : Ev) : execWf E → rfB E a w r → gmoOp E (a, w) (a, r) := by
  intro hwf hrf
  obtain ⟨hw, k, t, v, rfl, hr, hts⟩ := hrf
  rcases wrBDec E a (ev_at k) with hwr | hn
  · apply gmoOpLt
    rw [oposWr E a w hw, oposWr E a _ hwr, hts, evTsAt]
    have := readsAtTsLe E k a t v hwf hr; omega
  · apply gmoOpWrRd _ _ _ _ _ _ hw hn
    rw [oposWr E a w hw, hts]; exact oposRdGe E a k t v hn hr

/-- (iii) A READ IS BEFORE EVERY `co`-LATER WRITE OF ITS BYTE. -/
theorem readGap (E : Exec) (k : Nat) (s : Estep) (a : Int) (t : Nat) (v : BitVec 8) (w : Ev) :
    execWf E → E.exTr[k]? = some s → readsAt E k a t v → wrB E a w → t < evTs E w →
    max t (evpre E (ev_at k)) < evTs E w := by
  intro hwf hs hr hw hgt
  have hk := lookup_lt_Some hs
  obtain ⟨s', hs', _, _, hnw⟩ := readsAtByteRd E k a t v hwf hr
  rw [hs] at hs'; cases hs'
  rw [evpreAt E k s hs]
  by_cases hle : evTs E w ≤ loadVpre (ews E k s.esAg) (lbAq s.esLb)
  · exfalso
    have hbnd := evpreLeLog E k hwf (by omega)
    rw [evpreAt E k s hs] at hbnd
    apply hnw
    apply (writesInLogByte (eimg E k) _ _ _ _).2
    refine ⟨evTs E w, hgt, by omega, ?_⟩
    rw [← logByteFinal E k (evTs E w) a hwf (by omega) (by omega)]
    exact hw.2
  · omega

theorem frGmo (E : Exec) (a : Int) (r w : Ev) : execWf E → frB E a r w → gmoOp E (a, r) (a, w) := by
  rintro hwf ⟨⟨w0, hrf, hco⟩, hne⟩
  obtain ⟨hw0, hw, hlt⟩ := hco
  have hrf' := hrf
  obtain ⟨_, k, t, v, rfl, hr, hts⟩ := hrf'
  rcases wrBDec E a (ev_at k) with hwr | hn
  · -- the reader is an RMW: atomicity leaves no room
    apply gmoOpLt
    rw [oposWr E a _ hwr, oposWr E a w hw]
    have hnl : ¬ evTs E w < evTs E (ev_at k) :=
      soundAtomicity E hwf k a w0 w hwr.1 hrf hw hlt
    by_cases heq : evTs E w = evTs E (ev_at k)
    · exact absurd (evTsInj E (ev_at k) w hwf hwr.1 hw.1 heq.symm) hne
    · omega
  · -- a plain read: `readable`'s window
    apply gmoOpLt
    rw [oposNwr E a _ hn, etsRd E a k t v hn hr, oposWr E a w hw]
    have hr' := hr
    obtain ⟨s, _, _, _, _, hs, _⟩ := hr'
    exact readGap E k s a t v w hwf hs hr hw (by omega)

/-- (iv) NO WRITE OF THE SAME BYTE SITS BETWEEN AN `rf` EDGE'S ENDPOINTS. -/
theorem rfGmoTight (E : Exec) (a : Int) (w r w' : Ev) :
    execWf E → rfB E a w r → wrB E a w' → ¬ (gmoOp E (a, w) (a, w') ∧ gmoOp E (a, w') (a, r)) := by
  rintro hwf hrf hw' ⟨h1, h2⟩
  by_cases hrw : r = w'
  · subst hrw; exact gmoOpIrrefl E _ h2
  · apply gmoOpIrrefl E (a, w')
    refine gmoOpTrans E _ _ _ h2 ?_
    apply frGmo E a r w' hwf
    exact ⟨⟨w, hrf, gmoCo E a w w' hwf hrf.1 hw' h1⟩, hrw⟩

/-! # 6. `ob`-acyclicity

The preserved program order, lifted to operations, has five arms: `po` INTO A
WRITE operation (free in a promise-free machine); `poLocB` on one byte; a
pred-W/succ-R FENCE from a WRITE operation (`ordPw`); a pred-R/succ-R FENCE or
an ACQUIRE from a READ operation whose timestamp is PUBLISHED (`ordPr`, with
the recorded seam: the source operation must NOT write its byte); and RVWMO
ppo RULE 7 (`relAcqPo`). -/

theorem ordPwShape (E : Exec) (e1 e2 : Ev) :
    ordPw E e1 e2 →
    ∃ k1 k2 s1 s2, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ k1 < k2 ∧
      E.exTr[k1]? = some s1 ∧ E.exTr[k2]? = some s2 ∧ s1.esAg = s2.esAg := by
  rintro ⟨k1, k2, pr, sw, rfl, rfl, kf, sf, s1, s2, hlt1, hlt2, hs1, _, hs2, hag1, hag2, _⟩
  exact ⟨k1, k2, s1, s2, rfl, rfl, by omega, hs1, hs2, hag1.trans hag2⟩

theorem ordPrShape (E : Exec) (e1 e2 : Ev) :
    ordPr E e1 e2 →
    ∃ k1 k2 s1 s2, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ k1 < k2 ∧
      E.exTr[k1]? = some s1 ∧ E.exTr[k2]? = some s2 ∧ s1.esAg = s2.esAg := by
  rintro (⟨k1, k2, pw, sw, rfl, rfl, kf, sf, s1, s2, hlt1, hlt2, hs1, _, hs2, hag1, hag2, _⟩ |
          ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag, _, _⟩)
  · exact ⟨k1, k2, s1, s2, rfl, rfl, by omega, hs1, hs2, hag1.trans hag2⟩
  · exact ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩

/-! ### The four ppo arms embed -/

theorem ppoWGmo (E : Exec) (a1 : Int) (e1 : Ev) (a2 : Int) (e2 : Ev) :
    execWf E → po E e1 e2 → wrB E a2 e2 → gmoOp E (a1, e1) (a2, e2) := by
  rintro hwf ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, _⟩ hw2
  have hk1 := lookup_lt_Some hs1
  have hk2 := lookup_lt_Some hs2
  apply gmoOpLt
  have := oposLeNext E a1 k1 hwf (by omega)
  have := execLogLenLe E (k1 + 1) k2 hwf (by omega) (by omega)
  have := oposWrGt E a2 k2 hwf hw2
  omega

theorem ppoLocGmo (E : Exec) (a : Int) (e1 e2 : Ev) :
    execWf E → poLocB E a e1 e2 → gmoOp E (a, e1) (a, e2) := by
  rintro hwf ⟨hpo, hacc1, hacc2⟩
  rcases wrBDec E a e2 with hw2 | hn2
  · exact ppoWGmo E a e1 a e2 hwf hpo hw2
  obtain ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩ := hpo
  have hts := touchesMono E k1 k2 s1 s2 a (ets E a (ev_at k1)) (ets E a (ev_at k2)) hwf hlt hs1
    hs2 hag (accTouches E a k1 hacc1) (accTouches E a k2 hacc2)
  rcases wrBDec E a (ev_at k1) with hw1 | hn1
  · apply gmoOpWrRd _ _ _ _ _ _ hw1 hn2
    rw [oposWr E a _ hw1, ← etsWr E a _ hw1, oposNwr E a _ hn2]; omega
  · apply gmoOpIx
    · rw [oposNwr E a _ hn1, oposNwr E a _ hn2]
      rcases hacc1 with hw | ⟨k, t1, v1, hk, hr1⟩
      · exact absurd hw hn1
      · cases hk
        have := evpreMono E k1 k2 s1 s2 a t1 v1 hwf hlt hs1 hs2 hag hr1
        omega
    · rw [ophaseNwr E a _ hn1, ophaseNwr E a _ hn2]
    · simp only [evIx]; omega

theorem ppoOrdPwGmo (E : Exec) (a1 : Int) (e1 : Ev) (a2 : Int) (e2 : Ev) :
    execWf E → ordPw E e1 e2 → wrB E a1 e1 → gmoOp E (a1, e1) (a2, e2) := by
  intro hwf hord hw1
  obtain ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩ := ordPwShape E e1 e2 hord
  have hk2 := lookup_lt_Some hs2
  have hpub : pubW E (ev_at k1) (evTs E (ev_at k1)) := ⟨hw1.1, ⟨k1, rfl⟩, rfl⟩
  have hvr := ordVrNew E (ev_at k1) (evTs E (ev_at k1)) k2 s2 hwf hs2 (.inl ⟨hord, hpub⟩)
  have hrn := (execWsBounded E k2 s2.esAg hwf (by omega)).2.2.1
  rcases wrBDec E a2 (ev_at k2) with hw2 | hn2
  · apply gmoOpLt
    rw [oposWr E a1 _ hw1, oposWr E a2 _ hw2, evTsAt E k2]; omega
  · apply gmoOpWrRd _ _ _ _ _ _ hw1 hn2
    rw [oposWr E a1 _ hw1, oposNwr E a2 _ hn2]
    have := vrNewLeEvpre E k2 s2 hs2; omega

theorem ppoOrdPrGmo (E : Exec) (a1 : Int) (e1 : Ev) (a2 : Int) (e2 : Ev) :
    execWf E → ordPr E e1 e2 → ¬ wrB E a1 e1 → pubR E e1 (ets E a1 e1) →
    gmoOp E (a1, e1) (a2, e2) := by
  intro hwf hord hn1 hpub
  obtain ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩ := ordPrShape E e1 e2 hord
  have hk2 := lookup_lt_Some hs2
  have hvr := ordVrNew E (ev_at k1) (ets E a1 (ev_at k1)) k2 s2 hwf hs2 (.inr ⟨hord, hpub⟩)
  have hep : evpre E (ev_at k1) ≤ (ews E k2 s2.esAg).wVrNew := by
    obtain ⟨k, s, a, v, hk, hs, hr, _⟩ := hpub
    cases hk
    rw [hs1] at hs; cases hs
    refine Nat.le_trans (evpreLeVrNewPost E k1 s1 a _ v hwf hs1 hr) ?_
    rw [← hag]
    exact wsLeVrNew _ _ (execWsLe E (k1 + 1) k2 s1.esAg hwf (by omega) (by omega))
  have hrn := (execWsBounded E k2 s2.esAg hwf (by omega)).2.2.1
  rcases wrBDec E a2 (ev_at k2) with hw2 | hn2
  · apply gmoOpLt
    rw [oposNwr E a1 _ hn1, oposWr E a2 _ hw2, evTsAt E k2]; omega
  · apply gmoOpIx
    · rw [oposNwr E a1 _ hn1, oposNwr E a2 _ hn2]
      have := vrNewLeEvpre E k2 s2 hs2; omega
    · rw [ophaseNwr E a1 _ hn1, ophaseNwr E a2 _ hn2]
    · simp only [evIx]; omega

/-! ### RVWMO ppo RULE 7: a release write before a po-later acquire read

The machine enforces this pair UNCONDITIONALLY (`storePost` raises `wVRel` on
a `.rl` store, `loadVpre` joins it on an `.aq` load); under RISC-V's all-RCsc
reading of the annotations this COINCIDES with RVWMO ppo rule 7.  Rule 6 is
deliberately absent.  `relAcqPo` is the ppo edge itself; `relOrd` the ORD
fragment it generates (rule 7 alone, or rule 7 then rule 5 — the acquire read
ABSORBS `wVRel` into `wVrNew` only if it reads a byte). -/

def lbRl (l : Lbl) : Bool :=
  match l with
  | LStore rl _ _ _ => rl
  | LRmw _ rl _ _ _ _ _ => rl
  | _ => false

def relAcqPo (E : Exec) (e1 e2 : Ev) : Prop :=
  ∃ k1 k2 s1 s2, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ k1 < k2 ∧
    E.exTr[k1]? = some s1 ∧ E.exTr[k2]? = some s2 ∧ s1.esAg = s2.esAg ∧
    lbIsW s1.esLb = true ∧ lbRl s1.esLb = true ∧
    lbIsR s2.esLb = true ∧ lbAq s2.esLb = true

def relOrd (E : Exec) (e1 e2 : Ev) : Prop :=
  relAcqPo E e1 e2 ∨ ∃ em, relAcqPo E e1 em ∧ (∃ a, rdB E a em) ∧ acqPo E em e2

theorem relAcqPoShape (E : Exec) (e1 e2 : Ev) :
    relAcqPo E e1 e2 →
    ∃ k1 k2 s1 s2, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ k1 < k2 ∧
      E.exTr[k1]? = some s1 ∧ E.exTr[k2]? = some s2 ∧ s1.esAg = s2.esAg := by
  rintro ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag, _⟩
  exact ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, hag⟩

/-- The `wVRel` fold, `storeFoldVwOld`'s missing twin. -/
theorem storeBytesVRelRl (ws : Wstate) (as_ : List Int) (t : Nat) :
    as_ ≠ [] → t ≤ (storePostBytes ws true as_ t).wVRel := by
  cases as_ with
  | nil => intro h; exact absurd rfl h
  | cons a l =>
    intro _
    show t ≤ (storePostBytes (storePost ws true a t) true l t).wVRel
    exact Nat.le_trans (storePostVRelRl ws a t) (wsLeVRel _ _ (storePostBytesLe _ _ _ _))

theorem storeRunVRelRl (ws : Wstate) (base : Int) (n t : Nat) :
    0 < n → t ≤ (storePostRun ws true base n t).wVRel := by
  intro hn
  show t ≤ (storePostBytes ws true _ t).wVRel
  apply storeBytesVRelRl
  cases n with
  | zero => omega
  | succ n => simp [List.range'_succ]

/-- A RELEASE write's own timestamp is under its agent's `wVRel` straight
after. -/
theorem pubWVRel (E : Exec) (k : Nat) (s : Estep) :
    execWf E → E.exTr[k]? = some s → lbIsW s.esLb = true → lbRl s.esLb = true →
    evTs E (ev_at k) ≤ (ews E (k + 1) s.esAg).wVRel := by
  intro hwf hs hw hrl
  have hstep := execStepAt E k s hwf hs
  obtain ⟨base, vs, hwr, hne, _⟩ := mstepLogW _ _ _ _ hstep hw
  cases hl : s.esLb with
  | LLoad => rw [hl] at hw; simp [lbIsW] at hw
  | LStore rl b0 v0 kc =>
    rw [hl] at hrl; simp only [lbRl] at hrl; subst hrl
    rw [execWsStore E k s true b0 v0 kc hwf hs hl]
    apply storeRunVRelRl
    rw [hl] at hwr; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨-, hv⟩ := hwr
    have hne0 : v0 ≠ [] := by rw [hv]; exact hne
    cases v0 with
    | nil => exact absurd rfl hne0
    | cons _ _ => simp
  | LFence => rw [hl] at hw; simp [lbIsW] at hw
  | LRmw aq0 rl b0 t0 rv0 wv0 kc =>
    rw [hl] at hrl; simp only [lbRl] at hrl; subst hrl
    rw [execWsRmw E k s aq0 true b0 t0 rv0 wv0 kc hwf hs hl]
    apply storeRunVRelRl
    rw [hl] at hwr; simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨-, hv⟩ := hwr
    have hne0 : wv0 ≠ [] := by rw [hv]; exact hne
    cases wv0 with
    | nil => exact absurd rfl hne0
    | cons _ _ => simp

/-- ... and it is still there when the acquire read runs. -/
theorem relAcqVRel (E : Exec) (e1 : Ev) (t k2 : Nat) (s2 : Estep) :
    execWf E → E.exTr[k2]? = some s2 → relAcqPo E e1 (ev_at k2) → pubW E e1 t →
    t ≤ (ews E k2 s2.esAg).wVRel := by
  intro hwf hs2 hrel hpub
  obtain ⟨k1, k2', s1, s2'', rfl, hk, hlt, hs1, hs2'', hag, hw1, hrl1, _, _⟩ := hrel
  cases hk
  rw [hs2] at hs2''; cases hs2''
  have hk2 := lookup_lt_Some hs2
  obtain ⟨_, _, rfl⟩ := hpub
  rw [← hag]
  exact Nat.le_trans (pubWVRel E k1 s1 hwf hs1 hw1 hrl1)
    (wsLeVRel _ _ (execWsLe E (k1 + 1) k2 s1.esAg hwf (by omega) (by omega)))

/-- THE RULE-7 DELIVERY LEMMA: the release publication is under the target's
PRE-VIEW. -/
theorem relOrdEvpre (E : Exec) (e1 : Ev) (t k2 : Nat) (s2 : Estep) :
    execWf E → E.exTr[k2]? = some s2 → relOrd E e1 (ev_at k2) → pubW E e1 t →
    t ≤ evpre E (ev_at k2) := by
  intro hwf hs2 hcase hpub
  rcases hcase with hrel | ⟨em, hrel, ⟨a, hrd⟩, hacq⟩
  · -- rule 7 alone: the acquire read IS the target
    have hrel' := hrel
    obtain ⟨k1, k2', s1, s2'', rfl, hk, _, _, hs2'', _, _, _, _, haq⟩ := hrel'
    cases hk
    rw [hs2] at hs2''; cases hs2''
    rw [evpreAt E k2 s2 hs2]
    simp only [loadVpre, haq, ↓reduceIte]
    have := relAcqVRel E _ t k2 s2 hwf hs2 hrel hpub
    omega
  · -- rule 7 then rule 5: the acquire read absorbed `wVRel` into `wVrNew`
    obtain ⟨km, k2', sm, s2'', rfl, hk, hlt, hsm, hs2'', hagm, _, haqm⟩ := hacq
    cases hk
    rw [hs2] at hs2''; cases hs2''
    have hk2 := lookup_lt_Some hs2
    obtain ⟨kr, tr, vr, hkr, hr⟩ := hrd
    cases hkr
    have hkm : t ≤ evpre E (ev_at km) := by
      rw [evpreAt E km sm hsm]
      simp only [loadVpre, haqm, ↓reduceIte]
      have := relAcqVRel E _ t km sm hwf hsm hrel hpub
      omega
    refine Nat.le_trans hkm (Nat.le_trans (evpreLeVrNewPost E km sm a tr vr hwf hsm hr) ?_)
    refine Nat.le_trans ?_ (vrNewLeEvpre E k2 s2 hs2)
    rw [← hagm]
    exact wsLeVrNew _ _ (execWsLe E (km + 1) k2 sm.esAg hwf (by omega) (by omega))

theorem ppoRelGmo (E : Exec) (a1 : Int) (e1 : Ev) (a2 : Int) (e2 : Ev) :
    execWf E → relAcqPo E e1 e2 → wrB E a1 e1 → gmoOp E (a1, e1) (a2, e2) := by
  intro hwf hrel hw1
  have hrel' := hrel
  obtain ⟨k1, k2, s1, s2, rfl, rfl, hlt, hs1, hs2, _⟩ := hrel'
  have hk2 := lookup_lt_Some hs2
  have hpub : pubW E (ev_at k1) (evTs E (ev_at k1)) := ⟨hw1.1, ⟨k1, rfl⟩, rfl⟩
  have hev := relOrdEvpre E (ev_at k1) (evTs E (ev_at k1)) k2 s2 hwf hs2 (.inl hrel) hpub
  rcases wrBDec E a2 (ev_at k2) with hw2 | hn2
  · apply gmoOpLt
    rw [oposWr E a1 _ hw1, oposWr E a2 _ hw2, evTsAt E k2]
    have := evpreLeLog E k2 hwf (by omega); omega
  · apply gmoOpWrRd _ _ _ _ _ _ hw1 hn2
    rw [oposWr E a1 _ hw1, oposNwr E a2 _ hn2]; omega

/-- THE AXIOM the rule-7 arm contributes, in `axOrd`'s shape. -/
def axRelOrd (E : Exec) : Prop :=
  ∀ e1 k2 s2 a w t,
    E.exTr[k2]? = some s2 →
    relOrd E e1 (ev_at k2) → pubW E e1 t →
    frB E a (ev_at k2) w →
    t < evTs E w

theorem soundRelOrd (E : Exec) : execWf E → axRelOrd E := by
  intro hwf e1 k2 s2 a w t hs2 hrel hpub hfr
  have hev := relOrdEvpre E e1 t k2 s2 hwf hs2 hrel hpub
  obtain ⟨⟨w0, hrf0, hco⟩, _⟩ := hfr
  obtain ⟨_, hw, hlt⟩ := hco
  obtain ⟨_, k, t0, v0, hkeq, hr, hts0⟩ := hrf0
  cases hkeq
  have := readGap E k2 s2 a t0 v0 w hwf hs2 hr hw (by omega)
  omega

/-! ### `ob` and the theorem -/

def ppoOp (E : Exec) : Mop → Mop → Prop := fun o1 o2 =>
  (po E o1.2 o2.2 ∧ wrB E o2.1 o2.2)
  ∨ (o1.1 = o2.1 ∧ poLocB E o1.1 o1.2 o2.2)
  ∨ (ordPw E o1.2 o2.2 ∧ wrB E o1.1 o1.2)
  ∨ (ordPr E o1.2 o2.2 ∧ ¬ wrB E o1.1 o1.2 ∧ pubR E o1.2 (ets E o1.1 o1.2))
  ∨ (relAcqPo E o1.2 o2.2 ∧ wrB E o1.1 o1.2)

def rfOp (E : Exec) : Mop → Mop → Prop := fun o1 o2 => o1.1 = o2.1 ∧ rfB E o1.1 o1.2 o2.2
def coOp (E : Exec) : Mop → Mop → Prop := fun o1 o2 => o1.1 = o2.1 ∧ coB E o1.1 o1.2 o2.2
def frOp (E : Exec) : Mop → Mop → Prop := fun o1 o2 => o1.1 = o2.1 ∧ frB E o1.1 o1.2 o2.2

/-- NOTE: the union takes FULL `rf`, not just `rfe` (strictly stronger). -/
def obOp (E : Exec) : Mop → Mop → Prop := fun o1 o2 =>
  ppoOp E o1 o2 ∨ rfOp E o1 o2 ∨ coOp E o1 o2 ∨ frOp E o1 o2

theorem ppoOpGmo (E : Exec) (o1 o2 : Mop) : execWf E → ppoOp E o1 o2 → gmoOp E o1 o2 := by
  intro hwf hppo
  obtain ⟨a1, e1⟩ := o1
  obtain ⟨a2, e2⟩ := o2
  rcases hppo with ⟨hpo, hw2⟩ | ⟨heq, hpl⟩ | ⟨hord, hw1⟩ | ⟨hord, hn1, hpub⟩ | ⟨hrel, hw1⟩
  · exact ppoWGmo E a1 e1 a2 e2 hwf hpo hw2
  · simp only at heq; subst heq; exact ppoLocGmo E a1 e1 e2 hwf hpl
  · exact ppoOrdPwGmo E a1 e1 a2 e2 hwf hord hw1
  · exact ppoOrdPrGmo E a1 e1 a2 e2 hwf hord hn1 hpub
  · exact ppoRelGmo E a1 e1 a2 e2 hwf hrel hw1

theorem obOpGmo (E : Exec) (o1 o2 : Mop) : execWf E → obOp E o1 o2 → gmoOp E o1 o2 := by
  intro hwf hob
  obtain ⟨a1, e1⟩ := o1
  obtain ⟨a2, e2⟩ := o2
  rcases hob with hppo | ⟨heq, hrf⟩ | ⟨heq, hco⟩ | ⟨heq, hfr⟩
  · exact ppoOpGmo E _ _ hwf hppo
  · simp only at heq; subst heq; exact rfGmo E a1 e1 e2 hwf hrf
  · simp only at heq; subst heq; exact coGmo E a1 e1 e2 hco
  · simp only at heq; subst heq; exact frGmo E a1 e1 e2 hwf hfr

/-- THE SLICE-2 THEOREM: the global external axiom, over operations. -/
theorem promiseFreeObAcyclic (E : Exec) : execWf E → ∀ o, ¬ tc (obOp E) o o := by
  intro hwf
  apply tcKless _ (okey E)
  intro x y hxy
  exact obOpGmo E x y hwf hxy

/-- ... and the same statement in "there is a global memory order" form. -/
theorem promiseFreeGmo (E : Exec) :
    execWf E →
    (∀ o1 o2 o3, gmoOp E o1 o2 → gmoOp E o2 o3 → gmoOp E o1 o3) ∧
    (∀ o, ¬ gmoOp E o o) ∧
    (∀ o1 o2, gmoOp E o1 o2 ∨ o1 = o2 ∨ gmoOp E o2 o1) ∧
    (∀ o1 o2, obOp E o1 o2 → gmoOp E o1 o2) ∧
    (∀ a w1 w2, wrB E a w1 → wrB E a w2 → (gmoOp E (a, w1) (a, w2) ↔ coB E a w1 w2)) ∧
    (∀ a w r w', rfB E a w r → wrB E a w' →
      ¬ (gmoOp E (a, w) (a, w') ∧ gmoOp E (a, w') (a, r))) := by
  intro hwf
  refine ⟨fun o1 o2 o3 => gmoOpTrans E o1 o2 o3, gmoOpIrrefl E, gmoOpTotal E,
    fun o1 o2 => obOpGmo E o1 o2 hwf, ?_, fun a w r w' => rfGmoTight E a w r w' hwf⟩
  intro a w1 w2 hw1 hw2
  exact ⟨gmoCo E a w1 w2 hwf hw1 hw2, coGmo E a w1 w2⟩

/-! # 7. Completeness: replaying a candidate on the machine -/

/-! ## 7.1 The machine step, as a function plus a side condition -/

def mnext (σ : Mstate) (i : Nat) (l : Lbl) : Mstate :=
  match l with
  | LLoad aq base ts _ =>
    ⟨σ.msImg, σ.msLog, updWs σ.msWs i (loadPostRun (σ.msWs i) aq base ts)⟩
  | LStore rl base vs k =>
    ⟨σ.msImg, σ.msLog ++ [⟨base, vs, some i, k⟩],
     updWs σ.msWs i (storePostRun (σ.msWs i) rl base vs.length (σ.msLog.length + 1))⟩
  | LFence pr pw sr sw =>
    ⟨σ.msImg, σ.msLog, updWs σ.msWs i (fencePost (σ.msWs i) pr pw sr sw)⟩
  | LRmw aq rl base ts _ wvs k =>
    ⟨σ.msImg, σ.msLog ++ [⟨base, wvs, some i, k⟩],
     updWs σ.msWs i
       (storePostRun (loadPostRun (σ.msWs i) aq base ts) rl base wvs.length
         (σ.msLog.length + 1))⟩

def mstepOk (σ : Mstate) (i : Nat) (l : Lbl) : Prop :=
  match l with
  | LLoad aq base ts vs => rdOk σ.msImg σ.msLog (σ.msWs i) aq base ts vs
  | LStore _ _ vs _ => vs ≠ []
  | LFence .. => True
  | LRmw aq _ base ts rvs wvs _ =>
    wvs ≠ [] ∧ wvs.length = ts.length ∧
    rdOk σ.msImg σ.msLog (σ.msWs i) aq base ts rvs ∧
    rmwLatest σ.msImg σ.msLog base ts

theorem mstepOkStep (σ : Mstate) (i : Nat) (l : Lbl) : mstepOk σ i l → mstep σ i l (mnext σ i l) := by
  cases l with
  | LLoad aq base ts vs => intro h; exact mstep.MStepLoad aq base ts vs h
  | LStore rl base vs k => intro h; exact mstep.MStepStore rl base vs k h
  | LFence pr pw sr sw => intro _; exact mstep.MStepFence pr pw sr sw
  | LRmw aq rl base ts rvs wvs k =>
    rintro ⟨hne, hlen, hrd, hlat⟩; exact mstep.MStepRmw aq rl base ts rvs wvs k hne hlen hrd hlat

theorem mstepDet (σ : Mstate) (i : Nat) (l : Lbl) (σ' : Mstate) :
    mstep σ i l σ' → σ' = mnext σ i l ∧ mstepOk σ i l := by
  intro h
  cases h with
  | MStepLoad _ _ _ _ h => exact ⟨rfl, h⟩
  | MStepStore _ _ _ _ h => exact ⟨rfl, h⟩
  | MStepFence => exact ⟨rfl, trivial⟩
  | MStepRmw _ _ _ _ _ _ _ h1 h2 h3 h4 => exact ⟨rfl, h1, h2, h3, h4⟩

/-! ## 7.2 The replay -/

def replay (σ : Mstate) (tr : List Estep) : List Mstate :=
  σ :: match tr with
       | [] => []
       | s :: tr' => replay (mnext σ s.esAg s.esLb) tr'

theorem replayLength (σ : Mstate) (tr : List Estep) : (replay σ tr).length = tr.length + 1 := by
  induction tr generalizing σ with
  | nil => rfl
  | cons s tr ih => simp only [replay, List.length_cons, ih]

theorem replay0 (σ : Mstate) (tr : List Estep) : (replay σ tr)[0]? = some σ := by
  cases tr <;> rfl

theorem replayStep (σ : Mstate) (tr : List Estep) (k : Nat) (s : Estep) (σk : Mstate) :
    tr[k]? = some s → (replay σ tr)[k]? = some σk →
    (replay σ tr)[k + 1]? = some (mnext σk s.esAg s.esLb) := by
  induction tr generalizing σ k with
  | nil => intro hs; simp at hs
  | cons s0 tr ih =>
    intro hs hσ
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      simp only [replay, List.getElem?_cons_zero, Option.some.injEq] at hσ
      subst hσ
      simp only [replay, List.getElem?_cons_succ]
      exact replay0 _ _
    | succ k =>
      simp only [List.getElem?_cons_succ] at hs
      simp only [replay, List.getElem?_cons_succ] at hσ ⊢
      exact ih _ k hs hσ

/-- The messages a trace appends, and the log at each prefix. -/
def esMsg (s : Estep) : List Wmsg :=
  match lbWr s.esLb with
  | some (base, vs) => [⟨base, vs, some s.esAg, lbCls s.esLb⟩]
  | none => []

def trMsgs (tr : List Estep) : List Wmsg :=
  match tr with
  | [] => []
  | s :: tr' => esMsg s ++ trMsgs tr'

theorem mnextLog (σ : Mstate) (i : Nat) (l : Lbl) :
    (mnext σ i l).msLog = σ.msLog ++ esMsg ⟨i, l⟩ := by
  cases l <;> simp [mnext, esMsg, lbWr, lbCls]

theorem mnextImg (σ : Mstate) (i : Nat) (l : Lbl) : (mnext σ i l).msImg = σ.msImg := by
  cases l <;> rfl

theorem replayLog (σ : Mstate) (tr : List Estep) (k : Nat) (σk : Mstate) :
    (replay σ tr)[k]? = some σk → σk.msLog = σ.msLog ++ trMsgs (tr.take k) := by
  induction tr generalizing σ k with
  | nil =>
    intro hσ
    cases k with
    | zero =>
      simp only [replay, List.getElem?_cons_zero, Option.some.injEq] at hσ
      subst hσ; simp [trMsgs]
    | succ k => simp [replay] at hσ
  | cons s0 tr ih =>
    intro hσ
    cases k with
    | zero =>
      simp only [replay, List.getElem?_cons_zero, Option.some.injEq] at hσ
      subst hσ; simp [trMsgs]
    | succ k =>
      simp only [replay, List.getElem?_cons_succ] at hσ
      rw [ih _ _ hσ, mnextLog, List.take_succ_cons, trMsgs, List.append_assoc]

theorem replayImg (σ : Mstate) (tr : List Estep) (k : Nat) (σk : Mstate) :
    (replay σ tr)[k]? = some σk → σk.msImg = σ.msImg := by
  induction tr generalizing σ k with
  | nil =>
    intro hσ
    cases k with
    | zero =>
      simp only [replay, List.getElem?_cons_zero, Option.some.injEq] at hσ
      subst hσ; rfl
    | succ k => simp [replay] at hσ
  | cons s0 tr ih =>
    intro hσ
    cases k with
    | zero =>
      simp only [replay, List.getElem?_cons_zero, Option.some.injEq] at hσ
      subst hσ; rfl
    | succ k =>
      simp only [replay, List.getElem?_cons_succ] at hσ
      rw [ih _ _ hσ, mnextImg]

/-! ## 7.3 A candidate, and the general reachability theorem -/

structure Cand where
  cdImg : Image
  cdTr : List Estep

def candInit (c : Cand) : Mstate := ⟨c.cdImg, [], fun _ => wsInit⟩
def candExec (c : Cand) : Exec := ⟨replay (candInit c) c.cdTr, c.cdTr⟩
def cdLog (c : Cand) (k : Nat) : List Wmsg := trMsgs (c.cdTr.take k)

theorem candSt (c : Cand) (k : Nat) :
    k ≤ c.cdTr.length → (candExec c).exSt[k]? = some (stt (candExec c) k) := by
  intro hk
  have hlt : k < (replay (candInit c) c.cdTr).length := by rw [replayLength]; omega
  have h : (candExec c).exSt[k]? = some (replay (candInit c) c.cdTr)[k] :=
    List.getElem?_eq_getElem hlt
  rw [sttLookup _ _ _ h, h]

theorem candElog (c : Cand) (k : Nat) : k ≤ c.cdTr.length → elog (candExec c) k = cdLog c k := by
  intro hk
  unfold elog cdLog
  rw [replayLog _ _ _ _ (candSt c k hk)]
  rfl

theorem candEimg (c : Cand) (k : Nat) : k ≤ c.cdTr.length → eimg (candExec c) k = c.cdImg := by
  intro hk
  unfold eimg
  rw [replayImg _ _ _ _ (candSt c k hk)]
  rfl

theorem candNext (c : Cand) (k : Nat) (s : Estep) :
    c.cdTr[k]? = some s →
    stt (candExec c) (k + 1) = mnext (stt (candExec c) k) s.esAg s.esLb := by
  intro hs
  have hk := lookup_lt_Some hs
  have hnext := replayStep (candInit c) c.cdTr k s _ hs (candSt c k (by omega))
  exact sttLookup _ _ _ hnext

/-- THE REPLAY THEOREM.  Every candidate all of whose steps are admissible at
their own replay state is a machine execution, with EXACTLY the given trace
and image. -/
theorem candReachable (c : Cand) :
    (∀ k s, c.cdTr[k]? = some s → mstepOk (stt (candExec c) k) s.esAg s.esLb) →
    execWf (candExec c) ∧ (candExec c).exTr = c.cdTr ∧ exImg (candExec c) = c.cdImg := by
  intro hok
  have hwf : execWf (candExec c) := by
    refine ⟨replayLength (candInit c) c.cdTr, ?_, ?_⟩
    · intro σ0 hσ0
      have hσ : (replay (candInit c) c.cdTr)[0]? = some σ0 := hσ0
      rw [replay0] at hσ
      simp only [Option.some.injEq] at hσ
      subst hσ
      exact ⟨rfl, fun _ => rfl⟩
    · intro k s σ σ' hs hσ hσ'
      rw [← sttLookup _ _ _ hσ, ← sttLookup _ _ _ hσ']
      rw [candNext c k s hs]
      exact mstepOkStep _ _ _ (hok k s hs)
  exact ⟨hwf, rfl, candEimg c 0 (Nat.zero_le _)⟩

/-! ## 7.4 Boundedness along a replay -/

def cfgBounded (σ : Mstate) : Prop := ∀ i, wsBounded (σ.msWs i) σ.msLog.length

theorem updWsBounded (f : Nat → Wstate) (i : Nat) (w : Wstate) (n : Nat) :
    (∀ j, wsBounded (f j) n) → wsBounded w n → ∀ j, wsBounded (updWs f i w j) n := by
  intro hf hw j
  by_cases hj : j = i
  · subst hj; rw [updWsEq]; exact hw
  · rw [updWsNe _ _ _ _ hj]; exact hf j

theorem mnextBounded (σ : Mstate) (i : Nat) (l : Lbl) :
    cfgBounded σ →
    (∀ base ts vs, lbRd l = some (base, ts, vs) → ∀ t ∈ ts, t ≤ σ.msLog.length) →
    cfgBounded (mnext σ i l) := by
  intro hb hrd
  cases l with
  | LLoad aq base ts vs =>
    exact updWsBounded _ _ _ _ hb (loadPostRunBounded _ _ _ _ _ (hb i) (hrd base ts vs rfl))
  | LStore rl base vs kc =>
    show ∀ j, wsBounded (updWs _ _ _ j) (σ.msLog ++ _).length
    rw [List.length_append, List.length_singleton]
    exact updWsBounded _ _ _ _ (fun j => wsBoundedMono _ _ _ (hb j) (by omega))
      (storePostRunBounded _ _ _ _ _ σ.msLog.length _ (hb i) (Nat.le_refl _) (by omega))
  | LFence pr pw sr sw =>
    exact updWsBounded _ _ _ _ hb (fencePostBounded _ _ _ _ _ _ (hb i))
  | LRmw aq rl base ts rvs wvs kc =>
    show ∀ j, wsBounded (updWs _ _ _ j) (σ.msLog ++ _).length
    rw [List.length_append, List.length_singleton]
    exact updWsBounded _ _ _ _ (fun j => wsBoundedMono _ _ _ (hb j) (by omega))
      (storePostRunBounded _ _ _ _ _ σ.msLog.length _
        (loadPostRunBounded _ _ _ _ _ (hb i) (hrd base ts rvs rfl)) (Nat.le_refl _) (by omega))

theorem candBoundedUpto (c : Cand) (n : Nat) :
    n ≤ c.cdTr.length →
    (∀ k s, k < n → c.cdTr[k]? = some s → mstepOk (stt (candExec c) k) s.esAg s.esLb) →
    cfgBounded (stt (candExec c) n) := by
  induction n with
  | zero =>
    intro _ _
    have hσ : stt (candExec c) 0 = candInit c := sttLookup _ _ _ (replay0 (candInit c) c.cdTr)
    rw [hσ]; intro i; exact wsBoundedInit _
  | succ n ih =>
    intro hn hok
    obtain ⟨s, hs⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := c.cdTr) (i := n) (by omega))
    rw [candNext c n s hs]
    apply mnextBounded
    · exact ih (by omega) (fun k s' hk => hok k s' (by omega))
    · intro base ts vs hrd
      have hstep := hok n s (by omega) hs
      cases hl : s.esLb with
      | LLoad aq b0 t0 v0 =>
        rw [hl] at hrd hstep
        simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
        obtain ⟨rfl, rfl, rfl⟩ := hrd
        exact rdOkTsBounded _ _ _ _ _ _ _ hstep
      | LStore => rw [hl] at hrd; simp [lbRd] at hrd
      | LFence => rw [hl] at hrd; simp [lbRd] at hrd
      | LRmw aq rl b0 t0 rv0 wv0 kc =>
        rw [hl] at hrd hstep
        simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
        obtain ⟨rfl, rfl, rfl⟩ := hrd
        exact rdOkTsBounded _ _ _ _ _ _ _ hstep.2.2.1

/-! ## 7.5 Completeness for coherence-latest candidates (the SC fragment) -/

def candShape (c : Cand) : Prop :=
  ∀ (k : Nat) (s : Estep), c.cdTr[k]? = some s →
    match s.esLb with
    | LLoad _ _ ts vs => vs.length = ts.length
    | LStore _ _ vs _ => vs ≠ []
    | LFence .. => True
    | LRmw _ _ _ ts rvs wvs _ => wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length

def candValues (c : Cand) : Prop :=
  ∀ k s base ts vs, c.cdTr[k]? = some s → lbRd s.esLb = some (base, ts, vs) →
    ∀ (j : Nat) t v, ts[j]? = some t → vs[j]? = some v →
      logByte c.cdImg (cdLog c k) t (accAddr base j) = some v

def candLatest (c : Cand) : Prop :=
  ∀ k s base ts vs, c.cdTr[k]? = some s → lbRd s.esLb = some (base, ts, vs) →
    ∀ (j : Nat) t, ts[j]? = some t → latest c.cdImg (cdLog c k) (accAddr base j) t

theorem scRdOk (c : Cand) (k : Nat) (s : Estep) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    candValues c → candLatest c → vs.length = ts.length →
    cfgBounded (stt (candExec c) k) →
    c.cdTr[k]? = some s → lbRd s.esLb = some (base, ts, vs) →
    rdOk (stt (candExec c) k).msImg (stt (candExec c) k).msLog
      ((stt (candExec c) k).msWs s.esAg) aq base ts vs := by
  intro hval hlat hlen hb hs hrd
  have hk := lookup_lt_Some hs
  have himg : (stt (candExec c) k).msImg = c.cdImg := candEimg c k (by omega)
  have hlog : (stt (candExec c) k).msLog = cdLog c k := candElog c k (by omega)
  rw [himg, hlog]
  refine ⟨hlen, fun j t v hj hv => ⟨hval k s base ts vs hs hrd j t v hj hv, ?_⟩⟩
  apply latestReadable _ _ _ _ _ _ _ (hlat k s base ts vs hs hrd j t hj)
  have hbd := hb s.esAg
  rw [hlog] at hbd
  have := loadVpreBounded ((stt (candExec c) k).msWs s.esAg) aq _ hbd
  have := hbd.2.2.2.2.2.2.1 (accAddr base j)
  omega

theorem scMstepOk (c : Cand) :
    candShape c → candValues c → candLatest c →
    ∀ n k s, k < n → c.cdTr[k]? = some s → mstepOk (stt (candExec c) k) s.esAg s.esLb := by
  intro hsh hval hlat n
  induction n with
  | zero => intro k s hk; omega
  | succ n ih =>
    intro k s hk hs
    by_cases hlt : k < n
    · exact ih k s hlt hs
    have : k = n := by omega
    subst this
    have hn := lookup_lt_Some hs
    have hb : cfgBounded (stt (candExec c) k) :=
      candBoundedUpto c k (by omega) (fun k' s' hk' hs' => ih k' s' hk' hs')
    have hshape := hsh k s hs
    have himg : (stt (candExec c) k).msImg = c.cdImg := candEimg c k (by omega)
    have hlog : (stt (candExec c) k).msLog = cdLog c k := candElog c k (by omega)
    cases hl : s.esLb with
    | LLoad aq base ts vs =>
      rw [hl] at hshape
      exact scRdOk c k s aq base ts vs hval hlat hshape hb hs (by rw [hl]; rfl)
    | LStore rl base vs kc => rw [hl] at hshape; exact hshape
    | LFence => trivial
    | LRmw aq rl base ts rvs wvs kc =>
      rw [hl] at hshape
      obtain ⟨hne, hlenw, hlenr⟩ := hshape
      refine ⟨hne, hlenw, scRdOk c k s aq base ts rvs hval hlat hlenr hb hs (by rw [hl]; rfl), ?_⟩
      rw [himg, hlog]
      intro j t hj
      exact hlat k s base ts rvs hs (by rw [hl]; rfl) j t hj

/-- THE COMPLETENESS THEOREM FOR THE SC FRAGMENT. -/
theorem scCandReachable (c : Cand) :
    candShape c → candValues c → candLatest c →
    execWf (candExec c) ∧ (candExec c).exTr = c.cdTr ∧ exImg (candExec c) = c.cdImg := by
  intro hsh hval hlat
  apply candReachable
  intro k s hs
  exact scMstepOk c hsh hval hlat (k + 1) k s (by omega) hs

/-! # 8. The event-level statement of §7 is REFUTED -/

def rfeEv (E : Exec) (w r : Ev) : Prop :=
  ∃ a k s, r = ev_at k ∧ E.exTr[k]? = some s ∧ rfB E a w r ∧ extW E w s.esAg

theorem mnextWsNe (σ : Mstate) (i : Nat) (l : Lbl) (j : Nat) :
    j ≠ i → (mnext σ i l).msWs j = σ.msWs j := by
  intro hne; cases l <;> exact updWsNe _ _ _ _ hne

/-- An agent that has not stepped yet still holds `wsInit`. -/
theorem candWsUntouched (c : Cand) (i n : Nat) :
    n ≤ c.cdTr.length →
    (∀ k s, k < n → c.cdTr[k]? = some s → s.esAg ≠ i) →
    (stt (candExec c) n).msWs i = wsInit := by
  induction n with
  | zero =>
    intro _ _
    have hσ : stt (candExec c) 0 = candInit c := sttLookup _ _ _ (replay0 (candInit c) c.cdTr)
    rw [hσ]; rfl
  | succ n ih =>
    intro hn hne
    obtain ⟨s, hs⟩ := someOfIsSome (lookup_lt_is_Some_2 (l := c.cdTr) (i := n) (by omega))
    rw [candNext c n s hs, mnextWsNe _ s.esAg _ i (fun h => hne n s (by omega) hs h.symm)]
    exact ih (by omega) (fun k' s' hk' => hne k' s' (by omega))

/-- Three stores and one two-byte load: ts 1 writes byte 1; ts 2 writes bytes
0 and 1; ts 3 writes byte 0; then agent 2 loads bytes 0,1 taking ts 3 for
byte 0 and ts 1 for byte 1 (both admissible: agent 2's floor is 0). -/
def ceTr (v : BitVec 8) : List Estep :=
  [⟨0, LStore false 1 [v] .WCplain⟩,
   ⟨0, LStore false 0 [v, v] .WCplain⟩,
   ⟨1, LStore false 0 [v] .WCplain⟩,
   ⟨2, LLoad false 0 [3, 1] [v, v]⟩]

def ce (v : BitVec 8) : Cand := ⟨fun _ => none, ceTr v⟩
def ceE (v : BitVec 8) : Exec := candExec (ce v)

theorem ceLog (v : BitVec 8) (k : Nat) : k ≤ 4 → elog (ceE v) k = trMsgs ((ceTr v).take k) := by
  intro hk; exact candElog (ce v) k hk

theorem ceWs2 (v : BitVec 8) (k : Nat) : k ≤ 3 → (stt (ceE v) k).msWs 2 = wsInit := by
  intro hk
  apply candWsUntouched (ce v) 2 k (by simp [ce, ceTr]; omega)
  intro k' s' hk' hs'
  simp only [ce, ceTr] at hs'
  match k', hs' with
  | 0, hs' => simp at hs'; subst hs'; simp
  | 1, hs' => simp at hs'; subst hs'; simp
  | 2, hs' => simp at hs'; subst hs'; simp
  | k' + 3, _ => omega

theorem ceLen (v : BitVec 8) : (ceE v).exTr.length = 4 := rfl

theorem ceExLog (v : BitVec 8) : exLog (ceE v) = trMsgs (ceTr v) := by
  rw [exLog, ceLen, ceLog v 4 (Nat.le_refl _)]; rfl

theorem ceTs0 (v : BitVec 8) : evTs (ceE v) (ev_at 0) = 1 := by
  rw [evTsAt, ceLog v 0 (by omega)]; rfl

theorem ceTs1 (v : BitVec 8) : evTs (ceE v) (ev_at 1) = 2 := by
  rw [evTsAt, ceLog v 1 (by omega)]; rfl

theorem ceTs2 (v : BitVec 8) : evTs (ceE v) (ev_at 2) = 3 := by
  rw [evTsAt, ceLog v 2 (by omega)]; rfl

/-- The four write operations of the witness. -/
theorem ceW0_1 (v : BitVec 8) : wrB (ceE v) 1 (ev_at 0) := by
  refine ⟨⟨_, rfl, rfl⟩, ?_⟩
  unfold evWrites
  rw [ceTs0, ceExLog]
  simp [ceTr, trMsgs, esMsg, lbWr, lbCls, logByte, msgByte]

theorem ceW1_0 (v : BitVec 8) : wrB (ceE v) 0 (ev_at 1) := by
  refine ⟨⟨_, rfl, rfl⟩, ?_⟩
  unfold evWrites
  rw [ceTs1, ceExLog]
  simp [ceTr, trMsgs, esMsg, lbWr, lbCls, logByte, msgByte]

theorem ceW1_1 (v : BitVec 8) : wrB (ceE v) 1 (ev_at 1) := by
  refine ⟨⟨_, rfl, rfl⟩, ?_⟩
  unfold evWrites
  rw [ceTs1, ceExLog]
  simp [ceTr, trMsgs, esMsg, lbWr, lbCls, logByte, msgByte]

theorem ceW2_0 (v : BitVec 8) : wrB (ceE v) 0 (ev_at 2) := by
  refine ⟨⟨_, rfl, rfl⟩, ?_⟩
  unfold evWrites
  rw [ceTs2, ceExLog]
  simp [ceTr, trMsgs, esMsg, lbWr, lbCls, logByte, msgByte]

/-- The load's two byte reads. -/
theorem ceRd0 (v : BitVec 8) : readsAt (ceE v) 3 0 3 v :=
  ⟨⟨2, LLoad false 0 [3, 1] [v, v]⟩, 0, [3, 1], [v, v], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩

theorem ceRd1 (v : BitVec 8) : readsAt (ceE v) 3 1 1 v :=
  ⟨⟨2, LLoad false 0 [3, 1] [v, v]⟩, 0, [3, 1], [v, v], 1, rfl, rfl, rfl, rfl, by simp [accAddr]⟩

/-- The machine really does admit this run. -/
theorem ceRd (v : BitVec 8) :
    rdOk (stt (ceE v) 3).msImg (stt (ceE v) 3).msLog ((stt (ceE v) 3).msWs 2) false 0 [3, 1]
      [v, v] := by
  have hlog : (stt (ceE v) 3).msLog = trMsgs ((ceTr v).take 3) := ceLog v 3 (by omega)
  have himg : (stt (ceE v) 3).msImg = (fun _ : Int => (none : Option (BitVec 8))) :=
    candEimg (ce v) 3 (by simp [ce, ceTr])
  rw [hlog, himg, ceWs2 v 3 (by omega)]
  have hfloor : ∀ a, max (loadVpre wsInit false) (coh wsInit a) = 0 := by
    intro a; rw [cohInit]; rfl
  refine ⟨rfl, ?_⟩
  intro j t v' hj hv'
  match j, hj, hv' with
  | 0, hj, hv' =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj hv'
    subst hj hv'
    refine ⟨by simp [ceTr, trMsgs, esMsg, lbWr, lbCls, logByte, msgByte, accAddr], ?_, ?_⟩
    · simp [ceTr, trMsgs, esMsg, lbWr, lbCls, logByte, msgByte, accAddr]
    · rw [hfloor]; rintro ⟨t', h1, h2, _⟩; omega
  | 1, hj, hv' =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hj hv'
    subst hj hv'
    refine ⟨by simp [ceTr, trMsgs, esMsg, lbWr, lbCls, logByte, msgByte, accAddr], ?_, ?_⟩
    · simp [ceTr, trMsgs, esMsg, lbWr, lbCls, logByte, msgByte, accAddr]
    · rw [hfloor]; rintro ⟨t', h1, h2, _⟩; omega
  | j + 2, hj, _ => simp at hj

theorem ceOk (v : BitVec 8) :
    ∀ k s, (ce v).cdTr[k]? = some s → mstepOk (stt (ceE v) k) s.esAg s.esLb := by
  intro k s hs
  simp only [ce, ceTr] at hs
  match k, hs with
  | 0, hs => simp at hs; subst hs; simp [mstepOk]
  | 1, hs => simp at hs; subst hs; simp [mstepOk]
  | 2, hs => simp at hs; subst hs; simp [mstepOk]
  | 3, hs => simp at hs; subst hs; exact ceRd v
  | k + 4, hs => simp at hs

theorem ceWf (v : BitVec 8) : execWf (ceE v) := (candReachable (ce v) (ceOk v)).1

/-- THE CYCLE. -/
theorem evRfeCoFrCyclic (v : BitVec 8) :
    ∃ (E : Exec) (e : Ev), execWf E ∧ tc (fun x y => rfeEv E x y ∨ co E x y ∨ fr E x y) e e := by
  refine ⟨ceE v, ev_at 2, ceWf v, ?_⟩
  have hrf0 : rfB (ceE v) 0 (ev_at 2) (ev_at 3) := ⟨ceW2_0 v, 3, 3, v, rfl, ceRd0 v, ceTs2 v⟩
  have hrf1 : rfB (ceE v) 1 (ev_at 0) (ev_at 3) := ⟨ceW0_1 v, 3, 1, v, rfl, ceRd1 v, ceTs0 v⟩
  refine tc_l (y := ev_at 3) (.inl ⟨0, 3, ⟨2, LLoad false 0 [3, 1] [v, v]⟩, rfl, rfl, hrf0, ?_⟩) ?_
  · exact ⟨_, rfl, by simp⟩
  refine tc_l (y := ev_at 1) (.inr (.inr ⟨1, ⟨ev_at 0, hrf1, ceW0_1 v, ceW1_1 v, ?_⟩, by simp⟩)) ?_
  · rw [ceTs0, ceTs1]; omega
  refine tc_once (.inr (.inl ⟨0, ceW1_0 v, ceW2_0 v, ?_⟩))
  rw [ceTs1, ceTs2]; omega

/-! # 9. WHAT SLICE 2 DOES NOT DO — the remaining obligation (prose)

(1) FULL COMPLETENESS (`promise_free_complete`: `candShape`, `candValues` and
`cand_axiomatic_ok` imply machine-reachability) was open here; by
`candReachable` it is the discharge of `mstepOk` at every step, i.e. a
VIEW-DOMINATION lemma.  It is proved in `WeakAxiomatic3`
(`promiseFreeCompleteClean`), where the domination is stated per view
component and needs only the LOCAL axioms.  (2) The three places slice 1's §7
spec moved: `ob` is over OPERATIONS (forced by `evRfeCoFrCyclic`); `ppoOp` has
FIVE arms (po into a write; RVWMO ppo rule 7, without which completeness is
false — `WeakAxiomatic3` §13); the `ordPr` arm carries `¬ wrB E a1 e1`.
(3) OWED LIFTS: `rdOkTsBounded`, `execWsBounded` and `evpre` with its lemmas
now live in `WeakAxiomatic`. -/

end Weak
