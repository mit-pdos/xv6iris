/-
Weak: **allocproc route P, row P-W6 on the S-R walk — THE ISSUE-STAMP MAP and `ForeignBelowLanded`**
(F-PW6-1 (a), [OWN.149]; `PROGRESS-PW6.md` resume step "`SimRelP` … including the stamp map that turns
`SbIssueCo.noForeignBelow` into `SbRealP.ForeignBelowLanded`").  Lean-only, no Rocq twin.  A PRIMED TWIN:
nothing registered imports this file.

**Spec first.**  RVWMO does not order two harts' plain stores to one byte by the order they issued; MachCSL-P
does (`SbRealP.landBlockedForeign`): a pending entry lands only over LANDED foreign entries
(`SbRealP.ForeignBelowLanded`, the premise of the landing row `SbRealP.rmemPLand`).  The walk lands GF's next
write (`SbOrdR.landR`) and the named input `SbIssueCo.IssueCo` (discharged by the census,
`SbIssueCoR.issueCoOfCustodyR`) says a foreign store issued EARLIER on a common byte and still pending is GF
co-before — hence landed by then (`SbIssueCoR.noForeignBelowR`).  What is missing is the link between MachCSL's
ISSUE STAMPS and the walk's ISSUE ITEMS; that is the realization's stamp map:

* **`StampMap c σ ι`** (a conjunct of P-W6's `SimRelP`): the `k`-th pending MachCSL entry of hart `cpu`
  (stamp `s.1`) and the walk's `k`-th pending entry of row `hartAgent cpu` (tag `q.1`) come from the walk's
  EVENT ITEM `ι s.1`, which steps that store (`SbIssueCo.evAt`).
* **`StampMono σ ι`**: issue stamps increase with walk items (one MachCSL stamp per walk item at most: the plain
  store's issue, an AMO's write, the DMA pair's landing).

**`foreignBelowOfStamp`**: at an enabled S-R landing of hart `cpu`'s `k`-th pending entry, with `rmemP`, the
stamp map and `IssueCo`, MachCSL's `ForeignBelowLanded` holds at its stamp.  Proof: a foreign pending entry `y`
below the landing entry `x` in a byte's history has a smaller stamp (`histOkP`'s pending prefix in issue
order, `stampsNodup`), is a hart's buffered store (`okP`'s `sbAuth`), corresponds to a walk pending entry of
another row writing that byte (`R-sb` + `memStamp`), issued at an earlier item (`StampMono`) —
`noForeignBelowR` refutes it.

Spec: FAITHFUL (proof organisation; the one named input is `IssueCo`).  Lean-only helpers `SbRealPStamp.*`.
-/
import Weak.SbRealP
import Weak.SbIssueCoR

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbWalk SbAgree SbReplay SbOrd SbRealP SbIssueCo

namespace SbRealPStamp

/-! # 1. The stamp map -/

/-- **THE ISSUE-STAMP MAP**: MachCSL's pending entries and the walk's pending entries of a hart, index by
index, were created by the walk's event item `ι` of their stamp, which steps that store. -/
def StampMap (c : CandW) (σ : MState) (ι : Nat → Nat) : Prop :=
  ∀ (cpu : CPU) (k : Nat) (s : Nat × Nat) (q : Nat × SbEnt), (σ.sb cpu)[k]? = some s →
    ((SbWalk.cur c).pend (hartAgent cpu))[k]? = some q →
    ι s.1 < c.its.length ∧ SbIssueCo.evAt c (ι s.1) = some (hartAgent cpu, q.1)

/-- **ISSUE STAMPS INCREASE WITH WALK ITEMS.** -/
def StampMono (σ : MState) (ι : Nat → Nat) : Prop :=
  ∀ s1 s2, 1 ≤ s1 → s1 < s2 → s2 ≤ σ.top → ι s1 < ι s2

/-! # 2. Helpers -/

/-- In `H1 ++ x :: H2` with distinct stamps, an entry of `H2` has another stamp than `x`. -/
theorem stampNeBelow (H1 H2 : Hist) (x y : HEnt) (hnd : ((H1 ++ x :: H2).map HEnt.t).Nodup) (hy : y ∈ H2) :
    y.t ≠ x.t := by
  intro he
  rw [List.map_append, List.map_cons] at hnd
  have h2 := (List.nodup_append.1 hnd).2.1
  have := (List.nodup_cons.1 h2).1
  exact this (he ▸ List.mem_map_of_mem hy)

/-- In `H1 ++ x :: H2` in co order, `x` is co-above every entry of `H2`. -/
theorem coAboveBelow (lp : LandPos) (H1 H2 : Hist) (x y : HEnt) (hpw : (H1 ++ x :: H2).Pairwise (coAbove lp))
    (hy : y ∈ H2) : coAbove lp x y := by
  have h2 := (List.pairwise_append.1 hpw).2.1
  exact (List.pairwise_cons.1 h2).1 y hy

/-- A history entry gives a present stamp byte. -/
theorem stampByteOfMem (H : Hist) (y : HEnt) (hy : y ∈ H) : (stampByte H y.t).isSome := by
  unfold stampByte
  cases h : H.find? (fun e => e.t == y.t) with
  | none =>
    exfalso
    have := List.find?_eq_none.1 h y hy
    simp at this
  | some e => rfl

/-- A pending store's message byte makes its label write that byte. -/
theorem wrsBOfMsg (rl : Bool) (base : Int) (vs : List (BitVec 8)) (tid : Option Nat) (kc : WmClass) (a : Int)
    (h : (msgByte ⟨base, vs, tid, kc⟩ a).isSome) : wrsB (LStore rl base vs kc) a = true := by
  obtain ⟨j, hj, rfl⟩ := msgByteIndex base vs tid kc a h
  exact (wrsBIff _ _).2 ⟨base, vs, j, vs[j], rfl, List.getElem?_eq_getElem hj, rfl⟩

/-- The twin entry and the walk's tagged entry of agent `i` at index `k`. -/
theorem pendOfSb {img : Image} {w : WS} (hI : Inv img w) (i k : Nat) (e : SbEnt) (he : (w.σ.sb i)[k]? = some e) :
    ∃ q, (w.pend i)[k]? = some q ∧ q.2 = e := by
  rw [hI.sb i, List.getElem?_map] at he
  cases hq : (w.pend i)[k]? with
  | none => rw [hq] at he; cases he
  | some q =>
    rw [hq] at he
    exact ⟨q, rfl, Option.some.inj he⟩

/-! # 3. `ForeignBelowLanded` from the stamp map -/

/-- **`ForeignBelowLanded` AT AN ENABLED S-R LANDING**, from `rmemP`, the stamp map and `IssueCo`. -/
theorem foreignBelowOfStamp {N : Nat} {img : Image} {X : Geid → Prop} {dev : List Geid} (pol : SbPol)
    (G : Gexec) (c : CandW) (σ : MState) (ι : Nat → Nat) (hco : IssueCo G c) (hnd : G.gxGmo.Nodup)
    (hP : SbOrdR.PInvR N img G X dev (SbWalk.cur c)) (hR : rmemP img (SbWalk.cur c).σ σ)
    (hS : StampMap c σ ι) (hM : StampMono σ ι)
    (cpu : CPU) (k : Nat) (hg : SbOrdR.landR pol G (SbWalk.cur c) (hartAgent cpu) k)
    (s : Nat × Nat) (hs : (σ.sb cpu)[k]? = some s) :
    ForeignBelowLanded σ cpu s.1 := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hstn, hok⟩ := hR
  obtain ⟨h1, h2, h3, hndl, hll, hph, hsbA, hord, hep9⟩ := hok
  intro a H hHa H1 x H2 hHe hxt y hy hyt
  cases hly : σ.lp y.t with
  | some _ => rfl
  | none =>
    exfalso
    -- the landing entry `s` is pending, its stamp at most the top
    have hsm : s ∈ σ.sb cpu := List.mem_of_getElem? hs
    obtain ⟨hs1, hs2, -, hs4⟩ := (hsbA cpu s.1).1 ⟨s.2, hsm⟩
    have hlps : σ.lp s.1 = none := lpOf_none_of_not_mem σ.llog s.1 hs4 (by omega)
    -- `y` is below `x`: a smaller stamp
    have hok1 := h1 a H hHa
    rw [hHe] at hok1
    have hca := coAboveBelow σ.lp H1 H2 x y hok1.1 hy
    simp only [coAbove, hxt, hlps, hly] at hca
    have hne := stampNeBelow H1 H2 x y (by rw [← hHe]; exact hstn a H hHa) hy
    have hylt : y.t < s.1 := by rw [hxt] at hne; omega
    -- `y` is a foreign hart's buffered store
    have hy0 : y.t ≠ 0 := by
      intro h0
      have : σ.lp y.t = some 0 := by rw [h0]; rfl
      rw [hly] at this; cases this
    have hyM : y ∈ H := by rw [hHe]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)
    obtain ⟨hyle, hyl⟩ := hok1.2 y (by rw [← hHe]; exact hyM)
    have hyl' : σ.log[y.t - 1]? = some y.tid := by
      rcases hyl with h | h
      · exact absurd h hy0
      · exact h
    have hynl : y.t ∉ σ.llog := fun hm =>
      (Option.ne_none_iff_isSome.2 ((lpOf_isSome_iff σ.llog y.t hy0).2 hm)) hly
    obtain ⟨c', hc'⟩ := hph y.t (by omega) hyle hynl
    rw [hyl', Option.some.injEq] at hc'
    have hcne : hartAgent c' ≠ hartAgent cpu := fun h => hyt (by rw [hc']; exact h)
    obtain ⟨ey, hey⟩ := (hsbA c' y.t).2 ⟨by omega, hyle, by rw [← hc']; exact hyl', hynl⟩
    obtain ⟨k1, hk1⟩ := idxOfMem hey
    -- the twin's and the walk's entries for `y` and for `s`
    obtain ⟨e1, he1, hr1⟩ := forall2GetL (hsb c') hk1
    obtain ⟨q, hq, hqe⟩ := pendOfSb hP.inv (hartAgent c') k1 e1 he1
    obtain ⟨e2, he2, hr2⟩ := forall2GetL (hsb cpu) hs
    obtain ⟨p, hp, hpe⟩ := pendOfSb hP.inv (hartAgent cpu) k e2 he2
    -- both write the byte `paZ a`
    have hmy : (msgByte q.2.msg (paZ a)).isSome := by
      rw [hqe, ← hr1.2.2.2 a]
      unfold memStamp; rw [hHa]
      exact stampByteOfMem H y hyM
    have hmx : (msgByte p.2.msg (paZ a)).isSome := by
      rw [hpe, ← hr2.2.2.2 a]
      unfold memStamp; rw [hHa]
      have hxM : x ∈ H := by rw [hHe]; exact List.mem_append_right _ (List.mem_cons_self ..)
      have := stampByteOfMem H x hxM
      rwa [hxt] at this
    have hqm : q ∈ (SbWalk.cur c).pend (hartAgent c') := List.mem_of_getElem? hq
    have hpm : p ∈ (SbWalk.cur c).pend (hartAgent cpu) := List.mem_of_getElem? hp
    obtain ⟨rl1, base1, vs1, kc1, hl1, -, hm1⟩ := SbOrdR.pendLblR hP _ q hqm
    obtain ⟨rl2, base2, vs2, kc2, hl2, -, hm2⟩ := SbOrdR.pendLblR hP _ p hpm
    rw [hm1] at hmy
    rw [hm2] at hmx
    -- their issue items, in stamp order
    obtain ⟨hi1, hev1⟩ := hS c' k1 (y.t, ey) q hk1 hq
    obtain ⟨hi2, hev2⟩ := hS cpu k s p hs hp
    have hlt : ι y.t < ι s.1 := hM y.t s.1 (by omega) hylt hs2
    exact SbIssueCoR.noForeignBelowR pol G c hco hnd hP (hartAgent cpu) k hg p hp (hartAgent c') q hqm hcne
      (ι y.t) (ι s.1) hlt (Nat.le_of_lt hi2) hev1 hev2 _ _ hl1 hl2 rfl rfl (paZ a)
      (wrsBOfMsg _ _ _ _ _ _ hmy) (wrsBOfMsg _ _ _ _ _ _ hmx)

/-! # 4. The stamp map along the realization

The realization pairs each walk item with at most one MachCSL memory move that creates a stamp: a plain
store's ISSUE (`MState.issue`, the stamp pending), an exclusive write (`MState.storeL`) or the DMA pair's
landing (`MState.storeDma`), both landing at once; a hart landing (`MState.land`) moves no stamp; every other
item none.  `StampBound`: every stamp so far was created at an earlier item. -/

/-- Every issue stamp was created at an earlier walk item. -/
def StampBound (c : CandW) (σ : MState) (ι : Nat → Nat) : Prop :=
  ∀ s, 1 ≤ s → s ≤ σ.top → ι s < c.its.length

/-- **THE STAMP RELATION** (`SimRelP`'s conjunct). -/
def StampRel (c : CandW) (σ : MState) (ι : Nat → Nat) : Prop :=
  StampMap c σ ι ∧ StampMono σ ι ∧ StampBound c σ ι

theorem evAtSnoc (c : CandW) (it : Item) (k : Nat) (hk : k < c.its.length) :
    SbIssueCo.evAt (snocC c it) k = SbIssueCo.evAt c k := by
  unfold SbIssueCo.evAt
  have h1 : (snocC c it).its[k]? = c.its[k]? := by
    show (c.its ++ [it])[k]? = c.its[k]?
    rw [List.getElem?_append_left hk]
  rw [h1, stAtSnoc c it k (Nat.le_of_lt hk)]

theorem evAtSnocEnd (c : CandW) (s : Estep) :
    SbIssueCo.evAt (snocC c (.ev s)) c.its.length = some (s.esAg, ((SbWalk.cur c).rows s.esAg).length) := by
  unfold SbIssueCo.evAt
  have h1 : (snocC c (.ev s)).its[c.its.length]? = some (.ev s) := by
    show (c.its ++ [Item.ev s])[c.its.length]? = _
    simp
  rw [h1, stAtSnoc c _ _ (Nat.le_refl _)]
  rfl

theorem snocLen (c : CandW) (it : Item) : (snocC c it).its.length = c.its.length + 1 := by
  simp [snocC]

/-- **A FRAME ITEM** (no MachCSL stamp moves, the walk's pending tags unchanged): the stamp relation is kept. -/
theorem stampFrame (c : CandW) (it : Item) (σ σ' : MState) (ι : Nat → Nat) (hS : StampRel c σ ι)
    (hsb : σ'.sb = σ.sb) (htop : σ'.top = σ.top)
    (htag : ∀ cpu : CPU, ((SbWalk.cur (snocC c it)).pend (hartAgent cpu)).map Prod.fst =
      ((SbWalk.cur c).pend (hartAgent cpu)).map Prod.fst) :
    StampRel (snocC c it) σ' ι := by
  obtain ⟨hM, hO, hB⟩ := hS
  refine ⟨fun cpu k s q hs hq => ?_, fun s1 s2 h1 h2 h3 => hO s1 s2 h1 h2 (htop ▸ h3), fun s h1 h2 => ?_⟩
  · rw [hsb] at hs
    have hq' : (((SbWalk.cur c).pend (hartAgent cpu)).map Prod.fst)[k]? = some q.1 := by
      rw [← htag cpu, List.getElem?_map, hq]; rfl
    rw [List.getElem?_map] at hq'
    cases hq0 : ((SbWalk.cur c).pend (hartAgent cpu))[k]? with
    | none => rw [hq0] at hq'; cases hq'
    | some q0 =>
      rw [hq0] at hq'
      have hq01 : q0.1 = q.1 := Option.some.inj hq'
      obtain ⟨hlt, hev⟩ := hM cpu k s q0 hs hq0
      refine ⟨by rw [snocLen]; omega, ?_⟩
      rw [evAtSnoc c it _ hlt, hev, hq01]
  · rw [snocLen]; have := hB s h1 (htop ▸ h2); omega

/-- `filter` by a distinct key is `eraseIdx`. -/
theorem filterEraseIdx : ∀ (l : List (Nat × Nat)) (k : Nat) (x : Nat × Nat), l[k]? = some x →
    (l.map Prod.fst).Nodup → l.filter (fun p => p.1 != x.1) = l.eraseIdx k
  | [], _, _, h, _ => by simp at h
  | y :: l, 0, x, h, hnd => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.eraseIdx_cons_zero]
    rw [List.filter_eq_self]
    intro p hp
    simp only [bne_iff_ne, ne_eq]
    intro he
    exact hnd.1 ⟨p, hp, he⟩
  | y :: l, k + 1, x, h, hnd => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hyx : y.1 ≠ x.1 := by
      intro he
      exact hnd.1 ⟨x, List.mem_of_getElem? h, he.symm⟩
    simp only [List.filter_cons, List.eraseIdx_cons_succ]
    rw [if_pos (by simpa using hyx), filterEraseIdx l k x h hnd.2]

/-- Positions of an `eraseIdx`. -/
theorem eraseIdxGet {α : Type} (l : List α) (k k' : Nat) :
    (l.eraseIdx k)[k']? = if k' < k then l[k']? else l[k' + 1]? := by
  induction l generalizing k k' with
  | nil => simp
  | cons y l ih =>
    cases k with
    | zero => simp
    | succ k =>
      cases k' with
      | zero => simp
      | succ k' =>
        simp only [List.eraseIdx_cons_succ, List.getElem?_cons_succ, ih]
        by_cases h : k' < k
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]

/-- **A HART LANDING** (`MState.land` of `cpu`'s `k`-th pending stamp, the walk's landing of row
`hartAgent cpu`'s `k`-th pending entry): the stamp relation is kept. -/
theorem stampLand (c : CandW) (σ : MState) (ι : Nat → Nat) (hS : StampRel c σ ι) (hok : σ.okP)
    (cpu : CPU) (k : Nat) (s : Nat × Nat) (hs : (σ.sb cpu)[k]? = some s)
    (p : Nat × SbEnt) (hp : ((SbWalk.cur c).pend (hartAgent cpu))[k]? = some p) :
    StampRel (snocC c (.land (hartAgent cpu) k)) (σ.land cpu s.1) ι := by
  obtain ⟨hM, hO, hB⟩ := hS
  have hcur : SbWalk.cur (snocC c (.land (hartAgent cpu) k)) = nextI (SbWalk.cur c) (.land (hartAgent cpu) k) := by
    unfold SbWalk.cur; rw [snocLen]; exact stAtSnocEnd c _
  have hpe : ∀ j, (SbWalk.cur (snocC c (.land (hartAgent cpu) k))).pend j =
      if j = hartAgent cpu then ((SbWalk.cur c).pend (hartAgent cpu)).eraseIdx k else (SbWalk.cur c).pend j := by
    intro j
    rw [hcur]
    show (match ((SbWalk.cur c).pend (hartAgent cpu))[k]? with
      | some p => (⟨SbCand.nextL (SbWalk.cur c).σ (hartAgent cpu) k,
          upd (SbWalk.cur c).pend (hartAgent cpu) (((SbWalk.cur c).pend (hartAgent cpu)).eraseIdx k),
          (SbWalk.cur c).rows, (SbWalk.cur c).fw, (SbWalk.cur c).gmo ++ [(hartAgent cpu, p.1)]⟩ : WS)
      | none => SbWalk.cur c).pend j = _
    rw [hp]
    by_cases h : j = hartAgent cpu
    · subst h; simp [upd]
    · simp [upd, h]
  have hnd : ((σ.sb cpu).map Prod.fst).Nodup := by
    have := hok.2.2.2.2.2.2.2.1 cpu
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact this.imp (fun h => Nat.ne_of_lt h.1)
  refine ⟨fun cpu' k' s' q hs' hq => ?_, fun s1 s2 h1 h2 h3 => hO s1 s2 h1 h2 h3, fun s0 h1 h2 => ?_⟩
  · rw [hpe] at hq
    by_cases hc : cpu' = cpu
    · subst hc
      rw [if_pos rfl, eraseIdxGet] at hq
      have hs'' : ((σ.sb cpu').eraseIdx k)[k']? = some s' := by
        have : (σ.land cpu' s.1).sb cpu' = (σ.sb cpu').filter (fun p => p.1 != s.1) := by
          show (if cpu' = cpu' then _ else _) = _; rw [if_pos rfl]
        rw [this, filterEraseIdx _ k s hs hnd] at hs'
        exact hs'
      rw [eraseIdxGet] at hs''
      split at hq
      · rw [if_pos (by assumption)] at hs''
        obtain ⟨hlt, hev⟩ := hM cpu' k' s' q hs'' hq
        exact ⟨by rw [snocLen]; omega, by rw [evAtSnoc c _ _ hlt]; exact hev⟩
      · rw [if_neg (by assumption)] at hs''
        obtain ⟨hlt, hev⟩ := hM cpu' (k' + 1) s' q hs'' hq
        exact ⟨by rw [snocLen]; omega, by rw [evAtSnoc c _ _ hlt]; exact hev⟩
    · have hne : hartAgent cpu' ≠ hartAgent cpu := fun h => hc (SbRealP.hartAgentInj h)
      rw [if_neg hne] at hq
      have : (σ.land cpu s.1).sb cpu' = σ.sb cpu' := by
        show (if cpu' = cpu then _ else _) = _; rw [if_neg hc]
      rw [this] at hs'
      obtain ⟨hlt, hev⟩ := hM cpu' k' s' q hs' hq
      exact ⟨by rw [snocLen]; omega, by rw [evAtSnoc c _ _ hlt]; exact hev⟩
  · rw [snocLen]; have := hB s0 h1 h2; omega

/-- **A NEW STAMP** (a write landing at once: `storeL`, the DMA pair's landing; or a plain store's issue) at
the walk item `c.its.length`: the updated map. -/
def ιNew (ι : Nat → Nat) (top len : Nat) : Nat → Nat := fun s => if s = top + 1 then len else ι s

/-- **A WRITE LANDING AT ONCE** (`MState.storeL`, `MState.storeDma` with `n ≠ 0`): one new stamp, no buffer
move, the walk's pending tags unchanged. -/
theorem stampNew (c : CandW) (it : Item) (σ σ' : MState) (ι : Nat → Nat) (hS : StampRel c σ ι)
    (hsb : σ'.sb = σ.sb) (htop : σ'.top = σ.top + 1) (hok : σ.okP)
    (htag : ∀ cpu : CPU, ((SbWalk.cur (snocC c it)).pend (hartAgent cpu)).map Prod.fst =
      ((SbWalk.cur c).pend (hartAgent cpu)).map Prod.fst) :
    StampRel (snocC c it) σ' (ιNew ι σ.top c.its.length) := by
  obtain ⟨hM, hO, hB⟩ := hS
  refine ⟨fun cpu k s q hs hq => ?_, fun s1 s2 h1 h2 h3 => ?_, fun s h1 h2 => ?_⟩
  · rw [hsb] at hs
    have hsm := List.mem_of_getElem? hs
    obtain ⟨-, hst, -⟩ := (hok.2.2.2.2.2.2.1 cpu s.1).1 ⟨s.2, hsm⟩
    have hne : s.1 ≠ σ.top + 1 := by omega
    have hq' : (((SbWalk.cur c).pend (hartAgent cpu)).map Prod.fst)[k]? = some q.1 := by
      rw [← htag cpu, List.getElem?_map, hq]; rfl
    rw [List.getElem?_map] at hq'
    cases hq0 : ((SbWalk.cur c).pend (hartAgent cpu))[k]? with
    | none => rw [hq0] at hq'; cases hq'
    | some q0 =>
      rw [hq0] at hq'
      have hq01 : q0.1 = q.1 := Option.some.inj hq'
      obtain ⟨hlt, hev⟩ := hM cpu k s q0 hs hq0
      unfold ιNew; rw [if_neg hne]
      exact ⟨by rw [snocLen]; omega, by rw [evAtSnoc c it _ hlt, hev, hq01]⟩
  · unfold ιNew
    by_cases h2t : s2 = σ.top + 1
    · rw [if_pos h2t, if_neg (by omega)]
      exact hB s1 h1 (by omega)
    · rw [if_neg h2t, if_neg (by omega)]
      exact hO s1 s2 h1 h2 (by omega)
  · unfold ιNew; rw [snocLen]
    by_cases h2t : s = σ.top + 1
    · rw [if_pos h2t]; omega
    · rw [if_neg h2t]; have := hB s h1 (by omega); omega

/-- **A PLAIN STORE'S ISSUE** (`MState.issue` of hart `cpu`, the walk's `LStore` event of row `hartAgent cpu`):
the new pending stamp maps to the issuing item. -/
theorem stampIssue (c : CandW) (σ : MState) (ι : Nat → Nat) (hS : StampRel c σ ι) (hok : σ.okP)
    (cpu : CPU) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) (s : Estep) (hag : s.esAg = hartAgent cpu)
    (hlen : (σ.sb cpu).length = ((SbWalk.cur c).pend (hartAgent cpu)).length) (e : SbEnt)
    (hpe : ∀ i, (SbWalk.cur (snocC c (.ev s))).pend i =
      if i = hartAgent cpu then (SbWalk.cur c).pend (hartAgent cpu) ++
        [(((SbWalk.cur c).rows (hartAgent cpu)).length, e)]
      else (SbWalk.cur c).pend i) :
    StampRel (snocC c (.ev s)) (σ.issue cpu pa n w) (ιNew ι σ.top c.its.length) := by
  obtain ⟨hM, hO, hB⟩ := hS
  refine ⟨fun cpu' k s' q hs hq => ?_, fun s1 s2 h1 h2 h3 => ?_, fun s0 h1 h2 => ?_⟩
  · rw [hpe] at hq
    by_cases hc : cpu' = cpu
    · subst hc
      rw [if_pos rfl] at hq
      have hsb' : (σ.issue cpu' pa n w).sb cpu' = σ.sb cpu' ++ [(σ.top + 1, σ.sbEp cpu')] := by
        show (if cpu' = cpu' then _ else _) = _; rw [if_pos rfl]
      rw [hsb'] at hs
      by_cases hk : k < (σ.sb cpu').length
      · rw [List.getElem?_append_left hk] at hs
        rw [List.getElem?_append_left (by omega)] at hq
        have hsm := List.mem_of_getElem? hs
        obtain ⟨-, hst, -⟩ := (hok.2.2.2.2.2.2.1 cpu' s'.1).1 ⟨s'.2, hsm⟩
        unfold ιNew; rw [if_neg (by omega)]
        obtain ⟨hlt, hev⟩ := hM cpu' k s' q hs hq
        exact ⟨by rw [snocLen]; omega, by rw [evAtSnoc c _ _ hlt]; exact hev⟩
      · have hk' : k = (σ.sb cpu').length := by
          have := (List.getElem?_eq_some_iff.1 hs).1
          simp at this; omega
        subst hk'
        rw [List.getElem?_concat_length, Option.some.injEq] at hs
        rw [hlen, List.getElem?_concat_length, Option.some.injEq] at hq
        subst hs; subst hq
        unfold ιNew; rw [if_pos rfl]
        refine ⟨by rw [snocLen]; omega, ?_⟩
        rw [evAtSnocEnd, hag]
    · have hne : hartAgent cpu' ≠ hartAgent cpu := fun h => hc (SbRealP.hartAgentInj h)
      rw [if_neg hne] at hq
      have : (σ.issue cpu pa n w).sb cpu' = σ.sb cpu' := by
        show (if cpu' = cpu then _ else _) = _; rw [if_neg hc]
      rw [this] at hs
      have hsm := List.mem_of_getElem? hs
      obtain ⟨-, hst, -⟩ := (hok.2.2.2.2.2.2.1 cpu' s'.1).1 ⟨s'.2, hsm⟩
      unfold ιNew; rw [if_neg (by omega)]
      obtain ⟨hlt, hev⟩ := hM cpu' k s' q hs hq
      exact ⟨by rw [snocLen]; omega, by rw [evAtSnoc c _ _ hlt]; exact hev⟩
  · have htop : (σ.issue cpu pa n w).top = σ.top + 1 := by simp [MState.top]
    rw [htop] at h3
    unfold ιNew
    by_cases h2t : s2 = σ.top + 1
    · rw [if_pos h2t, if_neg (by omega)]
      exact hB s1 h1 (by omega)
    · rw [if_neg h2t, if_neg (by omega)]
      exact hO s1 s2 h1 h2 (by omega)
  · have htop : (σ.issue cpu pa n w).top = σ.top + 1 := by simp [MState.top]
    rw [htop] at h2
    unfold ιNew; rw [snocLen]
    by_cases h2t : s0 = σ.top + 1
    · rw [if_pos h2t]; omega
    · rw [if_neg h2t]; have := hB s0 h1 (by omega); omega

/-- The empty walk and the booted machine: no stamp. -/
theorem stampBoot (img : Image) (σ : MState) (hsb : ∀ cpu, σ.sb cpu = []) (htop : σ.top = 0) :
    StampRel ⟨img, []⟩ σ (fun _ => 0) :=
  ⟨fun cpu k s q hs _ => by rw [hsb cpu] at hs; simp at hs, fun s1 s2 _ _ h3 => by omega,
   fun s h1 h2 => by omega⟩

#print axioms Weak.SbRealPStamp.stampLand
#print axioms Weak.SbRealPStamp.stampIssue
#print axioms Weak.SbRealPStamp.foreignBelowOfStamp

end SbRealPStamp

end Weak
