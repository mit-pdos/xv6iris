/-
Weak: **W10-3c [OWN.94] (N2′), increment 1 — THE WALK ORDER: the scheduler from a linear order of the
graph's events** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

`CatLin.schedSupplyCZ` (`Weak/CertZ7.lean`) asks, at every walk state, an ENABLED hart whose next read
/ fetch values agree with the latest bytes, an extra invariant `X` kept, and the final lock co.  This
file supplies everything but the VALUE agreement from a LINEAR ORDER `L` of `GF`'s events:

  §1  **`CertZ8.walkOrd`** — `L` lists every row event once, each hart's events in program order and
      the fabric's events (`gfDev`) in fabric order; the counting lemmas (`CertZ8.ordCount`: the
      events of hart `x` before `L[i] = (x, a)` are exactly its first `a`; `CertZ8.countAll`;
      `CertZ8.devCount`: the fabric events before `L[k] = gfDev[m]` are exactly the first `m`);
  (later increments: the prefix invariant and the scheduler step; the final lock co.)

Spec: proof organisation (FAITHFUL).  Lean-only helpers file-qualified (`CertZ8.*`).
-/
import Weak.CertZ7

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The walk order and its counting lemmas -/

/-- An event of the rows. -/
def CertZ8.evsOf (rows : List (List Lbl)) (e : Geid) : Prop :=
  e.1 < rows.length ∧ e.2 < (rows.getD e.1 []).length

/-- **THE WALK ORDER**: `L` lists every row event once, each hart's events in program order, the
fabric's events in fabric order. -/
def CertZ8.walkOrd (rows : List (List Lbl)) (dev : List Geid) (L : List Geid) : Prop :=
  L.Nodup ∧ (∀ e, e ∈ L ↔ CertZ8.evsOf rows e) ∧
  (∀ (i j x a b : Nat), L[i]? = some (x, a) → L[j]? = some (x, b) → a < b → i < j) ∧
  (∀ (m n i j : Nat) (e e' : Geid), dev[m]? = some e → dev[n]? = some e' → m < n →
    L[i]? = some e → L[j]? = some e' → i < j)

/-- Two duplicate-free lists with the same members have the same length. -/
theorem CertZ8.lenOfMem {α : Type} [DecidableEq α] (A B : List α) :
    A.Nodup → B.Nodup → (∀ e, e ∈ A ↔ e ∈ B) → A.length = B.length :=
  fun ha hb h => ((List.perm_ext_iff_of_nodup ha hb).2 h).length_eq

theorem CertZ8.nodupFst (x n : Nat) : ((List.range n).map (fun b => (x, b))).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact List.nodup_range.imp (fun h e => h (by simp only [Prod.mk.injEq] at e; exact e.2))

theorem CertZ8.memTakeIff {α : Type} (L : List α) (i : Nat) (e : α) :
    e ∈ L.take i ↔ ∃ j, j < i ∧ L[j]? = some e := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨j, hj⟩
    rw [List.getElem?_take] at hj
    split at hj
    · exact ⟨j, by omega, hj⟩
    · cases hj
  · rintro ⟨j, hj, he⟩
    exact ⟨j, by rw [List.getElem?_take, if_pos hj]; exact he⟩

/-- **`CertZ8.ordCount`**: before `L[i] = (x, a)`, hart `x`'s events in `L` are exactly its first `a`. -/
theorem CertZ8.ordCount (rows : List (List Lbl)) (dev L : List Geid) (i x a : Nat) :
    CertZ8.walkOrd rows dev L → L[i]? = some (x, a) →
    ((L.take i).filter (fun e => decide (e.1 = x))).length = a := by
  rintro ⟨hnd, hmem, hpo, -⟩ hi
  have hev := (hmem _).1 (List.mem_of_getElem? hi)
  rw [CertZ8.lenOfMem _ ((List.range a).map (fun b => (x, b)))
    ((hnd.sublist (List.take_sublist _ _)).filter _) (CertZ8.nodupFst x a) (fun e => ?_),
    List.length_map, List.length_range]
  rw [List.mem_filter, CertZ8.memTakeIff, List.mem_map]
  constructor
  · rintro ⟨⟨j, hji, hj⟩, hx⟩
    obtain ⟨y, b⟩ := e
    have hy : y = x := of_decide_eq_true hx
    subst hy
    refine ⟨b, List.mem_range.2 ?_, rfl⟩
    rcases Nat.lt_trichotomy b a with h | h | h
    · exact h
    · subst h
      have := NoDup_lookup hnd hj hi
      omega
    · have := hpo i j y a b hi hj h
      omega
  · rintro ⟨b, hb, rfl⟩
    have hb' := List.mem_range.1 hb
    have hev' : CertZ8.evsOf rows (x, b) := ⟨hev.1, by have := hev.2; dsimp only at this ⊢; omega⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ((hmem _).2 hev')
    exact ⟨⟨j, hpo j i x b a hj hi hb', hj⟩, by simp⟩

/-- **`CertZ8.countAll`**: all of hart `x`'s events are in `L`. -/
theorem CertZ8.countAll (rows : List (List Lbl)) (dev L : List Geid) (x : Nat) :
    CertZ8.walkOrd rows dev L → x < rows.length →
    (L.filter (fun e => decide (e.1 = x))).length = (rows.getD x []).length := by
  rintro ⟨hnd, hmem, -, -⟩ hx
  rw [CertZ8.lenOfMem _ ((List.range (rows.getD x []).length).map (fun b => (x, b)))
    (hnd.filter _) (CertZ8.nodupFst x _) (fun e => ?_), List.length_map, List.length_range]
  rw [List.mem_filter, List.mem_map, hmem]
  constructor
  · rintro ⟨⟨-, h2⟩, hx'⟩
    obtain ⟨y, b⟩ := e
    have hy : y = x := of_decide_eq_true hx'
    subst hy
    exact ⟨b, List.mem_range.2 h2, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨hx, List.mem_range.1 hb⟩, by simp⟩

/-- **`CertZ8.devCount`**: before `L[k] = gfDev[m]`, the fabric events in `L` are exactly the first
`m` of `gfDev`. -/
theorem CertZ8.devCount (rows : List (List Lbl)) (dev L : List Geid) (k m : Nat) (e : Geid) :
    CertZ8.walkOrd rows dev L → dev.Nodup → (∀ e', e' ∈ dev → e' ∈ L) →
    dev[m]? = some e → L[k]? = some e →
    ((L.take k).filter (fun e' => decide (e' ∈ dev))).length = m := by
  rintro ⟨hnd, -, -, hdv⟩ hdnd hsub hm hk
  have hmlt : m < dev.length := lookup_lt_Some hm
  rw [CertZ8.lenOfMem _ (dev.take m) ((hnd.sublist (List.take_sublist _ _)).filter _)
    (hdnd.sublist (List.take_sublist _ _)) (fun e' => ?_), List.length_take]
  · omega
  rw [List.mem_filter, CertZ8.memTakeIff, CertZ8.memTakeIff]
  constructor
  · rintro ⟨⟨j, hjk, hj⟩, hd⟩
    obtain ⟨m', hm'⟩ := List.mem_iff_getElem?.1 (of_decide_eq_true hd)
    refine ⟨m', ?_, hm'⟩
    rcases Nat.lt_trichotomy m' m with h | h | h
    · exact h
    · subst h
      rw [hm] at hm'
      cases hm'
      have := NoDup_lookup hnd hj hk
      omega
    · have := hdv m m' k j e e' hm hm' h hk hj
      omega
  · rintro ⟨m', hm'm, hm'⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (hsub e' (List.mem_of_getElem? hm'))
    exact ⟨⟨j, hdv m' m j k e' e hm' hm hm'm hj hk, hj⟩,
      decide_eq_true (List.mem_of_getElem? hm')⟩

/-! # 2. The prefix invariant, the value policy, the scheduler -/

/-- **THE PREFIX INVARIANT**: the walk has walked exactly the first `k` events of `L`: the counters
count them per hart, the fabric is `fab` at the number of fabric events walked, the trace's agents
are theirs. -/
def CertZ8.prefInv (L dev : List Geid) (fab : Nat → Efab) : CertZ2.WInv :=
  fun St _ _ cnt => ∃ k, k ≤ L.length ∧
    (∀ x, cnt x = ((L.take k).filter (fun e => decide (e.1 = x))).length) ∧
    St.cstDv (cdEnd St.cstC) = fab (((L.take k).filter (fun e => decide (e ∈ dev))).length) ∧
    St.cstC.cdTr.map Estep.esAg = (L.take k).map Prod.fst

/-- The walk's extra invariant: the prefix invariant and the value policy's own `Y`. -/
def CertZ8.xInv (L dev : List Geid) (fab : Nat → Efab) (Y : CertZ2.WInv) : CertZ2.WInv :=
  fun St itvOf fiOf cnt => CertZ8.prefInv L dev fab St itvOf fiOf cnt ∧ Y St itvOf fiOf cnt

/-- **THE VALUE POLICY — W10-4's obligation along the order**: at every lockstep state that has walked
a prefix of `L`, the next event's read footprint exists, its read and fetch VALUES are the latest
bytes, and `Y` is kept at the appended state. -/
def CertZ8.valPol (d0 : Efab) (rows : List (List Lbl)) (D : Nat → CertZ7.EmData)
    (L dev : List Geid) (fab : Nat → Efab) (Y : CertZ2.WInv) : Prop :=
  ∀ (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (cnt : Nat → Nat)
    (x : Nat) (lb : Lbl),
    CertZ.cstOkZW d0 St itvOf fiOf →
    CertZ6.lockInv rows (fun x => (D x).f) (CertZ8.xInv L dev fab Y) St itvOf fiOf cnt →
    (rows.getD x [])[cnt x]? = some lb →
    (∃ k, L[k]? = some (x, cnt x) ∧
      ∀ y, cnt y = ((L.take k).filter (fun e => decide (e.1 = y))).length) →
    CertZ4.readFoot St.cstC lb ∧
    (∀ aq base ts vs, lb = .LLoad aq base ts vs → lrdVs St.cstC base ts.length = vs) ∧
    (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc →
      lrdVs St.cstC base ts.length = rvs) ∧
    CertZ5.fetchAgree St.cstC ((D x).g (cnt x)) ∧
    Y (CertZ2.stSnoc St x (CertZ4.machLbl St.cstC lb) ((D x).f (cnt x + 1))
        (CertZ6.dNext (fun x => (D x).dvo) (fun x => (D x).tq) St x (cnt x)))
      (CertZ.itvSnoc St.cstC ⟨x, CertZ4.machLbl St.cstC lb⟩
        (((D x).g (cnt x)).map (CertZ5.fetchRet St.cstC)) itvOf fiOf)
      (CertZ.fiSnoc St.cstC ⟨x, CertZ4.machLbl St.cstC lb⟩
        (((D x).g (cnt x)).map (CertZ5.fetchRet St.cstC)) fiOf)
      (CertZ2.bump cnt x)

theorem CertZ8.filterSnoc (L : List Geid) (e : Geid) (p : Geid → Bool) :
    ((L ++ [e]).filter p).length = (L.filter p).length + if p e then 1 else 0 := by
  rw [List.filter_append, List.length_append]
  by_cases h : p e <;> simp [h]

/-- A contact-free slot is not a fabric event. -/
theorem CertZ8.quietNotDev (boot : Nat → Pexv6) (fab : Nat → Efab) (GF : Gfexec)
    (D : Nat → CertZ7.EmData) (x a : Nat) (lb : Lbl) :
    CertZ7.emDataOk boot fab GF D → (GF.gfGd.gdG.gxProg.getD x [])[a]? = some lb →
    x < GF.gfGd.gdG.gxProg.length →
    (D x).tq a = false → (x, a) ∉ GF.gfDev := by
  intro hD hlb hx htq hin
  obtain ⟨em, hem, hiff, -, -, -, -⟩ := hD x _ (CertZ7.getDSome _ x hx)
  obtain ⟨f0, g0, r0, -, hblk⟩ :=
    GraphFetchBlocks.hemitfBlocks (D x).dvi (D x).dvo (D x).tq 0 wsInit _ (boot x) em.emItems
      em.emFin hem
  obtain ⟨-, hq, -⟩ := hblk a lb hlb
  simp only [Nat.add_zero] at hq
  obtain ⟨hdv, hio⟩ := hq htq
  rcases (hiff a (lookup_lt_Some hlb)).1 hin with h | h | h
  · have hl : gxLbl GF.gfGd.gdG (x, a) = some lb := by
      unfold gxLbl; rw [CertZ7.getDSome _ x hx]; exact hlb
    unfold gisIo at h
    rw [hl] at h
    simp [hio] at h
  · exact h hdv.symm
  · rw [htq] at h; cases h

/-- **`CertZ8.schedOfOrd` — THE SCHEDULER FROM THE ORDER**: walk `L`'s events in order; the next
hart is `L[k]`'s, its slot is its counter (`ordCount`), its block is enabled (a fabric event is the
`m`-th of `gfDev` and the walk's fabric is `fab m`, `devCount`; a contact-free one keeps the
fabric), and the value policy gives the rest. -/
theorem CertZ8.schedOfOrd (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (GF : Gfexec)
    (D : Nat → CertZ7.EmData) (L : List Geid) (Y : CertZ2.WInv) :
    CertZ7.emDataOk boot fab GF D → GF.gfDev.Nodup →
    CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
    (∀ e, e ∈ GF.gfDev → e ∈ L) →
    CertZ8.valPol d0 GF.gfGd.gdG.gxProg D L GF.gfDev fab Y →
    CertZ6.schedZ d0 GF.gfGd.gdG.gxProg (fun x => (D x).f) (fun x => (D x).g)
      (fun x => (D x).dvi) (fun x => (D x).dvo) (fun x => (D x).tq)
      (CertZ8.xInv L GF.gfDev fab Y) := by
  intro hD hdnd hord hsub hval St itvOf fiOf cnt hok hinv hnd
  have hinv' := hinv
  obtain ⟨hper, hagt, ⟨k, hkL, hcnt, hfab, hags⟩, hY⟩ := hinv
  obtain ⟨y0, hy0, hy0c⟩ := hnd
  -- the walk is not finished, so `k < |L|`
  have hkl : k < L.length := by
    refine Nat.lt_of_le_of_ne hkL (fun he => ?_)
    rw [hcnt y0, he, List.take_length, CertZ8.countAll _ _ L y0 hord hy0] at hy0c
    omega
  obtain ⟨⟨x, a⟩, hk⟩ : ∃ e, L[k]? = some e := ⟨L[k], List.getElem?_eq_getElem hkl⟩
  have hev := (hord.2.1 _).1 (List.mem_of_getElem? hk)
  have hx : x < GF.gfGd.gdG.gxProg.length := hev.1
  have hca : cnt x = a := by rw [hcnt x]; exact CertZ8.ordCount _ _ L k x a hord hk
  obtain ⟨lb, hlb⟩ : ∃ lb, (GF.gfGd.gdG.gxProg.getD x [])[a]? = some lb :=
    ⟨_, List.getElem?_eq_getElem hev.2⟩
  rw [← hca] at hlb hk
  obtain ⟨hft, hvl, hvr, hfag, hY'⟩ := hval St itvOf fiOf cnt x lb hok hinv' hlb ⟨k, hk, hcnt⟩
  -- the fabric
  have hdevIdx : (x, cnt x) ∈ GF.gfDev → ∃ m, GF.gfDev[m]? = some (x, cnt x) ∧
      ((L.take k).filter (fun e => decide (e ∈ GF.gfDev))).length = m := by
    intro hin
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hin
    exact ⟨m, hm, CertZ8.devCount _ _ L k m _ hord hdnd hsub hm hk⟩
  obtain ⟨em, -, hiff, hpin, -, -, -⟩ := hD x _ (CertZ7.getDSome _ x hx)
  refine ⟨x, lb, hx, hlb, fun htq => ?_, hft, hvl, hvr, hfag, ?_, hY'⟩
  · obtain ⟨m, hm, hmc⟩ := hdevIdx ((hiff _ (lookup_lt_Some hlb)).2 (.inr (.inr htq)))
    rw [hfab, hmc]
    exact (hpin _ m hm).1
  · refine ⟨k + 1, hkl, fun y => ?_, ?_, ?_⟩
    · rw [take_S_r hk, CertZ8.filterSnoc]
      by_cases hy : y = x
      · subst hy; rw [CertZ2.bumpSelf, hcnt y]; simp
      · rw [CertZ2.bumpNe cnt x y hy, hcnt y]
        simp [Ne.symm hy]
    · show dvSnoc St.cstC St.cstDv _ (cdEnd (candSnoc St.cstC _)) = _
      rw [cdEndSnoc, dvSnocGt _ _ _ _ (by omega), take_S_r hk, CertZ8.filterSnoc]
      unfold CertZ6.dNext
      dsimp only
      by_cases htq : (D x).tq (cnt x) = true
      · obtain ⟨m, hm, hmc⟩ := hdevIdx ((hiff _ (lookup_lt_Some hlb)).2 (.inr (.inr htq)))
        rw [if_pos htq, hmc, if_pos (decide_eq_true (List.mem_of_getElem? hm))]
        exact (hpin _ m hm).2
      · have htq' : (D x).tq (cnt x) = false := by simpa using htq
        have hnin := CertZ8.quietNotDev boot fab GF D x (cnt x) lb hD hlb hx htq'
        rw [if_neg htq, hfab, if_neg (by simpa using hnin), Nat.add_zero]
    · show (St.cstC.cdTr ++ [(⟨x, CertZ4.machLbl St.cstC lb⟩ : Estep)]).map Estep.esAg = _
      rw [List.map_append, hags, take_S_r hk, List.map_append]
      rfl

/-! # 3. The final lock co -/

theorem CertZ8.countMapAg (l : List Estep) (a : Nat) :
    (l.filter (fun s => decide (s.esAg = a))).length =
      ((l.map Estep.esAg).filter (fun y => decide (y = a))).length := by
  induction l with
  | nil => rfl
  | cons s l ih => by_cases h : s.esAg = a <;> simp [h, ih]

theorem CertZ8.countMapFst (l : List Geid) (a : Nat) :
    (l.filter (fun e => decide (e.1 = a))).length =
      ((l.map Prod.fst).filter (fun y => decide (y = a))).length := by
  induction l with
  | nil => rfl
  | cons e l ih => by_cases h : e.1 = a <;> simp [h, ih]

/-- The trace's `i`-th step IS the order's `i`-th event, as a graph event of the candidate. -/
theorem CertZ8.ceidOrd (rows : List (List Lbl)) (dev L : List Geid) (c : Cand) (i : Nat)
    (e : Geid) :
    CertZ8.walkOrd rows dev L → c.cdTr.map Estep.esAg = L.map Prod.fst → L[i]? = some e →
    ∃ s, c.cdTr[i]? = some s ∧ s.esAg = e.1 ∧ ceid (candExec c) i = e := by
  intro hord hags hi
  have hlen : c.cdTr.length = L.length := by
    have := congrArg List.length hags; simpa using this
  have hil : i < c.cdTr.length := by rw [hlen]; exact lookup_lt_Some hi
  obtain ⟨s, hs⟩ : ∃ s, c.cdTr[i]? = some s := ⟨_, List.getElem?_eq_getElem hil⟩
  have hag : s.esAg = e.1 := by
    have h1 : (c.cdTr.map Estep.esAg)[i]? = some s.esAg := by rw [List.getElem?_map, hs]; rfl
    rw [hags, List.getElem?_map, hi] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    exact h1.symm
  refine ⟨s, hs, hag, ?_⟩
  rw [ceidCf (candExec c) i s hs]
  obtain ⟨x, a⟩ := e
  show (s.esAg, ((c.cdTr.take i).filter (fun s' => decide (s'.esAg = s.esAg))).length) = (x, a)
  rw [hag, CertZ8.countMapAg, List.map_take, hags, ← List.map_take, ← CertZ8.countMapFst,
    CertZ8.ordCount rows dev L i x a hord hi]

/-- The member's write order on two trace writes IS their trace order. -/
theorem CertZ8.memberWixIff (n : Nat) (c : Cand) (i j : Nat) (si sj : Estep) :
    (∀ s, s ∈ c.cdTr → s.esAg < n) →
    c.cdTr[i]? = some si → c.cdTr[j]? = some sj → lbIsW si.esLb = true → lbIsW sj.esLb = true →
    (gwix (CertZ3.member n c) (ceid (candExec c) i) < gwix (CertZ3.member n c) (ceid (candExec c) j)
      ↔ i < j) := by
  intro hag hi hj hwi hwj
  rw [CertZ3.memberGwix n c _ hag, CertZ3.memberGwix n c _ hag]
  have hmi : ceid (candExec c) i ∈ gwrites (cg (candExec c)) :=
    (gwritesElemOf _ _).2 ⟨cgMem _ i si hi (lbIsWMem _ hwi),
      by unfold gisW; rw [(cgLbl _ i si hi).1]; exact hwi⟩
  have hmj : ceid (candExec c) j ∈ gwrites (cg (candExec c)) :=
    (gwritesElemOf _ _).2 ⟨cgMem _ j sj hj (lbIsWMem _ hwj),
      by unfold gisW; rw [(cgLbl _ j sj hj).1]; exact hwj⟩
  rw [gwixGposLt _ _ _ (cgNodup _) hmi hmj]
  constructor
  · intro hlt
    refine Nat.lt_of_not_le (fun hle => ?_)
    rcases Nat.eq_or_lt_of_le hle with heq | hgt
    · subst heq; omega
    · have := (cgLt (candExec c) j i sj si hj hi (lbIsWMem _ hwj) (lbIsWMem _ hwi) hgt).2.2
      omega
  · intro hlt
    exact (cgLt (candExec c) i j si sj hi hj (lbIsWMem _ hwi) (lbIsWMem _ hwj) hlt).2.2

/-- The order RESPECTS co on the lock bytes `Lb`. -/
def CertZ8.ordCoL (G : Gexec) (L : List Geid) (Lb : Int → Prop) : Prop :=
  ∀ (b : Int) (x y : Geid) (vx vy : BitVec 8) (i j : Nat), Lb b →
    gwritesByte G x b vx → gwritesByte G y b vy → gwix G x < gwix G y →
    L[i]? = some x → L[j]? = some y → i < j

/-- **`CertZ8.lockCoOfOrd` — THE FINAL LOCK CO**: a finished lockstep walk along `L` (its trace's
agents are `L`'s, each hart's labels `lblReidxW` of its whole row) whose order respects co on the
lock bytes gives a member whose lock co is `GF`'s. -/
theorem CertZ8.lockCoOfOrd (G : Gexec) (dev L : List Geid) (c : Cand) (Lb : Int → Prop) :
    gwf G → CertZ8.walkOrd G.gxProg dev L → CertZ8.ordCoL G L Lb →
    c.cdTr.map Estep.esAg = L.map Prod.fst →
    (∀ s, s ∈ c.cdTr → s.esAg < G.gxProg.length) →
    (∀ x, x < G.gxProg.length →
      List.Forall₂ lblReidxW (G.gxProg.getD x []) (CertZ2.hartTr c.cdTr x)) →
    GraphFetchN2.lockCoAgree G (CertZ3.member G.gxProg.length c) Lb := by
  intro hwf hord hco hags hag hrows b x y vx vy hb hx hy
  -- the GF events are in the order
  have hevOf : ∀ (e : Geid) (a : Int) (v : BitVec 8), gwritesByte G e a v →
      ∃ i : Nat, L[i]? = some e := by
    intro e a v he
    obtain ⟨l, -, -, -, hl, -⟩ := he
    unfold gxLbl at hl
    cases hr : G.gxProg[e.1]? with
    | none => rw [hr] at hl; cases hl
    | some row =>
      rw [hr] at hl
      have hlt := lookup_lt_Some hl
      have he1 : e.1 < G.gxProg.length := lookup_lt_Some hr
      have hgd : G.gxProg.getD e.1 [] = row := by
        rw [List.getD_eq_getElem?_getD, hr, Option.getD_some]
      exact List.mem_iff_getElem?.1 ((hord.2.1 e).2 ⟨he1, by rw [hgd]; exact hlt⟩)
  obtain ⟨i, hi⟩ := hevOf x b vx hx
  obtain ⟨j, hj⟩ := hevOf y b vy hy
  obtain ⟨si, hsi, hagi, hci⟩ := CertZ8.ceidOrd _ _ L c i x hord hags hi
  obtain ⟨sj, hsj, hagj, hcj⟩ := CertZ8.ceidOrd _ _ L c j y hord hags hj
  -- the trace's writes at `i`, `j` are writes (writes verbatim)
  have hW : ∀ (k : Nat) (e : Geid) (s : Estep) (a : Int) (v : BitVec 8), c.cdTr[k]? = some s →
      ceid (candExec c) k = e → gwritesByte G e a v → lbIsW s.esLb = true := by
    intro k e s a v hs hce he
    obtain ⟨l, base, vs, jj, hl, hwr, -, -⟩ := he
    have hlbl := (cgLbl (candExec c) k s hs).1
    rw [hce, ← CertZ3.memberLbl _ c e hag, CertZ3.memberLblHart _ c e hag] at hlbl
    unfold gxLbl at hl
    cases hr : G.gxProg[e.1]? with
    | none => rw [hr] at hl; cases hl
    | some row =>
      rw [hr] at hl
      have he1 : e.1 < G.gxProg.length := lookup_lt_Some hr
      have hf := hrows e.1 he1
      rw [List.getD_eq_getElem?_getD, hr, Option.getD_some] at hf
      rcases GraphFetchN2.forall₂Get _ _ _ hf e.2 with ⟨h1, -⟩ | ⟨l0, l1, h1, h2, h12⟩
      · simp only [Option.bind_some] at hl; rw [hl] at h1; cases h1
      · simp only [Option.bind_some] at hl
        rw [hl, Option.some.injEq] at h1
        subst h1
        rw [hlbl, Option.some.injEq] at h2
        subst h2
        rw [lblReidxWIsw _ _ h12]
        exact lbWrIsW _ _ hwr
  have hwi := hW i x si b vx hsi hci hx
  have hwj := hW j y sj b vy hsj hcj hy
  have key := CertZ8.memberWixIff _ c i j si sj hag hsi hsj hwi hwj
  rw [hci, hcj] at key
  rw [key]
  constructor
  · intro hlt
    exact hco b x y vx vy i j hb hx hy hlt hi hj
  · intro hij
    have hxw := gwritesByteGwrites G x b vx hwf hx
    have hyw := gwritesByteGwrites G y b vy hwf hy
    rcases Nat.lt_trichotomy (gwix G x) (gwix G y) with h | h | h
    · exact h
    · have := gwixInj G x y hwf.1 hxw hyw h
      subst this
      have := NoDup_lookup hord.1 hi hj
      omega
    · have := hco b y x vy vx j i hb hy hx h hj hi
      omega

/-! # 4. The scheduler supply from an ORDER supply and a VALUE supply -/

namespace CatLin

/-- **THE ORDER SUPPLY — W10-3c inc. 2's job (from the named lock-discipline premise)**: on every
cyclic class graph, a walk order respecting co on the lock bytes. -/
def orderSupplyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ L, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L ∧
      CertZ8.ordCoL GF.gfGd.gdG L (GraphFetchN2.lockBytes P)

/-- **THE VALUE SUPPLY — W10-4's job (the poison / taint arm discharges it)**: for every fitting
emission datum and walk order, an invariant `Y` holding at the start and the value policy. -/
def valueSupplyCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∀ D : Nat → CertZ7.EmData, CertZ7.emDataOk boot fab GF D →
    ∀ L, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L →
      CertZ8.ordCoL GF.gfGd.gdG L (GraphFetchN2.lockBytes P) →
    ∃ Y : CertZ2.WInv,
      (∀ itvOf fiOf, CertZ.cstOkZW d0 (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf →
        Y (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf (fun _ => 0)) ∧
      CertZ8.valPol d0 GF.gfGd.gdG.gxProg D L GF.gfDev fab Y

/-- **`schedSupplyOfOrdVal`** — the scheduler supply from the order supply and the value supply: the
walk follows `L` (`CertZ8.schedOfOrd`), a finished walk has walked all of `L` (so its agents are
`L`'s and every row is complete), its lock co is `GF`'s (`CertZ8.lockCoOfOrd`). -/
theorem schedSupplyOfOrdVal (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    orderSupplyCZ boot d0 fab im P → valueSupplyCZ boot d0 fab im N P →
    schedSupplyCZ boot d0 fab im N P := by
  intro hord hval GF ad z ss him hc hconf hres hdr hne hch D hD
  obtain ⟨L, hL, hco⟩ := hord GF ad z ss him hc hconf hres hdr hne hch
  obtain ⟨Y, hY0, hpol⟩ := hval GF ad z ss him hc hconf hres hdr hne hch D hD L hL hco
  have hsub : ∀ e, e ∈ GF.gfDev → e ∈ L := by
    intro e he
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨i, k⟩ := e
    obtain ⟨row, hrow, hk⟩ := hconf.2.2.1 n i k hn
    have hi : i < GF.gfGd.gdG.gxProg.length := lookup_lt_Some hrow
    refine (hL.2.1 _).2 ⟨hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, hrow, Option.getD_some]
    exact hk
  refine ⟨CertZ8.xInv L GF.gfDev fab Y, fun itvOf fiOf hok => ⟨⟨0, Nat.zero_le _, fun x => by simp,
    ?_, by simp [wlkStart]⟩, hY0 itvOf fiOf hok⟩,
    CertZ8.schedOfOrd boot d0 fab GF D L Y hD hconf.2.1 hL hsub hpol, ?_⟩
  · show d0 = fab _
    simp only [List.take_zero, List.filter_nil, List.length_nil]
    exact hconf.1.symm
  · intro Sf itvOf fiOf cntF hinv hok hdone
    obtain ⟨hper, hagt, ⟨k, hkL, hcnt, -, hags⟩, -⟩ := hinv
    -- the walk has walked all of `L`
    have hk : k = L.length := by
      refine Nat.le_antisymm hkL (Nat.le_of_not_lt (fun hlt => ?_))
      obtain ⟨⟨x, a⟩, hx⟩ : ∃ e, L[k]? = some e := ⟨L[k], List.getElem?_eq_getElem hlt⟩
      have hev := (hL.2.1 _).1 (List.mem_of_getElem? hx)
      have hca := CertZ8.ordCount _ _ L k x a hL hx
      rw [← hcnt x] at hca
      have := hdone x hev.1
      have := hev.2
      dsimp only at this
      omega
    rw [hk, List.take_length] at hags
    refine CertZ8.lockCoOfOrd _ GF.gfDev L Sf.cstC _ hc.1 hL hco hags hagt (fun x hx => ?_)
    obtain ⟨hle, -, hf⟩ := hper x hx
    rw [List.take_of_length_le (Nat.le_antisymm hle (hdone x hx) ▸ Nat.le_refl _)] at hf
    exact hf

end CatLin

end Weak
