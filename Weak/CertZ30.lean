/-
Weak: **W10-3c [OWN.94] (N2′), decision (A), step 4b — the PADDED member's lock co from the order**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

At the end of the walk with skips the trace's agents are the KEPT events of `L` (`CertZ29.prefInv4`).
A kept `GF` event at position `i0` of `L` is the trace's step at position `|(L.take i0).filter keepEv|`,
and the padded member renames that step back to the `GF` event (`CertZ30.ceidKeep`, `CertZ27.kidx`).
So the padded member's write order on kept `GF` writes IS their order in `L` (`CertZ30.memberIffOrd4`),
and the order's successful-protocol co is the padded member's (**`CertZ30.lockCoOfOrd4`**).

Spec: FAITHFUL (proof organisation).
-/
import Weak.CertZ29

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. Row and list lemmas -/

theorem CertZ30.kidxRank (Lb : Int → Prop) :
    ∀ (row : List Lbl) (a : Nat) (l : Lbl), row[a]? = some l → CertZ26.keepB Lb l = true →
      CertZ27.kidx Lb row ((row.take a).filter (CertZ26.keepB Lb)).length = a := by
  intro row
  induction row with
  | nil => intro a l h; simp at h
  | cons l0 row ih =>
    intro a l hl hk
    cases a with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
      subst hl
      simp only [List.take_zero, List.filter_nil, List.length_nil]
      unfold CertZ27.kidx
      rw [if_pos hk]
    | succ a =>
      simp only [List.getElem?_cons_succ] at hl
      have ih' := ih a l hl hk
      rw [List.take_succ_cons]
      by_cases hk0 : CertZ26.keepB Lb l0 = true
      · rw [List.filter_cons_of_pos hk0, List.length_cons]
        unfold CertZ27.kidx
        rw [if_pos hk0]
        simp only
        rw [ih']
      · rw [List.filter_cons_of_neg hk0]
        unfold CertZ27.kidx
        rw [if_neg hk0, ih']

theorem CertZ30.rangeKeep (rows : List (List Lbl)) (Lb : Int → Prop) (x : Nat) :
    ∀ a, a ≤ (rows.getD x []).length →
      ((List.range a).filter (fun b => CertZ29.keepEv rows Lb (x, b))).length =
        (((rows.getD x []).take a).filter (CertZ26.keepB Lb)).length := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    obtain ⟨l, hl⟩ : ∃ l, (rows.getD x [])[a]? = some l := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [List.range_succ, List.filter_append, take_S_r hl, List.filter_append, List.length_append,
      List.length_append, ih (by omega)]
    congr 1
    simp only [List.filter_cons, List.filter_nil, CertZ29.keepEvAt rows Lb x a l hl]
    split <;> rfl

theorem CertZ30.filterTakeLeft {α : Type} (p : α → Bool) (L : List α) (i0 : Nat) :
    (L.filter p).take ((L.take i0).filter p).length = (L.take i0).filter p := by
  have hsplit : L.filter p = (L.take i0).filter p ++ (L.drop i0).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  rw [hsplit, List.take_left]

theorem CertZ30.filterAt {α : Type} (p : α → Bool) (L : List α) (i0 : Nat) (e : α) :
    L[i0]? = some e → p e = true → (L.filter p)[((L.take i0).filter p).length]? = some e := by
  intro hi hp
  have hlt := lookup_lt_Some hi
  have hd : L.drop i0 = e :: L.drop (i0 + 1) := by
    rw [List.drop_eq_getElem_cons hlt]
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hi
    rw [hi]
  have hsplit : L.filter p = (L.take i0).filter p ++ (L.drop i0).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  rw [hsplit, hd, List.filter_cons_of_pos hp, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self]
  rfl

theorem CertZ30.filterTakeMono {α : Type} (p : α → Bool) (L : List α) (m m' : Nat) :
    m ≤ m' → ((L.take m).filter p).length ≤ ((L.take m').filter p).length := by
  intro h
  have : L.take m = (L.take m').take m := by rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact ((List.take_sublist _ _).filter p).length_le

theorem CertZ30.filterTakeLt {α : Type} (p : α → Bool) (L : List α) (i0 j0 : Nat) (e : α) :
    i0 < j0 → L[i0]? = some e → p e = true →
    ((L.take i0).filter p).length < ((L.take j0).filter p).length := by
  intro hlt hi hp
  have h1 := CertZ30.filterTakeMono p L (i0 + 1) j0 hlt
  rw [take_S_r hi, List.filter_append, List.filter_cons_of_pos hp, List.length_append] at h1
  simp at h1
  omega

/-- The kept events of hart `x` before position `i0` (whose event is `(x, a)`) are its kept slots
below `a`. -/
theorem CertZ30.keptCount (rows : List (List Lbl)) (Lb : Int → Prop) (dev L : List Geid)
    (i0 x a : Nat) :
    CertZ8.walkOrd rows dev L → L[i0]? = some (x, a) →
    (((L.take i0).filter (CertZ29.keepEv rows Lb)).filter (fun e => decide (e.1 = x))).length =
      (((rows.getD x []).take a).filter (CertZ26.keepB Lb)).length := by
  intro hord hi
  have hord' := hord
  obtain ⟨hnd, hmem, hpo, -⟩ := hord'
  have hev := (hmem _).1 (List.mem_of_getElem? hi)
  have hinj : Function.Injective (fun b : Nat => ((x, b) : Geid)) := fun _ _ h => by injection h
  rw [CertZ8.lenOfMem _ (((List.range a).filter (fun b => CertZ29.keepEv rows Lb (x, b))).map
      (fun b => (x, b)))
    (((hnd.sublist (List.take_sublist _ _)).filter _).filter _)
    (NoDup_fmap_2 hinj (List.nodup_range.filter _)) (fun e => ?_),
    List.length_map, CertZ30.rangeKeep rows Lb x a (Nat.le_of_lt hev.2)]
  rw [List.mem_filter, List.mem_filter, CertZ8.memTakeIff, List.mem_map]
  constructor
  · rintro ⟨⟨⟨j, hji, hj⟩, hk⟩, hx⟩
    obtain ⟨y, b⟩ := e
    have hy : y = x := of_decide_eq_true hx
    subst hy
    refine ⟨b, List.mem_filter.2 ⟨List.mem_range.2 ?_, hk⟩, rfl⟩
    rcases Nat.lt_trichotomy b a with h | h | h
    · exact h
    · subst h
      have := NoDup_lookup hnd hj hi
      omega
    · have := hpo i0 j y a b hi hj h
      omega
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨hb, hk⟩ := List.mem_filter.1 hb
    have hb' := List.mem_range.1 hb
    have hev' : CertZ8.evsOf rows (x, b) := ⟨hev.1, by have := hev.2; dsimp only at this ⊢; omega⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ((hmem _).2 hev')
    exact ⟨⟨⟨j, hpo j i0 x b a hj hi hb', hj⟩, hk⟩, by simp⟩

/-! # 2. The trace step of a kept event -/

/-- **A KEPT EVENT IS ITS TRACE STEP, RENAMED.** -/
theorem CertZ30.ceidKeep (rows : List (List Lbl)) (Lb : Int → Prop) (dev L : List Geid) (c : Cand)
    (i0 : Nat) (e : Geid) :
    CertZ8.walkOrd rows dev L →
    c.cdTr.map Estep.esAg = (L.filter (CertZ29.keepEv rows Lb)).map Prod.fst →
    L[i0]? = some e → CertZ29.keepEv rows Lb e = true →
    ∃ s, c.cdTr[((L.take i0).filter (CertZ29.keepEv rows Lb)).length]? = some s ∧
      s.esAg = e.1 ∧
      ceid (candExec c) ((L.take i0).filter (CertZ29.keepEv rows Lb)).length =
        (e.1, (((rows.getD e.1 []).take e.2).filter (CertZ26.keepB Lb)).length) := by
  intro hord hags hi hk
  generalize hidx : ((L.take i0).filter (CertZ29.keepEv rows Lb)).length = i
  have hfe := CertZ30.filterAt _ L i0 e hi hk
  rw [hidx] at hfe
  have hag1 : (c.cdTr.map Estep.esAg)[i]? = some e.1 := by
    rw [hags, List.getElem?_map, hfe]; rfl
  rw [List.getElem?_map] at hag1
  cases hs : c.cdTr[i]? with
  | none => rw [hs] at hag1; cases hag1
  | some s =>
    rw [hs] at hag1
    simp only [Option.map_some, Option.some.injEq] at hag1
    refine ⟨s, rfl, hag1, ?_⟩
    rw [ceidCf (candExec c) i s hs]
    obtain ⟨x, a⟩ := e
    show (s.esAg, ((c.cdTr.take i).filter (fun s' => decide (s'.esAg = s.esAg))).length) = _
    rw [hag1, CertZ8.countMapAg, List.map_take, hags, ← List.map_take, ← CertZ8.countMapFst, ← hidx,
      CertZ30.filterTakeLeft, CertZ30.keptCount rows Lb dev L i0 x a hord hi]

/-! # 3. The padded member's write order and lock co -/

theorem CertZ30.evOfWr (G : Gexec) (dev L : List Geid) (e : Geid) (a : Int) (v : BitVec 8) :
    CertZ8.walkOrd G.gxProg dev L → gwritesByte G e a v → ∃ i : Nat, L[i]? = some e := by
  intro hord he
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

/-- The trace step of a kept `GF` write writes, and the padded member's write index of the `GF` event
is the candidate member's of the step. -/
theorem CertZ30.keptStep (G : Gexec) (dev L : List Geid) (c : Cand) (Lb : Int → Prop) (i0 : Nat)
    (e : Geid) (a : Int) (v : BitVec 8) :
    CertZ8.walkOrd G.gxProg dev L →
    c.cdTr.map Estep.esAg = (L.filter (CertZ29.keepEv G.gxProg Lb)).map Prod.fst →
    CertZ27.hyp G.gxProg.length G.gxProg Lb c →
    L[i0]? = some e → CertZ29.keepEv G.gxProg Lb e = true → gwritesByte G e a v →
    ∃ s, c.cdTr[((L.take i0).filter (CertZ29.keepEv G.gxProg Lb)).length]? = some s ∧
      lbIsW s.esLb = true ∧
      gwix (CertZ27.pad G.gxProg.length G.gxProg Lb c) e =
        gwix (CertZ3.member G.gxProg.length c)
          (ceid (candExec c) ((L.take i0).filter (CertZ29.keepEv G.gxProg Lb)).length) := by
  intro hord hags hyp hi hk hw
  obtain ⟨s, hs, hag, hce⟩ := CertZ30.ceidKeep _ Lb dev L c i0 e hord hags hi hk
  generalize hidx : ((L.take i0).filter (CertZ29.keepEv G.gxProg Lb)).length = i at hs hce ⊢
  have hev := (hord.2.1 e).1 (List.mem_of_getElem? hi)
  obtain ⟨l0, hl0⟩ : ∃ l0, (G.gxProg.getD e.1 [])[e.2]? = some l0 :=
    ⟨_, List.getElem?_eq_getElem hev.2⟩
  have hk0 : CertZ26.keepB Lb l0 = true := by
    rw [← CertZ29.keepEvAt _ Lb e.1 e.2 l0 hl0]; exact hk
  -- the step's label is the hart's trace label at the rank, re-indexing `GF`'s
  have hh : (CertZ2.hartTr c.cdTr e.1)[
      (((G.gxProg.getD e.1 []).take e.2).filter (CertZ26.keepB Lb)).length]? = some s.esLb := by
    have h1 := (cgLbl (candExec c) i s hs).1
    rw [hce, CertZ3.cgLblHart] at h1
    exact h1
  have hrank := CertZ30.kidxRank Lb _ e.2 l0 hl0 hk0
  have hbnd : (((G.gxProg.getD e.1 []).take e.2).filter (CertZ26.keepB Lb)).length <
      ((G.gxProg.getD e.1 []).filter (CertZ26.keepB Lb)).length := by
    rw [← CertZ27.lenEq _ _ Lb c e.1 hyp hev.1]; exact lookup_lt_Some hh
  have hat := CertZ27.kidxAt Lb _ _ hbnd
  rw [hrank, hl0] at hat
  rcases GraphFetchN2.forall₂Get _ _ _ (hyp.2.2.2 e.1 hev.1)
      (((G.gxProg.getD e.1 []).take e.2).filter (CertZ26.keepB Lb)).length with
    ⟨h1, -⟩ | ⟨l1, l2, h1, h2, h12⟩
  · rw [← hat] at h1; cases h1
  · rw [← hat, Option.some.injEq] at h1
    subst h1
    rw [hh, Option.some.injEq] at h2
    subst h2
    have hlG : gxLbl G e = some l0 := by
      unfold gxLbl; rw [CertZ7.getDSome _ e.1 hev.1]; exact hl0
    have hW0 : lbIsW l0 = true := by
      obtain ⟨l, base, vs, j, hl, hwr, -, -⟩ := hw
      rw [hlG, Option.some.injEq] at hl
      subst hl
      exact lbWrIsW _ _ hwr
    have hW : lbIsW s.esLb = true := by rw [lblReidxWIsw _ _ h12]; exact hW0
    refine ⟨s, hs, hW, ?_⟩
    have hmem : ceid (candExec c) i ∈ gwrites (CertZ3.member G.gxProg.length c) := by
      rw [CertZ3.memberGwrites _ c hyp.2.2.1]
      exact (gwritesElemOf _ _).2 ⟨cgMem _ i s hs (lbIsWMem _ hW),
        by unfold gisW; rw [(cgLbl _ i s hs).1]; exact hW⟩
    have hphi : CertZ27.phi Lb G.gxProg (ceid (candExec c) i) = e := by
      rw [hce]
      show (e.1, CertZ27.kidx Lb (G.gxProg.getD e.1 [])
        (((G.gxProg.getD e.1 []).take e.2).filter (CertZ26.keepB Lb)).length) = e
      rw [hrank]
    rw [← hphi, CertZ27.padGwix _ _ _ _ _ hyp hmem]

/-- **THE PADDED MEMBER'S WRITE ORDER ON KEPT `GF` WRITES IS THEIR ORDER IN `L`.** -/
theorem CertZ30.memberIffOrd4 (G : Gexec) (dev L : List Geid) (c : Cand) (Lb : Int → Prop)
    (x y : Geid) (a a' : Int) (vx vy : BitVec 8) :
    CertZ8.walkOrd G.gxProg dev L →
    c.cdTr.map Estep.esAg = (L.filter (CertZ29.keepEv G.gxProg Lb)).map Prod.fst →
    CertZ27.hyp G.gxProg.length G.gxProg Lb c →
    gwritesByte G x a vx → gwritesByte G y a' vy →
    CertZ29.keepEv G.gxProg Lb x = true → CertZ29.keepEv G.gxProg Lb y = true →
    ∃ i j : Nat, L[i]? = some x ∧ L[j]? = some y ∧
      (gwix (CertZ27.pad G.gxProg.length G.gxProg Lb c) x <
        gwix (CertZ27.pad G.gxProg.length G.gxProg Lb c) y ↔ i < j) := by
  intro hord hags hyp hx hy hkx hky
  obtain ⟨i0, hi0⟩ := CertZ30.evOfWr G dev L x a vx hord hx
  obtain ⟨j0, hj0⟩ := CertZ30.evOfWr G dev L y a' vy hord hy
  obtain ⟨si, hsi, hWi, hgi⟩ := CertZ30.keptStep G dev L c Lb i0 x a vx hord hags hyp hi0 hkx hx
  obtain ⟨sj, hsj, hWj, hgj⟩ := CertZ30.keptStep G dev L c Lb j0 y a' vy hord hags hyp hj0 hky hy
  refine ⟨i0, j0, hi0, hj0, ?_⟩
  rw [hgi, hgj, CertZ8.memberWixIff _ c _ _ si sj hyp.2.2.1 hsi hsj hWi hWj]
  constructor
  · intro hlt
    refine Nat.lt_of_not_le (fun hle => ?_)
    rcases Nat.eq_or_lt_of_le hle with heq | hgt
    · subst heq; omega
    · have := CertZ30.filterTakeLt _ L j0 i0 y hgt hj0 hky; omega
  · intro hlt
    exact CertZ30.filterTakeLt _ L i0 j0 x hlt hi0 hkx

/-- **THE PADDED MEMBER'S SUCCESSFUL-PROTOCOL LOCK CO** from the order. -/
theorem CertZ30.lockCoOfOrd4 (G : Gexec) (dev L : List Geid) (c : Cand) (Lb : Int → Prop) :
    gwf G → CertZ8.walkOrd G.gxProg dev L → CertZ23.ordCoSP G L Lb →
    c.cdTr.map Estep.esAg = (L.filter (CertZ29.keepEv G.gxProg Lb)).map Prod.fst →
    CertZ27.hyp G.gxProg.length G.gxProg Lb c →
    (∀ b e v, Lb b → gwritesByte G e b v → CertZ18.sp G b e →
      CertZ29.keepEv G.gxProg Lb e = true) →
    CertZ18.lockCoSP G (CertZ27.pad G.gxProg.length G.gxProg Lb c) Lb := by
  intro hwf hord hco hags hyp hkeep b x y vx vy hb hx hy hsx hsy
  obtain ⟨i, j, hi, hj, key⟩ := CertZ30.memberIffOrd4 G dev L c Lb x y b b vx vy hord hags hyp hx hy
    (hkeep b x vx hb hx hsx) (hkeep b y vy hb hy hsy)
  rw [key]
  constructor
  · intro hlt
    exact hco b x y vx vy i j hb hx hy hsx hsy hlt hi hj
  · intro hij
    have hxw := gwritesByteGwrites G x b vx hwf hx
    have hyw := gwritesByteGwrites G y b vy hwf hy
    rcases Nat.lt_trichotomy (gwix G x) (gwix G y) with h | h | h
    · exact h
    · have := gwixInj G x y hwf.1 hxw hyw h
      subst this
      have := NoDup_lookup hord.1 hi hj
      omega
    · have := hco b y x vy vx j i hb hy hx hsy hsx h hj hi
      omega

/-- A successful protocol write is kept (`NF2c`: a non-plain write touches one lock byte). -/
theorem CertZ30.keepOfSp (GF : Gfexec) (Lb : Int → Prop) :
    CertZ23.lockDisc3 GF Lb →
    ∀ b e v, Lb b → gwritesByte GF.gfGd.gdG e b v → CertZ18.sp GF.gfGd.gdG b e →
      CertZ29.keepEv GF.gfGd.gdG.gxProg Lb e = true := by
  intro hld b e v hb hw hsp
  obtain ⟨-, -, hNF2c, -⟩ := hld
  have hev : e.1 < GF.gfGd.gdG.gxProg.length ∧
      ∃ l, (GF.gfGd.gdG.gxProg.getD e.1 [])[e.2]? = some l ∧ gxLbl GF.gfGd.gdG e = some l := by
    obtain ⟨l, -, -, -, hl, -⟩ := hw
    unfold gxLbl at hl
    cases hr : GF.gfGd.gdG.gxProg[e.1]? with
    | none => rw [hr] at hl; cases hl
    | some row =>
      rw [hr] at hl
      have he1 : e.1 < GF.gfGd.gdG.gxProg.length := lookup_lt_Some hr
      refine ⟨he1, l, ?_, ?_⟩
      · rw [List.getD_eq_getElem?_getD, hr, Option.getD_some]; exact hl
      · unfold gxLbl; rw [hr]; exact hl
  obtain ⟨-, l, hl, hlG⟩ := hev
  rw [CertZ29.keepEvAt _ Lb e.1 e.2 l hl, CertZ26.keepBTrue]
  intro hf
  obtain ⟨b', hb', hfa⟩ := (CertZ24.failIff _ Lb e l hlG).1 hf
  obtain ⟨⟨v', hw', -⟩, -⟩ := id hfa
  have hbb : b' = b := hNF2c b' b e v' v hb' hb hw' hw hsp.1
  subst hbb
  exact hsp.2 hfa

end Weak
