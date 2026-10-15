/-
Weak: **W10 F1 [OWN.94] (N2′), decision (A), step 3b — THE PADDED MEMBER** (`PROGRESS-W10N2p.md`).
Lean-only, no Rocq twin.

The walk with skips (`CertZ26`) ends at a candidate whose hart `x` trace re-indexes `GF`'s row `x` with
the failed acquires filtered out.  The PADDED member puts each trace label back at its `GF` slot
(`CertZ27.kidx`: the slot of the `j`-th kept label) and the placeholder `CertZ24.skipLbl` at every failed
slot (`CertZ27.padRow`); gmo is the candidate member's, renamed by `CertZ27.phi`.

  §1  the row calculus (`padLen`, `padAt`, `padSkip`, `kidxSurj`, `kidxMono`, `kidxAt`);
  §2  **`CertZ27.pad`**, the label facts (`padLblPhi`, `padLblInv`, `phiInj`);
  §3  the graph facts: **`CertZ27.padGwf`**, `padGwrites`, `padGwix`, **`padLogOf`**, **`padGwrowGmo`**,
      **`padRmwLatest`**, **`padLblAgree`** (`CertZ24.lblAgree4` with `GF`).

Spec: FAITHFUL (proof organisation).
-/
import Weak.CertZ26

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The row calculus -/

/-- The slot of the `j`-th kept label of a row. -/
noncomputable def CertZ27.kidx (L : Int → Prop) : List Lbl → Nat → Nat
  | [], _ => 0
  | l :: row, j =>
    if CertZ26.keepB L l = true then
      (match j with
       | 0 => 0
       | j + 1 => CertZ27.kidx L row j + 1)
    else CertZ27.kidx L row j + 1

/-- The padded row: trace labels at kept slots, the placeholder at failed slots. -/
noncomputable def CertZ27.padRow (L : Int → Prop) : List Lbl → List Lbl → List Lbl
  | [], _ => []
  | l :: row, tr =>
    if CertZ26.keepB L l = true then tr.headD CertZ24.skipLbl :: CertZ27.padRow L row tr.tail
    else CertZ24.skipLbl :: CertZ27.padRow L row tr

theorem CertZ27.padLen (L : Int → Prop) :
    ∀ (row tr : List Lbl), (CertZ27.padRow L row tr).length = row.length := by
  intro row
  induction row with
  | nil => intro tr; rfl
  | cons l row ih =>
    intro tr
    unfold CertZ27.padRow
    split <;> simp [ih]

theorem CertZ27.padAt (L : Int → Prop) :
    ∀ (row tr : List Lbl) (j : Nat), j < (row.filter (CertZ26.keepB L)).length → j < tr.length →
      (CertZ27.padRow L row tr)[CertZ27.kidx L row j]? = tr[j]? := by
  intro row
  induction row with
  | nil => intro tr j h; simp at h
  | cons l row ih =>
    intro tr j hj ht
    by_cases hk : CertZ26.keepB L l = true
    · rw [List.filter_cons_of_pos hk] at hj
      unfold CertZ27.padRow CertZ27.kidx
      rw [if_pos hk, if_pos hk]
      cases j with
      | zero =>
        cases tr with
        | nil => simp at ht
        | cons t tr => rfl
      | succ j =>
        cases tr with
        | nil => simp at ht
        | cons t tr =>
          simp only [List.getElem?_cons_succ, List.tail_cons]
          exact ih tr j (by simp at hj; omega) (by simp at ht; omega)
    · rw [List.filter_cons_of_neg hk] at hj
      unfold CertZ27.padRow CertZ27.kidx
      rw [if_neg hk, if_neg hk]
      simp only [List.getElem?_cons_succ]
      exact ih tr j hj ht

theorem CertZ27.padSkip (L : Int → Prop) :
    ∀ (row tr : List Lbl) (i : Nat) (l : Lbl), row[i]? = some l → CertZ26.keepB L l = false →
      (CertZ27.padRow L row tr)[i]? = some CertZ24.skipLbl := by
  intro row
  induction row with
  | nil => intro tr i l h; simp at h
  | cons l0 row ih =>
    intro tr i l hl hk
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
      subst hl
      unfold CertZ27.padRow
      rw [if_neg (by simp [hk])]
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at hl
      unfold CertZ27.padRow
      split
      · simp only [List.getElem?_cons_succ]; exact ih _ i l hl hk
      · simp only [List.getElem?_cons_succ]; exact ih _ i l hl hk

theorem CertZ27.kidxSurj (L : Int → Prop) :
    ∀ (row : List Lbl) (i : Nat) (l : Lbl), row[i]? = some l → CertZ26.keepB L l = true →
      ∃ j, j < (row.filter (CertZ26.keepB L)).length ∧ CertZ27.kidx L row j = i ∧
        (row.filter (CertZ26.keepB L))[j]? = some l := by
  intro row
  induction row with
  | nil => intro i l h; simp at h
  | cons l0 row ih =>
    intro i l hl hk
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
      subst hl
      refine ⟨0, by rw [List.filter_cons_of_pos hk]; simp, ?_, ?_⟩
      · unfold CertZ27.kidx; rw [if_pos hk]
      · rw [List.filter_cons_of_pos hk]; rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at hl
      obtain ⟨j, hj, hkj, hfj⟩ := ih i l hl hk
      by_cases hk0 : CertZ26.keepB L l0 = true
      · refine ⟨j + 1, by rw [List.filter_cons_of_pos hk0]; simp; omega, ?_, ?_⟩
        · unfold CertZ27.kidx; rw [if_pos hk0]; simp [hkj]
        · rw [List.filter_cons_of_pos hk0]; simpa using hfj
      · refine ⟨j, by rw [List.filter_cons_of_neg hk0]; exact hj, ?_, ?_⟩
        · unfold CertZ27.kidx; rw [if_neg hk0]; simp [hkj]
        · rw [List.filter_cons_of_neg hk0]; exact hfj

theorem CertZ27.kidxMono (L : Int → Prop) :
    ∀ (row : List Lbl) (j k : Nat), j < k → k < (row.filter (CertZ26.keepB L)).length →
      CertZ27.kidx L row j < CertZ27.kidx L row k := by
  intro row
  induction row with
  | nil => intro j k _ h; simp at h
  | cons l0 row ih =>
    intro j k hjk hk
    by_cases hk0 : CertZ26.keepB L l0 = true
    · rw [List.filter_cons_of_pos hk0] at hk
      unfold CertZ27.kidx
      rw [if_pos hk0, if_pos hk0]
      cases k with
      | zero => omega
      | succ k =>
        cases j with
        | zero => simp
        | succ j =>
          have := ih j k (by omega) (by simp at hk; omega)
          simp only
          omega
    · rw [List.filter_cons_of_neg hk0] at hk
      unfold CertZ27.kidx
      rw [if_neg hk0, if_neg hk0]
      have := ih j k hjk hk
      omega

theorem CertZ27.kidxAt (L : Int → Prop) :
    ∀ (row : List Lbl) (j : Nat), j < (row.filter (CertZ26.keepB L)).length →
      row[CertZ27.kidx L row j]? = (row.filter (CertZ26.keepB L))[j]? := by
  intro row
  induction row with
  | nil => intro j h; simp at h
  | cons l0 row ih =>
    intro j hj
    by_cases hk0 : CertZ26.keepB L l0 = true
    · rw [List.filter_cons_of_pos hk0] at hj ⊢
      unfold CertZ27.kidx
      rw [if_pos hk0]
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_succ]
        exact ih j (by simp at hj; omega)
    · rw [List.filter_cons_of_neg hk0] at hj ⊢
      unfold CertZ27.kidx
      rw [if_neg hk0]
      simp only [List.getElem?_cons_succ]
      exact ih j hj

/-! # 2. The padded member -/

/-- The renaming of the candidate member's events to their `GF` slots. -/
noncomputable def CertZ27.phi (L : Int → Prop) (rows : List (List Lbl)) (e : Geid) : Geid :=
  (e.1, CertZ27.kidx L (rows.getD e.1 []) e.2)

/-- **THE PADDED MEMBER.** -/
noncomputable def CertZ27.pad (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) :
    Gexec :=
  ⟨c.cdImg,
   (List.range' 0 n).map (fun x => CertZ27.padRow L (rows.getD x []) (CertZ2.hartTr c.cdTr x)),
   (CertZ3.member n c).gxGmo.map (CertZ27.phi L rows)⟩

/-- The walk's end facts the padded member needs. -/
def CertZ27.hyp (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) : Prop :=
  n = rows.length ∧ srvwmoConsistent c ∧ (∀ s, s ∈ c.cdTr → s.esAg < n) ∧
  (∀ x, x < n →
    List.Forall₂ lblReidxW ((rows.getD x []).filter (CertZ26.keepB L)) (CertZ2.hartTr c.cdTr x))

theorem CertZ27.padLbl (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) (e : Geid) :
    gxLbl (CertZ27.pad n rows L c) e =
      if e.1 < n then (CertZ27.padRow L (rows.getD e.1 []) (CertZ2.hartTr c.cdTr e.1))[e.2]?
      else none := by
  unfold gxLbl CertZ27.pad
  dsimp only
  rw [CertZ3.rowLookup]
  split <;> rfl

theorem CertZ27.lenEq (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) (x : Nat) :
    CertZ27.hyp n rows L c → x < n →
    (CertZ2.hartTr c.cdTr x).length = ((rows.getD x []).filter (CertZ26.keepB L)).length :=
  fun h hx => ((h.2.2.2 x hx).length_eq).symm

/-- A member label sits at its renamed slot. -/
theorem CertZ27.padLblPhi (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand)
    (e : Geid) (l : Lbl) :
    CertZ27.hyp n rows L c → gxLbl (CertZ3.member n c) e = some l →
    gxLbl (CertZ27.pad n rows L c) (CertZ27.phi L rows e) = some l := by
  intro h hl
  rw [CertZ3.memberLblHart n c e h.2.2.1] at hl
  have hx : e.1 < n := by
    refine Nat.lt_of_not_le (fun hge => ?_)
    rw [CertZ3.hartTrNil c.cdTr e.1 (fun s hs he => by have := h.2.2.1 s hs; omega)] at hl
    simp at hl
  have hj : e.2 < (CertZ2.hartTr c.cdTr e.1).length := lookup_lt_Some hl
  rw [CertZ27.padLbl, if_pos (show (CertZ27.phi L rows e).1 < n from hx)]
  show (CertZ27.padRow L (rows.getD e.1 []) (CertZ2.hartTr c.cdTr e.1))[
    CertZ27.kidx L (rows.getD e.1 []) e.2]? = some l
  rw [CertZ27.padAt L _ _ e.2 (by rw [← CertZ27.lenEq n rows L c e.1 h hx]; exact hj) hj]
  exact hl

/-- A padded label is a member label at its renamed slot, or the placeholder. -/
theorem CertZ27.padLblInv (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand)
    (e : Geid) (l : Lbl) :
    CertZ27.hyp n rows L c → gxLbl (CertZ27.pad n rows L c) e = some l →
    l = CertZ24.skipLbl ∨
      ∃ j, gxLbl (CertZ3.member n c) (e.1, j) = some l ∧ CertZ27.phi L rows (e.1, j) = e := by
  intro h hl
  rw [CertZ27.padLbl] at hl
  split at hl
  · rename_i hx
    have hi : e.2 < (rows.getD e.1 []).length := by
      have := lookup_lt_Some hl; rwa [CertZ27.padLen] at this
    obtain ⟨l0, hl0⟩ : ∃ l0, (rows.getD e.1 [])[e.2]? = some l0 :=
      ⟨_, List.getElem?_eq_getElem hi⟩
    cases hk : CertZ26.keepB L l0 with
    | false =>
      rw [CertZ27.padSkip L _ _ e.2 l0 hl0 hk, Option.some.injEq] at hl
      exact .inl hl.symm
    | true =>
      obtain ⟨j, hj, hkj, -⟩ := CertZ27.kidxSurj L _ e.2 l0 hl0 hk
      have hjt : j < (CertZ2.hartTr c.cdTr e.1).length := by
        rw [CertZ27.lenEq n rows L c e.1 h hx]; exact hj
      rw [← hkj, CertZ27.padAt L _ _ j hj hjt] at hl
      refine .inr ⟨j, ?_, ?_⟩
      · rw [CertZ3.memberLblHart n c _ h.2.2.1]; exact hl
      · show (e.1, CertZ27.kidx L (rows.getD e.1 []) j) = e
        rw [hkj]
  · cases hl

/-- The renaming is injective on member events. -/
theorem CertZ27.phiInj (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand)
    (e1 e2 : Geid) :
    CertZ27.hyp n rows L c → (gxLbl (CertZ3.member n c) e1).isSome →
    (gxLbl (CertZ3.member n c) e2).isSome →
    CertZ27.phi L rows e1 = CertZ27.phi L rows e2 → e1 = e2 := by
  intro h h1 h2 he
  simp only [CertZ27.phi, Prod.mk.injEq] at he
  obtain ⟨he1, he2⟩ := he
  have hb : ∀ e : Geid, (gxLbl (CertZ3.member n c) e).isSome → e.1 < n ∧
      e.2 < ((rows.getD e.1 []).filter (CertZ26.keepB L)).length := by
    intro e hs
    rw [CertZ3.memberLblHart n c e h.2.2.1] at hs
    have hx : e.1 < n := by
      refine Nat.lt_of_not_le (fun hge => ?_)
      rw [CertZ3.hartTrNil c.cdTr e.1 (fun s hs he => by have := h.2.2.1 s hs; omega)] at hs
      simp at hs
    refine ⟨hx, ?_⟩
    rw [← CertZ27.lenEq n rows L c e.1 h hx]
    exact (lookup_lt_is_Some).1 hs
  obtain ⟨-, hj1⟩ := hb e1 h1
  obtain ⟨-, hj2⟩ := hb e2 h2
  rw [he1] at he2 hj1
  apply Prod.ext he1
  rcases Nat.lt_trichotomy e1.2 e2.2 with hlt | heq | hgt
  · have := CertZ27.kidxMono L _ _ _ hlt hj2; omega
  · exact heq
  · have := CertZ27.kidxMono L _ _ _ hgt hj1; omega

/-! # 3. The graph facts -/

theorem CertZ27.memBound (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) (e : Geid) :
    CertZ27.hyp n rows L c → (gxLbl (CertZ3.member n c) e).isSome →
    e.1 < n ∧ e.2 < ((rows.getD e.1 []).filter (CertZ26.keepB L)).length := by
  intro h hs
  rw [CertZ3.memberLblHart n c e h.2.2.1] at hs
  have hx : e.1 < n := by
    refine Nat.lt_of_not_le (fun hge => ?_)
    rw [CertZ3.hartTrNil c.cdTr e.1 (fun s hs he => by have := h.2.2.1 s hs; omega)] at hs
    simp at hs
  refine ⟨hx, ?_⟩
  rw [← CertZ27.lenEq n rows L c e.1 h hx]
  exact (lookup_lt_is_Some).1 hs

theorem CertZ27.gwixOfLookup (G : Gexec) (i : Nat) (w : Geid) :
    G.gxGmo.Nodup → (gwrites G)[i]? = some w → gwix G w = i + 1 := by
  intro hnd h
  obtain ⟨i', hi', hix⟩ := gwixLookup G w (List.mem_of_getElem? h)
  have hndw : (gwrites G).Nodup := hnd.filter _
  rw [NoDup_lookup hndw h hi']
  exact hix

theorem CertZ27.skipNotMem : lbIsMem CertZ24.skipLbl = false := rfl

/-- **THE PADDED MEMBER IS WELL-FORMED.** -/
theorem CertZ27.padGwf (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) :
    CertZ27.hyp n rows L c → gwf (CertZ27.pad n rows L c) := by
  intro h
  have hwfM := CertZ3.memberGwf n c h.2.1 h.2.2.1
  refine ⟨?_, fun e => ?_, ?_⟩
  · refine NoDup_fmap_2_strong (fun x y hx hy he => ?_) hwfM.1
    obtain ⟨lx, hlx, -⟩ := (hwfM.2.1 x).1 hx
    obtain ⟨ly, hly, -⟩ := (hwfM.2.1 y).1 hy
    exact CertZ27.phiInj n rows L c x y h (by rw [hlx]; rfl) (by rw [hly]; rfl) he
  · constructor
    · intro he
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
      obtain ⟨l, hl, hm⟩ := (hwfM.2.1 e').1 he'
      exact ⟨l, CertZ27.padLblPhi n rows L c e' l h hl, hm⟩
    · rintro ⟨l, hl, hm⟩
      rcases CertZ27.padLblInv n rows L c e l h hl with hsk | ⟨j, hj, hphi⟩
      · rw [hsk] at hm; exact absurd hm (by simp [CertZ27.skipNotMem])
      · rw [← hphi]
        exact List.mem_map_of_mem ((hwfM.2.1 _).2 ⟨l, hj, hm⟩)
  · intro i p k l hp hl
    have hlbl : gxLbl (CertZ27.pad n rows L c) (i, k) = some l := by
      unfold gxLbl; rw [hp]; exact hl
    rcases CertZ27.padLblInv n rows L c (i, k) l h hlbl with hsk | ⟨j, hj, -⟩
    · rw [hsk]; trivial
    · unfold gxLbl at hj
      cases hq : (CertZ3.member n c).gxProg[(i, j).1]? with
      | none => rw [hq] at hj; cases hj
      | some q =>
        rw [hq] at hj
        exact hwfM.2.2 i q j l hq hj

theorem CertZ27.padGwrites (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) :
    CertZ27.hyp n rows L c →
    gwrites (CertZ27.pad n rows L c) = (gwrites (CertZ3.member n c)).map (CertZ27.phi L rows) := by
  intro h
  have hwfM := CertZ3.memberGwf n c h.2.1 h.2.2.1
  unfold gwrites
  show ((CertZ3.member n c).gxGmo.map (CertZ27.phi L rows)).filter _ = _
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e he
  obtain ⟨l, hl, -⟩ := (hwfM.2.1 e).1 he
  show gisW (CertZ27.pad n rows L c) (CertZ27.phi L rows e) = gisW (CertZ3.member n c) e
  unfold gisW
  rw [CertZ27.padLblPhi n rows L c e l h hl, hl]

theorem CertZ27.padGwix (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) (e : Geid) :
    CertZ27.hyp n rows L c → e ∈ gwrites (CertZ3.member n c) →
    gwix (CertZ27.pad n rows L c) (CertZ27.phi L rows e) = gwix (CertZ3.member n c) e := by
  intro h he
  obtain ⟨i, hi, hix⟩ := gwixLookup _ e he
  rw [hix]
  refine CertZ27.gwixOfLookup _ i _ (CertZ27.padGwf n rows L c h).1 ?_
  rw [CertZ27.padGwrites n rows L c h, List.getElem?_map, hi]
  rfl

theorem CertZ27.padGwriteAt (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand)
    (t : Nat) :
    CertZ27.hyp n rows L c →
    gwriteAt (CertZ27.pad n rows L c) t = (gwriteAt (CertZ3.member n c) t).map (CertZ27.phi L rows) := by
  intro h
  cases t with
  | zero => rfl
  | succ t =>
    show (gwrites _)[t]? = Option.map _ ((gwrites _)[t]?)
    rw [CertZ27.padGwrites n rows L c h, List.getElem?_map]

theorem CertZ27.padGmsg (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) (e : Geid)
    (l : Lbl) :
    CertZ27.hyp n rows L c → gxLbl (CertZ3.member n c) e = some l →
    WeakRvwmoKillArms.gmsg (CertZ27.pad n rows L c) (CertZ27.phi L rows e) =
      WeakRvwmoKillArms.gmsg (CertZ3.member n c) e := by
  intro h hl
  unfold WeakRvwmoKillArms.gmsg
  rw [CertZ27.padLblPhi n rows L c e l h hl, hl]
  rfl

/-- **THE PADDED MEMBER'S LOG IS THE MEMBER'S.** -/
theorem CertZ27.padLogOf (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand)
    (log : List Wmsg) :
    CertZ27.hyp n rows L c → logOf (CertZ3.member n c) log → logOf (CertZ27.pad n rows L c) log := by
  intro h hlog p m
  have hwfM := CertZ3.memberGwf n c h.2.1 h.2.2.1
  constructor
  · intro hm
    obtain ⟨w, hw, hgm⟩ := (hlog p m).1 hm
    obtain ⟨l, -, -, hl, -, -⟩ := gmsgInv _ w m hgm
    exact ⟨CertZ27.phi L rows w, by rw [CertZ27.padGwriteAt n rows L c _ h, hw]; rfl,
      by rw [CertZ27.padGmsg n rows L c w l h hl]; exact hgm⟩
  · rintro ⟨w', hw', hgm'⟩
    rw [CertZ27.padGwriteAt n rows L c _ h] at hw'
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hw'
    obtain ⟨hwm, -⟩ := gwriteAtInv _ _ w hwfM.1 hw
    obtain ⟨hg, hisw⟩ := (gwritesElemOf _ w).1 hwm
    obtain ⟨l, hl, -⟩ := (hwfM.2.1 w).1 hg
    rw [CertZ27.padGmsg n rows L c w l h hl] at hgm'
    exact (hlog p m).2 ⟨w, hw, hgm'⟩

theorem CertZ27.padWInv (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) (e : Geid) :
    CertZ27.hyp n rows L c → glblIs (CertZ27.pad n rows L c) e lbIsW →
    ∃ j l, gxLbl (CertZ3.member n c) (e.1, j) = some l ∧ lbIsW l = true ∧
      CertZ27.phi L rows (e.1, j) = e ∧ (e.1, j) ∈ gwrites (CertZ3.member n c) := by
  rintro h ⟨l, hl, hW⟩
  have hwfM := CertZ3.memberGwf n c h.2.1 h.2.2.1
  rcases CertZ27.padLblInv n rows L c e l h hl with hsk | ⟨j, hj, hphi⟩
  · rw [hsk] at hW; exact absurd hW (by simp [CertZ24.skipNoW])
  · refine ⟨j, l, hj, hW, hphi, (gwritesElemOf _ _).2 ⟨(hwfM.2.1 _).2 ⟨l, hj, ?_⟩, ?_⟩⟩
    · simp [lbIsMem, hW]
    · unfold gisW; rw [hj]; exact hW

/-- **EACH HART'S WRITES IN PROGRAM ORDER**, padded. -/
theorem CertZ27.padGwrowGmo (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand) :
    CertZ27.hyp n rows L c → gwrowGmo (CertZ3.member n c) → gwrowGmo (CertZ27.pad n rows L c) := by
  intro h hrow x j k hjk hj hk
  obtain ⟨j', lj, hlj, hWj, hpj, hgj⟩ := CertZ27.padWInv n rows L c (x, j) h hj
  obtain ⟨k', lk, hlk, hWk, hpk, hgk⟩ := CertZ27.padWInv n rows L c (x, k) h hk
  have hlj' : gxLbl (CertZ3.member n c) (x, j') = some lj := hlj
  have hlk' : gxLbl (CertZ3.member n c) (x, k') = some lk := hlk
  have hbj : j' < ((rows.getD x []).filter (CertZ26.keepB L)).length :=
    (CertZ27.memBound n rows L c (x, j') h (by rw [hlj']; rfl)).2
  have hbk : k' < ((rows.getD x []).filter (CertZ26.keepB L)).length :=
    (CertZ27.memBound n rows L c (x, k') h (by rw [hlk']; rfl)).2
  have hpj2 : CertZ27.kidx L (rows.getD x []) j' = j := congrArg Prod.snd hpj
  have hpk2 : CertZ27.kidx L (rows.getD x []) k' = k := congrArg Prod.snd hpk
  have hjk' : j' < k' := by
    refine Nat.lt_of_not_le (fun hle => ?_)
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · subst heq; omega
    · have := CertZ27.kidxMono L _ _ _ hlt hbj; omega
  have key := hrow x j' k' hjk' ⟨lj, hlj', hWj⟩ ⟨lk, hlk', hWk⟩
  have ej : (x, j) = CertZ27.phi L rows (x, j') := hpj.symm
  have ek : (x, k) = CertZ27.phi L rows (x, k') := hpk.symm
  rw [ej, ek, CertZ27.padGwix n rows L c (x, j') h hgj, CertZ27.padGwix n rows L c (x, k') h hgk]
  exact key

/-- **RMW ATOMICITY**, padded. -/
theorem CertZ27.padRmwLatest (n : Nat) (rows : List (List Lbl)) (L : Int → Prop) (c : Cand)
    (log : List Wmsg) :
    CertZ27.hyp n rows L c → CertZ18.rmwLatest (CertZ3.member n c) log →
    CertZ18.rmwLatest (CertZ27.pad n rows L c) log := by
  intro h hlat e a t v hW hrd
  obtain ⟨j, l, hl, hWl, hphi, hg⟩ := CertZ27.padWInv n rows L c e h hW
  have hrd' : greadsByte (CertZ3.member n c) (e.1, j) a t v := by
    obtain ⟨l0, base, ts, vs, jj, hl0, hr, ht, hv, ha⟩ := hrd
    rw [← hphi, CertZ27.padLblPhi n rows L c _ l h hl, Option.some.injEq] at hl0
    subst hl0
    exact ⟨l, base, ts, vs, jj, hl, hr, ht, hv, ha⟩
  have := hlat (e.1, j) a t v ⟨l, hl, hWl⟩ hrd'
  rw [← hphi, CertZ27.padGwix n rows L c _ h hg]
  exact this

/-- **THE PADDED LABEL AGREEMENT WITH `GF`.** -/
theorem CertZ27.padLblAgree (G : Gexec) (L : Int → Prop) (c : Cand) :
    CertZ27.hyp G.gxProg.length G.gxProg L c →
    CertZ24.lblAgree4 G (CertZ27.pad G.gxProg.length G.gxProg L c) (fun t => t) L := by
  intro h e
  by_cases hx : e.1 < G.gxProg.length
  · have hrow : G.gxProg[e.1]? = some (G.gxProg.getD e.1 []) := CertZ7.getDSome _ e.1 hx
    have hG : gxLbl G e = (G.gxProg.getD e.1 [])[e.2]? := by
      unfold gxLbl; rw [hrow]; rfl
    have hP : gxLbl (CertZ27.pad G.gxProg.length G.gxProg L c) e =
        (CertZ27.padRow L (G.gxProg.getD e.1 []) (CertZ2.hartTr c.cdTr e.1))[e.2]? := by
      rw [CertZ27.padLbl, if_pos hx]
    rw [hG, hP]
    cases hl : (G.gxProg.getD e.1 [])[e.2]? with
    | none =>
      left
      refine ⟨rfl, List.getElem?_eq_none ?_⟩
      rw [CertZ27.padLen]
      exact Nat.le_of_not_lt (fun hlt => by rw [List.getElem?_eq_getElem hlt] at hl; cases hl)
    | some l =>
      right
      cases hk : CertZ26.keepB L l with
      | false =>
        refine ⟨l, CertZ24.skipLbl, rfl, CertZ27.padSkip L _ _ e.2 l hl hk, .inr ⟨?_, rfl⟩⟩
        have : ¬ ¬ CertZ24.lblFail L l := by
          rw [← CertZ26.keepBTrue, hk]; simp
        exact Classical.not_not.1 this
      | true =>
        obtain ⟨j, hj, hkj, hfj⟩ := CertZ27.kidxSurj L _ e.2 l hl hk
        have hjt : j < (CertZ2.hartTr c.cdTr e.1).length := by
          rw [CertZ27.lenEq _ _ L c e.1 h hx]; exact hj
        rcases GraphFetchN2.forall₂Get _ _ _ (h.2.2.2 e.1 hx) j with ⟨h1, -⟩ | ⟨l0, l', h1, h2, h12⟩
        · rw [hfj] at h1; cases h1
        · rw [hfj, Option.some.injEq] at h1
          subst h1
          refine ⟨l, l', rfl, ?_, .inl ⟨(CertZ26.keepBTrue L l).1 hk, by rw [lblRenId]; exact h12⟩⟩
          rw [← hkj, CertZ27.padAt L _ _ j hj hjt]
          exact h2
  · left
    refine ⟨?_, ?_⟩
    · unfold gxLbl
      rw [List.getElem?_eq_none (by omega)]
      rfl
    · rw [CertZ27.padLbl, if_neg hx]

end Weak
