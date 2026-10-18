/-
Weak: **(c) [OWN.100], increment 5c-ii — the twin walk (every slot realized; a failed acquire SILENTLY)
and the cert supply from it** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

The twin of CertZ26 (walk) and CertZ28 (cert supply), with NO skips and NO padding: every row slot is
realized by an appended twin step; the policy relates the graph's label `lb` to the appended
`(lb', o)` by `SilWalk.relW` (a re-index, silent exactly at a failed acquire).

  §1  `SilWalk.relW`, `SilWalk.hartPr`, **`SilWalk.walkPol`**, **`SilWalk.walkRun`** (the free walk);
  §2  the realized member's rows (`SilWalk.projMapIdx`, `SilWalk.hartTrProj`, `SilWalk.projQ`),
      `SilWalk.relSOfW`, `SilWalk.forall₂Get`, **`SilWalk.lblAgreeOfRows`**;
  §3  **`CatLin.SilWalk.walkSupplyS`** and **`CatLin.SilWalk.certSupplyOfWalkS`** (→ `SilKill.certSupplyS`).

Spec: FAITHFUL (proof organisation).
-/
import Weak.SilWalk

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The walk -/

/-- The graph's label `lb` and the appended `(lb', o)`: a re-index, silent exactly at a failed acquire. -/
def SilWalk.relW (L : Int → Prop) (lb : Lbl) (q : Lbl × Option Nat) : Prop :=
  lblReidxW lb q.1 ∧ ((¬ CertZ24.lblFail L lb ∧ q.2 = none) ∨ (CertZ24.lblFail L lb ∧ q.2 ≠ none))

/-- Hart `x`'s appended labels with their silent marks. -/
def SilWalk.hartPr (pr : List (Estep × Option Nat)) (x : Nat) : List (Lbl × Option Nat) :=
  (pr.filter (fun p => decide (p.1.esAg = x))).map (fun p => (p.1.esLb, p.2))

theorem SilWalk.hartPrCons (p : Estep × Option Nat) (pr : List (Estep × Option Nat)) (x : Nat) :
    SilWalk.hartPr (p :: pr) x =
      if p.1.esAg = x then (p.1.esLb, p.2) :: SilWalk.hartPr pr x else SilWalk.hartPr pr x := by
  by_cases h : p.1.esAg = x <;> simp [SilWalk.hartPr, h]

/-- **THE TWIN WALK POLICY**: whenever some hart has slots left, the policy picks one, its next row
label `lb`, the appended `(lb', o)` (`relW`), discharges the step and keeps `Inv`. -/
def SilWalk.walkPol (d0 : Efab) (rows : List (List Lbl)) (L : Int → Prop)
    (Inv : SilWalk.St → (Nat → Nat) → Prop) : Prop :=
  ∀ (S : SilWalk.St) (cnt : Nat → Nat), SilWalk.ok d0 S → Inv S cnt →
    (∃ x, x < rows.length ∧ cnt x < (rows.getD x []).length) →
    ∃ (x : Nat) (lb : Lbl), x < rows.length ∧ (rows.getD x [])[cnt x]? = some lb ∧
      ∃ (lb' : Lbl) (o : Option Nat) (pC pa : Pexv6) (da : Efab) (ls : List Wlabel) (pC' : Pexv6)
        (d' : Efab) (w' : Wstate),
        (S.pst S.c.tr.length)[x]? = some pC ∧ SilWalk.relW L lb (lb', o) ∧
        SilWalk.stepOk S x lb' o pC pa da ls pC' d' w' ∧
        Inv (SilWalk.snoc S x lb' o pC' d' w') (CertZ2.bump cnt x)

/-- **THE FREE TWIN WALK.** -/
theorem SilWalk.walkRun (d0 : Efab) (rows : List (List Lbl)) (L : Int → Prop)
    (Inv : SilWalk.St → (Nat → Nat) → Prop) (hpol : SilWalk.walkPol d0 rows L Inv) :
    ∀ (m : Nat) (S : SilWalk.St) (cnt : Nat → Nat),
      CertZ2.rem rows.length (fun x => (rows.getD x []).length) cnt ≤ m →
      SilWalk.ok d0 S → Inv S cnt →
      ∃ (Sf : SilWalk.St) (cntF : Nat → Nat) (pr : List (Estep × Option Nat)),
        SilWalk.ok d0 Sf ∧ Inv Sf cntF ∧
        (∀ x, x < rows.length → (rows.getD x []).length ≤ cntF x) ∧
        (∀ x, cnt x ≤ cntF x) ∧
        Sf.c.tr = S.c.tr ++ pr.map Prod.fst ∧ Sf.c.sil = S.c.sil ++ pr.map Prod.snd ∧
        (∀ x, List.Forall₂ (SilWalk.relW L)
          (((rows.getD x []).drop (cnt x)).take (cntF x - cnt x)) (SilWalk.hartPr pr x)) ∧
        (∀ p, p ∈ pr → p.1.esAg < rows.length) ∧
        Sf.c.img = S.c.img ∧ Sf.pst 0 = S.pst 0 := by
  intro m
  induction m with
  | zero =>
    intro S cnt hm hok hinv
    refine ⟨S, cnt, [], hok, hinv, ?_, fun _ => Nat.le_refl _, by simp, by simp, ?_,
      fun p h => by simp at h, rfl, rfl⟩
    · intro x hx
      refine Nat.le_of_not_lt (fun hlt => ?_)
      have := CertZ2.remStep (fun x => (rows.getD x []).length) cnt x rows.length hx hlt
      omega
    · intro x
      simp [SilWalk.hartPr]
  | succ m ih =>
    intro S cnt hm hok hinv
    by_cases hd : ∃ x, x < rows.length ∧ cnt x < (rows.getD x []).length
    · obtain ⟨x, lb, hx, hlb, lb', o, pC, pa, da, ls, pC', d', w', hp, hre, hstep, hinv1⟩ :=
        hpol S cnt hok hinv hd
      have hcx : cnt x < (rows.getD x []).length := lookup_lt_Some hlb
      have hrem := CertZ2.remStep (fun x => (rows.getD x []).length) cnt x rows.length hx hcx
      have hok1 := SilWalk.okSnoc d0 S x lb' o pC pa da ls pC' d' w' hok hp hstep
      obtain ⟨Sf, cntF, pr, hokF, hinvF, hdone, hmono, htr, hsil, hf2, hagt, himg, hpst⟩ :=
        ih (SilWalk.snoc S x lb' o pC' d' w') (CertZ2.bump cnt x) (by omega) hok1 hinv1
      have hmonoF : ∀ y, cnt y ≤ cntF y := by
        intro y
        have := hmono y
        by_cases hy : y = x
        · subst hy; rw [CertZ2.bumpSelf] at this; omega
        · rw [CertZ2.bumpNe cnt x y hy] at this; exact this
      refine ⟨Sf, cntF, (⟨x, lb'⟩, o) :: pr, hokF, hinvF, hdone, hmonoF, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [htr]
        show (S.c.tr ++ [⟨x, lb'⟩]) ++ pr.map Prod.fst = S.c.tr ++ (⟨x, lb'⟩ :: pr.map Prod.fst)
        simp
      · rw [hsil]
        show (S.c.sil ++ [o]) ++ pr.map Prod.snd = S.c.sil ++ (o :: pr.map Prod.snd)
        simp
      · intro y
        rw [SilWalk.hartPrCons]
        have hfy := hf2 y
        by_cases hy : x = y
        · subst hy
          rw [if_pos rfl]
          rw [CertZ2.bumpSelf] at hfy
          have hge : cnt x + 1 ≤ cntF x := by
            have := hmono x; rw [CertZ2.bumpSelf] at this; exact this
          rw [CertZ.dropCons _ (cnt x) lb hlb,
            show cntF x - cnt x = (cntF x - (cnt x + 1)) + 1 by omega, List.take_succ_cons]
          exact .cons hre hfy
        · rw [if_neg hy]
          rw [CertZ2.bumpNe cnt x y (Ne.symm hy)] at hfy
          exact hfy
      · intro p hp'
        rcases List.mem_cons.1 hp' with rfl | hp'
        · exact hx
        · exact hagt p hp'
      · rw [himg]; rfl
      · rw [hpst]
        show (if 0 ≤ S.c.tr.length then S.pst 0 else (S.pst S.c.tr.length).set x pC') = S.pst 0
        rw [if_pos (Nat.zero_le _)]
    · refine ⟨S, cnt, [], hok, hinv, ?_, fun _ => Nat.le_refl _, by simp, by simp, ?_,
        fun p h => by simp at h, rfl, rfl⟩
      · intro x hx
        exact Nat.le_of_not_lt (fun hlt => hd ⟨x, hx, hlt⟩)
      · intro x
        simp [SilWalk.hartPr]

/-! # 2. The realized member's rows -/

theorem SilWalk.projMapIdx : ∀ pr : List (Estep × Option Nat),
    (pr.map Prod.fst).mapIdx (fun k s => SilCand.projStep s ((pr.map Prod.snd).getD k none))
      = pr.map (fun p => SilCand.projStep p.1 p.2) := by
  intro pr
  induction pr with
  | nil => rfl
  | cons p pr ih =>
    simp only [List.map_cons, List.mapIdx_cons, List.getD_cons_zero, List.getD_cons_succ]
    rw [ih]

/-- The member label of an appended `(lb', o)`: the label, or the read of a silent AMO. -/
def SilWalk.projQ (q : Lbl × Option Nat) : Lbl :=
  match q.2 with
  | some _ => SilCand.projLbl q.1
  | none => q.1

theorem SilWalk.projStepAg (s : Estep) (o : Option Nat) : (SilCand.projStep s o).esAg = s.esAg := by
  cases o <;> rfl

theorem SilWalk.projStepLb (s : Estep) (o : Option Nat) :
    (SilCand.projStep s o).esLb = SilWalk.projQ (s.esLb, o) := by
  cases o <;> rfl

theorem SilWalk.hartTrProj : ∀ (pr : List (Estep × Option Nat)) (x : Nat),
    CertZ2.hartTr (pr.map (fun p => SilCand.projStep p.1 p.2)) x
      = (SilWalk.hartPr pr x).map SilWalk.projQ := by
  intro pr x
  induction pr with
  | nil => rfl
  | cons p pr ih =>
    rw [List.map_cons, CertZ2.hartTrCons, SilWalk.hartPrCons, SilWalk.projStepAg]
    by_cases h : p.1.esAg = x
    · rw [if_pos h, if_pos h, ih, SilWalk.projStepLb]; rfl
    · rw [if_neg h, if_neg h, ih]

/-- A failed acquire's re-index is an `LRmw` with the same read values. -/
theorem SilWalk.failReidx (L : Int → Prop) (lb lb' : Lbl) :
    CertZ24.lblFail L lb → lblReidxW lb lb' →
    ∃ (aq rl : Bool) (base : Int) (ts ts' : List Nat) (rvs wvs : List (BitVec 8)) (k : WmClass),
      lb = .LRmw aq rl base ts rvs wvs k ∧ lb' = .LRmw aq rl base ts' rvs wvs k ∧
      ts'.length = ts.length := by
  rintro ⟨b, -, ⟨base, vs, j, v, hwr, -⟩, ⟨base', ts, vs', j', t, v', hrd, -⟩⟩ hre
  cases lb with
  | LRmw aq rl base0 ts0 rvs wvs k =>
    rcases hre with h | h | h
    · cases lb' with
      | LRmw aq' rl' base1 ts1 rvs' wvs' k' =>
        obtain ⟨h1, h2, h3, h4, h5, h6, hl⟩ := h
        subst h1 h2 h3 h4 h5 h6
        exact ⟨_, _, _, _, _, _, _, _, rfl, rfl, hl⟩
      | _ => simp [lblReidx] at h
    · simp [lblReidxSub] at h
    · simp [lblPoisoned] at h
  | _ => simp [lbWr, lbRd] at hwr hrd

theorem SilWalk.relSOfW (L : Int → Prop) (lb : Lbl) (q : Lbl × Option Nat) :
    SilWalk.relW L lb q → SilAgree.lblRelS L (fun t => t) lb (SilWalk.projQ q) := by
  obtain ⟨lb', o⟩ := q
  rintro ⟨hre, ⟨hnf, ho⟩ | ⟨hf, ho⟩⟩
  · dsimp only at ho
    subst ho
    exact .inl ⟨hnf, by rw [lblRenId]; exact hre⟩
  · dsimp only at ho
    obtain ⟨aq, rl, base, ts, ts', rvs, wvs, k, rfl, rfl, hl⟩ := SilWalk.failReidx L _ _ hf hre
    obtain ⟨q, rfl⟩ := Option.ne_none_iff_exists'.1 ho
    exact .inr ⟨hf, aq, rl, base, ts, ts', rvs, wvs, k, rfl, rfl, hl⟩

theorem SilWalk.forall₂Get {α β : Type _} (R : α → β → Prop) (l1 : List α) (l2 : List β) :
    List.Forall₂ R l1 l2 → ∀ j : Nat, (l1[j]? = none ∧ l2[j]? = none) ∨
      ∃ a b, l1[j]? = some a ∧ l2[j]? = some b ∧ R a b := by
  intro h
  induction h with
  | nil => intro j; exact .inl ⟨rfl, rfl⟩
  | @cons a b l1 l2 hab _ ih =>
    intro j
    cases j with
    | zero => exact .inr ⟨a, b, rfl, rfl, hab⟩
    | succ j => simpa using ih j

theorem SilWalk.forall₂Map {α β γ : Type _} (R : α → β → Prop) (R' : α → γ → Prop) (f : β → γ)
    (l1 : List α) (l2 : List β) :
    List.Forall₂ R l1 l2 → (∀ a b, R a b → R' a (f b)) → List.Forall₂ R' l1 (l2.map f) := by
  intro h hf
  induction h with
  | nil => exact .nil
  | @cons a b l1 l2 hab _ ih => exact .cons (hf a b hab) ih

theorem SilWalk.gxLblGetD (G : Gexec) (e : Geid) : gxLbl G e = (G.gxProg.getD e.1 [])[e.2]? := by
  unfold gxLbl
  rw [List.getD_eq_getElem?_getD]
  cases G.gxProg[e.1]? <;> simp

/-- **THE ROWS GIVE THE SILENT AGREEMENT.** -/
theorem SilWalk.lblAgreeOfRows (G : Gexec) (N : Nat) (L : Int → Prop) (c : SilCand.CandS) :
    (∀ s, s ∈ (SilCand.proj c).cdTr → s.esAg < N) →
    (∀ x, List.Forall₂ (SilAgree.lblRelS L (fun t => t)) (G.gxProg.getD x [])
      (CertZ2.hartTr (SilCand.proj c).cdTr x)) →
    SilAgree.lblAgreeS G (SilAgree.memberS N c) (fun t => t) L := by
  intro hag hrows e
  rw [SilWalk.gxLblGetD G e, SilAgree.memberS, CertZ3.memberLblHart N _ e hag]
  rcases SilWalk.forall₂Get _ _ _ (hrows e.1) e.2 with ⟨h1, h2⟩ | ⟨a, b, h1, h2, h3⟩
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨a, b, h1, h2, h3⟩

/-! # 3. The cert supply from the twin walk -/

namespace CatLin

/-- **THE TWIN WALK SUPPLY**: an invariant holding at the start, a twin walk policy over the graph's rows,
and — at every finished invariant state — the realized member's successful-protocol lock co. -/
def SilWalk.walkSupplyS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ Inv : SilWalk.St → (Nat → Nat) → Prop,
      Inv (SilWalk.start boot d0 N GF.gfGd.gdG) (fun _ => 0) ∧
      SilWalk.walkPol d0 GF.gfGd.gdG.gxProg (GraphFetchN2.lockBytes P) Inv ∧
      (∀ Sf cntF, Inv Sf cntF → SilWalk.ok d0 Sf →
        (∀ x, x < GF.gfGd.gdG.gxProg.length → (GF.gfGd.gdG.gxProg.getD x []).length ≤ cntF x) →
        CertZ18.lockCoSP GF.gfGd.gdG (SilAgree.memberS N Sf.c) (GraphFetchN2.lockBytes P))

/-- **(G-3) AT THE REALIZED TWIN MEMBER, FROM THE FREE TWIN WALK.** -/
theorem SilWalk.certSupplyOfWalkS (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    SilWalk.walkSupplyS boot d0 fab im N P → SilKill.certSupplyS boot d0 fab im N P := by
  intro hws GF ad _ z ss him hc hconf hres hdr _ _ _ _ _ hne hch
  obtain ⟨Inv, hI0, hpol, hco⟩ := hws GF ad z ss him hc hconf hres hdr hne hch
  obtain ⟨Sf, cntF, pr, hokF, hinvF, hdone, -, htr, hsil, hf2, -, himg, hpst⟩ :=
    SilWalk.walkRun d0 GF.gfGd.gdG.gxProg _ Inv hpol _ (SilWalk.start boot d0 N GF.gfGd.gdG)
      (fun _ => 0) (Nat.le_refl _) (SilWalk.okStart boot d0 N GF.gfGd.gdG) hI0
  have hrd : SilAgree.RunDataS boot d0 N GF.gfGd.gdG Sf.c Sf.pst Sf.dv :=
    SilWalk.runDataOfOk boot d0 N GF.gfGd.gdG Sf hokF himg hpst
  have htr' : Sf.c.tr = pr.map Prod.fst := by rw [htr]; rfl
  have hsil' : Sf.c.sil = pr.map Prod.snd := by rw [hsil]; rfl
  have hprojTr : (SilCand.proj Sf.c).cdTr = pr.map (fun p => SilCand.projStep p.1 p.2) := by
    show Sf.c.tr.mapIdx (fun k s => SilCand.projStep s (Sf.c.sil.getD k none)) = _
    rw [htr', hsil']
    exact SilWalk.projMapIdx pr
  refine ⟨Sf.c, Sf.pst, Sf.dv, fun t => t, hrd, ?_, ?_, hco Sf cntF hinvF hokF hdone⟩
  · show Sf.c.img = GF.gfGd.gdG.gxImg
    exact himg
  · refine SilWalk.lblAgreeOfRows _ N _ Sf.c (SilCand.projAg Sf.c N (SilAgree.runAg hrd))
      (fun x => ?_)
    rw [hprojTr, SilWalk.hartTrProj]
    have hfx := hf2 x
    simp only [List.drop_zero, Nat.sub_zero] at hfx
    have hrow : (GF.gfGd.gdG.gxProg.getD x []).take (cntF x) = GF.gfGd.gdG.gxProg.getD x [] := by
      by_cases hx : x < GF.gfGd.gdG.gxProg.length
      · exact List.take_of_length_le (hdone x hx)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
    rw [hrow] at hfx
    exact SilWalk.forall₂Map _ _ _ _ _ hfx (fun a b h => SilWalk.relSOfW _ a b h)

end CatLin

end Weak
