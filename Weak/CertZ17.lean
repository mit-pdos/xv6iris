/-
Weak: **W10-3c [OWN.94] (N2′, F2), increment 3 — `orderSupplyCZ2` DERIVED from the named GF-level
lock-discipline facts** (the coordinator's decision (2) and F2; `PROGRESS-W10N2p.md` "DESIGN").
Lean-only, no Rocq twin.

The walk order is a topological sort of all row events under `R := po ∪ gfDev-order ∪ coNP` (co out
of non-plain lock-byte writes).  `R` is acyclic because a KEY strictly increases along it
(`CertZ17.keyLt`): `g e` is the gmo position of `e`'s anchor (a non-plain RELEASE's own critical-section
acquire; any other ENDPOINT — lock-byte write or fabric member — itself), `κ e` the max of `g` over
`e`'s hart up to `e`, and the key `(κ e, e.2)` lexicographic.  The named facts
(**`CatLin.lockDiscCZ`**, W11-F per pc):

  (NF1) critical sections do not overlap in protocol co;
  (NF2) every non-plain release of a lock byte has its own hart's aq acquire po-before it with no own
        write of that byte between; every non-plain lock-byte write of a nonzero byte is an aq read;
        a non-plain write touches at most one lock byte;
  (NF3) no lock-byte write is a fabric member; a fabric-member RAM write is gmo-before every po-later
        lock-byte or fabric-member RAM write of its hart;
  (NF4) a plain lock-byte store is gmo-before every po-later lock-byte or fabric-member RAM write of
        its hart;
with `ioResidueGmo` (R1 RAM→I/O, R2 I/O→RAM-write, R3 I/O→I/O and fabric order), rule 1 and rule 5.

  §1  the named facts; §2 the anchors, `g`, `κ`, the key; §3 the key along `R`; §4 the order and
      **`CatLin.orderSupplyOfDisc`** (`lockDiscCZ → orderSupplyCZ2`).

Spec: the four facts are facts of xv6's lock / device code (FAITHFUL once proved per pc); assuming
acyclicity directly would be STRONGER than RVWMO.  Lean-only helpers file-qualified (`CertZ17.*`).
-/
import Weak.CertZ16

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The named facts -/

/-- A write of a lock byte. -/
def CertZ17.lockW (G : Gexec) (Lb : Int → Prop) (e : Geid) : Prop :=
  ∃ b v, Lb b ∧ gwritesByte G e b v

/-- A fabric member that is not an I/O event (a RAM write, under `gfDevWIo`). -/
def CertZ17.fabW (GF : Gfexec) (e : Geid) : Prop :=
  e ∈ GF.gfDev ∧ gisIo GF.gfGd.gdG e = false

/-- `a` is the critical-section acquire of the release `x` of `b`. -/
def CertZ17.csAcq (G : Gexec) (b : Int) (x a : Geid) : Prop :=
  lockAcq G b a ∧ CertZ14.np G a ∧ glblIs G a lbIsR ∧ glblIs G a lbAq ∧ a.1 = x.1 ∧ a.2 < x.2 ∧
  (gxLbl G a).isSome ∧
  ∀ y v, gwritesByte G y b v → y.1 = x.1 → ¬ (a.2 < y.2 ∧ y.2 < x.2)

/-- **WARNING — NF1 is FALSE on contended locks (a failed `amoswap.w.aq` inside the holder's critical section); vacuous — do not consume; superseded by the (b) route (`PROGRESS-W10N2p.md`).** **THE LOCK DISCIPLINE AT GF (NF1–NF4)**. -/
def CertZ17.lockDisc (GF : Gfexec) (Lb : Int → Prop) : Prop :=
  -- NF2
  (∀ b x, Lb b → lockRel GF.gfGd.gdG b x → CertZ14.np GF.gfGd.gdG x →
    ∃ a, CertZ17.csAcq GF.gfGd.gdG b x a) ∧
  (∀ b e v, Lb b → gwritesByte GF.gfGd.gdG e b v → v ≠ lockFree → CertZ14.np GF.gfGd.gdG e →
    glblIs GF.gfGd.gdG e lbIsR ∧ glblIs GF.gfGd.gdG e lbAq) ∧
  (∀ b b' e v v', Lb b → Lb b' → gwritesByte GF.gfGd.gdG e b v → gwritesByte GF.gfGd.gdG e b' v' →
    CertZ14.np GF.gfGd.gdG e → b = b') ∧
  -- NF1
  (∀ b x a w vw, Lb b → lockRel GF.gfGd.gdG b x → CertZ14.np GF.gfGd.gdG x →
    CertZ17.csAcq GF.gfGd.gdG b x a → gwritesByte GF.gfGd.gdG w b vw →
    CertZ14.np GF.gfGd.gdG w → w.1 ≠ x.1 →
    gwix GF.gfGd.gdG w < gwix GF.gfGd.gdG a ∨ gwix GF.gfGd.gdG x < gwix GF.gfGd.gdG w) ∧
  -- NF3
  (∀ e, CertZ17.lockW GF.gfGd.gdG Lb e → e ∉ GF.gfDev) ∧
  (∀ f e, CertZ17.fabW GF f →
    (CertZ17.lockW GF.gfGd.gdG Lb e ∨ CertZ17.fabW GF e) →
    WeakRvwmoGraph.gpo GF.gfGd.gdG f e → gmoLt GF.gfGd.gdG f e) ∧
  -- NF4
  (∀ u e, CertZ17.lockW GF.gfGd.gdG Lb u → ¬ CertZ14.np GF.gfGd.gdG u →
    (CertZ17.lockW GF.gfGd.gdG Lb e ∨ CertZ17.fabW GF e) →
    WeakRvwmoGraph.gpo GF.gfGd.gdG u e → gmoLt GF.gfGd.gdG u e)

/-! # 2. Anchors, `g`, `κ` -/

/-- An endpoint: a lock-byte write or a fabric member. -/
def CertZ17.isEnd (GF : Gfexec) (Lb : Int → Prop) (e : Geid) : Prop :=
  CertZ17.lockW GF.gfGd.gdG Lb e ∨ e ∈ GF.gfDev

/-- The release condition (its anchor is its critical-section acquire). -/
def CertZ17.relC (G : Gexec) (Lb : Int → Prop) (e a : Geid) : Prop :=
  ∃ b, Lb b ∧ lockRel G b e ∧ CertZ14.np G e ∧ CertZ17.csAcq G b e a

open Classical in
/-- The anchor of a non-plain release: its critical-section acquire. -/
noncomputable def CertZ17.anc (G : Gexec) (Lb : Int → Prop) (e : Geid) : Option Geid :=
  if h : ∃ a, CertZ17.relC G Lb e a then some (Classical.choose h) else none

theorem CertZ17.ancSome (G : Gexec) (Lb : Int → Prop) (e a : Geid) :
    CertZ17.anc G Lb e = some a → CertZ17.relC G Lb e a := by
  unfold CertZ17.anc
  split
  · rename_i h; intro he; cases he; exact Classical.choose_spec h
  · intro he; cases he

theorem CertZ17.ancNone (G : Gexec) (Lb : Int → Prop) (e : Geid) :
    CertZ17.anc G Lb e = none → ¬ ∃ a, CertZ17.relC G Lb e a := by
  unfold CertZ17.anc
  split
  · intro he; cases he
  · rename_i h; intro _; exact h

open Classical in
/-- The anchor's gmo position (0 off the endpoints). -/
noncomputable def CertZ17.g (GF : Gfexec) (Lb : Int → Prop) (e : Geid) : Nat :=
  match CertZ17.anc GF.gfGd.gdG Lb e with
  | some a => gpos GF.gfGd.gdG a
  | none => if CertZ17.isEnd GF Lb e then gpos GF.gfGd.gdG e else 0

/-- The max of `g` over `e`'s hart up to `e`. -/
noncomputable def CertZ17.kap (GF : Gfexec) (Lb : Int → Prop) (e : Geid) : Nat :=
  ((List.range (e.2 + 1)).map (fun j => CertZ17.g GF Lb (e.1, j))).foldr max 0

theorem CertZ17.foldMaxLe (l : List Nat) (M : Nat) : (∀ x, x ∈ l → x ≤ M) → l.foldr max 0 ≤ M := by
  induction l with
  | nil => intro _; exact Nat.zero_le _
  | cons a l ih =>
    intro h
    simp only [List.foldr_cons]
    have := h a (by simp)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem CertZ17.kapGe (GF : Gfexec) (Lb : Int → Prop) (e : Geid) (j : Nat) :
    j ≤ e.2 → CertZ17.g GF Lb (e.1, j) ≤ CertZ17.kap GF Lb e := by
  intro hj
  exact axViolSubsumeFoldrMaxLe _ _ (List.mem_map_of_mem (List.mem_range.2 (by omega)))

theorem CertZ17.kapSelf (GF : Gfexec) (Lb : Int → Prop) (e : Geid) :
    CertZ17.g GF Lb e ≤ CertZ17.kap GF Lb e :=
  CertZ17.kapGe GF Lb e e.2 (Nat.le_refl _)

theorem CertZ17.kapMono (GF : Gfexec) (Lb : Int → Prop) (x y : Geid) :
    x.1 = y.1 → x.2 ≤ y.2 → CertZ17.kap GF Lb x ≤ CertZ17.kap GF Lb y := by
  intro h1 h2
  apply CertZ17.foldMaxLe
  intro z hz
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
  rw [h1]
  exact CertZ17.kapGe GF Lb y j (by have := List.mem_range.1 hj; omega)

/-! # 3. The key along `R` -/

theorem CertZ17.lockWLbl (G : Gexec) (Lb : Int → Prop) (e : Geid) :
    CertZ17.lockW G Lb e → (gxLbl G e).isSome := by
  rintro ⟨b, v, -, l, -, -, -, hl, -⟩
  rw [hl]; rfl

theorem CertZ17.lockWIo (G : Gexec) (Lb : Int → Prop) (e : Geid) :
    CertZ17.lockW G Lb e → gisIo G e = false ∧ gisW G e = true ∧ gmem G e := by
  rintro ⟨b, v, -, hw⟩
  have hW := gwritesByteGlblW G e b v hw
  obtain ⟨l, base, vs, jj, hl, hwr, -, -⟩ := hw
  have hiw : lbIsW l = true := lbWrIsW l _ hwr
  refine ⟨?_, by unfold gisW; rw [hl]; exact hiw, WeakRvwmoGraph.glblIsWGmem G e hW⟩
  unfold gisIo; rw [hl]
  cases l <;> simp_all [lbIsW, lbIsIo]

/-- **THE ANCHOR BOUND**: the key's first component at an endpoint is at most its gmo position. -/
theorem CertZ17.kapLe (GF : Gfexec) (ad : List (Geid × Geid)) (Lb : Int → Prop) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gfDevWIo GF → CertZ17.lockDisc GF Lb →
    (∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome) →
    ∀ x, CertZ17.isEnd GF Lb x → CertZ17.kap GF Lb x ≤ gpos GF.gfGd.gdG x := by
  intro hc hres hwio hld hdevL x hx
  obtain ⟨hNF2a, hNF2b, -, -, -, hNF3b, hNF4⟩ := hld
  have h6 := hc.2.1
  -- the endpoint is a labelled memory event
  have hxm : gmem GF.gfGd.gdG x := by
    rcases hx with h | h
    · exact (CertZ17.lockWIo _ Lb x h).2.2
    · exact WeakRvwmoLin2.wioGmem _ x (hwio x h)
  have hxl : (gxLbl GF.gfGd.gdG x).isSome := by
    obtain ⟨l, hl, -⟩ := hxm; rw [hl]; rfl
  have hxkind : CertZ17.lockW GF.gfGd.gdG Lb x ∨ CertZ17.fabW GF x ∨
      gisIo GF.gfGd.gdG x = true := by
    rcases hx with h | h
    · exact .inl h
    · cases hio : gisIo GF.gfGd.gdG x with
      | true => exact .inr (.inr rfl)
      | false => exact .inr (.inl ⟨h, hio⟩)
  have hancLt : ∀ e a, CertZ17.relC GF.gfGd.gdG Lb e a → e.1 = x.1 → e.2 ≤ x.2 →
      gpos GF.gfGd.gdG a < gpos GF.gfGd.gdG x := by
    rintro e a ⟨b, -, -, -, hacq, -, hR, hAq, h1, h2, hal, -⟩ he1 he2
    have hpo : WeakRvwmoGraph.gpo GF.gfGd.gdG a x := ⟨by rw [h1, he1], by omega, hal, hxl⟩
    exact (CatLin.acqGmoAfterC _ a x h6 hpo hR hAq hxm).2.2
  apply CertZ17.foldMaxLe
  intro z hz
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
  have hjx : j ≤ x.2 := by have := List.mem_range.1 hj; omega
  unfold CertZ17.g
  cases hanc : CertZ17.anc GF.gfGd.gdG Lb (x.1, j) with
  | some a => exact Nat.le_of_lt (hancLt _ a (CertZ17.ancSome _ Lb _ a hanc) rfl hjx)
  | none =>
    dsimp only
    split
    · rename_i hend
      rcases Nat.lt_or_eq_of_le hjx with hlt | heq
      · have hel : (gxLbl GF.gfGd.gdG (x.1, j)).isSome := by
          rcases hend with h | h
          · exact CertZ17.lockWLbl _ Lb _ h
          · exact hdevL _ h
        have hpo : WeakRvwmoGraph.gpo GF.gfGd.gdG (x.1, j) x := ⟨rfl, hlt, hel, hxl⟩
        refine Nat.le_of_lt (?_ : gmoLt GF.gfGd.gdG (x.1, j) x).2.2
        rcases hend with hlw | hdv
        · obtain ⟨b, v, hb, hw⟩ := hlw
          by_cases hnp : CertZ14.np GF.gfGd.gdG (x.1, j)
          · by_cases hv : v = lockFree
            · subst hv
              obtain ⟨a, ha⟩ := hNF2a b (x.1, j) hb hw hnp
              exact absurd ⟨a, b, hb, hw, hnp, ha⟩ (CertZ17.ancNone _ Lb _ hanc)
            · obtain ⟨hR, hAq⟩ := hNF2b b _ v hb hw hv hnp
              exact CatLin.acqGmoAfterC _ _ x h6 hpo hR hAq hxm
          · rcases hxkind with hk | hk | hk
            · exact hNF4 (x.1, j) x ⟨b, v, hb, hw⟩ hnp (.inl hk) hpo
            · exact hNF4 (x.1, j) x ⟨b, v, hb, hw⟩ hnp (.inr hk) hpo
            · exact hres (x.1, j) x (.inl ⟨hpo, (CertZ17.lockWIo _ Lb _ ⟨b, v, hb, hw⟩).2.2,
                (CertZ17.lockWIo _ Lb _ ⟨b, v, hb, hw⟩).1, hk⟩)
        · cases hio : gisIo GF.gfGd.gdG (x.1, j) with
          | true =>
            rcases hxkind with hk | hk | hk
            · exact hres (x.1, j) x (.inr (.inl ⟨hpo, hio, (CertZ17.lockWIo _ Lb x hk).2.1⟩))
            · have hw : gisW GF.gfGd.gdG x = true := by
                have := hwio x hk.1
                unfold gisWIo at this
                have h2 := hk.2
                simpa [h2] using this
              exact hres (x.1, j) x (.inr (.inl ⟨hpo, hio, hw⟩))
            · exact hres (x.1, j) x (.inr (.inr (.inr (.inl ⟨hio, hk, hpo⟩))))
          | false =>
            have hfab : CertZ17.fabW GF (x.1, j) := ⟨hdv, hio⟩
            rcases hxkind with hk | hk | hk
            · exact hNF3b _ x hfab (.inl hk) hpo
            · exact hNF3b _ x hfab (.inr hk) hpo
            · have hem : gmem GF.gfGd.gdG (x.1, j) := WeakRvwmoLin2.wioGmem _ _ (hwio _ hdv)
              exact hres (x.1, j) x (.inl ⟨hpo, hem, hio, hk⟩)
      · rw [show ((x.1, j) : Geid) = x from Prod.ext rfl heq]
        exact Nat.le_refl _
    · exact Nat.zero_le _

/-- The order relation: program order on row events, fabric order, co out of non-plain lock writes. -/
def CertZ17.R (GF : Gfexec) (Lb : Int → Prop) (x y : Geid) : Prop :=
  (x.1 = y.1 ∧ x.2 < y.2 ∧ CertZ8.evsOf GF.gfGd.gdG.gxProg x ∧ CertZ8.evsOf GF.gfGd.gdG.gxProg y) ∨
  (∃ m n : Nat, GF.gfDev[m]? = some x ∧ GF.gfDev[n]? = some y ∧ m < n) ∨
  (∃ b vx vy, Lb b ∧ gwritesByte GF.gfGd.gdG x b vx ∧ gwritesByte GF.gfGd.gdG y b vy ∧
    CertZ14.np GF.gfGd.gdG x ∧ gwix GF.gfGd.gdG x < gwix GF.gfGd.gdG y)

/-- A bound on every row index. -/
def CertZ17.bnd (rows : List (List Lbl)) : Nat := (rows.map List.length).foldr max 0 + 1

theorem CertZ17.lblBnd (G : Gexec) (e : Geid) :
    (gxLbl G e).isSome → e.2 < CertZ17.bnd G.gxProg := by
  intro h
  unfold gxLbl at h
  cases hr : G.gxProg[e.1]? with
  | none => rw [hr] at h; cases h
  | some row =>
    rw [hr] at h
    simp only [Option.bind_some] at h
    have hlt : e.2 < row.length := by
      cases hl : row[e.2]? with
      | none => rw [hl] at h; cases h
      | some _ => exact lookup_lt_Some hl
    have := axViolSubsumeFoldrMaxLe (G.gxProg.map List.length) row.length
      (List.mem_map_of_mem (List.mem_of_getElem? hr))
    unfold CertZ17.bnd
    omega

/-- The key. -/
noncomputable def CertZ17.key (GF : Gfexec) (Lb : Int → Prop) (e : Geid) : Nat :=
  CertZ17.kap GF Lb e * CertZ17.bnd GF.gfGd.gdG.gxProg + e.2

theorem CertZ17.keyPo (GF : Gfexec) (Lb : Int → Prop) (x y : Geid) :
    x.1 = y.1 → x.2 < y.2 → CertZ17.key GF Lb x < CertZ17.key GF Lb y := by
  intro h1 h2
  have hk := CertZ17.kapMono GF Lb x y h1 (Nat.le_of_lt h2)
  have := Nat.mul_le_mul_right (CertZ17.bnd GF.gfGd.gdG.gxProg) hk
  unfold CertZ17.key
  omega

theorem CertZ17.keyStrict (GF : Gfexec) (Lb : Int → Prop) (x y : Geid) :
    x.2 < CertZ17.bnd GF.gfGd.gdG.gxProg → CertZ17.kap GF Lb x < CertZ17.kap GF Lb y →
    CertZ17.key GF Lb x < CertZ17.key GF Lb y := by
  intro hb hk
  have := Nat.mul_le_mul_right (CertZ17.bnd GF.gfGd.gdG.gxProg) (show CertZ17.kap GF Lb x + 1 ≤ _ from hk)
  rw [Nat.add_mul, Nat.one_mul] at this
  unfold CertZ17.key
  omega

/-- A non-release endpoint's `g` is its gmo position. -/
theorem CertZ17.gEnd (GF : Gfexec) (Lb : Int → Prop) (e : Geid) :
    CertZ17.anc GF.gfGd.gdG Lb e = none → CertZ17.isEnd GF Lb e →
    CertZ17.g GF Lb e = gpos GF.gfGd.gdG e := by
  intro hn he
  unfold CertZ17.g
  rw [hn]
  dsimp only
  rw [if_pos he]

/-- **THE KEY STRICTLY INCREASES ALONG `R`.** -/
theorem CertZ17.keyLt (GF : Gfexec) (ad : List (Geid × Geid)) (Lb : Int → Prop) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gfDevWIo GF → CertZ17.lockDisc GF Lb →
    (∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome) →
    ∀ x y, CertZ17.R GF Lb x y → CertZ17.key GF Lb x < CertZ17.key GF Lb y := by
  intro hc hres hwio hld hdevL x y hR
  have hwf := hc.1
  have h6 := hc.2.1
  have hld' := hld
  obtain ⟨-, -, hNF2c, hNF1, hNF3a, -, -⟩ := hld'
  rcases hR with ⟨h1, h2, -, -⟩ | ⟨m, n, hm, hn, hmn⟩ | ⟨b, vx, vy, hb, hx, hy, hnpx, hlt⟩
  · exact CertZ17.keyPo GF Lb x y h1 h2
  · -- fabric order
    have hxd : x ∈ GF.gfDev := List.mem_of_getElem? hm
    have hyd : y ∈ GF.gfDev := List.mem_of_getElem? hn
    have hxy : gmoLt GF.gfGd.gdG x y :=
      hres x y (.inr (.inr (.inr (.inr (.inl ⟨WeakRvwmoLin2.wioGmem _ x (hwio x hxd),
        WeakRvwmoLin2.wioGmem _ y (hwio y hyd), m, n, hm, hn, hmn⟩)))))
    have hkx := CertZ17.kapLe GF ad Lb hc hres hwio hld hdevL x (.inr hxd)
    have hny : CertZ17.anc GF.gfGd.gdG Lb y = none := by
      cases ha : CertZ17.anc GF.gfGd.gdG Lb y with
      | none => rfl
      | some a =>
        obtain ⟨b, hb, hrel, -, -⟩ := CertZ17.ancSome _ Lb y a ha
        exact absurd hyd (hNF3a y ⟨b, lockFree, hb, hrel⟩)
    have hgy := CertZ17.gEnd GF Lb y hny (.inr hyd)
    have hky := CertZ17.kapSelf GF Lb y
    exact CertZ17.keyStrict GF Lb x y (CertZ17.lblBnd _ x (hdevL x hxd)) (by
      have := hxy.2.2; omega)
  · -- co out of a non-plain lock write
    have hxw := gwritesByteGwrites _ x b vx hwf hx
    have hyw := gwritesByteGwrites _ y b vy hwf hy
    have hxl : (gxLbl GF.gfGd.gdG x).isSome := CertZ17.lockWLbl _ Lb x ⟨b, vx, hb, hx⟩
    have hyl : (gxLbl GF.gfGd.gdG y).isSome := CertZ17.lockWLbl _ Lb y ⟨b, vy, hb, hy⟩
    by_cases hh : x.1 = y.1
    · -- the same hart: program order (rule 1)
      rcases Nat.lt_trichotomy x.2 y.2 with h | h | h
      · exact CertZ17.keyPo GF Lb x y hh h
      · have := gwixInj _ x y hwf.1 hxw hyw (by
          rw [show x = y from Prod.ext hh h]); rw [this] at hlt; omega
      · have hpo : WeakRvwmoGraph.gpo GF.gfGd.gdG y x := ⟨hh.symm, h, hyl, hxl⟩
        have hmo := h6 y x (Or.inl ⟨hpo, b, Or.inl ⟨vy, hy⟩, vx, hx⟩)
        have := gmoGwixLt _ y x hwf hyw hxw hmo
        omega
    · have hkx := CertZ17.kapLe GF ad Lb hc hres hwio hld hdevL x (.inl ⟨b, vx, hb, hx⟩)
      have hxy := gwixLtGmo _ x y hwf hxw hyw hlt
      have hgy : gpos GF.gfGd.gdG x < CertZ17.g GF Lb y := by
        cases ha : CertZ17.anc GF.gfGd.gdG Lb y with
        | none =>
          rw [CertZ17.gEnd GF Lb y ha (.inl ⟨b, vy, hb, hy⟩)]
          exact hxy.2.2
        | some a =>
          obtain ⟨b', hb', hrel, hnpy, hcs⟩ := CertZ17.ancSome _ Lb y a ha
          have hbb : b' = b := hNF2c b' b y lockFree vy hb' hb hrel hy hnpy
          subst hbb
          have hAw := lockAcqGwrites _ b' a hwf hcs.1
          rcases hNF1 b' y a x vx hb' hrel hnpy hcs hx hnpx hh with h' | h'
          · unfold CertZ17.g
            rw [ha]
            exact (gwixLtGmo _ x a hwf hxw hAw h').2.2
          · omega
      have hky := CertZ17.kapSelf GF Lb y
      exact CertZ17.keyStrict GF Lb x y (CertZ17.lblBnd _ x hxl) (by omega)

/-- **`R` IS ACYCLIC.** -/
theorem CertZ17.rAcyc (GF : Gfexec) (ad : List (Geid × Geid)) (Lb : Int → Prop) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gfDevWIo GF → CertZ17.lockDisc GF Lb →
    (∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome) →
    ∀ x, ¬ tc (CertZ17.R GF Lb) x x := by
  intro hc hres hwio hld hdevL x hx
  have key : ∀ a b, tc (CertZ17.R GF Lb) a b → CertZ17.key GF Lb a < CertZ17.key GF Lb b := by
    intro a b h
    induction h with
    | single h => exact CertZ17.keyLt GF ad Lb hc hres hwio hld hdevL _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (CertZ17.keyLt GF ad Lb hc hres hwio hld hdevL _ _ h)
  exact Nat.lt_irrefl _ (key x x hx)

/-! # 4. The order -/

/-- All row events. -/
def CertZ17.evs (rows : List (List Lbl)) : List Geid :=
  (List.range rows.length).flatMap (fun x => (List.range (rows.getD x []).length).map (fun j => (x, j)))

theorem CertZ17.memEvs (rows : List (List Lbl)) (e : Geid) :
    e ∈ CertZ17.evs rows ↔ CertZ8.evsOf rows e := by
  unfold CertZ17.evs CertZ8.evsOf
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
    exact ⟨List.mem_range.1 hx, List.mem_range.1 hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e.1, List.mem_range.2 h1, List.mem_map.2 ⟨e.2, List.mem_range.2 h2, rfl⟩⟩

theorem CertZ17.evsNodupAux (f : Nat → Nat) :
    ∀ n, ((List.range n).flatMap (fun x => (List.range (f x)).map (fun j => (x, j)))).Nodup := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine List.nodup_append.2 ⟨ih, CertZ8.nodupFst n (f n), ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨x, hx, ha'⟩ := List.mem_flatMap.1 ha
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha'
    obtain ⟨j', -, he⟩ := List.mem_map.1 hb
    simp only [Prod.mk.injEq] at he
    have := List.mem_range.1 hx
    omega

theorem CertZ17.evsNodup (rows : List (List Lbl)) : (CertZ17.evs rows).Nodup :=
  CertZ17.evsNodupAux (fun x => (rows.getD x []).length) rows.length

/-- **`CertZ17.ordOfDisc` — THE WALK ORDER FROM THE LOCK DISCIPLINE.** -/
theorem CertZ17.ordOfDisc (GF : Gfexec) (ad : List (Geid × Geid)) (Lb : Int → Prop) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gfDevWIo GF → CertZ17.lockDisc GF Lb →
    (∀ e, e ∈ GF.gfDev → CertZ8.evsOf GF.gfGd.gdG.gxProg e) →
    (∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome) →
    ∃ L, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L ∧ CertZ16.ordCoNP GF.gfGd.gdG L Lb := by
  intro hc hres hwio hld hdevE hdevL
  haveI : DecidableRel (CertZ17.R GF Lb) := fun _ _ => Classical.propDecidable _
  obtain ⟨L, hnd, hmem, hidx⟩ := topoSort (CertZ17.R GF Lb) (CertZ17.evs GF.gfGd.gdG.gxProg)
    (CertZ17.rAcyc GF ad Lb hc hres hwio hld hdevL) (CertZ17.evsNodup _)
  have hmem' : ∀ e, e ∈ L ↔ CertZ8.evsOf GF.gfGd.gdG.gxProg e := fun e => (hmem e).trans
    (CertZ17.memEvs _ e)
  refine ⟨L, ⟨hnd, hmem', fun i j x a b hi hj hab => ?_, fun m n i j e e' hm hn hmn hi hj => ?_⟩,
    fun b x y vx vy i j hb hx hy hnp hlt hi hj => ?_⟩
  · exact hidx i j _ _ hi hj (.inl ⟨rfl, hab, (hmem' _).1 (List.mem_of_getElem? hi),
      (hmem' _).1 (List.mem_of_getElem? hj)⟩)
  · exact hidx i j e e' hi hj (.inr (.inl ⟨m, n, hm, hn, hmn⟩))
  · exact hidx i j x y hi hj (.inr (.inr ⟨b, vx, vy, hb, hx, hy, hnp, hlt⟩))

namespace CatLin

/-- **WARNING — NF1 is FALSE on contended locks (a failed `amoswap.w.aq` inside the holder's critical section); vacuous — do not consume; superseded by the (b) route (`PROGRESS-W10N2p.md`).** **THE LOCK DISCIPLINE — THE NAMED GF-LEVEL FACTS (NF1–NF4), W11-F per pc.** -/
def lockDiscCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    CertZ17.lockDisc GF (GraphFetchN2.lockBytes P)

/-- `gfDevWIo` over the class (discharged for xv6 bundles by `gfDevWIoOfXv6` + `usedElemGateOk`). -/
def gfDevWIoCZ (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    gfDevWIo GF

/-- **WARNING — NF1 is FALSE on contended locks (a failed `amoswap.w.aq` inside the holder's critical section); vacuous — do not consume; superseded by the (b) route (`PROGRESS-W10N2p.md`).** **`orderSupplyOfDisc` — `orderSupplyCZ2` DERIVED** from the lock discipline and `gfDevWIo`. -/
theorem orderSupplyOfDisc (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) :
    lockDiscCZ boot d0 fab im P → gfDevWIoCZ boot d0 fab im → orderSupplyCZ2 boot d0 fab im P := by
  intro hld hwio GF ad z ss him hc hconf hres hdr hne hch
  have hdevE : ∀ e, e ∈ GF.gfDev → CertZ8.evsOf GF.gfGd.gdG.gxProg e := by
    intro e he
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨i, k⟩ := e
    obtain ⟨row, hrow, hk⟩ := hconf.2.2.1 n i k hn
    refine ⟨lookup_lt_Some hrow, ?_⟩
    rw [List.getD_eq_getElem?_getD, hrow, Option.getD_some]
    exact hk
  have hdevL : ∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome := by
    intro e he
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨i, k⟩ := e
    obtain ⟨row, hrow, hk⟩ := hconf.2.2.1 n i k hn
    unfold gxLbl
    simp only [hrow, Option.bind_some]
    exact lookup_lt_is_Some_2 hk
  exact CertZ17.ordOfDisc GF ad _ hc hres (hwio GF ad him hc hconf) (hld GF ad him hc hconf) hdevE
    hdevL

end CatLin

namespace CatLin

section glue

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **WARNING — NF1 is FALSE on contended locks (a failed `amoswap.w.aq` inside the holder's critical section); vacuous — do not consume; superseded by the (b) route (`PROGRESS-W10N2p.md`).** **`cycleKillOfDiscSiteCZRC`** — (was) WHAT W11-F CONSUMES AT THE ZERO CUT (protocol lock co, order DERIVED):
the class kill from the WP package, the fetch-view premise, the hart count and (P2), the LOCK
DISCIPLINE (NF1–NF4) and `gfDevWIo`, the SITE supply, the two xv6 lock facts and the L2′ claim. -/
theorem cycleKillOfDiscSiteCZRC (hlc : HasLC) (GF0 : BundledGFunctors) [MachGpreS hlc GF0]
    [WeakGpreS GF0] (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (Nm : Int → Int → Namespace) (P : Int → Int → Prop)
    (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (N : Nat) :
    freshEra gen σ0 →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    wpPackage hlc GF0 gen σ0 D →
    (∀ a base, P a base → wpPackageProt hlc GF0 gen σ0 D (Nm a base) a base) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (∀ (GF : Gfexec) (ad : List (Geid × Geid)), GF.gfGd.gdG.gxImg = imgZ σ0.wgimg →
      rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      GF.gfGd.gdG.gxProg.length ≤ N ∧ GraphFetchBlocks.emPremOk boot GF.gfGd.gdG) →
    lockDiscCZ boot d0 fab (imgZ σ0.wgimg) P →
    gfDevWIoCZ boot d0 fab (imgZ σ0.wgimg) →
    siteSupplyCZ boot d0 fab (imgZ σ0.wgimg) →
    acqAqCZ2 boot d0 fab (imgZ σ0.wgimg) P →
    relCoversCZ2 boot d0 fab (imgZ σ0.wgimg) P →
    l2ClaimCZR2 boot d0 fab (imgZ σ0.wgimg) P (badRun gen σ0) →
    cycleKillCZC boot d0 fab (imgZ σ0.wgimg) :=
  fun hfr hb1 hb2 hwp hwpp hcov hpre hdisc hwio hsite hAQ hRC hl2 =>
    cycleKillOfOrdSiteCZRC2 hlc GF0 gen σ0 D hD Nm P boot d0 fab N hfr hb1 hb2 hwp hwpp hcov hpre
      (orderSupplyOfDisc boot d0 fab _ P hdisc hwio) hsite hAQ hRC hl2

end glue

end CatLin

end Weak
