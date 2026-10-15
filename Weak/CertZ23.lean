/-
Weak: **W10-3c [OWN.94] (N2′), decision (3) — the walk order at SUCCESSFUL-protocol lock co,
`ordCoSP`, DERIVED** (`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

`CertZ16.orderSupplyCZ2` (co out of EVERY non-plain lock write, to every write) is false on contended
xv6 graphs (failed acquires close po ∪ co cycles).  The transport (`CertZ18.lockCoSP`) needs only co among
SUCCESSFUL protocol writes (`CertZ18.sp`: non-plain, not a failed acquire).  The order is a topological
sort under `R := po ∪ gfDev-order ∪ co_sp`, acyclic by CertZ17's key with ENDPOINTS restricted to the
successful lock writes and the fabric members (`CertZ23.keyLt`).  The named facts
(**`CatLin.lockDiscCZ3`**, W11-F per pc):

  (NF2a) every non-plain release of a lock byte has its own hart's aq acquire po-before it, no own write
         of that byte between (`CertZ17.csAcq`);
  (NF2b) every SUCCESSFUL lock-byte write of a nonzero byte is an aq read (the `amoswap.w.aq`);
  (NF2c) a non-plain write touches at most one lock byte;
  (NF1′) a SUCCESSFUL write of a lock byte by another hart is co-outside every critical section;
  (NF3a) no lock-byte write is a fabric member; (NF3b) a fabric-member RAM write is gmo-before every
         po-later successful lock-byte write or fabric-member RAM write of its hart.
No plain-store fact (F2/NF4 dropped) and no failed acquire is ordered.

  §1 the facts; §2 endpoints, `g3`, `κ3`, key; §3 the key along `R3`; §4 the order, `ordCoSP`,
  `CatLin.orderSupplyCZ3`, `CatLin.orderSupplyOfDisc3`; §5 the member's `lockCoSP` from the order and
  the walk-supply → cert-supply step.

Spec: the facts are facts of xv6's lock / device code (FAITHFUL once proved per pc); assuming
acyclicity would be STRONGER.  Lean-only helpers file-qualified (`CertZ23.*`).
-/
import Weak.CertZ22

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The named facts -/

/-- A SUCCESSFUL protocol write of a lock byte. -/
def CertZ23.spW (G : Gexec) (Lb : Int → Prop) (e : Geid) : Prop :=
  ∃ b v, Lb b ∧ gwritesByte G e b v ∧ CertZ18.sp G b e

/-- **THE LOCK DISCIPLINE AT GF, SUCCESSFUL OPS (NF2a/b/c, NF1′, NF3a/b)**. -/
def CertZ23.lockDisc3 (GF : Gfexec) (Lb : Int → Prop) : Prop :=
  (∀ b x, Lb b → lockRel GF.gfGd.gdG b x → CertZ14.np GF.gfGd.gdG x →
    ∃ a, CertZ17.csAcq GF.gfGd.gdG b x a) ∧
  (∀ b e v, Lb b → gwritesByte GF.gfGd.gdG e b v → v ≠ lockFree → CertZ18.sp GF.gfGd.gdG b e →
    glblIs GF.gfGd.gdG e lbIsR ∧ glblIs GF.gfGd.gdG e lbAq) ∧
  (∀ b b' e v v', Lb b → Lb b' → gwritesByte GF.gfGd.gdG e b v → gwritesByte GF.gfGd.gdG e b' v' →
    CertZ14.np GF.gfGd.gdG e → b = b') ∧
  (∀ b x a w vw, Lb b → lockRel GF.gfGd.gdG b x → CertZ14.np GF.gfGd.gdG x →
    CertZ17.csAcq GF.gfGd.gdG b x a → gwritesByte GF.gfGd.gdG w b vw →
    CertZ18.sp GF.gfGd.gdG b w → w.1 ≠ x.1 →
    gwix GF.gfGd.gdG w < gwix GF.gfGd.gdG a ∨ gwix GF.gfGd.gdG x < gwix GF.gfGd.gdG w) ∧
  (∀ e, CertZ17.lockW GF.gfGd.gdG Lb e → e ∉ GF.gfDev) ∧
  (∀ f e, CertZ17.fabW GF f →
    (CertZ23.spW GF.gfGd.gdG Lb e ∨ CertZ17.fabW GF e) →
    WeakRvwmoGraph.gpo GF.gfGd.gdG f e → gmoLt GF.gfGd.gdG f e)

/-! # 2. Endpoints, `g3`, `κ3` -/

def CertZ23.isEnd (GF : Gfexec) (Lb : Int → Prop) (e : Geid) : Prop :=
  CertZ23.spW GF.gfGd.gdG Lb e ∨ e ∈ GF.gfDev

theorem CertZ23.spWLockW (G : Gexec) (Lb : Int → Prop) (e : Geid) :
    CertZ23.spW G Lb e → CertZ17.lockW G Lb e :=
  fun ⟨b, v, hb, hw, _⟩ => ⟨b, v, hb, hw⟩

open Classical in
noncomputable def CertZ23.g (GF : Gfexec) (Lb : Int → Prop) (e : Geid) : Nat :=
  match CertZ17.anc GF.gfGd.gdG Lb e with
  | some a => gpos GF.gfGd.gdG a
  | none => if CertZ23.isEnd GF Lb e then gpos GF.gfGd.gdG e else 0

noncomputable def CertZ23.kap (GF : Gfexec) (Lb : Int → Prop) (e : Geid) : Nat :=
  ((List.range (e.2 + 1)).map (fun j => CertZ23.g GF Lb (e.1, j))).foldr max 0

theorem CertZ23.kapGe (GF : Gfexec) (Lb : Int → Prop) (e : Geid) (j : Nat) :
    j ≤ e.2 → CertZ23.g GF Lb (e.1, j) ≤ CertZ23.kap GF Lb e := by
  intro hj
  exact axViolSubsumeFoldrMaxLe _ _ (List.mem_map_of_mem (List.mem_range.2 (by omega)))

theorem CertZ23.kapSelf (GF : Gfexec) (Lb : Int → Prop) (e : Geid) :
    CertZ23.g GF Lb e ≤ CertZ23.kap GF Lb e :=
  CertZ23.kapGe GF Lb e e.2 (Nat.le_refl _)

theorem CertZ23.kapMono (GF : Gfexec) (Lb : Int → Prop) (x y : Geid) :
    x.1 = y.1 → x.2 ≤ y.2 → CertZ23.kap GF Lb x ≤ CertZ23.kap GF Lb y := by
  intro h1 h2
  apply CertZ17.foldMaxLe
  intro z hz
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
  rw [h1]
  exact CertZ23.kapGe GF Lb y j (by have := List.mem_range.1 hj; omega)

/-- **THE ANCHOR BOUND** at an endpoint. -/
theorem CertZ23.kapLe (GF : Gfexec) (ad : List (Geid × Geid)) (Lb : Int → Prop) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gfDevWIo GF → CertZ23.lockDisc3 GF Lb →
    (∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome) →
    ∀ x, CertZ23.isEnd GF Lb x → CertZ23.kap GF Lb x ≤ gpos GF.gfGd.gdG x := by
  intro hc hres hwio hld hdevL x hx
  obtain ⟨hNF2a, hNF2b, -, -, -, hNF3b⟩ := hld
  have h6 := hc.2.1
  have hxm : gmem GF.gfGd.gdG x := by
    rcases hx with h | h
    · exact (CertZ17.lockWIo _ Lb x (CertZ23.spWLockW _ Lb x h)).2.2
    · exact WeakRvwmoLin2.wioGmem _ x (hwio x h)
  have hxl : (gxLbl GF.gfGd.gdG x).isSome := by
    obtain ⟨l, hl, -⟩ := hxm; rw [hl]; rfl
  have hxkind : CertZ23.spW GF.gfGd.gdG Lb x ∨ CertZ17.fabW GF x ∨
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
  unfold CertZ23.g
  cases hanc : CertZ17.anc GF.gfGd.gdG Lb (x.1, j) with
  | some a => exact Nat.le_of_lt (hancLt _ a (CertZ17.ancSome _ Lb _ a hanc) rfl hjx)
  | none =>
    dsimp only
    split
    · rename_i hend
      rcases Nat.lt_or_eq_of_le hjx with hlt | heq
      · have hel : (gxLbl GF.gfGd.gdG (x.1, j)).isSome := by
          rcases hend with h | h
          · exact CertZ17.lockWLbl _ Lb _ (CertZ23.spWLockW _ Lb _ h)
          · exact hdevL _ h
        have hpo : WeakRvwmoGraph.gpo GF.gfGd.gdG (x.1, j) x := ⟨rfl, hlt, hel, hxl⟩
        refine Nat.le_of_lt (?_ : gmoLt GF.gfGd.gdG (x.1, j) x).2.2
        rcases hend with hsw | hdv
        · obtain ⟨b, v, hb, hw, hsp⟩ := hsw
          by_cases hv : v = lockFree
          · subst hv
            obtain ⟨a, ha⟩ := hNF2a b (x.1, j) hb hw hsp.1
            exact absurd ⟨a, b, hb, hw, hsp.1, ha⟩ (CertZ17.ancNone _ Lb _ hanc)
          · obtain ⟨hR, hAq⟩ := hNF2b b _ v hb hw hv hsp
            exact CatLin.acqGmoAfterC _ _ x h6 hpo hR hAq hxm
        · cases hio : gisIo GF.gfGd.gdG (x.1, j) with
          | true =>
            rcases hxkind with hk | hk | hk
            · exact hres (x.1, j) x (.inr (.inl ⟨hpo, hio,
                (CertZ17.lockWIo _ Lb x (CertZ23.spWLockW _ Lb x hk)).2.1⟩))
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

/-! # 3. The key along `R3` -/

/-- The order relation: program order, fabric order, co among SUCCESSFUL lock writes. -/
def CertZ23.R (GF : Gfexec) (Lb : Int → Prop) (x y : Geid) : Prop :=
  (x.1 = y.1 ∧ x.2 < y.2 ∧ CertZ8.evsOf GF.gfGd.gdG.gxProg x ∧ CertZ8.evsOf GF.gfGd.gdG.gxProg y) ∨
  (∃ m n : Nat, GF.gfDev[m]? = some x ∧ GF.gfDev[n]? = some y ∧ m < n) ∨
  (∃ b vx vy, Lb b ∧ gwritesByte GF.gfGd.gdG x b vx ∧ gwritesByte GF.gfGd.gdG y b vy ∧
    CertZ18.sp GF.gfGd.gdG b x ∧ CertZ18.sp GF.gfGd.gdG b y ∧
    gwix GF.gfGd.gdG x < gwix GF.gfGd.gdG y)

noncomputable def CertZ23.key (GF : Gfexec) (Lb : Int → Prop) (e : Geid) : Nat :=
  CertZ23.kap GF Lb e * CertZ17.bnd GF.gfGd.gdG.gxProg + e.2

theorem CertZ23.keyPo (GF : Gfexec) (Lb : Int → Prop) (x y : Geid) :
    x.1 = y.1 → x.2 < y.2 → CertZ23.key GF Lb x < CertZ23.key GF Lb y := by
  intro h1 h2
  have hk := CertZ23.kapMono GF Lb x y h1 (Nat.le_of_lt h2)
  have := Nat.mul_le_mul_right (CertZ17.bnd GF.gfGd.gdG.gxProg) hk
  unfold CertZ23.key
  omega

theorem CertZ23.keyStrict (GF : Gfexec) (Lb : Int → Prop) (x y : Geid) :
    x.2 < CertZ17.bnd GF.gfGd.gdG.gxProg → CertZ23.kap GF Lb x < CertZ23.kap GF Lb y →
    CertZ23.key GF Lb x < CertZ23.key GF Lb y := by
  intro hb hk
  have := Nat.mul_le_mul_right (CertZ17.bnd GF.gfGd.gdG.gxProg)
    (show CertZ23.kap GF Lb x + 1 ≤ _ from hk)
  rw [Nat.add_mul, Nat.one_mul] at this
  unfold CertZ23.key
  omega

theorem CertZ23.gEnd (GF : Gfexec) (Lb : Int → Prop) (e : Geid) :
    CertZ17.anc GF.gfGd.gdG Lb e = none → CertZ23.isEnd GF Lb e →
    CertZ23.g GF Lb e = gpos GF.gfGd.gdG e := by
  intro hn he
  unfold CertZ23.g
  rw [hn]
  dsimp only
  rw [if_pos he]

/-- **THE KEY STRICTLY INCREASES ALONG `R3`.** -/
theorem CertZ23.keyLt (GF : Gfexec) (ad : List (Geid × Geid)) (Lb : Int → Prop) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gfDevWIo GF → CertZ23.lockDisc3 GF Lb →
    (∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome) →
    ∀ x y, CertZ23.R GF Lb x y → CertZ23.key GF Lb x < CertZ23.key GF Lb y := by
  intro hc hres hwio hld hdevL x y hR
  have hwf := hc.1
  have h6 := hc.2.1
  have hld' := hld
  obtain ⟨-, -, hNF2c, hNF1, hNF3a, -⟩ := hld'
  rcases hR with ⟨h1, h2, -, -⟩ | ⟨m, n, hm, hn, hmn⟩ |
      ⟨b, vx, vy, hb, hx, hy, hspx, hspy, hlt⟩
  · exact CertZ23.keyPo GF Lb x y h1 h2
  · have hxd : x ∈ GF.gfDev := List.mem_of_getElem? hm
    have hyd : y ∈ GF.gfDev := List.mem_of_getElem? hn
    have hxy : gmoLt GF.gfGd.gdG x y :=
      hres x y (.inr (.inr (.inr (.inr ⟨WeakRvwmoLin2.wioGmem _ x (hwio x hxd),
        WeakRvwmoLin2.wioGmem _ y (hwio y hyd), m, n, hm, hn, hmn⟩))))
    have hkx := CertZ23.kapLe GF ad Lb hc hres hwio hld hdevL x (.inr hxd)
    have hny : CertZ17.anc GF.gfGd.gdG Lb y = none := by
      cases ha : CertZ17.anc GF.gfGd.gdG Lb y with
      | none => rfl
      | some a =>
        obtain ⟨b, hb, hrel, -, -⟩ := CertZ17.ancSome _ Lb y a ha
        exact absurd hyd (hNF3a y ⟨b, lockFree, hb, hrel⟩)
    have hgy := CertZ23.gEnd GF Lb y hny (.inr hyd)
    have hky := CertZ23.kapSelf GF Lb y
    exact CertZ23.keyStrict GF Lb x y (CertZ17.lblBnd _ x (hdevL x hxd)) (by
      have := hxy.2.2; omega)
  · have hxw := gwritesByteGwrites _ x b vx hwf hx
    have hyw := gwritesByteGwrites _ y b vy hwf hy
    have hxl : (gxLbl GF.gfGd.gdG x).isSome := CertZ17.lockWLbl _ Lb x ⟨b, vx, hb, hx⟩
    have hyl : (gxLbl GF.gfGd.gdG y).isSome := CertZ17.lockWLbl _ Lb y ⟨b, vy, hb, hy⟩
    by_cases hh : x.1 = y.1
    · rcases Nat.lt_trichotomy x.2 y.2 with h | h | h
      · exact CertZ23.keyPo GF Lb x y hh h
      · have := gwixInj _ x y hwf.1 hxw hyw (by
          rw [show x = y from Prod.ext hh h]); rw [this] at hlt; omega
      · have hpo : WeakRvwmoGraph.gpo GF.gfGd.gdG y x := ⟨hh.symm, h, hyl, hxl⟩
        have hmo := h6 y x (Or.inl ⟨hpo, b, Or.inl ⟨vy, hy⟩, vx, hx⟩)
        have := gmoGwixLt _ y x hwf hyw hxw hmo
        omega
    · have hkx := CertZ23.kapLe GF ad Lb hc hres hwio hld hdevL x (.inl ⟨b, vx, hb, hx, hspx⟩)
      have hxy := gwixLtGmo _ x y hwf hxw hyw hlt
      have hgy : gpos GF.gfGd.gdG x < CertZ23.g GF Lb y := by
        cases ha : CertZ17.anc GF.gfGd.gdG Lb y with
        | none =>
          rw [CertZ23.gEnd GF Lb y ha (.inl ⟨b, vy, hb, hy, hspy⟩)]
          exact hxy.2.2
        | some a =>
          obtain ⟨b', hb', hrel, hnpy, hcs⟩ := CertZ17.ancSome _ Lb y a ha
          have hbb : b' = b := hNF2c b' b y lockFree vy hb' hb hrel hy hnpy
          subst hbb
          have hAw := lockAcqGwrites _ b' a hwf hcs.1
          rcases hNF1 b' y a x vx hb' hrel hnpy hcs hx hspx hh with h' | h'
          · unfold CertZ23.g
            rw [ha]
            exact (gwixLtGmo _ x a hwf hxw hAw h').2.2
          · omega
      have hky := CertZ23.kapSelf GF Lb y
      exact CertZ23.keyStrict GF Lb x y (CertZ17.lblBnd _ x hxl) (by omega)

theorem CertZ23.rAcyc (GF : Gfexec) (ad : List (Geid × Geid)) (Lb : Int → Prop) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gfDevWIo GF → CertZ23.lockDisc3 GF Lb →
    (∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome) →
    ∀ x, ¬ tc (CertZ23.R GF Lb) x x := by
  intro hc hres hwio hld hdevL x hx
  have key : ∀ a b, tc (CertZ23.R GF Lb) a b → CertZ23.key GF Lb a < CertZ23.key GF Lb b := by
    intro a b h
    induction h with
    | single h => exact CertZ23.keyLt GF ad Lb hc hres hwio hld hdevL _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (CertZ23.keyLt GF ad Lb hc hres hwio hld hdevL _ _ h)
  exact Nat.lt_irrefl _ (key x x hx)

/-! # 4. The order -/

/-- The order respects co among SUCCESSFUL protocol writes of the lock bytes. -/
def CertZ23.ordCoSP (G : Gexec) (L : List Geid) (Lb : Int → Prop) : Prop :=
  ∀ (b : Int) (x y : Geid) (vx vy : BitVec 8) (i j : Nat), Lb b →
    gwritesByte G x b vx → gwritesByte G y b vy → CertZ18.sp G b x → CertZ18.sp G b y →
    gwix G x < gwix G y → L[i]? = some x → L[j]? = some y → i < j

theorem CertZ23.ordOfDisc (GF : Gfexec) (ad : List (Geid × Geid)) (Lb : Int → Prop) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gfDevWIo GF → CertZ23.lockDisc3 GF Lb →
    (∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome) →
    ∃ L, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L ∧ CertZ23.ordCoSP GF.gfGd.gdG L Lb := by
  intro hc hres hwio hld hdevL
  haveI : DecidableRel (CertZ23.R GF Lb) := fun _ _ => Classical.propDecidable _
  obtain ⟨L, hnd, hmem, hidx⟩ := topoSort (CertZ23.R GF Lb) (CertZ17.evs GF.gfGd.gdG.gxProg)
    (CertZ23.rAcyc GF ad Lb hc hres hwio hld hdevL) (CertZ17.evsNodup _)
  have hmem' : ∀ e, e ∈ L ↔ CertZ8.evsOf GF.gfGd.gdG.gxProg e := fun e => (hmem e).trans
    (CertZ17.memEvs _ e)
  refine ⟨L, ⟨hnd, hmem', fun i j x a b hi hj hab => ?_, fun m n i j e e' hm hn hmn hi hj => ?_⟩,
    fun b x y vx vy i j hb hx hy hsx hsy hlt hi hj => ?_⟩
  · exact hidx i j _ _ hi hj (.inl ⟨rfl, hab, (hmem' _).1 (List.mem_of_getElem? hi),
      (hmem' _).1 (List.mem_of_getElem? hj)⟩)
  · exact hidx i j e e' hi hj (.inr (.inl ⟨m, n, hm, hn, hmn⟩))
  · exact hidx i j x y hi hj (.inr (.inr ⟨b, vx, vy, hb, hx, hy, hsx, hsy, hlt⟩))

/-! # 5. The member's lock co, the supplies -/

/-- **THE FINAL LOCK CO, SUCCESSFUL OPS**: the walk's member agrees with `GF` on co among successful
protocol writes. -/
theorem CertZ23.lockCoOfOrd3 (G : Gexec) (dev L : List Geid) (c : Cand) (Lb : Int → Prop) :
    gwf G → CertZ8.walkOrd G.gxProg dev L → CertZ23.ordCoSP G L Lb →
    c.cdTr.map Estep.esAg = L.map Prod.fst →
    (∀ s, s ∈ c.cdTr → s.esAg < G.gxProg.length) →
    (∀ x, x < G.gxProg.length →
      List.Forall₂ lblReidxW (G.gxProg.getD x []) (CertZ2.hartTr c.cdTr x)) →
    CertZ18.lockCoSP G (CertZ3.member G.gxProg.length c) Lb := by
  intro hwf hord hco hags hag hrows b x y vx vy hb hx hy hsx hsy
  obtain ⟨i, j, hi, hj, key⟩ :=
    CertZ16.memberIffOrd G dev L c b x y vx vy hwf hord hags hag hrows hx hy
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

namespace CatLin

/-- **THE NAMED LOCK DISCIPLINE (successful ops), W11-F per pc.** -/
def lockDiscCZ3 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    CertZ23.lockDisc3 GF (GraphFetchN2.lockBytes P)

/-- **THE ORDER SUPPLY at successful-protocol co.** -/
def orderSupplyCZ3 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF →
    ∃ L, CertZ8.walkOrd GF.gfGd.gdG.gxProg GF.gfDev L ∧
      CertZ23.ordCoSP GF.gfGd.gdG L (GraphFetchN2.lockBytes P)

/-- **`orderSupplyOfDisc3` — the order DERIVED** from the lock discipline and `gfDevWIo`. -/
theorem orderSupplyOfDisc3 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (P : Int → Int → Prop) :
    lockDiscCZ3 boot d0 fab im P → gfDevWIoCZ boot d0 fab im → orderSupplyCZ3 boot d0 fab im P := by
  intro hld hwio GF ad him hc hconf hres
  have hdevL : ∀ e, e ∈ GF.gfDev → (gxLbl GF.gfGd.gdG e).isSome := by
    intro e he
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨i, k⟩ := e
    obtain ⟨row, hrow, hk⟩ := hconf.2.2.1 n i k hn
    unfold gxLbl
    simp only [hrow, Option.bind_some]
    exact lookup_lt_is_Some_2 hk
  exact CertZ23.ordOfDisc GF ad _ hc hres (hwio GF ad him hc hconf) (hld GF ad him hc hconf) hdevL

/-- The walk supply with the final member at successful-protocol co. -/
def walkSupplyCZ3 (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image) (N : Nat)
    (P : Int → Int → Prop) : Prop :=
  ∀ (GF : Gfexec) (ad : List (Geid × Geid)) (z : Geid) (ss : List Seg),
    GF.gfGd.gdG.gxImg = im → rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
    ioResidueGmo GF → gdiskRead14 GF.gfGd.gdG →
    ss ≠ [] → rawChainC GF.gfGd (ioCross GF) z z ss →
    ∃ Inv : CertZ2.WInv,
      (∀ itvOf fiOf, CertZ.cstOkZW d0 (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf →
        Inv (wlkStart boot d0 N GF.gfGd.gdG) itvOf fiOf (fun _ => 0)) ∧
      CertZ2.walkPolZ d0 GF.gfGd.gdG.gxProg Inv ∧
      (∀ Sf itvOf fiOf cntF, Inv Sf itvOf fiOf cntF → CertZ.cstOkZW d0 Sf itvOf fiOf →
        (∀ x, x < GF.gfGd.gdG.gxProg.length →
          (GF.gfGd.gdG.gxProg.getD x []).length ≤ cntF x) →
        CertZ18.lockCoSP GF.gfGd.gdG
          (CertZ3.member GF.gfGd.gdG.gxProg.length Sf.cstC) (GraphFetchN2.lockBytes P))

/-- (G-3) at a successful-protocol member from the free walk, its RMW atomicity included. -/
theorem certSupplyCZROfWalkSP (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (N : Nat) (P : Int → Int → Prop) :
    walkSupplyCZ3 boot d0 fab im N P → certSupplyCZR3 boot d0 fab im N P := by
  intro hws GF ad _ z ss him hc hconf hres hdr _ _ _ _ _ hne hch
  obtain ⟨Inv, hI0, hpol, hco⟩ := hws GF ad z ss him hc hconf hres hdr hne hch
  have hstart := wlkStartInvZ boot d0 N GF.gfGd.gdG
  obtain ⟨itv0, fi0, hok0⟩ := CertZ.cstOkZWOf d0 _ hstart.1
  obtain ⟨_, Sf, itvF, fiF, cntF, tradd, hrun, hokF, hinvF, hdone, -, htr, hf2, hagt, himg,
    hpst⟩ := CertZ2.walkRunZ d0 GF.gfGd.gdG.gxProg Inv hpol _ (wlkStart boot d0 N GF.gfGd.gdG) itv0 fi0
      (fun _ => 0) (Nat.le_refl _) hok0 (hI0 itv0 fi0 hok0)
  have htr' : Sf.cstC.cdTr = tradd := by rw [htr]; rfl
  have hagS : ∀ s, s ∈ Sf.cstC.cdTr → s.esAg < GF.gfGd.gdG.gxProg.length := by
    rw [htr']; exact hagt
  have hcons := hokF.1
  refine ⟨Sf.cstC, Sf.cstPst, Sf.cstDv, CertZ3.member GF.gfGd.gdG.gxProg.length Sf.cstC, fun t => t,
    runDataZOfCyc boot d0 N GF.gfGd.gdG Sf (CertZ.cstOkZOfW _ _ _ _ hokF) (by rw [himg]; rfl)
      (by rw [hpst]; rfl),
    ?_, CertZ3.memberGwf _ _ hcons hagS,
    ⟨show Sf.cstC.cdImg = _ by rw [himg]; rfl, ?_, hco Sf itvF fiF cntF hinvF hokF hdone⟩,
    CertZ3.memberGwrowGmo _ _ hagS, CertZ20.memberRmwLatest _ _ hcons hagS⟩
  · have := CertZ3.memberLogPfx GF.gfGd.gdG.gxProg.length Sf.cstC hcons hagS
    exact logOfOfPfx _ _ this
  · show List.Forall₂ _ GF.gfGd.gdG.gxProg ((List.range' 0 GF.gfGd.gdG.gxProg.length).map _)
    refine CertZ3.forall₂Range _ _ GF.gfGd.gdG.gxProg 0 (fun x row hx => ?_)
    rw [Nat.zero_add, htr']
    have hfx := hf2 x
    have hlen : (GF.gfGd.gdG.gxProg.getD x []).length ≤ cntF x := hdone x (lookup_lt_Some hx)
    rw [List.getD_eq_getElem?_getD, hx, Option.getD_some] at hfx hlen
    rw [List.drop_zero, Nat.sub_zero, List.take_of_length_le hlen] at hfx
    have hre : List.Forall₂ (fun l l' => lblReidxW (lblRen (fun t => t) l) l') row
        (CertZ2.hartTr tradd x) := by
      refine List.Forall₂.imp (fun {l l'} h => ?_) hfx
      rw [lblRenId]; exact h
    exact hre

end CatLin

end Weak
