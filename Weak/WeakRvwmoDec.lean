/-
Weak: **`racyD` IS DECIDABLE, so the topological sort needs no side condition**
(route-b §4d.1 F2(ii); `WeakRvwmoTopo`'s header, open item (D)).

Rocq: `iris/WeakRvwmoDec.v` @ xxvzwolszwmp.

The Rocq header, in substance.  The minimal-element search of a finite
topological sort cannot pick a minimum constructively without deciding the
relation, so `WeakRvwmoTopo.topoExists` and `normalizeOfAcyclic` were stated
with an explicit hypothesis `∀ x y, Decidable (racyD GD x y)`.  THIS FILE
DISCHARGES IT — constructively, with no classical reasoning.  Every existential
inside `WeakRvwmoAcyc`'s relation is pinned by a row lookup or a list position,
so each arm is a BOUNDED search:

  - `gwrBytes` / `grdBytes` enumerate an event's write/read byte entries off
    its label (`gwritesByte` / `greadsByte` become list membership —
    `gwritesByteBytes` / `greadsByteBytes`);
  - `gaccAddrs` enumerates the addresses an event touches, so `gaccesses`'
    address existential (and `gpoloc`'s "∃ a") is a search over a list rather
    than over `Int`;
  - `gfenceCovers`' "∃ pr pw sr sw" is NOT searched over the sixteen bit
    patterns: the fence's position `kf` DETERMINES the label and hence the four
    bits, so `gfcovAt` reads them off `gxLbl` and the only search left is over
    `kf ∈ List.range' (e1.2 + 1) (e2.2 - (e1.2 + 1))`;
  - `gwriteAt`, `gwix`, `gpos` are functions; `gmoLt` and the dep set are list
    membership.

The reformulations are stated as `↔`s (`gpolocAlt`, `gfenceCoversAlt`,
`grfAlt`, `gcoAlt`, `gfrAlt`) and turned into instances by `decIff`, so
nothing here changes the model.

Delivered: `racyDDec`, and `topoExists'` / `normalizeOfAcyclic'` —
`WeakRvwmoTopo`'s two theorems with the `Decidable` hypothesis removed.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The Rocq names of
   this file listed in `notes/weak-port-dupnames.json` (`glbl_is_dec`,
   `gmem_dec`, `gpo_dec`, `gmo_lt_dec`, `grf_dec`) are FILE-QUALIFIED
   (`WeakRvwmoDec.glblIsDec`, …).  `Racy`/`RacyD` are `WeakRvwmoAcyc`'s
   `racy`/`racyD`; Rocq's `grf` is `WeakRvwmoAcyc.grf`, `gpo` is
   `WeakRvwmoGraph.gpo`.
2. VOCABULARY: `Decision` ↦ `Decidable` (`left`/`right` ↦ `isTrue`/`isFalse`);
   `imap` ↦ `List.mapIdx`; `zip` ↦ `List.zip`; `seq s n` ↦ `List.range' s n`;
   `x ≫= f` ↦ `Option.bind`.  The read-byte triple keeps Rocq's LEFT-nested
   product `(Int × Nat) × BitVec 8` (`Z * nat * bv 8`), so the projections
   `x.1.1` / `x.1.2` / `x.2` are Rocq's.
3. The instances are global `instance`s (Rocq `Global Instance`); they are
   transparent `def`-level terms (Rocq closes some with `Qed`), which only makes
   them more usable (`decide` can evaluate them).
4. `list_exists_dec` takes `l` explicitly as in Rocq; it is a `def` (its result
   is data).

**Name map** (Rocq → Lean): `dec_iff` ↦ `decIff`; `list_exists_dec` ↦
`listExistsDec`; `lookup_zip` ↦ `lookupZip`; `gwr_bytes` ↦ `gwrBytes`;
`grd_bytes` ↦ `grdBytes`; `gwrites_byte_bytes` ↦ `gwritesByteBytes`;
`greads_byte_bytes` ↦ `greadsByteBytes`; `gacc_addrs` ↦ `gaccAddrs`;
`gaccesses_addrs` ↦ `gaccessesAddrs`; `gwrites_byte_dec` ↦ `gwritesByteDec`;
`greads_byte_dec` ↦ `greadsByteDec`; `gaccesses_dec` ↦ `gaccessesDec`;
`glbl_is_dec` ↦ `WeakRvwmoDec.glblIsDec`; `gmem_dec` ↦ `WeakRvwmoDec.gmemDec`;
`gpo_dec` ↦ `WeakRvwmoDec.gpoDec`; `gmo_lt_dec` ↦ `WeakRvwmoDec.gmoLtDec`;
`gpow_dec` ↦ `gpowDec`; `gacq_po_dec` ↦ `gacqPoDec`; `grel_acq_dec` ↦
`grelAcqDec`; `gpoloc_alt` ↦ `gpolocAlt`; `gpoloc_dec` ↦ `gpolocDec`;
`gfcov_at` ↦ `gfcovAt`; `gfcov_at_dec` ↦ `gfcovAtDec`; `gfence_covers_alt` ↦
`gfenceCoversAlt`; `gfence_covers_dec` ↦ `gfenceCoversDec`; `gppo_dec` ↦
`gppoDec`; `grf_alt` ↦ `grfAlt`; `grf_dec` ↦ `WeakRvwmoDec.grfDec`; `gco_alt`
↦ `gcoAlt`; `gco_dec` ↦ `gcoDec`; `gfr_alt` ↦ `gfrAlt`; `gfr_dec` ↦ `gfrDec`;
`racy_dec` ↦ `racyDec`; `racyD_dec` ↦ `racyDDec`; `topo_exists'` ↦
`topoExists'`; `normalize_of_acyclic'` ↦ `normalizeOfAcyclic'`.

**Not ported:** nothing (the three `Print Assumptions` are commands, not
declarations).
-/
import Weak.WeakMem
import Weak.WeakAxiomatic
import Weak.WeakAxiomatic2
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoXchg
import Weak.WeakRvwmoNorm
import Weak.WeakRvwmoAcyc
import Weak.WeakRvwmoTopo

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. Two generic tools -/

/-- Transport a decision along an equivalence. -/
def decIff {P Q : Prop} (H : P ↔ Q) (d : Decidable Q) : Decidable P :=
  match d with
  | isTrue h => isTrue (H.2 h)
  | isFalse h => isFalse (fun p => h (H.1 p))

/-- Bounded search over a list — `WeakRvwmoTopo.listExDec` in `Decidable`
clothing. -/
def listExistsDec {A : Type _} (P : A → Prop) (Pdec : ∀ x, Decidable (P x))
    (l : List A) : Decidable (∃ x, x ∈ l ∧ P x) :=
  match listExDec P Pdec l with
  | .inl ⟨x, hx, hp⟩ => isTrue ⟨x, hx, hp⟩
  | .inr hno => isFalse (fun ⟨x, hx, hp⟩ => hno x hx hp)

/-- `zip`'s lookup, in the shape the read-byte enumeration wants. -/
theorem lookupZip {A B : Type _} (l : List A) (k : List B) (j : Nat) (x : A) (y : B) :
    (l.zip k)[j]? = some (x, y) ↔ l[j]? = some x ∧ k[j]? = some y := by
  rw [List.getElem?_zip_eq_some]

/-! # 2. THE BYTE ENUMERATIONS

An event's byte footprint is a function of its label, so both `gwritesByte`
and `greadsByte` are list membership. -/

def gwrBytes (G : Gexec) (e : Geid) : List (Int × BitVec 8) :=
  match (gxLbl G e).bind lbWr with
  | some (base, vs) => vs.mapIdx (fun j v => (accAddr base j, v))
  | none => []

def grdBytes (G : Gexec) (e : Geid) : List ((Int × Nat) × BitVec 8) :=
  match (gxLbl G e).bind lbRd with
  | some (base, ts, vs) =>
      (ts.zip vs).mapIdx (fun j tv => ((accAddr base j, tv.1), tv.2))
  | none => []

theorem gwritesByteBytes (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G e a v ↔ (a, v) ∈ gwrBytes G e := by
  unfold gwritesByte gwrBytes
  cases hl : gxLbl G e with
  | none => simp
  | some l =>
    cases hw : lbWr l with
    | none => simp [hw]
    | some p =>
      obtain ⟨base, vs⟩ := p
      simp only [Option.bind_some, hw]
      rw [List.mem_iff_getElem?]
      constructor
      · rintro ⟨l0, base0, vs0, j, hl0, hw0, hv, ha⟩
        cases hl0
        rw [hw] at hw0
        cases hw0
        exact ⟨j, by simp [List.getElem?_mapIdx, hv, ha]⟩
      · rintro ⟨j, hj⟩
        rw [List.getElem?_mapIdx] at hj
        cases hv : vs[j]? with
        | none => simp [hv] at hj
        | some v0 =>
          simp only [hv, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hj
          obtain ⟨ha, rfl⟩ := hj
          exact ⟨l, base, vs, j, rfl, hw, hv, ha⟩

theorem greadsByteBytes (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G e a t v ↔ ((a, t), v) ∈ grdBytes G e := by
  unfold greadsByte grdBytes
  cases hl : gxLbl G e with
  | none => simp
  | some l =>
    cases hr : lbRd l with
    | none => simp [hr]
    | some p =>
      obtain ⟨base, ts, vs⟩ := p
      simp only [Option.bind_some, hr]
      rw [List.mem_iff_getElem?]
      constructor
      · rintro ⟨l0, base0, ts0, vs0, j, hl0, hr0, ht, hv, ha⟩
        cases hl0
        rw [hr] at hr0
        cases hr0
        refine ⟨j, ?_⟩
        rw [List.getElem?_mapIdx, (lookupZip ts vs j t v).2 ⟨ht, hv⟩]
        simp [ha]
      · rintro ⟨j, hj⟩
        rw [List.getElem?_mapIdx] at hj
        cases hz : (ts.zip vs)[j]? with
        | none => simp [hz] at hj
        | some tv =>
          obtain ⟨t0, v0⟩ := tv
          simp only [hz, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hj
          obtain ⟨⟨ha, rfl⟩, rfl⟩ := hj
          obtain ⟨ht, hv⟩ := (lookupZip ts vs j t0 v0).1 hz
          exact ⟨l, base, ts, vs, j, rfl, hr, ht, hv, ha⟩

/-- The addresses an event touches. -/
def gaccAddrs (G : Gexec) (e : Geid) : List Int :=
  (gwrBytes G e).map (fun x : Int × BitVec 8 => x.1) ++
  (grdBytes G e).map (fun x : (Int × Nat) × BitVec 8 => x.1.1)

theorem gaccessesAddrs (G : Gexec) (e : Geid) (a : Int) :
    gaccesses G e a ↔ a ∈ gaccAddrs G e := by
  unfold gaccesses gaccAddrs
  rw [List.mem_append, List.mem_map, List.mem_map]
  constructor
  · rintro (⟨v, hw⟩ | ⟨t, v, hr⟩)
    · exact Or.inl ⟨(a, v), (gwritesByteBytes G e a v).1 hw, rfl⟩
    · exact Or.inr ⟨((a, t), v), (greadsByteBytes G e a t v).1 hr, rfl⟩
  · rintro (⟨⟨a0, v⟩, hx, ha⟩ | ⟨⟨⟨a0, t⟩, v⟩, hx, ha⟩)
    · cases ha
      exact Or.inl ⟨v, (gwritesByteBytes G e a0 v).2 hx⟩
    · cases ha
      exact Or.inr ⟨t, v, (greadsByteBytes G e a0 t v).2 hx⟩

/-! # 3. THE ELEMENTARY DECISIONS -/

instance gwritesByteDec (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    Decidable (gwritesByte G e a v) :=
  decIff (gwritesByteBytes G e a v) inferInstance

instance greadsByteDec (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    Decidable (greadsByte G e a t v) :=
  decIff (greadsByteBytes G e a t v) inferInstance

instance gaccessesDec (G : Gexec) (e : Geid) (a : Int) : Decidable (gaccesses G e a) :=
  decIff (gaccessesAddrs G e a) inferInstance

instance WeakRvwmoDec.glblIsDec (G : Gexec) (e : Geid) (P : Lbl → Bool) :
    Decidable (glblIs G e P) :=
  match h : gxLbl G e with
  | some l =>
    if hP : P l = true then isTrue ⟨l, h, hP⟩
    else isFalse (fun ⟨l0, hl0, hP0⟩ => hP (by rw [h] at hl0; cases hl0; exact hP0))
  | none => isFalse (fun ⟨l0, hl0, _⟩ => by rw [h] at hl0; cases hl0)

/-- `gmem` IS `glblIs _ _ lbIsMem`, definitionally. -/
instance WeakRvwmoDec.gmemDec (G : Gexec) (e : Geid) : Decidable (gmem G e) :=
  WeakRvwmoDec.glblIsDec G e lbIsMem

instance WeakRvwmoDec.gpoDec (G : Gexec) (x y : Geid) :
    Decidable (WeakRvwmoGraph.gpo G x y) := by
  unfold WeakRvwmoGraph.gpo; infer_instance

instance WeakRvwmoDec.gmoLtDec (G : Gexec) (x y : Geid) : Decidable (gmoLt G x y) := by
  unfold gmoLt; infer_instance

instance gpowDec (G : Gexec) (e w : Geid) : Decidable (gpow G e w) := by
  unfold gpow; infer_instance

instance gacqPoDec (G : Gexec) (e1 e2 : Geid) : Decidable (gacqPo G e1 e2) := by
  unfold gacqPo; infer_instance

instance grelAcqDec (G : Gexec) (e1 e2 : Geid) : Decidable (grelAcq G e1 e2) := by
  unfold grelAcq; infer_instance

/-! # 4. THE ARMS THAT NEEDED A REFORMULATION -/

/-! ## 4.1 `gpoloc`: the "∃ a" is a search over `Int` as written. -/

theorem gpolocAlt (G : Gexec) (e1 e2 : Geid) :
    gpoloc G e1 e2 ↔
    WeakRvwmoGraph.gpo G e1 e2 ∧ ∃ a, a ∈ gaccAddrs G e1 ∧ gaccesses G e2 a := by
  unfold gpoloc
  constructor
  · rintro ⟨hpo, a, h1, h2⟩
    exact ⟨hpo, a, (gaccessesAddrs G e1 a).1 h1, h2⟩
  · rintro ⟨hpo, a, h1, h2⟩
    exact ⟨hpo, a, (gaccessesAddrs G e1 a).2 h1, h2⟩

instance gpolocDec (G : Gexec) (e1 e2 : Geid) : Decidable (gpoloc G e1 e2) :=
  decIff (gpolocAlt G e1 e2)
    (@instDecidableAnd _ _ inferInstance
      (listExistsDec _ (fun a => inferInstance) (gaccAddrs G e1)))

/-! ## 4.2 `gfenceCovers`: the four bits are DETERMINED by the fence's
position, so only the position is searched. -/

def gfcovAt (G : Gexec) (e1 e2 : Geid) (kf : Nat) : Prop :=
  match gxLbl G (e1.1, kf) with
  | some (LFence pr pw sr sw) =>
      ((glblIs G e1 lbIsR ∧ pr = true) ∨
       (glblIs G e1 lbIsW ∧ pw = true)) ∧
      ((glblIs G e2 lbIsR ∧ sr = true) ∨
       (glblIs G e2 lbIsW ∧ sw = true))
  | _ => False

instance gfcovAtDec (G : Gexec) (e1 e2 : Geid) (kf : Nat) : Decidable (gfcovAt G e1 e2 kf) := by
  unfold gfcovAt
  split <;> infer_instance

theorem gfenceCoversAlt (G : Gexec) (e1 e2 : Geid) :
    gfenceCovers G e1 e2 ↔
    e1.1 = e2.1 ∧ e1.2 < e2.2 ∧
    ∃ kf, kf ∈ List.range' (e1.2 + 1) (e2.2 - (e1.2 + 1)) ∧ gfcovAt G e1 e2 kf := by
  unfold gfenceCovers gfenceBetween gfcovAt
  constructor
  · rintro ⟨pr, pw, sr, sw, ⟨hag, hlt, kf, hk1, hk2, hlf⟩, c1, c2⟩
    refine ⟨hag, hlt, kf, ?_, ?_⟩
    · rw [List.mem_range'_1]; omega
    · rw [hlf]; exact ⟨c1, c2⟩
  · rintro ⟨hag, hlt, kf, hkf, hcov⟩
    rw [List.mem_range'_1] at hkf
    revert hcov
    cases hl : gxLbl G (e1.1, kf) with
    | none => intro h; exact h.elim
    | some l =>
      cases l with
      | LFence pr pw sr sw =>
        rintro ⟨c1, c2⟩
        exact ⟨pr, pw, sr, sw, ⟨hag, hlt, kf, by omega, by omega, hl⟩, c1, c2⟩
      | _ => intro h; exact h.elim

instance gfenceCoversDec (G : Gexec) (e1 e2 : Geid) : Decidable (gfenceCovers G e1 e2) :=
  decIff (gfenceCoversAlt G e1 e2)
    (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ inferInstance
        (listExistsDec _ (fun kf => inferInstance) _)))

instance gppoDec (G : Gexec) (e1 e2 : Geid) : Decidable (gppo G e1 e2) := by
  unfold gppo; infer_instance

/-! ## 4.3 `grf` / `gco` / `gfr`: the byte existentials -/

theorem grfAlt (G : Gexec) (w r : Geid) :
    WeakRvwmoAcyc.grf G w r ↔ ∃ x, x ∈ grdBytes G r ∧ gwriteAt G x.1.2 = some w := by
  unfold WeakRvwmoAcyc.grf
  constructor
  · rintro ⟨a, t, v, hrd, hat⟩
    exact ⟨((a, t), v), (greadsByteBytes G r a t v).1 hrd, hat⟩
  · rintro ⟨⟨⟨a, t⟩, v⟩, hx, hat⟩
    exact ⟨a, t, v, (greadsByteBytes G r a t v).2 hx, hat⟩

instance WeakRvwmoDec.grfDec (G : Gexec) (w r : Geid) : Decidable (WeakRvwmoAcyc.grf G w r) :=
  decIff (grfAlt G w r) (listExistsDec _ (fun x => inferInstance) _)

theorem gcoAlt (G : Gexec) (w w' : Geid) :
    gco G w w' ↔
    gwix G w < gwix G w' ∧
    ∃ x, x ∈ gwrBytes G w ∧ ∃ y, y ∈ gwrBytes G w' ∧ y.1 = x.1 := by
  unfold gco
  constructor
  · rintro ⟨a, v, v', h1, h2, hlt⟩
    exact ⟨hlt, (a, v), (gwritesByteBytes G w a v).1 h1,
      (a, v'), (gwritesByteBytes G w' a v').1 h2, rfl⟩
  · rintro ⟨hlt, ⟨a, v⟩, hx, ⟨a', v'⟩, hy, heq⟩
    cases heq
    exact ⟨a, v, v', (gwritesByteBytes G w a v).2 hx, (gwritesByteBytes G w' a v').2 hy, hlt⟩

instance gcoDec (G : Gexec) (w w' : Geid) : Decidable (gco G w w') :=
  decIff (gcoAlt G w w')
    (@instDecidableAnd _ _ inferInstance
      (listExistsDec _ (fun x => listExistsDec _ (fun y => inferInstance) _) _))

theorem gfrAlt (G : Gexec) (r w' : Geid) :
    gfr G r w' ↔
    r ≠ w' ∧ ∃ x, x ∈ grdBytes G r ∧ x.1.2 < gwix G w' ∧
                  ∃ y, y ∈ gwrBytes G w' ∧ y.1 = x.1.1 := by
  unfold gfr
  constructor
  · rintro ⟨hne, a, t, v, v', hrd, hwb, hlt⟩
    exact ⟨hne, ((a, t), v), (greadsByteBytes G r a t v).1 hrd, hlt,
      (a, v'), (gwritesByteBytes G w' a v').1 hwb, rfl⟩
  · rintro ⟨hne, ⟨⟨a, t⟩, v⟩, hx, hlt, ⟨a', v'⟩, hy, heq⟩
    cases heq
    exact ⟨hne, a, t, v, v', (greadsByteBytes G r a t v).2 hx,
      (gwritesByteBytes G w' a v').2 hy, hlt⟩

instance gfrDec (G : Gexec) (r w' : Geid) : Decidable (gfr G r w') :=
  decIff (gfrAlt G r w')
    (@instDecidableAnd _ _ inferInstance
      (listExistsDec _ (fun x => @instDecidableAnd _ _ inferInstance
        (listExistsDec _ (fun y => inferInstance) _)) _))

/-! # 5. THE THEOREM -/

instance racyDec (G : Gexec) (x y : Geid) : Decidable (racy G x y) := by
  unfold racy; infer_instance

instance racyDDec (GD : Gdexec) (x y : Geid) : Decidable (racyD GD x y) := by
  unfold racyD; infer_instance

/-! # 6. `WeakRvwmoTopo`'s theorems, hypothesis-free -/

theorem topoExists' (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    (∀ x, ¬ tc (racyD GD) x x) →
    ∃ L, linExtD GD L := by
  intro hcons hacy
  exact topoExists GD hcons (fun x y => inferInstance) hacy

theorem normalizeOfAcyclic' (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD →
    (∀ x, ¬ tc (racyD GD) x x) →
    ∃ (GD' : Gdexec) (pi : Nat → Nat),
      rvwmoMinusDepsConsistent GD' ∧
      grule14 GD'.gdG ∧
      rowsRel pi GD.gdG GD'.gdG ∧
      GD'.gdDeps = GD.gdDeps ∧
      wperm pi GD.gdG GD'.gdG := by
  intro hcons hacy
  exact normalizeOfAcyclic GD hcons (fun x y => inferInstance) hacy

end Weak
