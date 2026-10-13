/-
Weak: **rule-14 linearizability ⇒ R acyclic** (route-b §4d.1 F2, corrected:
R includes co and fr — B2d's K3/K2 shapes).

Rocq: `iris/WeakRvwmoAcyc.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-route-b.md`
§4d.1 F2 and §4d.4 "B2e-3a (i)", with the orchestrator's scope correction).  The
obligation relation is not `po ∪ rf` but the full herd-style union

  `racy` := po-into-a-write ∪ rf ∪ co ∪ fr ∪ ppo⁻          (§2)

(and, over a `Gdexec`, the store-dep fragment as well — `racyD`).  Every arm is
gmo-forward in a rule-14 consistent graph, and `gmoLt` is a STRICT ORDER, so
acyclicity is immediate:

  `rGmo`     : rvwmoMinusConsistent G → grule14 G → racy G x y → gmoLt G x y
  `rAcyclic` : … → tc (racy G) x x → False                     (THE THEOREM)
  `rdGmo` / `rdAcyclic`                       — the same over a `Gdexec`.

Also delivered, because `po ∪ rf` is NOT a sub-relation of `racy` (a po edge into
a READ is in neither): `gcausAcyclic`, by its own induction — a causality path
from a reflexive-po prefix of a memory event to a WRITE is gmo-forward
(`causWriteGmo`); a cycle carries a write (`causWriteOnPath`); rotate to it.

THREE STATEMENT CORRECTIONS (recorded in Rocq): (1) `gpow` carries `gmem` of its
source (a fence is not in gmo); (2) `gfr` is BYTE-MATCHED; (3) `gfr` EXCLUDES THE
IDENTITY (a fused RMW reads byte `a` at `t` and writes it at `gwix > t`).

TRANSPORT along `rowsRel` / `wperm` (`WeakRvwmoNorm` §3) — §5: `gpo`, `gpow`,
`grf`, `gppo`, `gcaus` transport (`gcausAcyclicOrbit` / `rtAcyclicOrbit`).
NEGATIVE RESULT: `gco`/`gfr` do NOT transport (π is merely injective; the
co-order of unread same-byte writes is unconstrained), so they are stated under
an explicit monotonicity hypothesis (`gcoRowsRelMono`, `gfrRowsRelMono`) and the
unconditional orbit corollary is for `rt := gpow ∪ grf ∪ gppo` only.

A LEAF: nothing imports this file.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The four Rocq
   names of this file in `notes/weak-port-dupnames.json` (`gis_w_glbl_is`,
   `gis_w_gmem`, `grf`, `grf_gmo`) are FILE-QUALIFIED
   (`WeakRvwmoAcyc.gisWGlblIs`, …).  The `WeakRvwmoGraph` duplicates used are
   referred to qualified (`WeakRvwmoGraph.gpo`, `WeakRvwmoGraph.glblIsWGmem`,
   `WeakRvwmoGraph.gwritesByteGisW`).  The Prop-valued definitions `Racy`,
   `RacyD`, `Rt` are `racy`, `racyD`, `rt`, and the lemma names built on them
   start lowercase (`R_gmo` ↦ `rGmo`, `RD_acyclic` ↦ `rdAcyclic`, …).
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`l !! i` ↦ `l[i]?`, `S n` ↦
   `n + 1`, `f <$> l` ↦ `l.map f`, `NoDup` ↦ `List.Nodup`).
3. CLOSURE INDUCTIONS: the library `tc` splits at the LAST step (`MachCSL.Rel`
   deviation 1).  `causWriteGmo` and `causWriteOnPath` need Rocq's head-style
   induction and go through the Lean-only helpers `tcHeadDecomp` (a `tc` path
   has a first step) and `tcHeadInd` (head induction toward a fixed end);
   `tcMono`, `tcRGmo`, `tcRdGmo` use the tail induction directly (same
   statements, mirrored proofs).
4. PROOFS: `gpowRowsRel`, `gcausRowsRel`, `rowsRelGppo`, `rowsRelGfb` and
   `rowsRelFence` rewrite with the transport iffs instead of Rocq's
   arm-by-arm case analysis (same statements).

**Name map** (Rocq → Lean): `gis_w_glbl_is` ↦ `WeakRvwmoAcyc.gisWGlblIs`;
`gis_w_gmem` ↦ `WeakRvwmoAcyc.gisWGmem`; `gwrite_at_gwrites` ↦
`gwriteAtGwrites`; `gwrites_byte_in_gwrites` ↦ `gwritesByteInGwrites`;
`gwrites_byte_gmo` ↦ `gwritesByteGmo`; `greads_byte_gmo` ↦ `greadsByteGmo`;
`gpo_irrefl` ↦ `gpoIrrefl`; `gpo_trans` ↦ `gpoTrans`; `tc_mono` ↦ `tcMono`;
`grf` ↦ `WeakRvwmoAcyc.grf`; `gcaus`; `gco`; `gfr`; `gpow`; `Racy` ↦ `racy`;
`RacyD` ↦ `racyD`; `Rt` ↦ `rt`; `Rt_Racy` ↦ `rtRacy`; `grf_gmo` ↦
`WeakRvwmoAcyc.grfGmo`; `grf_gis_w` ↦ `grfGisW`; `grf_gmem_r` ↦ `grfGmemR`;
`gco_gmo` ↦ `gcoGmo`; `gfr_gmo` ↦ `gfrGmo`; `rule14_po_write` ↦
`rule14PoWrite`; `R_gmo` ↦ `rGmo`; `RD_gmo` ↦ `rdGmo`; `tc_R_gmo` ↦ `tcRGmo`;
`R_acyclic` ↦ `rAcyclic`; `tc_RD_gmo` ↦ `tcRdGmo`; `RD_acyclic` ↦ `rdAcyclic`;
`Rt_acyclic` ↦ `rtAcyclic`; `caus_write_gmo` ↦ `causWriteGmo`;
`caus_write_on_path` ↦ `causWriteOnPath`; `gcaus_acyclic` ↦ `gcausAcyclic`;
`caus_cycle_gviol` ↦ `causCycleGviol`; `lbl_ren_rd_inv` ↦ `lblRenRdInv`;
`rows_rel_rdb_inv` ↦ `rowsRelRdbInv`; `grf_rows_rel` ↦ `grfRowsRel`;
`gpow_rows_rel` ↦ `gpowRowsRel`; `gcaus_rows_rel` ↦ `gcausRowsRel`;
`rows_rel_gaccesses` ↦ `rowsRelGaccesses`; `rows_rel_fence` ↦
`rowsRelFence`; `rows_rel_gfb` ↦ `rowsRelGfb`; `rows_rel_gppo` ↦
`rowsRelGppo`; `gco_rows_rel_mono` ↦ `gcoRowsRelMono`; `gfr_rows_rel_mono` ↦
`gfrRowsRelMono`; `tc_gcaus_rows_rel` ↦ `tcGcausRowsRel`;
`gcaus_acyclic_orbit` ↦ `gcausAcyclicOrbit`; `Rt_rows_rel` ↦ `rtRowsRel`;
`Rt_acyclic_orbit` ↦ `rtAcyclicOrbit`.  Lean-only helpers (no Rocq twin):
`tcHeadDecomp`, `tcHeadInd` (deviation 3).

**Not ported:** nothing.

**W13 (K) (plan §C W13 (K); Lean-only, no Rocq twin).**  `racyDX GD X := racyD GD ∪ X`, the
parametric extension the I/O-aware normalization consumes (`WeakRvwmoTopo.normalizeOfAcyclicX`);
the I/O instance `racyDIO` is `WeakRvwmoKillIO`'s (its arms name the fabric bundle, downstream of
this file).  `racyD` itself is unchanged.
-/
import Weak.WeakMem
import Weak.WeakAxiomatic
import Weak.WeakAxiomatic2
import Weak.WeakRvwmoGraph
import Weak.WeakRvwmoXchg
import Weak.WeakRvwmoNorm

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. Small bridges the graph file does not export -/

/-- `gisW` is a `match` on `gxLbl`, so it certifies its own `some`. -/
theorem WeakRvwmoAcyc.gisWGlblIs (G : Gexec) (e : Geid) :
    gisW G e = true → glblIs G e lbIsW := by
  intro hw
  cases hl : gxLbl G e with
  | none => simp only [gisW, hl] at hw; cases hw
  | some l =>
    simp only [gisW, hl] at hw
    exact ⟨l, hl, hw⟩

theorem WeakRvwmoAcyc.gisWGmem (G : Gexec) (e : Geid) : gisW G e = true → gmem G e :=
  fun hw => WeakRvwmoGraph.glblIsWGmem G e (WeakRvwmoAcyc.gisWGlblIs G e hw)

/-- A named write index denotes a member of the write sub-order. -/
theorem gwriteAtGwrites (G : Gexec) (t : Nat) (w : Geid) :
    gwriteAt G t = some w → w ∈ gwrites G := by
  cases t with
  | zero => intro h; simp [gwriteAt] at h
  | succ i => intro h; exact gwritesLookupElem G i w h

theorem gwritesByteInGwrites (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwf G → gwritesByte G e a v → e ∈ gwrites G := by
  intro hwf hw
  exact (gwritesElemOf G e).2
    ⟨gwfMemGmo G e hwf (gaccessesGmem G e a (Or.inl ⟨v, hw⟩)),
     WeakRvwmoGraph.gwritesByteGisW G e a v hw⟩

theorem gwritesByteGmo (G : Gexec) (e : Geid) (a : Int) (v : BitVec 8) :
    gwf G → gwritesByte G e a v → e ∈ G.gxGmo :=
  fun hwf hw => ((gwritesElemOf G e).1 (gwritesByteInGwrites G e a v hwf hw)).1

theorem greadsByteGmo (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    gwf G → greadsByte G e a t v → e ∈ G.gxGmo :=
  fun hwf hrd => gwfMemGmo G e hwf (gaccessesGmem G e a (Or.inr ⟨t, v, hrd⟩))

/-- `gpo` is a strict order (it compares offsets inside one hart). -/
theorem gpoIrrefl (G : Gexec) (x : Geid) : ¬ WeakRvwmoGraph.gpo G x x :=
  fun h => Nat.lt_irrefl _ h.2.1

theorem gpoTrans (G : Gexec) (x y z : Geid) :
    WeakRvwmoGraph.gpo G x y → WeakRvwmoGraph.gpo G y z → WeakRvwmoGraph.gpo G x z := by
  rintro ⟨h1, h2, h3, _⟩ ⟨h4, h5, _, h6⟩
  exact ⟨h1.trans h4, Nat.lt_trans h2 h5, h3, h6⟩

/-- A sub-relation's transitive closure is inside the larger one's. -/
theorem tcMono {A : Type _} (R1 R2 : A → A → Prop) (x y : A) :
    (∀ a b, R1 a b → R2 a b) → tc R1 x y → tc R2 x y := by
  intro hsub h
  induction h with
  | single h => exact tc_once (hsub _ _ h)
  | tail _ h ih => exact tc_r ih (hsub _ _ h)

/-- Lean-only: a `tc` path has a FIRST step. -/
theorem tcHeadDecomp {A : Type _} {R : A → A → Prop} {y z : A} (h : tc R y z) :
    ∃ u, R y u ∧ rtc R u z := by
  induction h with
  | single h => exact ⟨_, h, rtc_refl _⟩
  | tail _ h2 ih =>
    obtain ⟨u, h1, hr⟩ := ih
    exact ⟨u, h1, rtc_r hr h2⟩

/-- Lean-only: stdpp-style HEAD induction on `tc`, toward a fixed end. -/
theorem tcHeadInd {A : Type _} {R : A → A → Prop} (P : A → Prop) (z : A)
    (Pone : ∀ y, R y z → P y) (Pstep : ∀ y u, R y u → tc R u z → P u → P y) :
    ∀ y, tc R y z → P y := by
  intro y h
  obtain ⟨u, hyu, hr⟩ := tcHeadDecomp h
  have key : ∀ u, rtc R u z → ∀ y, R y u → P y :=
    rtc_ind_l (fun u => ∀ y, R y u → P y) z Pone
      (fun x y' hxy hr' ih y hyx => Pstep y x hyx (tc_rtc_r (tc_once hxy) hr') (ih x hxy))
  exact key u hr y hyu

/-! # 2. THE RELATIONS -/

/-- `grf`: `r` reads a byte from the write `w`. -/
def WeakRvwmoAcyc.grf (G : Gexec) (w r : Geid) : Prop :=
  ∃ a t v, greadsByte G r a t v ∧ gwriteAt G t = some w

/-- `gcaus`: route B's F2 sentence's relation, `po ∪ rf`. -/
def gcaus (G : Gexec) (x y : Geid) : Prop :=
  WeakRvwmoGraph.gpo G x y ∨ WeakRvwmoAcyc.grf G x y

/-- `gco`: the same-byte write order, read off the write indices. -/
def gco (G : Gexec) (w w' : Geid) : Prop :=
  ∃ a v v', gwritesByte G w a v ∧ gwritesByte G w' a v' ∧ gwix G w < gwix G w'

/-- `gfr`: `rf⁻¹ ; co ∖ id`, byte-matched, stated on the read's `ts` entry. -/
def gfr (G : Gexec) (r w' : Geid) : Prop :=
  r ≠ w' ∧ ∃ a t v v', greadsByte G r a t v ∧ gwritesByte G w' a v' ∧ t < gwix G w'

/-- `gpow`: po INTO a write, from a MEMORY event — rule 14's own edges. -/
def gpow (G : Gexec) (e w : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e w ∧ gmem G e ∧ gisW G w = true

/-- THE OBLIGATION RELATION. -/
def racy (G : Gexec) (x y : Geid) : Prop :=
  gpow G x y ∨ WeakRvwmoAcyc.grf G x y ∨ gco G x y ∨ gfr G x y ∨ gppo G x y

/-- … and its `Gdexec` form, with the store-dep fragment. -/
def racyD (GD : Gdexec) (x y : Geid) : Prop :=
  racy GD.gdG x y ∨ (x, y) ∈ GD.gdDeps

/-- W13 (K) (plan §C W13 (K); Lean-only): `racyD` EXTENDED by an extra relation `X` — the form
the I/O-aware normalization consumes (`WeakRvwmoTopo.normalizeOfAcyclicX`).  The I/O instance
`racyDIO GF := racyDX GF.gfGd (ioExtra GF)` (= `racyD ∪ ioResidue ∪ gmo|IO ∪` the `gdiskRead14`
pairs) lives in `WeakRvwmoKillIO`: its arms name the fabric bundle, which is downstream of this
file. -/
def racyDX (GD : Gdexec) (X : Geid → Geid → Prop) (x y : Geid) : Prop :=
  racyD GD x y ∨ X x y

/-- W12 (1) (plan §C W12; D25 (a) [OWN.5]): THE CORE the topo / normalize / hull kit
consumes — well-formedness, load value, atomicity and the dep fragment's shape.  No ppo
arm and no `gdepsGmo`: the re-timed order takes both from `racyD`'s own arms, so every
cat-consistent graph (`CatLin.rvwmoCatAD`) and every RVWMO⁻ graph has it. -/
def rvwmoCoreD (GD : Gdexec) : Prop :=
  gwf GD.gdG ∧ gloadValue GD.gdG ∧ gatomicity GD.gdG ∧ gdepsWf GD.gdG GD.gdDeps

theorem WeakRvwmoAcyc.coreOfMinus (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD → rvwmoCoreD GD :=
  fun ⟨⟨hwf, _, hlv, hat⟩, hdw, _⟩ => ⟨hwf, hlv, hat, hdw⟩

/-- Lean-only: RVWMO⁻ callers of the core-stated kit keep their text (the coercion
inserts `WeakRvwmoAcyc.coreOfMinus`). -/
instance WeakRvwmoAcyc.coeCoreOfMinus (GD : Gdexec) :
    Coe (rvwmoMinusDepsConsistent GD) (rvwmoCoreD GD) :=
  ⟨WeakRvwmoAcyc.coreOfMinus GD⟩

/-- THE TRANSPORTING FRAGMENT (§5). -/
def rt (G : Gexec) (x y : Geid) : Prop :=
  gpow G x y ∨ WeakRvwmoAcyc.grf G x y ∨ gppo G x y

theorem rtRacy (G : Gexec) (x y : Geid) : rt G x y → racy G x y := by
  rintro (h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-! # 3. EVERY ARM IS GMO-FORWARD -/

/-- rf ⊆ gmo.  The forwarding half of `gvisible` is `gpoloc`-ordered, hence
gmo-ordered. -/
theorem WeakRvwmoAcyc.grfGmo (G : Gexec) (w r : Geid) :
    rvwmoMinusConsistent G → WeakRvwmoAcyc.grf G w r → gmoLt G w r := by
  rintro ⟨_, hppo, hlv, _⟩ ⟨a, t, v, hrd, hat⟩
  cases t with
  | zero => simp [gwriteAt] at hat
  | succ i =>
    have h1 := (hlv r a (i + 1) v hrd).1
    obtain ⟨w0, hat0, hwb, hvis⟩ := h1
    have hw0 : w0 = w := by
      rw [hat0] at hat
      exact Option.some.inj hat
    subst hw0
    rcases hvis with hmo | hpo
    · exact hmo
    · exact hppo _ _ (Or.inl ⟨hpo, a, Or.inl ⟨v, hwb⟩, Or.inr ⟨i + 1, v, hrd⟩⟩)

theorem grfGisW (G : Gexec) (w r : Geid) : WeakRvwmoAcyc.grf G w r → gisW G w = true := by
  rintro ⟨a, t, v, _, hat⟩
  exact ((gwritesElemOf G w).1 (gwriteAtGwrites G t w hat)).2

theorem grfGmemR (G : Gexec) (w r : Geid) : WeakRvwmoAcyc.grf G w r → gmem G r := by
  rintro ⟨a, t, v, hrd, _⟩
  exact gaccessesGmem G r a (Or.inr ⟨t, v, hrd⟩)

/-- co ⊆ gmo: write indices and gmo positions order the writes the same way. -/
theorem gcoGmo (G : Gexec) (w w' : Geid) : gwf G → gco G w w' → gmoLt G w w' := by
  rintro hwf ⟨a, v, v', h1, h2, hlt⟩
  have hw := gwritesByteInGwrites G w a v hwf h1
  have hw' := gwritesByteInGwrites G w' a v' hwf h2
  exact ⟨gwritesByteGmo G w a v hwf h1, gwritesByteGmo G w' a v' hwf h2,
    (gwixGposLt G w w' hwf.1 hw hw').1 hlt⟩

/-- fr ⊆ gmo: load-value's CO-MAXIMALITY half. -/
theorem gfrGmo (G : Gexec) (r w' : Geid) :
    rvwmoMinusConsistent G → gfr G r w' → gmoLt G r w' := by
  rintro ⟨hwf, _, hlv, _⟩ ⟨hne, a, t, v, v', hrd, hwb, hlt⟩
  have hr := greadsByteGmo G r a t v hwf hrd
  have hgw' := gwritesByteGmo G w' a v' hwf hwb
  have hmax := (hlv r a t v hrd).2
  have hnv : ¬ gvisible G w' r := by
    intro hvis
    have := hmax w' v' hwb hvis
    omega
  rcases gmoLtTotal G r w' hwf.1 hr hgw' hne with h | hbad
  · exact h
  · exact absurd (Or.inl hbad) hnv

/-- po-into-a-write ⊆ gmo: this IS `grule14`. -/
theorem rule14PoWrite (G : Gexec) (e w : Geid) : grule14 G → gpow G e w → gmoLt G e w := by
  rintro h14 ⟨hpo, hm, hw⟩
  exact h14 e w hpo hm (WeakRvwmoAcyc.gisWGlblIs G w hw)

/-- THE UNION. -/
theorem rGmo (G : Gexec) (x y : Geid) :
    rvwmoMinusConsistent G → grule14 G → racy G x y → gmoLt G x y := by
  intro hcons h14 h
  rcases h with h | h | h | h | h
  · exact rule14PoWrite G x y h14 h
  · exact WeakRvwmoAcyc.grfGmo G x y hcons h
  · exact gcoGmo G x y hcons.1 h
  · exact gfrGmo G x y hcons h
  · exact hcons.2.1 x y h

theorem rdGmo (GD : Gdexec) (x y : Geid) :
    rvwmoMinusDepsConsistent GD → grule14 GD.gdG → racyD GD x y → gmoLt GD.gdG x y := by
  rintro ⟨hcons, _, hdg⟩ h14 (hR | hd)
  · exact rGmo GD.gdG x y hcons h14 hR
  · exact hdg (x, y) hd

/-! # 4. THE THEOREM: R IS ACYCLIC -/

theorem tcRGmo (G : Gexec) (x y : Geid) :
    rvwmoMinusConsistent G → grule14 G → tc (racy G) x y → gmoLt G x y := by
  intro hcons h14 h
  induction h with
  | single h => exact rGmo G _ _ hcons h14 h
  | tail _ h ih => exact gmoLtTrans G _ _ _ ih (rGmo G _ _ hcons h14 h)

theorem rAcyclic (G : Gexec) (x : Geid) :
    rvwmoMinusConsistent G → grule14 G → tc (racy G) x x → False :=
  fun hcons h14 htc => gmoLtIrrefl G x (tcRGmo G x x hcons h14 htc)

theorem tcRdGmo (GD : Gdexec) (x y : Geid) :
    rvwmoMinusDepsConsistent GD → grule14 GD.gdG → tc (racyD GD) x y → gmoLt GD.gdG x y := by
  intro hcons h14 h
  induction h with
  | single h => exact rdGmo GD _ _ hcons h14 h
  | tail _ h ih => exact gmoLtTrans GD.gdG _ _ _ ih (rdGmo GD _ _ hcons h14 h)

theorem rdAcyclic (GD : Gdexec) (x : Geid) :
    rvwmoMinusDepsConsistent GD → grule14 GD.gdG → tc (racyD GD) x x → False :=
  fun hcons h14 htc => gmoLtIrrefl GD.gdG x (tcRdGmo GD x x hcons h14 htc)

/-- The transporting fragment inherits acyclicity. -/
theorem rtAcyclic (G : Gexec) (x : Geid) :
    rvwmoMinusConsistent G → grule14 G → tc (rt G) x x → False :=
  fun hcons h14 htc =>
    rAcyclic G x hcons h14 (tcMono _ _ x x (fun a b => rtRacy G a b) htc)

/-! # 4b. `po ∪ rf` IS ACYCLIC — route B's F2 sentence

A causality path `y →⁺ z` that ENDS AT A WRITE is gmo-forward from any
REFLEXIVE-PO PREFIX `x` of `y` that is itself a memory event. -/

theorem causWriteGmo (G : Gexec) :
    rvwmoMinusConsistent G → grule14 G →
    ∀ y z, tc (gcaus G) y z →
    ∀ x, (x = y ∨ WeakRvwmoGraph.gpo G x y) → gmem G x → gisW G z = true → gmoLt G x z := by
  intro hcons h14 y z htc
  refine tcHeadInd (R := gcaus G)
    (fun y => ∀ x, (x = y ∨ WeakRvwmoGraph.gpo G x y) → gmem G x → gisW G z = true →
      gmoLt G x z) z ?_ ?_ y htc
  · intro y hc x hx hmx hwz
    rcases hc with hpo | hrf
    · have hxz : WeakRvwmoGraph.gpo G x z := by
        rcases hx with rfl | hxy
        · exact hpo
        · exact gpoTrans G x y z hxy hpo
      exact rule14PoWrite G x z h14 ⟨hxz, hmx, hwz⟩
    · have hyz := WeakRvwmoAcyc.grfGmo G y z hcons hrf
      rcases hx with rfl | hxy
      · exact hyz
      · exact gmoLtTrans G _ _ _
          (rule14PoWrite G x y h14 ⟨hxy, hmx, grfGisW G y z hrf⟩) hyz
  · intro y u hc _ ih x hx hmx hwz
    rcases hc with hpo | hrf
    · refine ih x ?_ hmx hwz
      right
      rcases hx with rfl | hxy
      · exact hpo
      · exact gpoTrans G x y u hxy hpo
    · have hyu := WeakRvwmoAcyc.grfGmo G y u hcons hrf
      have huz := ih u (Or.inl rfl) (grfGmemR G y u hrf) hwz
      have hyz := gmoLtTrans G _ _ _ hyu huz
      rcases hx with rfl | hxy
      · exact hyz
      · exact gmoLtTrans G _ _ _
          (rule14PoWrite G x y h14 ⟨hxy, hmx, grfGisW G y u hrf⟩) hyz

/-- A causality path is either a single po edge or passes through a WRITE. -/
theorem causWriteOnPath (G : Gexec) (x y : Geid) :
    tc (gcaus G) x y →
    WeakRvwmoGraph.gpo G x y ∨
      ∃ w, gisW G w = true ∧ rtc (gcaus G) x w ∧ tc (gcaus G) w y := by
  refine tcHeadInd (R := gcaus G)
    (fun x => WeakRvwmoGraph.gpo G x y ∨
      ∃ w, gisW G w = true ∧ rtc (gcaus G) x w ∧ tc (gcaus G) w y) y ?_ ?_ x
  · intro x hc
    rcases hc with hpo | hrf
    · exact Or.inl hpo
    · exact Or.inr ⟨x, grfGisW G x y hrf, rtc_refl _, tc_once (Or.inr hrf : gcaus G x y)⟩
  · intro x u hc htc ih
    rcases ih with hpo | ⟨w, hw, hrw, htw⟩
    · rcases hc with hpo' | hrf
      · exact Or.inl (gpoTrans G x u y hpo' hpo)
      · exact Or.inr ⟨x, grfGisW G x u hrf, rtc_refl _,
          tc_l (Or.inr hrf : gcaus G x u) htc⟩
    · exact Or.inr ⟨w, hw, rtc_l hc hrw, htw⟩

theorem gcausAcyclic (G : Gexec) (x : Geid) :
    rvwmoMinusConsistent G → grule14 G → tc (gcaus G) x x → False := by
  intro hcons h14 htc
  rcases causWriteOnPath G x x htc with hpo | ⟨w, hw, hrw, htw⟩
  · exact gpoIrrefl G x hpo
  · have hww : tc (gcaus G) w w := tc_rtc_r htw hrw
    exact gmoLtIrrefl G w
      (causWriteGmo G hcons h14 w w hww w (Or.inl rfl) (WeakRvwmoAcyc.gisWGmem G w hw) hw)

/-- THE HEIGHT COROLLARY, stated constructively (via `gviolGrule14`). -/
theorem causCycleGviol (G : Gexec) (x : Geid) :
    rvwmoMinusConsistent G → tc (gcaus G) x x → ¬ (∀ e w, ¬ gviol G e w) :=
  fun hcons htc hno => gcausAcyclic G x hcons (gviolGrule14 G hcons.1 hno) htc

/-! # 5. TRANSPORT along `rowsRel` / `wperm` -/

/-- The inverse of `rowsRelRdb`: every read entry of `G'` comes from one of `G`,
renamed. -/
theorem lblRenRdInv (π : Nat → Nat) (l : Lbl) (base : Int) (ts' : List Nat)
    (vs : List (BitVec 8)) :
    lbRd (lblRen π l) = some (base, ts', vs) →
    ∃ ts, lbRd l = some (base, ts, vs) ∧ ts' = ts.map π := by
  intro h
  cases l with
  | LLoad aq b ts vs0 =>
    simp only [lblRen, lbRd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨ts, rfl, rfl⟩
  | LStore rl b vs0 k => simp [lblRen, lbRd] at h
  | LFence pr pw sr sw => simp [lblRen, lbRd] at h
  | LRmw aq rl b ts rvs wvs k =>
    simp only [lblRen, lbRd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨ts, rfl, rfl⟩
  | LIo => simp [lblRen, lbRd] at h

theorem rowsRelRdbInv (π : Nat → Nat) (G G' : Gexec) (e : Geid) (a : Int) (t' : Nat)
    (v : BitVec 8) :
    rowsRel π G G' → greadsByte G' e a t' v → ∃ t, t' = π t ∧ greadsByte G e a t v := by
  rintro hr ⟨l', base, ts', vs, j, hl', hrd', ht', hv, ha⟩
  rw [rowsRelLbl π G G' e hr] at hl'
  cases hl : gxLbl G e with
  | none => rw [hl] at hl'; simp at hl'
  | some l =>
    rw [hl] at hl'
    simp only [Option.map_some, Option.some.injEq] at hl'
    subst hl'
    obtain ⟨ts, hrd, rfl⟩ := lblRenRdInv π l base ts' vs hrd'
    rw [List.getElem?_map] at ht'
    cases htj : ts[j]? with
    | none => rw [htj] at ht'; simp at ht'
    | some t =>
      rw [htj] at ht'
      simp only [Option.map_some, Option.some.injEq] at ht'
      exact ⟨t, ht'.symm, l, base, ts, vs, j, hl, hrd, htj, hv, ha⟩

/-! ## 5.1 `grf`, `gpow`, `gcaus` -/

theorem grfRowsRel (π : Nat → Nat) (G G' : Gexec) (w r : Geid) :
    rowsRel π G G' → wperm π G G' →
    (WeakRvwmoAcyc.grf G w r ↔ WeakRvwmoAcyc.grf G' w r) := by
  intro hr hw
  have hwat := hw.2.1
  constructor
  · rintro ⟨a, t, v, hrd, hat⟩
    exact ⟨a, π t, v, rowsRelRdb π G G' r a t v hr hrd, by rw [hwat t]; exact hat⟩
  · rintro ⟨a, t', v, hrd', hat'⟩
    obtain ⟨t, rfl, hrd⟩ := rowsRelRdbInv π G G' r a t' v hr hrd'
    exact ⟨a, t, v, hrd, by rw [← hwat t]; exact hat'⟩

theorem gpowRowsRel (π : Nat → Nat) (G G' : Gexec) (e w : Geid) :
    rowsRel π G G' → (gpow G e w ↔ gpow G' e w) := by
  intro hr
  unfold gpow
  rw [rowsRelGisW π G G' w hr, rowsRelGpo π G G' e w hr, rowsRelGmem π G G' e hr]

theorem gcausRowsRel (π : Nat → Nat) (G G' : Gexec) :
    rowsRel π G G' → wperm π G G' → ∀ x y, gcaus G x y ↔ gcaus G' x y := by
  intro hr hw x y
  unfold gcaus
  rw [rowsRelGpo π G G' x y hr, grfRowsRel π G G' x y hr hw]

/-! ## 5.2 `gppo` — every arm, by the label lemmas -/

theorem rowsRelGaccesses (π : Nat → Nat) (G G' : Gexec) (e : Geid) (a : Int) :
    rowsRel π G G' → (gaccesses G' e a ↔ gaccesses G e a) := by
  intro hr
  constructor
  · rintro (⟨v, hwb⟩ | ⟨t, v, hrd⟩)
    · exact Or.inl ⟨v, (rowsRelWrb π G G' e a v hr).1 hwb⟩
    · obtain ⟨t0, _, hrd0⟩ := rowsRelRdbInv π G G' e a t v hr hrd
      exact Or.inr ⟨t0, v, hrd0⟩
  · rintro (⟨v, hwb⟩ | ⟨t, v, hrd⟩)
    · exact Or.inl ⟨v, (rowsRelWrb π G G' e a v hr).2 hwb⟩
    · exact Or.inr ⟨π t, v, rowsRelRdb π G G' e a t v hr hrd⟩

theorem rowsRelFence (π : Nat → Nat) (G G' : Gexec) (e : Geid) (pr pw sr sw : Bool) :
    rowsRel π G G' →
    (gxLbl G' e = some (LFence pr pw sr sw) ↔ gxLbl G e = some (LFence pr pw sr sw)) := by
  intro hr
  rw [rowsRelLbl π G G' e hr]
  cases gxLbl G e with
  | none => simp
  | some l => cases l <;> simp [lblRen]

theorem rowsRelGfb (π : Nat → Nat) (G G' : Gexec) (e1 e2 : Geid) (pr pw sr sw : Bool) :
    rowsRel π G G' →
    (gfenceBetween G' e1 e2 pr pw sr sw ↔ gfenceBetween G e1 e2 pr pw sr sw) := by
  intro hr
  unfold gfenceBetween
  constructor
  · rintro ⟨hag, hlt, kf, h1, h2, hl⟩
    exact ⟨hag, hlt, kf, h1, h2, (rowsRelFence π G G' (e1.1, kf) pr pw sr sw hr).1 hl⟩
  · rintro ⟨hag, hlt, kf, h1, h2, hl⟩
    exact ⟨hag, hlt, kf, h1, h2, (rowsRelFence π G G' (e1.1, kf) pr pw sr sw hr).2 hl⟩

theorem rowsRelGppo (π : Nat → Nat) (G G' : Gexec) (e1 e2 : Geid) :
    rowsRel π G G' → (gppo G' e1 e2 ↔ gppo G e1 e2) := by
  intro hr
  unfold gppo gpoloc gfenceCovers gacqPo grcsc
  simp only [rowsRelGpo π G G' e1 e2 hr, rowsRelGaccesses π G G' _ _ hr,
    rowsRelGfb π G G' e1 e2 _ _ _ _ hr,
    rowsRelGlblIs π G G' _ lbIsR hr (lblRenIsR π),
    rowsRelGlblIs π G G' _ lbIsW hr (lblRenIsW π),
    rowsRelGlblIs π G G' _ lbAq hr (lblRenAq π),
    rowsRelGlblIs π G G' _ lbRcsc hr (lblRenRcsc π),
    rowsRelGmem π G G' _ hr]

/-! ## 5.3 `gco` / `gfr` — ONLY under a MONOTONE renaming -/

theorem gcoRowsRelMono (π : Nat → Nat) (G G' : Gexec) (w w' : Geid) :
    gwf G → G'.gxGmo.Nodup → rowsRel π G G' → wperm π G G' →
    (∀ t1 t2, t1 < t2 → π t1 < π t2) →
    gco G w w' → gco G' w w' := by
  rintro hwf hnd' hr hw hmono ⟨a, v, v', h1, h2, hlt⟩
  refine ⟨a, v, v', (rowsRelWrb π G G' w a v hr).2 h1, (rowsRelWrb π G G' w' a v' hr).2 h2, ?_⟩
  rw [wpermGwix π G G' w hnd' hw (gwritesByteInGwrites G w a v hwf h1),
    wpermGwix π G G' w' hnd' hw (gwritesByteInGwrites G w' a v' hwf h2)]
  exact hmono _ _ hlt

theorem gfrRowsRelMono (π : Nat → Nat) (G G' : Gexec) (r w' : Geid) :
    gwf G → G'.gxGmo.Nodup → rowsRel π G G' → wperm π G G' →
    (∀ t1 t2, t1 < t2 → π t1 < π t2) →
    gfr G r w' → gfr G' r w' := by
  rintro hwf hnd' hr hw hmono ⟨hne, a, t, v, v', hrd, hwb, hlt⟩
  refine ⟨hne, a, π t, v, v', rowsRelRdb π G G' r a t v hr hrd,
    (rowsRelWrb π G G' w' a v' hr).2 hwb, ?_⟩
  rw [wpermGwix π G G' w' hnd' hw (gwritesByteInGwrites G w' a v' hwf hwb)]
  exact hmono _ _ hlt

/-! ## 5.4 The orbit corollaries -/

theorem tcGcausRowsRel (π : Nat → Nat) (G G' : Gexec) (x y : Geid) :
    rowsRel π G G' → wperm π G G' → tc (gcaus G) x y → tc (gcaus G') x y :=
  fun hr hw => tcMono _ _ x y (fun a b => (gcausRowsRel π G G' hr hw a b).1)

theorem gcausAcyclicOrbit (π : Nat → Nat) (G G' : Gexec) (x : Geid) :
    rvwmoMinusConsistent G' → grule14 G' → rowsRel π G G' → wperm π G G' →
    tc (gcaus G) x x → False :=
  fun hcons h14 hr hw htc => gcausAcyclic G' x hcons h14 (tcGcausRowsRel π G G' x x hr hw htc)

theorem rtRowsRel (π : Nat → Nat) (G G' : Gexec) (x y : Geid) :
    rowsRel π G G' → wperm π G G' → rt G x y → rt G' x y := by
  rintro hr hw (h | h | h)
  · exact Or.inl ((gpowRowsRel π G G' x y hr).1 h)
  · exact Or.inr (Or.inl ((grfRowsRel π G G' x y hr hw).1 h))
  · exact Or.inr (Or.inr ((rowsRelGppo π G G' x y hr).2 h))

theorem rtAcyclicOrbit (π : Nat → Nat) (G G' : Gexec) (x : Geid) :
    rvwmoMinusConsistent G' → grule14 G' → rowsRel π G G' → wperm π G G' →
    tc (rt G) x x → False :=
  fun hcons h14 hr hw htc =>
    rtAcyclic G' x hcons h14 (tcMono _ _ x x (fun a b => rtRowsRel π G G' a b hr hw) htc)

end Weak
