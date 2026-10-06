/-
Weak: **graph-level (pure, no Iris) facts for lock handoff** (AxSL tier).

Rocq: `iris/AxLockGraph.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-lb-axsl.md`
§7.R).  Over `AxGraphCat`'s `rvwmoCatConsistent` (the faithful riscv.cat ppo model,
WITH store-buffer forwarding):

  §1  glue: rfe ⇒ gmo (`catGrfeGmo`); `gobCat` ⇒ `gvisible` (`catGobGvisible`);
      `lbIsR`/`lbAq` of an `LRmw` with `.aq` (`lrmwAqIsRAq`); a byte read is a
      read (`greadsByteGlblR`); every RMW's read index is BELOW its own write
      index (`catRmwTsLt`, the cat-model generalization of
      `WeakRvwmoLock.acq_ts_lt`); `gatomicity` ⇒ at most one RMW reads (via a
      given index) a given byte (`catRmwUniqueReader`);
  §2  `lockHandoffGraph` — the MP + release/acquire core of a lock handoff:
      under the LOCK DISCIPLINE that `w_x` is gmo-maximal among writes to `x`,
      the po-later read `r_x` after an acquire reading the release reads from
      `w_x`.  The release ordering is taken as the abstract ppo edge
      `gppoCat GD w_x w_rel`: riscv.cat rule 6 is OMITTED from the model, so a
      bare `.rl` bit does NOT discharge it — a covering fence (`gfenceCovers`,
      rule 4) must;
  §3  the reader's byte-restricted coherence facts: a same-byte write gmo-before
      a read is its rf-source or a `gco`-predecessor of it
      (`xWritesGmoBeforeRead`); the genesis twin (`xNoWriteGmoBeforeReadGenesis`)
      and its converse (`greadsByteNoVisibleWriteIsImage`).

**Deviations from Rocq.**

1. NAMES: lowerCamelCase.  No name here is in `notes/weak-port-dupnames.json`;
   the dependencies' duplicates are referred to qualified
   (`WeakRvwmoGraph.gpo`, `WeakRvwmoGraph.gwixPos`, `WeakRvwmoGraph.glblIsRGmem`,
   `WeakRvwmoAcyc.grf`).
2. VOCABULARY: as `AxGraphCat` deviation 2 (`Z` ↦ `Int`, `bv 8` ↦ `BitVec 8`,
   `gx_img G a` ↦ `G.gxImg a`, `gd_g` ↦ `.gdG`).
3. The Rocq `Print Assumptions` lines have no Lean twin (the lint's axiom check
   covers them).

**Name map** (Rocq → Lean): `cat_grfe_gmo` ↦ `catGrfeGmo`; `cat_gob_gvisible` ↦
`catGobGvisible`; `lrmw_aq_is_r_aq` ↦ `lrmwAqIsRAq`; `greads_byte_glbl_r` ↦
`greadsByteGlblR`; `cat_rmw_ts_lt` ↦ `catRmwTsLt`; `cat_rmw_unique_reader` ↦
`catRmwUniqueReader`; `lock_handoff_graph` ↦ `lockHandoffGraph`;
`x_writes_gmo_before_read` ↦ `xWritesGmoBeforeRead`;
`x_no_write_gmo_before_read_genesis` ↦ `xNoWriteGmoBeforeReadGenesis`;
`greads_byte_no_visible_write_is_image` ↦ `greadsByteNoVisibleWriteIsImage`.

**Not ported:** nothing.
-/
import Weak.AxGraphCat
import Weak.WeakRvwmoLock

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. Graph glue lemmas -/

/-- rfe ⇒ gmo, under the full cat-model consistency. -/
theorem catGrfeGmo (GD : Gdexec) (w r : Geid) :
    rvwmoCatConsistent GD → grfe GD.gdG w r → gmoLt GD.gdG w r :=
  fun hcons hrfe => grfeGmo _ _ _ hcons.2.2.1 hrfe

/-- Every `gobCat` edge is visible (the `gmoLt` disjunct). -/
theorem catGobGvisible (GD : Gdexec) (x y : Geid) :
    rvwmoCatConsistent GD → gobCat GD x y → gvisible GD.gdG x y :=
  fun hcons hob => Or.inl (obCatSubGmo GD x y hcons hob)

/-- `lbIsR` / `lbAq` of an `LRmw` with its `aq` bit set — definitional. -/
theorem lrmwAqIsRAq (rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8))
    (k : WmClass) :
    lbIsR (LRmw true rl base ts rvs wvs k) = true ∧
    lbAq (LRmw true rl base ts rvs wvs k) = true :=
  ⟨rfl, rfl⟩

/-- A byte read is an `lbIsR` event. -/
theorem greadsByteGlblR (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte G e a t v → glblIs G e lbIsR := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, _, _, _⟩
  exact ⟨l, hl, lbRdIsR l _ hrd⟩

/-- Any fused RMW's own read index is BELOW its own write index. -/
theorem catRmwTsLt (GD : Gdexec) (A : Geid) (a : Int) (t : Nat) (v v' : BitVec 8) :
    rvwmoCatConsistent GD →
    greadsByte GD.gdG A a t v → gwritesByte GD.gdG A a v' →
    t < gwix GD.gdG A := by
  intro hcons hrd hwr
  obtain ⟨hwf, hppo, hlv, _, _, _⟩ := id hcons
  have hA := gwritesByteGwrites GD.gdG A a v' hwf hwr
  cases t with
  | zero => exact WeakRvwmoGraph.gwixPos GD.gdG A hA
  | succ i =>
    obtain ⟨r, hat0, hrb, hvis⟩ := (hlv A a (i + 1) v hrd).1
    obtain ⟨hr, hrix⟩ := gwriteAtInv GD.gdG (i + 1) r hwf.1 hat0
    rw [← hrix]
    apply gmoGwixLt GD.gdG r A hwf hr hA
    rcases hvis with hmo | hpo
    · exact hmo
    · exact hppo _ _ (Or.inl (Or.inl ⟨hpo, a, Or.inl ⟨v, hrb⟩, v', hwr⟩))

/-- `gatomicity` ⇒ UNIQUE SUCCESSFUL READER. -/
theorem catRmwUniqueReader (GD : Gdexec) (a : Int) (t : Nat)
    (e1 e2 : Geid) (v1 v2 v1' v2' : BitVec 8) :
    rvwmoCatConsistent GD →
    greadsByte GD.gdG e1 a t v1 → gwritesByte GD.gdG e1 a v1' →
    greadsByte GD.gdG e2 a t v2 → gwritesByte GD.gdG e2 a v2' →
    e1 = e2 := by
  intro hcons hrd1 hwr1 hrd2 hwr2
  obtain ⟨hwf, _, _, hat, _, _⟩ := id hcons
  have h1 := gwritesByteGwrites GD.gdG e1 a v1' hwf hwr1
  have h2 := gwritesByteGwrites GD.gdG e2 a v2' hwf hwr2
  have ht1 := catRmwTsLt GD e1 a t v1 v1' hcons hrd1 hwr1
  have ht2 := catRmwTsLt GD e2 a t v2 v2' hcons hrd2 hwr2
  by_cases heq : gwix GD.gdG e1 = gwix GD.gdG e2
  · exact gwixInj GD.gdG e1 e2 hwf.1 h1 h2 heq
  · exfalso
    by_cases hlt : gwix GD.gdG e1 < gwix GD.gdG e2
    · exact hat e2 a t v2 hrd2 (gwritesByteGlblW _ _ _ _ hwr2) e1 v1' hwr1 ⟨ht1, hlt⟩
    · exact hat e1 a t v1 hrd1 (gwritesByteGlblW _ _ _ _ hwr1) e2 v2' hwr2
        ⟨ht2, by omega⟩

/-! # 2. `lockHandoffGraph`: the MP + release/acquire core of a lock handoff -/

/-- Hart A's owned write `w_x` is ppo-before its release write `w_rel`; hart B's
acquire `acq` reads `w_rel` (rfe) and is po-before the read `r_x` of `x`.  Under
the LOCK DISCIPLINE (`w_x` gmo-maximal among writes to `x`), `r_x` reads from
`w_x`, with `w_x`'s data. -/
theorem lockHandoffGraph (GD : Gdexec) (x : Int)
    (w_x r_x w_rel acq : Geid) (vx v : BitVec 8) (t : Nat) :
    rvwmoCatConsistent GD →
    gwritesByte GD.gdG w_x x vx →
    gppoCat GD w_x w_rel →
    grfe GD.gdG w_rel acq →
    glblIs GD.gdG acq lbIsR →
    glblIs GD.gdG acq lbAq →
    WeakRvwmoGraph.gpo GD.gdG acq r_x →
    greadsByte GD.gdG r_x x t v →
    (∀ w vw, gwritesByte GD.gdG w x vw → w = w_x ∨ gmoLt GD.gdG w w_x) →
    WeakRvwmoAcyc.grf GD.gdG w_x r_x ∧ v = vx := by
  intro hcons hwx hrel hrf hacqR hacqAq hacqPo hrd hdisc
  obtain ⟨hwf, _, hlv, _, _, _⟩ := id hcons
  have hgob1 : gobCat GD w_x w_rel := gobCatStep GD _ _ (Or.inl hrel)
  have hgob2 : gobCat GD w_rel acq := gobCatStep GD _ _ (Or.inr (Or.inr (Or.inl hrf)))
  have hgmem : gmem GD.gdG r_x :=
    WeakRvwmoGraph.glblIsRGmem _ _ (greadsByteGlblR _ _ _ _ _ hrd)
  have hgacq : gacqPo GD.gdG acq r_x := ⟨hacqPo, hacqR, hacqAq, hgmem⟩
  have hgob4 : gobCat GD acq r_x :=
    gobCatStep GD _ _ (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgacq)))))))
  have hgob5 := gobCatTrans GD _ _ _ (gobCatTrans GD _ _ _ hgob1 hgob2) hgob4
  have hvis : gvisible GD.gdG w_x r_x := catGobGvisible GD _ _ hcons hgob5
  have hwxW := gwritesByteGwrites GD.gdG w_x x vx hwf hwx
  cases t with
  | zero =>
    exfalso
    have hc := (hlv r_x x 0 v hrd).2 w_x vx hwx hvis
    have := WeakRvwmoGraph.gwixPos GD.gdG w_x hwxW
    omega
  | succ i =>
    obtain ⟨w, hat0, hwb, _⟩ := (hlv r_x x (i + 1) v hrd).1
    have hcomax := (hlv r_x x (i + 1) v hrd).2 w_x vx hwx hvis
    obtain ⟨hwW, hwix⟩ := gwriteAtInv GD.gdG (i + 1) w hwf.1 hat0
    rcases hdisc w v hwb with rfl | hmo
    · exact ⟨⟨x, i + 1, v, hrd, hat0⟩, gwritesByteDet _ _ _ _ _ hwb hwx⟩
    · exfalso
      have := gmoGwixLt GD.gdG w w_x hwf hwW hwxW hmo
      omega

/-! # 3. The reader's byte-restricted coherence facts -/

/-- `w0` is `r`'s rf-source at byte `a`; any byte-`a` write `w` gmo-before `r` is
`w0` itself or `gco`-before it. -/
theorem xWritesGmoBeforeRead (GD : Gdexec) (a : Int) (r w w0 : Geid) (v : BitVec 8) :
    rvwmoCatConsistent GD →
    grfAt GD.gdG a w0 r →
    gwritesByte GD.gdG w a v →
    gmoLt GD.gdG w r →
    w = w0 ∨ gco GD.gdG w w0 := by
  intro hcons hrf0 hwb hmo
  obtain ⟨hwf, _, hlv, _, _, _⟩ := id hcons
  obtain ⟨t, v0, hrd, hat⟩ := hrf0
  cases t with
  | zero => simp [gwriteAt] at hat
  | succ i =>
    obtain ⟨hw0gw, hwix0⟩ := gwriteAtInv GD.gdG (i + 1) w0 hwf.1 hat
    have hwgw := gwritesByteGwrites GD.gdG w a v hwf hwb
    by_cases hne : w = w0
    · exact Or.inl hne
    · right
      by_cases hlt : gwix GD.gdG w < gwix GD.gdG w0
      · obtain ⟨w0', hat', hwb0, _⟩ := (hlv r a (i + 1) v0 hrd).1
        have : w0' = w0 := by
          rw [hat] at hat'
          exact (Option.some.inj hat').symm
        subst this
        exact ⟨a, v, v0, hwb, hwb0, hlt⟩
      · exfalso
        have hgt : gwix GD.gdG w0 < gwix GD.gdG w := by
          by_cases heq : gwix GD.gdG w = gwix GD.gdG w0
          · exact absurd (gwixInj GD.gdG w w0 hwf.1 hwgw hw0gw heq) hne
          · omega
        have hrw : r ≠ w := by
          rintro rfl
          exact gmoLtIrrefl _ _ hmo
        have hfr : gfr GD.gdG r w := ⟨hrw, a, i + 1, v0, v, hrd, hwb, hwix0 ▸ hgt⟩
        exact gmoLtIrrefl _ _ (gmoLtTrans _ _ _ _ hmo (gfrGmoLv _ _ _ hwf hlv hfr))

/-- THE GENESIS TWIN: a read of the era-initial image (`t = 0`) has NO byte-`a`
write gmo-before it. -/
theorem xNoWriteGmoBeforeReadGenesis (GD : Gdexec) (a : Int) (r w : Geid)
    (v vw : BitVec 8) :
    rvwmoCatConsistent GD →
    greadsByte GD.gdG r a 0 v →
    gwritesByte GD.gdG w a vw →
    ¬ gmoLt GD.gdG w r := by
  intro hcons hrd hwb hmo
  obtain ⟨hwf, _, hlv, _, _, _⟩ := id hcons
  have hmax := (hlv r a 0 v hrd).2 w vw hwb (Or.inl hmo)
  have := WeakRvwmoGraph.gwixPos GD.gdG w (gwritesByteGwrites GD.gdG w a vw hwf hwb)
  omega

/-- THE CONVERSE BRIDGE: if no byte-`a` write is visible to `r`, `r` read the
era-initial image. -/
theorem greadsByteNoVisibleWriteIsImage (GD : Gdexec) (a : Int) (r : Geid) (t : Nat)
    (v : BitVec 8) :
    rvwmoCatConsistent GD →
    greadsByte GD.gdG r a t v →
    (∀ w v', gwritesByte GD.gdG w a v' → ¬ gvisible GD.gdG w r) →
    t = 0 ∧ GD.gdG.gxImg a = some v := by
  intro hcons hrd hnov
  have hcase := (hcons.2.2.1 r a t v hrd).1
  cases t with
  | zero => exact ⟨rfl, hcase⟩
  | succ i =>
    exfalso
    obtain ⟨w, _, hwb, hvis⟩ := hcase
    exact hnov w v hwb hvis

end Weak
