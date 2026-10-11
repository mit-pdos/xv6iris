/-
Weak: **`gppoCat`, the FAITHFUL riscv.cat ppo, and the model `rvwmoCatConsistent`**
(AxSL tier).

Rocq: `iris/AxGraphCat.v` @ xxvzwolszwmp.

The Rocq header, in substance (design: `claude-notes/design/weak-memory-lb-axsl.md`
§0 "The model" and gate G0.5, rev 4: rule 12 as a derived edge).  PURE (no Iris).

THE POINT.  `WeakRvwmoGraph`'s RVWMO⁻ renders riscv.cat's same-address rules 1–3
as the whole of `gpoloc` — in particular it orders a WRITE before its own
po-later same-byte READ in gmo, which riscv.cat does NOT (`[M];po-loc;[W]` has the
write on the RIGHT).  That extra edge forbids store-buffer FORWARDING, so a logic
built on RVWMO⁻ would be sound only for hardware without a store buffer.  This
file states the faithful ppo and re-derives the graph lemmas the base logic
consumes over it.

  §1  the six program-order arms `gppoCat6` (rules 1, 2, 3, 4, 5, 7-RCsc), RULE
      12 `gppo12` as a DERIVED edge through `gdDeps` and `grf`, `gppoCat` := both;
      the model WITH rule 12 (`rvwmoCatConsistent`) and WITHOUT it
      (`rvwmoCat6Consistent`);
  §2  `minusImpliesCat` — RVWMO⁻ ⇒ the cat model, each inclusion separately;
  §3  `gobCat` := (ppo_cat ∪ deps ∪ rfe ∪ co ∪ fr)⁺, `obCatSubGmo`,
      `obCatIrreflexive`; `gobCat ⊆ gob` under RVWMO⁻;
  §4  the owned-read family over `gobCat` — INSTANCES of `AxGraph`'s generic
      `ownedReadWith` — and the COVERAGE-SHAPED restatement `ownedReadCatCov`;
  §5  `ownForwardCat` — the read rule's case (ii); it needs RULE 1 ONLY;
  §7  EPOCHS AND THE IDENTITY STOP: `ownedReadEpoch` (the boundary must be
      VISIBLE — counterexample `epc`), the tie invariant `tieInv` and the read
      rule's cases `tieReadI`/`tieReadIi`/`tieCases`/`tieAcqCase`, the
      identity-stop lemma on rows (`AxGraphCat.ident`, `identStop`,
      `identStopWrites`, `identStopLemma`, the computable `dCoversB`), and the
      hand-proved witnesses `epc` and `isw`/`isw13`/`iswOk` (the review-4 F1
      graph).

The Rocq header's audit notes stand unchanged: rule 4 is `gfenceCovers`, rule 5
`gacqPo` (riscv.cat's `[AQ];po;[M]` on this alphabet), the tree's rule 7
`grelAcq` includes RCpc pairs while `grcsc` (both bits on both ends — only an
`LRmw` carries both) is ⊆ `grelAcq` (`grcscGrelAcq`).  RULE 12 GAP: `gdDeps` is
untagged (address, data, control and translation deps alike), so `gppo12` over
`gdDeps` also orders `[M];ctrl;[W];rfi;[R]` — stronger than RVWMO there; it is
stated over an explicit edge list `dd` for that reason.  OMITTED (each enlarges
the model — sound direction): rule 6, rule 7's RCpc part, rule 8.  The §7 header
note on `gdepsWf` (no READ targets, so the identity stop quantifies over an
ABSTRACT relation `D` with `D ⊆ gmo`) also stands.

FETCHES (Stage C, owner 2026-10-06/07; D1 reversed): instruction fetches are not
graph events in this tier (an administrative `LIFetch` emission item, no row item;
`notes/weak-port-o2-stageC.md`).  This file never modelled one: every `LLoad` in its
witnesses (`epc`, `isw`, …) is a data load, so no row or `decide` check changed.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  The duplicated
   Rocq name (`notes/weak-port-dupnames.json`) `ident` is FILE-QUALIFIED
   (`AxGraphCat.ident`); the dependencies' duplicates are referred to qualified
   (`WeakRvwmoGraph.gpo`, `WeakRvwmoAcyc.grf`, `WeakRvwmoAcyc.grfGmo`).
2. VOCABULARY: as `WeakRvwmoGraph` deviation 2 (`l !! i` ↦ `l[i]?`, `is_Some o`
   ↦ `o.isSome = true`, `Z` ↦ `Int`, `bv 8` ↦ `BitVec 8`, `agent` ↦ `Nat`,
   `stdpp.list_basics.last` ↦ `List.getLast?`, `f <$> o` ↦ `o.map f`,
   `seq` ↦ `List.range'`, `forallb`/`existsb` ↦ `List.all`/`List.any`,
   `bool_decide` ↦ `decide`, `implb a b` ↦ `!a || b`, `GDExec (GExec img prog
   gmo) deps` ↦ `⟨⟨img, prog, gmo⟩, deps⟩`, `WeakLitmus.b0/b1/b2` ↦
   `b0`/`b1`/`b2`).
3. `ident_t` ↦ `IdentT` with `deriving DecidableEq` (Rocq's `ident_t_eq_dec`
   instance); `ident_stop_from`'s `decide` match is an `if`.
4. The `Local Instance gmo_lt_dec_cat` is a `local instance` built by
   `unfold; infer_instance`.
5. CLOSURE INDUCTION: `obCatSubGmo`/`gobCatGob` induct on the library `tc`,
   which splits at the LAST step (`MachCSL.Rel` deviation 1).
6. The closed `vm_compute` side conditions (gmo membership/positions, `gwix`,
   `gwriteAt`, `identStop`, `dCoversB`, `ident` maps) are `decide`; the Ltac
   `gmo_wit` is `decide` on `gmoLt`.
7. `epc_refutes_invisible_boundary`'s `let`s are kept in the statement (zeta-
   reduced at the start of the proof).

**Name map** (Rocq → Lean): `lb_is_rmw` ↦ `lbIsRmw`; `lb_rcsc` ↦ `lbRcsc`;
`gppo1`/`gppo2`/`gppo3`/`grcsc`/`gppo12` (same); `gppo_cat6` ↦ `gppoCat6`;
`gppo_cat` ↦ `gppoCat`; `gppo_cat6_gmo` ↦ `gppoCat6Gmo`; `gppo_cat_gmo` ↦
`gppoCatGmo`; `rvwmo_cat_consistent` ↦ `rvwmoCatConsistent`;
`rvwmo_cat6_consistent` ↦ `rvwmoCat6Consistent`; `cat_implies_cat6` ↦
`catImpliesCat6`; `gppo_cat6_gpo` ↦ `gppoCat6Gpo`; `gppo_cat_events` ↦
`gppoCatEvents`; `gppo1_gpoloc` ↦ `gppo1Gpoloc`; `gppo2_gpoloc` ↦
`gppo2Gpoloc`; `gppo3_gpoloc` ↦ `gppo3Gpoloc`; `lb_rcsc_bits` ↦ `lbRcscBits`;
`grcsc_grel_acq` ↦ `grcscGrelAcq`; `gppo_cat6_gppo` ↦ `gppoCat6Gppo`;
`gppo12_gmo_minus` ↦ `gppo12GmoMinus`; `minus_implies_cat` ↦ `minusImpliesCat`;
`gobr_cat` ↦ `gobrCat`; `gob_cat` ↦ `gobCat`; `gob_cat_step` ↦ `gobCatStep`;
`gob_cat_trans` ↦ `gobCatTrans`; `gfr_gmo_lv` ↦ `gfrGmoLv`; `gobr_cat_gmo` ↦
`gobrCatGmo`; `ob_cat_sub_gmo` ↦ `obCatSubGmo`; `ob_cat_irreflexive` ↦
`obCatIrreflexive`; `ob_cat_asym` ↦ `obCatAsym`; `gppo12_gob` ↦ `gppo12Gob`;
`gobr_cat_gob` ↦ `gobrCatGob`; `gob_cat_gob` ↦ `gobCatGob`; `ob_cat_chain` ↦
`obCatChain`; `owned_read_cat` ↦ `ownedReadCat`; `owned_read_cat_snoc` ↦
`ownedReadCatSnoc`; `owned_read_cat_value` ↦ `ownedReadCatValue`;
`owned_read_cat_cov` ↦ `ownedReadCatCov`; `own_forward_cat` ↦ `ownForwardCat`;
`own_forward_cat'` ↦ `ownForwardCat'`; `gmo_chain` ↦ `gmoChain`; `epoch_cov` ↦
`epochCov`; `owned_read_epoch` ↦ `ownedReadEpoch`; `owned_read_epoch_snoc` ↦
`ownedReadEpochSnoc`; `owned_read_epoch_value` ↦ `ownedReadEpochValue`;
`epoch_cov_of_cov` ↦ `epochCovOfCov`; `tie_inv` ↦ `tieInv`;
`tie_inv_visible` ↦ `tieInvVisible`; `tie_read_i` ↦ `tieReadI`;
`tie_read_i_S` ↦ `tieReadIS`; `tie_read_ii` ↦ `tieReadIi`; `gmo_lt_dec_cat` ↦
`gmoLtDecCat`; `tie_cases` ↦ `tieCases`; `tie_acq_case` ↦ `tieAcqCase`;
`ident_t` ↦ `IdentT` (`IdLoad`/`IdStore`/`IdFence`/`IdRmw`); `ident_t_eq_dec` ↦
the derived `DecidableEq IdentT`; `ident` ↦ `AxGraphCat.ident`; `ident_agree` ↦
`identAgree`; `ident_stop_from` ↦ `identStopFrom`; `ident_stop` ↦ `identStop`;
`ident_stop_from_Some` ↦ `identStopFromSome`; `ident_stop_from_None` ↦
`identStopFromNone`; `ident_stop_Some` ↦ `identStopSome`; `ident_stop_None` ↦
`identStopNone`; `ident_is_w` ↦ `identIsW`; `ident_is_r` ↦ `identIsR`;
`d_covers` ↦ `dCovers`; `d_gmo` ↦ `dGmo`; `ident_stop_writes` ↦
`identStopWrites`; `ident_stop_lemma` ↦ `identStopLemma`;
`ident_stop_none_agree` ↦ `identStopNoneAgree`; `forallb_all` ↦ `forallbAll`;
`existsb_some` ↦ `existsbSome`; `is_r_at` ↦ `isRAt`; `d_covers_b` ↦
`dCoversB`; `d_covers_b_spec` ↦ `dCoversBSpec`; `d_gmo_of_gdeps` ↦
`dGmoOfGdeps`; `img_zero` ↦ `imgZero`; `epc`; `epc_lbl` ↦ `epcLbl`; `epc_wr` ↦
`epcWr`; `epc_rd` ↦ `epcRd`; `epc_wf` ↦ `epcWf`; `epc_lv` ↦ `epcLv`; `epc_cat` ↦
`epcCat`; `epc_rf` ↦ `epcRf`; `epc_refutes_invisible_boundary` ↦
`epcRefutesInvisibleBoundary`; `epc_epoch_positive` ↦ `epcEpochPositive`;
`isw_row_real` ↦ `iswRowReal`; `isw_row_exp` ↦ `iswRowExp`; `isw`; `isw_lbl` ↦
`iswLbl`; `isw_wr` ↦ `iswWr`; `isw_rd` ↦ `iswRd`; `isw_wf` ↦ `iswWf`; `isw_lv` ↦
`iswLv`; `isw_cat` ↦ `iswCat`; `isw_ident_stop` ↦ `iswIdentStop`;
`isw_d_covers_fails` ↦ `iswDCoversFails`; `isw_write_before_read` ↦
`iswWriteBeforeRead`; `isw13`; `isw13_d_covers` ↦ `isw13DCovers`;
`isw13_not_gmo` ↦ `isw13NotGmo`; `isw_ok_row` ↦ `iswOkRow`; `isw_ok` ↦ `iswOk`;
`isw_ok_same_ident` ↦ `iswOkSameIdent`; `isw_ok_gdeps_gmo` ↦ `iswOkGdepsGmo`;
`isw_ok_conclusion` ↦ `iswOkConclusion`; `isw_ok_store_after_load` ↦
`iswOkStoreAfterLoad`.

**Not ported:** nothing (the §6/§8 `Print Assumptions` blocks have no Lean twin;
the lint's axiom check covers them).
-/
import Weak.AxGraph

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-! # 1. The kept arms -/

/-- A fused RMW: the only label that both reads and writes. -/
def lbIsRmw (l : Lbl) : Bool := lbIsR l && lbIsW l

/-- RCsc: both annotation bits. -/
def lbRcsc (l : Lbl) : Bool := lbAq l && lbRl l

/-- RULE 1  `[M];po-loc;[W]` — a same-byte access before a WRITE. -/
def gppo1 (G : Gexec) (e1 e2 : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e1 e2 ∧ ∃ a, gaccesses G e1 a ∧ ∃ v, gwritesByte G e2 a v

/-- RULE 2  `([R];po-loc-no-w;[R]) \ rsw` — two same-byte reads with no same-hart
write to that byte po-between, reading DIFFERENT sources. -/
def gppo2 (G : Gexec) (e1 e2 : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e1 e2 ∧
  ∃ a t1 v1 t2 v2,
    greadsByte G e1 a t1 v1 ∧ greadsByte G e2 a t2 v2 ∧ t1 ≠ t2 ∧
    (∀ w v, gwritesByte G w a v → WeakRvwmoGraph.gpo G e1 w → WeakRvwmoGraph.gpo G w e2 → False)

/-- RULE 3  `[AMO];rfi;[R]` — a fused RMW read by a po-later read of the same
hart. -/
def gppo3 (G : Gexec) (e1 e2 : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e1 e2 ∧ glblIs G e1 lbIsRmw ∧ ∃ a, grfAt G a e1 e2

/-- RULE 7, RCsc only  `[RCsc];po;[RCsc]`. -/
def grcsc (G : Gexec) (e1 e2 : Geid) : Prop :=
  WeakRvwmoGraph.gpo G e1 e2 ∧ glblIs G e1 lbRcsc ∧ glblIs G e2 lbRcsc

/-- The six program-order arms: rules 1, 2, 3, 4 (`gfenceCovers`), 5 (`gacqPo`),
7-RCsc. -/
def gppoCat6 (G : Gexec) (e1 e2 : Geid) : Prop :=
  gppo1 G e1 e2 ∨ gppo2 G e1 e2 ∨ gppo3 G e1 e2 ∨
  gfenceCovers G e1 e2 ∨ gacqPo G e1 e2 ∨ grcsc G e1 e2

/-- RULE 12  `[M];(addr|data);[W];rfi;[R]`, DERIVED: a dep-target store `m`
forwarded to a same-hart read `b` orders the dep-source `a` before `b`.  Over an
explicit edge list `dd` (see the header's gap note). -/
def gppo12 (G : Gexec) (dd : List (Geid × Geid)) (a b : Geid) : Prop :=
  a.1 = b.1 ∧ ∃ m, (a, m) ∈ dd ∧ WeakRvwmoAcyc.grf G m b

def gppoCat (GD : Gdexec) (e1 e2 : Geid) : Prop :=
  gppoCat6 GD.gdG e1 e2 ∨ gppo12 GD.gdG GD.gdDeps e1 e2

def gppoCat6Gmo (G : Gexec) : Prop :=
  ∀ e1 e2, gppoCat6 G e1 e2 → gmoLt G e1 e2

def gppoCatGmo (GD : Gdexec) : Prop :=
  ∀ e1 e2, gppoCat GD e1 e2 → gmoLt GD.gdG e1 e2

/-- THE MODEL (with rule 12) ... -/
def rvwmoCatConsistent (GD : Gdexec) : Prop :=
  gwf GD.gdG ∧ gppoCatGmo GD ∧ gloadValue GD.gdG ∧
  gatomicity GD.gdG ∧
  gdepsWf GD.gdG GD.gdDeps ∧ gdepsGmo GD.gdG GD.gdDeps

/-- ... and WITHOUT it — the comparison point. -/
def rvwmoCat6Consistent (GD : Gdexec) : Prop :=
  gwf GD.gdG ∧ gppoCat6Gmo GD.gdG ∧ gloadValue GD.gdG ∧
  gatomicity GD.gdG ∧
  gdepsWf GD.gdG GD.gdDeps ∧ gdepsGmo GD.gdG GD.gdDeps

theorem catImpliesCat6 (GD : Gdexec) : rvwmoCatConsistent GD → rvwmoCat6Consistent GD := by
  rintro ⟨hwf, hppo, hlv, hat, hdw, hdg⟩
  exact ⟨hwf, fun e1 e2 h => hppo e1 e2 (Or.inl h), hlv, hat, hdw, hdg⟩

/-- Every program-order arm is `gpo`. -/
theorem gppoCat6Gpo (G : Gexec) (e1 e2 : Geid) : gppoCat6 G e1 e2 → WeakRvwmoGraph.gpo G e1 e2 := by
  rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | h | ⟨h, _⟩ | ⟨h, _⟩)
  · exact h
  · exact h
  · exact h
  · obtain ⟨pr, pw, sr, sw, ⟨hag, hlt, _⟩, h1, h2⟩ := h
    refine ⟨hag, hlt, ?_, ?_⟩
    · rcases h1 with ⟨⟨l, hl, _⟩, _⟩ | ⟨⟨l, hl, _⟩, _⟩ <;> simp [hl]
    · rcases h2 with ⟨⟨l, hl, _⟩, _⟩ | ⟨⟨l, hl, _⟩, _⟩ <;> simp [hl]
  · exact h
  · exact h

/-- Every arm is same-hart with labelled endpoints (rule 12 through `gdepsWf` and
the read footprint). -/
theorem gppoCatEvents (GD : Gdexec) (e1 e2 : Geid) :
    gdepsWf GD.gdG GD.gdDeps → gppoCat GD e1 e2 →
    e1.1 = e2.1 ∧ (gxLbl GD.gdG e1).isSome = true ∧ (gxLbl GD.gdG e2).isSome = true := by
  rintro hdw (h | h)
  · obtain ⟨hag, _, h1, h2⟩ := gppoCat6Gpo _ _ _ h
    exact ⟨hag, h1, h2⟩
  · obtain ⟨hag, m, hd, a, t, v, hrd, _⟩ := h
    obtain ⟨_, _, ⟨l, hl, _⟩, _⟩ := hdw (e1, m) hd
    obtain ⟨l', _, _, _, _, hl', _⟩ := hrd
    exact ⟨hag, by simp [hl], by simp [hl']⟩

/-! # 2. RVWMO⁻ ⇒ the cat model -/

theorem gppo1Gpoloc (G : Gexec) (e1 e2 : Geid) : gppo1 G e1 e2 → gpoloc G e1 e2 := by
  rintro ⟨hpo, a, h1, v, h2⟩
  exact ⟨hpo, a, h1, Or.inl ⟨v, h2⟩⟩

theorem gppo2Gpoloc (G : Gexec) (e1 e2 : Geid) : gppo2 G e1 e2 → gpoloc G e1 e2 := by
  rintro ⟨hpo, a, t1, v1, t2, v2, h1, h2, _, _⟩
  exact ⟨hpo, a, Or.inr ⟨t1, v1, h1⟩, Or.inr ⟨t2, v2, h2⟩⟩

/-- Rule 3 needs load-value: the rf-source WRITES the byte it is read at. -/
theorem gppo3Gpoloc (G : Gexec) (e1 e2 : Geid) : gloadValue G → gppo3 G e1 e2 → gpoloc G e1 e2 := by
  rintro hlv ⟨hpo, _, a, t, v, hrd, hat⟩
  exact ⟨hpo, a, Or.inl ⟨v, greadSourceByte G e2 a t v e1 hlv hrd hat⟩, Or.inr ⟨t, v, hrd⟩⟩

/-- An RCsc label is a fused RMW carrying both bits. -/
theorem lbRcscBits (l : Lbl) :
    lbRcsc l = true →
    lbIsW l = true ∧ lbRl l = true ∧ lbIsR l = true ∧ lbAq l = true := by
  cases l <;> simp +contextual [lbRcsc, lbAq, lbRl, lbIsW, lbIsR]

theorem grcscGrelAcq (G : Gexec) (e1 e2 : Geid) : grcsc G e1 e2 → grelAcq G e1 e2 := by
  rintro ⟨hpo, ⟨l1, hl1, h1⟩, ⟨l2, hl2, h2⟩⟩
  obtain ⟨w1, r1, _, _⟩ := lbRcscBits l1 h1
  obtain ⟨_, _, r2, a2⟩ := lbRcscBits l2 h2
  exact ⟨hpo, ⟨l1, hl1, w1⟩, ⟨l1, hl1, r1⟩, ⟨l2, hl2, r2⟩, ⟨l2, hl2, a2⟩⟩

/-- The six arms ⊆ ppo⁻ (under load-value). -/
theorem gppoCat6Gppo (G : Gexec) (e1 e2 : Geid) : gloadValue G → gppoCat6 G e1 e2 → gppo G e1 e2 := by
  rintro hlv (h | h | h | h | h | h)
  · exact Or.inl (gppo1Gpoloc _ _ _ h)
  · exact Or.inl (gppo2Gpoloc _ _ _ h)
  · exact Or.inl (gppo3Gpoloc _ _ _ hlv h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (grcscGrelAcq _ _ _ h)))

/-- Rule 12 is gmo-forward under RVWMO⁻: `gdepsGmo` then `grfGmo` (whose
forwarding case is exactly `gpoloc`'s W→R edge). -/
theorem gppo12GmoMinus (GD : Gdexec) (a b : Geid) :
    rvwmoMinusDepsConsistent GD →
    gppo12 GD.gdG GD.gdDeps a b → gmoLt GD.gdG a b := by
  rintro ⟨hc, _, hdg⟩ ⟨_, m, hd, hrf⟩
  exact gmoLtTrans _ _ _ _ (hdg (a, m) hd) (WeakRvwmoAcyc.grfGmo _ _ _ hc hrf)

theorem minusImpliesCat (GD : Gdexec) :
    rvwmoMinusDepsConsistent GD → rvwmoCatConsistent GD := by
  intro hcons
  obtain ⟨⟨hwf, hppo, hlv, hat⟩, hdw, hdg⟩ := hcons
  refine ⟨hwf, ?_, hlv, hat, hdw, hdg⟩
  rintro e1 e2 (h | h)
  · exact hppo _ _ (gppoCat6Gppo _ _ _ hlv h)
  · exact gppo12GmoMinus GD e1 e2 ⟨⟨hwf, hppo, hlv, hat⟩, hdw, hdg⟩ h

/-! # 3. `gobCat` and `gobCat ⊆ gmo` -/

def gobrCat (GD : Gdexec) (x y : Geid) : Prop :=
  gppoCat GD x y ∨ gdepsRel GD x y ∨ grfe GD.gdG x y ∨
  gco GD.gdG x y ∨ gfr GD.gdG x y

def gobCat (GD : Gdexec) (x y : Geid) : Prop := tc (gobrCat GD) x y

theorem gobCatStep (GD : Gdexec) (x y : Geid) : gobrCat GD x y → gobCat GD x y := tc_once

theorem gobCatTrans (GD : Gdexec) (x y z : Geid) :
    gobCat GD x y → gobCat GD y z → gobCat GD x z := tc_transitive

/-- fr ⊆ gmo needs ONLY `gwf` + load-value: a same-byte write co-after the read's
source is not visible to the read, hence gmo-after it by totality. -/
theorem gfrGmoLv (G : Gexec) (r w' : Geid) : gwf G → gloadValue G → gfr G r w' → gmoLt G r w' := by
  rintro hwf hlv ⟨hne, a, t, v, v', hrd, hwb, hlt⟩
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

theorem gobrCatGmo (GD : Gdexec) (x y : Geid) :
    rvwmoCatConsistent GD → gobrCat GD x y → gmoLt GD.gdG x y := by
  rintro ⟨hwf, hppo, hlv, _, _, hdg⟩ (h | h | h | h | h)
  · exact hppo _ _ h
  · exact hdg (x, y) h
  · exact grfeGmo _ _ _ hlv h
  · exact gcoGmo _ _ _ hwf h
  · exact gfrGmoLv _ _ _ hwf hlv h

theorem obCatSubGmo (GD : Gdexec) (x y : Geid) :
    rvwmoCatConsistent GD → gobCat GD x y → gmoLt GD.gdG x y := by
  intro hcons h
  induction h with
  | single h => exact gobrCatGmo GD _ _ hcons h
  | tail _ h ih => exact gmoLtTrans _ _ _ _ ih (gobrCatGmo GD _ _ hcons h)

theorem obCatIrreflexive (GD : Gdexec) (x : Geid) : rvwmoCatConsistent GD → ¬ gobCat GD x x :=
  fun hcons hob => gmoLtIrrefl _ _ (obCatSubGmo GD x x hcons hob)

theorem obCatAsym (GD : Gdexec) (x y : Geid) :
    rvwmoCatConsistent GD → gobCat GD x y → ¬ gobCat GD y x :=
  fun hcons hxy hyx => obCatIrreflexive GD x hcons (gobCatTrans GD x y x hxy hyx)

/-- `gobCat ⊆ gob` under RVWMO⁻: the six arms are ppo⁻ arms; a rule-12 edge a→b
is the ob PATH a →deps→ m →gpoloc→ b, because under RVWMO⁻ the forwarded read `b`
is po-AFTER its source `m`. -/
theorem gppo12Gob (GD : Gdexec) (a b : Geid) :
    rvwmoMinusDepsConsistent GD →
    gppo12 GD.gdG GD.gdDeps a b → gob GD a b := by
  rintro hcons ⟨hag, m, hd, hrf⟩
  have ⟨⟨_, hppo, hlv, _⟩, hdw, _⟩ := hcons
  obtain ⟨ham, _, _, lm, hlm, _⟩ := hdw (a, m) hd
  have hmo := WeakRvwmoAcyc.grfGmo _ _ _ hcons.1 hrf
  obtain ⟨lb, hlb, _⟩ := grfGmemR _ _ _ hrf
  obtain ⟨x, t, v, hrd, hat⟩ := hrf
  have hwb := greadSourceByte _ _ _ _ _ _ hlv hrd hat
  -- `m` is po-before `b`
  have hpo : WeakRvwmoGraph.gpo GD.gdG m b := by
    refine ⟨ham.symm.trans hag, ?_, by simp [hlm], by simp [hlb]⟩
    by_cases hlt : m.2 < b.2
    · exact hlt
    exfalso
    by_cases heq : m.2 = b.2
    · have hmb : m = b := Prod.ext (ham.symm.trans hag) heq
      subst hmb
      exact gmoLtIrrefl _ _ hmo
    · have hpo' : WeakRvwmoGraph.gpo GD.gdG b m :=
        ⟨(ham.symm.trans hag).symm, by omega, by simp [hlb], by simp [hlm]⟩
      have hmo' : gmoLt GD.gdG b m :=
        hppo _ _ (Or.inl ⟨hpo', x, Or.inr ⟨t, v, hrd⟩, Or.inl ⟨v, hwb⟩⟩)
      exact gmoLtIrrefl _ _ (gmoLtTrans _ _ _ _ hmo' hmo)
  exact tc_l (Or.inr (Or.inl hd))
    (gobStep _ _ _ (Or.inl (Or.inl ⟨hpo, x, Or.inl ⟨v, hwb⟩, Or.inr ⟨t, v, hrd⟩⟩)))

theorem gobrCatGob (GD : Gdexec) (x y : Geid) :
    rvwmoMinusDepsConsistent GD → gobrCat GD x y → gob GD x y := by
  rintro hcons ((h | h) | h | h | h | h)
  · exact gobStep _ _ _ (Or.inl (gppoCat6Gppo _ _ _ hcons.1.2.2.1 h))
  · exact gppo12Gob GD x y hcons h
  · exact gobStep _ _ _ (Or.inr (Or.inl h))
  · exact gobStep _ _ _ (Or.inr (Or.inr (Or.inl h)))
  · exact gobStep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact gobStep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem gobCatGob (GD : Gdexec) (x y : Geid) :
    rvwmoMinusDepsConsistent GD → gobCat GD x y → gob GD x y := by
  intro hcons h
  induction h with
  | single h => exact gobrCatGob GD _ _ hcons h
  | tail _ h ih => exact gobTrans GD _ _ _ ih (gobrCatGob GD _ _ hcons h)

/-! # 4. The owned-read family over `gobCat` -/

def obCatChain (GD : Gdexec) (Hl : List Geid) : Prop :=
  chainWith (gobCat GD) Hl

theorem ownedReadCat (GD : Gdexec) (Hl : List Geid) (a : Int) (r w0 : Geid) :
    rvwmoCatConsistent GD →
    (∀ w, w ∈ Hl → ∃ v, gwritesByte GD.gdG w a v) →
    obCatChain GD Hl →
    (∀ w v, gwritesByte GD.gdG w a v → gvisible GD.gdG w r → w ∈ Hl) →
    w0 ∈ Hl → gvisible GD.gdG w0 r →
    (∃ t v, greadsByte GD.gdG r a t v) →
    ∃ w, lastVisible GD.gdG Hl r = some w ∧ grfAt GD.gdG a w r := fun hcons =>
  ownedReadWith GD.gdG (gobCat GD) Hl a r w0 (fun x y => obCatSubGmo GD x y hcons)
    hcons.1 hcons.2.2.1

theorem ownedReadCatSnoc (GD : Gdexec) (Hl0 : List Geid) (wl : Geid) (a : Int) (r : Geid) :
    rvwmoCatConsistent GD →
    (∀ w, w ∈ Hl0 ++ [wl] → ∃ v, gwritesByte GD.gdG w a v) →
    obCatChain GD (Hl0 ++ [wl]) →
    (∀ w v, gwritesByte GD.gdG w a v → gvisible GD.gdG w r → w ∈ Hl0 ++ [wl]) →
    gvisible GD.gdG wl r →
    (∃ t v, greadsByte GD.gdG r a t v) →
    grfAt GD.gdG a wl r := fun hcons =>
  ownedReadSnocWith GD.gdG (gobCat GD) Hl0 wl a r (fun x y => obCatSubGmo GD x y hcons)
    hcons.1 hcons.2.2.1

theorem ownedReadCatValue (GD : Gdexec) (Hl0 : List Geid) (wl : Geid) (a : Int) (r : Geid)
    (t : Nat) (v vl : BitVec 8) :
    rvwmoCatConsistent GD →
    (∀ w, w ∈ Hl0 ++ [wl] → ∃ v', gwritesByte GD.gdG w a v') →
    obCatChain GD (Hl0 ++ [wl]) →
    (∀ w v', gwritesByte GD.gdG w a v' → gvisible GD.gdG w r → w ∈ Hl0 ++ [wl]) →
    gvisible GD.gdG wl r →
    greadsByte GD.gdG r a t v →
    gwritesByte GD.gdG wl a vl →
    v = vl := fun hcons =>
  ownedReadValueWith GD.gdG (gobCat GD) Hl0 wl a r t v vl (fun x y => obCatSubGmo GD x y hcons)
    hcons.1 hcons.2.2.1

/-- THE COVERAGE-SHAPED FORM: every same-byte write gmo-BEFORE `r` is in the
history, and so is every own po-earlier same-byte write. -/
theorem ownedReadCatCov (GD : Gdexec) (Hl : List Geid) (a : Int) (r w0 : Geid) :
    rvwmoCatConsistent GD →
    (∀ w, w ∈ Hl → ∃ v, gwritesByte GD.gdG w a v) →
    obCatChain GD Hl →
    (∀ w v, gwritesByte GD.gdG w a v → gmoLt GD.gdG w r → w ∈ Hl) →
    (∀ w v, gwritesByte GD.gdG w a v → WeakRvwmoGraph.gpo GD.gdG w r → w ∈ Hl) →
    w0 ∈ Hl → gvisible GD.gdG w0 r →
    (∃ t v, greadsByte GD.gdG r a t v) →
    ∃ w, lastVisible GD.gdG Hl r = some w ∧ grfAt GD.gdG a w r := by
  intro hcons hwr hch hcov1 hcov2 hw0 hvis hrd
  refine ownedReadCat GD Hl a r w0 hcons hwr hch ?_ hw0 hvis hrd
  rintro w v hwb (hmo | hpo)
  · exact hcov1 w v hwb hmo
  · exact hcov2 w v hwb hpo

/-! # 5. FORWARDING — the read rule's case (ii), over the cat model

`w` is the hart's last same-byte write po-before `r` and is NOT gmo-before it.
Then `w` IS the rf-source of `r` at `a`, with the po-EARLIER case closed by RULE 1
instead of `gpoloc`.  The hypotheses are exactly what it consumes: `gwf`,
load-value and RULE 1. -/

theorem ownForwardCat (G : Gexec) (a : Int) (w r : Geid) (v : BitVec 8) (t : Nat) (vr : BitVec 8) :
    gwf G → (∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) → gloadValue G →
    WeakRvwmoGraph.gpo G w r → gwritesByte G w a v → greadsByte G r a t vr →
    ¬ gmoLt G w r →
    (∀ w' v', gwritesByte G w' a v' → WeakRvwmoGraph.gpo G w w' →
      WeakRvwmoGraph.gpo G w' r → False) →
    grfAt G a w r ∧ vr = v := by
  intro hwf hr1 hlv hpo hwb hrd hnmo hnoint
  obtain ⟨ws, hrf, hwbs, hviss, hor⟩ := ownForwardWeak G a w r v t vr hwf hlv hpo hwb hrd
  rcases hor with heq | hco
  · subst heq
    exact ⟨hrf, gwritesByteDet G ws a vr v hwbs hwb⟩
  exfalso
  have hmows := gcoGmo G w ws hwf hco
  -- `ws` is visible; the gmo disjunct would compose to `gmoLt w r`
  have hposr : WeakRvwmoGraph.gpo G ws r := by
    rcases hviss with hmo | hp
    · exact absurd (gmoLtTrans G _ _ _ hmows hmo) hnmo
    · exact hp
  obtain ⟨hag1, _, hs1, _⟩ := hpo
  obtain ⟨hag2, hlt2, hs3, hs4⟩ := hposr
  have hag : ws.1 = w.1 := hag2.trans hag1.symm
  by_cases hlt : w.2 < ws.2
  · -- `ws` is po-BETWEEN `w` and `r`: killed by the hypothesis
    exact hnoint ws vr hwbs ⟨hag.symm, hlt, hs1, hs3⟩ ⟨hag2, hlt2, hs3, hs4⟩
  · by_cases heq2 : w.2 = ws.2
    · -- same event: `gco` is irreflexive through `gmo`
      have hwe : w = ws := Prod.ext hag.symm heq2
      subst hwe
      exact gmoLtIrrefl G _ hmows
    · -- `ws` is po-EARLIER and `w` WRITES the byte: RULE 1
      have hmosw : gmoLt G ws w :=
        hr1 ws w ⟨⟨hag, by omega, hs3, hs1⟩, a, Or.inl ⟨vr, hwbs⟩, v, hwb⟩
      exact gmoLtIrrefl G _ (gmoLtTrans G _ _ _ hmosw hmows)

/-- The model-level form. -/
theorem ownForwardCat' (GD : Gdexec) (a : Int) (w r : Geid) (v : BitVec 8) (t : Nat)
    (vr : BitVec 8) :
    rvwmoCatConsistent GD →
    WeakRvwmoGraph.gpo GD.gdG w r → gwritesByte GD.gdG w a v →
    greadsByte GD.gdG r a t vr →
    ¬ gmoLt GD.gdG w r →
    (∀ w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w w' →
      WeakRvwmoGraph.gpo GD.gdG w' r → False) →
    grfAt GD.gdG a w r ∧ vr = v := by
  rintro ⟨hwf, hppo, hlv, _⟩
  exact ownForwardCat GD.gdG a w r v t vr hwf (fun e1 e2 h => hppo e1 e2 (Or.inl (Or.inl h))) hlv

/-! # 7. EPOCHS AND THE IDENTITY STOP -/

/-! ## 7.1 `ownedReadEpoch` -/

/-- The token's history is GMO-chained. -/
def gmoChain (G : Gexec) (Hl : List Geid) : Prop :=
  chainWith (gmoLt G) Hl

/-- EPOCH COVERAGE: every same-byte write visible to `r` is in the history or
co-before the boundary `b`. -/
def epochCov (G : Gexec) (Hl : List Geid) (a : Int) (b r : Geid) : Prop :=
  ∀ w v, gwritesByte G w a v → gvisible G w r → w ∈ Hl ∨ gco G w b

/-- THE LEMMA, with `gvisible G b r` ADDED (without it: `epcRefutesInvisibleBoundary`).
Bonus conclusion: the source is `b` or co-after it. -/
theorem ownedReadEpoch (G : Gexec) (Hl : List Geid) (a : Int) (r b : Geid) :
    gwf G → gloadValue G →
    (∀ w, w ∈ Hl → ∃ v, gwritesByte G w a v) →
    gmoChain G Hl →
    b ∈ Hl → gvisible G b r →
    epochCov G Hl a b r →
    (∃ t v, greadsByte G r a t v) →
    ∃ w, lastVisible G Hl r = some w ∧ grfAt G a w r ∧ (w = b ∨ gco G b w) := by
  rintro hwf hlv hwrites hch hb hvisb hcov ⟨t, v, hrd⟩
  obtain ⟨vb, hwbb⟩ := hwrites b hb
  obtain ⟨ws, hrf, hwbs, hviss⟩ := grfAtExists G r a t v b vb hwf hlv hrd hwbb hvisb
  have hbs := grfAtComax G a ws r b vb hwf hlv hrf hwbb hvisb
  have hgws := gwritesByteGwrites G ws a v hwf hwbs
  have hgb := gwritesByteGwrites G b a vb hwf hwbb
  -- the source is in the history: the co-before-`b` arm is killed by
  -- co-maximality at `b`
  have hins : ws ∈ Hl := by
    rcases hcov ws v hwbs hviss with h | ⟨_, _, _, _, _, hlt⟩
    · exact h
    · omega
  obtain ⟨k, hk⟩ := elem_of_list_lookup_1 hins
  obtain ⟨w, hlast⟩ := someOfIsSome
    (lastSuchIsSome (fun u => gvisible G u r) (fun u => gvisibleDec G u r) Hl k ws hk hviss)
  refine ⟨w, hlast, ?_⟩
  obtain ⟨m, hm, hvisw, hmax⟩ := lastSuchSpec _ _ _ _ hlast
  have hkm : k = m := by
    by_cases hne : k = m
    · exact hne
    exfalso
    have hkm' := hmax k ws hk hviss
    have hlt : k < m := by omega
    obtain ⟨vw, hwbw⟩ := hwrites w (elem_of_list_lookup_2 hm)
    obtain ⟨_, _, hpos⟩ := chainWithGmo G (gmoLt G) Hl k m ws w (fun _ _ h => h) hch hk hm hlt
    have hgw := gwritesByteGwrites G w a vw hwf hwbw
    have h1 := (gwixGposLt G ws w hwf.1 hgws hgw).2 hpos
    have h2 := grfAtComax G a ws r w vw hwf hlv hrf hwbw hvisw
    omega
  subst hkm
  rw [hk, Option.some.injEq] at hm
  subst hm
  refine ⟨hrf, ?_⟩
  by_cases heq : gwix G b = gwix G ws
  · exact Or.inl (gwixInj G b ws hwf.1 hgb hgws heq).symm
  · exact Or.inr ⟨a, vb, v, hwbb, hwbs, by omega⟩

/-- The consumable forms: the last entry visible ⇒ it is the source ... -/
theorem ownedReadEpochSnoc (G : Gexec) (Hl0 : List Geid) (wl : Geid) (a : Int) (r b : Geid) :
    gwf G → gloadValue G →
    (∀ w, w ∈ Hl0 ++ [wl] → ∃ v, gwritesByte G w a v) →
    gmoChain G (Hl0 ++ [wl]) →
    b ∈ Hl0 ++ [wl] → gvisible G b r →
    epochCov G (Hl0 ++ [wl]) a b r →
    gvisible G wl r →
    (∃ t v, greadsByte G r a t v) →
    grfAt G a wl r := by
  intro hwf hlv hwrites hch hb hvisb hcov hvisl hrd
  obtain ⟨w, hlast, hrf, _⟩ :=
    ownedReadEpoch G (Hl0 ++ [wl]) a r b hwf hlv hwrites hch hb hvisb hcov hrd
  have hsn : lastVisible G (Hl0 ++ [wl]) r = some wl := lastSuchSnoc _ _ _ _ hvisl
  rw [hsn, Option.some.injEq] at hlast
  subst hlast
  exact hrf

/-- ... ⇒ the value read is the value it wrote. -/
theorem ownedReadEpochValue (G : Gexec) (Hl0 : List Geid) (wl : Geid) (a : Int) (r b : Geid)
    (t : Nat) (v vl : BitVec 8) :
    gwf G → gloadValue G →
    (∀ w, w ∈ Hl0 ++ [wl] → ∃ v', gwritesByte G w a v') →
    gmoChain G (Hl0 ++ [wl]) →
    b ∈ Hl0 ++ [wl] → gvisible G b r →
    epochCov G (Hl0 ++ [wl]) a b r →
    gvisible G wl r →
    greadsByte G r a t v →
    gwritesByte G wl a vl →
    v = vl := by
  intro hwf hlv hwrites hch hb hvisb hcov hvisl hrd hwbl
  exact grfAtValue G a wl r t v vl hlv
    (ownedReadEpochSnoc G Hl0 wl a r b hwf hlv hwrites hch hb hvisb hcov hvisl ⟨t, v, hrd⟩)
    hrd hwbl

/-- Plain coverage is epoch coverage (any boundary). -/
theorem epochCovOfCov (G : Gexec) (Hl : List Geid) (a : Int) (b r : Geid) :
    (∀ w v, gwritesByte G w a v → gvisible G w r → w ∈ Hl) →
    epochCov G Hl a b r :=
  fun hcov w v hwb hvis => Or.inl (hcov w v hwb hvis)

/-! ## 7.2 The tie invariant in GMO form, and the read rule's cases

Per tie: `last H` is gmo-before the tie, or it is a same-hart po-earlier WRITE. -/

def tieInv (G : Gexec) (Hl : List Geid) (tie : Geid) : Prop :=
  ∃ wl, Hl.getLast? = some wl ∧
    (gmoLt G wl tie ∨ (WeakRvwmoGraph.gpo G wl tie ∧ glblIs G wl lbIsW))

/-- A tie gmo-before the read makes `last H` visible to it. -/
theorem tieInvVisible (G : Gexec) (Hl : List Geid) (tie r : Geid) :
    tieInv G Hl tie → gmoLt G tie r → WeakRvwmoGraph.gpo G tie r →
    ∃ wl, Hl.getLast? = some wl ∧ gvisible G wl r := by
  rintro ⟨wl, hlast, hmo | ⟨hpo, _⟩⟩ htr hpo'
  · exact ⟨wl, hlast, Or.inl (gmoLtTrans G _ _ _ hmo htr)⟩
  · exact ⟨wl, hlast, Or.inr (gpoTrans G _ _ _ hpo hpo')⟩

/-- CASE (i): some tie is gmo-before `r`.  Then `last H` is the rf-source —
under EPOCH coverage with `last H` as its own boundary. -/
theorem tieReadI (G : Gexec) (Hl : List Geid) (a : Int) (tie r wl : Geid) :
    gwf G → gloadValue G →
    (∀ w, w ∈ Hl → ∃ v, gwritesByte G w a v) →
    gmoChain G Hl →
    Hl.getLast? = some wl →
    tieInv G Hl tie → gmoLt G tie r → WeakRvwmoGraph.gpo G tie r →
    epochCov G Hl a wl r →
    (∃ t v, greadsByte G r a t v) →
    grfAt G a wl r := by
  intro hwf hlv hwr hch hlast htie hmo hpo hcov hrd
  obtain ⟨wl', hlast', hvis⟩ := tieInvVisible G Hl tie r htie hmo hpo
  rw [hlast, Option.some.injEq] at hlast'
  subst hlast'
  obtain ⟨Hl0, rfl⟩ := last_Some.1 hlast
  have hin : wl ∈ Hl0 ++ [wl] := elem_of_app.2 (Or.inr (elem_of_list_singleton.2 rfl))
  exact ownedReadEpochSnoc G Hl0 wl a r wl hwf hlv hwr hch hin hvis hcov hvis hrd

/-- ... with the tie a member of `S`. -/
theorem tieReadIS (G : Gexec) (Hl S : List Geid) (a : Int) (r wl : Geid) :
    gwf G → gloadValue G →
    (∀ w, w ∈ Hl → ∃ v, gwritesByte G w a v) →
    gmoChain G Hl →
    Hl.getLast? = some wl →
    (∀ e, e ∈ S → tieInv G Hl e ∧ WeakRvwmoGraph.gpo G e r) →
    (∃ e, e ∈ S ∧ gmoLt G e r) →
    epochCov G Hl a wl r →
    (∃ t v, greadsByte G r a t v) →
    grfAt G a wl r := by
  rintro hwf hlv hwr hch hlast hS ⟨e, he, hmo⟩ hcov hrd
  obtain ⟨htie, hpo⟩ := hS e he
  exact tieReadI G Hl a e r wl hwf hlv hwr hch hlast htie hmo hpo hcov hrd

/-- CASE (ii): ALL of `S` is not gmo-before `r`.  `ownForwardCat'` verbatim. -/
theorem tieReadIi (GD : Gdexec) (S : List Geid) (a : Int) (w r : Geid) (v : BitVec 8) (t : Nat)
    (vr : BitVec 8) :
    rvwmoCatConsistent GD →
    w ∈ S → (∀ e, e ∈ S → ¬ gmoLt GD.gdG e r) →
    WeakRvwmoGraph.gpo GD.gdG w r → gwritesByte GD.gdG w a v →
    greadsByte GD.gdG r a t vr →
    (∀ w' v', gwritesByte GD.gdG w' a v' → WeakRvwmoGraph.gpo GD.gdG w w' →
      WeakRvwmoGraph.gpo GD.gdG w' r → False) →
    grfAt GD.gdG a w r ∧ vr = v := by
  intro hcons hw hS hpo hwb hrd hnoint
  exact ownForwardCat' GD a w r v t vr hcons hpo hwb hrd (hS w hw) hnoint

local instance gmoLtDecCat (G : Gexec) (e1 e2 : Geid) : Decidable (gmoLt G e1 e2) := by
  unfold gmoLt; infer_instance

/-- The exhaustive split between the two cases. -/
theorem tieCases (G : Gexec) (S : List Geid) (r : Geid) :
    (∃ e, e ∈ S ∧ gmoLt G e r) ∨ (∀ e, e ∈ S → ¬ gmoLt G e r) := by
  induction S with
  | nil => exact Or.inr (fun e he => absurd he List.not_mem_nil)
  | cons e S ih =>
    by_cases h : gmoLt G e r
    · exact Or.inl ⟨e, elem_of_cons.2 (Or.inl rfl), h⟩
    rcases ih with ⟨e', he', h'⟩ | hall
    · exact Or.inl ⟨e', elem_of_cons.2 (Or.inr he'), h'⟩
    · refine Or.inr (fun e' he' => ?_)
      rcases elem_of_cons.1 he' with rfl | he'
      · exact h
      · exact hall e' he'

/-- THE ACQUIRE CASE: an `.aq` arrival event po-before `r` (rule 5) makes case
(ii) impossible under `gppoCatGmo`. -/
theorem tieAcqCase (GD : Gdexec) (S : List Geid) (acq r : Geid) :
    gppoCatGmo GD → acq ∈ S → gacqPo GD.gdG acq r →
    ¬ (∀ e, e ∈ S → ¬ gmoLt GD.gdG e r) :=
  fun hppo hin hacq hall =>
    hall acq hin (hppo acq r (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hacq)))))))

/-! ## 7.3 THE IDENTITY-STOP LEMMA (pure, on rows)

An event's IDENTITY: kind, base, byte count, the aq/rl bits and the (inert) write
class — never a value or a timestamp. -/

inductive IdentT where
  | IdLoad (aq : Bool) (base : Int) (n : Nat)
  | IdStore (rl : Bool) (base : Int) (n : Nat) (k : WmClass)
  | IdFence (pr pw sr sw : Bool)
  | IdRmw (aq rl : Bool) (base : Int) (n : Nat) (k : WmClass)
  /-- W13 (E): an I/O-class event's identity (kind, base, byte count). -/
  | IdIo (kind : IoKind) (base : Int) (n : Nat)
  deriving DecidableEq

def AxGraphCat.ident (l : Lbl) : IdentT :=
  match l with
  | LLoad aq base ts _ => .IdLoad aq base ts.length
  | LStore rl base vs k => .IdStore rl base vs.length k
  | LFence pr pw sr sw => .IdFence pr pw sr sw
  | LRmw aq rl base ts _ _ k => .IdRmw aq rl base ts.length k
  | LIo kd base vs => .IdIo kd base vs.length

def identAgree (rowExp rowReal : List Lbl) (j : Nat) : Prop :=
  (rowExp[j]?).map AxGraphCat.ident = (rowReal[j]?).map AxGraphCat.ident

/-- THE STOP: the least position at which the identities differ (a length
mismatch counts as a difference at the shorter row's end); `none` when the rows
agree in identity throughout. -/
def identStopFrom (k : Nat) : List Lbl → List Lbl → Option Nat
  | [], [] => none
  | le :: e', lr :: r' =>
    if AxGraphCat.ident le = AxGraphCat.ident lr then identStopFrom (k + 1) e' r' else some k
  | _, _ => some k

def identStop (rowExp rowReal : List Lbl) : Option Nat :=
  identStopFrom 0 rowExp rowReal

theorem identStopFromSome (k : Nat) (e r : List Lbl) (s : Nat) :
    identStopFrom k e r = some s →
    k ≤ s ∧
    (∀ j : Nat, j < s - k → (e[j]?).map AxGraphCat.ident = (r[j]?).map AxGraphCat.ident) ∧
    (e[s - k]?).map AxGraphCat.ident ≠ (r[s - k]?).map AxGraphCat.ident := by
  induction e generalizing k r with
  | nil =>
    cases r with
    | nil => simp [identStopFrom]
    | cons lr r =>
      simp only [identStopFrom, Option.some.injEq]
      rintro rfl
      refine ⟨Nat.le_refl _, fun j hj => by omega, ?_⟩
      simp
  | cons le e ih =>
    cases r with
    | nil =>
      simp only [identStopFrom, Option.some.injEq]
      rintro rfl
      refine ⟨Nat.le_refl _, fun j hj => by omega, ?_⟩
      simp
    | cons lr r =>
      by_cases heq : AxGraphCat.ident le = AxGraphCat.ident lr
      · simp only [identStopFrom, heq, if_true]
        intro h
        obtain ⟨hle, hag, hne⟩ := ih (k + 1) r h
        refine ⟨by omega, ?_, ?_⟩
        · intro j hj
          cases j with
          | zero => simp [heq]
          | succ j => simpa using hag j (by omega)
        · have hs : s - k = (s - (k + 1)) + 1 := by omega
          rw [hs]
          simpa using hne
      · simp only [identStopFrom, heq, if_false, Option.some.injEq]
        rintro rfl
        refine ⟨Nat.le_refl _, fun j hj => by omega, ?_⟩
        simpa using heq

theorem identStopFromNone (k : Nat) (e r : List Lbl) :
    identStopFrom k e r = none →
    ∀ j : Nat, (e[j]?).map AxGraphCat.ident = (r[j]?).map AxGraphCat.ident := by
  induction e generalizing k r with
  | nil =>
    cases r with
    | nil => intro _ j; simp
    | cons lr r => simp [identStopFrom]
  | cons le e ih =>
    cases r with
    | nil => simp [identStopFrom]
    | cons lr r =>
      by_cases heq : AxGraphCat.ident le = AxGraphCat.ident lr
      · simp only [identStopFrom, heq, if_true]
        intro h j
        cases j with
        | zero => simp [heq]
        | succ j => simpa using ih (k + 1) r h j
      · simp [identStopFrom, heq]

/-- The spec of `identStop`: agreement strictly below the stop, disagreement at
it — so it IS the least disagreeing position. -/
theorem identStopSome (rowExp rowReal : List Lbl) (s : Nat) :
    identStop rowExp rowReal = some s →
    (∀ j, j < s → identAgree rowExp rowReal j) ∧ ¬ identAgree rowExp rowReal s := by
  intro h
  obtain ⟨_, hag, hne⟩ := identStopFromSome 0 _ _ _ h
  rw [Nat.sub_zero] at hne
  exact ⟨fun j hj => hag j (by omega), hne⟩

theorem identStopNone (rowExp rowReal : List Lbl) :
    identStop rowExp rowReal = none → ∀ j, identAgree rowExp rowReal j :=
  identStopFromNone 0 rowExp rowReal

/-- `ident` agrees ⇒ kind agrees. -/
theorem identIsW (le lr : Lbl) : AxGraphCat.ident le = AxGraphCat.ident lr → lbIsW le = lbIsW lr := by
  cases le <;> cases lr <;> intro h <;> first | rfl | cases h

theorem identIsR (le lr : Lbl) : AxGraphCat.ident le = AxGraphCat.ident lr → lbIsR le = lbIsR lr := by
  cases le <;> cases lr <;> intro h <;> first | rfl | cases h

/-- THE DEPENDENCY SIDE.  `dCovers D row stop`: every WRITE of the row at or after
`stop` `D`-depends on a READ strictly before `stop`.  `dGmo`: `D`'s edges are
gmo-forward. -/
def dCovers (D : Nat → Nat → Prop) (row : List Lbl) (stop : Nat) : Prop :=
  ∀ k l, stop ≤ k → row[k]? = some l → lbIsW l = true →
    ∃ r lr, r < stop ∧ row[r]? = some lr ∧ lbIsR lr = true ∧ D r k

def dGmo (G : Gexec) (i : Nat) (D : Nat → Nat → Prop) : Prop :=
  ∀ r k, D r k → gmoLt G (i, r) (i, k)

/-- THE ABSTRACT LEMMA: every real write at or after the stop is gmo-after a
pre-stop READ of its hart. -/
theorem identStopWrites (G : Gexec) (i : Nat) (row : List Lbl) (D : Nat → Nat → Prop)
    (stop : Nat) :
    dCovers D row stop → dGmo G i D →
    ∀ k l, stop ≤ k → row[k]? = some l → lbIsW l = true →
      ∃ r lr, r < stop ∧ row[r]? = some lr ∧ lbIsR lr = true ∧ gmoLt G (i, r) (i, k) := by
  intro hcov hgmo k l hk hl hw
  obtain ⟨r, lr, hr, hlr, hrd, hD⟩ := hcov k l hk hl hw
  exact ⟨r, lr, hr, hlr, hrd, hgmo r k hD⟩

/-- THE ROW-LEVEL FORM: `rowReal` is hart `i`'s row of `G`; the stop is computed
from the expected row. -/
theorem identStopLemma (G : Gexec) (i : Nat) (rowExp rowReal : List Lbl)
    (D : Nat → Nat → Prop) (stop : Nat) :
    G.gxProg[i]? = some rowReal →
    identStop rowExp rowReal = some stop →
    dCovers D rowReal stop → dGmo G i D →
    (∀ j, j < stop → identAgree rowExp rowReal j) ∧
    (∀ k, stop ≤ k → glblIs G (i, k) lbIsW →
      ∃ r, r < stop ∧ glblIs G (i, r) lbIsR ∧ gmoLt G (i, r) (i, k)) := by
  intro hrow hstop hcov hgmo
  refine ⟨(identStopSome _ _ _ hstop).1, ?_⟩
  rintro k hk ⟨l, hl, hw⟩
  have hl' : rowReal[k]? = some l := by simpa [gxLbl, hrow] using hl
  obtain ⟨r, lr, hr, hlr, hrd, hmo⟩ := identStopWrites G i rowReal D stop hcov hgmo k l hk hl' hw
  exact ⟨r, hr, ⟨lr, by simp [gxLbl, hrow, hlr], hrd⟩, hmo⟩

/-- With NO stop the two rows agree in identity everywhere. -/
theorem identStopNoneAgree (rowExp rowReal : List Lbl) :
    identStop rowExp rowReal = none →
    ∀ (k : Nat) l, rowReal[k]? = some l →
      ∃ l', rowExp[k]? = some l' ∧ AxGraphCat.ident l' = AxGraphCat.ident l := by
  intro hnone k l hl
  have hag := identStopNone _ _ hnone k
  unfold identAgree at hag
  rw [hl] at hag
  cases he : rowExp[k]? with
  | none => rw [he] at hag; simp at hag
  | some l' =>
    rw [he] at hag
    exact ⟨l', rfl, Option.some.inj hag⟩

/-! ### 7.3.1 `dCovers` over an EDGE LIST, computably -/

theorem forallbAll {A : Type _} (f : A → Bool) (l : List A) :
    l.all f = true ↔ ∀ x, x ∈ l → f x = true := by
  simp

theorem existsbSome {A : Type _} (f : A → Bool) (l : List A) :
    l.any f = true ↔ ∃ x, x ∈ l ∧ f x = true := by
  simp

def isRAt (row : List Lbl) (r : Nat) : Bool :=
  match row[r]? with
  | some l => lbIsR l
  | none => false

def dCoversB (dd : List (Nat × Nat)) (row : List Lbl) (stop : Nat) : Bool :=
  (List.range' stop (row.length - stop)).all (fun k =>
    match row[k]? with
    | some l =>
      !lbIsW l || (List.range' 0 stop).any (fun r => isRAt row r && decide ((r, k) ∈ dd))
    | none => true)

theorem dCoversBSpec (dd : List (Nat × Nat)) (row : List Lbl) (stop : Nat) :
    dCoversB dd row stop = true ↔ dCovers (fun r k => (r, k) ∈ dd) row stop := by
  unfold dCoversB dCovers
  rw [forallbAll]
  constructor
  · intro h k l hk hl hw
    have hin : k ∈ List.range' stop (row.length - stop) := by
      have := lookup_lt_Some hl
      exact elem_of_seq.2 ⟨hk, by omega⟩
    have h1 := h k hin
    simp only [hl, hw, Bool.not_true, Bool.false_or] at h1
    obtain ⟨r, hr, h2⟩ := (existsbSome _ _).1 h1
    rw [Bool.and_eq_true] at h2
    obtain ⟨hrd, hd⟩ := h2
    have hr' := elem_of_seq.1 hr
    unfold isRAt at hrd
    cases hlr : row[r]? with
    | none => rw [hlr] at hrd; cases hrd
    | some lr =>
      rw [hlr] at hrd
      exact ⟨r, lr, by omega, hlr, hrd, of_decide_eq_true hd⟩
  · intro h k hk
    cases hl : row[k]? with
    | none => rfl
    | some l =>
      dsimp only
      cases hw : lbIsW l with
      | false => rfl
      | true =>
        have hk' := elem_of_seq.1 hk
        obtain ⟨r, lr, hr, hlr, hrd, hd⟩ := h k l hk'.1 hl hw
        simp only [Bool.not_true, Bool.false_or]
        have hrin : r ∈ List.range' 0 stop := elem_of_seq.2 ⟨Nat.zero_le _, by omega⟩
        refine (existsbSome _ _).2 ⟨r, hrin, ?_⟩
        rw [Bool.and_eq_true]
        exact ⟨by simp [isRAt, hlr, hrd], decide_eq_true hd⟩

/-- `gdepsGmo` on the hart's own edges IS `dGmo` for the projected relation. -/
theorem dGmoOfGdeps (GD : Gdexec) (i : Nat) :
    gdepsGmo GD.gdG GD.gdDeps →
    dGmo GD.gdG i (fun r k => ((i, r), (i, k)) ∈ GD.gdDeps) :=
  fun hdg r k hd => hdg ((i, r), (i, k)) hd

/-! ## 7.4 Witnesses (by hand: this file is BELOW `AxGraphDec`) -/

/-- The all-zero image (so `t = 0` reads are legal everywhere). -/
def imgZero : Image := fun _ => some b0

/-! ### 7.4.1 `epc`: the boundary must be visible

Byte 0 throughout.  H0: W (h0 = (0,0), v=1); R (r = (0,1)); W (b = (0,2), v=1).
H1: W (w = (1,0), v=2).  gmo = [h0; w; r; b].  `r` reads `w` (t = 2).  History
`[h0; b]` satisfies every hypothesis of the commissioned statement, yet `b` is NOT
visible and the source `w` is outside the history.  The graph is cat-consistent. -/

def epc : Gdexec :=
  ⟨⟨imgZero,
    [[LStore false 0 [b1] .WCplain, LLoad false 0 [2] [b2], LStore false 0 [b1] .WCplain],
     [LStore false 0 [b2] .WCplain]],
    [(0, 0), (1, 0), (0, 1), (0, 2)]⟩,
   []⟩

theorem epcLbl (e : Geid) (l : Lbl) :
    gxLbl epc.gdG e = some l →
    (e = (0, 0) ∧ l = LStore false 0 [b1] .WCplain) ∨
    (e = (0, 1) ∧ l = LLoad false 0 [2] [b2]) ∨
    (e = (0, 2) ∧ l = LStore false 0 [b1] .WCplain) ∨
    (e = (1, 0) ∧ l = LStore false 0 [b2] .WCplain) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | _ | k <;> simp [gxLbl, epc] at hl <;>
    subst hl <;> simp

theorem epcWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte epc.gdG e a v →
    (e = (0, 0) ∧ a = 0 ∧ v = b1) ∨ (e = (0, 2) ∧ a = 0 ∧ v = b1) ∨
    (e = (1, 0) ∧ a = 0 ∧ v = b2) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases epcLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | j <;> simp at hv <;> subst hv <;> simp [accAddr] at ha <;> subst ha <;> simp

theorem epcRd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte epc.gdG e a t v → e = (0, 1) ∧ a = 0 ∧ t = 2 ∧ v = b2 := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases epcLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
    rcases j with _ | j <;> simp at ht hv <;> subst ht hv <;> simp [accAddr] at ha <;>
    subst ha <;> simp

theorem epcWf : gwf epc.gdG := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · intro e
    constructor
    · intro he
      simp only [epc, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · rintro ⟨l, hl, _⟩
      rcases epcLbl e l hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [epc] at hp <;> subst hp <;>
      rcases k with _ | _ | _ | k <;> simp at hk <;> subst hk <;> simp

theorem epcLv : gloadValue epc.gdG := by
  intro e a t v hr
  obtain ⟨rfl, rfl, rfl, rfl⟩ := epcRd e a t v hr
  refine ⟨?_, ?_⟩
  · show ∃ w, gwriteAt epc.gdG 2 = some w ∧ gwritesByte epc.gdG w 0 b2 ∧ gvisible epc.gdG w (0, 1)
    exact ⟨(1, 0), by decide,
      ⟨LStore false 0 [b2] .WCplain, 0, [b2], 0, rfl, rfl, rfl, by simp [accAddr]⟩,
      Or.inl (by decide)⟩
  · intro w' v' hw' hvis
    rcases epcWr w' _ v' hw' with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · decide
    · exfalso
      rcases hvis with h | ⟨_, h, _⟩
      · exact absurd h (by decide)
      · simp at h
    · decide

theorem epcCat : rvwmoCatConsistent epc := by
  refine ⟨epcWf, ?_, epcLv, ?_, ?_, ?_⟩
  · rintro e1 e2 (h | h)
    · rcases h with h | h | h | h | h | h
      · -- rule 1: both edges into `b` are gmo-forward
        obtain ⟨⟨hag, hlt, _, _⟩, a, h1, v, h2⟩ := h
        rcases epcWr _ _ _ h2 with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
        · simp at hlt
        · rcases h1 with ⟨v', hw⟩ | ⟨t, v', hr⟩
          · rcases epcWr _ _ _ hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
            · decide
            · simp at hlt
            · simp at hag
          · obtain ⟨rfl, _⟩ := epcRd _ _ _ _ hr
            decide
        · simp at hlt
      · exfalso
        obtain ⟨⟨_, hlt, _⟩, a, t1, v1, t2, v2, h1, h2, _⟩ := h
        obtain ⟨rfl, _⟩ := epcRd _ _ _ _ h1
        obtain ⟨rfl, _⟩ := epcRd _ _ _ _ h2
        simp at hlt
      · exfalso
        obtain ⟨_, ⟨l, hl, hrmw⟩, _⟩ := h
        rcases epcLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
          simp [lbIsRmw, lbIsR, lbIsW] at hrmw
      · exfalso
        obtain ⟨pr, pw, sr, sw, ⟨_, _, kf, _, _, hlf⟩, _⟩ := h
        rcases epcLbl _ _ hlf with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
      · exfalso
        obtain ⟨_, ⟨l, hl, _⟩, ⟨l', hl', haq⟩, _⟩ := h
        rw [hl, Option.some.injEq] at hl'
        subst hl'
        rcases epcLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbAq] at haq
      · exfalso
        obtain ⟨_, ⟨l, hl, hrc⟩, _⟩ := h
        rcases epcLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
          simp [lbRcsc, lbAq, lbRl] at hrc
    · exfalso
      obtain ⟨_, m, hd, _⟩ := h
      simp [epc] at hd
  · rintro e a t v hr ⟨l, hl, hw⟩
    obtain ⟨rfl, _⟩ := epcRd _ _ _ _ hr
    simp [gxLbl, epc] at hl
    subst hl
    simp [lbIsW] at hw
  · intro rw hrw
    simp [epc] at hrw
  · intro rw hrw
    simp [epc] at hrw

/-- The read's source, computed: `w = (1,0)`. -/
theorem epcRf : grfAt epc.gdG 0 (1, 0) (0, 1) :=
  ⟨2, b2, ⟨LLoad false 0 [2] [b2], 0, [2], [b2], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩,
    by decide⟩

/-- THE REFUTATION of the commissioned (boundary-not-required-visible) statement. -/
theorem epcRefutesInvisibleBoundary :
    let Hl : List Geid := [(0, 0), (0, 2)]
    let r : Geid := (0, 1)
    let b : Geid := (0, 2)
    (∀ w, w ∈ Hl → ∃ v, gwritesByte epc.gdG w 0 v) ∧
    gmoChain epc.gdG Hl ∧
    b ∈ Hl ∧
    epochCov epc.gdG Hl 0 b r ∧
    ((0, 0) : Geid) ∈ Hl ∧ gvisible epc.gdG (0, 0) r ∧
    (∃ t v, greadsByte epc.gdG r 0 t v) ∧
    ¬ gvisible epc.gdG b r ∧
    ¬ (∃ w, w ∈ Hl ∧ grfAt epc.gdG 0 w r) := by
  dsimp only
  refine ⟨?_, ?_, by decide, ?_, by decide, Or.inl (by decide), ?_, ?_, ?_⟩
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;>
      exact ⟨b1, LStore false 0 [b1] .WCplain, 0, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩
  · intro i w1 w2 h1 h2
    rcases i with _ | _ | i <;> simp at h1 h2
    subst h1 h2
    decide
  · intro w v hw _
    rcases epcWr _ _ _ hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · refine Or.inr ⟨0, b2, b1, ?_, ?_, by decide⟩
      · exact ⟨LStore false 0 [b2] .WCplain, 0, [b2], 0, rfl, rfl, rfl, by simp [accAddr]⟩
      · exact ⟨LStore false 0 [b1] .WCplain, 0, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩
  · exact ⟨2, b2, LLoad false 0 [2] [b2], 0, [2], [b2], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩
  · rintro (h | ⟨_, h, _⟩)
    · exact absurd h (by decide)
    · simp at h
  · rintro ⟨w, hw, hrf⟩
    have := grfAtDet _ _ _ _ _ hrf epcRf
    subst this
    simp at hw

/-- ... and the CORRECTED lemma is non-vacuous on the same graph: history
`[h0; w]`, VISIBLE boundary `w`. -/
theorem epcEpochPositive :
    ∃ w, lastVisible epc.gdG [(0, 0), (1, 0)] (0, 1) = some w ∧
      grfAt epc.gdG 0 w (0, 1) ∧
      (w = (1, 0) ∨ gco epc.gdG (1, 0) w) := by
  refine ownedReadEpoch epc.gdG _ 0 (0, 1) (1, 0) epcWf epcLv ?_ ?_ (by decide) (Or.inl (by decide))
    ?_ ?_
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨b1, LStore false 0 [b1] .WCplain, 0, [b1], 0, rfl, rfl, rfl, by simp [accAddr]⟩
    · exact ⟨b2, LStore false 0 [b2] .WCplain, 0, [b2], 0, rfl, rfl, rfl, by simp [accAddr]⟩
  · intro i w1 w2 h1 h2
    rcases i with _ | _ | i <;> simp at h1 h2
    subst h1 h2
    decide
  · intro w v hw hvis
    rcases epcWr _ _ _ hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl (by decide)
    · exfalso
      rcases hvis with h | ⟨_, h, _⟩
      · exact absurd h (by decide)
      · simp at h
    · exact Or.inl (by decide)
  · exact ⟨2, b2, LLoad false 0 [2] [b2], 0, [2], [b2], 0, rfl, rfl, rfl, rfl, by simp [accAddr]⟩

/-! ### 7.4.2 `isw`: the review-4 F1 graph

Addresses: y = 0, z = 3; the first load's value is the second load's base (a0 = 2
in the REAL run, a0 = 1 in the EXPECTED run).  H0 (real): `ld a0,[y]` (0,0) reads
H1's store (t = 2, value 2); `ld a1,0(a0)` = `ld [2]` (0,1) reads the image;
`sd [z]` (0,2), value 1.  H1: `sd [y] = 2` (1,0).  gmo = [sd [z]; sd [y]; ld [y];
ld [2]] — THE STORE FIRST.  The tree's `gdDeps` for this row is EMPTY, so the cat
model ADMITS the order (`iswCat`); `dCovers` fails for the empty edge list and
the lemma's conclusion is FALSE here.  With the GENERAL rule-13 edge (0,2) the
same order violates `gdepsGmo`, and on the repaired order `iswOk` the lemma
yields the store gmo-after the first load. -/

def iswRowReal : List Lbl :=
  [LLoad false 0 [2] [b2], LLoad false 2 [0] [b0], LStore false 3 [b1] .WCplain]

def iswRowExp : List Lbl :=
  [LLoad false 0 [2] [b1], LLoad false 1 [0] [b0], LStore false 3 [b1] .WCplain]

def isw : Gdexec :=
  ⟨⟨imgZero, [iswRowReal, [LStore false 0 [b2] .WCplain]],
    [(0, 2), (1, 0), (0, 0), (0, 1)]⟩,
   []⟩

theorem iswLbl (e : Geid) (l : Lbl) :
    gxLbl isw.gdG e = some l →
    (e = (0, 0) ∧ l = LLoad false 0 [2] [b2]) ∨
    (e = (0, 1) ∧ l = LLoad false 2 [0] [b0]) ∨
    (e = (0, 2) ∧ l = LStore false 3 [b1] .WCplain) ∨
    (e = (1, 0) ∧ l = LStore false 0 [b2] .WCplain) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | _ | k <;>
    simp [gxLbl, isw, iswRowReal] at hl <;> subst hl <;> simp

theorem iswWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte isw.gdG e a v →
    (e = (0, 2) ∧ a = 3 ∧ v = b1) ∨ (e = (1, 0) ∧ a = 0 ∧ v = b2) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases iswLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbWr] at hwr <;> obtain ⟨rfl, rfl⟩ := hwr <;>
    rcases j with _ | j <;> simp at hv <;> subst hv <;> simp [accAddr] at ha <;> subst ha <;> simp

theorem iswRd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte isw.gdG e a t v →
    (e = (0, 0) ∧ a = 0 ∧ t = 2 ∧ v = b2) ∨
    (e = (0, 1) ∧ a = 2 ∧ t = 0 ∧ v = b0) := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases iswLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbRd] at hrd <;> obtain ⟨rfl, rfl, rfl⟩ := hrd <;>
    rcases j with _ | j <;> simp at ht hv <;> subst ht hv <;> simp [accAddr] at ha <;>
    subst ha <;> simp

theorem iswWf : gwf isw.gdG := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · intro e
    constructor
    · intro he
      simp only [isw, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · rintro ⟨l, hl, _⟩
      rcases iswLbl e l hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [isw, iswRowReal] at hp <;> subst hp <;>
      rcases k with _ | _ | _ | k <;> simp at hk <;> subst hk <;> simp

theorem iswLv : gloadValue isw.gdG := by
  intro e a t v hr
  rcases iswRd e a t v hr with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · show ∃ w, gwriteAt isw.gdG 2 = some w ∧ gwritesByte isw.gdG w 0 b2 ∧
        gvisible isw.gdG w (0, 0)
      exact ⟨(1, 0), by decide,
        ⟨LStore false 0 [b2] .WCplain, 0, [b2], 0, rfl, rfl, rfl, by simp [accAddr]⟩,
        Or.inl (by decide)⟩
    · intro w' v' hw' _
      rcases iswWr w' _ v' hw' with ⟨rfl, ha, _⟩ | ⟨rfl, _⟩
      · simp at ha
      · decide
  · refine ⟨rfl, ?_⟩
    intro w' v' hw' _
    rcases iswWr w' _ v' hw' with ⟨_, ha, _⟩ | ⟨_, ha, _⟩ <;> simp at ha

/-- THE ADMISSION: the tree's model, with its untagged deps, accepts `sd [z]`
gmo-before `ld [y]`. -/
theorem iswCat : rvwmoCatConsistent isw := by
  refine ⟨iswWf, ?_, iswLv, ?_, ?_, ?_⟩
  · rintro e1 e2 (h | h) <;> exfalso
    · rcases h with h | h | h | h | h | h
      · obtain ⟨⟨hag, hlt, _, _⟩, a, h1, v, h2⟩ := h
        rcases iswWr _ _ _ h2 with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
        · rcases h1 with ⟨v', hw⟩ | ⟨t, v', hr⟩
          · rcases iswWr _ _ _ hw with ⟨rfl, _⟩ | ⟨rfl, ha, _⟩
            · simp at hlt
            · simp at ha
          · rcases iswRd _ _ _ _ hr with ⟨rfl, ha, _⟩ | ⟨rfl, ha, _⟩ <;> simp at ha
        · simp at hlt
      · obtain ⟨⟨_, hlt, _⟩, a, t1, v1, t2, v2, h1, h2, _⟩ := h
        rcases iswRd _ _ _ _ h1 with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;>
          rcases iswRd _ _ _ _ h2 with ⟨rfl, ha, _⟩ | ⟨rfl, ha, _⟩ <;>
          simp at hlt ha
      · obtain ⟨_, ⟨l, hl, hrmw⟩, _⟩ := h
        rcases iswLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
          simp [lbIsRmw, lbIsR, lbIsW] at hrmw
      · obtain ⟨pr, pw, sr, sw, ⟨_, _, kf, _, _, hlf⟩, _⟩ := h
        rcases iswLbl _ _ hlf with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
      · obtain ⟨_, ⟨l, hl, _⟩, ⟨l', hl', haq⟩, _⟩ := h
        rw [hl, Option.some.injEq] at hl'
        subst hl'
        rcases iswLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbAq] at haq
      · obtain ⟨_, ⟨l, hl, hrc⟩, _⟩ := h
        rcases iswLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
          simp [lbRcsc, lbAq, lbRl] at hrc
    · obtain ⟨_, m, hd, _⟩ := h
      simp [isw] at hd
  · rintro e a t v hr ⟨l, hl, hw⟩
    rcases iswRd _ _ _ _ hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
      simp [gxLbl, isw, iswRowReal] at hl <;> subst hl <;> simp [lbIsW] at hw
  · intro rw hrw
    simp [isw] at hrw
  · intro rw hrw
    simp [isw] at hrw

/-- The identity stop is position 1 (the address-dependent load), by computation. -/
theorem iswIdentStop : identStop iswRowExp iswRowReal = some 1 := by decide

/-- `dCovers` FAILS for the tree's (empty) edge list at `stop = 1`. -/
theorem iswDCoversFails :
    dCoversB [] iswRowReal 1 = false ∧
    ¬ dCovers (fun r k => (r, k) ∈ ([] : List (Nat × Nat))) iswRowReal 1 := by
  refine ⟨by decide, ?_⟩
  intro hcov
  obtain ⟨r, lr, _, _, _, hd⟩ := hcov 2 (LStore false 3 [b1] .WCplain) (by omega) rfl rfl
  simp at hd

/-- ... and the lemma's CONCLUSION is false on `isw`: the unannotated store is
gmo-BEFORE the only pre-stop read. -/
theorem iswWriteBeforeRead :
    ¬ (∃ r lr, r < 1 ∧ iswRowReal[r]? = some lr ∧ lbIsR lr = true ∧
        gmoLt isw.gdG (0, r) (0, 2)) := by
  rintro ⟨r, lr, hr, _, _, h⟩
  have : r = 0 := by omega
  subst this
  exact absurd h (by decide)

/-- With the general rule-13 edge (0,2): `dCovers` HOLDS by computation, and
`isw`'s order violates `gdepsGmo`. -/
def isw13 : Gdexec := ⟨isw.gdG, [((0, 0), (0, 2))]⟩

theorem isw13DCovers :
    dCoversB [(0, 2)] iswRowReal 1 = true ∧
    dCovers (fun r k => (r, k) ∈ [((0 : Nat), (2 : Nat))]) iswRowReal 1 :=
  ⟨by decide, (dCoversBSpec _ _ _).1 (by decide)⟩

theorem isw13NotGmo : ¬ gdepsGmo isw13.gdG isw13.gdDeps := by
  intro h
  have hlt := h ((0, 0), (0, 2)) (by simp [isw13])
  exact absurd hlt (by decide)

/-- The repaired order: `ld [y]` (t = 1 now), `ld [2]`, `sd [z]` after `sd [y]`.
Same identities as `iswRowReal`. -/
def iswOkRow : List Lbl :=
  [LLoad false 0 [1] [b2], LLoad false 2 [0] [b0], LStore false 3 [b1] .WCplain]

def iswOk : Gdexec :=
  ⟨⟨imgZero, [iswOkRow, [LStore false 0 [b2] .WCplain]],
    [(1, 0), (0, 0), (0, 1), (0, 2)]⟩,
   [((0, 0), (0, 2))]⟩

theorem iswOkSameIdent : iswOkRow.map AxGraphCat.ident = iswRowReal.map AxGraphCat.ident := by
  decide

theorem iswOkGdepsGmo : gdepsGmo iswOk.gdG iswOk.gdDeps := by
  intro rw hrw
  simp only [iswOk, List.mem_cons, List.not_mem_nil, or_false] at hrw
  subst hrw
  decide

/-- The lemma, instantiated: with the rule-13 edge the stop is still 1 and the
store at 2 is gmo-after the first load. -/
theorem iswOkConclusion :
    (∀ j, j < 1 → identAgree iswRowExp iswOkRow j) ∧
    (∀ k, 1 ≤ k → glblIs iswOk.gdG (0, k) lbIsW →
      ∃ r, r < 1 ∧ glblIs iswOk.gdG (0, r) lbIsR ∧ gmoLt iswOk.gdG (0, r) (0, k)) := by
  refine identStopLemma iswOk.gdG 0 iswRowExp iswOkRow
    (fun r k => ((0, r), (0, k)) ∈ iswOk.gdDeps) 1 rfl (by decide) ?_
    (dGmoOfGdeps iswOk 0 iswOkGdepsGmo)
  intro k l hk hl hw
  rcases k with _ | _ | _ | k <;> simp [iswOkRow] at hl
  · omega
  · subst hl
    simp [lbIsW] at hw
  · subst hl
    exact ⟨0, LLoad false 0 [1] [b2], by omega, rfl, rfl, by simp [iswOk]⟩

/-- The concrete reading of that conclusion. -/
theorem iswOkStoreAfterLoad : gmoLt iswOk.gdG (0, 0) (0, 2) := by
  obtain ⟨_, h⟩ := iswOkConclusion
  obtain ⟨r, hr, _, hmo⟩ := h 2 (by omega) ⟨LStore false 3 [b1] .WCplain, rfl, rfl⟩
  have : r = 0 := by omega
  subst this
  exact hmo

end Weak
