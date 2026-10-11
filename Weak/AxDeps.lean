/-
Weak: **TAGGED dependencies** — the graph side (`GdexecT`, rule 12 over addr/data only) and the
emission side (`rowDepsT`, general rule 13, execution-context CSR edges).  PURE (no Iris).

Rocq: `iris/AxDeps.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-lb-axsl.md` §0 "The model" (rev 5: tagged deps, general
rule 13, context-CSR edges) and §2 gate G0.5.

THE PROBLEM (found in G0.5, `AxGraphCat`'s header).  The tree's `gdDeps` is an UNTAGGED list of
read→write edges mixing address (rule 9), data (10), control (11) and translation (13)
dependencies, and riscv.cat's rule 12 — `[R];(addr|data);[W];rfi;[R]` — must range over addr/data
edges only; `AxGraphCat.gppo12` over `gdDeps` also orders `ctrl;[W];rfi;[R]`, which riscv.cat does
NOT (UNSOUND for safety).  And rule 9's LOAD half is missing: `gdepsWf` admits only write
targets, because the emission's `rowDeps` records read→write edges only (D-8).

WHAT IS HERE.
  §1  `Dtag` and the tagged graph `GdexecT`; `gtdepsWf` (a read source, po-earlier, same hart;
      the target a WRITE for `DTdata`/`DTctrl`/`DTtrans`/`DTr13`, ANY memory event for
      `DTaddr`/`DTctx`); `gtdepsGmo`; `forget` (drop tags, keep write-targeted edges); `gtAd`
      (the addr/data edges into writes); `gppo12T` := rule 12 over `gtAd`; the model
      `rvwmoCatConsistentT`.
  §2  `catTOfCat`: the cat model on `forget GT` plus the read-targeted edges' well-formedness
      and gmo-ordering (`gtdepsRdOk`) gives the tagged model.  The CONVERSE FAILS (`AxDeps.tw`,
      §5): a ctrl-dep store forwarded to a later read — the untagged rule 12 is the strictly
      stronger (unsound) statement; every clause but rule 12 does hold backwards
      (`catTForgetAxioms`).
  §3  `gobCatT` := (ppo_cat_t ∪ ALL tagged deps ∪ rfe ∪ co ∪ fr)⁺, `obCatTSubGmo`,
      irreflexivity, `ownedReadCatT` — by REUSE: `gppoCatT GT` IS `AxGraphCat.gppoCat` on the
      untagged addr/data projection `gtAdGd GT`.
  §4  THE EMISSION SIDE: `DstateT` (the tree's `Dstate` plus the rule-13 accumulator `dtAdr`),
      `dstepT`, `rowDepsT` — a NEW fold, `WeakRvwmoConf` untouched — and its exact relation to
      `rowDeps`: `rowDepsSubT` (every existing edge is emitted, tagged, never `DTr13`),
      `rowDepsTSub` (`DTdata`/`DTctrl`/`DTtrans` edges are exactly existing edges),
      `rowDepsTAddr` (a `DTaddr` edge is an existing edge or targets a pure read).  Smoke tests
      by computation.
  §5  `AxDeps.tw`: two harts, one addr-dep LOAD, one ctrl-dep store forwarded to a later read;
      `rvwmoCatConsistentT AxDeps.tw` by COMPUTATION (`catTConsistentBSound`);
      `¬ rvwmoCatConsistent (forget AxDeps.tw)` by `notCatOfRule12`; `tw2` (same graph,
      rule-12-abiding gmo) discharges `catTOfCat`'s hypotheses non-vacuously.

The Rocq header's CORRECTIONS (1)–(5) stand unchanged: (1) `catTOfCat`'s second premise must
supply both the shape and the gmo-ordering of every read-targeted edge (`gtdepsRdOk`); (2) there
is no list equation between `rowDepsT` and `rowDeps`, only the three `∈`-statements of §4.3;
(3) `DTtrans` is the tree's intra-instruction W-TV edge (from `dsLd`), `DTr13` the general
riscv.cat rule 13 from the accumulator; (4) `WeakRvwmoConf.rowDepsChain`'s edge is an ADDRESS
dependency (`rowDepsTChain`); (5) SOUNDNESS FIX: `dtAdr` is fed only from a memory access's own
`asrc`, never from `LRegW rd (DLdRes :: srcs)` (`erw_srcs` includes AMO/SC's data register), so
`rowDepsTR13Masked` is `[]` and the general rule-13 edge needs the D-8 unmasking (full write-up:
`claude-notes/projects/weak-memory-lb-axsl-axdeps-report.md`).

A LEAF in Rocq: nothing imports this file.

FETCHES (O2 Stage C, owner rulings Q-C1/Q-C4: the fetch is an ADMINISTRATIVE label, not a graph
event).  Rocq's fetch row item was `LLoad false false pc tvs []`; the Lean instance label is
`LIFetch pc tvs`, which has no row item, no identity and no edges.  `dstepT`'s `LIFetch` arm is
`(s, [])` (no `dtLd` push, no `dtAdr` change, no edges), exactly `WeakRvwmoConf.dstep`'s
`LIFetch` arm (its deviation 3; `elbIsR (LIFetch ..) = false`), so `dstepTState` holds by `rfl`
in every arm.  The §5 witness `AxDeps.tw` (like Rocq's `tw_prog`) has no fetch row items, so its
rows, positions and kernel-checked verdicts are unchanged by Stage C.  Nothing in this file turns
`hartConf` blocks into `lblRealizes`.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  The duplicated Rocq names are file-qualified:
   `AxDeps.gisWGlbl`, `AxDeps.tw`.  The wlabel constructors are the unqualified ones
   (`open Wlabel`, as `WeakRvwmoConf`); graph labels are written `Lbl.LLoad`/`Lbl.LStore`.
2. TUPLES: Rocq's `tdep := geid * geid * dtag` and `redge := nat * nat * dtag` are LEFT-nested;
   Lean's `(x, y, z)` is right-nested, so `Tdep := (Geid × Geid) × Dtag` and
   `Redge := (Nat × Nat) × Dtag` (Lean-only abbrevs for the Rocq `Notation`s) and the literals are
   written `((x, y), z)`; the projections `e.1.1`/`e.1.2`/`e.2` keep their Rocq meaning.
3. VOCABULARY: `omap` ↦ `List.filterMap`; `mjoin (f <$> l)` ↦ `(l.map f).flatten`; `filter P` ↦
   `List.filter (decide ∘ P)`; `forallb` ↦ `List.all`; `bool_decide`/`Nat.ltb` ↦ `decide`;
   `implb a b` ↦ `!a || b`; `<[rd := v]> m` ↦ `WeakRvwmoConf.dprovSet` (the provenance map is a
   total function, `WeakRvwmoConf` deviation 2); Rocq's right-associative `++` chains are
   parenthesised explicitly (Lean's `++` is left-associative).
4. `dtag_eq_dec` ↦ `deriving DecidableEq`.  The `Local Notation`s `B0`/`B1`/`wld`/`wldA`/`wsd`
   are inlined (`b0`/`b1`, the literal labels); `Ltac vmr` and every `vm_compute` ↦
   `decide`/`decide +kernel`.  The `Example`s are named `theorem`s.
5. O2 / Stage C: `dstepT` has the Lean-only `LIFetch` arm `(s, [])` described above (Rocq has
   no fetch label; its fetch was an `LLoad` row item).
6. CLOSURE INDUCTION: `obCatTSubGmo` inducts on the library `tc`, which splits at the LAST step
   (`MachCSL.Rel` deviation 1).
7. Lean-only helpers: `Tdep`, `Redge`, `tagEdgesLt`, `dedgesRSnd`, `dedgesRLt`, `dedgesWLt`.

**Rocq → Lean name map.**  `dtag` `Dtag` (`DTaddr`…`DTctx` same), `dtag_w` `dtagW`, `dtag_ad`
`dtagAd`, `gdexec_t` `GdexecT` (`GDExecT` `GdexecT.mk`, `gt_g`/`gt_deps` `gtG`/`gtDeps`),
`gtdeps_wf` `gtdepsWf`, `gtdeps_gmo` `gtdepsGmo`, `forget_deps` `forgetDeps`, `forget` `forget`,
`gt_ad` `gtAd`, `gt_ad_gd` `gtAdGd`, `gppo12_t` `gppo12T`, `gppo_cat_t` `gppoCatT`,
`gppo_cat_t_alt` `gppoCatTAlt`, `gppo_cat_t_gmo` `gppoCatTGmo`, `rvwmo_cat_consistent_t`
`rvwmoCatConsistentT`, `elem_of_forget_deps` `elemOfForgetDeps`, `elem_of_gt_ad` `elemOfGtAd`,
`gt_ad_sub_forget` `gtAdSubForget`, `gppo12_t_alt` `gppo12TAlt`, `gis_w_glbl` `AxDeps.gisWGlbl`,
`gtdeps_wf_forget` `gtdepsWfForget`, `gtdeps_gmo_forget` `gtdepsGmoForget`, `gtdeps_wf_ad`
`gtdepsWfAd`, `gtdeps_gmo_ad` `gtdepsGmoAd`, `cat_t_ad` `catTAd`, `gtdeps_rd_ok` `gtdepsRdOk`,
`cat_t_of_cat` `catTOfCat`, `cat_t_forget_axioms` `catTForgetAxioms`, `gtdeps_rel` `gtdepsRel`,
`gobr_cat_t` `gobrCatT`, `gob_cat_t` `gobCatT`, `gob_cat_t_step` `gobCatTStep`,
`gob_cat_t_trans` `gobCatTTrans`, `gobr_cat_t_gmo` `gobrCatTGmo`, `ob_cat_t_sub_gmo`
`obCatTSubGmo`, `ob_cat_t_irreflexive` `obCatTIrreflexive`, `ob_cat_t_chain` `obCatTChain`,
`owned_read_cat_t` `ownedReadCatT`, `dstate_t` `DstateT` (`DStT` `DstateT.mk`,
`dt_prov`/`dt_ld`/`dt_ctl`/`dt_adr` `dtProv`/`dtLd`/`dtCtl`/`dtAdr`), `dt_init` `dtInit`,
`ds_of_t` `dsOfT`, `dtsrcs` `dtsrcs`, `ctx_csrs` `ctxCsrs`, `ctx_prov` `ctxProv`, `tag_edges`
`tagEdges`, `dedges_r` `dedgesR`, `dedges_w` `dedgesW`, `nodup_app` `nodupApp`, `dt_acc` `dtAcc`,
`dstep_t` `dstepT`, `row_deps_t_aux` `rowDepsTAux`, `row_deps_t` `rowDepsT`, `elem_of_tag_edges`
`elemOfTagEdges`, `elem_of_dedges` `elemOfDedges`, `ctx_prov_satp` `ctxProvSatp`, `dedges_w_sup`
`dedgesWSup`, `dedges_w_sub` `dedgesWSub`, `dedges_r_tags` `dedgesRTags`, `dstep_t_state`
`dstepTState`, `dstep_t_sup` `dstepTSup`, `dstep_t_sub` `dstepTSub`, `dstep_t_addr` `dstepTAddr`,
`dstep_t_lt` `dstepTLt`, `row_deps_t_aux_sup` `rowDepsTAuxSup`, `row_deps_t_aux_sub`
`rowDepsTAuxSub`, `row_deps_t_aux_addr` `rowDepsTAuxAddr`, `row_deps_sub_t` `rowDepsSubT`,
`row_deps_t_sub` `rowDepsTSub`, `row_deps_t_addr` `rowDepsTAddr`, `row_deps_t_lt` `rowDepsTLt`,
`row_deps_t_chain` `rowDepsTChain`, `es_r13` `esR13`, `es_r13m` `esR13m`, `row_deps_t_r13`
`rowDepsTR13`, `row_deps_t_r13_masked` `rowDepsTR13Masked`, `row_deps_r13_masked_gap`
`rowDepsR13MaskedGap`, `es_ctx` `esCtx`, `row_deps_t_ctx` `rowDepsTCtx`, `row_deps_ctx_gap`
`rowDepsCtxGap`, `gtdeps_wf_b` `gtdepsWfB`, `glbl_mem_gmem` `glblMemGmem`, `gtdeps_wf_b_sound`
`gtdepsWfBSound`, `gtdeps_gmo_b` `gtdepsGmoB`, `gtdeps_gmo_b_sound` `gtdepsGmoBSound`,
`gtdeps_rd_ok_b` `gtdepsRdOkB`, `gtdeps_rd_ok_b_sound` `gtdepsRdOkBSound`, `cat_t_consistent_b`
`catTConsistentB`, `cat_t_consistent_b_sound` `catTConsistentBSound`, `imgt` `imgt`, `mkgt`
`mkgt`, `tw_prog` `twProg`, `tw_deps` `twDeps`, `tw` `AxDeps.tw`, `tw2` `tw2`, `tw_cat_t`
`twCatT`, `tw_forget_deps` `twForgetDeps`, `tw_not_cat_forget` `twNotCatForget`, `tw_r12_edge`
`twR12Edge`, `cat_t_separates` `catTSeparates`, `tw2_cat_forget` `tw2CatForget`, `tw2_rd_ok`
`tw2RdOk`, `tw2_cat_t` `tw2CatT`, `tw2_cat_t_b` `tw2CatTB`.

**Not ported:** nothing (the §6 `Print Assumptions` block has no Lean twin; the lint's axiom
check covers it).
-/
import Weak.WeakRvwmoConf
import Weak.AxGraphDec

namespace Weak

open MachCSL MachCSL.Stdpp
open Wlabel
open WeakRvwmoConf (Dstate dstep)

/-! # 1. Tags, the tagged graph, the model -/

/-- `DTaddr` rule 9 (both halves) · `DTdata` rule 10 · `DTctrl` rule 11 · `DTtrans` the tree's
intra-instruction translation edge (W-TV) · `DTr13` riscv.cat rule 13 in its general form ·
`DTctx` the execution-context CSR edge (hardware-strengthening: serializing CSR writes — the same
justification as DEC-5's `satp` edge). -/
inductive Dtag where
  | DTaddr | DTdata | DTctrl | DTtrans | DTr13 | DTctx
  deriving DecidableEq, Inhabited

open Dtag

/-- Whether a tag's target must be a WRITE (else: any memory event). -/
def dtagW (tg : Dtag) : Bool :=
  match tg with
  | DTaddr | DTctx => false
  | _ => true

/-- The tags rule 12 ranges over. -/
def dtagAd (tg : Dtag) : Bool :=
  match tg with
  | DTaddr | DTdata => true
  | _ => false

/-- (Lean-only abbrev for Rocq's `Notation tdep`; deviation 2.) -/
abbrev Tdep : Type := (Geid × Geid) × Dtag

structure GdexecT where
  mk ::
  gtG : Gexec
  gtDeps : List Tdep

def gtdepsWf (G : Gexec) (deps : List Tdep) : Prop :=
  ∀ e : Tdep, e ∈ deps →
    e.1.1.1 = e.1.2.1 ∧ e.1.1.2 < e.1.2.2 ∧ glblIs G e.1.1 lbIsR ∧
    (if dtagW e.2 then glblIs G e.1.2 lbIsW else gmem G e.1.2)

/-- Rules 9 (both halves), 10, 11, 13 and the context edges: gmo-forward. -/
def gtdepsGmo (G : Gexec) (deps : List Tdep) : Prop :=
  ∀ e : Tdep, e ∈ deps → gmoLt G e.1.1 e.1.2

/-- `forget`: drop the tags, keep the write-targeted edges. -/
def forgetDeps (G : Gexec) (deps : List Tdep) : List (Geid × Geid) :=
  deps.filterMap (fun e : Tdep => if gisW G e.1.2 then some e.1 else none)

def forget (GT : GdexecT) : Gdexec :=
  ⟨GT.gtG, forgetDeps GT.gtG GT.gtDeps⟩

/-- The addr/data edges INTO WRITES, untagged — rule 12's domain.  (The write filter is
semantically idle, `gppo12TAlt`: an rf-source is a write; it keeps `gtAd ⊆ forgetDeps`
syntactic.) -/
def gtAd (G : Gexec) (deps : List Tdep) : List (Geid × Geid) :=
  deps.filterMap (fun e : Tdep => if dtagAd e.2 && gisW G e.1.2 then some e.1 else none)

def gtAdGd (GT : GdexecT) : Gdexec :=
  ⟨GT.gtG, gtAd GT.gtG GT.gtDeps⟩

/-- RULE 12 over addr/data edges only. -/
def gppo12T (GT : GdexecT) (a b : Geid) : Prop :=
  gppo12 GT.gtG (gtAd GT.gtG GT.gtDeps) a b

/-- THE TAGGED ppo IS `gppoCat` OF THE PROJECTION — the reuse hinge. -/
def gppoCatT (GT : GdexecT) : Geid → Geid → Prop :=
  gppoCat (gtAdGd GT)

theorem gppoCatTAlt (GT : GdexecT) (e1 e2 : Geid) :
    gppoCatT GT e1 e2 ↔ gppoCat6 GT.gtG e1 e2 ∨ gppo12T GT e1 e2 :=
  Iff.rfl

def gppoCatTGmo (GT : GdexecT) : Prop := gppoCatGmo (gtAdGd GT)

/-- THE MODEL. -/
def rvwmoCatConsistentT (GT : GdexecT) : Prop :=
  gwf GT.gtG ∧ gppoCatTGmo GT ∧ gloadValue GT.gtG ∧
  gatomicity GT.gtG ∧
  gtdepsWf GT.gtG GT.gtDeps ∧ gtdepsGmo GT.gtG GT.gtDeps

/-! ## 1.1 The projections, pointwise -/

theorem elemOfForgetDeps (G : Gexec) (deps : List Tdep) (a m : Geid) :
    (a, m) ∈ forgetDeps G deps ↔ ∃ tg, ((a, m), tg) ∈ deps ∧ gisW G m = true := by
  unfold forgetDeps
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨⟨a', m'⟩, tg⟩, hin, hf⟩
    dsimp only at hf
    split at hf
    · next hw =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨tg, hin, hw⟩
    · cases hf
  · rintro ⟨tg, hin, hw⟩
    exact ⟨((a, m), tg), hin, by simp [hw]⟩

theorem elemOfGtAd (G : Gexec) (deps : List Tdep) (a m : Geid) :
    (a, m) ∈ gtAd G deps ↔
    ∃ tg, ((a, m), tg) ∈ deps ∧ dtagAd tg = true ∧ gisW G m = true := by
  unfold gtAd
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨⟨a', m'⟩, tg⟩, hin, hf⟩
    dsimp only at hf
    split at hf
    · next hb =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      rw [Bool.and_eq_true] at hb
      exact ⟨tg, hin, hb.1, hb.2⟩
    · cases hf
  · rintro ⟨tg, hin, had, hw⟩
    exact ⟨((a, m), tg), hin, by simp [had, hw]⟩

theorem gtAdSubForget (G : Gexec) (deps : List Tdep) (rw : Geid × Geid) :
    rw ∈ gtAd G deps → rw ∈ forgetDeps G deps := by
  obtain ⟨a, m⟩ := rw
  rw [elemOfGtAd, elemOfForgetDeps]
  rintro ⟨tg, hin, _, hw⟩
  exact ⟨tg, hin, hw⟩

/-- Rule 12's natural reading: some addr/data-tagged edge into the rf-source.  The write filter
costs nothing (`gwriteAt` names writes). -/
theorem gppo12TAlt (GT : GdexecT) (a b : Geid) :
    gppo12T GT a b ↔
    a.1 = b.1 ∧ ∃ m tg, ((a, m), tg) ∈ GT.gtDeps ∧ dtagAd tg = true ∧
                        WeakRvwmoAcyc.grf GT.gtG m b := by
  unfold gppo12T gppo12
  constructor
  · rintro ⟨hag, m, hin, hrf⟩
    obtain ⟨tg, hin, had, _⟩ := (elemOfGtAd _ _ _ _).1 hin
    exact ⟨hag, m, tg, hin, had, hrf⟩
  · rintro ⟨hag, m, tg, hin, had, hrf⟩
    refine ⟨hag, m, (elemOfGtAd _ _ _ _).2 ⟨tg, hin, had, ?_⟩, hrf⟩
    obtain ⟨_, t, _, _, hat⟩ := hrf
    exact ((gwritesElemOf _ _).1 (gwriteAtGwrites _ _ _ hat)).2

theorem AxDeps.gisWGlbl (G : Gexec) (e : Geid) : gisW G e = true → glblIs G e lbIsW := by
  intro h
  unfold gisW at h
  cases hl : gxLbl G e with
  | none => rw [hl] at h; cases h
  | some l => rw [hl] at h; exact ⟨l, hl, h⟩

theorem gtdepsWfForget (G : Gexec) (deps : List Tdep) :
    gtdepsWf G deps → gdepsWf G (forgetDeps G deps) := by
  rintro H ⟨a, m⟩ hin
  obtain ⟨tg, hin, hw⟩ := (elemOfForgetDeps _ _ _ _).1 hin
  obtain ⟨h1, h2, h3, _⟩ := H _ hin
  exact ⟨h1, h2, h3, AxDeps.gisWGlbl _ _ hw⟩

theorem gtdepsGmoForget (G : Gexec) (deps : List Tdep) :
    gtdepsGmo G deps → gdepsGmo G (forgetDeps G deps) := by
  rintro H ⟨a, m⟩ hin
  obtain ⟨tg, hin, _⟩ := (elemOfForgetDeps _ _ _ _).1 hin
  exact H _ hin

theorem gtdepsWfAd (G : Gexec) (deps : List Tdep) :
    gtdepsWf G deps → gdepsWf G (gtAd G deps) :=
  fun H rw hrw => gtdepsWfForget G deps H rw (gtAdSubForget G deps rw hrw)

theorem gtdepsGmoAd (G : Gexec) (deps : List Tdep) :
    gtdepsGmo G deps → gdepsGmo G (gtAd G deps) :=
  fun H rw hrw => gtdepsGmoForget G deps H rw (gtAdSubForget G deps rw hrw)

/-- The tagged model IS the cat model on the addr/data projection. -/
theorem catTAd (GT : GdexecT) : rvwmoCatConsistentT GT → rvwmoCatConsistent (gtAdGd GT) := by
  rintro ⟨hwf, hppo, hlv, hat, hdw, hdg⟩
  exact ⟨hwf, hppo, hlv, hat, gtdepsWfAd _ _ hdw, gtdepsGmoAd _ _ hdg⟩

/-! # 2. `catTOfCat` and what fails backwards -/

/-- The read-targeted edges (dropped by `forget`): well-formed for a read-admitting tag and
gmo-forward. -/
def gtdepsRdOk (GT : GdexecT) : Prop :=
  ∀ e : Tdep, e ∈ GT.gtDeps → gisW GT.gtG e.1.2 = false →
    e.1.1.1 = e.1.2.1 ∧ e.1.1.2 < e.1.2.2 ∧ glblIs GT.gtG e.1.1 lbIsR ∧
    dtagW e.2 = false ∧ gmem GT.gtG e.1.2 ∧ gmoLt GT.gtG e.1.1 e.1.2

theorem catTOfCat (GT : GdexecT) :
    rvwmoCatConsistent (forget GT) → gtdepsRdOk GT → rvwmoCatConsistentT GT := by
  rintro ⟨hwf, hppo, hlv, hat, hdw, hdg⟩ hrd
  refine ⟨hwf, ?_, hlv, hat, ?_, ?_⟩
  · rintro e1 e2 (h | ⟨hag, m, hin, hrf⟩)
    · exact hppo _ _ (Or.inl h)
    · exact hppo _ _ (Or.inr ⟨hag, m, gtAdSubForget _ _ _ hin, hrf⟩)
  · rintro ⟨⟨a, m⟩, tg⟩ hin
    dsimp only
    cases hw : gisW GT.gtG m
    · obtain ⟨h1, h2, h3, h4, h5, _⟩ := hrd _ hin hw
      refine ⟨h1, h2, h3, ?_⟩
      dsimp only at h4
      rw [if_neg (by rw [h4]; decide)]
      exact h5
    · obtain ⟨h1, h2, h3, h4⟩ := hdw (a, m) ((elemOfForgetDeps _ _ _ _).2 ⟨tg, hin, hw⟩)
      refine ⟨h1, h2, h3, ?_⟩
      split
      · exact h4
      · exact WeakRvwmoGraph.glblIsWGmem _ _ h4
  · rintro ⟨⟨a, m⟩, tg⟩ hin
    cases hw : gisW GT.gtG m
    · exact (hrd _ hin hw).2.2.2.2.2
    · exact hdg (a, m) ((elemOfForgetDeps _ _ _ _).2 ⟨tg, hin, hw⟩)

/-- BACKWARDS, everything but rule 12 transfers (`AxDeps.tw` shows rule 12 does not). -/
theorem catTForgetAxioms (GT : GdexecT) :
    rvwmoCatConsistentT GT →
    gwf (forget GT).gdG ∧ gppoCat6Gmo (forget GT).gdG ∧
    gloadValue (forget GT).gdG ∧ gatomicity (forget GT).gdG ∧
    gdepsWf (forget GT).gdG (forget GT).gdDeps ∧
    gdepsGmo (forget GT).gdG (forget GT).gdDeps := by
  rintro ⟨hwf, hppo, hlv, hat, hdw, hdg⟩
  exact ⟨hwf, fun e1 e2 h => hppo e1 e2 (Or.inl h), hlv, hat, gtdepsWfForget _ _ hdw,
    gtdepsGmoForget _ _ hdg⟩

/-! # 3. `gobCatT` and the owned-read family, by reuse -/

def gtdepsRel (GT : GdexecT) (x y : Geid) : Prop :=
  ∃ tg, ((x, y), tg) ∈ GT.gtDeps

/-- One ob step: the projection's step (ppo_cat_t, addr/data deps, rfe, co, fr) or ANY tagged
dep edge. -/
def gobrCatT (GT : GdexecT) (x y : Geid) : Prop :=
  gobrCat (gtAdGd GT) x y ∨ gtdepsRel GT x y

def gobCatT (GT : GdexecT) (x y : Geid) : Prop := tc (gobrCatT GT) x y

theorem gobCatTStep (GT : GdexecT) (x y : Geid) : gobrCatT GT x y → gobCatT GT x y := tc_once

theorem gobCatTTrans (GT : GdexecT) (x y z : Geid) :
    gobCatT GT x y → gobCatT GT y z → gobCatT GT x z := tc_transitive

theorem gobrCatTGmo (GT : GdexecT) (x y : Geid) :
    rvwmoCatConsistentT GT → gobrCatT GT x y → gmoLt GT.gtG x y := by
  rintro hc (h | ⟨tg, h⟩)
  · exact gobrCatGmo _ _ _ (catTAd GT hc) h
  · exact hc.2.2.2.2.2 ((x, y), tg) h

theorem obCatTSubGmo (GT : GdexecT) (x y : Geid) :
    rvwmoCatConsistentT GT → gobCatT GT x y → gmoLt GT.gtG x y := by
  intro hc h
  induction h with
  | single h => exact gobrCatTGmo GT _ _ hc h
  | tail _ h ih => exact gmoLtTrans _ _ _ _ ih (gobrCatTGmo GT _ _ hc h)

theorem obCatTIrreflexive (GT : GdexecT) (x : Geid) :
    rvwmoCatConsistentT GT → ¬ gobCatT GT x x :=
  fun hc hob => gmoLtIrrefl _ _ (obCatTSubGmo GT x x hc hob)

def obCatTChain (GT : GdexecT) (Hl : List Geid) : Prop :=
  chainWith (gobCatT GT) Hl

/-- The owned-read lemma over `gobCatT` — an instance of `AxGraph.ownedReadWith`. -/
theorem ownedReadCatT (GT : GdexecT) (Hl : List Geid) (a : Int) (r w0 : Geid) :
    rvwmoCatConsistentT GT →
    (∀ w, w ∈ Hl → ∃ v, gwritesByte GT.gtG w a v) →
    obCatTChain GT Hl →
    (∀ w v, gwritesByte GT.gtG w a v → gvisible GT.gtG w r → w ∈ Hl) →
    w0 ∈ Hl → gvisible GT.gtG w0 r →
    (∃ t v, greadsByte GT.gtG r a t v) →
    ∃ w, lastVisible GT.gtG Hl r = some w ∧ grfAt GT.gtG a w r := fun hc =>
  ownedReadWith GT.gtG (gobCatT GT) Hl a r w0 (fun x y => obCatTSubGmo GT x y hc)
    hc.1 hc.2.2.1

/-! # 4. The emission side: `rowDepsT`

A NEW fold over `WeakRvwmoConf.Eitem` streams, alongside the tree's `dstep`/`rowDeps`
(untouched).  The state is the tree's `Dstate` — provenance map, the current instruction's loads
(`dtLd`, reset at `LInstr`), the control set (`dtCtl`, never reset) — plus `dtAdr`: the positions
of every read some access's ADDRESS depended on, never reset (riscv.cat rule 13,
`[R];addr;[M];po;[W]`).  It is fed ONLY from a memory label's own `asrc` (the load half is `[]`
until D-8 is unmasked); it is NOT fed from a load's result write `LRegW rd (DLdRes :: …)`
(UNSOUND, see the header's correction (5)).

EDGES.  A READ at `k`: `DTaddr` from its address sources (rule 9's load half), `DTctx` from the
context CSRs' provenance.  A WRITE at `k`: `DTaddr` (rule 9), `DTdata` (10), `DTctrl` (11, from
`dtCtl`), `DTtrans` (the tree's W-TV edge, from `dtLd`), `DTr13` (from `dtAdr`, BEFORE this
access's own sources are appended), `DTctx`.  The fused RMW is a write here and also joins
`dtLd`, exactly as in `dstep`.  The fetch (Stage C) is admin: `(s, [])`. -/

structure DstateT where
  mk ::
  dtProv : Nat → List Nat
  dtLd : List Nat
  dtCtl : List Nat
  dtAdr : List Nat

def dtInit : DstateT := ⟨fun _ => [], [], [], []⟩

/-- The tree's state is the projection. -/
def dsOfT (s : DstateT) : Dstate := ⟨s.dtProv, s.dtLd, s.dtCtl⟩

def dtsrcs (s : DstateT) (xs : List Dsrc) : List Nat :=
  dsrcsPos (dsOfT s) xs

/-- 4c — THE EXECUTION-CONTEXT CSRs.  Every memory event's identity (address translation,
privilege, trap routing) depends on them.  `wsatp` first: `ctxProvSatp` is the tree's DEC-5
edge. -/
def ctxCsrs : List Nat :=
  [wsatp, wcsr MSTATUS, wcsr MIE, wcsr MEDELEG, wcsr MIDELEG, wcsr STVEC, wcsr MTVEC]

def ctxProv (s : DstateT) : List Nat :=
  (ctxCsrs.map (fun r => dprov (dsOfT s) r)).flatten

/-- (Lean-only abbrev for Rocq's `Notation redge`; deviation 2.) -/
abbrev Redge : Type := (Nat × Nat) × Dtag

def tagEdges (tg : Dtag) (k : Nat) (js : List Nat) : List Redge :=
  (js.filter (fun j => decide (j < k))).map (fun j => ((j, k), tg))

def dedgesR (s : DstateT) (k : Nat) (asrc : List Dsrc) : List Redge :=
  tagEdges DTaddr k (dtsrcs s asrc) ++ tagEdges DTctx k (ctxProv s)

def dedgesW (s : DstateT) (k : Nat) (asrc vsrc : List Dsrc) : List Redge :=
  tagEdges DTaddr k (dtsrcs s asrc) ++ (tagEdges DTdata k (dtsrcs s vsrc) ++
  (tagEdges DTctrl k s.dtCtl ++ (tagEdges DTtrans k s.dtLd ++
  (tagEdges DTr13 k s.dtAdr ++ tagEdges DTctx k (ctxProv s)))))

/-- Append without duplicates (the same read can already be in `dtAdr` once the load label's own
`asrc` is unmasked and re-recorded). -/
def nodupApp (l1 l2 : List Nat) : List Nat :=
  l1 ++ l2.filter (fun x => decide (x ∉ l1))

def dtAcc (s : DstateT) (xs : List Dsrc) : List Nat :=
  nodupApp s.dtAdr (dtsrcs s xs)

def dstepT (s : DstateT) (it : Eitem) : DstateT × List Redge :=
  match it.1 with
  | LSilent | LDev .. | LFence _ _ _ _ | LIFetch _ _ => (s, [])
  | LInstr => (⟨s.dtProv, [], s.dtCtl, s.dtAdr⟩, [])
  | LRegW rd srcs =>
      (⟨dprovSet s.dtProv rd (dtsrcs s srcs), s.dtLd, s.dtCtl, s.dtAdr⟩, [])
  | LCtrl srcs =>
      (⟨s.dtProv, s.dtLd, s.dtCtl ++ dtsrcs s srcs, s.dtAdr⟩, [])
  | LLoad _ _ _ _ asrc | LExLoad _ _ _ asrc =>
      match it.2 with
      | some k => (⟨s.dtProv, k :: s.dtLd, s.dtCtl, dtAcc s asrc⟩, dedgesR s k asrc)
      | none => (s, [])
  | LStore _ _ _ asrc vsrc | LExStore _ _ _ asrc vsrc =>
      match it.2 with
      | some k => (⟨s.dtProv, s.dtLd, s.dtCtl, dtAcc s asrc⟩, dedgesW s k asrc vsrc)
      | none => (s, [])
  | LRmw _ _ _ _ _ asrc vsrc =>
      match it.2 with
      | some k => (⟨s.dtProv, k :: s.dtLd, s.dtCtl, dtAcc s asrc⟩, dedgesW s k asrc vsrc)
      | none => (s, [])

def rowDepsTAux (s : DstateT) (es : List Eitem) : List Redge :=
  match es with
  | [] => []
  | it :: es' => (dstepT s it).2 ++ rowDepsTAux (dstepT s it).1 es'

/-- THE TAGGED REGISTER-DATAFLOW RELATION of an emission. -/
def rowDepsT (es : List Eitem) : List Redge := rowDepsTAux dtInit es

/-! ## 4.1 Edge-list kit -/

theorem elemOfTagEdges (tg : Dtag) (k : Nat) (js : List Nat) (j k' : Nat) (tg' : Dtag) :
    ((j, k'), tg') ∈ tagEdges tg k js ↔ tg' = tg ∧ k' = k ∧ j ∈ js ∧ j < k := by
  simp only [tagEdges, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨j0, ⟨hin, hlt⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    exact ⟨rfl, rfl, hin, hlt⟩
  · rintro ⟨rfl, rfl, hin, hlt⟩
    exact ⟨j, ⟨hin, hlt⟩, rfl⟩

theorem elemOfDedges (s : Dstate) (k : Nat) (asrc vsrc : List Dsrc) (j k' : Nat) :
    (j, k') ∈ dedges s k asrc vsrc ↔
    k' = k ∧ j < k ∧
    j ∈ dsrcsPos s asrc ++ (dsrcsPos s vsrc ++ (s.dsCtl ++ (s.dsLd ++ dprov s wsatp))) := by
  simp only [dedges, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨j0, ⟨hin, hlt⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨rfl, hlt, hin⟩
  · rintro ⟨rfl, hlt, hin⟩
    exact ⟨j, ⟨hin, hlt⟩, rfl⟩

theorem ctxProvSatp (s : DstateT) (j : Nat) : j ∈ dprov (dsOfT s) wsatp → j ∈ ctxProv s := by
  intro h
  simp only [ctxProv, List.mem_flatten, List.mem_map]
  exact ⟨_, ⟨wsatp, List.mem_cons_self .., rfl⟩, h⟩

/-- (Lean-only) the target of a `tagEdges` edge climbs from its source. -/
theorem tagEdgesLt (tg : Dtag) (k : Nat) (js : List Nat) (j k' : Nat) (tg' : Dtag) :
    ((j, k'), tg') ∈ tagEdges tg k js → j < k' := by
  rw [elemOfTagEdges]
  rintro ⟨_, rfl, _, hlt⟩
  exact hlt

/-- Every edge the tree's write emits, this one emits tagged (never `DTr13`); the `satp` edge
becomes `DTctx`. -/
theorem dedgesWSup (s : DstateT) (k : Nat) (asrc vsrc : List Dsrc) (j k' : Nat) :
    (j, k') ∈ dedges (dsOfT s) k asrc vsrc →
    ∃ tg, ((j, k'), tg) ∈ dedgesW s k asrc vsrc ∧ tg ≠ DTr13 := by
  rw [elemOfDedges]
  rintro ⟨rfl, hlt, hin⟩
  simp only [List.mem_append] at hin
  simp only [dedgesW, List.mem_append]
  rcases hin with h | h | h | h | h
  · exact ⟨DTaddr, Or.inl ((elemOfTagEdges ..).2 ⟨rfl, rfl, h, hlt⟩), by decide⟩
  · exact ⟨DTdata, Or.inr (Or.inl ((elemOfTagEdges ..).2 ⟨rfl, rfl, h, hlt⟩)), by decide⟩
  · exact ⟨DTctrl, Or.inr (Or.inr (Or.inl ((elemOfTagEdges ..).2 ⟨rfl, rfl, h, hlt⟩))),
      by decide⟩
  · exact ⟨DTtrans, Or.inr (Or.inr (Or.inr (Or.inl ((elemOfTagEdges ..).2 ⟨rfl, rfl, h, hlt⟩)))),
      by decide⟩
  · exact ⟨DTctx, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((elemOfTagEdges ..).2 ⟨rfl, rfl, ctxProvSatp s j h, hlt⟩))))), by decide⟩

/-- A `DTaddr`/`DTdata`/`DTctrl`/`DTtrans` edge of a write IS a tree edge. -/
theorem dedgesWSub (s : DstateT) (k : Nat) (asrc vsrc : List Dsrc) (j k' : Nat) (tg : Dtag) :
    ((j, k'), tg) ∈ dedgesW s k asrc vsrc →
    tg = DTaddr ∨ tg = DTdata ∨ tg = DTctrl ∨ tg = DTtrans →
    (j, k') ∈ dedges (dsOfT s) k asrc vsrc := by
  intro h htg
  simp only [dedgesW, List.mem_append, elemOfTagEdges] at h
  rw [elemOfDedges]
  simp only [List.mem_append]
  rcases h with ⟨rfl, rfl, hin, hlt⟩ | ⟨rfl, rfl, hin, hlt⟩ | ⟨rfl, rfl, hin, hlt⟩ |
      ⟨rfl, rfl, hin, hlt⟩ | ⟨rfl, rfl, hin, hlt⟩ | ⟨rfl, rfl, hin, hlt⟩
  · exact ⟨rfl, hlt, Or.inl hin⟩
  · exact ⟨rfl, hlt, Or.inr (Or.inl hin)⟩
  · exact ⟨rfl, hlt, Or.inr (Or.inr (Or.inl hin))⟩
  · exact ⟨rfl, hlt, Or.inr (Or.inr (Or.inr (Or.inl hin)))⟩
  · rcases htg with h | h | h | h <;> cases h
  · rcases htg with h | h | h | h <;> cases h

theorem dedgesRTags (s : DstateT) (k : Nat) (asrc : List Dsrc) (j k' : Nat) (tg : Dtag) :
    ((j, k'), tg) ∈ dedgesR s k asrc → tg = DTaddr ∨ tg = DTctx := by
  simp only [dedgesR, List.mem_append, elemOfTagEdges]
  rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- (Lean-only) a read's edges target the read. -/
theorem dedgesRSnd (s : DstateT) (k : Nat) (asrc : List Dsrc) (j k' : Nat) (tg : Dtag) :
    ((j, k'), tg) ∈ dedgesR s k asrc → k' = k := by
  simp only [dedgesR, List.mem_append, elemOfTagEdges]
  rintro (⟨_, rfl, _⟩ | ⟨_, rfl, _⟩) <;> rfl

/-- (Lean-only) every read edge climbs. -/
theorem dedgesRLt (s : DstateT) (k : Nat) (asrc : List Dsrc) (j k' : Nat) (tg : Dtag) :
    ((j, k'), tg) ∈ dedgesR s k asrc → j < k' := by
  simp only [dedgesR, List.mem_append]
  rintro (h | h) <;> exact tagEdgesLt _ _ _ _ _ _ h

/-- (Lean-only) every write edge climbs. -/
theorem dedgesWLt (s : DstateT) (k : Nat) (asrc vsrc : List Dsrc) (j k' : Nat) (tg : Dtag) :
    ((j, k'), tg) ∈ dedgesW s k asrc vsrc → j < k' := by
  simp only [dedgesW, List.mem_append]
  rintro (h | h | h | h | h | h) <;> exact tagEdgesLt _ _ _ _ _ _ h

/-! ## 4.2 One step: state projection and edge correspondence -/

theorem dstepTState (s : DstateT) (it : Eitem) : dsOfT (dstepT s it).1 = (dstep (dsOfT s) it).1 := by
  obtain ⟨l, ok⟩ := it
  cases l <;> cases ok <;> rfl

theorem dstepTSup (s : DstateT) (it : Eitem) (j k : Nat) :
    (j, k) ∈ (dstep (dsOfT s) it).2 →
    ∃ tg, ((j, k), tg) ∈ (dstepT s it).2 ∧ tg ≠ DTr13 := by
  intro h
  obtain ⟨l, ok⟩ := it
  cases l <;> cases ok <;> simp only [dstep, List.not_mem_nil] at h <;>
    exact dedgesWSup _ _ _ _ _ _ h

theorem dstepTSub (s : DstateT) (it : Eitem) (j k : Nat) (tg : Dtag) :
    ((j, k), tg) ∈ (dstepT s it).2 → tg = DTdata ∨ tg = DTctrl ∨ tg = DTtrans →
    (j, k) ∈ (dstep (dsOfT s) it).2 := by
  intro h htg
  have htg' : tg = DTaddr ∨ tg = DTdata ∨ tg = DTctrl ∨ tg = DTtrans := Or.inr htg
  have hnr : ¬ (tg = DTaddr ∨ tg = DTctx) := by
    rcases htg with rfl | rfl | rfl <;> decide
  obtain ⟨l, ok⟩ := it
  cases l <;> cases ok <;> simp only [dstepT, List.not_mem_nil] at h <;>
    first
    | exact absurd (dedgesRTags _ _ _ _ _ _ h) hnr
    | exact dedgesWSub _ _ _ _ _ _ _ h htg'

theorem dstepTAddr (s : DstateT) (it : Eitem) (j k : Nat) :
    ((j, k), DTaddr) ∈ (dstepT s it).2 →
    (j, k) ∈ (dstep (dsOfT s) it).2 ∨
    (it.2 = some k ∧ elbIsR it.1 = true ∧ elbIsW it.1 = false) := by
  intro h
  obtain ⟨l, ok⟩ := it
  cases l <;> cases ok <;> simp only [dstepT, List.not_mem_nil] at h <;>
    first
    | exact Or.inl (dedgesWSub _ _ _ _ _ _ _ h (Or.inl rfl))
    | exact Or.inr ⟨by rw [dedgesRSnd _ _ _ _ _ _ h], rfl, rfl⟩

theorem dstepTLt (s : DstateT) (it : Eitem) (j k : Nat) (tg : Dtag) :
    ((j, k), tg) ∈ (dstepT s it).2 → j < k := by
  intro h
  obtain ⟨l, ok⟩ := it
  cases l <;> cases ok <;> simp only [dstepT, List.not_mem_nil] at h <;>
    first
    | exact dedgesRLt _ _ _ _ _ _ h
    | exact dedgesWLt _ _ _ _ _ _ _ h

/-! ## 4.3 The fold: the exact relation to `rowDeps` -/

theorem rowDepsTAuxSup (s : DstateT) (es : List Eitem) (j k : Nat) :
    (j, k) ∈ rowDepsAux (dsOfT s) es →
    ∃ tg, ((j, k), tg) ∈ rowDepsTAux s es ∧ tg ≠ DTr13 := by
  induction es generalizing s with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons it es ih =>
    intro h
    simp only [rowDepsAux, List.mem_append] at h
    simp only [rowDepsTAux, List.mem_append]
    rcases h with h | h
    · obtain ⟨tg, hin, hne⟩ := dstepTSup s it j k h
      exact ⟨tg, Or.inl hin, hne⟩
    · rw [← dstepTState] at h
      obtain ⟨tg, hin, hne⟩ := ih _ h
      exact ⟨tg, Or.inr hin, hne⟩

theorem rowDepsTAuxSub (s : DstateT) (es : List Eitem) (j k : Nat) (tg : Dtag) :
    ((j, k), tg) ∈ rowDepsTAux s es → tg = DTdata ∨ tg = DTctrl ∨ tg = DTtrans →
    (j, k) ∈ rowDepsAux (dsOfT s) es := by
  induction es generalizing s with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons it es ih =>
    intro h htg
    simp only [rowDepsTAux, List.mem_append] at h
    simp only [rowDepsAux, List.mem_append]
    rcases h with h | h
    · exact Or.inl (dstepTSub s it j k tg h htg)
    · right
      rw [← dstepTState]
      exact ih _ h htg

theorem rowDepsTAuxAddr (s : DstateT) (es : List Eitem) (j k : Nat) :
    ((j, k), DTaddr) ∈ rowDepsTAux s es →
    (j, k) ∈ rowDepsAux (dsOfT s) es ∨
    ∃ it, it ∈ es ∧ it.2 = some k ∧ elbIsR it.1 = true ∧ elbIsW it.1 = false := by
  induction es generalizing s with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons it es ih =>
    intro h
    simp only [rowDepsTAux, List.mem_append] at h
    simp only [rowDepsAux, List.mem_append]
    rcases h with h | h
    · rcases dstepTAddr s it j k h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr ⟨it, List.mem_cons_self .., h'⟩
    · rcases ih _ h with h' | ⟨it0, hin, h'⟩
      · rw [dstepTState] at h'
        exact Or.inl (Or.inr h')
      · exact Or.inr ⟨it0, List.mem_cons_of_mem _ hin, h'⟩

/-- (A) Every tree edge is a tagged edge, and its tag is not `DTr13`. -/
theorem rowDepsSubT (es : List Eitem) (j k : Nat) :
    (j, k) ∈ rowDeps es → ∃ tg, ((j, k), tg) ∈ rowDepsT es ∧ tg ≠ DTr13 :=
  rowDepsTAuxSup dtInit es j k

/-- (B) A `DTdata`/`DTctrl`/`DTtrans` edge is exactly a tree edge. -/
theorem rowDepsTSub (es : List Eitem) (j k : Nat) (tg : Dtag) :
    ((j, k), tg) ∈ rowDepsT es → tg = DTdata ∨ tg = DTctrl ∨ tg = DTtrans →
    (j, k) ∈ rowDeps es :=
  rowDepsTAuxSub dtInit es j k tg

/-- (C) A `DTaddr` edge is a tree edge or targets a pure READ item (rule 9's load half — what
the tree drops). -/
theorem rowDepsTAddr (es : List Eitem) (j k : Nat) :
    ((j, k), DTaddr) ∈ rowDepsT es →
    (j, k) ∈ rowDeps es ∨
    ∃ it, it ∈ es ∧ it.2 = some k ∧ elbIsR it.1 = true ∧ elbIsW it.1 = false :=
  rowDepsTAuxAddr dtInit es j k

/-- Shape: every edge climbs the row. -/
theorem rowDepsTLt (es : List Eitem) (j k : Nat) (tg : Dtag) :
    ((j, k), tg) ∈ rowDepsT es → j < k := by
  unfold rowDepsT
  generalize dtInit = s
  induction es generalizing s with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons it es ih =>
    intro h
    simp only [rowDepsTAux, List.mem_append] at h
    rcases h with h | h
    · exact dstepTLt _ _ _ _ _ h
    · exact ih _ h

/-! ## 4.4 Smoke tests (by computation) -/

/-- `WeakRvwmoConf.rowDepsChain`'s stream: its one edge is an ADDRESS dependency (`DReg 5` is the
store's `asrc`). -/
theorem rowDepsTChain :
    rowDepsT [ (LInstr, none),
               (LLoad false false 0 [(0, 0#8)] [], some 0),
               (LRegW 5 [.DLdRes], none),
               (LInstr, none),
               (LStore false 8 [0#8] [.DReg 5] [], some 1) ]
    = [((0, 1), DTaddr)] := by decide

/-- THE RULE-13 EXAMPLE (review 4 F1): `ld a0,[y]; ld a1,0(a0); sd [z]` — the store has NO data
dependency on either load.  `esR13` has the second load's label UNMASKED (`asrc = [DReg 10]`);
`esR13m` is TODAY's emission (D-8: `[]`). -/
def esR13 : List Eitem :=
  [ (LInstr, none), (LLoad false false 0 [(0, 0#8)] [], some 0),
    (LRegW 10 [.DLdRes, .DReg 9], none),
    (LInstr, none), (LLoad false false 8 [(0, 0#8)] [.DReg 10], some 1),
    (LRegW 11 [.DLdRes, .DReg 10], none),
    (LInstr, none), (LStore false 16 [0#8] [] [], some 2) ]

def esR13m : List Eitem :=
  [ (LInstr, none), (LLoad false false 0 [(0, 0#8)] [], some 0),
    (LRegW 10 [.DLdRes, .DReg 9], none),
    (LInstr, none), (LLoad false false 8 [(0, 0#8)] [], some 1),
    (LRegW 11 [.DLdRes, .DReg 10], none),
    (LInstr, none), (LStore false 16 [0#8] [] [], some 2) ]

/-- Unmasked: rule 9's load half (0,1) and the general rule 13 (0,2). -/
theorem rowDepsTR13 : rowDepsT esR13 = [((0, 1), DTaddr), ((0, 2), DTr13)] := by decide

/-- Masked: `dtAdr` is fed from a memory label's own `asrc` only, so with the load's `asrc`
masked to `[]` this fold records NOTHING either, same as the tree's.  Both the rule-9 load-half
edge AND the general rule-13 edge need the unmasking. -/
theorem rowDepsTR13Masked : rowDepsT esR13m = [] := by decide

theorem rowDepsR13MaskedGap : rowDeps esR13m = [] := by decide

/-- THE CONTEXT-CSR EXAMPLE (review 4 F2): `ld a0,[x]; csrw mstatus,a0; ld a1,[y]` — the second
load is `DTctx`-dependent on the first; the tree's fold (satp-only, writes-only) records
nothing. -/
def esCtx : List Eitem :=
  [ (LInstr, none), (LLoad false false 0 [(0, 0#8)] [], some 0),
    (LRegW 10 [.DLdRes, .DReg 9], none),
    (LInstr, none), (LRegW (wcsr MSTATUS) [.DReg 10], none),
    (LInstr, none), (LLoad false false 8 [(0, 0#8)] [], some 1) ]

theorem rowDepsTCtx : rowDepsT esCtx = [((0, 1), DTctx)] := by decide

theorem rowDepsCtxGap : rowDeps esCtx = [] := by decide

/-! # 5. The checker and the witness -/

def gtdepsWfB (G : Gexec) (deps : List Tdep) : Bool :=
  deps.all (fun e : Tdep =>
    decide (e.1.1.1 = e.1.2.1) && decide (e.1.1.2 < e.1.2.2) &&
    glblB G e.1.1 lbIsR &&
    (if dtagW e.2 then glblB G e.1.2 lbIsW else glblB G e.1.2 lbIsMem))

theorem glblMemGmem (G : Gexec) (e : Geid) : glblIs G e lbIsMem → gmem G e := fun h => h

theorem gtdepsWfBSound (G : Gexec) (deps : List Tdep) :
    gtdepsWfB G deps = true → gtdepsWf G deps := by
  rw [gtdepsWfB, forallbForallTrue]
  intro H e he
  have h := H e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, (glblBSpec _ _ _).1 h3, ?_⟩
  split
  · next hw => rw [if_pos hw] at h4; exact (glblBSpec _ _ _).1 h4
  · next hw => rw [if_neg hw] at h4; exact glblMemGmem _ _ ((glblBSpec _ _ _).1 h4)

def gtdepsGmoB (G : Gexec) (deps : List Tdep) : Bool :=
  deps.all (fun e : Tdep => gmoLtB G e.1.1 e.1.2)

theorem gtdepsGmoBSound (G : Gexec) (deps : List Tdep) :
    gtdepsGmoB G deps = true → gtdepsGmo G deps := by
  rw [gtdepsGmoB, forallbForallTrue]
  intro H e he
  exact (gmoLtBSpec _ _ _).1 (H e he)

def gtdepsRdOkB (G : Gexec) (deps : List Tdep) : Bool :=
  deps.all (fun e : Tdep =>
    !(!(gisW G e.1.2)) ||
      (decide (e.1.1.1 = e.1.2.1) && decide (e.1.1.2 < e.1.2.2) &&
       glblB G e.1.1 lbIsR && !(dtagW e.2) &&
       glblB G e.1.2 lbIsMem && gmoLtB G e.1.1 e.1.2))

theorem gtdepsRdOkBSound (GT : GdexecT) :
    gtdepsRdOkB GT.gtG GT.gtDeps = true → gtdepsRdOk GT := by
  rw [gtdepsRdOkB, forallbForallTrue]
  intro H e he hw
  have h := H e he
  rw [hw] at h
  simp only [Bool.not_false, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, (glblBSpec _ _ _).1 h3, h4, glblMemGmem _ _ ((glblBSpec _ _ _).1 h5),
    (gmoLtBSpec _ _ _).1 h6⟩

def catTConsistentB (GT : GdexecT) : Bool :=
  gwfB GT.gtG && gloadValueB GT.gtG && gatomB GT.gtG &&
  gtdepsWfB GT.gtG GT.gtDeps && gtdepsGmoB GT.gtG GT.gtDeps &&
  ppoGmoB (gppoCatB (gtAdGd GT)) GT.gtG

theorem catTConsistentBSound (GT : GdexecT) :
    catTConsistentB GT = true → rvwmoCatConsistentT GT := by
  rw [catTConsistentB]
  simp only [Bool.and_eq_true]
  rintro ⟨⟨⟨⟨⟨hwf, hlv⟩, hat⟩, hdw⟩, hdg⟩, hppo⟩
  have hdw' := gtdepsWfBSound _ _ hdw
  exact ⟨gwfBSound _ hwf, gppoCatGmoBSound (gtAdGd GT) (gtdepsWfAd _ _ hdw') hppo,
    gloadValueBSound _ hlv, gatomBSound _ hat, hdw', gtdepsGmoBSound _ _ hdg⟩

/-! ## 5.1 The witness

H0: R x (0,0) reads W1x; R y (0,1), ADDRESS-dependent on (0,0) (`DTaddr` into a READ — dropped
    by `forget`).
H1: R z (1,0); W x=1 (1,1), CONTROL-dependent on (1,0); R x (1,2) reads its own store
    (forwarded).
x = 0, y = 1, z = 2; the all-zero image.

`AxDeps.tw`: gmo = [R1x; R1z; W1x; R0x; R0y] — the forwarded read FIRST.  Tagged model: HOLDS
(rule 12 ranges over addr/data only, and the only addr edge targets a read).  Untagged cat model
on `forget AxDeps.tw`: FAILS — `gppo12` (1,0)→(1,2) through the ctrl edge demands R1z
gmo-before R1x.  riscv.cat admits it (a store whose data is known is forwarded before its branch
resolves).
`tw2`: gmo = [R1z; W1x; R1x; R0x; R0y] — both models hold; `catTOfCat`'s hypotheses are
discharged by computation. -/

def imgt : Image := fun _ => some b0

def mkgt (prog : List (List Lbl)) (gmo : List Geid) (deps : List Tdep) : GdexecT :=
  ⟨⟨imgt, prog, gmo⟩, deps⟩

def twProg : List (List Lbl) :=
  [[Lbl.LLoad false 0 [1] [b1],
    Lbl.LLoad false 1 [0] [b0]],
   [Lbl.LLoad false 2 [0] [b0],
    Lbl.LStore false 0 [b1] .WCplain,
    Lbl.LLoad false 0 [1] [b1]]]

def twDeps : List Tdep :=
  [(((0, 0), (0, 1)), DTaddr),
   (((1, 0), (1, 1)), DTctrl)]

def AxDeps.tw : GdexecT :=
  mkgt twProg [(1, 2), (1, 0), (1, 1), (0, 0), (0, 1)] twDeps

def tw2 : GdexecT :=
  mkgt twProg [(1, 0), (1, 1), (1, 2), (0, 0), (0, 1)] twDeps

theorem twCatT : rvwmoCatConsistentT AxDeps.tw :=
  catTConsistentBSound _ (by decide +kernel)

/-- `forget` keeps the ctrl edge only: the addr edge into the read is gone. -/
theorem twForgetDeps : (forget AxDeps.tw).gdDeps = [((1, 0), (1, 1))] := by decide +kernel

/-- THE SEPARATION: the untagged rule 12 orders ctrl;[W];rfi;[R]. -/
theorem twNotCatForget : ¬ rvwmoCatConsistent (forget AxDeps.tw) :=
  notCatOfRule12 _ (1, 0) (1, 2) (by decide +kernel) (by decide +kernel)

theorem twR12Edge :
    gppo12 (forget AxDeps.tw).gdG (forget AxDeps.tw).gdDeps (1, 0) (1, 2) ∧
    ¬ gppo12T AxDeps.tw (1, 0) (1, 2) ∧
    grfAt AxDeps.tw.gtG 0 (1, 1) (1, 2) := by
  refine ⟨(gppo12BSpec _ _ _ _).1 (by decide +kernel), fun H => ?_,
    (grfAtBSpec _ _ _ _).1 (by decide +kernel)⟩
  have hf : gppo12B AxDeps.tw.gtG (gtAd AxDeps.tw.gtG AxDeps.tw.gtDeps) (1, 0) (1, 2) = false := by
    decide +kernel
  have ht := (gppo12BSpec _ _ _ _).2 H
  rw [hf] at ht
  cases ht

theorem catTSeparates :
    rvwmoCatConsistentT AxDeps.tw ∧ ¬ rvwmoCatConsistent (forget AxDeps.tw) :=
  ⟨twCatT, twNotCatForget⟩

/-- `catTOfCat` exercised with every hypothesis computed. -/
theorem tw2CatForget : rvwmoCatConsistent (forget tw2) :=
  catConsistentBSound _ (by decide +kernel)

theorem tw2RdOk : gtdepsRdOk tw2 :=
  gtdepsRdOkBSound _ (by decide +kernel)

theorem tw2CatT : rvwmoCatConsistentT tw2 :=
  catTOfCat tw2 tw2CatForget tw2RdOk

/-- ... and the checker agrees. -/
theorem tw2CatTB : catTConsistentB tw2 = true := by decide +kernel

end Weak
