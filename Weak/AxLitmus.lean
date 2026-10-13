/-
Weak: **the LITMUS CONFORMANCE SUITE over the faithful `rvwmoCatConsistent`
model** (AxSL tier; design gate G0.5 track B).

Rocq: `iris/AxLitmus.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `AxGraphCat.rvwmoCatConsistent` is the faithful
riscv.cat ppo the base logic is built on; this file audits it against the
classic litmus catalogue (`WeakSrvwmoLitmus`'s shapes, in the `Gexec`/`Gdexec`
presentation).  Every test is a concrete candidate graph (tiny addresses and
values, `AxLitmus.imgw` the all-zero image) with its verdict PROVED.

TWO PROOF TECHNIQUES:
  - ALLOWED: one candidate gmo, closed by `catConsistentBSound` and the closed
    boolean computed by `decide +kernel`.
  - FORBIDDEN: the ONE NATURAL candidate gmo (usually an ALLOWED witness of this
    file plus one fence/annotation/dependency), refuted by ONE ppo edge it puts
    gmo-backwards (`notCatOfPpo`, the one-edge pattern of
    `AxGraphDec.notCatOfRule12` generalised to the whole ppo).  This is NOT a
    full permutation search ("no gmo at all works" needs completeness of
    `gwfB`/`gloadValueB`/`gatomB`, which `AxGraphDec` does not prove).  ONE test,
    `cowrForbidden`, IS proved ∀ gmo, ∀ read-index, directly at the `Prop` level.

RVWMO⁻ COMPARISON: §1 adds a whole-model boolean `minusConsistentB` for
`rvwmoMinusConsistent` (Rocq: rule 7-RCpc's boolean arm `grelAcqB` was missing;
D35-fix [OWN.54]: RVWMO⁻'s rule-7 arm is riscv.cat's RCsc `grcsc`, so `gppoMinusB` uses
`AxGraphDec.grcscB` and every litmus verdict is re-checked under riscv.cat's RCsc).
Every ALLOWED test is also checked against it; every FORBIDDEN verdict transfers
through `minusImpliesCat`'s contrapositive (`notCatNotMinus`).

No disagreement with riscv.cat/herd found.  SKIPPED in Rocq (and so here): the
.aq-RMW spinlock handoff, CoRW, 2+2W, the "R" test, and a computed RVWMO⁻
verdict for `cowr`/`corr`.  A LEAF: nothing imports this file.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase (`_b` ↦ `B`, `_spec` ↦ `Spec`, `_sound` ↦ `Sound`).
   Duplicated Rocq names (`notes/weak-port-dupnames.json`) are file-qualified:
   `AxLitmus.imgw`, `AxLitmus.mkgd`, `AxLitmus.mpw`, `AxLitmus.mpr`,
   `AxLitmus.lbCat`.
2. `vm_compute; reflexivity` (`vmr`) ↦ `decide +kernel` on the closed boolean
   (the `WeakDeps` recipe); the `vmr` tactic itself has no twin.
3. `lb_cat` / `lb_minus` are stated over `lbgd` (= `⟨lbg, []⟩`, the Rocq
   `GDExec lbg []`), definitionally the same graph.  The Lean `lbg` puts its
   second address at 8 (the Lean `WeakRvwmoGraph` port's choice); nothing here
   depends on it.
4. `cowrForbidden`: the Rocq proof's `vmr` side facts on a graph with free
   `t`/`gmo` become `rfl` / explicit witnesses (`decide` refuses free
   variables); the candidate-write case split is by `rcases` on the event id
   rather than by enumerating `gevents`.
5. The §4 `Print Assumptions` block has no Lean twin (the lint's axiom check
   covers it).
6. D35-fix ([OWN.54]; `WeakRvwmoGraph` deviation 7): `gppoMinusB`'s rule-7 arm is `grcscB`
   (Rocq: `grel_acq_b`); `grelAcqB`/`grelAcqBSpec` are kept.

**Name map** (Rocq → Lean): `imgw` ↦ `AxLitmus.imgw`; `mkgd` ↦
`AxLitmus.mkgd`; `not_cat_of_ppo` ↦ `notCatOfPpo`; `not_cat_not_minus` ↦
`notCatNotMinus`; `grel_acq_b` ↦ `grelAcqB`; `grel_acq_b_spec` ↦
`grelAcqBSpec`; `gppo_minus_b` ↦ `gppoMinusB`; `gppo_minus_b_spec` ↦
`gppoMinusBSpec`; `gppo_minus_gevents` ↦ `gppoMinusGevents`;
`minus_consistent_b` ↦ `minusConsistentB`; `minus_consistent_b_sound` ↦
`minusConsistentBSound`; `minus_consistent_b_gdexec_sound` ↦
`minusConsistentBGdexecSound`; `sb`; `sb_cat` ↦ `sbCat`; `sb_minus` ↦
`sbMinus`; `mpn`; `mpn_cat` ↦ `mpnCat`; `mpn_minus` ↦ `mpnMinus`; `mpw` ↦
`AxLitmus.mpw`; `mpw_cat` ↦ `mpwCat`; `mpw_minus` ↦ `mpwMinus`; `mpr` ↦
`AxLitmus.mpr`; `mpr_cat` ↦ `mprCat`; `mpr_minus` ↦ `mprMinus`; `mprmw`;
`mprmw_cat` ↦ `mprmwCat`; `mprmw_minus` ↦ `mprmwMinus`; `lb_cat` ↦
`AxLitmus.lbCat`; `lb_minus` ↦ `lbMinus`; `coww`; `coww_cand_inconsistent` ↦
`cowwCandInconsistent`; `coww_not_minus` ↦ `cowwNotMinus`; `mpdf`;
`mpdf_cand_inconsistent` ↦ `mpdfCandInconsistent`; `mpdf_not_minus` ↦
`mpdfNotMinus`; `mpaq`; `mpaq_cand_inconsistent` ↦ `mpaqCandInconsistent`;
`mpaq_not_minus` ↦ `mpaqNotMinus`; `sbdf`; `sbdf_cand_inconsistent` ↦
`sbdfCandInconsistent`; `sbdf_not_minus` ↦ `sbdfNotMinus`; `corr`;
`corr_cat_inconsistent` ↦ `corrCatInconsistent`; `corr_not_minus` ↦
`corrNotMinus`; `gppo_cat_no2_b` ↦ `gppoCatNo2B`; `cat_consistent_no2_b` ↦
`catConsistentNo2B`; `corr_no2_accepts` ↦ `corrNo2Accepts`; `lbgd_deps` ↦
`lbgdDeps`; `lb_deps_cand_inconsistent` ↦ `lbDepsCandInconsistent`;
`lb_deps_not_minus` ↦ `lbDepsNotMinus`; `cowr_prog` ↦ `cowrProg`; `cowr`;
`cowr_forbidden` ↦ `cowrForbidden`; `cowr_not_minus` ↦ `cowrNotMinus`.

**Not ported:** the `vmr` tactic and the `Print Assumptions` block (deviations
2 and 5).  Every definition and lemma is ported.
-/
import Weak.AxGraphDec

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl

/-- The all-zero image (every byte defined). -/
def AxLitmus.imgw : Image := fun _ => some b0

def AxLitmus.mkgd (prog : List (List Lbl)) (gmo : List Geid)
    (deps : List (Geid × Geid)) : Gdexec :=
  ⟨⟨AxLitmus.imgw, prog, gmo⟩, deps, []⟩

/-! # 1. General infrastructure -/

/-- The one-edge cat refuter: a `gppoCat` edge that is not gmo-forward. -/
theorem notCatOfPpo (GD : Gdexec) (e1 e2 : Geid) :
    gppoCatB GD e1 e2 = true → gmoLtB GD.gdG e1 e2 = false →
    ¬ rvwmoCatConsistent GD := by
  rintro hp hmo ⟨_, hppo, _⟩
  have h := (gmoLtBSpec _ _ _).2 (hppo e1 e2 ((gppoCatBSpec _ _ _).1 hp))
  rw [hmo] at h
  cases h

/-- Every FORBIDDEN verdict transfers to RVWMO⁻ (RVWMO⁻ ⊆ the cat model). -/
theorem notCatNotMinus (GD : Gdexec) :
    ¬ rvwmoCatConsistent GD → ¬ rvwmoMinusDepsConsistent GD :=
  fun hnc hm => hnc (minusImpliesCat GD hm)

/-- Rocq's RVWMO⁻ rule-7 arm `[W.rl];po;[R.aq]`, Boolean (D35-fix [OWN.54]: RVWMO⁻'s arm is now
the RCsc-wide `grcscB`, `AxGraphDec`; `grelAcqB` is kept as a lemma-level twin of `grelAcq`). -/
def grelAcqB (G : Gexec) (e1 e2 : Geid) : Bool :=
  gpoB G e1 e2 && glblB G e1 lbIsW && glblB G e1 lbRl &&
  glblB G e2 lbIsR && glblB G e2 lbAq

theorem grelAcqBSpec (G : Gexec) (e1 e2 : Geid) : grelAcqB G e1 e2 = true ↔ grelAcq G e1 e2 := by
  simp only [grelAcqB, grelAcq, Bool.and_eq_true, gpoBSpec, glblBSpec, and_assoc]

def gppoMinusB (G : Gexec) (e1 e2 : Geid) : Bool :=
  gpolocB G e1 e2 || gfenceB G e1 e2 || gacqB G e1 e2 || grcscB G e1 e2

theorem gppoMinusBSpec (G : Gexec) (e1 e2 : Geid) : gppoMinusB G e1 e2 = true ↔ gppo G e1 e2 := by
  simp only [gppoMinusB, gppo, Bool.or_eq_true, gpolocBSpec, gfenceBSpec, gacqBSpec,
    grcscBSpec, or_assoc]

/-- ppo⁻'s four arms are all events (fed to `ppoGmoBSound`). -/
theorem gppoMinusGevents (G : Gexec) (e1 e2 : Geid) :
    gppo G e1 e2 → e1 ∈ gevents G ∧ e2 ∈ gevents G := by
  rintro (⟨hpo, _⟩ | ⟨_, _, _, _, _, hc1, hc2⟩ | ⟨hpo, _⟩ | ⟨hpo, _⟩)
  · exact gpoGevents G e1 e2 hpo
  · refine ⟨?_, ?_⟩
    · rcases hc1 with ⟨⟨l, hl, _⟩, _⟩ | ⟨⟨l, hl, _⟩, _⟩ <;> exact geventsOfLbl G e1 l hl
    · rcases hc2 with ⟨⟨l, hl, _⟩, _⟩ | ⟨⟨l, hl, _⟩, _⟩ <;> exact geventsOfLbl G e2 l hl
  · exact gpoGevents G e1 e2 hpo
  · exact gpoGevents G e1 e2 hpo

def minusConsistentB (G : Gexec) : Bool :=
  gwfB G && gloadValueB G && gatomB G && ppoGmoB (gppoMinusB G) G

theorem minusConsistentBSound (G : Gexec) :
    minusConsistentB G = true → rvwmoMinusConsistent G := by
  rw [minusConsistentB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  rintro ⟨⟨⟨hwf, hlv⟩, hat⟩, hppo⟩
  exact ⟨gwfBSound G hwf,
    ppoGmoBSound (gppoMinusB G) (gppo G) G (gppoMinusBSpec G) (gppoMinusGevents G) hppo,
    gloadValueBSound G hlv, gatomBSound G hat⟩

/-- The `Gdexec`-level form for the deps-free witnesses. -/
theorem minusConsistentBGdexecSound (GD : Gdexec) :
    minusConsistentB GD.gdG = true → GD.gdDeps = [] →
    rvwmoMinusDepsConsistent GD := by
  intro hb hd
  refine ⟨minusConsistentBSound _ hb, ?_, ?_⟩ <;>
    (intro rw hrw; rw [hd] at hrw; cases hrw)

/-! # 2. ALLOWED — one witness gmo, `catConsistentBSound` + `decide +kernel` -/

/-- SB — both loads read 0 (herd: Allowed). -/
def sb : Gdexec :=
  AxLitmus.mkgd [[LStore false 0 [b1] .WCplain, LLoad false 1 [0] [b0]],
                 [LStore false 1 [b1] .WCplain, LLoad false 0 [0] [b0]]]
    [(1, 1), (0, 1), (0, 0), (1, 0)]
    []

theorem sbCat : rvwmoCatConsistent sb := catConsistentBSound _ (by decide +kernel)

theorem sbMinus : rvwmoMinusDepsConsistent sb :=
  minusConsistentBGdexecSound _ (by decide +kernel) rfl

/-- MP, no fences — flag seen, data stale (herd: Allowed). -/
def mpn : Gdexec :=
  AxLitmus.mkgd [[LStore false 0 [b1] .WCplain, LStore false 1 [b1] .WCplain],
                 [LLoad false 1 [2] [b1], LLoad false 0 [0] [b0]]]
    [(1, 1), (0, 0), (0, 1), (1, 0)]
    []

theorem mpnCat : rvwmoCatConsistent mpn := catConsistentBSound _ (by decide +kernel)

theorem mpnMinus : rvwmoMinusDepsConsistent mpn :=
  minusConsistentBGdexecSound _ (by decide +kernel) rfl

/-- MP, writer fence rw,w ONLY — still Allowed (the reader is unfenced). -/
def AxLitmus.mpw : Gdexec :=
  AxLitmus.mkgd [[LStore false 0 [b1] .WCplain, LFence true true false true,
                  LStore false 1 [b1] .WCplain],
                 [LLoad false 1 [2] [b1], LLoad false 0 [0] [b0]]]
    [(1, 1), (0, 0), (0, 2), (1, 0)]
    []

theorem mpwCat : rvwmoCatConsistent AxLitmus.mpw := catConsistentBSound _ (by decide +kernel)

theorem mpwMinus : rvwmoMinusDepsConsistent AxLitmus.mpw :=
  minusConsistentBGdexecSound _ (by decide +kernel) rfl

/-- MP, reader fence r,rw ONLY — still Allowed: the witness gmo places BOTH reads
before the writer's store to `x`. -/
def AxLitmus.mpr : Gdexec :=
  AxLitmus.mkgd [[LStore false 0 [b1] .WCplain, LStore false 1 [b1] .WCplain],
                 [LLoad false 1 [1] [b1], LFence true false true true,
                  LLoad false 0 [0] [b0]]]
    [(0, 1), (1, 0), (1, 2), (0, 0)]
    []

theorem mprCat : rvwmoCatConsistent AxLitmus.mpr := catConsistentBSound _ (by decide +kernel)

theorem mprMinus : rvwmoMinusDepsConsistent AxLitmus.mpr :=
  minusConsistentBGdexecSound _ (by decide +kernel) rfl

/-- MP through a PLAIN (non-.aq) RMW, then a plain load of data — Allowed: the
amoswap carries no acquire bit, so rule 5 never fires. -/
def mprmw : Gdexec :=
  AxLitmus.mkgd [[LStore false 0 [b1] .WCplain, LFence true true false true,
                  LStore false 1 [b1] .WCplain],
                 [LRmw false false 1 [2] [b1] [b2] .WCplain,
                  LLoad false 0 [0] [b0]]]
    [(1, 1), (0, 0), (0, 2), (1, 0)]
    []

theorem mprmwCat : rvwmoCatConsistent mprmw := catConsistentBSound _ (by decide +kernel)

theorem mprmwMinus : rvwmoMinusDepsConsistent mprmw :=
  minusConsistentBGdexecSound _ (by decide +kernel) rfl

/-- LB, plain — r1 = r2 = 1 (herd: Allowed under RVWMO/RVWMO⁻); cites the tree's
own witness. -/
theorem AxLitmus.lbCat : rvwmoCatConsistent lbgd := minusImpliesCat _ lbGraphDepsConsistent

theorem lbMinus : rvwmoMinusDepsConsistent lbgd := lbGraphDepsConsistent

/-! # 3. FORBIDDEN

Six of the seven exhibit the ONE NATURAL candidate gmo and refute it with
`notCatOfPpo` or `gdepsGmo` directly (`*CandInconsistent`, each naming the ppo
arm it certifies); `cowrForbidden` is the ∀-quantified exception. -/

/-- CoWW — two same-hart same-address writes, candidate gmo REVERSES them (herd:
Forbidden by rule 1). -/
def coww : Gdexec :=
  AxLitmus.mkgd [[LStore false 0 [b1] .WCplain, LStore false 0 [b2] .WCplain]]
    [(0, 1), (0, 0)]
    []

/-- Certifies: rule 1 (`[M];po-loc;[W]`) is a `gppoCat` edge on `coww`. -/
theorem cowwCandInconsistent : ¬ rvwmoCatConsistent coww :=
  notCatOfPpo coww (0, 0) (0, 1) (by decide +kernel) (by decide +kernel)

theorem cowwNotMinus : ¬ rvwmoMinusDepsConsistent coww :=
  notCatNotMinus coww cowwCandInconsistent

/-- MP, BOTH fences (writer rw,w AND reader r,rw) — herd: Forbidden. -/
def mpdf : Gdexec :=
  AxLitmus.mkgd [[LStore false 0 [b1] .WCplain, LFence true true false true,
                  LStore false 1 [b1] .WCplain],
                 [LLoad false 1 [2] [b1], LFence true false true true,
                  LLoad false 0 [0] [b0]]]
    [(1, 2), (0, 0), (0, 2), (1, 0)]
    []

/-- Certifies: rule 4 (through the reader's fence) is a `gppoCat` edge on `mpdf`. -/
theorem mpdfCandInconsistent : ¬ rvwmoCatConsistent mpdf :=
  notCatOfPpo mpdf (1, 0) (1, 2) (by decide +kernel) (by decide +kernel)

theorem mpdfNotMinus : ¬ rvwmoMinusDepsConsistent mpdf :=
  notCatNotMinus mpdf mpdfCandInconsistent

/-- MP, an .aq load on the reader + writer fence rw,w — herd: Forbidden (rule 5). -/
def mpaq : Gdexec :=
  AxLitmus.mkgd [[LStore false 0 [b1] .WCplain, LFence true true false true,
                  LStore false 1 [b1] .WCplain],
                 [LLoad true 1 [2] [b1], LLoad false 0 [0] [b0]]]
    [(1, 1), (0, 0), (0, 2), (1, 0)]
    []

/-- Certifies: rule 5 (`[AQ];po;[M]`) is a `gppoCat` edge on `mpaq`. -/
theorem mpaqCandInconsistent : ¬ rvwmoCatConsistent mpaq :=
  notCatOfPpo mpaq (1, 0) (1, 1) (by decide +kernel) (by decide +kernel)

theorem mpaqNotMinus : ¬ rvwmoMinusDepsConsistent mpaq :=
  notCatNotMinus mpaq mpaqCandInconsistent

/-- SB, fence rw,rw on BOTH — herd: Forbidden. -/
def sbdf : Gdexec :=
  AxLitmus.mkgd [[LStore false 0 [b1] .WCplain, LFence true true true true,
                  LLoad false 1 [0] [b0]],
                 [LStore false 1 [b1] .WCplain, LFence true true true true,
                  LLoad false 0 [0] [b0]]]
    [(1, 2), (0, 2), (0, 0), (1, 0)]
    []

/-- Certifies: rule 4 (through both fences) is a `gppoCat` edge on `sbdf`. -/
theorem sbdfCandInconsistent : ¬ rvwmoCatConsistent sbdf :=
  notCatOfPpo sbdf (0, 0) (0, 2) (by decide +kernel) (by decide +kernel)

theorem sbdfNotMinus : ¬ rvwmoMinusDepsConsistent sbdf :=
  notCatNotMinus sbdf sbdfCandInconsistent

/-- CoRR — the classic CROSS-HART shape: hart 1's first read sees the NEWER
value, its po-later read the OLDER one.  The candidate gmo satisfies
gwf/load-value/atomicity and isolates rule 2 (herd: Forbidden by rule 2). -/
def corr : Gdexec :=
  AxLitmus.mkgd [[LStore false 0 [b1] .WCplain, LStore false 0 [b2] .WCplain],
                 [LLoad false 0 [2] [b2], LLoad false 0 [1] [b1]]]
    [(0, 0), (1, 1), (0, 1), (1, 0)]
    []

/-- Certifies: rule 2 is a `gppoCat` edge on `corr`. -/
theorem corrCatInconsistent : ¬ rvwmoCatConsistent corr :=
  notCatOfPpo corr (1, 0) (1, 1) (by decide +kernel) (by decide +kernel)

theorem corrNotMinus : ¬ rvwmoMinusDepsConsistent corr :=
  notCatNotMinus corr corrCatInconsistent

/-- THE ISOLATION CHECK: the boolean ppo WITHOUT rule 2 accepts `corr`. -/
def gppoCatNo2B (GD : Gdexec) (e1 e2 : Geid) : Bool :=
  gppo1B GD.gdG e1 e2 || gppo3B GD.gdG e1 e2 ||
  gfenceB GD.gdG e1 e2 || gacqB GD.gdG e1 e2 ||
  grcscB GD.gdG e1 e2 || gppo12B GD.gdG GD.gdDeps e1 e2

def catConsistentNo2B (GD : Gdexec) : Bool :=
  axiomsB GD && ppoGmoB (gppoCatNo2B GD) GD.gdG

theorem corrNo2Accepts : catConsistentNo2B corr = true := by decide +kernel

/-- LB with a data dependency on EACH side (also the LB+ctrl shape: `gdDeps` does
not tag edges by kind). -/
def lbgdDeps : Gdexec := ⟨lbg, [((0, 0), (0, 1)), ((1, 0), (1, 1))], []⟩

/-- Certifies the `gdepsGmo` AXIOM, not a `gppoCat` arm. -/
theorem lbDepsCandInconsistent : ¬ rvwmoCatConsistent lbgdDeps := by
  rintro ⟨_, _, _, _, _, hdg⟩
  have h1 : gmoLt lbg (0, 0) (0, 1) := hdg ((0, 0), (0, 1)) (by decide)
  have h := (gmoLtBSpec _ _ _).2 h1
  rw [show gmoLtB lbg (0, 0) (0, 1) = false by decide +kernel] at h
  cases h

theorem lbDepsNotMinus : ¬ rvwmoMinusDepsConsistent lbgdDeps :=
  notCatNotMinus lbgdDeps lbDepsCandInconsistent

/-- CoWR — own-later-write coherence, proved ∀ gmo AND ∀ read-index.  One hart:
`w1`=1, `w2`=2 at the same address, then a read claiming the STALE `w1` value.
`w2` is po-before the read, hence visible in EVERY gmo, so the read's index must
dominate `gwix w2`; rule 1 forces `gwix w1 < gwix w2`; the read's own claim pins
its index to `gwix w1`. -/
def cowrProg (t : Nat) : List (List Lbl) :=
  [[LStore false 0 [b1] .WCplain,
    LStore false 0 [b2] .WCplain,
    LLoad false 0 [t] [b1]]]

def cowr (t : Nat) (gmo : List Geid) : Gdexec := AxLitmus.mkgd (cowrProg t) gmo []

theorem cowrForbidden (t : Nat) (gmo : List Geid) : ¬ rvwmoCatConsistent (cowr t gmo) := by
  rintro ⟨hwf, hppo, hlv, _, _, _⟩
  have hl0 : gxLbl (cowr t gmo).gdG (0, 0) = some (LStore false 0 [b1] .WCplain) := rfl
  have hl1 : gxLbl (cowr t gmo).gdG (0, 1) = some (LStore false 0 [b2] .WCplain) := rfl
  have hl2 : gxLbl (cowr t gmo).gdG (0, 2) = some (LLoad false 0 [t] [b1]) := rfl
  have hw1 : gwritesByte (cowr t gmo).gdG (0, 0) 0 b1 := ⟨_, 0, [b1], 0, hl0, rfl, rfl, rfl⟩
  have hw2 : gwritesByte (cowr t gmo).gdG (0, 1) 0 b2 := ⟨_, 0, [b2], 0, hl1, rfl, rfl, rfl⟩
  have hr : greadsByte (cowr t gmo).gdG (0, 2) 0 t b1 :=
    ⟨_, 0, [t], [b1], 0, hl2, rfl, rfl, rfl, rfl⟩
  have hgpo01 : WeakRvwmoGraph.gpo (cowr t gmo).gdG (0, 0) (0, 1) :=
    ⟨rfl, by decide, by rw [hl0]; rfl, by rw [hl1]; rfl⟩
  have hpo12 : WeakRvwmoGraph.gpo (cowr t gmo).gdG (0, 1) (0, 2) :=
    ⟨rfl, by decide, by rw [hl1]; rfl, by rw [hl2]; rfl⟩
  have hvisw2 : gvisible (cowr t gmo).gdG (0, 1) (0, 2) := Or.inr hpo12
  have hrule1 : gppo1 (cowr t gmo).gdG (0, 0) (0, 1) :=
    ⟨hgpo01, 0, Or.inl ⟨b1, hw1⟩, b2, hw2⟩
  have hlt12 : gmoLt (cowr t gmo).gdG (0, 0) (0, 1) := hppo _ _ (Or.inl (Or.inl hrule1))
  have hisw1 : gisW (cowr t gmo).gdG (0, 0) = true := rfl
  have hisw2 : gisW (cowr t gmo).gdG (0, 1) = true := rfl
  have hmemw1 : gmem (cowr t gmo).gdG (0, 0) := ⟨_, hl0, rfl⟩
  have hmemw2 : gmem (cowr t gmo).gdG (0, 1) := ⟨_, hl1, rfl⟩
  have hw1in : (0, 0) ∈ gwrites (cowr t gmo).gdG :=
    (gwritesElemOf _ _).2 ⟨(hwf.2.1 _).2 hmemw1, hisw1⟩
  have hw2in : (0, 1) ∈ gwrites (cowr t gmo).gdG :=
    (gwritesElemOf _ _).2 ⟨(hwf.2.1 _).2 hmemw2, hisw2⟩
  have hgwixlt : gwix (cowr t gmo).gdG (0, 0) < gwix (cowr t gmo).gdG (0, 1) :=
    (gwixGposLt _ _ _ hwf.1 hw1in hw2in).2 hlt12.2.2
  cases t with
  | zero =>
    have himg : some b0 = some b1 := (hlv _ _ _ _ hr).1
    exact b0NeB1 (Option.some.inj himg)
  | succ i =>
    obtain ⟨⟨w, hwa, hwb, _⟩, hmax⟩ := hlv _ _ _ _ hr
    have hw10 : w = (0, 0) := by
      obtain ⟨wi, wk⟩ := w
      obtain ⟨l, base, vs, j, hl, hwr, _, _⟩ := id hwb
      rcases wi with _ | wi
      · rcases wk with _ | _ | _ | wk
        · rfl
        · exact absurd (gwritesByteDet _ (0, 1) 0 b1 b2 hwb hw2) b1NeB2
        · rw [hl2] at hl
          cases hl
          cases hwr
        · simp [gxLbl, cowr, AxLitmus.mkgd, cowrProg] at hl
      · simp [gxLbl, cowr, AxLitmus.mkgd, cowrProg] at hl
    subst hw10
    obtain ⟨_, hwix1⟩ := gwriteAtInv _ (i + 1) (0, 0) hwf.1 hwa
    have hm := hmax (0, 1) b2 hw2 hvisw2
    omega

theorem cowrNotMinus (t : Nat) (gmo : List Geid) : ¬ rvwmoMinusDepsConsistent (cowr t gmo) :=
  notCatNotMinus (cowr t gmo) (cowrForbidden t gmo)

end Weak
