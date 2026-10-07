/-
Weak: **a real emission run is graph-value-pinned** (advisor fix 5, design §7.A) — a conformant
emission (`hemit`/`hartConf`, the tree's per-hart conformance relation) is a run of `astepAnyNfGv`
steps, GIVEN that the emission's own read items already carry the graph's values
(`emReadsAtGraphValues GD i em`: every read item `(l, some k)` has `graphValue GD (i, k) =
some (wlRvals l)`).

Rocq: `iris/AxRunGV2.v` @ xxvzwolszwmp.

## What this file proves

1. `itemsGv` (over an arbitrary item list — what the induction carries, since a block's tail is a
   suffix of the top list: `itemsGvAppR`/`itemsGvTail`/`itemsGvHead`) and its emission form
   `emReadsAtGraphValues`.
2. `hemitRunAtGraphValuesAux`: `AxOpsem.hemitAstepAux`'s induction, landing in
   `nsteps (astepAnyNfGv GD i)` instead of `nsteps (astepAny …)`; the read arm (`readBlockGv`,
   `readBlock`'s analogue) PINNED to the emission's recorded value via `itemsGv`, the admin
   stretch (`admRunAstepGv`, `admRunAstep`'s analogue) covering the wire step via `ANFGVWire`.
   Why `astepAnyNfGv` and not `runAtGraphValues` (Rocq header): an admin stretch of `hemit` may
   interleave a PLIC-wire step, which `runAtGraphValues` has no arm for.
3. `hemitRunAtGraphValues`: the `hartConf` specialization (row `AxOpsem.grow GD i`, position 0 to
   its length) and its `rtc` corollary `hemitRunAtGraphValuesRtc`.
4. Satisfiability: `emReadsAtGraphValuesNil`/`emReadsAtGraphValuesWitness` (the trivial
   read-free emission `⟨[], p0⟩` over an empty row).

## Deviations from Rocq

1. OWNER Q8 / STAGE C (AxRunGV deviation 2): `astepAnyNfGv`'s program arm carries the boot-image
   pin `WeakAxRealize.fetchPin GD.gdG.gxImg l` instead of Rocq's `wlabel_is_fetch l = false`.
   Write/fence labels are pinned trivially (`fetchPin` is `True` off `LIFetch`), but an ADMIN
   step may now be a fetch, so `admRunAstepGv`, `hemitRunAtGraphValuesAux`,
   `hemitRunAtGraphValues` and `hemitRunAtGraphValuesRtc` take the extra premise
   `hpin : ∀ p d l p' d', pstepProg p d l p' d' → lbAdmin true l →
   WeakAxRealize.fetchPin GD.gdG.gxImg l` (exactly `AxRunGV.runAtGraphValuesNfGv`'s; discharged
   from the pinned LTS, cf. `AxAdequacy.astepProgNfOfPinned`).  No Rocq file uses these lemmas
   (AxLock3Prog only imports the file).
2. NAMES: camelCase; `is_Some (wl_rd l)` ↦ `(wlRd l).isSome = true`; `S k` ↦ `k + 1`;
   `AThread p k` ↦ `⟨p, k⟩`; `HEm [] p0` ↦ `⟨[], p0⟩`; the Rocq section variables `GD`/`i` are
   explicit arguments.

## Rocq → Lean name map

`items_gv` `itemsGv`, `em_reads_at_graph_values` `emReadsAtGraphValues`, `items_gv_app_r`
`itemsGvAppR`, `items_gv_tail` `itemsGvTail`, `items_gv_head` `itemsGvHead`,
`em_reads_at_graph_values_nil` `emReadsAtGraphValuesNil`, `em_reads_at_graph_values_witness`
`emReadsAtGraphValuesWitness`, `adm_run_astep_gv` `admRunAstepGv`, `read_block_gv`
`readBlockGv`, `hemit_run_at_graph_values_aux` `hemitRunAtGraphValuesAux`,
`hemit_run_at_graph_values` `hemitRunAtGraphValues`, `hemit_run_at_graph_values_rtc`
`hemitRunAtGraphValuesRtc`.

**Dropped:** only the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxRunGV

namespace Weak

open MachCSL MachCSL.Stdpp
open Wlabel

/-! # 1. `emReadsAtGraphValues` -/

section RunGV2
variable (GD : Gdexec) (i : Agent)

/-- Every read item of an item list carries the graph's value at its row position. -/
def itemsGv (its : List Eitem) : Prop :=
  ∀ l k, (l, some k) ∈ its → (wlRd l).isSome = true →
    graphValue GD (i, k) = some (wlRvals l)

/-- The emission-level vocabulary. -/
def emReadsAtGraphValues (em : Hemission) : Prop :=
  itemsGv GD i em.emItems

theorem itemsGvAppR (a b : List Eitem) : itemsGv GD i (a ++ b) → itemsGv GD i b :=
  fun h l k hin hrd => h l k (List.mem_append.2 (.inr hin)) hrd

theorem itemsGvTail (x : Eitem) (xs : List Eitem) : itemsGv GD i (x :: xs) → itemsGv GD i xs :=
  fun h l k hin hrd => h l k (List.mem_cons_of_mem _ hin) hrd

theorem itemsGvHead (l : Wlabel) (k : Nat) (xs : List Eitem) :
    itemsGv GD i ((l, some k) :: xs) → (wlRd l).isSome = true →
    graphValue GD (i, k) = some (wlRvals l) :=
  fun h hrd => h l k List.mem_cons_self hrd

/-! ## 1.1 Satisfiability: the trivial read-free emission -/

theorem emReadsAtGraphValuesNil (p0 : Pexv6) : emReadsAtGraphValues GD i ⟨[], p0⟩ :=
  fun _ _ hin _ => absurd hin List.not_mem_nil

theorem emReadsAtGraphValuesWitness (p0 : Pexv6) (dv : Nat → Efab) :
    AxOpsem.grow GD i = [] →
    hartConf i (AxOpsem.grow GD i) p0 dv ⟨[], p0⟩ ∧ emReadsAtGraphValues GD i ⟨[], p0⟩ := by
  intro hrow
  rw [hrow]
  exact ⟨hartConfNil i p0 dv, emReadsAtGraphValuesNil GD i p0⟩

/-! # 2. The real run is graph-value-pinned -/

/-- `admRunAstep`'s analogue: an administrative stretch is a run of `astepAnyNfGv` steps at a
fixed row position — program steps as `AStepAdmin` (pinned by `hpin`, deviation 1), wire steps
via `ANFGVWire`. -/
theorem admRunAstepGv
    (hpin : ∀ p d l p' d', pstepProg p d l p' d' → lbAdmin true l →
      WeakAxRealize.fetchPin GD.gdG.gxImg l)
    (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6) (d' : Efab)
    (k : Nat) :
    admRun instr p d ls p' d' → nsteps (astepAnyNfGv GD i) ls.length ⟨p, k⟩ ⟨p', k⟩ := by
  intro h
  induction h with
  | ARnil p d => exact nsteps_O _
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih =>
    refine nsteps_l ?_ ih
    rcases (pstepEvSplit p d l p1 d1).1 hs with hs | hw
    · have ha' : lbAdmin true l := by
        cases instr
        · exact lbAdminMono true l ha
        · exact ha
      exact .ANFGVProg _ _ ⟨l, AxOpsem.astepProg.AStepAdmin p k d l p1 d1 ha' hs,
        hpin p d l p1 d1 hs ha'⟩
    · obtain ⟨rfl, _⟩ := pstepWireInv _ _ _ _ _ hw
      exact .ANFGVWire _ _ ⟨rfl, d, d1, hw⟩

/-- `readBlock`'s analogue: a program step realizing a read row item, at the PINNED value
`graphValue GD (i, k)`. -/
theorem readBlockGv (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) (k : Nat)
    (lb : Lbl) :
    pstepProg p d l p' d' → (wlRd l).isSome = true →
    (AxOpsem.grow GD i)[k]? = some lb → wlRd l = aidentRd (aident lb) →
    graphValue GD (i, k) = some (wlRvals l) →
    astepAnyNfGv GD i ⟨p, k⟩ ⟨p', k + aidentAdvRd (aident lb)⟩ := by
  intro hs hrd hrow hid hgv
  obtain ⟨F, rfl, hdd, HF⟩ := pstepProgReadCont p d l p' d' hs hrd
  subst d'
  obtain ⟨⟨aq, base, n⟩, hl⟩ := Option.isSome_iff_exists.1 hrd
  have hn : aidentN (aident lb) = (wlRvals l).length := by
    rw [aidentRdN _ aq base n (hid.symm.trans hl), wlRdN l aq base n hl]
  have hrb : areadStep (AxOpsem.grow GD i) ⟨p, k⟩ (aident lb)
      (fun vs => ⟨F vs, k + aidentAdvRd (aident lb)⟩) := by
    refine ⟨lb, hrow, rfl, by rw [← hid]; exact hrd, ?_⟩
    intro vs hvs
    refine ⟨wlReval l vs, d, d, ?_, wlRevalRvals l vs hrd, HF vs (by rw [hvs, hn]) d, rfl⟩
    rw [wlRevalRd l vs (by rw [hvs, hn])]
    exact hid
  exact astepAnyNfGv.ANFGVRead _ _ _ (wlRvals l) hrb hgv hn.symm

/-- THE MAIN INDUCTION: `hemitAstepAux`'s case split, retyped into `astepAnyNfGv` with the read
arm pinned by `itemsGv`. -/
theorem hemitRunAtGraphValuesAux
    (hpin : ∀ p d l p' d', pstepProg p d l p' d' → lbAdmin true l →
      WeakAxRealize.fetchPin GD.gdG.gxImg l)
    (dv : Nat → Efab) (k : Nat) (ws : Wstate) (rrow : List Lbl) (p : Pexv6) (es : List Eitem)
    (pfin : Pexv6) :
    hemit dv k ws rrow p es pfin →
    (∀ j, rrow[j]? = (AxOpsem.grow GD i)[k + j]?) →
    itemsGv GD i es →
    nsteps (astepAnyNfGv GD i) es.length ⟨p, k⟩ ⟨pfin, k + rrow.length⟩ := by
  intro h
  induction h with
  | HEnil k ws p => intro _ _; exact nsteps_O _
  | HEone k ws lb rrow' p ls pa da l p' es pfin har hre hst _ ih =>
    intro hrow hgv
    have hlb : (AxOpsem.grow GD i)[k]? = some lb := by
      have h0 := hrow 0
      simp only [List.getElem?_cons_zero, Nat.add_zero] at h0
      exact h0.symm
    have hrow' : ∀ j, rrow'[j]? = (AxOpsem.grow GD i)[k + 1 + j]? := by
      intro j
      have hj := hrow (j + 1)
      simp only [List.getElem?_cons_succ] at hj
      rw [hj, show k + (j + 1) = k + 1 + j by omega]
    have hgv1 : itemsGv GD i ((l, some k) :: es) := itemsGvAppR GD i (eadm ls) _ hgv
    have hgvT : itemsGv GD i es := itemsGvTail GD i _ _ hgv1
    have har' := admRunAstepGv GD i hpin true _ _ _ _ _ k har
    have hstep : astepAnyNfGv GD i ⟨pa, k⟩ ⟨p', k + 1⟩ := by
      obtain ⟨hnb, _, _, hpr⟩ := hre
      rcases (pstepEvSplit _ _ _ _ _).1 hst with hs | hw
      · cases l with
        | LLoad aq lat base tvs asrc =>
          have hrd := (aidentProj _ _ _ hpr rfl).1
          have hg := itemsGvHead GD i _ _ _ hgv1 rfl
          simp only [projLbl, Option.some.injEq] at hpr; subst hpr
          exact readBlockGv GD i _ _ _ _ _ k _ hs rfl hlb hrd hg
        | LExLoad aq base tvs asrc =>
          have hrd := (aidentProj _ _ _ hpr rfl).1
          have hg := itemsGvHead GD i _ _ _ hgv1 rfl
          simp only [projLbl, Option.some.injEq] at hpr; subst hpr
          exact readBlockGv GD i _ _ _ _ _ k _ hs rfl hlb hrd hg
        | LIFetch => simp [projLbl] at hpr
        | LStore rl base data asrc vsrc =>
          have hwr := (aidentProj _ _ _ hpr rfl).2.1
          have hdat := aidentProjData _ _ _ hpr rfl
          exact .ANFGVProg _ _ ⟨_, .AStepWrite _ k _ _ lb _ _ hlb rfl hwr hdat hs, trivial⟩
        | LFence pr pw sr sw =>
          have hf := (aidentProj _ _ _ hpr rfl).2.2
          exact .ANFGVProg _ _ ⟨_, .AStepFence _ k _ _ lb _ _ hlb rfl hf hs, trivial⟩
        | LRmw aq rl base tvs data asrc vsrc =>
          exact absurd hst (pstepEvNoRmw _ _ _ _ _ _ _ _ _ _ _)
        | LExStore => exact False.elim hnb
        | LSilent => simp [projLbl] at hpr
        | LDev => simp [projLbl] at hpr
        | LRegW => simp [projLbl] at hpr
        | LCtrl => simp [projLbl] at hpr
        | LInstr => simp [projLbl] at hpr
      · obtain ⟨rfl, _⟩ := pstepWireInv _ _ _ _ _ hw
        simp [projLbl] at hpr
    have e1 : (eadm ls ++ (l, some k) :: es).length = ls.length + (es.length + 1) := by
      simp [eadm]
    have e2 : k + (lb :: rrow').length = k + 1 + rrow'.length := by
      simp only [List.length_cons]; omega
    rw [e1, e2]
    exact nsteps_trans har' (nsteps_l hstep (ih hrow' hgvT))
  | HEpair k ws lb rrow' p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2
      hst2 _ ih =>
    intro hrow hgv
    have hlb : (AxOpsem.grow GD i)[k]? = some lb := by
      have h0 := hrow 0
      simp only [List.getElem?_cons_zero, Nat.add_zero] at h0
      exact h0.symm
    have hrow' : ∀ j, rrow'[j]? = (AxOpsem.grow GD i)[k + 1 + j]? := by
      intro j
      have hj := hrow (j + 1)
      simp only [List.getElem?_cons_succ] at hj
      rw [hj, show k + (j + 1) = k + 1 + j by omega]
    obtain ⟨hrd1, hsome1, hwr2, hsome2, hadv⟩ := aidentPair _ _ _ _ _ _ hre
    have hgv1 : itemsGv GD i ((l1, some k) :: (eadm ls2 ++ (l2, some k) :: es)) :=
      itemsGvAppR GD i (eadm ls1) _ hgv
    have hgv2 : itemsGv GD i (eadm ls2 ++ (l2, some k) :: es) := itemsGvTail GD i _ _ hgv1
    have hgv3 : itemsGv GD i ((l2, some k) :: es) := itemsGvAppR GD i (eadm ls2) _ hgv2
    have hgvT : itemsGv GD i es := itemsGvTail GD i _ _ hgv3
    have hgvv1 : graphValue GD (i, k) = some (wlRvals l1) := itemsGvHead GD i _ _ _ hgv1 hsome1
    have har1' := admRunAstepGv GD i hpin true _ _ _ _ _ k har1
    have har2' := admRunAstepGv GD i hpin false _ _ _ _ _ k har2
    have hs1 : astepAnyNfGv GD i ⟨pa, k⟩ ⟨pm, k⟩ := by
      rcases (pstepEvSplit _ _ _ _ _).1 hst1 with hs | hw
      · have hrb := readBlockGv GD i _ _ _ _ _ k lb hs hsome1 hlb hrd1 hgvv1
        rw [hadv, Nat.add_zero] at hrb
        exact hrb
      · obtain ⟨rfl, _⟩ := pstepWireInv _ _ _ _ _ hw
        simp [wlRd] at hsome1
    have hs2 : astepAnyNfGv GD i ⟨pm2, k⟩ ⟨p', k + 1⟩ := by
      rcases (pstepEvSplit _ _ _ _ _).1 hst2 with hs | hw
      · have hdat : wlWdata l2 = lblData lb := by
          obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _, _, rfl⟩ := hre
          rfl
        have hnf : WeakAxRealize.fetchPin GD.gdG.gxImg l2 := by
          obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ := hre
          trivial
        exact .ANFGVProg _ _ ⟨_, .AStepWrite _ k _ _ lb _ _ hlb hsome2 hwr2 hdat hs, hnf⟩
      · obtain ⟨rfl, _⟩ := pstepWireInv _ _ _ _ _ hw
        simp [wlWr] at hsome2
    have e1 : (eadm ls1 ++ (l1, some k) :: (eadm ls2 ++ (l2, some k) :: es)).length =
        ls1.length + (0 + 1 + (ls2.length + (es.length + 1))) := by
      simp [eadm]; omega
    have e2 : k + (lb :: rrow').length = k + 1 + rrow'.length := by
      simp only [List.length_cons]; omega
    rw [e1, e2]
    exact nsteps_trans har1' (nsteps_trans (nsteps_l hs1 (nsteps_O _))
      (nsteps_trans har2' (nsteps_l hs2 (ih hrow' hgvT))))

/-! ## 2.1 The `hartConf` specialization -/

theorem hemitRunAtGraphValues
    (hpin : ∀ p d l p' d', pstepProg p d l p' d' → lbAdmin true l →
      WeakAxRealize.fetchPin GD.gdG.gxImg l)
    (p0 : Pexv6) (dv : Nat → Efab) (em : Hemission) :
    hartConf i (AxOpsem.grow GD i) p0 dv em →
    emReadsAtGraphValues GD i em →
    nsteps (astepAnyNfGv GD i) em.emItems.length ⟨p0, 0⟩
      ⟨em.emFin, (AxOpsem.grow GD i).length⟩ := by
  intro h hgv
  have := hemitRunAtGraphValuesAux GD i hpin dv 0 wsInit (AxOpsem.grow GD i) p0 _ _ h
    (fun j => by rw [Nat.zero_add]) hgv
  rwa [Nat.zero_add] at this

theorem hemitRunAtGraphValuesRtc
    (hpin : ∀ p d l p' d', pstepProg p d l p' d' → lbAdmin true l →
      WeakAxRealize.fetchPin GD.gdG.gxImg l)
    (p0 : Pexv6) (dv : Nat → Efab) (em : Hemission) :
    hartConf i (AxOpsem.grow GD i) p0 dv em →
    emReadsAtGraphValues GD i em →
    rtc (astepAnyNfGv GD i) ⟨p0, 0⟩ ⟨em.emFin, (AxOpsem.grow GD i).length⟩ :=
  fun h hgv => rtc_nsteps_2 (hemitRunAtGraphValues GD i hpin p0 dv em h hgv)

end RunGV2

end Weak
