/-
Weak: **B1b-2's RESIDUE — the fabric bundle's hull restriction and the `cycle_kill` mirror**.

Rocq: `iris/WeakRvwmoFabInd.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4d.4 (B1b).  `WeakRvwmoFab` lands the
fabric-order bundle (`gfexecConf`) and its consistency restriction (`gfHullConsistent`); its §8
closing comment enumerates FIVE obligations (O1–O5) for the CONFORMANCE restriction and a
`cycle_kill` mirror.  This file discharges them:

  §1  O1/O2 — `hemitfPrefix` / `hemitfRen` (and their `hartConff` corollaries), the two-endpoint
      emission's stability lemmas; tag monotonicity (`hemitfTagLt`).
  §2  O3 — `emDev` under an item prefix (`emDevAppNoTag`), giving `isDevBlock` agreement below
      the cut (`hartConffPrefix`).
  §3  O4/O5 — `gfexecConfHull` (and `gfexecConfRen`, which the normalization needs).
  §4  THE MIRROR — `properCutF`, `gfHullEventsLt`, `cycleKillF`, `fconfRealize` /
      `hullRealizableOfAcyclicF`, `t2linOfCycleKillF`, `t2linSupplyF`.  The one place the fabric
      order is not free: `fconfSupply`'s last hypothesis (the trace visits the dev blocks in
      `gfDev`'s order) is HANDED BACK as the guard `trDevOrdered`.
  §5  THE DEV-ORDER FINDING: the T2-1c trace (`linCand`) does NOT respect the fabric order —
      two writes come out in gmo order (`glinGmoWrites`), but on the LB witness a cross-hart gmo
      pair comes out reversed (`lbfConsistent`, `lbfNotDevOrdered`, `linCrossHartGmoReversed`).
  §6  NON-VACUITY: `cycleKillOfF` — at an empty fabric order the fabric kill obligation SUBSUMES
      the quiescent one (`cycleKill`).

## Deviations from Rocq

1. NAMES: camelCase (map below); `l !! n` ↦ `l[n]?`; `default [] o` ↦ `o.getD []`;
   `seq 0 N` ↦ `List.range' 0 N`; `es_ag`/`cd_tr` ↦ `esAg`/`cdTr`; `filter (λ s, es_ag s = i)` ↦
   `filter (fun s => decide (s.esAg = i))`; `agent → pexv6` ↦ `Nat → Pexv6`; `RacyF` ↦ `racyF`,
   `RacyD` ↦ `racyD`; `tc_mono` ↦ `tcMono`.  `dev_state` ↦ `Efab` (the event instance's fabric,
   `WeakEvPf` deviation 9 / owner decision Q1).
2. O2 / D1 — THE FETCH-INERTNESS OBLIGATION (`WeakRvwmoFab` deviation 2): `fconfSupply` takes
   `candFetchInertF boot N c`.  So the supply conjunct of `fconfRealize`,
   `hullRealizableOfAcyclicF` and `t2linSupplyF` is Rocq's
   `trDevOrdered GF' c → ∃ pst, …` with the extra premise:
   `trDevOrdered GF' c → candFetchInertF boot N c → ∃ pst, …`.  Every other conjunct is Rocq's.
   The consumer discharges it at the candidate it receives.
3. PROOFS: per-constructor induction and `omega`; Rocq's `vm_compute` / `reflexivity` on `lbg`'s
   linearization ↦ the Lean-only `WeakRvwmoFabInd.lbgGlinEids` (`decide +kernel`) plus `rfl`;
   Lean-only `WeakRvwmoFabInd.eadmTag` (administrative items carry no tag).  Rocq's
   `Print Assumptions` audit is not reproduced (the lint bans axioms).

**Rocq → Lean name map.**  `hemitf_ren` `hemitfRen`, `hart_conff_ren` `hartConffRen`,
`hemitf_tag_lt` `hemitfTagLt`, `hemitf_tag_ge` `hemitfTagGe`, `hemitf_prefix` `hemitfPrefix`,
`em_dev_no_tag` `emDevNoTag`, `em_dev_app_no_tag` `emDevAppNoTag`, `hart_conff_prefix`
`hartConffPrefix`, `is_dev_block_ren` `isDevBlockRen`, `hart_conff_row_deps_lt`
`hartConffRowDepsLt`, `gfexec_conf_ren` `gfexecConfRen`, `gfexec_conf_hull` `gfexecConfHull`,
`proper_cut_F` `properCutF`, `gf_hull_events_lt` `gfHullEventsLt`, `cycle_kill_F` `cycleKillF`,
`tr_dev_ordered` `trDevOrdered`, `fconf_realize` `fconfRealize`, `hull_realizable_of_acyclic_F`
`hullRealizableOfAcyclicF`, `t2lin_aux_F` `t2linAuxF`, `t2lin_of_cycle_kill_F`
`t2linOfCycleKillF`, `t2lin_supply_F` `t2linSupplyF`, `glin_gmo_writes` `glinGmoWrites`, `lbf`
`lbf`, `lbg_gmo_lt_cross` `lbgGmoLtCross`, `lbf_consistent` `lbfConsistent`,
`lbf_not_dev_ordered` `lbfNotDevOrdered`, `lin_cross_hart_gmo_reversed`
`linCrossHartGmoReversed`, `cycle_kill_of_F` `cycleKillOfF`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.
-/
import Weak.WeakRvwmoFab
import Weak.WeakRvwmoLinInd
import Weak.WeakRvwmoLin
import Weak.WeakRvwmoHull
import Weak.WeakRvwmoTopo

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## 1. O1/O2: the two-endpoint emission's stability lemmas -/

/-! ### 1.1 O2: the normalization orbit -/

theorem hemitfRen (π : Nat → Nat) (dvi dvo : Nat → Efab) (k : Nat) (ws : Wstate)
    (row : List Lbl) (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo k ws row p es pfin →
    ∀ ws', ws'.wRelp = ws.wRelp →
    hemitf dvi dvo k ws' (row.map (lblRen π)) p (es.map (eitemRen π)) pfin := by
  intro h
  induction h with
  | HFnil k ws p => intro _ _; exact .HFnil _ _ _
  | HFone k ws lb row p ls pa da l p' es pfin har hre hst _ ih =>
    intro ws' hrelp
    rw [eitemRenBlock, List.map_cons]
    have hlat := hre.2.1
    have hrf := hre.2.2.1
    exact .HFone _ _ _ _ _ _ _ _ _ _ _ _ (admRunRen π true _ _ _ _ _ har)
      (hlblRealizesRen π pa ws ws' lb l hrelp hre) (pstepEvWren π _ _ _ _ _ hlat hrf hst)
      (ih _ (lblPostRelpRen π k ws ws' lb hrelp))
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 _
      ih =>
    intro ws' hrelp
    rw [eitemRenBlock, eitemRenBlock, List.map_cons]
    have hre' := hlblRealizesPairRen π pa pm2 ws ws' lb l1 l2 hrelp hre
    obtain ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, _, _, _⟩ := hre
    exact .HFpair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (admRunRen π true _ _ _ _ _ har1) hre'
      (pstepEvWren π _ _ _ _ _ trivial trivial hst1) (admRunRen π false _ _ _ _ _ har2)
      (pstepEvWren π _ _ _ _ _ trivial trivial hst2)
      (ih _ (lblPostRelpRen π k ws ws' _ hrelp))

theorem hartConffRen (π : Nat → Nat) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dvi dvo : Nat → Efab) (em : Hemission) :
    hartConff i row p0 dvi dvo em → hartConff i (row.map (lblRen π)) p0 dvi dvo (emRen π em) :=
  fun hem => hemitfRen π dvi dvo 0 wsInit row p0 _ _ hem wsInit rfl

/-! ### 1.2 Tag monotonicity -/

/-- (Lean-only) Administrative items carry no tag. -/
theorem WeakRvwmoFabInd.eadmTag (ls : List Wlabel) (it : Eitem) : it ∈ eadm ls → it.2 = none := by
  intro h
  unfold eadm at h
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 h
  rfl

/-- Every tag in the item list of `hemitf … k …` is a row position SHIFTED BY `k`. -/
theorem hemitfTagLt (dvi dvo : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) (it : Eitem) (j : Nat) :
    hemitf dvi dvo k ws row p es pfin → it ∈ es → it.2 = some j →
    k ≤ j ∧ j - k < row.length := by
  intro h
  induction h with
  | HFnil k ws p => intro hit; simp at hit
  | HFone k ws lb row p ls pa da l p' es pfin _ _ _ _ ih =>
    intro hit hj
    rcases List.mem_append.1 hit with h | h
    · rw [WeakRvwmoFabInd.eadmTag ls it h] at hj; cases hj
    · rcases List.mem_cons.1 h with rfl | h
      · simp only [Option.some.injEq] at hj
        subst hj
        simp only [List.length_cons]
        omega
      · obtain ⟨h1, h2⟩ := ih h hj
        simp only [List.length_cons]
        omega
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin _ _ _ _ _ _ ih =>
    intro hit hj
    rcases List.mem_append.1 hit with h | h
    · rw [WeakRvwmoFabInd.eadmTag ls1 it h] at hj; cases hj
    · rcases List.mem_cons.1 h with rfl | h
      · simp only [Option.some.injEq] at hj
        subst hj
        simp only [List.length_cons]
        omega
      · rcases List.mem_append.1 h with h | h
        · rw [WeakRvwmoFabInd.eadmTag ls2 it h] at hj; cases hj
        · rcases List.mem_cons.1 h with rfl | h
          · simp only [Option.some.injEq] at hj
            subst hj
            simp only [List.length_cons]
            omega
          · obtain ⟨h1, h2⟩ := ih h hj
            simp only [List.length_cons]
            omega

theorem hemitfTagGe (dvi dvo : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) (it : Eitem) (j : Nat) :
    hemitf dvi dvo k ws row p es pfin → it ∈ es → it.2 = some j → k ≤ j :=
  fun hem hit hj => (hemitfTagLt dvi dvo k ws row p es pfin it j hem hit hj).1

/-! ### 1.3 O1: prefix restriction, with the dropped tail's tags bounded -/

theorem hemitfPrefix (dvi dvo : Nat → Efab) (k : Nat) (ws : Wstate) (row : List Lbl)
    (p : Pexv6) (es : List Eitem) (pfin : Pexv6) :
    hemitf dvi dvo k ws row p es pfin →
    ∀ n, ∃ es1 es2 pfin', es = es1 ++ es2 ∧
      hemitf dvi dvo k ws (row.take n) p es1 pfin' ∧
      (∀ it j, it ∈ es2 → it.2 = some j → k + n ≤ j) := by
  intro h
  induction h with
  | HFnil k ws p =>
    intro n
    exact ⟨[], [], p, rfl, by rw [List.take_nil]; exact .HFnil _ _ _,
      fun it j hit => by simp at hit⟩
  | HFone k ws lb row p ls pa da l p' es pfin har hre hst hem ih =>
    intro n
    cases n with
    | zero =>
      refine ⟨[], eadm ls ++ (l, some k) :: es, p, rfl, .HFnil _ _ _, fun it j hit hj => ?_⟩
      have := hemitfTagGe dvi dvo k ws (lb :: row) p _ pfin it j
        (.HFone _ _ _ _ _ _ _ _ _ _ _ _ har hre hst hem) hit hj
      omega
    | succ n =>
      obtain ⟨es1, es2, pfin', rfl, hem', hbnd⟩ := ih n
      refine ⟨eadm ls ++ (l, some k) :: es1, es2, pfin', by simp, ?_, fun it j hit hj => ?_⟩
      · rw [List.take_succ_cons]
        exact .HFone _ _ _ _ _ _ _ _ _ _ _ _ har hre hst hem'
      · have := hbnd it j hit hj
        omega
  | HFpair k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2 hst2 hem
      ih =>
    intro n
    cases n with
    | zero =>
      refine ⟨[], eadm ls1 ++ (l1, some k) :: (eadm ls2 ++ (l2, some k) :: es), p, rfl,
        .HFnil _ _ _, fun it j hit hj => ?_⟩
      have := hemitfTagGe dvi dvo k ws (lb :: row) p _ pfin it j
        (.HFpair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ har1 hre hst1 har2 hst2 hem) hit hj
      omega
    | succ n =>
      obtain ⟨es1, es2, pfin', rfl, hem', hbnd⟩ := ih n
      refine ⟨eadm ls1 ++ (l1, some k) :: (eadm ls2 ++ (l2, some k) :: es1), es2, pfin',
        by simp, ?_, fun it j hit hj => ?_⟩
      · rw [List.take_succ_cons]
        exact .HFpair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ har1 hre hst1 har2 hst2 hem'
      · have := hbnd it j hit hj
        omega

/-! ## 2. O3: `emDev` under an item prefix -/

theorem emDevNoTag (k : Nat) (es : List Eitem) :
    (∀ it, it ∈ es → it.2 ≠ some k) → ∀ pend, emDev pend k es = false := by
  induction es with
  | nil => intro _ _; rfl
  | cons it es ih =>
    intro hnt pend
    have hrest : ∀ it', it' ∈ es → it'.2 ≠ some k :=
      fun it' h => hnt it' (List.mem_cons_of_mem _ h)
    obtain ⟨l, o⟩ := it
    cases o with
    | some j =>
      show (if j = k then _ else _) = false
      split
      · next hc => exact absurd (congrArg some hc) (hnt (l, some j) (List.mem_cons_self ..))
      · exact ih hrest false
    | none =>
      show emDev (pend || lbIsdev l) k es = false
      exact ih hrest _

theorem emDevAppNoTag (k : Nat) (es1 es2 : List Eitem) :
    (∀ it, it ∈ es2 → it.2 ≠ some k) →
    ∀ pend, emDev pend k (es1 ++ es2) = emDev pend k es1 := by
  intro hnt
  induction es1 with
  | nil => intro pend; exact emDevNoTag k es2 hnt pend
  | cons it es1 ih =>
    intro pend
    obtain ⟨l, o⟩ := it
    cases o with
    | some j =>
      show (if j = k then ((pend || lbIsdev l) || emDev false k (es1 ++ es2))
          else emDev false k (es1 ++ es2)) =
        (if j = k then ((pend || lbIsdev l) || emDev false k es1) else emDev false k es1)
      rw [ih]
    | none =>
      show emDev (pend || lbIsdev l) k (es1 ++ es2) = emDev (pend || lbIsdev l) k es1
      exact ih _

/-- THE PREFIX RESTRICTION, with the dev blocks below the cut AGREEING. -/
theorem hartConffPrefix (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab)
    (em : Hemission) (n : Nat) :
    hartConff i row p0 dvi dvo em →
    ∃ em', hartConff i (row.take n) p0 dvi dvo em' ∧
      em'.emItems <+: em.emItems ∧
      (∀ k, k < n → (isDevBlock em' k ↔ isDevBlock em k)) := by
  intro hem
  obtain ⟨es1, es2, pfin', heq, hem', hbnd⟩ := hemitfPrefix _ _ _ _ _ _ _ _ hem n
  refine ⟨⟨es1, pfin'⟩, hem', ⟨es2, heq.symm⟩, fun k hk => ?_⟩
  show emDev false k es1 = true ↔ emDev false k em.emItems = true
  rw [heq, emDevAppNoTag k es1 es2 (fun it hit hj => by have := hbnd it k hit hj; omega)]

/-- … and the renaming leaves them alone. -/
theorem isDevBlockRen (π : Nat → Nat) (em : Hemission) (k : Nat) :
    isDevBlock (emRen π em) k ↔ isDevBlock em k := by
  show emDev false k (em.emItems.map (eitemRen π)) = true ↔ emDev false k em.emItems = true
  rw [emDevRen]

/-- A `rowDeps` edge of an emission of `row` names row positions of `row`. -/
theorem hartConffRowDepsLt (i : Nat) (row : List Lbl) (p0 : Pexv6) (dvi dvo : Nat → Efab)
    (em : Hemission) (jk : Nat × Nat) :
    hartConff i row p0 dvi dvo em → jk ∈ rowDeps em.emItems →
    jk.1 < row.length ∧ jk.2 < row.length := by
  intro hem hjk
  have hem' : hemitf dvi dvo 0 wsInit row p0 em.emItems em.emFin := hem
  obtain ⟨it, hit, hpos, _⟩ := rowDepsSrc _ _ hjk
  obtain ⟨it', hit', hpos', _⟩ := rowDepsTgt _ _ hjk
  have h1 := (hemitfTagLt _ _ _ _ _ _ _ _ it jk.1 hem' hit hpos).2
  have h2 := (hemitfTagLt _ _ _ _ _ _ _ _ it' jk.2 hem' hit' hpos').2
  omega

/-! ## 3. O4/O5: the conformance restrictions -/

/-! ### 3.1 The normalization orbit -/

theorem gfexecConfRen (π : Nat → Nat) (boot : Nat → Pexv6) (d0 : Efab)
    (fab : Nat → Efab) (GF GF' : Gfexec) :
    rowsRel π GF.gfGd.gdG GF'.gfGd.gdG →
    GF'.gfGd.gdDeps = GF.gfGd.gdDeps →
    GF'.gfDev = GF.gfDev →
    gfexecConf boot d0 fab GF → gfexecConf boot d0 fab GF' := by
  rintro hrr hdeps hdev ⟨h0, hnd, hbnd, hc⟩
  refine ⟨h0, by rw [hdev]; exact hnd, ?_, ?_⟩
  · intro n i k hn
    rw [hdev] at hn
    obtain ⟨row, hrow, hlt⟩ := hbnd n i k hn
    exact ⟨row.map (lblRen π), rowsRelRow π _ _ i row hrr hrow, by rw [List.length_map]; exact hlt⟩
  · intro i row' hrow'
    obtain ⟨_, hprog, _⟩ := hrr
    rw [hprog, List.getElem?_map] at hrow'
    cases hrow0 : GF.gfGd.gdG.gxProg[i]? with
    | none => rw [hrow0] at hrow'; simp at hrow'
    | some row =>
      rw [hrow0] at hrow'
      simp only [Option.map_some, Option.some.injEq] at hrow'
      subst hrow'
      obtain ⟨em, dvi, dvo, hem, hiff, hpin, hdep⟩ := hc i row hrow0
      refine ⟨emRen π em, dvi, dvo, hartConffRen π i row (boot i) dvi dvo em hem, ?_, ?_, ?_⟩
      · intro k hk
        rw [List.length_map] at hk
        rw [hdev, isDevBlockRen]
        exact hiff k hk
      · intro k n hn
        rw [hdev] at hn
        exact hpin k n hn
      · intro jk hjk
        rw [hdeps]
        apply hdep
        simp only [emRen] at hjk
        rw [rowDepsRen] at hjk
        exact hjk

/-! ### 3.2 THE HULL: O1–O5 assembled -/

theorem gfexecConfHull (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) (cs : List Nat) :
    gfexecConsistent GF →
    dclosed cs GF.gfDev →
    hullOk GF.gfGd.gdG cs →
    gfexecConf boot d0 fab GF →
    gfexecConf boot d0 fab (gfHull GF cs) := by
  rintro _ hdc _ ⟨h0, hnd, hbnd, hc⟩
  refine ⟨h0, List.Nodup.sublist (List.filter_sublist) hnd, ?_, ?_⟩
  · intro n i k hn
    have hn' := gfHullDevLookup GF cs n (i, k) hdc hn
    have hcut := gfHullDevCut GF cs n (i, k) hn
    obtain ⟨c, hcs, hkc⟩ := gcutElim cs (i, k) hcut
    change cs[i]? = some c at hcs
    change k < c at hkc
    obtain ⟨row, hrow, hlt⟩ := hbnd n i k hn'
    refine ⟨(row.take c).map (lblRen (hren GF.gfGd.gdG cs)), ?_, ?_⟩
    · show (gxHull GF.gfGd.gdG cs).gxProg[i]? = _
      rw [gxhProgLookup, hcs]
      simp [hrow]
    · simp only [List.length_map, List.length_take]
      omega
  · intro i row' hrow'
    change (gxHull GF.gfGd.gdG cs).gxProg[i]? = some row' at hrow'
    rw [gxhProgLookup] at hrow'
    cases hcs : cs[i]? with
    | none => rw [hcs] at hrow'; simp at hrow'
    | some c =>
      rw [hcs] at hrow'
      cases hrow : GF.gfGd.gdG.gxProg[i]? with
      | none => rw [hrow] at hrow'; simp at hrow'
      | some row =>
        rw [hrow] at hrow'
        simp only [Option.bind_some, Option.some.injEq] at hrow'
        subst hrow'
        obtain ⟨em, dvi, dvo, hem, hiff, hpin, hdep⟩ := hc i row hrow
        obtain ⟨em', hem', hpre, hdevb⟩ := hartConffPrefix i row (boot i) dvi dvo em c hem
        refine ⟨emRen (hren GF.gfGd.gdG cs) em', dvi, dvo,
          hartConffRen _ _ _ _ _ _ _ hem', ?_, ?_, ?_⟩
        · intro k hk
          rw [List.length_map, List.length_take] at hk
          have hkc : k < c := by omega
          rw [isDevBlockRen, hdevb k hkc, hiff k (by omega)]
          show (i, k) ∈ GF.gfDev ↔ (i, k) ∈ GF.gfDev.filter (gcut cs)
          rw [List.mem_filter]
          exact ⟨fun h => ⟨h, gcutIntro cs (i, k) c hcs hkc⟩, fun h => h.1⟩
        · intro k n hn
          exact hpin k n (gfHullDevLookup GF cs n (i, k) hdc hn)
        · intro jk hjk
          simp only [emRen] at hjk
          rw [rowDepsRen] at hjk
          obtain ⟨hlt1, hlt2⟩ :=
            hartConffRowDepsLt i (row.take c) (boot i) dvi dvo em' jk hem' hjk
          rw [List.length_take] at hlt1 hlt2
          replace hlt1 : jk.1 < c := by omega
          replace hlt2 : jk.2 < c := by omega
          exact (gdHullDeps GF.gfGd cs _).2 ⟨hdep jk (rowDepsPrefix _ _ _ hpre hjk),
            gcutIntro cs (i, jk.1) c hcs hlt1, gcutIntro cs (i, jk.2) c hcs hlt2⟩

/-! ## 4. The `cycle_kill` mirror -/

def properCutF (GF : Gfexec) (cs : List Nat) : Prop :=
  properCut GF.gfGd.gdG cs ∧ dclosed cs GF.gfDev

theorem gfHullEventsLt (GF : Gfexec) (cs : List Nat) :
    properCutF GF cs →
    (gevs' (gfHull GF cs).gfGd.gdG).length < (gevs' GF.gfGd.gdG).length :=
  fun h => hullEventsLt _ _ h.1

def cycleKillF (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) : Prop :=
  ∀ GF : Gfexec,
    gfexecConsistent GF →
    gfexecConf boot d0 fab GF →
    (∀ cs, properCutF GF cs → ∀ x, ¬ tc (racyF (gfHull GF cs)) x x) →
    ∀ x, tc (racyF GF) x x → False

/-! ### 4.1 The form the kill consumes -/

/-- The guard handed back: the trace visits the dev blocks in `gfDev`'s order. -/
def trDevOrdered (GF : Gfexec) (c : Cand) : Prop :=
  ∀ k s, c.cdTr[k]? = some s →
    (s.esAg, tcnt s.esAg (c.cdTr.take k)) ∈ GF.gfDev →
    GF.gfDev[dcnt GF c.cdTr k]? = some (s.esAg, tcnt s.esAg (c.cdTr.take k))

/-- (Deviation 2: the supply also needs `candFetchInertF`.) -/
theorem fconfRealize (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) (N : Nat) :
    gfexecConsistent GF →
    gfexecConf boot d0 fab GF →
    (∀ x, ¬ tc (racyF GF) x x) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pi : Nat → Nat) (GF' : Gfexec),
      srvwmoConsistent c ∧
      c.cdImg = GF.gfGd.gdG.gxImg ∧
      rowsRel pi GF.gfGd.gdG GF'.gfGd.gdG ∧
      GF'.gfDev = GF.gfDev ∧
      gfexecConf boot d0 fab GF' ∧
      (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (GF'.gfGd.gdG.gxProg[i]?).getD []) ∧
      (trDevOrdered GF' c → candFetchInertF boot N c →
        ∃ pst : Nat → List Pexv6,
          pst 0 = (List.range' 0 N).map boot ∧
          execProgOk' pstepEv pclsEv pst (fun k => fab (dcnt GF' c.cdTr k)) (candExec c)) := by
  intro hc hconf hacy hN
  have hcons : rvwmoMinusDepsConsistent GF.gfGd := hc.1
  have hacyD : ∀ x, ¬ tc (racyD GF.gfGd) x x := fun x hcyc =>
    hacy x (tcMono _ _ x x (fun a b h => Or.inl h) hcyc)
  obtain ⟨GD', pi, hcons', h14, hrr, hdeps, _⟩ :=
    normalizeOfAcyclic GF.gfGd hcons (fun x y => racyDDec _ x y) hacyD
  have hconf' : gfexecConf boot d0 fab ⟨GD', GF.gfDev⟩ :=
    gfexecConfRen pi boot d0 fab GF ⟨GD', GF.gfDev⟩ hrr hdeps rfl hconf
  obtain ⟨c, hsr, himg, hrow, _⟩ := rule14Linearization GD'.gdG hcons'.1 h14
  refine ⟨c, pi, ⟨GD', GF.gfDev⟩, hsr, ?_, hrr, rfl, hconf', hrow, fun hord hfi => ?_⟩
  · rw [himg, rowsRelImg pi _ _ hrr]
  · obtain ⟨pst, hpst0, _, hprg⟩ := fconfSupply c boot d0 fab ⟨GD', GF.gfDev⟩ N hconf' hrow
      (by rw [rowsRelNharts pi _ _ hrr]; exact hN) hord hfi
    exact ⟨pst, hpst0, hprg⟩

/-! ### 4.2 The hull instance -/

theorem hullRealizableOfAcyclicF (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) (cs : List Nat) (N : Nat) :
    gfexecConsistent GF →
    gfexecConf boot d0 fab GF →
    properCutF GF cs →
    (∀ x, ¬ tc (racyF (gfHull GF cs)) x x) →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pi : Nat → Nat) (GF' : Gfexec),
      srvwmoConsistent c ∧
      c.cdImg = GF.gfGd.gdG.gxImg ∧
      GF'.gfDev = (gfHull GF cs).gfDev ∧
      gfexecConf boot d0 fab GF' ∧
      (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (((gxHull GF.gfGd.gdG cs).gxProg[i]?).getD []).map (lblRen pi)) ∧
      (trDevOrdered GF' c → candFetchInertF boot N c →
        ∃ pst : Nat → List Pexv6,
          pst 0 = (List.range' 0 N).map boot ∧
          execProgOk' pstepEv pclsEv pst (fun k => fab (dcnt GF' c.cdTr k)) (candExec c)) := by
  intro hc hconf hpc hacy hN
  have hok : hullOk GF.gfGd.gdG cs := properCutOk _ _ hpc.1
  have hch : gfexecConsistent (gfHull GF cs) := gfHullConsistent GF cs hc hok hpc.2
  have hcnf : gfexecConf boot d0 fab (gfHull GF cs) :=
    gfexecConfHull boot d0 fab GF cs hc hpc.2 hok hconf
  have hNh : (gfHull GF cs).gfGd.gdG.gxProg.length ≤ N := by
    have := gxhNharts GF.gfGd.gdG cs
    change (gxHull GF.gfGd.gdG cs).gxProg.length ≤ N
    omega
  obtain ⟨c, pi, GF', hsr, himg, hrr, hdev, hconf', hrow, hsup⟩ :=
    fconfRealize boot d0 fab (gfHull GF cs) N hch hcnf hacy hNh
  refine ⟨c, pi, GF', hsr, himg.trans (gxhImg _ _), hdev, hconf', fun i => ?_, hsup⟩
  rw [hrow i, hrr.2.1, List.getElem?_map]
  change (Option.map _ ((gxHull GF.gfGd.gdG cs).gxProg[i]?)).getD [] = _
  cases (gxHull GF.gfGd.gdG cs).gxProg[i]? <;> rfl

/-! ### 4.3 The induction -/

theorem t2linAuxF (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) :
    cycleKillF boot d0 fab →
    ∀ (n : Nat) (GF : Gfexec),
      (gevs' GF.gfGd.gdG).length ≤ n →
      gfexecConsistent GF →
      gfexecConf boot d0 fab GF →
      ∀ x, ¬ tc (racyF GF) x x := by
  intro hk n
  induction n with
  | zero =>
    intro GF hlen hcons hconf x hcyc
    refine hk GF hcons hconf ?_ x hcyc
    intro cs hpc y _
    have := gfHullEventsLt GF cs hpc
    omega
  | succ n ih =>
    intro GF hlen hcons hconf x hcyc
    refine hk GF hcons hconf ?_ x hcyc
    intro cs hpc
    have hok := properCutOk _ _ hpc.1
    refine ih (gfHull GF cs) ?_ (gfHullConsistent GF cs hcons hok hpc.2)
      (gfexecConfHull boot d0 fab GF cs hcons hpc.2 hok hconf)
    have := gfHullEventsLt GF cs hpc
    omega

theorem t2linOfCycleKillF (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) :
    cycleKillF boot d0 fab →
    ∀ GF : Gfexec,
      gfexecConsistent GF →
      gfexecConf boot d0 fab GF →
      ∀ x, ¬ tc (racyF GF) x x :=
  fun hk GF => t2linAuxF boot d0 fab hk (gevs' GF.gfGd.gdG).length GF (Nat.le_refl _)

/-! ### 4.4 The corollary: the whole graph is realized (modulo the guard) -/

theorem t2linSupplyF (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab)
    (GF : Gfexec) (N : Nat) :
    cycleKillF boot d0 fab →
    gfexecConsistent GF →
    gfexecConf boot d0 fab GF →
    GF.gfGd.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pi : Nat → Nat) (GF' : Gfexec),
      srvwmoConsistent c ∧
      c.cdImg = GF.gfGd.gdG.gxImg ∧
      GF'.gfDev = GF.gfDev ∧
      gfexecConf boot d0 fab GF' ∧
      (trDevOrdered GF' c → candFetchInertF boot N c →
        ∃ pst : Nat → List Pexv6,
          pst 0 = (List.range' 0 N).map boot ∧
          execProgOk' pstepEv pclsEv pst (fun k => fab (dcnt GF' c.cdTr k)) (candExec c)) := by
  intro hk hcons hconf hN
  obtain ⟨c, pi, GF', hsr, himg, _, hdev, hconf', _, hsup⟩ :=
    fconfRealize boot d0 fab GF N hcons hconf (t2linOfCycleKillF boot d0 fab hk GF hcons hconf) hN
  exact ⟨c, pi, GF', hsr, himg, hdev, hconf', hsup⟩

/-! ## 5. THE DEV-ORDER FINDING -/

/-! ### 5.1 The positive fragment: two WRITES do come out in gmo order -/

theorem glinGmoWrites (G : Gexec) (w1 w2 : Geid) (k1 k2 : Nat) :
    gwf G →
    (glinEids G)[k1]? = some w1 → (glinEids G)[k2]? = some w2 →
    w1 ∈ gwrites G → w2 ∈ gwrites G →
    gmoLt G w1 w2 → k1 < k2 := by
  rintro hwf h1 h2 hw1 hw2 ⟨_, _, hpos⟩
  refine glinRankLt G k1 k2 w1 w2 h1 h2 ?_
  rw [grankWrite G hwf w1 hw1, grankWrite G hwf w2 hw2]
  exact (gwixGposLt G w1 w2 hwf.1 hw1 hw2).2 hpos

/-! ### 5.2 The counterexample, on the landed LB witness -/

def lbf : Gfexec := ⟨lbgd, [(1, 1), (0, 0)]⟩

theorem lbgGmoLtCross : gmoLt lbg (1, 1) (0, 0) := by
  unfold gmoLt
  decide +kernel

/-- The bundle's MODEL clause is satisfied: the fabric order is gmo-ordered. -/
theorem lbfConsistent : gfexecConsistent lbf := by
  refine ⟨lbGraphDepsConsistent, ?_⟩
  rintro a b ⟨n, ha, hb⟩
  rcases n with _ | _ | n
  · have ea : ((1, 1) : Geid) = a := Option.some.inj ha
    have eb : ((0, 0) : Geid) = b := Option.some.inj hb
    subst ea eb
    exact lbgGmoLtCross
  · simp [lbf] at hb
  · simp [lbf] at ha

/-- (Lean-only) `lbg`'s linearization: hart 0 entire, then hart 1. -/
theorem WeakRvwmoFabInd.lbgGlinEids : glinEids lbg = [(0, 0), (0, 1), (1, 0), (1, 1)] := by
  decide +kernel

/-- THE TRACE DOES NOT REALIZE IT. -/
theorem lbfNotDevOrdered : ¬ trDevOrdered lbf (linCand lbg) := by
  intro h
  have hs : (linCand lbg).cdTr[0]? = some (glinStep lbg (0, 0)) := by
    show ((glinEids lbg).map (glinStep lbg))[0]? = _
    rw [WeakRvwmoFabInd.lbgGlinEids]
    rfl
  have hin : ((glinStep lbg (0, 0)).esAg,
      tcnt (glinStep lbg (0, 0)).esAg ((linCand lbg).cdTr.take 0)) ∈ lbf.gfDev := by
    change ((0 : Nat), tcnt 0 []) ∈ lbf.gfDev
    rw [show tcnt 0 [] = 0 from rfl]
    decide
  have heq := h 0 _ hs hin
  change lbf.gfDev[0]? = some ((0 : Nat), tcnt 0 []) at heq
  rw [show tcnt 0 [] = 0 from rfl] at heq
  exact absurd heq (by decide)

/-- … and in the general form: `linCand`'s trace REVERSES a cross-hart gmo pair. -/
theorem linCrossHartGmoReversed :
    ∃ (G : Gexec) (x y : Geid) (kx ky : Nat),
      gmoLt G x y ∧ x.1 ≠ y.1 ∧
      (glinEids G)[kx]? = some x ∧ (glinEids G)[ky]? = some y ∧ ky < kx :=
  ⟨lbg, (1, 1), (0, 0), 3, 0, lbgGmoLtCross, by decide,
    by rw [WeakRvwmoFabInd.lbgGlinEids]; rfl, by rw [WeakRvwmoFabInd.lbgGlinEids]; rfl,
    by decide⟩

/-! ## 6. Non-vacuity: the two skeletons are the same skeleton -/

theorem cycleKillOfF (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) :
    cycleKillF boot d0 (fun _ => d0) → cycleKill boot d0 im nh := by
  intro hkF GD hcons hq hhull x hcyc
  have hc : gfexecConsistent ⟨GD, []⟩ :=
    ⟨hcons, fun a b ⟨n, ha, _⟩ => by simp at ha⟩
  refine hkF ⟨GD, []⟩ hc (gfexecConfOfQconf boot d0 im nh GD hq) ?_ x ?_
  · rintro cs ⟨hpc, _⟩ y hcy
    refine hhull cs hpc y (tcMono _ _ y y ?_ hcy)
    rintro a b (hab | ⟨n, ha, _⟩)
    · exact hab
    · simp [gfHull] at ha
  · exact tcMono _ _ x x (fun a b hab => Or.inl hab) hcyc

end Weak
