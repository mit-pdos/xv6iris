/-
Weak: **T2-LIN's induction skeleton** (route B, stage B2e-3).

Rocq: `iris/WeakRvwmoLinInd.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4d.2 / §4d.4.  T2-LIN — "a conformant,
RVWMO⁻(+deps) consistent graph has an acyclic `racyD`" — is proved by STRONG INDUCTION on the
number of events, with the induction hypothesis applied to CAUSAL HULLS
(`WeakRvwmoHull.gxHull`).  Everything except the cycle kill itself is bookkeeping, landed here:

(1) THE MEASURE.  `gevs'` enumerates a graph's row positions; a hull's rows are prefixes
    (`gxhRow`), so a cut dropping at least one event (`properCut`) strictly decreases
    `(gevs' _).length` (`hullEventsLt`).
(2) THE KILL INTERFACE.  `cycleKill` is the open obligation, stated so that the induction
    hypothesis is HANDED TO IT (every PROPER hull is already `racyD`-acyclic).
    `hullRealizableOfAcyclic` is the form the kill consumes: an acyclic proper hull LINEARIZES
    and its linearization is a real promise-free run, its rows the hull's rows up to the
    normalization's write-index renaming.
(3) `t2linOfCycleKill` runs the induction; `t2linSupply` composes it with `topoSupply`.
(4) NON-VACUITY on both sides: the LB witness `lbgd` carries a `racyD` cycle (`lbgdCycle`), and
    the message-passing probe `mpgd` (a rule-14 violator) is `racyD`-acyclic (`mpgdAcyclic`).

The kill itself is NOT here (`cycleKill` is a definition; nothing assumes it).  A leaf.

## Deviations from Rocq

1. NAMES: camelCase (map below); `seq s N` ↦ `List.range' s N`; `sum_list (f <$> l)` ↦
   `(l.map f).sum`; `l !! i` ↦ `l[i]?`; `default d o` ↦ `o.getD d`; `RacyD` ↦ `racyD`, `Racy` ↦
   `racy`, `Rt` ↦ `rt`, `grf` ↦ `WeakRvwmoAcyc.grf`; `filter (λ s, es_ag s = i)` ↦
   `filter (fun s => decide (s.esAg = i))`.  `lbg_grf_01` / `lbg_grf_10` are duplicated Rocq
   names (also in WeakRvwmoKillArms): declared `WeakRvwmoLinInd.lbgGrf01` / `lbgGrf10`.
   `dev_state` ↦ `Efab` (the event instance's fabric, `WeakEvPf` deviation 9 / owner decision Q1).
2. O2 / STAGE C — THE PINNED LTS (`WeakRvwmoSupply` deviation 2; owner ruling Q-C1).  The
   fetch is an administrative label pinned to the boot image by `gdexecQconf`'s `emFetchImg`
   clause, and `supplyOfQconf` / `topoSupply` supply the trace at the PINNED program LTS
   `pstepPin c.cdImg pstepEv` (a sub-LTS of `pstepEv`, `WeakAxRealize.pstepPinSub`).  So
   `hullRealizableOfAcyclic` and `t2linSupply` are Rocq's statements (same quantifiers, the
   `∃ pst` unconditional) with `exec_prog_ok' pstep_ev …` read as
   `execProgOk' (pstepPin c.cdImg pstepEv) …`.  Stage B's `candFetchInert` conditional is gone.
3. PROOFS: `omega`/`simp` instead of `lia`/`csimpl`; `vm_compute` ↦ `decide`; Rocq's
   `Print Assumptions` audit is not reproduced (the lint bans axioms).

**Rocq → Lean name map.**  `sum_list_seq_le` `sumListSeqLe`, `sum_list_seq_lt` `sumListSeqLt`,
`length_gevs'` `lengthGevs'`, `nrow_lt_nharts` `nrowLtNharts`, `gxh_nrow` `gxhNrow`,
`gxh_nharts_eq` `gxhNhartsEq`, `proper_cut` `properCut`, `proper_cut_ok` `properCutOk`,
`hull_events_lt` `hullEventsLt`, `erg_proper_cut` `ergProperCut`, `erg_hull_events_lt`
`ergHullEventsLt`, `cycle_kill` `cycleKill`, `hull_realizable_of_acyclic`
`hullRealizableOfAcyclic`, `t2lin_aux` `t2linAux`, `t2lin_of_cycle_kill` `t2linOfCycleKill`,
`t2lin_supply` `t2linSupply`, `lbg_gpow_0` `lbgGpow0`, `lbg_gpow_1` `lbgGpow1`, `lbg_grf_01`
`WeakRvwmoLinInd.lbgGrf01`, `lbg_grf_10` `WeakRvwmoLinInd.lbgGrf10`, `lbgd_cycle` `lbgdCycle`,
`mpg_rd` `mpgRd`, `mpg_no_gco` `mpgNoGco`, `mpg_no_gfr` `mpgNoGfr`, `mpg_Racy_Rt` `mpgRacyRt`,
`mpgd_acyclic` `mpgdAcyclic`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.

**W12 (1) (plan §C W12; D25 (a) [OWN.5]) — statement edit (Lean-only).**  `hullRealizableOfAcyclic` takes the core `rvwmoCoreD` (the hull's core by `hullCoreD`); `cycleKill` and the chain are unchanged (their cat twins are `CatLin*`).  RVWMO⁻ callers
are unchanged in text (`WeakRvwmoAcyc.coeCoreOfMinus`).
-/
import Weak.WeakRvwmoSupply
import Weak.WeakRvwmoDec
import Weak.WeakRvwmoProbeK1
import Weak.WeakRvwmoProbeRestr

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## 1. The measure: the number of row positions -/

theorem sumListSeqLe (f g : Nat → Nat) (N : Nat) :
    (∀ i, f i ≤ g i) →
    ∀ s, ((List.range' s N).map f).sum ≤ ((List.range' s N).map g).sum := by
  intro hle
  induction N with
  | zero => intro s; simp
  | succ N ih =>
    intro s
    have h1 := hle s
    have h2 := ih (s + 1)
    simp only [List.range'_succ, List.map_cons, List.sum_cons]
    omega

theorem sumListSeqLt (f g : Nat → Nat) (N : Nat) :
    (∀ i, f i ≤ g i) →
    ∀ s i0, s ≤ i0 → i0 < s + N → f i0 < g i0 →
    ((List.range' s N).map f).sum < ((List.range' s N).map g).sum := by
  intro hle
  induction N with
  | zero => intro s i0 h1 h2 _; omega
  | succ N ih =>
    intro s i0 h1 h2 h3
    simp only [List.range'_succ, List.map_cons, List.sum_cons]
    by_cases he : i0 = s
    · subst he
      have := sumListSeqLe f g N hle (i0 + 1)
      omega
    · have := ih (s + 1) i0 (by omega) (by omega) h3
      have := hle s
      omega

/-- The measure, as a sum of row lengths. -/
theorem lengthGevs' (G : Gexec) :
    (gevs' G).length = ((List.range' 0 G.gxProg.length).map (nrow G)).sum := by
  simp [gevs', List.length_flatten, List.map_map, Function.comp_def]

/-- A nonempty row is a row of an EXISTING hart. -/
theorem nrowLtNharts (G : Gexec) (i : Nat) : 0 < nrow G i → i < G.gxProg.length := by
  unfold nrow
  cases h : G.gxProg[i]? with
  | none => simp
  | some p => intro _; exact lookup_lt_Some h

/-- The hull's row lengths are the `min`s. -/
theorem gxhNrow (G : Gexec) (cs : List Nat) (i : Nat) :
    nrow (gxHull G cs) i = min ((cs[i]?).getD 0) (nrow G i) := by
  unfold nrow
  rw [gxhRow, List.length_map, List.length_take]

theorem gxhNhartsEq (G : Gexec) (cs : List Nat) :
    cs.length = G.gxProg.length → (gxHull G cs).gxProg.length = G.gxProg.length := by
  intro h
  simp only [gxHull, List.length_map, List.length_zipWith]
  omega

/-- THE CUT VOCABULARY: a hull cut that DROPS AT LEAST ONE EVENT. -/
def properCut (G : Gexec) (cs : List Nat) : Prop :=
  hullOk G cs ∧ ∃ i, (cs[i]?).getD 0 < nrow G i

theorem properCutOk (G : Gexec) (cs : List Nat) : properCut G cs → hullOk G cs :=
  fun h => h.1

/-- THE INDUCTION'S DECREASE. -/
theorem hullEventsLt (G : Gexec) (cs : List Nat) :
    properCut G cs → (gevs' (gxHull G cs)).length < (gevs' G).length := by
  rintro ⟨hok, i0, hi0⟩
  have hlen := hullOkLen G cs hok
  rw [lengthGevs' (gxHull G cs), lengthGevs' G, gxhNhartsEq G cs hlen]
  have hle : ∀ i, nrow (gxHull G cs) i ≤ nrow G i := fun i => by rw [gxhNrow]; omega
  refine sumListSeqLt _ _ _ hle 0 i0 (Nat.zero_le _) ?_ ?_
  · have := nrowLtNharts G i0 (by omega)
    omega
  · rw [gxhNrow]
    omega

/-- NON-VACUITY of `properCut`: the frontier probe's cut `ecs = [1, 0]` is rf-closed and drops
hart 1's whole row. -/
theorem ergProperCut : properCut erg ecs := ⟨ergHullOk, 1, by decide⟩

theorem ergHullEventsLt : (gevs' (gxHull erg ecs)).length < (gevs' erg).length :=
  hullEventsLt _ _ ergProperCut

/-! ## 2. The kill interface -/

/-- §4d.2's induction step as an obligation: at a conformant consistent graph EVERY PROPER HULL
OF WHICH IS ALREADY ACYCLIC, there is no `racyD` cycle. -/
def cycleKill (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) : Prop :=
  ∀ GD : Gdexec,
    rvwmoMinusDepsConsistent GD →
    gdexecQconf boot d0 im nh GD →
    (∀ cs, properCut GD.gdG cs → ∀ x, ¬ tc (racyD (gdHull GD cs)) x x) →
    ∀ x, tc (racyD GD) x x → False

/-- THE FORM THE KILL CONSUMES (deviation 2: the supply at the pinned LTS). -/
theorem hullRealizableOfAcyclic (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) (cs : List Nat) (N : Nat) :
    rvwmoCoreD GD →
    gdexecQconf boot d0 im nh GD →
    properCut GD.gdG cs →
    (∀ x, ¬ tc (racyD (gdHull GD cs)) x x) →
    GD.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pst : Nat → List Pexv6) (pi : Nat → Nat),
      srvwmoConsistent c ∧
      c.cdImg = GD.gdG.gxImg ∧
      pst 0 = (List.range' 0 N).map boot ∧
      execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst (fun _ => d0) (candExec c) ∧
      (∀ i, (c.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
        (((gxHull GD.gdG cs).gxProg[i]?).getD []).map (lblRen pi)) := by
  intro hcons hq hpc hacy hN
  have hok : hullOk GD.gdG cs := properCutOk _ _ hpc
  have hch : rvwmoCoreD (gdHull GD cs) := hullCoreD GD cs hcons hok
  have hqh : gdexecQconf boot d0 im nh (gdHull GD cs) := gdexecQconfHull boot d0 im nh GD cs hq
  obtain ⟨GD', pi, hcons', h14, hrr, hdeps, _⟩ :=
    normalizeOfAcyclic (gdHull GD cs) hch (fun x y => racyDDec _ x y) hacy
  have hq' : gdexecQconf boot d0 im nh GD' := gdexecQconfRen pi boot d0 im nh _ GD' hrr hdeps hqh
  obtain ⟨c, hsr, himg, hrow, _⟩ := rule14Linearization GD'.gdG hcons'.1 h14
  -- the rows of `GD'` are the hull's rows, renamed
  have hprog : ∀ i : Nat, (GD'.gdG.gxProg[i]?).getD [] =
      (((gxHull GD.gdG cs).gxProg[i]?).getD []).map (lblRen pi) := by
    intro i
    rw [hrr.2.1, List.getElem?_map]
    change (Option.map _ ((gxHull GD.gdG cs).gxProg[i]?)).getD [] = _
    cases (gxHull GD.gdG cs).gxProg[i]? <;> rfl
  have hci : c.cdImg = im := himg.trans (gdexecQconfImg _ _ _ _ _ hq')
  have h1 := rowsRelNharts pi _ _ hrr
  have h2 : (gdHull GD cs).gdG.gxProg.length ≤ GD.gdG.gxProg.length := gxhNharts GD.gdG cs
  obtain ⟨pst, hpst0, hprg⟩ :=
    supplyOfQconf c boot d0 (fun i => (GD'.gdG.gxProg[i]?).getD []) N hrow
      (fun i hi => progRowNil _ _ (by omega))
      (fun i _ => by rw [hci]; exact qconfRows boot d0 im nh GD' i hq')
  refine ⟨c, pst, pi, hsr, ?_, hpst0, hprg, fun i => by rw [hrow i, hprog i]⟩
  rw [himg, rowsRelImg pi _ _ hrr]
  rfl

/-! ## 3. The theorem: T2-LIN, by strong induction on the event count -/

theorem t2linAux (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) :
    cycleKill boot d0 im nh →
    ∀ (n : Nat) (GD : Gdexec),
      (gevs' GD.gdG).length ≤ n →
      rvwmoMinusDepsConsistent GD →
      gdexecQconf boot d0 im nh GD →
      ∀ x, ¬ tc (racyD GD) x x := by
  intro hk n
  induction n with
  | zero =>
    -- no events at all: no cut is proper, so the hypothesis is vacuous
    intro GD hlen hcons hq x hcyc
    refine hk GD hcons hq ?_ x hcyc
    intro cs hpc y _
    have := hullEventsLt GD.gdG cs hpc
    omega
  | succ n ih =>
    intro GD hlen hcons hq x hcyc
    refine hk GD hcons hq ?_ x hcyc
    intro cs hpc
    refine ih (gdHull GD cs) ?_ (hullDepsConsistent GD cs hcons hpc.1)
      (gdexecQconfHull boot d0 im nh GD cs hq)
    have := hullEventsLt GD.gdG cs hpc
    change (gevs' (gxHull GD.gdG cs)).length ≤ n
    omega

theorem t2linOfCycleKill (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) :
    cycleKill boot d0 im nh →
    ∀ GD : Gdexec,
      rvwmoMinusDepsConsistent GD →
      gdexecQconf boot d0 im nh GD →
      ∀ x, ¬ tc (racyD GD) x x :=
  fun hk GD => t2linAux boot d0 im nh hk (gevs' GD.gdG).length GD (Nat.le_refl _)

/-- THE COROLLARY: the whole graph is realized (deviation 2: at the pinned LTS). -/
theorem t2linSupply (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GD : Gdexec) (N : Nat) :
    cycleKill boot d0 im nh →
    rvwmoMinusDepsConsistent GD →
    gdexecQconf boot d0 im nh GD →
    GD.gdG.gxProg.length ≤ N →
    ∃ (c : Cand) (pst : Nat → List Pexv6),
      srvwmoConsistent c ∧
      c.cdImg = GD.gdG.gxImg ∧
      pst 0 = (List.range' 0 N).map boot ∧
      execProgOk' (pstepPin c.cdImg pstepEv) pclsEv pst (fun _ => d0) (candExec c) := by
  intro hk hcons hq hN
  obtain ⟨c, hsr, himg, pst, hpst0, hprg⟩ := topoSupply boot d0 GD N hcons
    (fun x y => racyDDec GD x y) (t2linOfCycleKill boot d0 im nh hk GD hcons hq) im nh hq hN
  exact ⟨c, pst, hsr, himg, hpst0, hprg⟩

/-! ## 4. Non-vacuity (i): `cycleKill` is a real obligation -/

theorem lbgGpow0 : gpow lbg (0, 0) (0, 1) :=
  ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩

theorem lbgGpow1 : gpow lbg (1, 0) (1, 1) :=
  ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩

/-- hart 1's load reads hart 0's store (write index 1). -/
theorem WeakRvwmoLinInd.lbgGrf01 : WeakRvwmoAcyc.grf lbg (0, 1) (1, 0) :=
  ⟨8, 1, b1, ⟨Lbl.LLoad false 8 [1] [b1], 8, [1], [b1], 0, rfl, rfl, rfl, rfl,
    by simp [accAddr]⟩, by decide⟩

/-- hart 0's load reads hart 1's store (write index 2). -/
theorem WeakRvwmoLinInd.lbgGrf10 : WeakRvwmoAcyc.grf lbg (1, 1) (0, 0) :=
  ⟨0, 2, b1, ⟨Lbl.LLoad false 0 [2] [b1], 0, [2], [b1], 0, rfl, rfl, rfl, rfl,
    by simp [accAddr]⟩, by decide⟩

theorem lbgdCycle : ∃ x, tc (racyD lbgd) x x :=
  ⟨(0, 0),
    tc_l (Or.inl (Or.inl lbgGpow0))
      (tc_l (Or.inl (Or.inr (Or.inl WeakRvwmoLinInd.lbgGrf01)))
        (tc_l (Or.inl (Or.inl lbgGpow1))
          (tc_once (Or.inl (Or.inr (Or.inl WeakRvwmoLinInd.lbgGrf10))))))⟩

/-! ## 5. Non-vacuity (ii): the hull hypothesis is not absurd

`mpg`'s `racy` has no `gco` and no `gfr` edge, so `racy mpg ⊆ rt mpg`, which transports along
the normalization orbit to the rule-14 graph `mpg'` (`rtAcyclicOrbit`). -/

theorem mpgRd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte mpg e a t v → e = (0, 0) ∧ a = 0 ∧ t = 2 := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases mpgLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [lbRd] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  rcases j with _ | j <;> simp at ht
  subst ht
  simp [accAddr] at ha
  exact ⟨rfl, by omega, rfl⟩

theorem mpgNoGco (w w' : Geid) : ¬ gco mpg w w' := by
  rintro ⟨a, v, v', h1, h2, hlt⟩
  rcases mpgWr _ _ _ h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases mpgWr _ _ _ h2 with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> first | omega | exact Nat.lt_irrefl _ hlt

theorem mpgNoGfr (r w' : Geid) : ¬ gfr mpg r w' := by
  rintro ⟨hne, a, t, v, v', hrd, hwb, hlt⟩
  obtain ⟨rfl, rfl, rfl⟩ := mpgRd r a t v hrd
  rcases mpgWr _ _ _ hwb with ⟨rfl, hc⟩ | ⟨rfl, _⟩
  · omega
  · have hw : gwix mpg (1, 0) = 2 := by decide
    rw [hw] at hlt
    omega

theorem mpgRacyRt (x y : Geid) : racy mpg x y → rt mpg x y := by
  rintro (h | h | h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h (mpgNoGco x y)
  · exact absurd h (mpgNoGfr x y)
  · exact Or.inr (Or.inr h)

theorem mpgdAcyclic (x : Geid) : ¬ tc (racyD mpgd) x x := by
  intro hcyc
  refine rtAcyclicOrbit (tswap 1) mpg mpg' x mpg'Consistent mpg'Rule14 mpgRowsRel mpgWperm ?_
  refine tcMono _ _ x x ?_ hcyc
  rintro a b (h | h)
  · exact mpgRacyRt a b h
  · simp [mpgd] at h

end Weak
