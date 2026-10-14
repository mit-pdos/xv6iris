/-
Weak: **W10-2 [OWN.94] (N2′), increment 1 — the one-step extension of the Zifencei threaded state**
(the W10 sizing `~/dev/weak-orch/parked/PROGRESS-W10size.md` §(4) row W10-2, as adjusted by N2′
`parked/PROGRESS-W10N2.md`; progress `PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

The walk (`GraphFetchWalkZ`, discharging `CatLin.tailPolicyCZ`) certifies a segment by APPENDING
its steps one at a time to the threaded state `cstOkZ` (`GraphFetchRun` §3).  The pinned chain's
one-step lemmas are `snocConsistent` (axiomatic half, reused verbatim) and `execProgOk'Snoc` /
`execProgOk'SnocPair` (`WeakRvwmoCert` §2, at the pinned `execProgOk'`).  Their Z twin must extend
M2's conjunct `execProgOk'STC pstepEv pclsEv fokTriv cohSrc (fcutEM2 cohSrc (candExec c) itvOf
fiOf)`, i.e. also clause (i) `lbFused`, the label-carrying stars `admRunG`, the per-step
single-copy atomicity `scaOk`, the shadow clause `execScaT cohSrc`, the disk clause `execDiskLat`,
and THE PER-INDEX FETCH CUT `fcutEM2` — whose instruction-view functions `itvOf`/`fiOf` are
EXISTENTIAL in `cstOkZ`:

  §1  `CertZ.cstOkZW` — `cstOkZ` with `itvOf`/`fiOf` EXPOSED (`CertZ.cstOkZOfW`,
      `CertZ.cstOkZWOf`): the walk must know the instruction view to discharge a fetch's cut;
  §2  the extension of `itvOf`/`fiOf` past the end (`CertZ.itvSnoc`/`CertZ.fiSnoc`: frozen up to
      the old end, M2's recurrence at the new index — the recurrences are DEFINITIONS, only a
      fetch's cut is an obligation) and the stability of `fcutEM2` under appending
      (`CertZ.fcutEM2Snoc`: it reads `E.exTr[k]?` and `E.exTr.take k` only);
  §3  **`CertZ.cstOkZWSnoc`** — THE ONE-STEP EXTENSION: a threaded state, one shaped block for
      hart `i` (its leading star `admRunG … true`, then either a fused realizing step or the
      exclusive pair) whose label is admissible at the candidate's last state (`mstepOk`), whose
      load (if any) is `scaOkT` at the trace shadow and `diskLatOk`, and whose leading star's
      fetches satisfy the cut at `itvOf (cdEnd c) i`, extends to the appended state;
      `CertZ.cstOkZSnoc` (its `cstOkZ` form, the fetch obligation for EVERY admissible
      `itvOf`) is NOT stated: the cut depends on the witness, so the walk carries `cstOkZW`.

Spec: proof organisation — the shaped conformance predicate and M2's clause are the merged trusted
text; nothing is assumed (FAITHFUL).  Lean-only helpers file-qualified (`CertZ.*`).
-/
import Weak.GraphFetchRun

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The threaded state with its instruction views exposed -/

/-- `cstOkZ` at GIVEN `itvOf`/`fiOf`. -/
def CertZ.cstOkZW (d0 : Efab) (St : CycState) (itvOf : Nat → Nat → Nat)
    (fiOf : Nat → Nat → Bool) : Prop :=
  srvwmoConsistent St.cstC ∧
  (∀ i, itvOf 0 i = 0) ∧ (∀ i, fiOf 0 i = false) ∧
  execProgOk'STC pstepEv pclsEv PfRunUnpinned.fokTriv cohSrc
    (PfRunUnpinned.fcutEM2 cohSrc (candExec St.cstC) itvOf fiOf) St.cstPst St.cstDv
    (candExec St.cstC) ∧
  St.cstDv 0 = d0

theorem CertZ.cstOkZOfW (d0 : Efab) (St : CycState) (itvOf : Nat → Nat → Nat)
    (fiOf : Nat → Nat → Bool) : CertZ.cstOkZW d0 St itvOf fiOf → cstOkZ d0 St :=
  fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, ⟨itvOf, fiOf, h2, h3, h4⟩, h5⟩

theorem CertZ.cstOkZWOf (d0 : Efab) (St : CycState) :
    cstOkZ d0 St → ∃ itvOf fiOf, CertZ.cstOkZW d0 St itvOf fiOf :=
  fun ⟨h1, ⟨itvOf, fiOf, h2, h3, h4⟩, h5⟩ => ⟨itvOf, fiOf, h1, h2, h3, h4, h5⟩

/-! # 2. The instruction views past the end, and the stability of the cut clause -/

/-- `fiOf` extended past the end of `c` by M2's recurrence at the appended step `s` (leading star
`ls`); every other agent is framed. -/
def CertZ.fiSnoc (c : Cand) (s : Estep) (ls : List Wlabel) (fiOf : Nat → Nat → Bool) :
    Nat → Nat → Bool :=
  fun k ag =>
    if k ≤ cdEnd c then fiOf k ag
    else if ag = s.esAg then PfRunUnpinned.fiFold (fiOf (cdEnd c) ag) ls
    else fiOf (cdEnd c) ag

/-- `itvOf` extended past the end of `c` by M2's recurrence (`itvStep` at the appended
candidate). -/
def CertZ.itvSnoc (c : Cand) (s : Estep) (ls : List Wlabel) (itvOf : Nat → Nat → Nat)
    (fiOf : Nat → Nat → Bool) : Nat → Nat → Nat :=
  fun k ag =>
    if k ≤ cdEnd c then itvOf k ag
    else if ag = s.esAg then
      PfRunUnpinned.itvStep cohSrc (candExec (candSnoc c s)) (cdEnd c) ag (itvOf (cdEnd c) ag)
        (PfRunUnpinned.fiFold (fiOf (cdEnd c) ag) ls)
    else itvOf (cdEnd c) ag

theorem CertZ.fiSnocLe (c : Cand) (s : Estep) (ls : List Wlabel) (fiOf : Nat → Nat → Bool)
    (k ag : Nat) : k ≤ cdEnd c → CertZ.fiSnoc c s ls fiOf k ag = fiOf k ag := by
  intro h; simp [CertZ.fiSnoc, h]

theorem CertZ.itvSnocLe (c : Cand) (s : Estep) (ls : List Wlabel) (itvOf : Nat → Nat → Nat)
    (fiOf : Nat → Nat → Bool) (k ag : Nat) :
    k ≤ cdEnd c → CertZ.itvSnoc c s ls itvOf fiOf k ag = itvOf k ag := by
  intro h; simp [CertZ.itvSnoc, h]

/-- The trace prefix before an old index is unchanged by appending. -/
theorem CertZ.takeSnoc (c : Cand) (s : Estep) (k : Nat) :
    k ≤ cdEnd c → (candExec (candSnoc c s)).exTr.take k = (candExec c).exTr.take k := by
  intro hk
  show (c.cdTr ++ [s]).take k = c.cdTr.take k
  exact List.take_append_of_le_length hk

/-- `itvStep` at an old index is unchanged by appending. -/
theorem CertZ.itvStepSnoc (c : Cand) (s : Estep) (k ag itv : Nat) (arm : Bool) :
    k < cdEnd c →
    PfRunUnpinned.itvStep cohSrc (candExec (candSnoc c s)) k ag itv arm =
      PfRunUnpinned.itvStep cohSrc (candExec c) k ag itv arm := by
  intro hk
  have h1 : (candExec (candSnoc c s)).exTr[k]? = (candExec c).exTr[k]? := candSnocTrLt c s k hk
  have h2 := CertZ.takeSnoc c s k (Nat.le_of_lt hk)
  unfold PfRunUnpinned.itvStep
  rw [h1, h2]

/-- THE CUT CLAUSE IS STABLE: at an old index, M2's per-index clause of the appended candidate (at
the extended views) is the old one. -/
theorem CertZ.fcutEM2Snoc (c : Cand) (s : Estep) (ls0 : List Wlabel) (itvOf : Nat → Nat → Nat)
    (fiOf : Nat → Nat → Bool) (k ag : Nat) (ls : List Wlabel) (σ : Mstate) :
    k < cdEnd c →
    PfRunUnpinned.fcutEM2 cohSrc (candExec c) itvOf fiOf k ag ls σ →
    PfRunUnpinned.fcutEM2 cohSrc (candExec (candSnoc c s)) (CertZ.itvSnoc c s ls0 itvOf fiOf)
      (CertZ.fiSnoc c s ls0 fiOf) k ag ls σ := by
  intro hk ⟨hf, hfi, hitv, hfr⟩
  have hk1 : k + 1 ≤ cdEnd c := hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro base tvs hm
    rw [CertZ.itvSnocLe c s ls0 itvOf fiOf k ag (Nat.le_of_lt hk)]
    exact hf base tvs hm
  · rw [CertZ.fiSnocLe c s ls0 fiOf _ _ hk1, CertZ.fiSnocLe c s ls0 fiOf _ _ (Nat.le_of_lt hk)]
    exact hfi
  · rw [CertZ.itvSnocLe c s ls0 itvOf fiOf _ _ hk1,
      CertZ.itvSnocLe c s ls0 itvOf fiOf _ _ (Nat.le_of_lt hk),
      CertZ.fiSnocLe c s ls0 fiOf _ _ (Nat.le_of_lt hk), CertZ.itvStepSnoc c s _ _ _ _ hk]
    exact hitv
  · intro i hi
    rw [CertZ.fiSnocLe c s ls0 fiOf _ _ hk1, CertZ.fiSnocLe c s ls0 fiOf _ _ (Nat.le_of_lt hk),
      CertZ.itvSnocLe c s ls0 itvOf fiOf _ _ hk1,
      CertZ.itvSnocLe c s ls0 itvOf fiOf _ _ (Nat.le_of_lt hk)]
    exact hfr i hi

/-- THE CUT CLAUSE AT THE NEW INDEX: the recurrences hold by definition; only the leading star's
fetches owe their cut. -/
theorem CertZ.fcutEM2End (c : Cand) (i : Nat) (lb : Lbl) (ls : List Wlabel)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool) (σ : Mstate) :
    (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
      PfRunUnpinned.fcutM2 (itvOf (cdEnd c) i) σ.msImg σ.msLog i base tvs) →
    PfRunUnpinned.fcutEM2 cohSrc (candExec (candSnoc c ⟨i, lb⟩))
      (CertZ.itvSnoc c ⟨i, lb⟩ ls itvOf fiOf) (CertZ.fiSnoc c ⟨i, lb⟩ ls fiOf) (cdEnd c) i ls σ := by
  intro hcut
  have hgt : ¬ cdEnd c + 1 ≤ cdEnd c := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro base tvs hm
    rw [CertZ.itvSnocLe _ _ _ _ _ _ _ (Nat.le_refl _)]
    exact hcut base tvs hm
  · simp only [CertZ.fiSnoc, hgt, Nat.le_refl, if_true, if_false]
  · simp only [CertZ.itvSnoc, CertZ.fiSnoc, hgt, Nat.le_refl, if_true, if_false]
  · intro ag hag
    constructor <;> simp [CertZ.itvSnoc, CertZ.fiSnoc, hgt, hag]

/-! # 3. THE ONE-STEP EXTENSION -/

/-- **`CertZ.cstOkZWSnoc` — THE ONE-STEP EXTENSION** (`execProgOk'Snoc`/`execProgOk'SnocPair`'s
twin at M2's conjunct, with `snocConsistent`): appending hart `i`'s step `lb`, realized by a
shaped block from the hart's current program state, keeps the threaded state, at the views
extended by M2's recurrence. -/
theorem CertZ.cstOkZWSnoc (d0 : Efab) (St : CycState) (itvOf : Nat → Nat → Nat)
    (fiOf : Nat → Nat → Bool) (i : Nat) (lb : Lbl) (p pa : Pexv6) (da : Efab)
    (ls : List Wlabel) (p' : Pexv6) (d' : Efab) :
    CertZ.cstOkZW d0 St itvOf fiOf →
    mstepOk (candLastSt St.cstC) i lb →
    (∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
      lb = .LLoad aq base ts vs →
      scaOkT (shadowOf cohSrc St.cstC.cdTr i) (candLastSt St.cstC).msImg
          (candLastSt St.cstC).msLog i base ts ∧
        diskLatOk (candLastSt St.cstC).msImg (candLastSt St.cstC).msLog i base ts) →
    (St.cstPst (cdEnd St.cstC))[i]? = some p →
    admRunG pstepEv true p (St.cstDv (cdEnd St.cstC)) ls pa da →
    (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
      PfRunUnpinned.fcutM2 (itvOf (cdEnd St.cstC) i) (candLastSt St.cstC).msImg
        (candLastSt St.cstC).msLog i base tvs) →
    ((∃ l, lbFused l ∧ lblRealizes pclsEv pa (candLastSt St.cstC) i lb l ∧
        pstepEv pa da l p' d') ∨
     (∃ (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab)
        (l1 l2 : Wlabel),
        lblRealizesPair pclsEv pa pm2 (candLastSt St.cstC) i lb l1 l2 ∧
        pstepEv pa da l1 pm dm ∧
        admRunG pstepEv false pm dm ls2 pm2 dm2 ∧
        pstepEv pm2 dm2 l2 p' d')) →
    CertZ.cstOkZW d0
      ⟨candSnoc St.cstC ⟨i, lb⟩, pstSnoc St.cstC St.cstPst i p', dvSnoc St.cstC St.cstDv d'⟩
      (CertZ.itvSnoc St.cstC ⟨i, lb⟩ ls itvOf fiOf) (CertZ.fiSnoc St.cstC ⟨i, lb⟩ ls fiOf) := by
  obtain ⟨c, pst, dv⟩ := St
  dsimp only
  rintro ⟨hsr, hi0, hf0, ⟨hSC, hscaT, hdl⟩, hd0⟩ hok hld hp hrun hcut harm
  have hlast : stt (candExec (candSnoc c ⟨i, lb⟩)) (cdEnd c) = candLastSt c :=
    candSnocLastSt c _
  have htkEnd : (candExec (candSnoc c ⟨i, lb⟩)).exTr.take (cdEnd c) = c.cdTr := by
    rw [CertZ.takeSnoc c _ _ (Nat.le_refl _)]
    exact List.take_length
  -- the trace lookup splits into the old indices and the new one
  have hsplit : ∀ k s, (candExec (candSnoc c ⟨i, lb⟩)).exTr[k]? = some s →
      (k < cdEnd c ∧ c.cdTr[k]? = some s) ∨ (k = cdEnd c ∧ s = ⟨i, lb⟩) := by
    intro k s hs
    change (c.cdTr ++ [⟨i, lb⟩])[k]? = some s at hs
    have hlt := lookup_lt_Some hs
    simp only [List.length_append, List.length_singleton] at hlt
    by_cases hk : k < cdEnd c
    · exact .inl ⟨hk, by rw [← candSnocTrLt c ⟨i, lb⟩ k hk]; exact hs⟩
    · have hke : k = cdEnd c := by unfold cdEnd at hk ⊢; omega
      subst hke
      have hs2 := candSnocTrEnd c ⟨i, lb⟩
      change (c.cdTr ++ [⟨i, lb⟩])[cdEnd c]? = some ⟨i, lb⟩ at hs2
      rw [hs2, Option.some.injEq] at hs
      exact .inr ⟨rfl, hs.symm⟩
  refine ⟨snocConsistent c ⟨i, lb⟩ hsr hok,
    fun ag => by rw [CertZ.itvSnocLe _ _ _ _ _ _ _ (Nat.zero_le _)]; exact hi0 ag,
    fun ag => by rw [CertZ.fiSnocLe _ _ _ _ _ _ (Nat.zero_le _)]; exact hf0 ag,
    ⟨?_, ?_, ?_⟩, by dsimp only; rw [dvSnocLe c dv d' 0 (Nat.zero_le _)]; exact hd0⟩
  · -- the shaped conformance predicate
    intro k s hs
    rcases hsplit k s hs with ⟨hk, hs'⟩ | ⟨hk, hse⟩
    · obtain ⟨hsca, q, qa, qd, q', qls, h1, h2, h3, h4, h5, h6⟩ := hSC k s hs'
      have hstt := candSnocStt c ⟨i, lb⟩ k (Nat.le_of_lt hk)
      refine ⟨fun aq base ts vs hl => by rw [hstt]; exact hsca aq base ts vs hl,
        q, qa, qd, q', qls, ?_⟩
      have hk1 : k + 1 ≤ cdEnd c := hk
      dsimp only
      rw [pstSnocLe c pst i p' k (Nat.le_of_lt hk), pstSnocLe c pst i p' (k + 1) hk1,
        dvSnocLe c dv d' k (Nat.le_of_lt hk), dvSnocLe c dv d' (k + 1) hk1, hstt]
      exact ⟨h1, h2, h3, h4, CertZ.fcutEM2Snoc c _ ls itvOf fiOf k _ qls _ hk h5, h6⟩
    · subst hk
      subst hse
      refine ⟨fun aq base ts vs hl => by
          rw [hlast]; exact scaOkTSca _ _ _ _ _ _ (hld aq base ts vs hl).1,
        p, pa, da, p', ls, ?_⟩
      dsimp only
      rw [pstSnocLe c pst i p' (cdEnd c) (Nat.le_refl _),
        pstSnocGt c pst i p' (cdEnd c + 1) (by omega),
        dvSnocLe c dv d' (cdEnd c) (Nat.le_refl _), dvSnocGt c dv d' (cdEnd c + 1) (by omega),
        hlast]
      refine ⟨hp, rfl, hrun, fun _ _ _ => trivial, ?_, harm⟩
      exact CertZ.fcutEM2End c i lb ls itvOf fiOf _ hcut
  · -- the shadow clause
    intro k s hs aq base ts vs hl
    rcases hsplit k s hs with ⟨hk, hs'⟩ | ⟨hk, hse⟩
    · rw [CertZ.takeSnoc c _ k (Nat.le_of_lt hk), candSnocStt c _ k (Nat.le_of_lt hk)]
      exact hscaT k s hs' aq base ts vs hl
    · subst hk
      subst hse
      rw [htkEnd, hlast]
      exact (hld aq base ts vs hl).1
  · -- the disk clause
    intro k s hs aq base ts vs hl
    rcases hsplit k s hs with ⟨hk, hs'⟩ | ⟨hk, hse⟩
    · rw [candSnocStt c _ k (Nat.le_of_lt hk)]
      exact hdl k s hs' aq base ts vs hl
    · subst hk
      subst hse
      rw [hlast]
      exact (hld aq base ts vs hl).2

/-! # 4. THE SEGMENT ENGINE -/

/-- **THE PER-STEP POLICY** (`certSegment''`'s `Hpol''`/`Hpres`/`Hrdsp` collapsed to what
`cstOkZWSnoc` consumes, at an invariant `Sync` the policy chooses): from every threaded state at
row slot `n` (`Sync n`), hart `x`'s program state `pC`, the policy supplies the appended label `lb'`
(`lblReidxW` of the row's: a read re-indexed, re-valued or poisoned, a write verbatim), its
admissibility at the candidate's last state, the load facts, the shaped block from `pC` and the
leading star's fetch cut — and `Sync` at the next slot.  W10-3 builds `Sync` (the walk invariant:
the emission's run in lockstep with the certified run off a taint set, `csync`'s twin) and W10-4
the per-site datum. -/
def CertZ.stepPolZ (d0 : Efab) (x : Nat) (row : List Lbl) (Sync : Nat → CycState → Prop) : Prop :=
  ∀ (n : Nat) (lb : Lbl) (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool)
    (pC : Pexv6),
    row[n]? = some lb → CertZ.cstOkZW d0 St itvOf fiOf →
    (St.cstPst (cdEnd St.cstC))[x]? = some pC → Sync n St →
    ∃ (lb' : Lbl) (pa : Pexv6) (da : Efab) (ls : List Wlabel) (pC' : Pexv6) (d' : Efab),
      lblReidxW lb lb' ∧
      mstepOk (candLastSt St.cstC) x lb' ∧
      (∀ (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
        lb' = .LLoad aq base ts vs →
        scaOkT (shadowOf cohSrc St.cstC.cdTr x) (candLastSt St.cstC).msImg
            (candLastSt St.cstC).msLog x base ts ∧
          diskLatOk (candLastSt St.cstC).msImg (candLastSt St.cstC).msLog x base ts) ∧
      admRunG pstepEv true pC (St.cstDv (cdEnd St.cstC)) ls pa da ∧
      (∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
        PfRunUnpinned.fcutM2 (itvOf (cdEnd St.cstC) x) (candLastSt St.cstC).msImg
          (candLastSt St.cstC).msLog x base tvs) ∧
      ((∃ l, lbFused l ∧ lblRealizes pclsEv pa (candLastSt St.cstC) x lb' l ∧
          pstepEv pa da l pC' d') ∨
       (∃ (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel) (pm2 : Pexv6) (dm2 : Efab)
          (l1 l2 : Wlabel),
          lblRealizesPair pclsEv pa pm2 (candLastSt St.cstC) x lb' l1 l2 ∧
          pstepEv pa da l1 pm dm ∧
          admRunG pstepEv false pm dm ls2 pm2 dm2 ∧
          pstepEv pm2 dm2 l2 pC' d')) ∧
      Sync (n + 1)
        ⟨candSnoc St.cstC ⟨x, lb'⟩, pstSnoc St.cstC St.cstPst x pC', dvSnoc St.cstC St.cstDv d'⟩

theorem CertZ.dropCons (row : List Lbl) (k : Nat) (lb : Lbl) :
    row[k]? = some lb → row.drop k = lb :: row.drop (k + 1) := by
  induction row generalizing k with
  | nil => intro h; simp at h
  | cons a row ih =>
    intro h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rfl
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.drop_succ_cons]
      exact ih k h

/-- **THE SEGMENT ENGINE** (`certSegment''`'s iteration at M2's conjunct): under the per-step
policy, `len` slots of hart `x`'s row from slot `k0` are appended, one `cstOkZWSnoc` each; the
appended labels are `lblReidxW` of the row's. -/
theorem CertZ.segRunZ (d0 : Efab) (x : Nat) (row : List Lbl) (Sync : Nat → CycState → Prop)
    (hpol : CertZ.stepPolZ d0 x row Sync) :
    ∀ (len k0 : Nat) (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool)
      (pC : Pexv6),
      k0 + len ≤ row.length → CertZ.cstOkZW d0 St itvOf fiOf →
      (St.cstPst (cdEnd St.cstC))[x]? = some pC → Sync k0 St →
      ∃ (tradd : List Estep) (St' : CycState) (itvOf' : Nat → Nat → Nat)
        (fiOf' : Nat → Nat → Bool) (pC' : Pexv6),
        St'.cstC.cdTr = St.cstC.cdTr ++ tradd ∧
        (∀ s, s ∈ tradd → s.esAg = x) ∧
        List.Forall₂ lblReidxW ((row.drop k0).take len) (tradd.map (fun s => s.esLb)) ∧
        CertZ.cstOkZW d0 St' itvOf' fiOf' ∧
        (St'.cstPst (cdEnd St'.cstC))[x]? = some pC' ∧
        Sync (k0 + len) St' ∧
        St'.cstC.cdImg = St.cstC.cdImg ∧ St'.cstPst 0 = St.cstPst 0 := by
  intro len
  induction len with
  | zero =>
    intro k0 St itvOf fiOf pC _ hok hp hs
    refine ⟨[], St, itvOf, fiOf, pC, (List.append_nil _).symm, fun s h => by simp at h, ?_,
      hok, hp, hs, rfl, rfl⟩
    simp
  | succ len ih =>
    intro k0 St itvOf fiOf pC hlen hok hp hs
    obtain ⟨c, pst, dv⟩ := St
    have hk0 : k0 < row.length := by omega
    obtain ⟨lb, hlb⟩ : ∃ lb, row[k0]? = some lb := ⟨row[k0], List.getElem?_eq_getElem hk0⟩
    obtain ⟨lb', pa, da, ls, pC', d', hre, hmok, hld, hrun, hcut, harm, hs1⟩ :=
      hpol k0 lb ⟨c, pst, dv⟩ itvOf fiOf pC hlb hok hp hs
    have hok1 := CertZ.cstOkZWSnoc d0 ⟨c, pst, dv⟩ itvOf fiOf x lb' pC pa da ls pC' d' hok hmok
      hld hp hrun hcut harm
    have hp1 : (pstSnoc c pst x pC' (cdEnd (candSnoc c ⟨x, lb'⟩)))[x]? = some pC' := by
      rw [cdEndSnoc, pstSnocGt c pst x pC' (cdEnd c + 1) (by omega)]
      exact List.getElem?_set_self (lookup_lt_Some hp)
    obtain ⟨tradd, St', itvOf', fiOf', pC'', htr, hag, hf2, hok', hp', hs', himg, hpst⟩ :=
      ih (k0 + 1) _ _ _ pC' (by omega) hok1 hp1 hs1
    refine ⟨⟨x, lb'⟩ :: tradd, St', itvOf', fiOf', pC'', ?_, ?_, ?_, hok', hp', ?_, ?_, ?_⟩
    · rw [htr]
      show (c.cdTr ++ [⟨x, lb'⟩]) ++ tradd = c.cdTr ++ ⟨x, lb'⟩ :: tradd
      simp
    · intro s hsm
      rcases List.mem_cons.1 hsm with rfl | hsm
      · rfl
      · exact hag s hsm
    · rw [CertZ.dropCons row k0 lb hlb, List.take_succ_cons, List.map_cons]
      exact .cons hre hf2
    · rw [show k0 + (len + 1) = k0 + 1 + len by omega]
      exact hs'
    · rw [himg]; rfl
    · rw [hpst]
      exact pstSnocLe c pst x pC' 0 (Nat.zero_le _)

/-- **`CertZ.segStepZOfPol`** (`segStepOfSegment`'s twin at the unpinned supply): the engine's
output IS one `segStepZ` (the walk's step relation, `GraphFetchRun` §3). -/
theorem CertZ.segStepZOfPol (d0 : Efab) (x : Nat) (row : List Lbl)
    (Sync : Nat → CycState → Prop) (hpol : CertZ.stepPolZ d0 x row Sync)
    (len k0 : Nat) (St : CycState) (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool)
    (pC : Pexv6) :
    k0 + len ≤ row.length → CertZ.cstOkZW d0 St itvOf fiOf →
    (St.cstPst (cdEnd St.cstC))[x]? = some pC → Sync k0 St →
    ∃ (tradd : List Estep) (St' : CycState) (itvOf' : Nat → Nat → Nat)
      (fiOf' : Nat → Nat → Bool) (pC' : Pexv6),
      segStepZ d0 ⟨x, (row.drop k0).take len, cdEnd St.cstC, tradd⟩ St St' ∧
      CertZ.cstOkZW d0 St' itvOf' fiOf' ∧
      (St'.cstPst (cdEnd St'.cstC))[x]? = some pC' ∧
      Sync (k0 + len) St' ∧
      St'.cstC.cdImg = St.cstC.cdImg ∧ St'.cstPst 0 = St.cstPst 0 := by
  intro hlen hok hp hs
  obtain ⟨tradd, St', itvOf', fiOf', pC', htr, hag, hf2, hok', hp', hs', himg, hpst⟩ :=
    CertZ.segRunZ d0 x row Sync hpol len k0 St itvOf fiOf pC hlen hok hp hs
  exact ⟨tradd, St', itvOf', fiOf', pC',
    ⟨CertZ.cstOkZOfW d0 St itvOf fiOf hok, CertZ.cstOkZOfW d0 St' itvOf' fiOf' hok', rfl, htr,
      hag, hf2⟩, hok', hp', hs', himg, hpst⟩

end Weak
