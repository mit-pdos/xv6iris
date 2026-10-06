/-
Weak: **acyclicity of the EXTENDED graph D⁺ = gdep ∪ gE** (M6 W2b, design item
(iii): the milestone-floor measure).

Rocq: `iris/WeakRobustAcyc2.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `Weak/WeakRobustAcyc.lean` refutes every
`gdep`-cycle with the MESSAGE TIMESTAMP as the measure; `Weak/WeakRobustOrd.lean`
extends the graph with the floor-protection edges `gE` (fulfil of a LEAF of read
`r`'s byte-`a` floor `F = rdFloor TS r a` to the fulfil of a byte-`a` write
`t̂ > F`).  This file re-runs the walk on `gdep2 = gdep ∪ gE`.  A `gE` edge may be
same-agent and need not move forward in the trace, so the raw timestamp no
longer works.  MILESTONE EDGES (`gmile`) are {cross-agent rf} ∪ {all `gE`};
everything else is a same-agent `gdep` edge (index-increasing).  THE MEASURE µ
is the MILESTONE FLOOR: a cross-rf milestone reading `ts` carries `ts`; a `gE`
milestone out of read `r` at byte `a` carries `F(r,a)` (`mileMu`).  THE WALK:
`onCycle2 TS µ` says a milestone edge of measure µ sits on a cycle; the advance
step follows the return path to its FIRST milestone (`rtcGdep2FirstMile`); the
one arithmetic fact is `mileMuGain` (µ < ts(x) for every fulfil `x` of `u`'s
agent at or after `u`): S1 (`atraceS1LeF`) for a cross-rf entry, the new
premise `eeOk` (or the edge's own `F < t̂` when `x = u`) for a `gE` entry.
BOUNDEDNESS: a `gE` milestone's µ is below the real fulfilled `t̂`
(`gevTsMsg`), so no `ptracesWsInit` premise is needed.  A0
(`rfEdgesOkMs`): the per-edge premise relativized to MILESTONE-SOURCE fulfils,
concluding `edgeOkF`; implied by `rfEdgesOk` (`rfEdgesOkRfEdgesOkMs`).
DEPENDENCY-FREE: no Iris, no Sail.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase as `Weak/WeakMem.lean` deviation 1.  No name of this
   file is in `notes/weak-port-dupnames.json`.  `grf` is
   `WeakRobustGraph.grf`.
2. VOCABULARY: as `WeakRobustAcyc` deviation 2 (`l !! i` ↦ `l[i]?`,
   `is_Some o` ↦ `o.isSome`, `surjective_pairing` ↦ structure eta).
3. SECTION VARIABLES: `pstep` (and `pdev` in `wpBehaviorGdep2Acyclic`) are
   explicit arguments exactly where a statement mentions them, in Rocq's order
   (`WeakRobustAcyc` deviation 3).
4. `tc` is core `Relation.TransGen` (built from the LAST step):
   `tcGdep2Split` goes by tail induction (Rocq: head `induction 1`);
   `rtcGdep2FirstMile` uses `MachCSL.rtc_ind_l`.  Statements unchanged.
5. Imports: only `Weak.WeakRobustOrd` (which brings `WeakRobustAcyc`,
   `WeakRobustLin`, `WeakRobustProv`, `WeakRobustGraph`, `WeakRobustTrace`);
   `WeakAxiomatic` / `WeakRobust` are not needed (`WeakRobustAcyc` deviation 5).

**Rocq → Lean name map.**  `gE_ra` ↦ `gERa`; `gE_ra_gE_at` ↦ `gERaGEAt`;
`gE_at_gE_ra` ↦ `gEAtGERa`; `gE_ra_gdep2` ↦ `gERaGdep2`; `ee_ok` ↦ `eeOk`;
`gmile`; `mile_mu` ↦ `mileMu`; `mile_mu_gdep2` ↦ `mileMuGdep2`;
`mile_mu_gmile` ↦ `mileMuGmile`; `rf_edges_ok_ms` ↦ `rfEdgesOkMs`;
`rf_edges_ok_rf_edges_ok_ms` ↦ `rfEdgesOkRfEdgesOkMs`; `gmile_mile_mu` ↦
`gmileMileMu`; `mile_mu_src_ts` ↦ `mileMuSrcTs`; `mile_mu_bounded` ↦
`mileMuBounded`; `gdep2_mile_or_sa` ↦ `gdep2MileOrSa`; `rtc_gdep2_first_mile`
↦ `rtcGdep2FirstMile`; `tc_gdep2_split` ↦ `tcGdep2Split`; `mile_mu_gain` ↦
`mileMuGain`; `on_cycle2` ↦ `onCycle2`; `on_cycle2_advance` ↦
`onCycle2Advance`; `on_cycle2_bounded` ↦ `onCycle2Bounded`; `on_cycle2_empty`
↦ `onCycle2Empty`; `gdep2_acyclic_edges_ok` ↦ `gdep2AcyclicEdgesOk`;
`gdep_acyclic_of_gdep2` ↦ `gdepAcyclicOfGdep2`; `wp_behavior_gdep2_acyclic` ↦
`wpBehaviorGdep2Acyclic`.

**Not ported:** nothing.
-/
import Weak.WeakRobustOrd

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Wlabel

/-! ## The E edge with its BYTE named -/

section edges

variable {P D : Type}

/-- `gEAt` with the byte `a` hoisted into the parameters (µ must name it). -/
def gERa (TS : Ptraces P D) (r : Gev) (a : Int) (e1 e2 : Gev) : Prop :=
  ∃ (l : Wlabel) (ts tstar that : Nat),
    gevLb TS r = some l ∧ (a, ts) ∈ lbReads l ∧
    tstar ∈ rdLeaves TS r a ∧ 0 < tstar ∧
    gevTs TS e1 = some tstar ∧
    gevTs TS e2 = some that ∧
    msgWrites TS that a ∧
    rdFloor TS r a < that

theorem gERaGEAt (TS : Ptraces P D) (r : Gev) (a : Int) (e1 e2 : Gev) :
    gERa TS r a e1 e2 → gEAt TS r e1 e2 := by
  rintro ⟨l, ts, tstar, that, h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨l, a, ts, tstar, that, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem gEAtGERa (TS : Ptraces P D) (r e1 e2 : Gev) :
    gEAt TS r e1 e2 → ∃ a, gERa TS r a e1 e2 := by
  rintro ⟨l, a, ts, tstar, that, h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨a, l, ts, tstar, that, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem gERaGdep2 (TS : Ptraces P D) (r : Gev) (a : Int) (e1 e2 : Gev) :
    gERa TS r a e1 e2 → gdep2 TS e1 e2 :=
  fun h => gEGdep2 TS e1 e2 ⟨r, gERaGEAt TS r a e1 e2 h⟩

end edges

/-! ## THE NEW PREMISE `eeOk` — the E-edge analogue of `rfEdgesOk`

For every E edge (read `r`, byte `a`, floor `F = rdFloor TS r a`, source `e1`,
target `et`) and EVERY fulfil `ey` of `et`'s own agent strictly po-AFTER `et`:
`F < ts(ey)`.  No cycle quantifier: a property of the bundle alone. -/

def eeOk {P D : Type} (TS : Ptraces P D) : Prop :=
  ∀ (r : Gev) (a : Int) (e1 et ey : Gev) (y : Nat),
    gERa TS r a e1 et →
    et.1 = ey.1 → et.2 < ey.2 →
    gevTs TS ey = some y →
    rdFloor TS r a < y

section acyc2

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pdev : P → Wlabel → P → Bool)

/-! ### MILESTONE EDGES and the measure µ -/

/-- A MILESTONE: a cross-agent `gdep` edge (necessarily rf) or ANY `gE` edge. -/
def gmile (TS : Ptraces P D) (e1 e2 : Gev) : Prop :=
  (gdep TS e1 e2 ∧ e1.1 ≠ e2.1) ∨ gE TS e1 e2

/-- The milestone edge `v → u` TOGETHER WITH ITS MEASURE µ. -/
def mileMu (TS : Ptraces P D) (mu : Nat) (v u : Gev) : Prop :=
  (∃ a, gevTs TS v = some mu ∧ gevReads TS u a mu ∧ v.1 ≠ u.1) ∨
  (∃ r a, gERa TS r a v u ∧ mu = rdFloor TS r a)

theorem mileMuGdep2 (TS : Ptraces P D) (mu : Nat) (v u : Gev) :
    mileMu TS mu v u → gdep2 TS v u := by
  rintro (⟨a, hts, hrd, -⟩ | ⟨r, a, hra, -⟩)
  · exact grfGdep2 TS v u ⟨mu, a, hts, hrd⟩
  · exact gERaGdep2 TS r a v u hra

/-- A milestone edge WITH its measure IS a milestone edge. -/
theorem mileMuGmile (TS : Ptraces P D) (mu : Nat) (v u : Gev) :
    mileMu TS mu v u → gmile TS v u := by
  rintro (⟨a, hts, hrd, hne⟩ | ⟨r, a, hra, -⟩)
  · exact Or.inl ⟨Or.inr ⟨mu, a, hts, hrd⟩, hne⟩
  · exact Or.inr ⟨r, gERaGEAt TS r a v u hra⟩

/-! ### A0: THE PER-EDGE PREMISE, RELATIVIZED TO THE WALK'S FULFILS

Only milestone-source fulfils `k'` are quantified, the conclusion is `edgeOkF`
(coverage at the fulfil), and the rmw case `k' = e2.2` is excluded. -/

def rfEdgesOkMs (TS : Ptraces P D) : Prop :=
  ∀ (e1 e2 : Gev) (T : Atrace P D) (ts : Nat) (a : Int) (k' : Nat) (ev' : Aev D),
    gevTs TS e1 = some ts → gevReads TS e2 a ts → e1.1 ≠ e2.1 →
    TS.ptTrs[e2.1]? = some T →
    e2.2 < k' →
    T.atEvs[k']? = some ev' → ev'.aeTs.isSome →
    (∃ y, gmile TS (e2.1, k') y) →
    edgeOkF T e2.2 k' ts

/-- THE OLD PREMISE IMPLIES THE NEW ONE. -/
theorem rfEdgesOkRfEdgesOkMs (TS : Ptraces P D) :
    ptracesWf pstep TS → rfEdgesOk TS → rfEdgesOkMs TS := by
  intro hwf h e1 e2 T ts a k' ev' hts hrd hne hT hlt hev hsome _
  exact edgeOkEdgeOkF pstep TS.ptImg TS.ptLog e2.1 T e2.2 k' ts ev' (hwf _ _ hT) (by omega)
    hev hsome (h e1 e2 T ts a k' ev' hts hrd hne hT hlt hev hsome)

theorem gmileMileMu (TS : Ptraces P D) (v u : Gev) :
    gmile TS v u → ∃ mu, mileMu TS mu v u := by
  rintro (⟨hd, hne⟩ | ⟨r, hat⟩)
  · have hrf : WeakRobustGraph.grf TS v u := by
      rcases hd with ⟨hag, _⟩ | hrf
      · exact absurd hag hne
      · exact hrf
    obtain ⟨ts, a, hts, hrd⟩ := hrf
    exact ⟨ts, Or.inl ⟨a, hts, hrd, hne⟩⟩
  · obtain ⟨a, hra⟩ := gEAtGERa TS r v u hat
    exact ⟨rdFloor TS r a, Or.inr ⟨r, a, hra, rfl⟩⟩

/-- The milestone's SOURCE is always a fulfil, at or below µ. -/
theorem mileMuSrcTs (TS : Ptraces P D) (mu : Nat) (v u : Gev) :
    mileMu TS mu v u → ∃ tv, gevTs TS v = some tv ∧ tv ≤ mu := by
  rintro (⟨a, hts, -⟩ | ⟨r, a, hra, rfl⟩)
  · exact ⟨mu, hts, Nat.le_refl _⟩
  · obtain ⟨l, ts, tstar, that, -, -, hleaf, -, h5, -⟩ := hra
    exact ⟨tstar, h5, lvalGe id _ _ hleaf⟩

/-- µ IS BOUNDED BY THE LOG. -/
theorem mileMuBounded (TS : Ptraces P D) (mu : Nat) (v u : Gev) :
    ptracesWf pstep TS → mileMu TS mu v u → mu ≤ TS.ptLog.length := by
  rintro hwf (⟨a, hts, -⟩ | ⟨r, a, hra, rfl⟩)
  · obtain ⟨base, data, kc, hm⟩ := gevTsMsg pstep TS v mu hwf hts
    have := lookup_lt_Some hm
    have := gevTsPos pstep TS v mu hwf hts
    omega
  · obtain ⟨l, ts, tstar, that, -, -, -, -, -, h6, -, hlt⟩ := hra
    obtain ⟨base, data, kc, hm⟩ := gevTsMsg pstep TS u that hwf h6
    have := lookup_lt_Some hm
    have := gevTsPos pstep TS u that hwf h6
    omega

/-! ### THE FIRST-MILESTONE DECOMPOSITION -/

theorem gdep2MileOrSa (TS : Ptraces P D) (e1 e2 : Gev) :
    gdep2 TS e1 e2 → gmile TS e1 e2 ∨ (gdep TS e1 e2 ∧ e1.1 = e2.1) := by
  rintro (hd | he)
  · by_cases hag : e1.1 = e2.1
    · exact Or.inr ⟨hd, hag⟩
    · exact Or.inl (Or.inl ⟨hd, hag⟩)
  · exact Or.inl (Or.inr he)

/-- Follow an `rtc gdep2` path from `u` until its FIRST milestone. -/
theorem rtcGdep2FirstMile (TS : Ptraces P D) (u v : Gev) :
    ptracesWf pstep TS → rtc (gdep2 TS) u v →
    (u.1 = v.1 ∧ u.2 ≤ v.2) ∨
    ∃ x y, u.1 = x.1 ∧ u.2 ≤ x.2 ∧ rtc (gdep2 TS) u x ∧
           gmile TS x y ∧ rtc (gdep2 TS) y v := by
  intro hwf hr
  refine rtc_ind_l (R := gdep2 TS)
    (fun u => (u.1 = v.1 ∧ u.2 ≤ v.2) ∨
      ∃ x y, u.1 = x.1 ∧ u.2 ≤ x.2 ∧ rtc (gdep2 TS) u x ∧
             gmile TS x y ∧ rtc (gdep2 TS) y v)
    v (Or.inl ⟨rfl, Nat.le_refl _⟩) ?_ u hr
  intro u w huw hwv ih
  rcases gdep2MileOrSa TS u w huw with hmile | ⟨hd, hag⟩
  · exact Or.inr ⟨u, w, rfl, Nat.le_refl _, rtc_refl u, hmile, hwv⟩
  · have hlt := gdepSameAgentLt pstep TS u w hwf hd hag
    rcases ih with ⟨hag', hle⟩ | ⟨x, y, hx1, hx2, hrx, hmile, hry⟩
    · exact Or.inl ⟨hag.trans hag', by omega⟩
    · exact Or.inr ⟨x, y, hag.trans hx1, by omega, rtc_l huw hrx, hmile, hry⟩

/-- …and the `tc` form: a `gdep2` path either stayed same-agent and forward, or
it contains a milestone. -/
theorem tcGdep2Split (TS : Ptraces P D) (e1 e2 : Gev) :
    ptracesWf pstep TS → tc (gdep2 TS) e1 e2 →
    (e1.1 = e2.1 ∧ e1.2 < e2.2) ∨
    (∃ x y, rtc (gdep2 TS) e1 x ∧ gmile TS x y ∧ rtc (gdep2 TS) y e2) := by
  intro hwf h
  induction h with
  | single hxy =>
    rcases gdep2MileOrSa TS _ _ hxy with hm | ⟨hd, hag⟩
    · exact Or.inr ⟨e1, _, rtc_refl _, hm, rtc_refl _⟩
    · exact Or.inl ⟨hag, gdepSameAgentLt pstep TS _ _ hwf hd hag⟩
  | tail hxy hyz ih =>
    rcases gdep2MileOrSa TS _ _ hyz with hm | ⟨hd, hag⟩
    · exact Or.inr ⟨_, _, tc_rtc hxy, hm, rtc_refl _⟩
    · have hlt := gdepSameAgentLt pstep TS _ _ hwf hd hag
      rcases ih with ⟨hag', hlt'⟩ | ⟨p, q, hrp, hpq, hrq⟩
      · exact Or.inl ⟨hag'.trans hag, by omega⟩
      · exact Or.inr ⟨p, q, hrp, hpq, rtc_r hrq hyz⟩

/-! ### THE GAIN LEMMA -/

/-- Entering agent `u.1` through a milestone of measure µ, EVERY milestone-source
fulfil `x` of that agent at or after `u` has `ts(x) > µ`. -/
theorem mileMuGain (TS : Ptraces P D) (mu : Nat) (v u x : Gev) (tx : Nat) :
    ptracesWf pstep TS → ptracesFwdOwn TS → rfEdgesOkMs TS → eeOk TS →
    mileMu TS mu v u → u.1 = x.1 → u.2 ≤ x.2 →
    (∃ y, gmile TS x y) →
    gevTs TS x = some tx →
    mu < tx := by
  rintro hwf hfo hrf hee (⟨a, hts1, hrd, hne⟩ | ⟨r, a, hra, rfl⟩) hag hle hms htx
  · -- CROSS-RF ENTRY: S1.
    obtain ⟨T, hT, _⟩ := (gevWfBounds TS u).1 (gevReadsWf TS u a mu hrd)
    have hTx : TS.ptTrs[x.1]? = some T := by rw [← hag]; exact hT
    obtain ⟨ev, hev, hinr⟩ := gevReadsEv TS u a mu T hT hrd
    obtain ⟨evx, hevx, htsx⟩ := gevTsEv TS x tx T hTx htx
    -- the entry edge's source is FOREIGN, so the read is not forwarded
    obtain ⟨base, data, kc, hm⟩ := gevTsMsg pstep TS v mu hwf hts1
    have hunf : readUnforwarded TS.ptLog u.1 ev.aeLb mu :=
      Or.inr ⟨⟨base, data, some v.1, kc⟩, v.1, hm, rfl, hne⟩
    exact atraceS1LeF pstep TS.ptImg TS.ptLog u.1 T u.2 x.2 ev evx a mu tx (hwf u.1 T hT)
      (fun n ag hag' => hfo u.1 T n ag hT hag') hev hinr hunf hevx htsx hle
      (fun hklt => hrf v u T mu a x.2 evx hts1 hrd hne hT hklt hevx (by rw [htsx]; rfl)
        (by obtain ⟨y, hy⟩ := hms; exact ⟨y, by rw [hag]; exact hy⟩))
  · -- gE ENTRY.
    by_cases heq : u.2 = x.2
    · -- `x = u`: the E-target itself.  The edge's own bound.
      have hux : u = x := Prod.ext hag heq
      subst hux
      obtain ⟨l, ts, tstar, that, -, -, -, -, -, h6, -, hlt⟩ := hra
      rw [h6] at htx
      cases htx
      exact hlt
    · -- a STRICTLY later fulfil of the same agent: `eeOk`.
      exact hee r a v u x tx hra hag (by omega) htx

/-! ### THE MEASURE ON A CYCLE -/

/-- A milestone edge of measure µ SITS ON A CYCLE. -/
def onCycle2 (TS : Ptraces P D) (mu : Nat) : Prop :=
  ∃ v u, mileMu TS mu v u ∧ rtc (gdep2 TS) u v

/-- THE ADVANCE STEP. -/
theorem onCycle2Advance (TS : Ptraces P D) (mu : Nat) :
    ptracesWf pstep TS → ptracesFwdOwn TS → rfEdgesOkMs TS → eeOk TS →
    onCycle2 TS mu → ∃ mu', mu < mu' ∧ onCycle2 TS mu' := by
  rintro hwf hfo hrf hee ⟨v, u, hm, hpath⟩
  rcases rtcGdep2FirstMile pstep TS u v hwf hpath with
    ⟨hag, hle⟩ | ⟨x, y, hag, hle, hux, hmile, hyv⟩
  · -- NO milestone on the return path: the gain lemma applies to `v` itself.
    exfalso
    obtain ⟨tv, htv, hlev⟩ := mileMuSrcTs TS mu v u hm
    have hgt := mileMuGain pstep TS mu v u v tv hwf hfo hrf hee hm hag hle
      ⟨u, mileMuGmile TS mu v u hm⟩ htv
    omega
  · -- THE EXIT MILESTONE `x → y`.
    have hedge := mileMuGdep2 TS mu v u hm
    have hyx : rtc (gdep2 TS) y x := rtc_transitive hyv (rtc_l hedge hux)
    have hgm : gmile TS x y := hmile
    rcases hmile with ⟨hd, hne⟩ | ⟨r', hat⟩
    · -- CROSS-RF EXIT: µ' := ts(x).
      have hrfxy : WeakRobustGraph.grf TS x y := by
        rcases hd with ⟨hag', _⟩ | hrf'
        · exact absurd hag' hne
        · exact hrf'
      obtain ⟨ts2, a2, hts2, hrd2⟩ := hrfxy
      have hlt := mileMuGain pstep TS mu v u x ts2 hwf hfo hrf hee hm hag hle ⟨y, hgm⟩ hts2
      exact ⟨ts2, hlt, x, y, Or.inl ⟨a2, hts2, hrd2, hne⟩, hyx⟩
    · -- gE EXIT: µ' := F(r', a') ≥ ts(x), a LEAF of that floor.
      obtain ⟨a', hra'⟩ := gEAtGERa TS r' x y hat
      have hra'' := hra'
      obtain ⟨l', ts', tstar', that', -, -, hleaf', -, h5', -⟩ := hra''
      have hlt := mileMuGain pstep TS mu v u x tstar' hwf hfo hrf hee hm hag hle ⟨y, hgm⟩ h5'
      have hle' : tstar' ≤ rdFloor TS r' a' := lvalGe id _ _ hleaf'
      exact ⟨rdFloor TS r' a', by omega, x, y, Or.inr ⟨r', a', hra', rfl⟩, hyx⟩

theorem onCycle2Bounded (TS : Ptraces P D) (mu : Nat) :
    ptracesWf pstep TS → onCycle2 TS mu → mu ≤ TS.ptLog.length := by
  rintro hwf ⟨v, u, hm, -⟩
  exact mileMuBounded pstep TS mu v u hwf hm

/-- THE REFUTATION (measure `length log - µ`). -/
theorem onCycle2Empty (TS : Ptraces P D) :
    ptracesWf pstep TS → ptracesFwdOwn TS → rfEdgesOkMs TS → eeOk TS →
    ∀ mu, ¬ onCycle2 TS mu := by
  intro hwf hfo hrf hee
  have hgen : ∀ n mu, TS.ptLog.length - mu ≤ n → ¬ onCycle2 TS mu := by
    intro n
    induction n with
    | zero =>
      intro mu hn hoc
      have hb := onCycle2Bounded pstep TS mu hwf hoc
      obtain ⟨mu', hlt, hoc'⟩ := onCycle2Advance pstep TS mu hwf hfo hrf hee hoc
      have hb' := onCycle2Bounded pstep TS mu' hwf hoc'
      omega
    | succ n ih =>
      intro mu hn hoc
      obtain ⟨mu', hlt, hoc'⟩ := onCycle2Advance pstep TS mu hwf hfo hrf hee hoc
      have hb' := onCycle2Bounded pstep TS mu' hwf hoc'
      exact ih mu' (by omega) hoc'
  exact fun mu => hgen _ mu (Nat.le_refl _)

/-! ### THE THEOREM -/

theorem gdep2AcyclicEdgesOk (TS : Ptraces P D) :
    ptracesWf pstep TS → ptracesFwdOwn TS → rfEdgesOkMs TS → eeOk TS →
    gdep2Acyclic TS := by
  intro hwf hfo hrf hee e hc
  rcases tcGdep2Split pstep TS e e hwf hc with ⟨-, hlt⟩ | ⟨x, y, hrx, hmile, hry⟩
  · exact absurd hlt (Nat.lt_irrefl _)
  · obtain ⟨mu, hm⟩ := gmileMileMu TS x y hmile
    exact onCycle2Empty pstep TS hwf hfo hrf hee mu ⟨x, y, hm, rtc_transitive hry hrx⟩

/-- The `gdep`-acyclicity of `WeakRobustAcyc` is a corollary. -/
theorem gdepAcyclicOfGdep2 (TS : Ptraces P D) :
    ptracesWf pstep TS → ptracesFwdOwn TS → rfEdgesOkMs TS → eeOk TS →
    gdepAcyclic TS :=
  fun hwf hfo hrf hee => gdep2AcyclicGdep TS (gdep2AcyclicEdgesOk pstep TS hwf hfo hrf hee)

/-- …at the behavior level, with `fwdOwn` and `wsInit` DISCHARGED. -/
theorem wpBehaviorGdep2Acyclic (img : Image) (d0 : D) (ps : List P) (c : Wpcfg P D) :
    pdevOk pstep pdev →
    latFreeProg pstep → wpBehavior pstep img d0 ps c →
    ∃ (mid : Wpcfg P D) (TS : Ptraces P D),
      rtc (wpPromiseStep (P := P) (D := D)) (wpInit img d0 ps) mid ∧
      ptracesOf pstep TS mid c ∧
      noPromises c ∧
      ptracesWf pstep TS ∧
      ptracesFwdOwn TS ∧
      ptracesWsInit TS ∧
      (rfEdgesOkMs TS → eeOk TS → gdep2Acyclic TS) := by
  intro hpok hlfp hb
  obtain ⟨mid, TS, hprom, hTS, hnp⟩ := wpBehaviorTraced pstep pdev img d0 ps c hpok hlfp hb
  have hwf := ptracesOfWf pstep TS mid c hTS
  have hinit : cfgWsInit mid := cfgWsInitPromiseRun _ _ (cfgWsInitInit img d0 ps) hprom
  have hfo := ptracesOfFwdOwn pstep TS mid c hinit hTS
  have hwsi := ptracesOfWsInit pstep TS mid c hTS hinit
  exact ⟨mid, TS, hprom, hTS, hnp, hwf, hfo, hwsi,
    fun hrf hee => gdep2AcyclicEdgesOk pstep TS hwf hfo hrf hee⟩

end acyc2

/-! ## What W2b inherits from this file

`eeOk` (the one new premise, per (E edge, later fulfil), no cycle quantifier,
stated over the byte-named `gERa`); `gdep2AcyclicEdgesOk` (the hypothesis
`WeakRobustOrd`'s `toposortIndS` / `toposortIndFull` consume) and the
behavior-level wrapper `wpBehaviorGdep2Acyclic`; `rfEdgesOkMs` (A0) with
`rfEdgesOkRfEdgesOkMs`; and the milestone vocabulary (`gmile`, `mileMu`,
`onCycle2`, `mileMuGain`, `rtcGdep2FirstMile`, `tcGdep2Split`). -/

end Weak
